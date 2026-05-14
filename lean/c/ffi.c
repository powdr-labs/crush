/*
 * C bridge between the Rust caller and the Lean implementation of
 * `sequence_parallel_copies`.
 *
 * The Lean side exposes (via `@[export rust_seq_parallel_copies]`):
 *
 *     lean_object* rust_seq_parallel_copies(lean_object* /\* ByteArray *\/);
 *
 * Wire format (little-endian, packed):
 *   Input  : [src0, dst0, src1, dst1, ...]                       (UInt32 each)
 *   Output : [tag_s, val_s, tag_d, val_d, ...] per emitted copy   (UInt32 each)
 *            tag == 0 -> Register::Temp (val ignored)
 *            tag == 1 -> Register::Given(val)
 *
 * The caller (Rust) owns the output buffer returned by
 * `crush_seq_parallel_copies` and must release it via
 * `crush_seq_parallel_copies_free`.
 */

#include <lean/lean.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>

#include <stdio.h>

/* Symbols produced by the Lean compiler. */
extern lean_object *rust_seq_parallel_copies(lean_object *input);
extern lean_object *initialize_ParallelCopies_ParallelCopies(uint8_t builtin);

/* Runtime entry points (declared in libleanshared but not in lean.h). */
extern void lean_initialize_runtime_module(void);
extern void lean_io_mark_end_initialization(void);

/*
 * One-time runtime initialization. `lean_initialize_runtime_module` boots
 * the Lean heap allocator and runtime; the per-module `initialize_*` boots
 * the constants and closures emitted by Lean.
 */
static pthread_once_t init_once = PTHREAD_ONCE_INIT;

static void do_init(void) {
    lean_initialize_runtime_module();
    lean_object *res = initialize_ParallelCopies_ParallelCopies(1 /* builtin */);
    if (lean_io_result_is_error(res)) {
        /* If module initialization failed there is no recovery. */
        fprintf(stderr, "lean: ParallelCopies initialization failed\n");
        abort();
    }
    lean_dec_ref(res);
    lean_io_mark_end_initialization();
}

/*
 * Buffer handed back to Rust. `ptr` is malloc'd by us so Rust frees it via
 * `crush_seq_parallel_copies_free` (not `lean_dec_ref` — the Lean object's
 * lifetime ended inside this function).
 */
typedef struct {
    uint32_t *ptr;
    size_t    len_u32;
} crush_buf_t;

/*
 * Run the Lean implementation. `pairs` must point to `2 * num_pairs` u32s
 * (interleaved src/dst). On return, the output buffer's length in u32s is
 * 4 * (number of emitted copies). A NULL return indicates allocation failure.
 */
crush_buf_t crush_seq_parallel_copies(const uint32_t *pairs, size_t num_pairs) {
    pthread_once(&init_once, do_init);

    const size_t in_bytes = num_pairs * 2 * sizeof(uint32_t);

    /* Build a Lean ByteArray and copy the input into it. */
    lean_object *input = lean_alloc_sarray(1, in_bytes, in_bytes);
    if (in_bytes > 0) {
        memcpy(lean_sarray_cptr(input), pairs, in_bytes);
    }

    /* Call into Lean. Ownership of `input` transfers to Lean. */
    lean_object *output = rust_seq_parallel_copies(input);

    const size_t out_bytes = lean_sarray_size(output);
    crush_buf_t buf;
    buf.len_u32 = out_bytes / sizeof(uint32_t);

    if (buf.len_u32 == 0) {
        buf.ptr = NULL;
    } else {
        buf.ptr = (uint32_t *)malloc(out_bytes);
        if (buf.ptr == NULL) {
            lean_dec_ref(output);
            buf.len_u32 = 0;
            return buf;
        }
        memcpy(buf.ptr, lean_sarray_cptr(output), out_bytes);
    }

    lean_dec_ref(output);
    return buf;
}

void crush_seq_parallel_copies_free(crush_buf_t buf) {
    free(buf.ptr);
}
