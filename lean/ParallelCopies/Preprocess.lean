import ParallelCopies
import ParallelCopies.Spec
import Std.Data.HashSet.Lemmas

namespace ParallelCopies.Spec

variable (edges : Array Edge)

/-- Pure step function of `preprocess`'s loop body, used to rephrase the
    do-block as an `Array.foldl` for induction. -/
private def preprocessStep (e : Edge) (b : MProd (Array Edge) (Std.HashSet Edge)) :
    MProd (Array Edge) (Std.HashSet Edge) :=
  if e.1 == e.2 then b
  else if b.snd.contains e then b
  else ⟨b.fst.push e, b.snd.insert e⟩

/-- `preprocess` factors through `Array.foldl preprocessStep`. -/
private theorem preprocess_eq_foldl :
    preprocess edges =
      (edges.foldl (fun b a => preprocessStep a b) ⟨#[], ∅⟩).fst := by
  simp [preprocess, Id.run, bind_pure_comp, map_pure,
             ← apply_ite (fun x => pure (f := Id) (ForInStep.yield x)),
             -beq_iff_eq]
  rfl

theorem preprocess_no_id :
  ∀ e ∈ preprocess edges, e.1 ≠ e.2 := by
  rw [preprocess_eq_foldl]
  apply Array.foldl_induction
      (fun _ (b : MProd (Array Edge) _) => ∀ x ∈ b.fst, x.1 ≠ x.2) <;> grind [preprocessStep]

theorem preprocess_subset :
  ∀ e ∈ preprocess edges, e ∈ edges := by
  rw [preprocess_eq_foldl]
  apply Array.foldl_induction
      (motive := fun _ (b : MProd (Array Edge) (Std.HashSet Edge)) =>
                   ∀ x ∈ b.fst, x ∈ edges) <;> grind [preprocessStep]

/-- Strong loop invariant of `preprocess`: after processing the prefix `[0, i)`,
    every prior non-self-copy is in the result, and the HashSet only contains
    elements that are already in the result. -/
private def preprocessInv (i : Nat) (b : MProd (Array Edge) (Std.HashSet Edge)) : Prop :=
  (∀ j (hj : j < edges.size), j < i → edges[j].1 ≠ edges[j].2 → edges[j] ∈ b.fst) ∧
  (∀ x : Edge, b.snd.contains x = true → x ∈ b.fst)

theorem preprocess_complete :
  ∀ e ∈ edges, e.1 ≠ e.2 → e ∈ preprocess edges := by
  rw [preprocess_eq_foldl]
  have key : preprocessInv edges edges.size
      (edges.foldl (fun b a => preprocessStep a b) ⟨#[], ∅⟩) := by
    apply Array.foldl_induction (motive := preprocessInv edges) <;>
      grind [preprocessInv, preprocessStep]
  intro e he hne
  obtain ⟨j, hj, heq⟩ := Array.mem_iff_getElem.mp he
  subst heq
  exact key.1 j hj hj hne

end ParallelCopies.Spec
