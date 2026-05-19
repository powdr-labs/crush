import ParallelCopies
namespace ParallelCopies

def mkChain (n : Nat) : List Edge :=
  (List.range n).map fun i => (i.toUInt32, (i + 1).toUInt32)

def bench (label : String) (pairs : List Edge) (runs : Nat) : IO Unit := do
  let start ← IO.monoMsNow
  let mut checksum := 0
  let pairs := pairs.toArray
  for _ in [:runs] do
    let copies := sequenceParallelCopies pairs
    checksum := checksum + copies.size
  let elapsed ← IO.monoMsNow
  IO.println s!"{label}: {runs} runs of {pairs.size} copies -> checksum {checksum} in {elapsed - start} ms"

end ParallelCopies

def main : IO Unit := do
  ParallelCopies.bench "chain-10" (ParallelCopies.mkChain 10) 1000
  ParallelCopies.bench "chain-100" (ParallelCopies.mkChain 100) 100
  ParallelCopies.bench "chain-1000" (ParallelCopies.mkChain 1000) 1
