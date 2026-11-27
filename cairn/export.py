"""Emit the self-contained Lean source for Cairn Commons' single-file checker."""
from pathlib import Path

root = Path(__file__).resolve().parents[1]
print("import FormalConjectures.OEIS.«260194»")
for module in ("Checker", "Certificate", "Results", "Lift", "Proof"):
    source = (root / "A260194" / f"{module}.lean").read_text()
    _, body = source.split("@[expose] public section", 1)
    # The full Formal Conjectures import reserves additional notation.
    body = body.replace("size≤i", "size ≤ i")
    print("\n".join(line for line in body.splitlines() if not line.startswith("#print axioms ")))

print("""
private theorem sameSequence (n : Nat) : JumpResearch.a n = OeisA260194.a n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rcases n with _ | (_ | (_ | k))
    · rfl
    · rfl
    · rfl
    · rw [JumpResearch.a, OeisA260194.a, ih (k + 2) (by omega), ih k (by omega)]

/-- Negative answer to Cairn's pinned question, with its original sequence and domains. -/
theorem main : ¬ (type_of% @OeisA260194.conjecture) := by
  intro all
  apply JumpResearch.refutesCatalogueStatement
  simpa only [sameSequence] using all
""".strip())
