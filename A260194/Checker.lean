module

public import Lean

@[expose] public section

namespace JumpCert

structure Cell where
  x : Nat
  y : Nat
  tests : List (Nat × Nat)
deriving Repr

inductive Act
| block (q : Nat)
| move (i : Nat)
deriving Repr

def fits (c : Cell) (a : Nat) : Prop :=
  ∀ t ∈ c.tests, t.2.testBit (a % t.1) = true

def permit (c : Cell) (q r : Nat) : Bool :=
  c.tests.all fun t => t.1 != q || t.2.testBit r

def projection (c : Cell) (d q mask : Nat) : Bool :=
  decide (0<q) && (List.range q).all fun r =>
    !(permit c q r) || Nat.gcd r (Nat.gcd q (c.x+c.y)) != Nat.gcd d (Nat.gcd q (c.x+c.y))
      || mask.testBit ((r+d)%q)

theorem projected {c : Cell} {a d q mask : Nat} (fit : fits c a)
    (hd : d = Nat.gcd a (c.x+c.y)) (ok : projection c d q mask = true) :
    mask.testBit ((a+d)%q) = true := by
  simp only [projection, Bool.and_eq_true, decide_eq_true_eq] at ok
  have h := List.all_eq_true.mp ok.2 (a%q) (List.mem_range.mpr (Nat.mod_lt _ ok.1))
  have hp : permit c q (a%q) = true := by
    apply List.all_eq_true.mpr
    intro t ht
    by_cases he : t.1=q
    · have ht' := fit t ht
      simpa [he] using ht'
    · simp [he]
  let g := Nat.gcd q (c.x+c.y)
  have hgq : g ∣ q := Nat.gcd_dvd_left _ _
  have hgs : g ∣ c.x+c.y := Nat.gcd_dvd_right _ _
  have eq : Nat.gcd (a%q) g = Nat.gcd d g := by
    rw [hd, Nat.gcd_assoc, Nat.gcd_eq_right hgs, Nat.gcd_comm (a%q) g,
      Nat.gcd_rec g (a%q),Nat.mod_mod_of_dvd _ hgq, ← Nat.gcd_rec, Nat.gcd_comm]
  change ((!permit c q (a%q) || Nat.gcd (a%q) g != Nat.gcd d g) ||
    mask.testBit ((a%q+d)%q)) = true at h
  simpa [hp,eq,Nat.mod_add_mod] using h

def allowed : List Nat :=
  [1,2,3,4,5,6,7,8,9,10,11,12,13,15,16,17,18,19,20,21,22,23,24,25,29,31,32,34,41,43,44,64,73,74]

def edge (get : Nat → Cell) (size : Nat) (c : Cell) (d : Nat) : Act → Bool
  | .block q => projection c d q 0
  | .move i => decide (i<size) && allowed.contains d && (get i).x == c.y &&
      (get i).y == d && (get i).tests.all (fun t => projection c d t.1 t.2)

def row (get : Nat → Cell) (size : Nat) (i : Nat) (rules : List (Nat × Act)) : Bool :=
  let c := get i
  ((List.range (c.x+c.y+1)).all fun d =>
    d == 0 || (c.x+c.y)%d != 0 || rules.any (fun r => r.1 == d && edge get size c d r.2))

theorem localStep {get : Nat → Cell} {size i a d : Nat} {rules : List (Nat × Act)}
    (hr : row get size i rules = true) (fit : fits (get i) a)
    (hd : d = Nat.gcd a ((get i).x+(get i).y)) (hp : 0<d)
    (hs : 0<(get i).x+(get i).y) :
    d ∈ allowed ∧ ∃ k<size, (get k).x=(get i).y ∧ (get k).y=d ∧ fits (get k) (a+d) := by
  have hv : d ∣ (get i).x+(get i).y := hd ▸ Nat.gcd_dvd_right _ _
  have hl := Nat.le_of_dvd hs hv
  have hb := List.all_eq_true.mp hr d (List.mem_range.mpr (by omega))
  simp only [Nat.mod_eq_zero_of_dvd hv, bne_self_eq_false, Bool.or_false,
    show (d == 0) = false from beq_eq_false_iff_ne.mpr (by omega), Bool.false_or] at hb
  obtain ⟨⟨v,act⟩,_,hv⟩ := List.any_eq_true.mp hb
  simp only [Bool.and_eq_true, beq_iff_eq] at hv
  obtain ⟨rfl,h⟩ := hv
  cases act with
  | block q =>
    have impossible := projected fit hd h
    simp at impossible
  | move k =>
    simp only [edge, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem, beq_iff_eq] at h
    exact ⟨h.1.1.1.2,k,h.1.1.1.1,h.1.1.2,h.1.2,
      fun t ht => projected fit hd (List.all_eq_true.mp h.2 t ht)⟩

end JumpCert
