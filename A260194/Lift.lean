module

public import A260194.Results
public import Mathlib.Data.Int.GCD

@[expose] public section

namespace JumpResearch

theorem lift (n : ℕ) :
    let x := j (n+1)
    let y := j n
    let z := j (n+2)
    ∃ k k' : ℕ, 0<k ∧ a (n+3) = x*y*k ∧ a (n+4) = x*(1+k*y) ∧
      z = Nat.gcd (1+k*y) (x+y) ∧ z*k'=1+k*y ∧ a (n+5) = z*(1+k'*x) := by
  dsimp only
  let x := j (n+1)
  let y := j n
  let z := j (n+2)
  have hxy : Nat.Coprime x y := (show Nat.Coprime y x from adjacent n).symm
  have hd : x*y ∣ a (n+3) := by
    apply hxy.mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_left _ _)
    rw [step n]
    exact Nat.dvd_add (Nat.gcd_dvd_left _ _) (dvd_refl _)
  obtain ⟨k,hk⟩ := hd
  have hpos : 0<k := by
    by_contra h
    have : k=0 := by omega
    have := term_pos (n+3)
    simp_all
  have ha : a (n+4) = x*(1+k*y) := by
    rw [step (n+1),hk,Nat.mul_add,Nat.mul_one,Nat.mul_comm k y,Nat.mul_assoc,Nat.add_comm]
  have hs : Nat.Coprime x (x+y) := by
    change Nat.gcd x (x+y)=1
    simpa [Nat.add_comm] using hxy
  have hz : z=Nat.gcd (1+k*y) (x+y) := by
    change j (n+2)=_
    rw [twoStep,ha,show j n+j (n+1)=x+y from Nat.add_comm y x,
      Nat.gcd_comm (x*_), Nat.Coprime.gcd_mul_left_cancel_right _ hs,Nat.gcd_comm]
  obtain ⟨k',hk'⟩ : z ∣ 1+k*y := hz ▸ Nat.gcd_dvd_left _ _
  refine ⟨k,k',hpos,hk,ha,hz,hk'.symm,?_⟩
  rw [step (n+2),ha,hk']
  change x*(z*k')+z=z*(1+k'*x)
  rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm x, Nat.mul_assoc,Nat.add_comm]

end JumpResearch

namespace JumpResearch

theorem gcdShear (b s k : ℤ) : Int.gcd (b+k*s) s = Int.gcd b s := by
  apply Nat.dvd_antisymm
  · apply Int.natCast_dvd_natCast.mp
    apply Int.dvd_coe_gcd _ (Int.gcd_dvd_right _ _)
    have ha : (Int.gcd (b+k*s) s : ℤ) ∣ b+k*s := (Int.gcd_dvd_left _ _)
    have hs : (Int.gcd (b+k*s) s : ℤ) ∣ s := (Int.gcd_dvd_right _ _)
    have h := Int.dvd_sub ha (dvd_mul_of_dvd_right hs k)
    simpa using h
  · apply Int.natCast_dvd_natCast.mp
    exact Int.dvd_coe_gcd (Int.dvd_add (Int.gcd_dvd_left _ _) (dvd_mul_of_dvd_right (Int.gcd_dvd_right _ _) k)) (Int.gcd_dvd_right _ _)

theorem signedFormula (k x y : ℕ) :
    Nat.gcd (1+k*y) (x+y) = Int.gcd (1-(k:ℤ)*x) ((x:ℤ)+y) := by
  have eq : (1-(k:ℤ)*x)+(k:ℤ)*((x:ℤ)+y)=1+(k:ℤ)*y := by rw [Int.mul_add]; omega
  have h := gcdShear (1-(k:ℤ)*x) ((x:ℤ)+y) (k:ℤ)
  rw [eq] at h
  exact h

end JumpResearch
