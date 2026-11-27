module

public import A260194.Certificate
public import A260194.Results
public import A260194.Lift

@[expose] public section

namespace JumpResearch
open JumpCert

def Reach (n : ℕ) : Prop := ∃ i < size, (node i).x=j n ∧ (node i).y=j (n+1) ∧ fits (node i) (a (n+4))

theorem initialReach : Reach 13 := by
  refine ⟨0,by decide,by decide,by decide,?_⟩
  exact List.all_eq_true.mp (by decide : ((node 0).tests.all (fun t => t.2.testBit (a 17 % t.1))) = true)

theorem push {n : ℕ} (h : Reach n) : j (n+2) ∈ allowed ∧ Reach (n+1) := by
  obtain ⟨i,hi,hx,hy,fit⟩ := h
  have hd : j (n+2) = Nat.gcd (a (n+4)) ((node i).x+(node i).y) := by
    rw [hx,hy,twoStep n]
  have hs : 0 < (node i).x+(node i).y := by rw [hx,hy]; have := jumpPos n; omega
  obtain ⟨mem,k,hk,kx,ky,kfit⟩ := localStep (checked i hi) fit hd (jumpPos _) hs
  refine ⟨mem,k,hk,kx.trans hy,ky,?_⟩
  exact (step (n+2)) ▸ kfit

theorem reachable (t : ℕ) : Reach (13+t) := by
  induction t with
  | zero => exact initialReach
  | succ t ih => exact (push ih).2

theorem allJumps (n : ℕ) : j n ∈ allowed := by
  by_cases hn : n<15
  · have early : ∀ i : Fin 15, j i.val ∈ allowed := by decide
    exact early ⟨n,hn⟩
  · have he : 13+(n-15)+2=n := by omega
    exact he ▸ (push (reachable (n-15))).1

theorem omitsFourteen (n : ℕ) : j n ≠ 14 := by
  intro h
  have hm := allJumps n
  rw [h] at hm
  exact (by decide : 14 ∉ allowed) hm

theorem disproof : ¬ Universal := by
  intro universal
  obtain ⟨k,hk⟩ := (target.mp universal) 14 (by decide)
  exact omitsFourteen k hk

theorem periodic : PeriodicTail := by
  apply boundedIff.mp
  have h : ∀ d ∈ allowed, d ≤ 74 := by decide
  exact ⟨74,fun n => h _ (allJumps n)⟩

#print axioms disproof
#print axioms periodic
end JumpResearch

-- Literal quantifiers of FormalConjectures.OEIS.«260194».
theorem JumpResearch.refutesCatalogueStatement :
    ¬ (∀ d : ℕ, d > 0 → ∃ n : ℕ, JumpResearch.a (n+1) = JumpResearch.a n+d) :=
  JumpResearch.disproof

#print axioms JumpResearch.refutesCatalogueStatement
