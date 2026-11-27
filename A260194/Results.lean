module

public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Nat.Factorial.Basic

@[expose] public section

namespace JumpResearch

-- Lean term n corresponds to OEIS term n+1.
def a : ℕ → ℕ
  | 0 | 1 | 2 => 1
  | n+3 => a (n+2) + Nat.gcd (a (n+2)) (a n)

def Universal : Prop := ∀ d > 0, ∃ n, a (n+1) = a n + d

def j (n : ℕ) := Nat.gcd (a (n+2)) (a n)
theorem step (n : ℕ) : a (n+3) = a (n+2) + j n := by rw [a]; rfl

theorem target : Universal ↔ ∀ d > 0, ∃ k, j k = d := by
  constructor
  · intro h d hd
    obtain ⟨n, hn⟩ := h d hd
    rcases n with _ | n
    · change 1 = 1+d at hn; omega
    rcases n with _ | k
    · change 1 = 1+d at hn; omega
    exact ⟨k, Nat.add_left_cancel ((step k).symm.trans hn)⟩
  · intro h d hd
    obtain ⟨k,hk⟩ := h d hd
    exact ⟨k+2, hk ▸ step k⟩

theorem triple (n : ℕ) : Nat.gcd (a n) (Nat.gcd (a (n+1)) (a (n+2))) = 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [step, j, Nat.add_comm (a (n+2)), Nat.gcd_add_self_right]
    rw [Nat.gcd_eq_right (Nat.gcd_dvd_left _ _), Nat.gcd_comm (a (n+2))]
    rw [← Nat.gcd_assoc, Nat.gcd_comm (a (n+1)), Nat.gcd_assoc]
    exact ih

theorem adjacent (n : ℕ) : Nat.gcd (j n) (j (n+1)) = 1 := by
  apply Nat.dvd_one.mp
  apply (triple n) ▸ Nat.dvd_gcd
  · exact Nat.dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
  apply Nat.dvd_gcd
  · exact Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _)
  · exact Nat.dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)

theorem twoStep (n : ℕ) : j (n+2) = Nat.gcd (a (n+4)) (j n + j (n+1)) := by
  have e : a (n+4) = a (n+2) + (j n+j (n+1)) := by
    rw [step (n+1), step n, Nat.add_assoc]
  change Nat.gcd (a (n+4)) (a (n+2)) = _
  rw [e, Nat.gcd_comm ((a (n+2)) + _) (a (n+2)), Nat.add_comm (a (n+2))]
  simp [Nat.gcd_comm]

theorem term_pos (n : ℕ) : 0 < a n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 | 1 | 2 => decide
    | k+3 => have := ih (k+2) (by omega); rw [step]; omega

theorem recordJump (n : ℕ) (hx : j n < j (n+2)) (hy : j (n+1) < j (n+2)) :
    j (n+2) = j n + j (n+1) := by
  have hd : j (n+2) ∣ j n + j (n+1) := twoStep n ▸ Nat.gcd_dvd_right _ _
  obtain ⟨k,hk⟩ := hd
  cases k with
  | zero => have h := term_pos n; have h2 := term_pos (n+2); have h3 := Nat.gcd_pos_of_pos_left (a n) h2; change 0 < j n at h3; simp at hk; omega
  | succ k =>
    cases k with
    | zero => simpa using hk.symm
    | succ k => rw [Nat.mul_succ, Nat.mul_succ] at hk; omega

end JumpResearch

namespace JumpResearch

theorem jumpPos (n : ℕ) : 0 < j n :=
  Nat.gcd_pos_of_pos_left _ (term_pos _)

-- The modular argument behind the eight-jump obstruction.
theorem modThreeBlock (A x y : ℕ) (cop : Nat.gcd x y = 1)
    (h0 : 3 ∣ x → 3 ∣ A)
    (h1 : 3 ∣ y → 3 ∣ A+x)
    (h2 : 3 ∣ x+y → 3 ∣ A+x+y)
    (h3 : 3 ∣ x+2*y → 3 ∣ A+2*x+2*y)
    (h4 : 3 ∣ 2*x+3*y → 3 ∣ A+3*x+4*y)
    (h5 : 3 ∣ 3*x+5*y → 3 ∣ A+5*x+7*y)
    (h6 : 3 ∣ 5*x+8*y → 3 ∣ A+8*x+12*y)
    (h7 : 3 ∣ 8*x+13*y → 3 ∣ A+13*x+20*y) : False := by
  have hn : ¬ (3 ∣ x ∧ 3 ∣ y) := by
    rintro ⟨hx,hy⟩
    have h := Nat.dvd_gcd hx hy
    rw [cop] at h
    omega
  have residues (z : ℕ) : z%3=0 ∨ z%3=1 ∨ z%3=2 := by omega
  rcases residues x with hx|hx|hx <;> rcases residues y with hy|hy|hy <;>
    rcases residues A with ha|ha|ha <;> omega

def stateStep (s : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  let g := Nat.gcd s.1 (s.2.1+s.2.2)
  (s.1+g,s.2.2,g)

def advance : ℕ → (ℕ × ℕ × ℕ) → (ℕ × ℕ × ℕ)
  | 0,s => s
  | k+1,s => advance k (stateStep s)

theorem sync0 : advance 20 (0, 1, 1) = (57,2,1) := by decide
theorem sync1 : advance 25 (0, 1, 2) = (57,2,1) := by decide
theorem sync2 : advance 20 (0, 1, 3) = (57,2,1) := by decide
theorem sync3 : advance 26 (1, 0, 0) = (57,2,1) := by decide
end JumpResearch

namespace JumpResearch

def EqState (M i k : ℕ) : Prop :=
  a (i+4)%M = a (k+4)%M ∧ j i = j k ∧ j (i+1) = j (k+1)

theorem successor {B M i k : ℕ} (hM : M = (2*B).factorial)
    (bound : ∀ t, j t ≤ B) (h : EqState M i k) : EqState M (i+1) (k+1) := by
  obtain ⟨ha,hx,hy⟩ := h
  have hs : j k+j (k+1) ∣ M := by
    rw [hM]
    apply Nat.dvd_factorial
    · have := jumpPos k; omega
    · have := bound k; have := bound (k+1); omega
  have same (u v s : ℕ) (hd : s ∣ M) (h : u%M=v%M) : Nat.gcd u s = Nat.gcd v s := by
    have h' := congrArg (fun z => z%s) h
    simp only [Nat.mod_mod_of_dvd _ hd] at h'
    rw [Nat.gcd_comm u, Nat.gcd_rec s u, Nat.gcd_comm v, Nat.gcd_rec s v,h']
  have hz : j (i+2)=j (k+2) := by
    rw [twoStep i,twoStep k,hx,hy]
    exact same _ _ _ hs ha
  refine ⟨?_,hy,hz⟩
  rw [step (i+2),step (k+2),Nat.add_mod, Nat.add_mod (a (k+4)), ha,hz]

def PeriodicTail : Prop := ∃ start p : ℕ, 0<p ∧ ∀ t, j (start+t)=j (start+p+t)

theorem boundedIff : (∃ B, ∀ t, j t ≤ B) ↔ PeriodicTail := by
  constructor
  · rintro ⟨B,hB⟩
    let M := (2*B).factorial
    let f (t : ℕ) : Fin M × Fin (B+1) × Fin (B+1) :=
      (⟨_,Nat.mod_lt (a (t+4)) (Nat.factorial_pos _)⟩,
       ⟨j t,Nat.lt_succ_of_le (hB t)⟩,⟨j (t+1),Nat.lt_succ_of_le (hB _)⟩)
    obtain ⟨i,k,hne,he⟩ := Finite.exists_ne_map_eq_of_infinite f
    have build (i k : ℕ) (hi : i<k) (he : f i=f k) : PeriodicTail := by
      have base : EqState M i k := ⟨congrArg (fun z => z.1.val) he,
        congrArg (fun z => z.2.1.val) he, congrArg (fun z => z.2.2.val) he⟩
      refine ⟨i,k-i,by omega,?_⟩
      intro t
      have ht : EqState M (i+t) (k+t) := by
        induction t with
        | zero => exact base
        | succ t ih => exact successor rfl hB ih
      have heq : i+(k-i)=k := by omega
      rw [heq]
      exact ht.2.1
    rcases lt_or_gt_of_ne hne with h|h
    · exact build i k h he
    · exact build k i h he.symm
  · rintro ⟨s,p,hp,h⟩
    let B := ((Finset.range (s+p)).image j).sup id
    refine ⟨B,?_⟩
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n<s+p
      · exact Finset.le_sup (s := (Finset.range (s+p)).image j) (f := id)
          (Finset.mem_image_of_mem j (Finset.mem_range.mpr hn))
      · have eq1 : s+p+(n-(s+p))=n := by omega
        have eq2 := h (n-(s+p))
        rw [eq1] at eq2
        rw [← eq2]
        exact ih _ (by omega)
end JumpResearch

namespace JumpResearch

theorem noEight (n : ℕ)
    (full : ∀ k < 6, j (n+k+2) = j (n+k)+j (n+k+1)) : False := by
  have transfer (k : ℕ) (h : 3 ∣ j (n+k)) : 3 ∣ a (n+k+2) :=
    Nat.dvd_trans h (Nat.gcd_dvd_left _ _)
  have f0 : j (n+2)=j (n+0)+j (n+1) := full 0 (by decide)
  have f1 : j (n+3)=j (n+1)+j (n+2) := full 1 (by decide)
  have f2 : j (n+4)=j (n+2)+j (n+3) := full 2 (by decide)
  have f3 : j (n+5)=j (n+3)+j (n+4) := full 3 (by decide)
  have f4 : j (n+6)=j (n+4)+j (n+5) := full 4 (by decide)
  have f5 : j (n+7)=j (n+5)+j (n+6) := full 5 (by decide)
  have e0 : a (n+3)=a (n+2)+j (n+0) := step (n+0)
  have e1 : a (n+4)=a (n+3)+j (n+1) := step (n+1)
  have e2 : a (n+5)=a (n+4)+j (n+2) := step (n+2)
  have e3 : a (n+6)=a (n+5)+j (n+3) := step (n+3)
  have e4 : a (n+7)=a (n+6)+j (n+4) := step (n+4)
  have e5 : a (n+8)=a (n+7)+j (n+5) := step (n+5)
  have e6 : a (n+9)=a (n+8)+j (n+6) := step (n+6)
  apply modThreeBlock (a (n+2)) (j n) (j (n+1)) (adjacent n)
  · intro h; have hd : 3 ∣ j (n+0) → 3 ∣ a (n+2) := transfer 0; simp only [Nat.add_zero] at *; omega
  · intro h; have hd : 3 ∣ j (n+1) → 3 ∣ a (n+3) := transfer 1; simp only [Nat.add_zero] at *; omega
  · intro h; have hd : 3 ∣ j (n+2) → 3 ∣ a (n+4) := transfer 2; simp only [Nat.add_zero] at *; omega
  · intro h; have hd : 3 ∣ j (n+3) → 3 ∣ a (n+5) := transfer 3; simp only [Nat.add_zero] at *; omega
  · intro h; have hd : 3 ∣ j (n+4) → 3 ∣ a (n+6) := transfer 4; simp only [Nat.add_zero] at *; omega
  · intro h; have hd : 3 ∣ j (n+5) → 3 ∣ a (n+7) := transfer 5; simp only [Nat.add_zero] at *; omega
  · intro h; have hd : 3 ∣ j (n+6) → 3 ∣ a (n+8) := transfer 6; simp only [Nat.add_zero] at *; omega
  · intro h; have hd : 3 ∣ j (n+7) → 3 ∣ a (n+9) := transfer 7; simp only [Nat.add_zero] at *; omega
end JumpResearch

namespace JumpResearch

theorem distanceTwo (n : ℕ) : Nat.gcd (j n) (j (n+2)) = 1 := by
  apply Nat.dvd_one.mp
  apply (triple (n+2)) ▸ Nat.dvd_gcd
  · exact Nat.dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)
  apply Nat.dvd_gcd
  · apply Nat.dvd_trans (Nat.gcd_dvd_left _ _)
    rw [step]
    exact Nat.dvd_add (Nat.gcd_dvd_left _ _) (dvd_refl _)
  · exact Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)

theorem squareBound (n : ℕ) : j (n+2)*j (n+2) ≤ 2*a (n+4) := by
  let d := j (n+2)
  have h1 : j n * d ≤ a (n+2) := by
    apply Nat.le_of_dvd (term_pos _)
    exact (show Nat.Coprime (j n) d from distanceTwo n).mul_dvd_of_dvd_of_dvd
      (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
  have h2 : j (n+1)*d ≤ a (n+4) := by
    apply Nat.le_of_dvd (term_pos _)
    apply (show Nat.Coprime (j (n+1)) d from adjacent (n+1)).mul_dvd_of_dvd_of_dvd
    · rw [step (n+1)]
      exact Nat.dvd_add (Nat.gcd_dvd_left _ _) (dvd_refl _)
    · exact Nat.gcd_dvd_left _ _
  have hd : d ≤ j n+j (n+1) := by
    have h := jumpPos n
    apply Nat.le_of_dvd (by omega)
    change j (n+2) ∣ _
    rw [twoStep]; exact Nat.gcd_dvd_right _ _
  have up := Nat.mul_le_mul_right d hd
  rw [Nat.add_mul] at up
  have h3 := step n
  have h4 : a (n+4)=a (n+3)+j (n+1) := step (n+1)
  change d*d ≤ _
  omega

end JumpResearch

namespace JumpResearch

theorem termSquare (n : ℕ) : 2*a (n+4) ≤ (n+3)*(n+3) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h := squareBound n
    have hj := Nat.mul_self_le_mul_self_iff.mp (le_trans h ih)
    have hs : a (n+5) = a (n+4)+j (n+2) := step (n+2)
    change 2*a (n+5) ≤ (n+3+1)*(n+3+1)
    rw [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega

theorem indexBound (n : ℕ) : j (n+2) ≤ n+3 :=
  Nat.mul_self_le_mul_self_iff.mp ((squareBound n).trans (termSquare n))

end JumpResearch

namespace JumpResearch

theorem smallIncoming (q y : ℕ) (hq : 0<q) (hy : 0<y)
    (hqy : q ∣ y+1) (hyq : y ∣ q+1) : y ≤ 3 := by
  have l := Nat.le_of_dvd (by omega : 0<y+1) hqy
  have r := Nat.le_of_dvd (by omega : 0<q+1) hyq
  rcases lt_trichotomy q y with h|h|h
  · have e : y=q+1 := by omega
    have d : q ∣ (y+1)-q := Nat.dvd_sub hqy (dvd_refl _)
    have : (y+1)-q=2 := by omega
    rw [this] at d
    have := Nat.le_of_dvd (by decide : 0<2) d
    omega
  · subst y
    have d := Nat.dvd_sub hqy (dvd_refl q)
    have : q+1-q=1 := by omega
    rw [this] at d
    have := Nat.dvd_one.mp d
    omega
  · have e : q=y+1 := by omega
    have d : y ∣ (q+1)-y := Nat.dvd_sub hyq (dvd_refl _)
    have : (q+1)-y=2 := by omega
    rw [this] at d
    have := Nat.le_of_dvd (by decide : 0<2) d
    omega

theorem incomingAtAnchor (H q x y : ℕ) (hy : 0<y) (hq : 0<q)
    (bounds : x+y ≤ H)
    (hxH : x ∣ H) (hxEnd : x ∣ H-y)
    (hqH : q ∣ H) (hqEnd : q ∣ H-y-x)
    (hySum : y ∣ q+x) (cop : Nat.gcd x y=1) : x=1 ∧ y≤3 := by
  have hxd := Nat.dvd_sub hxH hxEnd
  have ex : H-(H-y)=y := by omega
  rw [ex] at hxd
  have hx := (Nat.gcd_eq_left hxd).symm.trans cop
  subst x
  have hqd := Nat.dvd_sub hqH hqEnd
  have eq : H-(H-y-1)=y+1 := by omega
  rw [eq] at hqd
  exact ⟨rfl,smallIncoming q y hq hy hqd hySum⟩

#print axioms boundedIff
#print axioms noEight
#print axioms indexBound
#print axioms incomingAtAnchor
end JumpResearch

namespace JumpResearch

def shift (H : ℕ) (s : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (H+s.1,s.2)

theorem translateStep (H : ℕ) (s : ℕ × ℕ × ℕ) (hd : s.2.1+s.2.2 ∣ H) :
    stateStep (shift H s) = shift H (stateStep s) := by
  rcases s with ⟨t,x,y⟩
  simp only [shift,stateStep, Nat.gcd_add_left_left_of_dvd t hd, Nat.add_assoc]

theorem advanceSucc (s : ℕ × ℕ × ℕ) (n : ℕ) :
    advance (n+1) s = stateStep (advance n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact ih (stateStep s)

-- Divisibility is assumed only on the shifted trajectory.
theorem translateOrbit (H : ℕ) (s : ℕ × ℕ × ℕ)
    (hd : ∀ n, (advance n (shift H s)).2.1+(advance n (shift H s)).2.2 ∣ H)
    (k : ℕ) : advance k (shift H s) = shift H (advance k s) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hh := hd k
    rw [ih] at hh
    rw [advanceSucc,advanceSucc,ih]
    exact translateStep H (advance k s) hh

-- A divisible step cannot straddle a multiple of its length.
theorem cannotOvershoot (a d H : ℕ) (ha : d ∣ a) (hH : d ∣ H) (lt : a<H) :
    a+d ≤ H := by
  have hd := Nat.dvd_sub hH ha
  have h := Nat.le_of_dvd (by omega : 0<H-a) hd
  omega

end JumpResearch

namespace JumpResearch

theorem extensionGcd (T u v w t : ℕ) (hs : u+v=w*t)
    (hd : w ∣ T+v) (hc : Nat.Coprime t (T+v)) :
    Nat.gcd (T+v) (u+v) = w := by
  rw [hs,Nat.gcd_comm,Nat.mul_comm w t]
  exact Nat.gcd_mul_of_coprime_of_dvd hc hd

-- Direct finite witness: start from the actual three seed terms.
def jumpsFrom : ℕ → ℕ → ℕ → ℕ → List ℕ
  | 0, _, _, _ => []
  | k+1, a, b, c => let d := Nat.gcd c a; d :: jumpsFrom k b c (c+d)

def seedA : ℕ := 232231460613007145212031072070099179616313067038047523721322418270607236072327592521978927086811483536244428647198867059733078238190700455802034190087758518207427291246874323599917663102132789228229703921556250229944477518524008200408556029851964817531946926309251331948603722223051133775010608352050667847474074144456987142186799788493260146048516184915290116532378524297922804231790057037506469883874770022179074664893787612051725284484167196914707326499112919849242778491638681239211439350741232200022743435596156560108356347197016804224648591573386292196780946974865864684519367496884045538849527624459793558076216220124189605482862978226096732982189875627077191825433535684859154063081421415316628431355387414675993087635737628032632132237285348662846540826029145138931858565681139277593371798467045325664443622124621243477140074642190135064890036976277840018628261670043422877772292212264881780869992568250954824692952656341491608863420237759552844976961400495493149233855048786498822953866410907182695659158346896206398062083604088119553483609510613284075410617986790423855423094461898342207845039998978120192146686870017845850164486502939206560036923403925429338554558800469987079734973478919811542280933216649520880480087778421840111728574234023181662319556615067030283525802755402737000951859066209344351032645586657025987826229200054295415710416053594058020569595718019473323515455714396443213038871995859793453965937552052307431954
def seedB : ℕ := seedA + 799170110108322945099894023424404086477908129286638387158
def seedC : ℕ := seedB + 170857446128816603145683218696710047040387095433227204363
theorem primitiveExample : Nat.gcd seedA (Nat.gcd seedB seedC) = 1 := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem lateExample : let jumps := jumpsFrom 50 seedA seedB seedC
                      14 ∉ jumps.take 49 ∧ jumps[49]? = some 14 := by decide
end JumpResearch
