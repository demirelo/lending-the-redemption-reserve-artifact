/-
Machine-checked proof of the safety theorem (Theorem 1) of
"Lending the Redemption Reserve".

The reserve function `R` is abstract. `Sched R Pf C` records the two
properties of a reserve function that the proof uses (Lemma 1 of the paper):
`R 0 = 0` and `Pf * (b - a) ≤ R b - R a` for `0 ≤ a ≤ b ≤ C`. Every reserve
function `R(x) = ∫₀ˣ p` of a non-decreasing schedule `p ≥ Pf` has them.

Accounts are `Fin n`. A loan is a pair `(l i, d i)`; `(0, 0)` means "no loan".
-/
import Mathlib

open Finset BigOperators

namespace FloorCredit

variable {n : ℕ}

/-- The properties of a reserve function used by the safety proof. -/
structure Sched (R : ℝ → ℝ) (Pf C : ℝ) : Prop where
  pf_pos : 0 < Pf
  cap_pos : 0 < C
  zero : R 0 = 0
  slope : ∀ a b, 0 ≤ a → a ≤ b → b ≤ C → Pf * (b - a) ≤ R b - R a

/-- State of the issuer. -/
structure State (n : ℕ) where
  R : ℝ → ℝ
  Pf : ℝ
  C : ℝ
  S : ℝ
  A : ℝ
  γ : ℝ
  h : Fin n → ℝ
  l : Fin n → ℝ
  d : Fin n → ℝ

/-- Locked supply. -/
def State.L (s : State n) : ℝ := ∑ i, s.l i
/-- Total debt. -/
def State.D (s : State n) : ℝ := ∑ i, s.d i
/-- Total free balance. -/
def State.H (s : State n) : ℝ := ∑ i, s.h i

/-- Domain conditions ("valid state"). -/
structure Valid (γb : ℝ) (s : State n) : Prop where
  sched : Sched s.R s.Pf s.C
  S_nonneg : 0 ≤ s.S
  S_le : s.S ≤ s.C
  A_nonneg : 0 ≤ s.A
  γ_pos : 0 < s.γ
  γ_le : s.γ ≤ γb
  h_nonneg : ∀ i, 0 ≤ s.h i
  l_nonneg : ∀ i, 0 ≤ s.l i
  d_nonneg : ∀ i, 0 ≤ s.d i

/-- The safety invariant `J` together with validity. -/
structure Inv (γb : ℝ) (s : State n) : Prop where
  valid : Valid γb s
  J1 : s.H + s.L = s.S
  J2 : ∀ i, s.d i ≤ γb * s.Pf * s.l i
  J3 : s.R s.S ≤ s.A + s.D

/-- The operations of the mechanism, each with its guard. -/
inductive Step (γb : ℝ) : State n → State n → Prop
  | buy (s : State n) (u : Fin n) (x c : ℝ)
      (hx : 0 < x) (hcap : s.S + x ≤ s.C) (hc : s.R (s.S + x) - s.R s.S ≤ c) :
      Step γb s { s with S := s.S + x, A := s.A + c,
                         h := Function.update s.h u (s.h u + x) }
  | sell (s : State n) (u : Fin n) (x o : ℝ)
      (hx : 0 < x) (hbal : x ≤ s.h u) (ho : 0 ≤ o) (hret : o ≤ s.R s.S - s.R (s.S - x)) :
      Step γb s { s with S := s.S - x, A := s.A - o,
                         h := Function.update s.h u (s.h u - x) }
  | borrow (s : State n) (i : Fin n) (lp b o : ℝ)
      (hlp : 0 ≤ lp) (hbal : lp ≤ s.h i) (hb : 0 < b)
      (hltv : s.d i + b ≤ s.γ * s.Pf * (s.l i + lp)) (ho : 0 ≤ o) (hob : o ≤ b) :
      Step γb s { s with A := s.A - o,
                         h := Function.update s.h i (s.h i - lp),
                         l := Function.update s.l i (s.l i + lp),
                         d := Function.update s.d i (s.d i + b) }
  | repayFull (s : State n) (i : Fin n) (hd : 0 < s.d i) :
      Step γb s { s with A := s.A + s.d i,
                         h := Function.update s.h i (s.h i + s.l i),
                         l := Function.update s.l i 0,
                         d := Function.update s.d i 0 }
  | repayPart (s : State n) (i : Fin n) (r u : ℝ)
      (hr : 0 < r) (hrd : r < s.d i) (hu : 0 ≤ u) (hrel : u * s.d i ≤ s.l i * r) :
      Step γb s { s with A := s.A + r,
                         h := Function.update s.h i (s.h i + u),
                         l := Function.update s.l i (s.l i - u),
                         d := Function.update s.d i (s.d i - r) }
  | setLTV (s : State n) (g : ℝ) (hg : 0 < g) (hgb : g ≤ γb) :
      Step γb s { s with γ := g }
  | transfer (s : State n) (u v : Fin n) (x : ℝ)
      (hx : 0 < x) (hbal : x ≤ s.h u) (huv : v ≠ u) :
      Step γb s { s with h := Function.update (Function.update s.h u (s.h u - x)) v (s.h v + x) }
  | reshape (s : State n) (R' : ℝ → ℝ) (Pf' C' c : ℝ)
      (hs : Sched R' Pf' C') (hcap : s.S ≤ C') (hc : 0 ≤ c)
      (G1 : s.Pf ≤ Pf') (G2 : R' s.S ≤ s.A + c + s.D) :
      Step γb s { s with R := R', Pf := Pf', C := C', A := s.A + c }
  | skim (s : State n) (w : ℝ) (hw : 0 < w) (hsur : w ≤ s.A + s.D - s.R s.S) :
      Step γb s { s with A := s.A - w }
  | accrue (s : State n) (i : Fin n) (δ : ℝ)
      (hδ : 0 < δ) (hcap : s.d i + δ ≤ γb * s.Pf * s.l i) :
      Step γb s { s with d := Function.update s.d i (s.d i + δ) }

/-! ### Auxiliary lemmas -/

lemma sum_update (f : Fin n → ℝ) (i : Fin n) (x : ℝ) :
    ∑ j, Function.update f i x j = ∑ j, f j - f i + x := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
  have := Finset.add_sum_erase Finset.univ f (Finset.mem_univ i)
  linarith

lemma Sched.mono {R : ℝ → ℝ} {Pf C : ℝ} (hs : Sched R Pf C) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ C) : R a ≤ R b := by
  have h := hs.slope a b ha hab hb
  have : 0 ≤ Pf * (b - a) := mul_nonneg hs.pf_pos.le (by linarith)
  linarith

lemma Sched.floor {R : ℝ → ℝ} {Pf C : ℝ} (hs : Sched R Pf C) {x : ℝ}
    (hx : 0 ≤ x) (hxC : x ≤ C) : Pf * x ≤ R x := by
  have h := hs.slope 0 x le_rfl hx hxC
  rw [hs.zero] at h
  linarith

variable {γb : ℝ}

lemma Inv.L_nonneg {s : State n} (hI : Inv γb s) : 0 ≤ s.L :=
  Finset.sum_nonneg fun i _ => hI.valid.l_nonneg i

lemma Inv.H_nonneg {s : State n} (hI : Inv γb s) : 0 ≤ s.H :=
  Finset.sum_nonneg fun i _ => hI.valid.h_nonneg i

lemma Inv.L_le_S {s : State n} (hI : Inv γb s) : s.L ≤ s.S := by
  have := hI.H_nonneg; have := hI.J1; linarith

lemma Inv.h_le_H {s : State n} (hI : Inv γb s) (u : Fin n) : s.h u ≤ s.H :=
  Finset.single_le_sum (fun i _ => hI.valid.h_nonneg i) (Finset.mem_univ u)

/-- Total debt is at most `γb * Pf * L` (sum of (J2)). -/
lemma Inv.D_le {s : State n} (hI : Inv γb s) : s.D ≤ γb * s.Pf * s.L := by
  unfold State.D State.L
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => hI.J2 i

/-- Total debt is at most `γb * R(L)`. -/
lemma Inv.D_le_R {s : State n} (hγ0 : 0 ≤ γb) (hI : Inv γb s) : s.D ≤ γb * s.R s.L := by
  have h1 := hI.D_le
  have h2 := hI.valid.sched.floor hI.L_nonneg (hI.L_le_S.trans hI.valid.S_le)
  have h3 : γb * (s.Pf * s.L) ≤ γb * s.R s.L := mul_le_mul_of_nonneg_left h2 hγ0
  nlinarith

/-! ### Theorem 1 (b): coverage with slack -/

/-- In every `J`-state the cash covers the curve return of any `x ≤ S - L`
free tokens, with slack `(1 - γb) * R(L)`. -/
theorem coverage (hγ0 : 0 ≤ γb) {s : State n} (hI : Inv γb s) {x : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ s.S - s.L) :
    s.R s.S - s.R (s.S - x) + (1 - γb) * s.R s.L ≤ s.A := by
  have hD := hI.D_le_R hγ0
  have hmono : s.R s.L ≤ s.R (s.S - x) :=
    hI.valid.sched.mono hI.L_nonneg (by linarith) (by linarith [hI.valid.S_le])
  have := hI.J3
  nlinarith

/-- Every sale whose guard holds can be paid its full curve return. -/
theorem sell_payable (hγ0 : 0 ≤ γb) (hγ1 : γb ≤ 1) {s : State n} (hI : Inv γb s)
    {u : Fin n} {x : ℝ} (hx : 0 < x) (hbal : x ≤ s.h u) :
    s.R s.S - s.R (s.S - x) ≤ s.A := by
  have hxS : x ≤ s.S - s.L := by
    have := hI.h_le_H u; have := hI.J1; linarith
  have hc := coverage hγ0 hI hx.le hxS
  have hRL : 0 ≤ s.R s.L := by
    have := hI.valid.sched.floor hI.L_nonneg (hI.L_le_S.trans hI.valid.S_le)
    have : 0 ≤ s.Pf * s.L := mul_nonneg hI.valid.sched.pf_pos.le hI.L_nonneg
    linarith
  have : 0 ≤ (1 - γb) * s.R s.L := mul_nonneg (by linarith) hRL
  linarith

/-! ### Theorem 1 (c): loans and skims can be paid -/

/-- Every borrow whose guard holds satisfies `b ≤ A - (1 - γb) * R(S)`. -/
theorem borrow_payable (hγ0 : 0 ≤ γb) {s : State n} (hI : Inv γb s)
    {i : Fin n} {lp b : ℝ} (hlp : 0 ≤ lp) (hbal : lp ≤ s.h i)
    (hltv : s.d i + b ≤ s.γ * s.Pf * (s.l i + lp)) :
    b ≤ s.A - (1 - γb) * s.R s.S := by
  have hPf := hI.valid.sched.pf_pos
  have hli := hI.valid.l_nonneg i
  -- the borrower's new loan respects the cap
  have hi : s.d i + b ≤ γb * s.Pf * (s.l i + lp) := by
    have h1 : s.γ * (s.Pf * (s.l i + lp)) ≤ γb * (s.Pf * (s.l i + lp)) :=
      mul_le_mul_of_nonneg_right hI.valid.γ_le (mul_nonneg hPf.le (by linarith))
    nlinarith
  -- the other loans: D - d i ≤ γb Pf (L - l i)
  have hrest : s.D - s.d i ≤ γb * s.Pf * (s.L - s.l i) := by
    have h1 : ∑ j ∈ Finset.univ.erase i, s.d j ≤ ∑ j ∈ Finset.univ.erase i, γb * s.Pf * s.l j :=
      Finset.sum_le_sum fun j _ => hI.J2 j
    rw [← Finset.mul_sum] at h1
    have hd := Finset.add_sum_erase Finset.univ s.d (Finset.mem_univ i)
    have hl := Finset.add_sum_erase Finset.univ s.l (Finset.mem_univ i)
    unfold State.D State.L
    have e1 : ∑ j ∈ Finset.univ.erase i, s.d j = ∑ j, s.d j - s.d i := by linarith
    have e2 : ∑ j ∈ Finset.univ.erase i, s.l j = ∑ j, s.l j - s.l i := by linarith
    rw [e1, e2] at h1
    exact h1
  -- new totals
  have hDb : s.D + b ≤ γb * s.Pf * (s.L + lp) := by nlinarith
  have hLS : s.L + lp ≤ s.S := by
    have := hI.h_le_H i; have := hI.J1; linarith
  have hL0 : 0 ≤ s.L + lp := by have := hI.L_nonneg; linarith
  have hfl := hI.valid.sched.floor hL0 (hLS.trans hI.valid.S_le)
  have hmono := hI.valid.sched.mono hL0 hLS hI.valid.S_le
  have h2 : γb * (s.Pf * (s.L + lp)) ≤ γb * s.R s.S :=
    mul_le_mul_of_nonneg_left (hfl.trans hmono) hγ0
  have := hI.J3
  nlinarith

/-- Every skim whose guard holds satisfies `w ≤ A`. -/
theorem skim_payable (hγ0 : 0 ≤ γb) (hγ1 : γb ≤ 1) {s : State n} (hI : Inv γb s)
    {w : ℝ} (hsur : w ≤ s.A + s.D - s.R s.S) : w ≤ s.A := by
  have hD := hI.D_le_R hγ0
  have hmono := hI.valid.sched.mono hI.L_nonneg hI.L_le_S hI.valid.S_le
  have hRS : 0 ≤ s.R s.S := by
    have := hI.valid.sched.floor hI.valid.S_nonneg hI.valid.S_le
    have : 0 ≤ s.Pf * s.S := mul_nonneg hI.valid.sched.pf_pos.le hI.valid.S_nonneg
    linarith
  have h1 : γb * s.R s.L ≤ γb * s.R s.S := mul_le_mul_of_nonneg_left hmono hγ0
  have h2 : γb * s.R s.S ≤ 1 * s.R s.S := mul_le_mul_of_nonneg_right hγ1 hRS
  linarith

/-! ### Theorem 1 (a): the invariant is inductive -/

/-- The empty state satisfies the invariant. -/
theorem inv_empty {R : ℝ → ℝ} {Pf C g : ℝ} (hs : Sched R Pf C) (hg : 0 < g) (hgb : g ≤ γb) :
    Inv γb ({ R := R, Pf := Pf, C := C, S := 0, A := 0, γ := g,
              h := fun _ => 0, l := fun _ => 0, d := fun _ => 0 } : State n) := by
  refine ⟨⟨hs, le_rfl, hs.cap_pos.le, le_rfl, hg, hgb, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals simp [State.H, State.L, State.D, hs.zero]

/-- Every operation whose guard holds preserves the invariant. -/
theorem step_preserves (hγ0 : 0 < γb) (hγ1 : γb ≤ 1) {s s' : State n}
    (hI : Inv γb s) (hstep : Step γb s s') : Inv γb s' := by
  have hV := hI.valid
  have hPf := hV.sched.pf_pos
  cases hstep with
  | buy u x c hx hcap hc =>
    have hRmono := hV.sched.mono hV.S_nonneg (by linarith : s.S ≤ s.S + x) hcap
    refine ⟨⟨hV.sched, ?_, hcap, ?_, hV.γ_pos, hV.γ_le, ?_, hV.l_nonneg, hV.d_nonneg⟩, ?_, hI.J2, ?_⟩
    · show 0 ≤ s.S + x; linarith [hV.S_nonneg]
    · show 0 ≤ s.A + c; linarith [hV.A_nonneg]
    · intro j; show 0 ≤ Function.update s.h u (s.h u + x) j
      by_cases hj : j = u
      · subst hj; simp; linarith [hV.h_nonneg j]
      · simp [hj]; exact hV.h_nonneg j
    · show ∑ j, Function.update s.h u (s.h u + x) j + s.L = s.S + x
      rw [sum_update]; have := hI.J1; unfold State.H at this; linarith
    · show s.R (s.S + x) ≤ s.A + c + s.D
      have := hI.J3; linarith
  | sell u x o hx hbal ho hret =>
    have hpay := sell_payable hγ0.le hγ1 hI hx hbal
    have hxS : x ≤ s.S - s.L := by
      have := hI.h_le_H u; have := hI.J1; linarith
    refine ⟨⟨hV.sched, ?_, ?_, ?_, hV.γ_pos, hV.γ_le, ?_, hV.l_nonneg, hV.d_nonneg⟩, ?_, hI.J2, ?_⟩
    · show 0 ≤ s.S - x; linarith [hI.L_nonneg]
    · show s.S - x ≤ s.C; linarith [hV.S_le]
    · show 0 ≤ s.A - o; linarith
    · intro j; show 0 ≤ Function.update s.h u (s.h u - x) j
      by_cases hj : j = u
      · subst hj; simp; linarith
      · simp [hj]; exact hV.h_nonneg j
    · show ∑ j, Function.update s.h u (s.h u - x) j + s.L = s.S - x
      rw [sum_update]; have := hI.J1; unfold State.H at this; linarith
    · show s.R (s.S - x) ≤ s.A - o + s.D
      have := hI.J3; linarith
  | borrow i lp b o hlp hbal hb hltv ho hob =>
    have hpay := borrow_payable hγ0.le hI hlp hbal hltv
    have hRS : 0 ≤ s.R s.S := by
      have := hV.sched.floor hV.S_nonneg hV.S_le
      have : 0 ≤ s.Pf * s.S := mul_nonneg hPf.le hV.S_nonneg
      linarith
    have hslack : 0 ≤ (1 - γb) * s.R s.S := mul_nonneg (by linarith) hRS
    refine ⟨⟨hV.sched, hV.S_nonneg, hV.S_le, ?_, hV.γ_pos, hV.γ_le, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · show 0 ≤ s.A - o; linarith
    · intro j; show 0 ≤ Function.update s.h i (s.h i - lp) j
      by_cases hj : j = i
      · subst hj; simp; linarith
      · simp [hj]; exact hV.h_nonneg j
    · intro j; show 0 ≤ Function.update s.l i (s.l i + lp) j
      by_cases hj : j = i
      · subst hj; simp; linarith [hV.l_nonneg j]
      · simp [hj]; exact hV.l_nonneg j
    · intro j; show 0 ≤ Function.update s.d i (s.d i + b) j
      by_cases hj : j = i
      · subst hj; simp; linarith [hV.d_nonneg j]
      · simp [hj]; exact hV.d_nonneg j
    · show ∑ j, Function.update s.h i (s.h i - lp) j + ∑ j, Function.update s.l i (s.l i + lp) j = s.S
      rw [sum_update, sum_update]
      have := hI.J1; unfold State.H State.L at this; linarith
    · intro j
      show Function.update s.d i (s.d i + b) j ≤ γb * s.Pf * Function.update s.l i (s.l i + lp) j
      by_cases hj : j = i
      · subst hj; simp
        have h1 : s.γ * (s.Pf * (s.l j + lp)) ≤ γb * (s.Pf * (s.l j + lp)) :=
          mul_le_mul_of_nonneg_right hV.γ_le (mul_nonneg hPf.le (by linarith [hV.l_nonneg j]))
        nlinarith
      · simp [hj]; exact hI.J2 j
    · show s.R s.S ≤ s.A - o + ∑ j, Function.update s.d i (s.d i + b) j
      rw [sum_update]
      have := hI.J3; unfold State.D at this; linarith
  | repayFull i hd =>
    refine ⟨⟨hV.sched, hV.S_nonneg, hV.S_le, ?_, hV.γ_pos, hV.γ_le, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · show 0 ≤ s.A + s.d i; linarith [hV.A_nonneg]
    · intro j; show 0 ≤ Function.update s.h i (s.h i + s.l i) j
      by_cases hj : j = i
      · subst hj; simp; linarith [hV.h_nonneg j, hV.l_nonneg j]
      · simp [hj]; exact hV.h_nonneg j
    · intro j; show 0 ≤ Function.update s.l i 0 j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]; exact hV.l_nonneg j
    · intro j; show 0 ≤ Function.update s.d i 0 j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]; exact hV.d_nonneg j
    · show ∑ j, Function.update s.h i (s.h i + s.l i) j + ∑ j, Function.update s.l i 0 j = s.S
      rw [sum_update, sum_update]
      have := hI.J1; unfold State.H State.L at this; linarith
    · intro j
      show Function.update s.d i 0 j ≤ γb * s.Pf * Function.update s.l i 0 j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]; exact hI.J2 j
    · show s.R s.S ≤ s.A + s.d i + ∑ j, Function.update s.d i 0 j
      rw [sum_update]
      have := hI.J3; unfold State.D at this; linarith
  | repayPart i r u hr hrd hu hrel =>
    have hdi : 0 < s.d i := by linarith
    have hJ2i := hI.J2 i
    have hli := hV.l_nonneg i
    -- u ≤ l i (since u * d ≤ l * r ≤ l * d)
    have hul : u ≤ s.l i := by
      by_contra hcon
      rw [not_le] at hcon
      have : s.l i * r ≤ s.l i * s.d i := mul_le_mul_of_nonneg_left hrd.le hli
      nlinarith
    refine ⟨⟨hV.sched, hV.S_nonneg, hV.S_le, ?_, hV.γ_pos, hV.γ_le, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · show 0 ≤ s.A + r; linarith [hV.A_nonneg]
    · intro j; show 0 ≤ Function.update s.h i (s.h i + u) j
      by_cases hj : j = i
      · subst hj; simp; linarith [hV.h_nonneg j]
      · simp [hj]; exact hV.h_nonneg j
    · intro j; show 0 ≤ Function.update s.l i (s.l i - u) j
      by_cases hj : j = i
      · subst hj; simp; linarith
      · simp [hj]; exact hV.l_nonneg j
    · intro j; show 0 ≤ Function.update s.d i (s.d i - r) j
      by_cases hj : j = i
      · subst hj; simp; linarith
      · simp [hj]; exact hV.d_nonneg j
    · show ∑ j, Function.update s.h i (s.h i + u) j + ∑ j, Function.update s.l i (s.l i - u) j = s.S
      rw [sum_update, sum_update]
      have := hI.J1; unfold State.H State.L at this; linarith
    · intro j
      show Function.update s.d i (s.d i - r) j ≤ γb * s.Pf * Function.update s.l i (s.l i - u) j
      by_cases hj : j = i
      · subst hj; simp
        -- (d - r) * d ≤ γb Pf (l - u) * d, then divide by d > 0
        have key : (s.d j - r) * s.d j ≤ γb * s.Pf * (s.l j - u) * s.d j := by
          have hgp : 0 ≤ γb * s.Pf := mul_nonneg hγ0.le hPf.le
          have h1 : γb * s.Pf * (u * s.d j) ≤ γb * s.Pf * (s.l j * r) :=
            mul_le_mul_of_nonneg_left hrel hgp
          have h2 : s.d j * (s.d j - r) ≤ γb * s.Pf * s.l j * (s.d j - r) :=
            mul_le_mul_of_nonneg_right hJ2i (by linarith)
          nlinarith
        have h3 := le_of_mul_le_mul_right key hdi
        linarith
      · simp [hj]; exact hI.J2 j
    · show s.R s.S ≤ s.A + r + ∑ j, Function.update s.d i (s.d i - r) j
      rw [sum_update]
      have := hI.J3; unfold State.D at this; linarith
  | setLTV g hg hgb =>
    exact ⟨⟨hV.sched, hV.S_nonneg, hV.S_le, hV.A_nonneg, hg, hgb, hV.h_nonneg, hV.l_nonneg,
      hV.d_nonneg⟩, hI.J1, hI.J2, hI.J3⟩
  | transfer u v x hx hbal huv =>
    refine ⟨⟨hV.sched, hV.S_nonneg, hV.S_le, hV.A_nonneg, hV.γ_pos, hV.γ_le, ?_, hV.l_nonneg,
      hV.d_nonneg⟩, ?_, hI.J2, hI.J3⟩
    · intro j
      show 0 ≤ Function.update (Function.update s.h u (s.h u - x)) v (s.h v + x) j
      by_cases hjv : j = v
      · subst hjv; simp; linarith [hV.h_nonneg j]
      · by_cases hju : j = u
        · subst hju; simp [hjv]; linarith
        · simp [hjv, hju]; exact hV.h_nonneg j
    · show ∑ j, Function.update (Function.update s.h u (s.h u - x)) v (s.h v + x) j + s.L = s.S
      rw [sum_update, sum_update]
      have h1 : Function.update s.h u (s.h u - x) v = s.h v := by simp [huv]
      rw [h1]
      have := hI.J1; unfold State.H at this; linarith
  | reshape R' Pf' C' c hs hcap hc G1 G2 =>
    refine ⟨⟨hs, hV.S_nonneg, hcap, ?_, hV.γ_pos, hV.γ_le, hV.h_nonneg, hV.l_nonneg,
      hV.d_nonneg⟩, hI.J1, ?_, ?_⟩
    · show 0 ≤ s.A + c; linarith [hV.A_nonneg]
    · intro j
      show s.d j ≤ γb * Pf' * s.l j
      have h1 := hI.J2 j
      have h2 : γb * s.Pf * s.l j ≤ γb * Pf' * s.l j :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left G1 hγ0.le) (hV.l_nonneg j)
      linarith
    · show R' s.S ≤ s.A + c + s.D; exact G2
  | skim w hw hsur =>
    have hpay := skim_payable hγ0.le hγ1 hI hsur
    refine ⟨⟨hV.sched, hV.S_nonneg, hV.S_le, ?_, hV.γ_pos, hV.γ_le, hV.h_nonneg, hV.l_nonneg,
      hV.d_nonneg⟩, hI.J1, hI.J2, ?_⟩
    · show 0 ≤ s.A - w; linarith
    · show s.R s.S ≤ s.A - w + s.D; linarith
  | accrue i δ hδ hcap =>
    refine ⟨⟨hV.sched, hV.S_nonneg, hV.S_le, hV.A_nonneg, hV.γ_pos, hV.γ_le, hV.h_nonneg,
      hV.l_nonneg, ?_⟩, hI.J1, ?_, ?_⟩
    · intro j; show 0 ≤ Function.update s.d i (s.d i + δ) j
      by_cases hj : j = i
      · subst hj; simp; linarith [hV.d_nonneg j]
      · simp [hj]; exact hV.d_nonneg j
    · intro j
      show Function.update s.d i (s.d i + δ) j ≤ γb * s.Pf * s.l j
      by_cases hj : j = i
      · subst hj; simp; exact hcap
      · simp [hj]; exact hI.J2 j
    · show s.R s.S ≤ s.A + ∑ j, Function.update s.d i (s.d i + δ) j
      rw [sum_update]
      have := hI.J3; unfold State.D at this; linarith

/-- States reachable from a state by finitely many operations. -/
inductive Reach (γb : ℝ) (s₀ : State n) : State n → Prop
  | refl : Reach γb s₀ s₀
  | step {s s' : State n} : Reach γb s₀ s → Step γb s s' → Reach γb s₀ s'

/-- Theorem 1: every state reachable from a `J`-state is a `J`-state. -/
theorem reach_inv (hγ0 : 0 < γb) (hγ1 : γb ≤ 1) {s₀ s : State n}
    (h₀ : Inv γb s₀) (hr : Reach γb s₀ s) : Inv γb s := by
  induction hr with
  | refl => exact h₀
  | step _ hstep ih => exact step_preserves hγ0 hγ1 ih hstep

/-- Corollary: on every reachable path, every sale by a holder of free tokens
can be paid its full curve return, without any repayment being assumed. -/
theorem reach_sell_payable (hγ0 : 0 < γb) (hγ1 : γb ≤ 1) {s₀ s : State n}
    (h₀ : Inv γb s₀) (hr : Reach γb s₀ s) {u : Fin n} {x : ℝ}
    (hx : 0 < x) (hbal : x ≤ s.h u) : s.R s.S - s.R (s.S - x) ≤ s.A :=
  sell_payable hγ0.le hγ1 (reach_inv hγ0 hγ1 h₀ hr) hx hbal

/-! ### Reserve functions of price schedules satisfy `Sched` -/

/-- If `p` is non-decreasing on `[0, C]` and at least `Pf` there, the reserve
function `R x = ∫₀ˣ p` satisfies `Sched`. This connects the abstract hypothesis
of the safety theorem with Definition 1 of the paper. -/
theorem sched_of_integral (p : ℝ → ℝ) (Pf C : ℝ) (hPf : 0 < Pf) (hC : 0 < C)
    (hmono : MonotoneOn p (Set.Icc 0 C)) (hfloor : ∀ x ∈ Set.Icc (0 : ℝ) C, Pf ≤ p x) :
    Sched (fun x => ∫ t in (0 : ℝ)..x, p t) Pf C := by
  have hint : ∀ u v, 0 ≤ u → u ≤ v → v ≤ C →
      IntervalIntegrable p MeasureTheory.volume u v := by
    intro u v hu huv hv
    apply MonotoneOn.intervalIntegrable
    rw [Set.uIcc_of_le huv]
    exact hmono.mono (Set.Icc_subset_Icc hu hv)
  refine ⟨hPf, hC, by simp, ?_⟩
  intro a b ha hab hb
  have hsplit : (∫ t in (0 : ℝ)..b, p t) - ∫ t in (0 : ℝ)..a, p t = ∫ t in a..b, p t :=
    intervalIntegral.integral_interval_sub_left
      (hint 0 b le_rfl (ha.trans hab) hb) (hint 0 a le_rfl ha (hab.trans hb))
  show Pf * (b - a) ≤ (∫ t in (0 : ℝ)..b, p t) - ∫ t in (0 : ℝ)..a, p t
  rw [hsplit]
  have hconst : ∫ _t in a..b, Pf = Pf * (b - a) := by
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  rw [← hconst]
  apply intervalIntegral.integral_mono_on hab intervalIntegrable_const (hint a b ha hab hb)
  intro x hx
  exact hfloor x ⟨ha.trans hx.1, hx.2.trans hb⟩

end FloorCredit
