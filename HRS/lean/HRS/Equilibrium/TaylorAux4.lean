/-
# HRS.Equilibrium.TaylorAux4 — `L^p` bookkeeping for extended nonnegative functions
(Lemma 4.7, packet TAYLOR)

Minkowski for finite sums, a Jensen-type inequality `(∫ F G)^p ≤ (∫ F)^{p-1} ∫ F G^p`, and the
transfer wrapper that turns the bound of Lemma 4.4 (stated for real measurable functions) into a
bound `∫ B² dP ≤ (C₀ N^ε b)²` for an extended nonnegative `B` with `∫ B^{2q} dμ^{⊗n} ≤ b^{2q}`.
-/
import HRS.Equilibrium.PoleCavity
import HRS.Equilibrium.TaylorAux3

open MeasureTheory
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.TaylorAux

section Lp

variable {α : Type*} [MeasurableSpace α]

/-- The `L^p` seminorm of an extended nonnegative function. -/
def taylorLp (P : Measure α) (p : ℝ) (F : α → ℝ≥0∞) : ℝ≥0∞ := (∫⁻ a, F a ^ p ∂P) ^ (1 / p)

theorem taylorLp_add {P : Measure α} {p : ℝ} (hp : 1 ≤ p) {F G : α → ℝ≥0∞}
    (hF : AEMeasurable F P) (hG : AEMeasurable G P) :
    taylorLp P p (fun a => F a + G a) ≤ taylorLp P p F + taylorLp P p G :=
  ENNReal.lintegral_Lp_add_le hF hG hp

theorem taylorLp_sum {ι : Type*} {P : Measure α} {p : ℝ} (hp : 1 ≤ p) (J : Finset ι)
    {F : ι → α → ℝ≥0∞} (hF : ∀ j, Measurable (F j)) :
    taylorLp P p (fun a => ∑ j ∈ J, F j a) ≤ ∑ j ∈ J, taylorLp P p (F j) := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, taylorLp]
    have hp0 : 0 < p := by linarith
    simp [ENNReal.zero_rpow_of_pos hp0, hp0]
  | insert a J ha ih =>
    simp only [Finset.sum_insert ha]
    refine (taylorLp_add hp (hF a).aemeasurable
      (Finset.measurable_sum _ fun j _ => hF j).aemeasurable).trans ?_
    gcongr

theorem taylorLp_mono {P : Measure α} {p : ℝ} (hp : 0 ≤ p) {F G : α → ℝ≥0∞}
    (h : ∀ a, F a ≤ G a) : taylorLp P p F ≤ taylorLp P p G := by
  unfold taylorLp
  exact ENNReal.rpow_le_rpow (lintegral_mono fun a => ENNReal.rpow_le_rpow (h a) hp)
    (one_div_nonneg.2 hp)

theorem taylorLp_const_mul {P : Measure α} {p : ℝ} (hp : 0 < p) (c : ℝ≥0∞) {F : α → ℝ≥0∞}
    (hF : Measurable F) :
    taylorLp P p (fun a => c * F a) = c * taylorLp P p F := by
  unfold taylorLp
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  rw [lintegral_const_mul _ (hF.pow_const p), ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one]

theorem taylorLp_const {P : Measure α} [IsProbabilityMeasure P] {p : ℝ} (hp : 0 < p) (c : ℝ≥0∞) :
    taylorLp P p (fun _ => c) = c := by
  unfold taylorLp
  rw [lintegral_const, measure_univ, mul_one, ← ENNReal.rpow_mul, mul_one_div_cancel hp.ne',
    ENNReal.rpow_one]

theorem taylorLp_rpow {P : Measure α} {p : ℝ} (hp : 0 < p) (F : α → ℝ≥0∞) :
    (taylorLp P p F) ^ p = ∫⁻ a, F a ^ p ∂P := by
  unfold taylorLp
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]

theorem taylorLp_le_of_lintegral_le {P : Measure α} {p : ℝ} (hp : 0 < p) (F : α → ℝ≥0∞)
    {b : ℝ≥0∞} (h : ∫⁻ a, F a ^ p ∂P ≤ b ^ p) : taylorLp P p F ≤ b := by
  by_contra hlt
  push Not at hlt
  have := ENNReal.rpow_lt_rpow hlt hp
  rw [taylorLp_rpow hp] at this
  exact absurd h (not_le.2 this)

/-- A Jensen-type inequality: `(∫ F G)^p ≤ (∫ F)^{p-1} ∫ F G^p`. -/
theorem taylor_jensen {ν : Measure α} {F G : α → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G)
    (p : ℕ) (hp : 2 ≤ p) :
    (∫⁻ a, F a * G a ∂ν) ^ p ≤ (∫⁻ a, F a ∂ν) ^ (p - 1) * ∫⁻ a, F a * G a ^ p ∂ν := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  set qr : ℝ := (p : ℝ).conjExponent with hqr
  have hc : (p : ℝ).HolderConjugate qr := Real.HolderConjugate.conjExponent hpR
  have hq0 : 0 < qr := hc.symm.pos
  have hsum : 1 / (p : ℝ) + 1 / qr = 1 := by
    have := hc.inv_add_inv_eq_one; simpa [one_div] using this
  set f : α → ℝ≥0∞ := fun a => F a ^ (1 / (p : ℝ)) * G a with hf
  set g : α → ℝ≥0∞ := fun a => F a ^ (1 / qr) with hg
  have hfm : Measurable f := (hF.pow_const _).mul hG
  have hgm : Measurable g := hF.pow_const _
  have hfg : ∀ a, F a * G a = f a * g a := by
    intro a
    simp only [hf, hg]
    calc F a * G a = F a ^ (1 : ℝ) * G a := by rw [ENNReal.rpow_one]
      _ = F a ^ (1 / (p : ℝ) + 1 / qr) * G a := by rw [hsum]
      _ = _ := by
        rw [ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity)]; ring
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hc hfm.aemeasurable hgm.aemeasurable
  have h1 : ∫⁻ a, f a ^ (p : ℝ) ∂ν = ∫⁻ a, F a * G a ^ p ∂ν := by
    refine lintegral_congr fun a => ?_
    simp only [hf]
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne',
      ENNReal.rpow_one, ENNReal.rpow_natCast]
  have h2 : ∫⁻ a, g a ^ qr ∂ν = ∫⁻ a, F a ∂ν := by
    refine lintegral_congr fun a => ?_
    simp only [hg]
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one]
  have hlhs : ∫⁻ a, F a * G a ∂ν = ∫⁻ a, (f * g) a ∂ν := lintegral_congr hfg
  rw [hlhs]
  refine (pow_le_pow_left' hH p).trans ?_
  rw [h1, h2, mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (_ ^ (1 / qr)),
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  have e1 : (1 / (p : ℝ)) * p = 1 := by field_simp
  have e2 : (1 / qr) * p = ((p - 1 : ℕ) : ℝ) := by
    have : 1 / qr = 1 - 1 / (p : ℝ) := by linarith
    rw [this, sub_mul, e1]
    rw [Nat.cast_sub (by omega)]; simp
  rw [e1, e2, ENNReal.rpow_one, ENNReal.rpow_natCast, mul_comm]

theorem taylor_iSup_min (x : ℝ≥0∞) : ⨆ k : ℕ, (min x (k : ℝ≥0∞)) ^ 2 = x ^ 2 := by
  refine le_antisymm (iSup_le fun k => pow_le_pow_left' (min_le_left _ _) 2) ?_
  by_cases hx : x = ⊤
  · subst hx
    rw [ENNReal.top_pow (by norm_num : 2 ≠ 0)]
    refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    obtain ⟨k, hk⟩ := exists_nat_ge (r : ℝ)
    refine le_iSup_of_le k ?_
    rw [min_eq_right le_top]
    have h1 : (r : ℝ≥0∞) ≤ k := by exact_mod_cast (by exact_mod_cast hk : (r : ℝ) ≤ k)
    exact h1.trans (by
      calc (k : ℝ≥0∞) ≤ (k : ℝ≥0∞) ^ 2 := by
            rcases Nat.eq_zero_or_pos k with h | h
            · simp [h]
            · exact_mod_cast (by nlinarith : k ≤ k ^ 2))
  · obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt hx
    refine le_iSup_of_le k ?_
    rw [min_eq_left hk.le]

theorem taylor_eLpNorm_eq (P : Measure α) (B : α → ℝ≥0∞) (hB : Measurable B)
    (hfin : ∀ a, B a ≠ ∞) (p : ℝ≥0∞) (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    eLpNorm (fun a => (B a).toReal) p P = taylorLp P p.toReal B := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop (f := fun a => (B a).toReal)
    (ENNReal.measurable_toReal.comp hB).aestronglyMeasurable]
  unfold taylorLp
  have key : ∀ a, ‖(B a).toReal‖ₑ = B a := fun a => by
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hfin a)]
  simp only [key]

/-- Transfer wrapper: a bound `‖Y‖_{L²(P)} ≤ K ‖Y‖_{L^{2q}(Pi)}` for real measurable `Y` gives
`∫ B² dP ≤ (K b)²` for any extended nonnegative measurable `B` with `∫ B^{2q} dPi ≤ b^{2q}`. -/
theorem taylor_transfer_wrap (P Pi : Measure α) (q : ℕ) (hq : 1 ≤ q) (K : ℝ≥0∞)
    (hT : ∀ Y : α → ℝ, Measurable Y →
      eLpNorm Y 2 P ≤ K * eLpNorm Y ((2 * q : ℕ) : ℝ≥0∞) Pi)
    (B : α → ℝ≥0∞) (hB : Measurable B) (b : ℝ≥0∞)
    (hb : ∫⁻ a, B a ^ (2 * q) ∂Pi ≤ b ^ (2 * q)) :
    ∫⁻ a, B a ^ 2 ∂P ≤ (K * b) ^ 2 := by
  have hq0 : (0 : ℝ) < ((2 * q : ℕ) : ℝ) := by
    have : 1 ≤ 2 * q := by omega
    exact_mod_cast (by omega : 0 < 2 * q)
  have hk : ∀ k : ℕ, ∫⁻ a, (min (B a) (k : ℝ≥0∞)) ^ 2 ∂P ≤ (K * b) ^ 2 := by
    intro k
    set Bk : α → ℝ≥0∞ := fun a => min (B a) (k : ℝ≥0∞) with hBk
    have hBkm : Measurable Bk := hB.min measurable_const
    have hBkfin : ∀ a, Bk a ≠ ∞ := fun a =>
      ne_top_of_le_ne_top (ENNReal.natCast_ne_top k) (min_le_right _ _)
    set R : α → ℝ := fun a => (Bk a).toReal with hR
    have hRm : Measurable R := ENNReal.measurable_toReal.comp hBkm
    have n1 : eLpNorm R ((2 * q : ℕ) : ℝ≥0∞) Pi = taylorLp Pi ((2 * q : ℕ) : ℝ) Bk := by
      have := taylor_eLpNorm_eq Pi Bk hBkm hBkfin ((2 * q : ℕ) : ℝ≥0∞)
        (by exact_mod_cast (by omega : 2 * q ≠ 0)) (ENNReal.natCast_ne_top _)
      rwa [ENNReal.toReal_natCast] at this
    have n1' : taylorLp Pi ((2 * q : ℕ) : ℝ) Bk ≤ b := by
      refine taylorLp_le_of_lintegral_le hq0 Bk ?_
      simp_rw [ENNReal.rpow_natCast]
      exact (lintegral_mono fun a => pow_le_pow_left' (min_le_left _ _) _).trans hb
    have n2 : eLpNorm R 2 P = taylorLp P 2 Bk := by
      have := taylor_eLpNorm_eq P Bk hBkm hBkfin 2 (by norm_num) (by norm_num)
      simpa using this
    have h3 : eLpNorm R 2 P ≤ K * b := by
      refine (hT R hRm).trans ?_
      rw [n1]
      exact mul_le_mul' le_rfl n1'
    have h4 : (taylorLp P 2 Bk) ^ (2 : ℝ) = ∫⁻ a, Bk a ^ (2 : ℝ) ∂P := taylorLp_rpow (by norm_num) Bk
    simp only [ENNReal.rpow_two] at h4
    rw [← n2] at h4
    show ∫⁻ a, Bk a ^ 2 ∂P ≤ _
    rw [← h4]
    exact pow_le_pow_left' h3 2
  have hmeas : ∀ k : ℕ, Measurable fun a => (min (B a) (k : ℝ≥0∞)) ^ 2 := fun k =>
    (hB.min measurable_const).pow_const 2
  have hmono : Monotone fun k : ℕ => fun a => (min (B a) (k : ℝ≥0∞)) ^ 2 := by
    intro k k' hkk' a
    exact pow_le_pow_left' (min_le_min le_rfl (by exact_mod_cast hkk')) 2
  calc ∫⁻ a, B a ^ 2 ∂P = ∫⁻ a, ⨆ k : ℕ, (min (B a) (k : ℝ≥0∞)) ^ 2 ∂P :=
        lintegral_congr fun a => (taylor_iSup_min (B a)).symm
    _ = ⨆ k : ℕ, ∫⁻ a, (min (B a) (k : ℝ≥0∞)) ^ 2 ∂P := lintegral_iSup hmeas hmono
    _ ≤ _ := iSup_le hk

end Lp

end HRS.TaylorAux
