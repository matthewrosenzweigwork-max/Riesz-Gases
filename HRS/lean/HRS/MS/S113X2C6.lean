import HRS.MS.S113X2C5

/-!
# S11.3 X2 wiring (worker S11W), C6: the integrated power chain inequality for the killed density, in configuration coordinates

* `s113c_Gp_integrable`: for absolutely continuous `p > 1`, the right-hand side density `s113b_Gp` of part B is interval integrable
  (measurability and boundedness of the two `x`-integrals from `s113b_fam`, integrability of `p'`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory intervalIntegral
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2C

open HRS HRS.Whole HRS.MS.S113X2 HRS.MS.S113X2B
open HRS.MC.CepP3 (Jc Jc_single fderiv2_comp_clm)

theorem s113c_Gp_integrable {n : ℕ} {ν : ℝ} {b : s113b_E n → s113b_E n} {q : ℝ → s113b_E n → ℝ} {T : ℝ}
    {u : ℝ → s113b_E n → ℝ} {K G : Set (s113b_E n)} {B : ℝ} (hD : s113b_Data ν b q T u K G B)
    (hT : 0 ≤ T) {p : ℝ → ℝ} (hp : AbsolutelyContinuousOnInterval p 0 T) (hp1 : ∀ t ∈ Icc 0 T, 1 < p t) :
    IntervalIntegrable (s113b_Gp ν b q u p) volume 0 T := by
  have hpc : ContinuousOn p (Icc 0 T) := by simpa [uIcc_of_le hT] using hp.continuousOn
  obtain ⟨i2, hi2m, hi2⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hT) hpc
  have hpb : ∀ t ∈ Icc 0 T, p t ∈ Icc (1 : ℝ) (p i2) := fun t ht =>
    ⟨(hp1 t ht).le, isMaxOn_iff.1 hi2 t ht⟩
  obtain ⟨Z, hZ0, hr⟩ := s113b_ratio hD
  have hb1 : (1 : ℝ) ≤ p i2 := (hp1 i2 hi2m).le
  have hφ1 : Measurable (fun y : ℝ × ℝ => y.2 ^ y.1) := measurable_snd.pow measurable_fst
  have hφ2 : Measurable (fun y : ℝ × ℝ => y.2 ^ y.1 * Real.log y.2) :=
    hφ1.mul (Real.measurable_log.comp measurable_snd)
  have famN := s113b_fam hD (w := s113b_N ν b q) (s113b_N_contB9 ν hD.hb hD.hq) (φ := fun e z => z ^ e) hr hφ1
    (s113b_pow_props 1 (p i2) Z one_pos hZ0)
  have famC := s113b_fam hD (w := q) hD.hq.continuous (φ := fun e z => z ^ e * Real.log z) hr hφ2
    (s113b_log_props 1 (p i2) Z one_pos hZ0)
  obtain ⟨CA, hCA⟩ := famN.2.1
  obtain ⟨CC, hCC⟩ := famC.2.1
  set pe : ℝ → ℝ := fun τ => p (max 0 (min τ T)) with hpe
  have hpec : Continuous pe := by
    refine hpc.comp_continuous (continuous_const.max (continuous_id.min continuous_const)) fun τ => ?_
    exact ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  have hpeq : ∀ τ ∈ Ioc 0 T, pe τ = p τ := fun τ hτ => by
    simp only [hpe]
    rw [min_eq_left hτ.2, max_eq_right hτ.1.le]
  set A : ℝ → ℝ := fun τ => ∫ x, s113b_N ν b q τ x * (u τ x / q τ x) ^ (p τ) with hA
  set C : ℝ → ℝ := fun τ => ∫ x, q τ x * ((u τ x / q τ x) ^ (p τ) * Real.log (u τ x / q τ x)) with hC
  have hS : ∀ τ ∈ Ioc 0 T, τ ∈ Icc (0 : ℝ) T := fun τ hτ => ⟨hτ.1.le, hτ.2⟩
  have hae : ∀ {P : ℝ → Prop}, (∀ τ ∈ Ioc 0 T, P τ) → ∀ᵐ τ ∂(volume.restrict (Ioc 0 T)), P τ := fun h =>
    (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ h)
  have hAm : AEStronglyMeasurable A (volume.restrict (Ioc 0 T)) := by
    refine ((famN.2.2 pe hpec).restrict (s := Ioc 0 T)).congr (hae fun τ hτ => ?_)
    simp only [hA, hpeq τ hτ]
  have hCm : AEStronglyMeasurable C (volume.restrict (Ioc 0 T)) := by
    refine ((famC.2.2 pe hpec).restrict (s := Ioc 0 T)).congr (hae fun τ hτ => ?_)
    simp only [hC, hpeq τ hτ]
  have hAb : ∀ τ ∈ Ioc 0 T, ‖A τ‖ ≤ CA := fun τ hτ => by
    rw [Real.norm_eq_abs]; exact hCA τ (hS τ hτ) (p τ) (hpb τ (hS τ hτ))
  have hCb : ∀ τ ∈ Ioc 0 T, ‖C τ‖ ≤ CC := fun τ hτ => by
    rw [Real.norm_eq_abs]; exact hCC τ (hS τ hτ) (p τ) (hpb τ (hS τ hτ))
  have hpm : AEStronglyMeasurable p (volume.restrict (Ioc 0 T)) :=
    (hpc.mono (Ioc_subset_Icc_self)).aestronglyMeasurable measurableSet_Ioc
  have hpb' : ∀ τ ∈ Ioc 0 T, ‖p τ - 1‖ ≤ p i2 := fun τ hτ => by
    have := hpb τ (hS τ hτ)
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [this.1])]; linarith [this.2]
  have hI1 : Integrable (fun τ => (p τ - 1) * A τ) (volume.restrict (Ioc 0 T)) := by
    refine Integrable.of_bound ((hpm.sub aestronglyMeasurable_const).mul hAm) (p i2 * CA) (hae fun τ hτ => ?_)
    rw [norm_mul]
    exact mul_le_mul (hpb' τ hτ) (hAb τ hτ) (norm_nonneg _) (by linarith)
  have hd : Integrable (deriv p) (volume.restrict (Ioc 0 T)) := hp.intervalIntegrable_deriv.1
  have hI2 : Integrable (fun τ => C τ * deriv p τ) (volume.restrict (Ioc 0 T)) :=
    hd.bdd_mul hCm (hae hCb)
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 ?_
  have hint : Integrable (fun τ => (p τ - 1) * A τ + deriv p τ * C τ) (volume.restrict (Ioc 0 T)) := by
    refine hI1.add ?_
    simpa [mul_comm] using hI2
  refine hint.congr (hae fun τ hτ => ?_)
  rw [s113b_Gp_eq hD p (hS τ hτ)]

/-- The data of the moving reference in `ℝ^{Nd}` coordinates on a compact set `K` (the content of the core QREG for `K`):
an open set `G' ⊇ Jc⁻¹ K` and a `C²` space-time function `q̃`, positive on `[0,T]`, agreeing with
`movQDensity (ρ t) ∘ Jc` on `G'` for `t ∈ [0,T+1]`. -/
structure s113c_QReg (d N : ℕ) (s β : ℝ) (ρ : ℝ → Euc d → ℝ) (T : ℝ) (K : Set (EucConfig d N))
    (qt : ℝ → s113b_E (N * d) → ℝ) (G' : Set (s113b_E (N * d))) : Prop where
  isOpen : IsOpen G'
  subset : ∀ z, Jc d N z ∈ K → z ∈ G'
  smooth : ContDiff ℝ 2 (fun z : ℝ × s113b_E (N * d) => qt z.1 z.2)
  pos : ∀ t ∈ Icc (0 : ℝ) T, ∀ z, 0 < qt t z
  match_ : ∀ t ∈ Icc (0 : ℝ) (T + 1), ∀ z ∈ G', qt t z = movQDensity d s β N (ρ t) (Jc d N z)

/-- The power mass `∫ q_t (u_t/q_t)^{p(t)}` in configuration coordinates. -/
def s113c_Mc (d : ℕ) (s β : ℝ) (N : ℕ) (ρ : ℝ → Euc d → ℝ) (u : ℝ → EucConfig d N → ℝ) (p : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x, movQDensity d s β N (ρ t) x * (u t x / movQDensity d s β N (ρ t) x) ^ (p t)

open HRS.MS.S113BD (s113x_source) in
/-- The right-hand side density in configuration coordinates. -/
def s113c_Gc (d : ℕ) (s q β : ℝ) (N : ℕ) (ρ : ℝ → Euc d → ℝ) (u : ℝ → EucConfig d N → ℝ) (p : ℝ → ℝ) (τ : ℝ) : ℝ :=
  (p τ - 1) * (∫ x, movQDensity d s β N (ρ τ) x * s113x_source d s q β N ρ τ x *
      (u τ x / movQDensity d s β N (ρ τ) x) ^ (p τ)) +
    deriv p τ * ∫ x, movQDensity d s β N (ρ τ) x * (u τ x / movQDensity d s β N (ρ τ) x) ^ (p τ) *
      Real.log (u τ x / movQDensity d s β N (ρ τ) x)

end HRS.MS.S113X2C

end
