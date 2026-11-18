import HRS.MS.S111X2Aux18

/-!
# S11.1 X2, packet E06 consumption: sharp `L²_0` decay of classical solutions at rate `2λ/β`

`s111x2_sharp_decay`: for a classical adjoint solution `f` on `[0,H]` with terminal datum `φ` and a Poincaré constant
`λ` of `μ`, `‖P_μ f_{H-t}‖² ≤ η⁻¹ e^{-2 (λ/β) t} ‖P_μ φ‖²`, `η` the coercivity constant of the response form
(depending only on the model).  This is the exact response identity (E03) + Poincaré + `s111x2_sharp_energy` (E06).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X2

open HRS (Euc)
open HRS.Whole HRS.Whole.Q34

variable {d : ℕ}

/-- **Sharp decay.** -/
theorem s111x2_sharp_decay (hd : 2 ≤ d) (s a β lam Γ : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hβ : 0 < β) (hlam : 0 < lam) (hΓ : β ≤ Γ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ ρ : Euc d → ℝ, IsThermalEquilibrium d s a β ρ →
      (∀ θ ∈ Icc (0 : ℝ) Γ, ResponseForm (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) θ η) ∧
      (IsR2Poincare (HRS.Whole.withDensityReal ρ) lam →
      ∀ H : ℝ, 0 < H → ∀ (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ),
        IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) H φ f →
        ∀ t ∈ Icc 0 H, s111x2_centeredSquare (HRS.Whole.withDensityReal ρ) (f (H - t)) ≤
          η⁻¹ * Real.exp (-2 * (lam / β) * t) * s111x2_centeredSquare (HRS.Whole.withDensityReal ρ) φ) := by
  obtain ⟨η, hη0, hη1, hRF⟩ := s111x2_thermal_response_forms hd s a β Γ hs0 hs ha hβ (hβ.le.trans hΓ)
  refine ⟨η, hη0, hη1, fun ρ hρ => ⟨hRF ρ hρ, fun hP H hH φ f hf t ht => ?_⟩⟩
  have RF := hRF ρ hρ β ⟨hβ.le, hΓ⟩
  obtain ⟨hder, hcont⟩ := s111x2_classical_fd_deriv hd hs0 hs ha hβ hH hρ hf hf
  obtain ⟨M, T⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  haveI := isProbabilityMeasure_nu T.prob
  obtain ⟨B0, B1, B2, hB0, hB1, hB2, hfB⟩ := HRS.MS.S111X1.classical_bounds hf
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set E : ℝ → ℝ := fun r => HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) μ β (f r) (f r) with hE
  set D : ℝ → ℝ := fun r => s111x2_dirichlet μ (f r) (f r) with hD
  have hDb : ∀ r ∈ Icc (0 : ℝ) H, |D r| ≤ B1 * B1 := fun r hr =>
    s111x2_dirichlet_bound T (fun x => (hfB r hr x).2.1) (fun x => (hfB r hr x).2.1)
  have hrefl : ∀ r ∈ Icc (0 : ℝ) H, H - r ∈ Icc (0 : ℝ) H := fun r hr =>
    ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have hreflo : ∀ r ∈ Ioo (0 : ℝ) H, H - r ∈ Ioo (0 : ℝ) H := fun r hr =>
    ⟨by linarith [hr.2], by linarith [hr.1]⟩
  -- the forward-time energy
  set EF : ℝ → ℝ := fun r => E (H - r) with hEF
  have hcontF : ContinuousOn EF (Icc 0 H) :=
    hcont.comp (by fun_prop : ContinuousOn (fun r : ℝ => H - r) (Icc 0 H))
      (fun r hr => hrefl r hr)
  have hderF : ∀ r ∈ Ioo (0 : ℝ) H, HasDerivAt EF (-(2 * β⁻¹ * D (H - r))) r := by
    intro r hr
    have h1 : HasDerivAt (fun q : ℝ => H - q) (-1) r := by
      simpa using (hasDerivAt_id r).const_sub H
    have h2 := HasDerivAt.comp r (hder (H - r) (hreflo r hr)) h1
    have e : -(2 * β⁻¹ * D (H - r)) = 2 * β⁻¹ * D (H - r) * -1 := by ring
    rw [e]
    exact h2
  have hbdF : ∀ r ∈ Ioo (0 : ℝ) H, |-(2 * β⁻¹ * D (H - r))| ≤ 2 * β⁻¹ * (B1 * B1) := by
    intro r hr
    have hβ2 : 0 < 2 * β⁻¹ := by positivity
    rw [abs_neg, abs_mul, abs_of_pos hβ2]
    exact mul_le_mul_of_nonneg_left (hDb _ (hrefl r ⟨hr.1.le, hr.2.le⟩)) hβ2.le
  have hACF := s111x2_ac_of_deriv_bdd hH hcontF hderF hbdF
  -- Poincaré and coercivity
  have hmem : ∀ r ∈ Icc (0 : ℝ) H, MemLp (f r) 2 μ := fun r hr =>
    MemLp.of_bound (hf.c2 r hr).continuous.aestronglyMeasurable B0
      (Filter.Eventually.of_forall fun x => (hfB r hr x).1) |>.mono_exponent le_top
  have hVcs : ∀ r, 0 ≤ s111x2_centeredSquare μ (f r) := fun r =>
    integral_nonneg fun x => sq_nonneg _
  have hpoin : ∀ r ∈ Icc (0 : ℝ) H, lam * s111x2_centeredSquare μ (f r) ≤ D r := by
    intro r hr
    have := hP (f r) ((hf.c2 r hr).of_le (by norm_num)) ⟨B1, fun x => by
      rw [s111x2_norm_gradient]; exact (hfB r hr x).2.1⟩ (hmem r hr)
    have hv : ProbabilityTheory.variance (f r) μ = s111x2_centeredSquare μ (f r) := by
      rw [ProbabilityTheory.variance_eq_integral (hmem r hr).aemeasurable]
      rfl
    rw [hv] at this
    have hDe : D r = ∫ x, ‖gradient (f r) x‖ ^ 2 ∂μ := by
      simp only [hD, s111x2_dirichlet, real_inner_self_eq_norm_sq]
    rw [hDe]; exact this
  have key := s111x2_sharp_energy H β⁻¹ lam η hH.le (inv_pos.2 hβ) hlam hη0 EF
    (fun t => s111x2_centeredSquare μ (f (H - t))) (fun t => D (H - t)) hACF ?_ ?_ ?_ ?_ t ht
  · have hf0 : f H = φ := hf.terminal
    have := key.2
    simp only [sub_zero, hf0] at this
    have e : -2 * β⁻¹ * lam * t = -2 * (lam / β) * t := by field_simp
    rw [e] at this
    exact this
  · -- integrability of D(H - ·)
    have hae : ∀ᵐ t ∂(volume.restrict (Icc 0 H)), D (H - t) = -(2 * β⁻¹)⁻¹ * deriv EF t :=
      s111x2_ae_icc_of_ioo fun r hr => by
        rw [(hderF r hr).deriv]; field_simp
    have hmeas : AEStronglyMeasurable (fun t => D (H - t)) (volume.restrict (Icc 0 H)) := by
      have : AEStronglyMeasurable (fun t => -(2 * β⁻¹)⁻¹ * deriv EF t) (volume.restrict (Icc 0 H)) :=
        ((measurable_deriv EF).const_mul _).aestronglyMeasurable
      exact this.congr (hae.mono fun t ht => ht.symm)
    refine (integrableOn_const (C := B1 * B1) (by simp)).mono' hmeas ?_
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun t ht => by
      rw [Real.norm_eq_abs]; exact hDb _ (hrefl t ht)
  · intro t ht
    obtain ⟨c1, c2⟩ := RF.coercive (f (H - t)) (hmem _ (hrefl t ht))
    exact ⟨hVcs _, c1, c2⟩
  · rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun t ht => by
      have := hpoin _ (hrefl t ht)
      simpa using this
  · exact s111x2_ae_icc_of_ioo fun r hr => by
      have := hderF r hr
      convert this using 1
      ring

end HRS.MS.S111X2
