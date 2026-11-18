import HRS.MC.CepH2Aux30

/-!
# CEPH2, helper 31: the mollified dissipation inequality (statement of `cepH2_mollified_ineq`, narrow version)

Bridge from `H2Set.result2` (kernel variance `v = 2θε`, family clamped to `[0,T]`) to the vocabulary of the specification.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

theorem h2_gauss_eq (θ ε : ℝ) : (h2_gauss θ ε : Ch N → ℝ) = h2_g (2 * θ * ε) := by
  funext w
  unfold h2_gauss h2_g
  have e1 : 2 * Real.pi * (2 * θ * ε) = 4 * Real.pi * θ * ε := by ring
  have e2 : -(1 / (2 * (2 * θ * ε))) * ‖w‖ ^ 2 = -‖w‖ ^ 2 / (4 * θ * ε) := by
    by_cases h : θ * ε = 0
    · have : 4 * θ * ε = 0 := by linarith [show 4 * θ * ε = 4 * (θ * ε) by ring]
      have h2 : 2 * (2 * θ * ε) = 0 := by linarith [show 2 * (2 * θ * ε) = 4 * (θ * ε) by ring]
      rw [this, h2]; simp
    · have h1 : θ ≠ 0 := left_ne_zero_of_mul h
      have h2 : ε ≠ 0 := right_ne_zero_of_mul h
      field_simp
      ring
  rw [e1, e2]

theorem h2_kern_eq (θ ε : ℝ) : (h2_kern θ ε : Ch N → ℝ) = h2_per (2 * θ * ε) := by
  funext w
  unfold h2_kern h2_per
  rw [h2_gauss_eq]

theorem h2_mol_eq (θ ε : ℝ) (μ : Measure (Ch N)) : h2_mol θ ε μ = h2_mu (2 * θ * ε) μ := by
  funext x
  unfold h2_mol h2_mu
  rw [h2_kern_eq]

/-- Clamping of the time parameter to `[0,T]`. -/
def h2_clamp (T s : ℝ) : ℝ := max 0 (min s T)

theorem h2_clamp_mem {T : ℝ} (hT : 0 ≤ T) (s : ℝ) : h2_clamp T s ∈ Icc (0 : ℝ) T :=
  ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

theorem h2_clamp_of_mem {T s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) : h2_clamp T s = s := by
  unfold h2_clamp
  rw [min_eq_left hs.2, max_eq_right hs.1]

theorem h2_continuous_clamp (T : ℝ) : Continuous (h2_clamp T) :=
  continuous_const.max (continuous_id.min continuous_const)

/-- **C-ε (mollified dissipation inequality)**, with narrow continuity of the family on `[0,T]`. -/
theorem cepH2_mollified_ineq_narrow {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U)
    (hUper : ∀ z, U (z + cep_diag N) = U z) {K : ℝ≥0} (hK : LipschitzWith K (gradient U))
    {θ : ℝ} (hθ : 0 < θ) {μ : ℝ → Measure (Ch N)} [∀ t, IsProbabilityMeasure (μ t)]
    (hcell : ∀ t, 0 ≤ t → μ t (cep_cell N)ᶜ = 0) {T : ℝ} (hT : 0 ≤ T)
    (hmom : ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ t ∈ Icc (0 : ℝ) T, ∫⁻ z, ENNReal.ofReal (‖h2_perp z‖ ^ 2) ∂(μ t) ≤ M)
    (hnar : ∀ g : Ch N → ℝ, Continuous g → (∀ z, g (z + cep_diag N) = g z) → (∃ C : ℝ, ∀ z, |g z| ≤ C) →
      ContinuousOn (fun t => ∫ z, g z ∂(μ t)) (Icc (0 : ℝ) T))
    (hfp : H2WeakFP θ U μ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∀ t ∈ Icc (0 : ℝ) T,
      h2_free θ U (h2_mol θ ε (μ t)) + θ * (1 - δ) * ∫ r in Icc (0 : ℝ) t, h2_diss θ U (h2_mol θ ε (μ r))
        ≤ h2_free θ U (h2_mol θ ε (μ 0)) + t * (K ^ 2 * N * ε / (2 * δ)) := by
  intro t ht
  obtain ⟨M, hMtop, hM⟩ := hmom
  set μ' : ℝ → Measure (Ch N) := fun s => μ (h2_clamp T s) with hμ'
  have hmeas : Measurable fun z : Ch N => ‖h2_perp z‖ ^ 2 := (h2_continuous_perp.norm.pow 2).measurable
  have hint : ∀ s, Integrable (fun y => ‖h2_perp y‖ ^ 2) (μ' s) := fun s => by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => by positivity)]
    exact lt_of_le_of_lt (hM _ (h2_clamp_mem hT s)) hMtop
  have S : H2Set θ (2 * θ * ε) U K μ' T M.toReal :=
    { hθ := hθ
      hv := by positivity
      hU := hU
      hUper := hUper
      hK := hK
      hT := hT
      hprob := fun s => inferInstanceAs (IsProbabilityMeasure (μ (h2_clamp T s)))
      hcell := fun s => hcell _ (h2_clamp_mem hT s).1
      hmom := hint
      hM := fun s => by
        rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => by positivity) hmeas.aestronglyMeasurable]
        exact ENNReal.toReal_mono hMtop.ne (hM _ (h2_clamp_mem hT s))
      hnar := fun g hg hper hb => (hnar g hg hper hb).comp_continuous (h2_continuous_clamp T)
        (h2_clamp_mem hT)
      hfp := fun g hg s hs => by
        have h1 : ∀ r ∈ Icc (0 : ℝ) T, μ' r = μ r := fun r hr => by simp only [hμ', h2_clamp_of_mem hr]
        have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
        rw [h1 s hs, h1 0 h0]
        have := hfp g hg s hs.1
        rw [this]
        congr 1
        refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
        simp only [h1 r ⟨hr.1, hr.2.trans hs.2⟩] }
  have h := S.result2 hδ hδ1 ht
  have h1 : ∀ r ∈ Icc (0 : ℝ) T, μ' r = μ r := fun r hr => by simp only [hμ', h2_clamp_of_mem hr]
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  rw [h1 t ht, h1 0 h0] at h
  have hI : ∫ r in Icc (0 : ℝ) t, h2_diss θ U (h2_mu (2 * θ * ε) (μ' r)) =
      ∫ r in Icc (0 : ℝ) t, h2_diss θ U (h2_mu (2 * θ * ε) (μ r)) := by
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    simp only [h1 r ⟨hr.1, hr.2.trans ht.2⟩]
  rw [hI] at h
  have hc : (K : ℝ) ^ 2 * (N * (2 * θ * ε)) / (4 * θ * δ) = (K : ℝ) ^ 2 * N * ε / (2 * δ) := by
    field_simp
    ring
  rw [hc] at h
  simpa only [h2_mol_eq] using h

end HRS.MC.CepH2
