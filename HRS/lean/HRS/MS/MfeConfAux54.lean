import HRS.MS.MfeConfAux53

/-!
# S.B.1, packet F6 (part 16): the initial Jensen bound for a non-confining reference

`sb1_init_jensen`: `∫ (u log u + u U/θ) ≤ (klDiv μ (q dx)).toReal + e(v)`, `u = G_v * μ`, `q = exp(-U/θ)` (mass one),
`∇U = -b₀` with `b₀` Lipschitz and `U` bounded below, `μ` a probability law with finite second moment and finite relative
entropy (transplant of `p4_initial_jensen_proof`, replacing the Gaussian majorant of the reference by the density bridge
`sb1_klDiv_density`).
-/

open MeasureTheory Filter Topology InformationTheory
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

theorem sb1_init_jensen {θ : ℝ} (hθ : 0 < θ) {U : EucConfig d N → ℝ} {b0 : EucConfig d N → EucConfig d N}
    {K : ℝ≥0} (hU : ∀ x, HasFDerivAt U (-(p4InnerL (b0 x))) x) (hb : LipschitzWith K b0) {C0 : ℝ}
    (hC0 : ∀ x, 0 ≤ U x + C0) (hZ : ∫⁻ x, ENNReal.ofReal (Real.exp (-θ⁻¹ * U x)) = 1)
    {μ : Measure (EucConfig d N)} [IsProbabilityMeasure μ] (hm : Integrable p4m_q μ)
    (hfin : klDiv μ (sb1Dm (fun x => Real.exp (-θ⁻¹ * U x))) ≠ ⊤) :
    ∃ e : ℝ → ℝ, Tendsto e (𝓝[>] 0) (𝓝 0) ∧ ∀ v : ℝ, 0 < v →
      ∫ x, (p4Mol v μ x * Real.log (p4Mol v μ x) + p4Mol v μ x * U x / θ) ≤
        (klDiv μ (sb1Dm (fun x => Real.exp (-θ⁻¹ * U x)))).toReal + e v := by
  have hUc : Continuous U := continuous_iff_continuousAt.2 fun x => (hU x).continuousAt
  set q : EucConfig d N → ℝ := fun x => Real.exp (-θ⁻¹ * U x) with hqdef
  have hqm : Measurable q := Real.measurable_exp.comp (hUc.measurable.const_mul _)
  have hq0 : ∀ x, 0 < q x := fun x => Real.exp_pos _
  have hlogq : ∀ x, Real.log (q x) = -θ⁻¹ * U x := fun x => Real.log_exp _
  have hQ : IsProbabilityMeasure (sb1Dm q) := sb1Dm_prob hZ
  have hΦμ : Integrable (p4j_Phi : EucConfig d N → ℝ) μ := hm
  obtain ⟨hμQ, hint⟩ := klDiv_ne_top_iff.1 hfin
  have hμvol : μ ≪ (volume : Measure (EucConfig d N)) := hμQ.trans (withDensity_absolutelyContinuous _ _)
  -- the density of `μ`
  set ρ : EucConfig d N → ℝ := fun x => (μ.rnDeriv volume x).toReal with hρdef
  have hρm : Measurable ρ := (Measure.measurable_rnDeriv μ volume).ennreal_toReal
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => ENNReal.toReal_nonneg
  have hμeq : μ = sb1Dm ρ := by
    unfold sb1Dm
    have h1 : ∀ᵐ x ∂(volume : Measure (EucConfig d N)), ENNReal.ofReal (ρ x) = μ.rnDeriv volume x := by
      filter_upwards [Measure.rnDeriv_lt_top μ volume] with x hx
      exact ENNReal.ofReal_toReal hx.ne
    rw [withDensity_congr_ae h1, Measure.withDensity_rnDeriv_eq μ volume hμvol]
  have hρ1 : ∫⁻ x, ENNReal.ofReal (ρ x) = 1 := by
    have h := measure_univ (μ := μ)
    rw [hμeq] at h
    unfold sb1Dm at h
    rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  have hρi : Integrable ρ := p4j_integrable_of_lintegral hρm hρ0 hρ1
  -- integrability of the entropy density
  have hllr := sb1_llr_density hρm hρ0 hqm hq0 hQ
  have hLq : Integrable (fun x => Real.log (ρ x) - Real.log (q x)) (sb1Dm ρ) := by
    rw [← hμeq] at hllr ⊢
    exact hint.congr (by filter_upwards [hllr] with x hx using hx)
  have hΦρ : Integrable (fun x => ρ x * (Real.log (ρ x) - Real.log (q x))) :=
    (p4j_integrable_dMeas_iff hρm hρ0 _).1 hLq
  obtain ⟨Cq, hCq0, hq'⟩ := sb1_quad_growth hU hb
  obtain ⟨κ, hκ, hsym⟩ := sb1_symm_bound hU hb
  have hUμ : Integrable U μ :=
    Integrable.mono' (((integrable_const (1 : ℝ)).add hΦμ).const_mul Cq) hUc.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hq' x)
  have hρU : Integrable (fun x => ρ x * U x) := by
    have h' : Integrable U (sb1Dm ρ) := by rw [← hμeq]; exact hUμ
    exact (p4j_integrable_dMeas_iff hρm hρ0 U).1 h'
  have hL : Integrable (fun y => ρ y * Real.log (ρ y)) := by
    refine (hΦρ.sub (hρU.const_mul θ⁻¹)).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.sub_apply, hlogq]; ring
  have hKLval : (klDiv μ (sb1Dm q)).toReal = (∫ x, ρ x * Real.log (ρ x)) + θ⁻¹ * ∫ x, ρ x * U x := by
    have h := (sb1_klDiv_density hρm hρ0 hρ1 hqm hq0 hZ hΦρ).2
    rw [← hμeq] at h
    rw [h]
    have e : ∀ x, ρ x * (Real.log (ρ x) - Real.log (q x)) = ρ x * Real.log (ρ x) + θ⁻¹ * (ρ x * U x) := by
      intro x; rw [hlogq]; ring
    simp_rw [e]
    rw [integral_add hL (hρU.const_mul θ⁻¹), integral_const_mul]
  have hVint : ∫ y, U y ∂μ = ∫ x, ρ x * U x := by
    rw [hμeq]; exact p4j_integral_dMeas hρm hρ0 U
  refine ⟨fun v => θ⁻¹ * κ * (v * p4j_m d N 1), ?_, fun v hv => ?_⟩
  · have hc : Continuous fun v : ℝ => θ⁻¹ * κ * (v * p4j_m d N 1) := by fun_prop
    have h0 : θ⁻¹ * κ * ((0 : ℝ) * p4j_m d N 1) = 0 := by simp
    have := hc.tendsto 0
    rw [h0] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  · have hu : p4Mol v μ = p4j_conv v ρ := by
      funext x
      rw [hμeq]; exact p4j_mol_eq hv hρm hρ0 x
    have hpos : ∀ x, 0 < p4j_conv v ρ x := fun x => hu ▸ p4j_mol_pos hv μ hΦμ x
    have hIlog : Integrable (fun x => p4j_conv v ρ x * Real.log (p4j_conv v ρ x)) := by
      rw [← hu]; exact p4j_mol_log_integrable hv μ hΦμ
    have hJ := p4j_entropy_term_le hv hρ0 hρi hL hpos hIlog
    obtain ⟨hPI, hPle⟩ := p4j_pot_real hv hUc hC0 hκ hsym hq' μ hUμ hΦμ
    have hPI' : Integrable (fun x => p4Mol v μ x * U x / θ) := hPI.div_const θ
    have hIlog' : Integrable (fun x => p4Mol v μ x * Real.log (p4Mol v μ x)) := by
      rw [hu]; exact hIlog
    have hfree : ∫ x, (p4Mol v μ x * Real.log (p4Mol v μ x) + p4Mol v μ x * U x / θ) =
        (∫ x, p4Mol v μ x * Real.log (p4Mol v μ x)) + (∫ x, p4Mol v μ x * U x) / θ := by
      rw [integral_add hIlog' hPI', integral_div]
    have hJ' : ∫ x, p4Mol v μ x * Real.log (p4Mol v μ x) ≤ ∫ y, ρ y * Real.log (ρ y) := by
      rw [hu]; exact hJ
    have hm1 : p4j_m d N v = v * p4j_m d N 1 := p4j_m_scaling hv
    rw [hfree, hKLval]
    rw [hVint, hm1] at hPle
    have : (∫ x, p4Mol v μ x * U x) / θ ≤ θ⁻¹ * ((∫ x, ρ x * U x) + κ * (v * p4j_m d N 1)) := by
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left hPle (inv_pos.2 hθ).le
    have e : θ⁻¹ * ((∫ x, ρ x * U x) + κ * (v * p4j_m d N 1)) =
        θ⁻¹ * (∫ x, ρ x * U x) + θ⁻¹ * κ * (v * p4j_m d N 1) := by ring
    linarith

end HRS.MS.MfeConf
