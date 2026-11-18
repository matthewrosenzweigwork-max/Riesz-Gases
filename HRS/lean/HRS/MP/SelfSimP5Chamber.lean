import HRS.MP.SelfSimP5Trunc
import HRS.MP.SelfSimP5Conv

/-!
# MPP5B (3): the solution in chamber coordinates, `ss5_chamber_reading`

`HRS.MP.SelfSimP5Impl.ss5_chamber_reading_proof` has the statement of `HRS.MP.SelfSimP5.ss5_chamber_reading`.
Parts: (a) the permuted noise is a Brownian filtration (reindexing of Gaussian increments);
(b) the second moment of `y₀` is finite: Gibbs variational inequality (pointwise Young inequality
`v ≤ log ρ + e^v/ρ` with `ρ = dμ/dν`) against `v = |ξ|²/(16 invβ)`, using `Ḡ ≤ C e^{-|ξ|²/(8 invβ)}`;
(c) deterministic core: a continuous weakly ordered path with null collision occupation and integrable drift components
has integrable inverse gaps (triangular induction from the lowest particle), is a.e. in the open chamber, and solves the
chamber equation with drift `-∇Φ - y/2`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open HRS HRS.MP.SelfSimP5 HRS.MP.SelfSim HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP5Impl

/-! ### (b) Finite second moment from finite entropy -/

/-- Young-type moment bound: `∫ v dμ ≤ ∫ log(dμ/dν) dμ + ∫ e^v dν` (lintegral form). -/
theorem ss5h_young_moment {α : Type*} [MeasurableSpace α] {μ ν : Measure α} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hμν : μ ≪ ν) (hint : Integrable (llr μ ν) μ) {v : α → ℝ}
    (hv : Measurable v) (hexp : ∫⁻ x, ENNReal.ofReal (Real.exp (v x)) ∂ν < ⊤) :
    ∫⁻ x, ENNReal.ofReal (v x) ∂μ < ⊤ := by
  have h1 : ∀ᵐ x ∂μ, ENNReal.ofReal (v x) ≤ ENNReal.ofReal (llr μ ν x) +
      ENNReal.ofReal (Real.exp (v x) / (μ.rnDeriv ν x).toReal) := by
    filter_upwards [Measure.rnDeriv_pos hμν, hμν.ae_le (Measure.rnDeriv_lt_top μ ν)] with x hpos hlt
    have hρ : 0 < (μ.rnDeriv ν x).toReal := ENNReal.toReal_pos hpos.ne' hlt.ne
    set ρ := (μ.rnDeriv ν x).toReal with hρdef
    have key : v x ≤ Real.log ρ + Real.exp (v x) / ρ := by
      have h := Real.add_one_le_exp (v x - Real.log ρ)
      rw [Real.exp_sub, Real.exp_log hρ] at h
      linarith
    calc ENNReal.ofReal (v x) ≤ ENNReal.ofReal (Real.log ρ + Real.exp (v x) / ρ) :=
          ENNReal.ofReal_le_ofReal key
      _ ≤ _ := ENNReal.ofReal_add_le
  have hmeasρ : Measurable fun x => Real.exp (v x) / (μ.rnDeriv ν x).toReal :=
    (Real.measurable_exp.comp hv).div (Measure.measurable_rnDeriv μ ν).ennreal_toReal
  calc ∫⁻ x, ENNReal.ofReal (v x) ∂μ
      ≤ ∫⁻ x, (ENNReal.ofReal (llr μ ν x) +
          ENNReal.ofReal (Real.exp (v x) / (μ.rnDeriv ν x).toReal)) ∂μ := lintegral_mono_ae h1
    _ = ∫⁻ x, ENNReal.ofReal (llr μ ν x) ∂μ +
          ∫⁻ x, ENNReal.ofReal (Real.exp (v x) / (μ.rnDeriv ν x).toReal) ∂μ :=
        lintegral_add_left (measurable_llr μ ν).ennreal_ofReal _
    _ < ⊤ := by
      refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
      · refine lt_of_le_of_lt (lintegral_mono fun x => Real.ofReal_le_enorm _) hint.hasFiniteIntegral
      · rw [← lintegral_rnDeriv_mul hμν hmeasρ.ennreal_ofReal.aemeasurable]
        refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hexp
        by_cases h0 : μ.rnDeriv ν x = 0
        · simp [h0]
        by_cases htop : μ.rnDeriv ν x = ⊤
        · simp [htop]
        have hρ : 0 < (μ.rnDeriv ν x).toReal := ENNReal.toReal_pos h0 htop
        rw [← ENNReal.ofReal_toReal htop, ← ENNReal.ofReal_mul hρ.le, ENNReal.ofReal_toReal htop,
          mul_div_cancel₀ _ hρ.ne']

/-- `V ξ = ∑ ‖ξ_i‖²`. -/
def ss5h_V {N : ℕ} (ξ : EucConfig 1 N) : ℝ := ∑ i, ‖ξ i‖ ^ 2

theorem ss5h_V_nonneg {N : ℕ} (ξ : EucConfig 1 N) : 0 ≤ ss5h_V ξ :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem ss5h_log_le {t : ℝ} (ht : 0 < t) : Real.log t ≤ t ^ 2 / 16 + 1 := by
  have h := Real.log_le_sub_one_of_pos (x := t ^ 2 / 8) (by positivity)
  rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at h
  have h8 : Real.log 8 < 3 := by
    have : (8 : ℝ) = 2 ^ 3 := by norm_num
    rw [this, Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast
    linarith
  push_cast at h
  linarith

theorem ss5h_sq_sub_le (a b : ℝ) : (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a + b)]

/-- The Gibbs weight is bounded by a Gaussian: `Ḡ(ξ) ≤ exp(θ⁻¹ (N/2 - V(ξ)/8))`. -/
theorem ss5h_weight_le {N : ℕ} (hN : 0 < N) {θ : ℝ} (hθ : 0 < θ) (ξ : EucConfig 1 N) :
    selfSimWeight 1 0 θ N 0 ξ ≤ Real.exp (θ⁻¹ * ((N : ℝ) / 2 - ss5h_V ξ / 8)) := by
  unfold selfSimWeight
  split_ifs with hc
  · exact (Real.exp_pos _).le
  · apply Real.exp_le_exp.2
    have hnc : ∀ i j : Fin N, i ≠ j → 0 < ‖ξ i - ξ j‖ := by
      intro i j hij
      apply norm_pos_iff.2
      intro h
      exact hc ⟨i, j, hij, sub_eq_zero.1 h⟩
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    -- the sum of logarithms
    have hlog : ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, Real.log ‖ξ i - ξ j‖ ≤
        (N : ℝ) ^ 2 + (N : ℝ) * ss5h_V ξ / 4 := by
      have h1 : ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, Real.log ‖ξ i - ξ j‖ ≤
          ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, (‖ξ i - ξ j‖ ^ 2 / 16 + 1) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj =>
          ss5h_log_le (hnc i j (Finset.ne_of_mem_erase hj).symm)
      have h2 : ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, (‖ξ i - ξ j‖ ^ 2 / 16 + 1) ≤
          ∑ i : Fin N, ∑ j : Fin N, ((2 * ‖ξ i‖ ^ 2 + 2 * ‖ξ j‖ ^ 2) / 16 + 1) := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine (Finset.sum_le_sum fun j _ => ?_).trans
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i _) (fun j _ _ => by positivity))
        have h3 : ‖ξ i - ξ j‖ ≤ ‖ξ i‖ + ‖ξ j‖ := norm_sub_le _ _
        have h4 : ‖ξ i - ξ j‖ ^ 2 ≤ 2 * ‖ξ i‖ ^ 2 + 2 * ‖ξ j‖ ^ 2 := by
          nlinarith [norm_nonneg (ξ i - ξ j), norm_nonneg (ξ i), norm_nonneg (ξ j), sq_nonneg (‖ξ i‖ - ‖ξ j‖)]
        linarith
      have h5 : ∑ i : Fin N, ∑ j : Fin N, ((2 * ‖ξ i‖ ^ 2 + 2 * ‖ξ j‖ ^ 2) / 16 + 1) =
          (N : ℝ) ^ 2 + (N : ℝ) * ss5h_V ξ / 4 := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ss5h_V, Finset.sum_comm (f := fun i j => ‖ξ j‖ ^ 2)]
        ring_nf
      linarith
    have hpot : selfSimPotential 1 0 N 0 ξ ≥ ss5h_V ξ / 8 - (N : ℝ) / 2 := by
      unfold selfSimPotential
      have ha : aSelfSim 0 0 = 1 := by simp [aSelfSim]
      rw [ha]
      have hr : ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, rieszKernel 1 0 (ξ i - ξ j) =
          -∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, Real.log ‖ξ i - ξ j‖ := by
        simp [rieszKernel, Finset.sum_neg_distrib]
      rw [hr]
      have hV : ∑ i, ‖ξ i‖ ^ 2 = ss5h_V ξ := rfl
      rw [hV]
      have : (1 / (2 * (N : ℝ))) * (-∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, Real.log ‖ξ i - ξ j‖) ≥
          -((N : ℝ) / 2 + ss5h_V ξ / 8) := by
        have h6 : (1 / (2 * (N : ℝ))) * (∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, Real.log ‖ξ i - ξ j‖) ≤
            (1 / (2 * (N : ℝ))) * ((N : ℝ) ^ 2 + (N : ℝ) * ss5h_V ξ / 4) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
        have h7 : (1 / (2 * (N : ℝ))) * ((N : ℝ) ^ 2 + (N : ℝ) * ss5h_V ξ / 4) =
            (N : ℝ) / 2 + ss5h_V ξ / 8 := by field_simp; ring
        rw [mul_neg]
        linarith
      show _ ≥ _
      have e : (1 / 1 : ℝ) = 1 := by norm_num
      simp only [div_one, one_div] at *
      nlinarith [this]
    have : -θ⁻¹ * selfSimPotential 1 0 N 0 ξ ≤ θ⁻¹ * ((N : ℝ) / 2 - ss5h_V ξ / 8) := by
      have hθi : 0 < θ⁻¹ := inv_pos.2 hθ
      nlinarith [mul_le_mul_of_nonneg_left hpot hθi.le]
    exact this

theorem ss5h_coll_measurable (N : ℕ) : MeasurableSet (eucCollisionSet 1 N) := by
  have : eucCollisionSet 1 N = ⋃ i : Fin N, ⋃ j : Fin N, ⋃ (_ : i ≠ j), {X : EucConfig 1 N | X i = X j} := by
    ext X; simp [eucCollisionSet]
  rw [this]
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ =>
    measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)

theorem ss5h_weight_measurable (N : ℕ) (θ : ℝ) : Measurable (selfSimWeight 1 0 θ N 0) := by
  unfold selfSimWeight
  refine Measurable.ite (ss5h_coll_measurable N) measurable_const ?_
  unfold selfSimPotential
  refine Real.measurable_exp.comp (Measurable.const_mul ?_ _)
  refine Measurable.add ?_ ?_
  · refine Measurable.const_mul ?_ _
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    simp only [rieszKernel, if_true]
    exact (Real.measurable_log.comp (measurable_norm.comp
      ((measurable_pi_apply i).sub (measurable_pi_apply j)))).neg
  · refine Measurable.const_mul ?_ _
    exact Finset.measurable_sum _ fun i _ => (measurable_norm.comp (measurable_pi_apply i)).pow_const 2

theorem ss5h_gauss_integrable (N : ℕ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun ξ : EucConfig 1 N => Real.exp (-c * ss5h_V ξ)) := by
  have h1 : Integrable (fun x : Euc 1 => Real.exp (-c * ‖x‖ ^ 2)) := by
    have := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Euc 1) (b := (c : ℂ)) (by simpa using hc) 0 0).norm
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [zero_mul, add_zero, Complex.norm_exp]
    congr 1
    simp
    left
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have h2 := Integrable.fintype_prod (ι := Fin N) (μ := fun _ => (volume : Measure (Euc 1)))
    (f := fun _ (x : Euc 1) => Real.exp (-c * ‖x‖ ^ 2)) (fun _ => h1)
  refine h2.congr (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [ss5h_V, Finset.mul_sum, Real.exp_sum]

theorem ss5h_V_measurable (N : ℕ) : Measurable (ss5h_V : EucConfig 1 N → ℝ) :=
  Finset.measurable_sum _ fun i _ => (measurable_norm.comp (measurable_pi_apply i)).pow_const 2

/-- Finite Gibbs entropy of a probability measure implies a finite second moment. -/
theorem ss5h_moment_V {N : ℕ} (hN : 0 < N) {θ : ℝ} (hθ : 0 < θ) {μ : Measure (EucConfig 1 N)}
    [IsProbabilityMeasure μ] (hH : gibbsEntropyW (selfSimWeight 1 0 θ N 0) μ < ⊤) :
    ∫⁻ ξ, ENNReal.ofReal (ss5h_V ξ) ∂μ < ⊤ := by
  set G := selfSimWeight 1 0 θ N 0 with hG
  have hGm : Measurable G := ss5h_weight_measurable N θ
  have hG0 : ∀ ξ, 0 ≤ G ξ := fun ξ => by
    simp only [hG, selfSimWeight]
    split_ifs
    · exact le_rfl
    · exact (Real.exp_pos _).le
  have hK : InformationTheory.klDiv μ (gibbsRefW G) ≠ ⊤ := by
    intro htop
    have : relEntropy μ (gibbsRefW G) = ⊤ := htop
    rw [gibbsEntropyW, this] at hH
    simp at hH
  obtain ⟨hac, hint⟩ := InformationTheory.klDiv_ne_top_iff.1 hK
  have hν : gibbsRefW G ≠ 0 := by
    intro h0
    rw [h0] at hac
    have := Measure.absolutelyContinuous_zero_iff.1 hac
    have h1 := measure_univ (μ := μ)
    rw [this] at h1
    simp at h1
  have hZ0 : gibbsPartitionW G ≠ 0 := by
    intro hz
    apply hν
    refine Measure.ext fun s hs => ?_
    have : ∫⁻ x in s, ENNReal.ofReal (G x) = 0 := by
      refine le_antisymm ?_ bot_le
      calc ∫⁻ x in s, ENNReal.ofReal (G x) ≤ ∫⁻ x, ENNReal.ofReal (G x) := setLIntegral_le_lintegral _ _
        _ = 0 := hz
    simp [gibbsRefW, withDensity_apply _ hs, this]
  have hZt : gibbsPartitionW G ≠ ⊤ := by
    intro hz
    apply hν
    simp [gibbsRefW, hz]
  haveI : IsFiniteMeasure (gibbsRefW G) := ⟨by
    have : gibbsRefW G Set.univ = 1 := by
      simp only [gibbsRefW, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
        Measure.restrict_univ, smul_eq_mul]
      exact ENNReal.inv_mul_cancel hZ0 hZt
    rw [this]; exact ENNReal.one_lt_top⟩
  -- the exponential moment
  set c : ℝ := 1 / (16 * θ) with hc
  have hcpos : 0 < c := by positivity
  have hexp : ∫⁻ ξ, ENNReal.ofReal (Real.exp (c * ss5h_V ξ)) ∂(gibbsRefW G) < ⊤ := by
    have hmeas : Measurable fun ξ : EucConfig 1 N => ENNReal.ofReal (Real.exp (c * ss5h_V ξ)) :=
      (Real.measurable_exp.comp ((ss5h_V_measurable N).const_mul c)).ennreal_ofReal
    simp only [gibbsRefW, lintegral_smul_measure]
    rw [lintegral_withDensity_eq_lintegral_mul _ hGm.ennreal_ofReal hmeas]
    refine ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hZ0)) ?_
    set K : ℝ := Real.exp (θ⁻¹ * ((N : ℝ) / 2)) with hK
    have hGauss := ((ss5h_gauss_integrable N hcpos).const_mul K).lintegral_lt_top
    refine lt_of_le_of_lt (lintegral_mono fun ξ => ?_) hGauss
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (hG0 ξ)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := ss5h_weight_le hN hθ ξ
    calc G ξ * Real.exp (c * ss5h_V ξ)
        ≤ Real.exp (θ⁻¹ * ((N : ℝ) / 2 - ss5h_V ξ / 8)) * Real.exp (c * ss5h_V ξ) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = K * Real.exp (-c * ss5h_V ξ) := by
          rw [← Real.exp_add, hK, ← Real.exp_add]
          congr 1
          rw [hc]
          field_simp
          ring
  have := ss5h_young_moment hac hint ((ss5h_V_measurable N).const_mul c) hexp
  have hmeasV : Measurable fun ξ : EucConfig 1 N => ENNReal.ofReal (c * ss5h_V ξ) :=
    ((ss5h_V_measurable N).const_mul c).ennreal_ofReal
  have e : ∀ ξ : EucConfig 1 N, ENNReal.ofReal (ss5h_V ξ) =
      ENNReal.ofReal c⁻¹ * ENNReal.ofReal (c * ss5h_V ξ) := fun ξ => by
    rw [← ENNReal.ofReal_mul (inv_pos.2 hcpos).le, ← mul_assoc, inv_mul_cancel₀ hcpos.ne', one_mul]
  simp only [e]
  rw [lintegral_const_mul _ hmeasV]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top this

/-! ### (a) The permuted noise is a Brownian filtration -/

/-- Reindexing equivalence `k ↦ (σ k, 0)`. -/
def ss5h_idx {N : ℕ} (σ : Equiv.Perm (Fin N)) : Fin N ≃ Fin N × Fin 1 :=
  σ.trans (Equiv.prodUnique (Fin N) (Fin 1)).symm

theorem ss5h_noise_brownian {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω}
    {ℱ : Filtration ℝ mΩ} {N : ℕ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (σ : Equiv.Perm (Fin N))
    (h : IsBrownianFiltration Q ℱ W') : IsBrownianFiltration Q ℱ (ss5_chNoise σ W') := by
  have hred : Measurable fun (g : Fin N × Fin 1 → ℝ) (k : Fin N) => g (σ k, 0) :=
    measurable_pi_iff.2 fun k => measurable_pi_apply _
  refine ⟨h.complete, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    exact hred.comp (h.adapted t)
  · intro ζ
    funext k
    simp [ss5_chNoise, h.zero ζ]
  · intro ζ
    exact continuous_pi fun k => (continuous_apply _).comp (h.cont ζ)
  · intro s t hst
    refine indep_of_indep_of_le_left (h.indep_incr s t hst) ?_
    have e : (fun ζ => ss5_chNoise σ W' t ζ - ss5_chNoise σ W' s ζ) =
        (fun g : Fin N × Fin 1 → ℝ => fun k : Fin N => g (σ k, 0)) ∘ (fun ζ => W' t ζ - W' s ζ) := by
      funext ζ k; simp [ss5_chNoise]
    rw [e, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hred.comap_le
  · intro s t hst
    have e : (fun ζ => ss5_chNoise σ W' t ζ - ss5_chNoise σ W' s ζ) =
        (fun g : Fin N × Fin 1 → ℝ => fun k : Fin N => g (σ k, 0)) ∘ (fun ζ => W' t ζ - W' s ζ) := by
      funext ζ k; simp [ss5_chNoise]
    rw [e]
    have hmp := (measurePreserving_piCongrLeft (fun _ : Fin N × Fin 1 => (gaussianReal 0 (t - s)))
      (ss5h_idx σ)).symm
    have e2 : (⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin N × Fin 1 => ℝ) (ss5h_idx σ)).symm) =
        fun g : Fin N × Fin 1 → ℝ => fun k : Fin N => g (σ k, 0) := by
      funext g k
      change (Equiv.piCongrLeft (fun _ : Fin N × Fin 1 => ℝ) (ss5h_idx σ)).symm g k = _
      rw [Equiv.piCongrLeft_symm_apply]
      simp [ss5h_idx]
    rw [e2] at hmp
    exact hmp.comp_hasLaw (h.gaussian_incr s t hst)

/-! ### (c) The deterministic core -/

/-- Contribution of the lower neighbours: `∑_{l<m} (z_m - z_l)⁻¹`. -/
def ss5h_low {N : ℕ} (z : Ch5 N) (m : Fin N) : ℝ := ∑ l : Fin N, if l < m then (z m - z l)⁻¹ else 0

/-- Contribution of the upper neighbours: `∑_{l>m} (z_l - z_m)⁻¹`. -/
def ss5h_high {N : ℕ} (z : Ch5 N) (m : Fin N) : ℝ := ∑ l : Fin N, if m < l then (z l - z m)⁻¹ else 0

/-- The drift in chamber coordinates, `b_m(z) = N⁻¹ ∑_{l≠m} (z_m - z_l)⁻¹ - z_m/2`. -/
def ss5h_bdr {N : ℕ} (z : Ch5 N) (m : Fin N) : ℝ :=
  (1 / (N : ℝ)) * ∑ l ∈ Finset.univ.erase m, (z m - z l)⁻¹ - z m / 2

theorem ss5h_erase_sum {N : ℕ} (z : Ch5 N) (m : Fin N) :
    ∑ l ∈ Finset.univ.erase m, (z m - z l)⁻¹ = ss5h_low z m - ss5h_high z m := by
  have h0 := Finset.sum_erase (Finset.univ : Finset (Fin N)) (f := fun l => (z m - z l)⁻¹) (a := m)
    (by simp)
  rw [h0, ss5h_low, ss5h_high, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rcases lt_trichotomy l m with h | h | h
  · simp [h, not_lt.2 h.le]
  · subst h; simp
  · have h' : ¬ l < m := not_lt.2 h.le
    simp [h, h']
    rw [← inv_neg, neg_sub]

theorem ss5h_pairGrad_coord {N : ℕ} (z : Ch5 N) (m : Fin N) :
    (ss5t_pairGrad N (fun g => -(g⁻¹)) z) m = (1 / (N : ℝ)) * (ss5h_high z m - ss5h_low z m) := by
  unfold ss5t_pairGrad ss5h_high ss5h_low
  simp only [PiLp.smul_apply, smul_eq_mul, WithLp.ofLp_sum, Finset.sum_apply]
  congr 1
  have key : ∀ x c : Fin N, (if x < c then -(z c - z x)⁻¹ • ss5t_v x c else 0 : Ch5 N).ofLp m =
      if x < c then -(z c - z x)⁻¹ * ((if m = c then 1 else 0) - (if m = x then 1 else 0)) else 0 := by
    intro x c
    by_cases hxc : x < c
    · simp [hxc, ss5t_v, EuclideanSpace.single_apply]
    · simp [hxc]
  simp only [key]
  have h1 : ∀ x : Fin N, ∑ c : Fin N, (if x < c then -(z c - z x)⁻¹ * (if m = c then (1 : ℝ) else 0) else 0) =
      if x < m then -(z m - z x)⁻¹ else 0 := by
    intro x
    rw [Finset.sum_eq_single m]
    · simp
    · intro c _ hc
      have : m ≠ c := fun h => hc h.symm
      simp [this]
    · simp
  have h2 : ∀ x : Fin N, ∑ c : Fin N, (if x < c then -(z c - z x)⁻¹ * (if m = x then (1 : ℝ) else 0) else 0) =
      if m = x then ∑ c : Fin N, (if x < c then -(z c - z x)⁻¹ else 0) else 0 := by
    intro x
    by_cases hx : m = x
    · simp [hx]
    · simp [hx]
  have e : ∀ x c : Fin N, (if x < c then -(z c - z x)⁻¹ * ((if m = c then (1 : ℝ) else 0) - (if m = x then 1 else 0)) else 0) =
      (if x < c then -(z c - z x)⁻¹ * (if m = c then (1 : ℝ) else 0) else 0) -
        (if x < c then -(z c - z x)⁻¹ * (if m = x then (1 : ℝ) else 0) else 0) := by
    intro x c
    by_cases hxc : x < c
    · simp only [hxc, if_true]; ring
    · simp [hxc]
  simp only [e, Finset.sum_sub_distrib, h1, h2]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ m)]
  have n1 : ∀ x : Fin N, (if x < m then -(z m - z x)⁻¹ else 0) = -(if x < m then (z m - z x)⁻¹ else 0) := by
    intro x; split_ifs <;> simp
  have n2 : ∀ c : Fin N, (if m < c then -(z c - z m)⁻¹ else 0) = -(if m < c then (z c - z m)⁻¹ else 0) := by
    intro x; split_ifs <;> simp
  simp only [n1, n2, Finset.sum_neg_distrib]
  ring

theorem ss5h_coord_continuous {N : ℕ} {y : ℝ → Ch5 N} (hyc : Continuous y) (k : Fin N) :
    Continuous fun r => y r k :=
  (EuclideanSpace.proj k : Ch5 N →L[ℝ] ℝ).continuous.comp hyc

/-- Deterministic core: from a weakly ordered continuous path with null collision occupation and integrable
drift components, the inverse gaps are integrable (triangular induction) and the chamber equation holds. -/
theorem ss5h_det_core {N : ℕ} {S : ℝ} (hS : 0 ≤ S) {y w : ℝ → Ch5 N} {d : ℝ → Fin N → ℝ}
    (hyc : Continuous y)
    (hord : ∀ r ∈ Icc (0 : ℝ) S, ∀ k l : Fin N, k ≤ l → y r k ≤ y r l)
    (hnull : volume {r : ℝ | r ∈ Icc (0 : ℝ) S ∧ ∃ k l : Fin N, k ≠ l ∧ y r k = y r l} = 0)
    (hd : ∀ r ∈ Icc (0 : ℝ) S, y r ∈ ss5_chamber N → ∀ m, d r m = ss5h_bdr (y r) m)
    (hint : ∀ m, IntegrableOn (fun r => d r m) (Icc (0 : ℝ) S))
    (heq : ∀ t ∈ Icc (0 : ℝ) S, ∀ m, y t m = y 0 m + (∫ r in Icc (0 : ℝ) t, d r m) + w t m) :
    (∀ᵐ r ∂volume, r ∈ Icc (0 : ℝ) S → y r ∈ ss5_chamber N) ∧
    (∀ k l : Fin N, k < l → IntegrableOn (fun r : ℝ => (y r l - y r k)⁻¹) (Icc (0 : ℝ) S)) ∧
    ∀ t ∈ Icc (0 : ℝ) S, y t = y 0 + (∫ r in (0 : ℝ)..t,
      (-(gradient (ss5_Phi N) (y r)) - (1 / 2 : ℝ) • y r)) + w t := by
  have hnull' : ∀ᵐ r ∂volume, ¬ (r ∈ Icc (0 : ℝ) S ∧ ∃ k l : Fin N, k ≠ l ∧ y r k = y r l) :=
    measure_eq_zero_iff_ae_notMem.1 hnull
  have hch : ∀ᵐ r ∂volume, r ∈ Icc (0 : ℝ) S → y r ∈ ss5_chamber N := by
    filter_upwards [hnull'] with r hr hrS k l hkl
    exact lt_of_le_of_ne (hord r hrS k l hkl.le) fun he => hr ⟨hrS, k, l, hkl.ne, he⟩
  have hchR : ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) S)), y r ∈ ss5_chamber N :=
    (ae_restrict_iff' measurableSet_Icc).2 hch
  have hmemR : ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) S)), r ∈ Icc (0 : ℝ) S :=
    ae_restrict_mem measurableSet_Icc
  have hGm : ∀ k l : Fin N, Measurable fun r => (y r l - y r k)⁻¹ := fun k l =>
    (((ss5h_coord_continuous hyc l).sub (ss5h_coord_continuous hyc k)).measurable).inv
  -- Step 2: inverse gaps
  have hgap : ∀ k l : Fin N, k < l → IntegrableOn (fun r : ℝ => (y r l - y r k)⁻¹) (Icc (0 : ℝ) S) := by
    intro k
    induction k using WellFoundedLT.induction with
    | _ k ih =>
    intro l hkl
    have hNpos : (0 : ℝ) < N := by exact_mod_cast Fin.pos k
    have hlow : IntegrableOn (fun r => ss5h_low (y r) k) (Icc (0 : ℝ) S) := by
      refine integrable_finsetSum _ fun l' _ => ?_
      by_cases hl' : l' < k
      · simp only [hl', if_true]; exact ih l' hl' k hl'
      · simp only [hl', if_false]; exact integrable_zero _ _ _
    have hy : IntegrableOn (fun r => y r k) (Icc (0 : ℝ) S) :=
      (ss5h_coord_continuous hyc k).integrableOn_Icc
    have hhigh : IntegrableOn (fun r => ss5h_high (y r) k) (Icc (0 : ℝ) S) := by
      have h1 : IntegrableOn (fun r => ss5h_low (y r) k - (N : ℝ) * (d r k + y r k / 2)) (Icc (0 : ℝ) S) :=
        hlow.sub (((hint k).add (hy.div_const 2)).const_mul (N : ℝ))
      refine h1.congr ?_
      filter_upwards [hchR, hmemR] with r hr hrS
      rw [hd r hrS hr k]
      unfold ss5h_bdr
      rw [ss5h_erase_sum]
      field_simp
      ring
    have hnn : ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) S)), ∀ l' : Fin N,
        0 ≤ (if k < l' then (y r l' - y r k)⁻¹ else 0) := by
      filter_upwards [hchR] with r hr l'
      by_cases h : k < l'
      · simp only [h, if_true]; exact inv_nonneg.2 (sub_nonneg.2 (hr k l' h).le)
      · simp [h]
    refine hhigh.mono' (hGm k l).aestronglyMeasurable ?_
    filter_upwards [hnn, hchR] with r hr hrc
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (sub_nonneg.2 (hrc k l hkl).le))]
    have := Finset.single_le_sum (f := fun l' => if k < l' then (y r l' - y r k)⁻¹ else 0)
      (fun l' _ => hr l') (Finset.mem_univ l)
    simpa [hkl, ss5h_high] using this
  refine ⟨hch, hgap, ?_⟩
  -- Step 3: the equation
  have hBint := ss5c_B_integrable hgap
  set F : ℝ → Ch5 N := fun r => -(gradient (ss5_Phi N) (y r)) - (1 / 2 : ℝ) • y r with hF
  set F' : ℝ → Ch5 N := fun r => -(ss5t_pairGrad N (fun g => -(g⁻¹)) (y r)) - (1 / 2 : ℝ) • y r with hF'
  have hFF' : ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) S)), F r = F' r := by
    filter_upwards [hchR] with r hr
    simp only [hF, hF', ss5t_gradient_Phi hr]
  have hF'meas : Measurable F' := by
    have h2 : Measurable (ss5t_pairGrad N (fun g : ℝ => -(g⁻¹))) :=
      ss5c_measurable_pairGrad N (measurable_inv.neg)
    exact (h2.comp hyc.measurable).neg.sub (hyc.measurable.const_smul (1 / 2 : ℝ))
  have hF'int : IntegrableOn F' (Icc (0 : ℝ) S) := by
    have hyn : IntegrableOn (fun r => ‖y r‖) (Icc (0 : ℝ) S) := hyc.norm.integrableOn_Icc
    refine ((hBint.const_mul 2).add (hyn.div_const 2)).mono' hF'meas.aestronglyMeasurable ?_
    filter_upwards [hchR] with r hr
    have h1 := ss5c_pairGrad_sub_le (N := N) (fun g => -(g⁻¹)) (fun _ => 0) (c := 1) zero_le_one (y r) hr
      (fun g hg => by simp [abs_of_pos (inv_pos.2 hg)])
    rw [ss5c_pairGrad_zero, sub_zero] at h1
    have e1 : ‖F' r‖ ≤ ‖ss5t_pairGrad N (fun g => -(g⁻¹)) (y r)‖ + ‖(1 / 2 : ℝ) • y r‖ := by
      have := norm_sub_le (-(ss5t_pairGrad N (fun g => -(g⁻¹)) (y r))) ((1 / 2 : ℝ) • y r)
      rwa [norm_neg] at this
    have e2 : ‖(1 / 2 : ℝ) • y r‖ = ‖y r‖ / 2 := by
      rw [norm_smul]; norm_num; ring
    simp only [Pi.add_apply]
    linarith
  have hF_int : IntegrableOn F (Icc (0 : ℝ) S) := hF'int.congr (hFF'.mono fun r h => h.symm)
  intro t ht
  ext m
  have hcoord := ss5c_intervalIntegral_coord (ss5c_interval_of_integrableOn hF_int ht.1 ht.2) m
  have hae : ∀ᵐ r ∂(volume.restrict (Ioc (0 : ℝ) t)), F r m = d r m := by
    have hsub : Ioc (0 : ℝ) t ⊆ Icc (0 : ℝ) S := fun r hr => ⟨hr.1.le, hr.2.trans ht.2⟩
    have h1 := ae_restrict_of_ae_restrict_of_subset hsub hchR
    have h2 := ae_restrict_of_ae_restrict_of_subset hsub hmemR
    filter_upwards [h1, h2] with r hr hrS
    have hFr : F r = F' r := by simp only [hF, hF', ss5t_gradient_Phi hr]
    rw [hFr, hd r hrS hr m]
    simp only [hF', PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul, ss5h_pairGrad_coord]
    unfold ss5h_bdr
    rw [ss5h_erase_sum]
    ring
  have hI : ∫ r in (0 : ℝ)..t, F r m = ∫ r in Icc (0 : ℝ) t, d r m := by
    rw [intervalIntegral.integral_of_le ht.1, integral_Icc_eq_integral_Ioc]
    exact integral_congr_ae hae
  rw [heq t ht m, PiLp.add_apply, PiLp.add_apply, hcoord, hI]

/-! ### Assembly -/

theorem ss5h_toCh_continuous {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    Continuous (ss5_toCh σ : EucConfig 1 N → Ch5 N) := by
  unfold ss5_toCh
  refine (PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).comp ?_
  exact continuous_pi fun k => (PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp (continuous_apply (σ k))

theorem ss5h_toCh_norm_sq {N : ℕ} (σ : Equiv.Perm (Fin N)) (ξ : EucConfig 1 N) :
    ‖ss5_toCh σ ξ‖ ^ 2 = ss5h_V ξ := by
  rw [EuclideanSpace.norm_sq_eq, ss5h_V]
  have h1 : ∀ i : Fin N, ‖ξ i‖ ^ 2 = ‖ξ i 0‖ ^ 2 := fun i => by
    rw [EuclideanSpace.norm_sq_eq]; simp
  simp only [h1]
  exact Equiv.sum_comp σ (fun i => ‖ξ i 0‖ ^ 2)

theorem ss5h_drift_coord {N : ℕ} (τ : ℝ) (Ξ : EucConfig 1 N) (i : Fin N)
    (hx : ∀ j, j ≠ i → Ξ i 0 ≠ Ξ j 0) :
    (ssDrift 1 0 N τ Ξ i) 0 =
      (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i, (Ξ i 0 - Ξ j 0)⁻¹ - Ξ i 0 / 2 := by
  have hs : ∀ j ∈ Finset.univ.erase i, rieszKernelGrad 1 0 (Ξ i - Ξ j) 0 = -((Ξ i 0 - Ξ j 0)⁻¹) := by
    intro j hj
    have hji := Finset.ne_of_mem_erase hj
    have hu : Ξ i - Ξ j ≠ 0 := by
      intro h
      apply hx j hji
      have := congrArg (fun v : Euc 1 => v 0) h
      simpa [sub_eq_zero] using this
    rw [HRS.MP.SelfSimP1.ssp1c_rkg_apply hu]
    simp [one_div]
  simp only [ssDrift, PiLp.neg_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, WithLp.ofLp_sum,
    Finset.sum_apply]
  rw [Finset.sum_congr rfl hs]
  simp [aSelfSim, Finset.sum_neg_distrib]
  ring

theorem ss5_chamber_reading_proof (N : ℕ) (hN : 2 ≤ N) (invβ : ℝ) (hβ : 0 < invβ) (S : ℝ) (hS : 0 < S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc 1)}
    {Y : ℝ≥0 → Ω → EucConfig 1 N}
    (hY : SSAddSol Q invβ (ssDrift 1 0 N) S ℱ W' W Y) (σ : Equiv.Perm (Fin N))
    (hord : ∀ᵐ ζ ∂Q, ∀ t : ℝ≥0, (t : ℝ) ≤ S → ∀ k k' : Fin N, k ≤ k' → Y t ζ (σ k) 0 ≤ Y t ζ (σ k') 0)
    (h0 : ∀ᵐ ζ ∂Q, Y 0 ζ ∈ ss5_cone σ)
    (hH0 : gibbsEntropyW (selfSimWeight 1 0 invβ N 0) (law Q (Y 0)) < ⊤) :
    IsBrownianFiltration Q ℱ (ss5_chNoise σ W') ∧
      Measurable[ℱ 0] (fun ζ => ss5_toCh σ (Y 0 ζ)) ∧
      ∫⁻ ζ, ENNReal.ofReal (‖ss5_toCh σ (Y 0 ζ)‖ ^ 2) ∂Q < ⊤ ∧
      (∀ ζ, Continuous fun r : ℝ => ss5_toCh σ (Y (Real.toNNReal r) ζ)) ∧
      ∀ᵐ ζ ∂Q,
        (∀ᵐ r ∂volume, r ∈ Icc (0 : ℝ) S → ss5_toCh σ (Y (Real.toNNReal r) ζ) ∈ ss5_chamber N) ∧
        (∀ k l : Fin N, k < l → IntegrableOn
          (fun r : ℝ => (ss5_toCh σ (Y (Real.toNNReal r) ζ) l - ss5_toCh σ (Y (Real.toNNReal r) ζ) k)⁻¹)
          (Icc (0 : ℝ) S)) ∧
        ∀ t ∈ Icc (0 : ℝ) S, ss5_toCh σ (Y (Real.toNNReal t) ζ) = ss5_toCh σ (Y 0 ζ) +
          (∫ r in (0 : ℝ)..t, (-(gradient (ss5_Phi N) (ss5_toCh σ (Y (Real.toNNReal r) ζ))) -
            (1 / 2 : ℝ) • ss5_toCh σ (Y (Real.toNNReal r) ζ))) +
          Real.sqrt (2 * invβ) • WithLp.toLp 2 (ss5_chNoise σ W' (Real.toNNReal t) ζ) := by
  have hN0 : 0 < N := by omega
  have hYm : ∀ t, Measurable (Y t) := fun t => (hY.filtered.adapted t).mono (ℱ.le _) le_rfl
  have hY0 : Measurable[ℱ 0] (Y 0) := by
    have h := hY.filtered.adapted 0
    rwa [NNReal.coe_zero] at h
  have hcont : ∀ ζ, Continuous fun r : ℝ => ss5_toCh σ (Y (Real.toNNReal r) ζ) := fun ζ =>
    (ss5h_toCh_continuous σ).comp ((hY.cont ζ).comp continuous_real_toNNReal)
  refine ⟨ss5h_noise_brownian σ hY.filtered.brownian, ?_, ?_, hcont, ?_⟩
  · exact (ss5h_toCh_continuous σ).measurable.comp hY0
  · haveI : IsProbabilityMeasure (law Q (Y 0)) :=
      (Measure.isProbabilityMeasure_map_iff (hYm 0).aemeasurable).2 inferInstance
    have := ss5h_moment_V hN0 hβ (μ := law Q (Y 0)) hH0
    have e : ∀ ζ, ENNReal.ofReal (‖ss5_toCh σ (Y 0 ζ)‖ ^ 2) = ENNReal.ofReal (ss5h_V (Y 0 ζ)) :=
      fun ζ => by rw [ss5h_toCh_norm_sq]
    simp only [e]
    rw [← lintegral_map (f := fun ξ => ENNReal.ofReal (ss5h_V ξ))
      ((ss5h_V_measurable N).ennreal_ofReal) (hYm 0)]
    exact this
  · filter_upwards [hord, hY.eqn, hY.occupation, hY.filtered.coords] with ζ hordζ heqζ hoccζ hcoζ
    -- the data of the deterministic core
    set y : ℝ → Ch5 N := fun r => ss5_toCh σ (Y (Real.toNNReal r) ζ) with hy
    set w : ℝ → Ch5 N := fun t => Real.sqrt (2 * invβ) • WithLp.toLp 2 (ss5_chNoise σ W' (Real.toNNReal t) ζ)
      with hw
    set d : ℝ → Fin N → ℝ := fun r m => (ssDrift 1 0 N r (Y (Real.toNNReal r) ζ) (σ m)) 0 with hd
    have hycoord : ∀ r (m : Fin N), y r m = Y (Real.toNNReal r) ζ (σ m) 0 := fun r m => rfl
    have hcoe : ∀ r : ℝ, 0 ≤ r → ((Real.toNNReal r : ℝ≥0) : ℝ) = r := fun r hr => Real.coe_toNNReal r hr
    have hord' : ∀ r ∈ Icc (0 : ℝ) S, ∀ k l : Fin N, k ≤ l → y r k ≤ y r l := by
      intro r hr k l hkl
      exact hordζ (Real.toNNReal r) (by rw [hcoe r hr.1]; exact hr.2) k l hkl
    have hnull : volume {r : ℝ | r ∈ Icc (0 : ℝ) S ∧ ∃ k l : Fin N, k ≠ l ∧ y r k = y r l} = 0 := by
      refine measure_mono_null (fun r hr => ?_) hoccζ
      obtain ⟨hrS, k, l, hkl, he⟩ := hr
      refine ⟨hrS, σ k, σ l, fun h => hkl (σ.injective h), ?_⟩
      ext j
      fin_cases j
      simpa [hycoord] using he
    have hdr : ∀ r ∈ Icc (0 : ℝ) S, y r ∈ ss5_chamber N → ∀ m, d r m = ss5h_bdr (y r) m := by
      intro r hr hch m
      have hx : ∀ j, j ≠ σ m → Y (Real.toNNReal r) ζ (σ m) 0 ≠ Y (Real.toNNReal r) ζ j 0 := by
        intro j hj he
        obtain ⟨l, rfl⟩ := σ.surjective j
        have hml : m ≠ l := fun h => hj (by rw [h])
        rcases lt_or_gt_of_ne hml with h | h
        · exact (ne_of_lt (hch m l h)) he
        · exact (ne_of_gt (hch l m h)) he
      simp only [hd]
      rw [ss5h_drift_coord _ _ _ hx]
      unfold ss5h_bdr
      congr 2
      refine Finset.sum_equiv σ.symm (fun l => by simp [Finset.mem_erase, Equiv.symm_apply_eq]) (fun l _ => ?_)
      simp [hycoord]
    have hintd : ∀ m, IntegrableOn (fun r => d r m) (Icc (0 : ℝ) S) := by
      intro m
      have hcS : ((Real.toNNReal S : ℝ≥0) : ℝ) = S := hcoe S hS.le
      have := (heqζ (Real.toNNReal S) (by rw [hcS])).1 (σ m)
      rw [hcS] at this
      exact ss5c_integrableOn_coord (N := 1) this 0
    have heqd : ∀ t ∈ Icc (0 : ℝ) S, ∀ m, y t m = y 0 m + (∫ r in Icc (0 : ℝ) t, d r m) + w t m := by
      intro t ht m
      have hct : ((Real.toNNReal t : ℝ≥0) : ℝ) = t := hcoe t ht.1
      obtain ⟨hI, hE⟩ := heqζ (Real.toNNReal t) (by rw [hct]; exact ht.2)
      rw [hct] at hI hE
      have h1 := congrArg (fun v : Euc 1 => v 0) (hE (σ m))
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at h1
      have h2 : (∫ r in Icc (0 : ℝ) t, ssDrift 1 0 N r (Y (Real.toNNReal r) ζ) (σ m)) 0 =
          ∫ r in Icc (0 : ℝ) t, d r m := by
        have := (EuclideanSpace.proj (0 : Fin 1) : Euc 1 →L[ℝ] ℝ).integral_comp_comm (hI (σ m))
        simpa [hd] using this.symm
      rw [h2] at h1
      have h3 : W' (Real.toNNReal t) ζ (σ m, 0) = W (Real.toNNReal t) ζ (σ m) 0 := (hcoζ _ _ _)
      have h4 : W' 0 ζ (σ m, 0) = W 0 ζ (σ m) 0 := hcoζ _ _ _
      have h5 : W' 0 ζ (σ m, 0) = 0 := by simp [hY.filtered.brownian.zero ζ]
      rw [hycoord, h1]
      simp only [hy, hw, ss5_toCh, ss5_chNoise, Real.toNNReal_zero, PiLp.smul_apply, smul_eq_mul]
      rw [← h3, ← h4, h5]
      simp
    obtain ⟨hA, hB, hC⟩ := ss5h_det_core hS.le (y := y) (w := w) (d := d)
      (hcont ζ) hord' hnull hdr hintd heqd
    refine ⟨hA, hB, ?_⟩
    intro t ht
    have := hC t ht
    simpa [hy, hw, Real.toNNReal_zero] using this

example := (@ss5_chamber_reading_proof : type_of% @HRS.MP.SelfSimP5.ss5_chamber_reading)

end HRS.MP.SelfSimP5Impl
