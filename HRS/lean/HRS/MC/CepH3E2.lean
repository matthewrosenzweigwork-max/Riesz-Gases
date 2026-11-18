import HRS.MC.CepH3E1

/-!
# Packet CEPH3, part E2: domination of the regularised Gibbs weights, reference measures
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
namespace HRS.MC.CepH3
open HRS HRS.MC.Cepa
noncomputable section
variable {N : ℕ}

theorem h3e_dominated [NeZero N] {J : ℝ → Ch N → Ch N} {Φn : ℝ → Ch N → ℝ} (hJ : cep_Yosida 1 N J)
    (hΦ : ∀ n z, 0 < n → HasGradientAt (Φn n) (n • (z - J n z)) z)
    (hΦlim : ∀ z, z ∈ cep_Alcove N → Tendsto (fun n : ℕ => Φn n z) atTop (𝓝 (cep_chamberPot 1 N z)))
    {Ψ : Ch N → ℝ} {L : ℝ≥0} (hΨ : ContDiff ℝ 1 Ψ) (hΨL : LipschitzWith L (gradient Ψ))
    {β : ℝ} (hβ : 0 < β) :
    ∃ (n₀ : ℕ) (K : ℝ), 1 ≤ n₀ ∧ 0 < K ∧ ∀ n : ℕ, n₀ ≤ n → ∀ z ∈ cep_cell N,
      Real.exp (-(Φn n z + Ψ z) / β) ≤ K * Real.exp (-(1 / (2 * β)) * ‖z‖ ^ 2) := by
  obtain ⟨w, hw, -⟩ := h3e_alcove_point (N := N)
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hc := h3b_c_tendsto hJ hΦlim hw
  obtain ⟨n₁, hn₁⟩ := (hc.eventually (lt_mem_nhds (show (-1 : ℝ) < 0 by norm_num))).exists_forall_of_atTop
  set a : ℝ := ‖gradient Ψ 0‖ with ha
  set B : ℝ := (N : ℝ) * Real.log 2 + 1 + |Ψ 0| with hB
  set C : ℝ := B + a ^ 2 / 2 + 4 * a * Real.sqrt N + 16 * N * L + 8 * N with hC
  refine ⟨max (max n₁ 1) ⌈32 * (N : ℝ) * (L + 1)⌉₊, Real.exp (C / β), ?_, Real.exp_pos _, fun n hn z hz => ?_⟩
  · exact (le_max_right n₁ 1).trans (le_max_left _ _)
  have hn1 : n₁ ≤ n := ((le_max_left _ _).trans (le_max_left _ _)).trans hn
  have hn2 : 32 * (N : ℝ) * (L + 1) ≤ n := by
    have := (le_max_right _ _).trans hn
    exact (Nat.le_ceil _).trans (by exact_mod_cast this)
  have hnpos : (0 : ℝ) < n := by
    have : (0:ℝ) < 32 * N * (L + 1) := by positivity
    linarith
  have hlow := h3b_Phin_lower hJ hΦ hnpos w z
  have hcn := hn₁ n hn1
  have hΨb := h3e_Psi_bound hΨ hΨL z
  have hdist := h3e_norm_le_infDist hz
  have hd0 : 0 ≤ Metric.infDist z (cep_Alcove N) := Metric.infDist_nonneg
  have hreal := h3e_real_ineq (N := (N : ℝ)) (a := a) (L := L) (n := n) (s := ‖z‖)
    (d := Metric.infDist z (cep_Alcove N)) (B := B) hN (norm_nonneg _) L.2 (norm_nonneg _) hd0 hdist hn2
  have hΨ' : -Ψ z ≤ |Ψ 0| + a * ‖z‖ + L * ‖z‖ ^ 2 := by
    have := (abs_le.mp hΨb).1
    have := neg_abs_le (Ψ 0)
    linarith
  have hsum : -(Φn n z + Ψ z) ≤ C - ‖z‖ ^ 2 / 2 := by
    have : -(Φn n z) ≤ (N : ℝ) * Real.log 2 + 1 - n / 2 * Metric.infDist z (cep_Alcove N) ^ 2 := by
      linarith
    have e : B + a * ‖z‖ + L * ‖z‖ ^ 2 - n / 2 * Metric.infDist z (cep_Alcove N) ^ 2 =
        ((N : ℝ) * Real.log 2 + 1 - n / 2 * Metric.infDist z (cep_Alcove N) ^ 2) + (|Ψ 0| + a * ‖z‖ + L * ‖z‖ ^ 2) := by
      rw [hB]; ring
    linarith
  have hexp : -(Φn n z + Ψ z) / β ≤ C / β + (-(1 / (2 * β)) * ‖z‖ ^ 2) := by
    have : -(Φn n z + Ψ z) / β ≤ (C - ‖z‖ ^ 2 / 2) / β := div_le_div_of_nonneg_right hsum hβ.le
    refine this.trans (le_of_eq ?_)
    field_simp
    ring
  calc Real.exp (-(Φn n z + Ψ z) / β) ≤ Real.exp (C / β + (-(1 / (2 * β)) * ‖z‖ ^ 2)) := Real.exp_le_exp.mpr hexp
    _ = _ := Real.exp_add _ _

/-! ### The reference measures -/

/-- The unnormalised cylinder reference measure `1_cell e^{-U/β} dz`. -/
def h3e_mn [NeZero N] (β : ℝ) (U : Ch N → ℝ) : Measure (Ch N) :=
  (volume.restrict (cep_cell N)).withDensity (cep_cylWeight β U)

/-- The limit reference measure `1_{cell ∩ alcove} e^{-U/β} dz`. -/
def h3e_mE [NeZero N] (β : ℝ) (U : Ch N → ℝ) : Measure (Ch N) :=
  (volume.restrict (cep_cell N)).withDensity ((cep_Alcove N).indicator (cep_cylWeight β U))

lemma h3e_cell_measurable [NeZero N] : MeasurableSet (cep_cell N) := by
  have : cep_cell N = (fun z : Ch N => z 0) ⁻¹' Ico (0:ℝ) 1 := by ext z; simp [cep_cell]
  rw [this]; exact (by fun_prop : Measurable fun z : Ch N => z 0) measurableSet_Ico

lemma h3e_weight_measurable {U : Ch N → ℝ} (hU : Measurable U) {β : ℝ} :
    Measurable (cep_cylWeight β U) := by
  unfold cep_cylWeight
  exact ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp (hU.neg.div_const β))

lemma h3e_cyl_eq_F [NeZero N] (β : ℝ) (U : Ch N → ℝ) (μ : Measure (Ch N)) :
    cep_cylEntropy β U μ = h3c_F μ (h3e_mn β U) := by
  have hu : (h3e_mn β U) univ = cep_cylPartition β U := by
    unfold h3e_mn cep_cylPartition
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  unfold cep_cylEntropy h3c_F relEntropy cep_cylRef
  rw [hu]
  rfl

lemma h3e_map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {Q : α → β}
    (hQ : Measurable Q) {μ : Measure α} {f : β → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity (f ∘ Q)).map Q = (μ.map Q).withDensity f := by
  ext T hT
  rw [Measure.map_apply hQ hT, withDensity_apply _ (hQ hT), withDensity_apply _ hT,
    setLIntegral_map hT hf hQ]
  rfl
end
end HRS.MC.CepH3
