import HRS.MS.MfeConfAux108

/-!
# S.B.1, packet F9 (part 12): convergence of the initial relative entropy `H(ν₀|Q^M_0) → H(ν₀|Q_0)` (D07 of the Pro note)

For a probability law `ν` with `H(ν|μ^{⊗N}) < ∞`, finite second moment and integrable singular modulated energy
(`MFEFiniteW`), and admissible kernels `k_M → g`:
* `sb1_kl_Q`: `H(ν|Q_k) = H(ν|μ^{⊗N}) + βN ∫ En_k dν + log K_k` for any admissible `k` with `En_k ∈ L¹(ν)`;
* `sb1_En_dom`: `|En_k(X)| ≤ B(X)` off the collision set, uniformly in `k`, with `B ∈ L¹(ν)`;
* `sb1_init_tendsto`: `H(ν|Q^M) → H(ν|Q)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open HRS HRS.Whole
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section Init

variable {s : ℝ} {ρ0 : Euc d → ℝ} {Cρ M1 : ℝ} {kn : ℕ → Euc d → ℝ} {k : Euc d → ℝ}

theorem sb1_k_abs_le' (hs0 : 0 ≤ s) (hk : Sb1KerU d s k) {z : Euc d} (hz : z ≠ 0) :
    |k z| ≤ |Whole.rieszKernel d s z| + Real.log (1 + ‖z‖) := by
  have hl := hk.lower z
  have hu := hk.upper z hz
  have hlog : 0 ≤ Real.log (1 + ‖z‖) := Real.log_nonneg (by linarith [norm_nonneg z])
  have hκ0 := sb1kap_nonneg s
  have hκ1 : sb1kap s ≤ 1 := by unfold sb1kap; split_ifs <;> norm_num
  have : sb1kap s * Real.log (1 + ‖z‖) ≤ Real.log (1 + ‖z‖) := by nlinarith
  rw [abs_le]
  constructor
  · nlinarith [abs_nonneg (Whole.rieszKernel d s z)]
  · nlinarith [le_abs_self (Whole.rieszKernel d s z)]

theorem sb1_riesz_abs_le (hs0 : 0 ≤ s) (z : Euc d) :
    |Whole.rieszKernel d s z| ≤ Whole.rieszKernel d s z + 2 * Real.log (1 + ‖z‖) := by
  have hlog : 0 ≤ Real.log (1 + ‖z‖) := Real.log_nonneg (by linarith [norm_nonneg z])
  unfold Whole.rieszKernel
  by_cases h0 : s = 0
  · simp only [h0, ite_true]
    rw [abs_le]
    constructor
    · by_cases hz : ‖z‖ = 0
      · simp [hz]
      · have hzp : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
        have : Real.log ‖z‖ ≤ Real.log (1 + ‖z‖) := Real.log_le_log hzp (by linarith)
        nlinarith
    · by_cases hz : ‖z‖ = 0
      · simp [hz]
      · have hzp : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
        have : Real.log ‖z‖ ≤ Real.log (1 + ‖z‖) := Real.log_le_log hzp (by linarith)
        nlinarith
  · simp only [h0, ite_false]
    rw [abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
    linarith

/-- the integrable majorant of the modulated energies -/
def sb1Bd (d : ℕ) (s CG M1 : ℝ) (N : ℕ) (X : Whole.EucConfig d N) : ℝ :=
  (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, Whole.rieszKernel d s (X i - X j) + 4 * ‖X‖ +
    (3 / 2) * CG + M1 / 2

theorem sb1_En_dom (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hN : 1 ≤ N) (hk : Sb1KerU d s k)
    (R : Sb1Rho ρ0 Cρ M1) (X : Whole.EucConfig d N) (hX : ∀ i j, i ≠ j → X i ≠ X j) :
    |sb1En k ρ0 X| ≤ sb1Bd d s (sb1CG d s Cρ M1) M1 N X := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hCG : 0 ≤ sb1CG d s Cρ M1 := sb1CG_nonneg R
  have hM1 := R.M1_nonneg
  have hXn : ∀ i, ‖X i‖ ≤ ‖X‖ := fun i => norm_le_pi_norm X i
  -- the pair part
  have hpair : ∀ i j, j ∈ Finset.univ.erase i →
      |k (X i - X j)| ≤ Whole.rieszKernel d s (X i - X j) + 6 * ‖X‖ := by
    intro i j hj
    have hz : X i - X j ≠ 0 := sub_ne_zero.2 (hX i j (Finset.ne_of_mem_erase hj).symm)
    have h1 := sb1_k_abs_le' hs0 hk hz
    have h2 := sb1_riesz_abs_le (d := d) hs0 (X i - X j)
    have h3 : Real.log (1 + ‖X i - X j‖) ≤ ‖X i - X j‖ := sb1_log_le_norm _
    have h4 : ‖X i - X j‖ ≤ 2 * ‖X‖ := by
      calc ‖X i - X j‖ ≤ ‖X i‖ + ‖X j‖ := norm_sub_le _ _
        _ ≤ ‖X‖ + ‖X‖ := add_le_add (hXn i) (hXn j)
        _ = 2 * ‖X‖ := by ring
    linarith
  have hS1 : |∑ i, ∑ j ∈ Finset.univ.erase i, k (X i - X j)| ≤
      ∑ i, ∑ j ∈ Finset.univ.erase i, (Whole.rieszKernel d s (X i - X j) + 6 * ‖X‖) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => hpair i j hj)
  have hcard : ∑ i : Fin N, ∑ _j ∈ Finset.univ.erase i, (6 * ‖X‖) ≤ (N : ℝ) ^ 2 * (6 * ‖X‖) := by
    have : ∀ i : Fin N, ∑ _j ∈ Finset.univ.erase i, (6 * ‖X‖) ≤ (N : ℝ) * (6 * ‖X‖) := fun i => by
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i)]
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
      nlinarith [norm_nonneg X]
    calc _ ≤ ∑ _i : Fin N, (N : ℝ) * (6 * ‖X‖) := Finset.sum_le_sum fun i _ => this i
      _ = (N : ℝ) ^ 2 * (6 * ‖X‖) := by simp; ring
  have hS1' : |∑ i, ∑ j ∈ Finset.univ.erase i, k (X i - X j)| ≤
      ∑ i, ∑ j ∈ Finset.univ.erase i, Whole.rieszKernel d s (X i - X j) + (N : ℝ) ^ 2 * (6 * ‖X‖) := by
    refine hS1.trans ?_
    simp only [Finset.sum_add_distrib]
    linarith
  -- the one-body part
  have hG : |∑ i, sb1G k ρ0 (X i)| ≤ N * (‖X‖ + sb1CG d s Cρ M1) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |sb1G k ρ0 (X i)| ≤ ∑ _i : Fin N, (‖X‖ + sb1CG d s Cρ M1) := Finset.sum_le_sum fun i _ => by
          have := sb1_G_abs_le hd hs0 hsd hk R (X i)
          have := sb1_log_le_norm (X i)
          have := hXn i
          linarith
      _ = N * (‖X‖ + sb1CG d s Cρ M1) := by simp; ring
  have hc := sb1_c_abs_le hd hs0 hsd hk R
  unfold sb1En sb1Bd
  have hA : 0 ≤ 1 / (2 * (N : ℝ) ^ 2) := by positivity
  have e1 : (1 / (2 * (N : ℝ) ^ 2)) * ((N : ℝ) ^ 2 * (6 * ‖X‖)) = 3 * ‖X‖ := by field_simp; ring
  have e2 : (1 / (N : ℝ)) * (N * (‖X‖ + sb1CG d s Cρ M1)) = ‖X‖ + sb1CG d s Cρ M1 := by field_simp
  calc |(1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, k (X i - X j) -
        (1 / (N : ℝ)) * ∑ i, sb1G k ρ0 (X i) + (1 / 2) * sb1c k ρ0|
      ≤ |(1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, k (X i - X j)| +
        |(1 / (N : ℝ)) * ∑ i, sb1G k ρ0 (X i)| + |(1 / 2) * sb1c k ρ0| := by
        refine (abs_add_le _ _).trans ?_
        refine add_le_add ((abs_sub _ _).trans ?_) le_rfl
        exact le_rfl
    _ ≤ (1 / (2 * (N : ℝ) ^ 2)) * (∑ i, ∑ j ∈ Finset.univ.erase i, Whole.rieszKernel d s (X i - X j) +
          (N : ℝ) ^ 2 * (6 * ‖X‖)) + (1 / (N : ℝ)) * (N * (‖X‖ + sb1CG d s Cρ M1)) +
        (1 / 2) * (M1 + sb1CG d s Cρ M1) := by
        rw [abs_mul, abs_of_nonneg hA, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ)),
          abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        gcongr
    _ = _ := by rw [mul_add, e1, e2]; ring

theorem sb1_integrable_norm (ν : Measure (Whole.EucConfig d N)) [IsProbabilityMeasure ν] (hmom : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂ν < ⊤) :
    Integrable (fun x : Whole.EucConfig d N => ‖x‖) ν := by
  have h2 : Integrable (fun x : Whole.EucConfig d N => ‖x‖ ^ 2) ν := by
    refine ⟨(measurable_norm.pow_const 2).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    refine lt_of_le_of_lt (le_of_eq ?_) hmom
    refine lintegral_congr fun x => ?_
    rw [Real.enorm_eq_ofReal (by positivity)]
  refine (h2.add (integrable_const (1 : ℝ))).mono' measurable_norm.aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (‖x‖ - 1)]

theorem sb1_Bd_int (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hN : 1 ≤ N) (R : Sb1Rho ρ0 Cρ M1)
    (ν : Measure (Whole.EucConfig d N)) [IsProbabilityMeasure ν] (hmom : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂ν < ⊤)
    (hEn : Integrable (sb1En (Whole.rieszKernel d s) ρ0 : Whole.EucConfig d N → ℝ) ν) :
    Integrable (sb1Bd d s (sb1CG d s Cρ M1) M1 N : Whole.EucConfig d N → ℝ) ν := by
  have hg := sb1KerU_riesz d s hs0
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hnorm := sb1_integrable_norm ν hmom
  have hGm : Measurable fun X : Whole.EucConfig d N => (1 / (N : ℝ)) * ∑ i, sb1G (Whole.rieszKernel d s) ρ0 (X i) :=
    (Finset.measurable_sum _ fun i _ => (sb1_G_meas hg R).comp (measurable_pi_apply i)).const_mul _
  have hGi : Integrable (fun X : Whole.EucConfig d N => (1 / (N : ℝ)) * ∑ i, sb1G (Whole.rieszKernel d s) ρ0 (X i)) ν := by
    refine (hnorm.add (integrable_const (sb1CG d s Cρ M1))).mono' hGm.aestronglyMeasurable
      (Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ))]
    have h1 : |∑ i, sb1G (Whole.rieszKernel d s) ρ0 (X i)| ≤ N * (‖X‖ + sb1CG d s Cρ M1) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i, |sb1G (Whole.rieszKernel d s) ρ0 (X i)| ≤ ∑ _i : Fin N, (‖X‖ + sb1CG d s Cρ M1) :=
            Finset.sum_le_sum fun i _ => by
              have := sb1_G_abs_le hd hs0 hsd hg R (X i)
              have := sb1_log_le_norm (X i)
              have := norm_le_pi_norm X i
              linarith
        _ = N * (‖X‖ + sb1CG d s Cρ M1) := by simp; ring
    calc 1 / (N : ℝ) * |∑ i, sb1G (Whole.rieszKernel d s) ρ0 (X i)| ≤ 1 / (N : ℝ) * (N * (‖X‖ + sb1CG d s Cρ M1)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ‖X‖ + sb1CG d s Cρ M1 := by field_simp
  have hid : (sb1Bd d s (sb1CG d s Cρ M1) M1 N : Whole.EucConfig d N → ℝ) = fun X =>
      (sb1En (Whole.rieszKernel d s) ρ0 X + (1 / (N : ℝ)) * ∑ i, sb1G (Whole.rieszKernel d s) ρ0 (X i) -
        (1 / 2) * sb1c (Whole.rieszKernel d s) ρ0) + 4 * ‖X‖ + (3 / 2) * sb1CG d s Cρ M1 + M1 / 2 := by
    funext X
    unfold sb1Bd sb1En
    ring
  rw [hid]
  exact ((((hEn.add hGi).sub (integrable_const _)).add (hnorm.const_mul 4)).add (integrable_const _)).add
    (integrable_const _)

theorem sb1_modGibbs_tilted (R : Sb1Rho ρ0 Cρ M1) {β : ℝ}
    (hK : 0 < Whole.gibbsNormalizer k N β (Whole.withDensityReal ρ0)) :
    Whole.modulatedGibbs k N β (Whole.withDensityReal ρ0) =
      (Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0).tilted
        (fun X : Whole.EucConfig d N => -β * N * Whole.modulatedEnergy k X (Whole.withDensityReal ρ0)) := by
  unfold Whole.modulatedGibbs Measure.tilted
  have hKdef : Whole.gibbsNormalizer k N β (Whole.withDensityReal ρ0) =
      ∫ x, Real.exp (-β * N * Whole.modulatedEnergy k x (Whole.withDensityReal ρ0))
        ∂(Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0) := rfl
  rw [hKdef] at hK ⊢
  set K := ∫ x, Real.exp (-β * N * Whole.modulatedEnergy k x (Whole.withDensityReal ρ0))
    ∂(Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0) with hKK
  have e : (fun x : Whole.EucConfig d N => ENNReal.ofReal
      (Real.exp (-β * N * Whole.modulatedEnergy k x (Whole.withDensityReal ρ0)) / K)) =
      (ENNReal.ofReal K)⁻¹ • fun x => ENNReal.ofReal
        (Real.exp (-β * N * Whole.modulatedEnergy k x (Whole.withDensityReal ρ0))) := by
    funext x
    rw [ENNReal.ofReal_div_of_pos hK]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [ENNReal.div_eq_inv_mul]
  rw [e, withDensity_smul' _ _ (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hK).ne')]

/-- **the entropy against a regularised Gibbs reference**: `H(ν|Q_k) = H(ν|μ^{⊗N}) + βN ∫ En_k dν + log K_k` -/
theorem sb1_kl_Q (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hN : 1 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    (hk : Sb1KerU d s k) (R : Sb1Rho ρ0 Cρ M1) {ν : Measure (Whole.EucConfig d N)} [IsProbabilityMeasure ν]
    (hν : relEntropy ν (Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0) ≠ ⊤)
    (hEn : Integrable (sb1En k ρ0 : Whole.EucConfig d N → ℝ) ν) :
    relEntropy ν (Whole.modulatedGibbs k N β (Whole.withDensityReal ρ0)) ≠ ⊤ ∧
      (relEntropy ν (Whole.modulatedGibbs k N β (Whole.withDensityReal ρ0))).toReal =
        (relEntropy ν (Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0)).toReal +
          β * N * ∫ X, sb1En k ρ0 X ∂ν + Real.log (Whole.gibbsNormalizer k N β (Whole.withDensityReal ρ0)) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ0) := HRS.MS.Thm.cb_withDensityReal_isProb R.dens
  have hK : 0 < Whole.gibbsNormalizer k N β (Whole.withDensityReal ρ0) := by
    rw [sb1_K_eq R]; exact sb1_Kpi_pos' hd hs0 hsd hN hβ hk R
  have hexp : Integrable (fun X : Whole.EucConfig d N =>
      Real.exp (-β * N * Whole.modulatedEnergy k X (Whole.withDensityReal ρ0)))
      (Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0) := by
    refine Integrable.of_bound (C := sb1CwR d s Cρ M1 β N)
      (Real.measurable_exp.comp ((sb1_measurable_modulatedEnergy hk.meas _).const_mul _)).aestronglyMeasurable
      (Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), sb1_modEnergy_eq R.dens]
    exact sb1_E_le hd hs0 hsd hN hβ hk R X
  have hfν : Integrable (fun X : Whole.EucConfig d N =>
      -β * N * Whole.modulatedEnergy k X (Whole.withDensityReal ρ0)) ν := by
    have : (fun X : Whole.EucConfig d N => -β * N * Whole.modulatedEnergy k X (Whole.withDensityReal ρ0)) =
        fun X => -β * N * sb1En k ρ0 X := funext fun X => by rw [sb1_modEnergy_eq R.dens]
    rw [this]; exact hEn.const_mul _
  obtain ⟨h1, h2⟩ := sb1_kl_tilted (Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0) ν hexp hfν
  rw [sb1_modGibbs_tilted R hK]
  simp only [relEntropy] at hν ⊢
  refine ⟨h1.2 hν, ?_⟩
  rw [h2 hν]
  have e1 : ∫ X, -β * N * Whole.modulatedEnergy k X (Whole.withDensityReal ρ0) ∂ν = -β * N * ∫ X, sb1En k ρ0 X ∂ν := by
    rw [integral_const_mul]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun X => (sb1_modEnergy_eq R.dens k X))
  rw [e1]
  have e2 : Real.log (∫ x, Real.exp (-β * N * Whole.modulatedEnergy k x (Whole.withDensityReal ρ0))
      ∂(Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0)) =
      Real.log (Whole.gibbsNormalizer k N β (Whole.withDensityReal ρ0)) := rfl
  rw [e2]
  ring

/-- **D07: convergence of the initial relative entropy** -/
theorem sb1_init_tendsto (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hN : 1 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    (hkn : ∀ n, Sb1KerU d s (kn n))
    (hconv : ∀ z, z ≠ 0 → Tendsto (fun n => kn n z) atTop (𝓝 (Whole.rieszKernel d s z))) (R : Sb1Rho ρ0 Cρ M1)
    {ν : Measure (Whole.EucConfig d N)} [IsProbabilityMeasure ν]
    (hν : relEntropy ν (Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0) ≠ ⊤)
    (hmom : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂ν < ⊤)
    (hEn : Integrable (sb1En (Whole.rieszKernel d s) ρ0 : Whole.EucConfig d N → ℝ) ν) :
    (∀ n, relEntropy ν (Whole.modulatedGibbs (kn n) N β (Whole.withDensityReal ρ0)) ≠ ⊤) ∧
      relEntropy ν (Whole.modulatedGibbs (Whole.rieszKernel d s) N β (Whole.withDensityReal ρ0)) ≠ ⊤ ∧
      Tendsto (fun n => (relEntropy ν (Whole.modulatedGibbs (kn n) N β (Whole.withDensityReal ρ0))).toReal) atTop
        (𝓝 (relEntropy ν (Whole.modulatedGibbs (Whole.rieszKernel d s) N β (Whole.withDensityReal ρ0))).toReal) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ0) := HRS.MS.Thm.cb_withDensityReal_isProb R.dens
  have hg := sb1KerU_riesz d s hs0
  have hae := HRS.MS.Wr.ae_injective_pi_Euc (N := N) (HRS.MS.Wr.wr12_atomless hd ρ0)
  have hνP : ν ≪ Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0 := (klDiv_ne_top_iff.1 hν).1
  have haeν := hνP.ae_le hae
  have hBd := sb1_Bd_int hd hs0 hsd hN R ν hmom hEn
  have hEnI : ∀ n, Integrable (sb1En (kn n) ρ0 : Whole.EucConfig d N → ℝ) ν := fun n =>
    hBd.mono' (sb1_En_meas (hkn n) R).aestronglyMeasurable (by
      filter_upwards [haeν] with X hX
      rw [Real.norm_eq_abs]
      exact sb1_En_dom hd hs0 hsd hN (hkn n) R X hX)
  have hint : Tendsto (fun n => ∫ X, sb1En (kn n) ρ0 X ∂ν) atTop (𝓝 (∫ X, sb1En (Whole.rieszKernel d s) ρ0 X ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence (sb1Bd d s (sb1CG d s Cρ M1) M1 N)
      (fun n => (sb1_En_meas (hkn n) R).aestronglyMeasurable) hBd (fun n => ?_) ?_
    · filter_upwards [haeν] with X hX
      rw [Real.norm_eq_abs]
      exact sb1_En_dom hd hs0 hsd hN (hkn n) R X hX
    · filter_upwards [haeν] with X hX
      exact sb1_En_tendsto hd hs0 hsd hkn hconv R X hX
  have hK := sb1_K_tendsto hd hs0 hsd hN hβ hkn hg hconv R (N := N)
  have hKpos := sb1_Kpi_pos' (N := N) hd hs0 hsd hN hβ hg R
  have hlogK : Tendsto (fun n => Real.log (∫ X : Whole.EucConfig d N, sb1FF (kn n) β N ρ0 X
      ∂(Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0))) atTop
      (𝓝 (Real.log (∫ X : Whole.EucConfig d N, sb1FF (Whole.rieszKernel d s) β N ρ0 X
        ∂(Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0)))) :=
    (Real.continuousAt_log hKpos.ne').tendsto.comp hK
  have hQ := fun n => sb1_kl_Q hd hs0 hsd hN hβ (hkn n) R hν (hEnI n)
  have hQg := sb1_kl_Q hd hs0 hsd hN hβ hg R hν hEn
  refine ⟨fun n => (hQ n).1, hQg.1, ?_⟩
  simp_rw [(hQ _).2]
  rw [hQg.2]
  simp_rw [sb1_K_eq R]
  exact (tendsto_const_nhds.add (hint.const_mul _)).add hlogK

end Init

end HRS.MS.MfeConf
