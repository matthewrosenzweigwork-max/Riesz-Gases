import HRS.MS.ShiftFldAux2

/-!
# S79: the deterministic shift `sqrt N (m_N - mu) - N^{3/2-p} b` in `B_m`

From the sharp bias estimate (`SharpBiasConclusion`, S7.1) and `s79_bias_vec_bound`:
`||sqrt N (m_N - mu) - N^{3/2-p} b_{beta,mu}||_{B_m} <= K C_b N^{3/2-p-theta}` for `d/2 < s < d`, `m > d`,
`N >= 2`, where `K` depends only on `d, m` (`S:eq:field-bias-remainder`, S L6178-6183).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Whole.S79

open HRS (Euc)

variable {d : ℕ} {s : ℝ}

theorem s79_l2Norm_const_mul (μ : Measure (Euc d)) (c : ℝ) (f : Euc d → ℝ) :
    l2Norm μ (fun x => c * f x) = |c| * l2Norm μ f := by
  unfold l2Norm
  have : ∫ x, (c * f x) ^ 2 ∂μ = c ^ 2 * ∫ x, f x ^ 2 ∂μ := by
    simp_rw [mul_pow]; exact integral_const_mul _ _
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

theorem s79_deltaN_pos (hs : (d : ℝ) / 2 < s) {N : ℕ} (hN : 1 ≤ N) : 0 < deltaN d s N := by
  rw [HRS.Whole.S78.s78_deltaN_eq hs]
  exact Real.rpow_pos_of_pos (by exact_mod_cast hN) _

theorem s79_sqrt_mul_deltaN (hs : (d : ℝ) / 2 < s) {N : ℕ} (hN : 1 ≤ N) :
    Real.sqrt N * deltaN d s N = (N : ℝ) ^ (3 / 2 - biasP d s) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [HRS.Whole.S78.s78_deltaN_eq hs, Real.sqrt_eq_rpow, ← Real.rpow_add hN']
  congr 1; ring

theorem s79_shift_bound (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) {m : ℝ}
    (hmd : (d : ℝ) < m) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (β : ℝ) (ρ : Euc d → ℝ), IsProbDensity ρ → ∀ (N : ℕ), 2 ≤ N →
      ∀ Cb : ℝ, SharpBiasConclusion d s N β ρ Cb →
      ‖Real.sqrt N • OscDual.ofMeasureDiff m
          (firstMarginal (modulatedGibbs (rieszKernel d s) N β (withDensityReal ρ)))
          (withDensityReal ρ) -
        (N : ℝ) ^ (3 / 2 - biasP d s) • biasField m d s β ρ‖ ≤
        K * max Cb 0 * (N : ℝ) ^ (3 / 2 - biasP d s - biasTheta d s) := by
  obtain ⟨K, hK0, hK⟩ := s79_bias_vec_bound (d := d) hmd
  refine ⟨K, hK0, fun β ρ hρ N hN Cb hSB => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  obtain ⟨-, hRP, ⟨φ, hφm, hφ0, hmarg, hMem, hl2⟩, -⟩ := hSB
  haveI : IsProbabilityMeasure (withDensityReal ρ) := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  set δ := deltaN d s N with hδdef
  have hδ : 0 < δ := s79_deltaN_pos hs hN1
  have hbd : MemLp (biasDensity d s β ρ) 2 (withDensityReal ρ) :=
    hRP.const_mul (2 * biasConst d s * β ^ biasP d s)
  have hfun : (fun x => φ x - 1 - δ * biasDensity d s β ρ x) =
      fun x => δ * ((φ x - 1) / δ - biasDensity d s β ρ x) := by
    funext x; field_simp
  have hr : MemLp (fun x => φ x - 1 - δ * biasDensity d s β ρ x) 2 (withDensityReal ρ) := by
    rw [hfun]; exact hMem.const_mul δ
  have hvec := hK ρ (biasDensity d s β ρ) φ δ hρ hφm hφ0 hbd hr
  rw [hfun, s79_l2Norm_const_mul, abs_of_pos hδ] at hvec
  rw [hmarg]
  have hθ := HRS.Whole.S78.s78_biasTheta_pos hd hs hsd
  have hnt : 0 < (N : ℝ) ^ (-biasTheta d s) := Real.rpow_pos_of_pos hN0 _
  have hl2' : l2Norm (withDensityReal ρ) (fun x => (φ x - 1) / δ - biasDensity d s β ρ x) ≤
      max Cb 0 * (N : ℝ) ^ (-biasTheta d s) :=
    hl2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hnt.le)
  have e : (N : ℝ) ^ (3 / 2 - biasP d s) = Real.sqrt N * δ := (s79_sqrt_mul_deltaN hs hN1).symm
  have hsq : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  rw [e, mul_smul, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hsq]
  have hv2 : ‖OscDual.ofMeasureDiff m ((withDensityReal ρ).withDensity fun x => ENNReal.ofReal (φ x))
      (withDensityReal ρ) - δ • biasField m d s β ρ‖ ≤ K * (δ * (max Cb 0 * (N : ℝ) ^ (-biasTheta d s))) :=
    hvec.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hl2' hδ.le) hK0)
  have e2 : (N : ℝ) ^ (3 / 2 - biasP d s - biasTheta d s) =
      (Real.sqrt N * δ) * (N : ℝ) ^ (-biasTheta d s) := by
    rw [← e, ← Real.rpow_add hN0]; congr 1
  calc Real.sqrt N * ‖_‖ ≤ Real.sqrt N * (K * (δ * (max Cb 0 * (N : ℝ) ^ (-biasTheta d s)))) :=
        mul_le_mul_of_nonneg_left hv2 hsq
    _ = K * max Cb 0 * (N : ℝ) ^ (3 / 2 - biasP d s - biasTheta d s) := by rw [e2]; ring

end HRS.Whole.S79
