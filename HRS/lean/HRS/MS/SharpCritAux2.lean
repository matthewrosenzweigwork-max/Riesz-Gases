import HRS.MS.SharpCritAux1

/-!
# HRS.MS.SharpCritAux2 -- S7.8: abstract `L²` estimates
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction

noncomputable section

namespace HRS.Whole.S78

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The displayed `(∫⁻ ofReal|Z|² )^{1/2}` is the `L²` norm. -/
theorem s78_lhs_eq_eLpNorm (P : Measure Ω) {Z : Ω → ℝ} (hZ : AEStronglyMeasurable Z P) :
    (∫⁻ ω, ENNReal.ofReal |Z ω| ^ 2 ∂P) ^ (1 / 2 : ℝ) = eLpNorm Z 2 P := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hZ]
  simp only [ENNReal.toReal_ofNat, Real.enorm_eq_ofReal_abs, ENNReal.rpow_two]

/-- `‖a(Y - m₀) - c‖_{L²} ≤ |a| √Var Y + |a(E Y - m₀) - c|`. -/
theorem s78_eLpNorm_affine (P : Measure Ω) [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : AEStronglyMeasurable Y P) (a m0 c : ℝ) :
    eLpNorm (fun ω => a * (Y ω - m0) - c) 2 P ≤
      ENNReal.ofReal |a| * evariance Y P ^ (1 / 2 : ℝ) +
        ENNReal.ofReal |a * (∫ ω, Y ω ∂P - m0) - c| := by
  have h1 : (fun ω => a * (Y ω - m0) - c) =
      (a • fun ω => (Y ω - ∫ ω', Y ω' ∂P)) + fun _ => (a * (∫ ω', Y ω' ∂P - m0) - c) := by
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h1]
  refine (eLpNorm_add_le one_le_two).trans ?_
  gcongr
  · rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs]
    gcongr
    have hm : AEStronglyMeasurable (fun ω => Y ω - ∫ ω', Y ω' ∂P) P :=
      hY.sub aestronglyMeasurable_const
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hm]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, evariance]
    exact le_rfl
  · rw [eLpNorm_const _ two_ne_zero (IsProbabilityMeasure.ne_zero P)]
    simp [Real.enorm_eq_ofReal_abs]

/-! ### Euclidean specifics -/

section Euc

variable {d : ℕ} {s : ℝ}

/-- The canonical Gibbs law is a probability measure for every `N ≥ 1` (`d/2 < s < d`, `a, β > 0`). -/
theorem s78_isProb (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) {N : ℕ} (hN : 1 ≤ N) :
    IsProbabilityMeasure (canonicalGibbs (rieszKernel d s) (confinement a) N β) := by
  have hs0 : 0 < s := by
    have : (1 : ℝ) ≤ (d : ℝ) / 2 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    linarith
  obtain ⟨hprob, ⟨M, hM⟩, -, hcan, -⟩ := HRS.Whole.S71.sharp_bias_quadratic_proof hd hs hsd a β ha hβ
  rw [hcan N]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hW := HRS.Whole.S71.s71_gwd hd hs0 hsd hprob hM hβ.le n
  have : IsProbabilityMeasure (thermalMeasure d s a β) := HRS.MS.Wr.wr13a_isProb_density hprob
  exact HRS.MS.Wr.wr9_gibbs_prob (G := fun x y => rieszKernel d s (x - y)) hW

/-- `E[μ_N(f)] = m_N(f)` for an exchangeable law. -/
theorem s78_integral_linStat {N : ℕ} (hN : 1 ≤ N) {P : Measure (EucConfig d N)} [IsProbabilityMeasure P]
    (hP : IsExchangeable P) {f : Euc d → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    ∫ X, linStat f X ∂P = ∫ x, f x ∂(firstMarginal P) := by
  have hN' : 0 < N := hN
  have hex : HRS.External.Entropy.IsExchangeable P := fun σ => hP σ
  have hmarg : ∀ i : Fin N, ∫ X, f (X i) ∂P = ∫ x, f x ∂(firstMarginal P) := by
    intro i
    have h1 : P.map (fun X : EucConfig d N => X i) = firstMarginal P := by
      unfold firstMarginal
      rw [dif_pos hN']
      exact hex.marginal_eq i ⟨0, hN'⟩
    rw [← h1, integral_map (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable]
  have hint : ∀ i : Fin N, Integrable (fun X : EucConfig d N => f (X i)) P := by
    intro i
    refine Integrable.of_bound (hf.comp (measurable_pi_apply i)).aestronglyMeasurable B
      (ae_of_all _ fun X => ?_)
    rw [Real.norm_eq_abs]
    exact hB _
  have e : ∀ X : EucConfig d N, linStat f X = (N : ℝ)⁻¹ * ∑ i, f (X i) := fun X => pair_empirical hN' X f
  simp_rw [e]
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hint i)]
  simp_rw [hmarg]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (N : ℝ) ≠ 0 := by exact_mod_cast hN'.ne'
  field_simp

/-- `μ_N(f)` is measurable (`N ≥ 1`, `f` measurable). -/
theorem s78_measurable_linStat {N : ℕ} (hN : 1 ≤ N) {f : Euc d → ℝ} (hf : Measurable f) :
    Measurable (linStat (N := N) f) := by
  have hN' : 0 < N := hN
  have e : (linStat (N := N) f) = fun X : EucConfig d N => (N : ℝ)⁻¹ * ∑ i, f (X i) :=
    funext fun X => pair_empirical hN' X f
  rw [e]
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ => hf.comp (measurable_pi_apply i))

/-- `δ_N = N^{1-p}` for `d/2 < s` (reproof of the frozen auxiliary `deltaN_eq_bias`). -/
theorem s78_deltaN_eq (hs : (d : ℝ) / 2 < s) (N : ℕ) :
    deltaN d s N = (N : ℝ) ^ (1 - biasP d s) := by
  rw [deltaN_eq, if_neg (by linarith), if_neg (by linarith)]
  rfl

/-- `θ_{d,s} > 0` for `d/2 < s < d` (reproof of the frozen auxiliary `biasTheta_pos`). -/
theorem s78_biasTheta_pos (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) :
    0 < biasTheta d s := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by linarith
  have hp1 : 1 < biasP d s := by
    unfold biasP
    rw [lt_div_iff₀ hs0]
    linarith
  have hp2 : biasP d s < 2 := by
    unfold biasP
    rw [div_lt_iff₀ hs0]
    linarith
  have hp0 : 0 < biasP d s := by linarith
  unfold biasTheta
  refine lt_min (div_pos (by nlinarith) hp0) (lt_min (by linarith) (by positivity))

/-- Crude bound: a bounded function has `L²(P)` norm at most the bound (probability measure). -/
theorem s78_eLpNorm_le_bound (P : Measure Ω) [IsProbabilityMeasure P] {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f P) {B : ℝ} (hB : ∀ ω, |f ω| ≤ B) :
    eLpNorm f 2 P ≤ ENNReal.ofReal B := by
  have := eLpNorm_le_of_ae_bound (p := 2) (μ := P) hf (ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs]; exact hB ω)
  simpa using this

/-- `|μ_N(f)| ≤ B` if `|f| ≤ B` (`N ≥ 1`). -/
theorem s78_abs_linStat_le {N : ℕ} (hN : 1 ≤ N) {f : Euc d → ℝ} {B : ℝ} (hB : ∀ x, |f x| ≤ B)
    (X : EucConfig d N) : |linStat f X| ≤ B := by
  have hN' : 0 < N := hN
  rw [show linStat f X = (N : ℝ)⁻¹ * ∑ i, f (X i) from pair_empirical hN' X f]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN'
  rw [abs_mul, abs_of_pos (inv_pos.2 hNr)]
  have h1 : |∑ i, f (X i)| ≤ ∑ i : Fin N, B :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hB _)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  calc (N : ℝ)⁻¹ * |∑ i, f (X i)| ≤ (N : ℝ)⁻¹ * (N * B) :=
        mul_le_mul_of_nonneg_left h1 (inv_pos.2 hNr).le
    _ = B := by field_simp

/-- **Bias estimate** (from `sharp_bias_quadratic`): `|N^{p-1}(E μ_N(ρ) - μ(ρ)) - 2Aβ^pV_ρ| ≤ K N^{-θ}`. -/
theorem s78_bias_est (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ N : ℕ, 1 ≤ N →
      |(N : ℝ) ^ (biasP d s - 1) *
          (∫ X, linStat (thermalDensity d s a β) X ∂(canonicalGibbs (rieszKernel d s) (confinement a) N β) -
            pair (withDensityReal (thermalDensity d s a β)) (thermalDensity d s a β)) -
        2 * biasConst d s * β ^ biasP d s * scoreVariance d s β (thermalDensity d s a β)| ≤
      Kb * (N : ℝ) ^ (-biasTheta d s) := by
  have hs0 : 0 < s := by
    have : (1 : ℝ) ≤ (d : ℝ) / 2 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    linarith
  obtain ⟨hprob, ⟨M, hM⟩, -, hcan, Cb, hCb⟩ := HRS.Whole.S71.sharp_bias_quadratic_proof hd hs hsd a β ha hβ
  set ρ := thermalDensity d s a β with hρdef
  have hprobμ : IsProbabilityMeasure (withDensityReal ρ) := HRS.MS.Wr.wr13a_isProb_density hprob
  have hρm : Measurable ρ := hprob.measurable
  have hρb : ∀ x, |ρ x| ≤ M := fun x => by rw [abs_of_nonneg (hprob.nonneg x)]; exact hM x
  have hρL2 : MemLp ρ 2 (withDensityReal ρ) :=
    MemLp.of_bound hρm.aestronglyMeasurable M (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hρb x)
  set p := biasP d s with hp
  set θ := biasTheta d s with hθdef
  set V := scoreVariance d s β ρ with hV
  set c := 2 * biasConst d s * β ^ p * V with hc
  set K := l2Norm (withDensityReal ρ) (projMean (withDensityReal ρ) ρ) with hK
  set m0 := pair (withDensityReal ρ) ρ with hm0
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  set K2 : ℝ := |Cb| * K with hK2
  refine ⟨K2, mul_nonneg (abs_nonneg _) hK0, fun N hN1 => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hP : IsProbabilityMeasure (canonicalGibbs (rieszKernel d s) (confinement a) N β) :=
    s78_isProb hd hs hsd ha hβ hN1
  have hNθ : 0 ≤ (N : ℝ) ^ (-θ) := Real.rpow_nonneg hNpos.le _
  set P := canonicalGibbs (rieszKernel d s) (confinement a) N β with hPdef
  have hPm : P = modulatedGibbs (rieszKernel d s) N β (withDensityReal ρ) := hcan N
  have hexch : IsExchangeable P := by
    rw [hPm]
    exact modulatedGibbs_isExchangeable (rieszKernel d s) β _ (fun x => rieszKernel_neg x)
  have hbias := ((hCb N hN1).2.2.2 ρ hρL2).2
  have hE : ∫ X, linStat ρ X ∂P = ∫ x, ρ x ∂(firstMarginal P) :=
    s78_integral_linStat hN1 hexch hρm hρb
  have hE2 : ∫ X, linStat ρ X ∂P =
      ∫ x, ρ x ∂(firstMarginal (modulatedGibbs (rieszKernel d s) N β (withDensityReal ρ))) := by
    rw [← hPm]; exact hE
  have hδ : deltaN d s N = (N : ℝ) ^ (1 - p) := s78_deltaN_eq hs N
  have haδ : (N : ℝ) ^ (p - 1) * deltaN d s N = 1 := by
    rw [hδ, ← Real.rpow_add hNpos]
    simp
  have hapos : 0 < (N : ℝ) ^ (p - 1) := Real.rpow_pos_of_pos hNpos _
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  have hr : |(N : ℝ) ^ (p - 1) * (∫ X, linStat ρ X ∂P - m0) - c| ≤ K2 * (N : ℝ) ^ (-θ) := by
    have hX : (N : ℝ) ^ (p - 1) * (2 * biasConst d s * β ^ p * deltaN d s N * V) = c := by
      calc (N : ℝ) ^ (p - 1) * (2 * biasConst d s * β ^ p * deltaN d s N * V)
          = ((N : ℝ) ^ (p - 1) * deltaN d s N) * (2 * biasConst d s * β ^ p * V) := by ring
        _ = c := by rw [haδ, one_mul]
    have e1 : (N : ℝ) ^ (p - 1) * (∫ X, linStat ρ X ∂P - m0) - c =
        (N : ℝ) ^ (p - 1) * (∫ x, ρ x ∂(firstMarginal (modulatedGibbs (rieszKernel d s) N β (withDensityReal ρ))) -
          ∫ x, ρ x ∂(withDensityReal ρ) -
          2 * biasConst d s * β ^ p * deltaN d s N * V) := by
      rw [hE2]
      have : m0 = ∫ x, ρ x ∂(withDensityReal ρ) := rfl
      rw [this]
      linear_combination hX
    rw [e1, abs_mul, abs_of_pos hapos]
    calc (N : ℝ) ^ (p - 1) * |∫ x, ρ x ∂(firstMarginal (modulatedGibbs (rieszKernel d s) N β (withDensityReal ρ))) -
          ∫ x, ρ x ∂(withDensityReal ρ) - 2 * biasConst d s * β ^ p * deltaN d s N * V|
        ≤ (N : ℝ) ^ (p - 1) * (Cb * deltaN d s N * (N : ℝ) ^ (-θ) * K) :=
          mul_le_mul_of_nonneg_left hbias hapos.le
      _ = ((N : ℝ) ^ (p - 1) * deltaN d s N) * (Cb * K * (N : ℝ) ^ (-θ)) := by ring
      _ = Cb * K * (N : ℝ) ^ (-θ) := by rw [haδ, one_mul]
      _ ≤ K2 * (N : ℝ) ^ (-θ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hK0) hNθ
  exact hr

/-- **Core `L²` estimate** (`S:eq:supercritical-L2` with its rate): for `d/2 < s < d` and `ρ = ρ_β` the thermal
density, `‖N^{p-1}(μ_N(ρ) - μ(ρ)) - 2Aβ^p V_ρ‖_{L²(P_{N,β})} ≤ C (N^{p-3/2} + N^{-θ})` for every `N ≥ 1`.
Route (TeX S L6048-6055): `N^{p-1}√Var(μ_N(ρ)) ≤ C N^{p-3/2}` from `euc_static` (`N ≥ 2`), and
`N^{p-1}|m_N(ρ) - μ(ρ) - δ_N b(ρ)| ≤ C N^{-θ}` from `sharp_bias_quadratic` (`δ_N N^{p-1} = 1`);
`N = 1` by the crude bound. -/
theorem s78_core (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      eLpNorm (fun X : EucConfig d N => (N : ℝ) ^ (biasP d s - 1) *
          (linStat (thermalDensity d s a β) X - pair (withDensityReal (thermalDensity d s a β)) (thermalDensity d s a β)) -
        2 * biasConst d s * β ^ biasP d s * scoreVariance d s β (thermalDensity d s a β)) 2
        (canonicalGibbs (rieszKernel d s) (confinement a) N β) ≤
      ENNReal.ofReal (C * ((N : ℝ) ^ (biasP d s - 3 / 2) + (N : ℝ) ^ (-biasTheta d s))) := by
  have hs0 : 0 < s := by
    have : (1 : ℝ) ≤ (d : ℝ) / 2 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    linarith
  obtain ⟨hprob, ⟨M, hM⟩, -, hcan, Cb, hCb⟩ := HRS.Whole.S71.sharp_bias_quadratic_proof hd hs hsd a β ha hβ
  obtain ⟨Cv, hCv⟩ := HRS.MS.Wr.euc_static_proof hd hs0 hsd β β M hβ le_rfl
  obtain ⟨Kb, hKb0, hKb⟩ := s78_bias_est hd hs hsd ha hβ
  set ρ := thermalDensity d s a β with hρdef
  have hμ : thermalMeasure d s a β = withDensityReal ρ := rfl
  have hprobμ : IsProbabilityMeasure (withDensityReal ρ) := HRS.MS.Wr.wr13a_isProb_density hprob
  have hρm : Measurable ρ := hprob.measurable
  have hρb : ∀ x, |ρ x| ≤ M := fun x => by rw [abs_of_nonneg (hprob.nonneg x)]; exact hM x
  have hρL2 : MemLp ρ 2 (withDensityReal ρ) :=
    MemLp.of_bound hρm.aestronglyMeasurable M (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hρb x)
  set p := biasP d s with hp
  set θ := biasTheta d s with hθdef
  have hθ : 0 < θ := s78_biasTheta_pos hd hs hsd
  set V := scoreVariance d s β ρ with hV
  set c := 2 * biasConst d s * β ^ p * V with hc
  set I := ∫ x, ρ x ^ 2 ∂(withDensityReal ρ) with hI
  have hI0 : 0 ≤ I := integral_nonneg fun x => sq_nonneg _
  set K := l2Norm (withDensityReal ρ) (projMean (withDensityReal ρ) ρ) with hK
  set m0 := pair (withDensityReal ρ) ρ with hm0
  set K1 : ℝ := (|Cv| * I) ^ (1 / 2 : ℝ) with hK1
  set K2 : ℝ := Kb with hK2
  have hK1n : 0 ≤ K1 := Real.rpow_nonneg (mul_nonneg (abs_nonneg _) hI0) _
  have hK2n : 0 ≤ K2 := hKb0
  -- crude constant for `N = 1`
  set B1 : ℝ := M + |m0| + |c| with hB1
  refine ⟨max (max K1 K2) (B1 / 2), le_max_of_le_left (le_max_of_le_left hK1n), fun N hN1 => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hP : IsProbabilityMeasure (canonicalGibbs (rieszKernel d s) (confinement a) N β) :=
    s78_isProb hd hs hsd ha hβ hN1
  have hYm : Measurable (linStat (N := N) ρ) := s78_measurable_linStat hN1 hρm
  have hNθ : 0 ≤ (N : ℝ) ^ (-θ) := Real.rpow_nonneg hNpos.le _
  have hNp : 0 ≤ (N : ℝ) ^ (p - 3 / 2) := Real.rpow_nonneg hNpos.le _
  by_cases hN2 : 2 ≤ N
  · set P := canonicalGibbs (rieszKernel d s) (confinement a) N β with hPdef
    have hPm : P = modulatedGibbs (rieszKernel d s) N β (withDensityReal ρ) := hcan N
    have hexch : IsExchangeable P := by
      rw [hPm]
      exact modulatedGibbs_isExchangeable (rieszKernel d s) β _ (fun x => rieszKernel_neg x)
    have hvar : evariance (linStat (N := N) ρ) P ≤ ENNReal.ofReal (|Cv| / N * I) := by
      rw [hPm]
      refine ((hCv ρ hprob hM β ⟨le_rfl, le_rfl⟩ N hN2).2.1 ρ hρL2).trans (ENNReal.ofReal_le_ofReal ?_)
      have h1 : Cv / N ≤ |Cv| / N := div_le_div_of_nonneg_right (le_abs_self Cv) hNpos.le
      exact mul_le_mul_of_nonneg_right h1 hI0
    have hr : |(N : ℝ) ^ (p - 1) * (∫ X, linStat ρ X ∂P - m0) - c| ≤ K2 * (N : ℝ) ^ (-θ) :=
      hKb N hN1
    have hapos : 0 < (N : ℝ) ^ (p - 1) := Real.rpow_pos_of_pos hNpos _
    have hv : ENNReal.ofReal |(N : ℝ) ^ (p - 1)| * evariance (linStat (N := N) ρ) P ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (K1 * (N : ℝ) ^ (p - 3 / 2)) := by
      have hx0 : 0 ≤ |Cv| * I := mul_nonneg (abs_nonneg _) hI0
      have h1 : evariance (linStat (N := N) ρ) P ^ (1 / 2 : ℝ) ≤
          ENNReal.ofReal (|Cv| / N * I) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hvar (by norm_num)
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)] at h1
      calc ENNReal.ofReal |(N : ℝ) ^ (p - 1)| * evariance (linStat (N := N) ρ) P ^ (1 / 2 : ℝ)
          ≤ ENNReal.ofReal |(N : ℝ) ^ (p - 1)| * ENNReal.ofReal ((|Cv| / N * I) ^ (1 / 2 : ℝ)) := by gcongr
        _ = ENNReal.ofReal (|(N : ℝ) ^ (p - 1)| * (|Cv| / N * I) ^ (1 / 2 : ℝ)) :=
            (ENNReal.ofReal_mul (abs_nonneg _)).symm
        _ = ENNReal.ofReal (K1 * (N : ℝ) ^ (p - 3 / 2)) := by
            congr 1
            have e2 : |Cv| / N * I = (|Cv| * I) / N := by ring
            have e3 : p - 3 / 2 = (p - 1) - 1 / 2 := by ring
            rw [abs_of_pos hapos, e2, Real.div_rpow hx0 hNpos.le, e3, Real.rpow_sub hNpos (p - 1) (1 / 2)]
            simp only [hK1]
            ring
    have haff := s78_eLpNorm_affine P hYm.aestronglyMeasurable ((N : ℝ) ^ (p - 1)) m0 c
    refine haff.trans ?_
    refine (add_le_add hv (ENNReal.ofReal_le_ofReal hr)).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hC1 : K1 ≤ max (max K1 K2) (B1 / 2) := le_max_of_le_left (le_max_left _ _)
    have hC2 : K2 ≤ max (max K1 K2) (B1 / 2) := le_max_of_le_left (le_max_right _ _)
    calc K1 * (N : ℝ) ^ (p - 3 / 2) + K2 * (N : ℝ) ^ (-θ)
        ≤ max (max K1 K2) (B1 / 2) * (N : ℝ) ^ (p - 3 / 2) + max (max K1 K2) (B1 / 2) * (N : ℝ) ^ (-θ) :=
          add_le_add (mul_le_mul_of_nonneg_right hC1 hNp) (mul_le_mul_of_nonneg_right hC2 hNθ)
      _ = _ := by ring
  · obtain rfl : N = 1 := by omega
    have hb : ∀ X : EucConfig d 1, |(((1 : ℕ) : ℝ)) ^ (p - 1) * (linStat ρ X - m0) - c| ≤ B1 := by
      intro X
      have hY : |linStat (N := 1) ρ X| ≤ M := s78_abs_linStat_le (by omega) hρb X
      simp only [Nat.cast_one, Real.one_rpow, one_mul]
      calc |linStat ρ X - m0 - c| ≤ |linStat ρ X - m0| + |c| := abs_sub _ _
        _ ≤ (|linStat ρ X| + |m0|) + |c| := by gcongr; exact abs_sub _ _
        _ ≤ B1 := by rw [hB1]; linarith
    refine (s78_eLpNorm_le_bound _ (((measurable_const.mul ((hYm.sub_const m0))).sub_const c).aestronglyMeasurable) hb).trans ?_
    apply ENNReal.ofReal_le_ofReal
    simp only [Nat.cast_one, Real.one_rpow]
    have : B1 / 2 ≤ max (max K1 K2) (B1 / 2) := le_max_right _ _
    linarith

end Euc

/-! ### Slutsky for a deterministic shift (varying probability spaces) -/

section Shift

variable {ι : Type*}

/-- A bounded Lipschitz function composed with a translation is bounded and Lipschitz, so that
`g (x + a)` is a bounded continuous function of `x`. -/
theorem s78_norm_le {g : ℝ → ℝ} {C0 : ℝ} (hC0 : ∀ x y, dist (g x) (g y) ≤ C0) (x : ℝ) :
    ‖g x‖ ≤ ‖g 0‖ + C0 := by
  have h := hC0 x 0
  rw [Real.dist_eq] at h
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have := abs_sub_abs_le_abs_sub (g x) (g 0)
  linarith

/-- Slutsky for a convergent deterministic shift: if `T_N ⇒ ν` (weakly, on varying probability spaces)
and `b_N → c₀` then `T_N + b_N ⇒ ν(· + c₀)`, tested on bounded continuous `f`. -/
theorem s78_shift {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [hP : ∀ N, IsProbabilityMeasure (P N)] (T : ∀ N, Ω N → ℝ) (hT : ∀ N, Measurable (T N))
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : ∀ f : ℝ →ᵇ ℝ, Tendsto (fun N => ∫ ω, f (T N ω) ∂(P N)) atTop (𝓝 (∫ y, f y ∂ν)))
    (b : ℕ → ℝ) (c0 : ℝ) (hb : Tendsto b atTop (𝓝 c0)) (f : ℝ →ᵇ ℝ) :
    Tendsto (fun N => ∫ ω, f (T N ω + b N) ∂(P N)) atTop (𝓝 (∫ y, f (y + c0) ∂ν)) := by
  have hsh : ∀ a : ℝ, Measurable (fun x : ℝ => x + a) := fun a => measurable_id.add_const a
  have hTb : ∀ N, Measurable (fun ω => T N ω + b N) := fun N => (hT N).add_const _
  let PM : ℕ → ProbabilityMeasure ℝ := fun N => ⟨(P N).map (fun ω => T N ω + b N),
    (Measure.isProbabilityMeasure_map_iff (hTb N).aemeasurable).2 inferInstance⟩
  let PM0 : ProbabilityMeasure ℝ := ⟨ν.map (· + c0), (Measure.isProbabilityMeasure_map_iff (hsh c0).aemeasurable).2 inferInstance⟩
  have hTend : Tendsto PM atTop (𝓝 PM0) := by
    rw [tendsto_iff_forall_lipschitz_integral_tendsto]
    intro g ⟨C0, hC0⟩ ⟨L, hL⟩
    have hgc : Continuous g := hL.continuous
    let g0 : ℝ →ᵇ ℝ :=
      ⟨⟨fun x => g (x + c0), hgc.comp (continuous_id.add continuous_const)⟩, ⟨C0, fun x y => hC0 _ _⟩⟩
    have h0 : Tendsto (fun N => ∫ ω, g (T N ω + c0) ∂(P N)) atTop (𝓝 (∫ y, g (y + c0) ∂ν)) := h g0
    have hz : Tendsto (fun N => (L : ℝ) * dist (b N) c0) atTop (𝓝 0) := by
      have := (tendsto_iff_dist_tendsto_zero.1 hb).const_mul (L : ℝ)
      simpa using this
    change Tendsto (fun N => ∫ x, g x ∂((P N).map (fun ω => T N ω + b N))) atTop
      (𝓝 (∫ x, g x ∂(ν.map (· + c0))))
    have e1 : ∀ N, ∫ x, g x ∂((P N).map (fun ω => T N ω + b N)) = ∫ ω, g (T N ω + b N) ∂(P N) :=
      fun N => integral_map (hTb N).aemeasurable hgc.aestronglyMeasurable
    have e2 : ∫ x, g x ∂(ν.map (· + c0)) = ∫ y, g (y + c0) ∂ν :=
      integral_map (hsh c0).aemeasurable hgc.aestronglyMeasurable
    simp_rw [e1, e2]
    refine h0.congr_dist (squeeze_zero (fun _ => dist_nonneg) (fun N => ?_) hz)
    have hi : ∀ a : ℝ, Integrable (fun ω => g (T N ω + a)) (P N) := fun a =>
      Integrable.of_bound (hgc.measurable.comp ((hT N).add_const a)).aestronglyMeasurable
        (‖g 0‖ + C0) (Filter.Eventually.of_forall fun x => s78_norm_le hC0 _)
    rw [Real.dist_eq, ← integral_sub (hi c0) (hi (b N))]
    have := norm_integral_le_of_norm_le_const (μ := P N)
      (f := fun ω => g (T N ω + c0) - g (T N ω + b N)) (C := (L : ℝ) * dist (b N) c0)
      (Filter.Eventually.of_forall fun ω => by
        rw [← dist_eq_norm]
        refine (hL.dist_le_mul _ _).trans ?_
        rw [dist_add_left, dist_comm])
    simpa [Real.norm_eq_abs] using this
  have h1 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hTend) f
  have e1 : ∀ N, ∫ x, f x ∂((P N).map (fun ω => T N ω + b N)) = ∫ ω, f (T N ω + b N) ∂(P N) :=
    fun N => integral_map (hTb N).aemeasurable f.continuous.aestronglyMeasurable
  have e2 : ∫ x, f x ∂(ν.map (· + c0)) = ∫ y, f (y + c0) ∂ν :=
    integral_map (hsh c0).aemeasurable f.continuous.aestronglyMeasurable
  change Tendsto (fun N => ∫ x, f x ∂((P N).map (fun ω => T N ω + b N))) atTop
    (𝓝 (∫ x, f x ∂(ν.map (· + c0)))) at h1
  simp_rw [e1, e2] at h1
  exact h1

end Shift

/-! ### The `ℓ²` model of the scalar CLT: test functions, Gaussian, Lévy -/

theorem s78_cbBall {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] (L : H →L[ℝ] ℝ)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hb : ∀ j ≤ 2, ∀ y, ‖iteratedFDeriv ℝ j g y‖ ≤ 1) :
    (fun z : H => (1 + ‖L‖ + ‖L‖ ^ 2)⁻¹ * g (L z)) ∈ CbUnitBall H 2 := by
  set c : ℝ := 1 + ‖L‖ + ‖L‖ ^ 2 with hc
  have hc0 : 0 < c := by positivity
  have hLn : 0 ≤ ‖L‖ := norm_nonneg _
  have hG : ContDiff ℝ 2 (fun y : ℝ => c⁻¹ * g y) := contDiff_const.mul hg
  have hF : ContDiff ℝ 2 (fun z : H => c⁻¹ * g (L z)) := hG.comp L.contDiff
  have hj : ∀ j ≤ 2, ∀ z : H, ‖iteratedFDeriv ℝ j (fun z : H => c⁻¹ * g (L z)) z‖ ≤ c⁻¹ * ‖L‖ ^ j := by
    intro j hj z
    have e1 : (fun z : H => c⁻¹ * g (L z)) = (fun y : ℝ => c⁻¹ * g y) ∘ L := rfl
    rw [e1, L.iteratedFDeriv_comp_right hG z (by exact_mod_cast hj)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have e2 : iteratedFDeriv ℝ j (fun y : ℝ => c⁻¹ * g y) (L z) = c⁻¹ • iteratedFDeriv ℝ j g (L z) := by
      have h := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := c⁻¹) (f := g) (x := L z) (i := j)
        (hg.contDiffAt.of_le (by exact_mod_cast hj))
      simpa only [smul_eq_mul] using h
    rw [e2, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hc0)]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have := hb j hj (L z)
    calc c⁻¹ * ‖iteratedFDeriv ℝ j g (L z)‖ * ‖L‖ ^ j ≤ c⁻¹ * 1 * ‖L‖ ^ j := by gcongr
      _ = c⁻¹ * ‖L‖ ^ j := by ring
  refine ⟨hF, fun j hj' => ⟨c⁻¹ * ‖L‖ ^ j, ?_⟩, ?_⟩
  · rintro _ ⟨z, rfl⟩
    exact hj j hj' z
  · unfold cbNorm
    have hs : ∀ j ≤ 2, (⨆ z : H, ‖iteratedFDeriv ℝ j (fun z : H => c⁻¹ * g (L z)) z‖) ≤ c⁻¹ * ‖L‖ ^ j :=
      fun j hj' => ciSup_le fun z => hj j hj' z
    calc ∑ j ∈ Finset.range (2 + 1), (⨆ z : H, ‖iteratedFDeriv ℝ j (fun z : H => c⁻¹ * g (L z)) z‖)
        ≤ ∑ j ∈ Finset.range (2 + 1), c⁻¹ * ‖L‖ ^ j :=
          Finset.sum_le_sum fun j hj' => hs j (by simpa [Nat.lt_succ_iff] using hj')
      _ = 1 := by
          simp only [Finset.sum_range_succ, Finset.sum_range_zero]
          field_simp
          ring

theorem s78_cos_bound : ∀ j ≤ 2, ∀ y : ℝ, ‖iteratedFDeriv ℝ j Real.cos y‖ ≤ 1 := by
  intro j hj y
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  interval_cases j
  · simpa using Real.abs_cos_le_one y
  · simpa [iteratedDeriv_one, Real.deriv_cos] using Real.abs_sin_le_one y
  · have : iteratedDeriv 2 Real.cos = fun x => -Real.cos x := by
      rw [iteratedDeriv_succ, iteratedDeriv_one, Real.deriv_cos']
      funext x
      simp
    rw [this]
    simpa using Real.abs_cos_le_one y

theorem s78_sin_bound : ∀ j ≤ 2, ∀ y : ℝ, ‖iteratedFDeriv ℝ j Real.sin y‖ ≤ 1 := by
  intro j hj y
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  interval_cases j
  · simpa using Real.abs_sin_le_one y
  · simpa [iteratedDeriv_one, Real.deriv_sin] using Real.abs_cos_le_one y
  · have : iteratedDeriv 2 Real.sin = fun x => -Real.sin x := by
      rw [iteratedDeriv_succ, iteratedDeriv_one, Real.deriv_sin]
      funext x
      simp
    rw [this]
    simpa using Real.abs_sin_le_one y

/-- The first basis vector of `ℓ²`. -/
def s78_e0 : SeqL2 := (lp.single 2 0 (1 : ℝ) : lp (fun _ : ℕ => ℝ) 2)

/-- `x ↦ x e₀`. -/
def s78_E : ℝ →L[ℝ] SeqL2 := ContinuousLinearMap.toSpanSingleton ℝ s78_e0

theorem s78_E_apply (x : ℝ) : s78_E x = x • s78_e0 := rfl

theorem s78_coord_e0 (i : ℕ) : SeqL2.coord s78_e0 i = if i = 0 then 1 else 0 := by
  unfold SeqL2.coord s78_e0
  rw [lp.single_apply]
  by_cases h : i = 0
  · subst h; simp
  · simp [h]

theorem s78_coord_E (x : ℝ) (i : ℕ) : SeqL2.coord (s78_E x) i = x * (if i = 0 then 1 else 0) := by
  rw [s78_E_apply, ← s78_coord_e0]
  rfl

theorem s78_norm_e0 : ‖s78_e0‖ = 1 := by
  have h : ‖s78_e0‖ = ‖(lp.single 2 0 (1 : ℝ) : lp (fun _ : ℕ => ℝ) 2)‖ := rfl
  rw [h, lp.norm_single (by norm_num)]
  simp

theorem s78_inner_e0 (z : SeqL2) : inner ℝ s78_e0 z = SeqL2.coord z 0 := by
  have h := lp.inner_single_left (𝕜 := ℝ) (G := fun _ : ℕ => ℝ) (0 : ℕ) (1 : ℝ)
    (show lp (fun _ : ℕ => ℝ) 2 from z)
  refine h.trans ?_
  simp [SeqL2.coord]


theorem s78_coord_eq_inner (i : ℕ) (z : SeqL2) :
    SeqL2.coord z i = inner ℝ ((lp.single 2 i (1 : ℝ) : lp (fun _ : ℕ => ℝ) 2) : SeqL2) z := by
  have h := lp.inner_single_left (𝕜 := ℝ) (G := fun _ : ℕ => ℝ) i (1 : ℝ)
    (show lp (fun _ : ℕ => ℝ) 2 from z)
  refine Eq.trans ?_ h.symm
  simp [SeqL2.coord]

theorem s78_measurable_coord (i : ℕ) : Measurable fun z : SeqL2 => SeqL2.coord z i := by
  have : (fun z : SeqL2 => SeqL2.coord z i) =
      fun z : SeqL2 => inner ℝ ((lp.single 2 i (1 : ℝ) : lp (fun _ : ℕ => ℝ) 2) : SeqL2) z :=
    funext fun z => s78_coord_eq_inner i z
  rw [this]
  exact (continuous_const.inner continuous_id).measurable

/-- The centered Gaussian on `ℓ²` supported on the first axis, variance `v`. -/
def s78_gamma (v : ℝ≥0) : Measure SeqL2 := (gaussianReal 0 v).map s78_E

theorem s78_gamma_centered (v : ℝ≥0) : IsCenteredGaussian (s78_gamma v) := by
  refine ⟨isGaussian_map s78_E, fun L => ?_⟩
  unfold s78_gamma
  rw [integral_map s78_E.continuous.measurable.aemeasurable L.continuous.aestronglyMeasurable]
  have : ∀ x, L (s78_E x) = x * L s78_e0 := fun x => by rw [s78_E_apply, map_smul, smul_eq_mul]
  simp_rw [this]
  rw [integral_mul_const, integral_id_gaussianReal]
  simp

theorem s78_gamma_cov (v : ℝ≥0) (i j : ℕ) :
    Integrable (fun z => SeqL2.coord z i * SeqL2.coord z j) (s78_gamma v) ∧
      ∫ z, SeqL2.coord z i * SeqL2.coord z j ∂(s78_gamma v) = if i = 0 ∧ j = 0 then (v : ℝ) else 0 := by
  have hm : AEStronglyMeasurable (fun z => SeqL2.coord z i * SeqL2.coord z j) (s78_gamma v) :=
    ((s78_measurable_coord i).mul (s78_measurable_coord j)).aestronglyMeasurable
  have e : ∀ x : ℝ, SeqL2.coord (s78_E x) i * SeqL2.coord (s78_E x) j =
      x ^ 2 * ((if i = 0 then (1 : ℝ) else 0) * (if j = 0 then (1 : ℝ) else 0)) := fun x => by
    rw [s78_coord_E, s78_coord_E]; ring
  have hint : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) := by
    have := (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
    simpa using this
  have hsq : ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 v) = v := by
    have h1 := variance_id_gaussianReal (μ := (0 : ℝ)) (v := v)
    rw [variance_eq_integral measurable_id.aemeasurable] at h1
    simpa [integral_id_gaussianReal] using h1
  unfold s78_gamma
  constructor
  · rw [integrable_map_measure hm s78_E.continuous.measurable.aemeasurable]
    simp_rw [Function.comp_def, e]
    exact hint.mul_const _
  · rw [integral_map s78_E.continuous.measurable.aemeasurable hm]
    simp_rw [e]
    rw [integral_mul_const, hsq]
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj]


theorem s78_charFun_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : Measurable X) (t : ℝ) :
    charFun (P.map X) t = ((∫ ω, Real.cos (t * X ω) ∂P : ℝ) : ℂ) +
      ((∫ ω, Real.sin (t * X ω) ∂P : ℝ) : ℂ) * Complex.I := by
  have hcont : Continuous (fun x : ℝ => Complex.exp (↑t * ↑x * Complex.I)) := by fun_prop
  have h2 : ∫ x : ℝ, Complex.exp (↑t * ↑x * Complex.I) ∂(P.map X) =
      ∫ ω, Complex.exp (↑t * ↑(X ω) * Complex.I) ∂P :=
    integral_map hX.aemeasurable hcont.aestronglyMeasurable
  rw [charFun_apply_real, h2]
  have hmt : Measurable (fun ω => t * X ω) := hX.const_mul t
  have hmc : Measurable (fun ω => Real.cos (t * X ω)) := Real.continuous_cos.measurable.comp hmt
  have hms : Measurable (fun ω => Real.sin (t * X ω)) := Real.continuous_sin.measurable.comp hmt
  have hc : Integrable (fun ω => Real.cos (t * X ω)) P :=
    Integrable.of_bound hmc.aestronglyMeasurable 1
      (ae_of_all _ fun ω => by simpa using Real.abs_cos_le_one (t * X ω))
  have hs : Integrable (fun ω => Real.sin (t * X ω)) P :=
    Integrable.of_bound hms.aestronglyMeasurable 1
      (ae_of_all _ fun ω => by simpa using Real.abs_sin_le_one (t * X ω))
  have e : ∀ ω, Complex.exp (↑t * ↑(X ω) * Complex.I) =
      ((Real.cos (t * X ω) : ℝ) : ℂ) + ((Real.sin (t * X ω) : ℝ) : ℂ) * Complex.I := by
    intro ω
    rw [← Complex.ofReal_mul, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp_rw [e]
  rw [integral_add (hc.ofReal) (hs.ofReal.mul_const _), integral_mul_const, integral_complex_ofReal, integral_complex_ofReal]


/-- Weak convergence on `ℝ` from convergence of the trigonometric moments (Lévy). -/
theorem s78_weak_of_trig {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] (T : ∀ n, Ω n → ℝ) (hT : ∀ n, Measurable (T n))
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hcos : ∀ t : ℝ, ∀ n, |∫ ω, Real.cos (t * T n ω) ∂(P n) - ∫ y, Real.cos (t * y) ∂ν| ≤
      (1 + |t| + t ^ 2) * ε n)
    (hsin : ∀ t : ℝ, ∀ n, |∫ ω, Real.sin (t * T n ω) ∂(P n) - ∫ y, Real.sin (t * y) ∂ν| ≤
      (1 + |t| + t ^ 2) * ε n) (f : ℝ →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, f (T n ω) ∂(P n)) atTop (𝓝 (∫ y, f y ∂ν)) := by
  have hchar : ∀ t : ℝ, Tendsto (fun n => charFun ((P n).map (T n)) t) atTop (𝓝 (charFun (ν.map id) t)) := by
    intro t
    have hz : Tendsto (fun n => (1 + |t| + t ^ 2) * ε n) atTop (𝓝 0) := by
      simpa using hε.const_mul (1 + |t| + t ^ 2)
    have hc : Tendsto (fun n => ∫ ω, Real.cos (t * T n ω) ∂(P n)) atTop (𝓝 (∫ y, Real.cos (t * y) ∂ν)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero_norm' (Filter.Eventually.of_forall fun n => by
        simpa [Real.dist_eq] using hcos t n) hz
    have hs : Tendsto (fun n => ∫ ω, Real.sin (t * T n ω) ∂(P n)) atTop (𝓝 (∫ y, Real.sin (t * y) ∂ν)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero_norm' (Filter.Eventually.of_forall fun n => by
        simpa [Real.dist_eq] using hsin t n) hz
    have e1 := fun n => s78_charFun_eq (P n) (hT n) t
    have e2 := s78_charFun_eq ν (measurable_id : Measurable (id : ℝ → ℝ)) t
    simp_rw [e1, e2]
    exact ((Complex.continuous_ofReal.tendsto _).comp hc).add
      (((Complex.continuous_ofReal.tendsto _).comp hs).mul_const _)
  have hX : ∀ n, AEMeasurable (T n) (P n) := fun n => (hT n).aemeasurable
  have hX' : AEMeasurable (id : ℝ → ℝ) ν := measurable_id.aemeasurable
  have h := TendstoInDistribution.of_tendsto_charFun hX hX' hchar
  exact (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ hX hX').1 h f


theorem s78_inner_E (t x : ℝ) : inner ℝ (t • s78_e0) (s78_E x) = t * x := by
  rw [s78_E_apply, inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq, s78_norm_e0]
  simp

theorem s78_norm_Lt (t : ℝ) : ‖innerSL ℝ (t • s78_e0)‖ = |t| := by
  rw [innerSL_apply_norm, norm_smul, s78_norm_e0, Real.norm_eq_abs, mul_one]

/-- Transfer of the `C_b²` distance bound to a trigonometric moment on the first axis. -/
instance s78_gamma_prob (v : ℝ≥0) : IsProbabilityMeasure (s78_gamma v) :=
  (Measure.isProbabilityMeasure_map_iff s78_E.continuous.measurable.aemeasurable).2 inferInstance

theorem s78_trig_dist {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    {T : Ω → ℝ} (hT : Measurable T) (v : ℝ≥0) {ε : ℝ} {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hb : ∀ j ≤ 2, ∀ y, ‖iteratedFDeriv ℝ j g y‖ ≤ 1) (hsm : smoothDist 2 (Q.map fun ω => s78_E (T ω)) (s78_gamma v) ≤ ε) (t : ℝ) :
    |∫ ω, g (t * T ω) ∂Q - ∫ y, g (t * y) ∂(gaussianReal 0 v)| ≤ (1 + |t| + t ^ 2) * ε := by
  set L : SeqL2 →L[ℝ] ℝ := innerSL ℝ (t • s78_e0) with hL
  have hLn : ‖L‖ = |t| := s78_norm_Lt t
  set c : ℝ := 1 + |t| + t ^ 2 with hc
  have hc0 : 0 < c := by positivity
  have hΦ := s78_cbBall L hg hb
  rw [hLn, sq_abs] at hΦ
  have hLE : ∀ x, L (s78_E x) = t * x := fun x => s78_inner_E t x
  have hF : Measurable fun ω => s78_E (T ω) := s78_E.continuous.measurable.comp hT
  have hcont : Continuous fun z : SeqL2 => c⁻¹ * g (L z) := hΦ.1.continuous
  have h1 := abs_integral_sub_le_smoothDist hΦ (Q.map fun ω => s78_E (T ω)) (s78_gamma v)
  have e1 : ∫ z, c⁻¹ * g (L z) ∂(Q.map fun ω => s78_E (T ω)) = c⁻¹ * ∫ ω, g (t * T ω) ∂Q := by
    rw [integral_map hF.aemeasurable hcont.aestronglyMeasurable]
    simp_rw [hLE]
    rw [integral_const_mul]
  have e2 : ∫ z, c⁻¹ * g (L z) ∂(s78_gamma v) = c⁻¹ * ∫ y, g (t * y) ∂(gaussianReal 0 v) := by
    unfold s78_gamma
    rw [integral_map s78_E.continuous.measurable.aemeasurable hcont.aestronglyMeasurable]
    simp_rw [hLE]
    rw [integral_const_mul]
  rw [e1, e2, ← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hc0)] at h1
  have h2 := h1.trans hsm
  have h3 : |∫ ω, g (t * T ω) ∂Q - ∫ y, g (t * y) ∂(gaussianReal 0 v)| ≤ c * ε := by
    have := (mul_le_mul_of_nonneg_left h2 hc0.le)
    rwa [← mul_assoc, mul_inv_cancel₀ hc0.ne', one_mul] at this
  exact h3

end HRS.Whole.S78
