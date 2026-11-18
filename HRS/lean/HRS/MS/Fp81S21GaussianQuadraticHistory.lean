import HRS.MS.Fp81S21GaussianQuadraticChaos
import HRS.MS.Fp81S21GaussianQuadraticChaos2

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal
open HRS HRS.MC.E213U13

namespace HRS.Fp81.S21

/-- The scalar L² second-chaos closure has finite polynomial approximants
in the retained Gaussian sequence. -/
theorem fp81s21_InQ2_L2_polynomials
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ)
    {Y : Ω → ℝ} (hY : InQ2 hξ Y) :
    ∃ (N : ℕ → ℕ) (c : ℕ → ℕ → ℕ → ℝ),
      Tendsto (fun n => eLpNorm (fun ω => quadSum (c n) ξ (N n) ω - Y ω) 2 P)
        atTop (𝓝 0) := by
  classical
  obtain ⟨hmem, hclosed⟩ := hY
  have hex : ∀ n : ℕ, ∃ k, ∃ x ∈ K2 hξ k,
      dist x (hmem.toLp Y) < 1 / (n + 1 : ℝ) := by
    intro n
    exact (mem_Qc_iff (K2_mono hξ)).1 hclosed _ (by positivity)
  choose N x hx hdist using hex
  have hp : ∀ n, ∃ c, (x n : Ω → ℝ) =ᵐ[P] quadSum c ξ (N n) := by
    intro n
    obtain ⟨c, hc⟩ := K2_poly hξ (x n) (hx n)
    refine ⟨c, hc.trans ?_⟩
    exact Filter.Eventually.of_forall fun ω => by
      simp only [quadSum, smul_eq_mul, mul_comm]
  choose c hc using hp
  refine ⟨N, c, ?_⟩
  have hd : Tendsto (fun n : ℕ => dist (x n) (hmem.toLp Y)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => dist_nonneg) (fun n => (hdist n).le) ?_
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have he : Tendsto (fun n : ℕ => ENNReal.ofReal (dist (x n) (hmem.toLp Y))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hd
  refine he.congr fun n => ?_
  rw [← eLpNorm_sub_eq_dist (x n) hmem]
  apply eLpNorm_congr_ae
  filter_upwards [hc n] with ω hω
  simp only [Pi.sub_apply, hω]

/-- A sharp fourth-moment estimate passes to an L² limit, including
finiteness of its fourth moment. -/
theorem fp81s21_fourth_limit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Qn : ℕ → Ω → ℝ} {Q : Ω → ℝ}
    (hQ : MemLp Q 2 P) (hm : ∀ n, MemLp (Qn n) 2 P)
    (ht : Tendsto (fun n => eLpNorm (fun ω => Qn n ω - Q ω) 2 P) atTop (𝓝 0))
    (hf : ∀ n, Integrable (fun ω => Qn n ω ^ 4) P ∧
      (∫ ω, Qn n ω ^ 4 ∂P) ≤ 15 * (∫ ω, Qn n ω ^ 2 ∂P) ^ 2) :
    MemLp Q 4 P ∧ (∫ ω, Q ω ^ 4 ∂P) ≤ 15 * (∫ ω, Q ω ^ 2 ∂P) ^ 2 := by
  have ht' : Tendsto (fun n => eLpNorm (Qn n - Q) 2 P) atTop (𝓝 0) := ht
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' Qn hm Q hQ).2 ht'
  have hsq : Tendsto (fun n => ∫ ω, Qn n ω ^ 2 ∂P) atTop
      (𝓝 (∫ ω, Q ω ^ 2 ∂P)) := by
    have hnorm := ((continuous_norm.tendsto (hQ.toLp Q)).comp hLp).pow 2
    have heq (n : ℕ) : ‖(hm n).toLp (Qn n)‖ ^ 2 = ∫ ω, Qn n ω ^ 2 ∂P := by
      rw [Lp2_norm_sq]
      exact integral_congr_ae (by filter_upwards [(hm n).coeFn_toLp] with ω hω; rw [hω])
    have heq' : ‖hQ.toLp Q‖ ^ 2 = ∫ ω, Q ω ^ 2 ∂P := by
      rw [Lp2_norm_sq]
      exact integral_congr_ae (by filter_upwards [hQ.coeFn_toLp] with ω hω; rw [hω])
    simpa only [Function.comp_def, heq, heq'] using hnorm
  have hin := tendstoInMeasure_of_tendsto_eLpNorm (p := 2) two_ne_zero ht
  obtain ⟨ns, hns, hae⟩ := hin.exists_seq_tendsto_ae
  have hc : Continuous fun x : ℝ => ENNReal.ofReal (x ^ 4) :=
    ENNReal.continuous_ofReal.comp (continuous_pow 4)
  have hkey : ∫⁻ ω, ENNReal.ofReal (Q ω ^ 4) ∂P ≤
      ENNReal.ofReal (15 * (∫ ω, Q ω ^ 2 ∂P) ^ 2) := by
    calc
      ∫⁻ ω, ENNReal.ofReal (Q ω ^ 4) ∂P =
          ∫⁻ ω, liminf (fun n => ENNReal.ofReal (Qn (ns n) ω ^ 4)) atTop ∂P := by
            refine lintegral_congr_ae ?_
            filter_upwards [hae] with ω hω
            exact (((hc.tendsto _).comp hω).liminf_eq).symm
      _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (Qn (ns n) ω ^ 4) ∂P) atTop :=
        lintegral_liminf_le' fun n => (((hm _).aestronglyMeasurable.pow 4).aemeasurable).ennreal_ofReal
      _ ≤ liminf (fun n => ENNReal.ofReal (15 * (∫ ω, Qn (ns n) ω ^ 2 ∂P) ^ 2)) atTop := by
        apply liminf_le_liminf
        · filter_upwards [] with n
          rw [← ofReal_integral_eq_lintegral_ofReal (hf _).1 (Eventually.of_forall fun ω => by positivity)]
          exact ENNReal.ofReal_le_ofReal (hf _).2
        · exact Filter.isBoundedUnder_of ⟨(0 : ℝ≥0∞), fun _ => bot_le⟩
        · exact Filter.IsCoboundedUnder.of_frequently_le (a := (⊤ : ℝ≥0∞)) (.of_forall fun _ => le_top)
      _ = _ := by
        have h : Tendsto (fun n => ENNReal.ofReal (15 * (∫ ω, Qn (ns n) ω ^ 2 ∂P) ^ 2)) atTop
            (𝓝 (ENNReal.ofReal (15 * (∫ ω, Q ω ^ 2 ∂P) ^ 2))) :=
          ENNReal.tendsto_ofReal (tendsto_const_nhds.mul ((hsq.comp hns.tendsto_atTop).pow 2))
        exact h.liminf_eq
  have hi : Integrable (fun ω => Q ω ^ 4) P := by
    refine ⟨hQ.aestronglyMeasurable.pow 4, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have hb : ∫⁻ ω, ‖Q ω ^ 4‖ₑ ∂P ≤
        ENNReal.ofReal (15 * (∫ ω, Q ω ^ 2 ∂P) ^ 2) := by
      calc
        ∫⁻ ω, ‖Q ω ^ 4‖ₑ ∂P = ∫⁻ ω, ENNReal.ofReal (Q ω ^ 4) ∂P := by
          apply lintegral_congr
          intro ω
          rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        _ ≤ _ := hkey
    exact hb.trans_lt ENNReal.ofReal_lt_top
  have h4 : MemLp Q 4 P := by
    apply (integrable_norm_rpow_iff hQ.aestronglyMeasurable (by norm_num) (by norm_num)).1
    have heq : (fun ω => ‖Q ω‖ ^ (4 : ℝ≥0∞).toReal) = (fun ω => Q ω ^ 4) := by
      funext ω
      simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat, Real.norm_eq_abs, ← abs_pow,
        abs_of_nonneg (show 0 ≤ (Q ω) ^ 4 by positivity)]
    rw [heq]
    exact hi
  refine ⟨h4, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun ω => Q ω ^ 4)
    (Eventually.of_forall fun ω => by positivity) (hQ.aestronglyMeasurable.pow 4)]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hkey

/-- Every scalar element of the retained second-chaos closure has a
fourth moment controlled by its second moment. -/
theorem fp81s21_InQ2_fourth
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ)
    {Y : Ω → ℝ} (hY : InQ2 hξ Y) :
    MemLp Y 4 P ∧ (∫ ω, Y ω ^ 4 ∂P) ≤ 15 * (∫ ω, Y ω ^ 2 ∂P) ^ 2 := by
  obtain ⟨N, c, ht⟩ := fp81s21_InQ2_L2_polynomials hξ hY
  apply fp81s21_fourth_limit hY.1 (fun n => memLp_quadSum hξ (c n) (N n)) ht
  intro n
  have h := fp81s21_quadratic_difference_fourth_general hξ (c n) (fun _ _ => 0) (N n)
  simpa [quadSum] using h

/-- Finite Wick polynomials belong to the same L² second-chaos closure. -/
theorem fp81s21_quadSum_InQ2
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ)
    (c : ℕ → ℕ → ℝ) (N : ℕ) : InQ2 hξ (quadSum c ξ N) := by
  unfold quadSum
  apply InQ2.sum
  intro i hi
  apply InQ2.sum
  intro j hj
  exact InQ2.const_mul _ (InQ2_term hξ i j)

/-- L² convergence within the scalar second chaos automatically upgrades
to L⁴ convergence. -/
theorem fp81s21_InQ2_L4_convergence
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ)
    {Y : Ω → ℝ} {Yn : ℕ → Ω → ℝ}
    (hY : InQ2 hξ Y) (hYn : ∀ n, InQ2 hξ (Yn n))
    (ht : Tendsto (fun n => eLpNorm (fun ω => Yn n ω - Y ω) 2 P) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun ω => Yn n ω - Y ω) 4 P) atTop (𝓝 0) := by
  let D : ℕ → Ω → ℝ := fun n ω => Yn n ω - Y ω
  have hD (n : ℕ) : InQ2 hξ (D n) := by
    have h := InQ2.add (hYn n) (InQ2.const_mul (-1) hY)
    simpa [D, sub_eq_add_neg] using h
  have hm (n : ℕ) : MemLp (D n) 2 P := (hD n).1
  have htD : Tendsto (fun n => eLpNorm (D n) 2 P) atTop (𝓝 0) := ht
  have hsq : Tendsto (fun n => ∫ ω, D n ω ^ 2 ∂P) atTop (𝓝 0) := by
    have heq (n : ℕ) : ENNReal.ofReal (∫ ω, D n ω ^ 2 ∂P) = eLpNorm (D n) 2 P ^ 2 := by
      rw [← HRS.lintegral_enorm_sq_eq (hm n).aestronglyMeasurable,
        ofReal_integral_eq_lintegral_ofReal (hm n).integrable_sq
          (Eventually.of_forall fun ω => sq_nonneg _)]
      apply lintegral_congr
      intro ω
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
    have hp : Tendsto (fun n => eLpNorm (D n) 2 P ^ 2) atTop (𝓝 0) := by
      simpa only [Function.comp_def, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
        ((ENNReal.continuous_pow 2).tendsto 0).comp htD
    have hn := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hp
    simp only [Function.comp_def, ENNReal.toReal_zero, ← heq,
      ENNReal.toReal_ofReal (integral_nonneg fun ω => sq_nonneg _)] at hn
    exact hn
  have hfour (n : ℕ) := fp81s21_InQ2_fourth hξ (hD n)
  have hi (n : ℕ) : Integrable (fun ω => D n ω ^ 4) P := by
    have hh := (hfour n).1.integrable_norm_pow'
    have heq : (fun ω => ‖D n ω‖ ^ 4) = (fun ω => D n ω ^ 4) := by
      funext ω
      rw [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (show 0 ≤ (D n ω) ^ 4 by positivity)]
    rw [heq] at hh
    exact hh
  have h4lim : Tendsto (fun n => ∫ ω, D n ω ^ 4 ∂P) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => integral_nonneg fun ω => by positivity) (fun n => (hfour n).2) ?_
    simpa using tendsto_const_nhds.mul (hsq.pow 2)
  have hlin : Tendsto (fun n => ∫⁻ ω, ‖D n ω‖ₑ ^ (4 : ℝ) ∂P) atTop (𝓝 0) := by
    have heq (n : ℕ) : (∫⁻ ω, ‖D n ω‖ₑ ^ (4 : ℝ) ∂P) = ENNReal.ofReal (∫ ω, D n ω ^ 4 ∂P) := by
      rw [ofReal_integral_eq_lintegral_ofReal (hi n) (Eventually.of_forall fun ω => by positivity)]
      apply lintegral_congr
      intro ω
      rw [ENNReal.rpow_ofNat, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
        Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (show 0 ≤ (D n ω) ^ 4 by positivity)]
    simp_rw [heq]
    simpa using ENNReal.tendsto_ofReal h4lim
  have hres := (tendsto_lintegral_iff_eLpNorm (fun n => (hm n).aestronglyMeasurable)
    (by norm_num : (0 : ℝ) < 4)).1 hlin
  simpa [D] using hres

/-- Every retained scalar second-chaos element is an L⁴ limit of finite
quadratic polynomials in the same Gaussian sequence. -/
theorem fp81s21_InQ2_L4_polynomials
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ)
    {Y : Ω → ℝ} (hY : InQ2 hξ Y) :
    ∃ (N : ℕ → ℕ) (c : ℕ → ℕ → ℕ → ℝ),
      Tendsto (fun n => eLpNorm (fun ω => quadSum (c n) ξ (N n) ω - Y ω) 4 P)
        atTop (𝓝 0) := by
  obtain ⟨N, c, ht⟩ := fp81s21_InQ2_L2_polynomials hξ hY
  exact ⟨N, c, fp81s21_InQ2_L4_convergence hξ hY
    (fun n => fp81s21_quadSum_InQ2 hξ (c n) (N n)) ht⟩

/-- Under the retained first-chaos source certificate, each scalar output of
the supplied half-Wick operator has a fourth moment and retained-sequence
finite polynomial approximations in L⁴. -/
theorem fp81s21_wick_operator_L4_polynomials
    {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ) (hm : ∀ i, Measurable (ξ i))
    (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P) (Kstar : ℝ) (hL : ‖L‖ ≤ Kstar)
    (hJoint : ∀ r (v : Fin r → Lp ℝ 2 μ),
      IsCenteredGaussian (P.map fun ω => fun i => (L (v i)) ω))
    (hsrc : ∀ f, InFirstChaos P ξ 2 (fun ω => (L f) ω))
    (k : Lp ℝ 2 (μ.prod μ)) :
    let Y : Ω → ℝ := fun ω => fp81s21_wickG_operator L Kstar hL hJoint k ω
    MemLp Y 4 P ∧ (∫ ω, Y ω ^ 4 ∂P) ≤ 15 * (∫ ω, Y ω ^ 2 ∂P) ^ 2 ∧
      ∃ (N : ℕ → ℕ) (c : ℕ → ℕ → ℕ → ℝ),
        Tendsto (fun n => eLpNorm (fun ω => quadSum (c n) ξ (N n) ω - Y ω) 4 P)
          atTop (𝓝 0) := by
  have hY := fp81s21_wick_operator_InQ2 hξ hm L Kstar hL hJoint hsrc k
  exact ⟨(fp81s21_InQ2_fourth hξ hY).1, (fp81s21_InQ2_fourth hξ hY).2,
    fp81s21_InQ2_L4_polynomials hξ hY⟩

#print axioms fp81s21_wick_operator_L4_polynomials

#print axioms fp81s21_InQ2_L4_polynomials

#print axioms fp81s21_InQ2_L4_convergence

#print axioms fp81s21_quadSum_InQ2

#print axioms fp81s21_InQ2_fourth

#print axioms fp81s21_fourth_limit

#print axioms fp81s21_InQ2_L2_polynomials

end HRS.Fp81.S21
end
