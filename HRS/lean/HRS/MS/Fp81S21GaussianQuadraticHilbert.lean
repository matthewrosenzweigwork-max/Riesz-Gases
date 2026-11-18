import HRS.MS.Fp81S21GaussianQuadraticHistory
import HRS.MS.ProClosureS111ThermalTrace
import HRS.MS.Fp81S21EmbedField12
import HRS.MC.E213U13c

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal BigOperators
open HRS HRS.MC.E213U13 HRS.MS.R26T6 HRS.MS.ProClosureS111
namespace HRS.Fp81.S21

/-- The integrated ℓ² norm is the sum of the integrated coordinate energies. -/
theorem fp81s21_coeff_coordinate_energy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q : Ω → r26t6_Coeff) (hq : MemLp q 2 P) :
    Summable (fun j => ∫ ω, (q ω j) ^ 2 ∂P) ∧
      (∑' j, ∫ ω, (q ω j) ^ 2 ∂P) = ∫ ω, ‖q ω‖ ^ 2 ∂P := by
  let q' := hq.aestronglyMeasurable.mk q
  have hqe : q' =ᵐ[P] q := hq.aestronglyMeasurable.ae_eq_mk.symm
  have hqm : Measurable q' := hq.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hqi : Integrable (fun ω => ‖q' ω‖ ^ 2) P := by
    apply hq.integrable_norm_pow'.congr
    filter_upwards [hqe] with ω hω
    rw [hω]
  have hf : ∀ j, Measurable (fun ω => q' ω j) := fun j =>
    (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 j).continuous.measurable.comp hqm
  have hb : ∀ S : Finset ℕ, ∀ ω, (∑ j ∈ S, q' ω j ^ 2) ≤ ‖q' ω‖ ^ 2 := by
    intro S ω
    rw [HRS.StaticLimitAux.lp_norm_sq]
    exact (HRS.StaticLimitAux.lp_sq_summable (q' ω)).sum_le_tsum S
      (fun j _ => sq_nonneg _)
  have ht := summable_integral_sq_of_finite_trace P (fun j ω => q' ω j)
    (fun ω => ‖q' ω‖ ^ 2) hf hqi hb
  have he : ∀ j, (∫ ω, q' ω j ^ 2 ∂P) = ∫ ω, q ω j ^ 2 ∂P := by
    intro j
    apply integral_congr_ae
    filter_upwards [hqe] with ω hω
    rw [hω]
  have hs : Summable (fun j => ∫ ω, q ω j ^ 2 ∂P) := by
    simpa only [he] using ht.2.1
  refine ⟨hs, ?_⟩
  have hseries : ∀ ω, Summable (fun j => q' ω j ^ 2) := fun ω =>
    HRS.StaticLimitAux.lp_sq_summable (q' ω)
  have hint : ∀ j, Integrable (fun ω => q' ω j ^ 2) P := fun j => (ht.1 j).integrable_sq
  have hnormsum : Summable (fun j => ∫ ω, ‖q' ω j ^ 2‖ ∂P) := by
    convert ht.2.1 using 1
    funext j
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => by
      change ‖q' ω j ^ 2‖ = q' ω j ^ 2
      exact Real.norm_of_nonneg (sq_nonneg _)
  calc
    (∑' j, ∫ ω, q ω j ^ 2 ∂P) = ∑' j, ∫ ω, q' ω j ^ 2 ∂P := by simp_rw [he]
    _ = ∫ ω, ∑' j, q' ω j ^ 2 ∂P :=
      (integral_tsum_of_summable_integral_norm hint hnormsum)
    _ = ∫ ω, ‖q' ω‖ ^ 2 ∂P := by simp_rw [← HRS.StaticLimitAux.lp_norm_sq]
    _ = ∫ ω, ‖q ω‖ ^ 2 ∂P := integral_congr_ae (by
      filter_upwards [hqe] with ω hω; rw [hω])

/-- A scalar second-chaos square has L² norm bounded by its energy. -/
theorem fp81s21_InQ2_square_L2_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ)
    {Y : Ω → ℝ} (hY : InQ2 hξ Y) :
    eLpNorm (fun ω => Y ω ^ 2) 2 P ≤
      ENNReal.ofReal (Real.sqrt 15 * ∫ ω, Y ω ^ 2 ∂P) := by
  have hfour := fp81s21_InQ2_fourth hξ hY
  have hI : Integrable (fun ω => Y ω ^ 4) P := by
    have h := hfour.1.integrable_norm_pow'
    have heq : (fun ω => ‖Y ω‖ ^ 4) = (fun ω => Y ω ^ 4) := by
      funext ω
      rw [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (show 0 ≤ Y ω ^ 4 by positivity)]
    rw [heq] at h
    exact h
  have hlin : (∫⁻ ω, ‖Y ω‖ₑ ^ (4 : ℝ) ∂P) ≤
      ENNReal.ofReal (15 * (∫ ω, Y ω ^ 2 ∂P) ^ 2) := by
    calc
      _ = ∫⁻ ω, ENNReal.ofReal (Y ω ^ 4) ∂P := by
        apply lintegral_congr
        intro ω
        rw [ENNReal.rpow_ofNat, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
          Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (show 0 ≤ Y ω ^ 4 by positivity)]
      _ = ENNReal.ofReal (∫ ω, Y ω ^ 4 ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall fun ω => by positivity)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hfour.2
  have hv : 0 ≤ ∫ ω, Y ω ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  have hm : AEStronglyMeasurable (fun ω => Y ω ^ 2) P := by
    exact (hY.1.aestronglyMeasurable.aemeasurable.pow_const 2).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hm]
  norm_num only [ENNReal.toReal_ofNat]
  have he : ∀ ω, ‖Y ω ^ 2‖ₑ ^ (2 : ℝ) = ‖Y ω‖ₑ ^ (4 : ℝ) := by
    intro ω
    rw [enorm_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  simp_rw [he]
  calc
    (∫⁻ ω, ‖Y ω‖ₑ ^ (4 : ℝ) ∂P) ^ (1 / (2 : ℝ)) ≤
        ENNReal.ofReal (15 * (∫ ω, Y ω ^ 2 ∂P) ^ 2) ^ (1 / (2 : ℝ)) :=
      ENNReal.rpow_le_rpow hlin (by positivity)
    _ = ENNReal.ofReal (Real.sqrt 15 * ∫ ω, Y ω ^ 2 ∂P) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
      congr 1
      rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity), Real.sqrt_sq hv]

/-- The fourth moment of an ℓ²-valued second-chaos field is bounded by
fifteen times the square of its second moment. -/
theorem fp81s21_InQ2_coeff_fourth
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ)
    (q : Ω → r26t6_Coeff) (hq : MemLp q 2 P)
    (hcoord : ∀ j, InQ2 hξ (fun ω => q ω j)) :
    MemLp q 4 P ∧ (∫ ω, ‖q ω‖ ^ 4 ∂P) ≤ 15 * (∫ ω, ‖q ω‖ ^ 2 ∂P) ^ 2 := by
  let w : ℕ → ℝ := fun j => ∫ ω, q ω j ^ 2 ∂P
  let S : ℝ := ∑' j, w j
  have hw : ∀ j, 0 ≤ w j := fun j => integral_nonneg fun ω => sq_nonneg _
  have htrace := fp81s21_coeff_coordinate_energy P q hq
  have hws : Summable w := htrace.1
  have hS : S = ∫ ω, ‖q ω‖ ^ 2 ∂P := htrace.2
  have hS0 : 0 ≤ S := tsum_nonneg hw
  have hmeas : ∀ j, AEMeasurable (fun ω => q ω j) P :=
    fun j => (hcoord j).1.aestronglyMeasurable.aemeasurable
  have hfinite : ∀ F : Finset ℕ,
      ∫⁻ ω, (∑ j ∈ F, ENNReal.ofReal (q ω j ^ 2)) ^ (2 : ℝ) ∂P ≤
        ENNReal.ofReal (15 * S ^ 2) := by
    intro F
    have hn : ∀ ω, (∑ j ∈ F, ENNReal.ofReal (q ω j ^ 2)) =
        ‖∑ j ∈ F, q ω j ^ 2‖ₑ := by
      intro ω
      rw [← ofReal_norm, Real.norm_of_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _),
        ENNReal.ofReal_sum_of_nonneg fun j _ => sq_nonneg _]
    have hmink := eLpNorm_sum_le (μ := P) (f := fun j ω => q ω j ^ 2)
      (s := F) (p := (2 : ℝ≥0∞)) (by norm_num)
    have hbound : eLpNorm (∑ j ∈ F, fun ω => q ω j ^ 2) 2 P ≤
        ENNReal.ofReal (Real.sqrt 15 * S) := by
      refine hmink.trans ((Finset.sum_le_sum fun j _ => fp81s21_InQ2_square_L2_bound hξ (hcoord j)).trans ?_)
      rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => mul_nonneg (Real.sqrt_nonneg _) (hw j)]
      apply ENNReal.ofReal_le_ofReal
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hws.sum_le_tsum F (fun j _ => hw j)) (Real.sqrt_nonneg _)
    have heq : (∫⁻ ω, ‖∑ j ∈ F, q ω j ^ 2‖ₑ ^ (2 : ℝ) ∂P) =
        eLpNorm (∑ j ∈ F, fun ω => q ω j ^ 2) 2 P ^ (2 : ℝ) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
        (Finset.aestronglyMeasurable_sum F fun j _ => ((hmeas j).pow_const 2).aestronglyMeasurable),
        ENNReal.toReal_ofNat, ← ENNReal.rpow_mul, one_div,
        inv_mul_cancel₀ (by norm_num), ENNReal.rpow_one]
      simp only [Finset.sum_apply]
    calc
      _ = ∫⁻ ω, ‖∑ j ∈ F, q ω j ^ 2‖ₑ ^ (2 : ℝ) ∂P := by simp_rw [hn]
      _ = _ := heq
      _ ≤ ENNReal.ofReal (Real.sqrt 15 * S) ^ (2 : ℝ) := ENNReal.rpow_le_rpow hbound (by norm_num)
      _ = _ := by
        rw [ENNReal.rpow_ofNat, ← ENNReal.ofReal_pow (mul_nonneg (Real.sqrt_nonneg _) hS0)]
        congr 1
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15)]
  have hpoint : ∀ ω, ENNReal.ofReal (‖q ω‖ ^ 4) =
      ⨆ F : Finset ℕ, (∑ j ∈ F, ENNReal.ofReal (q ω j ^ 2)) ^ (2 : ℝ) := by
    intro ω
    have hs : Summable (fun j => q ω j ^ 2) := HRS.StaticLimitAux.lp_sq_summable (q ω)
    have he : (∑' j, ENNReal.ofReal (q ω j ^ 2)) = ENNReal.ofReal (‖q ω‖ ^ 2) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => sq_nonneg _) hs, ← HRS.StaticLimitAux.lp_norm_sq]
    have hh := Monotone.map_iSup_of_continuousAt
      (f := fun x : ℝ≥0∞ => x ^ (2 : ℝ))
      (g := fun F : Finset ℕ => ∑ j ∈ F, ENNReal.ofReal (q ω j ^ 2))
      (ENNReal.continuous_rpow_const.continuousAt)
      (ENNReal.monotone_rpow_of_nonneg (by norm_num))
      (by simp [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)])
    rw [← ENNReal.tsum_eq_iSup_sum, he] at hh
    rw [← hh, ENNReal.rpow_ofNat, ← ENNReal.ofReal_pow (sq_nonneg _)]
    congr 1
    ring
  have hlin : (∫⁻ ω, ENNReal.ofReal (‖q ω‖ ^ 4) ∂P) ≤ ENNReal.ofReal (15 * S ^ 2) := by
    simp_rw [hpoint]
    rw [lintegral_iSup_directed]
    · exact iSup_le hfinite
    · intro F
      exact (Finset.aemeasurable_fun_sum F fun j _ => ((hmeas j).pow_const 2).ennreal_ofReal).pow_const _
    · intro F F'
      refine ⟨F ∪ F', ?_, ?_⟩
      · intro ω
        exact ENNReal.rpow_le_rpow (Finset.sum_le_sum_of_subset (by simp)) (by norm_num)
      · intro ω
        exact ENNReal.rpow_le_rpow (Finset.sum_le_sum_of_subset (by simp)) (by norm_num)
  have hi : Integrable (fun ω => ‖q ω‖ ^ 4) P := by
    refine ⟨(hq.aestronglyMeasurable.norm.pow 4), ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω => by positivity)]
    exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  have h4 : MemLp q 4 P := by
    apply (integrable_norm_rpow_iff hq.aestronglyMeasurable (by norm_num) (by norm_num)).1
    simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat] using hi
  refine ⟨h4, ?_⟩
  rw [← hS]
  have he : ENNReal.ofReal (∫ ω, ‖q ω‖ ^ 4 ∂P) ≤ ENNReal.ofReal (15 * S ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun ω => by positivity)]
    exact hlin
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 he

/-- Uniform fourth moments for a specified supplied Wick family, conditional
on its retained-source first-chaos certificate and coordinate identities. -/
theorem fp81s21_wick_coeff_uniform_fourth
    {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ) (hm : ∀ i, Measurable (ξ i))
    (T : ℝ → Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P)
    (W : ℝ → Lp ℝ 2 (μ.prod μ) →L[ℝ] Lp ℝ 2 P)
    (k : ℕ → Lp ℝ 2 (μ.prod μ)) (q : ℝ → Ω → r26t6_Coeff)
    (K M : ℝ) (hM : 0 ≤ M)
    (hW : ∀ u, 0 ≤ u → ∃ hL : ‖T u‖ ≤ K,
      ∃ hJoint : ∀ r (v : Fin r → Lp ℝ 2 μ),
        IsCenteredGaussian (P.map fun ω => fun i => (T u (v i)) ω),
        W u = fp81s21_wickG_operator (T u) K hL hJoint)
    (hsrc : ∀ u, 0 ≤ u → ∀ f, InFirstChaos P ξ 2 (fun ω => T u f ω))
    (hq : ∀ u, 0 ≤ u → MemLp (q u) 2 P ∧
      (∫ ω, ‖q u ω‖ ^ 2 ∂P) ≤ M ∧
      ∀ j, (fun ω => q u ω j) =ᵐ[P] (fun ω => W u (k j) ω)) :
    ∃ M4 : ℝ, 0 ≤ M4 ∧ ∀ u, 0 ≤ u → MemLp (q u) 4 P ∧
      (∫ ω, ‖q u ω‖ ^ 4 ∂P) ≤ M4 := by
  refine ⟨15 * M ^ 2, by positivity, ?_⟩
  intro u hu
  obtain ⟨hL, hJoint, hWu⟩ := hW u hu
  obtain ⟨hqu, henergy, heq⟩ := hq u hu
  have hc : ∀ j, InQ2 hξ (fun ω => q u ω j) := by
    intro j
    apply InQ2.congr_ae (heq j).symm
    rw [hWu]
    exact fp81s21_wick_operator_InQ2 hξ hm (T u) K hL hJoint (hsrc u hu) (k j)
  have h := fp81s21_InQ2_coeff_fourth hξ (q u) hqu hc
  refine ⟨h.1, h.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (integral_nonneg fun ω => sq_nonneg _) henergy 2) (by norm_num)

/-- Finite coordinate projections converge in L⁴ to the coefficient field. -/
theorem fp81s21_InQ2_coeff_truncations
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ)
    (q : Ω → r26t6_Coeff) (hq : MemLp q 2 P)
    (hcoord : ∀ j, InQ2 hξ (fun ω => q ω j)) :
    Tendsto (fun n => eLpNorm (fun ω => fp81s21_projectField n (q ω) - q ω) 4 P)
      atTop (𝓝 0) := by
  have h4 := (fp81s21_InQ2_coeff_fourth hξ q hq hcoord).1
  have h4' : MemLp q (ENNReal.ofReal (4 : ℝ)) P := by simpa using h4
  simpa using dct_proj hq.aestronglyMeasurable (q := 4) (by norm_num) h4'
    fp81s21_projectField fp81s21_projectField_norm_le fp81s21_projectField_tendsto

/-- A coefficient field with scalar second-chaos coordinates is an L⁴
limit of finite coefficient-valued polynomials in the retained sequence. -/
theorem fp81s21_InQ2_coeff_L4_polynomials
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ)
    (q : Ω → r26t6_Coeff) (hq : MemLp q 2 P)
    (hcoord : ∀ j, InQ2 hξ (fun ω => q ω j)) :
    ∃ (N : ℕ → ℕ → ℕ) (c : ℕ → ℕ → ℕ → ℕ → ℝ),
      Tendsto (fun n => eLpNorm (fun ω =>
        (∑ j ∈ Finset.range n, quadSum (c n j) ξ (N n j) ω • fp81s21_coeffBasis j) - q ω)
        4 P) atTop (𝓝 0) := by
  classical
  choose N c hc using fun j => fp81s21_InQ2_L4_polynomials hξ (hcoord j)
  let g : ℕ → ℕ → Ω → r26t6_Coeff := fun n m ω =>
    ∑ j ∈ Finset.range n, quadSum (c j m) ξ (N j m) ω • fp81s21_coeffBasis j
  let F : ℕ → Ω → r26t6_Coeff := fun n ω => fp81s21_projectField n (q ω)
  have h1 : ∀ n, Tendsto (fun m => eLpNorm (g n m - F n) 4 P) atTop (𝓝 0) := by
    intro n
    have heq : ∀ m, g n m - F n = fun ω => ∑ j ∈ Finset.range n,
        (quadSum (c j m) ξ (N j m) ω - q ω j) • fp81s21_coeffBasis j := by
      intro m
      funext ω
      simp only [g, F, Pi.sub_apply, fp81s21_projectField_apply_coordinate,
        sub_smul, Finset.sum_sub_distrib]
    simp_rw [heq]
    have hb : ∀ m, eLpNorm (fun ω => ∑ j ∈ Finset.range n,
        (quadSum (c j m) ξ (N j m) ω - q ω j) • fp81s21_coeffBasis j) 4 P ≤
        ∑ j ∈ Finset.range n, ‖fp81s21_coeffBasis j‖ₑ *
          eLpNorm (fun ω => quadSum (c j m) ξ (N j m) ω - q ω j) 4 P := by
      intro m
      apply eLpNorm_finsum_smul_le (Finset.range n) (fun j => fp81s21_coeffBasis j)
      · intro j hj
        exact (memLp_quadSum hξ (c j m) (N j m)).aestronglyMeasurable.sub
          (hcoord j).1.aestronglyMeasurable
      · norm_num
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun m => bot_le) hb
    have hsum : Tendsto (fun m => ∑ j ∈ Finset.range n, ‖fp81s21_coeffBasis j‖ₑ *
        eLpNorm (fun ω => quadSum (c j m) ξ (N j m) ω - q ω j) 4 P)
        atTop (𝓝 (∑ j ∈ Finset.range n, ‖fp81s21_coeffBasis j‖ₑ * 0)) := by
      refine tendsto_finsetSum _ fun j hj => ?_
      exact ENNReal.Tendsto.const_mul (hc j) (Or.inr (by simp))
    simpa using hsum
  have h2 : Tendsto (fun n => eLpNorm (F n - q) 4 P) atTop (𝓝 0) :=
    fp81s21_InQ2_coeff_truncations hξ q hq hcoord
  obtain ⟨mm, hmm⟩ := exists_diag (p := (4 : ℝ≥0∞)) (by norm_num) g F q h1 h2
  refine ⟨fun n j => N j (mm n), fun n j => c j (mm n), ?_⟩
  refine hmm.congr fun n => ?_
  apply congrArg (fun f : Ω → r26t6_Coeff => eLpNorm f 4 P)
  funext ω
  rfl

#print axioms fp81s21_InQ2_coeff_L4_polynomials

#print axioms fp81s21_InQ2_coeff_truncations

#print axioms fp81s21_wick_coeff_uniform_fourth

#print axioms fp81s21_InQ2_coeff_fourth

#print axioms fp81s21_InQ2_square_L2_bound

#print axioms fp81s21_coeff_coordinate_energy
end HRS.Fp81.S21
end
