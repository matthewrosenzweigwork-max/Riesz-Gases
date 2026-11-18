import HRS.Uniform.Q07cAux4

/-!
# Q07c, part 5: from Itô data to `IsHilbertMartingaleWithCovariation`
-/

noncomputable section

open HRS
open MeasureTheory Filter Topology HRS.HilbertCLTAux ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q07c

section Pack

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {A : Type*} [Countable A]

lemma traceNormForm_hsCovForm_eq {Φ : A → H} (hΦ : Summable fun k => ‖Φ k‖ ^ 2) :
    traceNormForm (hsCovForm Φ) = ∑' k, ‖Φ k‖ ^ 2 := by
  obtain ⟨ι₀, -, b, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := H)
  refine le_antisymm (traceNormForm_hsCov_le hΦ) ?_
  have h := (isTraceClassCov_hsCovForm hΦ).tsum_basis_le b
  refine le_trans (le_of_eq ?_) h
  rw [← (hasSum_diag_decomp hΦ b).tsum_eq]
  refine tsum_congr fun i => ?_
  rw [hsCovForm_apply hΦ]
  exact tsum_congr fun k => sq _

lemma memLp_two_of_lintegral {f : Ω → H} (hf : AEStronglyMeasurable f P)
    (h : ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂P ≠ ⊤) : MemLp f 2 P := by
  have h2 : eLpNorm f 2 P ≠ ⊤ := by
    intro htop
    have := HRS.lintegral_enorm_sq_eq_eLpNorm_sq hf
    rw [htop] at this
    exact h (by simpa using this)
  exact lt_top_iff_ne_top.2 h2


variable {𝔚 : ℝ≥0 → Ω → A → ℝ}

lemma hsum_aux {Z : ℝ → Ω → A → H} (hZ : ∀ T, IsHSIntegrand P ℱ T Z) (r : ℝ) (ω : Ω) :
    Summable fun a => ‖Z r ω a‖ ^ 2 := (hZ 0).summable r ω

lemma ctbl_coord {Z : ℝ → Ω → A → H} (hZ : ∀ T, IsHSIntegrand P ℱ T Z) (x : H) :
    IsCtbl P ℱ (fun r ω a => inner ℝ (Z r ω a) x) := by
  refine pc_isCtbl_of_HS hZ x (fun a i => ((hZ 0).prog a i).inner measurable_const) (fun r ω => ?_)
  calc ∑' a, ‖inner ℝ (Z r ω a) x‖ₑ ^ 2 ≤ ∑' a, ‖Z r ω a‖ₑ ^ 2 * ‖x‖ₑ ^ 2 :=
        ENNReal.tsum_le_tsum fun a => pc_enorm_inner_sq_le _ _
    _ = (∑' a, ‖Z r ω a‖ₑ ^ 2) * ‖x‖ₑ ^ 2 := ENNReal.tsum_mul_right

lemma isProgressive_hsCov {Z : ℝ → Ω → A → H} (hZ : ∀ T, IsHSIntegrand P ℱ T Z) (x y : H) :
    IsProgressive ℱ (fun r ω => hsCovForm (Z r ω) x y) := by
  intro i
  letI : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
  have : (fun p : Set.Iic i × Ω => hsCovForm (Z p.1 p.2) x y) =
      fun p => ∑' a, inner ℝ (Z p.1 p.2 a) x * inner ℝ (Z p.1 p.2 a) y := by
    funext p; exact hsCovForm_apply ((hZ 0).summable _ _) x y
  rw [this]
  exact Measurable.tsum fun a => (((hZ 0).prog a i).inner measurable_const).mul
    (((hZ 0).prog a i).inner measurable_const)


lemma integrable_trace {Z : ℝ → Ω → A → H} (hZ : ∀ T, IsHSIntegrand P ℱ T Z) (t : ℝ) :
    Integrable (fun p : ℝ × Ω => ∑' a, ‖Z p.1 p.2 a‖ ^ 2) ((volume.restrict (Set.Icc 0 t)).prod P) := by
  have hm : Measurable fun p : ℝ × Ω => ∑' a, ‖Z p.1 p.2 a‖ ^ 2 :=
    Measurable.tsum fun a => ((HRS.MRep.isProgressive_measurable_uncurry
      (f := fun r ω => Z r ω a) ((hZ 0).prog a)).norm).pow_const 2
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have h1 : ∫⁻ p, ‖∑' a, ‖Z p.1 p.2 a‖ ^ 2‖ₑ ∂((volume.restrict (Set.Icc 0 t)).prod P) =
      hsSqIntegralOn P Z t := by
    rw [lintegral_prod_symm _ (hm.enorm.aemeasurable)]
    unfold hsSqIntegralOn
    refine lintegral_congr fun ω => lintegral_congr fun r => ?_
    rw [Real.enorm_eq_ofReal (tsum_nonneg fun a => sq_nonneg _),
      ENNReal.ofReal_tsum_of_nonneg (fun a => sq_nonneg _) (hsum_aux hZ r ω)]
    exact tsum_congr fun a => (pc_enorm_sq_vec' _).symm
  rw [h1]
  exact (hZ t).sq

lemma adapted_hsCov {Z : ℝ → Ω → A → H} (hZ : ∀ T, IsHSIntegrand P ℱ T Z) (σ : ℝ) (x y : H) :
    Measurable[ℱ σ] fun ω => hsCovForm (Z σ ω) x y := by
  exact (isProgressive_hsCov hZ x y).adapted σ


lemma memLp_N (hW : IsCylindricalBrownian P ℱ 𝔚) {Z : ℝ → Ω → A → H}
    (hZ : ∀ T, IsHSIntegrand P ℱ T Z) {N : ℝ → Ω → H} (hNa : ∀ τ, Measurable[ℱ τ] (N τ))
    (hNJ : ∀ x : H, ∃ J : ℝ → Ω → ℝ, IsItoC P ℱ 𝔚 (fun r ω a => inner ℝ (Z r ω a) x) J ∧
      ∀ τ, 0 ≤ τ → (fun ω => inner ℝ (N τ ω) x) =ᵐ[P] J τ) {τ : ℝ} (hτ : 0 ≤ τ) :
    MemLp (N τ) 2 P := by
  obtain ⟨ι₀, hc₀, e, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := H)
  have hm : AEStronglyMeasurable (N τ) P := ((hNa τ).mono (ℱ.le τ) le_rfl).aestronglyMeasurable
  refine memLp_two_of_lintegral hm ?_
  choose J hJ hNJ' using hNJ
  have hctb := fun x => ctbl_coord hZ x
  have hprog : ∀ i a, IsProgressive ℱ (fun r ω => inner ℝ (Z r ω a) (e i)) :=
    fun i a i' => ((hZ 0).prog a i').inner measurable_const
  have h1 : ∀ i, ∫⁻ ω, ‖inner ℝ (N τ ω) (e i)‖ₑ ^ 2 ∂P ≤
      ∫⁻ ω, (∫⁻ r in Set.Icc 0 τ, ∑' a, ‖inner ℝ (Z r ω a) (e i)‖ₑ ^ 2) ∂P := by
    intro i
    have hae := hNJ' (e i) τ hτ
    calc ∫⁻ ω, ‖inner ℝ (N τ ω) (e i)‖ₑ ^ 2 ∂P = ∫⁻ ω, ‖J (e i) τ ω‖ₑ ^ 2 ∂P :=
          lintegral_congr_ae (hae.mono fun ω h => by
            show ‖inner ℝ (N τ ω) (e i)‖ₑ ^ 2 = ‖J (e i) τ ω‖ₑ ^ 2
            rw [show inner ℝ (N τ ω) (e i) = J (e i) τ ω from h])
      _ ≤ ∑' a, cT P (fun r ω a => inner ℝ (Z r ω a) (e i)) a τ :=
          (hJ (e i)).lintegral_sq_le (hctb (e i)) hW hτ
      _ = _ := pc_tsum_cT (fun a i' => ((hZ 0).prog a i').inner measurable_const) τ
  refine ne_top_of_le_ne_top (hZ τ).sq.ne ?_
  show ∫⁻ ω, ‖N τ ω‖ₑ ^ 2 ∂P ≤ ∫⁻ ω, (∫⁻ r in Set.Icc 0 τ, ∑' a, ‖Z r ω a‖ₑ ^ 2) ∂P
  calc ∫⁻ ω, ‖N τ ω‖ₑ ^ 2 ∂P = ∫⁻ ω, ∑' i, ‖inner ℝ (N τ ω) (e i)‖ₑ ^ 2 ∂P :=
        lintegral_congr fun ω => pc_enorm_sq_tsum e _
    _ = ∑' i, ∫⁻ ω, ‖inner ℝ (N τ ω) (e i)‖ₑ ^ 2 ∂P := by
        rw [lintegral_tsum]
        intro i
        exact (((hNa τ).mono (ℱ.le τ) le_rfl).inner measurable_const).enorm.pow_const 2 |>.aemeasurable
    _ ≤ ∑' i, ∫⁻ ω, (∫⁻ r in Set.Icc 0 τ, ∑' a, ‖inner ℝ (Z r ω a) (e i)‖ₑ ^ 2) ∂P :=
        ENNReal.tsum_le_tsum h1
    _ ≤ ∫⁻ ω, (∫⁻ r in Set.Icc 0 τ, ∑' a, ‖Z r ω a‖ₑ ^ 2) ∂P := by
        refine le_of_eq ?_
        rw [← lintegral_tsum]
        · refine lintegral_congr fun ω => ?_
          rw [← lintegral_tsum]
          · refine lintegral_congr fun r => ?_
            rw [ENNReal.tsum_comm]
            exact tsum_congr fun a => (pc_enorm_sq_tsum e _).symm
          · intro i
            exact (measurable_slice_sq (w := fun r ω a => inner ℝ (Z r ω a) (e i)) (hprog i) ω).aemeasurable
        · intro i
          exact (measurable_innerSq (w := fun r ω a => inner ℝ (Z r ω a) (e i)) (hprog i) τ).aemeasurable


lemma trace_eq_aux {Z : ℝ → Ω → A → H} (hZ : ∀ T, IsHSIntegrand P ℱ T Z) :
    ∀ σ ω, traceNormForm (hsCovForm (Z σ ω)) = ∑' a, ‖Z σ ω a‖ ^ 2 :=
  fun σ ω => traceNormForm_hsCovForm_eq (hsum_aux hZ σ ω)

lemma sigma_int_aux {Z : ℝ → Ω → A → H} (hZ : ∀ T, IsHSIntegrand P ℱ T Z) (t : ℝ) :
    Integrable (fun ω => ∫ σ in Set.Icc 0 t, traceNormForm (hsCovForm (Z σ ω))) P := by
  simp_rw [trace_eq_aux hZ]
  exact (integrable_trace hZ t).integral_prod_right

lemma sigma_pathint_aux {Z : ℝ → Ω → A → H} (hZ : ∀ T, IsHSIntegrand P ℱ T Z) (t : ℝ) :
    ∀ᵐ ω ∂P, IntegrableOn (fun σ => traceNormForm (hsCovForm (Z σ ω))) (Set.Icc 0 t) := by
  simp_rw [trace_eq_aux hZ]
  exact (integrable_trace hZ t).prod_left_ae

lemma abs_hsCov_le {Φ : A → H} (hΦ : Summable fun k => ‖Φ k‖ ^ 2) (x y : H) :
    |hsCovForm Φ x y| ≤ ‖x‖ * ‖y‖ * ∑' k, ‖Φ k‖ ^ 2 := by
  have hb : ∀ a, |inner ℝ (Φ a) x * inner ℝ (Φ a) y| ≤ ‖x‖ * ‖y‖ * ‖Φ a‖ ^ 2 := by
    intro a
    rw [abs_mul]
    calc |inner ℝ (Φ a) x| * |inner ℝ (Φ a) y| ≤ (‖Φ a‖ * ‖x‖) * (‖Φ a‖ * ‖y‖) :=
          mul_le_mul (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _) (abs_nonneg _)
            (by positivity)
      _ = ‖x‖ * ‖y‖ * ‖Φ a‖ ^ 2 := by ring
  have hs2 : Summable fun a => ‖x‖ * ‖y‖ * ‖Φ a‖ ^ 2 := hΦ.mul_left _
  have hs1 : Summable fun a => inner ℝ (Φ a) x * inner ℝ (Φ a) y :=
    Summable.of_norm_bounded hs2 (fun a => by rw [Real.norm_eq_abs]; exact hb a)
  rw [hsCovForm_apply hΦ, ← tsum_mul_left]
  calc |∑' a, inner ℝ (Φ a) x * inner ℝ (Φ a) y|
      = ‖∑' a, inner ℝ (Φ a) x * inner ℝ (Φ a) y‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' a, ‖inner ℝ (Φ a) x * inner ℝ (Φ a) y‖ := norm_tsum_le_tsum_norm hs1.norm
    _ ≤ ∑' a, ‖x‖ * ‖y‖ * ‖Φ a‖ ^ 2 :=
        hs1.norm.tsum_le_tsum (fun a => by rw [Real.norm_eq_abs]; exact hb a) hs2

lemma sigma_entry_aux {Z : ℝ → Ω → A → H} (hZ : ∀ T, IsHSIntegrand P ℱ T Z) (t : ℝ) :
    ∀ᵐ ω ∂P, ∀ x y : H, IntegrableOn (fun σ => hsCovForm (Z σ ω) x y) (Set.Icc 0 t) := by
  have hg := integrable_trace hZ t
  filter_upwards [hg.prod_left_ae] with ω hω x y
  have hω' : Integrable (fun σ : ℝ => ‖x‖ * ‖y‖ * ∑' a, ‖Z σ ω a‖ ^ 2) (volume.restrict (Set.Icc 0 t)) :=
    hω.const_mul (‖x‖ * ‖y‖)
  have hm : Measurable fun σ : ℝ => hsCovForm (Z σ ω) x y := by
    exact Measurable.of_uncurry_right
      (HRS.MRep.isProgressive_measurable_uncurry (isProgressive_hsCov hZ x y))
  have hb : ∀ σ : ℝ, ‖hsCovForm (Z σ ω) x y‖ ≤ ‖x‖ * ‖y‖ * ∑' a, ‖Z σ ω a‖ ^ 2 := fun σ => by
    rw [Real.norm_eq_abs]
    exact abs_hsCov_le (hsum_aux hZ σ ω) x y
  exact Integrable.mono' hω' hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)

theorem isHM_of_ito (hW : IsCylindricalBrownian P ℱ 𝔚) {Z : ℝ → Ω → A → H}
    (hZ : ∀ T, IsHSIntegrand P ℱ T Z) {N : ℝ → Ω → H} (hNc : ∀ ω, Continuous fun τ => N τ ω)
    (hNa : ∀ τ, Measurable[ℱ τ] (N τ)) (hN0 : ∀ τ, τ ≤ 0 → ∀ ω, N τ ω = 0)
    (hNJ : ∀ x : H, ∃ J : ℝ → Ω → ℝ, IsItoC P ℱ 𝔚 (fun r ω a => inner ℝ (Z r ω a) x) J ∧
      ∀ τ, 0 ≤ τ → (fun ω => inner ℝ (N τ ω) x) =ᵐ[P] J τ) (t : ℝ) :
    IsHilbertMartingaleWithCovariation P ℱ t N (fun r ω => hsCovForm (Z r ω)) := by
  have hsum : ∀ r ω, Summable fun a => ‖Z r ω a‖ ^ 2 := fun r ω => (hZ 0).summable r ω
  have hadN : ∀ x : H, ∀ τ, Measurable[ℱ τ] fun ω => inner ℝ (N τ ω) x := fun x τ =>
    (hNa τ).inner measurable_const
  have hae : ∀ x : H, ∀ J : ℝ → Ω → ℝ, IsItoC P ℱ 𝔚 (fun r ω a => inner ℝ (Z r ω a) x) J →
      (∀ τ, 0 ≤ τ → (fun ω => inner ℝ (N τ ω) x) =ᵐ[P] J τ) →
      ∀ τ, (fun ω => inner ℝ (N τ ω) x) =ᵐ[P] J τ := by
    intro x J hJ h τ
    by_cases hτ : 0 ≤ τ
    · exact h τ hτ
    · refine Filter.Eventually.of_forall fun ω => ?_
      show inner ℝ (N τ ω) x = J τ ω
      rw [hN0 τ (not_le.1 hτ).le ω, hJ.zero τ (not_le.1 hτ).le ω]; simp
  refine ⟨fun x => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨J, hJ, hNJ'⟩ := hNJ x
    exact HRS.martingale_congr_ae (hJ.martingale (ctbl_coord hZ x) hW)
      (fun τ => (hadN x τ).stronglyMeasurable) (hae x J hJ hNJ')
  · exact Filter.Eventually.of_forall fun ω => hN0 0 le_rfl ω
  · exact Filter.Eventually.of_forall fun ω => (hNc ω).continuousOn
  · exact fun τ hτ => memLp_N hW hZ hNa hNJ hτ.1
  · exact fun x y => HRS.MRep.isProgressive_measurable_uncurry (isProgressive_hsCov hZ x y)
  · exact fun σ x y => adapted_hsCov hZ σ x y
  · exact Filter.Eventually.of_forall fun ω σ _ => isTraceClassCov_hsCovForm (hsum σ ω)
  · exact sigma_int_aux hZ t
  · exact sigma_pathint_aux hZ t
  · exact sigma_entry_aux hZ t
  · intro x y
    obtain ⟨J, hJ, hNJ'⟩ := hNJ x
    obtain ⟨J', hJ', hNJ''⟩ := hNJ y
    have hsx : ∀ r ω, Summable fun a => inner ℝ (Z r ω a) x ^ 2 := fun r ω =>
      (((hsum r ω).mul_right (‖x‖ ^ 2)).of_nonneg_of_le (fun a => sq_nonneg _) fun a => by
        calc inner ℝ (Z r ω a) x ^ 2 = |inner ℝ (Z r ω a) x| ^ 2 := (sq_abs _).symm
          _ ≤ (‖Z r ω a‖ * ‖x‖) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2
          _ = ‖Z r ω a‖ ^ 2 * ‖x‖ ^ 2 := by ring)
    have hsy : ∀ r ω, Summable fun a => inner ℝ (Z r ω a) y ^ 2 := fun r ω =>
      (((hsum r ω).mul_right (‖y‖ ^ 2)).of_nonneg_of_le (fun a => sq_nonneg _) fun a => by
        calc inner ℝ (Z r ω a) y ^ 2 = |inner ℝ (Z r ω a) y| ^ 2 := (sq_abs _).symm
          _ ≤ (‖Z r ω a‖ * ‖y‖) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2
          _ = ‖Z r ω a‖ ^ 2 * ‖y‖ ^ 2 := by ring)
    have hM := isItoC_martingale_mul_sub_random hW (ctbl_coord hZ x) (ctbl_coord hZ y) hJ hJ' hsx hsy
    refine HRS.martingale_congr_ae hM ?_ ?_
    · intro τ
      refine (Measurable.stronglyMeasurable ?_)
      exact (((hadN x τ).mul (hadN y τ)).sub (measurable_setIntegral_progressive
        (isProgressive_hsCov hZ x y) τ))
    · intro τ
      have hint : ∀ ω, ∫ σ in Set.Icc 0 τ, hsCovForm (Z σ ω) x y =
          ∫ r in Set.Icc 0 τ, ∑' a, inner ℝ (Z r ω a) x * inner ℝ (Z r ω a) y := fun ω =>
        setIntegral_congr_fun measurableSet_Icc fun σ _ => hsCovForm_apply (hsum σ ω) x y
      have hx := hae x J hJ hNJ' τ
      have hy := hae y J' hJ' hNJ'' τ
      filter_upwards [hx, hy] with ω h1 h2
      show inner ℝ (N τ ω) x * inner ℝ (N τ ω) y - ∫ σ in Set.Icc 0 τ, hsCovForm (Z σ ω) x y =
        J τ ω * J' τ ω - ∫ r in Set.Icc 0 τ, ∑' a, inner ℝ (Z r ω a) x * inner ℝ (Z r ω a) y
      rw [hint ω, show inner ℝ (N τ ω) x = J τ ω from h1, show inner ℝ (N τ ω) y = J' τ ω from h2]

end Pack

end HRS.Uniform.Q07c
