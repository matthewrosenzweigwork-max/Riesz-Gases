import HRS.Uniform.Q07cAux3

/-!
# Q07c, part 4: the random-bracket martingale for countable-index Itô integrals
-/

noncomputable section

open HRS
open MeasureTheory Filter Topology HRS.HilbertCLTAux ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q07c

section Bracket

open Classical

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {A : Type*} [Countable A] {ξ ξ' : ℝ → Ω → A → ℝ}

/-- `‖x y‖ₑ ≤ ‖x‖ₑ² + ‖y‖ₑ²`. -/
lemma enorm_mul_le_sq_add (x y : ℝ) : ‖x * y‖ₑ ≤ ‖x‖ₑ ^ 2 + ‖y‖ₑ ^ 2 := by
  have h : |x * y| ≤ x ^ 2 + y ^ 2 := by
    rw [abs_mul]; nlinarith [sq_nonneg (|x| - |y|), sq_abs x, sq_abs y, abs_nonneg x, abs_nonneg y]
  rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
    ← ENNReal.ofReal_pow (abs_nonneg _), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  simpa [sq_abs, abs_mul] using h

/-- pointwise bound of the truncation error of the compensator -/
lemma compensator_pointwise (hs : ∀ r ω, Summable fun a => ξ r ω a ^ 2)
    (hs' : ∀ r ω, Summable fun a => ξ' r ω a ^ 2) (F : Finset A) (r : ℝ) (ω : Ω) :
    ‖(∑ a ∈ F, ξ r ω a * ξ' r ω a) - ∑' a, ξ r ω a * ξ' r ω a‖ₑ ≤
      ∑' a, (‖if a ∈ F then 0 else ξ r ω a‖ₑ ^ 2 + ‖if a ∈ F then 0 else ξ' r ω a‖ₑ ^ 2) := by
  classical
  have hsum : Summable fun a => ξ r ω a * ξ' r ω a := by
    refine Summable.of_norm_bounded ((hs r ω).add (hs' r ω)) (fun a => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_nonneg (|ξ r ω a| - |ξ' r ω a|), sq_abs (ξ r ω a), sq_abs (ξ' r ω a),
      abs_nonneg (ξ r ω a), abs_nonneg (ξ' r ω a)]
  have h1 := hsum.sum_add_tsum_compl (s := F)
  have h2 : (∑ a ∈ F, ξ r ω a * ξ' r ω a) - ∑' a, ξ r ω a * ξ' r ω a =
      -∑' a : ((F : Set A)ᶜ : Set A), ξ r ω a * ξ' r ω a := by
    rw [← h1]; ring
  rw [h2]
  have hneg : ∀ x : ℝ, ‖-x‖ₑ = ‖x‖ₑ := fun x => by simp [Real.enorm_eq_ofReal_abs]
  rw [hneg]
  refine (enorm_tsum_le_tsum_enorm).trans ?_
  rw [tsum_subtype ((F : Set A)ᶜ) (fun a => ‖ξ r ω a * ξ' r ω a‖ₑ)]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ F
  · simp [ha]
  · have := enorm_mul_le_sq_add (ξ r ω a) (ξ' r ω a)
    simpa [ha, enorm_mul] using this


lemma tail_eq (hξ : IsCtbl P ℱ ξ) (t : ℝ) (G : Finset A) :
    ∫⁻ ω, (∫⁻ r in Set.Icc 0 t, ∑' a, ‖if a ∈ G then 0 else ξ r ω a‖ₑ ^ 2) ∂P =
      ∑' b : {x // x ∉ G}, cT P ξ b t := by
  have hprog : ∀ a, IsProgressive ℱ (fun r ω => if a ∈ G then (0:ℝ) else ξ r ω a) := by
    intro a
    by_cases h : a ∈ G
    · simp only [h, ite_true]; exact isProgressive_const ℱ 0
    · simp only [h, ite_false]; exact hξ.prog a
  rw [← pc_tsum_cT (ξ := fun r ω a => if a ∈ G then (0:ℝ) else ξ r ω a) hprog t]
  rw [show ∑' b : {x // x ∉ G}, cT P ξ b t =
    ∑' a, {x : A | x ∉ G}.indicator (fun a => cT P ξ a t) a from
    tsum_subtype {x : A | x ∉ G} (fun a => cT P ξ a t)]
  refine tsum_congr fun a => ?_
  by_cases h : a ∈ G
  · simp [h, cT]
  · simp [h, cT]

lemma tail_tendsto (hξ : IsCtbl P ℱ ξ) (t : ℝ) {F : ℕ → Finset A} (hF : Tendsto F atTop atTop) :
    Tendsto (fun n => ∫⁻ ω, (∫⁻ r in Set.Icc 0 t, ∑' a, ‖if a ∈ F n then 0 else ξ r ω a‖ₑ ^ 2) ∂P)
      atTop (𝓝 0) := by
  simp_rw [tail_eq hξ t]
  exact (ENNReal.tendsto_tsum_compl_atTop_zero (hξ.sq t)).comp hF

lemma measurable_innerSq {w : ℝ → Ω → A → ℝ} (hw : ∀ a, IsProgressive ℱ (fun r ω => w r ω a))
    (t : ℝ) : Measurable fun ω => ∫⁻ r in Set.Icc 0 t, ∑' a, ‖w r ω a‖ₑ ^ 2 := by
  have hm : Measurable fun p : ℝ × Ω => ∑' a, ‖w p.1 p.2 a‖ₑ ^ 2 :=
    Measurable.ennreal_tsum fun a => ((HRS.MRep.isProgressive_measurable_uncurry (hw a))).enorm.pow_const 2
  exact (hm.comp (measurable_swap (α := Ω) (β := ℝ))).lintegral_prod_right'
    (ν := volume.restrict (Set.Icc 0 t))


lemma prog_tl (hξ : ∀ a, IsProgressive ℱ (fun r ω => ξ r ω a)) (G : Finset A) (a : A) :
    IsProgressive ℱ (fun r ω => if a ∈ G then (0:ℝ) else ξ r ω a) := by
  by_cases h : a ∈ G
  · simp only [h, ite_true]; exact isProgressive_const ℱ 0
  · simp only [h, ite_false]; exact hξ a

lemma measurable_slice_sq {w : ℝ → Ω → A → ℝ} (hw : ∀ a, IsProgressive ℱ (fun r ω => w r ω a))
    (ω : Ω) : Measurable fun r => ∑' a, ‖w r ω a‖ₑ ^ 2 :=
  Measurable.ennreal_tsum fun a =>
    (((HRS.MRep.isProgressive_measurable_uncurry (hw a)).comp
      (measurable_prodMk_right (y := ω)))).enorm.pow_const 2

lemma lintegral_tsum_add {f g : ℝ → Ω → A → ℝ} (hf : ∀ a, IsProgressive ℱ (fun r ω => f r ω a))
    (hg : ∀ a, IsProgressive ℱ (fun r ω => g r ω a)) (t : ℝ) (ω : Ω) :
    (∫⁻ r in Set.Icc 0 t, ∑' a, (‖f r ω a‖ₑ ^ 2 + ‖g r ω a‖ₑ ^ 2)) =
      (∫⁻ r in Set.Icc 0 t, ∑' a, ‖f r ω a‖ₑ ^ 2) + (∫⁻ r in Set.Icc 0 t, ∑' a, ‖g r ω a‖ₑ ^ 2) := by
  simp_rw [ENNReal.tsum_add]
  exact lintegral_add_left (measurable_slice_sq hf ω) _

lemma tendsto_compensator (hξ : IsCtbl P ℱ ξ) (hξ' : IsCtbl P ℱ ξ')
    (hs : ∀ r ω, Summable fun a => ξ r ω a ^ 2) (hs' : ∀ r ω, Summable fun a => ξ' r ω a ^ 2)
    (t : ℝ) {F : ℕ → Finset A} (hF : Tendsto F atTop atTop) :
    Tendsto (fun n => ∫⁻ ω, ‖(∫ r in Set.Icc 0 t, ∑ a ∈ F n, ξ r ω a * ξ' r ω a) -
      ∫ r in Set.Icc 0 t, ∑' a, ξ r ω a * ξ' r ω a‖ₑ ∂P) atTop (𝓝 0) := by
  classical
  set U : Finset A → Ω → ℝ≥0∞ := fun G ω =>
    ∫⁻ r in Set.Icc 0 t, ∑' a, ‖if a ∈ G then 0 else ξ r ω a‖ₑ ^ 2 with hU
  set U' : Finset A → Ω → ℝ≥0∞ := fun G ω =>
    ∫⁻ r in Set.Icc 0 t, ∑' a, ‖if a ∈ G then 0 else ξ' r ω a‖ₑ ^ 2 with hU'
  have hUm : ∀ G, Measurable (U G) := fun G => measurable_innerSq (prog_tl hξ.prog G) t
  have hU'm : ∀ G, Measurable (U' G) := fun G => measurable_innerSq (prog_tl hξ'.prog G) t
  have hlim : Tendsto (fun n => ∫⁻ ω, (U (F n) ω + U' (F n) ω) ∂P) atTop (𝓝 0) := by
    have e : ∀ n, ∫⁻ ω, (U (F n) ω + U' (F n) ω) ∂P = ∫⁻ ω, U (F n) ω ∂P + ∫⁻ ω, U' (F n) ω ∂P :=
      fun n => lintegral_add_left (hUm _) _
    simp_rw [e]
    have := (tail_tendsto hξ t hF).add (tail_tendsto hξ' t hF)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => bot_le) ?_
  intro n
  refine lintegral_mono_ae ?_
  -- finiteness a.e.
  have hW : ∀ᵐ ω ∂P, U ∅ ω < ⊤ ∧ U' ∅ ω < ⊤ := by
    have h1 : ∫⁻ ω, U ∅ ω ∂P ≠ ⊤ := by
      simp only [hU]
      rw [tail_eq hξ t ∅]
      exact ne_top_of_le_ne_top (hξ.sq t)
        (ENNReal.tsum_comp_le_tsum_of_injective Subtype.coe_injective (fun a => cT P ξ a t))
    have h2 : ∫⁻ ω, U' ∅ ω ∂P ≠ ⊤ := by
      simp only [hU']
      rw [tail_eq hξ' t ∅]
      exact ne_top_of_le_ne_top (hξ'.sq t)
        (ENNReal.tsum_comp_le_tsum_of_injective Subtype.coe_injective (fun a => cT P ξ' a t))
    filter_upwards [ae_lt_top (hUm ∅) h1, ae_lt_top (hU'm ∅) h2] with ω a b using ⟨a, b⟩
  filter_upwards [hW] with ω ⟨h1, h2⟩
  have hU0 : U ∅ ω = ∫⁻ r in Set.Icc 0 t, ∑' a, ‖ξ r ω a‖ₑ ^ 2 := by simp [hU]
  have hU0' : U' ∅ ω = ∫⁻ r in Set.Icc 0 t, ∑' a, ‖ξ' r ω a‖ₑ ^ 2 := by simp [hU']
  have hslice : ∀ a, Measurable fun r => ξ r ω a := fun a =>
    (HRS.MRep.isProgressive_measurable_uncurry (hξ.prog a)).comp (measurable_prodMk_right (y := ω))
  have hslice' : ∀ a, Measurable fun r => ξ' r ω a := fun a =>
    (HRS.MRep.isProgressive_measurable_uncurry (hξ'.prog a)).comp (measurable_prodMk_right (y := ω))
  set V : ℝ → ℝ≥0∞ := fun r => ∑' a, (‖ξ r ω a‖ₑ ^ 2 + ‖ξ' r ω a‖ₑ ^ 2) with hV
  have hVfin : ∫⁻ r in Set.Icc 0 t, V r < ⊤ := by
    rw [hV, lintegral_tsum_add hξ.prog hξ'.prog t ω, ← hU0, ← hU0']
    exact ENNReal.add_lt_top.2 ⟨h1, h2⟩
  have hbound : ∀ r (G : Finset A), ‖∑ a ∈ G, ξ r ω a * ξ' r ω a‖ₑ ≤ V r := by
    intro r G
    calc ‖∑ a ∈ G, ξ r ω a * ξ' r ω a‖ₑ ≤ ∑ a ∈ G, ‖ξ r ω a * ξ' r ω a‖ₑ := enorm_sum_le _ _
      _ ≤ ∑ a ∈ G, (‖ξ r ω a‖ₑ ^ 2 + ‖ξ' r ω a‖ₑ ^ 2) :=
          Finset.sum_le_sum fun a _ => enorm_mul_le_sq_add _ _
      _ ≤ V r := ENNReal.sum_le_tsum G
  have hboundT : ∀ r, ‖∑' a, ξ r ω a * ξ' r ω a‖ₑ ≤ V r := by
    intro r
    calc ‖∑' a, ξ r ω a * ξ' r ω a‖ₑ ≤ ∑' a, ‖ξ r ω a * ξ' r ω a‖ₑ := enorm_tsum_le_tsum_enorm
      _ ≤ V r := ENNReal.tsum_le_tsum fun a => enorm_mul_le_sq_add _ _
  have hint : ∀ f : ℝ → ℝ, Measurable f → (∀ r, ‖f r‖ₑ ≤ V r) → IntegrableOn f (Set.Icc 0 t) := by
    intro f hf hfV
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    exact lt_of_le_of_lt (lintegral_mono hfV) hVfin
  have hmc : Measurable fun r => ∑ a ∈ F n, ξ r ω a * ξ' r ω a :=
    Finset.measurable_sum _ fun a _ => (hslice a).mul (hslice' a)
  have hmT : Measurable fun r => ∑' a, ξ r ω a * ξ' r ω a :=
    Measurable.tsum fun a => (hslice a).mul (hslice' a)
  have hi1 := hint _ hmc (fun r => hbound r (F n))
  have hi2 := hint _ hmT hboundT
  rw [← integral_sub hi1 hi2]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  have hpt : ∀ r, ‖(∑ a ∈ F n, ξ r ω a * ξ' r ω a) - ∑' a, ξ r ω a * ξ' r ω a‖ₑ ≤
      ∑' a, (‖if a ∈ F n then 0 else ξ r ω a‖ₑ ^ 2 + ‖if a ∈ F n then 0 else ξ' r ω a‖ₑ ^ 2) :=
    fun r => compensator_pointwise hs hs' (F n) r ω
  refine (lintegral_mono hpt).trans (le_of_eq ?_)
  have := lintegral_tsum_add (f := fun r ω a => if a ∈ F n then (0:ℝ) else ξ r ω a)
    (g := fun r ω a => if a ∈ F n then (0:ℝ) else ξ' r ω a) (prog_tl hξ.prog (F n))
    (prog_tl hξ'.prog (F n)) t ω
  exact this


variable {𝔚 : ℝ≥0 → Ω → A → ℝ} {I I' : ℝ → Ω → ℝ}

/-- Random-bracket martingale for countable-index Itô integrals. -/
theorem isItoC_martingale_mul_sub_random (hW : IsCylindricalBrownian P ℱ 𝔚) (hξ : IsCtbl P ℱ ξ)
    (hξ' : IsCtbl P ℱ ξ') (hI : IsItoC P ℱ 𝔚 ξ I) (hI' : IsItoC P ℱ 𝔚 ξ' I')
    (hs : ∀ r ω, Summable fun a => ξ r ω a ^ 2) (hs' : ∀ r ω, Summable fun a => ξ' r ω a ^ 2) :
    Martingale (fun t ω => I t ω * I' t ω - ∫ r in Set.Icc 0 t, ∑' a, ξ r ω a * ξ' r ω a) ℱ P := by
  obtain ⟨F, hF⟩ := exists_finset_seq (A := A)
  have hX : ∀ n, Martingale (fun t ω => ItoF P ℱ 𝔚 ξ (F n) t ω * ItoF P ℱ 𝔚 ξ' (F n) t ω -
      ∫ r in Set.Icc 0 t, ∑ a ∈ F n, ξ r ω a * ξ' r ω a) ℱ P := by
    intro n
    have h := martingale_itoIntegral_mul_sub (hW (F n)) (hξ.progressiveL2 (F n))
      (hξ'.progressiveL2 (F n))
    convert h using 3 with t ω
    simp only [covProcess, ξF]
    congr 1
    refine setIntegral_congr_fun measurableSet_Icc fun r _ => ?_
    exact (Finset.sum_coe_sort (F n) (fun a => ξ r ω a * ξ' r ω a)).symm
  have hmeasI : ∀ t, Measurable (I t) := fun t => (hI.adapted t).mono (ℱ.le t) le_rfl
  have hmeasI' : ∀ t, Measurable (I' t) := fun t => (hI'.adapted t).mono (ℱ.le t) le_rfl
  have hjoint : Measurable fun p : ℝ × Ω => ∑' a, ξ p.1 p.2 a * ξ' p.1 p.2 a :=
    Measurable.tsum fun a => (HRS.MRep.isProgressive_measurable_uncurry (hξ.prog a)).mul
      (HRS.MRep.isProgressive_measurable_uncurry (hξ'.prog a))
  have hWm : ∀ t, Measurable fun ω => I t ω * I' t ω - ∫ r in Set.Icc 0 t, ∑' a, ξ r ω a * ξ' r ω a :=
    fun t => ((hmeasI t).mul (hmeasI' t)).sub
      (measurable_setIntegral_Icc (fun p : ℝ × Ω => ∑' a, ξ p.1 p.2 a * ξ' p.1 p.2 a) hjoint 0 t)
  refine HRS.MRep.martingale_of_L1_limit' (hW ∅).complete (fun n => hX n) hWm ?_
  intro t
  by_cases ht : 0 ≤ t
  · -- the product part
    have hL2 : ∀ (J : ℝ → Ω → ℝ) (ζ : ℝ → Ω → A → ℝ) (hζ : IsCtbl P ℱ ζ) (hJ : IsItoC P ℱ 𝔚 ζ J),
        Tendsto (fun n => eLpNorm (fun ω => ItoF P ℱ 𝔚 ζ (F n) t ω - J t ω) 2 P) atTop (𝓝 0) := by
      intro J ζ hζ hJ
      have h1 := (hJ.approx t ht).comp hF
      refine HRS.MRep.tendsto_of_tendsto_sq (h1.congr fun n => ?_)
      exact HRS.lintegral_enorm_sq_eq_eLpNorm_sq
        (((aemeasurable_ItoF (P := P) (ℱ := ℱ) (𝔚 := 𝔚) (ξ := ζ) (F n) t).sub
          (hJ.aemeasurable t)).aestronglyMeasurable)
    have hAB := HRS.MRep.tendsto_eLpNorm_mul_pair (P := P)
      (a := fun n ω => ItoF P ℱ 𝔚 ξ (F n) t ω) (b := fun n ω => ItoF P ℱ 𝔚 ξ' (F n) t ω)
      (a₀ := I t) (b₀ := I' t) (hI'.memLp hξ' hW ht).eLpNorm_ne_top (hI.memLp hξ hW ht).eLpNorm_ne_top
      (hL2 I ξ hξ hI) (hL2 I' ξ' hξ' hI')
    have hAB1 : Tendsto (fun n => ∫⁻ ω, ‖ItoF P ℱ 𝔚 ξ (F n) t ω * ItoF P ℱ 𝔚 ξ' (F n) t ω -
        I t ω * I' t ω‖ₑ ∂P) atTop (𝓝 0) := by
      refine hAB.congr fun n => ?_
      rw [eLpNorm_one_eq_lintegral_enorm]
      exact (((aemeasurable_ItoF (P := P) (ℱ := ℱ) (𝔚 := 𝔚) (ξ := ξ) (F n) t).mul
        (aemeasurable_ItoF (P := P) (ℱ := ℱ) (𝔚 := 𝔚) (ξ := ξ') (F n) t)).sub
        ((hmeasI t).mul (hmeasI' t)).aemeasurable).aestronglyMeasurable
    have hcomp := tendsto_compensator hξ hξ' hs hs' t hF
    have hsum := hAB1.add hcomp
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun n => bot_le) fun n => ?_
    have hmA : AEMeasurable (fun ω => ‖ItoF P ℱ 𝔚 ξ (F n) t ω * ItoF P ℱ 𝔚 ξ' (F n) t ω -
        I t ω * I' t ω‖ₑ) P :=
      (((aemeasurable_ItoF (P := P) (ℱ := ℱ) (𝔚 := 𝔚) (ξ := ξ) (F n) t).mul
        (aemeasurable_ItoF (P := P) (ℱ := ℱ) (𝔚 := 𝔚) (ξ := ξ') (F n) t)).sub
        ((hmeasI t).mul (hmeasI' t)).aemeasurable).enorm
    rw [← lintegral_add_left' hmA]
    refine lintegral_mono fun ω => ?_
    have : (ItoF P ℱ 𝔚 ξ (F n) t ω * ItoF P ℱ 𝔚 ξ' (F n) t ω -
          ∫ r in Set.Icc 0 t, ∑ a ∈ F n, ξ r ω a * ξ' r ω a) -
        (I t ω * I' t ω - ∫ r in Set.Icc 0 t, ∑' a, ξ r ω a * ξ' r ω a) =
        (ItoF P ℱ 𝔚 ξ (F n) t ω * ItoF P ℱ 𝔚 ξ' (F n) t ω - I t ω * I' t ω) -
        ((∫ r in Set.Icc 0 t, ∑ a ∈ F n, ξ r ω a * ξ' r ω a) -
          ∫ r in Set.Icc 0 t, ∑' a, ξ r ω a * ξ' r ω a) := by ring
    rw [this]
    exact enorm_sub_le
  · -- negative times: everything vanishes
    push Not at ht
    have hz : ∀ n ω, (ItoF P ℱ 𝔚 ξ (F n) t ω * ItoF P ℱ 𝔚 ξ' (F n) t ω -
        ∫ r in Set.Icc 0 t, ∑ a ∈ F n, ξ r ω a * ξ' r ω a) -
        (I t ω * I' t ω - ∫ r in Set.Icc 0 t, ∑' a, ξ r ω a * ξ' r ω a) = 0 := by
      intro n ω
      simp [ItoF, itoIntegral_of_nonpos _ _ _ _ ht.le, hI.zero t ht.le, hI'.zero t ht.le,
        Set.Icc_eq_empty (not_le.2 ht)]
    simp only [hz, enorm_zero, lintegral_zero]
    exact tendsto_const_nhds

end Bracket

end HRS.Uniform.Q07c
