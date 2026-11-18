import HRS.MS.SpecAux64

/-!
# S8R: the convolution bound `E‖D(t)‖² ≤ C sup_r E‖S_r - Sb_r‖²_HS` (S8.7, packet C6)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_conv_bound`: for the `ℓ²`-valued Itô integral `D` of the killed integrand
`1_{r ≤ t} e^{-(t-r)ω}(S_r - Sb_r) b_j` against the cylindrical Brownian motion `B`, if `E ∑_j ‖(S_r - Sb_r) b_j‖² ≤ Z` for all
`r ∈ [0,T]`, then `E ‖D(t)‖² ≤ 2 Z/(2 ω_0)`, uniformly in `t ∈ [0,T]`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace HRS.MS.Spec

open HRS HRS.Whole

theorem s8p_conv_bound {Ω Ω' : Type} {mΩ' : MeasurableSpace Ω'} [MeasurableSpace Ω]
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {π : Ω' → Ω} {ℱ' : Filtration ℝ mΩ'}
    {B : ℝ≥0 → Ω' → ℕ → ℝ} (hB : IsCylindricalBrownian P' ℱ' B) {β : ℝ} (hβ : 0 < β)
    {om : ℕ → ℝ} (hom : ∀ l, 0 < om l) (hmono : Monotone om) {τ : ℝ} (hτ : 0 < τ)
    {S : ℝ → Ω → SeqL2 →L[ℝ] SeqL2} {Sb : ℝ → SeqL2 →L[ℝ] SeqL2} {T : ℝ}
    (hSprog : ∀ x y, IsProgressive ℱ' (fun r w => ⟪S r (π w) x, y⟫))
    (hSb : ∀ r ∈ Set.Icc 0 T, IsSqrtOfForm (Sb r) (s8p_Cdet hβ hom hτ)) {Z : ℝ≥0∞} (hZ : Z ≠ ⊤)
    (hbound : ∀ r ∈ Set.Icc 0 T, ∫⁻ w, ∑' j, ‖(S r (π w) - Sb r) (S45.s45_seqBasis j)‖ₑ ^ 2 ∂P' ≤ Z)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) {D : ℝ → Ω' → SeqL2}
    (hD : IsHilbertItoIntegral P' ℱ' B (fun r w j => if r ≤ t then
      semiDiag om (t - r) ((S r (π w) - Sb r) (S45.s45_seqBasis j)) else 0) D) :
    ∫⁻ w, ‖D t w‖ₑ ^ 2 ∂P' ≤ 2 * (Z * ENNReal.ofReal (1 / (2 * om 0))) := by
  set b := S45.s45_seqBasis with hb
  set ee : ℕ → ℝ := fun k => Real.sqrt (s8p_dv β om τ k) with hee
  have hSbk : ∀ r ∈ Set.Icc 0 T, ∀ k, Sb r (b k) = ee k • b k := fun r hr k =>
    s8p_sqrt_basis hβ hom hτ (hSb r hr) k
  set Ψ' : ℝ → Ω' → ℕ → SeqL2 := fun r w k =>
    if 0 ≤ r ∧ r ≤ t then semiDiag om (t - r) (S r (π w) (b k) - ee k • b k) else 0 with hΨ'
  have hΨΨ' : ∀ r, 0 ≤ r → ∀ w k, (if r ≤ t then
      semiDiag om (t - r) ((S r (π w) - Sb r) (b k)) else 0) = Ψ' r w k := by
    intro r hr w k
    by_cases hrt : r ≤ t
    · simp only [hΨ', hr, hrt, and_self, if_true]
      rw [ContinuousLinearMap.sub_apply, hSbk r ⟨hr, hrt.trans ht.2⟩ k]
    · simp [hΨ', hrt]
  -- coordinates
  set g : ℕ → ℝ → ℝ := fun l => Set.indicator (Set.Icc 0 t) (fun r => Real.exp (-(t - r) * om l)) with hg
  have hgm : ∀ l, Measurable (g l) := fun l =>
    (by fun_prop : Measurable fun r : ℝ => Real.exp (-(t - r) * om l)).indicator measurableSet_Icc
  have hcoord : ∀ r w k l, SeqL2.coord (Ψ' r w k) l =
      g l r * (⟪S r (π w) (b k), b l⟫ - ee k * (if l = k then 1 else 0)) := by
    intro r w k l
    by_cases hr : 0 ≤ r ∧ r ≤ t
    · have hrI : r ∈ Set.Icc 0 t := hr
      simp only [hΨ', hr, and_self, if_true, hg, Set.indicator_of_mem hrI]
      rw [s8p_coord_semiDiag hom (by linarith [hr.2]), u11_coord_sub, s8p_coord_smul,
        s8p_coord_basis, ← s8p_inner_basis]
    · have hrI : r ∉ Set.Icc 0 t := hr
      simp only [hΨ', hr, if_false, hg, Set.indicator_of_notMem hrI]
      have h0 : SeqL2.coord (0 : SeqL2) l = 0 := rfl
      rw [h0]; ring
  have hprog : ∀ k l, IsProgressive ℱ' (fun r w => SeqL2.coord (Ψ' r w k) l) := by
    intro k l
    simp_rw [hcoord]
    refine s8p_isProgressive_mul (f := fun r w => ⟪S r (π w) (b k), b l⟫ -
      ee k * (if l = k then 1 else 0)) (fun i => ?_) (hgm l)
    exact (hSprog (b k) (b l) i).sub measurable_const
  -- the pointwise bound
  set Zf : ℝ → Ω' → ℝ≥0∞ := fun r w => ∑' k, ‖S r (π w) (b k) - ee k • b k‖ₑ ^ 2 with hZf
  set K : ℝ → ℝ≥0∞ := Set.indicator (Set.Icc 0 t)
    (fun r => ENNReal.ofReal (Real.exp (-(2 * (t - r) * om 0)))) with hK
  have hKm : Measurable K := (ENNReal.measurable_ofReal.comp
    (by fun_prop : Measurable fun r : ℝ => Real.exp (-(2 * (t - r) * om 0)))).indicator measurableSet_Icc
  have hpt : ∀ r w, ∑' k, ‖Ψ' r w k‖ₑ ^ 2 ≤ K r * Zf r w := by
    intro r w
    by_cases hr : r ∈ Set.Icc 0 t
    · simp only [hK, Set.indicator_of_mem hr, hZf, ← ENNReal.tsum_mul_left]
      refine ENNReal.tsum_le_tsum fun k => ?_
      have hr' : 0 ≤ r ∧ r ≤ t := hr
      simp only [hΨ', hr', and_self, if_true]
      exact s8p_semiDiag_enorm_sq_le hom hmono (by linarith [hr.2]) _
    · have hr' : ¬ (0 ≤ r ∧ r ≤ t) := hr
      simp [hΨ', hr', hK, Set.indicator_of_notMem hr]
  have hZfm : Measurable fun q : Ω' × ℝ => Zf q.2 q.1 := by
    have : ∀ q : Ω' × ℝ, Zf q.2 q.1 = ∑' k, ∑' l, ENNReal.ofReal
        ((⟪S q.2 (π q.1) (b k), b l⟫ - ee k * (if l = k then 1 else 0)) ^ 2) := by
      intro q
      simp only [hZf]
      refine tsum_congr fun k => ?_
      rw [s8p_seq_enorm_sq]
      refine tsum_congr fun l => ?_
      rw [u11_coord_sub, s8p_coord_smul, s8p_coord_basis, ← s8p_inner_basis]
    simp_rw [this]
    refine Measurable.ennreal_tsum fun k => Measurable.ennreal_tsum fun l =>
      ENNReal.measurable_ofReal.comp ((?_ : Measurable _).pow_const 2)
    exact ((HRS.MRep.isProgressive_measurable_uncurry (hSprog (b k) (b l))).comp
      measurable_swap).sub measurable_const
  have hZfb : ∀ r ∈ Set.Icc 0 t, ∫⁻ w, Zf r w ∂P' ≤ Z := by
    intro r hr
    have hrT : r ∈ Set.Icc 0 T := ⟨hr.1, hr.2.trans ht.2⟩
    refine le_trans (le_of_eq ?_) (hbound r hrT)
    refine lintegral_congr fun w => tsum_congr fun k => ?_
    rw [ContinuousLinearMap.sub_apply, hSbk r hrT k]
  have hKint : ∀ T' : ℝ, ∫⁻ r in Set.Icc 0 T', K r ≤ ENNReal.ofReal (1 / (2 * om 0)) := by
    intro T'
    have h1 : ∫⁻ r in Set.Icc 0 T', K r = ∫⁻ r in Set.Icc 0 T' ∩ Set.Icc 0 t,
        ENNReal.ofReal (Real.exp (-(2 * (t - r) * om 0))) := by
      rw [hK, lintegral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
        Set.inter_comm]
    rw [h1]
    refine (lintegral_mono_set Set.inter_subset_right).trans ?_
    have := s8p_lintegral_exp_le (c := 2 * om 0) (by linarith [hom 0]) ht.1
    refine le_trans (le_of_eq ?_) this
    refine lintegral_congr fun r => ?_
    congr 2
    ring
  -- the master estimate
  have hmaster : ∀ T' : ℝ, ∫⁻ w, (∫⁻ r in Set.Icc 0 T', ∑' k, ‖Ψ' r w k‖ₑ ^ 2) ∂P' ≤
      Z * ENNReal.ofReal (1 / (2 * om 0)) := by
    intro T'
    calc ∫⁻ w, (∫⁻ r in Set.Icc 0 T', ∑' k, ‖Ψ' r w k‖ₑ ^ 2) ∂P'
        ≤ ∫⁻ w, (∫⁻ r in Set.Icc 0 T', K r * Zf r w) ∂P' :=
          lintegral_mono fun w => lintegral_mono fun r => hpt r w
      _ = ∫⁻ r in Set.Icc 0 T', (∫⁻ w, K r * Zf r w ∂P') := by
          refine lintegral_lintegral_swap ?_
          refine (?_ : Measurable fun q : Ω' × ℝ => K q.2 * Zf q.2 q.1).aemeasurable
          refine Measurable.mul ?_ hZfm
          exact hKm.comp measurable_snd
      _ ≤ ∫⁻ r in Set.Icc 0 T', K r * Z := by
          refine lintegral_mono fun r => ?_
          by_cases hr : r ∈ Set.Icc 0 t
          · rw [lintegral_const_mul' _ _ (by simp [hK, Set.indicator_of_mem hr])]
            exact mul_le_mul_right (hZfb r hr) _
          · simp [hK, Set.indicator_of_notMem hr]
      _ = (∫⁻ r in Set.Icc 0 T', K r) * Z := lintegral_mul_const' _ _ hZ
      _ ≤ ENNReal.ofReal (1 / (2 * om 0)) * Z := by gcongr; exact hKint T'
      _ = _ := mul_comm _ _
  have hfin : ∀ T', ∫⁻ w, (∫⁻ r in Set.Icc 0 T', ∑' k, ‖Ψ' r w k‖ₑ ^ 2) ∂P' < ⊤ := fun T' =>
    lt_of_le_of_lt (hmaster T') (ENNReal.mul_lt_top hZ.lt_top ENNReal.ofReal_lt_top)
  exact (s8p_ito_sq_le hB hD hΨΨ' hprog hfin t ht.1).trans (by gcongr; exact hmaster t)

end HRS.MS.Spec
