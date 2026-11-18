import HRS.MS.SpecAux62

/-!
# S8R: the Itô inequality `E‖D_τ‖² ≤ 2 E ∫_0^τ ∑_k ‖Ψ_k‖²` for `ℓ²`-valued integrals (S8.7, packet C6)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_ito_sq_le`: if `D = ∫ Ψ dB` in the sense of `IsHilbertItoIntegral` (coordinatewise
`L²` limits of real Itô integrals over finite sets of indices), `Ψ` agrees on `[0,∞)` with an integrand `Ψ'` whose standard
coordinates are progressive and `L²`, then `E‖D_τ‖² ≤ 2 E ∫_0^τ ∑_k ‖Ψ'_k‖² dr`.  (The factor `2` comes from
`(a+b)² ≤ 2a² + 2b²` in the passage to the limit; only the order of magnitude is used.)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace HRS.MS.Spec

open HRS HRS.Whole

/-- The scalar coordinate integrand is bounded by the norm. -/
theorem s8p_coord_enorm_le (z : SeqL2) (l : ℕ) : ‖SeqL2.coord z l‖ₑ ≤ ‖z‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  have := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (show lp (fun _ : ℕ => ℝ) 2 from z) l
  exact this

theorem s8p_coord_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {f : Ω → SeqL2} (hf : Measurable f)
    (l : ℕ) : Measurable fun w => SeqL2.coord (f w) l := by
  have : (fun w => SeqL2.coord (f w) l) = fun w => ⟪f w, S45.s45_seqBasis l⟫ := by
    funext w; rw [s8p_inner_basis]
  rw [this]
  exact hf.inner measurable_const

theorem s8p_ito_sq_le {Ω' : Type} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {ℱ' : Filtration ℝ mΩ'} {B : ℝ≥0 → Ω' → ℕ → ℝ} (hB : IsCylindricalBrownian P' ℱ' B)
    {Ψ Ψ' : ℝ → Ω' → ℕ → SeqL2} {D : ℝ → Ω' → SeqL2}
    (hD : IsHilbertItoIntegral P' ℱ' B Ψ D)
    (hΨΨ' : ∀ r, 0 ≤ r → ∀ w k, Ψ r w k = Ψ' r w k)
    (hprog : ∀ k l, IsProgressive ℱ' (fun r w => SeqL2.coord (Ψ' r w k) l))
    (hfin : ∀ T', ∫⁻ w, (∫⁻ r in Set.Icc 0 T', ∑' k, ‖Ψ' r w k‖ₑ ^ 2) ∂P' < ⊤)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    ∫⁻ w, ‖D τ w‖ₑ ^ 2 ∂P' ≤ 2 * ∫⁻ w, (∫⁻ r in Set.Icc 0 τ, ∑' k, ‖Ψ' r w k‖ₑ ^ 2) ∂P' := by
  -- joint measurability of the coordinates
  have hjm : ∀ k l, Measurable fun q : Ω' × ℝ => SeqL2.coord (Ψ' q.2 q.1 k) l := fun k l =>
    (HRS.MRep.isProgressive_measurable_uncurry (hprog k l)).comp measurable_swap
  have hGm : ∀ l, Measurable fun q : Ω' × ℝ => ∑' k, ENNReal.ofReal (SeqL2.coord (Ψ' q.2 q.1 k) l ^ 2) :=
    fun l => Measurable.ennreal_tsum fun k => ENNReal.measurable_ofReal.comp ((hjm k l).pow_const 2)
  -- the per-coordinate bound
  have hcoord : ∀ l, ∫⁻ w, ENNReal.ofReal (SeqL2.coord (D τ w) l ^ 2) ∂P' ≤
      2 * ∫⁻ w, (∫⁻ r in Set.Icc 0 τ, ∑' k, ENNReal.ofReal (SeqL2.coord (Ψ' r w k) l ^ 2)) ∂P' := by
    intro l
    set A := ∫⁻ w, (∫⁻ r in Set.Icc 0 τ, ∑' k, ENNReal.ofReal (SeqL2.coord (Ψ' r w k) l ^ 2)) ∂P' with hA
    have hDm : Measurable (D τ) := (hD.adapted τ).mono (ℱ'.le τ) le_rfl
    have hYm : Measurable fun w => SeqL2.coord (D τ w) l := s8p_coord_measurable hDm l
    have hbound : ∀ s : Finset ℕ, ∫⁻ w, ENNReal.ofReal (SeqL2.coord (D τ w) l ^ 2) ∂P' ≤
        2 * A + 2 * ∫⁻ w, ‖itoIntegral P' ℱ' (fun t ω (k : s) => B t ω k)
          (fun r ω (k : s) => inner ℝ (Ψ r ω k) (S45.s45_seqBasis l)) τ w -
            inner ℝ (D τ w) (S45.s45_seqBasis l)‖ₑ ^ 2 ∂P' := by
      intro s
      have hBs : IsBrownianFiltration P' ℱ' (fun t ω (k : s) => B t ω k) := hB s
      set φ' : ℝ → Ω' → s → ℝ := fun r ω k => SeqL2.coord (Ψ' r ω k) l with hφ'
      have hprogL2 : IsProgressiveL2 P' ℱ' φ' := by
        refine ⟨fun i => ?_, fun T' => ?_⟩
        · letI : MeasurableSpace (Set.Iic i × Ω') := Subtype.instMeasurableSpace.prod (ℱ' i)
          exact measurable_pi_iff.2 fun k => hprog k l i
        unfold sqIntegralOn
        refine lt_of_le_of_lt (lintegral_mono fun w => lintegral_mono fun r => ?_) (hfin T')
        calc ∑ k : s, ‖φ' r w k‖ₑ ^ 2 ≤ ∑ k : s, ‖Ψ' r w k‖ₑ ^ 2 :=
              Finset.sum_le_sum fun k _ => pow_le_pow_left' (s8p_coord_enorm_le _ l) 2
          _ = ∑ k ∈ s, ‖Ψ' r w k‖ₑ ^ 2 := Finset.sum_coe_sort s fun k => ‖Ψ' r w k‖ₑ ^ 2
          _ ≤ ∑' k, ‖Ψ' r w k‖ₑ ^ 2 := ENNReal.sum_le_tsum s
      have hcongr : itoIntegral P' ℱ' (fun t ω (k : s) => B t ω k)
          (fun r ω (k : s) => inner ℝ (Ψ r ω k) (S45.s45_seqBasis l)) = itoIntegral P' ℱ'
            (fun t ω (k : s) => B t ω k) φ' := by
        refine s8p_itoIntegral_congr P' ℱ' _ fun r hr w k => ?_
        simp only [hφ', hΨΨ' r hr w k, s8p_inner_basis]
      rw [hcongr]
      set I : Ω' → ℝ := itoIntegral P' ℱ' (fun t ω (k : s) => B t ω k) φ' τ with hI
      have hIm : Measurable I := ((adapted_itoIntegral P' ℱ' _ φ') τ).mono (ℱ'.le τ) le_rfl
      have hIsq : ∫⁻ w, ENNReal.ofReal (I w ^ 2) ∂P' ≤ A := by
        have h1 := lintegral_itoIntegral_sq hBs hprogL2 τ
        have h2 : ∫⁻ w, ENNReal.ofReal (I w ^ 2) ∂P' = ∫⁻ w, ‖I w‖ₑ ^ 2 ∂P' :=
          lintegral_congr fun w => (s8p_enorm_sq_eq _).symm
        rw [h2, h1]
        unfold sqIntegralOn
        refine lintegral_mono fun w => lintegral_mono fun r => ?_
        calc ∑ k : s, ‖φ' r w k‖ₑ ^ 2 = ∑ k ∈ s, ENNReal.ofReal (SeqL2.coord (Ψ' r w k) l ^ 2) := by
              rw [← Finset.sum_coe_sort s fun k => ENNReal.ofReal (SeqL2.coord (Ψ' r w k) l ^ 2)]
              exact Finset.sum_congr rfl fun k _ => s8p_enorm_sq_eq _
          _ ≤ _ := ENNReal.sum_le_tsum s
      have hpt : ∀ w, ENNReal.ofReal (SeqL2.coord (D τ w) l ^ 2) ≤
          2 * ENNReal.ofReal (I w ^ 2) + 2 * ‖I w - inner ℝ (D τ w) (S45.s45_seqBasis l)‖ₑ ^ 2 := by
        intro w
        rw [s8p_enorm_sq_eq, ← s8p_inner_basis]
        have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
        rw [h2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith [sq_nonneg (2 * I w - inner ℝ (D τ w) (S45.s45_seqBasis l))]
      have hIYm : Measurable fun w => ‖I w - inner ℝ (D τ w) (S45.s45_seqBasis l)‖ₑ ^ 2 :=
        ((hIm.sub (hDm.inner measurable_const)).enorm).pow_const 2
      calc ∫⁻ w, ENNReal.ofReal (SeqL2.coord (D τ w) l ^ 2) ∂P'
          ≤ ∫⁻ w, (2 * ENNReal.ofReal (I w ^ 2) +
              2 * ‖I w - inner ℝ (D τ w) (S45.s45_seqBasis l)‖ₑ ^ 2) ∂P' := lintegral_mono hpt
        _ = 2 * ∫⁻ w, ENNReal.ofReal (I w ^ 2) ∂P' +
              2 * ∫⁻ w, ‖I w - inner ℝ (D τ w) (S45.s45_seqBasis l)‖ₑ ^ 2 ∂P' := by
            have hm1 : Measurable fun w => ENNReal.ofReal (I w ^ 2) :=
              ENNReal.measurable_ofReal.comp (hIm.pow_const 2)
            rw [lintegral_add_left (f := fun w => 2 * ENNReal.ofReal (I w ^ 2))
              (measurable_const.mul hm1),
              lintegral_const_mul (f := fun w => ENNReal.ofReal (I w ^ 2)) 2 hm1,
              lintegral_const_mul (f := fun w => ‖I w - inner ℝ (D τ w) (S45.s45_seqBasis l)‖ₑ ^ 2) 2 hIYm]
        _ ≤ 2 * A + 2 * ∫⁻ w, ‖I w - inner ℝ (D τ w) (S45.s45_seqBasis l)‖ₑ ^ 2 ∂P' := by
            gcongr
    have hlim := hD.approx τ hτ (S45.s45_seqBasis l)
    have hg : Tendsto (fun s : Finset ℕ => 2 * A + 2 * ∫⁻ w, ‖itoIntegral P' ℱ'
        (fun t ω (k : s) => B t ω k) (fun r ω (k : s) => inner ℝ (Ψ r ω k) (S45.s45_seqBasis l)) τ w -
          inner ℝ (D τ w) (S45.s45_seqBasis l)‖ₑ ^ 2 ∂P') atTop (𝓝 (2 * A + 2 * 0)) :=
      tendsto_const_nhds.add (ENNReal.Tendsto.const_mul hlim (Or.inr (by simp)))
    simpa using ge_of_tendsto' hg hbound
  have hDm : Measurable (D τ) := (hD.adapted τ).mono (ℱ'.le τ) le_rfl
  have e1 : ∀ w, ‖D τ w‖ₑ ^ 2 = ∑' l, ENNReal.ofReal (SeqL2.coord (D τ w) l ^ 2) :=
    fun w => s8p_seq_enorm_sq _
  simp_rw [e1]
  rw [lintegral_tsum (f := fun l w => ENNReal.ofReal (SeqL2.coord (D τ w) l ^ 2))
    (fun l => (ENNReal.measurable_ofReal.comp
      ((s8p_coord_measurable hDm l).pow_const 2)).aemeasurable)]
  have hFm : ∀ l, Measurable fun w : Ω' => ∫⁻ r in Set.Icc 0 τ,
      ∑' k, ENNReal.ofReal (SeqL2.coord (Ψ' r w k) l ^ 2) := fun l =>
    Measurable.lintegral_prod_right' (f := fun q : Ω' × ℝ =>
      ∑' k, ENNReal.ofReal (SeqL2.coord (Ψ' q.2 q.1 k) l ^ 2)) (hGm l)
  calc ∑' l, ∫⁻ w, ENNReal.ofReal (SeqL2.coord (D τ w) l ^ 2) ∂P'
      ≤ ∑' l, 2 * ∫⁻ w, (∫⁻ r in Set.Icc 0 τ,
          ∑' k, ENNReal.ofReal (SeqL2.coord (Ψ' r w k) l ^ 2)) ∂P' := ENNReal.tsum_le_tsum hcoord
    _ = 2 * ∑' l, ∫⁻ w, (∫⁻ r in Set.Icc 0 τ,
          ∑' k, ENNReal.ofReal (SeqL2.coord (Ψ' r w k) l ^ 2)) ∂P' := ENNReal.tsum_mul_left
    _ = 2 * ∫⁻ w, ∑' l, (∫⁻ r in Set.Icc 0 τ,
          ∑' k, ENNReal.ofReal (SeqL2.coord (Ψ' r w k) l ^ 2)) ∂P' := by
        rw [lintegral_tsum (f := fun l w => ∫⁻ r in Set.Icc 0 τ,
          ∑' k, ENNReal.ofReal (SeqL2.coord (Ψ' r w k) l ^ 2)) fun l => (hFm l).aemeasurable]
    _ = 2 * ∫⁻ w, (∫⁻ r in Set.Icc 0 τ, ∑' k, ‖Ψ' r w k‖ₑ ^ 2) ∂P' := by
        congr 1
        refine lintegral_congr fun w => ?_
        rw [← lintegral_tsum (f := fun l r => ∑' k, ENNReal.ofReal (SeqL2.coord (Ψ' r w k) l ^ 2))
          fun l => ((hGm l).comp (measurable_prodMk_left (x := w))).aemeasurable]
        refine lintegral_congr fun r => ?_
        rw [ENNReal.tsum_comm]
        exact tsum_congr fun k => (s8p_seq_enorm_sq _).symm

end HRS.MS.Spec
