import HRS.MS.SA12V3T

/-!
# S.A.12 C2 (SA12V3 worker): `sa12v3_periodic_initial_bounds`

The statement of the skeleton theorem `periodic_initial_bounds` (`SA12-CONSTRUCTION`, C2), with the explicit hypotheses
`1 ≤ d`, `IsUlocCutoff χ`, `IsCutoffRad (1/4) (1/3) ζ`, `IsMollifier η`, proved:
`BddJets`, periodicity, the uloc bound (part O), the weighted `varpiNormE` bound (part R) and the weak convergence of the
datum (part T) for `periodicDatum ζ η L ε φ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Pointwise

namespace HRS.MH.AdjointRd.Phase2SA12V3

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12v3_latticePt_norm_ge {z : Fin d → ℤ} (hz : z ≠ 0) : 1 ≤ ‖(latticePt z : Euc d)‖ := by
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra hcon; push_neg at hcon; exact hz (funext hcon)
  have h1 : |(latticePt z : Euc d) i| ≤ ‖(latticePt z : Euc d)‖ := by
    have := PiLp.norm_apply_le (latticePt z : Euc d) i
    simpa [Real.norm_eq_abs] using this
  have h2 : (1 : ℝ) ≤ |(latticePt z : Euc d) i| := by
    have : (1 : ℤ) ≤ |z i| := Int.one_le_abs hi
    have h3 : (1 : ℝ) ≤ |(z i : ℝ)| := by exact_mod_cast this
    simpa [latticePt] using h3
  linarith

theorem sa12v3_g_supp {ζ : Euc d → ℝ} (hζ : HRS.Whole.AppendixALemmas.IsCutoffRad (1 / 4) (1 / 3) ζ) {L : ℝ}
    (hL0 : 0 < L) (w : Euc d → ℝ) : ∀ y : Euc d, L / 3 ≤ ‖y‖ → ζ (L⁻¹ • y) * w y = 0 := by
  intro y hy
  by_contra hne
  have hz1 : ζ (L⁻¹ • y) ≠ 0 := fun h => hne (by simp [h])
  have h1 : L⁻¹ • y ∈ Metric.ball (0 : Euc d) (1 / 3) :=
    hζ.2.2.1 (subset_tsupport _ (Function.mem_support.2 hz1))
  rw [Metric.mem_ball, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hL0] at h1
  have : ‖y‖ < L / 3 := by
    have := mul_lt_mul_of_pos_left h1 hL0
    rw [← mul_assoc, mul_inv_cancel₀ hL0.ne', one_mul] at this
    linarith
  linarith

theorem sa12v3_pd_regular {η ζ χ : Euc d → ℝ} (hη : IsMollifier η) (hχ : IsUlocCutoff χ)
    (hζ : HRS.Whole.AppendixALemmas.IsCutoffRad (1 / 4) (1 / 3) ζ) (m : ℕ) {φ : Euc d → ℝ}
    (hφ : ulocNormE m χ φ < ⊤) {L ε : ℝ} (hL : 1 ≤ L) (hε : 0 < ε) :
    BddJets m (periodicDatum ζ η L ε φ) ∧
      ∀ (x : Euc d) (k : Fin d → ℤ), periodicDatum ζ η L ε φ (x + L • latticePt k) =
        periodicDatum ζ η L ε φ x := by
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have hε' : 0 < min ε 1 := lt_min hε one_pos
  have hli := sa12v3_locInt_of_uloc hχ hφ
  have hg : ContDiff ℝ ∞ (fun x => ζ (L⁻¹ • x) * mollify η (min ε 1) φ x) :=
    (hζ.1.comp (contDiff_const_smul _)).mul (sa12v3_mollify_smooth hη hε' hli)
  have hsm := sa12v3_perL_smooth hL0 hg (sa12v3_g_supp hζ hL0 _)
  have hper := sa12k_perL_periodic L (fun x => ζ (L⁻¹ • x) * mollify η (min ε 1) φ x)
  exact ⟨sa12v3_bddJets_of_periodic hL0 hsm hper m, hper⟩

theorem sa12v3_pd_eq_mollify {η ζ : Euc d → ℝ} (hζ : HRS.Whole.AppendixALemmas.IsCutoffRad (1 / 4) (1 / 3) ζ)
    {L ε R : ℝ} (hL : 1 ≤ L) (hLR : 4 * R ≤ L) (φ : Euc d → ℝ) {x : Euc d} (hx : ‖x‖ ≤ R) :
    periodicDatum ζ η L ε φ x = mollify η (min ε 1) φ x := by
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have hR0 : 0 ≤ R := (norm_nonneg x).trans hx
  unfold periodicDatum perL
  rw [tsum_eq_single 0]
  · have h0 : (latticePt (0 : Fin d → ℤ) : Euc d) = 0 := by ext i; simp [latticePt]
    rw [h0, smul_zero, sub_zero]
    have : ζ (L⁻¹ • x) = 1 := by
      apply hζ.2.2.2.2
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hL0,
        inv_mul_le_iff₀ hL0]
      linarith
    show ζ (L⁻¹ • x) * mollify η (min ε 1) φ x = _
    rw [this, one_mul]
  · intro z hz
    apply sa12v3_g_supp hζ hL0
    have h1 := sa12v3_latticePt_norm_ge hz
    have h2 : L ≤ ‖L • (latticePt z : Euc d)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL0]; nlinarith
    have h3 := norm_sub_norm_le (L • (latticePt z : Euc d)) x
    rw [norm_sub_rev] at h3
    linarith

theorem sa12v3_periodic_initial_bounds (hd : 1 ≤ d) (m : ℕ) (χ ζ η : Euc d → ℝ) (hχ : IsUlocCutoff χ)
    (hζ : HRS.Whole.AppendixALemmas.IsCutoffRad (1 / 4) (1 / 3) ζ) (hη : IsMollifier η) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ : Euc d → ℝ, ulocNormE m χ φ < ⊤ →
      (∀ L ε : ℝ, 1 ≤ L → 0 < ε →
        BddJets m (periodicDatum ζ η L ε φ) ∧
        (∀ (x : Euc d) (k : Fin d → ℤ),
          periodicDatum ζ η L ε φ (x + L • latticePt k) = periodicDatum ζ η L ε φ x) ∧
        ulocNormE m χ (periodicDatum ζ η L ε φ) ≤ ENNReal.ofReal C * ulocNormE m χ φ ∧
        varpiNormE m χ (periodicDatum ζ η L ε φ) ≤ ENNReal.ofReal C * varpiNormE m χ φ) ∧
      ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ δ : ℝ, 0 < δ →
        ∃ L₁ ε₀ : ℝ, 0 < ε₀ ∧ ∀ L : ℝ, max 1 L₁ ≤ L →
          ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
            |(∫ x, periodicDatum ζ η L ε φ x * ψ x) - (∫ x, φ x * ψ x)| ≤ δ := by
  obtain ⟨Cu, hCu, huloc⟩ := sa12v3_pd_uloc hη hχ hζ m
  obtain ⟨Cv, hCv, hvarpi⟩ := sa12v3_pd_varpi hd hη hχ hζ m
  refine ⟨max Cu Cv, lt_max_of_lt_left hCu, fun φ hφ => ⟨fun L ε hL hε => ?_, ?_⟩⟩
  · obtain ⟨hb, hp⟩ := sa12v3_pd_regular hη hχ hζ m hφ hL hε
    refine ⟨hb, hp, (huloc φ L ε hL hε).trans ?_, (hvarpi φ hφ L ε hL hε).trans ?_⟩
    · exact mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) le_rfl
    · exact mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right _ _)) le_rfl
  · intro ψ hψ δ hδ
    obtain ⟨R, A, hR, hA0, hjet, hvan⟩ := HRS.MH.AdjointRd.Phase2SA12Limit.sa12k_psi_data hψ
    have hψs : ∀ y : Euc d, R < ‖y‖ → ψ y = 0 := by
      intro y hy
      have := hvan 0 y hy
      have h2 := norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := ψ) (x := y)
      rw [this, norm_zero] at h2
      exact norm_eq_zero.1 h2.symm
    have hli := sa12v3_locInt_of_uloc hχ hφ
    obtain ⟨ε₀, hε₀, hmw⟩ := sa12v3_mollify_weak hη hli hψ.1.continuous R hψs δ hδ
    refine ⟨4 * R, ε₀, hε₀, fun L hL ε hε hεle => ?_⟩
    have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
    have hLR : 4 * R ≤ L := (le_max_right _ _).trans hL
    have heq : (∫ x, periodicDatum ζ η L ε φ x * ψ x) = ∫ x, mollify η (min ε 1) φ x * ψ x := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      by_cases hx : ‖x‖ ≤ R
      · simp only [sa12v3_pd_eq_mollify hζ hL1 hLR φ hx]
      · simp [hψs x (not_le.1 hx)]
    rw [heq]
    exact hmw (min ε 1) (lt_min hε one_pos) ((min_le_left _ _).trans hεle) (min_le_right _ _)

end HRS.MH.AdjointRd.Phase2SA12V3
