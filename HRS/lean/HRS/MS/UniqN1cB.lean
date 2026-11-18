import HRS.MS.UniqN1cA

/-!
# N1c of `UniqPlan.md`, part (b): the Hessian term `∫ f (a · ∂_jH_i)` for `s ≤ d - 2`

Near region `B(c₀, 2R)`: Cauchy–Schwarz with `‖1_{B(c₀,2R)} f‖₂ ≤ N A` (`n2b_ball_eLpNorm`) and the local
Hessian bound `n1c_hess_local` (`‖1_B ∂_jH_i‖₂ ≤ C ‖ψ‖₂`, radius fixed); far region: `n0_far_pairing_dH`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN1c

open HRS HRS.Whole HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqM1 HRS.MS.UniqNDefs
  HRS.MS.UniqN2b HRS.MS.UniqN0

variable {d : ℕ}

/-- **The Hessian-term estimate for `s ≤ d - 2`.**  `ψ ∈ C²_c` is supported in `B̄(c₀, R₂)`, `|ψ| ≤ |f|`. -/
theorem n1c_case_hess (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hs2 : s ≤ (d : ℝ) - 2)
    (R2 Λ : ℝ) (hR2 : 0 ≤ R2) (hΛ : 0 ≤ Λ) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ (c0 : Euc d) (A : ℝ) (f a ψ : Euc d → ℝ) (i j : Fin d), 0 ≤ A →
      LocMass A f → (∀ x, jbracket x ^ ((d : ℝ) + 3) * |a x| ≤ Λ) →
      ContDiff ℝ 2 ψ → HasCompactSupport ψ → Function.support ψ ⊆ closedBall c0 R2 →
      (∀ y, |ψ y| ≤ |f y|) →
      |∫ y, f y * (a y * D1 j (kernelConvDeriv d s i ψ) y)| ≤ C0 * A ^ 2 := by
  set R : ℝ := R2 + 1 with hR
  have hR1 : 1 ≤ R := by linarith
  obtain ⟨Cfar, hCfar0, hfar⟩ := n0_far_pairing_dH d hs0 hsd
  obtain ⟨Cl, Cl', hloc⟩ := n1c_hess_local hd hs0 hs2
  obtain ⟨K1, hK10, hK1⟩ := exists_closedBall_l1_real d R2
  obtain ⟨N1, hN1⟩ := n2b_ball_eLpNorm d R
  obtain ⟨N2, hN2⟩ := n2b_ball_eLpNorm d (2 * R)
  set Kloc : ℝ := |Cl' * (2 * R) ^ Cl| with hKloc
  have hKloc0 : 0 ≤ Kloc := abs_nonneg _
  refine ⟨Cfar * Λ * K1 + Λ * Real.sqrt N2 * (Kloc * Real.sqrt N1), by positivity, ?_⟩
  intro c0 A f a ψ i j hA hf ha hψ hψc hsupp hψf
  have haΛ : ∀ y, |a y| ≤ Λ := n2b_abs_le_of_jb ha
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have hψm : AEStronglyMeasurable ψ volume := hψ.continuous.aestronglyMeasurable
  have hHc : Continuous (D1 j (kernelConvDeriv d s i ψ)) := n1c_D1_kcd_cont hs0 hsd hψ hψc i j
  have hAabs : |A| = A := abs_of_nonneg hA
  have henorm : ∀ x y : ℝ, |x| ≤ |y| → ‖x‖ₑ ≤ ‖y‖ₑ := fun x y h => by
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (by simpa [Real.norm_eq_abs] using h)
  -- `L²` norm of `ψ`
  have hψL2 : eLpNorm ψ 2 volume ≤ ENNReal.ofReal (Real.sqrt N1 * A) := by
    have h1 : eLpNorm ψ 2 volume ≤ eLpNorm ((ball c0 R).indicator f) 2 volume := by
      refine eLpNorm_mono_enorm hψm (fun y => ?_)
      by_cases hy : ψ y = 0
      · simp [hy]
      · have hyb : y ∈ ball c0 R := by
          have := hsupp (Function.mem_support.2 hy)
          rw [mem_closedBall] at this; rw [mem_ball]; linarith
        rw [Set.indicator_of_mem hyb]
        exact henorm _ _ (hψf y)
    have := hN1 A f hf c0
    rw [hAabs] at this
    exact h1.trans this
  -- `L¹` norm of `ψ`
  have hψL1 : ∫ x, |ψ x| ≤ K1 * A := by
    have hI0 : Integrable (fun x => |ψ x|) volume :=
      (hψ.continuous.integrable_of_hasCompactSupport hψc).abs
    have hsub : closedBall c0 R2 ⊆ ball c0 R := fun y hy => by
      rw [mem_closedBall] at hy; rw [mem_ball]; linarith
    have hI1 : IntegrableOn (fun y => ‖f y‖) (closedBall c0 R2) volume :=
      ((hf.integrableOn_ball c0 R).mono_set hsub).norm
    have hz : ∀ y ∉ closedBall c0 R2, |ψ y| = 0 := fun y hy => by
      have : ψ y = 0 := by
        by_contra h0; exact hy (hsupp (Function.mem_support.2 h0))
      simp [this]
    calc ∫ x, |ψ x| = ∫ x in closedBall c0 R2, |ψ x| :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero hz).symm
      _ ≤ ∫ x in closedBall c0 R2, ‖f x‖ :=
          setIntegral_mono_on hI0.integrableOn hI1 measurableSet_closedBall
            (fun y _ => by simpa [Real.norm_eq_abs] using hψf y)
      _ ≤ K1 * A := hK1 A f hA hf c0
  -- the far region
  set F : Set (Euc d) := {y : Euc d | 2 * R ≤ ‖y - c0‖} with hF
  have hFm : MeasurableSet F :=
    (isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))).measurableSet
  have hsupp' : Function.support ψ ⊆ closedBall c0 R :=
    hsupp.trans (closedBall_subset_closedBall (by linarith))
  have hfarB := hfar Λ A c0 R f a ψ i j hΛ hR1 hf ha hψ hψc hsupp'
  have hfarB' : ∫⁻ y in F, ‖f y * (a y * D1 j (kernelConvDeriv d s i ψ) y)‖ₑ ≤
      ENNReal.ofReal (Cfar * Λ * (K1 * A) * A) := by
    refine hfarB.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hAabs]
    have : 0 ≤ Cfar * Λ := by positivity
    gcongr
  -- the near region
  have hsupp2 : Function.support ψ ⊆ closedBall c0 (2 * R) :=
    hsupp.trans (closedBall_subset_closedBall (by linarith))
  have hnormv : eLpNorm ((closedBall c0 (2 * R)).indicator (D1 j (kernelConvDeriv d s i ψ))) 2 volume ≤
      ENNReal.ofReal Kloc * ENNReal.ofReal (Real.sqrt N1 * A) := by
    have h1 := hloc i j (2 * R) (by linarith) c0 ψ hψ hψc hsupp2 c0 (2 * R) le_rfl
    refine h1.trans ?_
    gcongr
    · exact (le_abs_self _)
  have hnormu : eLpNorm ((ball c0 (2 * R)).indicator f) 2 volume ≤ ENNReal.ofReal (Real.sqrt N2 * A) := by
    have := hN2 A f hf c0
    rwa [hAabs] at this
  have hnear : ∫⁻ y in Fᶜ, ‖f y * (a y * D1 j (kernelConvDeriv d s i ψ) y)‖ₑ ≤
      ENNReal.ofReal Λ * (ENNReal.ofReal (Real.sqrt N2 * A) *
        (ENNReal.ofReal Kloc * ENNReal.ofReal (Real.sqrt N1 * A))) := by
    set u : Euc d → ℝ := (ball c0 (2 * R)).indicator f with hu
    set v : Euc d → ℝ := (closedBall c0 (2 * R)).indicator (D1 j (kernelConvDeriv d s i ψ)) with hv
    have hum : AEStronglyMeasurable u volume := hf.1.indicator measurableSet_ball
    have hvm : AEStronglyMeasurable v volume :=
      (hHc.aestronglyMeasurable).indicator measurableSet_closedBall
    have hpt : ∀ y ∈ Fᶜ, ‖f y * (a y * D1 j (kernelConvDeriv d s i ψ) y)‖ₑ ≤
        ENNReal.ofReal Λ * (‖u y‖ₑ * ‖v y‖ₑ) := by
      intro y hy
      have hyb : y ∈ ball c0 (2 * R) := by
        simp only [hF, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hy
        rw [mem_ball, dist_eq_norm]; exact hy
      have hyb' : y ∈ closedBall c0 (2 * R) := ball_subset_closedBall hyb
      rw [hu, hv, Set.indicator_of_mem hyb, Set.indicator_of_mem hyb', enorm_mul, enorm_mul]
      have : ‖a y‖ₑ ≤ ENNReal.ofReal Λ := by
        rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (haΛ y)
      calc ‖f y‖ₑ * (‖a y‖ₑ * ‖D1 j (kernelConvDeriv d s i ψ) y‖ₑ)
          ≤ ‖f y‖ₑ * (ENNReal.ofReal Λ * ‖D1 j (kernelConvDeriv d s i ψ) y‖ₑ) := by gcongr
        _ = _ := by ring
    calc ∫⁻ y in Fᶜ, ‖f y * (a y * D1 j (kernelConvDeriv d s i ψ) y)‖ₑ
        ≤ ∫⁻ y in Fᶜ, ENNReal.ofReal Λ * (‖u y‖ₑ * ‖v y‖ₑ) :=
          setLIntegral_mono' hFm.compl hpt
      _ ≤ ∫⁻ y, ENNReal.ofReal Λ * (‖u y‖ₑ * ‖v y‖ₑ) := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal Λ * ∫⁻ y, ‖u y‖ₑ * ‖v y‖ₑ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal Λ * (eLpNorm u 2 volume * eLpNorm v 2 volume) := by
          gcongr; exact n2b_holder hum hvm
      _ ≤ _ := by gcongr
  -- assemble
  have htot : ∫⁻ y, ‖f y * (a y * D1 j (kernelConvDeriv d s i ψ) y)‖ₑ ≤
      ENNReal.ofReal ((Cfar * Λ * K1 + Λ * Real.sqrt N2 * (Kloc * Real.sqrt N1)) * A ^ 2) := by
    rw [← lintegral_add_compl _ hFm]
    refine (add_le_add hfarB' hnear).trans (le_of_eq ?_)
    have hs2' : 0 ≤ Real.sqrt N2 := Real.sqrt_nonneg _
    have hs1' : 0 ≤ Real.sqrt N1 := Real.sqrt_nonneg _
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; ring
  have hnn : 0 ≤ (Cfar * Λ * K1 + Λ * Real.sqrt N2 * (Kloc * Real.sqrt N1)) * A ^ 2 := by positivity
  calc |∫ y, f y * (a y * D1 j (kernelConvDeriv d s i ψ) y)|
      = ‖∫ y, f y * (a y * D1 j (kernelConvDeriv d s i ψ) y)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ENNReal.toReal (∫⁻ y, ENNReal.ofReal ‖f y * (a y * D1 j (kernelConvDeriv d s i ψ) y)‖) :=
        norm_integral_le_lintegral_norm _
    _ ≤ _ := by
        simp only [ofReal_norm_eq_enorm]
        exact ENNReal.toReal_le_of_le_ofReal hnn htot

end HRS.MS.UniqN1c
