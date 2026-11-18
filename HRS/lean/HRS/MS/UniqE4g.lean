import HRS.MS.UniqE4f

/-!
# E4 of `UniqPlan.md`, part 7: `L¹` and `L²`-gradient bounds for `ψ' = ς z_ε`

For a cutoff `ς` (values in `[0,1]`, `‖∇ς‖ ≤ K`, `tsupport ς ⊆ B̄(c₀,R)`) and `z = η_ε * u`,
`ulocNormE 1 χ u ≤ B`:  `∫ |ς z| ≤ K_p B`  and  `∫⁻ ‖∂_i(ς z)‖² ≤ Q_c B²`, `K_p, Q_c` depending on `(d, K, R)` only.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.UniqE4

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqM1 HRS.MS.UniqM2
  HRS.MS.UniqM3 HRS.MS.UniqT3 HRS.MS.UniqC3 HRS.MS.UniqE3 HRS.MS.UniqN0

variable {d : ℕ}

theorem e4_locMass_moll (d : ℕ) :
    ∃ N : ℕ, ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ (B : ℝ), 0 ≤ B → ∀ (F : Euc d → ℝ), LocMass B F →
      LocMass (Real.sqrt N * B) (moll d ε F) := by
  obtain ⟨N, hN⟩ := moll_mass_le_const d 1
  refine ⟨N, fun ε hε hε1 B hB F hF => ?_⟩
  refine ⟨(e3_moll_continuous hε hF.locallyIntegrable).aestronglyMeasurable, fun c => ?_⟩
  refine (hN ε hε hε1 B _ hF c).trans (le_of_eq ?_)
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N), ENNReal.ofReal_mul (Nat.cast_nonneg N),
    ENNReal.ofReal_natCast]

/-- `∫⁻ ‖f‖² = ofReal ∫ f²` for `f` continuous, vanishing off a compact set. -/
theorem e4_lintegral_sq {f : Euc d → ℝ} (hf : Continuous f) {S : Set (Euc d)} (hS : IsCompact S)
    (hfS : ∀ x, x ∉ S → f x = 0) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 = ENNReal.ofReal (∫ x, f x ^ 2) := by
  have hi : Integrable (fun x => f x ^ 2) volume :=
    (hf.pow 2).integrable_of_hasCompactSupport (e3_hasCompactSupport_of_zero hS fun x hx => by
      simp [hfS x hx])
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => sq_nonneg _)]
  refine lintegral_congr fun x => ?_
  rw [enorm_sq_eq]

theorem e4_PQ (d : ℕ) (K R : ℝ) :
    ∃ Kp Qc : ℝ, 0 ≤ Kp ∧ 0 ≤ Qc ∧ ∀ {χ : Euc d → ℝ}, IsUlocCutoff χ → ∀ (u : Euc d → ℝ) (B : ℝ),
      0 ≤ B → ulocNormE 1 χ u ≤ ENNReal.ofReal B → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ (ς : Euc d → ℝ) (c0 : Euc d), ContDiff ℝ 1 ς → (∀ x, ‖fderiv ℝ ς x‖ ≤ K) →
      (∀ x, 0 ≤ ς x) → (∀ x, ς x ≤ 1) → tsupport ς ⊆ closedBall c0 R → HasCompactSupport ς →
      (∫ x, |ς x * moll d ε u x|) ≤ Kp * B ∧
      ∀ i : Fin d, ∫⁻ x, ‖D1 i (fun y => ς y * moll d ε u y) x‖ₑ ^ 2 ≤ ENNReal.ofReal (Qc * B ^ 2) := by
  obtain ⟨N0, hN0⟩ := e4_locMass_moll d
  obtain ⟨Kl, hKl0, hKl⟩ := exists_ball_l1_bound d (R + 1)
  obtain ⟨N1, hN1⟩ := e3_moll_sq_set_le d (R + 1)
  obtain ⟨N2, hN2⟩ := e3_grad_sq_set_le d (R + 1)
  refine ⟨Kl * Real.sqrt N0, 2 * K ^ 2 * N1 + 2 * N2, by positivity, by positivity, ?_⟩
  intro χ hχ u B hB hu ε hε hε1 ς c0 hς hK hς0 hς1 hsupp hςc
  have hLM : LocMass B u := locMass_of_ulocNormE hχ hB hu
  have hz : ContDiff ℝ ∞ (moll d ε u) := moll_contDiff hε hLM.locallyIntegrable
  have hz1 : ContDiff ℝ 1 (moll d ε u) := hz.of_le (by exact_mod_cast le_top)
  set z : Euc d → ℝ := moll d ε u with hzdef
  set S : Set (Euc d) := closedBall c0 R with hS
  have hSc : IsCompact S := isCompact_closedBall _ _
  have hSball : S ⊆ ball c0 (R + 1) := closedBall_subset_ball (by linarith)
  have hψ1 : ContDiff ℝ 1 (fun y => ς y * z y) := hς.mul hz1
  have hzero : ∀ x, x ∉ S → ς x = 0 ∧ ∀ i, D1 i ς x = 0 := fun x hx =>
    ⟨image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp h)), fun i => (e3_zero_off (fun h => hx (hsupp h)) i).2⟩
  refine ⟨?_, fun i => ?_⟩
  · -- the `L¹` bound
    have hLz : LocMass (Real.sqrt N0 * B) z := hN0 ε hε hε1 B hB u hLM
    have hl1 := hKl (Real.sqrt N0 * B) z (by positivity) hLz c0
    have hcont : Continuous (fun x => ς x * z x) := hς.continuous.mul hz1.continuous
    have hint0 : ∀ x, x ∉ S → ς x * z x = 0 := fun x hx => by simp [(hzero x hx).1]
    have hmeas : AEStronglyMeasurable (fun x => ς x * z x) volume := hcont.aestronglyMeasurable
    have e1 : ∫ x, |ς x * z x| = (∫⁻ x, ‖ς x * z x‖ₑ).toReal := by
      rw [← integral_norm_eq_lintegral_enorm hmeas]
      simp [Real.norm_eq_abs]
    rw [e1]
    have h2 : ∫⁻ x, ‖ς x * z x‖ₑ ≤ ENNReal.ofReal (Kl * (Real.sqrt N0 * B)) := by
      calc ∫⁻ x, ‖ς x * z x‖ₑ = ∫⁻ x in S, ‖ς x * z x‖ₑ := by
            rw [← lintegral_indicator hSc.measurableSet]
            refine lintegral_congr fun x => ?_
            by_cases hx : x ∈ S
            · simp [Set.indicator_of_mem hx]
            · simp [Set.indicator_of_notMem hx, hint0 x hx]
        _ ≤ ∫⁻ x in S, ‖z x‖ₑ := by
            refine lintegral_mono fun x => ?_
            rw [enorm_mul]
            have : ‖ς x‖ₑ ≤ 1 := by
              rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hς0 x)]
              exact ENNReal.ofReal_le_one.2 (hς1 x)
            calc ‖ς x‖ₑ * ‖z x‖ₑ ≤ 1 * ‖z x‖ₑ := by gcongr
              _ = _ := one_mul _
        _ ≤ ∫⁻ x in ball c0 (R + 1), ‖z x‖ₑ := lintegral_mono_set hSball
        _ ≤ _ := hl1
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
    rw [ENNReal.toReal_ofReal (by positivity)] at this
    calc _ ≤ Kl * (Real.sqrt N0 * B) := this
      _ = _ := by ring
  · -- the gradient bound
    have hDc : Continuous (D1 i fun y => ς y * z y) := e3_continuous_D1 hψ1 i
    have hD0 : ∀ x, x ∉ S → D1 i (fun y => ς y * z y) x = 0 := fun x hx => by
      rw [e3_D1_mul (hς.differentiable (by simp)) (hz1.differentiable (by simp))]
      simp [(hzero x hx).1, (hzero x hx).2 i]
    rw [e4_lintegral_sq hDc hSc hD0]
    refine ENNReal.ofReal_le_ofReal ?_
    have hpt : ∀ x, D1 i (fun y => ς y * z y) x ^ 2 ≤ 2 * K ^ 2 * z x ^ 2 + 2 * ‖fderiv ℝ z x‖ ^ 2 :=
      fun x => e3_D1_prod_bound hς hz1 hK hς0 hς1 i x
    have hzc : Continuous z := hz1.continuous
    have hgc : Continuous (fun x => ‖fderiv ℝ z x‖) := (hz1.continuous_fderiv (by simp)).norm
    have hrestr : ∫ x, D1 i (fun y => ς y * z y) x ^ 2 = ∫ x in S, D1 i (fun y => ς y * z y) x ^ 2 :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [hD0 x hx]).symm
    rw [hrestr]
    have i1 : IntegrableOn (fun x => z x ^ 2) S volume :=
      (hzc.pow 2).continuousOn.integrableOn_compact hSc
    have i2 : IntegrableOn (fun x => ‖fderiv ℝ z x‖ ^ 2) S volume :=
      (hgc.pow 2).continuousOn.integrableOn_compact hSc
    have i0 : IntegrableOn (fun x => D1 i (fun y => ς y * z y) x ^ 2) S volume :=
      (hDc.pow 2).continuousOn.integrableOn_compact hSc
    calc ∫ x in S, D1 i (fun y => ς y * z y) x ^ 2
        ≤ ∫ x in S, (2 * K ^ 2 * z x ^ 2 + 2 * ‖fderiv ℝ z x‖ ^ 2) :=
          setIntegral_mono_on i0
            (show IntegrableOn (fun x => 2 * K ^ 2 * z x ^ 2 + 2 * ‖fderiv ℝ z x‖ ^ 2) S volume from
              (i1.const_mul (2 * K ^ 2)).add (i2.const_mul 2)) hSc.measurableSet
            fun x _ => hpt x
      _ = 2 * K ^ 2 * (∫ x in S, z x ^ 2) + 2 * ∫ x in S, ‖fderiv ℝ z x‖ ^ 2 := by
          rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul,
            integral_const_mul]
      _ ≤ 2 * K ^ 2 * (N1 * B ^ 2) + 2 * (N2 * B ^ 2) := by
          have a1 := hN1 ε hε hε1 B u hLM c0 S hSball
          have a2 := hN2 hχ u B hB hu ε hε hε1 c0 S hSball
          gcongr
      _ = _ := by ring

end HRS.MS.UniqE4
