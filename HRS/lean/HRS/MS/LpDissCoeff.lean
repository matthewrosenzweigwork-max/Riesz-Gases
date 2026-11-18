import HRS.MS.LpDissDefs
import HRS.MS.CzElemAux3

/-!
# S.A.16.C2: uniform cutoff fractional coefficient bound

`sa16bd_lapCut_cb2`: for `μ ∈ C_b²` and every positive cutoff `ε`, the truncated fractional
difference of `μ` is bounded by `C * cbNorm 2 μ`, with `C` independent of `ε`, `x`, `μ`.
-/

set_option autoImplicit false

noncomputable section
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.CZ.Pv HRS.CZ.ElemA

universe u

namespace HRS.Whole.AppendixA.BreakdownSA16

/-- the near-zero constant -/
def sa16bd_J1 (d : ℕ) (θ : ℝ) : ℝ :=
  (∫ z in closedBall (0 : Euc d) 1, ‖z‖ ^ (-((d : ℝ) + θ - 2))) / 2

/-- the far constant -/
def sa16bd_J2 (d : ℕ) (θ : ℝ) : ℝ :=
  2 * ∫ z in {z : Euc d | 1 < ‖z‖}, ‖z‖ ^ (-((d : ℝ) + θ))

lemma sa16bd_J1_nonneg (d : ℕ) (θ : ℝ) : 0 ≤ sa16bd_J1 d θ := by
  unfold sa16bd_J1
  refine div_nonneg (setIntegral_nonneg measurableSet_closedBall fun z _ => ?_) zero_le_two
  exact Real.rpow_nonneg (norm_nonneg _) _

lemma sa16bd_J2_nonneg (d : ℕ) (θ : ℝ) : 0 ≤ sa16bd_J2 d θ := by
  unfold sa16bd_J2
  refine mul_nonneg zero_le_two (setIntegral_nonneg ?_ fun z _ => ?_)
  · exact measurableSet_lt measurable_const measurable_norm
  · exact Real.rpow_nonneg (norm_nonneg _) _

/-- absolute integral of the symmetrised kernel integrand -/
lemma sa16bd_symm_abs_bound {d : ℕ} (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2)
    {f : Euc d → ℝ} {Bf L M : ℝ} (hf : PvC2 f Bf L M) (x : Euc d) :
    ∫ z, |(2 * f x - f (x - z) - f (x + z)) / 2 / ‖z‖ ^ ((d : ℝ) + θ)|
      ≤ M * sa16bd_J1 d θ + Bf * sa16bd_J2 d θ := by
  set g : Euc d → ℝ := fun z => (2 * f x - f (x - z) - f (x + z)) / 2 / ‖z‖ ^ ((d : ℝ) + θ)
    with hg
  have hgi : Integrable g := pvapi_hsym_integrable hd hθ0 hθ2 hf x
  have hgabs : Integrable (fun z => |g z|) := hgi.abs
  have hTm : MeasurableSet {z : Euc d | 1 < ‖z‖} :=
    measurableSet_lt measurable_const measurable_norm
  have hU : closedBall (0 : Euc d) 1 ∪ {z : Euc d | 1 < ‖z‖} = univ := by
    ext z
    simp only [mem_univ, mem_union, mem_closedBall, dist_zero_right, Set.mem_ofPred_eq, iff_true]
    by_cases h : ‖z‖ ≤ 1
    · exact Or.inl h
    · exact Or.inr (not_le.1 h)
  have hdisj : Disjoint (closedBall (0 : Euc d) 1) {z : Euc d | 1 < ‖z‖} := by
    rw [Set.disjoint_left]
    intro z h1 h2
    have : ‖z‖ ≤ 1 := by simpa using h1
    have h3 : 1 < ‖z‖ := h2
    linarith
  have hsplit := setIntegral_union hdisj hTm hgabs.integrableOn hgabs.integrableOn
  rw [hU, setIntegral_univ] at hsplit
  rw [hsplit]
  -- near part
  have hnear : ∫ z in closedBall (0 : Euc d) 1, |g z| ≤ M * sa16bd_J1 d θ := by
    have hint : IntegrableOn (fun z : Euc d => (M / 2) * ‖z‖ ^ (-((d : ℝ) + θ - 2)))
        (closedBall 0 1) := by
      have : IntegrableOn (fun z : Euc d => (M / 2) * ‖z‖ ^ (-((d : ℝ) + θ - 2))) (ball 0 2) :=
        (pvapi_integrableOn_ball_rpow hd (α := (d : ℝ) + θ - 2) (by linarith) 2).const_mul (M / 2)
      exact this.mono_set (closedBall_subset_ball (by norm_num))
    calc ∫ z in closedBall (0 : Euc d) 1, |g z|
        ≤ ∫ z in closedBall (0 : Euc d) 1, (M / 2) * ‖z‖ ^ (-((d : ℝ) + θ - 2)) := by
          refine setIntegral_mono_on hgabs.integrableOn hint measurableSet_closedBall fun z _ => ?_
          by_cases hz : z = 0
          · subst hz
            simp only [hg, sub_zero, add_zero, norm_zero]
            have : 2 * f x - f x - f x = 0 := by ring
            rw [this, zero_div, zero_div, abs_zero]
            exact mul_nonneg (div_nonneg hf.M_nonneg zero_le_two) (Real.rpow_nonneg le_rfl _)
          · have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
            have hs := hf.second x z
            have hneg : 2 * f x - f (x - z) - f (x + z) =
                -(f (x + z) + f (x - z) - 2 * f x) := by ring
            simp only [hg]
            rw [abs_div, abs_div, abs_of_pos (Real.rpow_pos_of_pos hn _), hneg, abs_neg, abs_two]
            have h3 : ‖z‖ ^ (-((d : ℝ) + θ - 2)) = ‖z‖ ^ 2 / ‖z‖ ^ ((d : ℝ) + θ) := by
              rw [show -((d : ℝ) + θ - 2) = (2 : ℝ) - ((d : ℝ) + θ) by ring, Real.rpow_sub hn,
                Real.rpow_two]
            rw [h3]
            have hpos : 0 < ‖z‖ ^ ((d : ℝ) + θ) := Real.rpow_pos_of_pos hn _
            calc |f (x + z) + f (x - z) - 2 * f x| / 2 / ‖z‖ ^ ((d : ℝ) + θ)
                ≤ (M * ‖z‖ ^ 2) / 2 / ‖z‖ ^ ((d : ℝ) + θ) := by gcongr
              _ = M / 2 * (‖z‖ ^ 2 / ‖z‖ ^ ((d : ℝ) + θ)) := by ring
      _ = M * sa16bd_J1 d θ := by
          rw [integral_const_mul]
          unfold sa16bd_J1
          ring
  have hfar : ∫ z in {z : Euc d | 1 < ‖z‖}, |g z| ≤ Bf * sa16bd_J2 d θ := by
    have hint : IntegrableOn (fun z : Euc d => (2 * Bf) * ‖z‖ ^ (-((d : ℝ) + θ)))
        {z : Euc d | 1 < ‖z‖} :=
      (pvapi_integrableOn_tail_rpow hd (s := (d : ℝ) + θ) (by linarith)).const_mul (2 * Bf)
    calc ∫ z in {z : Euc d | 1 < ‖z‖}, |g z|
        ≤ ∫ z in {z : Euc d | 1 < ‖z‖}, (2 * Bf) * ‖z‖ ^ (-((d : ℝ) + θ)) := by
          refine setIntegral_mono_on hgabs.integrableOn hint hTm fun z hz => ?_
          have hz1 : 1 < ‖z‖ := hz
          have hn : 0 < ‖z‖ := lt_trans one_pos hz1
          have a1 := hf.bdd x
          have a2 := hf.bdd (x - z)
          have a3 := hf.bdd (x + z)
          simp only [hg]
          rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hn _), Real.rpow_neg hn.le,
            ← div_eq_mul_inv, abs_div, abs_two]
          have : |2 * f x - f (x - z) - f (x + z)| ≤ 4 * Bf := by
            rw [abs_le]
            constructor <;> linarith [abs_le.1 a1, abs_le.1 a2, abs_le.1 a3]
          have hpos : 0 < ‖z‖ ^ ((d : ℝ) + θ) := Real.rpow_pos_of_pos hn _
          rw [div_div, div_le_div_iff₀ (by positivity) hpos]
          nlinarith [this, hpos]
      _ = Bf * sa16bd_J2 d θ := by
          rw [integral_const_mul]
          unfold sa16bd_J2
          ring
  linarith

theorem sa16bd_lapCut_cb2 {d : ℕ} (hd : 1 ≤ d) (θ : ℝ)
    (hθ0 : 0 < θ) (hθ2 : θ < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ μ : Euc d → ℝ, MemCb 2 μ →
      ∀ ε : ℝ, 0 < ε → ∀ x : Euc d,
        IntegrableOn (fun z : Euc d =>
          (μ x - μ (x - z)) / ‖z‖ ^ ((d : ℝ) + θ))
          {z : Euc d | ε < ‖z‖} ∧
        |sa16bd_lapCut d θ ε μ x| ≤ C * cbNorm 2 μ := by
  refine ⟨sa16bd_J1 d θ + sa16bd_J2 d θ,
    add_nonneg (sa16bd_J1_nonneg d θ) (sa16bd_J2_nonneg d θ), fun μ hμ ε hε x => ?_⟩
  obtain ⟨B0, B1, B2, hB0, hB1, hB2, hcb, -, h0, h1, h2⟩ := elema_cb2_data hμ
  have hc : ContDiff ℝ 2 μ := by simpa using hμ.1
  have hpv : PvC2 μ B0 B1 B2 :=
    PvC2.of_contDiff hc (fun y => by simpa [Real.norm_eq_abs] using h0 y)
      (fun y => by simpa using h1 y) h2
  refine ⟨pvapi_integrableOn_h1 hd hθ0 hpv x hε, ?_⟩
  have hS : MeasurableSet {z : Euc d | ε < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  have heq : sa16bd_lapCut d θ ε μ x =
      ∫ z in {z : Euc d | ε < ‖z‖},
        (2 * μ x - μ (x - z) - μ (x + z)) / 2 / ‖z‖ ^ ((d : ℝ) + θ) :=
    (pvapi_sym_trunc_eq hd hθ0 hpv x hε).symm
  have hgi := pvapi_hsym_integrable hd hθ0 hθ2 hpv x
  rw [heq]
  calc |∫ z in {z : Euc d | ε < ‖z‖},
          (2 * μ x - μ (x - z) - μ (x + z)) / 2 / ‖z‖ ^ ((d : ℝ) + θ)|
      ≤ ∫ z in {z : Euc d | ε < ‖z‖},
          |(2 * μ x - μ (x - z) - μ (x + z)) / 2 / ‖z‖ ^ ((d : ℝ) + θ)| := by
        have := norm_integral_le_integral_norm
          (μ := volume.restrict {z : Euc d | ε < ‖z‖})
          (fun z => (2 * μ x - μ (x - z) - μ (x + z)) / 2 / ‖z‖ ^ ((d : ℝ) + θ))
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∫ z, |(2 * μ x - μ (x - z) - μ (x + z)) / 2 / ‖z‖ ^ ((d : ℝ) + θ)| :=
        setIntegral_le_integral hgi.abs (Eventually.of_forall fun z => abs_nonneg _)
    _ ≤ B2 * sa16bd_J1 d θ + B0 * sa16bd_J2 d θ := sa16bd_symm_abs_bound hd hθ0 hθ2 hpv x
    _ ≤ (sa16bd_J1 d θ + sa16bd_J2 d θ) * cbNorm 2 μ := by
        rw [hcb]
        have := sa16bd_J1_nonneg d θ
        have := sa16bd_J2_nonneg d θ
        nlinarith [mul_nonneg hB1 (sa16bd_J1_nonneg d θ), mul_nonneg hB1 (sa16bd_J2_nonneg d θ),
          mul_nonneg hB0 (sa16bd_J1_nonneg d θ), mul_nonneg hB2 (sa16bd_J2_nonneg d θ)]

end HRS.Whole.AppendixA.BreakdownSA16
