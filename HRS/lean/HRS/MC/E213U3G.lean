import HRS.MC.E213U3F
import HRS.MC.E213Defs
import HRS.Sections.AdjKGlue

/-!
# Packet E213U3, part G: the far-window bound `winJ_far`

`winJ_far_proof` has the statement of `HRS.MC.E213Plan.winJ_far` verbatim.  The existence of the tensor at the horizon
`a + T` is `u3_L1` (the weighted integrability gives `L¹` on the bounded range), converted to `IsJValue`; the bound
is `u3_decay` (near piece + unit blocks with the dual evolution of `adjk_evolution_along_trajectory`), identified with
`winJ` by uniqueness of `SJW`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U3

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

set_option maxSynthPendingDepth 3

variable {d : ℕ}

/-- `SJ` for the regime shifted by `0` is `SJ` for the regime. -/
theorem u3_SJ_shift_zero (R : Regime d) (r m G : ℝ) (h0 : (0 : ℝ) ≤ 0) {z : ℝ → NegSobolev d r}
    {I : Set ℝ} {J : TensorDual (PathSpace d m G) 2}
    (h : SJ (HRS.MC.E213F.shift R 0 h0) r m G z I J) : SJ R r m G z I J := by
  have hρ : (HRS.MC.E213F.shift R 0 h0).ρ = R.ρ := funext fun t => by simp
  have hF : ∀ ta tb φa φb u, Fser (HRS.MC.E213F.shift R 0 h0) r m z ta tb φa φb u =
      Fser R r m z ta tb φa φb u := by
    intro ta tb φa φb u
    unfold Fser Fterm
    rw [show (HRS.MC.E213F.shift R 0 h0).D = R.D from rfl, hρ]
  refine ⟨h.1, ?_⟩
  intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
  rw [h.2 ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂]
  simp only [hF]
  rfl

/-- `IsJValue` only sees the coefficient on `I ∩ [0, ∞)`. -/
theorem u3_IsJValue_congr (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m G : ℝ) {z z' : ℝ → NegSobolev d m}
    {I : Set ℝ} (hIm : MeasurableSet I) (hzz : ∀ u ∈ I, 0 ≤ u → z u = z' u)
    {J : TensorDual (PathSpace d m G) 2} (h : IsJValue D ρ m G z I J) : IsJValue D ρ m G z' I J := by
  refine ⟨h.1, ?_⟩
  intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
  rw [h.2 ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂]
  congr 1
  refine setIntegral_congr_fun (hIm.inter measurableSet_Icc) fun u hu => ?_
  simp only [hzz u hu.1 hu.2.1]

theorem winJ_far_proof {S : PreparedData d} {β₀ m : ℝ} (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (a : ℝ) (ha : 0 ≤ a) (b : ℝ), 0 ≤ b →
      ∀ (zr : ℝ → NegSobolev d (rLvl d)), Measurable (nearCoef 0 zr) →
      IntegrableOn (fun v => Real.exp (-c * (a - v)) * ‖zr v‖) (Set.Ioc 0 (min b (a + T))) →
      ∀ u u' : ℝ, 0 ≤ u → u ≤ u' → u' ≤ a + T →
        (∃ J, IsJValue (regime S β₀ hE).D (regime S β₀ hE).ρ m (a + T)
            (farCoef b (fun v => NegSobolev.embed m (zr v))) (Set.Ioc u u') J) ∧
        ‖winJ (regime S β₀ hE) m T a ha (farCoef b (fun v => NegSobolev.embed m (zr v))) (Set.Ioc u u')‖ ≤
          C * ∫ v in Set.Ioc u u' ∩ Set.Iio b, Real.exp (-c * (a - v)) * ‖zr v‖ := by
  classical
  have hm : 3 * (d : ℝ) + 8 < m := hE.m_gt
  have hr : rLvl d = 2 * (d : ℝ) + 6 := rfl
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hrm : rLvl d ≤ m := by rw [hr]; linarith
  set R : Regime d := regime S β₀ hE with hR
  -- the dual evolution
  obtain ⟨Cr, cr, hCr, hcr, Vev, hdual, hplain, hdec, -⟩ :=
    HRS.AdjK.adjk_evolution_along_trajectory S.hd (HRS.MC.E213A.isSmoothPositiveTrajectory_of_prepared S) m
  have hdual' : IsDualEvolution R.D R.ρ m Vev := hdual
  obtain ⟨C, c, hC0, hc, hdecay⟩ := u3_decay R (rLvl d) hr m hm T hT Vev hdual' hplain Cr cr hcr hdec
  refine ⟨C + 1, c, by linarith, hc, fun a ha b hb zr hzr hint u u' hu huu' hu' => ?_⟩
  have hG : 0 < a + T := by linarith
  -- the coefficient
  set z' : ℝ → NegSobolev d (rLvl d) := farCoef b (nearCoef 0 zr) with hz'
  have hz'm : Measurable z' := by
    rw [hz']; unfold farCoef
    exact Measurable.ite measurableSet_Iio hzr measurable_const
  -- pointwise description of `z'` on `v ≥ 0`
  have hz'v : ∀ v : ℝ, 0 ≤ v → z' v = if v < b then zr v else 0 := by
    intro v hv
    simp only [hz', farCoef, nearCoef, hv, if_true]
  -- integrability of `‖z'‖` on `(u,u']`
  have hS0 : IntegrableOn (fun v => ‖z' v‖) (Set.Ioc 0 (min b (a + T))) := by
    refine Integrable.mono' (hint.const_mul (Real.exp (c * a))) hz'm.norm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun v hv => ?_)
    rw [norm_norm]
    have hw : 0 ≤ Real.exp (-c * (a - v)) * ‖zr v‖ := by positivity
    rw [hz'v v hv.1.le]
    split_ifs with hvb
    · have h1 : 1 ≤ Real.exp (c * a) * Real.exp (-c * (a - v)) := by
        rw [← Real.exp_add, ← Real.exp_zero]
        exact Real.exp_le_exp.2 (by nlinarith [mul_nonneg hc.le hv.1.le])
      calc ‖zr v‖ = 1 * ‖zr v‖ := (one_mul _).symm
        _ ≤ (Real.exp (c * a) * Real.exp (-c * (a - v))) * ‖zr v‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = Real.exp (c * a) * (Real.exp (-c * (a - v)) * ‖zr v‖) := by ring
    · rw [norm_zero]; positivity
  have hint' : IntegrableOn (fun v => ‖z' v‖) (Set.Ioc u u') := by
    have hA : IntegrableOn (fun v => ‖z' v‖) (Set.Ioc 0 (min b (a + T)) ∩ Set.Ioc u u') :=
      hS0.mono_set Set.inter_subset_left
    have hB : IntegrableOn (fun v => ‖z' v‖) (Set.Ioc u u' \ Set.Ioc 0 (min b (a + T))) := by
      refine (integrableOn_zero (μ := volume)).congr_fun (fun v hv => ?_)
        (measurableSet_Ioc.diff measurableSet_Ioc)
      have hv0 : 0 < v := lt_of_le_of_lt hu hv.1.1
      have hnot : ¬ v ≤ min b (a + T) := fun h => hv.2 ⟨hv0, h⟩
      have hb' : b < v := by
        by_contra hcon
        exact hnot (le_min (not_lt.1 hcon) (hv.1.2.trans hu'))
      rw [hz'v v hv0.le, if_neg (not_lt.2 hb'.le), norm_zero]
    refine (hA.union hB).mono_set ?_
    intro v hv
    by_cases h : v ∈ Set.Ioc 0 (min b (a + T))
    · exact Or.inl ⟨h, hv⟩
    · exact Or.inr ⟨hv, h⟩
  -- the tensor at the horizon `a + T`
  obtain ⟨CL, hCL0, hL⟩ := u3_L1 R (rLvl d) hr m hm (a + T) hG
  obtain ⟨J0, hJ0, -⟩ := hL 0 le_rfl z' hz'm u u' hu hu' hint'
  have hJ0' : SJ R (rLvl d) m (a + T) z' (Set.Ioc u u') J0 := u3_SJ_shift_zero R _ _ _ le_rfl hJ0
  have hIJ := u3_SJ_isJValue R (rLvl d) hr m hm (a + T) hG measurableSet_Ioc hJ0'
  have hembed0 : (NegSobolev.embed m (0 : NegSobolev d (rLvl d)) : NegSobolev d m) = 0 := by
    have := NegSobolev.norm_embed_le (d := d) (m := rLvl d) m hrm (0 : NegSobolev d (rLvl d))
    rw [norm_zero] at this
    exact norm_le_zero_iff.1 this
  have hIJ' : IsJValue R.D R.ρ m (a + T) (farCoef b (fun v => NegSobolev.embed m (zr v))) (Set.Ioc u u') J0 := by
    refine u3_IsJValue_congr R.D R.ρ m (a + T) measurableSet_Ioc (fun v hv hv0 => ?_) hIJ
    rw [hz'v v hv0]
    unfold farCoef
    by_cases hvb : v < b
    · simp only [hvb, if_true]; rfl
    · simp only [hvb, if_false]
      rw [← hembed0]; rfl
  have hex : ∃ J, IsJValue R.D R.ρ m (a + T) (farCoef b (fun v => NegSobolev.embed m (zr v))) (Set.Ioc u u') J :=
    ⟨J0, hIJ'⟩
  refine ⟨hex, ?_⟩
  -- `jTensor` is `J0`
  have hjT : jTensor R.D R.ρ m (a + T) (farCoef b (fun v => NegSobolev.embed m (zr v))) (Set.Ioc u u') = J0 := by
    unfold jTensor
    rw [dif_pos hex]
    exact HRS.MC.Sec7.S7PIC.s7_PI_C_J_unique_proof R m (a + T) _ _ _ _ hex.choose_spec hIJ'
  have hwin : winJ R m T a ha (farCoef b (fun v => NegSobolev.embed m (zr v))) (Set.Ioc u u') =
      tensorPow' 2 (winRestr a ha) J0 := by
    unfold winJ; rw [hjT]
  rw [hwin]
  -- the weighted bound
  obtain ⟨X, hX, hXn⟩ := hdecay a ha z' hz'm u u' hu huu' hu' hint'
  have hXeq : tensorPow' 2 (winRestr a ha) J0 = X :=
    u3_SJW_unique R _ m T a (u3_SJ_toSJW R _ m T a ha hJ0') hX
  rw [hXeq]
  have hint_eq : ∫ v in Set.Ioc u u', Real.exp (-c * (a - v)) * ‖z' v‖ =
      ∫ v in Set.Ioc u u' ∩ Set.Iio b, Real.exp (-c * (a - v)) * ‖zr v‖ := by
    rw [← setIntegral_indicator measurableSet_Iio]
    refine setIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
    have hv0 : 0 ≤ v := hu.trans hv.1.le
    rw [hz'v v hv0]
    by_cases hvb : v < b
    · rw [Set.indicator_of_mem (show v ∈ Set.Iio b from hvb), if_pos hvb]
    · rw [Set.indicator_of_notMem (show v ∉ Set.Iio b from hvb), if_neg hvb, norm_zero, mul_zero]
  have hI0 : 0 ≤ ∫ v in Set.Ioc u u' ∩ Set.Iio b, Real.exp (-c * (a - v)) * ‖zr v‖ :=
    setIntegral_nonneg (measurableSet_Ioc.inter measurableSet_Iio) fun v _ =>
      mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  calc ‖X‖ ≤ C * ∫ v in Set.Ioc u u', Real.exp (-c * (a - v)) * ‖z' v‖ := hXn
    _ = C * ∫ v in Set.Ioc u u' ∩ Set.Iio b, Real.exp (-c * (a - v)) * ‖zr v‖ := by rw [hint_eq]
    _ ≤ (C + 1) * ∫ v in Set.Ioc u u' ∩ Set.Iio b, Real.exp (-c * (a - v)) * ‖zr v‖ :=
        mul_le_mul_of_nonneg_right (by linarith) hI0

end HRS.MC.E213U3

end
