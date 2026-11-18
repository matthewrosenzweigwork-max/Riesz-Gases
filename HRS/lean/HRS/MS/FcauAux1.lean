import HRS.MS.UniqG2
import HRS.MS.UniqN0d
import HRS.Whole.AppendixAAdjoint
import HRS.MH.DualityRdA1
import HRS.MH.DualityRdB3Aux

/-!
# F-CAU, part 1: classical adjoint solutions are bounded in `L^∞([0,t]; H^1_uloc)`

Infrastructure for the uniqueness of classical adjoint solutions (`HRS/MS/FcauTie.lean`).  This
file contains the norm part: a `C¹` function `u` with `|u|, ‖∇u‖ ≤ A` has `ulocNormE 1 χ u ≤ C_χ A`
(`fcau_ul_bound`), where `ulocNormE` is the (Fourier-defined) `H¹_uloc` norm; and the existence of
a uniformly local cutoff (`fcau_exists_cutoff`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.Fcau

open HRS HRS.Whole HRS.Whole.AppendixA HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

/-- A uniformly local cutoff exists. -/
theorem fcau_exists_cutoff : ∃ χ : Euc d → ℝ, IsUlocCutoff χ := by
  let b : ContDiffBump (0 : Euc d) := ⟨1, 3 / 2, one_pos, by norm_num⟩
  refine ⟨b, b.contDiff, b.hasCompactSupport, ?_, fun x => ⟨b.nonneg, b.le_one⟩, fun x hx => ?_⟩
  · rw [b.tsupport_eq]
    intro x hx
    rw [mem_closedBall_zero_iff] at hx
    rw [mem_ball_zero_iff]
    have : ‖x‖ ≤ 3 / 2 := hx
    show ‖x‖ < 2
    linarith
  · exact b.one_of_mem_closedBall hx

/-- `H¹` norm bound of a Lipschitz function supported in a ball. -/
theorem fcau_sobNormSq_le {ψ : Euc d → ℝ} {L A R : ℝ} {c : Euc d}
    (hL : ∀ x y, |ψ x - ψ y| ≤ L * ‖x - y‖) (hA : ∀ x, |ψ x| ≤ A)
    (hs : Function.support ψ ⊆ closedBall c R) (hcont : Continuous ψ) :
    HRS.PDE.ToolboxRd.MemSobolev 1 ψ ∧ HRS.PDE.ToolboxRd.sobolevNormSq 1 ψ ≤ A ^ 2 * (volume (closedBall c R)).toReal +
      d * (2 * L ^ 2 * (volume (closedBall c R)).toReal) := by
  set S : Set (Euc d) := closedBall c R with hS
  have hSm : MeasurableSet S := measurableSet_closedBall
  have hSfin : volume S < ⊤ := measure_closedBall_lt_top
  set V : ℝ := (volume S).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hψc : HasCompactSupport ψ :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c R) hs
  have hmem : MemLp ψ 2 volume := hcont.memLp_of_hasCompactSupport hψc
  have hind : Integrable (S.indicator (fun _ => (1 : ℝ))) volume :=
    (integrable_indicator_iff hSm).2 (integrableOn_const hSfin.ne)
  have hdiff : ∀ h : Euc d, ∫ x, (ψ x - ψ (x - h)) ^ 2 ≤ (2 * L ^ 2 * V) * ‖h‖ ^ 2 := by
    intro h
    have hind' : Integrable (fun x => S.indicator (fun _ => (1 : ℝ)) (x - h)) volume :=
      hind.comp_sub_right h
    have hrhs : Integrable (fun x => L ^ 2 * ‖h‖ ^ 2 *
        (S.indicator (fun _ => (1 : ℝ)) x + S.indicator (fun _ => (1 : ℝ)) (x - h))) volume :=
      (hind.add hind').const_mul _
    have hpt : ∀ x, (ψ x - ψ (x - h)) ^ 2 ≤ L ^ 2 * ‖h‖ ^ 2 *
        (S.indicator (fun _ => (1 : ℝ)) x + S.indicator (fun _ => (1 : ℝ)) (x - h)) := by
      intro x
      have hi1 : 0 ≤ S.indicator (fun _ => (1 : ℝ)) x :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) _
      have hi2 : 0 ≤ S.indicator (fun _ => (1 : ℝ)) (x - h) :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) _
      have h1 : |ψ x - ψ (x - h)| ≤ L * ‖h‖ := by
        have := hL x (x - h)
        simpa using this
      have h2 : (ψ x - ψ (x - h)) ^ 2 ≤ (L * ‖h‖) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx]
        nlinarith [mul_nonneg (mul_nonneg (sq_nonneg L) (sq_nonneg ‖h‖)) hi2]
      · by_cases hxh : x - h ∈ S
        · rw [Set.indicator_of_mem hxh]
          nlinarith [mul_nonneg (mul_nonneg (sq_nonneg L) (sq_nonneg ‖h‖)) hi1]
        · have e1 : ψ x = 0 := by
            by_contra hne; exact hx (hs (Function.mem_support.2 hne))
          have e2 : ψ (x - h) = 0 := by
            by_contra hne; exact hxh (hs (Function.mem_support.2 hne))
          rw [e1, e2]
          simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
          have : 0 ≤ L ^ 2 * ‖h‖ ^ 2 *
              (S.indicator (fun _ => (1 : ℝ)) x + S.indicator (fun _ => (1 : ℝ)) (x - h)) :=
            mul_nonneg (by positivity) (add_nonneg hi1 hi2)
          exact this
    calc ∫ x, (ψ x - ψ (x - h)) ^ 2
        ≤ ∫ x, L ^ 2 * ‖h‖ ^ 2 * (S.indicator (fun _ => (1 : ℝ)) x +
            S.indicator (fun _ => (1 : ℝ)) (x - h)) :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hrhs
            (Eventually.of_forall hpt)
      _ = 2 * L ^ 2 * V * ‖h‖ ^ 2 := by
          rw [integral_const_mul, integral_add hind hind', integral_indicator hSm,
            integral_sub_right_eq_self (S.indicator (fun _ => (1 : ℝ))) h,
            integral_indicator hSm]
          simp [hV, Measure.real]
          ring
  refine ⟨memSobolev_one_of_diff_bound hmem _ hdiff, ?_⟩
  -- the norm
  have hsum : Integrable (fun ξ : Euc d => ‖fourierL2 ψ ξ‖ ^ 2 +
      ∑ i : Fin d, 4 * Real.pi ^ 2 * (ξ i) ^ 2 * ‖fourierL2 ψ ξ‖ ^ 2) volume :=
    (integrable_norm_sq_fourierL2 hmem).add
      (integrable_finsetSum _ fun i _ => (coord_integrable hmem _ hdiff i).1)
  have hform : HRS.PDE.ToolboxRd.sobolevNormSq 1 ψ = ∫ ξ, (‖fourierL2 ψ ξ‖ ^ 2 +
      ∑ i : Fin d, 4 * Real.pi ^ 2 * (ξ i) ^ 2 * ‖fourierL2 ψ ξ‖ ^ 2) := by
    unfold HRS.PDE.ToolboxRd.sobolevNormSq
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    beta_reduce
    rw [Real.rpow_one]
    have hn : ‖ξ‖ ^ 2 = ∑ i : Fin d, (ξ i) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp
    simp only [hn, ← Finset.sum_mul, ← Finset.mul_sum]
    ring
  rw [hform, integral_add (integrable_norm_sq_fourierL2 hmem)
    (integrable_finsetSum _ fun i _ => (coord_integrable hmem _ hdiff i).1),
    integral_finsetSum _ fun i _ => (coord_integrable hmem _ hdiff i).1,
    integral_norm_sq_fourierL2 hmem]
  have h1 : ∫ x, ψ x ^ 2 ≤ A ^ 2 * V := by
    have hAi : Integrable (fun x => A ^ 2 * S.indicator (fun _ => (1 : ℝ)) x) volume :=
      hind.const_mul _
    calc ∫ x, ψ x ^ 2 ≤ ∫ x, A ^ 2 * S.indicator (fun _ => (1 : ℝ)) x := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hAi
            (Eventually.of_forall fun x => ?_)
          beta_reduce
          by_cases hx : x ∈ S
          · rw [Set.indicator_of_mem hx, mul_one, ← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hA x) 2
          · have e1 : ψ x = 0 := by
              by_contra hne; exact hx (hs (Function.mem_support.2 hne))
            rw [e1]
            have : 0 ≤ S.indicator (fun _ => (1 : ℝ)) x :=
              Set.indicator_nonneg (fun _ _ => zero_le_one) _
            simpa using mul_nonneg (sq_nonneg A) this
      _ = A ^ 2 * V := by
          rw [integral_const_mul, integral_indicator hSm]
          simp [hV, Measure.real]
  have h2 : ∑ i : Fin d, ∫ ξ, 4 * Real.pi ^ 2 * (ξ i) ^ 2 * ‖fourierL2 ψ ξ‖ ^ 2 ≤
      d * (2 * L ^ 2 * V) := by
    calc ∑ i : Fin d, ∫ ξ, 4 * Real.pi ^ 2 * (ξ i) ^ 2 * ‖fourierL2 ψ ξ‖ ^ 2
        ≤ ∑ _i : Fin d, (2 * L ^ 2 * V) :=
          Finset.sum_le_sum fun i _ => (coord_integrable hmem _ hdiff i).2
      _ = d * (2 * L ^ 2 * V) := by simp
  linarith

/-- A `C¹` function with `|u|, ‖∇u‖ ≤ A` is bounded in `H¹_uloc` by `C_χ A`. -/
theorem fcau_ul_bound {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) :
    ∃ Cχ : ℝ, 0 ≤ Cχ ∧ ∀ (u : Euc d → ℝ) (A : ℝ), ContDiff ℝ 1 u → (∀ x, |u x| ≤ A) →
      (∀ x, ‖fderiv ℝ u x‖ ≤ A) → ulocNormE 1 χ u ≤ ENNReal.ofReal (Cχ * A) := by
  have hχ1 : ContDiff ℝ 1 χ := hχ.1.of_le (by exact_mod_cast le_top)
  have hχd : Differentiable ℝ χ := hχ1.differentiable one_ne_zero
  obtain ⟨Aχ, hAχ⟩ : ∃ Aχ : ℝ, ∀ x, ‖fderiv ℝ χ x‖ ≤ Aχ := by
    have hc : Continuous (fderiv ℝ χ) := hχ1.continuous_fderiv one_ne_zero
    obtain ⟨L, hL⟩ := hc.bounded_above_of_compact_support (hχ.2.1.fderiv (𝕜 := ℝ))
    exact ⟨L, hL⟩
  have hAχ0 : 0 ≤ Aχ := (norm_nonneg _).trans (hAχ 0)
  set V : ℝ := (volume (closedBall (0 : Euc d) 2)).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  refine ⟨Real.sqrt (V + d * (2 * (Aχ + 1) ^ 2 * V)), Real.sqrt_nonneg _,
    fun u A hu hu0 hu1 => ?_⟩
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hu0 0)
  have hud : Differentiable ℝ u := hu.differentiable one_ne_zero
  unfold ulocNormE
  refine iSup_le fun z => ?_
  set ψ : Euc d → ℝ := fun x => χ (x - z) * u x with hψ
  have hψc : Continuous ψ := (hχ1.continuous.comp (continuous_id.sub continuous_const)).mul hu.continuous
  have hsupp : Function.support ψ ⊆ closedBall z 2 := by
    intro x hx
    have hx1 : χ (x - z) ≠ 0 := left_ne_zero_of_mul hx
    have : x - z ∈ tsupport χ := subset_tsupport _ hx1
    have h2 := hχ.2.2.1 this
    rw [mem_ball_zero_iff] at h2
    rw [mem_closedBall_iff_norm]
    exact h2.le
  have hχb : ∀ x, |χ x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (hχ.2.2.2.1 x).1]; exact (hχ.2.2.2.1 x).2
  have hψb : ∀ x, |ψ x| ≤ A := fun x => by
    rw [hψ]; beta_reduce; rw [abs_mul]
    calc |χ (x - z)| * |u x| ≤ 1 * A :=
          mul_le_mul (hχb _) (hu0 x) (abs_nonneg _) zero_le_one
      _ = A := one_mul A
  have hψd : ∀ x, HasFDerivAt ψ (χ (x - z) • fderiv ℝ u x + u x • fderiv ℝ χ (x - z)) x := by
    intro x
    have h1 : HasFDerivAt (fun x => χ (x - z)) (fderiv ℝ χ (x - z)) x := by
      have := (hχd (x - z)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const z)
      simpa [Function.comp_def] using this
    have h2 := h1.mul (hud x).hasFDerivAt
    convert h2 using 1
  have hψL : ∀ x y, |ψ x - ψ y| ≤ (Aχ * A + A) * ‖x - y‖ := by
    intro x y
    have hb : ∀ w ∈ (Set.univ : Set (Euc d)), ‖fderiv ℝ ψ w‖ ≤ Aχ * A + A := by
      intro w _
      rw [(hψd w).fderiv]
      refine (norm_add_le _ _).trans ?_
      have e1 : ‖χ (w - z) • fderiv ℝ u w‖ ≤ A := by
        rw [norm_smul, Real.norm_eq_abs]
        calc |χ (w - z)| * ‖fderiv ℝ u w‖ ≤ 1 * A :=
              mul_le_mul (hχb _) (hu1 w) (norm_nonneg _) zero_le_one
          _ = A := one_mul A
      have e2 : ‖u w • fderiv ℝ χ (w - z)‖ ≤ Aχ * A := by
        rw [norm_smul, Real.norm_eq_abs]
        calc |u w| * ‖fderiv ℝ χ (w - z)‖ ≤ A * Aχ :=
              mul_le_mul (hu0 w) (hAχ _) (norm_nonneg _) hA0
          _ = Aχ * A := mul_comm _ _
      linarith
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := ψ)
      (fun w _ => (hψd w).differentiableAt) hb convex_univ (Set.mem_univ y) (Set.mem_univ x)
    simpa [Real.norm_eq_abs, norm_sub_rev] using this
  obtain ⟨hmem, hnorm⟩ := fcau_sobNormSq_le hψL hψb hsupp hψc
  have hvol : (volume (closedBall z 2)).toReal = V := by
    rw [hV, Measure.addHaar_closedBall_center]
  rw [hvol] at hnorm
  unfold sobolevNormE
  rw [if_pos (by simpa using hmem)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hn : HRS.PDE.ToolboxRd.sobolevNormSq ((1 : ℕ) : ℝ) ψ = HRS.PDE.ToolboxRd.sobolevNormSq 1 ψ := by
    simp
  rw [hn]
  have hnn : 0 ≤ HRS.PDE.ToolboxRd.sobolevNormSq 1 ψ := by
    unfold HRS.PDE.ToolboxRd.sobolevNormSq
    exact integral_nonneg fun ξ => by
      have := one_le_wt ξ
      unfold wt at this
      rw [Real.rpow_one]; positivity
  calc Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq 1 ψ)
      ≤ Real.sqrt (A ^ 2 * (V + d * (2 * (Aχ + 1) ^ 2 * V))) := by
        refine Real.sqrt_le_sqrt (hnorm.trans ?_)
        have : (Aχ * A + A) ^ 2 = A ^ 2 * (Aχ + 1) ^ 2 := by ring
        rw [this]
        nlinarith [mul_nonneg (sq_nonneg A) hV0, Nat.cast_nonneg (α := ℝ) d]
    _ = Real.sqrt (V + d * (2 * (Aχ + 1) ^ 2 * V)) * A := by
        rw [Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq hA0, mul_comm]

/-! ### The time integral of a classical solution against a test function -/

section Time

open HRS.MH.DualityRd

/-- `u ↦ ∫ ψ ∂_u f` is continuous on `[0,t]`. -/
theorem fcau_Gcont {t : ℝ} {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft) {ψ : Euc d → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    ContinuousOn (fun u => ∫ x, ψ x * ft u x) (Set.Icc 0 t) := by
  obtain ⟨B, hB⟩ := hf.lin_growth
  have hbd : Integrable (fun x => ‖ψ x‖ * (|B| * (1 + ‖x‖))) volume := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · fun_prop
    · exact hψc.norm.mul_right
  refine continuousOn_of_dominated (bound := fun x => ‖ψ x‖ * (|B| * (1 + ‖x‖))) ?_ ?_ hbd ?_
  · intro u hu
    have hc : Continuous fun x => ft u x :=
      hf.cont_time_deriv.comp (Continuous.prodMk (continuous_const (y := (⟨u, hu⟩ : Set.Icc (0 : ℝ) t)))
        continuous_id)
    exact (hψ.mul hc).aestronglyMeasurable
  · intro u hu
    refine Eventually.of_forall fun x => ?_
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [Real.norm_eq_abs]
    exact (hB u hu x).trans (mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity))
  · exact Eventually.of_forall fun x =>
      continuousOn_const.mul (da1_continuousOn_timeDeriv hf x)

/-- Fubini for the time integral of `ft` against a compactly supported test function. -/
theorem fcau_fubini {t : ℝ} (ht : 0 ≤ t) {ft : ℝ → Euc d → ℝ}
    (hft : Continuous fun q : Set.Icc (0 : ℝ) t × Euc d => ft q.1.1 q.2) {B : ℝ}
    (hB : ∀ u ∈ Set.Icc (0 : ℝ) t, ∀ x, |ft u x| ≤ B * (1 + ‖x‖)) {ψ : Euc d → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hbt : b ≤ t) :
    ∫ x, ψ x * (∫ u in a..b, ft u x) = ∫ u in a..b, ∫ x, ψ x * ft u x := by
  set Φ : ℝ → Euc d → ℝ := fun u x => ft (max 0 (min u t)) x with hΦdef
  have hΦc : Continuous (fun q : ℝ × Euc d => Φ q.1 q.2) := db3_Phi_cont ht hft
  have hΦB : ∀ u : ℝ, ∀ x, |Φ u x| ≤ |B| * (1 + ‖x‖) := fun u x => by
    have := hB _ (db3_clamp_mem ht u) x
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity))
  have hFi : Integrable (fun z : Euc d × ℝ => ψ z.1 * Φ z.2 z.1)
      ((volume : Measure (Euc d)).prod (volume.restrict (Set.Ioc a b))) := by
    have : IsFiniteMeasure (volume.restrict (Set.Ioc a b)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
    have hg : Integrable (fun x : Euc d => |B| * (‖ψ x‖ * (1 + ‖x‖))) volume := by
      refine Continuous.integrable_of_hasCompactSupport ?_ ?_
      · fun_prop
      · exact (hψc.norm.mul_right).mul_left
    have hprod := hg.mul_prod (integrable_const (1 : ℝ) (μ := volume.restrict (Set.Ioc a b)))
    refine hprod.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact ((hψ.measurable.comp measurable_fst).mul
        (hΦc.measurable.comp (measurable_snd.prodMk measurable_fst))).aestronglyMeasurable
    · show ‖ψ z.1 * Φ z.2 z.1‖ ≤ (|B| * (‖ψ z.1‖ * (1 + ‖z.1‖))) * 1
      rw [norm_mul, Real.norm_eq_abs]
      calc ‖ψ z.1‖ * |Φ z.2 z.1| ≤ ‖ψ z.1‖ * (|B| * (1 + ‖z.1‖)) :=
            mul_le_mul_of_nonneg_left (hΦB _ _) (norm_nonneg _)
        _ = (|B| * (‖ψ z.1‖ * (1 + ‖z.1‖))) * 1 := by ring
  have hswap := integral_integral_swap (μ := volume) (ν := volume.restrict (Set.Ioc a b))
    (f := fun x u => ψ x * Φ u x) hFi
  have e1 : ∀ x : Euc d, ∫ u in a..b, ft u x = ∫ u, Φ u x ∂(volume.restrict (Set.Ioc a b)) := by
    intro x
    rw [intervalIntegral.integral_of_le hab]
    refine setIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)
    have hu' : u ∈ Set.Icc (0 : ℝ) t := ⟨ha.trans (le_of_lt hu.1), hu.2.trans hbt⟩
    show ft u x = ft (max 0 (min u t)) x
    rw [db3_clamp_eq hu']
  calc ∫ x, ψ x * (∫ u in a..b, ft u x)
      = ∫ x, ∫ u, ψ x * Φ u x ∂(volume.restrict (Set.Ioc a b)) := by
        congr 1
        funext x
        rw [e1 x, integral_const_mul]
    _ = ∫ u, ∫ x, ψ x * Φ u x ∂volume ∂(volume.restrict (Set.Ioc a b)) := hswap
    _ = ∫ u in a..b, ∫ x, ψ x * ft u x := by
        rw [intervalIntegral.integral_of_le hab]
        refine setIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)
        have hu' : u ∈ Set.Icc (0 : ℝ) t := ⟨ha.trans (le_of_lt hu.1), hu.2.trans hbt⟩
        show ∫ x, ψ x * Φ u x = ∫ x, ψ x * ft u x
        congr 1
        funext x
        show ψ x * ft (max 0 (min u t)) x = ψ x * ft u x
        rw [db3_clamp_eq hu']

/-- The integrated form: `∫ψ f(b) - ∫ψ f(a) = ∫_a^b ∫ψ ∂_u f`. -/
theorem fcau_ftc_integral {t : ℝ} {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft) {ψ : Euc d → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hbt : b ≤ t) :
    (∫ x, ψ x * f b x) - ∫ x, ψ x * f a x = ∫ u in a..b, ∫ x, ψ x * ft u x := by
  have ht : 0 ≤ t := ha.trans (hab.trans hbt)
  obtain ⟨B, hB⟩ := hf.lin_growth
  have hfcont : ∀ u ∈ Set.Icc (0 : ℝ) t, Continuous (f u) := fun u hu =>
    (hf.c2 u hu).continuous
  have hI : ∀ u ∈ Set.Icc (0 : ℝ) t, Integrable (fun x => ψ x * f u x) volume := fun u hu =>
    (hψ.mul (hfcont u hu)).integrable_of_hasCompactSupport hψc.mul_right
  have hb : b ∈ Set.Icc (0 : ℝ) t := ⟨ha.trans hab, hbt⟩
  have ha' : a ∈ Set.Icc (0 : ℝ) t := ⟨ha, hab.trans hbt⟩
  rw [← integral_sub (hI b hb) (hI a ha')]
  rw [← fcau_fubini ht hf.cont_time_deriv (fun u hu x => by
    have := hB u hu x
    exact this) hψ hψc ha hab hbt]
  congr 1
  funext x
  rw [db3_ftc hf ha hab hbt x]
  ring

end Time

end HRS.MS.Fcau
