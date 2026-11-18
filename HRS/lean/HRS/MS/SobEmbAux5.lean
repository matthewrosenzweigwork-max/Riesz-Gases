import HRS.MS.SobEmbAux4

/-!
# SA1, Aux5: Morrey's inequality `‖g x‖ ≤ K (‖g‖_q + ‖Dg‖_q)` for `q > d`

Proof by the ball-average argument (all in `ℝ≥0∞`, no junk values): for `z` in the unit ball,
`‖g x‖ ≤ ‖g(x+z)‖ + ∫₀¹ ‖Dg(x+tz)‖ ‖z‖ dt`; average over `z`, swap, rescale `z ↦ tz`, and Hölder in `z`
for each `t`.  The `t`-integral is `∫₀¹ t^{-d/q} dt < ∞` exactly because `q > d`.
-/

noncomputable section

open MeasureTheory Filter Topology Module Set
open scoped ENNReal NNReal ContDiff

namespace HRS.SA1

variable {d : ℕ}

/-- Segment bound. -/
theorem sa1_segment {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {g : EuclideanSpace ℝ (Fin d) → F} (hg : ContDiff ℝ 1 g) (x z : EuclideanSpace ℝ (Fin d)) :
    ‖g x‖ₑ ≤ ‖g (x + z)‖ₑ + ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ g (x + t • z)‖ₑ * ‖z‖ₑ := by
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hder : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => g (x + t • z))
      (fderiv ℝ g (x + t • z) z) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => x + t • z) z t := by
      simpa using ((hasDerivAt_id t).smul_const z).const_add x
    have h2 := (hgd (x + t • z)).hasFDerivAt.comp_hasDerivAt t h1
    exact h2
  have hcont : Continuous (fun t : ℝ => fderiv ℝ g (x + t • z) z) :=
    ((hg.continuous_fderiv (by simp)).comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
      continuous_const
  have hint := hcont.intervalIntegrable (μ := volume) 0 1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint
  simp only [one_smul, zero_smul, add_zero] at hftc
  have hle : ‖g (x + z) - g x‖ₑ ≤ ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ g (x + t • z)‖ₑ * ‖z‖ₑ := by
    rw [← hftc, intervalIntegral.integral_of_le zero_le_one]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun t => ?_)
    exact ContinuousLinearMap.le_opENorm _ _
  calc ‖g x‖ₑ = ‖g (x + z) - (g (x + z) - g x)‖ₑ := by rw [sub_sub_cancel]
    _ ≤ ‖g (x + z)‖ₑ + ‖g (x + z) - g x‖ₑ := enorm_sub_le
    _ ≤ _ := by gcongr

/-- Rescaling in a ball. -/
theorem sa1_scale (G : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hG : Measurable G) {t : ℝ} (ht : 0 < t) :
    ∫⁻ z in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1, G (t • z) =
      ENNReal.ofReal ((t ^ d)⁻¹) * ∫⁻ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) t, G y := by
  set F : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) t).indicator G with hF
  have hFm : Measurable F := hG.indicator Metric.isOpen_ball.measurableSet
  have h1 : ∫⁻ z, F (t • z) = ENNReal.ofReal ((t ^ d)⁻¹) * ∫⁻ y, F y := by
    have h2 := lintegral_map hFm (measurable_const_smul t) (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
    rw [Measure.map_addHaar_smul volume ht.ne', lintegral_smul_measure] at h2
    simp only [finrank_euclideanSpace_fin] at h2
    rw [← h2]
    congr 2
    rw [abs_of_pos (by positivity)]
  have h3 : ∀ z, F (t • z) = (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1).indicator (fun z => G (t • z)) z := by
    intro z
    simp only [hF, Set.indicator, Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.le]
    have : t * ‖z‖ < t ↔ ‖z‖ < 1 := by
      constructor
      · intro h; by_contra h'; push Not at h'; nlinarith
      · intro h; nlinarith
    simp only [this]
  have h4 : ∫⁻ z, F (t • z) = ∫⁻ z in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1, G (t • z) := by
    simp_rw [h3]
    rw [lintegral_indicator Metric.isOpen_ball.measurableSet]
  rw [← h4, h1, hF, lintegral_indicator Metric.isOpen_ball.measurableSet]


/-- **Morrey's inequality** on `ℝ^d`: for `q > d`, `‖g x‖ ≤ K (‖g‖_q + ‖Dg‖_q)` for every `C¹` map `g`. -/
theorem sa1_morrey (hd : 1 ≤ d) {q : ℝ} (hq : (d : ℝ) < q) {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] :
    ∃ K : ℝ≥0, ∀ g : EuclideanSpace ℝ (Fin d) → F, ContDiff ℝ 1 g → ∀ x,
      ‖g x‖ₑ ≤ K * (eLpNorm g (ENNReal.ofReal q) volume + eLpNorm (fderiv ℝ g) (ENNReal.ofReal q) volume) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hq1 : 1 < q := by linarith
  have hq0 : 0 < q := by linarith
  set q' : ℝ := Real.conjExponent q with hq'def
  have hconj : q.HolderConjugate q' := Real.HolderConjugate.conjExponent hq1
  have hq'pos : 0 < q' := hconj.symm.pos
  set B : Set (EuclideanSpace ℝ (Fin d)) := Metric.ball 0 1 with hB
  set V : ℝ≥0∞ := volume B with hV
  have hV0 : V ≠ 0 := (Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin d)) one_pos).ne'
  have hVtop : V ≠ ⊤ := measure_ball_lt_top.ne
  set W : ℝ≥0∞ := V ^ (1 / q') with hW
  have hWtop : W ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hVtop
  set s : ℝ := d / q with hs
  have hs0 : 0 < s := by positivity
  have hs1 : s < 1 := by rw [hs, div_lt_one hq0]; exact hq
  have hJ : ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ (-s)) < ⊤ := by
    have : IntegrableOn (fun t : ℝ => t ^ (-s)) (Ioc 0 1) :=
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (by linarith : -1 < -s)).1
    exact this.lintegral_lt_top
  set J : ℝ≥0∞ := ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ (-s)) with hJdef
  have hJtop : J ≠ ⊤ := hJ.ne
  -- Hölder on the unit ball against a function bounded by 1
  have holder : ∀ (f h : EuclideanSpace ℝ (Fin d) → ℝ≥0∞), Measurable f → Measurable h →
      (∀ z ∈ B, h z ≤ 1) →
      ∫⁻ z in B, f z * h z ≤ (∫⁻ z in B, f z ^ q) ^ (1 / q) * W := by
    intro f h hf hh h1
    refine (ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict B) hconj hf.aemeasurable hh.aemeasurable).trans ?_
    refine mul_le_mul' le_rfl ?_
    rw [hW]
    refine ENNReal.rpow_le_rpow ?_ (by positivity)
    calc ∫⁻ z in B, h z ^ q' ≤ ∫⁻ z in B, 1 := by
          refine setLIntegral_mono measurable_const fun z hz => ?_
          exact ENNReal.rpow_le_one (h1 z hz) hq'pos.le
      _ = V := by rw [setLIntegral_one]
  set K' : ℝ≥0∞ := V⁻¹ * W * (1 + J) with hK'
  have hK'top : K' ≠ ⊤ := by
    rw [hK']
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hV0) hWtop)
      (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hJtop⟩)
  refine ⟨K'.toNNReal, fun g hg x => ?_⟩
  have hgc : Continuous g := hg.continuous
  have hdc : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by simp)
  set H : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun y => ‖fderiv ℝ g y‖ₑ with hH
  have hHm : Measurable H := hdc.enorm.measurable
  have hq0' : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.2 hq0).ne'
  have hNg : eLpNorm g (ENNReal.ofReal q) volume = (∫⁻ y, ‖g y‖ₑ ^ q) ^ (1 / q) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0' ENNReal.ofReal_ne_top hgc.aestronglyMeasurable,
      ENNReal.toReal_ofReal hq0.le]
  have hNH : eLpNorm (fderiv ℝ g) (ENNReal.ofReal q) volume = (∫⁻ y, H y ^ q) ^ (1 / q) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0' ENNReal.ofReal_ne_top hdc.aestronglyMeasurable,
      ENNReal.toReal_ofReal hq0.le]
  -- the first term
  have hT1 : ∫⁻ z in B, ‖g (x + z)‖ₑ ≤ eLpNorm g (ENNReal.ofReal q) volume * W := by
    have h1 := holder (fun z => ‖g (x + z)‖ₑ) (fun _ => 1)
      (hgc.comp (continuous_const.add continuous_id)).enorm.measurable measurable_const (fun _ _ => le_rfl)
    simp only [mul_one] at h1
    refine h1.trans (mul_le_mul' ?_ le_rfl)
    rw [hNg]
    refine ENNReal.rpow_le_rpow ?_ (by positivity)
    refine (setLIntegral_le_lintegral B _).trans (le_of_eq ?_)
    exact lintegral_add_left_eq_self (fun y => ‖g y‖ₑ ^ q) x
  -- the second term, for fixed t
  have hT2 : ∀ t ∈ Ioc (0 : ℝ) 1, ∫⁻ z in B, H (x + t • z) * ‖z‖ₑ ≤
      ENNReal.ofReal (t ^ (-s)) * eLpNorm (fderiv ℝ g) (ENNReal.ofReal q) volume * W := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have h1 := holder (fun z => H (x + t • z)) (fun z => ‖z‖ₑ)
      (hHm.comp (measurable_const.add (measurable_const_smul t))) measurable_id.enorm
      (fun z hz => by
        have : ‖z‖ < 1 := by simpa [hB] using hz
        rw [← ofReal_norm]; exact ENNReal.ofReal_le_one.2 this.le)
    refine h1.trans (mul_le_mul' ?_ le_rfl)
    have hsc := sa1_scale (fun y => H (x + y) ^ q) ((hHm.comp (measurable_const.add measurable_id)).pow_const q) ht0
    have hrw : ∫⁻ z in B, H (x + t • z) ^ q = ENNReal.ofReal ((t ^ d)⁻¹) *
        ∫⁻ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) t, H (x + y) ^ q := hsc
    have hle : ∫⁻ z in B, H (x + t • z) ^ q ≤ ENNReal.ofReal ((t ^ d)⁻¹) * ∫⁻ y, H y ^ q := by
      rw [hrw]
      refine mul_le_mul' le_rfl ((setLIntegral_le_lintegral _ _).trans (le_of_eq ?_))
      exact lintegral_add_left_eq_self (fun y => H y ^ q) x
    calc (∫⁻ z in B, H (x + t • z) ^ q) ^ (1 / q)
        ≤ (ENNReal.ofReal ((t ^ d)⁻¹) * ∫⁻ y, H y ^ q) ^ (1 / q) := ENNReal.rpow_le_rpow hle (by positivity)
      _ = ENNReal.ofReal ((t ^ d)⁻¹) ^ (1 / q) * (∫⁻ y, H y ^ q) ^ (1 / q) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
      _ = ENNReal.ofReal (t ^ (-s)) * eLpNorm (fderiv ℝ g) (ENNReal.ofReal q) volume := by
          rw [hNH, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
          congr 2
          rw [← Real.rpow_natCast, ← Real.rpow_neg ht0.le, ← Real.rpow_mul ht0.le, hs]
          congr 1
          ring
  have step1 : V * ‖g x‖ₑ ≤ (∫⁻ z in B, ‖g (x + z)‖ₑ) +
      ∫⁻ z in B, ∫⁻ t in Ioc (0 : ℝ) 1, H (x + t • z) * ‖z‖ₑ := by
    calc V * ‖g x‖ₑ = ∫⁻ z in B, ‖g x‖ₑ := by rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ z in B, (‖g (x + z)‖ₑ + ∫⁻ t in Ioc (0 : ℝ) 1, H (x + t • z) * ‖z‖ₑ) :=
          lintegral_mono fun z => sa1_segment hg x z
      _ = _ := lintegral_add_left (hgc.comp (continuous_const.add continuous_id)).enorm.measurable _
  have hswap : ∫⁻ z in B, ∫⁻ t in Ioc (0 : ℝ) 1, H (x + t • z) * ‖z‖ₑ =
      ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ z in B, H (x + t • z) * ‖z‖ₑ := by
    refine lintegral_lintegral_swap ?_
    refine Measurable.aemeasurable ?_
    show Measurable (fun p : EuclideanSpace ℝ (Fin d) × ℝ => H (x + p.2 • p.1) * ‖p.1‖ₑ)
    exact (hHm.comp (measurable_const.add (measurable_snd.smul measurable_fst))).mul measurable_fst.enorm
  have hT2int : ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ z in B, H (x + t • z) * ‖z‖ₑ ≤
      J * eLpNorm (fderiv ℝ g) (ENNReal.ofReal q) volume * W := by
    calc ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ z in B, H (x + t • z) * ‖z‖ₑ
        ≤ ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ (-s)) *
            eLpNorm (fderiv ℝ g) (ENNReal.ofReal q) volume * W := setLIntegral_mono' measurableSet_Ioc hT2
      _ = J * eLpNorm (fderiv ℝ g) (ENNReal.ofReal q) volume * W := by
          have hm : Measurable (fun t : ℝ => ENNReal.ofReal (t ^ (-s))) :=
            ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
          rw [lintegral_mul_const _ (hm.mul_const _), lintegral_mul_const _ hm]
  have key : V * ‖g x‖ₑ ≤ eLpNorm g (ENNReal.ofReal q) volume * W +
      J * eLpNorm (fderiv ℝ g) (ENNReal.ofReal q) volume * W := by
    refine step1.trans ?_
    rw [hswap]
    exact add_le_add hT1 hT2int
  have hcoe : ((K'.toNNReal : ℝ≥0) : ℝ≥0∞) = K' := ENNReal.coe_toNNReal hK'top
  rw [hcoe]
  set Ng := eLpNorm g (ENNReal.ofReal q) volume
  set NH := eLpNorm (fderiv ℝ g) (ENNReal.ofReal q) volume
  calc ‖g x‖ₑ = V⁻¹ * (V * ‖g x‖ₑ) := by rw [← mul_assoc, ENNReal.inv_mul_cancel hV0 hVtop, one_mul]
    _ ≤ V⁻¹ * (Ng * W + J * NH * W) := by gcongr
    _ = V⁻¹ * W * (Ng + J * NH) := by ring
    _ ≤ V⁻¹ * W * ((1 + J) * (Ng + NH)) := by
        gcongr
        calc Ng + J * NH ≤ (Ng + J * Ng) + (NH + J * NH) := add_le_add le_self_add le_add_self
          _ = (1 + J) * (Ng + NH) := by ring
    _ = K' * (Ng + NH) := by rw [hK']; ring

end HRS.SA1
