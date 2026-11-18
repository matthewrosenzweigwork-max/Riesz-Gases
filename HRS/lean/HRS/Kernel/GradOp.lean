import HRS.Kernel.GradBasic

/-!
# The cancellation convolution with a kernel of order `|z|^{-s-1}`

Auxiliary file of `HRS/Kernel/GradConv.lean`.  For a measurable odd kernel `G` with
`‖G z‖ ≤ C (|z|^{-s-1} + 1)`, the cancellation convolution `convGradConv G h` of a Lipschitz
function `h` is an absolutely convergent integral; we record the basic estimates.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.KernelGrad

variable {d : ℕ}

instance instNegInvariantTorus (d : ℕ) : (volume : Measure (Torus d)).IsNegInvariant :=
  Measure.IsAddHaarMeasure.isNegInvariant_of_regular _

/-! ### Integrability of powers of the torus norm -/

theorem norm_boxPt {y : Fin d → ℝ} (hy : y ∈ HRS.KernelAux.Box d) :
    ‖HRS.KernelAux.boxPt y‖ = ‖y‖ := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    have : ‖((y i : ℝ) : UnitAddCircle)‖ = |y i| := by
      rw [AddCircle.norm_coe_eq_abs_iff (1:ℝ) one_ne_zero]
      simpa using HRS.KernelAux.Box_abs_le hy i
    show ‖((y i : ℝ) : UnitAddCircle)‖ ≤ _
    rw [this, ← Real.norm_eq_abs]
    exact norm_le_pi_norm y i
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    have : ‖((y i : ℝ) : UnitAddCircle)‖ = |y i| := by
      rw [AddCircle.norm_coe_eq_abs_iff (1:ℝ) one_ne_zero]
      simpa using HRS.KernelAux.Box_abs_le hy i
    rw [Real.norm_eq_abs, ← this]
    exact norm_le_pi_norm (HRS.KernelAux.boxPt y) i

theorem integrable_norm_rpow_neg (hd : 0 < d) {α : ℝ} (hα : α < d) :
    Integrable (fun z : Torus d => ‖z‖ ^ (-α)) := by
  refine ⟨(measurable_norm.pow_const _).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  rw [HRS.KernelAux.lintegral_torus_box]
  have h := (HRS.KernelAux.integrableOn_Box_rpow hd hα).2
  unfold HasFiniteIntegral at h
  refine lt_of_le_of_lt (le_of_eq ?_) h
  refine setLIntegral_congr_fun (HRS.KernelAux.measurableSet_Box d) fun y hy => ?_
  show ‖‖HRS.KernelAux.boxPt y‖ ^ (-α)‖ₑ = ‖‖y‖ ^ (-α)‖ₑ
  rw [norm_boxPt hy]

theorem torus_ae_ne' (hd : 0 < d) : ∀ᵐ x : Torus d, x ≠ 0 := HRS.KernelAux.torus_ae_ne hd


/-! ### Good kernels and the integrand of the cancellation convolution -/

/-- Hypotheses on a kernel `G` (`G = ∇g` or a heat regularisation of it) used to control the
cancellation convolution. -/
structure GoodKernel (d : ℕ) (s C : ℝ) (G : Torus d → Euc d) : Prop where
  pos : 0 < d
  hs0 : 0 ≤ s
  hsd : s < d
  hC0 : 0 ≤ C
  meas : Measurable G
  odd : ∀ z, G (-z) = -G z
  bound : ∀ z, z ≠ 0 → ‖G z‖ ≤ C * (tdist z 0 ^ (-s - 1) + 1)

variable {s C : ℝ} {G : Torus d → Euc d}

/-- The integrand of the cancellation convolution after the substitution `y = x - z`. -/
def kern (G : Torus d → Euc d) (h : Torus d → ℝ) (x z : Torus d) : Euc d :=
  if ‖z‖ ≤ 1 / 4 then (h (x - z) - h x) • G z else h (x - z) • G z

theorem convGradConv_eq_integral_kern (G : Torus d → Euc d) (h : Torus d → ℝ) (x : Torus d) :
    convGradConv G h x = ∫ z, kern G h x z := by
  unfold convGradConv kern
  rw [← integral_sub_left_eq_self (fun y => if ‖x - y‖ ≤ 1 / 4 then (h y - h x) • G (x - y)
    else h y • G (x - y)) volume x]
  simp only [sub_sub_cancel]

theorem tdist_le_card (z : Torus d) : tdist z 0 ≤ d := by
  rw [tdist_zero_right]
  have h := HRS.KernelAux.norm_toLp_le_sum (WithLp.ofLp (centeredRep z))
  rw [WithLp.toLp_ofLp] at h
  refine h.trans ?_
  calc ∑ j, |(WithLp.ofLp (centeredRep z)) j| ≤ ∑ _j : Fin d, (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => (abs_centeredRep_le z j).trans (by norm_num)
    _ = d := by simp

theorem GoodKernel.bound_norm (hG : GoodKernel d s C G) :
    ∀ z, z ≠ 0 → ‖G z‖ ≤ C * (‖z‖ ^ (-s - 1) + 1) := by
  intro z hz
  refine (hG.bound z hz).trans ?_
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have : tdist z 0 ^ (-s - 1) ≤ ‖z‖ ^ (-s - 1) :=
    Real.rpow_le_rpow_of_nonpos hz0 (norm_le_tdist z) (by have := hG.hs0; linarith)
  have := hG.hC0
  gcongr

theorem GoodKernel.norm_mul_tdist_le (hG : GoodKernel d s C G) :
    ∀ z, z ≠ 0 → tdist z 0 * ‖G z‖ ≤ C * (‖z‖ ^ (-s) + d) := by
  intro z hz
  have hC0 := hG.hC0
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have ht0 : 0 < tdist z 0 := tdist_pos hz
  have h1 : tdist z 0 ^ (-s) ≤ ‖z‖ ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos hz0 (norm_le_tdist z) (by have := hG.hs0; linarith)
  have h2 : tdist z 0 ≤ d := tdist_le_card z
  have h3 : tdist z 0 * tdist z 0 ^ (-s - 1) = tdist z 0 ^ (-s) := by
    have := Real.rpow_add ht0 1 (-s - 1)
    rw [Real.rpow_one] at this
    rw [← this]; congr 1; ring
  calc tdist z 0 * ‖G z‖ ≤ tdist z 0 * (C * (tdist z 0 ^ (-s - 1) + 1)) := by
        gcongr; exact hG.bound z hz
    _ = C * (tdist z 0 ^ (-s) + tdist z 0) := by rw [← h3]; ring
    _ ≤ C * (‖z‖ ^ (-s) + d) := by gcongr

theorem tdist_le_mul_norm (z : Torus d) : tdist z 0 ≤ d * ‖z‖ := by
  rw [tdist_zero_right]
  have h := HRS.KernelAux.norm_toLp_le_sum (WithLp.ofLp (centeredRep z))
  rw [WithLp.toLp_ofLp] at h
  refine h.trans ?_
  calc ∑ j, |(WithLp.ofLp (centeredRep z)) j| ≤ ∑ _j : Fin d, ‖z‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [← norm_apply_eq]
        exact norm_le_pi_norm z j
    _ = d * ‖z‖ := by simp

theorem tdist_eq_sub_zero (x y : Torus d) : tdist x y = tdist (x - y) 0 := by
  simp [tdist]

theorem tdist_sub_comm (x y : Torus d) : tdist x y = tdist y x := by
  unfold tdist
  rw [← neg_sub y x, ← tdist_zero_right, ← tdist_zero_right, tdist_neg]

theorem IsLipschitz.continuous {L : ℝ} {h : Torus d → ℝ} (hL : IsLipschitz L h) (hL0 : 0 ≤ L) :
    Continuous h := by
  have : LipschitzWith (Real.toNNReal (L * d)) h := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
    refine (hL x y).trans ?_
    have h1 : tdist x y ≤ d * ‖x - y‖ := by
      rw [tdist_eq_sub_zero]; exact tdist_le_mul_norm (x - y)
    calc L * tdist x y ≤ L * (d * ‖x - y‖) := by gcongr
      _ = L * d * ‖x - y‖ := by ring
  exact this.continuous

/-- The pointwise bound for the integrand `kern`. -/
theorem kern_norm_le (hG : GoodKernel d s C G)
    {h : Torus d → ℝ} {B L : ℝ} (hB : ∀ x, |h x| ≤ B) (hL : IsLipschitz L h) (hL0 : 0 ≤ L)
    (hB0 : 0 ≤ B) (x : Torus d) {z : Torus d} (hz : z ≠ 0) :
    ‖kern G h x z‖ ≤ L * C * (‖z‖ ^ (-s) + d) + B * C * ((1 / 4 : ℝ) ^ (-s - 1) + 1) := by
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hC0 := hG.hC0
  have hC := hG.bound_norm
  have hC' := hG.norm_mul_tdist_le
  have hpos1 : 0 ≤ L * C * (‖z‖ ^ (-s) + d) := by positivity
  have hpos2 : 0 ≤ B * C * ((1 / 4 : ℝ) ^ (-s - 1) + 1) := by positivity
  unfold kern
  split_ifs with hcube
  · rw [norm_smul, Real.norm_eq_abs]
    have h1 : |h (x - z) - h x| ≤ L * tdist z 0 := by
      refine (hL (x - z) x).trans ?_
      rw [tdist_eq_sub_zero (x - z) x, sub_sub_cancel_left, tdist_neg]
    calc |h (x - z) - h x| * ‖G z‖ ≤ (L * tdist z 0) * ‖G z‖ := by gcongr
      _ = L * (tdist z 0 * ‖G z‖) := by ring
      _ ≤ L * (C * (‖z‖ ^ (-s) + d)) := mul_le_mul_of_nonneg_left (hC' z hz) hL0
      _ = L * C * (‖z‖ ^ (-s) + d) := by ring
      _ ≤ _ := by linarith
  · push Not at hcube
    rw [norm_smul, Real.norm_eq_abs]
    have h1 : ‖z‖ ^ (-s - 1) ≤ (1 / 4 : ℝ) ^ (-s - 1) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hcube.le (by have := hG.hs0; linarith)
    calc |h (x - z)| * ‖G z‖ ≤ B * (C * (‖z‖ ^ (-s - 1) + 1)) := by
          gcongr; exact hB _; exact hC z hz
      _ ≤ B * (C * ((1 / 4 : ℝ) ^ (-s - 1) + 1)) := by gcongr
      _ = B * C * ((1 / 4 : ℝ) ^ (-s - 1) + 1) := by ring
      _ ≤ _ := by linarith


/-- The dominating function of `kern`. -/
def dom (s C L B : ℝ) (d : ℕ) (z : Torus d) : ℝ :=
  L * C * (‖z‖ ^ (-s) + d) + B * C * ((1 / 4 : ℝ) ^ (-s - 1) + 1)

theorem integrable_dom (hG : GoodKernel d s C G) (L B : ℝ) : Integrable (dom s C L B d) := by
  unfold dom
  have h1 := integrable_norm_rpow_neg hG.pos hG.hsd
  exact (((h1.add (integrable_const (d : ℝ))).const_mul (L * C)).add (integrable_const _))

theorem integral_dom (hG : GoodKernel d s C G) (L B : ℝ) :
    ∫ z, dom s C L B d z = L * C * ((∫ z : Torus d, ‖z‖ ^ (-s)) + d) +
      B * C * ((1 / 4 : ℝ) ^ (-s - 1) + 1) := by
  unfold dom
  have h1 := integrable_norm_rpow_neg hG.pos hG.hsd
  have h2 : Integrable (fun z : Torus d => ‖z‖ ^ (-s) + (d : ℝ)) := h1.add (integrable_const (d : ℝ))
  have h3 : Integrable (fun z : Torus d => L * C * (‖z‖ ^ (-s) + (d : ℝ))) := h2.const_mul (L * C)
  rw [integral_add h3 (integrable_const _), integral_const_mul, integral_add h1 (integrable_const (d : ℝ))]
  simp

theorem measurable_kern (hG : GoodKernel d s C G) {h : Torus d → ℝ} (hh : Measurable h) (x : Torus d) :
    Measurable (kern G h x) := by
  unfold kern
  refine Measurable.ite (measurableSet_le measurable_norm measurable_const) ?_ ?_
  · exact ((hh.comp (measurable_const.sub measurable_id)).sub measurable_const).smul hG.meas
  · exact (hh.comp (measurable_const.sub measurable_id)).smul hG.meas

theorem kern_bound_ae (hG : GoodKernel d s C G)
    {h : Torus d → ℝ} {B L : ℝ} (hB : ∀ x, |h x| ≤ B) (hL : IsLipschitz L h) (hL0 : 0 ≤ L)
    (hB0 : 0 ≤ B) (x : Torus d) : ∀ᵐ z : Torus d, ‖kern G h x z‖ ≤ dom s C L B d z := by
  filter_upwards [torus_ae_ne' hG.pos] with z hz
  exact kern_norm_le hG hB hL hL0 hB0 x hz

theorem integrable_kern (hG : GoodKernel d s C G)
    {h : Torus d → ℝ} {B L : ℝ} (hh : Measurable h) (hB : ∀ x, |h x| ≤ B) (hL : IsLipschitz L h)
    (hL0 : 0 ≤ L) (hB0 : 0 ≤ B) (x : Torus d) : Integrable (kern G h x) :=
  (integrable_dom hG L B).mono' (measurable_kern hG hh x).aestronglyMeasurable
    (kern_bound_ae hG hB hL hL0 hB0 x)


/-- Constants in the bound of the cancellation convolution (they depend on `d, s, C` only). -/
def opM1 (d : ℕ) (s C : ℝ) : ℝ := C * ((∫ z : Torus d, ‖z‖ ^ (-s)) + d)

def opM2 (s C : ℝ) : ℝ := C * ((1 / 4 : ℝ) ^ (-s - 1) + 1)

theorem opM1_nonneg (hG : GoodKernel d s C G) : 0 ≤ opM1 d s C := by
  have hI : 0 ≤ ∫ z : Torus d, ‖z‖ ^ (-s) := integral_nonneg fun z => Real.rpow_nonneg (norm_nonneg _) _
  have := hG.hC0
  unfold opM1; positivity

theorem opM2_nonneg (hG : GoodKernel d s C G) : 0 ≤ opM2 s C := by
  have := hG.hC0
  unfold opM2; positivity

/-- A uniform bound for the cancellation convolution of Lipschitz bounded functions. -/
theorem GoodKernel.bound_op (hG : GoodKernel d s C G) (h : Torus d → ℝ) (B L : ℝ)
    (hh : Measurable h) (hB : ∀ x, |h x| ≤ B) (hL : IsLipschitz L h) (hL0 : 0 ≤ L) (hB0 : 0 ≤ B)
    (x : Torus d) :
    ‖convGradConv G h x‖ ≤ L * opM1 d s C + B * opM2 s C := by
  rw [convGradConv_eq_integral_kern]
  refine (norm_integral_le_of_norm_le (integrable_dom hG L B)
    (kern_bound_ae hG hB hL hL0 hB0 x)).trans ?_
  rw [integral_dom hG]
  apply le_of_eq
  unfold opM1 opM2
  ring

theorem GoodKernel.continuous_op (hG : GoodKernel d s C G) {h : Torus d → ℝ} (hc : Continuous h)
    {B L : ℝ} (hB : ∀ x, |h x| ≤ B) (hL : IsLipschitz L h) (hL0 : 0 ≤ L) (hB0 : 0 ≤ B) :
    Continuous (convGradConv G h) := by
  have : convGradConv G h = fun x => ∫ z, kern G h x z := funext (convGradConv_eq_integral_kern G h)
  rw [this]
  refine continuous_of_dominated (bound := dom s C L B d)
    (fun x => (measurable_kern hG hc.measurable x).aestronglyMeasurable)
    (fun x => kern_bound_ae hG hB hL hL0 hB0 x) (integrable_dom hG L B)
    (Eventually.of_forall fun z => ?_)
  unfold kern
  split_ifs
  · fun_prop
  · fun_prop


/-! ### Functions of class `C¹` are bounded and Lipschitz -/

theorem norm_fderiv_le_of_isCk {h : Torus d → ℝ} (hh : Torus.IsCk 1 h) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ y : Euc d, ‖fderiv ℝ (Torus.lift h) y‖ ≤ L := by
  have h1 : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (Torus.lift h) := by exact_mod_cast hh
  obtain ⟨L, hL⟩ := Torus.bddAbove_norm_iteratedFDeriv_lift 1 h h1
  refine ⟨max L 0, le_max_right _ _, fun y => ?_⟩
  have := hL ⟨y, rfl⟩
  simp only at this
  have e : ‖iteratedFDeriv ℝ 1 (Torus.lift h) y‖ = ‖fderiv ℝ (Torus.lift h) y‖ := by
    rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero]
  rw [e] at this
  exact this.trans (le_max_left _ _)

theorem isCk_continuous {h : Torus d → ℝ} (hh : Torus.IsCk 1 h) : Continuous h :=
  continuous_of_lift (hh.continuous)

theorem isCk_bounded {h : Torus d → ℝ} (hh : Torus.IsCk 1 h) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |h x| ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn (isCk_continuous hh).continuousOn
  exact ⟨max B 0, le_max_right _ _, fun x => by
    have := hB x (mem_univ x)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)⟩

theorem isLipschitz_of_isCk {h : Torus d → ℝ} (hh : Torus.IsCk 1 h) :
    ∃ L : ℝ, 0 ≤ L ∧ IsLipschitz L h := by
  obtain ⟨L, hL0, hL⟩ := norm_fderiv_le_of_isCk hh
  have h1 : Differentiable ℝ (Torus.lift h) := hh.differentiable one_ne_zero
  refine ⟨L, hL0, fun x y => ?_⟩
  set r := centeredRep (x - y) with hr
  have hmk : Torus.mk (Torus.rep y + r) = x := by
    rw [mk_add, Torus.mk_rep, hr, mk_centeredRep]; abel
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := Torus.lift h) (fun u _ => h1 u)
    (fun u _ => hL u) convex_univ (mem_univ (Torus.rep y)) (mem_univ (Torus.rep y + r))
  have e1 : Torus.lift h (Torus.rep y + r) = h x := by simp [Torus.lift, hmk]
  have e2 : Torus.lift h (Torus.rep y) = h y := by simp [Torus.lift, Torus.mk_rep]
  rw [e1, e2, Real.norm_eq_abs] at this
  rw [add_sub_cancel_left] at this
  exact this


/-! ### Agreement with the plain integral for `s + 1 < d` -/

theorem GoodKernel.integrable_G (hG : GoodKernel d s C G) (hs1 : s + 1 < d) : Integrable G := by
  have hC := hG.bound_norm
  have h1 : Integrable (fun z : Torus d => ‖z‖ ^ (-(s + 1))) := integrable_norm_rpow_neg hG.pos hs1
  have h2 : Integrable (fun z : Torus d => C * (‖z‖ ^ (-(s + 1)) + 1)) :=
    (h1.add (integrable_const (1 : ℝ))).const_mul C
  refine h2.mono' hG.meas.aestronglyMeasurable ?_
  filter_upwards [torus_ae_ne' hG.pos] with z hz
  have := hC z hz
  rwa [show -s - 1 = -(s + 1) by ring] at this

theorem GoodKernel.integral_cube_eq_zero (hG : GoodKernel d s C G) :
    ∫ z : Torus d, (if ‖z‖ ≤ 1 / 4 then G z else 0) = 0 := by
  set Q : Torus d → Euc d := fun z => if ‖z‖ ≤ 1 / 4 then G z else 0 with hQ
  have hodd : ∀ z, Q (-z) = - Q z := by
    intro z
    simp only [hQ, norm_neg, hG.odd z]
    split_ifs <;> simp
  have h1 : ∫ z, Q (-z) = ∫ z, Q z := integral_neg_eq_self Q volume
  simp_rw [hodd] at h1
  rw [integral_neg] at h1
  have : ∫ z, Q z = 0 := by
    have h2 : (-(∫ z, Q z)) = ∫ z, Q z := h1
    have h3 : (2 : ℝ) • ∫ z, Q z = 0 := by rw [two_smul]; nth_rewrite 1 [← h2]; simp
    simpa using h3
  exact this

theorem GoodKernel.eq_plain_of_integrable (hG : GoodKernel d s C G) (hGi : Integrable G)
    {h : Torus d → ℝ} (hm : Measurable h) {B : ℝ} (hB : ∀ x, |h x| ≤ B) (x : Torus d) :
    convGradConv G h x = ∫ y, h y • G (x - y) := by
  rw [convGradConv_eq_integral_kern]
  have e1 : ∫ y, h y • G (x - y) = ∫ z, h (x - z) • G z := by
    rw [← integral_sub_left_eq_self (fun y => h y • G (x - y)) volume x]
    simp only [sub_sub_cancel]
  rw [e1]
  have hint : Integrable (fun z => h (x - z) • G z) := by
    refine Integrable.mono' (hGi.norm.const_mul B) ?_ (Eventually.of_forall fun z => ?_)
    · exact ((hm.comp (measurable_const.sub measurable_id)).smul hG.meas).aestronglyMeasurable
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
  have hQi : Integrable (fun z : Torus d => if ‖z‖ ≤ 1 / 4 then G z else 0) := by
    refine hGi.norm.mono' ?_ (Eventually.of_forall fun z => ?_)
    · exact (Measurable.ite (measurableSet_le measurable_norm measurable_const) hG.meas
        measurable_const).aestronglyMeasurable
    · split_ifs <;> simp
  have hpt : ∀ z, kern G h x z = h (x - z) • G z - h x • (if ‖z‖ ≤ 1 / 4 then G z else 0) := by
    intro z
    unfold kern
    split_ifs
    · simp [sub_smul]
    · simp
  have hQs : Integrable (fun z : Torus d => h x • (if ‖z‖ ≤ 1 / 4 then G z else 0)) := hQi.smul (h x)
  simp_rw [hpt]
  rw [integral_sub hint hQs, integral_smul, hG.integral_cube_eq_zero]
  simp

theorem GoodKernel.eq_plain (hG : GoodKernel d s C G) (hs1 : s + 1 < d) {h : Torus d → ℝ}
    (hm : Measurable h) {B : ℝ} (hB : ∀ x, |h x| ≤ B) (x : Torus d) :
    convGradConv G h x = ∫ y, h y • G (x - y) :=
  hG.eq_plain_of_integrable (hG.integrable_G hs1) hm hB x

end HRS.KernelGrad
