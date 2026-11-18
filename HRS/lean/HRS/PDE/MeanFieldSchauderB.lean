import HRS.PDE.MeanFieldSchauder

/-!
# Differentiability of the convolution with a Hölder function (package MF-01, packet P4b)

Second half of the Schauder estimate: for `h ∈ C^{0,a}` and `a + (d - p) > 1`, `g ⋆ h ∈ C¹` with
gradient `∫ (h(x-z) - h(x)) ∇g(z) dz`, of class `C^{0,γ'}`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.PDE.MFSchauder

variable {d : ℕ} {g : Torus d → ℝ} {G : Torus d → Euc d} {p C : ℝ}

theorem KB.psi_aesm (K : KB d g G p C) {h : Torus d → ℝ} (hc : Continuous h) (x : Torus d)
    (w : Euc d) :
    AEStronglyMeasurable (fun z => (g (z + Torus.mk w) - g z - inner ℝ (G z) w) * (h (x - z) - h x))
      volume := by
  refine AEStronglyMeasurable.mul ?_ ?_
  · refine AEStronglyMeasurable.sub (AEStronglyMeasurable.sub ?_ ?_) ?_
    · exact (K.gint.comp_add_right (Torus.mk w)).aestronglyMeasurable
    · exact K.gint.aestronglyMeasurable
    · exact (K.Gmeas.inner measurable_const).aestronglyMeasurable
  · exact (((hc.comp (continuous_const.sub continuous_id)).sub continuous_const)).aestronglyMeasurable

/-- Pointwise differentiability of `g` as a limit statement. -/
theorem KB.g_tendsto (K : KB d g G p C) {z : Torus d} (hz : z ≠ 0) :
    Tendsto (fun w : Euc d => ‖w‖⁻¹ * |g (z + Torus.mk w) - g z - inner ℝ (G z) w|)
      (𝓝[≠] (0 : Euc d)) (𝓝 0) := by
  obtain ⟨xz, hxz, _⟩ := exists_lift z
  have hd := hasFDerivAt_iff_tendsto.1
    (hasGradientAt_iff_hasFDerivAt.1 (K.grad xz (by rw [hxz]; exact hz)))
  have hφ : Tendsto (fun w : Euc d => xz + w) (𝓝[≠] (0 : Euc d)) (𝓝 xz) := by
    have : Tendsto (fun w : Euc d => xz + w) (𝓝 (0 : Euc d)) (𝓝 (xz + 0)) :=
      (continuous_const.add continuous_id).tendsto 0
    rw [add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine (hd.comp hφ).congr (fun w => ?_)
  simp only [Function.comp, add_sub_cancel_left, InnerProductSpace.toDual_apply_apply,
    Real.norm_eq_abs, Torus.lift, Torus.mk_add, hxz]

theorem KB.psi_tendsto (K : KB d g G p C) {a M : ℝ} (ha : 0 ≤ a) (hθ : 1 < a + (d - p))
    (hM0 : 0 ≤ M) {h : Torus d → ℝ} (hc : Continuous h)
    (hM : ∀ x z, |h (x - z) - h x| ≤ M * ‖z‖ ^ a) (x : Torus d) :
    Tendsto (Psi g G h x) (𝓝[≠] (0 : Euc d)) (𝓝 0) := by
  have hC := K.C0
  set q₁ : ℝ := p + 1 - a with hq₁
  have hq₁d : q₁ < d := by rw [hq₁]; linarith
  have hI : Integrable (fun z : Torus d => ‖z‖ ^ (-q₁)) := KernelGrad.integrable_norm_rpow_neg K.hd hq₁d
  set c : ℝ := d * C * 2 ^ (p + 1) with hc'
  have hc0 : 0 ≤ c := by positivity
  unfold Psi
  have key := tendsto_integral_filter_of_dominated_convergence (μ := (volume : Measure (Torus d)))
    (l := 𝓝[≠] (0 : Euc d))
    (F := fun (w : Euc d) (z : Torus d) => ‖w‖⁻¹ * Set.indicator {z : Torus d | 2 * ‖Torus.mk w‖ < ‖z‖}
        (fun z => |(g (z + Torus.mk w) - g z - inner ℝ (G z) w) * (h (x - z) - h x)|) z)
    (f := fun _ => (0 : ℝ)) (fun z => (c + C) * M * ‖z‖ ^ (-q₁)) ?_ ?_ ?_ ?_
  · simpa using key
  · refine Filter.Eventually.of_forall fun w => ?_
    refine AEStronglyMeasurable.const_mul ?_ _
    refine AEStronglyMeasurable.indicator ?_ (measurableSet_lt measurable_const measurable_norm)
    exact (K.psi_aesm hc x w).norm
  · -- domination
    have hev1 : ∀ᶠ w in 𝓝[≠] (0 : Euc d), w ≠ 0 := self_mem_nhdsWithin
    have hev2 : ∀ᶠ w in 𝓝[≠] (0 : Euc d), ‖w‖ < 1 / 2 :=
      eventually_nhdsWithin_of_eventually_nhds (by
        have := Metric.ball_mem_nhds (0 : Euc d) (by norm_num : (0 : ℝ) < 1 / 2)
        filter_upwards [this] with w hw
        simpa using hw)
    filter_upwards [hev1, hev2] with w hw0 hw
    refine Filter.Eventually.of_forall fun z => ?_
    have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw0
    have hbd0 : 0 ≤ (c + C) * M * ‖z‖ ^ (-q₁) := by positivity
    set y : Torus d := Torus.mk w with hydef
    have hrw : ‖y‖ ≤ ‖w‖ := norm_mk_le_norm w
    by_cases hz : 2 * ‖y‖ < ‖z‖
    · rw [Set.indicator_of_mem (by simpa using hz)]
      have hzn : 0 < ‖z‖ := by
        have : 0 ≤ ‖y‖ := norm_nonneg _
        linarith
      have hz0 : z ≠ 0 := norm_pos_iff.1 hzn
      have hdiff := K.diff_bound hz
      have hG : |inner ℝ (G z) w| ≤ C * ‖z‖ ^ (-p - 1) * ‖w‖ :=
        (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (K.Gb z hz0) (norm_nonneg _))
      have hΔ := hM x z
      have e : ‖z‖ ^ (-q₁) = ‖z‖ ^ (-p - 1) * ‖z‖ ^ a := by
        rw [← rpow_split hzn]; congr 1; rw [hq₁]; ring
      have hr0 : 0 ≤ ‖z‖ ^ (-p - 1) := Real.rpow_nonneg hzn.le _
      have h1 : |g (z + y) - g z - inner ℝ (G z) w| ≤ (c + C) * ‖w‖ * ‖z‖ ^ (-p - 1) := by
        calc _ ≤ |g (z + y) - g z| + |inner ℝ (G z) w| := abs_sub _ _
          _ ≤ c * ‖y‖ * ‖z‖ ^ (-p - 1) + C * ‖z‖ ^ (-p - 1) * ‖w‖ := add_le_add hdiff hG
          _ ≤ c * ‖w‖ * ‖z‖ ^ (-p - 1) + C * ‖z‖ ^ (-p - 1) * ‖w‖ := by gcongr
          _ = _ := by ring
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_mul]
      calc ‖w‖⁻¹ * (|g (z + y) - g z - inner ℝ (G z) w| * |h (x - z) - h x|)
          ≤ ‖w‖⁻¹ * (((c + C) * ‖w‖ * ‖z‖ ^ (-p - 1)) * (M * ‖z‖ ^ a)) := by
            gcongr
        _ = (c + C) * M * (‖z‖ ^ (-p - 1) * ‖z‖ ^ a) := by
            field_simp
        _ = _ := by rw [← e]
    · rw [Set.indicator_of_notMem (by simpa using hz)]
      simpa using hbd0
  · exact (hI.const_mul _)
  · -- pointwise limit
    filter_upwards [KernelGrad.torus_ae_ne' K.hd] with z hz
    have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hev : ∀ᶠ w in 𝓝[≠] (0 : Euc d), ‖w‖ < ‖z‖ / 2 :=
      eventually_nhdsWithin_of_eventually_nhds (by
        have := Metric.ball_mem_nhds (0 : Euc d) (by positivity : (0 : ℝ) < ‖z‖ / 2)
        filter_upwards [this] with w hw
        simpa using hw)
    have hev1 : ∀ᶠ w in 𝓝[≠] (0 : Euc d), w ≠ 0 := self_mem_nhdsWithin
    have hlim := (K.g_tendsto hz).mul_const (|h (x - z) - h x|)
    rw [zero_mul] at hlim
    refine hlim.congr' ?_
    filter_upwards [hev, hev1] with w hw hw0
    have hrw : ‖Torus.mk w‖ ≤ ‖w‖ := norm_mk_le_norm w
    rw [Set.indicator_of_mem (by simp only [Set.mem_setOf_eq]; linarith), abs_mul]
    ring


theorem KB.hasFDerivAt_conv (K : KB d g G p C) {a M : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hθ : 1 < a + (d - p)) (hM0 : 0 ≤ M) {h : Torus d → ℝ} (hc : Continuous h)
    (hM : ∀ x z, |h (x - z) - h x| ≤ M * ‖z‖ ^ a) (v : Euc d) :
    HasFDerivAt (Torus.lift (convFun g h))
      (InnerProductSpace.toDual ℝ (Euc d) (Wgrad G h (Torus.mk v))) v := by
  set x : Torus d := Torus.mk v with hx
  set γ : ℝ := (1 + (a + (d - p))) / 2 with hγ
  set γ₃ : ℝ := (a + (d - p) - 1) / 2 with hγ₃
  have hγ1 : 1 < γ := by rw [hγ]; linarith
  have hγθ : γ < a + (d - p) := by rw [hγ]; linarith
  have hγ₃0 : 0 < γ₃ := by rw [hγ₃]; linarith
  have hγ₃θ : γ₃ < a + (d - p) - 1 := by rw [hγ₃]; linarith
  set q : ℝ := p + γ - a with hq
  set q₃ : ℝ := p + 1 - a + γ₃ with hq₃
  set Γ : ℝ := C * M * 3 ^ γ + d * C * 2 ^ (p + 1) * M with hΓ
  set A₁ : ℝ := 2 * Γ * (∫ z : Torus d, ‖z‖ ^ (-q)) with hA₁
  set A₂ : ℝ := C * M * (∫ z : Torus d, ‖z‖ ^ (-q₃)) with hA₂
  set Φ : Euc d → ℝ := fun w => A₁ * ‖w‖ ^ (γ - 1) + A₂ * (2 * ‖w‖) ^ γ₃ with hΦ
  have hΦ0 : Tendsto Φ (𝓝 (0 : Euc d)) (𝓝 0) := by
    have c1 : Continuous fun w : Euc d => ‖w‖ ^ (γ - 1) :=
      continuous_norm.rpow_const fun _ => Or.inr (by linarith)
    have c2 : Continuous fun w : Euc d => (2 * ‖w‖) ^ γ₃ :=
      (continuous_const.mul continuous_norm).rpow_const fun _ => Or.inr hγ₃0.le
    have hcont : Continuous Φ := (continuous_const.mul c1).add (continuous_const.mul c2)
    have := hcont.tendsto 0
    have e : Φ 0 = 0 := by
      simp only [hΦ, norm_zero, mul_zero]
      rw [Real.zero_rpow (by linarith), Real.zero_rpow hγ₃0.ne']
      ring
    rwa [e] at this
  have hΨ := K.psi_tendsto ha hθ hM0 hc hM x
  have hsum : Tendsto (fun w => Φ w + Psi g G h x w) (𝓝[≠] (0 : Euc d)) (𝓝 0) := by
    simpa using (hΦ0.mono_left nhdsWithin_le_nhds).add hΨ
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  have hev := (tendsto_order.1 hsum).2 ε hε
  have hev1 : ∀ᶠ w in 𝓝[≠] (0 : Euc d), ‖w‖ < 1 / 2 :=
    eventually_nhdsWithin_of_eventually_nhds (by
      have := Metric.ball_mem_nhds (0 : Euc d) (by norm_num : (0 : ℝ) < 1 / 2)
      filter_upwards [this] with w hw
      simpa using hw)
  have hev2 : ∀ᶠ w in 𝓝[≠] (0 : Euc d), w ≠ 0 := self_mem_nhdsWithin
  have hfin : ∀ᶠ w in 𝓝[≠] (0 : Euc d),
      ‖Torus.lift (convFun g h) (v + w) - Torus.lift (convFun g h) v -
        InnerProductSpace.toDual ℝ (Euc d) (Wgrad G h x) w‖ ≤ ε * ‖w‖ := by
    filter_upwards [hev, hev1, hev2] with w hw hw1 hw0
    have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw0
    have hR := K.remainder_bound ha (by linarith) hγ1.le hγθ hγ₃0.le hγ₃θ hθ hM0 hc hM x hw0 hw1
    have e : Torus.lift (convFun g h) (v + w) - Torus.lift (convFun g h) v -
        InnerProductSpace.toDual ℝ (Euc d) (Wgrad G h x) w =
        convFun g h (x + Torus.mk w) - convFun g h x - inner ℝ (Wgrad G h x) w := by
      simp [Torus.lift, Torus.mk_add, hx]
    rw [e, Real.norm_eq_abs]
    calc _ ≤ ‖w‖ * (Φ w + Psi g G h x w) := hR
      _ ≤ ‖w‖ * ε := mul_le_mul_of_nonneg_left hw.le hwn.le
      _ = ε * ‖w‖ := mul_comm _ _
  rw [eventually_nhdsWithin_iff] at hfin
  filter_upwards [hfin] with w hw
  by_cases hw0 : w = 0
  · subst hw0
    simp
  · exact hw hw0


theorem continuous_of_holder_bound {E : Type*} [NormedAddCommGroup E] {f : Torus d → E} {C' γ' : ℝ}
    (hγ' : 0 < γ') (hb : ∀ x y, ‖f (x + y) - f x‖ ≤ C' * ‖y‖ ^ γ') : Continuous f := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hg : Tendsto (fun t : Torus d => C' * ‖t - x‖ ^ γ') (𝓝 x) (𝓝 0) := by
    have hcont : Continuous fun t : Torus d => C' * ‖t - x‖ ^ γ' :=
      continuous_const.mul ((continuous_norm.comp (continuous_id.sub continuous_const)).rpow_const
        fun _ => Or.inr hγ'.le)
    have := hcont.tendsto x
    simpa [Real.zero_rpow hγ'.ne'] using this
  refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) hg
  have := hb x (t - x)
  rwa [add_sub_cancel] at this

theorem KB.cross (K : KB d g G p C) {a M γ' : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hθ : 1 < a + (d - p)) (hγ'0 : 0 < γ') (hγ'a : γ' ≤ a) (hγ'θ : γ' < a + (d - p) - 1)
    (hM0 : 0 ≤ M) {h : Torus d → ℝ} (hc : Continuous h)
    (hM : ∀ x z, |h (x - z) - h x| ≤ M * ‖z‖ ^ a) :
    Torus.IsCk 1 (convFun g h) ∧
      ∀ j : Fin d, MFHolder.Hol0 γ' (Torus.partialDeriv j (convFun g h)) := by
  have hW : ∀ x y, ‖Wgrad G h (x + y) - Wgrad G h x‖ ≤
      (2 * C * M * ∫ z : Torus d, ‖z‖ ^ (-(p + 1 - a + γ'))) * ‖y‖ ^ γ' :=
    fun x y => K.W_holder ha0 hθ hγ'0.le hγ'a hγ'θ hc hM hM0 x y
  have hWc : Continuous (Wgrad G h) := continuous_of_holder_bound hγ'0 hW
  have hd : ∀ v : Euc d, HasFDerivAt (Torus.lift (convFun g h))
      (InnerProductSpace.toDual ℝ (Euc d) (Wgrad G h (Torus.mk v))) v :=
    fun v => K.hasFDerivAt_conv ha0 ha1 hθ hM0 hc hM v
  have hC1 : Torus.IsCk 1 (convFun g h) := by
    unfold Torus.IsCk
    rw [contDiff_one_iff_fderiv]
    refine ⟨fun v => (hd v).differentiableAt, ?_⟩
    have : fderiv ℝ (Torus.lift (convFun g h)) =
        fun v => InnerProductSpace.toDual ℝ (Euc d) (Wgrad G h (Torus.mk v)) :=
      funext fun v => (hd v).fderiv
    rw [this]
    exact (InnerProductSpace.toDual ℝ (Euc d)).continuous.comp (hWc.comp Torus.continuous_mk)
  refine ⟨hC1, fun j => ?_⟩
  have hpd : Torus.partialDeriv j (convFun g h) = fun x => Wgrad G h x j := by
    funext x
    have e0 : Torus.partialDeriv j (convFun g h) x =
        fderiv ℝ (Torus.lift (convFun g h)) (Torus.rep x) (EuclideanSpace.single j 1) := rfl
    rw [e0, (hd (Torus.rep x)).fderiv, Torus.mk_rep, InnerProductSpace.toDual_apply_apply,
      EuclideanSpace.inner_single_right]
    simp
  rw [hpd]
  have hcj : Continuous fun x => Wgrad G h x j :=
    (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous.comp hWc
  refine ⟨hcj, 2 * C * M * ∫ z : Torus d, ‖z‖ ^ (-(p + 1 - a + γ')), fun x y => ?_⟩
  have h1 := hW y (x - y)
  rw [add_sub_cancel] at h1
  calc |Wgrad G h x j - Wgrad G h y j| = ‖(Wgrad G h x - Wgrad G h y) j‖ := by simp
    _ ≤ ‖Wgrad G h x - Wgrad G h y‖ := PiLp.norm_apply_le _ j
    _ ≤ _ := h1


theorem KB.cross_HC (K : KB d g G p C) : ∀ (m : ℕ) {a γ' : ℝ} {h : Torus d → ℝ}, 0 ≤ a → a ≤ 1 →
    1 < a + (d - p) → 0 < γ' → γ' ≤ a → γ' < a + (d - p) - 1 → MFHolder.HC m a h →
    MFHolder.HC (m + 1) γ' (convFun g h)
  | 0, _, _, _, ha0, ha1, hθ, hγ'0, hγ'a, hγ'θ, H => by
    obtain ⟨M, hM0, hM⟩ := Hol0.increment H
    exact K.cross ha0 ha1 hθ hγ'0 hγ'a hγ'θ hM0 H.1 hM
  | m + 1, _, _, h, ha0, ha1, hθ, hγ'0, hγ'a, hγ'θ, H => by
    refine ⟨convFun_isCk_one K.gint H.1, fun j => ?_⟩
    have e : Torus.partialDeriv j (convFun g h) = convFun g (Torus.partialDeriv j h) :=
      funext fun x => convFun_partialDeriv K.gint H.1 j x
    rw [e]
    exact K.cross_HC m ha0 ha1 hθ hγ'0 hγ'a hγ'θ (H.2 j)

end HRS.PDE.MFSchauder
