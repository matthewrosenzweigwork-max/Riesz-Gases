import HRS.MS.SuppU2Aux3

/-!
# U2 auxiliary 4: differentiation of `u2Conv κ h` with the derivatives on `h`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

set_option synthInstance.maxHeartbeats 400000

variable {d : ℕ}

section Diff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma u2_wt_L0 {L : ℝ} (hL : (d : ℝ) < L) : 0 ≤ L := by
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

lemma u2_conv_hasFDerivAt {κ : Euc d → ℝ} {a L : ℝ} (hker : U2Ker κ a) (hL : (d : ℝ) < L)
    {h : Euc d → E} (hh : ContDiff ℝ 1 h) {A A' : ℝ} (hA : 0 ≤ A) (hA' : 0 ≤ A')
    (h0 : ∀ y, ‖h y‖ ≤ A * u2Wt L y) (h1 : ∀ y, ‖fderiv ℝ h y‖ ≤ A' * u2Wt L y) (x0 : Euc d) :
    HasFDerivAt (u2Conv κ h) (u2Conv κ (fun y => fderiv ℝ h y) x0) x0 := by
  have hL0 := u2_wt_L0 hL
  have hcont : Continuous h := hh.continuous
  have hfc : Continuous (fderiv ℝ h) := hh.continuous_fderiv one_ne_zero
  have hdiff : Differentiable ℝ h := hh.differentiable one_ne_zero
  have hbi : Integrable (fun z => (A' * 2 ^ L) * (‖κ z‖ * u2Wt L (x0 - z))) volume :=
    (u2_wt_translate_int hker hL x0).const_mul _
  have hsub : Continuous fun z : Euc d => x0 - z := continuous_const.sub continuous_id
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
    (F := fun x z => κ z • h (x - z)) (F' := fun x z => κ z • fderiv ℝ h (x - z)) (x₀ := x0)
    (s := ball x0 1) (bound := fun z => (A' * 2 ^ L) * (‖κ z‖ * u2Wt L (x0 - z)))
    (ball_mem_nhds x0 one_pos) ?_ ?_ ?_ ?_ hbi ?_
  · refine Filter.Eventually.of_forall fun x => ?_
    exact hker.meas.aestronglyMeasurable.smul
      (hcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · exact u2_conv_integrable hker hL hcont hA h0 x0
  · exact hker.meas.aestronglyMeasurable.smul
      (hfc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun z x hx => ?_
    have hx1 : ‖x - x0‖ ≤ 1 := by
      have := mem_ball_iff_norm.mp hx
      exact this.le
    rw [norm_smul]
    have h2 := u2_peetre hL0 hx1 z
    calc ‖κ z‖ * ‖fderiv ℝ h (x - z)‖ ≤ ‖κ z‖ * (A' * u2Wt L (x - z)) :=
          mul_le_mul_of_nonneg_left (h1 _) (norm_nonneg _)
      _ ≤ ‖κ z‖ * (A' * (2 ^ L * u2Wt L (x0 - z))) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left h2 hA'
      _ = (A' * 2 ^ L) * (‖κ z‖ * u2Wt L (x0 - z)) := by ring
  · refine Filter.Eventually.of_forall fun z x _ => ?_
    have h1 : HasFDerivAt (fun x : Euc d => h (x - z)) (fderiv ℝ h (x - z)) x := by
      have h2 : HasFDerivAt (fun x : Euc d => x - z) (ContinuousLinearMap.id ℝ (Euc d)) x :=
        (hasFDerivAt_id x).sub_const z
      have := HasFDerivAt.comp x (hdiff (x - z)).hasFDerivAt h2
      rw [ContinuousLinearMap.comp_id] at this
      exact this
    exact h1.const_smul (κ z)

lemma u2_conv_continuous {κ : Euc d → ℝ} {a L : ℝ} (hker : U2Ker κ a) (hL : (d : ℝ) < L)
    {g : Euc d → E} (hg : Continuous g) {A : ℝ} (hA : 0 ≤ A)
    (hg0 : ∀ y, ‖g y‖ ≤ A * u2Wt L y) : Continuous (u2Conv κ g) := by
  have hL0 := u2_wt_L0 hL
  refine continuous_iff_continuousAt.2 fun x0 => ?_
  have hbi : Integrable (fun z => (A * 2 ^ L) * (‖κ z‖ * u2Wt L (x0 - z))) volume :=
    (u2_wt_translate_int hker hL x0).const_mul _
  refine MeasureTheory.continuousAt_of_dominated (μ := volume)
    (F := fun x z => κ z • g (x - z)) (bound := fun z => (A * 2 ^ L) * (‖κ z‖ * u2Wt L (x0 - z)))
    ?_ ?_ hbi ?_
  · refine Filter.Eventually.of_forall fun x => ?_
    exact hker.meas.aestronglyMeasurable.smul
      (hg.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · have : ∀ᶠ x in 𝓝 x0, ‖x - x0‖ ≤ 1 := by
      have : ball x0 1 ∈ 𝓝 x0 := ball_mem_nhds x0 one_pos
      filter_upwards [this] with x hx
      exact (mem_ball_iff_norm.mp hx).le
    filter_upwards [this] with x hx1
    refine Filter.Eventually.of_forall fun z => ?_
    rw [norm_smul]
    have h2 := u2_peetre hL0 hx1 z
    calc ‖κ z‖ * ‖g (x - z)‖ ≤ ‖κ z‖ * (A * u2Wt L (x - z)) :=
          mul_le_mul_of_nonneg_left (hg0 _) (norm_nonneg _)
      _ ≤ ‖κ z‖ * (A * (2 ^ L * u2Wt L (x0 - z))) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left h2 hA
      _ = (A * 2 ^ L) * (‖κ z‖ * u2Wt L (x0 - z)) := by ring
  · refine Filter.Eventually.of_forall fun z => ?_
    exact (continuous_const.smul (hg.comp (continuous_id.sub continuous_const))).continuousAt

lemma u2_conv_clm {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
    (φ : E →L[ℝ] E') (κ : Euc d → ℝ) (g : Euc d → E) (x : Euc d)
    (hint : Integrable (fun z => κ z • g (x - z)) volume) :
    φ (u2Conv κ g x) = u2Conv κ (fun y => φ (g y)) x := by
  unfold u2Conv
  rw [← ContinuousLinearMap.integral_comp_comm φ hint]
  simp [map_smul]

end Diff

/-- `h` is `C^k` with `‖D^m h(y)‖ ≤ A (1+‖y‖)^{-L}` for `m ≤ k`. -/
def U2Dec (k : ℕ) (L A : ℝ) (h : Euc d → ℝ) : Prop :=
  ContDiff ℝ k h ∧ ∀ m ≤ k, ∀ y, ‖iteratedFDeriv ℝ m h y‖ ≤ A * u2Wt L y

lemma u2_norm_fderiv_iteratedFDeriv (h : Euc d → ℝ) (m : ℕ) (y : Euc d) :
    ‖fderiv ℝ (iteratedFDeriv ℝ m h) y‖ = ‖iteratedFDeriv ℝ (m + 1) h y‖ := by
  rw [fderiv_iteratedFDeriv]
  simp only [Function.comp_apply]
  exact LinearIsometryEquiv.norm_map _ _

lemma u2_conv_hasFDerivAt_iter {κ : Euc d → ℝ} {a L : ℝ} (hker : U2Ker κ a) (hL : (d : ℝ) < L)
    {k : ℕ} {A : ℝ} (hA : 0 ≤ A) {h : Euc d → ℝ} (hdec : U2Dec k L A h) {m : ℕ} (hm : m + 1 ≤ k)
    (x : Euc d) :
    HasFDerivAt (u2Conv κ (iteratedFDeriv ℝ m h))
      (u2Conv κ (fun y => fderiv ℝ (iteratedFDeriv ℝ m h) y) x) x := by
  have hc : ContDiff ℝ 1 (iteratedFDeriv ℝ m h) := by
    have := hdec.1.iteratedFDeriv_right (m := 1) (i := m) (by
      have : ((1 : ℕ) + m : ℕ) ≤ k := by omega
      exact_mod_cast this)
    exact this
  refine u2_conv_hasFDerivAt hker hL hc hA hA (hdec.2 m (by omega)) (fun y => ?_) x
  rw [u2_norm_fderiv_iteratedFDeriv]
  exact hdec.2 (m + 1) hm y

theorem u2_conv_iter {κ : Euc d → ℝ} {a L : ℝ} (hker : U2Ker κ a) (hL : (d : ℝ) < L)
    {k : ℕ} {A : ℝ} (hA : 0 ≤ A) {h : Euc d → ℝ} (hdec : U2Dec k L A h) :
    (∀ m ≤ k, ∀ x, iteratedFDeriv ℝ m (u2Conv κ h) x = u2Conv κ (iteratedFDeriv ℝ m h) x) ∧
      ContDiff ℝ k (u2Conv κ h) := by
  have hcm : ∀ m ≤ k, Continuous (iteratedFDeriv ℝ m h) := fun m hm =>
    hdec.1.continuous_iteratedFDeriv (by exact_mod_cast hm)
  have hint : ∀ m ≤ k, ∀ x, Integrable (fun z => κ z • iteratedFDeriv ℝ m h (x - z)) volume :=
    fun m hm x => u2_conv_integrable hker hL (hcm m hm) hA (hdec.2 m hm) x
  have key : ∀ m ≤ k, ∀ x, iteratedFDeriv ℝ m (u2Conv κ h) x = u2Conv κ (iteratedFDeriv ℝ m h) x := by
    intro m
    induction m with
    | zero =>
      intro _ x
      have hint0 : Integrable (fun z => κ z • h (x - z)) volume :=
        u2_conv_integrable hker hL hdec.1.continuous hA
          (fun y => by simpa using hdec.2 0 (Nat.zero_le _) y) x
      have h0 := u2_conv_clm
        ((continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap)
        κ h x hint0
      rw [iteratedFDeriv_zero_eq_comp]
      exact h0
    | succ m ih =>
      intro hm x
      have hfun : iteratedFDeriv ℝ m (u2Conv κ h) = u2Conv κ (iteratedFDeriv ℝ m h) :=
        funext (ih (by omega))
      have hd := u2_conv_hasFDerivAt_iter hker hL hA hdec hm x
      have hc : ContDiff ℝ 1 (iteratedFDeriv ℝ m h) := by
        have := hdec.1.iteratedFDeriv_right (m := 1) (i := m) (by
          have : ((1 : ℕ) + m : ℕ) ≤ k := by omega
          exact_mod_cast this)
        exact this
      haveI : CompleteSpace (Euc d →L[ℝ] (Euc d [×m]→L[ℝ] ℝ)) := inferInstance
      have hint' :=
        u2_conv_integrable hker hL (hc.continuous_fderiv one_ne_zero) hA
          (fun y => by
            rw [u2_norm_fderiv_iteratedFDeriv]
            exact hdec.2 (m + 1) hm y) x
      have h1 := u2_conv_clm
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => Euc d) ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap)
        κ (fun y => fderiv ℝ (iteratedFDeriv ℝ m h) y) x hint'
      rw [iteratedFDeriv_succ_eq_comp_left (f := u2Conv κ h),
        iteratedFDeriv_succ_eq_comp_left (f := h)]
      simp only [Function.comp_apply]
      rw [hfun, hd.fderiv]
      exact h1
  refine ⟨key, ?_⟩
  rw [contDiff_nat_iff_continuous_differentiable]
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · have hm' : m ≤ k := by exact_mod_cast hm
    have : (fun x => iteratedFDeriv ℝ m (u2Conv κ h) x) = u2Conv κ (iteratedFDeriv ℝ m h) :=
      funext (key m hm')
    rw [this]
    exact u2_conv_continuous hker hL (hcm m hm') hA (hdec.2 m hm')
  · have hm' : m + 1 ≤ k := by exact_mod_cast hm
    have : (fun x => iteratedFDeriv ℝ m (u2Conv κ h) x) = u2Conv κ (iteratedFDeriv ℝ m h) :=
      funext (key m (by omega))
    rw [this]
    exact fun x => (u2_conv_hasFDerivAt_iter hker hL hA hdec hm' x).differentiableAt

end HRS.Whole
