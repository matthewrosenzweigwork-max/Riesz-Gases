import HRS.MS.FlowCAux1

/-!
# MS-FLOW-C, derivative bounds for a `C^{m+1}` parametrisation `Ξ` with `G ∘ Ξ = const`

`Ξ : E → ℝ →ᵇ E`, `Gmap S b (Ξ x) = constCLM E x`.  Then `‖DΞ‖ ≤ e^{ΛS}` and, for `2 ≤ j ≤ m+1`,
`‖D^jΞ(x0)‖ ≤ e^{ΛS} * card * (ΛS) * K^j` if the lower derivatives at `x0` are bounded by `K ≥ 1`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped BoundedContinuousFunction

namespace HRS.MS.FlowC

open HRS.MS.FlowB

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

theorem fc_V_bound {S : ℝ} (hS : 0 ≤ S) {m : ℕ} {Λ : ℝ} {b : ℝ → E → E} (hb : DB S m Λ b)
    (α : ℝ →ᵇ E) (γ : ℝ →ᵇ E) (t : ℝ) :
    ‖continuousMultilinearCurryFin1 ℝ (ℝ →ᵇ E) (ℝ →ᵇ E) (tay S b α 1) γ t‖ ≤
      ∫ s in (0 : ℝ)..clampT S t, Λ * ‖γ s‖ := by
  have hct := clampT_nonneg S t
  have hB : HasB (fun s => iteratedFDeriv ℝ 1 (bt S b s) (α s)) :=
    (hb.good hS (by omega)).hasB α
  have hint0 := (hB.goodInt (fun _ => γ)).integrable 0 (clampT S t)
  have hint : IntervalIntegrable (fun s => fderiv ℝ (b (clampT S s)) (α s) (γ s)) volume 0
      (clampT S t) := by
    have e : (fun s => fderiv ℝ (b (clampT S s)) (α s) (γ s)) =
        intg 1 (fun s => iteratedFDeriv ℝ 1 (bt S b s) (α s)) (fun _ => γ) := by
      funext s; simp [intg, iteratedFDeriv_one_apply, bt]
    rw [e]; exact hint0
  rw [dnem_apply hS hb]
  refine (intervalIntegral.norm_integral_le_integral_norm hct).trans ?_
  refine intervalIntegral.integral_mono_on hct hint.norm ?_ fun s _ => ?_
  · exact ((γ.continuous.norm.const_mul Λ)).intervalIntegrable _ _
  · refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]
    exact hb.deriv_bound _ (clampT_mem hS s) 1 le_rfl (by omega) _

theorem fc_tay_norm {S : ℝ} (hS : 0 ≤ S) {m : ℕ} {Λ : ℝ} {b : ℝ → E → E} (hb : DB S m Λ b)
    (α : ℝ →ᵇ E) {k : ℕ} (hk1 : 1 ≤ k) (hkm : k ≤ m + 1) : ‖tay S b α k‖ ≤ Λ * S := by
  have hB : HasB (fun s => iteratedFDeriv ℝ k (bt S b s) (α s)) := (hb.good hS hkm).hasB α
  unfold tay
  refine (norm_Vop_le hS hB).trans ?_
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := S) (C := Λ)
    (f := fun s => ‖iteratedFDeriv ℝ k (bt S b s) (α s)‖) (fun s _ => by
      rw [norm_norm]
      exact hb.deriv_bound _ (clampT_mem hS s) k hk1 hkm _)
  calc _ ≤ ‖∫ s in (0 : ℝ)..S, ‖iteratedFDeriv ℝ k (bt S b s) (α s)‖‖ := Real.le_norm_self _
    _ ≤ Λ * |S - 0| := h
    _ = Λ * S := by rw [sub_zero, abs_of_nonneg hS]

/-- A global `C^{m+1}` parametrisation of the flow. -/
theorem fc_exists_param {T : ℝ} (hT : 0 ≤ T) {m : ℕ} {Λ : ℝ} {b : ℝ → E → E} (hb : DB T m Λ b)
    {Ψ : ℝ → E → E} (h0 : ∀ x, Ψ 0 x = x) (hs : ∀ x, FlowA.Sol T b (fun τ => Ψ τ x)) :
    ∃ Ξ : E → (ℝ →ᵇ E), ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) Ξ ∧
      (∀ x, Gmap T b (Ξ x) = constCLM E x) ∧ ∀ x, ∀ t ∈ Icc (0 : ℝ) T, Ξ x t = Ψ t x := by
  have hpath : ∀ x, ∃ A : ℝ →ᵇ E, ∀ t, A t = Ψ (clampT T t) x := by
    intro x
    have hc : Continuous fun t => Ψ (clampT T t) x :=
      (hs x).continuousOn.comp_continuous (continuous_clampT T) (fun t => clampT_mem hT t)
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hs x).continuousOn
    exact ⟨BoundedContinuousFunction.ofNormedAddCommGroup _ hc C
      (fun t => hC _ (clampT_mem hT t)), fun t => rfl⟩
  choose Ξ hΞ using hpath
  have hGΞ : ∀ x, Gmap T b (Ξ x) = constCLM E x := fun x => Gpath hT hb h0 hs x (Ξ x) (hΞ x)
  refine ⟨Ξ, ?_, hGΞ, fun x t ht => by rw [hΞ, clampT_of_mem ht]⟩
  refine contDiff_iff_contDiffAt.2 fun x0 => ?_
  obtain ⟨A, hA, hAG, hAΨ⟩ := exists_local_param hT hb h0 hs x0
  refine hA.congr_of_eventuallyEq ?_
  filter_upwards [hAG, hAΨ] with x hxG hxΨ
  ext t
  have e1 : ∀ s, A x s + nem T b (A x) s = x := fun s => by
    have := congrArg (fun F : ℝ →ᵇ E => F s) hxG
    simpa [Gmap, constCLM_apply] using this
  have e2 : A x t = A x (clampT T t) := by
    have h1 := e1 t
    have h2 := e1 (clampT T t)
    rw [nem_apply hT hb, ] at h1 h2
    rw [clampT_of_mem (clampT_mem hT t)] at h2
    have := h1.trans h2.symm
    exact add_right_cancel this
  rw [hΞ x t, e2, hxΨ _ (clampT_mem hT t)]

section Step

variable {S : ℝ} {m : ℕ} {Λ : ℝ} {b : ℝ → E → E} {Ξ : E → (ℝ →ᵇ E)}

theorem fc_base (hS : 0 ≤ S) (hb : DB S m Λ b)
    (hΞ : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) Ξ) (hG : ∀ x, Gmap S b (Ξ x) = constCLM E x)
    (x0 : E) : ‖fderiv ℝ Ξ x0‖ ≤ Real.exp (Λ * S) := by
  have hΛ := hb.Λ_nonneg hS
  have hn1 : ((m + 1 : ℕ) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hd : HasFDerivAt Ξ (fderiv ℝ Ξ x0) x0 := ((hΞ.differentiable hn1) x0).hasFDerivAt
  have hcomp := (hasFDerivAt_Gmap hS hb (Ξ x0)).comp x0 hd
  have hconst : HasFDerivAt (fun x => Gmap S b (Ξ x)) (constCLM E) x0 :=
    (constCLM E).hasFDerivAt.congr_of_eventuallyEq (Eventually.of_forall fun x => hG x)
  have huniq := hcomp.unique hconst
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hv := congrArg (fun L : E →L[ℝ] (ℝ →ᵇ E) => L v) huniq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.one_apply] at hv
  have := sup_gronwall hS hΛ
    (continuousMultilinearCurryFin1 ℝ (ℝ →ᵇ E) (ℝ →ᵇ E) (tay S b (Ξ x0) 1))
    (fc_V_bound hS hb (Ξ x0)) (fderiv ℝ Ξ x0 v) (constCLM E v) hv
  have hc : ‖constCLM E v‖ = ‖v‖ := BoundedContinuousFunction.norm_const_eq v
  rw [hc] at this
  exact this

theorem fc_ccl_zero {j : ℕ} (hj : 2 ≤ j) (x0 : E) :
    iteratedFDeriv ℝ j (⇑(constCLM E)) x0 = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  ext v
  rw [iteratedFDeriv_succ_apply_right]
  have : (fun y => fderiv ℝ (⇑(constCLM E)) y) = fun _ => constCLM E := funext fun y =>
    (constCLM E).fderiv
  rw [this, iteratedFDeriv_succ_const]
  simp

theorem fc_step (hS : 0 ≤ S) (hb : DB S m Λ b)
    (hΞ : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) Ξ) (hG : ∀ x, Gmap S b (Ξ x) = constCLM E x)
    {j : ℕ} (hj2 : 2 ≤ j) (hjm : j ≤ m + 1) (x0 : E) {K : ℝ} (hK : 1 ≤ K)
    (hlow : ∀ i, 1 ≤ i → i < j → ‖iteratedFDeriv ℝ i Ξ x0‖ ≤ K) :
    ‖iteratedFDeriv ℝ j Ξ x0‖ ≤
      Real.exp (Λ * S) * (Fintype.card (OrderedFinpartition j) * (Λ * S) * K ^ j) := by
  have hΛ := hb.Λ_nonneg hS
  set n : WithTop ℕ∞ := ((m + 1 : ℕ) : WithTop ℕ∞) with hn_def
  have hnem : HasFTaylorSeriesUpTo n (nem S b) (tay S b) := by
    have := hasFTaylor hS hb
    exact_mod_cast this
  have hjn : (j : WithTop ℕ∞) ≤ n := by rw [hn_def]; exact_mod_cast hjm
  have hcomp : HasFTaylorSeriesUpTo n (nem S b ∘ Ξ)
      (fun x => (tay S b (Ξ x)).taylorComp (ftaylorSeries ℝ Ξ x)) :=
    hasFTaylorSeriesUpToOn_univ_iff.1
      (HasFTaylorSeriesUpToOn.comp (hasFTaylorSeriesUpToOn_univ_iff.2 hnem)
        (hasFTaylorSeriesUpToOn_univ_iff.2 hΞ.ftaylorSeries) (mapsTo_univ _ _))
  have hD := hcomp.eq_iteratedFDeriv hjn x0
  have hident : (fun x => Ξ x + nem S b (Ξ x)) = ⇑(constCLM E) := funext fun x => hG x
  have hΞj : ContDiffAt ℝ (j : ℕ) Ξ x0 := (hΞ.of_le hjn).contDiffAt
  have hNj : ContDiffAt ℝ (j : ℕ) (nem S b ∘ Ξ) x0 :=
    (((contDiff_nem hS hb).comp hΞ).of_le hjn).contDiffAt
  have hdiff : iteratedFDeriv ℝ j (fun x => Ξ x + nem S b (Ξ x)) x0 =
      iteratedFDeriv ℝ j Ξ x0 + iteratedFDeriv ℝ j (nem S b ∘ Ξ) x0 :=
    iteratedFDeriv_add_apply hΞj hNj
  rw [hident, fc_ccl_zero hj2] at hdiff
  have hsum : iteratedFDeriv ℝ j Ξ x0 +
      (tay S b (Ξ x0)).taylorComp (ftaylorSeries ℝ Ξ x0) j = 0 := by
    rw [hD, ← hdiff]
  obtain ⟨R, hR, hRb⟩ := fc_fdb_split (n := j) (by omega) (tay S b (Ξ x0))
    (ftaylorSeries ℝ Ξ x0)
  have hRn := hRb (Λ * S) K hK (fun k hk1 hkj => fc_tay_norm hS hb (Ξ x0) hk1 (hkj.trans hjm))
    (fun k hk1 hkj => hlow k hk1 hkj)
  set M : ℝ := Real.exp (Λ * S) * (Fintype.card (OrderedFinpartition j) * (Λ * S) * K ^ j)
    with hM
  have hM0 : 0 ≤ M := by positivity
  refine ContinuousMultilinearMap.opNorm_le_bound hM0 fun v => ?_
  have hv := congrArg (fun M : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) (ℝ →ᵇ E) => M v) hsum
  rw [hR] at hv
  simp only [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.zero_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply] at hv
  set η := iteratedFDeriv ℝ j Ξ x0 v with hη
  have h2 : η + continuousMultilinearCurryFin1 ℝ (ℝ →ᵇ E) (ℝ →ᵇ E) (tay S b (Ξ x0) 1) η =
      -(R v) := by
    have : η + (continuousMultilinearCurryFin1 ℝ (ℝ →ᵇ E) (ℝ →ᵇ E) (tay S b (Ξ x0) 1) η + R v) = 0 :=
      hv
    rw [← add_assoc] at this
    exact eq_neg_of_add_eq_zero_left this
  have h3 := sup_gronwall hS hΛ
    (continuousMultilinearCurryFin1 ℝ (ℝ →ᵇ E) (ℝ →ᵇ E) (tay S b (Ξ x0) 1))
    (fc_V_bound hS hb (Ξ x0)) η (-(R v)) h2
  rw [norm_neg] at h3
  refine h3.trans ?_
  calc Real.exp (Λ * S) * ‖R v‖ ≤ Real.exp (Λ * S) * (‖R‖ * ∏ i, ‖v i‖) :=
        mul_le_mul_of_nonneg_left (R.le_opNorm v) (Real.exp_pos _).le
    _ ≤ Real.exp (Λ * S) * ((Fintype.card (OrderedFinpartition j) * (Λ * S) * K ^ j) *
          ∏ i, ‖v i‖) := by
        gcongr
    _ = M * ∏ i, ‖v i‖ := by rw [hM]; ring

end Step

end HRS.MS.FlowC
