import HRS.MS.FlowBAux4
import HRS.MS.FlowBAux5
import HRS.MS.FlowAAux1
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# MS-FLOW-B, `C^{m+1}` regularity of the flow via the inverse function theorem

`G(α) = α + 𝒩(α)` is `C^{m+1}` on `X = ℝ →ᵇ E`, `DG(α0) = 1 + V` is invertible (Volterra), and
`G α = const x` iff `α` solves the ODE with initial value `x`; so `Ψ_τ(x) = α_x(τ)` is the evaluation at `τ`
of the local inverse of `G` at `const x`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped BoundedContinuousFunction

namespace HRS.MS.FlowB

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

theorem DB.hyp {T : ℝ} (hT : 0 ≤ T) {m : ℕ} {Λ : ℝ} {b : ℝ → E → E} (hb : DB T m Λ b) :
    FlowA.Hyp T Λ b where
  Λ_nonneg := hb.Λ_nonneg hT
  cont := hb.cont
  lip τ hτ x y := by
    have hd : Differentiable ℝ (b τ) :=
      (hb.smooth τ hτ).differentiable (by exact_mod_cast Nat.succ_ne_zero m)
    have := (convex_univ (𝕜 := ℝ) (E := E)).norm_image_sub_le_of_norm_fderiv_le
      (f := b τ) (C := Λ) (fun x _ => hd x)
      (fun x _ => by
        rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]
        exact hb.deriv_bound τ hτ 1 le_rfl (by omega) x) (mem_univ y) (mem_univ x)
    exact this
  growth := hb.growth

/-- Constants as bounded continuous functions. -/
noncomputable def constCLM (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    E →L[ℝ] (ℝ →ᵇ E) :=
  LinearMap.mkContinuous
    { toFun := fun x => BoundedContinuousFunction.const ℝ x
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl } 1 (fun x => by
        show ‖BoundedContinuousFunction.const ℝ x‖ ≤ 1 * ‖x‖
        rw [BoundedContinuousFunction.norm_const_eq, one_mul])

theorem constCLM_apply (x : E) (t : ℝ) : constCLM E x t = x := rfl

/-- FTC for a solution. -/
theorem sol_integral {T : ℝ} {b : ℝ → E → E} {f : ℝ → E} (hf : FlowA.Sol T b f)
    (hbc : ContinuousOn (fun p : ℝ × E => b p.1 p.2) (Icc (0 : ℝ) T ×ˢ univ)) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) T) : ∫ s in (0 : ℝ)..τ, b s (f s) = f 0 - f τ := by
  have hsub : Icc (0 : ℝ) τ ⊆ Icc (0 : ℝ) T := Icc_subset_Icc_right hτ.2
  have hcf : ContinuousOn (fun s => b s (f s)) (Icc (0 : ℝ) T) := by
    have := hbc.comp (f := fun s : ℝ => (s, f s)) (s := Icc (0 : ℝ) T)
      (t := Icc (0 : ℝ) T ×ˢ univ)
      (continuousOn_id.prodMk hf.continuousOn) (fun s hs => ⟨hs, trivial⟩)
    exact this
  have h1 : ∫ s in (0 : ℝ)..τ, -(b s (f s)) = f τ - f 0 := by
    refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hτ.1
      (hf.continuousOn.mono hsub) (fun s hs => ?_) ?_
    · have h := hf s ⟨hs.1.le, hs.2.le.trans hτ.2⟩
      have hnhds : Icc (0 : ℝ) T ∈ 𝓝 s := Icc_mem_nhds hs.1 (lt_of_lt_of_le hs.2 hτ.2)
      exact (h.hasDerivAt hnhds).hasDerivWithinAt
    · exact ((hcf.mono hsub).neg).intervalIntegrable_of_Icc hτ.1
  rw [intervalIntegral.integral_neg] at h1
  rw [neg_eq_iff_eq_neg.1 h1]
  abel

/-- The solution map `G`. -/
noncomputable def Gmap (T : ℝ) (b : ℝ → E → E) (α : ℝ →ᵇ E) : ℝ →ᵇ E := α + nem T b α

theorem Gpath {T : ℝ} (hT : 0 ≤ T) {m : ℕ} {Λ : ℝ} {b : ℝ → E → E} (hb : DB T m Λ b)
    {Ψ : ℝ → E → E} (h0 : ∀ x, Ψ 0 x = x) (hs : ∀ x, FlowA.Sol T b (fun τ => Ψ τ x))
    (x : E) (A : ℝ →ᵇ E) (hA : ∀ t, A t = Ψ (clampT T t) x) :
    Gmap T b A = constCLM E x := by
  ext t
  have hct := clampT_nonneg T t
  have hmem := clampT_mem hT t
  show A t + nem T b A t = x
  rw [nem_apply hT hb, hA]
  have : ∫ s in (0 : ℝ)..clampT T t, b (clampT T s) (A s) =
      ∫ s in (0 : ℝ)..clampT T t, b s (Ψ s x) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hct] at hs
    have hs' : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans hmem.2⟩
    simp only [clampT_of_mem hs', hA]
  rw [this, sol_integral (hs x) hb.cont hmem, h0]
  abel

theorem Guniq {T : ℝ} (hT : 0 ≤ T) {m : ℕ} {Λ : ℝ} {b : ℝ → E → E} (hb : DB T m Λ b)
    {Ψ : ℝ → E → E} (h0 : ∀ x, Ψ 0 x = x) (hs : ∀ x, FlowA.Sol T b (fun τ => Ψ τ x))
    (x : E) (A : ℝ →ᵇ E) (hA : Gmap T b A = constCLM E x) :
    ∀ t ∈ Icc (0 : ℝ) T, A t = Ψ t x := by
  have hAt : ∀ t, A t + ∫ s in (0 : ℝ)..clampT T t, b (clampT T s) (A s) = x := fun t => by
    have := congrArg (fun F : ℝ →ᵇ E => F t) hA
    simpa [Gmap, nem_apply hT hb, constCLM_apply] using this
  have hFc : Continuous fun s : ℝ => b (clampT T s) (A s) := by
    have := hb.cont.comp (f := fun s : ℝ => (clampT T s, A s)) (s := univ)
      (t := Icc (0 : ℝ) T ×ˢ univ)
      ((continuous_clampT T).prodMk A.continuous).continuousOn
      (fun s _ => ⟨clampT_mem hT s, trivial⟩)
    exact continuousOn_univ.1 this
  have hA0 : A 0 = x := by
    have := hAt 0
    rwa [clampT_of_mem ⟨le_rfl, hT⟩, intervalIntegral.integral_same, add_zero] at this
  have hsol : FlowA.Sol T b A := by
    intro τ hτ
    have hφ : HasDerivAt (fun t => x - ∫ s in (0 : ℝ)..t, b (clampT T s) (A s))
        (-(b (clampT T τ) (A τ))) τ :=
      (hFc.integral_hasStrictDerivAt 0 τ).hasDerivAt.const_sub x
    have := hφ.hasDerivWithinAt (s := Icc (0 : ℝ) T)
    rw [clampT_of_mem hτ] at this
    refine this.congr (fun t ht => ?_) ?_
    · rw [← hAt t, clampT_of_mem ht]; abel
    · rw [← hAt τ, clampT_of_mem hτ]; abel
  exact fun t ht => FlowA.sol_unique (hb.hyp hT) le_rfl hsol (hs x) (by rw [hA0, h0]) t ht

theorem hasFDerivAt_Gmap {T : ℝ} (hT : 0 ≤ T) {m : ℕ} {Λ : ℝ} {b : ℝ → E → E}
    (hb : DB T m Λ b) (α : ℝ →ᵇ E) :
    HasFDerivAt (Gmap T b)
      (1 + continuousMultilinearCurryFin1 ℝ (ℝ →ᵇ E) (ℝ →ᵇ E) (tay T b α 1)) α := by
  have := (hasFDerivAt_id α).add (hasFDerivAt_nem hT hb α)
  exact this

/-- Local parametrisation of the flow by the inverse function theorem. -/
theorem exists_local_param {T : ℝ} (hT : 0 ≤ T) {m : ℕ} {Λ : ℝ} {b : ℝ → E → E}
    (hb : DB T m Λ b) {Ψ : ℝ → E → E} (h0 : ∀ x, Ψ 0 x = x)
    (hs : ∀ x, FlowA.Sol T b (fun τ => Ψ τ x)) (x0 : E) :
    ∃ A : E → (ℝ →ᵇ E), ContDiffAt ℝ ((m + 1 : ℕ) : WithTop ℕ∞) A x0 ∧
      (∀ᶠ x in 𝓝 x0, Gmap T b (A x) = constCLM E x) ∧
      (∀ᶠ x in 𝓝 x0, ∀ t ∈ Icc (0 : ℝ) T, A x t = Ψ t x) := by
  have hpath : ∀ x, ∃ A : ℝ →ᵇ E, ∀ t, A t = Ψ (clampT T t) x := by
    intro x
    have hc : Continuous fun t => Ψ (clampT T t) x :=
      (hs x).continuousOn.comp_continuous (continuous_clampT T) (fun t => clampT_mem hT t)
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hs x).continuousOn
    exact ⟨BoundedContinuousFunction.ofNormedAddCommGroup _ hc C
      (fun t => hC _ (clampT_mem hT t)), fun t => rfl⟩
  choose Ξ hΞ using hpath
  have hGΞ : ∀ x, Gmap T b (Ξ x) = constCLM E x := fun x => Gpath hT hb h0 hs x (Ξ x) (hΞ x)
  set n : WithTop ℕ∞ := ((m + 1 : ℕ) : WithTop ℕ∞) with hn_def
  have hn : n ≠ 0 := by rw [hn_def]; exact_mod_cast Nat.succ_ne_zero m
  have hΛ := hb.Λ_nonneg hT
  have hG : ContDiff ℝ n (Gmap T b) := contDiff_id.add (contDiff_nem hT hb)
  set α0 := Ξ x0 with hα0
  set V : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E) :=
    continuousMultilinearCurryFin1 ℝ (ℝ →ᵇ E) (ℝ →ᵇ E) (tay T b α0 1) with hVdef
  have hDG : HasFDerivAt (Gmap T b) (1 + V) α0 := hasFDerivAt_Gmap hT hb α0
  have hV : ∀ γ t, ‖V γ t‖ ≤ ∫ s in (0 : ℝ)..clampT T t, Λ * ‖γ s‖ := by
    intro γ t
    have hct := clampT_nonneg T t
    have hB : HasB (fun s => iteratedFDeriv ℝ 1 (bt T b s) (α0 s)) :=
      (hb.good hT (by omega)).hasB α0
    have hint0 := (hB.goodInt (fun _ => γ)).integrable 0 (clampT T t)
    have hint : IntervalIntegrable (fun s => fderiv ℝ (b (clampT T s)) (α0 s) (γ s)) volume 0
        (clampT T t) := by
      have e : (fun s => fderiv ℝ (b (clampT T s)) (α0 s) (γ s)) =
          intg 1 (fun s => iteratedFDeriv ℝ 1 (bt T b s) (α0 s)) (fun _ => γ) := by
        funext s; simp [intg, iteratedFDeriv_one_apply, bt]
      rw [e]; exact hint0
    rw [hVdef, dnem_apply hT hb]
    refine (intervalIntegral.norm_integral_le_integral_norm hct).trans ?_
    refine intervalIntegral.integral_mono_on hct hint.norm ?_ fun s _ => ?_
    · exact ((γ.continuous.norm.const_mul Λ)).intervalIntegrable _ _
    · refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]
      exact hb.deriv_bound _ (clampT_mem hT s) 1 le_rfl (by omega) _
  have hu : IsUnit (1 + V) := isUnit_one_add_volterra hT hΛ V hV
  set f' : (ℝ →ᵇ E) ≃L[ℝ] (ℝ →ᵇ E) := ContinuousLinearEquiv.unitsEquiv ℝ (ℝ →ᵇ E) hu.unit
    with hf'def
  have hf'eq : ((f' : (ℝ →ᵇ E) ≃L[ℝ] (ℝ →ᵇ E)) : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E)) = 1 + V := by
    ext γ
    simp [hf'def, ContinuousLinearEquiv.unitsEquiv_apply]
  have hf' : HasFDerivAt (Gmap T b) ((f' : (ℝ →ᵇ E) ≃L[ℝ] (ℝ →ᵇ E)) : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
      α0 := by rw [hf'eq]; exact hDG
  have hGat : ContDiffAt ℝ n (Gmap T b) α0 := hG.contDiffAt
  have hg : ContDiffAt ℝ n (hGat.localInverse hf' hn) (Gmap T b α0) := hGat.to_localInverse hf' hn
  have hev : ∀ᶠ y in 𝓝 (Gmap T b α0), Gmap T b (hGat.localInverse hf' hn y) = y :=
    (hGat.hasStrictFDerivAt' hf' hn).eventually_right_inverse
  have hGα0 : Gmap T b α0 = constCLM E x0 := hGΞ x0
  rw [hGα0] at hg hev
  have hev' : ∀ᶠ x in 𝓝 x0, Gmap T b (hGat.localInverse hf' hn (constCLM E x)) = constCLM E x :=
    ((constCLM E).continuous.tendsto x0).eventually hev
  refine ⟨fun x => hGat.localInverse hf' hn (constCLM E x), hg.comp x0 (constCLM E).contDiff.contDiffAt,
    hev', ?_⟩
  filter_upwards [hev'] with x hx
  exact fun t ht => Guniq hT hb h0 hs x _ hx t ht

theorem contDiffAt_flow {T : ℝ} (hT : 0 ≤ T) {m : ℕ} {Λ : ℝ} {b : ℝ → E → E}
    (hb : DB T m Λ b) {Ψ : ℝ → E → E} (h0 : ∀ x, Ψ 0 x = x)
    (hs : ∀ x, FlowA.Sol T b (fun τ => Ψ τ x)) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) (x0 : E) :
    ContDiffAt ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (Ψ τ) x0 := by
  obtain ⟨A, hA, -, hAΨ⟩ := exists_local_param hT hb h0 hs x0
  set n : WithTop ℕ∞ := ((m + 1 : ℕ) : WithTop ℕ∞) with hn_def
  have h2 : ContDiffAt ℝ n (fun α : ℝ →ᵇ E => α τ) (A x0) := by
    have : ContDiff ℝ n (BoundedContinuousFunction.evalCLM (β := E) ℝ τ) :=
      ContinuousLinearMap.contDiff _
    exact this.contDiffAt
  have hcd : ContDiffAt ℝ n (fun x => (A x) τ) x0 := by
    have := h2.comp x0 hA
    exact this
  refine hcd.congr_of_eventuallyEq ?_
  filter_upwards [hAΨ] with x hx
  exact (hx τ hτ).symm

/-- Integral form of the variational equation. -/
theorem fderiv_flow_integral {T : ℝ} (hT : 0 ≤ T) {m : ℕ} {Λ : ℝ} {b : ℝ → E → E}
    (hb : DB T m Λ b) {Ψ : ℝ → E → E} (h0 : ∀ x, Ψ 0 x = x)
    (hs : ∀ x, FlowA.Sol T b (fun τ => Ψ τ x)) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) (x0 v : E) :
    fderiv ℝ (Ψ τ) x0 v = v - ∫ s in (0 : ℝ)..τ, fderiv ℝ (b s) (Ψ s x0) (fderiv ℝ (Ψ s) x0 v) := by
  obtain ⟨A, hA, hAG, hAΨ⟩ := exists_local_param hT hb h0 hs x0
  have hn1 : ((m + 1 : ℕ) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hAd : HasFDerivAt A (fderiv ℝ A x0) x0 := (hA.differentiableAt hn1).hasFDerivAt
  have hcomp := (hasFDerivAt_Gmap hT hb (A x0)).comp x0 hAd
  have hconst : HasFDerivAt (fun x => Gmap T b (A x)) (constCLM E) x0 :=
    (constCLM E).hasFDerivAt.congr_of_eventuallyEq (hAG.mono fun x hx => hx)
  have huniq := hcomp.unique hconst
  have hAx0 : ∀ t ∈ Icc (0 : ℝ) T, A x0 t = Ψ t x0 := hAΨ.self_of_nhds
  set γ : ℝ →ᵇ E := fderiv ℝ A x0 v with hγ
  have hfd : ∀ s ∈ Icc (0 : ℝ) T, fderiv ℝ (Ψ s) x0 v = γ s := by
    intro s hs'
    have h1 : HasFDerivAt (fun x => A x s)
        ((BoundedContinuousFunction.evalCLM (β := E) ℝ s).comp (fderiv ℝ A x0)) x0 :=
      (BoundedContinuousFunction.evalCLM (β := E) ℝ s).hasFDerivAt.comp x0 hAd
    have h2 : HasFDerivAt (Ψ s) ((BoundedContinuousFunction.evalCLM (β := E) ℝ s).comp
        (fderiv ℝ A x0)) x0 :=
      h1.congr_of_eventuallyEq (hAΨ.mono fun x hx => hx s hs' |>.symm)
    rw [h2.fderiv]
    rfl
  have hvec := congrArg (fun F : (ℝ →ᵇ E) => F τ) (congrArg (fun L : E →L[ℝ] (ℝ →ᵇ E) => L v) huniq)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
    BoundedContinuousFunction.coe_add, Pi.add_apply, constCLM_apply] at hvec
  have hint : continuousMultilinearCurryFin1 ℝ (ℝ →ᵇ E) (ℝ →ᵇ E) (tay T b (A x0) 1) γ τ =
      ∫ s in (0 : ℝ)..τ, fderiv ℝ (b s) (Ψ s x0) (fderiv ℝ (Ψ s) x0 v) := by
    rw [dnem_apply hT hb, clampT_of_mem hτ]
    refine intervalIntegral.integral_congr fun s hs' => ?_
    rw [uIcc_of_le hτ.1] at hs'
    have hs'' : s ∈ Icc (0 : ℝ) T := ⟨hs'.1, hs'.2.trans hτ.2⟩
    simp only [clampT_of_mem hs'', hAx0 s hs'', hfd s hs'']
  rw [hfd τ hτ, ← hint]
  exact eq_sub_of_add_eq hvec

end HRS.MS.FlowB
