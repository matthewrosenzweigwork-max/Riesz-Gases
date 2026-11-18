import HRS.MS.LcFlowAux2
import HRS.MS.FlowC

/-!
# LC-6 (part 1): deterministic inputs for the backward equation of `lcSg` (S4.11, step 6)

Pathwise facts about the flow `lcFlow Q c B g r t` for a fixed continuous noise path `g`:

* `lc6_flow_bound`: the derivatives of order `1, 2, 3` of `lcFlow Q c B g r t` are bounded by a constant
  `K` depending only on `d, Q, Λc, ΛB, T` (not on `g, r, t ≤ T`), from `FlowC.flow_iter_bound`;
* `lc6_flow_deriv_cont`: `(r, x) ↦ D (lcFlow … r t) x` and `D² (lcFlow … r t) x` are continuous on
  `[0,t] × ℝ^d`.  The proof is an interpolation argument: `(r,x) ↦ lcFlow … r t x` is continuous
  (`lc_flow_continuous`) and the third derivatives are uniformly bounded, so the first and second
  derivatives converge locally uniformly (`lc6_interp1`, `lc6_step`);
* `lc6_chain2`: the second-order chain rule `D²(f ∘ φ)`.

Everything here is for `LcHyp Q 2 Λc ΛB c B` (flow of class `C^3`).
-/

open MeasureTheory Set Filter Topology
open scoped NNReal
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace HRS.MS.Lc

/-! ### Interpolation -/

section Interp

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem lc6_lip_of_fderiv_le {f : E → V} (hf : Differentiable ℝ f) {C : ℝ}
    (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ C) (y z : E) : ‖f y - f z‖ ≤ C * ‖y - z‖ :=
  (convex_univ).norm_image_sub_le_of_norm_fderiv_le (fun x _ => hf x) (fun x _ => hb x)
    (mem_univ z) (mem_univ y)

/-- If `h` is small on a ball and its derivative is `M`-Lipschitz, the derivative is small. -/
theorem lc6_interp1 {h : E → V} (hd : Differentiable ℝ h) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y z, ‖fderiv ℝ h y - fderiv ℝ h z‖ ≤ M * ‖y - z‖) (y : E) {ρ ε : ℝ} (hρ : 0 < ρ)
    (hε : ∀ z, ‖z - y‖ ≤ ρ → ‖h z‖ ≤ ε) : ‖fderiv ℝ h y‖ ≤ (2 * ε + M * ρ ^ 2) / ρ := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hε y (by simp [hρ.le]))
  have hC : 0 ≤ (2 * ε + M * ρ ^ 2) / ρ := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun e => ?_
  by_cases he : e = 0
  · simp [he]
  have hne : 0 < ‖e‖ := norm_pos_iff.2 he
  set e' : E := (ρ / ‖e‖) • e with he'
  have hne' : ‖e'‖ = ρ := by
    rw [he', norm_smul, Real.norm_of_nonneg (by positivity)]; field_simp
  set k : E → V := fun w => h w - fderiv ℝ h y w with hk
  have hkd : Differentiable ℝ k := hd.sub (fderiv ℝ h y).differentiable
  have hkb : ∀ w ∈ Metric.closedBall y ρ, ‖fderiv ℝ k w‖ ≤ M * ρ := by
    intro w hw
    have e1 : fderiv ℝ k w = fderiv ℝ h w - fderiv ℝ h y := by
      rw [hk, fderiv_fun_sub (hd w) ((fderiv ℝ h y).differentiableAt), ContinuousLinearMap.fderiv]
    rw [e1]
    refine (hM w y).trans ?_
    have : ‖w - y‖ ≤ ρ := by simpa [dist_eq_norm] using hw
    exact mul_le_mul_of_nonneg_left this hM0
  have hmem : y + e' ∈ Metric.closedBall y ρ := by
    simp [dist_eq_norm, hne']
  have h1 := (convex_closedBall y ρ).norm_image_sub_le_of_norm_fderiv_le (fun w _ => hkd w) hkb
    (Metric.mem_closedBall_self hρ.le) hmem
  have e2 : k (y + e') - k y = h (y + e') - h y - fderiv ℝ h y e' := by
    simp only [hk, map_add]; abel
  rw [e2] at h1
  have e3 : ‖y + e' - y‖ = ρ := by simp [hne']
  rw [e3] at h1
  have h2 : ‖fderiv ℝ h y e'‖ ≤ 2 * ε + M * ρ ^ 2 := by
    have h3 : ‖h (y + e')‖ ≤ ε := hε _ (by simp [hne'])
    have h4 : ‖h y‖ ≤ ε := hε y (by simp [hρ.le])
    have h5 : ‖fderiv ℝ h y e'‖ ≤ ‖h (y + e') - h y‖ + ‖h (y + e') - h y - fderiv ℝ h y e'‖ := by
      calc ‖fderiv ℝ h y e'‖ = ‖(h (y + e') - h y) - (h (y + e') - h y - fderiv ℝ h y e')‖ := by
            congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    have h6 := norm_sub_le (h (y + e')) (h y)
    nlinarith
  have e4 : fderiv ℝ h y e' = (ρ / ‖e‖) • fderiv ℝ h y e := by rw [he', map_smul]
  rw [e4, norm_smul, Real.norm_of_nonneg (by positivity)] at h2
  calc ‖fderiv ℝ h y e‖ = (‖e‖ / ρ) * ((ρ / ‖e‖) * ‖fderiv ℝ h y e‖) := by field_simp
    _ ≤ (‖e‖ / ρ) * (2 * ε + M * ρ ^ 2) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (2 * ε + M * ρ ^ 2) / ρ * ‖e‖ := by ring

/-- One step of the interpolation: locally uniform convergence of `A r` to `A r0` and uniformly
Lipschitz derivatives give locally uniform convergence of the derivatives. -/
theorem lc6_step (S : Set ℝ) (r0 : ℝ) (A : ℝ → E → V) {M : ℝ} (hM0 : 0 ≤ M)
    (hd : ∀ r ∈ S, Differentiable ℝ (A r))
    (hM : ∀ r ∈ S, ∀ y z, ‖fderiv ℝ (A r) y - fderiv ℝ (A r) z‖ ≤ M * ‖y - z‖) (hr0 : r0 ∈ S)
    (hU : ∀ (x0 : E) (R ε : ℝ), 0 < ε → ∃ δ > 0, ∀ r ∈ S, |r - r0| < δ → ∀ y, ‖y - x0‖ ≤ R →
      ‖A r y - A r0 y‖ < ε) :
    ∀ (x0 : E) (R ε : ℝ), 0 < ε → ∃ δ > 0, ∀ r ∈ S, |r - r0| < δ → ∀ y, ‖y - x0‖ ≤ R →
      ‖fderiv ℝ (A r) y - fderiv ℝ (A r0) y‖ < ε := by
  intro x0 R ε hε
  set ρ : ℝ := ε / (4 * M + 4) with hρ
  have hρ0 : 0 < ρ := by positivity
  obtain ⟨δ, hδ, hδ'⟩ := hU x0 (R + ρ) (ε * ρ / 8) (by positivity)
  refine ⟨δ, hδ, fun r hr hrδ y hy => ?_⟩
  set h : E → V := fun z => A r z - A r0 z with hh
  have hhd : Differentiable ℝ h := (hd r hr).sub (hd r0 hr0)
  have hfd : ∀ z, fderiv ℝ h z = fderiv ℝ (A r) z - fderiv ℝ (A r0) z := fun z =>
    fderiv_fun_sub ((hd r hr) z) ((hd r0 hr0) z)
  have hM2 : ∀ y z, ‖fderiv ℝ h y - fderiv ℝ h z‖ ≤ (2 * M) * ‖y - z‖ := by
    intro y z
    rw [hfd, hfd]
    have e : fderiv ℝ (A r) y - fderiv ℝ (A r0) y - (fderiv ℝ (A r) z - fderiv ℝ (A r0) z) =
        (fderiv ℝ (A r) y - fderiv ℝ (A r) z) - (fderiv ℝ (A r0) y - fderiv ℝ (A r0) z) := by abel
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have := hM r hr y z
    have := hM r0 hr0 y z
    linarith
  have h1 := lc6_interp1 hhd (by positivity) hM2 y hρ0 (ε := ε * ρ / 8) (fun z hz => by
    refine (hδ' r hr hrδ z ?_).le
    calc ‖z - x0‖ ≤ ‖z - y‖ + ‖y - x0‖ := norm_sub_le_norm_sub_add_norm_sub z y x0
      _ ≤ ρ + R := add_le_add hz hy
      _ = R + ρ := add_comm _ _)
  rw [hfd] at h1
  refine lt_of_le_of_lt h1 ?_
  have e1 : (2 * (ε * ρ / 8) + 2 * M * ρ ^ 2) / ρ = ε / 4 + 2 * M * ρ := by
    field_simp; ring
  rw [e1]
  have e2 : 2 * M * ρ ≤ ε / 2 := by
    rw [hρ]
    rw [show 2 * M * (ε / (4 * M + 4)) = ε * (2 * M / (4 * M + 4)) by ring]
    have : 2 * M / (4 * M + 4) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    nlinarith
  linarith

/-- Continuity of `(r,x) ↦ A r x` at `(r0, x0)` from locally uniform convergence and continuity of
`A r0`. -/
theorem lc6_cwa (S : Set ℝ) (r0 : ℝ) (A : ℝ → E → V) (x0 : E)
    (hU : ∀ (x0 : E) (R ε : ℝ), 0 < ε → ∃ δ > 0, ∀ r ∈ S, |r - r0| < δ → ∀ y, ‖y - x0‖ ≤ R →
      ‖A r y - A r0 y‖ < ε)
    (hc : ContinuousAt (A r0) x0) :
    ContinuousWithinAt (fun p : ℝ × E => A p.1 p.2) (S ×ˢ univ) (r0, x0) := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ1, hδ1, h1⟩ := hU x0 1 (ε / 2) (half_pos hε)
  obtain ⟨δ2, hδ2, h2⟩ := Metric.continuousAt_iff.1 hc (ε / 2) (half_pos hε)
  refine ⟨min (min δ1 δ2) 1, by positivity, ?_⟩
  rintro ⟨r, x⟩ ⟨hr, -⟩ hd
  simp only at hr
  rw [Prod.dist_eq, max_lt_iff] at hd
  have hdr : |r - r0| < δ1 := by
    have := hd.1; rw [Real.dist_eq] at this
    exact lt_of_lt_of_le this ((min_le_left _ _).trans (min_le_left _ _))
  have hdx2 : dist x x0 < δ2 :=
    lt_of_lt_of_le hd.2 ((min_le_left _ _).trans (min_le_right _ _))
  have hdx1 : ‖x - x0‖ ≤ 1 := by
    have := hd.2; rw [dist_eq_norm] at this
    exact this.le.trans (min_le_right _ _)
  have a1 := h1 r hr hdr x hdx1
  have a2 := h2 hdx2
  rw [dist_eq_norm] at a2 ⊢
  calc ‖A r x - A r0 x0‖ ≤ ‖A r x - A r0 x‖ + ‖A r0 x - A r0 x0‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε := by linarith

end Interp

/-! ### Interpolation for iterated derivatives -/

section IterStep

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem lc6_fderiv_iter (j : ℕ) (f : E → F) (y : E) :
    fderiv ℝ (iteratedFDeriv ℝ j f) y =
      continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F
        (iteratedFDeriv ℝ (j + 1) f y) := by
  rw [iteratedFDeriv_succ_eq_comp_left]; simp

theorem lc6_iter_step (j : ℕ) (S : Set ℝ) (r0 : ℝ) (φ : ℝ → E → F) {M : ℝ} (hM0 : 0 ≤ M)
    (hφ : ∀ r ∈ S, ContDiff ℝ ((j + 2 : ℕ) : WithTop ℕ∞) (φ r))
    (hb : ∀ r ∈ S, ∀ y, ‖iteratedFDeriv ℝ (j + 2) (φ r) y‖ ≤ M) (hr0 : r0 ∈ S)
    (hU : ∀ (x0 : E) (R ε : ℝ), 0 < ε → ∃ δ > 0, ∀ r ∈ S, |r - r0| < δ → ∀ y, ‖y - x0‖ ≤ R →
      ‖iteratedFDeriv ℝ j (φ r) y - iteratedFDeriv ℝ j (φ r0) y‖ < ε) :
    ∀ (x0 : E) (R ε : ℝ), 0 < ε → ∃ δ > 0, ∀ r ∈ S, |r - r0| < δ → ∀ y, ‖y - x0‖ ≤ R →
      ‖iteratedFDeriv ℝ (j + 1) (φ r) y - iteratedFDeriv ℝ (j + 1) (φ r0) y‖ < ε := by
  have hnorm : ∀ r y r' y', ‖fderiv ℝ (iteratedFDeriv ℝ j (φ r)) y -
      fderiv ℝ (iteratedFDeriv ℝ j (φ r')) y'‖ =
      ‖iteratedFDeriv ℝ (j + 1) (φ r) y - iteratedFDeriv ℝ (j + 1) (φ r') y'‖ := by
    intro r y r' y'
    rw [lc6_fderiv_iter, lc6_fderiv_iter]
    have := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F).norm_map
      (iteratedFDeriv ℝ (j + 1) (φ r) y - iteratedFDeriv ℝ (j + 1) (φ r') y')
    rw [LinearIsometryEquiv.map_sub] at this
    exact this
  have hlt : (j : WithTop ℕ∞) < ((j + 2 : ℕ) : WithTop ℕ∞) := by exact_mod_cast (by omega)
  have key := lc6_step S r0 (fun r => iteratedFDeriv ℝ j (φ r)) hM0
    (fun r hr => (hφ r hr).differentiable_iteratedFDeriv hlt)
    (fun r hr y z => by
      rw [hnorm]
      have hd : Differentiable ℝ (iteratedFDeriv ℝ (j + 1) (φ r)) :=
        (hφ r hr).differentiable_iteratedFDeriv (by exact_mod_cast (by omega))
      refine lc6_lip_of_fderiv_le hd (fun x => ?_) y z
      rw [norm_fderiv_iteratedFDeriv]; exact hb r hr x) hr0 hU
  intro x0 R ε hε
  obtain ⟨δ, hδ, h⟩ := key x0 R ε hε
  exact ⟨δ, hδ, fun r hr hrδ y hy => by rw [← hnorm]; exact h r hr hrδ y hy⟩

end IterStep

/-! ### Norms of iterated derivatives and the chain rule -/

section Chain

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem lc6_norm_fd2 (G : E → F) (y : E) :
    ‖fderiv ℝ (fderiv ℝ G) y‖ = ‖iteratedFDeriv ℝ 2 G y‖ := by
  rw [← norm_iteratedFDeriv_one (𝕜 := ℝ) (f := fderiv ℝ G), norm_iteratedFDeriv_fderiv]

theorem lc6_cd3 {G : E → F} (hG : ContDiff ℝ ((2 + 1 : ℕ) : WithTop ℕ∞) G) :
    Differentiable ℝ G ∧ Differentiable ℝ (fderiv ℝ G) ∧ Differentiable ℝ (fderiv ℝ (fderiv ℝ G)) ∧
      Continuous (fderiv ℝ G) ∧ Continuous (fderiv ℝ (fderiv ℝ G)) := by
  have h2 : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (fderiv ℝ G) := hG.fderiv_right (by norm_cast)
  have h1 : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (fderiv ℝ (fderiv ℝ G)) :=
    h2.fderiv_right (by norm_cast)
  exact ⟨hG.differentiable (by norm_cast), h2.differentiable (by norm_cast),
    h1.differentiable (by norm_cast), h2.continuous, h1.continuous⟩

theorem lc6_fderiv_comp {f : F → ℝ} {φ : E → F} (hφ : Differentiable ℝ φ)
    (hf : Differentiable ℝ f) :
    fderiv ℝ (fun x => f (φ x)) = fun x => (fderiv ℝ f (φ x)).comp (fderiv ℝ φ x) := by
  funext x
  exact fderiv_comp x (hf (φ x)) (hφ x)

/-- Second-order chain rule. -/
theorem lc6_chain2 {f : F → ℝ} {φ : E → F} (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 2 f) (x v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => f (φ y))) x v w =
      fderiv ℝ (fderiv ℝ f) (φ x) (fderiv ℝ φ x v) (fderiv ℝ φ x w) +
        fderiv ℝ f (φ x) (fderiv ℝ (fderiv ℝ φ) x v w) := by
  have hφ1 : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hf1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hφ2 : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hf2 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  rw [lc6_fderiv_comp hφ1 hf1]
  have hc : HasFDerivAt (fun y => fderiv ℝ f (φ y))
      ((fderiv ℝ (fderiv ℝ f) (φ x)).comp (fderiv ℝ φ x)) x :=
    (hf2 (φ x)).hasFDerivAt.comp x (hφ1 x).hasFDerivAt
  have hd : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) x) x := (hφ2 x).hasFDerivAt
  have := (hc.clm_comp hd).fderiv
  rw [this]
  simp only [ContinuousLinearMap.comp_apply, add_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
  ring

end Chain

/-! ### Uniform derivative bounds of the flow -/

section Bounds

variable {d : ℕ}

theorem lc6_flow_bound (Q : Matrix (Fin d) (Fin d) ℝ) (Λc ΛB T : ℝ) (hT : 0 ≤ T) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {c : ℝ → Euc d} {B : ℝ → Euc d → Euc d},
      LcHyp Q 2 Λc ΛB c B → ∀ {g : ℝ → Euc d}, Continuous g → ∀ {r t : ℝ}, 0 ≤ r → r ≤ t → t ≤ T →
      ∀ (x : Euc d) (j : ℕ), 1 ≤ j → j ≤ 3 → ‖iteratedFDeriv ℝ j (lcFlow Q c B g r t) x‖ ≤ K := by
  obtain ⟨C, hC, hCb⟩ := HRS.MS.FlowC.flow_iter_bound d 2 T (lcLam Q Λc ΛB) hT
  refine ⟨max 1 (max (Real.exp (lcLam Q Λc ΛB * T)) (C * Real.exp (C * (2 : ℕ) * T))), le_max_left _ _,
    fun {c B} H {g} hg {r t} hr hrt htT x j hj1 hj3 => ?_⟩
  have hΛ := H.lam_nonneg
  have hτ0 : 0 ≤ t - r := sub_nonneg.2 hrt
  have hτT : t - r ≤ T := by linarith
  by_cases hj : j = 1
  · subst hj
    rw [norm_iteratedFDeriv_one]
    refine (lcFlow_fderiv_le H hg hr hrt x).trans ?_
    refine le_trans ?_ ((le_max_left _ _).trans (le_max_right _ _))
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hτT hΛ)
  · have hj2 : 2 ≤ j := by omega
    have hΨ := lc2_isNegDriftFlow H hg hr hT
    have hb := lcDrift_isDriftBounds H hg hr T
    obtain ⟨hA, -⟩ := hCb _ hb _ hΨ (t - r) ⟨hτ0, hτT⟩
    have hA' := hA j hj2 hj3 x
    have hΨc : ContDiff ℝ ((2 + 1 : ℕ) : WithTop ℕ∞) (fun x => lcZ (lcDrift Q c B g r) x (t - r)) :=
      FlowB.flow_contDiff hT hb hΨ (t - r) ⟨hτ0, hτT⟩
    have e : lcFlow Q c B g r t = fun x => lcZ (lcDrift Q c B g r) x (t - r) + lcU Q g r t := rfl
    rw [e, HRS.MS.PoisFlow.pf_iter_add_const _ hΨc (by omega) hj3 x]
    refine hA'.trans ?_
    refine le_trans ?_ ((le_max_right _ _).trans (le_max_right _ _))
    have : Real.exp (C * (2 : ℕ) * (t - r)) ≤ Real.exp (C * (2 : ℕ) * T) :=
      Real.exp_le_exp.2 (by gcongr)
    exact mul_le_mul_of_nonneg_left this hC.le

theorem lc6_iter0_sub {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f f' : E → F) (y : E) :
    ‖iteratedFDeriv ℝ 0 f y - iteratedFDeriv ℝ 0 f' y‖ = ‖f y - f' y‖ := by
  rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp]
  have := (continuousMultilinearCurryFin0 ℝ E F).symm.norm_map (f y - f' y)
  rw [LinearIsometryEquiv.map_sub] at this
  exact this

end Bounds

/-! ### Continuity of the derivatives of the flow in `(r, x)` -/

section DerivCont

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {Λc ΛB : ℝ} {c : ℝ → Euc d}
  {B : ℝ → Euc d → Euc d} {g : ℝ → Euc d}

theorem lc6_flow_cont_t (H : LcHyp Q 2 Λc ΛB c B) (hg : Continuous g) (t : ℝ)
    (S : Set (ℝ × Euc d)) (hS : ∀ p ∈ S, 0 ≤ p.1 ∧ p.1 ≤ t) :
    ContinuousOn (fun p : ℝ × Euc d => lcFlow Q c B g p.1 t p.2) S := by
  have h1 := lc_flow_continuous H hg
  have h2 : Continuous (fun p : ℝ × Euc d => ((p.1, t, p.2) : ℝ × ℝ × Euc d)) :=
    (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
  have hm : Set.MapsTo (fun p : ℝ × Euc d => ((p.1, t, p.2) : ℝ × ℝ × Euc d)) S
      {p : ℝ × ℝ × Euc d | 0 ≤ p.1 ∧ p.1 ≤ p.2.1} := fun p hp => hS p hp
  have := ContinuousOn.comp (f := fun p : ℝ × Euc d => ((p.1, t, p.2) : ℝ × ℝ × Euc d))
    h1 h2.continuousOn hm
  exact this

theorem lc6_unif0 (H : LcHyp Q 2 Λc ΛB c B) (hg : Continuous g) {t : ℝ} {r0 : ℝ}
    (hr0 : r0 ∈ Icc 0 t) (x0 : Euc d) (R ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ r ∈ Icc 0 t, |r - r0| < δ → ∀ y, ‖y - x0‖ ≤ R →
      ‖lcFlow Q c B g r t y - lcFlow Q c B g r0 t y‖ < ε := by
  have hK0 : IsCompact (Icc 0 t ×ˢ Metric.closedBall x0 R : Set (ℝ × Euc d)) :=
    isCompact_Icc.prod (isCompact_closedBall x0 R)
  have hcont := lc6_flow_cont_t H hg t (Icc 0 t ×ˢ Metric.closedBall x0 R)
    (fun p hp => hp.1)
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.1
    (hK0.uniformContinuousOn_of_continuous hcont) ε hε
  refine ⟨δ, hδ, fun r hr hrδ y hy => ?_⟩
  have hy' : y ∈ Metric.closedBall x0 R := by simpa [dist_eq_norm] using hy
  have := h (r, y) ⟨hr, hy'⟩ (r0, y) ⟨hr0, hy'⟩
    (by rw [Prod.dist_eq, dist_self, Real.dist_eq]; exact max_lt hrδ hδ)
  rw [dist_eq_norm] at this
  exact this

/-- Continuity in `(r, x)` of the first and second derivative of the flow, as continuous
multilinear maps. -/
theorem lc6_flow_deriv_cont (H : LcHyp Q 2 Λc ΛB c B) (hg : Continuous g) {t : ℝ} (ht : 0 ≤ t)
    {K : ℝ} (hK : ∀ r, 0 ≤ r → r ≤ t → ∀ (x : Euc d) (j : ℕ), 1 ≤ j → j ≤ 3 →
      ‖iteratedFDeriv ℝ j (lcFlow Q c B g r t) x‖ ≤ K) (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ 2) :
    ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ j (lcFlow Q c B g p.1 t) p.2)
      (Icc 0 t ×ˢ univ) := by
  set φ : ℝ → Euc d → Euc d := fun r => lcFlow Q c B g r t with hφ
  set S : Set ℝ := Icc 0 t with hS
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 le_rfl ht 0 1 le_rfl (by norm_num))
  have hC : ∀ r ∈ S, ContDiff ℝ ((2 + 1 : ℕ) : WithTop ℕ∞) (φ r) := fun r hr =>
    lcFlow_contDiff H hg hr.1 hr.2 |> fun h => by simpa using h
  have hb : ∀ n : ℕ, 2 ≤ n → n ≤ 3 → ∀ r ∈ S, ∀ y, ‖iteratedFDeriv ℝ n (φ r) y‖ ≤ K :=
    fun n h1 h2 r hr y => hK r hr.1 hr.2 y n (by omega) h2
  have U0 : ∀ r0 ∈ S, ∀ (x0 : Euc d) (R ε : ℝ), 0 < ε → ∃ δ > 0, ∀ r ∈ S, |r - r0| < δ →
      ∀ y, ‖y - x0‖ ≤ R → ‖iteratedFDeriv ℝ 0 (φ r) y - iteratedFDeriv ℝ 0 (φ r0) y‖ < ε := by
    intro r0 hr0 x0 R ε hε
    obtain ⟨δ, hδ, h⟩ := lc6_unif0 H hg hr0 x0 R ε hε
    exact ⟨δ, hδ, fun r hr hrδ y hy => by rw [lc6_iter0_sub]; exact h r hr hrδ y hy⟩
  have U1 : ∀ r0 ∈ S, ∀ (x0 : Euc d) (R ε : ℝ), 0 < ε → ∃ δ > 0, ∀ r ∈ S, |r - r0| < δ →
      ∀ y, ‖y - x0‖ ≤ R → ‖iteratedFDeriv ℝ 1 (φ r) y - iteratedFDeriv ℝ 1 (φ r0) y‖ < ε :=
    fun r0 hr0 => lc6_iter_step 0 S r0 φ hK0
      (fun r hr => (hC r hr).of_le (by norm_cast)) (fun r hr y => hb 2 le_rfl (by norm_num) r hr y)
      hr0 (U0 r0 hr0)
  have U2 : ∀ r0 ∈ S, ∀ (x0 : Euc d) (R ε : ℝ), 0 < ε → ∃ δ > 0, ∀ r ∈ S, |r - r0| < δ →
      ∀ y, ‖y - x0‖ ≤ R → ‖iteratedFDeriv ℝ 2 (φ r) y - iteratedFDeriv ℝ 2 (φ r0) y‖ < ε :=
    fun r0 hr0 => lc6_iter_step 1 S r0 φ hK0 (fun r hr => hC r hr)
      (fun r hr y => hb 3 (by norm_num) le_rfl r hr y) hr0 (U1 r0 hr0)
  rintro ⟨r0, x0⟩ ⟨hr0, -⟩
  have hr0' : r0 ∈ S := hr0
  have hcd : ContDiff ℝ ((2 + 1 : ℕ) : WithTop ℕ∞) (φ r0) := hC r0 hr0'
  have hcj : ContinuousAt (iteratedFDeriv ℝ j (φ r0)) x0 :=
    (hcd.continuous_iteratedFDeriv (by norm_cast; omega)).continuousAt
  interval_cases j
  · exact lc6_cwa S r0 (fun r => iteratedFDeriv ℝ 1 (φ r)) x0 (U1 r0 hr0') hcj
  · exact lc6_cwa S r0 (fun r => iteratedFDeriv ℝ 2 (φ r)) x0 (U2 r0 hr0') hcj

/-- Continuity in `(r, x)` of the integrand of the backward equation: `f ∘ Φ^r`, its first and its
second derivative (evaluated on fixed vectors), for `f ∈ C²`. -/
theorem lc6_integrand_cont (H : LcHyp Q 2 Λc ΛB c B) (hg : Continuous g) {t : ℝ} (ht : 0 ≤ t)
    {K : ℝ} (hK : ∀ r, 0 ≤ r → r ≤ t → ∀ (x : Euc d) (j : ℕ), 1 ≤ j → j ≤ 3 →
      ‖iteratedFDeriv ℝ j (lcFlow Q c B g r t) x‖ ≤ K) {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) :
    ContinuousOn (fun p : ℝ × Euc d => f (lcFlow Q c B g p.1 t p.2)) (Icc 0 t ×ˢ univ) ∧
    (∀ v, ContinuousOn (fun p : ℝ × Euc d =>
      fderiv ℝ (fun y => f (lcFlow Q c B g p.1 t y)) p.2 v) (Icc 0 t ×ˢ univ)) ∧
    (∀ v w, ContinuousOn (fun p : ℝ × Euc d =>
      fderiv ℝ (fderiv ℝ (fun y => f (lcFlow Q c B g p.1 t y))) p.2 v w) (Icc 0 t ×ˢ univ)) := by
  set φ : ℝ → Euc d → Euc d := fun r => lcFlow Q c B g r t with hφ
  have hφc : ContinuousOn (fun p : ℝ × Euc d => φ p.1 p.2) (Icc 0 t ×ˢ univ) :=
    lc6_flow_cont_t H hg t _ (fun p hp => hp.1)
  have hC : ∀ r ∈ Icc (0 : ℝ) t, ContDiff ℝ 2 (φ r) := fun r hr =>
    (lcFlow_contDiff H hg hr.1 hr.2).of_le (by norm_cast)
  have hf1 : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hf2 : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hf.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have D1 : ∀ v : Euc d, ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (φ p.1) p.2 v)
      (Icc 0 t ×ˢ univ) := by
    intro v
    have h := lc6_flow_deriv_cont H hg ht hK 1 le_rfl (by norm_num)
    have e : (fun p : ℝ × Euc d => fderiv ℝ (φ p.1) p.2 v) = fun p =>
        (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Euc d) (Euc d) (fun _ => v))
          (iteratedFDeriv ℝ 1 (φ p.1) p.2) := by
      funext p; simp [iteratedFDeriv_one_apply]
    rw [e]
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Euc d) (Euc d)
      (fun _ => v)).continuous.comp_continuousOn h
  have D2 : ∀ v w : Euc d, ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (fderiv ℝ (φ p.1)) p.2 v w)
      (Icc 0 t ×ˢ univ) := by
    intro v w
    have h := lc6_flow_deriv_cont H hg ht hK 2 (by norm_num) le_rfl
    have e : (fun p : ℝ × Euc d => fderiv ℝ (fderiv ℝ (φ p.1)) p.2 v w) = fun p =>
        (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euc d) (Euc d) ![v, w])
          (iteratedFDeriv ℝ 2 (φ p.1) p.2) := by
      funext p; simp [iteratedFDeriv_two_apply]
    rw [e]
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euc d) (Euc d)
      ![v, w]).continuous.comp_continuousOn h
  have hdiff : ∀ r ∈ Icc (0 : ℝ) t, Differentiable ℝ (φ r) := fun r hr =>
    (hC r hr).differentiable (by norm_num)
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  refine ⟨hf.continuous.comp_continuousOn hφc, fun v => ?_, fun v w => ?_⟩
  · have e : ∀ p ∈ (Icc 0 t ×ˢ univ : Set (ℝ × Euc d)),
        fderiv ℝ (fun y => f (φ p.1 y)) p.2 v = fderiv ℝ f (φ p.1 p.2) (fderiv ℝ (φ p.1) p.2 v) := by
      intro p hp
      rw [lc6_fderiv_comp (hdiff p.1 hp.1) hfd]; rfl
    refine ContinuousOn.congr (f := fun p : ℝ × Euc d =>
      fderiv ℝ f (φ p.1 p.2) (fderiv ℝ (φ p.1) p.2 v)) ?_ e
    exact (hf1.comp_continuousOn hφc).clm_apply (D1 v)
  · have e : ∀ p ∈ (Icc 0 t ×ˢ univ : Set (ℝ × Euc d)),
        fderiv ℝ (fderiv ℝ (fun y => f (φ p.1 y))) p.2 v w =
          fderiv ℝ (fderiv ℝ f) (φ p.1 p.2) (fderiv ℝ (φ p.1) p.2 v) (fderiv ℝ (φ p.1) p.2 w) +
            fderiv ℝ f (φ p.1 p.2) (fderiv ℝ (fderiv ℝ (φ p.1)) p.2 v w) := fun p hp =>
      lc6_chain2 (hC p.1 hp.1) hf p.2 v w
    refine ContinuousOn.congr (f := fun p : ℝ × Euc d =>
      fderiv ℝ (fderiv ℝ f) (φ p.1 p.2) (fderiv ℝ (φ p.1) p.2 v) (fderiv ℝ (φ p.1) p.2 w) +
        fderiv ℝ f (φ p.1 p.2) (fderiv ℝ (fderiv ℝ (φ p.1)) p.2 v w)) ?_ e
    refine ContinuousOn.add ?_ ?_
    · exact ((hf2.comp_continuousOn hφc).clm_apply (D1 v)).clm_apply (D1 w)
    · exact (hf1.comp_continuousOn hφc).clm_apply (D2 v w)

end DerivCont


/-! ### The Taylor-Gaussian expansion (abstract) -/

section Expansion

theorem lc6_taylor {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : E → ℝ}
    (hg : ContDiff ℝ 2 g) (x z : E) {ε : ℝ}
    (hε : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ g) (x + s • z) - fderiv ℝ (fderiv ℝ g) x‖ ≤ ε) :
    |g (x + z) - g x - fderiv ℝ g x z - (1 / 2) * fderiv ℝ (fderiv ℝ g) x z z| ≤ ε * ‖z‖ ^ 2 := by
  have hd1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hpath : ∀ s : ℝ, HasDerivAt (fun s : ℝ => x + s • z) z s := fun s => by
    simpa using ((hasDerivAt_id s).smul_const z).const_add x
  have h1 : ∀ s : ℝ, HasDerivAt (fun s : ℝ => g (x + s • z)) (fderiv ℝ g (x + s • z) z) s :=
    fun s => (hd1 (x + s • z)).hasFDerivAt.comp_hasDerivAt s (hpath s)
  have h2 : ∀ s : ℝ, HasDerivAt (fun s : ℝ => fderiv ℝ g (x + s • z) z)
      (fderiv ℝ (fderiv ℝ g) (x + s • z) z z) s := fun s => by
    have hc : HasDerivAt (fun s : ℝ => fderiv ℝ g (x + s • z))
        (fderiv ℝ (fderiv ℝ g) (x + s • z) z) s :=
      (hd2 (x + s • z)).hasFDerivAt.comp_hasDerivAt s (hpath s)
    simpa using hc.clm_apply (hasDerivAt_const s z)
  have hε0 : 0 ≤ ε := by
    have h := hε 0 (left_mem_Icc.2 zero_le_one)
    have h' := norm_nonneg (fderiv ℝ (fderiv ℝ g) (x + (0 : ℝ) • z) - fderiv ℝ (fderiv ℝ g) x)
    exact h'.trans h
  set A : ℝ := fderiv ℝ g x z with hA
  set Bq : ℝ := fderiv ℝ (fderiv ℝ g) x z z with hB
  have hθ : ∀ s : ℝ, HasDerivAt (fun s : ℝ => fderiv ℝ g (x + s • z) z - fderiv ℝ g x z - s * Bq)
      (fderiv ℝ (fderiv ℝ g) (x + s • z) z z - Bq) s := fun s => by
    have := ((h2 s).sub_const (fderiv ℝ g x z)).sub ((hasDerivAt_id s).mul_const Bq)
    convert this using 1
    · funext s; simp
    · simp
  have hθb : ∀ s ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ (fderiv ℝ g) (x + s • z) z z - Bq‖ ≤ ε * ‖z‖ ^ 2 := by
    intro s hs
    have e : fderiv ℝ (fderiv ℝ g) (x + s • z) z z - Bq =
        (fderiv ℝ (fderiv ℝ g) (x + s • z) - fderiv ℝ (fderiv ℝ g) x) z z := by simp [hB]
    rw [e]
    calc _ ≤ ‖fderiv ℝ (fderiv ℝ g) (x + s • z) - fderiv ℝ (fderiv ℝ g) x‖ * ‖z‖ * ‖z‖ :=
          ((ContinuousLinearMap.le_opNorm₂ _ _ _))
      _ ≤ ε * ‖z‖ * ‖z‖ := by gcongr; exact hε s hs
      _ = ε * ‖z‖ ^ 2 := by ring
  have hθ1 : ∀ s ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ g (x + s • z) z - fderiv ℝ g x z - s * Bq‖
      ≤ ε * ‖z‖ ^ 2 := by
    intro s hs
    have := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun s : ℝ => fderiv ℝ g (x + s • z) z - fderiv ℝ g x z - s * Bq)
      (f' := fun s => fderiv ℝ (fderiv ℝ g) (x + s • z) z z - Bq)
      (fun s _ => (hθ s).hasDerivWithinAt) hθb (left_mem_Icc.2 zero_le_one) hs
    have h0 : ‖s‖ ≤ 1 := by rw [Real.norm_of_nonneg hs.1]; exact hs.2
    simp only [zero_smul, add_zero, sub_self, zero_mul, sub_zero] at this
    exact this.trans (mul_le_of_le_one_right (by positivity) h0)
  have hη : ∀ s : ℝ, HasDerivAt (fun s : ℝ => g (x + s • z) - g x - s * A - (1/2) * s ^ 2 * Bq)
      (fderiv ℝ g (x + s • z) z - fderiv ℝ g x z - s * Bq) s := fun s => by
    have := (((h1 s).sub_const (g x)).sub ((hasDerivAt_id s).mul_const A)).sub
      ((((hasDerivAt_id s).pow 2).const_mul (1/2)).mul_const Bq)
    convert this using 1
    · funext s; simp [hA]
    · simp [hA]
  have := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s : ℝ => g (x + s • z) - g x - s * A - (1/2) * s ^ 2 * Bq)
    (f' := fun s => fderiv ℝ g (x + s • z) z - fderiv ℝ g x z - s * Bq)
    (fun s _ => (hη s).hasDerivWithinAt) hθ1 (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
  simpa [Real.norm_eq_abs, hA, hB] using this

theorem lc6_expand {d : ℕ} (v : Euc d) : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
  have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v
  simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using this.symm

theorem lc6_lin_expand {d : ℕ} (ξ : Euc d →L[ℝ] ℝ) (v : Euc d) :
    ξ v = ∑ i, v i * ξ (EuclideanSpace.single i 1) := by
  conv_lhs => rw [lc6_expand v]
  simp [map_sum, map_smul]

theorem lc6_bil_expand {d : ℕ} (Hh : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) (u v : Euc d) :
    Hh u v = ∑ i, ∑ j, u i * v j *
      Hh (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  conv_lhs => rw [lc6_expand u, lc6_expand v]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem lc6_norm_sq_eq {d : ℕ} (v : Euc d) : ‖v‖ ^ 2 = ∑ i, v i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp

/-- Integrability from a pointwise polynomial bound. -/
theorem lc6_int_of_bound {Δ : Ω → Euc d} {s : Ω → ℝ} (hΔ4 : Integrable (fun ω => ‖Δ ω‖ ^ 4) P)
    (hs4 : Integrable (fun ω => s ω ^ 4) P) {F : Ω → ℝ} (hF : Measurable F) {K : ℝ}
    (hb : ∀ ω, |F ω| ≤ K * (1 + ‖Δ ω‖ ^ 4 + s ω ^ 4)) : Integrable F P := by
  have : Integrable (fun ω => K * (1 + ‖Δ ω‖ ^ 4 + s ω ^ 4)) P :=
    (((integrable_const (1 : ℝ)).add hΔ4).add hs4).const_mul K
  refine this.mono' hF.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  simpa [Real.norm_eq_abs] using hb ω


theorem lc6_pow4_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), mul_nonneg ha hb, sq_nonneg (a ^ 2 - b ^ 2),
    mul_nonneg (mul_nonneg ha hb) (sq_nonneg (a - b)), pow_nonneg ha 2, pow_nonneg hb 2]

theorem lc6_le_one_add_pow4 {t : ℝ} (ht : 0 ≤ t) : t ≤ 1 + t ^ 4 := by
  nlinarith [sq_nonneg (t ^ 2 - 1), sq_nonneg (t - 1), sq_nonneg t]

theorem lc6_sq_le_one_add_pow4 {t : ℝ} : t ^ 2 ≤ 1 + t ^ 4 := by
  nlinarith [sq_nonneg (t ^ 2 - 1)]

theorem lc6_le_pow4_of_one_le {t : ℝ} (ht : 1 ≤ t) : t ≤ t ^ 4 := by
  nlinarith [sq_nonneg (t - 1), sq_nonneg t, mul_nonneg (by linarith : (0:ℝ) ≤ t - 1) (by linarith : (0:ℝ) ≤ t), pow_pos (by linarith : (0:ℝ) < t) 2, pow_pos (by linarith : (0:ℝ) < t) 3]

theorem lc6_sq_le_pow4_of_one_le {t : ℝ} (ht : 1 ≤ t) : t ^ 2 ≤ t ^ 4 := by
  have : (1:ℝ) ≤ t ^ 2 := by nlinarith
  nlinarith

/-- Fixed-parameter decomposition of `E[g(x + Δ + w) - g x]`. -/
theorem lc6_decomp {x : Euc d} {g : Euc d → ℝ} (hg : ContDiff ℝ 2 g) {M0 m2 : ℝ}
    (hgb : ∀ y, ‖g y‖ ≤ M0) (hg2 : ∀ y, ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ m2)
    {Δ w : Ω → Euc d} (hΔm : Measurable Δ) (hwm : Measurable w) {σ2 h C1 : ℝ}
    (hΔ1 : ∀ i, ∫ ω, Δ ω i ∂P = 0)
    (hΔ2 : ∀ i j, ∫ ω, Δ ω i * Δ ω j ∂P = if i = j then σ2 else 0)
    (hΔ4 : Integrable (fun ω => ‖Δ ω‖ ^ 4) P)
    {s : Ω → ℝ} (hs1 : ∀ ω, 1 ≤ s ω) (hsm : Measurable s) (hs4 : Integrable (fun ω => s ω ^ 4) P)
    (hw : ∀ ω, ‖w ω‖ ≤ h * C1 * s ω) (hh : 0 ≤ h) (hC1 : 0 ≤ C1) :
    Integrable (fun ω => fderiv ℝ g x (w ω)) P ∧
    Integrable (fun ω => (1 / 2) * (fderiv ℝ (fderiv ℝ g) x (Δ ω + w ω) (Δ ω + w ω) -
      fderiv ℝ (fderiv ℝ g) x (Δ ω) (Δ ω))) P ∧
    Integrable (fun ω => g (x + (Δ ω + w ω)) - g x - fderiv ℝ g x (Δ ω + w ω) -
      (1 / 2) * fderiv ℝ (fderiv ℝ g) x (Δ ω + w ω) (Δ ω + w ω)) P ∧
    ∫ ω, (g (x + (Δ ω + w ω)) - g x) ∂P =
      ∫ ω, fderiv ℝ g x (w ω) ∂P +
      (1 / 2) * σ2 * ∑ i, fderiv ℝ (fderiv ℝ g) x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) +
      ∫ ω, (1 / 2) * (fderiv ℝ (fderiv ℝ g) x (Δ ω + w ω) (Δ ω + w ω) -
        fderiv ℝ (fderiv ℝ g) x (Δ ω) (Δ ω)) ∂P +
      ∫ ω, (g (x + (Δ ω + w ω)) - g x - fderiv ℝ g x (Δ ω + w ω) -
        (1 / 2) * fderiv ℝ (fderiv ℝ g) x (Δ ω + w ω) (Δ ω + w ω)) ∂P := by
  set ξ : Euc d →L[ℝ] ℝ := fderiv ℝ g x with hξ
  set H : Euc d →L[ℝ] Euc d →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ g) x with hH
  have hm2 : 0 ≤ m2 := by
    have h' := norm_nonneg (fderiv ℝ (fderiv ℝ g) x)
    exact h'.trans (hg2 x)
  have hM0 : 0 ≤ M0 := (norm_nonneg _).trans (hgb x)
  have hHn : ‖H‖ ≤ m2 := hg2 x
  have hHab : ∀ a b : Euc d, |H a b| ≤ m2 * ‖a‖ * ‖b‖ := by
    intro a b
    have := ContinuousLinearMap.le_opNorm₂ H a b
    rw [Real.norm_eq_abs] at this
    exact this.trans (by gcongr)
  have hz : Measurable (fun ω => Δ ω + w ω) := hΔm.add hwm
  have hg1 : Continuous g := hg.continuous
  set Pk : Ω → ℝ := fun ω => 1 + ‖Δ ω‖ ^ 4 + s ω ^ 4 with hPk
  have hP1 : ∀ ω, 1 ≤ Pk ω := fun ω => by
    have := pow_nonneg (norm_nonneg (Δ ω)) 4; have := pow_nonneg (le_trans zero_le_one (hs1 ω)) 4
    simp only [hPk]; linarith
  have hΔle : ∀ ω, ‖Δ ω‖ ≤ Pk ω := fun ω => by
    have := lc6_le_one_add_pow4 (norm_nonneg (Δ ω)); have := pow_nonneg (le_trans zero_le_one (hs1 ω)) 4; simp only [hPk]; linarith
  have hΔ2le : ∀ ω, ‖Δ ω‖ ^ 2 ≤ Pk ω := fun ω => by
    have := lc6_sq_le_one_add_pow4 (t := ‖Δ ω‖); have := pow_nonneg (le_trans zero_le_one (hs1 ω)) 4; simp only [hPk]; linarith
  have hsle : ∀ ω, s ω ≤ Pk ω := fun ω => by
    have := lc6_le_pow4_of_one_le (hs1 ω); have := pow_nonneg (norm_nonneg (Δ ω)) 4; simp only [hPk]; linarith
  have hs2le : ∀ ω, s ω ^ 2 ≤ Pk ω := fun ω => by
    have := lc6_sq_le_pow4_of_one_le (hs1 ω); have := pow_nonneg (norm_nonneg (Δ ω)) 4; simp only [hPk]; linarith
  have hwle : ∀ ω, ‖w ω‖ ≤ h * C1 * Pk ω := fun ω =>
    (hw ω).trans (mul_le_mul_of_nonneg_left (hsle ω) (mul_nonneg hh hC1))
  have hw2le : ∀ ω, ‖w ω‖ ^ 2 ≤ (h * C1) ^ 2 * Pk ω := fun ω => by
    have h1 : ‖w ω‖ ^ 2 ≤ (h * C1 * s ω) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hw ω) 2
    calc ‖w ω‖ ^ 2 ≤ (h * C1 * s ω) ^ 2 := h1
      _ = (h * C1) ^ 2 * s ω ^ 2 := by ring
      _ ≤ (h * C1) ^ 2 * Pk ω := mul_le_mul_of_nonneg_left (hs2le ω) (sq_nonneg _)
  have hzle : ∀ ω, ‖Δ ω + w ω‖ ^ 2 ≤ 2 * Pk ω + 2 * ((h * C1) ^ 2 * Pk ω) := fun ω => by
    have h1 := norm_add_le (Δ ω) (w ω)
    have h2 : ‖Δ ω + w ω‖ ^ 2 ≤ (‖Δ ω‖ + ‖w ω‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [hΔ2le ω, hw2le ω, sq_nonneg (‖Δ ω‖ - ‖w ω‖)]
  -- integrability of each piece
  have I1 : Integrable (fun ω => ξ (w ω)) P := by
    refine lc6_int_of_bound hΔ4 hs4 (K := ‖ξ‖ * (h * C1)) (ξ.continuous.measurable.comp hwm) fun ω => ?_
    have := ξ.le_opNorm (w ω)
    rw [Real.norm_eq_abs] at this
    calc |ξ (w ω)| ≤ ‖ξ‖ * ‖w ω‖ := this
      _ ≤ ‖ξ‖ * (h * C1 * Pk ω) := mul_le_mul_of_nonneg_left (hwle ω) (norm_nonneg _)
      _ = ‖ξ‖ * (h * C1) * Pk ω := by ring
  have I2 : Integrable (fun ω => ξ (Δ ω)) P := by
    refine lc6_int_of_bound hΔ4 hs4 (K := ‖ξ‖) (ξ.continuous.measurable.comp hΔm) fun ω => ?_
    have := ξ.le_opNorm (Δ ω)
    rw [Real.norm_eq_abs] at this
    exact this.trans (mul_le_mul_of_nonneg_left (hΔle ω) (norm_nonneg _))
  have hHm : ∀ f : Ω → Euc d, Measurable f → Measurable (fun ω => H (f ω) (f ω)) := fun f hf =>
    (show Continuous fun u : Euc d => H u u from H.continuous.clm_apply continuous_id).measurable.comp hf
  have I3 : Integrable (fun ω => (1 / 2) * H (Δ ω) (Δ ω)) P := by
    refine lc6_int_of_bound hΔ4 hs4 (K := m2) (((hHm Δ hΔm)).const_mul _) fun ω => ?_
    have := hHab (Δ ω) (Δ ω)
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    nlinarith [hΔ2le ω]
  have hΔi : ∀ i, Integrable (fun ω => Δ ω i) P := by
    intro i
    refine lc6_int_of_bound hΔ4 hs4 (K := 1) ?_ fun ω => ?_
    · exact ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.measurable.comp hΔm)
    · have := PiLp.norm_apply_le (Δ ω) i
      rw [Real.norm_eq_abs] at this
      linarith [hΔle ω]
  have hΔij : ∀ i j, Integrable (fun ω => Δ ω i * Δ ω j) P := by
    intro i j
    refine lc6_int_of_bound hΔ4 hs4 (K := 1) ?_ fun ω => ?_
    · exact (((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.measurable.comp hΔm)).mul
        ((EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous.measurable.comp hΔm)
    · have h1 := PiLp.norm_apply_le (Δ ω) i
      have h2 := PiLp.norm_apply_le (Δ ω) j
      rw [Real.norm_eq_abs] at h1 h2
      rw [abs_mul]
      nlinarith [hΔ2le ω, abs_nonneg (Δ ω i), abs_nonneg (Δ ω j), norm_nonneg (Δ ω)]
  have I4 : Integrable (fun ω => (1 / 2) * (H (Δ ω + w ω) (Δ ω + w ω) - H (Δ ω) (Δ ω))) P := by
    refine lc6_int_of_bound hΔ4 hs4 (K := m2 * (2 + (h * C1) ^ 2))
      (((hHm _ hz).sub (hHm Δ hΔm)).const_mul _) fun ω => ?_
    have h1 := hHab (Δ ω + w ω) (Δ ω + w ω)
    have h2 := hHab (Δ ω) (Δ ω)
    have h3 := hzle ω
    have h4 := hΔ2le ω
    have h5 : |H (Δ ω + w ω) (Δ ω + w ω) - H (Δ ω) (Δ ω)| ≤
        m2 * ‖Δ ω + w ω‖ * ‖Δ ω + w ω‖ + m2 * ‖Δ ω‖ * ‖Δ ω‖ := (abs_sub _ _).trans (add_le_add h1 h2)
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    have hP := hP1 ω
    have hq : 0 ≤ (h * C1) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg hm2 (sub_nonneg.2 h3), mul_nonneg hm2 (sub_nonneg.2 h4),
      mul_nonneg hm2 (mul_nonneg hq (sub_nonneg.2 hP))]
  have hTay : ∀ z : Euc d, |g (x + z) - g x - ξ z - (1 / 2) * H z z| ≤ (2 * m2) * ‖z‖ ^ 2 := by
    intro z
    refine lc6_taylor hg x z (fun s _ => ?_)
    have h1 := hg2 (x + s • z)
    have h2 := hg2 x
    have h3 := norm_sub_le (fderiv ℝ (fderiv ℝ g) (x + s • z)) (fderiv ℝ (fderiv ℝ g) x)
    linarith
  have I5 : Integrable (fun ω => g (x + (Δ ω + w ω)) - g x - ξ (Δ ω + w ω) -
      (1 / 2) * H (Δ ω + w ω) (Δ ω + w ω)) P := by
    have hΨ : Continuous fun y : Euc d => g (x + y) - g x - ξ y - (1 / 2) * H y y :=
      ((hg1.comp (continuous_const.add continuous_id)).sub continuous_const).sub ξ.continuous |>.sub
        (continuous_const.mul (H.continuous.clm_apply continuous_id))
    refine lc6_int_of_bound hΔ4 hs4 (K := 4 * m2 * (1 + (h * C1) ^ 2)) (hΨ.measurable.comp hz) fun ω => ?_
    refine (hTay _).trans ?_
    have h3 := hzle ω
    have hP := hP1 ω
    have hq : 0 ≤ (h * C1) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg hm2 (sub_nonneg.2 h3), mul_nonneg hm2 hq, mul_nonneg (mul_nonneg hm2 hq) (sub_nonneg.2 hP)]
  refine ⟨I1, I4, I5, ?_⟩
  have hsplit : (fun ω => g (x + (Δ ω + w ω)) - g x) = fun ω => ξ (w ω) + (ξ (Δ ω) +
      ((1 / 2) * H (Δ ω) (Δ ω) + ((1 / 2) * (H (Δ ω + w ω) (Δ ω + w ω) - H (Δ ω) (Δ ω)) +
        (g (x + (Δ ω + w ω)) - g x - ξ (Δ ω + w ω) - (1 / 2) * H (Δ ω + w ω) (Δ ω + w ω))))) := by
    funext ω; simp only [map_add]; ring
  have e1 := integral_add I1 (I2.add (I3.add (I4.add I5)))
  have e2 := integral_add I2 (I3.add (I4.add I5))
  have e3 := integral_add I3 (I4.add I5)
  have e4 := integral_add I4 I5
  simp only [Pi.add_apply] at e1 e2 e3
  rw [hsplit, e1, e2, e3, e4]
  have hA2 : ∫ ω, ξ (Δ ω) ∂P = 0 := by
    simp_rw [lc6_lin_expand ξ (Δ _)]
    rw [integral_finset_sum _ (fun i _ => (hΔi i).mul_const _)]
    simp [integral_mul_const, hΔ1]
  have hA3 : ∫ ω, (1 / 2) * H (Δ ω) (Δ ω) ∂P =
      (1 / 2) * σ2 * ∑ i, H (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
    simp_rw [lc6_bil_expand H (Δ _) (Δ _)]
    rw [integral_const_mul]
    have : ∀ i j, Integrable (fun ω => Δ ω i * Δ ω j *
        H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) P :=
      fun i j => (hΔij i j).mul_const _
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => this i j))]
    simp_rw [integral_finset_sum _ (fun j _ => this _ j), integral_mul_const, hΔ2]
    simp [mul_comm, mul_left_comm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hA2, hA3]
  ring

theorem lc6_sq_moment {Δ : Ω → Euc d} (hΔm : Measurable Δ) {σ2 : ℝ}
    (hΔ2 : ∀ i j, ∫ ω, Δ ω i * Δ ω j ∂P = if i = j then σ2 else 0)
    (hΔij : ∀ i j, Integrable (fun ω => Δ ω i * Δ ω j) P) :
    Integrable (fun ω => ‖Δ ω‖ ^ 2) P ∧ ∫ ω, ‖Δ ω‖ ^ 2 ∂P = d * σ2 := by
  have e : (fun ω => ‖Δ ω‖ ^ 2) = fun ω => ∑ i, Δ ω i * Δ ω i := by
    funext ω; rw [lc6_norm_sq_eq]; simp [sq]
  rw [e]
  refine ⟨integrable_finset_sum _ fun i _ => hΔij i i, ?_⟩
  rw [integral_finset_sum _ fun i _ => hΔij i i]
  simp [hΔ2]

/-- Bound for the cross-term `E3`. -/
theorem lc6_E3 {x : Euc d} {g : Euc d → ℝ} {m2 : ℝ}
    (hg2 : ∀ y, ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ m2)
    {Δ w : Ω → Euc d} (hΔm : Measurable Δ) (hwm : Measurable w) {σ2 h C1 νs : ℝ}
    (hΔ2 : ∀ i j, ∫ ω, Δ ω i * Δ ω j ∂P = if i = j then σ2 else 0)
    (hΔij : ∀ i j, Integrable (fun ω => Δ ω i * Δ ω j) P)
    {s : Ω → ℝ} (hs1 : ∀ ω, 1 ≤ s ω) (hsm : Measurable s) (hs2 : Integrable (fun ω => s ω ^ 2) P)
    (hw : ∀ ω, ‖w ω‖ ≤ h * C1 * s ω) (hh : 0 < h) (hC1 : 0 ≤ C1) (hσ0 : 0 ≤ σ2)
    (hσ : σ2 ≤ 2 * νs * h) (hνs : 0 ≤ νs) :
    |∫ ω, (1 / 2) * (fderiv ℝ (fderiv ℝ g) x (Δ ω + w ω) (Δ ω + w ω) -
        fderiv ℝ (fderiv ℝ g) x (Δ ω) (Δ ω)) ∂P| ≤
      h * ((1 / 2) * m2 * C1 * Real.sqrt h * (∫ ω, s ω ^ 2 ∂P + 2 * d * νs) +
        (1 / 2) * m2 * C1 ^ 2 * h * ∫ ω, s ω ^ 2 ∂P) := by
  set H : Euc d →L[ℝ] Euc d →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ g) x with hH
  have hm2 : 0 ≤ m2 := by
    have h' := norm_nonneg (fderiv ℝ (fderiv ℝ g) x)
    exact h'.trans (hg2 x)
  have hHab : ∀ a b : Euc d, |H a b| ≤ m2 * ‖a‖ * ‖b‖ := by
    intro a b
    have := ContinuousLinearMap.le_opNorm₂ H a b
    rw [Real.norm_eq_abs] at this
    exact this.trans (by gcongr; exact hg2 x)
  obtain ⟨hΔsq, hΔsqI⟩ := lc6_sq_moment hΔm hΔ2 hΔij
  set θ : ℝ := Real.sqrt h with hθdef
  have hθ : 0 < θ := Real.sqrt_pos.2 hh
  have hθ2 : θ ^ 2 = h := Real.sq_sqrt hh.le
  set A2 : ℝ := ∫ ω, s ω ^ 2 ∂P with hA2
  set B3 : Ω → ℝ := fun ω => m2 * h * C1 * (1 / 2) * (θ * s ω ^ 2 + ‖Δ ω‖ ^ 2 / θ) +
    (1 / 2) * m2 * (h * C1) ^ 2 * s ω ^ 2 with hB3
  have hB3i : Integrable B3 P :=
    (((hs2.const_mul θ).add (hΔsq.div_const θ)).const_mul _).add (hs2.const_mul _)
  have hpt : ∀ ω, |(1 / 2) * (H (Δ ω + w ω) (Δ ω + w ω) - H (Δ ω) (Δ ω))| ≤ B3 ω := by
    intro ω
    have hid : H (Δ ω + w ω) (Δ ω + w ω) - H (Δ ω) (Δ ω) =
        H (Δ ω) (w ω) + H (w ω) (Δ ω) + H (w ω) (w ω) := by simp only [map_add, add_apply]; ring
    have h1 := hHab (Δ ω) (w ω)
    have h2 := hHab (w ω) (Δ ω)
    have h3 := hHab (w ω) (w ω)
    have hb := hw ω
    have hb0 := norm_nonneg (w ω)
    have ha0 := norm_nonneg (Δ ω)
    have hs0 := hs1 ω
    set a := ‖Δ ω‖ with ha
    set b := ‖w ω‖ with hbb
    set W := h * C1 * s ω with hW
    have hW0 : 0 ≤ W := by positivity
    have hab : |H (Δ ω) (w ω) + H (w ω) (Δ ω) + H (w ω) (w ω)| ≤ 2 * m2 * a * b + m2 * b * b := by
      refine ((abs_add_three _ _ _)).trans ?_
      nlinarith
    rw [hid, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    have hkey : 2 * (s ω * a) ≤ θ * s ω ^ 2 + a ^ 2 / θ := by
      rw [← sub_nonneg]
      have : θ * s ω ^ 2 + a ^ 2 / θ - 2 * (s ω * a) = (θ * s ω - a) ^ 2 / θ := by
        field_simp; ring
      rw [this]; positivity
    have hh1 : 0 ≤ h * C1 := by positivity
    have hb2 : b * b ≤ W * W := mul_self_le_mul_self hb0 hb
    have hab2 : a * b ≤ a * W := mul_le_mul_of_nonneg_left hb ha0
    simp only [hB3]
    have e1 : a * W = h * C1 * (s ω * a) := by simp only [hW]; ring
    have e2 : W * W = (h * C1) ^ 2 * s ω ^ 2 := by simp only [hW]; ring
    nlinarith [mul_nonneg hm2 hh1, mul_le_mul_of_nonneg_left hkey (mul_nonneg hm2 hh1),
      mul_le_mul_of_nonneg_left hb2 hm2, mul_le_mul_of_nonneg_left hab2 hm2]
  have hint : ∫ ω, B3 ω ∂P = m2 * h * C1 * (1 / 2) * (θ * A2 + (d * σ2) / θ) +
      (1 / 2) * m2 * (h * C1) ^ 2 * A2 := by
    have i1 : Integrable (fun ω => θ * s ω ^ 2) P := hs2.const_mul θ
    have i2 : Integrable (fun ω => ‖Δ ω‖ ^ 2 / θ) P := hΔsq.div_const θ
    have i3 : Integrable (fun ω => θ * s ω ^ 2 + ‖Δ ω‖ ^ 2 / θ) P := i1.add i2
    have i4 : Integrable (fun ω => m2 * h * C1 * (1 / 2) * (θ * s ω ^ 2 + ‖Δ ω‖ ^ 2 / θ)) P :=
      i3.const_mul _
    have i5 : Integrable (fun ω => (1 / 2) * m2 * (h * C1) ^ 2 * s ω ^ 2) P := hs2.const_mul _
    simp only [hB3]
    rw [integral_add i4 i5, integral_const_mul, integral_const_mul, integral_add i1 i2,
      integral_const_mul, integral_div, hΔsqI]
  have hdσ : (d * σ2) / θ ≤ 2 * d * νs * θ := by
    rw [div_le_iff₀ hθ]
    have h1 : d * σ2 ≤ d * (2 * νs * h) := mul_le_mul_of_nonneg_left hσ (by positivity)
    have h2 : 2 * d * νs * θ * θ = d * (2 * νs * h) := by rw [← hθ2]; ring
    linarith
  calc |∫ ω, (1 / 2) * (H (Δ ω + w ω) (Δ ω + w ω) - H (Δ ω) (Δ ω)) ∂P|
      ≤ ∫ ω, |(1 / 2) * (H (Δ ω + w ω) (Δ ω + w ω) - H (Δ ω) (Δ ω))| ∂P := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun ω => (1 / 2) * (H (Δ ω + w ω) (Δ ω + w ω) - H (Δ ω) (Δ ω)))
    _ ≤ ∫ ω, B3 ω ∂P := integral_mono_of_nonneg (Eventually.of_forall fun ω => abs_nonneg _) hB3i
        (Eventually.of_forall hpt)
    _ = m2 * h * C1 * (1 / 2) * (θ * A2 + (d * σ2) / θ) + (1 / 2) * m2 * (h * C1) ^ 2 * A2 := hint
    _ ≤ h * ((1 / 2) * m2 * C1 * θ * (A2 + 2 * d * νs) + (1 / 2) * m2 * C1 ^ 2 * h * A2) := by
        have hA2 : 0 ≤ A2 := integral_nonneg fun ω => sq_nonneg _
        have hc : 0 ≤ m2 * h * C1 * (1 / 2) := by positivity
        have := mul_le_mul_of_nonneg_left hdσ hc
        nlinarith [this]

/-- Bound for the Taylor remainder term `E4`. -/
theorem lc6_E4 {x : Euc d} {g : Euc d → ℝ} (hg : ContDiff ℝ 2 g) {m2 : ℝ}
    (hg2 : ∀ y, ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ m2)
    {Δ w : Ω → Euc d} (hΔm : Measurable Δ) (hwm : Measurable w) {σ2 h C1 ε δ : ℝ}
    (hΔ2 : ∀ i j, ∫ ω, Δ ω i * Δ ω j ∂P = if i = j then σ2 else 0)
    (hΔij : ∀ i j, Integrable (fun ω => Δ ω i * Δ ω j) P)
    (hΔ4 : Integrable (fun ω => ‖Δ ω‖ ^ 4) P) (hΔ4b : ∫ ω, ‖Δ ω‖ ^ 4 ∂P ≤ 3 * d ^ 2 * σ2 ^ 2)
    {s : Ω → ℝ} (hs1 : ∀ ω, 1 ≤ s ω) (hsm : Measurable s) (hs4 : Integrable (fun ω => s ω ^ 4) P)
    (hw : ∀ ω, ‖w ω‖ ≤ h * C1 * s ω) (hh : 0 ≤ h) (hC1 : 0 ≤ C1)
    (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hmod : ∀ y, ‖y - x‖ < δ → ‖fderiv ℝ (fderiv ℝ g) y - fderiv ℝ (fderiv ℝ g) x‖ ≤ ε) :
    |∫ ω, (g (x + (Δ ω + w ω)) - g x - fderiv ℝ g x (Δ ω + w ω) -
        (1 / 2) * fderiv ℝ (fderiv ℝ g) x (Δ ω + w ω) (Δ ω + w ω)) ∂P| ≤
      ε * (2 * (d * σ2) + 2 * (h * C1) ^ 2 * ∫ ω, s ω ^ 2 ∂P) +
        (2 * m2 / δ ^ 2) * (8 * (3 * d ^ 2 * σ2 ^ 2) + 8 * (h * C1) ^ 4 * ∫ ω, s ω ^ 4 ∂P) := by
  set ξ : Euc d →L[ℝ] ℝ := fderiv ℝ g x with hξ
  set H : Euc d →L[ℝ] Euc d →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ g) x with hH
  have hm2 : 0 ≤ m2 := by
    have h' := norm_nonneg (fderiv ℝ (fderiv ℝ g) x)
    exact h'.trans (hg2 x)
  obtain ⟨hΔsq, hΔsqI⟩ := lc6_sq_moment hΔm hΔ2 hΔij
  have hs2 : Integrable (fun ω => s ω ^ 2) P := by
    refine lc6_int_of_bound hΔ4 hs4 (K := 1) (hsm.pow_const 2) fun ω => ?_
    have := lc6_sq_le_pow4_of_one_le (hs1 ω)
    have := pow_nonneg (norm_nonneg (Δ ω)) 4
    rw [abs_of_nonneg (sq_nonneg _)]; linarith
  set B4 : Ω → ℝ := fun ω => ε * (2 * ‖Δ ω‖ ^ 2 + 2 * ((h * C1) ^ 2 * s ω ^ 2)) +
    (2 * m2 / δ ^ 2) * (8 * (‖Δ ω‖ ^ 4 + (h * C1) ^ 4 * s ω ^ 4)) with hB4
  have i1 : Integrable (fun ω => 2 * ‖Δ ω‖ ^ 2 + 2 * ((h * C1) ^ 2 * s ω ^ 2)) P :=
    (hΔsq.const_mul 2).add ((hs2.const_mul _).const_mul 2)
  have i2 : Integrable (fun ω => ‖Δ ω‖ ^ 4 + (h * C1) ^ 4 * s ω ^ 4) P :=
    hΔ4.add (hs4.const_mul _)
  have hB4i : Integrable B4 P := (i1.const_mul ε).add ((i2.const_mul 8).const_mul _)
  have hpt : ∀ ω, |g (x + (Δ ω + w ω)) - g x - ξ (Δ ω + w ω) - (1 / 2) * H (Δ ω + w ω) (Δ ω + w ω)| ≤ B4 ω := by
    intro ω
    set z := Δ ω + w ω with hz
    have hz2 : ‖z‖ ^ 2 ≤ 2 * ‖Δ ω‖ ^ 2 + 2 * ((h * C1) ^ 2 * s ω ^ 2) := by
      have h1 := norm_add_le (Δ ω) (w ω)
      have h2 : ‖z‖ ^ 2 ≤ (‖Δ ω‖ + ‖w ω‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      have h3 : ‖w ω‖ ^ 2 ≤ (h * C1 * s ω) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hw ω) 2
      nlinarith [sq_nonneg (‖Δ ω‖ - ‖w ω‖)]
    have hz4 : ‖z‖ ^ 4 ≤ 8 * (‖Δ ω‖ ^ 4 + (h * C1) ^ 4 * s ω ^ 4) := by
      have h1 := norm_add_le (Δ ω) (w ω)
      have h2 : ‖z‖ ^ 4 ≤ (‖Δ ω‖ + ‖w ω‖) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) h1 4
      have h3 : ‖w ω‖ ^ 4 ≤ (h * C1 * s ω) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) (hw ω) 4
      have h4 := lc6_pow4_add (norm_nonneg (Δ ω)) (norm_nonneg (w ω))
      have h5 : (h * C1 * s ω) ^ 4 = (h * C1) ^ 4 * s ω ^ 4 := by ring
      nlinarith
    have hbound : |g (x + z) - g x - ξ z - (1 / 2) * H z z| ≤ ε * ‖z‖ ^ 2 + (2 * m2 / δ ^ 2) * ‖z‖ ^ 4 := by
      by_cases hzδ : ‖z‖ < δ
      · refine (lc6_taylor hg x z (fun t ht => hmod _ ?_)).trans ?_
        · simp only [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1]
          calc t * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
            _ < δ := by linarith
        · have : 0 ≤ (2 * m2 / δ ^ 2) * ‖z‖ ^ 4 := by positivity
          linarith
      · push_neg at hzδ
        have hT : |g (x + z) - g x - ξ z - (1 / 2) * H z z| ≤ (2 * m2) * ‖z‖ ^ 2 := by
          refine lc6_taylor hg x z (fun t ht => ?_)
          have h1 := hg2 (x + t • z)
          have h2 := hg2 x
          have h3 := norm_sub_le (fderiv ℝ (fderiv ℝ g) (x + t • z)) (fderiv ℝ (fderiv ℝ g) x)
          linarith
        refine hT.trans ?_
        have hq : δ ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ hδ.le hzδ 2
        have hq4 : ‖z‖ ^ 2 ≤ ‖z‖ ^ 4 / δ ^ 2 := by
          rw [le_div_iff₀ (by positivity)]
          nlinarith [sq_nonneg ‖z‖]
        have : 0 ≤ ε * ‖z‖ ^ 2 := by positivity
        calc (2 * m2) * ‖z‖ ^ 2 ≤ (2 * m2) * (‖z‖ ^ 4 / δ ^ 2) := mul_le_mul_of_nonneg_left hq4 (by positivity)
          _ = (2 * m2 / δ ^ 2) * ‖z‖ ^ 4 := by ring
          _ ≤ _ := by linarith
    refine hbound.trans ?_
    simp only [hB4]
    have := mul_le_mul_of_nonneg_left hz2 hε
    have := mul_le_mul_of_nonneg_left hz4 (by positivity : 0 ≤ 2 * m2 / δ ^ 2)
    linarith
  have hint : ∫ ω, B4 ω ∂P = ε * (2 * (d * σ2) + 2 * (h * C1) ^ 2 * ∫ ω, s ω ^ 2 ∂P) +
      (2 * m2 / δ ^ 2) * (8 * (∫ ω, ‖Δ ω‖ ^ 4 ∂P + (h * C1) ^ 4 * ∫ ω, s ω ^ 4 ∂P)) := by
    simp only [hB4]
    rw [integral_add (i1.const_mul ε) ((i2.const_mul 8).const_mul _), integral_const_mul,
      integral_const_mul, integral_add (hΔsq.const_mul 2) ((hs2.const_mul _).const_mul 2),
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_add hΔ4 (hs4.const_mul _), integral_const_mul, hΔsqI]
    ring
  calc _ ≤ ∫ ω, |g (x + (Δ ω + w ω)) - g x - ξ (Δ ω + w ω) - (1 / 2) * H (Δ ω + w ω) (Δ ω + w ω)| ∂P := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun ω => g (x + (Δ ω + w ω)) - g x - ξ (Δ ω + w ω) - (1 / 2) * H (Δ ω + w ω) (Δ ω + w ω))
    _ ≤ ∫ ω, B4 ω ∂P := integral_mono_of_nonneg (Eventually.of_forall fun ω => abs_nonneg _) hB4i
        (Eventually.of_forall hpt)
    _ = _ := hint
    _ ≤ _ := by
        have h8 : 0 ≤ 2 * m2 / δ ^ 2 := by positivity
        have := mul_le_mul_of_nonneg_left (add_le_add_right hΔ4b ((h * C1) ^ 4 * ∫ ω, s ω ^ 4 ∂P))
          (mul_nonneg h8 (by norm_num : (0:ℝ) ≤ 8))
        nlinarith [this]

theorem lc6_Delta_ij_int {Δ : Ω → Euc d} (hΔm : Measurable Δ)
    (hΔ4 : Integrable (fun ω => ‖Δ ω‖ ^ 4) P) (i j : Fin d) :
    Integrable (fun ω => Δ ω i * Δ ω j) P := by
  refine lc6_int_of_bound hΔ4 (s := fun _ => (1 : ℝ)) (integrable_const _) (K := 1) ?_ fun ω => ?_
  · exact (((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.measurable.comp hΔm)).mul
        ((EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous.measurable.comp hΔm)
  · have h1 := PiLp.norm_apply_le (Δ ω) i
    have h2 := PiLp.norm_apply_le (Δ ω) j
    rw [Real.norm_eq_abs] at h1 h2
    rw [abs_mul]
    have := lc6_sq_le_one_add_pow4 (t := ‖Δ ω‖)
    nlinarith [abs_nonneg (Δ ω i), abs_nonneg (Δ ω j), norm_nonneg (Δ ω)]

theorem lc6_s_int {s : Ω → ℝ} (hs1 : ∀ ω, 1 ≤ s ω) (hsm : Measurable s)
    (hs4 : Integrable (fun ω => s ω ^ 4) P) : Integrable s P := by
  refine hs4.mono' hsm.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (by linarith [hs1 ω])]
  exact lc6_le_pow4_of_one_le (hs1 ω)

theorem lc6_tendsto_clm_apply {X E F : Type*} {ℓ : Filter X} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {a : X → E →L[ℝ] F} {A : E →L[ℝ] F}
    {b : X → E} {B : E} (ha : Tendsto a ℓ (𝓝 A)) (hb : Tendsto b ℓ (𝓝 B)) :
    Tendsto (fun p => a p (b p)) ℓ (𝓝 (A B)) :=
  ((continuous_fst.clm_apply continuous_snd).tendsto (A, B)).comp (ha.prodMk_nhds hb)

set_option maxHeartbeats 1000000 in
theorem lc6_expansion {X : Type*} {ℓ : Filter X} [ℓ.IsCountablyGenerated]
    (x : Euc d) (h σ2 : X → ℝ) (Δ w : X → Ω → Euc d) (g : X → Euc d → ℝ) {s : Ω → ℝ}
    (ξ : Euc d →L[ℝ] ℝ) (Hh : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) (β : Euc d) (ν0 : ℝ)
    {C1 m2 νs M0 : ℝ} (hm2 : 0 ≤ m2)
    (hh0 : ∀ᶠ p in ℓ, 0 < h p) (hh : Tendsto h ℓ (𝓝 0))
    (hΔm : ∀ᶠ p in ℓ, Measurable (Δ p)) (hwm : ∀ᶠ p in ℓ, Measurable (w p))
    (hΔ1 : ∀ᶠ p in ℓ, ∀ i, ∫ ω, Δ p ω i ∂P = 0)
    (hΔ2 : ∀ᶠ p in ℓ, ∀ i j, ∫ ω, Δ p ω i * Δ p ω j ∂P = if i = j then σ2 p else 0)
    (hΔ4 : ∀ᶠ p in ℓ, Integrable (fun ω => ‖Δ p ω‖ ^ 4) P ∧
      ∫ ω, ‖Δ p ω‖ ^ 4 ∂P ≤ 3 * d ^ 2 * σ2 p ^ 2)
    (hσ : ∀ᶠ p in ℓ, 0 ≤ σ2 p ∧ σ2 p ≤ 2 * νs * h p) (hνs : 0 ≤ νs)
    (hσlim : Tendsto (fun p => σ2 p / h p) ℓ (𝓝 (2 * ν0)))
    (hs1 : ∀ ω, 1 ≤ s ω) (hsm : Measurable s) (hs4 : Integrable (fun ω => s ω ^ 4) P)
    (hw : ∀ᶠ p in ℓ, ∀ ω, ‖w p ω‖ ≤ h p * C1 * s ω) (hC1 : 0 ≤ C1)
    (hwlim : ∀ ω, Tendsto (fun p => (h p)⁻¹ • w p ω) ℓ (𝓝 β))
    (hg : ∀ᶠ p in ℓ, ContDiff ℝ 2 (g p)) (hgb : ∀ᶠ p in ℓ, ∀ y, ‖g p y‖ ≤ M0)
    (hg2 : ∀ᶠ p in ℓ, ∀ y, ‖fderiv ℝ (fderiv ℝ (g p)) y‖ ≤ m2)
    (hξ : Tendsto (fun p => fderiv ℝ (g p) x) ℓ (𝓝 ξ))
    (hH : Tendsto (fun p => fderiv ℝ (fderiv ℝ (g p)) x) ℓ (𝓝 Hh))
    (hmod : ∀ ε > 0, ∃ δ > 0, ∀ᶠ p in ℓ, ∀ y, ‖y - x‖ < δ →
      ‖fderiv ℝ (fderiv ℝ (g p)) y - fderiv ℝ (fderiv ℝ (g p)) x‖ ≤ ε) :
    Tendsto (fun p => (∫ ω, (g p (x + (Δ p ω + w p ω)) - g p x) ∂P) / h p) ℓ
      (𝓝 (ξ β + ν0 * ∑ i, Hh (EuclideanSpace.single i 1) (EuclideanSpace.single i 1))) := by
  have hs1i : Integrable s P := lc6_s_int hs1 hsm hs4
  have hs2 : Integrable (fun ω => s ω ^ 2) P := by
    refine hs4.mono' (hsm.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]; exact lc6_sq_le_pow4_of_one_le (hs1 ω)
  set A2 : ℝ := ∫ ω, s ω ^ 2 ∂P with hA2
  set A4 : ℝ := ∫ ω, s ω ^ 4 ∂P with hA4
  have hA2n : 0 ≤ A2 := integral_nonneg fun ω => sq_nonneg _
  have hA4n : 0 ≤ A4 := integral_nonneg fun ω => by positivity
  -- the pointwise (in `p`) decomposition
  have hdec : ∀ᶠ p in ℓ, (∫ ω, (g p (x + (Δ p ω + w p ω)) - g p x) ∂P) / h p =
      (∫ ω, fderiv ℝ (g p) x ((h p)⁻¹ • w p ω) ∂P) +
      (1 / 2) * (σ2 p / h p) * ∑ i, fderiv ℝ (fderiv ℝ (g p)) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single i 1) +
      (∫ ω, (1 / 2) * (fderiv ℝ (fderiv ℝ (g p)) x (Δ p ω + w p ω) (Δ p ω + w p ω) -
        fderiv ℝ (fderiv ℝ (g p)) x (Δ p ω) (Δ p ω)) ∂P) / h p +
      (∫ ω, (g p (x + (Δ p ω + w p ω)) - g p x - fderiv ℝ (g p) x (Δ p ω + w p ω) -
        (1 / 2) * fderiv ℝ (fderiv ℝ (g p)) x (Δ p ω + w p ω) (Δ p ω + w p ω)) ∂P) / h p := by
    filter_upwards [hh0, hΔ1, hΔ2, hΔ4, hσ, hw, hΔm, hwm, hg, hgb, hg2] with p hp h1 h2 h4 hs hwp hΔmp hwmp hgp hgbp hg2p
    obtain ⟨-, -, -, hEq⟩ := lc6_decomp hgp hgbp hg2p hΔmp hwmp h1 h2 h4.1 hs1 hsm
      hs4 hwp hp.le hC1
    rw [hEq]
    have e : ∫ ω, fderiv ℝ (g p) x ((h p)⁻¹ • w p ω) ∂P = (h p)⁻¹ * ∫ ω, fderiv ℝ (g p) x (w p ω) ∂P := by
      simp only [map_smul, smul_eq_mul]
      exact integral_const_mul _ _
    rw [e]
    field_simp
  -- (a) the drift term
  have hTa : Tendsto (fun p => ∫ ω, fderiv ℝ (g p) x ((h p)⁻¹ • w p ω) ∂P) ℓ (𝓝 (ξ β)) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := P) (l := ℓ)
      (F := fun p ω => fderiv ℝ (g p) x ((h p)⁻¹ • w p ω)) (f := fun _ => ξ β)
      (fun ω => ((‖ξ‖ + 1) * C1) * s ω) ?_ ?_ ?_ ?_
    · simpa using this
    · filter_upwards [hwm] with p hwmp
      exact (Measurable.aestronglyMeasurable (by
          exact (fderiv ℝ (g p) x).continuous.measurable.comp (hwmp.const_smul ((h p)⁻¹))))
    · filter_upwards [hh0, hw, hξ.norm.eventually (gt_mem_nhds (lt_add_one ‖ξ‖))] with p hp hwp hxp
      refine Eventually.of_forall fun ω => ?_
      have h1 := (fderiv ℝ (g p) x).le_opNorm ((h p)⁻¹ • w p ω)
      rw [Real.norm_eq_abs] at h1 ⊢
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hp.le)] at h1
      have h2 : (h p)⁻¹ * ‖w p ω‖ ≤ C1 * s ω := by
        rw [inv_mul_le_iff₀ hp]; nlinarith [hwp ω]
      have hs0 : 0 ≤ s ω := by linarith [hs1 ω]
      calc _ ≤ ‖fderiv ℝ (g p) x‖ * ((h p)⁻¹ * ‖w p ω‖) := h1
        _ ≤ (‖ξ‖ + 1) * (C1 * s ω) := by
            gcongr
        _ = _ := by ring
    · exact hs1i.const_mul _
    · exact Eventually.of_forall fun ω => (lc6_tendsto_clm_apply hξ (hwlim ω))
  -- (b) the diffusion term
  have hTb : Tendsto (fun p => (1 / 2) * (σ2 p / h p) * ∑ i, fderiv ℝ (fderiv ℝ (g p)) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) ℓ
      (𝓝 (ν0 * ∑ i, Hh (EuclideanSpace.single i 1) (EuclideanSpace.single i 1))) := by
    have hsum : Tendsto (fun p => ∑ i, fderiv ℝ (fderiv ℝ (g p)) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single i 1)) ℓ
        (𝓝 (∑ i, Hh (EuclideanSpace.single i 1) (EuclideanSpace.single i 1))) :=
      tendsto_finset_sum _ fun i _ =>
        lc6_tendsto_clm_apply (lc6_tendsto_clm_apply hH tendsto_const_nhds) tendsto_const_nhds
    have := (hσlim.const_mul (1 / 2)).mul hsum
    convert this using 2
    ring
  -- (c) the cross term
  have hΔij : ∀ᶠ p in ℓ, ∀ i j, Integrable (fun ω => Δ p ω i * Δ p ω j) P := by
    filter_upwards [hΔ4, hΔm] with p h4 hΔmp i j using lc6_Delta_ij_int hΔmp h4.1 i j
  have hTc : Tendsto (fun p => (∫ ω, (1 / 2) * (fderiv ℝ (fderiv ℝ (g p)) x (Δ p ω + w p ω)
      (Δ p ω + w p ω) - fderiv ℝ (fderiv ℝ (g p)) x (Δ p ω) (Δ p ω)) ∂P) / h p) ℓ (𝓝 0) := by
    set φ : ℝ → ℝ := fun t => (1 / 2) * m2 * C1 * Real.sqrt t * (A2 + 2 * d * νs) +
      (1 / 2) * m2 * C1 ^ 2 * t * A2 with hφ
    have hφc : Continuous φ := by
      simp only [hφ]; fun_prop
    have hφ0 : Tendsto φ (𝓝 0) (𝓝 0) := by simpa [hφ] using hφc.tendsto 0
    refine squeeze_zero_norm' ?_ (hφ0.comp hh)
    filter_upwards [hh0, hΔ2, hσ, hw, hΔij, hΔm, hwm, hg2] with p hp h2 hs hwp hij hΔmp hwmp hg2p
    have := lc6_E3 (x := x) hg2p hΔmp hwmp h2 hij hs1 hsm hs2 hwp hp hC1 hs.1 hs.2 hνs
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hp, div_le_iff₀ hp]
    refine this.trans (le_of_eq ?_)
    simp only [hφ, Function.comp]
    ring
  -- (d) the Taylor remainder
  have hTd : Tendsto (fun p => (∫ ω, (g p (x + (Δ p ω + w p ω)) - g p x -
      fderiv ℝ (g p) x (Δ p ω + w p ω) - (1 / 2) * fderiv ℝ (fderiv ℝ (g p)) x (Δ p ω + w p ω)
        (Δ p ω + w p ω)) ∂P) / h p) ℓ (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    set K0 : ℝ := 4 * d * νs + 2 * C1 ^ 2 * A2 + 1 with hK0
    have hK0p : 0 < K0 := by positivity
    set ε : ℝ := η / (2 * K0) with hε
    have hεp : 0 < ε := by positivity
    obtain ⟨δ, hδ, hmodp⟩ := hmod ε hεp
    set φ4 : ℝ → ℝ := fun t => (2 * m2 / δ ^ 2) * (96 * d ^ 2 * νs ^ 2 * t + 8 * t ^ 3 * C1 ^ 4 * A4)
      with hφ4def
    have hφ4 : Tendsto φ4 (𝓝 0) (𝓝 0) := by
      have : Continuous φ4 := by simp only [hφ4def]; fun_prop
      simpa [hφ4def] using this.tendsto 0
    filter_upwards [hh0, hΔ2, hΔ4, hσ, hw, hmodp, (hφ4.comp hh).eventually (gt_mem_nhds (half_pos hη)),
      hh.eventually (gt_mem_nhds one_pos), hΔij, hΔm, hwm, hg, hg2] with p hp h2 h4 hs hwp hm hφ hh1 hij hΔmp hwmp hgp hg2p
    have hE := lc6_E4 (x := x) hgp hg2p hΔmp hwmp h2 hij h4.1 h4.2 hs1 hsm hs4 hwp hp.le
      hC1 hεp.le hδ hm
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hp, div_lt_iff₀ hp]
    refine lt_of_le_of_lt hE ?_
    have hσ0 := hs.1
    have hσh := hs.2
    have e1 : 2 * (d * σ2 p) ≤ 4 * d * νs * h p := by nlinarith [hσh, (Nat.cast_nonneg d : (0:ℝ) ≤ d)]
    have e2 : (h p * C1) ^ 2 * A2 ≤ h p * C1 ^ 2 * A2 := by
      have : (h p) ^ 2 ≤ h p := by nlinarith
      nlinarith [mul_nonneg (sq_nonneg C1) hA2n]
    have hA : ε * (2 * (d * σ2 p) + 2 * (h p * C1) ^ 2 * A2) ≤
        h p * (ε * (4 * d * νs + 2 * C1 ^ 2 * A2)) := by
      have : 2 * (d * σ2 p) + 2 * (h p * C1) ^ 2 * A2 ≤ h p * (4 * d * νs + 2 * C1 ^ 2 * A2) := by
        nlinarith
      calc _ ≤ ε * (h p * (4 * d * νs + 2 * C1 ^ 2 * A2)) := mul_le_mul_of_nonneg_left this hεp.le
        _ = _ := by ring
    have hB : (2 * m2 / δ ^ 2) * (8 * (3 * d ^ 2 * σ2 p ^ 2) + 8 * (h p * C1) ^ 4 * A4) ≤
        h p * φ4 (h p) := by
      have hs2' : σ2 p ^ 2 ≤ (2 * νs * h p) ^ 2 := pow_le_pow_left₀ hσ0 hσh 2
      have : 8 * (3 * d ^ 2 * σ2 p ^ 2) + 8 * (h p * C1) ^ 4 * A4 ≤
          h p * (96 * d ^ 2 * νs ^ 2 * h p + 8 * h p ^ 3 * C1 ^ 4 * A4) := by
        have hd2 : (0:ℝ) ≤ (d:ℝ) ^ 2 := sq_nonneg _
        have t1 := mul_le_mul_of_nonneg_left hs2' hd2
        have e : h p * (96 * d ^ 2 * νs ^ 2 * h p + 8 * h p ^ 3 * C1 ^ 4 * A4) =
            24 * (d ^ 2 * (2 * νs * h p) ^ 2) + 8 * (h p * C1) ^ 4 * A4 := by ring
        rw [e]
        have e2 : 8 * (3 * (d:ℝ) ^ 2 * σ2 p ^ 2) = 24 * (d ^ 2 * σ2 p ^ 2) := by ring
        rw [e2]
        linarith
      simp only [hφ4def]
      calc _ ≤ (2 * m2 / δ ^ 2) * (h p * (96 * d ^ 2 * νs ^ 2 * h p + 8 * h p ^ 3 * C1 ^ 4 * A4)) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    have hKε : ε * (4 * d * νs + 2 * C1 ^ 2 * A2) ≤ η / 2 := by
      have h1 : ε * K0 = η / 2 := by simp only [hε]; field_simp
      calc _ ≤ ε * K0 := mul_le_mul_of_nonneg_left (by simp only [hK0]; linarith) hεp.le
        _ = η / 2 := h1
    have hφ' : φ4 (h p) < η / 2 := hφ
    have h1 := mul_le_mul_of_nonneg_left hKε hp.le
    have h2 := mul_lt_mul_of_pos_left hφ' hp
    linarith
  have key := (((hTa.add hTb).add hTc).add hTd).congr' (hdec.mono fun p hp => hp.symm)
  simpa using key

end Expansion
end HRS.MS.Lc
