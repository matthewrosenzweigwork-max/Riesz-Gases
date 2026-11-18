import HRS.MS.ThCorrDefs
import HRS.MS.Ker1Aux4

/-!
# TC-4 (part 1): differentiation under the integral to all orders, and the far kernel

Infrastructure for the S4.4 chain (`docs/TC_PLAN.md`, steps 4-5; packet TC-4).  Namespace `HRS.MS.TcF`.

* `tc4_conv ν f G x = ∫ f y • G (x - y) ∂ν`: the convolution of a weight `f ∈ L¹(ν)` against a kernel `G`
  with values in a Banach space.
* `tc4_hasFDerivAt_conv`, `tc4_contDiff_conv`, `tc4_norm_iteratedFDeriv_conv_le`: differentiation under the
  integral to all orders (`tc4_contDiff_integral` of the brief is `tc4_contDiff_conv`), derivatives falling on
  the kernel.  The kernel itself need not be bounded in `tc4_contDiff_conv_succ` (only its derivatives).
* `tc4_G θ d s z = (1 - θ z) * rieszKernel d s z` (the far kernel); for a cutoff `θ` (`TcCutoff`) it is
  `C^∞`, globally Lipschitz, with all derivatives of order `≥ 1` bounded (`tc4_G_*`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace HRS.MS.TcF

universe u

section Generic

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [SecondCountableTopology E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable {ν : Measure E}

/-- `H_G(x) = ∫ f(y) • G(x - y) dν(y)`. -/
def tc4_conv (ν : Measure E) (f : E → ℝ) (G : E → F) (x : E) : F := ∫ y, f y • G (x - y) ∂ν

theorem tc4_meas {f : E → ℝ} (hf : AEStronglyMeasurable f ν) {G : E → F} (hG : Continuous G)
    (x : E) : AEStronglyMeasurable (fun y => f y • G (x - y)) ν :=
  hf.smul (hG.comp (continuous_const.sub continuous_id)).aestronglyMeasurable

theorem tc4_hasFDerivAt_conv {f : E → ℝ} (hf : Integrable f ν) {G : E → F}
    (hG : ContDiff ℝ 1 G) {A : ℝ} (hA : ∀ z, ‖fderiv ℝ G z‖ ≤ A)
    (hint : ∀ x, Integrable (fun y => f y • G (x - y)) ν) (x : E) :
    HasFDerivAt (tc4_conv ν f G) (∫ y, f y • fderiv ℝ G (x - y) ∂ν) x := by
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hcont' : Continuous (fderiv ℝ G) := hG.continuous_fderiv (by norm_num)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x y => f y • G (x - y))
    (F' := fun x y => f y • fderiv ℝ G (x - y)) (s := Set.univ) (bound := fun y => A * ‖f y‖)
    Filter.univ_mem ?_ (hint x) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x => tc4_meas hf.aestronglyMeasurable hGd.continuous x
  · exact hf.aestronglyMeasurable.smul
      (hcont'.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y x _ => ?_
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hA _) (norm_nonneg _)
  · exact hf.norm.const_mul A
  · refine Filter.Eventually.of_forall fun y x _ => ?_
    have h1 : HasFDerivAt (fun x : E => x - y) (ContinuousLinearMap.id ℝ E) x :=
      (hasFDerivAt_id x).sub_const y
    have h2 := ((hGd (x - y)).hasFDerivAt.comp x h1).const_smul (f y)
    have h3 : (fun x : E => f y • G (x - y)) = f y • G ∘ fun x => x - y := rfl
    rw [h3]
    simpa using h2

theorem tc4_fderiv_conv {f : E → ℝ} (hf : Integrable f ν) {G : E → F}
    (hG : ContDiff ℝ 1 G) {A : ℝ} (hA : ∀ z, ‖fderiv ℝ G z‖ ≤ A)
    (hint : ∀ x, Integrable (fun y => f y • G (x - y)) ν) :
    fderiv ℝ (tc4_conv ν f G) = tc4_conv ν f (fderiv ℝ G) := by
  funext x
  exact (tc4_hasFDerivAt_conv hf hG hA hint x).fderiv

theorem tc4_integrable_of_bdd {f : E → ℝ} (hf : Integrable f ν) {G : E → F} (hG : Continuous G)
    {A : ℝ} (hA : ∀ z, ‖G z‖ ≤ A) (x : E) : Integrable (fun y => f y • G (x - y)) ν := by
  refine (hf.norm.const_mul A).mono' (tc4_meas hf.aestronglyMeasurable hG x)
    (Filter.Eventually.of_forall fun y => ?_)
  show ‖f y • G (x - y)‖ ≤ A * ‖f y‖
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hA _) (norm_nonneg _)

theorem tc4_norm_conv_le {f : E → ℝ} (hf : Integrable f ν) {G : E → F} {A : ℝ}
    (hA : ∀ z, ‖G z‖ ≤ A) (x : E) : ‖tc4_conv ν f G x‖ ≤ A * ∫ y, ‖f y‖ ∂ν := by
  unfold tc4_conv
  calc ‖∫ y, f y • G (x - y) ∂ν‖ ≤ ∫ y, ‖f y • G (x - y)‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ y, A * ‖f y‖ ∂ν := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
          (hf.norm.const_mul A) (Filter.Eventually.of_forall fun y => ?_)
        show ‖f y • G (x - y)‖ ≤ A * ‖f y‖
        rw [norm_smul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hA _) (norm_nonneg _)
    _ = A * ∫ y, ‖f y‖ ∂ν := integral_const_mul _ _

/-- Differentiation under the integral to all finite orders (kernel with all derivatives of order
`0..n` bounded). -/
theorem tc4_contDiff_conv {f : E → ℝ} (hf : Integrable f ν) :
    ∀ (n : ℕ) (F : Type u) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (G : E → F),
      ContDiff ℝ n G → (∀ j ≤ n, ∃ A, ∀ z, ‖iteratedFDeriv ℝ j G z‖ ≤ A) →
      ContDiff ℝ n (tc4_conv ν f G) := by
  intro n
  induction n with
  | zero =>
    intro F _ _ _ G hG hb
    obtain ⟨A, hA⟩ := hb 0 le_rfl
    have hGc : Continuous G := by simpa using hG
    rw [Nat.cast_zero, contDiff_zero]
    refine continuous_of_dominated (bound := fun y => A * ‖f y‖)
      (fun x => tc4_meas hf.aestronglyMeasurable hGc x) (fun x => ?_) (hf.norm.const_mul A)
      (Filter.Eventually.of_forall fun y => ?_)
    · refine Filter.Eventually.of_forall fun y => ?_
      show ‖f y • G (x - y)‖ ≤ A * ‖f y‖
      rw [norm_smul, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      simpa using hA (x - y)
    · exact continuous_const.smul (hGc.comp (continuous_id.sub continuous_const))
  | succ n ih =>
    intro F _ _ _ G hG hb
    obtain ⟨A, hA⟩ := hb 1 (by omega)
    have hG1 : ContDiff ℝ 1 G := hG.of_le (by exact_mod_cast Nat.succ_pos n)
    have hA1 : ∀ z, ‖fderiv ℝ G z‖ ≤ A := fun z => by
      have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := G) (x := z) (n := 0)
      rw [norm_iteratedFDeriv_zero] at h
      rw [h]; exact hA z
    obtain ⟨A0, hA0⟩ := hb 0 (Nat.zero_le _)
    have hGc : Continuous G := hG.continuous
    have hint : ∀ x, Integrable (fun y => f y • G (x - y)) ν :=
      tc4_integrable_of_bdd hf hGc (A := A0) (fun z => by simpa using hA0 z)
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
    refine ⟨fun x => (tc4_hasFDerivAt_conv hf hG1 hA1 hint x).differentiableAt, ?_, ?_⟩
    · intro h; simp at h
    · rw [tc4_fderiv_conv hf hG1 hA1 hint]
      refine ih (E →L[ℝ] F) (fderiv ℝ G) ?_ ?_
      · exact hG.fderiv_right (by exact_mod_cast le_rfl)
      · intro j hj
        obtain ⟨B, hB⟩ := hb (j + 1) (by omega)
        refine ⟨B, fun z => ?_⟩
        rw [norm_iteratedFDeriv_fderiv]
        exact hB z

/-- Same as `tc4_contDiff_conv` for a kernel `G` that is not itself bounded (only its derivatives of
orders `1..n+1`); the integrability of `f y • G (x - y)` at every `x` is then a hypothesis. -/
theorem tc4_contDiff_conv_succ {f : E → ℝ} (hf : Integrable f ν) (n : ℕ) {G : E → F}
    (hG : ContDiff ℝ (n + 1 : ℕ) G) (hb : ∀ j, 1 ≤ j → j ≤ n + 1 → ∃ A, ∀ z, ‖iteratedFDeriv ℝ j G z‖ ≤ A)
    (hint : ∀ x, Integrable (fun y => f y • G (x - y)) ν) : ContDiff ℝ (n + 1 : ℕ) (tc4_conv ν f G) := by
  obtain ⟨A, hA⟩ := hb 1 le_rfl (by omega)
  have hG1 : ContDiff ℝ 1 G := hG.of_le (by exact_mod_cast Nat.succ_pos n)
  have hA1 : ∀ z, ‖fderiv ℝ G z‖ ≤ A := fun z => by
    have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := G) (x := z) (n := 0)
    rw [norm_iteratedFDeriv_zero] at h
    rw [h]; exact hA z
  rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
  refine ⟨fun x => (tc4_hasFDerivAt_conv hf hG1 hA1 hint x).differentiableAt, ?_, ?_⟩
  · intro h; simp at h
  · rw [tc4_fderiv_conv hf hG1 hA1 hint]
    refine tc4_contDiff_conv hf n (E →L[ℝ] F) (fderiv ℝ G) ?_ ?_
    · exact hG.fderiv_right (by exact_mod_cast le_rfl)
    · intro j hj
      obtain ⟨B, hB⟩ := hb (j + 1) (by omega) (by omega)
      refine ⟨B, fun z => ?_⟩
      rw [norm_iteratedFDeriv_fderiv]
      exact hB z

/-- Norm bound of the derivatives of `H_G`: they fall on the kernel. -/
theorem tc4_norm_iteratedFDeriv_conv_le {f : E → ℝ} (hf : Integrable f ν) :
    ∀ (j : ℕ) (F : Type u) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (G : E → F),
      ContDiff ℝ (j + 1 : ℕ) G → (∀ i, 1 ≤ i → i ≤ j + 1 → ∃ A, ∀ z, ‖iteratedFDeriv ℝ i G z‖ ≤ A) →
      (∀ x, Integrable (fun y => f y • G (x - y)) ν) → ∀ B : ℝ,
      (∀ z, ‖iteratedFDeriv ℝ (j + 1) G z‖ ≤ B) →
      ∀ x, ‖iteratedFDeriv ℝ (j + 1) (tc4_conv ν f G) x‖ ≤ B * ∫ y, ‖f y‖ ∂ν := by
  intro j
  induction j with
  | zero =>
    intro F _ _ _ G hG hb hint B hB x
    obtain ⟨A, hA⟩ := hb 1 le_rfl le_rfl
    have hG1 : ContDiff ℝ 1 G := by simpa using hG
    have hA1 : ∀ z, ‖fderiv ℝ G z‖ ≤ A := fun z => by
      have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := G) (x := z) (n := 0)
      rw [norm_iteratedFDeriv_zero] at h
      rw [h]; exact hA z
    have hB1 : ∀ z, ‖fderiv ℝ G z‖ ≤ B := fun z => by
      have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := G) (x := z) (n := 0)
      rw [norm_iteratedFDeriv_zero] at h
      rw [h]; exact hB z
    rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero, tc4_fderiv_conv hf hG1 hA1 hint]
    exact tc4_norm_conv_le hf hB1 x
  | succ j ih =>
    intro F _ _ _ G hG hb hint B hB x
    obtain ⟨A, hA⟩ := hb 1 le_rfl (by omega)
    have hG1 : ContDiff ℝ 1 G := hG.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _))
    have hA1 : ∀ z, ‖fderiv ℝ G z‖ ≤ A := fun z => by
      have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := G) (x := z) (n := 0)
      rw [norm_iteratedFDeriv_zero] at h
      rw [h]; exact hA z
    rw [← norm_iteratedFDeriv_fderiv, tc4_fderiv_conv hf hG1 hA1 hint]
    have hGc' : Continuous (fderiv ℝ G) := hG1.continuous_fderiv (by norm_num)
    refine ih (E →L[ℝ] F) (fderiv ℝ G) (hG.fderiv_right (by exact_mod_cast le_rfl)) ?_
      (tc4_integrable_of_bdd hf hGc' hA1) B ?_ x
    · intro i hi1 hi2
      obtain ⟨A', hA'⟩ := hb (i + 1) (by omega) (by omega)
      refine ⟨A', fun z => ?_⟩
      rw [norm_iteratedFDeriv_fderiv]
      exact hA' z
    · intro z
      rw [norm_iteratedFDeriv_fderiv]
      exact hB z

end Generic

section Kernel

open HRS HRS.Whole HRS.MS.Ker1

variable {d : ℕ}

/-- Cutoff hypotheses: `θ ∈ C^∞`, `θ = 0` for `‖z‖ ≥ 1` (so `supp θ ⊆ B(0,1)`, compact), `θ = 1` on the
closed ball of radius `1/2`. -/
structure TcCutoff (θ : Euc d → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ θ
  zero_outside : ∀ z : Euc d, 1 ≤ ‖z‖ → θ z = 0
  one_inside : ∀ z : Euc d, ‖z‖ ≤ 1 / 2 → θ z = 1

/-- The far kernel `g_far = (1 - θ) g`. -/
def tc4_G (d : ℕ) (s : ℝ) (θ : Euc d → ℝ) (z : Euc d) : ℝ := (1 - θ z) * rieszKernel d s z

theorem TcCutoff.hasCompactSupport {θ : Euc d → ℝ} (h : TcCutoff θ) : HasCompactSupport θ := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Euc d) 1) ?_
  intro z hz
  by_contra hz'
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz'
  exact hz (h.zero_outside z hz'.le)

theorem tc4_G_contDiff {θ : Euc d → ℝ} (h : TcCutoff θ) (s : ℝ) :
    ContDiff ℝ ∞ (tc4_G d s θ) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    have hev : tc4_G d s θ =ᶠ[𝓝 (0 : Euc d)] fun _ => 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : Euc d) (show (0 : ℝ) < 1 / 2 by norm_num)] with y hy
      have : ‖y‖ ≤ 1 / 2 := by
        rw [Metric.mem_ball, dist_zero_right] at hy; exact hy.le
      simp [tc4_G, h.one_inside y this]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have h1 : ContDiffAt ℝ ∞ (fun y => 1 - θ y) z := contDiffAt_const.sub h.smooth.contDiffAt
    have h2 : ContDiffAt ℝ ∞ (rieszKernel d s) z :=
      (rieszKernel_contDiffOn (d := d) (s := s)).contDiffAt (isOpen_ne.mem_nhds hz)
    exact h1.mul h2

theorem tc4_G_eventuallyEq_outside {θ : Euc d → ℝ} (h : TcCutoff θ) (s : ℝ) {z : Euc d}
    (hz : 1 < ‖z‖) : tc4_G d s θ =ᶠ[𝓝 z] rieszKernel d s := by
  have : {y : Euc d | 1 < ‖y‖} ∈ 𝓝 z := (isOpen_lt continuous_const continuous_norm).mem_nhds hz
  filter_upwards [this] with y hy
  simp [tc4_G, h.zero_outside y (le_of_lt hy)]

theorem tc4_G_bound {θ : Euc d → ℝ} (h : TcCutoff θ) {s : ℝ} (hs0 : 0 ≤ s) {j : ℕ} (hj : 1 ≤ j) :
    ∃ A : ℝ, ∀ z : Euc d, ‖iteratedFDeriv ℝ j (tc4_G d s θ) z‖ ≤ A := by
  have hc : Continuous (iteratedFDeriv ℝ j (tc4_G d s θ)) :=
    (tc4_G_contDiff h s).continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Euc d) 1).exists_bound_of_continuousOn hc.continuousOn
  have hn : 0 < (j : ℝ) + s := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  obtain ⟨C', hC'0, hC'⟩ := ker1_E_bound (d := d) hs0 j hn
  refine ⟨max C C', fun z => ?_⟩
  by_cases hz : ‖z‖ ≤ 1
  · exact (hC z (by simpa using hz)).trans (le_max_left _ _)
  · push Not at hz
    have hz0 : z ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hz; linarith
    rw [(tc4_G_eventuallyEq_outside h s hz).iteratedFDeriv ℝ j |>.eq_of_nhds]
    refine (hC' z hz0).trans ?_
    have : ‖z‖ ^ (-s - (j : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hz.le (by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)
    calc C' * ‖z‖ ^ (-s - (j : ℝ)) ≤ C' * 1 := mul_le_mul_of_nonneg_left this hC'0
      _ = C' := mul_one _
      _ ≤ _ := le_max_right _ _

theorem tc4_G_fderiv_bound {θ : Euc d → ℝ} (h : TcCutoff θ) {s : ℝ} (hs0 : 0 ≤ s) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ z : Euc d, ‖fderiv ℝ (tc4_G d s θ) z‖ ≤ A := by
  obtain ⟨A, hA⟩ := tc4_G_bound h hs0 (j := 1) le_rfl
  refine ⟨max A 0, le_max_right _ _, fun z => ?_⟩
  have h1 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := tc4_G d s θ) (x := z) (n := 0)
  rw [norm_iteratedFDeriv_zero] at h1
  rw [h1]
  exact (hA z).trans (le_max_left _ _)

/-- `g_far` is globally Lipschitz (any constant bounding `‖D g_far‖`). -/
theorem tc4_G_lipschitz {θ : Euc d → ℝ} (h : TcCutoff θ) {s : ℝ} {A : ℝ}
    (hA : ∀ z : Euc d, ‖fderiv ℝ (tc4_G d s θ) z‖ ≤ A) (z w : Euc d) :
    |tc4_G d s θ z - tc4_G d s θ w| ≤ A * ‖z - w‖ := by
  have hd : Differentiable ℝ (tc4_G d s θ) := (tc4_G_contDiff h s).differentiable (by simp)
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := tc4_G d s θ) (s := Set.univ)
    (fun x _ => hd x) (fun x _ => hA x) convex_univ (Set.mem_univ w) (Set.mem_univ z)
  simpa [Real.norm_eq_abs] using this

end Kernel

end HRS.MS.TcF

end
