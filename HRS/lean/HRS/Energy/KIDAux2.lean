import HRS.Energy.KIDAux1

/-!
# KID helper file 2: the convolution `f_r = h * ρ_r` (part B of the plan in `KIDAux1`)

`convD H g k w = ∫ g(z) • D^k H (w - rep z) dz` and `iteratedFDeriv k (convL H g) = convD H g k`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open HRS HRS.PDE HRS.Uniform.Q54c

namespace HRS.KID

variable {d : ℕ}

section Conv

/-- `∫ g(z) • D^k H (w - rep z) dz`. -/
def convD (H : Euc d → ℝ) (g : Torus d → ℝ) (k : ℕ) (w : Euc d) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => Euc d) ℝ :=
  ∫ z : Torus d, g z • iteratedFDeriv ℝ k H (w - Torus.rep z)

/-- `∫ g(z) H (w - rep z) dz`. -/
def convL (H : Euc d → ℝ) (g : Torus d → ℝ) (w : Euc d) : ℝ :=
  ∫ z : Torus d, g z * H (w - Torus.rep z)

theorem convD_integrable {H : Euc d → ℝ} {g : Torus d → ℝ} (hg : Integrable g) (k : ℕ)
    (hcont : Continuous (iteratedFDeriv ℝ k H)) {L0 : ℝ}
    (hL0 : ∀ y, ‖iteratedFDeriv ℝ k H y‖ ≤ L0) (w : Euc d) :
    Integrable (fun z : Torus d => g z • iteratedFDeriv ℝ k H (w - Torus.rep z)) := by
  have hrep := measurable_torusRep d
  refine Integrable.mono' (hg.norm.mul_const L0)
    (hg.aestronglyMeasurable.smul
      (hcont.comp_aestronglyMeasurable (measurable_const.sub hrep).aestronglyMeasurable))
    (Eventually.of_forall fun z => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hL0 _) (norm_nonneg _)

theorem convD_hasFDerivAt {H : Euc d → ℝ} {g : Torus d → ℝ} (hg : Integrable g) (k : ℕ)
    (hH : ContDiff ℝ (k + 1) H) {L0 L : ℝ} (hL0 : ∀ y, ‖iteratedFDeriv ℝ k H y‖ ≤ L0)
    (hL : ∀ y, ‖iteratedFDeriv ℝ (k + 1) H y‖ ≤ L) (w : Euc d) :
    HasFDerivAt (convD H g k)
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => Euc d) ℝ) (convD H g (k + 1) w)) w := by
  have hrep := measurable_torusRep d
  have hHk : ContDiff ℝ 1 (iteratedFDeriv ℝ k H) := by
    have := hH.iteratedFDeriv_right (i := k) (m := 1) (by
      rw [add_comm])
    simpa using this
  have hdiff : Differentiable ℝ (iteratedFDeriv ℝ k H) := hHk.differentiable one_ne_zero
  have hcont : Continuous (iteratedFDeriv ℝ k H) := hHk.continuous
  have hcont' : Continuous (fderiv ℝ (iteratedFDeriv ℝ k H)) := hHk.continuous_fderiv one_ne_zero
  have hΦ : ∀ y, fderiv ℝ (iteratedFDeriv ℝ k H) y =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => Euc d) ℝ)
        (iteratedFDeriv ℝ (k + 1) H y) := by
    intro y
    rw [iteratedFDeriv_succ_eq_comp_left]
    simp
  have hmeasw : ∀ v : Euc d, AEStronglyMeasurable (fun z : Torus d => v - Torus.rep z) volume :=
    fun v => (measurable_const.sub hrep).aestronglyMeasurable
  have hmeas : ∀ v : Euc d, AEStronglyMeasurable
      (fun z : Torus d => g z • iteratedFDeriv ℝ k H (v - Torus.rep z)) volume := fun v =>
    hg.aestronglyMeasurable.smul (hcont.comp_aestronglyMeasurable (hmeasw v))
  have hint : Integrable (fun z : Torus d => g z • iteratedFDeriv ℝ k H (w - Torus.rep z)) := by
    refine Integrable.mono' (hg.norm.mul_const L0) (hmeas w) (Eventually.of_forall fun z => ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hL0 _) (norm_nonneg _)
  have hmeas' : AEStronglyMeasurable
      (fun z : Torus d => g z • fderiv ℝ (iteratedFDeriv ℝ k H) (w - Torus.rep z)) volume :=
    hg.aestronglyMeasurable.smul (hcont'.comp_aestronglyMeasurable (hmeasw w))
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun v z => g z • iteratedFDeriv ℝ k H (v - Torus.rep z))
    (F' := fun v z => g z • fderiv ℝ (iteratedFDeriv ℝ k H) (v - Torus.rep z))
    (bound := fun z => ‖g z‖ * L) (s := Set.univ) Filter.univ_mem
    (Eventually.of_forall hmeas) hint hmeas'
    (Eventually.of_forall fun z v _ => by
      rw [norm_smul, hΦ]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [LinearIsometryEquiv.norm_map]
      exact hL _)
    (hg.norm.mul_const L)
    (Eventually.of_forall fun z v _ => by
      have h1 := (hdiff (v - Torus.rep z)).hasFDerivAt.comp v ((hasFDerivAt_id v).sub_const (Torus.rep z))
      have h1' := h1.congr_fderiv (g' := fderiv ℝ (iteratedFDeriv ℝ k H) (v - Torus.rep z)) (by simp)
      exact h1'.const_smul (g z))
  have hint1 : Integrable (fun z : Torus d => g z • iteratedFDeriv ℝ (k + 1) H (w - Torus.rep z)) := by
    refine Integrable.mono' (hg.norm.mul_const L)
      (hg.aestronglyMeasurable.smul
        ((hH.continuous_iteratedFDeriv (le_refl _)).comp_aestronglyMeasurable (hmeasw w)))
      (Eventually.of_forall fun z => ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hL _) (norm_nonneg _)
  have hcomm := ContinuousLinearMap.integral_comp_comm (μ := volume)
    (E := ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => Euc d) ℝ)
    (Fₗ := Euc d →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => Euc d) ℝ)
    ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => Euc d) ℝ).toContinuousLinearEquiv :
      _ →L[ℝ] _) hint1
  have e : (∫ z : Torus d, g z • fderiv ℝ (iteratedFDeriv ℝ k H) (w - Torus.rep z)) =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => Euc d) ℝ) (convD H g (k + 1) w) := by
    unfold convD
    refine (integral_congr_ae (Eventually.of_forall fun z => ?_)).trans hcomm
    simp only [hΦ, map_smul]
    rfl
  rw [e] at key
  exact key

theorem iteratedFDeriv_convL {h : Torus d → ℝ} (hsm : Torus.IsSmooth h) {g : Torus d → ℝ}
    (hg : Integrable g) (k : ℕ) :
    iteratedFDeriv ℝ k (convL (Torus.lift h) g) = convD (Torus.lift h) g k := by
  have hck : ∀ j : ℕ, Torus.IsCk (j : WithTop ℕ∞) h := fun j =>
    ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift h) from hsm)
      (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
  have hbd : ∀ j : ℕ, ∀ y, ‖iteratedFDeriv ℝ j (Torus.lift h) y‖ ≤ Torus.cbNorm j h := fun j y =>
    HRS.KernelGrad.norm_iteratedFDeriv_le_cbNorm (hck j) le_rfl y
  have hcd : ∀ j : ℕ, ContDiff ℝ j (Torus.lift h) := fun j => hck j
  have hcdi : ∀ j : ℕ, Continuous (iteratedFDeriv ℝ j (Torus.lift h)) := fun j =>
    (hcd j).continuous_iteratedFDeriv (le_refl _)
  induction k with
  | zero =>
    funext w
    ext m
    have hint := convD_integrable (H := Torus.lift h) hg 0 (hcdi 0) (hbd 0) w
    unfold convD
    rw [ContinuousMultilinearMap.integral_apply hint]
    simp [convL, iteratedFDeriv_zero_eq_comp]
  | succ k ih =>
    funext w
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih]
    have hd := convD_hasFDerivAt (H := Torus.lift h) hg k (by exact_mod_cast hcd (k + 1)) (hbd k)
      (hbd (k + 1)) w
    rw [hd.fderiv]
    simp

theorem contDiff_convL {h : Torus d → ℝ} (hsm : Torus.IsSmooth h) {g : Torus d → ℝ}
    (hg : Integrable g) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convL (Torus.lift h) g) := by
  have hck : ∀ j : ℕ, Torus.IsCk (j : WithTop ℕ∞) h := fun j =>
    ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift h) from hsm)
      (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
  have hbd : ∀ j : ℕ, ∀ y, ‖iteratedFDeriv ℝ j (Torus.lift h) y‖ ≤ Torus.cbNorm j h := fun j y =>
    HRS.KernelGrad.norm_iteratedFDeriv_le_cbNorm (hck j) le_rfl y
  have hcd : ∀ j : ℕ, ContDiff ℝ j (Torus.lift h) := fun j => hck j
  refine contDiff_of_differentiable_iteratedFDeriv (n := ⊤) fun m _ => ?_
  rw [iteratedFDeriv_convL hsm hg m]
  intro w
  exact (convD_hasFDerivAt (H := Torus.lift h) hg m (by exact_mod_cast hcd (m + 1)) (hbd m)
    (hbd (m + 1)) w).differentiableAt

/-- Joint continuity of the derivative convolutions along a pointwise-continuous path. -/
theorem continuous_convD {h : Torus d → ℝ} (hsm : Torus.IsSmooth h) (k : ℕ) {g : ℝ → Torus d → ℝ}
    {B : ℝ} (hgb : ∀ r z, |g r z| ≤ B) (hgm : ∀ r, Measurable (g r))
    (hgc : ∀ z, Continuous fun r => g r z) :
    Continuous fun p : ℝ × Euc d => convD (Torus.lift h) (g p.1) k p.2 := by
  have hck : ∀ j : ℕ, Torus.IsCk (j : WithTop ℕ∞) h := fun j =>
    ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift h) from hsm)
      (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
  have hbd : ∀ y, ‖iteratedFDeriv ℝ k (Torus.lift h) y‖ ≤ Torus.cbNorm k h := fun y =>
    HRS.KernelGrad.norm_iteratedFDeriv_le_cbNorm (hck k) le_rfl y
  have hcdi : Continuous (iteratedFDeriv ℝ k (Torus.lift h)) :=
    (show ContDiff ℝ k (Torus.lift h) from hck k).continuous_iteratedFDeriv (le_refl _)
  have hrep := measurable_torusRep d
  unfold convD
  refine continuous_of_dominated (bound := fun _ => B * Torus.cbNorm k h) ?_ ?_ (integrable_const _) ?_
  · intro p
    exact ((hgm p.1).aestronglyMeasurable).smul
      (hcdi.comp_aestronglyMeasurable (measurable_const.sub hrep).aestronglyMeasurable)
  · intro p
    refine Eventually.of_forall fun z => ?_
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hgb _ _) (hbd _) (norm_nonneg _) ((abs_nonneg _).trans (hgb 0 z))
  · refine Eventually.of_forall fun z => ?_
    exact ((hgc z).comp continuous_fst).smul (hcdi.comp (continuous_snd.sub continuous_const))

end Conv

section Psi

/-- The test function `ψ_x(y) = h(y - x)`. -/
def psi (h : Torus d → ℝ) (x : Torus d) : Torus d → ℝ := fun y => h (y - x)

/-- `f_r(x) = ⟨ρ_r, ψ_x⟩ = ∫ h(y - x) ρ_r(y) dy` (the background potential `h * ρ_r`). -/
def fK (h : Torus d → ℝ) (ρ : ℝ → Torus d → ℝ) (r : ℝ) (x : Torus d) : ℝ :=
  pair (withDensityReal (ρ r)) (psi h x)

theorem psi_lift (h : Torus d → ℝ) (x : Torus d) :
    Torus.lift (psi h x) = fun w => Torus.lift h (w + (-Torus.rep x)) := by
  funext w
  simp only [Torus.lift, Function.comp, psi]
  congr 1
  rw [mk_add', HRS.KernelGrad.mk_neg, Torus.mk_rep]
  abel

theorem isCk_psi {h : Torus d → ℝ} {k : WithTop ℕ∞} (hh : Torus.IsCk k h) (x : Torus d) :
    Torus.IsCk k (psi h x) := by
  unfold Torus.IsCk
  rw [psi_lift]
  exact (show ContDiff ℝ k (Torus.lift h) from hh).comp (contDiff_id.add contDiff_const)

theorem rep_sub_eq (y x : Torus d) : y - x = Torus.mk (Torus.rep y + (-Torus.rep x)) := by
  rw [mk_add', HRS.KernelGrad.mk_neg, Torus.mk_rep, Torus.mk_rep]; abel

theorem grad_psi (h : Torus d → ℝ) (x y : Torus d) :
    Torus.grad (psi h x) y = Torus.grad h (y - x) := by
  rw [rep_sub_eq y x, grad_mk]
  unfold Torus.grad
  rw [psi_lift]
  unfold gradient
  rw [fderiv_comp_add_right]

theorem laplacian_comp_add_right (G : Euc d → ℝ) (a v : Euc d) :
    Laplacian.laplacian (fun w => G (w + a)) v = Laplacian.laplacian G (v + a) := by
  rw [laplacian_eq_sum_fderiv, laplacian_eq_sum_fderiv]
  have e1 : fderiv ℝ (fun w => G (w + a)) = fun w => fderiv ℝ G (w + a) := by
    funext w; exact fderiv_comp_add_right a
  rw [e1, fderiv_comp_add_right a]

theorem laplacian_psi (h : Torus d → ℝ) (x y : Torus d) :
    Torus.laplacian (psi h x) y = Torus.laplacian h (y - x) := by
  rw [rep_sub_eq y x, laplacian_mk]
  unfold Torus.laplacian
  rw [psi_lift, laplacian_comp_add_right]

end Psi

section MFf

variable {D : DynData d} {T Λ : ℝ} {ρ : ℝ → Torus d → ℝ}

theorem exists_norm_bound {E : Type*} [NormedAddCommGroup E] (g : Torus d → E) (hg : Continuous g) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖g x‖ ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
  exact ⟨max B 0, le_max_right _ _, fun x => (hB x (Set.mem_univ x)).trans (le_max_left _ _)⟩

theorem lift_even {h : Torus d → ℝ} (hev : ∀ x, h (-x) = h x) (v : Euc d) :
    Torus.lift h (-v) = Torus.lift h v := by
  simp only [Torus.lift, Function.comp]
  rw [HRS.KernelGrad.mk_neg, hev]

theorem MFctx.lift_fK (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hev : ∀ x, h (-x) = h x) {r : ℝ}
    (hr : r ∈ Icc 0 T) : Torus.lift (fK h ρ r) = convL (Torus.lift h) (ρ r) := by
  funext w
  simp only [Torus.lift, Function.comp, fK]
  rw [pair_wDR (c.dens hr)]
  unfold convL
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [psi]
  have e : h (y - Torus.mk w) = Torus.lift h (w - Torus.rep y) := by
    have h1 : Torus.lift h (w - Torus.rep y) = h (Torus.mk w - y) := by
      simp only [Torus.lift, Function.comp]
      rw [HRS.KernelGrad.mk_sub, Torus.mk_rep]
    rw [h1, ← hev (y - Torus.mk w)]
    congr 1; abel
  rw [e, mul_comm]
  rfl

theorem MFctx.contDiff_fK (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) {r : ℝ} (hr : r ∈ Icc 0 T) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift (fK h ρ r)) := by
  rw [c.lift_fK hev hr]
  exact contDiff_convL hsm ((c.cont hr).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

theorem MFctx.Gcont_pt (c : MFctx D T Λ ρ) (y : Torus d) :
    Continuous fun r => convGradConv (periodicRieszGrad d D.s) (ρ (clampT T r)) y := by
  rw [continuous_iff_continuousAt]
  intro r0
  rw [Metric.continuousAt_iff']
  intro ε hε
  filter_upwards [c.Gdiff r0 hε] with r hr
  rw [dist_eq_norm]
  exact hr y

/-- First part of the weak-form integrand with test `ψ_x`: `(β Δψ_x - ∇V·∇ψ_x) ρ_r`. -/
def wk1 (D : DynData d) (h : Torus d → ℝ) (ρ : ℝ → Torus d → ℝ) (r : ℝ) (x y : Torus d) : ℝ :=
  (D.invβ * Torus.laplacian h (y - x) - inner ℝ (Torus.grad D.V y) (Torus.grad h (y - x))) * ρ r y

/-- Second part: `ρ_r ∇ψ_x · M (∇g * ρ_r)`. -/
def wk2 (D : DynData d) (h : Torus d → ℝ) (ρ : ℝ → Torus d → ℝ) (r : ℝ) (x y : Torus d) : ℝ :=
  ρ r y * inner ℝ (Torus.grad h (y - x))
    (Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) (ρ r) y))

theorem MFctx.wkG_eq (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hh : Torus.IsCk 2 h) (x : Torus d)
    {r : ℝ} (hr : r ∈ Icc 0 T) :
    wkG D ρ (psi h x) r = (∫ y, wk1 D h ρ r x y) + ∫ y, wk2 D h ρ r x y := by
  unfold wkG
  have hψ := isCk_psi hh x
  rw [HRS.PDE.MFPairing.interactionPairing_eq_of_isCk c.hd D (ρ r)
    ((c.ck3 hr).of_le (by norm_num)) (c.dens hr).nonneg (psi h x) hψ, pair_wDR (c.dens hr)]
  simp only [laplacian_psi, grad_psi, wk1, wk2]

theorem MFctx.wk_bounds (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hh : Torus.IsCk 2 h) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r ∈ Icc 0 T, ∀ x y, |wk1 D h ρ r x y| ≤ B ∧ |wk2 D h ρ r x y| ≤ B := by
  have h1 : Torus.IsCk 1 h := hh.of_le (by norm_num)
  have hV1 : Torus.IsCk 1 D.V := c.hV.of_le (by norm_num)
  obtain ⟨B1, hB10, hB1⟩ := exists_norm_bound (fun y => Torus.laplacian h y)
    (HRS.PDE.MFApriori.continuous_laplacian_of_isCk hh)
  obtain ⟨B2, hB20, hB2⟩ := exists_norm_bound (Torus.grad h) (HRS.PDE.MFLinear.continuous_grad h1)
  obtain ⟨B3, hB30, hB3⟩ := exists_norm_bound (Torus.grad D.V) (HRS.PDE.MFLinear.continuous_grad hV1)
  obtain ⟨Kg, hKg⟩ := c.Gbound
  obtain ⟨cM, hcM0, hcM⟩ := exists_matVec_bound D.M
  have hΛ := c.Λ_nonneg
  have hβ0 := D.hβ
  have hKg0 : 0 ≤ Kg := (norm_nonneg _).trans (hKg 0 ⟨le_rfl, c.hT⟩ 0)
  refine ⟨((D.invβ * B1 + B3 * B2) * Λ) + Λ * (B2 * (cM * Kg)), by positivity, fun r hr x y => ⟨?_, ?_⟩⟩
  · unfold wk1
    rw [abs_mul]
    have hb1 : |D.invβ * Torus.laplacian h (y - x) - inner ℝ (Torus.grad D.V y) (Torus.grad h (y - x))|
        ≤ D.invβ * B1 + B3 * B2 := by
      refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_of_nonneg D.hβ]
        exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hB1 (y - x)) D.hβ
      · exact (abs_real_inner_le_norm _ _).trans (mul_le_mul (hB3 y) (hB2 _) (norm_nonneg _) hB30)
    calc _ ≤ (D.invβ * B1 + B3 * B2) * Λ := mul_le_mul hb1 (c.abs_le hr y) (abs_nonneg _) (by positivity)
      _ ≤ _ := by have : 0 ≤ Λ * (B2 * (cM * Kg)) := by positivity
                  linarith
  · unfold wk2
    rw [abs_mul]
    have hb2 : |inner ℝ (Torus.grad h (y - x)) (Torus.matVec D.M
        (convGradConv (periodicRieszGrad d D.s) (ρ r) y))| ≤ B2 * (cM * Kg) := by
      refine (abs_real_inner_le_norm _ _).trans (mul_le_mul (hB2 _) ((hcM _).trans ?_)
        (norm_nonneg _) hB20)
      exact mul_le_mul_of_nonneg_left (hKg r hr y) hcM0
    calc _ ≤ Λ * (B2 * (cM * Kg)) := mul_le_mul (c.abs_le hr y) hb2 (abs_nonneg _) hΛ
      _ ≤ _ := by have : 0 ≤ (D.invβ * B1 + B3 * B2) * Λ := by positivity
                  linarith

theorem MFctx.continuous_wk (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hh : Torus.IsCk 2 h) :
    Continuous (fun p : ℝ × Torus d =>
      (∫ y, wk1 D h ρ (clampT T p.1) p.2 y) + ∫ y, wk2 D h ρ (clampT T p.1) p.2 y) := by
  have h1 : Torus.IsCk 1 h := hh.of_le (by norm_num)
  have hV1 : Torus.IsCk 1 D.V := c.hV.of_le (by norm_num)
  obtain ⟨B, hB0, hB⟩ := c.wk_bounds hh
  obtain ⟨C, hG⟩ := KernelGradD1.goodKernel_periodicRieszGrad_of_one_le c.hd D.hs0 D.hsd
  have hlap : Continuous (Torus.laplacian h) := HRS.PDE.MFApriori.continuous_laplacian_of_isCk hh
  have hgh : Continuous (Torus.grad h) := HRS.PDE.MFLinear.continuous_grad h1
  have hgV : Continuous (Torus.grad D.V) := HRS.PDE.MFLinear.continuous_grad hV1
  have hmat : Continuous (fun v : Euc d => Torus.matVec D.M v) :=
    LinearMap.continuous_of_finiteDimensional (Matrix.toEuclideanLin D.M)
  refine Continuous.add ?_ ?_
  · refine continuous_of_dominated (bound := fun _ => B) ?_ ?_ (integrable_const _) ?_
    · intro p
      have hc := c.cont (clampT_mem c.hT p.1)
      exact (((continuous_const.mul (hlap.comp (continuous_id.sub continuous_const))).sub
        ((hgV.inner (hgh.comp (continuous_id.sub continuous_const))))).mul hc).aestronglyMeasurable
    · intro p
      exact Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact (hB _ (clampT_mem c.hT p.1) p.2 y).1
    · refine Eventually.of_forall fun y => ?_
      unfold wk1
      refine Continuous.mul (Continuous.sub (continuous_const.mul ?_) ?_) (c.pt_cont y |>.comp continuous_fst)
      · exact hlap.comp (continuous_const.sub continuous_snd)
      · exact continuous_const.inner (hgh.comp (continuous_const.sub continuous_snd))
  · refine continuous_of_dominated (bound := fun _ => B) ?_ ?_ (integrable_const _) ?_
    · intro p
      have hc := c.cont (clampT_mem c.hT p.1)
      have hGm : Measurable (convGradConv (periodicRieszGrad d D.s) (ρ (clampT T p.1))) :=
        HRS.Duality.measurable_conv hG hc.measurable
      unfold wk2
      refine (hc.measurable.mul ?_).aestronglyMeasurable
      exact Measurable.inner (hgh.measurable.comp (measurable_id.sub measurable_const))
        (hmat.measurable.comp hGm)
    · intro p
      exact Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact (hB _ (clampT_mem c.hT p.1) p.2 y).2
    · refine Eventually.of_forall fun y => ?_
      unfold wk2
      refine Continuous.mul (c.pt_cont y |>.comp continuous_fst) ?_
      exact (hgh.comp (continuous_const.sub continuous_snd)).inner
        (hmat.comp ((c.Gcont_pt y).comp continuous_fst))

theorem MFctx.continuous_ft_clamp (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hh : Torus.IsCk 2 h) :
    Continuous (fun p : ℝ × Torus d => wkG D ρ (psi h p.2) (clampT T p.1)) := by
  refine (c.continuous_wk hh).congr fun p => ?_
  exact (c.wkG_eq hh p.2 (clampT_mem c.hT p.1)).symm

theorem MFctx.hasDerivAt_fK (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hh : Torus.IsCk 2 h)
    (x : Torus d) {r : ℝ} (hr : r ∈ Ioo 0 T) :
    HasDerivAt (fun r => fK h ρ r x) (wkG D ρ (psi h x) r) r := by
  have hG : Continuous fun s : ℝ => wkG D ρ (psi h x) (clampT T s) := by
    have := (c.continuous_ft_clamp hh).comp (Continuous.prodMk_left x)
    simpa only [Function.comp_def] using this
  have hψ := isCk_psi hh x
  have hF : ∀ s ∈ Icc 0 T, fK h ρ s x = fK h ρ 0 x +
      ∫ u in (0 : ℝ)..s, wkG D ρ (psi h x) (clampT T u) := by
    intro s hs
    have h1 := weak_eq_wkG c.hmf hψ hs
    have h2 : (∫ u in Icc 0 s, wkG D ρ (psi h x) u) =
        ∫ u in (0 : ℝ)..s, wkG D ρ (psi h x) (clampT T u) := by
      rw [intervalIntegral.integral_of_le hs.1, ← integral_Icc_eq_integral_Ioc]
      refine setIntegral_congr_fun measurableSet_Icc fun u hu => ?_
      rw [clampT_of_mem ⟨hu.1, hu.2.trans hs.2⟩]
    rw [h2] at h1
    unfold fK
    linarith
  have hD : HasDerivAt (fun s => fK h ρ 0 x + ∫ u in (0 : ℝ)..s, wkG D ρ (psi h x) (clampT T u))
      (wkG D ρ (psi h x) (clampT T r)) r :=
    ((intervalIntegral.integral_hasDerivAt_right (hG.intervalIntegrable _ _)
      (hG.stronglyMeasurableAtFilter _ _) hG.continuousAt)).const_add _
  rw [clampT_of_mem ⟨hr.1.le, hr.2.le⟩] at hD
  refine hD.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hr.1 hr.2] with s hs
  exact hF s ⟨hs.1.le, hs.2.le⟩

theorem two_le_top : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  have : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
  exact this

theorem MFctx.iter_fK (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) {r : ℝ} (hr : r ∈ Icc 0 T) (j : ℕ) :
    iteratedFDeriv ℝ j (Torus.lift (fK h ρ r)) = convD (Torus.lift h) (ρ r) j := by
  rw [c.lift_fK hev hr]
  exact iteratedFDeriv_convL hsm ((c.cont hr).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)) j

theorem MFctx.continuous_iter_fK (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) (j : ℕ) :
    Continuous fun p : ℝ × Euc d =>
      iteratedFDeriv ℝ j (Torus.lift (fK h ρ (clampT T p.1))) p.2 := by
  have h1 := continuous_convD (h := h) hsm j (g := fun r z => ρ (clampT T r) z) (B := Λ)
    (fun r z => c.abs_le (clampT_mem c.hT r) z) (fun r => (c.cont (clampT_mem c.hT r)).measurable)
    (fun z => c.pt_cont z)
  refine h1.congr fun p => ?_
  rw [c.iter_fK hsm hev (clampT_mem c.hT p.1) j]

theorem MFctx.isC12Test (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) {t : ℝ} (ht : t ∈ Icc 0 T) :
    IsC12Test t (fK h ρ) (fun r x => wkG D ρ (psi h x) r) := by
  have hh : Torus.IsCk 2 h := ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift h) from hsm)
    two_le_top
  have hsub : ∀ r ∈ Icc 0 t, r ∈ Icc 0 T := fun r hr => ⟨hr.1, hr.2.trans ht.2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr
    exact ContDiff.of_le (c.contDiff_fK hsm hev (hsub r hr))
      two_le_top
  · intro j _
    have hc := (c.continuous_iter_fK hsm hev j).comp
      (show Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => ((p.1 : ℝ), p.2) from
        (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    refine hc.congr fun p => ?_
    simp only [Function.comp_apply]
    rw [clampT_of_mem (hsub _ p.1.2)]
  · intro x r hr
    exact c.hasDerivAt_fK hh x ⟨hr.1, hr.2.trans_le ht.2⟩
  · have hc := (c.continuous_ft_clamp hh).comp
      (show Continuous fun p : Set.Icc (0 : ℝ) t × Torus d => ((p.1 : ℝ), p.2) from
        (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    refine hc.congr fun p => ?_
    simp only [Function.comp_apply]
    rw [clampT_of_mem (hsub _ p.1.2)]

theorem fderiv_convL_apply {h : Torus d → ℝ} (hsm : Torus.IsSmooth h) {g : Torus d → ℝ}
    (hg : Integrable g) (w v : Euc d) :
    fderiv ℝ (convL (Torus.lift h) g) w v =
      ∫ z : Torus d, g z * fderiv ℝ (Torus.lift h) (w - Torus.rep z) v := by
  have hck : ∀ j : ℕ, Torus.IsCk (j : WithTop ℕ∞) h := fun j =>
    ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift h) from hsm)
      (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
  have hbd : ∀ j : ℕ, ∀ y, ‖iteratedFDeriv ℝ j (Torus.lift h) y‖ ≤ Torus.cbNorm j h := fun j y =>
    HRS.KernelGrad.norm_iteratedFDeriv_le_cbNorm (hck j) le_rfl y
  have hcdi : ∀ j : ℕ, Continuous (iteratedFDeriv ℝ j (Torus.lift h)) := fun j =>
    (show ContDiff ℝ j (Torus.lift h) from hck j).continuous_iteratedFDeriv (le_refl _)
  have h1 := congrArg (fun F => F w (fun _ => v)) (iteratedFDeriv_convL hsm hg 1)
  simp only [iteratedFDeriv_one_apply] at h1
  rw [h1]
  unfold convD
  rw [ContinuousMultilinearMap.integral_apply (convD_integrable hg 1 (hcdi 1) (hbd 1) w)]
  simp

theorem fderiv2_convL_apply {h : Torus d → ℝ} (hsm : Torus.IsSmooth h) {g : Torus d → ℝ}
    (hg : Integrable g) (w u v : Euc d) :
    fderiv ℝ (fderiv ℝ (convL (Torus.lift h) g)) w u v =
      ∫ z : Torus d, g z * fderiv ℝ (fderiv ℝ (Torus.lift h)) (w - Torus.rep z) u v := by
  have hck : ∀ j : ℕ, Torus.IsCk (j : WithTop ℕ∞) h := fun j =>
    ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift h) from hsm)
      (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
  have hbd : ∀ j : ℕ, ∀ y, ‖iteratedFDeriv ℝ j (Torus.lift h) y‖ ≤ Torus.cbNorm j h := fun j y =>
    HRS.KernelGrad.norm_iteratedFDeriv_le_cbNorm (hck j) le_rfl y
  have hcdi : ∀ j : ℕ, Continuous (iteratedFDeriv ℝ j (Torus.lift h)) := fun j =>
    (show ContDiff ℝ j (Torus.lift h) from hck j).continuous_iteratedFDeriv (le_refl _)
  have h1 := congrArg (fun F => F w ![u, v]) (iteratedFDeriv_convL hsm hg 2)
  simp only [iteratedFDeriv_two_apply] at h1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1
  rw [h1]
  unfold convD
  rw [ContinuousMultilinearMap.integral_apply (convD_integrable hg 2 (hcdi 2) (hbd 2) w)]
  simp [iteratedFDeriv_two_apply]

theorem inner_gradient' (f : Euc d → ℝ) (u v : Euc d) :
    inner ℝ (gradient f u) v = fderiv ℝ f u v := by
  unfold gradient
  rw [InnerProductSpace.toDual_symm_apply]

theorem grad_sub_eq (h : Torus d → ℝ) (y z : Torus d) :
    Torus.grad h (y - z) = gradient (Torus.lift h) (Torus.rep y - Torus.rep z) := by
  rw [rep_sub_eq y z, grad_mk, ← sub_eq_add_neg]

theorem laplacian_sub_eq (h : Torus d → ℝ) (y z : Torus d) :
    Torus.laplacian h (y - z) = Laplacian.laplacian (Torus.lift h) (Torus.rep y - Torus.rep z) := by
  rw [rep_sub_eq y z, laplacian_mk, ← sub_eq_add_neg]

theorem MFctx.grad_fK (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) {r : ℝ} (hr : r ∈ Icc 0 T) (y : Torus d) :
    Torus.grad (fK h ρ r) y = ∫ z : Torus d, ρ r z • Torus.grad h (y - z) := by
  have h1 : Torus.IsCk 1 h := ContDiff.of_le
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift h) from hsm)
    (by exact_mod_cast (le_top : ((1 : ℕ) : ℕ∞) ≤ ⊤))
  have hcont : Continuous fun z : Torus d => ρ r z • Torus.grad h (y - z) :=
    (c.cont hr).smul ((HRS.PDE.MFLinear.continuous_grad h1).comp (continuous_const.sub continuous_id))
  have hint : Integrable (fun z : Torus d => ρ r z • Torus.grad h (y - z)) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hg : Integrable (ρ r) := (c.cont hr).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply ext_inner_left ℝ
  intro v
  rw [← integral_inner hint v]
  have e : Torus.grad (fK h ρ r) y = gradient (Torus.lift (fK h ρ r)) (Torus.rep y) := rfl
  rw [e, c.lift_fK hev hr, real_inner_comm, inner_gradient', fderiv_convL_apply hsm hg]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [grad_sub_eq, real_inner_smul_right, real_inner_comm, inner_gradient']

theorem MFctx.lap_fK (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) {r : ℝ} (hr : r ∈ Icc 0 T) (y : Torus d) :
    Torus.laplacian (fK h ρ r) y = ∫ z : Torus d, ρ r z * Torus.laplacian h (y - z) := by
  have hg : Integrable (ρ r) := (c.cont hr).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hck : ∀ j : ℕ, Torus.IsCk (j : WithTop ℕ∞) h := fun j =>
    ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift h) from hsm)
      (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
  have hcd2 : ContDiff ℝ 2 (Torus.lift h) := hck 2
  have hc2 : ∀ j : Fin d, Continuous fun w : Euc d =>
      fderiv ℝ (fderiv ℝ (Torus.lift h)) w (EuclideanSpace.single j 1) (EuclideanSpace.single j 1) := by
    intro j
    have h2 : Continuous (fderiv ℝ (fderiv ℝ (Torus.lift h))) := by
      have := (hcd2.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)
      exact this.continuous
    exact (h2.clm_apply continuous_const).clm_apply continuous_const
  have e : Torus.laplacian (fK h ρ r) y =
      Laplacian.laplacian (Torus.lift (fK h ρ r)) (Torus.rep y) := rfl
  rw [e, c.lift_fK hev hr, laplacian_eq_sum_fderiv]
  simp_rw [laplacian_sub_eq, laplacian_eq_sum_fderiv, fderiv2_convL_apply hsm hg]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  intro j _
  have hbd2 : ∀ w, |fderiv ℝ (fderiv ℝ (Torus.lift h)) w (EuclideanSpace.single j 1)
      (EuclideanSpace.single j 1)| ≤ Torus.cbNorm 2 h := by
    intro w
    have h1 := HRS.KernelGrad.norm_iteratedFDeriv_le_cbNorm (hck 2) le_rfl w
    have h2 := (iteratedFDeriv ℝ 2 (Torus.lift h) w).le_opNorm
      ![(EuclideanSpace.single j 1 : Euc d), EuclideanSpace.single j 1]
    rw [iteratedFDeriv_two_apply] at h2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.prod_univ_two, EuclideanSpace.norm_single,
      norm_one, mul_one, Real.norm_eq_abs] at h2
    exact h2.trans h1
  have hrep := measurable_torusRep d
  refine Integrable.mono' (hg.norm.mul_const (Torus.cbNorm 2 h))
    (hg.aestronglyMeasurable.mul ((hc2 j).comp_aestronglyMeasurable
      (measurable_const.sub hrep).aestronglyMeasurable)) (Eventually.of_forall fun z => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hbd2 _) (norm_nonneg _)

/-- Generic first part of the weak-form integrand for a test function `φ`. -/
def wk1g (D : DynData d) (φ : Torus d → ℝ) (ρ : ℝ → Torus d → ℝ) (r : ℝ) (y : Torus d) : ℝ :=
  (D.invβ * Torus.laplacian φ y - inner ℝ (Torus.grad D.V y) (Torus.grad φ y)) * ρ r y

/-- Generic second part. -/
def wk2g (D : DynData d) (φ : Torus d → ℝ) (ρ : ℝ → Torus d → ℝ) (r : ℝ) (y : Torus d) : ℝ :=
  ρ r y * inner ℝ (Torus.grad φ y)
    (Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) (ρ r) y))

theorem MFctx.wkG_eq_gen (c : MFctx D T Λ ρ) {φ : Torus d → ℝ} (hφ : Torus.IsCk 2 φ)
    {r : ℝ} (hr : r ∈ Icc 0 T) :
    wkG D ρ φ r = (∫ y, wk1g D φ ρ r y) + ∫ y, wk2g D φ ρ r y := by
  unfold wkG
  rw [HRS.PDE.MFPairing.interactionPairing_eq_of_isCk c.hd D (ρ r)
    ((c.ck3 hr).of_le (by norm_num)) (c.dens hr).nonneg φ hφ, pair_wDR (c.dens hr)]
  simp only [wk1g, wk2g]

theorem MFctx.continuous_wk1_gen (c : MFctx D T Λ ρ) {P : Type*} [TopologicalSpace P]
    [FirstCountableTopology P] (p0 : P) (φ : P → Torus d → ℝ)
    (hlap : Continuous fun q : P × Torus d => Torus.laplacian (φ q.1) q.2)
    (hgr : Continuous fun q : P × Torus d => Torus.grad (φ q.1) q.2) {Bl Bg : ℝ}
    (hBl : ∀ p y, |Torus.laplacian (φ p) y| ≤ Bl) (hBg : ∀ p y, ‖Torus.grad (φ p) y‖ ≤ Bg) :
    Continuous fun q : ℝ × P => ∫ y, wk1g D (φ q.2) ρ (clampT T q.1) y := by
  have hV1 : Torus.IsCk 1 D.V := c.hV.of_le (by norm_num)
  obtain ⟨B3, hB30, hB3⟩ := exists_norm_bound (Torus.grad D.V) (HRS.PDE.MFLinear.continuous_grad hV1)
  have hΛ := c.Λ_nonneg
  have hβ0 := D.hβ
  have hBg0 : 0 ≤ Bg := (norm_nonneg _).trans (hBg p0 0)
  have hBl0 : 0 ≤ Bl := (abs_nonneg _).trans (hBl p0 0)
  have hgV : Continuous (Torus.grad D.V) := HRS.PDE.MFLinear.continuous_grad hV1
  refine continuous_of_dominated (bound := fun _ => (D.invβ * Bl + B3 * Bg) * Λ) ?_ ?_
    (integrable_const _) ?_
  · intro q
    have hc := c.cont (clampT_mem c.hT q.1)
    have gq : Continuous fun y : Torus d => ((q.2, y) : P × Torus d) :=
      continuous_const.prodMk continuous_id
    have c1 : Continuous fun y : Torus d => Torus.laplacian (φ q.2) y := by
      have := hlap.comp gq
      simpa only [Function.comp_def] using this
    have c2 : Continuous fun y : Torus d => Torus.grad (φ q.2) y := by
      have := hgr.comp gq
      simpa only [Function.comp_def] using this
    exact (((continuous_const.mul c1).sub (hgV.inner c2)).mul hc).aestronglyMeasurable
  · intro q
    refine Eventually.of_forall fun y => ?_
    unfold wk1g
    rw [Real.norm_eq_abs, abs_mul]
    have hb1 : |D.invβ * Torus.laplacian (φ q.2) y - inner ℝ (Torus.grad D.V y) (Torus.grad (φ q.2) y)|
        ≤ D.invβ * Bl + B3 * Bg := by
      refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_of_nonneg D.hβ]
        exact mul_le_mul_of_nonneg_left (hBl _ _) D.hβ
      · exact (abs_real_inner_le_norm _ _).trans (mul_le_mul (hB3 y) (hBg _ _) (norm_nonneg _) hB30)
    exact mul_le_mul hb1 (c.abs_le (clampT_mem c.hT q.1) y) (abs_nonneg _) (by positivity)
  · refine Eventually.of_forall fun y => ?_
    have gq : Continuous fun q : ℝ × P => ((q.2, y) : P × Torus d) :=
      continuous_snd.prodMk continuous_const
    have c1 : Continuous fun q : ℝ × P => Torus.laplacian (φ q.2) y := by
      have := hlap.comp gq
      simpa only [Function.comp_def] using this
    have c2 : Continuous fun q : ℝ × P => Torus.grad (φ q.2) y := by
      have := hgr.comp gq
      simpa only [Function.comp_def] using this
    have c3 : Continuous fun q : ℝ × P => ρ (clampT T q.1) y := (c.pt_cont y).comp continuous_fst
    exact ((continuous_const.mul c1).sub (continuous_const.inner c2)).mul c3

theorem MFctx.continuous_wk2_gen (c : MFctx D T Λ ρ) {P : Type*} [TopologicalSpace P]
    [FirstCountableTopology P] (p0 : P) (φ : P → Torus d → ℝ)
    (hgr : Continuous fun q : P × Torus d => Torus.grad (φ q.1) q.2) {Bg : ℝ}
    (hBg : ∀ p y, ‖Torus.grad (φ p) y‖ ≤ Bg) :
    Continuous fun q : ℝ × P => ∫ y, wk2g D (φ q.2) ρ (clampT T q.1) y := by
  obtain ⟨Kg, hKg⟩ := c.Gbound
  obtain ⟨cM, hcM0, hcM⟩ := exists_matVec_bound D.M
  obtain ⟨C, hG⟩ := KernelGradD1.goodKernel_periodicRieszGrad_of_one_le c.hd D.hs0 D.hsd
  have hΛ := c.Λ_nonneg
  have hBg0 : 0 ≤ Bg := (norm_nonneg _).trans (hBg p0 0)
  have hmat : Continuous (fun v : Euc d => Torus.matVec D.M v) :=
    LinearMap.continuous_of_finiteDimensional (Matrix.toEuclideanLin D.M)
  refine continuous_of_dominated (bound := fun _ => Λ * (Bg * (cM * Kg))) ?_ ?_
    (integrable_const _) ?_
  · intro q
    have hc := c.cont (clampT_mem c.hT q.1)
    have hGm : Measurable (convGradConv (periodicRieszGrad d D.s) (ρ (clampT T q.1))) :=
      HRS.Duality.measurable_conv hG hc.measurable
    have gq : Continuous fun y : Torus d => ((q.2, y) : P × Torus d) :=
      continuous_const.prodMk continuous_id
    have c2 : Continuous fun y : Torus d => Torus.grad (φ q.2) y := by
      have := hgr.comp gq
      simpa only [Function.comp_def] using this
    unfold wk2g
    refine (hc.measurable.mul ?_).aestronglyMeasurable
    exact Measurable.inner c2.measurable (hmat.measurable.comp hGm)
  · intro q
    refine Eventually.of_forall fun y => ?_
    unfold wk2g
    rw [Real.norm_eq_abs, abs_mul]
    have hb2 : |inner ℝ (Torus.grad (φ q.2) y) (Torus.matVec D.M
        (convGradConv (periodicRieszGrad d D.s) (ρ (clampT T q.1)) y))| ≤ Bg * (cM * Kg) := by
      refine (abs_real_inner_le_norm _ _).trans (mul_le_mul (hBg _ _) ((hcM _).trans ?_)
        (norm_nonneg _) hBg0)
      have hKg0 : 0 ≤ Kg := (norm_nonneg _).trans (hKg 0 ⟨le_rfl, c.hT⟩ 0)
      exact mul_le_mul_of_nonneg_left (hKg _ (clampT_mem c.hT q.1) y) hcM0
    exact mul_le_mul (c.abs_le (clampT_mem c.hT q.1) y) hb2 (abs_nonneg _) hΛ
  · refine Eventually.of_forall fun y => ?_
    have gq : Continuous fun q : ℝ × P => ((q.2, y) : P × Torus d) :=
      continuous_snd.prodMk continuous_const
    have c3 : Continuous fun q : ℝ × P => ρ (clampT T q.1) y := (c.pt_cont y).comp continuous_fst
    have c4 : Continuous fun q : ℝ × P => Torus.grad (φ q.2) y := by
      have := hgr.comp gq
      simpa only [Function.comp_def] using this
    have c5 : Continuous fun q : ℝ × P => Torus.matVec D.M
        (convGradConv (periodicRieszGrad d D.s) (ρ (clampT T q.1)) y) :=
      hmat.comp ((c.Gcont_pt y).comp continuous_fst)
    exact c3.mul (c4.inner c5)

theorem MFctx.continuous_wkG_gen (c : MFctx D T Λ ρ) {P : Type*} [TopologicalSpace P]
    [FirstCountableTopology P] (p0 : P)
    (φ : P → Torus d → ℝ) (hφ : ∀ p, Torus.IsCk 2 (φ p))
    (hlap : Continuous fun q : P × Torus d => Torus.laplacian (φ q.1) q.2)
    (hgr : Continuous fun q : P × Torus d => Torus.grad (φ q.1) q.2) {Bl Bg : ℝ}
    (hBl : ∀ p y, |Torus.laplacian (φ p) y| ≤ Bl) (hBg : ∀ p y, ‖Torus.grad (φ p) y‖ ≤ Bg) :
    Continuous fun q : ℝ × P => wkG D ρ (φ q.2) (clampT T q.1) := by
  have e : (fun q : ℝ × P => wkG D ρ (φ q.2) (clampT T q.1)) = fun q =>
      (∫ y, wk1g D (φ q.2) ρ (clampT T q.1) y) + ∫ y, wk2g D (φ q.2) ρ (clampT T q.1) y := by
    funext q; exact c.wkG_eq_gen (hφ q.2) (clampT_mem c.hT q.1)
  rw [e]
  exact (c.continuous_wk1_gen p0 φ hlap hgr hBl hBg).add (c.continuous_wk2_gen p0 φ hgr hBg)

end MFf

section MFfCont

variable {D : DynData d} {T Λ : ℝ} {ρ : ℝ → Torus d → ℝ}

theorem MFctx.continuous_lap_fK (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) :
    Continuous fun q : ℝ × Torus d => Torus.laplacian (fK h ρ (clampT T q.1)) q.2 := by
  have hh : Torus.IsCk 2 h := ContDiff.of_le
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift h) from hsm) two_le_top
  have hlap : Continuous (Torus.laplacian h) := HRS.PDE.MFApriori.continuous_laplacian_of_isCk hh
  obtain ⟨B, hB0, hB⟩ := exists_norm_bound (Torus.laplacian h) hlap
  have e : (fun q : ℝ × Torus d => Torus.laplacian (fK h ρ (clampT T q.1)) q.2) = fun q =>
      ∫ z : Torus d, ρ (clampT T q.1) z * Torus.laplacian h (q.2 - z) := by
    funext q; exact c.lap_fK hsm hev (clampT_mem c.hT q.1) q.2
  rw [e]
  refine continuous_of_dominated (bound := fun _ => Λ * B) ?_ ?_ (integrable_const _) ?_
  · intro q
    exact ((c.cont (clampT_mem c.hT q.1)).mul (hlap.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · intro q
    refine Eventually.of_forall fun z => ?_
    rw [norm_mul]
    exact mul_le_mul (by simpa [Real.norm_eq_abs] using c.abs_le (clampT_mem c.hT q.1) z) (hB _)
      (norm_nonneg _) c.Λ_nonneg
  · refine Eventually.of_forall fun z => ?_
    exact ((c.pt_cont z).comp continuous_fst).mul (hlap.comp (continuous_snd.sub continuous_const))

theorem MFctx.continuous_grad_fK (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) :
    Continuous fun q : ℝ × Torus d => Torus.grad (fK h ρ (clampT T q.1)) q.2 := by
  have h1 : Torus.IsCk 1 h := ContDiff.of_le
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift h) from hsm)
    (by exact_mod_cast (le_top : ((1 : ℕ) : ℕ∞) ≤ ⊤))
  have hgr : Continuous (Torus.grad h) := HRS.PDE.MFLinear.continuous_grad h1
  obtain ⟨B, hB0, hB⟩ := exists_norm_bound (Torus.grad h) hgr
  have e : (fun q : ℝ × Torus d => Torus.grad (fK h ρ (clampT T q.1)) q.2) = fun q =>
      ∫ z : Torus d, ρ (clampT T q.1) z • Torus.grad h (q.2 - z) := by
    funext q; exact c.grad_fK hsm hev (clampT_mem c.hT q.1) q.2
  rw [e]
  refine continuous_of_dominated (bound := fun _ => Λ * B) ?_ ?_ (integrable_const _) ?_
  · intro q
    exact ((c.cont (clampT_mem c.hT q.1)).smul (hgr.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · intro q
    refine Eventually.of_forall fun z => ?_
    rw [norm_smul]
    exact mul_le_mul (by simpa [Real.norm_eq_abs] using c.abs_le (clampT_mem c.hT q.1) z) (hB _)
      (norm_nonneg _) c.Λ_nonneg
  · refine Eventually.of_forall fun z => ?_
    exact ((c.pt_cont z).comp continuous_fst).smul (hgr.comp (continuous_snd.sub continuous_const))

theorem MFctx.lap_fK_le (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) {B : ℝ} (hB : ∀ x, |Torus.laplacian h x| ≤ B) {r : ℝ}
    (hr : r ∈ Icc 0 T) (y : Torus d) : |Torus.laplacian (fK h ρ r) y| ≤ B := by
  rw [c.lap_fK hsm hev hr]
  have hp := c.dens hr
  have hρi : Integrable (ρ r) := (c.cont hr).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hh : Torus.IsCk 2 h := ContDiff.of_le
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift h) from hsm) two_le_top
  have hlap : Continuous (Torus.laplacian h) := HRS.PDE.MFApriori.continuous_laplacian_of_isCk hh
  have hi : Integrable (fun z : Torus d => ρ r z * Torus.laplacian h (y - z)) :=
    ((c.cont hr).mul (hlap.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc |∫ z, ρ r z * Torus.laplacian h (y - z)| ≤ ∫ z, |ρ r z * Torus.laplacian h (y - z)| := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun z => ρ r z * Torus.laplacian h (y - z))
    _ ≤ ∫ z, B * ρ r z := by
        refine integral_mono hi.abs (hρi.const_mul B) fun z => ?_
        simp only
        rw [abs_mul, abs_of_nonneg (hp.nonneg z), mul_comm]
        exact mul_le_mul_of_nonneg_right (hB _) (hp.nonneg z)
    _ = B := by rw [integral_const_mul, hp.integral_one, mul_one]

theorem MFctx.grad_fK_le (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) {B : ℝ} (hB : ∀ x, ‖Torus.grad h x‖ ≤ B) {r : ℝ}
    (hr : r ∈ Icc 0 T) (y : Torus d) : ‖Torus.grad (fK h ρ r) y‖ ≤ B := by
  rw [c.grad_fK hsm hev hr]
  have hp := c.dens hr
  have hρi : Integrable (ρ r) := (c.cont hr).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h1 : Torus.IsCk 1 h := ContDiff.of_le
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift h) from hsm)
    (by exact_mod_cast (le_top : ((1 : ℕ) : ℕ∞) ≤ ⊤))
  have hgr : Continuous (Torus.grad h) := HRS.PDE.MFLinear.continuous_grad h1
  have hi : Integrable (fun z : Torus d => ρ r z • Torus.grad h (y - z)) :=
    ((c.cont hr).smul (hgr.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc ‖∫ z, ρ r z • Torus.grad h (y - z)‖ ≤ ∫ z, ‖ρ r z • Torus.grad h (y - z)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ z, B * ρ r z := by
        refine integral_mono hi.norm (hρi.const_mul B) fun z => ?_
        simp only
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hp.nonneg z), mul_comm]
        exact mul_le_mul_of_nonneg_right (hB _) (hp.nonneg z)
    _ = B := by rw [integral_const_mul, hp.integral_one, mul_one]

/-- `W(u,s) = wkG(ρ, f_s)(u)` is jointly continuous (clamped). -/
theorem MFctx.continuous_W (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) :
    Continuous fun q : ℝ × ℝ => wkG D ρ (fK h ρ (clampT T q.2)) (clampT T q.1) := by
  have hh : Torus.IsCk 2 h := ContDiff.of_le
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift h) from hsm) two_le_top
  have h1 : Torus.IsCk 1 h := ContDiff.of_le
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift h) from hsm)
    (by exact_mod_cast (le_top : ((1 : ℕ) : ℕ∞) ≤ ⊤))
  obtain ⟨Bl, hBl0, hBl⟩ := exists_norm_bound (Torus.laplacian h)
    (HRS.PDE.MFApriori.continuous_laplacian_of_isCk hh)
  obtain ⟨Bg, hBg0, hBg⟩ := exists_norm_bound (Torus.grad h) (HRS.PDE.MFLinear.continuous_grad h1)
  exact c.continuous_wkG_gen (0 : ℝ) (fun s => fK h ρ (clampT T s))
    (fun s => ContDiff.of_le (c.contDiff_fK hsm hev (clampT_mem c.hT s)) two_le_top)
    (c.continuous_lap_fK hsm hev) (c.continuous_grad_fK hsm hev)
    (Bl := Bl) (Bg := Bg)
    (fun s y => c.lap_fK_le hsm hev (fun x => by simpa [Real.norm_eq_abs] using hBl x)
      (clampT_mem c.hT s) y)
    (fun s y => c.grad_fK_le hsm hev hBg (clampT_mem c.hT s) y)

/-- `⟨ρ_u, f_s⟩ = ⟨ρ_s, f_u⟩`: the pairing `∬ h(y-x) ρ_u(x) ρ_s(y)` is symmetric (`h` even). -/
theorem MFctx.pair_comm (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) {u s : ℝ} (hu : u ∈ Icc 0 T) (hs : s ∈ Icc 0 T) :
    pair (withDensityReal (ρ u)) (fK h ρ s) = pair (withDensityReal (ρ s)) (fK h ρ u) := by
  have hh : Torus.IsCk 0 h := ContDiff.of_le
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift h) from hsm) (by exact_mod_cast le_top)
  have hhc : Continuous h := isCk_continuous hh
  have key : ∀ a b : ℝ, a ∈ Icc 0 T → b ∈ Icc 0 T →
      pair (withDensityReal (ρ a)) (fK h ρ b) =
        ∫ x, ∫ y, h (y - x) * ρ b y * ρ a x := by
    intro a b ha hb
    rw [pair_wDR (c.dens ha)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [fK, psi]
    rw [pair_wDR (c.dens hb), ← integral_mul_const]
    rfl
  rw [key u s hu hs, key s u hs hu]
  have hint : Integrable (Function.uncurry fun x y : Torus d => h (y - x) * ρ s y * ρ u x)
      ((volume : Measure (Torus d)).prod volume) := by
    have hc : Continuous (Function.uncurry fun x y : Torus d => h (y - x) * ρ s y * ρ u x) := by
      refine Continuous.mul (Continuous.mul ?_ ?_) ?_
      · exact hhc.comp (continuous_snd.sub continuous_fst)
      · exact (c.cont hs).comp continuous_snd
      · exact (c.cont hu).comp continuous_fst
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Function.uncurry]
  rw [show y - x = -(x - y) by abel, hev]
  ring

/-- The diagonal `D(r) = ⟨ρ_r, f_r⟩` (twice the quadratic background term). -/
def Dg (h : Torus d → ℝ) (ρ : ℝ → Torus d → ℝ) (r : ℝ) : ℝ :=
  pair (withDensityReal (ρ r)) (fK h ρ r)

theorem MFctx.pair_diff_int (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) {s : ℝ} (hs : s ∈ Icc 0 T) {u v : ℝ} (hu : u ∈ Icc 0 T)
    (hv : v ∈ Icc 0 T) :
    pair (withDensityReal (ρ v)) (fK h ρ s) - pair (withDensityReal (ρ u)) (fK h ρ s) =
      ∫ τ in u..v, wkG D ρ (fK h ρ (clampT T s)) (clampT T τ) := by
  have hψ : Torus.IsCk 2 (fK h ρ s) := ContDiff.of_le (c.contDiff_fK hsm hev hs) two_le_top
  have hWc : Continuous fun τ : ℝ => wkG D ρ (fK h ρ (clampT T s)) (clampT T τ) := by
    have := (c.continuous_W hsm hev).comp (Continuous.prodMk_left (s : ℝ))
    simpa only [Function.comp_def] using this
  have hI0 : ∀ t ∈ Icc 0 T, pair (withDensityReal (ρ t)) (fK h ρ s) -
      pair (withDensityReal (ρ 0)) (fK h ρ s) =
      ∫ τ in (0 : ℝ)..t, wkG D ρ (fK h ρ (clampT T s)) (clampT T τ) := by
    intro t ht
    rw [weak_eq_wkG c.hmf hψ ht, intervalIntegral.integral_of_le ht.1, ← integral_Icc_eq_integral_Ioc]
    refine setIntegral_congr_fun measurableSet_Icc fun τ hτ => ?_
    rw [clampT_of_mem ⟨hτ.1, hτ.2.trans ht.2⟩, clampT_of_mem hs]
  have hv' := hI0 v hv
  have hu' := hI0 u hu
  rw [← intervalIntegral.integral_interval_sub_left (hWc.intervalIntegrable 0 v) (hWc.intervalIntegrable 0 u),
    ← hv', ← hu']
  ring

theorem MFctx.diag_diff (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) {r r' : ℝ} (hr : r ∈ Icc 0 T) (hr' : r' ∈ Icc 0 T) :
    Dg h ρ r' - Dg h ρ r = ∫ τ in r..r',
      (wkG D ρ (fK h ρ (clampT T r')) (clampT T τ) + wkG D ρ (fK h ρ (clampT T r)) (clampT T τ)) := by
  have hWc : ∀ s : ℝ, Continuous fun τ : ℝ => wkG D ρ (fK h ρ (clampT T s)) (clampT T τ) := by
    intro s
    have := (c.continuous_W hsm hev).comp (Continuous.prodMk_left (s : ℝ))
    simpa only [Function.comp_def] using this
  rw [intervalIntegral.integral_add ((hWc r').intervalIntegrable _ _) ((hWc r).intervalIntegrable _ _),
    ← c.pair_diff_int hsm hev hr' hr hr', ← c.pair_diff_int hsm hev hr hr hr']
  unfold Dg
  rw [c.pair_comm hsm hev hr hr']
  ring

theorem MFctx.hasDerivAt_Dg (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) {r : ℝ} (hr : r ∈ Ioo 0 T) :
    HasDerivAt (Dg h ρ) (2 * wkG D ρ (fK h ρ r) r) r := by
  have hrI : r ∈ Icc 0 T := ⟨hr.1.le, hr.2.le⟩
  have hWj := c.continuous_W hsm hev
  set Wc : ℝ × ℝ → ℝ := fun q => wkG D ρ (fK h ρ (clampT T q.2)) (clampT T q.1) with hWc
  have hVeq : Wc (r, r) = wkG D ρ (fK h ρ r) r := by
    simp only [hWc, clampT_of_mem hrI]
  have hWcc : ∀ s : ℝ, Continuous fun τ : ℝ => Wc (τ, s) := fun s =>
    hWj.comp (Continuous.prodMk_left s)
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨η, hη, hball⟩ := Metric.continuousAt_iff.1 (hWj.continuousAt (x := (r, r))) (ε / 2) (by positivity)
  filter_upwards [Ioo_mem_nhds hr.1 hr.2, Metric.ball_mem_nhds r hη] with r' hr'I hr'ball
  have hr'I' : r' ∈ Icc 0 T := ⟨hr'I.1.le, hr'I.2.le⟩
  have hdf : Dg h ρ r' - Dg h ρ r = ∫ τ in r..r', (Wc (τ, r') + Wc (τ, r)) :=
    c.diag_diff hsm hev hrI hr'I'
  set V := wkG D ρ (fK h ρ r) r with hV
  have hi1 : IntervalIntegrable (fun τ => Wc (τ, r')) volume r r' := (hWcc r').intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun τ => Wc (τ, r)) volume r r' := (hWcc r).intervalIntegrable _ _
  have hic : IntervalIntegrable (fun _ : ℝ => V) volume r r' := intervalIntegrable_const
  have e : Dg h ρ r' - Dg h ρ r - (r' - r) • (2 * V) =
      ∫ τ in r..r', ((Wc (τ, r') - V) + (Wc (τ, r) - V)) := by
    have h1 : ∫ τ in r..r', ((Wc (τ, r') - V) + (Wc (τ, r) - V)) =
        ((∫ τ in r..r', Wc (τ, r')) - (r' - r) • V) + ((∫ τ in r..r', Wc (τ, r)) - (r' - r) • V) := by
      rw [intervalIntegral.integral_add (hi1.sub hic) (hi2.sub hic),
        intervalIntegral.integral_sub hi1 hic, intervalIntegral.integral_sub hi2 hic,
        intervalIntegral.integral_const]
    rw [h1, hdf, intervalIntegral.integral_add hi1 hi2]
    simp only [smul_eq_mul]
    ring
  have hbd : ∀ τ ∈ Set.uIoc r r', ‖(Wc (τ, r') - V) + (Wc (τ, r) - V)‖ ≤ ε := by
    intro τ hτ
    have hτ' : |τ - r| ≤ |r' - r| := Set.abs_sub_left_of_mem_uIcc (Set.uIoc_subset_uIcc hτ)
    have hr'd : |r' - r| < η := by simpa [Real.dist_eq] using hr'ball
    have d1 : dist (τ, r') (r, r) < η := by
      rw [Prod.dist_eq, max_lt_iff]
      exact ⟨by rw [Real.dist_eq]; exact lt_of_le_of_lt hτ' hr'd, by rw [Real.dist_eq]; exact hr'd⟩
    have d2 : dist (τ, r) (r, r) < η := by
      rw [Prod.dist_eq, max_lt_iff]
      exact ⟨by rw [Real.dist_eq]; exact lt_of_le_of_lt hτ' hr'd, by rw [dist_self]; exact hη⟩
    have b1 := hball d1
    have b2 := hball d2
    rw [Real.dist_eq, hVeq] at b1 b2
    rw [Real.norm_eq_abs]
    refine (abs_add_le _ _).trans ?_
    linarith [b1.le, b2.le]
  rw [e]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hbd).trans (le_of_eq ?_)
  rw [Real.norm_eq_abs]

theorem MFctx.continuousOn_Dg (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) : ContinuousOn (Dg h ρ) (Icc 0 T) := by
  have hWj := c.continuous_W hsm hev
  obtain ⟨Bw, hBw⟩ := (isCompact_Icc.prod isCompact_Icc : IsCompact (Icc (0 : ℝ) T ×ˢ Icc (0 : ℝ) T)).exists_bound_of_continuousOn
    hWj.continuousOn
  have hlip : ∀ r ∈ Icc 0 T, ∀ r' ∈ Icc 0 T, |Dg h ρ r' - Dg h ρ r| ≤ (2 * |Bw|) * |r' - r| := by
    intro r hr r' hr'
    rw [c.diag_diff hsm hev hr hr']
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := r) (b := r')
      (f := fun τ => wkG D ρ (fK h ρ (clampT T r')) (clampT T τ) + wkG D ρ (fK h ρ (clampT T r)) (clampT T τ))
      (C := 2 * |Bw|) (fun τ hτ => by
        have hτI : τ ∈ Icc 0 T := by
          have := Set.uIoc_subset_uIcc hτ
          rcases le_total r r' with h' | h'
          · rw [Set.uIcc_of_le h'] at this; exact ⟨hr.1.trans this.1, this.2.trans hr'.2⟩
          · rw [Set.uIcc_of_ge h'] at this; exact ⟨hr'.1.trans this.1, this.2.trans hr.2⟩
        have b1 := hBw (τ, r') ⟨hτI, hr'⟩
        have b2 := hBw (τ, r) ⟨hτI, hr⟩
        refine (norm_add_le _ _).trans ?_
        have := le_abs_self Bw
        simp only at b1 b2
        linarith)
    simpa [Real.norm_eq_abs] using this
  intro r hr
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨ε / (2 * |Bw| + 1), by positivity, fun r' hr' hd => ?_⟩
  rw [Real.dist_eq]
  have := hlip r hr r' hr'
  rw [Real.dist_eq] at hd
  calc |Dg h ρ r' - Dg h ρ r| ≤ (2 * |Bw|) * |r' - r| := this
    _ < ε := by
      have h1 : |r' - r| < ε / (2 * |Bw| + 1) := hd
      rw [lt_div_iff₀ (by positivity)] at h1
      nlinarith [abs_nonneg Bw, abs_nonneg (r' - r)]

theorem MFctx.continuousOn_Wdiag (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) :
    ContinuousOn (fun τ : ℝ => wkG D ρ (fK h ρ τ) τ) (Icc 0 T) := by
  have hWj := c.continuous_W hsm hev
  have h1 : Continuous fun τ : ℝ => wkG D ρ (fK h ρ (clampT T τ)) (clampT T τ) := by
    have := hWj.comp (continuous_id.prodMk continuous_id)
    simpa only [Function.comp_def, id_eq] using this
  refine h1.continuousOn.congr fun τ hτ => ?_
  simp only [clampT_of_mem hτ]

theorem MFctx.Dg_eq (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Dg h ρ t - Dg h ρ 0 = ∫ τ in (0 : ℝ)..t, 2 * wkG D ρ (fK h ρ τ) τ := by
  rcases ht.1.eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hint : IntervalIntegrable (fun τ : ℝ => 2 * wkG D ρ (fK h ρ τ) τ) volume 0 t := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le ht.1]
    exact (continuousOn_const.mul ((c.continuousOn_Wdiag hsm hev).mono hsub))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    ((c.continuousOn_Dg hsm hev).mono hsub) (fun x hx => c.hasDerivAt_Dg hsm hev
      ⟨hx.1, hx.2.trans_le ht.2⟩) hint]

end MFfCont

end HRS.KID
