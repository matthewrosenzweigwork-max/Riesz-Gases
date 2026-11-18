import HRS.Energy.KIDAux3

/-!
# KID helper file 4: the pointwise algebra (part D of the plan in `KIDAux1`)
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.PDE HRS.Uniform.Q54c

namespace HRS.KID

variable {d N : ℕ}

section Even

theorem fderiv2_even {H : Euc d → ℝ} (hH : ContDiff ℝ 2 H) (hev : ∀ w, H (-w) = H w) (w : Euc d) :
    fderiv ℝ (fderiv ℝ H) (-w) = fderiv ℝ (fderiv ℝ H) w := by
  have hd : Differentiable ℝ H := hH.differentiable (by norm_num)
  have hd1 : Differentiable ℝ (fderiv ℝ H) :=
    (hH.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hodd : ∀ v, fderiv ℝ H (-v) = -fderiv ℝ H v := fun v => fderiv_odd_of_even hd hev v
  have h1 : HasFDerivAt (fun v => fderiv ℝ H (-v))
      ((fderiv ℝ (fderiv ℝ H) (-w)).comp (-ContinuousLinearMap.id ℝ (Euc d))) w :=
    (hd1 (-w)).hasFDerivAt.comp w (hasFDerivAt_id w).neg
  have e : (fun v => fderiv ℝ H (-v)) = fun v => -fderiv ℝ H v := funext hodd
  rw [e] at h1
  have h2 : HasFDerivAt (fun v => -fderiv ℝ H v) (-fderiv ℝ (fderiv ℝ H) w) w :=
    (hd1 w).hasFDerivAt.neg
  have h3 := h1.unique h2
  ext u v
  have := congrArg (fun L => L u v) h3
  simp at this
  simpa using this

theorem laplacian_lift_even {H : Euc d → ℝ} (hH : ContDiff ℝ 2 H) (hev : ∀ w, H (-w) = H w)
    (w : Euc d) : Laplacian.laplacian H (-w) = Laplacian.laplacian H w := by
  rw [laplacian_eq_sum_fderiv, laplacian_eq_sum_fderiv, fderiv2_even hH hev]

theorem laplacian_even {h : Torus d → ℝ} (hsm : Torus.IsSmooth h) (hev : ∀ x, h (-x) = h x)
    (x : Torus d) : Torus.laplacian h (-x) = Torus.laplacian h x := by
  have hx : x = Torus.mk (Torus.rep x) := (Torus.mk_rep x).symm
  rw [hx, ← HRS.KernelGrad.mk_neg, laplacian_mk, laplacian_mk]
  exact laplacian_lift_even (isCk2_of_smooth hsm) (lift_even hev) _

end Even

section CG

theorem convGradConv_odd (G : Torus d → Euc d) (hG : Continuous G) (hodd : ∀ z, G (-z) = -G z)
    (ρ : Torus d → ℝ) (hρ : Continuous ρ) (x : Torus d) :
    convGradConv G ρ x = ∫ y, ρ y • G (x - y) := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_bound G hG
  have hind : Integrable (fun y : Torus d => if ‖x - y‖ ≤ 1 / 4 then G (x - y) else 0) := by
    refine Integrable.of_bound (C := B) ?_ ?_
    · refine (Measurable.ite ?_ (hG.measurable.comp (measurable_const.sub measurable_id))
        measurable_const).aestronglyMeasurable
      exact measurableSet_le (measurable_norm.comp (measurable_const.sub measurable_id)) measurable_const
    · refine Eventually.of_forall fun y => ?_
      split_ifs
      · exact hB _
      · simpa using hB0
  have hi1 : Integrable (fun y : Torus d => ρ y • G (x - y)) :=
    (hρ.smul (hG.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hzero : ∫ y : Torus d, (if ‖x - y‖ ≤ 1 / 4 then G (x - y) else 0) = 0 := by
    have h1 : ∫ y : Torus d, (if ‖x - y‖ ≤ 1 / 4 then G (x - y) else 0) =
        ∫ z : Torus d, (if ‖z‖ ≤ 1 / 4 then G z else 0) :=
      integral_sub_left_eq_self (fun z : Torus d => if ‖z‖ ≤ 1 / 4 then G z else 0) volume x
    rw [h1]
    have h2 : ∫ z : Torus d, (if ‖-z‖ ≤ 1 / 4 then G (-z) else 0) =
        ∫ z : Torus d, (if ‖z‖ ≤ 1 / 4 then G z else 0) :=
      integral_neg_eq_self (fun z : Torus d => if ‖z‖ ≤ 1 / 4 then G z else 0) volume
    have h3 : ∫ z : Torus d, (if ‖-z‖ ≤ 1 / 4 then G (-z) else 0) =
        -∫ z : Torus d, (if ‖z‖ ≤ 1 / 4 then G z else 0) := by
      rw [← integral_neg]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [norm_neg, hodd]
      split_ifs <;> simp
    have h4 : ∫ z : Torus d, (if ‖z‖ ≤ 1 / 4 then G z else 0) =
        -∫ z : Torus d, (if ‖z‖ ≤ 1 / 4 then G z else 0) := by
      have h3' := h3
      rw [h2] at h3'
      exact h3'
    have := congrArg (fun v => v + ∫ z : Torus d, (if ‖z‖ ≤ 1 / 4 then G z else 0)) h4
    simp only [neg_add_cancel] at this
    have h5 : (2 : ℝ) • ∫ z : Torus d, (if ‖z‖ ≤ 1 / 4 then G z else 0) = 0 := by
      rw [two_smul]; exact this
    exact (smul_eq_zero.1 h5).resolve_left (by norm_num)
  unfold convGradConv
  have e : (fun y : Torus d => if ‖x - y‖ ≤ 1 / 4 then (ρ y - ρ x) • G (x - y) else ρ y • G (x - y)) =
      fun y => ρ y • G (x - y) - ρ x • (if ‖x - y‖ ≤ 1 / 4 then G (x - y) else 0) := by
    funext y
    split_ifs
    · rw [sub_smul]
    · simp
  have hi2 : Integrable (fun y : Torus d => ρ x • (if ‖x - y‖ ≤ 1 / 4 then G (x - y) else 0)) :=
    hind.smul (ρ x)
  rw [e, integral_sub hi1 hi2, integral_smul, hzero]
  simp

end CG

section Formulas

variable {D : DynData d} {T Λ : ℝ} {ρ : ℝ → Torus d → ℝ}

theorem MFctx.Gcont (c : MFctx D T Λ ρ) {r : ℝ} (hr : r ∈ Icc 0 T) :
    Continuous (convGradConv (periodicRieszGrad d D.s) (ρ r)) := by
  obtain ⟨C, hG⟩ := KernelGradD1.goodKernel_periodicRieszGrad_of_one_le c.hd D.hs0 D.hsd
  exact HRS.PDE.MFPairing.LipB.conv_continuous hG
    (HRS.PDE.MFPairing.LipB.of_isCk ((c.ck3 hr).of_le (by norm_num)))

theorem MFctx.ucont (c : MFctx D T Λ ρ) {r : ℝ} (hr : r ∈ Icc 0 T) :
    Continuous (meanFieldDrift D (ρ r)) := by
  have hV1 : Torus.IsCk 1 D.V := c.hV.of_le (by norm_num)
  have hmat : Continuous (fun v : Euc d => Torus.matVec D.M v) :=
    LinearMap.continuous_of_finiteDimensional (Matrix.toEuclideanLin D.M)
  unfold meanFieldDrift
  exact (hmat.comp (c.Gcont hr)).sub (HRS.PDE.MFLinear.continuous_grad hV1)

theorem MFctx.meanFieldDrift_eq (D : DynData d) (ρ : Torus d → ℝ) (y : Torus d) :
    meanFieldDrift D ρ y = Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) ρ y) -
      Torus.grad D.V y := rfl

/-- Continuous functions on the torus are integrable (shorthand). -/
theorem integrable_of_cont {E : Type*} [NormedAddCommGroup E] {g : Torus d → E} (hg : Continuous g) :
    Integrable g :=
  hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem MFctx.ftK_eq (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) {r : ℝ} (hr : r ∈ Icc 0 T) (x : Torus d) :
    ftK D h ρ r x = D.invβ * Torus.laplacian (fK h ρ r) x -
      ∫ y, ρ r y * inner ℝ (Torus.grad h (x - y)) (meanFieldDrift D (ρ r) y) := by
  have hh := isCk2_of_smooth hsm
  have h1 := isCk1_of_smooth hsm
  have hV1 : Torus.IsCk 1 D.V := c.hV.of_le (by norm_num)
  unfold ftK
  rw [c.wkG_eq hh x hr, c.lap_fK hsm hev hr]
  have hρc := c.cont hr
  have hgh : Continuous (Torus.grad h) := HRS.PDE.MFLinear.continuous_grad h1
  have hgV : Continuous (Torus.grad D.V) := HRS.PDE.MFLinear.continuous_grad hV1
  have hlap : Continuous (Torus.laplacian h) := HRS.PDE.MFApriori.continuous_laplacian_of_isCk hh
  have hmat : Continuous (fun v : Euc d => Torus.matVec D.M v) :=
    LinearMap.continuous_of_finiteDimensional (Matrix.toEuclideanLin D.M)
  have hGc := c.Gcont hr
  have hsub : Continuous fun y : Torus d => y - x := continuous_id.sub continuous_const
  have hsub' : Continuous fun y : Torus d => x - y := continuous_const.sub continuous_id
  -- rewrite the integrands
  have e1 : ∀ y, wk1 D h ρ r x y =
      D.invβ * (ρ r y * Torus.laplacian h (x - y)) - ρ r y * inner ℝ (Torus.grad D.V y) (Torus.grad h (y - x)) := by
    intro y
    unfold wk1
    rw [show y - x = -(x - y) by abel, laplacian_even hsm hev]
    ring
  have e2 : ∀ y, wk2 D h ρ r x y =
      ρ r y * inner ℝ (Torus.grad h (y - x)) (Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) (ρ r) y)) := fun _ => rfl
  have hi1 : Integrable (fun y => ρ r y * Torus.laplacian h (x - y)) :=
    integrable_of_cont (hρc.mul (hlap.comp hsub'))
  have hi2 : Integrable (fun y => ρ r y * inner ℝ (Torus.grad D.V y) (Torus.grad h (y - x))) :=
    integrable_of_cont (hρc.mul (hgV.inner (hgh.comp hsub)))
  have hi3 : Integrable (fun y => ρ r y * inner ℝ (Torus.grad h (y - x))
      (Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) (ρ r) y))) :=
    integrable_of_cont (hρc.mul ((hgh.comp hsub).inner (hmat.comp hGc)))
  simp_rw [e1, e2]
  rw [integral_sub (hi1.const_mul _) hi2, integral_const_mul]
  have e3 : ∀ y, ρ r y * inner ℝ (Torus.grad h (x - y)) (meanFieldDrift D (ρ r) y) =
      -(ρ r y * inner ℝ (Torus.grad h (y - x)) (Torus.matVec D.M
          (convGradConv (periodicRieszGrad d D.s) (ρ r) y)) -
        ρ r y * inner ℝ (Torus.grad D.V y) (Torus.grad h (y - x))) := by
    intro y
    rw [show x - y = -(y - x) by abel, grad_odd h1 hev, meanFieldDrift_eq, inner_neg_left,
      inner_sub_right, real_inner_comm (Torus.grad D.V y)]
    ring
  simp_rw [e3]
  rw [integral_neg, integral_sub hi3 hi2]
  ring

theorem MFctx.w_eq (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) {r : ℝ} (hr : r ∈ Icc 0 T) :
    wkG D ρ (fK h ρ r) r = D.invβ * (∫ y, ρ r y * Torus.laplacian (fK h ρ r) y) +
      ∫ y, ρ r y * inner ℝ (Torus.grad (fK h ρ r) y) (meanFieldDrift D (ρ r) y) := by
  have hφ : Torus.IsCk 2 (fK h ρ r) := ContDiff.of_le (c.contDiff_fK hsm hev hr) two_le_top
  have hφ1 : Torus.IsCk 1 (fK h ρ r) := hφ.of_le (by norm_num)
  have hV1 : Torus.IsCk 1 D.V := c.hV.of_le (by norm_num)
  rw [c.wkG_eq_gen hφ hr]
  have hρc := c.cont hr
  have hgφ : Continuous (Torus.grad (fK h ρ r)) := HRS.PDE.MFLinear.continuous_grad hφ1
  have hgV : Continuous (Torus.grad D.V) := HRS.PDE.MFLinear.continuous_grad hV1
  have hlap : Continuous (Torus.laplacian (fK h ρ r)) :=
    HRS.PDE.MFApriori.continuous_laplacian_of_isCk hφ
  have hmat : Continuous (fun v : Euc d => Torus.matVec D.M v) :=
    LinearMap.continuous_of_finiteDimensional (Matrix.toEuclideanLin D.M)
  have hGc := c.Gcont hr
  have hi1 : Integrable (fun y => ρ r y * Torus.laplacian (fK h ρ r) y) :=
    integrable_of_cont (hρc.mul hlap)
  have hi2 : Integrable (fun y => ρ r y * inner ℝ (Torus.grad D.V y) (Torus.grad (fK h ρ r) y)) :=
    integrable_of_cont (hρc.mul (hgV.inner hgφ))
  have hi3 : Integrable (fun y => ρ r y * inner ℝ (Torus.grad (fK h ρ r) y)
      (Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) (ρ r) y))) :=
    integrable_of_cont (hρc.mul (hgφ.inner (hmat.comp hGc)))
  have e1 : ∀ y, wk1g D (fK h ρ r) ρ r y =
      D.invβ * (ρ r y * Torus.laplacian (fK h ρ r) y) -
        ρ r y * inner ℝ (Torus.grad D.V y) (Torus.grad (fK h ρ r) y) := by
    intro y; unfold wk1g; ring
  have e2 : ∀ y, ρ r y * inner ℝ (Torus.grad (fK h ρ r) y) (meanFieldDrift D (ρ r) y) =
      ρ r y * inner ℝ (Torus.grad (fK h ρ r) y)
        (Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) (ρ r) y)) -
        ρ r y * inner ℝ (Torus.grad D.V y) (Torus.grad (fK h ρ r) y) := by
    intro y
    rw [meanFieldDrift_eq, inner_sub_right,
      ← real_inner_comm (Torus.grad (fK h ρ r) y) (Torus.grad D.V y)]
    ring
  have hL : ∫ y, wk1g D (fK h ρ r) ρ r y = D.invβ * (∫ y, ρ r y * Torus.laplacian (fK h ρ r) y) -
      ∫ y, ρ r y * inner ℝ (Torus.grad D.V y) (Torus.grad (fK h ρ r) y) := by
    simp_rw [e1]
    rw [integral_sub (hi1.const_mul _) hi2, integral_const_mul]
  have hR : ∫ y, ρ r y * inner ℝ (Torus.grad (fK h ρ r) y) (meanFieldDrift D (ρ r) y) =
      (∫ y, ρ r y * inner ℝ (Torus.grad (fK h ρ r) y)
        (Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) (ρ r) y))) -
      ∫ y, ρ r y * inner ℝ (Torus.grad D.V y) (Torus.grad (fK h ρ r) y) := by
    simp_rw [e2]
    rw [integral_sub hi3 hi2]
  rw [hL, hR]
  simp only [wk2g]
  ring

theorem int_h_eq_fK {h : Torus d → ℝ} (hev : ∀ x, h (-x) = h x) (μ : ℝ → Torus d → ℝ) (r : ℝ)
    (x : Torus d) : ∫ y, h (x - y) ∂(withDensityReal (μ r)) = fK h μ r x := by
  unfold fK pair psi
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [← hev (x - y), neg_sub]

theorem energy_eq {h : Torus d → ℝ} (hev : ∀ x, h (-x) = h x) (hN : 0 < N) (ρ : ℝ → Torus d → ℝ)
    (r : ℝ) (X : Config d N) :
    modulatedEnergyKernel h X (withDensityReal (ρ r)) =
      Fpp h X - pair (empirical X) (fK h ρ r) + (1 / 2) * Dg h ρ r := by
  unfold modulatedEnergyKernel modulatedEnergy Fpp Dg
  simp only [int_h_eq_fK hev]
  rw [pair_empirical hN]
  unfold pair
  ring

theorem ae_ne_pt (hd : 0 < d) (x : Torus d) : ∀ᵐ y : Torus d, x ≠ y := by
  have h := (measurePreserving_sub_right (volume : Measure (Torus d)) x).quasiMeasurePreserving.ae
    (HRS.KernelGrad.torus_ae_ne' hd)
  filter_upwards [h] with y hy hxy
  exact hy (by rw [← hxy, sub_self])

theorem integral_offdiag_kernel (c : MFctx D T Λ ρ) {r : ℝ} (hr : r ∈ Icc 0 T) (k : Torus d → ℝ)
    (x : Torus d) :
    ∫ y, (if x = y then 0 else k (x - y)) ∂(withDensityReal (ρ r)) =
      ∫ y, ρ r y * k (x - y) := by
  rw [HRS.PDE.MFPairing.integral_withDensityReal (c.dens hr).measurable (c.dens hr).nonneg]
  refine integral_congr_ae ?_
  filter_upwards [ae_ne_pt c.hd x] with y hy
  simp [hy]

theorem MFctx.offDiag_eval (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) {r : ℝ} (hr : r ∈ Icc 0 T) (hN : 0 < N) (X : Config d N)
    (hX : X ∉ collisionSet d N) :
    offDiagDiffPairing (Torus.laplacian h) X (withDensityReal (ρ r)) =
      (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, Torus.laplacian h (X i - X j)
        - (2 / (N : ℝ)) * ∑ i, Torus.laplacian (fK h ρ r) (X i)
        + ∫ x, ρ r x * Torus.laplacian (fK h ρ r) x := by
  unfold offDiagDiffPairing offDiagPairing
  have hp : ∀ i, ∑ j ∈ Finset.univ.erase i,
      (if X i = X j then (0 : ℝ) else Torus.laplacian h (X i - X j)) =
      ∑ j ∈ Finset.univ.erase i, Torus.laplacian h (X i - X j) := by
    intro i
    refine Finset.sum_congr rfl fun j hj => ?_
    have hne : X i ≠ X j := fun h' => hX ⟨i, j, (Finset.ne_of_mem_erase hj).symm, h'⟩
    simp [hne]
  have hy : ∀ x, ∫ y, (if x = y then (0 : ℝ) else Torus.laplacian h (x - y)) ∂(withDensityReal (ρ r)) =
      Torus.laplacian (fK h ρ r) x := by
    intro x
    rw [integral_offdiag_kernel c hr (Torus.laplacian h) x, c.lap_fK hsm hev hr]
  simp only [hp, hy]
  rw [HRS.PDE.MFPairing.integral_withDensityReal (c.dens hr).measurable (c.dens hr).nonneg]

/-- `J_x = ∫ ρ_r(y) u_r(y) · ∇h(x - y) dy`. -/
def Jx (D : DynData d) (h : Torus d → ℝ) (ρ : ℝ → Torus d → ℝ) (r : ℝ) (x : Torus d) : ℝ :=
  ∫ y, ρ r y * inner ℝ (meanFieldDrift D (ρ r) y) (Torus.grad h (x - y))

theorem MFctx.Cx_eq (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) {r : ℝ} (hr : r ∈ Icc 0 T) (x : Torus d) :
    ∫ y, commKernel (Torus.grad h) (meanFieldDrift D (ρ r)) x y ∂(withDensityReal (ρ r)) =
      inner ℝ (meanFieldDrift D (ρ r) x) (Torus.grad (fK h ρ r) x) - Jx D h ρ r x := by
  have h1 := isCk1_of_smooth hsm
  have hρc := c.cont hr
  have hgh : Continuous (Torus.grad h) := HRS.PDE.MFLinear.continuous_grad h1
  have hu := c.ucont hr
  have hsub' : Continuous fun y : Torus d => x - y := continuous_const.sub continuous_id
  rw [HRS.PDE.MFPairing.integral_withDensityReal (c.dens hr).measurable (c.dens hr).nonneg]
  have e : ∀ᵐ y : Torus d, ρ r y * commKernel (Torus.grad h) (meanFieldDrift D (ρ r)) x y =
      ρ r y * inner ℝ (meanFieldDrift D (ρ r) x) (Torus.grad h (x - y)) -
        ρ r y * inner ℝ (meanFieldDrift D (ρ r) y) (Torus.grad h (x - y)) := by
    filter_upwards [ae_ne_pt c.hd x] with y hy
    simp only [commKernel, if_neg hy, inner_sub_left]
    ring
  rw [integral_congr_ae e]
  have hi1 : Integrable (fun y => ρ r y * inner ℝ (meanFieldDrift D (ρ r) x) (Torus.grad h (x - y))) :=
    integrable_of_cont (hρc.mul (continuous_const.inner (hgh.comp hsub')))
  have hi2 : Integrable (fun y => ρ r y * inner ℝ (meanFieldDrift D (ρ r) y) (Torus.grad h (x - y))) :=
    integrable_of_cont (hρc.mul (hu.inner (hgh.comp hsub')))
  rw [integral_sub hi1 hi2]
  unfold Jx
  congr 1
  have hF : Integrable (fun y : Torus d => ρ r y • Torus.grad h (x - y)) :=
    integrable_of_cont (hρc.smul (hgh.comp hsub'))
  rw [c.grad_fK hsm hev hr x, ← integral_inner hF]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [inner_smul_right]

theorem MFctx.Jx_swap (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) {r : ℝ} (hr : r ∈ Icc 0 T) :
    ∫ x, ρ r x * Jx D h ρ r x =
      -∫ x, ρ r x * inner ℝ (meanFieldDrift D (ρ r) x) (Torus.grad (fK h ρ r) x) := by
  have h1 := isCk1_of_smooth hsm
  have hρc := c.cont hr
  have hgh : Continuous (Torus.grad h) := HRS.PDE.MFLinear.continuous_grad h1
  have hu := c.ucont hr
  have hint : Integrable (Function.uncurry fun x y : Torus d =>
      ρ r x * (ρ r y * inner ℝ (meanFieldDrift D (ρ r) y) (Torus.grad h (x - y))))
      ((volume : Measure (Torus d)).prod volume) := by
    have hc : Continuous (Function.uncurry fun x y : Torus d =>
        ρ r x * (ρ r y * inner ℝ (meanFieldDrift D (ρ r) y) (Torus.grad h (x - y)))) := by
      refine Continuous.mul (hρc.comp continuous_fst) (Continuous.mul (hρc.comp continuous_snd) ?_)
      exact (hu.comp continuous_snd).inner (hgh.comp (continuous_fst.sub continuous_snd))
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold Jx
  have e1 : ∀ x, ρ r x * ∫ y, ρ r y * inner ℝ (meanFieldDrift D (ρ r) y) (Torus.grad h (x - y)) =
      ∫ y, ρ r x * (ρ r y * inner ℝ (meanFieldDrift D (ρ r) y) (Torus.grad h (x - y))) := fun x =>
    (integral_const_mul _ _).symm
  simp_rw [e1]
  rw [integral_integral_swap hint]
  have e2 : ∀ y, ∫ x, ρ r x * (ρ r y * inner ℝ (meanFieldDrift D (ρ r) y) (Torus.grad h (x - y))) =
      -(ρ r y * inner ℝ (meanFieldDrift D (ρ r) y) (Torus.grad (fK h ρ r) y)) := by
    intro y
    have hF : Integrable (fun x : Torus d => ρ r x • Torus.grad h (y - x)) :=
      integrable_of_cont (hρc.smul (hgh.comp (continuous_const.sub continuous_id)))
    have : ∀ x, ρ r x * (ρ r y * inner ℝ (meanFieldDrift D (ρ r) y) (Torus.grad h (x - y))) =
        -(ρ r y * inner ℝ (meanFieldDrift D (ρ r) y) (ρ r x • Torus.grad h (y - x))) := by
      intro x
      rw [show x - y = -(y - x) by abel, grad_odd h1 hev, inner_neg_right, inner_smul_right]
      ring
    simp_rw [this]
    rw [integral_neg, integral_const_mul, integral_inner hF, ← c.grad_fK hsm hev hr y]
  simp_rw [e2]
  rw [integral_neg]

theorem MFctx.Jx_cont (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h) {r : ℝ}
    (hr : r ∈ Icc 0 T) : Continuous (Jx D h ρ r) := by
  have h1 := isCk1_of_smooth hsm
  have hρc := c.cont hr
  have hgh : Continuous (Torus.grad h) := HRS.PDE.MFLinear.continuous_grad h1
  have hu := c.ucont hr
  obtain ⟨Bg, hBg0, hBg⟩ := exists_norm_bound (Torus.grad h) hgh
  obtain ⟨Bu, hBu0, hBu⟩ := exists_norm_bound (meanFieldDrift D (ρ r)) hu
  unfold Jx
  refine continuous_of_dominated (bound := fun _ => Λ * (Bu * Bg)) ?_ ?_ (integrable_const _) ?_
  · intro x
    exact (hρc.mul (hu.inner (hgh.comp (continuous_const.sub continuous_id)))).aestronglyMeasurable
  · intro x
    refine Eventually.of_forall fun y => ?_
    rw [norm_mul, Real.norm_eq_abs]
    refine mul_le_mul (c.abs_le hr y) ?_ (norm_nonneg _) c.Λ_nonneg
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul (hBu y) (hBg _) (norm_nonneg _) hBu0)
  · refine Eventually.of_forall fun y => ?_
    exact continuous_const.mul (continuous_const.inner (hgh.comp (continuous_id.sub continuous_const)))

theorem MFctx.comm_eval (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) {r : ℝ} (hr : r ∈ Icc 0 T) (hN : 0 < N) (X : Config d N)
    (hX : X ∉ collisionSet d N) :
    commQuantityWith (Torus.grad h) (meanFieldDrift D (ρ r)) X (withDensityReal (ρ r)) =
      (2 / (N : ℝ)) * ∑ i, inner ℝ (meanFieldDrift D (ρ r) (X i)) (Pvec h X i)
        - (2 / (N : ℝ)) * ∑ i, (inner ℝ (meanFieldDrift D (ρ r) (X i)) (Torus.grad (fK h ρ r) (X i))
            - Jx D h ρ r (X i))
        + 2 * ∫ x, ρ r x * inner ℝ (meanFieldDrift D (ρ r) x) (Torus.grad (fK h ρ r) x) := by
  have h1 := isCk1_of_smooth hsm
  have hρc := c.cont hr
  have hgh : Continuous (Torus.grad h) := HRS.PDE.MFLinear.continuous_grad h1
  have hφ : Torus.IsCk 2 (fK h ρ r) := ContDiff.of_le (c.contDiff_fK hsm hev hr) two_le_top
  have hgφ : Continuous (Torus.grad (fK h ρ r)) :=
    HRS.PDE.MFLinear.continuous_grad (hφ.of_le (by norm_num))
  have hu := c.ucont hr
  unfold commQuantityWith offDiagPairing
  -- the particle part
  have hodd : ∀ i j : Fin N, Torus.grad h (X j - X i) = -Torus.grad h (X i - X j) := by
    intro i j
    rw [show X j - X i = -(X i - X j) by abel, grad_odd h1 hev]
  have hpart : ∑ i, ∑ j ∈ Finset.univ.erase i,
      commKernel (Torus.grad h) (meanFieldDrift D (ρ r)) (X i) (X j) =
      2 * ∑ i, inner ℝ (meanFieldDrift D (ρ r) (X i)) (∑ j ∈ Finset.univ.erase i, Torus.grad h (X i - X j)) := by
    have hsym := sum_inner_offdiag_symm (fun i => meanFieldDrift D (ρ r) (X i))
      (fun i j => Torus.grad h (X i - X j)) (fun i j => hodd i j)
    have hk : ∀ i, ∑ j ∈ Finset.univ.erase i,
        commKernel (Torus.grad h) (meanFieldDrift D (ρ r)) (X i) (X j) =
        ∑ j ∈ Finset.univ.erase i, inner ℝ (meanFieldDrift D (ρ r) (X i) - meanFieldDrift D (ρ r) (X j))
          (Torus.grad h (X i - X j)) := by
      intro i
      refine Finset.sum_congr rfl fun j hj => ?_
      have hne : X i ≠ X j := fun h' => hX ⟨i, j, (Finset.ne_of_mem_erase hj).symm, h'⟩
      simp [commKernel, hne]
    simp only [hk]
    simp only [← inner_sum] at hsym
    linarith
  have hP : ∀ i, ∑ j ∈ Finset.univ.erase i, Torus.grad h (X i - X j) = (N : ℝ) • Pvec h X i := by
    intro i
    unfold Pvec
    rw [smul_smul, mul_one_div_cancel (by exact_mod_cast hN.ne'), one_smul]
  simp only [hpart, hP, inner_smul_right, ← Finset.mul_sum]
  have hCx : ∀ x, ∫ y, commKernel (Torus.grad h) (meanFieldDrift D (ρ r)) x y ∂(withDensityReal (ρ r)) =
      inner ℝ (meanFieldDrift D (ρ r) x) (Torus.grad (fK h ρ r) x) - Jx D h ρ r x :=
    fun x => c.Cx_eq hsm hev hr x
  simp only [hCx]
  rw [HRS.PDE.MFPairing.integral_withDensityReal (c.dens hr).measurable (c.dens hr).nonneg]
  have hi1 : Integrable (fun x => ρ r x * inner ℝ (meanFieldDrift D (ρ r) x) (Torus.grad (fK h ρ r) x)) :=
    integrable_of_cont (hρc.mul (hu.inner hgφ))
  have hi2 : Integrable (fun x => ρ r x * Jx D h ρ r x) :=
    integrable_of_cont (hρc.mul (c.Jx_cont hsm hr))
  have e : ∀ x, ρ r x * (inner ℝ (meanFieldDrift D (ρ r) x) (Torus.grad (fK h ρ r) x) - Jx D h ρ r x) =
      ρ r x * inner ℝ (meanFieldDrift D (ρ r) x) (Torus.grad (fK h ρ r) x) - ρ r x * Jx D h ρ r x := by
    intro x; ring
  simp_rw [e]
  rw [integral_sub hi1 hi2, c.Jx_swap hsm hev hr]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

theorem MFctx.selfForce_grad (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) {r : ℝ} (hr : r ∈ Icc 0 T) (X : Config d N) (i : Fin N) :
    selfForce (Torus.grad h) (ρ r) X i = Pvec h X i - Torus.grad (fK h ρ r) (X i) := by
  have h1 := isCk1_of_smooth hsm
  have hgh : Continuous (Torus.grad h) := HRS.PDE.MFLinear.continuous_grad h1
  have hodd : ∀ z, Torus.grad h (-z) = -Torus.grad h z := fun z => grad_odd h1 hev z
  unfold selfForce Pvec
  rw [convGradConv_odd (Torus.grad h) hgh hodd (ρ r) (c.cont hr), ← c.grad_fK hsm hev hr]

theorem MFctx.particleDrift_eq (c : MFctx D T Λ ρ) (X : Config d N) (i : Fin N) {r : ℝ} :
    particleDrift D X i = Torus.matVec D.M (selfForce (periodicRieszGrad d D.s) (ρ r) X i) +
      meanFieldDrift D (ρ r) (X i) := by
  unfold particleDrift selfForce meanFieldDrift
  simp only [Torus.matVec, map_sub, map_smul, map_sum]
  abel

theorem MFctx.ftK_eq' (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) {r : ℝ} (hr : r ∈ Icc 0 T) (x : Torus d) :
    ftK D h ρ r x = D.invβ * Torus.laplacian (fK h ρ r) x - Jx D h ρ r x := by
  rw [c.ftK_eq hsm hev hr x]
  unfold Jx
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [real_inner_comm]

theorem MFctx.main_alg (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) {r : ℝ} (hr : r ∈ Icc 0 T) (hN : 0 < N) (X : Config d N)
    (hX : X ∉ collisionSet d N) :
    ppDrift D h X - fDrift D h ρ r X + wkG D ρ (fK h ρ r) r =
      (1 / 2) * commQuantityWith (Torus.grad h) (meanFieldDrift D (ρ r)) X (withDensityReal (ρ r)) +
        microTerm D h (ρ r) X +
        D.invβ * offDiagDiffPairing (Torus.laplacian h) X (withDensityReal (ρ r)) := by
  rw [c.comm_eval hsm hev hr hN X hX, c.offDiag_eval hsm hev hr hN X hX, c.w_eq hsm hev hr]
  unfold ppDrift fDrift microTerm
  have hb : ∀ i, particleDrift D X i = Torus.matVec D.M (selfForce (periodicRieszGrad d D.s) (ρ r) X i) +
      meanFieldDrift D (ρ r) (X i) := fun i => c.particleDrift_eq X i
  have ha : ∀ i, selfForce (Torus.grad h) (ρ r) X i = Pvec h X i - Torus.grad (fK h ρ r) (X i) :=
    fun i => c.selfForce_grad hsm hev hr X i
  have hft : ∀ i, ftK D h ρ r (X i) = D.invβ * Torus.laplacian (fK h ρ r) (X i) - Jx D h ρ r (X i) :=
    fun i => c.ftK_eq' hsm hev hr (X i)
  simp only [ha, hb, hft, inner_add_right, inner_sub_left]
  have hI : ∫ x, ρ r x * inner ℝ (meanFieldDrift D (ρ r) x) (Torus.grad (fK h ρ r) x) =
      ∫ y, ρ r y * inner ℝ (Torus.grad (fK h ρ r) y) (meanFieldDrift D (ρ r) y) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [real_inner_comm]
  have c1 : ∀ i, inner ℝ (meanFieldDrift D (ρ r) (X i)) (Pvec h X i) =
      inner ℝ (Pvec h X i) (meanFieldDrift D (ρ r) (X i)) := fun i => real_inner_comm _ _
  have c2 : ∀ i, inner ℝ (meanFieldDrift D (ρ r) (X i)) (Torus.grad (fK h ρ r) (X i)) =
      inner ℝ (Torus.grad (fK h ρ r) (X i)) (meanFieldDrift D (ρ r) (X i)) := fun i => real_inner_comm _ _
  simp only [hI, c1, c2, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

end Formulas

end HRS.KID
