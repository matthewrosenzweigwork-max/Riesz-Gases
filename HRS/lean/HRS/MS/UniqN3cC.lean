import HRS.MS.UniqN3cB

/-!
# N3c, part C: `√ρ` is Lipschitz for `ρ ≥ 0` of class `C²` with bounded Hessian

`n3c_grad_sq`: `‖∇φ‖² ≤ 2 B φ` for `φ ≥ 0` with `‖D²φ‖ ≤ B`, `B > 0` (Taylor upper bound at `x + h`,
`h = -∇φ(x)/B`);  `n3c_sqrt_lip`: `√φ` is `√(B/2)`-Lipschitz (regularization `√(φ + ε)`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN3c

variable {d : ℕ}

/-- Taylor upper bound for a `C²` function with Hessian bounded by `B`. -/
theorem n3c_taylor {φ : Euc d → ℝ} (hφ : ContDiff ℝ 2 φ) {B : ℝ}
    (hB : ∀ x, ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ B) (x h : Euc d) :
    φ (x + h) ≤ φ x + fderiv ℝ φ x h + B * ‖h‖ ^ 2 / 2 := by
  have hd1 : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hB0 : 0 ≤ B := le_trans (ContinuousLinearMap.opNorm_nonneg _) (hB 0)
  have hlip : ∀ y z, ‖fderiv ℝ φ y - fderiv ℝ φ z‖ ≤ B * ‖y - z‖ := fun y z => by
    have := convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun w _ => hd2 w) (fun w _ => hB w)
      (Set.mem_univ z) (Set.mem_univ y)
    simpa using this
  set g : ℝ → ℝ := fun t => φ (x + t • h) - t * fderiv ℝ φ x h - B * ‖h‖ ^ 2 * t ^ 2 / 2 with hg
  have hgd : ∀ t : ℝ, HasDerivAt g (fderiv ℝ φ (x + t • h) h - fderiv ℝ φ x h - B * ‖h‖ ^ 2 * t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x + t • h) h t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_add x
    have h2 := (hd1 (x + t • h)).hasFDerivAt.comp_hasDerivAt t h1
    have h3 : HasDerivAt (fun t : ℝ => t * fderiv ℝ φ x h) (fderiv ℝ φ x h) t := by
      simpa using (hasDerivAt_id t).mul_const (fderiv ℝ φ x h)
    have h4 : HasDerivAt (fun t : ℝ => B * ‖h‖ ^ 2 * t ^ 2 / 2) (B * ‖h‖ ^ 2 * t) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (B * ‖h‖ ^ 2)).div_const 2
      convert this using 1; simp; ring
    exact (h2.sub h3).sub h4
  have hanti : AntitoneOn g (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) (fun t _ => (hgd t).continuousAt.continuousWithinAt)
      (fun t _ => (hgd t).differentiableAt.differentiableWithinAt) (fun t ht => ?_)
    rw [interior_Ici] at ht
    have ht0 : 0 < t := ht
    rw [(hgd t).deriv]
    have h5 : fderiv ℝ φ (x + t • h) h - fderiv ℝ φ x h ≤ B * ‖h‖ ^ 2 * t := by
      calc fderiv ℝ φ (x + t • h) h - fderiv ℝ φ x h
          = (fderiv ℝ φ (x + t • h) - fderiv ℝ φ x) h := by simp
        _ ≤ ‖(fderiv ℝ φ (x + t • h) - fderiv ℝ φ x) h‖ := le_abs_self _
        _ ≤ ‖fderiv ℝ φ (x + t • h) - fderiv ℝ φ x‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (B * ‖x + t • h - x‖) * ‖h‖ := by gcongr; exact hlip _ _
        _ = B * ‖h‖ ^ 2 * t := by
            rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]; ring
    linarith
  have := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 zero_le_one) zero_le_one
  simp only [hg, zero_smul, add_zero, zero_mul, sub_zero, one_smul, one_mul] at this
  norm_num at this
  linarith

/-- `‖∇φ‖² ≤ 2 B φ`. -/
theorem n3c_grad_sq {φ : Euc d → ℝ} (hφ : ContDiff ℝ 2 φ) (h0 : ∀ x, 0 ≤ φ x) {B : ℝ}
    (hB0 : 0 < B) (hB : ∀ x, ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ B) (x : Euc d) :
    ‖fderiv ℝ φ x‖ ^ 2 ≤ 2 * B * φ x := by
  set w : Euc d := (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ φ x) with hw
  have hwn : ‖w‖ = ‖fderiv ℝ φ x‖ := by rw [hw]; exact LinearIsometryEquiv.norm_map _ _
  have hwv : ∀ h, fderiv ℝ φ x h = inner ℝ w h := fun h => by
    rw [hw, InnerProductSpace.toDual_symm_apply]
  have h1 := n3c_taylor hφ hB x (-(1 / B) • w)
  have h2 := h0 (x + -(1 / B) • w)
  rw [hwv, inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs] at h1
  have h3 : |(-(1 / B))| = 1 / B := by rw [abs_neg, abs_of_pos (by positivity)]
  rw [h3] at h1
  rw [← hwn]
  have h4 : 0 ≤ φ x - ‖w‖ ^ 2 / (2 * B) := by
    have : φ x + -(1 / B) * ‖w‖ ^ 2 + B * (1 / B * ‖w‖) ^ 2 / 2 = φ x - ‖w‖ ^ 2 / (2 * B) := by
      field_simp; ring
    linarith
  have h5 : ‖w‖ ^ 2 / (2 * B) ≤ φ x := by linarith
  rw [div_le_iff₀ (by positivity)] at h5
  linarith

theorem n3c_sqrt_add_le (b ε : ℝ) (hb : 0 ≤ b) (hε : 0 ≤ ε) :
    Real.sqrt (b + ε) ≤ Real.sqrt b + Real.sqrt ε := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt hb, Real.sq_sqrt hε, mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg ε)]

/-- **`√φ` is Lipschitz.** -/
theorem n3c_sqrt_lip {φ : Euc d → ℝ} (hφ : ContDiff ℝ 2 φ) (h0 : ∀ x, 0 ≤ φ x) {B : ℝ}
    (hB : ∀ x, ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ B) :
    HRS.PDE.ToolboxRd.IsLipschitz (Real.sqrt ((B + 1) / 2)) (fun x => Real.sqrt (φ x)) := by
  have hB0 : 0 ≤ B := le_trans (ContinuousLinearMap.opNorm_nonneg _) (hB 0)
  have hB1 : 0 < B + 1 := by linarith
  have hB' : ∀ x, ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ B + 1 := fun x => (hB x).trans (by linarith)
  have hd1 : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  set L : ℝ := Real.sqrt ((B + 1) / 2) with hL
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  -- the regularization
  have key : ∀ ε : ℝ, 0 < ε → ∀ x y : Euc d,
      |Real.sqrt (φ x + ε) - Real.sqrt (φ y + ε)| ≤ L * ‖x - y‖ := by
    intro ε hε x y
    have hpos : ∀ z, 0 < φ z + ε := fun z => by linarith [h0 z]
    have hder : ∀ z, HasFDerivAt (fun w => Real.sqrt (φ w + ε))
        ((1 / (2 * Real.sqrt (φ z + ε))) • fderiv ℝ φ z) z := fun z =>
      ((hd1 z).hasFDerivAt.add_const ε).sqrt (hpos z).ne'
    have hbd : ∀ z, ‖(1 / (2 * Real.sqrt (φ z + ε))) • fderiv ℝ φ z‖ ≤ L := by
      intro z
      have hs : 0 < Real.sqrt (φ z + ε) := Real.sqrt_pos.2 (hpos z)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have h1 := n3c_grad_sq hφ h0 hB1 hB' z
      have h2 : ‖fderiv ℝ φ z‖ ≤ Real.sqrt (2 * (B + 1) * φ z) :=
        Real.le_sqrt_of_sq_le h1
      have h3 : Real.sqrt (2 * (B + 1) * φ z) ≤ Real.sqrt (2 * (B + 1)) * Real.sqrt (φ z + ε) := by
        rw [← Real.sqrt_mul (by positivity)]
        exact Real.sqrt_le_sqrt (by nlinarith [h0 z])
      have h4 : Real.sqrt (2 * (B + 1)) = 2 * L := by
        rw [hL]
        have : 2 * (B + 1) = 2 ^ 2 * ((B + 1) / 2) := by ring
        rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
      rw [one_div, inv_mul_le_iff₀ (by positivity)]
      calc ‖fderiv ℝ φ z‖ ≤ 2 * L * Real.sqrt (φ z + ε) := by rw [← h4]; exact h2.trans h3
        _ = 2 * Real.sqrt (φ z + ε) * L := by ring
    have := convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z _ => (hder z).hasFDerivWithinAt) (fun z _ => hbd z) (Set.mem_univ y) (Set.mem_univ x)
    simpa [Real.norm_eq_abs] using this
  intro x y
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hε := key (δ ^ 2) (by positivity) x y
  have hsδ : Real.sqrt (δ ^ 2) = δ := Real.sqrt_sq hδ.le
  have e1 := n3c_sqrt_add_le (φ x) (δ ^ 2) (h0 x) (sq_nonneg _)
  have e2 := n3c_sqrt_add_le (φ y) (δ ^ 2) (h0 y) (sq_nonneg _)
  have e3 : Real.sqrt (φ x) ≤ Real.sqrt (φ x + δ ^ 2) := Real.sqrt_le_sqrt (by linarith [sq_nonneg δ])
  have e4 : Real.sqrt (φ y) ≤ Real.sqrt (φ y + δ ^ 2) := Real.sqrt_le_sqrt (by linarith [sq_nonneg δ])
  rw [hsδ] at e1 e2
  rw [abs_le] at hε ⊢
  constructor <;> linarith [hε.1, hε.2]

end HRS.MS.UniqN3c
