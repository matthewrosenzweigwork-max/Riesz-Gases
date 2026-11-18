import HRS.MS.MovOpAux8
import HRS.MS.MovForceTie
import HRS.MS.MovLinAux2
import HRS.MS.R2ScrAux2

/-!
# MOV-2a, part 1: the ground-state transform of the linearised generator `S` (S6.2, TeX L4278-4343)

Namespace `HRS.MS.MovLin`, helper prefix `mov2a_`.  Infrastructure for S6.2 (`W:lem:r2mov-linear`); not a manuscript row.

For the frozen operator (`HRS.Whole.movS`)
`S v = -ρ^{-1/2} div(ρ ∇(ν v/√ρ)) + P v`, `ν = β⁻¹`,
and a smooth positive `ρ` we prove (`mov_S_ground_state_gen`, any `β`) that for `v ∈ C^∞`
`S v = ν(-Δ v + V v) + P v`, `V = (1/4)|∇ log ρ|² + (1/2) Δ log ρ` (`mov2a_V`),
and the thermal instance `mov_S_ground_state` for `IsThermalEquilibrium d s q β ρ` and `v` Schwartz.
The proof is the pointwise identity `ρ ∇(v/√ρ) = √ρ ∇v - v ∇√ρ` (so `div(ρ ∇(v/√ρ)) = √ρ Δv - v Δ√ρ`)
together with `Δ√ρ = √ρ V`.  No junk-value branch occurs: all fields involved are `C^∞` and `ρ > 0`, which the
hypotheses of the generic form include.

Statement adjustments relative to the plan sketch: the Laplacian is `Laplacian.laplacian` (as in `mov_S0`), the
smoothness hypothesis on `v` is `C^∞` (Schwartz functions are).  The decomposition of `V` and the bounds on `V_1`
are in `MovLinAux6`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovLin

open HRS HRS.Whole

variable {d : ℕ}

/-- The ground-state potential `V = (1/4)|∇ log ρ|² + (1/2) Δ log ρ`. -/
def mov2a_V (ρ : Euc d → ℝ) (x : Euc d) : ℝ :=
  (1 / 4) * ‖gradient (fun y => Real.log (ρ y)) x‖ ^ 2 +
    (1 / 2) * Laplacian.laplacian (fun y => Real.log (ρ y)) x

/-! ### Elementary calculus -/

lemma mov2a_sum_fderiv_mul (f : Euc d → ℝ) (x G : Euc d) :
    ∑ i, fderiv ℝ f x (EuclideanSpace.single i 1) * G i = inner ℝ (gradient f x) G := by
  rw [← HRS.MS.Gap.gap1_sum_inner (gradient f x) G]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [HRS.MS.PoisKolm.kl_inner_gradient, EuclideanSpace.inner_single_left]
  simp

lemma mov2a_gradient_diff {u : Euc d → ℝ} (hu : ContDiff ℝ ∞ u) (x : Euc d) :
    DifferentiableAt ℝ (fun y => gradient u y) x :=
  ((HRS.MS.Gap.gap1_contDiff_gradient hu 1).differentiable (by norm_num)) x

lemma mov2a_movDiv_add {A B : Euc d → Euc d} {x : Euc d} (hA : DifferentiableAt ℝ A x)
    (hB : DifferentiableAt ℝ B x) : movDiv (fun y => A y + B y) x = movDiv A x + movDiv B x := by
  unfold movDiv
  have h : fderiv ℝ (fun y => A y + B y) x = fderiv ℝ A x + fderiv ℝ B x :=
    (hA.hasFDerivAt.add hB.hasFDerivAt).fderiv
  rw [h]
  simp [Finset.sum_add_distrib]

lemma mov2a_movDiv_gradient {u : Euc d → ℝ} (hu : ContDiff ℝ ∞ u) (x : Euc d) :
    movDiv (fun y => gradient u y) x = Laplacian.laplacian u x :=
  HRS.MS.S98.s98_movDiv_gradient (hu.of_le (by simp)) x

/-- `∇ √ρ = (1/2) √ρ ∇ log ρ`. -/
lemma mov2a_grad_sqrt {ρ : Euc d → ℝ} (hρ : Differentiable ℝ ρ) (hpos : ∀ x, 0 < ρ x) (x : Euc d) :
    gradient (fun y => Real.sqrt (ρ y)) x =
      ((1 / 2) * Real.sqrt (ρ x)) • gradient (fun y => Real.log (ρ y)) x := by
  refine ext_inner_left ℝ fun e => ?_
  rw [inner_smul_right]
  simp only [HRS.MS.PoisKolm.kl_inner_gradient]
  exact HRS.MS.MovForce.mv1_fderiv_sqrt (hρ x) (hpos x) e

/-- `Δ √ρ = √ρ V`. -/
theorem mov2a_laplacian_sqrt {ρ : Euc d → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ x, 0 < ρ x) (x : Euc d) :
    Laplacian.laplacian (fun y => Real.sqrt (ρ y)) x = Real.sqrt (ρ x) * mov2a_V ρ x := by
  have hψ : ContDiff ℝ ∞ (fun y => Real.sqrt (ρ y)) := hρ.sqrt fun x => (hpos x).ne'
  have hφ : ContDiff ℝ ∞ (fun y => Real.log (ρ y)) := hρ.log fun x => (hpos x).ne'
  have hρd : Differentiable ℝ ρ := hρ.differentiable (by simp)
  rw [← mov2a_movDiv_gradient hψ]
  have e1 : (fun y => gradient (fun z => Real.sqrt (ρ z)) y) =
      fun y => ((1 / 2) * Real.sqrt (ρ y)) • gradient (fun z => Real.log (ρ z)) y :=
    funext fun y => mov2a_grad_sqrt hρd hpos y
  rw [e1]
  have hcd : DifferentiableAt ℝ (fun y => (1 / 2) * Real.sqrt (ρ y)) x :=
    (hψ.differentiable (by simp) x).const_mul _
  rw [HRS.MS.MovForce.mv1_movDiv_smul hcd (mov2a_gradient_diff hφ x), mov2a_movDiv_gradient hφ]
  have hfd : fderiv ℝ (fun y => (1 / 2) * Real.sqrt (ρ y)) x =
      (1 / 2 : ℝ) • fderiv ℝ (fun y => Real.sqrt (ρ y)) x := by
    rw [fderiv_const_mul (hψ.differentiable (by simp) x)]
  have hsum : ∑ i, fderiv ℝ (fun y => (1 / 2) * Real.sqrt (ρ y)) x (EuclideanSpace.single i 1) *
      (gradient (fun z => Real.log (ρ z)) x) i =
      (1 / 4) * Real.sqrt (ρ x) * ‖gradient (fun y => Real.log (ρ y)) x‖ ^ 2 := by
    have : ∀ i : Fin d, fderiv ℝ (fun y => (1 / 2) * Real.sqrt (ρ y)) x (EuclideanSpace.single i 1) *
        (gradient (fun z => Real.log (ρ z)) x) i =
        (1 / 4) * Real.sqrt (ρ x) * (fderiv ℝ (fun y => Real.log (ρ y)) x (EuclideanSpace.single i 1) *
        (gradient (fun z => Real.log (ρ z)) x) i) := by
      intro i
      rw [hfd, smul_apply, ← HRS.MS.PoisKolm.kl_inner_gradient,
        mov2a_grad_sqrt hρd hpos x, inner_smul_right, HRS.MS.PoisKolm.kl_inner_gradient]
      simp only [smul_eq_mul]
      ring
    simp_rw [this]
    rw [← Finset.mul_sum, mov2a_sum_fderiv_mul, real_inner_self_eq_norm_sq]
  rw [hsum]
  unfold mov2a_V
  ring

/-! ### The ground-state transform -/

/-- The flux identity `ρ ∇(β⁻¹ v/√ρ) = β⁻¹ (√ρ ∇v - v ∇√ρ)`. -/
lemma mov2a_flux {ρ : Euc d → ℝ} {β : ℝ} (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ x, 0 < ρ x)
    {v : Euc d → ℝ} (hv : ContDiff ℝ ∞ v) (y : Euc d) :
    ρ y • gradient (fun z => β⁻¹ * (v z / Real.sqrt (ρ z))) y =
      (β⁻¹ * Real.sqrt (ρ y)) • gradient v y +
        (-(β⁻¹ * v y)) • gradient (fun z => Real.sqrt (ρ z)) y := by
  have hψ : ContDiff ℝ ∞ (fun y => Real.sqrt (ρ y)) := hρ.sqrt fun x => (hpos x).ne'
  have hs : 0 < Real.sqrt (ρ y) := Real.sqrt_pos.2 (hpos y)
  have hss : Real.sqrt (ρ y) * Real.sqrt (ρ y) = ρ y := Real.mul_self_sqrt (hpos y).le
  have hvd : HasFDerivAt v (fderiv ℝ v y) y := (hv.differentiable (by simp) y).hasFDerivAt
  have hψd : HasFDerivAt (fun z => Real.sqrt (ρ z)) (fderiv ℝ (fun z => Real.sqrt (ρ z)) y) y :=
    (hψ.differentiable (by simp) y).hasFDerivAt
  have hinv : HasFDerivAt (fun z => (Real.sqrt (ρ z))⁻¹)
      ((-(Real.sqrt (ρ y) ^ 2)⁻¹) • fderiv ℝ (fun z => Real.sqrt (ρ z)) y) y :=
    (hasDerivAt_inv hs.ne').comp_hasFDerivAt y hψd
  have hw : HasFDerivAt (fun z => β⁻¹ * (v z * (Real.sqrt (ρ z))⁻¹))
      (β⁻¹ • (v y • ((-(Real.sqrt (ρ y) ^ 2)⁻¹) • fderiv ℝ (fun z => Real.sqrt (ρ z)) y) +
        (Real.sqrt (ρ y))⁻¹ • fderiv ℝ v y)) y :=
    (hvd.mul hinv).const_mul β⁻¹
  have hfun : (fun z => β⁻¹ * (v z / Real.sqrt (ρ z))) = fun z => β⁻¹ * (v z * (Real.sqrt (ρ z))⁻¹) := by
    funext z; rw [div_eq_mul_inv]
  rw [hfun]
  refine ext_inner_left ℝ fun e => ?_
  rw [inner_smul_right, inner_add_right, inner_smul_right, inner_smul_right]
  simp only [HRS.MS.PoisKolm.kl_inner_gradient, hw.fderiv]
  simp only [smul_apply, add_apply, smul_eq_mul]
  generalize Real.sqrt (ρ y) = a at hs hss ⊢
  rw [← hss]
  field_simp
  ring

/-- **Ground-state transform, generic form.**  For `ρ > 0` smooth (any `β`) and `v ∈ C^∞`:
`-ρ^{-1/2} div(ρ ∇(β⁻¹ v/√ρ)) = β⁻¹ (-Δ v + V v)`. -/
theorem mov2a_diffusion_gen {ρ : Euc d → ℝ} {β : ℝ} (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ x, 0 < ρ x)
    {v : Euc d → ℝ} (hv : ContDiff ℝ ∞ v) (x : Euc d) :
    -(Real.sqrt (ρ x))⁻¹ *
        movDiv (fun y => ρ y • gradient (fun z => β⁻¹ * (v z / Real.sqrt (ρ z))) y) x =
      β⁻¹ * (-Laplacian.laplacian v x + mov2a_V ρ x * v x) := by
  have hψ : ContDiff ℝ ∞ (fun y => Real.sqrt (ρ y)) := hρ.sqrt fun x => (hpos x).ne'
  have hs : 0 < Real.sqrt (ρ x) := Real.sqrt_pos.2 (hpos x)
  have e1 : (fun y => ρ y • gradient (fun z => β⁻¹ * (v z / Real.sqrt (ρ z))) y) =
      fun y => ((β⁻¹ * Real.sqrt (ρ y)) • gradient v y +
        (-(β⁻¹ * v y)) • gradient (fun z => Real.sqrt (ρ z)) y) :=
    funext fun y => mov2a_flux hρ hpos hv y
  rw [e1]
  have hc1 : DifferentiableAt ℝ (fun y => β⁻¹ * Real.sqrt (ρ y)) x :=
    (hψ.differentiable (by simp) x).const_mul _
  have hc2 : DifferentiableAt ℝ (fun y => -(β⁻¹ * v y)) x :=
    ((hv.differentiable (by simp) x).const_mul _).neg
  have hd1 : DifferentiableAt ℝ (fun y => (β⁻¹ * Real.sqrt (ρ y)) • gradient v y) x :=
    hc1.smul (mov2a_gradient_diff hv x)
  have hd2 : DifferentiableAt ℝ (fun y => (-(β⁻¹ * v y)) • gradient (fun z => Real.sqrt (ρ z)) y) x :=
    hc2.smul (mov2a_gradient_diff hψ x)
  rw [mov2a_movDiv_add hd1 hd2, HRS.MS.MovForce.mv1_movDiv_smul hc1 (mov2a_gradient_diff hv x),
    HRS.MS.MovForce.mv1_movDiv_smul hc2 (mov2a_gradient_diff hψ x),
    mov2a_movDiv_gradient hv, mov2a_movDiv_gradient hψ, mov2a_laplacian_sqrt hρ hpos x]
  have hf1 : fderiv ℝ (fun y => β⁻¹ * Real.sqrt (ρ y)) x =
      β⁻¹ • fderiv ℝ (fun y => Real.sqrt (ρ y)) x := by
    rw [fderiv_const_mul (hψ.differentiable (by simp) x)]
  have hf2 : fderiv ℝ (fun y => -(β⁻¹ * v y)) x = -(β⁻¹ • fderiv ℝ v x) := by
    exact ((hv.differentiable (by simp) x).hasFDerivAt.const_mul β⁻¹).neg.fderiv
  have s1 : ∑ i, fderiv ℝ (fun y => β⁻¹ * Real.sqrt (ρ y)) x (EuclideanSpace.single i 1) *
      (gradient v x) i = β⁻¹ * inner ℝ (gradient (fun y => Real.sqrt (ρ y)) x) (gradient v x) := by
    rw [← mov2a_sum_fderiv_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hf1]; simp only [smul_apply, smul_eq_mul]; ring
  have s2 : ∑ i, fderiv ℝ (fun y => -(β⁻¹ * v y)) x (EuclideanSpace.single i 1) *
      (gradient (fun z => Real.sqrt (ρ z)) x) i =
      -(β⁻¹ * inner ℝ (gradient v x) (gradient (fun y => Real.sqrt (ρ y)) x)) := by
    rw [← mov2a_sum_fderiv_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hf2]; simp only [neg_apply, smul_apply, smul_eq_mul]; ring
  rw [s1, s2, real_inner_comm (gradient v x)]
  field_simp
  ring

/-- **Ground-state transform for `movS`, generic form** (any smooth positive `ρ`, any `β`, `v ∈ C^∞`):
`S v = β⁻¹ (-Δ v + V v) + P v`. -/
theorem mov_S_ground_state_gen {s β : ℝ} {ρ : Euc d → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ x, 0 < ρ x)
    {v : Euc d → ℝ} (hv : ContDiff ℝ ∞ v) (x : Euc d) :
    movS d s β ρ v x =
      β⁻¹ * (-Laplacian.laplacian v x + mov2a_V ρ x * v x) + movP d s ρ v x := by
  unfold movS
  rw [mov2a_diffusion_gen hρ hpos hv x]

/-- **MOV-2a, ground-state transform (S6.2, TeX L4278-4343).**  For a thermal equilibrium `ρ` and Schwartz `v`:
`movS d s β ρ v = ν(-Δ v + V v) + movP d s ρ v`, `ν = β⁻¹`, `V = (1/4)|∇ log ρ|² + (1/2) Δ log ρ`. -/
theorem mov_S_ground_state {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ) (hβ : 0 < β)
    (hq : 0 < q) (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ) (v : SchwartzMap (Euc d) ℝ)
    (x : Euc d) :
    movS d s β ρ v x =
      β⁻¹ * (-Laplacian.laplacian (v : Euc d → ℝ) x + mov2a_V ρ x * v x) + movP d s ρ v x := by
  obtain ⟨B, -, hR, -⟩ := HRS.MS.Mov0.mv0_gapref hd hs0 hsd hq hβ hρ
  exact mov_S_ground_state_gen hR.smooth hR.pos (v.smooth ⊤) x

end HRS.MS.MovLin

end
