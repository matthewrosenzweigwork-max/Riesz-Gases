import HRS.MS.MovForceAux2

/-!
# MOV-B1 (3): Gaussian bounds of `h = ψ v`, the data structure `MovRhoData`, and the formulas for `P`, `B`

Namespace `HRS.MS.MovForce`, prefix `mv1_`.

* `MovRhoData d ρ` (Prop structure): `ρ > 0`, `ρ ∈ C^∞`, and Gaussian bounds `‖D^k √ρ‖ ≤ C e^{-c‖x‖²}`
  for all `k` (the output of MOV-0, `mv0_sqrt_gauss`).
* `mv1_h_gauss`: for `v` Schwartz, `h = √ρ · v` is `C^∞` with `MovGauss k h` for every `k`.
* `mv1_P_formula`: `movP d s ρ v x = -√(ρ x) (g*Δh (x) + ∑_i ∂_i log ρ (x) · (g*∂_i h)(x))`, `h = √ρ v`
  (the scalar product `⟨∇log ρ, g*∇h⟩` is written as a sum over coordinates; `mv1_P_formula_inner` gives the
  inner-product form with the vector `movForce d s h x = ∇(g*h)(x)`).
* `mv1_B_formula`: `movB d s ρ v w x = ∑_i ∂_i v (g*∂_i h_w) + v (g*Δh_w + (1/2) ∑_i ∂_i log ρ (g*∂_i h_w))`,
  `h_w = √ρ w`, for `v ∈ C¹` and `w` Schwartz.

No statement was weakened relative to the brief, except that the hypothesis `2 ≤ d` of the brief is `1 ≤ d` here.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovForce

open HRS.Whole

variable {d : ℕ}

/-- Thermal data on `ρ` needed for the formulas of `P` and `B` (to be instantiated by MOV-0). -/
structure MovRhoData (d : ℕ) (ρ : Euc d → ℝ) : Prop where
  pos : ∀ x, 0 < ρ x
  smooth : ContDiff ℝ ∞ ρ
  sqrt_gauss : ∀ k : ℕ, ∃ C c : ℝ, 0 < c ∧
    ∀ x, ‖iteratedFDeriv ℝ k (fun y => Real.sqrt (ρ y)) x‖ ≤ C * Real.exp (-c * ‖x‖ ^ 2)

lemma MovRhoData.sqrt_smooth {ρ : Euc d → ℝ} (hρ : MovRhoData d ρ) :
    ContDiff ℝ ∞ (fun y => Real.sqrt (ρ y)) :=
  hρ.smooth.sqrt fun x => (hρ.pos x).ne'

/-- A single Gaussian rate working for the first `k+1` derivatives. -/
lemma mv1_gauss_common {ψ : Euc d → ℝ}
    (hψ : ∀ k : ℕ, ∃ C c : ℝ, 0 < c ∧ ∀ x, ‖iteratedFDeriv ℝ k ψ x‖ ≤ C * Real.exp (-c * ‖x‖ ^ 2))
    (k : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ j, j ≤ k → ∃ C : ℝ, ∀ x,
      ‖iteratedFDeriv ℝ j ψ x‖ ≤ C * Real.exp (-c * ‖x‖ ^ 2) := by
  induction k with
  | zero =>
    obtain ⟨C, c, hc, hb⟩ := hψ 0
    exact ⟨c, hc, fun j hj => ⟨C, by
      have : j = 0 := by omega
      subst this; exact hb⟩⟩
  | succ k ih =>
    obtain ⟨c', hc', hj⟩ := ih
    obtain ⟨C, c, hc, hb⟩ := hψ (k + 1)
    refine ⟨min c' c, lt_min hc' hc, fun j hjk => ?_⟩
    by_cases hjk' : j ≤ k
    · obtain ⟨C0, h0⟩ := hj j hjk'
      refine ⟨max C0 0, fun x => ?_⟩
      refine (h0 x).trans ?_
      have hexp : Real.exp (-c' * ‖x‖ ^ 2) ≤ Real.exp (-(min c' c) * ‖x‖ ^ 2) :=
        Real.exp_le_exp.mpr (by nlinarith [min_le_left c' c, sq_nonneg ‖x‖])
      calc C0 * Real.exp (-c' * ‖x‖ ^ 2) ≤ max C0 0 * Real.exp (-c' * ‖x‖ ^ 2) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
        _ ≤ _ := mul_le_mul_of_nonneg_left hexp (le_max_right _ _)
    · have : j = k + 1 := by omega
      subst this
      refine ⟨max C 0, fun x => ?_⟩
      refine (hb x).trans ?_
      have hexp : Real.exp (-c * ‖x‖ ^ 2) ≤ Real.exp (-(min c' c) * ‖x‖ ^ 2) :=
        Real.exp_le_exp.mpr (by nlinarith [min_le_right c' c, sq_nonneg ‖x‖])
      calc C * Real.exp (-c * ‖x‖ ^ 2) ≤ max C 0 * Real.exp (-c * ‖x‖ ^ 2) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
        _ ≤ _ := mul_le_mul_of_nonneg_left hexp (le_max_right _ _)

/-- Leibniz: a Gaussian-bounded smooth factor times a smooth factor with bounded derivatives has
Gaussian-bounded derivatives. -/
lemma mv1_gauss_mul {ψ v : Euc d → ℝ} (hψs : ContDiff ℝ ∞ ψ) (hvs : ContDiff ℝ ∞ v)
    (hψ : ∀ k : ℕ, ∃ C c : ℝ, 0 < c ∧ ∀ x, ‖iteratedFDeriv ℝ k ψ x‖ ≤ C * Real.exp (-c * ‖x‖ ^ 2))
    (hv : ∀ k : ℕ, ∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ k v x‖ ≤ M) (k : ℕ) :
    ∃ C c : ℝ, 0 < c ∧ ∀ x,
      ‖iteratedFDeriv ℝ k (fun y => ψ y * v y) x‖ ≤ C * Real.exp (-c * ‖x‖ ^ 2) := by
  obtain ⟨c, hc, hj⟩ := mv1_gauss_common hψ k
  choose! Cψ hCψ using hj
  choose Mv hMv using hv
  refine ⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Cψ i * Mv (k - i), c, hc, fun x => ?_⟩
  have h1 := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := (⊤ : ℕ∞)) hψs hvs x (n := k)
    (by exact_mod_cast le_top)
  refine h1.trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hik : i ≤ k := by simpa [Nat.lt_succ_iff] using hi
  have hb1 := hCψ i hik x
  have hb2 := hMv (k - i) x
  have hM : 0 ≤ Mv (k - i) := (norm_nonneg _).trans hb2
  calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ x‖ * ‖iteratedFDeriv ℝ (k - i) v x‖
      ≤ (k.choose i : ℝ) * (Cψ i * Real.exp (-c * ‖x‖ ^ 2)) * Mv (k - i) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hb1 (Nat.cast_nonneg _)) hb2 (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) ((norm_nonneg _).trans hb1))
    _ = _ := by ring

/-- Schwartz functions have bounded derivatives of every order. -/
lemma mv1_schwartz_bdd (v : SchwartzMap (Euc d) ℝ) (k : ℕ) :
    ∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ k v x‖ ≤ M :=
  ⟨SchwartzMap.seminorm ℝ 0 k v, fun x => SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ v k x⟩

/-- **Gaussian bounds of `h = ψ v`** (`ψ = √ρ`, `v` Schwartz): `h ∈ C^∞` and `‖D^k h‖ ≤ C_k e^{-c_k‖x‖²}`
for every `k`. -/
theorem mv1_h_gauss {ρ : Euc d → ℝ} (hρ : MovRhoData d ρ) (v : SchwartzMap (Euc d) ℝ) :
    ContDiff ℝ ∞ (fun z => Real.sqrt (ρ z) * v z) ∧
      ∀ k : ℕ, ∃ C c : ℝ, 0 < c ∧
        ∀ x, ‖iteratedFDeriv ℝ k (fun z => Real.sqrt (ρ z) * v z) x‖ ≤ C * Real.exp (-c * ‖x‖ ^ 2) :=
  ⟨hρ.sqrt_smooth.mul (v.smooth ⊤),
    mv1_gauss_mul hρ.sqrt_smooth (v.smooth ⊤) hρ.sqrt_gauss (mv1_schwartz_bdd v)⟩

lemma mv1_h_movGauss {ρ : Euc d → ℝ} (hρ : MovRhoData d ρ) (v : SchwartzMap (Euc d) ℝ) (k : ℕ) :
    MovGauss k (fun z => Real.sqrt (ρ z) * v z) := fun j _ => (mv1_h_gauss hρ v).2 j

section Formulas

variable {s : ℝ}

/-- Product rule for the divergence of `c F`. -/
lemma mv1_movDiv_smul {c : Euc d → ℝ} {F : Euc d → Euc d} {x : Euc d}
    (hc : DifferentiableAt ℝ c x) (hF : DifferentiableAt ℝ F x) :
    movDiv (fun y => c y • F y) x =
      c x * movDiv F x + ∑ i, fderiv ℝ c x (EuclideanSpace.single i 1) * F x i := by
  unfold movDiv
  have h1 : fderiv ℝ (fun y => c y • F y) x =
      c x • fderiv ℝ F x + (fderiv ℝ c x).smulRight (F x) :=
    (hc.hasFDerivAt.smul hF.hasFDerivAt).fderiv
  rw [h1]
  simp [Finset.mul_sum, Finset.sum_add_distrib]

/-- `∂ρ = ρ ∂log ρ` for `ρ > 0`. -/
lemma mv1_fderiv_rho {ρ : Euc d → ℝ} {x : Euc d} (hρd : DifferentiableAt ℝ ρ x) (hpos : 0 < ρ x)
    (e : Euc d) :
    fderiv ℝ ρ x e = ρ x * fderiv ℝ (fun y => Real.log (ρ y)) x e := by
  have h := hρd.hasFDerivAt.log hpos.ne'
  rw [h.fderiv]
  simp only [smul_apply, smul_eq_mul]
  field_simp

/-- `∂√ρ = (1/2) √ρ ∂log ρ` for `ρ > 0`. -/
lemma mv1_fderiv_sqrt {ρ : Euc d → ℝ} {x : Euc d} (hρd : DifferentiableAt ℝ ρ x) (hpos : 0 < ρ x)
    (e : Euc d) :
    fderiv ℝ (fun y => Real.sqrt (ρ y)) x e =
      (1 / 2) * Real.sqrt (ρ x) * fderiv ℝ (fun y => Real.log (ρ y)) x e := by
  have h := hρd.hasFDerivAt.sqrt hpos.ne'
  rw [h.fderiv]
  simp only [smul_apply, smul_eq_mul]
  rw [mv1_fderiv_rho hρd hpos e]
  have hs : 0 < Real.sqrt (ρ x) := Real.sqrt_pos.2 hpos
  have hr : ρ x = Real.sqrt (ρ x) * Real.sqrt (ρ x) := (Real.mul_self_sqrt hpos.le).symm
  have hx : ρ x ≠ 0 := hpos.ne'
  generalize fderiv ℝ (fun y => Real.log (ρ y)) x e = t
  generalize Real.sqrt (ρ x) = a at hs hr ⊢
  rw [hr]
  field_simp

/-- Differentiability of the force of `h = √ρ v` at every point, and the coordinate formula. -/
lemma mv1_force_data (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : MovRhoData d ρ) (v : SchwartzMap (Euc d) ℝ) (x : Euc d) :
    DifferentiableAt ℝ (movForce d s (fun z => Real.sqrt (ρ z) * v z)) x ∧
      movDiv (movForce d s (fun z => Real.sqrt (ρ z) * v z)) x =
        HRS.Whole.convFun (rieszKernel d s)
          (fun y => Laplacian.laplacian (fun z => Real.sqrt (ρ z) * v z) y) x ∧
      ∀ i : Fin d, (movForce d s (fun z => Real.sqrt (ρ z) * v z) x) i =
        HRS.Whole.convFun (rieszKernel d s)
          (fun y => gradient (fun z => Real.sqrt (ρ z) * v z) y i) x := by
  have hh := (mv1_h_gauss hρ v).1
  have hg := mv1_h_movGauss hρ v
  have hh1 : ContDiff ℝ 1 (fun z => Real.sqrt (ρ z) * v z) := hh.of_le (by exact_mod_cast le_top)
  have hh2 : ContDiff ℝ 2 (fun z => Real.sqrt (ρ z) * v z) :=
    hh.of_le (by norm_num)
  have hh' : ContDiff ℝ ((1 + 1 : ℕ) : WithTop ℕ∞) (fun z => Real.sqrt (ρ z) * v z) := by
    simpa using hh2
  obtain ⟨C, c, hC, hc, h0, h1⟩ := mv1_gauss01 (hg 1)
  refine ⟨?_, mv1_div_force hd hs0 hsd hh2 (hg 2) x, fun i => ?_⟩
  · exact ((mv1_force_contDiff hd hs0 hsd 1 hh' (hg (1 + 1))).differentiable (by norm_num)) x
  · rw [mv1_force_eq_conv_grad hd hs0 hsd hc hC hh1 h0 h1 x i]
    simp_rw [movtr_gradient_apply]

/-- **Formula for `P`** (S6.1, step 2): for `v` Schwartz and `h = √ρ v`,
`P v = -√ρ (g * Δh + ∑_i ∂_i log ρ · (g * ∂_i h))`; the `ρ^{-1/2}` cancels. -/
theorem mv1_P_formula (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : MovRhoData d ρ) (v : SchwartzMap (Euc d) ℝ) (x : Euc d) :
    movP d s ρ v x = -(Real.sqrt (ρ x)) *
      (HRS.Whole.convFun (rieszKernel d s)
          (fun y => Laplacian.laplacian (fun z => Real.sqrt (ρ z) * v z) y) x +
        ∑ i, gradient (fun y => Real.log (ρ y)) x i *
          HRS.Whole.convFun (rieszKernel d s)
            (fun y => gradient (fun z => Real.sqrt (ρ z) * v z) y i) x) := by
  obtain ⟨hFd, hdiv, hcomp⟩ := mv1_force_data (s := s) hd hs0 hsd hρ v x
  have hρd : DifferentiableAt ℝ ρ x := (hρ.smooth.differentiable (by simp)) x
  have hpos := hρ.pos x
  unfold movP
  rw [mv1_movDiv_smul hρd hFd, hdiv]
  have hs : 0 < Real.sqrt (ρ x) := Real.sqrt_pos.2 hpos
  have hr : ρ x = Real.sqrt (ρ x) * Real.sqrt (ρ x) := (Real.mul_self_sqrt hpos.le).symm
  have hsum : ∑ i, fderiv ℝ ρ x (EuclideanSpace.single i 1) *
      (movForce d s (fun z => Real.sqrt (ρ z) * v z) x) i =
      ρ x * ∑ i, gradient (fun y => Real.log (ρ y)) x i *
          HRS.Whole.convFun (rieszKernel d s)
            (fun y => gradient (fun z => Real.sqrt (ρ z) * v z) y i) x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mv1_fderiv_rho hρd hpos, hcomp i, movtr_gradient_apply]
    ring
  rw [hsum, ← mul_add]
  have hinv : (Real.sqrt (ρ x))⁻¹ * ρ x = Real.sqrt (ρ x) := by
    rw [inv_mul_eq_iff_eq_mul₀ hs.ne']; exact hr
  rw [neg_mul, ← mul_assoc, hinv, neg_mul]

/-- Inner-product form of the `P` formula: `⟨∇log ρ, ∇(g*h)⟩`. -/
theorem mv1_P_formula_inner (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : MovRhoData d ρ) (v : SchwartzMap (Euc d) ℝ) (x : Euc d) :
    movP d s ρ v x = -(Real.sqrt (ρ x)) *
      (HRS.Whole.convFun (rieszKernel d s)
          (fun y => Laplacian.laplacian (fun z => Real.sqrt (ρ z) * v z) y) x +
        inner ℝ (gradient (fun y => Real.log (ρ y)) x)
          (movForce d s (fun z => Real.sqrt (ρ z) * v z) x)) := by
  rw [mv1_P_formula hd hs0 hsd hρ v x]
  obtain ⟨-, -, hcomp⟩ := mv1_force_data (s := s) hd hs0 hsd hρ v x
  congr 2
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hcomp i]
  simp [mul_comm]

/-- **Formula for `B`** (S6.1, step 2): for `v ∈ C¹`, `w` Schwartz and `h_w = √ρ w`,
`B(v,w) = ∑_i ∂_i v · (g * ∂_i h_w) + v (g * Δh_w + (1/2) ∑_i ∂_i log ρ · (g * ∂_i h_w))`. -/
theorem mv1_B_formula (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : MovRhoData d ρ) {v : Euc d → ℝ} (hv : Differentiable ℝ v)
    (w : SchwartzMap (Euc d) ℝ) (x : Euc d) :
    movB d s ρ v w x =
      ∑ i, gradient v x i *
          HRS.Whole.convFun (rieszKernel d s)
            (fun y => gradient (fun z => Real.sqrt (ρ z) * w z) y i) x +
      v x * (HRS.Whole.convFun (rieszKernel d s)
          (fun y => Laplacian.laplacian (fun z => Real.sqrt (ρ z) * w z) y) x +
        (1 / 2) * ∑ i, gradient (fun y => Real.log (ρ y)) x i *
          HRS.Whole.convFun (rieszKernel d s)
            (fun y => gradient (fun z => Real.sqrt (ρ z) * w z) y i) x) := by
  obtain ⟨hFd, hdiv, hcomp⟩ := mv1_force_data (s := s) hd hs0 hsd hρ w x
  have hρd : DifferentiableAt ℝ ρ x := (hρ.smooth.differentiable (by simp)) x
  have hpos := hρ.pos x
  have hψd : DifferentiableAt ℝ (fun y => Real.sqrt (ρ y)) x :=
    (hρ.sqrt_smooth.differentiable (by simp)) x
  have hcd : DifferentiableAt ℝ (fun y => Real.sqrt (ρ y) * v y) x := hψd.mul (hv x)
  unfold movB
  rw [mv1_movDiv_smul hcd hFd, hdiv]
  have hs : 0 < Real.sqrt (ρ x) := Real.sqrt_pos.2 hpos
  have hder : ∀ i : Fin d, fderiv ℝ (fun y => Real.sqrt (ρ y) * v y) x (EuclideanSpace.single i 1) =
      Real.sqrt (ρ x) * gradient v x i +
        v x * ((1 / 2) * Real.sqrt (ρ x) * gradient (fun y => Real.log (ρ y)) x i) := by
    intro i
    have := (hψd.hasFDerivAt.mul (hv x).hasFDerivAt).fderiv
    change fderiv ℝ (fun y => Real.sqrt (ρ y) * v y) x = _ at this
    rw [this, movtr_gradient_apply, movtr_gradient_apply, ← mv1_fderiv_sqrt hρd hpos]
    simp
  simp_rw [hder, hcomp]
  set D := HRS.Whole.convFun (rieszKernel d s)
          (fun y => Laplacian.laplacian (fun z => Real.sqrt (ρ z) * w z) y) x
  set A := ∑ i, gradient v x i *
          HRS.Whole.convFun (rieszKernel d s)
            (fun y => gradient (fun z => Real.sqrt (ρ z) * w z) y i) x with hA
  set Lg := ∑ i, gradient (fun y => Real.log (ρ y)) x i *
          HRS.Whole.convFun (rieszKernel d s)
            (fun y => gradient (fun z => Real.sqrt (ρ z) * w z) y i) x with hL
  have hsum : ∑ i, (Real.sqrt (ρ x) * gradient v x i +
        v x * ((1 / 2) * Real.sqrt (ρ x) * gradient (fun y => Real.log (ρ y)) x i)) *
        HRS.Whole.convFun (rieszKernel d s)
          (fun y => gradient (fun z => Real.sqrt (ρ z) * w z) y i) x =
      Real.sqrt (ρ x) * A + Real.sqrt (ρ x) * (v x * ((1 / 2) * Lg)) := by
    rw [hA, hL]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  field_simp
  ring

end Formulas

end HRS.MS.MovForce
