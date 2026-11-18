import HRS.PDE.MovAAux8

/-!
# MOVA Aux9: closed form of the one-body function `k = Δ/ρ + β g_M * Δ`, `Δ = div(ρ u^M) - ∂_tρ`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

/-- `div(ρ u^M)`. -/
def mova_divRW (D : DynData d) (M : ℝ) (ρ : Torus d → ℝ) (y : Torus d) : ℝ :=
  ∑ j, Torus.partialDeriv j (fun z => ρ z * mova_wc D M ρ j z) y

/-- `Δ = div(ρ u^M) - ∂_tρ`. -/
def mova_Delta (D : DynData d) (M : ℝ) (ρ ρt : ℝ → Torus d → ℝ) (r : ℝ) (y : Torus d) : ℝ :=
  mova_divRW D M (ρ r) y - ρt r y

theorem mova_grad_phi_apply (D : DynData d) (M : ℝ) {ρ : ℝ → Torus d → ℝ} {r : ℝ}
    (hρ : Torus.IsCk 2 (ρ r)) (hpos : ∀ x, 0 < ρ r x) (hV : Torus.IsCk 2 D.V) (hκ : 0 < D.invβ)
    (j : Fin d) (x : Torus d) :
    Torus.partialDeriv j (movT_phi D M ρ r) x = D.invβ⁻¹ * mova_wc D M (ρ r) j x := by
  rw [← mova_grad_apply, mova_grad_phi D M hρ hpos hV hκ, PiLp.smul_apply]
  rfl

theorem mova_lap_phi (D : DynData d) (M : ℝ) {ρ : ℝ → Torus d → ℝ} {r : ℝ}
    (hρ : Torus.IsCk 2 (ρ r)) (hpos : ∀ x, 0 < ρ r x) (hV : Torus.IsCk 2 D.V) (hκ : 0 < D.invβ)
    (x : Torus d) :
    D.invβ * Torus.laplacian (movT_phi D M ρ r) x =
      ∑ j, Torus.partialDeriv j (mova_wc D M (ρ r) j) x := by
  have hφ2 := mova_phi_isCk_two D M hρ hpos hV
  rw [mova_laplacian_eq_sum hφ2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : Torus.partialDeriv j (movT_phi D M ρ r) = fun y => D.invβ⁻¹ * mova_wc D M (ρ r) j y :=
    funext fun y => mova_grad_phi_apply D M hρ hpos hV hκ j y
  rw [e, mova_partialDeriv_const_mul j (mova_wc_isCk_one D M hρ hpos hV j)]
  field_simp [hκ.ne']

theorem mova_wc_decomp (D : DynData d) (M : ℝ) {ρ : Torus d → ℝ} (hρ : Torus.IsCk 2 ρ)
    (hpos : ∀ x, 0 < ρ x) (j : Fin d) (x : Torus d) :
    mova_wc D M ρ j x = D.invβ * (Torus.partialDeriv j ρ x / ρ x) +
      Torus.partialDeriv j (convFun (b15c_gReg d D.s M) ρ) x + Torus.partialDeriv j D.V x := by
  unfold mova_wc
  rw [mova_uReg_apply, mova_partialDeriv_log j (mova_isCk_one_of_two hρ) hpos x]

theorem mova_continuous_divRW (D : DynData d) (M : ℝ) {ρ : Torus d → ℝ} (hρ : Torus.IsCk 2 ρ)
    (hpos : ∀ x, 0 < ρ x) (hV : Torus.IsCk 2 D.V) : Continuous (mova_divRW D M ρ) := by
  unfold mova_divRW
  exact continuous_finsetSum _ fun j _ => mova_continuous_partialDeriv
    (mova_isCk_mul (mova_isCk_one_of_two hρ) (mova_wc_isCk_one D M hρ hpos hV j)) j

theorem mova_k_eq (D : DynData d) (M : ℝ) {ρ ρt : ℝ → Torus d → ℝ} {r : ℝ}
    (hρ : Torus.IsCk 2 (ρ r)) (hdens : IsProbDensity (ρ r)) (hpos : ∀ x, 0 < ρ r x)
    (hV : Torus.IsCk 2 D.V) (hκ : 0 < D.invβ) (hρtc : Continuous (ρt r)) (x : Torus d) :
    mova_k D M ρ ρt r x = mova_Delta D M ρ ρt r x / ρ r x +
      D.invβ⁻¹ * convFun (b15c_gReg d D.s M) (mova_Delta D M ρ ρt r) x := by
  have hρ1 := mova_isCk_one_of_two hρ
  have hρc := mova_continuous_of_isCk hρ
  have hwc := mova_wc_isCk_one D M hρ hpos hV
  have hgi := mova_integrable_gReg D M
  have hcdiv := mova_continuous_divRW D M hρ hpos hV
  have hne : D.invβ ≠ 0 := hκ.ne'
  have hrho : ρ r x ≠ 0 := (hpos x).ne'
  -- the convolution of `Δ`
  have hconv : convFun (b15c_gReg d D.s M) (mova_Delta D M ρ ρt r) x =
      convFun (b15c_gReg d D.s M) (mova_divRW D M (ρ r)) x - convFun (b15c_gReg d D.s M) (ρt r) x :=
    mova_convFun_sub_right hgi hcdiv hρtc x
  rw [hconv]
  unfold mova_k movT_phit mova_Delta
  rw [mova_c1_eq D M hρ hdens hpos hV x, mova_lap_phi D M hρ hpos hV hκ x]
  -- expand the gradient terms
  have hn : ‖Torus.grad (movT_phi D M ρ r) x‖ ^ 2 = ∑ j, (D.invβ⁻¹ * mova_wc D M (ρ r) j x) ^ 2 := by
    rw [mova_norm_sq_eq_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mova_grad_apply, mova_grad_phi_apply D M hρ hpos hV hκ]
  have hi : inner ℝ (Torus.grad (movT_phi D M ρ r) x) (Torus.grad D.V x) =
      ∑ j, (D.invβ⁻¹ * mova_wc D M (ρ r) j x) * Torus.partialDeriv j D.V x := by
    rw [mova_inner_eq_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mova_grad_apply, mova_grad_apply, mova_grad_phi_apply D M hρ hpos hV hκ]
  have hi2 : inner ℝ (movT_uReg D M (ρ r) x) (Torus.grad (convFun (b15c_gReg d D.s M) (ρ r)) x) =
      ∑ j, mova_wc D M (ρ r) j x * Torus.partialDeriv j (convFun (b15c_gReg d D.s M) (ρ r)) x := by
    rw [mova_inner_eq_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mova_grad_apply]
    rfl
  have hdiv : mova_divRW D M (ρ r) x = ∑ j, (Torus.partialDeriv j (ρ r) x * mova_wc D M (ρ r) j x +
      ρ r x * Torus.partialDeriv j (mova_wc D M (ρ r) j) x) := by
    unfold mova_divRW
    refine Finset.sum_congr rfl fun j _ => ?_
    exact mova_partialDeriv_mul j hρ1 (hwc j) x
  rw [hn, hi, hi2]
  have hj : ∀ j, D.invβ * (D.invβ⁻¹ * mova_wc D M (ρ r) j x) ^ 2 -
      (D.invβ⁻¹ * mova_wc D M (ρ r) j x) * Torus.partialDeriv j D.V x -
      D.invβ⁻¹ * (mova_wc D M (ρ r) j x * Torus.partialDeriv j (convFun (b15c_gReg d D.s M) (ρ r)) x) =
        mova_wc D M (ρ r) j x * (Torus.partialDeriv j (ρ r) x / ρ r x) := by
    intro j
    have h1 := mova_wc_decomp D M hρ hpos j x
    have h2 : D.invβ⁻¹ * (D.invβ * (Torus.partialDeriv j (ρ r) x / ρ r x)) =
        Torus.partialDeriv j (ρ r) x / ρ r x := by field_simp
    have h3 : mova_wc D M (ρ r) j x - Torus.partialDeriv j (convFun (b15c_gReg d D.s M) (ρ r)) x -
        Torus.partialDeriv j D.V x = D.invβ * (Torus.partialDeriv j (ρ r) x / ρ r x) := by linarith
    calc _ = D.invβ⁻¹ * mova_wc D M (ρ r) j x * (mova_wc D M (ρ r) j x -
          Torus.partialDeriv j (convFun (b15c_gReg d D.s M) (ρ r)) x - Torus.partialDeriv j D.V x) := by
          field_simp
          ring
      _ = _ := by rw [h3, mul_assoc, ← mul_assoc _ (mova_wc D M (ρ r) j x), mul_comm _ (mova_wc D M (ρ r) j x),
            mul_assoc, h2]
  have hsum := Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hj j)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  have hc' : convFun (b15c_gReg d D.s M) (fun y => ∑ j, Torus.partialDeriv j
      (fun z => ρ r z * mova_wc D M (ρ r) j z) y) x =
      convFun (b15c_gReg d D.s M) (mova_divRW D M (ρ r)) x := rfl
  rw [hc']
  have hd2 : mova_divRW D M (ρ r) x / ρ r x = ∑ j, Torus.partialDeriv j (mova_wc D M (ρ r) j) x +
      ∑ j, mova_wc D M (ρ r) j x * (Torus.partialDeriv j (ρ r) x / ρ r x) := by
    rw [hdiv, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
    ring
  rw [sub_div]
  linarith

end HRS
