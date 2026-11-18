import HRS.PDE.MovAAux4

/-!
# MOVA Aux5: the exact algebraic identity `S^M = -βN C^M + ∑_i k(x_i) + const`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem mova_phi_apply (D : DynData d) (M : ℝ) (ρ : ℝ → Torus d → ℝ) (r : ℝ) (x : Torus d) :
    movT_phi D M ρ r x =
      D.invβ⁻¹ * (D.V x + convFun (b15c_gReg d D.s M) (ρ r) x) + Real.log (ρ r x) := rfl

theorem mova_phi_isCk_two (D : DynData d) (M : ℝ) {ρ : ℝ → Torus d → ℝ} {r : ℝ}
    (hρ : Torus.IsCk 2 (ρ r)) (hpos : ∀ x, 0 < ρ r x) (hV : Torus.IsCk 2 D.V) :
    Torus.IsCk 2 (movT_phi D M ρ r) :=
  mova_isCk_add (mova_isCk_const_mul _ (mova_isCk_add hV
    (mova_isCk_two_convFun (mova_integrable_gReg D M) hρ))) (mova_isCk_log hρ hpos)

theorem mova_grad_phi (D : DynData d) (M : ℝ) {ρ : ℝ → Torus d → ℝ} {r : ℝ}
    (hρ : Torus.IsCk 2 (ρ r)) (hpos : ∀ x, 0 < ρ r x) (hV : Torus.IsCk 2 D.V) (hκ : 0 < D.invβ)
    (x : Torus d) :
    Torus.grad (movT_phi D M ρ r) x = D.invβ⁻¹ • movT_uReg D M (ρ r) x := by
  have hρ1 := mova_isCk_one_of_two hρ
  have hV1 := mova_isCk_one_of_two hV
  have hc1 : Torus.IsCk 1 (convFun (b15c_gReg d D.s M) (ρ r)) :=
    mova_isCk_one_convFun (mova_integrable_gReg D M) hρ1
  have hl1 : Torus.IsCk 1 (fun y => Real.log (ρ r y)) :=
    mova_isCk_of_le (by norm_num) (mova_isCk_log hρ hpos)
  ext j
  rw [mova_grad_apply, PiLp.smul_apply, mova_uReg_apply]
  have e : movT_phi D M ρ r = fun y => D.invβ⁻¹ * (D.V y + convFun (b15c_gReg d D.s M) (ρ r) y) +
      Real.log (ρ r y) := funext (mova_phi_apply D M ρ r)
  rw [e, mova_partialDeriv_add j (mova_isCk_const_mul _ (mova_isCk_add hV1 hc1)) hl1,
    mova_partialDeriv_const_mul j (mova_isCk_add hV1 hc1), mova_partialDeriv_add j hV1 hc1,
    mova_partialDeriv_log j hρ1 hpos]
  have hne : D.invβ ≠ 0 := hκ.ne'
  simp only [smul_eq_mul]
  field_simp
  ring

/-- The one-body function `k` of the decomposition `S^M = -βN C^M + ∑_i k(x_i) + const`. -/
def mova_k (D : DynData d) (M : ℝ) (ρ ρt : ℝ → Torus d → ℝ) (r : ℝ) (x : Torus d) : ℝ :=
  D.invβ * Torus.laplacian (movT_phi D M ρ r) x + D.invβ * ‖Torus.grad (movT_phi D M ρ r) x‖ ^ 2
    - inner ℝ (Torus.grad (movT_phi D M ρ r) x) (Torus.grad D.V x) - movT_phit D M ρ ρt r x
    - D.invβ⁻¹ * ∫ y, commKernel (Torus.grad (b15c_gReg d D.s M)) (movT_uReg D M (ρ r)) x y
        ∂(withDensityReal (ρ r))

/-- The constant of the decomposition. -/
def mova_const (D : DynData d) (N : ℕ) (M : ℝ) (ρ ρt : ℝ → Torus d → ℝ) (r : ℝ) : ℝ :=
  (∫ Y, movT_psit D M ρ ρt r Y ∂(movT_Q (b15c_gReg d D.s M) D N ρ r)) +
    (D.invβ⁻¹ * N / 2) * ∫ x, ∫ y, commKernel (Torus.grad (b15c_gReg d D.s M))
      (movT_uReg D M (ρ r)) x y ∂(withDensityReal (ρ r)) ∂(withDensityReal (ρ r))

theorem mova_srcReg_alg (hN : 0 < N) (D : DynData d) (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ))
    (M : ℝ) {ρ ρt : ℝ → Torus d → ℝ} {r : ℝ} (hρ : Torus.IsCk 2 (ρ r)) (hpos : ∀ x, 0 < ρ r x)
    (hV : Torus.IsCk 2 D.V) (hκ : 0 < D.invβ) (X : Config d N) :
    movT_srcReg D N M ρ ρt r X =
      -(D.invβ⁻¹ * N) * movT_commReg D N M (ρ r) X + ∑ i, mova_k D M ρ ρt r (X i) +
        mova_const D N M ρ ρt r := by
  have hφ2 := mova_phi_isCk_two D M hρ hpos hV
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hκ' : D.invβ ≠ 0 := hκ.ne'
  set φ := movT_phi D M ρ r with hφdef
  set G := Torus.grad (b15c_gReg d D.s M) with hG
  set w := movT_uReg D M (ρ r) with hw
  set β := D.invβ⁻¹ with hβ
  have hGodd : ∀ z, G (-z) = -G z := fun z =>
    mova_grad_odd (mova_gReg_isCk D 1 M) (fun x => b15c_gReg_neg D.s M x) z
  have hgφ : ∀ x, Torus.grad φ x = β • w x := fun x => mova_grad_phi D M hρ hpos hV hκ x
  -- the drift pairing
  have hb : ∀ i : Fin N, inner ℝ (Torus.grad φ (X i)) (b15d_configDriftReg D M X i) =
      -(β / N) * ∑ j ∈ Finset.univ.erase i, inner ℝ (w (X i)) (G (X i - X j)) -
        β * inner ℝ (w (X i)) (Torus.grad D.V (X i)) := by
    intro i
    unfold b15d_configDriftReg
    rw [hM, hgφ, inner_sub_right, real_inner_smul_left, real_inner_smul_left, real_inner_smul_right,
      inner_sum]
    simp_rw [mova_matVec_neg_one, inner_neg_right]
    rw [Finset.sum_neg_distrib]
    simp only [div_eq_inv_mul, one_div]
    ring
  have e0 : d1_configGen D.invβ (b15d_configDriftReg D M) (movT_psi D M ρ r) X =
      D.invβ * ∑ i, Torus.laplacian φ (X i) +
        ∑ i, inner ℝ (Torus.grad φ (X i)) (b15d_configDriftReg D M X i) :=
    mova_gen_sum D.invβ (b15d_configDriftReg D M) hφ2 X
  unfold movT_srcReg
  rw [e0]
  simp_rw [hb]
  unfold movT_commReg modulatedEnergy mova_k mova_const
  rw [mova_pair_sum_comm G w hGodd]
  simp only [movT_psit, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_neg_distrib, ← Finset.sum_mul]
  rw [← hφdef, ← hβ]
  have hinner : ∀ x, inner ℝ (Torus.grad φ x) (Torus.grad D.V x) =
      β * inner ℝ (w x) (Torus.grad D.V x) := fun x => by rw [hgφ, real_inner_smul_left]
  simp_rw [hinner]
  simp only [← Finset.mul_sum]
  field_simp
  ring

end HRS
