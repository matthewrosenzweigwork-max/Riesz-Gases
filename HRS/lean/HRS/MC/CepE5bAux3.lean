import HRS.MC.CepE5bAux2
import HRS.MC.CepE2Aux3

/-!
# Packet CEPE5B, auxiliary 3: the Moreau envelope `Φ_n` is `C²` with `0 ≤ D²Φ_n ≤ min (n, H_{J_n z})`

`Φ_n z = Φ(J_n z) + (n/2)|z - J_n z|²`, `∇Φ_n = G_n = n(1 - J_n)` (from the force relation).  The second derivative
`D²Φ_n(z) = D G_n(z) = n (1 - DJ)` satisfies, with `w = DJ u` and `n u = n w + H w`,
`⟨D²Φ_n u, u⟩ = ⟨H w, w⟩ + n⁻¹ |H w|² ∈ [0, min(n |u|², ⟨H u, u⟩)]`.
-/

open Set Filter Topology
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE5b

open HRS.MC.Cepa
open HRS.MC.CepE1 (cepe1_h1 cepe1_pairGrad cepe1_vec cepe1_inner_vec)

variable {N : ℕ} {a : ℝ} {J : ℝ → Ch N → Ch N}

/-- The Moreau envelope `Φ_n` (as `Φ(J_n z) + (n/2)|z - J_n z|²`). -/
def e5b_Pn (a : ℝ) (N : ℕ) (J : ℝ → Ch N → Ch N) (n : ℝ) (z : Ch N) : ℝ :=
  cep_chamberPot a N (J n z) + n / 2 * ‖z - J n z‖ ^ 2

theorem e5b_toDual (x : Ch N) : InnerProductSpace.toDual ℝ (Ch N) x = innerSL ℝ x := by
  ext v
  simp [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]

theorem e5b_hasFDerivAt_J (ha : 0 < a) (hJ : cep_Yosida a N J) {n : ℝ} (hn : 0 < n) (z : Ch N) :
    HasFDerivAt (J n) (fderiv ℝ (J n) z) z :=
  ((e5b_contDiffAt_J ha hJ hn z).differentiableAt one_ne_zero).hasFDerivAt

theorem e5b_hasFDerivAt_Pn (ha : 0 < a) (hJ : cep_Yosida a N J) {n : ℝ} (hn : 0 < n) (z : Ch N) :
    HasFDerivAt (e5b_Pn a N J n) (innerSL ℝ (n • (z - J n z))) z := by
  have hJd := e5b_hasFDerivAt_J ha hJ hn z
  have hy := hJ.mem n z hn
  have hΦ : HasFDerivAt (cep_chamberPot a N) (innerSL ℝ (e5b_pg a N (J n z))) (J n z) := by
    have := (e5b_hasGradient_Phi a hy)
    rw [hasGradientAt_iff_hasFDerivAt, e5b_toDual] at this
    exact this
  have h1 := hΦ.comp z hJd
  have h2 : HasFDerivAt (fun z' : Ch N => z' - J n z') (ContinuousLinearMap.id ℝ (Ch N) - fderiv ℝ (J n) z) z :=
    (hasFDerivAt_id z).sub hJd
  have h3 := (h2.norm_sq).const_mul (n / 2)
  have h4 := h1.add h3
  have hf := e5b_force hJ hn z
  refine h4.congr_fderiv ?_
  ext u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
  rw [← hf, real_inner_smul_left, real_inner_smul_left, inner_sub_right]
  ring

theorem e5b_Pn_lower (ha : 0 ≤ a) (hJ : cep_Yosida a N J) {n : ℝ} (hn : 0 < n) (z : Ch N) :
    -((a / N) * HRS.MC.CepE2.cepe2_npairs N * Real.log 2) ≤ e5b_Pn a N J n z := by
  have h : -((a / N) * HRS.MC.CepE2.cepe2_npairs N * Real.log 2) ≤ cep_chamberPot a N (J n z) :=
    HRS.MC.CepE2.cepe2_lower ha (hJ.mem n z hn)
  unfold e5b_Pn
  have : 0 ≤ n / 2 * ‖z - J n z‖ ^ 2 := by positivity
  linarith

theorem e5b_Pn_le (ha : 0 ≤ a) (hJ : cep_Yosida a N J) {n : ℝ} (hn : 0 < n) (z : Ch N) {y' : Ch N}
    (hy' : y' ∈ cep_Alcove N) :
    e5b_Pn a N J n z ≤ cep_chamberPot a N y' + n / 2 * ‖z - y'‖ ^ 2 := by
  have hy := hJ.mem n z hn
  have hc : cep_chamberPot a N (J n z) + inner ℝ (e5b_pg a N (J n z)) (y' - J n z) ≤ cep_chamberPot a N y' :=
    HRS.MC.CepE2.cepe2_convex ha (x := y') (x' := J n z) hy' hy
  have hf := e5b_force hJ hn z
  unfold e5b_Pn
  set y := J n z
  have hd : z - y' = (z - y) + (y - y') := by abel
  have e1 : inner ℝ (e5b_pg a N y) (y' - y) = -(n * inner ℝ (z - y) (y - y')) := by
    have hneg : y' - y = -(y - y') := by abel
    rw [← hf, real_inner_smul_left, hneg, inner_neg_right]
    ring
  have e2 : ‖z - y'‖ ^ 2 = ‖z - y‖ ^ 2 + 2 * inner ℝ (z - y) (y - y') + ‖y - y'‖ ^ 2 := by
    rw [hd, norm_add_sq_real]
  rw [e1] at hc
  have hnn : 0 ≤ n / 2 * ‖y - y'‖ ^ 2 := by positivity
  rw [e2]
  nlinarith

theorem e5b_fderiv_Pn (ha : 0 < a) (hJ : cep_Yosida a N J) {n : ℝ} (hn : 0 < n) :
    fderiv ℝ (e5b_Pn a N J n) = fun z => innerSL ℝ (n • (z - J n z)) :=
  funext fun z => (e5b_hasFDerivAt_Pn ha hJ hn z).fderiv

theorem e5b_contDiff_Pn (ha : 0 < a) (hJ : cep_Yosida a N J) {n : ℝ} (hn : 0 < n) :
    ContDiff ℝ 2 (e5b_Pn a N J n) := by
  have h2 : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
  rw [h2, contDiff_succ_iff_fderiv]
  refine ⟨fun z => (e5b_hasFDerivAt_Pn ha hJ hn z).differentiableAt, by simp, ?_⟩
  rw [e5b_fderiv_Pn ha hJ hn]
  have hG : ContDiff ℝ 1 (fun z : Ch N => n • (z - J n z)) :=
    (contDiff_id.sub (e5b_contDiff_J ha hJ hn)).const_smul n
  exact (innerSL ℝ : Ch N →L[ℝ] Ch N →L[ℝ] ℝ).contDiff.comp hG

/-- The second derivative of `Φ_n` in the direction `(u, v)`. -/
theorem e5b_hess_apply (ha : 0 < a) (hJ : cep_Yosida a N J) {n : ℝ} (hn : 0 < n) (z u v : Ch N) :
    fderiv ℝ (fderiv ℝ (e5b_Pn a N J n)) z u v = inner ℝ (n • (u - fderiv ℝ (J n) z u)) v := by
  have hJd := e5b_hasFDerivAt_J ha hJ hn z
  have hG : HasFDerivAt (fun z' : Ch N => n • (z' - J n z'))
      (n • (ContinuousLinearMap.id ℝ (Ch N) - fderiv ℝ (J n) z)) z :=
    ((hasFDerivAt_id z).sub hJd).const_smul n
  have h2 := (innerSL ℝ : Ch N →L[ℝ] Ch N →L[ℝ] ℝ).hasFDerivAt.comp z hG
  rw [e5b_fderiv_Pn ha hJ hn]
  have := h2.fderiv
  simp only [Function.comp_def] at this
  rw [this]
  rfl

/-- The key relation `n (u - DJ u) = H (DJ u)`. -/
theorem e5b_relation (ha : 0 < a) (hJ : cep_Yosida a N J) {n : ℝ} (hn : 0 < n) (z u : Ch N) :
    n • (u - fderiv ℝ (J n) z u) = e5b_Hop a N (J n z) (fderiv ℝ (J n) z u) := by
  have hJd := e5b_hasFDerivAt_J ha hJ hn z
  have hy := hJ.mem n z hn
  have hG : HasFDerivAt (fun z' : Ch N => n • (z' - J n z'))
      (n • (ContinuousLinearMap.id ℝ (Ch N) - fderiv ℝ (J n) z)) z :=
    ((hasFDerivAt_id z).sub hJd).const_smul n
  have hG' : HasFDerivAt (fun z' : Ch N => e5b_pg a N (J n z'))
      ((e5b_Hop a N (J n z)).comp (fderiv ℝ (J n) z)) z :=
    (e5b_hasFDerivAt_pg a hy).comp z hJd
  have hfun : (fun z' : Ch N => n • (z' - J n z')) = fun z' => e5b_pg a N (J n z') :=
    funext fun z' => e5b_force hJ hn z'
  rw [hfun] at hG
  have := hG.unique hG'
  have := congrArg (fun A => A u) this
  simpa using this

theorem e5b_hess_bounds (ha : 0 < a) (hJ : cep_Yosida a N J) {n : ℝ} (hn : 0 < n) (z u : Ch N) :
    0 ≤ fderiv ℝ (fderiv ℝ (e5b_Pn a N J n)) z u u ∧
    fderiv ℝ (fderiv ℝ (e5b_Pn a N J n)) z u u ≤ n * ‖u‖ ^ 2 ∧
    fderiv ℝ (fderiv ℝ (e5b_Pn a N J n)) z u u ≤ e5b_hq a N (J n z) u u := by
  rw [e5b_hess_apply ha hJ hn]
  set y := J n z
  set w := fderiv ℝ (J n) z u with hw
  set H := e5b_Hop a N y with hH
  have hR : n • (u - w) = H w := e5b_relation ha hJ hn z u
  have hu : u = w + n⁻¹ • H w := by
    rw [← hR, smul_smul, inv_mul_cancel₀ hn.ne', one_smul]
    abel
  have hqw : 0 ≤ inner ℝ (H w) w := by
    rw [e5b_inner_Hop]; exact e5b_hq_nonneg ha.le y w
  have hqq : 0 ≤ inner ℝ (H w) (H w) := real_inner_self_nonneg
  have hni : 0 ≤ n⁻¹ := inv_nonneg.2 hn.le
  have hsym : inner ℝ (H w) (H w) = inner ℝ (H (H w)) w := by
    rw [e5b_inner_Hop, e5b_inner_Hop, e5b_hq_comm]
  have hHH : 0 ≤ inner ℝ (H (H w)) (H w) := by
    rw [e5b_inner_Hop]; exact e5b_hq_nonneg ha.le y (H w)
  have hwu : inner ℝ (H w) u = inner ℝ (H w) w + n⁻¹ * inner ℝ (H w) (H w) := by
    conv_lhs => rw [hu]
    rw [inner_add_right, real_inner_smul_right]
  have hD : inner ℝ (n • (u - w)) u = inner ℝ (H w) u := by rw [hR]
  refine ⟨?_, ?_, ?_⟩
  · rw [hD, hwu]; nlinarith [mul_nonneg hni hqq]
  · rw [hD]
    have h1 : inner ℝ (n • (u - w)) u = n * inner ℝ u u - n * inner ℝ w u := by
      rw [real_inner_smul_left, inner_sub_left]; ring
    have h2 : inner ℝ w u = inner ℝ w w + n⁻¹ * inner ℝ w (H w) := by
      conv_lhs => rw [hu]
      rw [inner_add_right, real_inner_smul_right]
    have h3 : inner ℝ w (H w) = inner ℝ (H w) w := real_inner_comm _ _
    have h4 : 0 ≤ inner ℝ w w := real_inner_self_nonneg
    have h5 : inner ℝ u u = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u
    have h6 : inner ℝ (n • (u - w)) u = inner ℝ (H w) u := hD
    rw [← h6, h1, h2, h3, h5]
    nlinarith [mul_nonneg hni hqw]
  · rw [hD, ← e5b_inner_Hop]
    have hexp : inner ℝ (H u) u = inner ℝ (H w) w + n⁻¹ * inner ℝ (H w) (H w) + n⁻¹ * inner ℝ (H (H w)) w +
        n⁻¹ ^ 2 * inner ℝ (H (H w)) (H w) := by
      conv_lhs => rw [hu]
      simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
      ring
    rw [hwu, hexp, ← hsym]
    nlinarith [mul_nonneg (sq_nonneg n⁻¹) hHH, mul_nonneg hni hqq]

end HRS.MC.CepE5b
