import HRS.MS.Mov63FAux1

/-!
# S6.3, packet N7 (part 2): the Gaussian Lyapunov function

Namespace `HRS.MS.Mov63`, prefix `mnf_`.  See `Mov63FAux1`.  `mnf_lyap l κ t x = exp(l t + κ‖x‖²)`:
`∇ = 2κ x φ` (`mnf_lyap_grad`), `Δ = (2κ d + 4κ²‖x‖²) φ` (`mnf_lyap_lap`), `∂_t φ = l φ` (`mnf_lyap_hasDerivAt`), joint continuity, and
**`mnf_lyap_super`**: for `ν > 0`, `0 < κ`, `2νκ < q` (i.e. `κ < q/(2ν) = βq/2`) and every drift `b` with `⟨b,x⟩ ≤ -q‖x‖² + M‖x‖`, the function
`φ` with `l = 2νκd + κ²M²/(2κq - 4νκ²) + 1` is a strict supersolution: `νΔφ + ⟨b,∇φ⟩ < ∂_tφ`.
-/

noncomputable section

open Filter Topology Set
open scoped RealInnerProductSpace

namespace HRS.MS.Mov63

open HRS HRS.MS.PoissonSpike

variable {d : ℕ}

/-- The Gaussian Lyapunov function `exp(l t + κ‖x‖²)`. -/
def mnf_lyap (l κ : ℝ) (t : ℝ) (x : Euc d) : ℝ := Real.exp (l * t + κ * ‖x‖ ^ 2)

lemma mnf_lyap_pos (l κ t : ℝ) (x : Euc d) : 0 < mnf_lyap l κ t x := Real.exp_pos _

lemma mnf_lyap_cd (l κ t : ℝ) : ContDiff ℝ 2 (mnf_lyap (d := d) l κ t) := by
  unfold mnf_lyap
  have h : ContDiff ℝ 2 (fun z : Euc d => l * t + κ * ‖z‖ ^ 2) :=
    contDiff_const.add (contDiff_const.mul (contDiff_norm_sq ℝ))
  exact Real.contDiff_exp.comp h

lemma mnf_lyap_cont (l κ : ℝ) : Continuous (fun p : ℝ × Euc d => mnf_lyap l κ p.1 p.2) := by
  unfold mnf_lyap
  fun_prop

lemma mnf_lyap_hasDerivAt (l κ t : ℝ) (x : Euc d) :
    HasDerivAt (fun s => mnf_lyap l κ s x) (l * mnf_lyap l κ t x) t := by
  unfold mnf_lyap
  have h : HasDerivAt (fun s : ℝ => l * s + κ * ‖x‖ ^ 2) l t := by
    simpa using ((hasDerivAt_id t).const_mul l).add_const (κ * ‖x‖ ^ 2)
  have := h.exp
  simpa [mul_comm] using this

lemma mnf_lyap_fderiv (l κ t : ℝ) (x v : Euc d) :
    fderiv ℝ (mnf_lyap (d := d) l κ t) x v = mnf_lyap l κ t x * (2 * κ * inner ℝ x v) := by
  have h : HasFDerivAt (fun z : Euc d => l * t + κ * ‖z‖ ^ 2) (κ • (2 • innerSL ℝ x)) x := by
    simpa using ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul κ).const_add (l * t)
  have h2 := h.exp
  have e : mnf_lyap (d := d) l κ t = fun z => Real.exp (l * t + κ * ‖z‖ ^ 2) := rfl
  rw [e, h2.fderiv]
  simp [mnf_lyap, two_mul]
  ring

lemma mnf_lyap_grad (l κ t : ℝ) (x : Euc d) :
    gradient (mnf_lyap (d := d) l κ t) x = (2 * κ * mnf_lyap l κ t x) • x := by
  refine ext_inner_left ℝ fun e => ?_
  rw [HRS.MS.PoisKolm.kl_inner_gradient, mnf_lyap_fderiv, inner_smul_right, real_inner_comm]
  ring

lemma mnf_lyap_D2 (l κ t : ℝ) (x v : Euc d) :
    iteratedFDeriv ℝ 2 (mnf_lyap (d := d) l κ t) x ![v, v] =
      mnf_lyap l κ t x * (4 * κ ^ 2 * (inner ℝ x v) ^ 2 + 2 * κ * ‖v‖ ^ 2) := by
  have h1 := line_hasDerivAt2 (mnf_lyap_cd (d := d) l κ t) x v 0
  have hn : ∀ s : ℝ, ‖x + s • v‖ ^ 2 = ‖x‖ ^ 2 + 2 * s * inner ℝ x v + s ^ 2 * ‖v‖ ^ 2 := by
    intro s
    rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  have e : (fun s : ℝ => fderiv ℝ (mnf_lyap (d := d) l κ t) (x + s • v) v) =
      fun s => Real.exp (l * t + κ * (‖x‖ ^ 2 + 2 * s * inner ℝ x v + s ^ 2 * ‖v‖ ^ 2)) *
        (2 * κ * (inner ℝ x v + s * ‖v‖ ^ 2)) := by
    funext s
    rw [mnf_lyap_fderiv, inner_add_left, inner_smul_left]
    simp only [mnf_lyap, hn, real_inner_self_eq_norm_sq, conj_trivial]
  have h2 : HasDerivAt (fun s : ℝ => Real.exp (l * t + κ * (‖x‖ ^ 2 + 2 * s * inner ℝ x v + s ^ 2 * ‖v‖ ^ 2)) *
        (2 * κ * (inner ℝ x v + s * ‖v‖ ^ 2)))
      (Real.exp (l * t + κ * ‖x‖ ^ 2) * (4 * κ ^ 2 * (inner ℝ x v) ^ 2 + 2 * κ * ‖v‖ ^ 2)) 0 := by
    have hq : HasDerivAt (fun s : ℝ => l * t + κ * (‖x‖ ^ 2 + 2 * s * inner ℝ x v + s ^ 2 * ‖v‖ ^ 2))
        (κ * (2 * inner ℝ x v)) 0 := by
      have a1 : HasDerivAt (fun s : ℝ => 2 * s * inner ℝ x v) (2 * inner ℝ x v) 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).const_mul 2).mul_const (inner ℝ x v)
      have a2 : HasDerivAt (fun s : ℝ => s ^ 2 * ‖v‖ ^ 2) (2 * (0:ℝ) * ‖v‖ ^ 2) 0 := by
        simpa using ((hasDerivAt_pow 2 (0:ℝ))).mul_const (‖v‖ ^ 2)
      have := (((a1.const_add (‖x‖ ^ 2)).add a2).const_mul κ).const_add (l * t)
      convert this using 1
      ring
    have hp := hq.exp
    have hlin : HasDerivAt (fun s : ℝ => 2 * κ * (inner ℝ x v + s * ‖v‖ ^ 2)) (2 * κ * ‖v‖ ^ 2) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).mul_const (‖v‖ ^ 2)).const_add (inner ℝ x v) |>.const_mul (2 * κ)
    have := hp.mul hlin
    convert this using 1
    simp
    ring
  rw [e] at h1
  have := h1.unique h2
  simp only [zero_smul, add_zero] at this
  rw [this]
  simp [mnf_lyap]

lemma mnf_lyap_lap (l κ t : ℝ) (x : Euc d) :
    Laplacian.laplacian (mnf_lyap (d := d) l κ t) x = mnf_lyap l κ t x * (2 * κ * d + 4 * κ ^ 2 * ‖x‖ ^ 2) := by
  rw [congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin d) ℝ)) x]
  have h1 : ∑ i : Fin d, (inner ℝ x ((EuclideanSpace.basisFun (Fin d) ℝ) i)) ^ 2 = ‖x‖ ^ 2 :=
    OrthonormalBasis.sum_sq_inner_left _ x
  have hD : ∀ i : Fin d, iteratedFDeriv ℝ 2 (mnf_lyap (d := d) l κ t) x
      ![(EuclideanSpace.basisFun (Fin d) ℝ) i, (EuclideanSpace.basisFun (Fin d) ℝ) i] =
      mnf_lyap l κ t x * (4 * κ ^ 2 * (inner ℝ x ((EuclideanSpace.basisFun (Fin d) ℝ) i)) ^ 2 + 2 * κ) := by
    intro i
    rw [mnf_lyap_D2, OrthonormalBasis.norm_eq_one]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hD i), ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, h1]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **The Lyapunov function is a strict supersolution** of `∂_t - νΔ - ⟨b,∇·⟩` for drifts `b` with
`⟨b,x⟩ ≤ -q‖x‖² + M‖x‖`, `2νκ < q`. -/
theorem mnf_lyap_super {ν q κ M : ℝ} (hν : 0 < ν) (hκ : 0 < κ) (hνκ : 2 * ν * κ < q) (t : ℝ)
    (x : Euc d) (b : Euc d) (hb : inner ℝ b x ≤ -q * ‖x‖ ^ 2 + M * ‖x‖) :
    ν * Laplacian.laplacian (mnf_lyap (d := d) (2 * ν * κ * d + κ ^ 2 * M ^ 2 / (2 * κ * q - 4 * ν * κ ^ 2) + 1) κ t) x +
      inner ℝ b (gradient (mnf_lyap (d := d) (2 * ν * κ * d + κ ^ 2 * M ^ 2 / (2 * κ * q - 4 * ν * κ ^ 2) + 1) κ t) x) <
    (2 * ν * κ * d + κ ^ 2 * M ^ 2 / (2 * κ * q - 4 * ν * κ ^ 2) + 1) *
      mnf_lyap (d := d) (2 * ν * κ * d + κ ^ 2 * M ^ 2 / (2 * κ * q - 4 * ν * κ ^ 2) + 1) κ t x := by
  set a : ℝ := 2 * κ * q - 4 * ν * κ ^ 2 with ha
  have hapos : 0 < a := by
    have : 0 < 2 * κ * (q - 2 * ν * κ) := by
      apply mul_pos (by positivity); linarith
    rw [ha]; nlinarith
  set lam : ℝ := 2 * ν * κ * d + κ ^ 2 * M ^ 2 / a + 1 with hlam
  set φ := mnf_lyap (d := d) lam κ t x with hφ
  have hφp : 0 < φ := mnf_lyap_pos _ _ _ _
  rw [mnf_lyap_lap, mnf_lyap_grad, inner_smul_right]
  set r := ‖x‖ with hr
  have hbx : inner ℝ b x ≤ -q * r ^ 2 + M * r := hb
  have hsq : -a * r ^ 2 + 2 * κ * M * r ≤ κ ^ 2 * M ^ 2 / a := by
    have h : κ ^ 2 * M ^ 2 / a - (-a * r ^ 2 + 2 * κ * M * r) = (a * r - κ * M) ^ 2 / a := by
      field_simp
      ring
    have : 0 ≤ (a * r - κ * M) ^ 2 / a := by positivity
    linarith
  have key : ν * (2 * κ * d + 4 * κ ^ 2 * r ^ 2) + 2 * κ * inner ℝ b x < lam := by
    have h1 : 2 * κ * inner ℝ b x ≤ 2 * κ * (-q * r ^ 2 + M * r) :=
      mul_le_mul_of_nonneg_left hbx (by positivity)
    have h2 : ν * (2 * κ * d + 4 * κ ^ 2 * r ^ 2) + 2 * κ * (-q * r ^ 2 + M * r) =
        2 * ν * κ * d + (-a * r ^ 2 + 2 * κ * M * r) := by rw [ha]; ring
    rw [hlam]
    linarith
  have := mul_lt_mul_of_pos_left key hφp
  nlinarith

end HRS.MS.Mov63

end
