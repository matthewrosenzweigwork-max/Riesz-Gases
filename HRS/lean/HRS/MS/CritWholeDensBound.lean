import HRS.MS.CritWholeRespErr
import HRS.MS.CritWholePoleCoefficient
import HRS.MS.SharpBiasAux1
import HRS.Whole.Critical

/-!
# S8.1 XS (S81d), CR12: `critical_density_bound`

`W_N = θ - 1 - a_N c_β R_{β,μ} P_μ ρ` (`a_N = log N / N`, `c_β = β²|S^{d-1}|/d`) solves `W + β K_μ W = P_μ (E_N + D_N - a_N c_β ρ)`
(CR11 gives `E_N = z + β K_μ z - P_μ D_N ∈ L²_0`; `R P_μ ρ` is the response; linearity `s71_Kop_lin`).  The forcing is bounded in `L²` by
`‖E_N‖₂ + sup |D_N - a_N c_β ρ|`, the sup bound being CR09 plus the scalar coefficient K3 (`s81bd_pole_taylor_beta_N`);
`s71_response_bound` contracts.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole HRS.MS.Wr

namespace HRS.Whole.S81b

variable {d : ℕ}

/-- `z_N = θ - 1 ∈ L²_0(μ)`. -/
theorem s81d_z_zero (hd : 2 ≤ d) (M βm βp : ℝ) (hβm : 0 < βm) (hβ : βm ≤ βp) :
    ∀ D : Data d M βm βp, ∀ N : ℕ, 2 ≤ N → MemL2Zero (mu D) (fun x => theta D N x - 1) := by
  have hd1 : 1 ≤ d := by omega
  have hs0 := s81c_hs0 hd1
  have hsd := s81c_hsd hd1
  obtain ⟨Cθ, hCθ1, hCθ⟩ := s81b_full_density_sup hd M βm βp hβm hβ
  intro D N hN
  have hβ0 : 0 < D.beta := hβm.trans_le D.beta_mem.1
  have := s81c_prob D
  have hCθ0 : 0 < Cθ := by linarith
  obtain ⟨-, hδ1, -⟩ := s81c_num_facts hd1 hN
  have hsδ1 : Real.sqrt (deltaN d ((d : ℝ) / 2) N) ≤ 1 := Real.sqrt_le_one.2 hδ1
  have hθ0 : ∀ x, 0 < theta D N x := fun x => lt_of_lt_of_le (inv_pos.2 hCθ0) (hCθ D N hN x).1
  have hzbd : ∀ x, |theta D N x - 1| ≤ Cθ := fun x => ((hCθ D N hN x).2).trans
    (by nlinarith [mul_le_mul_of_nonneg_left hsδ1 hCθ0.le])
  have hθle : ∀ x, theta D N x ≤ 1 + Cθ := fun x => by
    have := (abs_le.1 (hzbd x)).2
    linarith
  have hθm : Measurable (theta D N) := wr13d_theta_meas hd hs0 hsd D.prob D.bound hβ0.le (N - 1)
  have hθint : Integrable (theta D N) (mu D) :=
    Integrable.of_bound hθm.aestronglyMeasurable (1 + Cθ) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (hθ0 x)]; exact hθle x)
  have hθ1 : ∫ x, theta D N x ∂(mu D) = 1 :=
    wr13d_theta_integral hd hs0 hsd D.prob D.bound hβ0.le (n := N - 1) (by omega)
  refine ⟨MemLp.of_bound (hθm.sub_const 1).aestronglyMeasurable Cθ (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hzbd x), ?_⟩
  rw [integral_sub hθint (integrable_const _), hθ1]; simp

set_option maxHeartbeats 3200000 in
/-- **CR12** `critical_density_bound` (statement = Pro skeleton, copied). -/
theorem s81d_critical_density_bound (hd : 2 ≤ d) (M : ℝ) (Λ : ℝ≥0)
    (βm βp : ℝ) (hβm : 0 < βm) (hβ : βm ≤ βp) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D : Data d M βm βp, LipschitzWith Λ D.rho →
      ∀ N : ℕ, 2 ≤ N →
        MemLp (fun x => theta D N x - 1 -
          (Real.log N / N) * critBiasDensity d D.beta D.rho x) 2 (mu D) ∧
        l2Norm (mu D) (fun x => theta D N x - 1 -
          (Real.log N / N) * critBiasDensity d D.beta D.rho x) ≤ C * rate N := by
  have hd1 : 1 ≤ d := by omega
  have hs0 := s81c_hs0 hd1
  have hsd := s81c_hsd hd1
  obtain ⟨C11, hC110, hC11⟩ := s81d_relative_response_error hd M βm βp hβm hβ
  obtain ⟨C9, hC90, hC9⟩ := s81d_interacting_diagonal_reduction hd M βm βp hβm hβ
  obtain ⟨C3, hC30, hC3⟩ := BreakdownS81.s81bd_pole_taylor_beta_N hd M Λ βm βp hβm hβ
  obtain ⟨c1, c3, hc10, hc30, hnum⟩ := s81d_num (d := d) hd1
  have hz := s81d_z_zero hd M βm βp hβm hβ
  refine ⟨C11 + C9 + C3 * c1, by positivity, fun D hlip N hN => ?_⟩
  have hβ0 : 0 < D.beta := hβm.trans_le D.beta_mem.1
  have := s81c_prob D
  have hq : Q34.Q34Hyp d ((d : ℝ) / 2) D.rho M := ⟨hd1, hs0, hsd, D.prob, D.bound⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  obtain ⟨hE0, hEn⟩ := hC11 D N hN
  obtain ⟨hDm, hD9⟩ := hC9 D N hN
  obtain ⟨hc1N, -, -⟩ := hnum N hN
  have hrate0 : 0 ≤ rate N := div_nonneg (Real.sqrt_nonneg _) hN0.le
  have hz0 := hz D N hN
  have hM0 : 0 ≤ M := (D.prob.nonneg 0).trans (D.bound 0)
  have hρL : MemLp D.rho 2 (mu D) :=
    MemLp.of_bound D.prob.measurable.aestronglyMeasurable M (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (D.prob.nonneg x)]; exact D.bound x)
  have hρi : Integrable D.rho (mu D) := hρL.integrable one_le_two
  set aN : ℝ := Real.log N / N with haN
  set c : ℝ := D.beta ^ 2 * sphereArea d / d with hc
  set R : Euc d → ℝ := responseInverse (rieszKernel d ((d : ℝ) / 2)) (withDensityReal D.rho) D.beta D.rho with hR
  have hresp : IsResponse (rieszKernel d ((d : ℝ) / 2)) (withDensityReal D.rho) D.beta D.rho R :=
    HRS.Whole.S71.s71_resp_spec hq hβ0 hρL
  have hR0 : MemL2Zero (mu D) R := hresp.1
  set b : ℝ := -(aN * c) with hb
  set W : Euc d → ℝ := fun x => (theta D N x - 1) + b * R x with hW
  have hWeq : (fun x => theta D N x - 1 - (Real.log N / N) * critBiasDensity d D.beta D.rho x) = W := by
    funext x; simp only [hW, hb, haN, hc, critBiasDensity, hR]; ring
  rw [hWeq]
  have hWL : MemLp W 2 (mu D) := hz0.1.add (hR0.1.const_mul b)
  have hW0 : MemL2Zero (mu D) W := by
    refine ⟨hWL, ?_⟩
    simp only [hW]
    rw [integral_add (hz0.1.integrable one_le_two) ((hR0.1.integrable one_le_two).const_mul b),
      hz0.2, integral_const_mul, hR0.2]; simp
  -- the forcing
  set Δ : Euc d → ℝ := fun x => defect D N x + b * D.rho x with hΔ
  have hΔb : ∀ x, |Δ x| ≤ (C9 + C3 * c1) * rate N := by
    intro x
    obtain ⟨-, -, -, hdef⟩ := hD9 x
    obtain ⟨-, hK3⟩ := hC3 D.rho D.prob D.bound hlip D.beta D.beta_mem N hN x
    have h1 : Δ x = (defect D N x - ((N - 1 : ℕ) : ℝ) * ∫ y, taylorH ((D.beta / N) * critG d (x - y)) ∂(mu D)) +
        (((N - 1 : ℕ) : ℝ) * (∫ y, taylorH ((D.beta / N) * rieszKernel d ((d : ℝ) / 2) (x - y)) ∂(withDensityReal D.rho)) -
          (D.beta ^ 2 * sphereArea d / (d : ℝ)) * D.rho x * (Real.log N / N)) := by
      simp only [hΔ, hb, haN, hc]; ring
    rw [h1]
    refine (abs_add_le _ _).trans ?_
    have h2 : C3 / N ≤ C3 * c1 * rate N := by
      rw [div_eq_mul_inv, mul_assoc]
      exact mul_le_mul_of_nonneg_left hc1N hC30
    have h3 := hdef
    linarith
  have hΔm : Measurable Δ := hDm.add (measurable_const.mul D.prob.measurable)
  have hΔL : MemLp Δ 2 (mu D) :=
    MemLp.of_bound hΔm.aestronglyMeasurable ((C9 + C3 * c1) * rate N) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hΔb x)
  have hDi : Integrable (defect D N) (mu D) := by
    have : defect D N = fun x => Δ x - b * D.rho x := by funext x; simp only [hΔ]; ring
    rw [this]; exact (hΔL.integrable one_le_two).sub (hρi.const_mul b)
  set G : Euc d → ℝ := fun x => responseError D N x + Δ x with hG
  have hGL : MemLp G 2 (mu D) := hE0.1.add hΔL
  have hWG : ∀ᵐ x ∂(mu D), W x + D.beta * Kop (rieszKernel d ((d : ℝ) / 2)) (withDensityReal D.rho) W x =
      projMean (mu D) G x := by
    have hlin := HRS.Whole.S71.s71_Kop_lin hq hz0 hR0 1 b
    have hW' : (fun x => 1 * (theta D N x - 1) + b * R x) = W := by funext x; simp only [hW]; ring
    rw [hW'] at hlin
    filter_upwards [hlin, hresp.2] with x hx1 hx2
    have hE : responseError D N x = (theta D N x - 1) + D.beta * Kop (critG d) (mu D) (fun y => theta D N y - 1) x -
        projMean (mu D) (defect D N) x := rfl
    have hK : Kop (rieszKernel d ((d : ℝ) / 2)) (withDensityReal D.rho) W x =
        1 * Kop (critG d) (mu D) (fun y => theta D N y - 1) x + b * Kop (rieszKernel d ((d : ℝ) / 2)) (withDensityReal D.rho) R x := hx1
    have hi1 : Integrable (fun x => responseError D N x + defect D N x) (mu D) :=
      (hE0.1.integrable one_le_two).add hDi
    have hint : pair (mu D) G = pair (mu D) (defect D N) + b * pair (mu D) D.rho := by
      simp only [pair, hG, hΔ]
      have : (fun x => responseError D N x + (defect D N x + b * D.rho x)) =
          fun x => (responseError D N x + defect D N x) + b * D.rho x := by funext x; ring
      rw [this, integral_add hi1 (hρi.const_mul b),
        integral_add (hE0.1.integrable one_le_two) hDi, hE0.2, integral_const_mul]
      ring
    have hR1 : R x + D.beta * Kop (rieszKernel d ((d : ℝ) / 2)) (withDensityReal D.rho) R x =
        projMean (mu D) D.rho x := hx2
    have e1 : projMean (mu D) G x = G x - pair (mu D) G := rfl
    rw [e1, hint, hK]
    unfold projMean at hE hR1
    simp only [hW, hG, hΔ]
    linear_combination (-1 : ℝ) * hE + b * hR1
  have hbound := HRS.Whole.S71.s71_response_bound hq hβ0 hW0 hGL hWG
  refine ⟨hWL, hbound.trans ?_⟩
  have hGn : l2Norm (mu D) G ≤ l2Norm (mu D) (responseError D N) + l2Norm (mu D) Δ :=
    s81d_l2_add hE0.1 hΔL
  have hΔn : l2Norm (mu D) Δ ≤ (C9 + C3 * c1) * rate N :=
    s81d_l2_le_bound (by positivity) hΔb hΔm
  calc l2Norm (mu D) G ≤ _ := hGn
    _ ≤ C11 * rate N + (C9 + C3 * c1) * rate N := add_le_add hEn hΔn
    _ = _ := by ring

end HRS.Whole.S81b
