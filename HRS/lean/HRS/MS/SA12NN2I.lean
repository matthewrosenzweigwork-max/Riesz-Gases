import HRS.MS.SA12NN2H

/-!
# S.A.12 N2 (SA12N), part I: the frequency-space commutator estimate

`‖∫ m_q(F u · conj F(x_l v)) - ∫ m_q (F(x_l u) · conj F v)‖ ≤ (3 κ ‖q‖² / 2π) ‖u‖₂ ‖v‖₂`
for `u, v ∈ C_c`, where `F = 𝓕` and `m_q = sa12n_mq κ q`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff ComplexConjugate FourierTransform

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.MS.UniqN1a HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

/-- `û` as a pointwise Fourier integral. -/
def sa12n_F (a : Euc d → ℝ) : Euc d → ℂ := 𝓕 (fun x : Euc d => ((a x : ℝ) : ℂ))

theorem sa12n_F_diff {a : Euc d → ℝ} (ha : Continuous a) (hc : HasCompactSupport a) :
    Differentiable ℝ (sa12n_F a) := by
  have hfc : Continuous (fun x : Euc d => ((a x : ℝ) : ℂ)) := Complex.continuous_ofReal.comp ha
  have hcf : HasCompactSupport (fun x : Euc d => ((a x : ℝ) : ℂ)) :=
    hc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  exact Real.differentiable_fourier (hfc.integrable_of_hasCompactSupport hcf)
    ((continuous_norm.mul hfc.norm).integrable_of_hasCompactSupport hcf.norm.mul_left)

theorem sa12n_F_ae {a : Euc d → ℝ} (ha : Continuous a) (hc : HasCompactSupport a) :
    fourierL2 a =ᵐ[volume] sa12n_F a :=
  HRS.Commutator.Whole.energyAux_fourierL2_eq a (ha.integrable_of_hasCompactSupport hc)
    (ha.memLp_of_hasCompactSupport hc)

theorem sa12n_F_sq {a : Euc d → ℝ} (ha : Continuous a) (hc : HasCompactSupport a) :
    Integrable (fun ξ => ‖sa12n_F a ξ‖ ^ 2) volume ∧ ∫ ξ, ‖sa12n_F a ξ‖ ^ 2 = ∫ x, a x ^ 2 := by
  have hL : MemLp a 2 volume := ha.memLp_of_hasCompactSupport hc
  have hae := sa12n_F_ae ha hc
  refine ⟨(integrable_norm_sq_fourierL2 hL).congr ?_, ?_⟩
  · filter_upwards [hae] with ξ hξ
    rw [hξ]
  · rw [← integral_norm_sq_fourierL2 hL]
    refine integral_congr_ae ?_
    filter_upwards [hae] with ξ hξ
    rw [hξ]

theorem sa12n_conj_mul (z : ℂ) :
    conj (-(2 * (Real.pi : ℂ) * Complex.I) * z) = (2 * (Real.pi : ℂ) * Complex.I) * conj z := by
  simp only [map_mul, map_neg, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem sa12n_pair_core (hd : 1 ≤ d) {κ : ℝ} (hκ : 0 ≤ κ) (q : Euc d) (l : Fin d) {u v : Euc d → ℝ}
    (hu : Continuous u) (huc : HasCompactSupport u) (hv : Continuous v) (hvc : HasCompactSupport v)
    (hA : Integrable (fun ξ => (sa12n_mq κ q ξ : ℂ) *
      (sa12n_F (fun x => x l * u x) ξ * conj (sa12n_F v ξ))) volume)
    (hB : Integrable (fun ξ => (sa12n_mq κ q ξ : ℂ) *
      (sa12n_F u ξ * conj (sa12n_F (fun x => x l * v x) ξ))) volume)
    (hC : Integrable (fun ξ => (sa12n_mq κ q ξ : ℂ) *
      (sa12n_F u ξ * conj (sa12n_F v ξ))) volume) :
    ‖(∫ ξ, (sa12n_mq κ q ξ : ℂ) * (sa12n_F u ξ * conj (sa12n_F (fun x => x l * v x) ξ))) -
        ∫ ξ, (sa12n_mq κ q ξ : ℂ) * (sa12n_F (fun x => x l * u x) ξ * conj (sa12n_F v ξ))‖ ≤
      3 * κ * ‖q‖ ^ 2 / (2 * Real.pi) * (Real.sqrt (∫ x, u x ^ 2) * Real.sqrt (∫ x, v x ^ 2)) := by
  set e : Euc d := EuclideanSpace.single l (1 : ℝ) with he
  set m : Euc d → ℝ := sa12n_mq κ q with hm
  set Fu := sa12n_F u with hFu
  set Fv := sa12n_F v with hFv
  set Fu1 := sa12n_F (fun x => x l * u x) with hFu1
  set Fv1 := sa12n_F (fun x => x l * v x) with hFv1
  have hdu : ∀ ξ, fderiv ℝ Fu ξ e = -(2 * (Real.pi : ℂ) * Complex.I) * Fu1 ξ := fun ξ =>
    sa12n_fourier_deriv hu huc l ξ
  have hdv : ∀ ξ, fderiv ℝ Fv ξ e = -(2 * (Real.pi : ℂ) * Complex.I) * Fv1 ξ := fun ξ =>
    sa12n_fourier_deriv hv hvc l ξ
  have hdu' : ∀ ξ, fderiv ℝ Fu ξ (EuclideanSpace.single l 1) =
      -(2 * (Real.pi : ℂ) * Complex.I) * Fu1 ξ := hdu
  have hdv' : ∀ ξ, fderiv ℝ Fv ξ (EuclideanSpace.single l 1) =
      -(2 * (Real.pi : ℂ) * Complex.I) * Fv1 ξ := hdv
  have hLu : MemLp u 2 volume := hu.memLp_of_hasCompactSupport huc
  have hLv : MemLp v 2 volume := hv.memLp_of_hasCompactSupport hvc
  have hI4 : Integrable (fun ξ => Fu ξ * conj (Fv ξ)) volume := by
    refine (integrable_fourierL2_mul_conj hLu hLv).congr ?_
    filter_upwards [sa12n_F_ae hu huc, sa12n_F_ae hv hvc] with ξ h1 h2
    rw [h1, h2]
  have hfreq := sa12n_freq_ibp hd l (m := m) (Λ := 3 * κ * ‖q‖ ^ 2) (M0 := κ * ‖q‖ ^ 2)
    (by positivity) (by positivity) (sa12n_mq_continuous hκ q)
    (fun ξ hξ => (sa12n_mq_deriv hκ q hξ l).1) (fun ξ hξ => (sa12n_mq_deriv hκ q hξ l).2)
    (fun ξ => by
      have := sa12n_mq_bound hκ q ξ
      rw [hm]; linarith [this])
    (F1 := Fu) (F2 := Fv) (sa12n_F_diff hu huc) (sa12n_F_diff hv hvc)
    ((hA.const_mul (-(2 * (Real.pi : ℂ) * Complex.I))).congr (Eventually.of_forall fun ξ => by
      simp only [hdu' ξ]; ring))
    ((hB.const_mul (2 * (Real.pi : ℂ) * Complex.I)).congr (Eventually.of_forall fun ξ => by
      simp only [hdv' ξ, sa12n_conj_mul]; ring))
    hC hI4
  have hZ : ∫ ξ, (m ξ : ℂ) * (fderiv ℝ Fu ξ (EuclideanSpace.single l 1) * conj (Fv ξ) +
        Fu ξ * conj (fderiv ℝ Fv ξ (EuclideanSpace.single l 1))) =
      (2 * (Real.pi : ℂ) * Complex.I) * ((∫ ξ, (m ξ : ℂ) * (Fu ξ * conj (Fv1 ξ))) -
        ∫ ξ, (m ξ : ℂ) * (Fu1 ξ * conj (Fv ξ))) := by
    have e1 : (fun ξ => (m ξ : ℂ) * (fderiv ℝ Fu ξ (EuclideanSpace.single l 1) * conj (Fv ξ) +
        Fu ξ * conj (fderiv ℝ Fv ξ (EuclideanSpace.single l 1)))) =
        fun ξ => (-(2 * (Real.pi : ℂ) * Complex.I)) * ((m ξ : ℂ) * (Fu1 ξ * conj (Fv ξ))) +
          (2 * (Real.pi : ℂ) * Complex.I) * ((m ξ : ℂ) * (Fu ξ * conj (Fv1 ξ))) :=
      funext fun ξ => by simp only [hdu' ξ, hdv' ξ, sa12n_conj_mul]; ring
    rw [e1, integral_add (hA.const_mul _) (hB.const_mul _), integral_const_mul, integral_const_mul]
    ring
  have hP := sa12n_F_sq hu huc
  have hQ := sa12n_F_sq hv hvc
  have hnorm : ∀ ξ, ‖Fu ξ * conj (Fv ξ)‖ = ‖Fu ξ‖ * ‖Fv ξ‖ := fun ξ => by
    rw [norm_mul, Complex.norm_conj]
  have hR : Integrable (fun ξ => ‖Fu ξ‖ * ‖Fv ξ‖) volume :=
    hI4.norm.congr (Eventually.of_forall hnorm)
  have hcs := cs_aux hP.1 hQ.1 hR (fun t ξ => by nlinarith [sq_nonneg (t * ‖Fu ξ‖ - ‖Fv ξ‖)])
  rw [hP.2, hQ.2] at hcs
  have hint : ∫ ξ, ‖Fu ξ * conj (Fv ξ)‖ = ∫ ξ, ‖Fu ξ‖ * ‖Fv ξ‖ :=
    integral_congr_ae (Eventually.of_forall hnorm)
  have hsq : ∫ ξ, ‖Fu ξ * conj (Fv ξ)‖ ≤ Real.sqrt (∫ x, u x ^ 2) * Real.sqrt (∫ x, v x ^ 2) := by
    rw [hint, ← Real.sqrt_mul (integral_nonneg (fun x => sq_nonneg _))]
    exact (le_abs_self _).trans (Real.abs_le_sqrt hcs)
  rw [hZ, norm_mul] at hfreq
  have h2pi : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    simp [abs_of_pos Real.pi_pos]
  rw [h2pi] at hfreq
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hpi]
  exact (mul_comm _ _).le.trans (hfreq.trans (mul_le_mul_of_nonneg_left hsq (by positivity)))

end HRS.MH.AdjointRd.Phase2SA12Near
