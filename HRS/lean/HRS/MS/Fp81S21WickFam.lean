import HRS.MS.Fp81S21WickB317
import HRS.MS.Fp81S21WickG2

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3

/-- The half-Wick operator associated with a supplied bounded Gaussian map
`L`. It acts on the full product `L²` kernel space. -/
def fp81s21_wickFam_operator
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (G : GaussianRealization R)
    (L : Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ) →L[ℝ] Lp ℝ 2 G.P)
    (Kstar : ℝ)
    (hL : ‖L‖ ≤ Kstar)
    (hJoint : ∀ r (v : Fin r → Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ)),
      HRS.IsCenteredGaussian (G.P.map fun ω => fun i => (L (v i)) ω)) :
    Lp ℝ 2 ((HRS.Whole.withDensityReal R.ρβ).prod
      (HRS.Whole.withDensityReal R.ρβ)) →L[ℝ] Lp ℝ 2 G.P := by
  letI : IsProbabilityMeasure (HRS.Whole.withDensityReal R.ρβ) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  exact fp81s21_wickG_operator L Kstar hL hJoint

/-- Every oscillator test is square-integrable under the supplied thermal
reference probability measure. -/
private theorem fp81s21_wickFam_oscillator_memLp
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (φ : Euc p.d → ℝ)
    (hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ) :
    MemLp φ 2 (HRS.Whole.withDensityReal R.ρβ) := by
  obtain ⟨_, _, hthermal⟩ := sol13_uniform_thermal_sup_bound p
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hρeq : R.ρβ = HRS.Whole.thermalDensity p.d p.s p.a p.β :=
    HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ R.thermal
  have hρmeas : Measurable R.ρβ := by
    obtain ⟨-, ψ'', hψ''⟩ := HRS.MS.S21.s21_schwartz_thermal
      p.hd p.hs0 hsd p.ha p.hβ
    rw [hρeq, ← hψ'']
    exact ψ''.continuous.measurable
  exact HRS.MS.S111X1.x1_osc_memLp hρmeas
    (fun x => (HRS.Whole.u4_thermal_pos R.thermal x).le)
    (hthermal δ R) hφ

/-- Uniform-in-time supplied-Gaussian half-Wick family.  The common `Kstar`
is selected before the realization `G` and time `u`, exactly as in the
Gaussian extension theorem. The linear map agrees with the time-`u`
oscillator evaluations and is centered; its half-Wick operator has the sharp
operator bound and is centered. -/
theorem fp81s21_wickFam_supplied_operator (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ Kstar : ℝ, 0 ≤ Kstar ∧
          ∀ G : GaussianRealization R, ∀ u : ℝ, 0 ≤ u →
            ∃ L : Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ) →L[ℝ]
                Lp ℝ 2 G.P,
              ∃ hL : ‖L‖ ≤ Kstar,
                ∃ hJoint : ∀ r (v : Fin r →
                    Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ)),
                    HRS.IsCenteredGaussian
                      (G.P.map fun ω => fun i => (L (v i)) ω),
                  (∀ φ : Euc p.d → ℝ,
                    IsOscTest (wholeSpaceIndex p.d : ℝ) φ →
                    ∀ hφ : MemLp φ 2 (HRS.Whole.withDensityReal R.ρβ),
                      L (hφ.toLp φ) =ᵐ[G.P]
                        fun ω => OscDual.eval (G.Z u ω) φ) ∧
                  (∀ f : Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ),
                    ∫ ω, (L f) ω ∂G.P = 0) ∧
                  ‖fp81s21_wickFam_operator R G L Kstar hL hJoint‖ ≤
                    Kstar ^ 2 / Real.sqrt 2 ∧
                  ∀ k : Lp ℝ 2 ((HRS.Whole.withDensityReal R.ρβ).prod
                      (HRS.Whole.withDensityReal R.ρβ)),
                    (∫ ω, fp81s21_wickFam_operator R G L Kstar hL hJoint k ω
                      ∂G.P) = 0 := by
  obtain ⟨δ0, hδ0, hδ0half, hG2⟩ :=
    fp81s21_wickG_extension_joint_gaussian p
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R
  letI : IsProbabilityMeasure (HRS.Whole.withDensityReal R.ρβ) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  obtain ⟨Kstar, hKstar, hG2R⟩ := hG2 δ hδ hδle R
  refine ⟨Kstar, hKstar, ?_⟩
  intro G u hu
  obtain ⟨L, hL, hAgree, hCenter, hJointData⟩ := hG2R G u hu
  let hJoint : ∀ r (v : Fin r → Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ)),
      HRS.IsCenteredGaussian (G.P.map fun ω => fun i => (L (v i)) ω) :=
    fun r v => (hJointData r v).1
  refine ⟨L, hL, hJoint, hAgree, hCenter, ?_, ?_⟩
  · simpa [fp81s21_wickFam_operator] using
      fp81s21_wickB311_operator_norm L Kstar hL hJoint
  · intro k
    simpa [fp81s21_wickFam_operator] using
      fp81s21_wickB312_centered L Kstar hL hJoint k

/-- On oscillator-test factors, the supplied-Gaussian operator agrees almost
everywhere with the finite half-Wick polynomial formed from the extension
`L`.  This is the finite-rank identity with the test functions' `L²`
membership discharged from the trajectory's thermal bound. -/
theorem fp81s21_wickFam_oscillator_finite_rank
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (G : GaussianRealization R)
    (L : Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ) →L[ℝ] Lp ℝ 2 G.P)
    (Kstar : ℝ) (hL : ‖L‖ ≤ Kstar)
    (hJoint : ∀ r (v : Fin r → Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ)),
      HRS.IsCenteredGaussian (G.P.map fun ω => fun i => (L (v i)) ω))
    {n : ℕ} (φ : Fin n → Euc p.d → ℝ)
    (hφ : ∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i))
    (c : Fin n → Fin n → ℝ)
    (hk : MemLp (fp81s21_wickG_finite_rank_kernel φ c) 2
      ((HRS.Whole.withDensityReal R.ρβ).prod
        (HRS.Whole.withDensityReal R.ρβ))) :
    (fp81s21_wickFam_operator R G L Kstar hL hJoint
      (hk.toLp (fp81s21_wickG_finite_rank_kernel φ c)) : G.Ω → ℝ) =ᵐ[G.P]
      fp81s21_wickG_finite_rank_polynomial L φ
        (fun i => fp81s21_wickFam_oscillator_memLp p R (φ i) (hφ i)) c := by
  let μstar : Measure (Euc p.d) := HRS.Whole.withDensityReal R.ρβ
  letI : IsProbabilityMeasure μstar :=
    HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  let hu : ∀ i, MemLp (φ i) 2 μstar := fun i =>
    fp81s21_wickFam_oscillator_memLp p R (φ i) (hφ i)
  have hW : MemLp (fp81s21_wickG_finite_rank_polynomial L φ hu c) 2 G.P :=
    (fp81s21_wickG_finite_rank_bound L Kstar hL hJoint φ hu c).2.1
  have hAgree := fp81s21_wickB316_finite_rank_agreement
    L Kstar hL hJoint φ hu c hk hW
  have hAgreeAE := Lp.ext_iff.mp hAgree
  filter_upwards [hAgreeAE, hW.coeFn_toLp] with ω hOp hPoly
  exact hOp.trans hPoly

#print axioms fp81s21_wickFam_supplied_operator
#print axioms fp81s21_wickFam_oscillator_finite_rank

end HRS.Fp81.S21

end
