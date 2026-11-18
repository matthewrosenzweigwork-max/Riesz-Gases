import HRS.MS.Fp81S21ErrorPhysical
import HRS.MS.Fp81S21GaussianContractionO1
import HRS.MS.Fp81S21GaussianWindowRS2
import HRS.MS.Fp81S21GaussLaw3
import HRS.MS.Fp81S21ErrorEnvelope2

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S21E
attribute [local instance] fp81s21_initialMeasure_isProbability

/-- The interpolation, contraction, and two cutoff bounds for the same records.
The particle carrier is polymorphic; its concrete packet-20 carrier may be used. -/
def fp81s21_physical_supplied_data
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Q : fp81s21_Physical35 p R)
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d) H))
    (C c : ℝ) (E J : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup J] [NormedSpace ℝ J] [CompleteSpace J] : Prop :=
  ∀ L : ℝ, 0 < L → ∃ eL : ℕ → ℝ,
    (∀ N, 0 ≤ eL N) ∧ Tendsto eL atTop (𝓝 0) ∧
    ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N, ∀ (a : ℝ) (ha : 0 ≤ a)
      (Φ : Window p → ℝ), Φ ∈ CbUnitBall (Window p) 5 →
      ∃ (Ad : A.Ω → ℝ → E →L[ℝ] ℝ) (Fd : A.Ω → ℝ → E)
        (Aj : A.Ω → ℝ → J →L[ℝ] ℝ) (Fj : A.Ω → ℝ → J),
      ∃ (WN : fp81s21_WindowRS A.P (a + p.T) Ad Fd Aj Fj)
        (Wg : fp81s21_GRS Q future a ha Φ),
        Real.sqrt N * ((∫ ω, Φ (r26t3_zetapath A a ω) ∂A.P) -
          ∫ X, initialHeat future a ha Φ 0 (initialWindow R N a X) ∂(r26t3_Q R N)) =
            fp81s21_WindowRS_corr WN 0 (a + p.T) ∧
        (1 / 6 : ℝ) * (∫ ω, (s21eKappa Q.src.G0.P (initialKappa R a)
          (fp81s21_physical35_D Q.tofp81s21_Gaussian35Selection Q.OD a)
          (r26t3_Zpath Q.src.G0 a)
          (fun ω => (fp81s21_physical35_J Q.tofp81s21_Gaussian35Selection Q.OJ a ω :
            TensorDual (Window p) 2)))
          (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath Q.src.G0 a ω)) ∂Q.src.G0.P) =
          (1 / 6 : ℝ) * (∫ ω, initialKappa R a
            (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath Q.src.G0 a ω)) ∂Q.src.G0.P) +
            fp81s21_WindowRS_corr Wg.WG 0 (a + p.T) ∧
        |fp81s21_WindowRS_corr WN (max (a - L) 0) (a + p.T) -
          fp81s21_WindowRS_corr Wg.WG (max (a - L) 0) (a + p.T)| ≤ eL N ∧
        |fp81s21_WindowRS_corr WN 0 (max (a - L) 0)| +
          |fp81s21_WindowRS_corr Wg.WG 0 (max (a - L) 0)| ≤ C * Real.exp (-c * L)

/-- Supplied physical records yield the actual error-envelope decomposition. -/
theorem fp81s21_errorEnvelope_physical_supplied
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Q : fp81s21_Physical35 p R)
    (O1 : fp81s21_O1_gaussian_wick p.d p.s p.a p.β p.γ p.T R.ρ)
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d) H))
    (α : ℕ → ℝ) (C c : ℝ)
    (E J : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup J] [NormedSpace ℝ J] [CompleteSpace J]
    (hκ : ∀ a : ℝ, 0 ≤ a → (fp81s21_O1_kappa O1 a : TensorDual (Window p) 3) =
      s21eKappa Q.src.G0.P (initialKappa R a)
        (fp81s21_physical35_D Q.tofp81s21_Gaussian35Selection Q.OD a)
        (r26t3_Zpath Q.src.G0 a)
        (fun ω => (fp81s21_physical35_J Q.tofp81s21_Gaussian35Selection Q.OJ a ω :
          TensorDual (Window p) 2)))
    (hα : (∀ N, 0 ≤ α N) ∧ Tendsto α atTop (𝓝 0))
    (hinit : ∀ N : ℕ, 2 ≤ N → ∀ (a : ℝ) (ha : 0 ≤ a) (Φ : Window p → ℝ),
      Φ ∈ CbUnitBall (Window p) 5 → ∀ G : GaussianRealization R,
        |initialRemainder R future N G a ha Φ| ≤ α N)
    (hC : 0 ≤ C) (_hc : 0 < c)
    (hsup : fp81s21_physical_supplied_data p R Q future C c E J) :
    ∀ L : ℝ, 0 < L → ∃ eL : ℕ → ℝ,
      (∀ N, 0 ≤ eL N) ∧ Tendsto eL atTop (𝓝 0) ∧
      ∀ N : ℕ, 2 ≤ N →
        fp81s21_errorEnvelope p R (fp81s21_O1_kappa O1) N ≤
          α N + eL N + C * Real.exp (-c * L) := by
  intro L hL
  obtain ⟨eL, he, het, hs⟩ := hsup L hL
  refine ⟨eL, he, het, ?_⟩
  intro N hN
  apply fp81s21_errorEnvelope_le_of_pointwise p R O1 N hN _
  · exact add_nonneg (add_nonneg (hα.1 N) (he N))
      (mul_nonneg hC (Real.exp_pos _).le)
  · intro A G a ha Φ hΦ
    obtain ⟨Ad, Fd, Aj, Fj, WN, Wg, hI, hcontract, hrecent, hremote⟩ :=
      hs N hN A a ha Φ hΦ
    rw [fp81s21_r26t3_error_realization_invariant p R Q.src.G0
      (fp81s21_O1_kappa O1) A G a ha Φ hΦ]
    have hc' := fp81s21_gaussian_contraction_O1 Q O1 a ha Φ Wg.WG (hκ a ha) hcontract
    have hb := fp81s21_error_physical_bound p R future N A Q.src.G0 a ha Φ
      (fp81s21_O1_kappa O1) WN Wg.WG hI hc' L hL.le
    have hi := hinit N hN a ha Φ hΦ Q.src.G0
    linarith

/-- The O5 consumer only needs convergence of each recent profile. -/
theorem fp81s21_errorEnvelope_physical_hdec
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (O1 : fp81s21_O1_gaussian_wick p.d p.s p.a p.β p.γ p.T R.ρ)
    (α : ℕ → ℝ) (C c : ℝ)
    (hdec : ∀ L : ℝ, 0 < L → ∃ eL : ℕ → ℝ,
      (∀ N, 0 ≤ eL N) ∧ Tendsto eL atTop (𝓝 0) ∧
      ∀ N : ℕ, 2 ≤ N →
        fp81s21_errorEnvelope p R (fp81s21_O1_kappa O1) N ≤
          α N + eL N + C * Real.exp (-c * L)) :
    ∀ L : ℝ, 0 < L → ∃ eL : ℕ → ℝ,
      Tendsto eL atTop (𝓝 0) ∧ ∀ N : ℕ, 2 ≤ N →
        fp81s21_errorEnvelope p R (fp81s21_O1_kappa O1) N ≤
          α N + eL N + C * Real.exp (-c * L) := by
  intro L hL
  obtain ⟨eL, _, ht, hb⟩ := hdec L hL
  exact ⟨eL, ht, hb⟩

#print axioms fp81s21_errorEnvelope_physical_hdec
#print axioms fp81s21_physical_supplied_data
#print axioms fp81s21_errorEnvelope_physical_supplied
end HRS.Fp81.S21
end
