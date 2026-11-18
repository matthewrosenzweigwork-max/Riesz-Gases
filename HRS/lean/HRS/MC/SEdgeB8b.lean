import HRS.MC.SEdgeB8bAux9

/-!
# Packet B8b: Wick integration by parts for the Gaussian chaos limit

Relocated proof of `HRS.MC.SEdge.sed_B8b_chaos_ibp`.  Route: the finite-dimensional second-order
Gaussian IBP `sed_B8a_gauss_ibp2_proof` on the truncations `(G_i)_{i<L}`, then `L → ∞` using the
`L²` convergences of `hdata`, the Hilbert-Schmidt continuity of `h` on `L²(μ)` (envelope), and the
self-adjointness of the response operator.  Helper files: `HRS.MC.SEdgeB8bAux1` ... `Aux9`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B8b

open HRS.Sec7 HRS.Q08

section Gauss

variable {d : ℕ} {s : ℝ}

theorem sed_B8b_chaos_ibp_proof (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {c B : ℝ}
    (hc : ∀ z, z ≠ 0 → 1 ≤ periodicRiesz d s z + c) {h : Torus d → Torus d → ℝ}
    (hmeas : Measurable (Function.uncurry h)) (hsymm : ∀ x y, h x y = h y x)
    (hB : ∀ x y, x ≠ y → |h x y| ≤ B * (periodicRiesz d s (x - y) + c))
    {e : ℕ → Torus d → ℝ} (he : IsONBL2Zero (withDensityReal ρ) e) {p : ℕ}
    {φ : Fin p → Torus d → ℝ} (hφ : ∀ a, Measurable (φ a) ∧ ∃ M, ∀ x, |φ a x| ≤ M)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : ℕ → Ω → ℝ) (Qv : Ω → ℝ) (Lin : Fin p → Ω → ℝ)
    (hdata : sed_QLData d s β ρ h e φ P G Qv Lin) :
    law P (fun ω => (WithLp.toLp 2 fun a => Lin a ω : EuclideanSpace ℝ (Fin p))) =
        multivariateGaussian 0 (Matrix.of fun a b =>
          susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (φ a) (φ b)) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin p) → ℝ, MemCb 2 ψ →
        ∫ ω, Qv ω * ψ (WithLp.toLp 2 fun a => Lin a ω) ∂P =
          (1 / 2) * ∑ b, ∑ c',
              (∫ x, ∫ y, h x y *
                  responseInverse (periodicRiesz d s) (withDensityReal ρ) β (φ b) x *
                  responseInverse (periodicRiesz d s) (withDensityReal ρ) β (φ c') y
                  ∂(withDensityReal ρ) ∂(withDensityReal ρ)) *
                ∫ z, iteratedFDeriv ℝ 2 ψ z ![stdVec b, stdVec c']
                  ∂(multivariateGaussian 0 (Matrix.of fun a b =>
                    susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (φ a) (φ b))) := by
  obtain ⟨hGm, hQm, hLinm, hlawG, hLin, hQ⟩ := hdata
  let D : Q08Data d := ⟨s, β, ρ, c, B, h, e, p, φ, hd, hs0, hs, hβ, hρ, hc, hmeas, hsymm, hB, he, hφ⟩
  have hCs := q08_Cmat_spec D
  have hSpsd : ∀ n, (Matrix.of fun i j : Fin n => D.Cmat i j).PosSemidef := fun n =>
    (q08c_ch_cov_fin D.Cmat hCs.1 hCs.2.1 hCs.2.2.1 n).1
  have hmain := b8b_prob_main P G hGm (fun i j => D.Cmat i j) hSpsd hlawG (fun a k => D.coef a k)
    Lin hLinm hLin (fun i j => D.Hmat i j) Qv hQm hQ
    (Matrix.of fun a b => susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (φ a) (φ b))
    (fun a b => b8b_CL_tendsto D a b)
    (fun b c' => ∫ x, ∫ y, h x y *
      responseInverse (periodicRiesz d s) (withDensityReal ρ) β (φ b) x *
      responseInverse (periodicRiesz d s) (withDensityReal ρ) β (φ c') y
      ∂(withDensityReal ρ) ∂(withDensityReal ρ))
    (fun b c' => b8b_Theta_tendsto D b c')
  exact hmain


end Gauss

end HRS.MC.SEdge.B8b
