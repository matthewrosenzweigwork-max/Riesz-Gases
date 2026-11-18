import HRS.MC.SEdgeVocab
import HRS.MC.SEdgeB1
import HRS.MC.SEdgeB6
import HRS.MC.SEdgeB9sym
import HRS.Equilibrium.LocalDivTaylor

/-!
# Packet B13a: mean bias of the drift observable (relocation of `sed_B13a_bias`)

`C_ab = mu(phi_b-response . ...)`: with `rphi` the smooth representative of `responseInverse (phi b)` (B1),
B9sym (i) gives `mu(v_a . grad phi_b) = mu(r_a phi_b)` and (ii) gives `mu(phi_b r_a) = mu(phi_a rphi)`, so
`C_ab = mu(v_a . grad phi_b)`.  Then B6 applied to the smooth observable `w = v_a . grad phi_b` gives the `O(1/N)` bias.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B13a

open HRS.Sec7
open HRS.MC.SEdge

variable {d : ℕ} {s : ℝ}

theorem b13a_isSmooth_sum {ι : Type*} (S : Finset ι) {f : ι → Torus d → ℝ}
    (h : ∀ i, Torus.IsSmooth (f i)) : Torus.IsSmooth (fun x => ∑ i ∈ S, f i x) := by
  unfold Torus.IsSmooth Torus.IsCk Torus.lift
  exact ContDiff.sum fun i _ => h i

theorem b13a_isSmooth_mul {f g : Torus d → ℝ} (hf : Torus.IsSmooth f) (hg : Torus.IsSmooth g) :
    Torus.IsSmooth (fun x => f x * g x) := by
  unfold Torus.IsSmooth Torus.IsCk Torus.lift at hf hg ⊢
  exact ContDiff.mul hf hg

theorem sed_B13a_bias_proof (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 ≤ β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {p : ℕ} {φ : Fin p → Torus d → ℝ}
    (hφ : ∀ a, Torus.IsSmooth (φ a))
    {a b : Fin p} {ra : Torus d → ℝ} (hra : Torus.IsSmooth ra) {v : Fin d → Torus d → ℝ}
    (hv : ∀ j, Torus.IsSmooth (v j))
    (hdiv : ∀ x, ∑ j, Torus.partialDeriv j (fun y => ρ y * v j y) x = -(ρ x * ra x))
    (hresp : ∀ x, ra x + β * Kop (periodicRiesz d s) (withDensityReal ρ) ra x =
      projMean (withDensityReal ρ) (φ a) x) :
    ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
      |sed_Cmat d s β ρ φ a b - ∫ X, sed_A v (φ b) X ∂(sed_Q d s N β ρ)| ≤ K / N := by
  -- smooth representative of the response to `phi b` (B1)
  obtain ⟨rφ, -, hrφ, -, hae, hrespφ, -, -⟩ :=
    HRS.MC.SEdge.B1.sed_B1_regular_proof hd hs0 hs hβ hρ (hφ b)
  obtain ⟨hsymI, hsymII⟩ := HRS.MC.SEdge.B9sym.sed_B9sym_response_proof hd hs0 hs hβ hρ
    (hφ a) (hφ b) hra hrφ hv hdiv hresp hrespφ
  -- the covariance equals the smooth-representative pairing
  have h1 : ∫ x, φ a x * responseInverse (periodicRiesz d s) (withDensityReal ρ) β (φ b) x
      ∂(withDensityReal ρ) = ∫ x, φ a x * rφ x ∂(withDensityReal ρ) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  have h2 : ∫ x, sed_drift v (φ b) x ∂(withDensityReal ρ) =
      ∫ x, φ a x * rφ x ∂(withDensityReal ρ) := by
    rw [hsymI, ← hsymII]
    congr 1
    funext x
    ring
  have hC : sed_Cmat d s β ρ φ a b = ∫ x, sed_drift v (φ b) x ∂(withDensityReal ρ) := by
    simp only [sed_Cmat, Matrix.of_apply]
    rw [h1, h2]
  -- the drift observable is smooth, so B6 applies
  have hwsm : Torus.IsSmooth (sed_drift v (φ b)) := by
    have := b13a_isSmooth_sum (Finset.univ : Finset (Fin d))
      (f := fun k x => v k x * Torus.partialDeriv k (φ b) x)
      (fun k => b13a_isSmooth_mul (hv k) (HRS.LocalDivAux.isSmooth_partialDeriv (hφ b) k))
    exact this
  obtain ⟨C, hCB⟩ := HRS.MC.SEdge.B6.sed_B6_mean_bias_proof hd hs0 hs hβ hρ hwsm
  refine ⟨C, fun N hN => ?_⟩
  have h := hCB N hN
  rw [hC, abs_sub_comm]
  exact h

end HRS.MC.SEdge.B13a


end
