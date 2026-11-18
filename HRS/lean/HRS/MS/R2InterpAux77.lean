import HRS.MS.R2InterpAux76
import HRS.MS.R2InterpAux67
import HRS.MS.R2QtAux1
import HRS.MS.R2S11Aux1
import HRS.MS.WsStatAux4

/-!
# S10.2 (worker S102), part 77 (packet M1a): the time marginals of the Gibbs-started particle system have an `L^p` density against `Q_{N,β}`

Reweighting `P' = P.withDensity (φ₀(X₀)⁻¹)`, `φ₀ = dQ_{N,γ}/dQ_{N,β}`, the invariance `hinv` gives `law_{P'}(X_t) = Q_{N,β}`, hence `law_P(X_t) = (Q_{N,γ}) κ` with
`κ = condDistrib X_t X₀ P'` preserving `Q_{N,β}`, and `s92_quench_density` applies.  `γ > 0` is assumed (the quench transfer needs `b₀ > 0`).
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

variable {d N : ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem s102_rew_inv {E : Type*} [MeasurableSpace E] (P : Measure Ω) (X0 : Ω → E) (hX0 : Measurable X0)
    (φ : E → ℝ≥0∞) (hφ : Measurable φ) (hpos : ∀ x, 0 < φ x) (hfin : ∀ x, φ x ≠ ⊤) :
    P = (s102_rew P X0 φ).withDensity (fun ω => φ (X0 ω)) := by
  unfold s102_rew
  rw [← withDensity_mul P (f := fun ω => (φ (X0 ω))⁻¹) (g := fun ω => φ (X0 ω)) (hφ.comp hX0).inv (hφ.comp hX0)]
  have : ((fun ω => (φ (X0 ω))⁻¹) * (fun ω => φ (X0 ω))) = fun _ => (1 : ℝ≥0∞) := by
    funext ω
    simp only [Pi.mul_apply]
    exact ENNReal.inv_mul_cancel (hpos _).ne' (hfin _)
  rw [this]
  exact withDensity_one.symm

theorem s102_strong_rew {P P' : Measure Ω} {D : WholeDyn d} {T : ℝ} {X0 : Ω → EucConfig d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N} (hS : IsWholeStrongSolution P D T X0 W X)
    (hac : P' ≪ P) : IsWholeStrongSolution P' D T X0 W X :=
  ⟨hac.ae_le hS.init, hac.ae_le hS.eqn, hac.ae_le hS.cont, hS.adapted, hac.ae_le hS.no_collision⟩

theorem s102_strong_ae {P : Measure Ω} {D : WholeDyn d} {T : ℝ} {X0 : Ω → EucConfig d N}
    {W W' : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N} (hS : IsWholeStrongSolution P D T X0 W X)
    (hae : ∀ᵐ ζ ∂P, ∀ t, W' t ζ = W t ζ) : IsWholeStrongSolution P D T X0 W' X := by
  refine ⟨hS.init, ?_, hS.cont, hS.adapted, hS.no_collision⟩
  filter_upwards [hS.eqn, hae] with ζ h hζ
  intro t ht
  obtain ⟨h1, h2⟩ := h t ht
  refine ⟨h1, fun i => ?_⟩
  rw [hζ t, hζ 0]
  exact h2 i

/-- The measurable version of `W` built from the Brownian filtration process `W'`. -/
def s102_Wt (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) : ℝ≥0 → Ω → (Fin N → Euc d) :=
  fun t ζ i => WithLp.toLp 2 (fun j => W' t ζ (i, j))

theorem s102_Wt_measurable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ)
    (hm : ∀ t : ℝ≥0, Measurable[ℱ t] (W' t)) (t : ℝ≥0) : Measurable (s102_Wt W' t) := by
  refine measurable_pi_iff.2 (fun i => ?_)
  have : Measurable (fun ζ j => W' t ζ (i, j)) :=
    measurable_pi_iff.2 (fun j => (measurable_pi_apply (i, j)).comp ((hm t).mono (ℱ.le t) le_rfl))
  exact (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.measurable.comp this

end HRS.MS.R2Interp

end
