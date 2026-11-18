import HRS.MC.CepE5bAux10
import HRS.MC.CepE5bAux11
import HRS.MC.CepE5bAux8

/-!
# Packet CEPE5B, auxiliary 12: the `n`-step inequality

For the chamber solution `Z` of the drift `-G_n + F`,
`E ∫_0^T |G_n(Z)|² ≤ 2 (E Φ_n(z₀) + c_L) + E∫|F(Z)|² + σ'² E∫ tr D²Φ_n(Z)`,
and the trace term is bounded by the Lyapunov functional through `e5b_trace_final`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE5b

open HRS HRS.MC.Cepa HRS.MC.CepE4

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

theorem e5b_quad_of_le {f h : Ch N → ℝ} (hf : E4Quad f) (hc : Continuous h) (hle : ∀ z, |h z| ≤ |f z|) :
    E4Quad h := by
  obtain ⟨_, c0, c1, h0, h1, hb⟩ := hf
  exact ⟨hc, c0, c1, h0, h1, fun z => (hle z).trans (hb z)⟩

theorem e5b_quad_sqnorm {G : Ch N → Ch N} (hGc : Continuous G) {β L : ℝ} (hβ : 0 ≤ β) (hL : 0 ≤ L)
    (hGb : ∀ z, ‖G z‖ ≤ β + L * ‖z‖) : E4Quad fun z => ‖G z‖ ^ 2 := by
  refine ⟨(hGc.norm).pow 2, 2 * β ^ 2, 2 * L ^ 2, by positivity, by positivity, fun z => ?_⟩
  rw [abs_of_nonneg (by positivity)]
  have h1 := hGb z
  have h2 : ‖G z‖ ^ 2 ≤ (β + L * ‖z‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (β - L * ‖z‖)]

theorem e5b_quad_inner {G F : Ch N → Ch N} (hGc : Continuous G) (hFc : Continuous F)
    (hG : E4Quad fun z => ‖G z‖ ^ 2) (hF : E4Quad fun z => ‖F z‖ ^ 2) :
    E4Quad fun z => inner ℝ (G z) (F z) := by
  have hs : E4Quad fun z => (1 / 2) * ‖G z‖ ^ 2 + (1 / 2) * ‖F z‖ ^ 2 :=
    (hG.const_mul (1 / 2)).add (hF.const_mul (1 / 2))
  refine e5b_quad_of_le hs (hGc.inner hFc) fun z => ?_
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 2) * ‖G z‖ ^ 2 + (1 / 2) * ‖F z‖ ^ 2)]
  have := abs_real_inner_le_norm (G z) (F z)
  nlinarith [sq_nonneg (‖G z‖ - ‖F z‖)]

/-- Three-term linearity of the double integral. -/
theorem e5b_lin3 [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {T σ' : ℝ} {w Z : ℝ → Ω → Ch N} {A : Ω → ℝ}
    (S : E4Setup P ℱ N T σ' w Z A) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) {f1 f2 f3 : Ch N → ℝ}
    (h1 : E4Quad f1) (h2 : E4Quad f2) (h3 : E4Quad f3) (c1 c2 c3 : ℝ) :
    ∫ ω, (∫ s in (0 : ℝ)..t, (c1 * f1 (Z s ω) + c2 * f2 (Z s ω) + c3 * f3 (Z s ω))) ∂P =
      c1 * (∫ ω, (∫ s in (0 : ℝ)..t, f1 (Z s ω)) ∂P) + c2 * (∫ ω, (∫ s in (0 : ℝ)..t, f2 (Z s ω)) ∂P) +
        c3 * (∫ ω, (∫ s in (0 : ℝ)..t, f3 (Z s ω)) ∂P) := by
  have h12 : E4Quad fun z => c1 * f1 z + c2 * f2 z := (h1.const_mul c1).add (h2.const_mul c2)
  have e1 := e4Q_lin S ht0 htT h12 h3 1 c3
  have e2 := e4Q_lin S ht0 htT h1 h2 c1 c2
  simp only [one_mul] at e1
  rw [e2] at e1
  exact e1

end HRS.MC.CepE5b
