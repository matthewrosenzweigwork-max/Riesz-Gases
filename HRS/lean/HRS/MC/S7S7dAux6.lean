import HRS.MC.S7S7dAux3
import HRS.MC.S7S7dAux5
import HRS.MC.SEdgeB13b

/-!
# Packet `s7_S7d_uniform_limits`, helper 6: finite-dimensional core of (R2), uniform over the Stein class

For `κ : Fin p → modes`, a smooth `w`, `η > 0` there is `N₀` such that for all `N ≥ N₀`, all `f` in the class
`s7d_Cl` and all `u, u'` in the unit ball of `E_r`:
`| E[Y_w D²f(ι cs_N)[u,u']] - Σ_c t_c ∫ D³f(ι z)[u,u',ι e_c] dN(0,C)(z) | ≤ η`.

Route: joint weak convergence of `cs(w, φ_κ)` (`sed_B10b_clt_proof`), `W_2`-coupling transfer
(`s7d_uniform_weak`, with the uniform fourth moments of `s7d_fourth_moment`), pointwise identification of the limit
by `sed_B13b_linear_limit_proof` and uniqueness of limits.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7d

open HRS HRS.Sec7 HRS.MC.SEdge

variable {d : ℕ}

/-- Restriction `R^{p+1} → R^p` forgetting the zeroth coordinate. -/
def s7d_tail (p : ℕ) : EuclideanSpace ℝ (Fin (p + 1)) →L[ℝ] EuclideanSpace ℝ (Fin p) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun a => x a.succ)
      map_add' := fun x y => by ext a; simp
      map_smul' := fun c x => by ext a; simp }

theorem s7d_tail_apply {p : ℕ} (x : EuclideanSpace ℝ (Fin (p + 1))) (a : Fin p) :
    s7d_tail p x a = x a.succ := rfl

theorem s7d_cons_smooth {p : ℕ} {w : Torus d → ℝ} {φ : Fin p → Torus d → ℝ} (hw : Torus.IsSmooth w)
    (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    ∀ a, Torus.IsSmooth ((Fin.cons w φ : Fin (p + 1) → Torus d → ℝ) a) := by
  intro a
  refine Fin.cases ?_ (fun b => ?_) a
  · simpa using hw
  · simpa using hφ b

theorem s7d_cs_cons {p N : ℕ} (Q : Measure (Config d N)) (w : Torus d → ℝ) (φ : Fin p → Torus d → ℝ)
    (X : Config d N) :
    s7d_tail p (centeredStat Q (Fin.cons w φ : Fin (p + 1) → Torus d → ℝ) X) = centeredStat Q φ X := by
  ext a
  simp [s7d_tail_apply, centeredStat]

theorem s7d_cs_cons_zero {p N : ℕ} (Q : Measure (Config d N)) (w : Torus d → ℝ) (φ : Fin p → Torus d → ℝ)
    (X : Config d N) :
    (EuclideanSpace.proj (0 : Fin (p + 1)) : EuclideanSpace ℝ (Fin (p + 1)) →L[ℝ] ℝ)
      (centeredStat Q (Fin.cons w φ : Fin (p + 1) → Torus d → ℝ) X) = sed_Y Q w X := by
  simp [centeredStat, sed_Y]

section Ident

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]

/-- Uniform convergence over the bounded Lipschitz class towards any limit already known pointwise. -/
theorem s7d_uniform_ident (μ : ℕ → Measure B) [∀ N, IsProbabilityMeasure (μ N)]
    (ν : Measure B) [IsProbabilityMeasure ν]
    (hweak : ∀ F : B → ℝ, Continuous F → (∃ M, ∀ x, |F x| ≤ M) →
      Tendsto (fun N => ∫ x, F x ∂(μ N)) atTop (𝓝 (∫ x, F x ∂ν)))
    {C4 : ℝ} (hmom : ∀ N, Integrable (fun x : B => ‖x‖ ^ ((2 : ℝ) + 2)) (μ N) ∧
      ∫ x, ‖x‖ ^ ((2 : ℝ) + 2) ∂(μ N) ≤ C4)
    (h : B →L[ℝ] ℝ) {M : ℝ} (hM : 0 ≤ M) (L : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ Ψ : B → ℝ, (∀ x, |Ψ x| ≤ M) → LipschitzWith L Ψ → ∀ lim : ℝ,
      Tendsto (fun n => ∫ x, h x * Ψ x ∂(μ n)) atTop (𝓝 lim) →
      |∫ x, h x * Ψ x ∂(μ N) - lim| ≤ ε := by
  obtain ⟨N₀, hN₀⟩ := s7d_uniform_weak μ ν hweak hmom h hM L hε
  refine ⟨N₀, fun N hN Ψ hb hl lim hlim => ?_⟩
  have hν : Tendsto (fun n => ∫ x, h x * Ψ x ∂(μ n)) atTop (𝓝 (∫ x, h x * Ψ x ∂ν)) := by
    rw [Metric.tendsto_atTop]
    intro e he
    obtain ⟨N₁, h1⟩ := s7d_uniform_weak μ ν hweak hmom h hM L (half_pos he)
    refine ⟨N₁, fun n hn => ?_⟩
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (h1 n hn Ψ hb hl) (half_lt_self he)
  have := tendsto_nhds_unique hlim hν
  rw [this]
  exact hN₀ N hN Ψ hb hl

end Ident

end HRS.MC.Sec7.S7d

end
