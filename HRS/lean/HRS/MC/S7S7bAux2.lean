import HRS.MC.S7S7bAux1
import HRS.MC.SEdgeB4b
import HRS.Equilibrium.QuadraticLimit.FeaturesAux

/-!
# Packet `s7_S7b_weighted_moments`, helper 2: the exponential pair estimate under `Q_{N,gamma}`
For every symmetric measurable `h` with `|h| <= g + c` and every `N >= 1`:
`E_Q exp(theta N |F_N^h|) <= M` (`N:eq:pair-exp`, `Nδ_N = 1` for `s < d/2`), constants uniform in `h`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7b

open HRS HRS.Sec7 HRS.MC.SEdge

variable {d : ℕ} {s : ℝ}

theorem s7b_expmom (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 < γ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (c : ℝ)
    (hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + c) :
    ∃ θ M : ℝ, 0 < θ ∧ 0 ≤ M ∧ ∀ h : Torus d → Torus d → ℝ, Measurable (Function.uncurry h) →
      (∀ x y, h x y = h y x) → (∀ x y, |h x y| ≤ periodicRiesz d s (x - y) + c) →
      ∀ N : ℕ, 1 ≤ N →
        ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (θ * N *
          |modulatedEnergy h X (withDensityReal ρ)|)) ∂(sed_Q d s N γ ρ) ≤ ENNReal.ofReal M := by
  have hsd : s < (d : ℝ) := by
    have : (0 : ℝ) ≤ d := by positivity
    linarith
  haveI hμ : IsProbabilityMeasure (withDensityReal ρ) := HRS.MC.SEdge.B3.b3_prob hρ
  obtain ⟨x0, -, hx0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
    (PoleCavityAux.continuous_of_smoothPos hρ).continuousOn
  have hc₀ : 0 < ρ x0 := hρ.pos x0
  have hlow : ∀ x, ρ x0 ≤ ρ x := fun x => isMinOn_iff.1 hx0 x (Set.mem_univ x)
  obtain ⟨θ₀, θ₁, C, hθ₀, hθ₁, H⟩ := perturbed_pressure (by omega) s hs0 hsd c hw γ γ hγ (ρ x0) hc₀
    (fun k => Torus.cbNorm k ρ) 1
  obtain ⟨B, Cc, hB, hK⟩ := PoleCavityAux.kerData_periodicRiesz (by omega) hs0 hsd hρ
  have hCc := hK.Cc_nonneg
  refine ⟨θ₁, max (Real.exp C) (Real.exp (θ₁ * (3 * (Cc + |c|)))), hθ₁, (Real.exp_pos _).le.trans
    (le_max_left _ _), fun h hm hsym hdom N hN => ?_⟩
  haveI hQ : IsProbabilityMeasure (sed_Q d s N γ ρ) :=
    HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hγ.le hρ N hN
  rcases Nat.lt_or_ge N 2 with hN2 | hN2
  · have hN1 : N = 1 := by omega
    subst hN1
    -- deterministic bound for a single particle
    have hgc : ∀ x y, 0 ≤ periodicRiesz d s (x - y) + c := fun x y => (abs_nonneg _).trans (hdom x y)
    have hint : ∀ x, Integrable (fun y => periodicRiesz d s (x - y) + c) (withDensityReal ρ) :=
      fun x => (hK.int x).add (integrable_const _)
    have h1 : ∀ x, |∫ y, h x y ∂(withDensityReal ρ)| ≤ Cc + |c| := fun x => by
      have := norm_integral_le_of_norm_le (hint x) (μ := withDensityReal ρ) (f := fun y => h x y)
        (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hdom x y)
      rw [Real.norm_eq_abs] at this
      refine this.trans ?_
      rw [integral_add (hK.int x) (integrable_const _)]
      have := hK.conv x
      have h2 : |c| ≥ c := le_abs_self c
      have hcc : ∫ _y, c ∂(withDensityReal ρ) = c := by simp
      rw [hcc]
      unfold HRS.convMeasure at this
      rw [abs_le] at this
      linarith [this.2]
    have h2 : |∫ x, ∫ y, h x y ∂(withDensityReal ρ) ∂(withDensityReal ρ)| ≤ Cc + |c| := by
      have := norm_integral_le_of_norm_le_const (μ := withDensityReal ρ)
        (f := fun x => ∫ y, h x y ∂(withDensityReal ρ)) (C := Cc + |c|)
        (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact h1 x)
      simpa using this
    have hE : ∀ X : Config d 1, |modulatedEnergy h X (withDensityReal ρ)| ≤ 3 * (Cc + |c|) := by
      intro X
      unfold modulatedEnergy
      have h0 : Finset.univ.erase (0 : Fin 1) = ∅ := by
        ext j; simp [Subsingleton.elim j 0]
      have hsum : ∀ i : Fin 1, Finset.univ.erase i = ∅ := fun i => by
        rw [Subsingleton.elim i 0]; exact h0
      simp only [hsum, Finset.sum_empty, mul_zero, zero_sub, Nat.cast_one, div_one, one_div, inv_one,
        one_mul, Finset.univ_unique, Finset.sum_singleton, Finset.erase_singleton]
      have a1 := h1 (X default)
      rw [abs_le] at a1 h2 ⊢
      constructor <;> linarith [a1.1, a1.2, h2.1, h2.2]
    calc ∫⁻ X : Config d 1, ENNReal.ofReal (Real.exp (θ₁ * ((1 : ℕ) : ℝ) *
          |modulatedEnergy h X (withDensityReal ρ)|)) ∂(sed_Q d s 1 γ ρ)
        ≤ ∫⁻ _X : Config d 1, ENNReal.ofReal (Real.exp (θ₁ * (3 * (Cc + |c|)))) ∂(sed_Q d s 1 γ ρ) := by
          refine lintegral_mono fun X => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
          have := hE X
          simp only [Nat.cast_one, mul_one]
          exact mul_le_mul_of_nonneg_left this hθ₁.le
      _ = ENNReal.ofReal (Real.exp (θ₁ * (3 * (Cc + |c|)))) := by simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal (le_max_right _ _)
  · have hρΛ := H ρ hρ.density hρ.smooth hlow (fun k => le_rfl) h hm hsym
      (fun x y => by simpa using hdom x y) N hN2 γ ⟨le_rfl, le_rfl⟩
    have := hρΛ.2.1
    have hdel : (N : ℝ) * deltaN d s N = 1 := by
      have hN0 : (N : ℝ) ≠ 0 := by
        have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
        exact this.ne'
      unfold deltaN
      rw [if_pos hs]
      field_simp
    refine this.trans (ENNReal.ofReal_le_ofReal ((Real.exp_le_exp.2 ?_).trans (le_max_left _ _)))
    have : C * N * deltaN d s N = C * ((N : ℝ) * deltaN d s N) := by ring
    rw [this, hdel, mul_one]

end HRS.MC.Sec7.S7b

end
