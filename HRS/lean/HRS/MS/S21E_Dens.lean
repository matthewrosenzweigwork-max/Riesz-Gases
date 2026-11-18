import HRS.MS.S111X1Aux9

/-!
# S2.1(iii) packet G1: the cross-density family for a MOVING reference

`s111_cross_densities_of_functionals` (S11.1) is the constant-reference version.  Here `rho : ℝ → Euc d → ℝ` is the resulting solution,
the initial covariance is `HRS.Whole.susceptibilityCov .. (HRS.Whole.withDensityReal (rho 0)) β₀`, and the densities `χ_i^r` are `L²(μ_r)`-relative densities,
exactly the existence clause of the frozen `whole_space_edgeworth`.  The analytic input is `S21eCovCore` (the covariance functional is
`L²(μ_r)`-bounded on oscillator tests, for every `r ≥ 0`, uniformly in nothing: the bound may depend on `(r, t, φ)`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S21E

open HRS HRS.Whole

variable {d : ℕ}

/-- The covariance functional of the frozen clause. -/
def s21eCov (d : ℕ) (s a β β₀ : ℝ) (ρ : ℝ → Euc d → ℝ) (r t : ℝ) (ψ φ : Euc d → ℝ) : ℝ :=
  linearGaussianCov ((quadraticGradientDyn d s a β).coeff ρ) β⁻¹
    (HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal (ρ 0)) β₀) r t ψ φ

/-- The open analytic core: for every `r ≥ 0`, `ρ_r` is a measurable positive density with `L²(μ_r)` oscillator tests, and for every `t ≥ 0` and
oscillator test `φ` the covariance functional `ψ ↦ Cov(Z^r ψ, Z^t φ)` is linear and bounded by `B ‖ψ‖_{L²(μ_r)}` on oscillator tests. -/
def S21eCovCore (d : ℕ) (s a β β₀ : ℝ) (ρ : ℝ → Euc d → ℝ) : Prop :=
  ∀ r : ℝ, 0 ≤ r → Measurable (ρ r) ∧ (∀ x, 0 < ρ r x) ∧
    (∀ ψ : Euc d → ℝ, IsOscTest (wholeSpaceIndex d : ℝ) ψ → MemLp ψ 2 (HRS.Whole.withDensityReal (ρ r))) ∧
    ∀ t : ℝ, 0 ≤ t → ∀ φ : Euc d → ℝ, IsOscTest (wholeSpaceIndex d : ℝ) φ →
      (∀ ψ₁ ψ₂ : Euc d → ℝ, IsOscTest (wholeSpaceIndex d : ℝ) ψ₁ → IsOscTest (wholeSpaceIndex d : ℝ) ψ₂ → ∀ c : ℝ,
        s21eCov d s a β β₀ ρ r t (fun x => ψ₁ x + c * ψ₂ x) φ =
          s21eCov d s a β β₀ ρ r t ψ₁ φ + c * s21eCov d s a β β₀ ρ r t ψ₂ φ) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ ψ : Euc d → ℝ, IsOscTest (wholeSpaceIndex d : ℝ) ψ →
        |s21eCov d s a β β₀ ρ r t ψ φ| ≤ B * Real.sqrt (∫ x, ψ x ^ 2 ∂(HRS.Whole.withDensityReal (ρ r)))

/-- The existence clause of the frozen conclusion for a window start `a₀`. -/
def S21eCrossExist (d : ℕ) (s a β β₀ : ℝ) (ρ : ℝ → Euc d → ℝ) (T a₀ : ℝ) : Prop :=
  ∀ (τ : Fin 3 → Set.Icc (0 : ℝ) T) (φ : Fin 3 → Euc d → ℝ), (∀ i, IsOscTest (wholeSpaceIndex d : ℝ) (φ i)) →
    ∃ χ : Fin 3 → ℝ → Euc d → ℝ,
      ∀ i, ∀ r ∈ Set.Icc (0 : ℝ) (a₀ + T),
        MemLp (fun x => χ i r x / ρ r x) 2 (HRS.Whole.withDensityReal (ρ r)) ∧
        ∀ ψ', IsOscTest (wholeSpaceIndex d : ℝ) ψ' →
          Integrable (fun x => ψ' x * χ i r x) ∧
          ∫ x, ψ' x * χ i r x = s21eCov d s a β β₀ ρ r (a₀ + τ i) ψ' (φ i)

/-- One density: Riesz representation of the covariance functional in `L²(μ_r)`. -/
theorem s21e_density_one {s a β β₀ : ℝ} {ρ : ℝ → Euc d → ℝ} (hcore : S21eCovCore d s a β β₀ ρ)
    {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) {φ : Euc d → ℝ} (hφ : IsOscTest (wholeSpaceIndex d : ℝ) φ) :
    ∃ χ : Euc d → ℝ, MemLp (fun x => χ x / ρ r x) 2 (HRS.Whole.withDensityReal (ρ r)) ∧
      ∀ ψ', IsOscTest (wholeSpaceIndex d : ℝ) ψ' →
        Integrable (fun x => ψ' x * χ x) ∧ ∫ x, ψ' x * χ x = s21eCov d s a β β₀ ρ r t ψ' φ := by
  obtain ⟨hm, hpos, hS, hrest⟩ := hcore r hr
  obtain ⟨hlin, B, hB0, hB⟩ := hrest t ht φ hφ
  set m : ℝ := (wholeSpaceIndex d : ℝ) with hmdef
  let ℓ : HRS.MS.S111X1.oscSub d m →ₗ[ℝ] ℝ :=
    { toFun := fun ψ => s21eCov d s a β β₀ ρ r t (ψ : Euc d → ℝ) φ
      map_add' := fun ψ₁ ψ₂ => by
        have := hlin ψ₁ ψ₂ ψ₁.2 ψ₂.2 1
        simp only [one_mul] at this
        exact this
      map_smul' := fun c ψ => by
        have h0 : IsOscTest m (0 : Euc d → ℝ) := (HRS.MS.S111X1.oscSub d m).zero_mem
        have h1 := hlin 0 ψ h0 ψ.2 c
        have h2 := hlin 0 0 h0 h0 1
        have h3 : s21eCov d s a β β₀ ρ r t (0 : Euc d → ℝ) φ = 0 := by
          have e : (fun x => (0 : Euc d → ℝ) x + 1 * (0 : Euc d → ℝ) x) = (0 : Euc d → ℝ) := by
            funext x; simp
          rw [e] at h2
          linarith
        have e : (c • (ψ : Euc d → ℝ)) = (fun x => (0 : Euc d → ℝ) x + c * (ψ : Euc d → ℝ) x) := by
          funext x; simp
        show s21eCov d s a β β₀ ρ r t (c • (ψ : Euc d → ℝ)) φ = c * s21eCov d s a β β₀ ρ r t (ψ : Euc d → ℝ) φ
        rw [e, h1, h3, zero_add] }
  have hS' : ∀ ψ ∈ HRS.MS.S111X1.oscSub d m, MemLp ψ 2 (HRS.Whole.withDensityReal (ρ r)) := fun ψ hψ => hS ψ hψ
  obtain ⟨χ, hχ1, hχ2⟩ := HRS.MS.TensRel.s111_density_of_l2_bound hm hpos (HRS.MS.S111X1.oscSub d m) hS' ℓ B (by
    intro ψ
    have e : ‖HRS.MS.TensRel.s111_toLp (HRS.MS.S111X1.oscSub d m) hS' ψ‖ =
        Real.sqrt (∫ x, (ψ : Euc d → ℝ) x ^ 2 ∂(HRS.Whole.withDensityReal (ρ r))) :=
      HRS.MS.S111X1.x1_toLp_norm (hS' ψ ψ.2)
    rw [e]
    exact hB ψ ψ.2)
  refine ⟨χ, hχ1, fun ψ' hψ' => ?_⟩
  exact hχ2 ⟨ψ', hψ'⟩

/-- **G1.**  The existence clause of `whole_space_edgeworth` for a moving reference, from the covariance core. -/
theorem s21e_cross_exist_of_core {s a β β₀ : ℝ} {ρ : ℝ → Euc d → ℝ} (hcore : S21eCovCore d s a β β₀ ρ)
    (T a₀ : ℝ) (ha₀ : 0 ≤ a₀) : S21eCrossExist d s a β β₀ ρ T a₀ := by
  classical
  intro τ φ hφ
  have key : ∀ (i : Fin 3) (r : ℝ), ∃ χ : Euc d → ℝ, r ∈ Set.Icc (0 : ℝ) (a₀ + T) →
      MemLp (fun x => χ x / ρ r x) 2 (HRS.Whole.withDensityReal (ρ r)) ∧
      ∀ ψ', IsOscTest (wholeSpaceIndex d : ℝ) ψ' →
        Integrable (fun x => ψ' x * χ x) ∧ ∫ x, ψ' x * χ x = s21eCov d s a β β₀ ρ r (a₀ + τ i) ψ' (φ i) := by
    intro i r
    by_cases hr : r ∈ Set.Icc (0 : ℝ) (a₀ + T)
    · obtain ⟨χ, h1, h2⟩ := s21e_density_one hcore (r := r) (t := a₀ + (τ i : ℝ)) hr.1
        (by linarith [(τ i).2.1]) (hφ i)
      exact ⟨χ, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hr⟩
  choose χ hχ using key
  exact ⟨fun i r => χ i r, fun i r hr => hχ i r hr⟩

end HRS.MS.S21E
