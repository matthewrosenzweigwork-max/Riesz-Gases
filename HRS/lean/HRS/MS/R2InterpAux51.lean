import HRS.MS.R2InterpAux50

/-!
# S10.2 (worker S102), part 51 (packet F6, vocabulary): the truncated orbit test, the cylindrical densities `cylA`, `cylJ`, and the bracket identity for the grid
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MC.Sec7.PI

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ}

/-- The test function of the `i`-th observation, truncated after its terminal time: `U^{r,τ_i}φ_{α_i}` for `r ≤ τ_i`, `0` after. -/
def s102_ot (C : WholeCoeff d) (m : ℝ) {q : ℕ} {T : ℝ} (τ : Fin q → Icc (0 : ℝ) T) (α : Fin q → MultiIndex d)
    (i : Fin q) (r : ℝ) : Euc d → ℝ :=
  if r ≤ (τ i : ℝ) then propagatorW C r (τ i) (oscTestFun m (α i)) else 0

/-- The drift density `∑_i ∂_iF(r, obs Y_r) ℬ_N^r(obsTest_i r)` of the cylindrical Itô identity. -/
def s102_cylA (C : WholeCoeff d) (m T s : ℝ) (μ : Measure (Euc d)) {N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig d N) {q : ℕ} (τ : Fin q → Icc (0 : ℝ) T)
    (α : Fin q → MultiIndex d) (G : EuclideanSpace ℝ (Fin q) → ℝ) (ζ : Ω) (r : ℝ) : ℝ :=
  ∑ i, fderiv ℝ (gaussHeat (s102_obsCov C m τ α) G r) (s102_obs τ α (s102_Y C m T P X ζ r))
      (EuclideanSpace.single i 1) * s102_hh C m τ α (fun u => r2QuadField s μ P X u ζ) i r

/-- The covariance density `∑_{ij} ∂_{ij}F(r, obs Y_r) 2ν η_N^r(∇obsTest_i·∇obsTest_j)`. -/
def s102_cylJ (C : WholeCoeff d) (m T : ℝ) (μ : Measure (Euc d)) {N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig d N) {q : ℕ} (τ : Fin q → Icc (0 : ℝ) T)
    (α : Fin q → MultiIndex d) (G : EuclideanSpace ℝ (Fin q) → ℝ) (ζ : Ω) (r : ℝ) : ℝ :=
  ∑ i, ∑ j, iteratedFDeriv ℝ 2 (gaussHeat (s102_obsCov C m τ α) G r) (s102_obs τ α (s102_Y C m T P X ζ r))
    ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] * (2 * C.ν * s102_hh2 C m τ α (s102_etaf μ X ζ) i j r)

theorem s102_gradient_zero : gradient (0 : Euc d → ℝ) = fun _ => 0 := by
  funext x; simp [gradient]

/-- `2ν μ(∇obsTest_i·∇obsTest_j) = rate_{ij}` for the grid. -/
theorem s102_pair_ot (hT : 0 < T) (L : ℕ) (μ : Measure (Euc d)) {s : ℝ}
    (hμ : ∀ f : Euc d → ℝ, HRS.Whole.pair μ f = ∫ x, f x * C.ρ s x) (i j : Fin (s102_q d L)) :
    2 * C.ν * HRS.Whole.pair μ (fun y => inner ℝ (gradient (s102_ot C m (s102_tauk hT L) (s102_alk L) i s) y)
      (gradient (s102_ot C m (s102_tauk hT L) (s102_alk L) j s) y)) = s102_rateM C m hT L s i j := by
  unfold s102_rateM s102_gram
  simp only [Matrix.of_apply]
  by_cases h : s ≤ min (s102_tk hT L i) (s102_tk hT L j)
  · have h1 : s ≤ s102_tk hT L i := h.trans (min_le_left _ _)
    have h2 : s ≤ s102_tk hT L j := h.trans (min_le_right _ _)
    rw [if_pos h, hμ]
    simp only [s102_ot, s102_tk] at h1 h2 ⊢
    rw [if_pos h1, if_pos h2]
  · rw [if_neg h, mul_zero]
    have : (fun y => inner ℝ (gradient (s102_ot C m (s102_tauk hT L) (s102_alk L) i s) y)
        (gradient (s102_ot C m (s102_tauk hT L) (s102_alk L) j s) y)) = fun _ => 0 := by
      funext y
      by_cases h1 : s ≤ s102_tk hT L i
      · have h2 : ¬ s ≤ s102_tk hT L j := fun h2 => h (le_min h1 h2)
        simp only [s102_ot, s102_tk] at h2
        rw [s102_ot, s102_ot, if_neg h2, s102_gradient_zero]
        simp
      · simp only [s102_ot, s102_tk] at h1
        rw [s102_ot, if_neg h1, s102_gradient_zero]
        simp
    rw [this, hμ]
    simp

/-- The `η`-side of the bracket identity. -/
theorem s102_eta_ot {N : ℕ} {Ω : Type} (hT : 0 < T) (L : ℕ) (μ : Measure (Euc d)) (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω)
    (s : ℝ) (i j : Fin (s102_q d L)) :
    s102_etaf μ X ζ s (fun y => inner ℝ (gradient (s102_ot C m (s102_tauk hT L) (s102_alk L) i s) y)
      (gradient (s102_ot C m (s102_tauk hT L) (s102_alk L) j s) y)) =
    s102_hh2 C m (s102_tauk hT L) (s102_alk L) (s102_etaf μ X ζ) i j s := by
  unfold s102_hh2
  by_cases h : s ≤ min ((s102_tauk hT L i : Icc (0 : ℝ) T) : ℝ) ((s102_tauk hT L j : Icc (0 : ℝ) T) : ℝ)
  · rw [indicator_of_mem (show s ∈ Iic _ from h)]
    have h1 := h.trans (min_le_left _ _)
    have h2 := h.trans (min_le_right _ _)
    simp only [s102_ot]
    rw [if_pos h1, if_pos h2]
  · rw [indicator_of_notMem (show s ∉ Iic _ from h)]
    have : (fun y => inner ℝ (gradient (s102_ot C m (s102_tauk hT L) (s102_alk L) i s) y)
        (gradient (s102_ot C m (s102_tauk hT L) (s102_alk L) j s) y)) = fun _ => 0 := by
      funext y
      by_cases h1 : s ≤ ((s102_tauk hT L i : Icc (0 : ℝ) T) : ℝ)
      · have h2 : ¬ s ≤ ((s102_tauk hT L j : Icc (0 : ℝ) T) : ℝ) := fun h2 => h (le_min h1 h2)
        rw [s102_ot, s102_ot, if_neg h2, s102_gradient_zero]
        simp
      · rw [s102_ot, if_neg h1, s102_gradient_zero]
        simp
    rw [this]
    simp [s102_etaf, HRS.Whole.pair]

end HRS.MS.R2Interp

end
