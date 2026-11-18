import HRS.MS.S113X2B1
import HRS.MS.S113X2B3

/-!
# S11.3 X2 part B (worker S11Z3), hypotheses and quantities of the abstract power-chain inequality

`s113b_Data` bundles the hypotheses on a nonnegative bounded density `u` (the killed density of part A, extended by zero)
supported in a compact `K` inside the open set `G` where the drift is smooth: the EVERY-TIME slice subsolution
inequality `sub` (from the stopped Itô formula with time-independent tests) for the operator
`φ ↦ ν Δφ + Dφ[b]`.  `q` is the moving reference (positive, `C²` in space-time), `s113b_R` its source.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Set Filter Topology intervalIntegral

namespace HRS.MS.S113X2B

/-- The source `R = (ν Δq - div(b q) - ∂_t q) / q`. -/
def s113b_R {n : ℕ} (ν : ℝ) (b : s113b_E n → s113b_E n) (q : ℝ → s113b_E n → ℝ) (τ : ℝ) (x : s113b_E n) : ℝ :=
  (ν * s113b_lap (q τ) x - s113b_div (fun y => q τ y • b y) x - deriv (fun σ => q σ x) τ) / q τ x

/-- Hypotheses of the abstract chain inequality. -/
structure s113b_Data {n : ℕ} (ν : ℝ) (b : s113b_E n → s113b_E n) (q : ℝ → s113b_E n → ℝ) (T : ℝ)
    (u : ℝ → s113b_E n → ℝ) (K G : Set (s113b_E n)) (B : ℝ) : Prop where
  hν : 0 < ν
  hb : ContDiff ℝ 2 b
  hq : ContDiff ℝ 2 (fun z : ℝ × s113b_E n => q z.1 z.2)
  hq0 : ∀ t, t ∈ Icc 0 T → ∀ x, 0 < q t x
  hKc : IsCompact K
  hG : IsOpen G
  hKG : K ⊆ G
  hKu : ∀ t x, x ∉ K → u t x = 0
  hu0 : ∀ t x, 0 ≤ u t x
  huB : ∀ t, t ∈ Icc 0 T → ∀ x, u t x ≤ B
  hum : Measurable (fun z : ℝ × s113b_E n => u z.1 z.2)
  sub : ∀ φ : s113b_E n → ℝ, s113b_Cinf φ → HasCompactSupport φ → (∀ x, 0 ≤ φ x) → tsupport φ ⊆ G →
    ∀ s t, 0 ≤ s → s ≤ t → t ≤ T →
      ∫ x, φ x * u t x ≤ (∫ x, φ x * u s x) +
        ∫ τ in s..t, ∫ x, (ν * s113b_lap φ x + fderiv ℝ φ x (b x)) * u τ x

/-- The power mass `M(t) = ∫ q_t (u_t/q_t)^{p(t)} dx`. -/
def s113b_M {n : ℕ} (q : ℝ → s113b_E n → ℝ) (u : ℝ → s113b_E n → ℝ) (p : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x, q t x * (u t x / q t x) ^ (p t)

/-- The right-hand side density `(p-1) ∫ q R r^p + p' ∫ q r^p log r`. -/
def s113b_Gp {n : ℕ} (ν : ℝ) (b : s113b_E n → s113b_E n) (q : ℝ → s113b_E n → ℝ) (u : ℝ → s113b_E n → ℝ)
    (p : ℝ → ℝ) (τ : ℝ) : ℝ :=
  (p τ - 1) * (∫ x, q τ x * s113b_R ν b q τ x * (u τ x / q τ x) ^ (p τ)) +
    deriv p τ * ∫ x, q τ x * (u τ x / q τ x) ^ (p τ) * Real.log (u τ x / q τ x)

/-- The regularized integrand `F_ε(t,x,w) = q Φ_{p(t),ε}(w/q)`. -/
def s113b_F {n : ℕ} (q : ℝ → s113b_E n → ℝ) (p : ℝ → ℝ) (ε : ℝ) (t : ℝ) (x : s113b_E n) (w : ℝ) : ℝ :=
  q t x * s113b_Phi (p t) ε (w / q t x)

/-- The regularized right-hand side at a ratio profile `r`:
`∫ [q R Θ_ε(r) + p' q ∂_pΦ_ε(r)]`. -/
def s113b_rhsE {n : ℕ} (ν : ℝ) (b : s113b_E n → s113b_E n) (q : ℝ → s113b_E n → ℝ) (p : ℝ → ℝ) (ε : ℝ)
    (τ : ℝ) (r : s113b_E n → ℝ) : ℝ :=
  ∫ x, (q τ x * s113b_R ν b q τ x * s113b_Theta (p τ) ε (r x) +
    deriv p τ * q τ x * s113b_PhiP (p τ) ε (r x))

end HRS.MS.S113X2B
