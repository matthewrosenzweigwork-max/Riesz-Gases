import HRS.Sections.Sec7Static
import HRS.Sections.Q66AuxN
import HRS.Sections.Q66GaussB
import HRS.Equilibrium.QuadraticLimit.Assembly
import HRS.Prob.Gaussian

/-!
# Vocabulary for the Proposition 7.4 chain (sorry-free; split from `SEdgeSpec.lean`)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge

open HRS.Sec7

/-- The modulated Gibbs law `Q_{N,beta}(rho dx)` for the periodic Riesz kernel. -/
abbrev sed_Q (d : ℕ) (s : ℝ) (N : ℕ) (β : ℝ) (ρ : Torus d → ℝ) : Measure (Config d N) :=
  modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)

/-- The exactly centred linear statistic `sqrt N (mu_N(w) - E_Q mu_N(w))`. By definition
`centeredStat Q phi X = (sed_Y Q (phi a) X)_a`. -/
def sed_Y {d N : ℕ} (Q : Measure (Config d N)) (w : Torus d → ℝ) (X : Config d N) : ℝ :=
  Real.sqrt N * (pair (empirical X) w - ∫ Y, pair (empirical Y) w ∂Q)

/-- The drift observable `v . grad phi = sum_k v_k d_k phi` (TeX `N:eq:Stein-terms`). -/
def sed_drift {d : ℕ} (v : Fin d → Torus d → ℝ) (φ : Torus d → ℝ) (x : Torus d) : ℝ :=
  ∑ k, v k x * Torus.partialDeriv k φ x

/-- `A_{N,ab} = mu_N(v_a . grad phi_b)` (TeX `N:eq:Stein-terms`), for a field `v` and a test `phi`. -/
def sed_A {d N : ℕ} (v : Fin d → Torus d → ℝ) (φ : Torus d → ℝ) (X : Config d N) : ℝ :=
  pair (empirical X) (sed_drift v φ)

/-- `B_N = N (F_N^{h_v} - E_Q F_N^{h_v})` (TeX `N:eq:Stein-terms`; `h_v = Q66.q66_hv`, the pair kernel
`(v(x)-v(y)) . grad g(x-y)`). -/
def sed_B (d : ℕ) (s : ℝ) (ρ : Torus d → ℝ) (β : ℝ) {N : ℕ} (v : Fin d → Torus d → ℝ)
    (X : Config d N) : ℝ :=
  (N : ℝ) * (modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ) -
    ∫ Y, modulatedEnergy (Q66.q66_hv d s v) Y (withDensityReal ρ) ∂(sed_Q d s N β ρ))

/-- The tensor `Q_{v;fg} = iint h_v(x,y) f(x) g(y) dmu dmu` (TeX `N:eq:Qabc`). -/
def sed_Qt (d : ℕ) (s : ℝ) (ρ : Torus d → ℝ) (v : Fin d → Torus d → ℝ) (f g : Torus d → ℝ) : ℝ :=
  ∫ x, ∫ y, Q66.q66_hv d s v x y * f x * g y ∂(withDensityReal ρ) ∂(withDensityReal ρ)

/-- The covariance matrix `C_ab = mu(phi_a r_b)` of `static_edge` (verbatim from `Sec7Static`). -/
def sed_Cmat (d : ℕ) (s : ℝ) (β : ℝ) (ρ : Torus d → ℝ) {p : ℕ} (φ : Fin p → Torus d → ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun a b => ∫ x, φ a x *
    responseInverse (periodicRiesz d s) (withDensityReal ρ) β (φ b) x ∂(withDensityReal ρ)

/-- The tensor `kappa_abc = mu(r_a r_b r_c)` of `static_edge` (verbatim from `Sec7Static`). -/
def sed_kappa (d : ℕ) (s : ℝ) (β : ℝ) (ρ : Torus d → ℝ) {p : ℕ} (φ : Fin p → Torus d → ℝ)
    (a b c : Fin p) : ℝ :=
  ∫ x, responseInverse (periodicRiesz d s) (withDensityReal ρ) β (φ a) x *
    responseInverse (periodicRiesz d s) (withDensityReal ρ) β (φ b) x *
    responseInverse (periodicRiesz d s) (withDensityReal ρ) β (φ c) x ∂(withDensityReal ρ)

/-- `f` is `C^n` with bounded derivatives of orders `1..n` (the Stein solution `f` itself need not be
bounded); the form in which `stein_bounds` delivers it. -/
def sed_StBdd {p : ℕ} (f : EuclideanSpace ℝ (Fin p) → ℝ) (n : ℕ) : Prop :=
  ContDiff ℝ n f ∧ ∀ j : ℕ, 1 ≤ j → j ≤ n → ∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ M

/-- The Gaussian-chaos data produced by `quadratic_limit` (Lemma 7.5): its three `L^2` conjuncts plus
measurability (which the proof of `quadratic_limit_proof` has but does not export). -/
def sed_QLData (d : ℕ) (s : ℝ) (β : ℝ) (ρ : Torus d → ℝ) (h : Torus d → Torus d → ℝ)
    (e : ℕ → Torus d → ℝ) {p : ℕ} (φ : Fin p → Torus d → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (G : ℕ → Ω → ℝ) (Qv : Ω → ℝ) (Lin : Fin p → Ω → ℝ) : Prop :=
  (∀ i, Measurable (G i)) ∧ Measurable Qv ∧ (∀ a, Measurable (Lin a)) ∧
  (∀ n : ℕ, law P (fun ω => (WithLp.toLp 2 fun i : Fin n => G i ω : EuclideanSpace ℝ (Fin n))) =
    multivariateGaussian 0 (Matrix.of fun i j : Fin n =>
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j))) ∧
  (∀ a, Tendsto (fun L => ∫⁻ ω, ‖Lin a ω - ∑ i ∈ Finset.range L,
      l2Inner (withDensityReal ρ) (φ a) (e i) * G i ω‖ₑ ^ 2 ∂P) atTop (𝓝 0)) ∧
  Tendsto (fun L => ∫⁻ ω, ‖Qv ω - (1 / 2) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
      (∫ x, ∫ y, h x y * e i x * e j y ∂(withDensityReal ρ) ∂(withDensityReal ρ)) *
        (G i ω * G j ω -
          susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j))‖ₑ ^ 2 ∂P)
    atTop (𝓝 0)

/-- The test family of Part U: `cos(t x_0)` (`σ = true`) or `sin(t x_0)` (`σ = false`) on `R^1`. -/
def sed_Ucf (σ : Bool) (t : ℝ) (z : EuclideanSpace ℝ (Fin 1)) : ℝ :=
  if σ then Real.cos (t * z 0) else Real.sin (t * z 0)

/-- The scaled remainder of `static_edge` for `p = 1`, the test `phi` and `F = sed_Ucf σ t`:
`e_N(t) = sqrt N (E F_t(W_N) - E F_t(Z) - (1/(6 sqrt N)) kappa E D^3 F_t(Z))`. -/
def sed_Uerr (d : ℕ) (s : ℝ) (β : ℝ) (ρ : Torus d → ℝ) (φ : Torus d → ℝ) (σ : Bool) (N : ℕ)
    (t : ℝ) : ℝ :=
  Real.sqrt N * (
    ∫ X, sed_Ucf σ t (centeredStat (sed_Q d s N β ρ) (fun _ : Fin 1 => φ) X) ∂(sed_Q d s N β ρ) -
    ∫ z, sed_Ucf σ t z ∂(multivariateGaussian 0 (sed_Cmat d s β ρ (fun _ : Fin 1 => φ))) -
    (1 / (6 * Real.sqrt N)) * sed_kappa d s β ρ (fun _ : Fin 1 => φ) 0 0 0 *
      ∫ z, iteratedFDeriv ℝ 3 (sed_Ucf σ t) z ![stdVec 0, stdVec 0, stdVec 0]
        ∂(multivariateGaussian 0 (sed_Cmat d s β ρ (fun _ : Fin 1 => φ))))


end HRS.MC.SEdge

end
