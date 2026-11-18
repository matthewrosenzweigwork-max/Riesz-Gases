import HRS.MC.SEdgeVocab
import HRS.Sections.Sec7Fields
import HRS.Sections.Sec7Static
import HRS.Equilibrium.StaticLimits
import HRS.Equilibrium.PairCorrection

/-!
# Vocabulary for the Section 7 plan (`HRS/MC/Sec7Plan.md`; sorry-free)

Definitions used by `HRS/MC/Sec7Spec.lean` (packets for Lemma 7.6 `field_chaos`, Proposition 7.7
`static_field`, Proposition 7.11 `path_Ito`, Proposition 7.16 `slow_correction`, Proposition 7.18).
Namespace `HRS.MC.Sec7`, prefix `s7_`.  Nothing here redefines an existing object.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7

open HRS HRS.Sec7 HRS.MC.SEdge

/-! ### Proposition 7.18: Gaussian quadratic chaos with the susceptibility covariance -/

/-- The Gaussian data `(G_i)` of Lemma 7.5 / Proposition 7.18: `G = (G_i)` is jointly Gaussian along the
orthonormal basis `e` of `L^2_0(mu)`, with covariance `C_{beta,mu}(e_i,e_j)` (`susceptibilityCov`).  This is the
first conjunct of the Gaussian data of `quadratic_limit` (and of `sed_QLData`). -/
def s7_GaussData (d : ℕ) (s β : ℝ) (ρ : Torus d → ℝ) (e : ℕ → Torus d → ℝ) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) (G : ℕ → Ω → ℝ) : Prop :=
  (∀ i, Measurable (G i)) ∧ ∀ n : ℕ,
    law P (fun ω => (WithLp.toLp 2 fun i : Fin n => G i ω : EuclideanSpace ℝ (Fin n))) =
      multivariateGaussian 0 (Matrix.of fun i j : Fin n =>
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j))

/-- `Q = (1/2) I_2^{C_{beta,mu}}(h)`: `Q` is the `L^2(P)`-limit of the finite sections
`(1/2) sum_{i,j<L} H_ij (G_i G_j - C_ij)`, `H_ij = iint h e_i e_j dmu dmu` (the form of `E:eq:Qepsilon` with
`A = C^{1/2} H C^{1/2}` and the correlated coordinates `C^{1/2} g`; the integral kernel `h` is only used through
its coefficients in the basis of `L^2_0(mu)`, so `h` and its canonical centring `(P_mu x P_mu)h` give the same
`Q`).  Same expression as in `quadratic_limit`. -/
def s7_IsChaosLimit (d : ℕ) (s β : ℝ) (ρ : Torus d → ℝ) (e : ℕ → Torus d → ℝ) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) (G : ℕ → Ω → ℝ) (h : Torus d → Torus d → ℝ)
    (Q : Ω → ℝ) : Prop :=
  Tendsto (fun L : ℕ => ∫⁻ ω, ‖Q ω - (1 / 2) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
      (∫ x, ∫ y, h x y * e i x * e j y ∂(withDensityReal ρ) ∂(withDensityReal ρ)) *
        (G i ω * G j ω -
          susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j))‖ₑ ^ 2 ∂P)
    atTop (𝓝 0)

/-- `‖h°‖²_{L²(mu⊗mu)}` with `h° = (P_mu ⊗ P_mu) h` the canonical centring (`canonicalCenter`). -/
def s7_hcNorm2 (d : ℕ) (ρ : Torus d → ℝ) (h : Torus d → Torus d → ℝ) : ℝ :=
  ∫ p : Torus d × Torus d, canonicalCenter (withDensityReal ρ) h p.1 p.2 ^ 2
    ∂((withDensityReal ρ).prod (withDensityReal ρ))

/-! ### Proposition 7.7 / 7.16: the mode families in `E_r` -/

/-- The dual test `phi_k = <k>^{-r} e_k` (TeX L8274-8275): the `k`-th coordinate functional of `E_r`,
`NegSobolev.coord F k = F(phi_k)`. -/
def s7_phi {d : ℕ} (r : ℝ) (k : NonzeroLattice d) : Torus d → ℝ :=
  fun x => Lattice.jp k.1 ^ (-r) * Torus.realMode k x

/-- The orthonormal basis vector `epsilon_k = <k>^r e_k` of `E_r` (the unit vector at `k` of `l^2`). -/
def s7_eps {d : ℕ} (r : ℝ) (k : NonzeroLattice d) : NegSobolev d r :=
  (lp.single 2 k (1 : ℝ) : lp (fun _ : NonzeroLattice d => ℝ) 2)

/-- The data of Proposition 7.7 for all modes at once (TeX L8274-8296): smooth `a_k = R_{gamma,mu} P_mu phi_k`
(response equation EVERYWHERE, `mu(a_k) = 0`), smooth transport fields `v_k` with `-div(rho v_k) = rho a_k`, and the
weighted bounds `|a_k|_{C^1}, |v_k|_{C^1} <= C <k>^{-d-3}` (`b_k` of `F:eq:static-weights`, summable). -/
structure s7_ModeData (d : ℕ) (s γ : ℝ) (ρ : Torus d → ℝ) (r : ℝ)
    (a : NonzeroLattice d → Torus d → ℝ) (v : NonzeroLattice d → Fin d → Torus d → ℝ) (C : ℝ) :
    Prop where
  smooth_a : ∀ k, Torus.IsSmooth (a k)
  smooth_v : ∀ k j, Torus.IsSmooth (v k j)
  resp : ∀ k x, a k x + γ * Kop (periodicRiesz d s) (withDensityReal ρ) (a k) x =
    projMean (withDensityReal ρ) (s7_phi r k) x
  mean_zero : ∀ k, ∫ x, a k x ∂(withDensityReal ρ) = 0
  div : ∀ k x, ∑ j, Torus.partialDeriv j (fun y => ρ y * v k j y) x = -(ρ x * a k x)
  bound_a : ∀ k, Torus.cbNorm 1 (a k) ≤ C * Lattice.jp k.1 ^ (-((d : ℝ) + 3))
  bound_v : ∀ k j, Torus.cbNorm 1 (v k j) ≤ C * Lattice.jp k.1 ^ (-((d : ℝ) + 3))

/-- The weight `b_k = <k>^{-d-3}`. -/
def s7_b {d : ℕ} (k : NonzeroLattice d) : ℝ := Lattice.jp k.1 ^ (-((d : ℝ) + 3))

/-- `C_{kl} = mu(phi_k a_l)` (covariance of the limit `G`). -/
def s7_Cmode {d : ℕ} (r : ℝ) (ρ : Torus d → ℝ) (a : NonzeroLattice d → Torus d → ℝ)
    (k l : NonzeroLattice d) : ℝ :=
  ∫ x, s7_phi r k x * a l x ∂(withDensityReal ρ)

/-! ### Proposition 7.16: the radial coordinates of the field -/

/-- `-k` as a nonzero frequency. -/
def s7_neg {d : ℕ} (k : NonzeroLattice d) : NonzeroLattice d := ⟨-k.1, neg_ne_zero.2 k.2⟩

/-- The pair of real Fourier coefficients `(F^(k), F^(-k)) in R^2` of a field (the coordinates
`(zeta^0(cos 2 pi k x), zeta^0(sin 2 pi k x))` of `O:eq:radial-weight` up to a sign). -/
def s7_modePair {d : ℕ} (m : ℝ) (k : NonzeroLattice d) (F : NegSobolev d m) :
    EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 fun i : Fin 2 => if i = 0 then NegSobolev.fourierCoeff F k else
    NegSobolev.fourierCoeff F (s7_neg k)

/-- The initial law `f_N = w(|pi eta_N|^2) Q_{N,beta} / E_Q[w(|pi eta_N|^2)]` of the proof of Proposition 7.16
(`O:eq:radial-weight`) as a measure: tilt of `Q_{N,beta}(dx)` by `theta(|pi eta_N|^2)`, normalised by the
`lintegral`. -/
def s7_tiltedLaw (d : ℕ) (s β : ℝ) (N : ℕ) (m : ℝ) (k : NonzeroLattice d) (θ : ℝ → ℝ) :
    Measure (Config d N) :=
  (∫⁻ X, ENNReal.ofReal (θ (‖s7_modePair m k (etaE m X volume)‖ ^ 2))
      ∂(modulatedGibbs (periodicRiesz d s) N β volume))⁻¹ •
    (modulatedGibbs (periodicRiesz d s) N β volume).withDensity
      fun X => ENNReal.ofReal (θ (‖s7_modePair m k (etaE m X volume)‖ ^ 2))

/-! ### Lemma 7.6: finite-rank smooth symmetric kernels -/

/-- `k = sum_{i,j<n} c_ij f_i(x) f_j(y)` with `c` symmetric and the `f_i` smooth (the smooth finite-rank kernels
`h_L` of `F:eq:input-tail`). -/
def s7_IsFiniteRankSmooth {d : ℕ} (k : Torus d → Torus d → ℝ) : Prop :=
  ∃ (n : ℕ) (f : Fin n → Torus d → ℝ) (c : Fin n → Fin n → ℝ),
    (∀ i, Torus.IsSmooth (f i)) ∧ (∀ i j, c i j = c j i) ∧
      ∀ x y, k x y = ∑ i, ∑ j, c i j * f i x * f j y

end HRS.MC.Sec7

end
