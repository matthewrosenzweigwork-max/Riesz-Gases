import HRS.MC.CepP3Aux13
import HRS.Whole.MovingDyn

/-!
# S11.3 X2, part A (worker S11Z1): shared definitions

Namespace `HRS.MS.S113X2`, declaration prefix `s113a_`.  Interface for parts A (this worker), B (S11Z3, power chain),
C (wiring).  Notation: `EucConfig d N = Fin N → Euc d`; the particle SDE is
`dX = b(X) dt + √(2β⁻¹) dW` with `b = particleDriftW (quadraticGradientDyn d s q β)`.

* `s113a_survives D X t` : paths that stay in `D` on `[0,t]`.
* `s113a_killedLaw P D X₀ X chi t` : the weighted killed law `Law(X_t ; chi(X₀) 1_{X_r ∈ D, r ≤ t})`.
* `s113a_killedSpacetime P D X₀ X chi T` : the space-time measure `∫_0^T δ_t ⊗ killedLaw t dt` (a finite measure on `ℝ × EucConfig d N`).
* `s113a_drift`, `s113a_gen` : the space-time forward operator `L Φ = ∂_t Φ + β⁻¹ Δ_x Φ + D_xΦ[b]`.
* `s113a_domain d N k` : the exhaustion of the collision-free configuration space by bounded open sets with compact closure
  inside the free set (`separation > 1/(k+1)`, `‖x_i‖ < k+1`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MS.S113X2

open HRS.Whole

variable {d N : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- Paths that stay in `D` on the whole interval `[0,t]`. -/
def s113a_survives (D : Set (EucConfig d N)) (X : ℝ≥0 → Ω → EucConfig d N) (t : ℝ≥0) : Set Ω :=
  {w | ∀ r : ℝ≥0, r ≤ t → X r w ∈ D}

open Classical in
/-- The weighted killed law at time `t`. -/
def s113a_killedLaw (P : Measure Ω) (D : Set (EucConfig d N))
    (X₀ : Ω → EucConfig d N) (X : ℝ≥0 → Ω → EucConfig d N)
    (chi : EucConfig d N → ℝ) (t : ℝ≥0) : Measure (EucConfig d N) :=
  (P.withDensity fun w =>
    if w ∈ s113a_survives D X t then ENNReal.ofReal (chi (X₀ w)) else 0).map (X t)

open Classical in
/-- The killed space-time measure on `(0,T)`. -/
def s113a_killedSpacetime (P : Measure Ω) (D : Set (EucConfig d N))
    (X₀ : Ω → EucConfig d N) (X : ℝ≥0 → Ω → EucConfig d N)
    (chi : EucConfig d N → ℝ) (T : ℝ) : Measure (ℝ × EucConfig d N) :=
  (((volume.restrict (Set.Ioo 0 T)).prod P).withDensity fun z =>
    if z.2 ∈ s113a_survives D X z.1.toNNReal then ENNReal.ofReal (chi (X₀ z.2)) else 0).map
      (fun z => (z.1, X z.1.toNNReal z.2))

/-- The physical drift as a vector field on space-time. -/
def s113a_drift (d : ℕ) (s q β : ℝ) (N : ℕ) (p : ℝ × EucConfig d N) : EucConfig d N :=
  fun i => particleDriftW (quadraticGradientDyn d s q β) p.2 i

/-- The space-time forward operator `∂_t Φ + β⁻¹ Δ_x Φ + D_xΦ[b]`. -/
def s113a_gen (d : ℕ) (s q β : ℝ) (N : ℕ) (Phi : ℝ × EucConfig d N → ℝ) :
    ℝ × EucConfig d N → ℝ :=
  HRS.MC.CepP3.Lop β⁻¹ (s113a_drift d s q β N) Phi

/-- The `k`-th bounded open set of the exhaustion of the collision-free configuration space. -/
def s113a_domain (d N k : ℕ) : Set (EucConfig d N) :=
  {x | (∀ i j, i ≠ j → 1 / ((k : ℝ) + 1) < ‖x i - x j‖) ∧ ∀ i, ‖x i‖ < (k : ℝ) + 1}

end HRS.MS.S113X2

end
