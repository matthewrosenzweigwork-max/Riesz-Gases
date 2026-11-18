import HRS.MC.S7PIF6D
import HRS.MC.S7PIF1Brk

/-!
# Packet piF6, part E: the Itô drift of the extension on `(a,b]` is the cylindrical density
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MatrixOrder

noncomputable section

namespace HRS.MC.Sec7.S7PIF6

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIS3

variable {d : ℕ}

/-- pointwise identification of `itoDrift` with `-N^{-1/2} cylA + (2√N)⁻¹ cylJ` on `(a,b]` -/
theorem S7PIF6_drift_pt (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (N : ℕ) (hN : 1 ≤ N)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → Config d N) (ω : Ω)
    {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (hφ : ∀ i, Torus.IsSmooth (φ i))
    (G : EuclideanSpace ℝ (Fin q) → ℝ) (f : ℝ → EuclideanSpace ℝ (Fin q) → ℝ)
    (bd : ℝ → Ω → EuclideanSpace ℝ (Fin q))
    (Φc : ℝ → Ω → (Fin N × Fin d) → EuclideanSpace ℝ (Fin q))
    (Z : ℝ → Ω → EuclideanSpace ℝ (Fin q)) (a b : ℝ)
    (hfeq : ∀ r ∈ Set.Icc a b, f r = gaussHeat (obsCov R.D R.ρ t φ) G r)
    (hfd : ∀ r ∈ Set.Ioc a b, ∀ c, derivWithin (fun s => f s c) (Set.Icc 0 T) r =
      -(1 / 2) * ∑ i, ∑ j, obsRate R.D R.ρ t φ r i j *
        iteratedFDeriv ℝ 2 (gaussHeat (obsCov R.D R.ρ t φ) G r) c
          ![EuclideanSpace.single i 1, EuclideanSpace.single j 1])
    (hbform : ∀ r ω i, bd r ω i = if 0 ≤ r then -(Real.sqrt N)⁻¹ * NegSobolev.eval
        (quadFieldAt m R.D.s (fun s => withDensityReal (R.ρ s)) P X r ω) (obsTest R.D R.ρ t φ i r) else 0)
    (hΦform : ∀ s ω k i, Φc s ω k i = Real.sqrt N *
        empiricalNoiseIntegrand R.D (t i) (fun r => propagator R.D R.ρ r (t i) (φ i)) X s ω k)
    {s : ℝ} (hs : s ∈ Set.Ioc a b) (hsT : s ∈ Set.Icc (0 : ℝ) T)
    (hZ : Z s ω = obsVec m T t φ (predicted R.D R.ρ (zetaWin m T 0 P X ω) s)) :
    itoDrift T f Z bd Φc s ω = -(Real.sqrt N)⁻¹ * cylA R m T P X t φ G ω s +
      (1 / (2 * Real.sqrt N)) * cylJ R m T P X t φ G ω s := by
  have hsab : s ∈ Set.Icc a b := ⟨hs.1.le, hs.2⟩
  unfold itoDrift
  rw [hfd s hs, hfeq s hsab]
  have hbr : ∀ i j, ∑ k, Φc s ω k i * Φc s ω k j = obsRate R.D R.ρ t φ s i j +
      (Real.sqrt N)⁻¹ * (2 * R.D.invβ *
        NegSobolev.eval (etaE m (X s.toNNReal ω) (withDensityReal (R.ρ s)))
          (fun y => inner ℝ (Torus.grad (obsTest R.D R.ρ t φ i s) y)
            (Torus.grad (obsTest R.D R.ρ t φ j s) y))) := by
    intro i j
    simp_rw [hΦform]
    exact HRS.MC.Sec7.S7PIF1.s7_PIF_bracket_proof R m hm T N hN X ω t φ ht hφ i j s hsT
  rw [S7PIF6_drift_alg (gaussHeat (obsCov R.D R.ρ t φ) G s) (Z s ω) (obsRate R.D R.ρ t φ s)
    (fun i j => (Real.sqrt N)⁻¹ * (2 * R.D.invβ *
        NegSobolev.eval (etaE m (X s.toNNReal ω) (withDensityReal (R.ρ s)))
          (fun y => inner ℝ (Torus.grad (obsTest R.D R.ρ t φ i s) y)
            (Torus.grad (obsTest R.D R.ρ t φ j s) y)))) (Φc s ω) (bd s ω) _ rfl hbr]
  rw [hZ]
  unfold cylA cylJ
  simp_rw [hbform, if_pos hsT.1]
  have hsN : Real.sqrt N ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    exact (Real.sqrt_pos.2 this).ne'
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  have e1 : ∀ i, -(Real.sqrt N)⁻¹ * (fderiv ℝ (gaussHeat (obsCov R.D R.ρ t φ) G s)
        (obsVec m T t φ (predicted R.D R.ρ (zetaWin m T 0 P X ω) s)) (EuclideanSpace.single i 1) *
      NegSobolev.eval (quadFieldAt m R.D.s (fun s => withDensityReal (R.ρ s)) P X s ω)
        (obsTest R.D R.ρ t φ i s)) = _ := fun i => rfl
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp

end HRS.MC.Sec7.S7PIF6

end
