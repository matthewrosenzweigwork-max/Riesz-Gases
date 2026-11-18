import HRS.MS.Fp81S21MovingM1
import HRS.MS.R2InterpAux19
import HRS.MS.Fp81S21SLin

/-!
# Physical drift cumulative: deterministic and physical stages

The intended full export has this telescope (where `B H` abbreviates
`OscPath p.d (wholeSpaceIndex p.d : ℝ) H`):

```
(p : Parameters) :
  ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
    ∃ future : (H : ℝ) → ℝ → Measure (B H),
      fp81s21_moving_heat_full_clause p R future ∧
      ∀ (a : ℝ) (ha : 0 ≤ a) (N : ℕ) (hN : 2 ≤ N)
        (A : Particle R N),
      ∃ (Fd : A.Ω → ℝ → B (a + p.T)) (V : A.Ω → ℝ),
        (∀ t : ℝ, Measurable (fun ω => Fd ω t)) ∧
        Integrable V A.P ∧
        ∀ᵐ ω ∂A.P,
          Fd ω 0 = 0 ∧
          ContinuousOn (Fd ω) (Set.Icc 0 (a + p.T)) ∧
          BoundedVariationOn (Fd ω) (Set.Icc 0 (a + p.T)) ∧
          (eVariationOn (Fd ω) (Set.Icc 0 (a + p.T))).toReal ≤ V ω ∧
          ∀ q r : ℝ, 0 ≤ q → q ≤ r → r ≤ a + p.T →
            Fd ω r - Fd ω q =
              r2DriftInc (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) (a + p.T)
                (fun v f => r2QuadField p.s (r26t3_mu R v) A.P A.X v ω f) q r
```

The declarations below establish a pathwise stage, with explicit standing
inputs as allowed by the design.  They do not claim the missing measurable
version or the full common-radius export.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp

/-- A monotone increment control bounds the total variation itself. -/
theorem fp81s21_variation_le_of_increment {E : Type*} [NormedAddCommGroup E]
    {H : ℝ} (hH : 0 ≤ H) (F : ℝ → E) (Φ : ℝ → ℝ)
    (hΦ : MonotoneOn Φ (Icc 0 H))
    (h : ∀ x y, x ∈ Icc (0 : ℝ) H → y ∈ Icc (0 : ℝ) H → x ≤ y →
      ‖F y - F x‖ ≤ Φ y - Φ x) :
    eVariationOn F (Icc 0 H) ≤ ENNReal.ofReal (Φ H - Φ 0) := by
  unfold eVariationOn
  refine iSup_le fun p => ?_
  obtain ⟨n, u, hu, hus⟩ := p
  calc ∑ i ∈ Finset.range n, edist (F (u (i + 1))) (F (u i))
      ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal (Φ (u (i + 1)) - Φ (u i)) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [edist_dist, dist_eq_norm]
        exact ENNReal.ofReal_le_ofReal (h _ _ (hus i) (hus (i + 1)) (hu (Nat.le_succ i)))
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n, (Φ (u (i + 1)) - Φ (u i))) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro i hi
        exact sub_nonneg.2 (hΦ (hus i) (hus (i + 1)) (hu (Nat.le_succ i)))
    _ = ENNReal.ofReal (Φ (u n) - Φ (u 0)) := by rw [Finset.sum_range_sub (fun i => Φ (u i))]
    _ ≤ ENNReal.ofReal (Φ H - Φ 0) := by
        apply ENNReal.ofReal_le_ofReal
        have h1 := hΦ (hus n) (⟨hH, le_rfl⟩ : H ∈ Icc (0 : ℝ) H) (hus n).2
        have h2 := hΦ (⟨le_rfl, hH⟩ : (0 : ℝ) ∈ Icc (0 : ℝ) H) (hus 0) (hus 0).1
        linarith

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_variation_le_of_increment
