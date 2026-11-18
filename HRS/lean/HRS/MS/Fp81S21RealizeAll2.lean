import HRS.MS.Fp81S21RealizeAll
import HRS.MS.Fp81S21RealizePatch2

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS.Whole

/-- Apply the supplied-space Kolmogorov–Chentsov modification on each integer
horizon, keeping the original process and probability measure. -/
theorem fp81s21_realize_local_modifications
    {d : ℕ} {m : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℝ → Ω → OscDual d m)
    (hXmeas : ∀ t, Measurable (X t))
    (hNorm : ∀ H : ℝ, 0 < H →
      ∃ L : MultiIndex d → ℝ,
        (∀ α, 0 ≤ L α) ∧ Summable L ∧
        ∃ C : ℝ, C = 3 * (∑' α, L α) ^ 2 ∧ 0 ≤ C ∧
          ∀ s ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc (0 : ℝ) H,
            ∫⁻ ω, ‖X t ω - X s ω‖ₑ ^ (4 : ℝ) ∂P ≤
              ENNReal.ofReal (C * |t - s| ^ 2)) :
    ∃ Y : ∀ n : ℕ, Ω → OscPath d m ((n : ℝ) + 1),
      (∀ n, Measurable (Y n)) ∧
      (∀ (n : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) ((n : ℝ) + 1)),
        (fun ω => OscPath.at' (Y n ω) ⟨t, ht⟩) =ᵐ[P] X t) := by
  classical
  have hLocal : ∀ n : ℕ,
      ∃ Yn : Ω → OscPath d m ((n : ℝ) + 1),
        Measurable Yn ∧
        ∀ t (ht : t ∈ Icc (0 : ℝ) ((n : ℝ) + 1)),
          (fun ω => OscPath.at' (Yn ω) ⟨t, ht⟩) =ᵐ[P] X t := by
    intro n
    let H : ℝ := (n : ℝ) + 1
    have hH : 0 < H := by dsimp [H]; positivity
    obtain ⟨L, hL0, hLsum, C, hCeq, hC0, hBound⟩ := hNorm H hH
    have h4 : ∀ s ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc (0 : ℝ) H,
        ∫⁻ ω, ‖X t ω - X s ω‖ₑ ^ (4 : ℝ) ∂P ≤
          ENNReal.ofReal (C * |t - s| ^ (2 : ℝ)) := by
      intro s hs t ht
      calc
        ∫⁻ ω, ‖X t ω - X s ω‖ₑ ^ (4 : ℝ) ∂P ≤
            ENNReal.ofReal (C * |t - s| ^ 2) := hBound s hs t ht
        _ = ENNReal.ofReal (C * |t - s| ^ (2 : ℝ)) := by
          congr 1
          exact congrArg (fun x : ℝ => C * x) (Real.rpow_natCast _ 2).symm
    obtain ⟨Yn, hYnmeas, hYnmod⟩ :=
      fp81s21_local_modification hH X hXmeas h4
    simpa [H] using (show ∃ Yn : Ω → OscPath d m H,
      Measurable Yn ∧
      ∀ t (ht : t ∈ Icc (0 : ℝ) H),
        (fun ω => OscPath.at' (Yn ω) ⟨t, ht⟩) =ᵐ[P] X t from
          ⟨Yn, hYnmeas, hYnmod⟩)
  refine ⟨fun n => Classical.choose (hLocal n), ?_, ?_⟩
  · intro n
    exact (Classical.choose_spec (hLocal n)).1
  · intro n t ht
    exact (Classical.choose_spec (hLocal n)).2 t ht

#print axioms fp81s21_realize_local_modifications

end HRS.Fp81.S21

end
