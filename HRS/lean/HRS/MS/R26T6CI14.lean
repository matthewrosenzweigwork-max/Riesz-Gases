import HRS.MS.R26T6CI11
import HRS.MS.R26T6CI12

set_option autoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff
namespace HRS.MS.R26T6C
open HRS
open HRS.Whole

theorem r26t6c_initial_H1_L3_lift (d : ℕ) (m T : ℝ) (hT : 0 < T) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P],
      ∀ f g : MultiIndex d → ℝ → Omega → ℝ,
      ∀ b : MultiIndex d → ℝ, (∀ alpha, 0 ≤ b alpha) →
      Summable (fun alpha => b alpha ^ 2) → (∑' alpha, b alpha ^ 2) ≤ 1 →
      ∀ A : ℝ, 0 ≤ A →
      (∀ alpha, MemLp (f alpha 0) 3 P) →
      (∀ alpha, AEStronglyMeasurable (fun z : ℝ × Omega => g alpha z.1 z.2)
        ((volume.restrict (Set.Icc 0 T)).prod P)) →
      (∀ alpha, ∀ t ∈ Set.Icc 0 T, MemLp (g alpha t) 3 P) →
      (∀ alpha, (∫ w, |f alpha 0 w| ^ 3 ∂P) ≤ (A * b alpha) ^ 3) →
      (∀ alpha, ∀ t ∈ Set.Icc 0 T,
        (∫ w, |g alpha t w| ^ 3 ∂P) ≤ (A * b alpha) ^ 3) →
      (∀ᵐ w ∂P, ∀ alpha,
        IntegrableOn (fun t => g alpha t w) (Set.Icc 0 T) ∧
        ∀ t ∈ Set.Icc 0 T, f alpha t w =
          f alpha 0 w + ∫ v in Set.Icc 0 t, g alpha v w) →
      ∃ L : Omega → OscPath d m T, MemLp L 3 P ∧
        (∀ᵐ w ∂P, ∀ t : Set.Icc (0 : ℝ) T, ∀ alpha,
          OscDual.coord (OscPath.at' (L w) t) alpha = f alpha t w) ∧
        (∫ w, ‖L w‖ ^ 3 ∂P) ≤ K * A ^ 3 ∧
        ∃ I : projTensor (OscPath d m T) 3,
          (∀ M : (OscPath d m T) [×3]→L[ℝ] ℝ,
            (I : TensorDual (OscPath d m T) 3) M = ∫ w, M ![L w, L w, L w] ∂P) ∧
          ‖I‖ ≤ K * A ^ 3 := by
  obtain ⟨K, hK, hLift⟩ := r26t6c_initial_path_L3 d m T hT
  refine ⟨K, hK, ?_⟩
  intro Omega ms P prob f g b hb0 hb hb1 A hA hf0 hgm hgLp hfm hgBound hFTC
  obtain ⟨L, hLp, hcoord, hcubebound⟩ :=
    hLift P f g b hb0 hb hb1 A hA hf0 hgm hgLp hfm hgBound hFTC
  obtain ⟨I, hpair, hnorm⟩ :=
    r26t6c_cubic_tensor_expectation P L hLp
  exact ⟨L, hLp, hcoord, hcubebound, I, hpair, le_trans hnorm hcubebound⟩

end HRS.MS.R26T6C
