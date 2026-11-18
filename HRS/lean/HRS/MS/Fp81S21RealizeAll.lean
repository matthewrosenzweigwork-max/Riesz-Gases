import HRS.MS.Fp81S21RawEval3
import HRS.MS.Fp81S21RawIncr4

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111 HRS.MS.S111X2

/-- Retain one fourth-increment raw-family witness and intersect its radius
with the independent feature-horizon radius. -/
theorem fp81s21_realize_retained_bundle (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 →
        ∀ R : Trajectory p δ,
        ∀ (hμ₀ : IsProbabilityMeasure (r26t3_mu R 0)),
          ∃ Mg : ℝ,
          ∃ K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0),
          ∃ hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg,
          ∃ V : ℝ,
          ∃ J : Fp81S21GaussFeatureHilbert p R →ₗᵢ[ℝ] GaussianFeatureHilbert,
          ∃ Ω : Type, ∃ mΩ : MeasurableSpace Ω,
          ∃ P : Measure Ω, ∃ hP : IsProbabilityMeasure P,
          ∃ e : ℕ → GaussianFeatureHilbert, ∃ ξ : ℕ → Ω → ℝ,
          ∃ W : GaussianFeatureHilbert → Ω → ℝ,
          ∃ Z0 : ℝ → Ω → OscDual p.d (wholeSpaceIndex p.d : ℝ),
            fp81s21_rawGaussianBundleSpec (P := P) p R hK V J e ξ W Z0 ∧
            (∀ H : ℝ, 0 < H →
              ∃ L : MultiIndex p.d → ℝ,
                (∀ α, 0 ≤ L α) ∧ Summable L ∧
                ∃ C : ℝ, C = 3 * (∑' α, L α) ^ 2 ∧ 0 ≤ C ∧
                  ∀ s ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc (0 : ℝ) H,
                    ∫⁻ ω, ‖Z0 t ω - Z0 s ω‖ₑ ^ (4 : ℝ) ∂P ≤
                      ENNReal.ofReal (C * |t - s| ^ 2)) ∧
            (∀ t : ℝ, 0 ≤ t → ∃ B : ℝ, 0 ≤ B ∧
              ∀ ψ : Euc p.d → ℝ,
                IsOscTest (wholeSpaceIndex p.d : ℝ) ψ →
                  ‖fp81s21_combinedFeature p R hK t ψ‖ ≤
                    B * oscNorm (wholeSpaceIndex p.d : ℝ) ψ) := by
  obtain ⟨δRaw, hδRaw, hδRawHalf, hRaw⟩ :=
    fp81s21_rawGaussianFamily_fourth_increment p
  obtain ⟨δH, hδH, hδHHalf, hHorizon⟩ :=
    fp81s21_combinedFeature_horizon_bound p
  let δ0 : ℝ := min δRaw δH
  have hδ0 : 0 < δ0 := lt_min hδRaw hδH
  have hδ0Half : δ0 ≤ 1 / 2 :=
    (min_le_left _ _).trans hδRawHalf
  refine ⟨δ0, hδ0, hδ0Half, ?_⟩
  intro δ hδ hδle R hμ₀
  letI : IsProbabilityMeasure (r26t3_mu R 0) := hμ₀
  have hδRaw' : δ ≤ δRaw := hδle.trans (min_le_left _ _)
  have hδH' : δ ≤ δH := hδle.trans (min_le_right _ _)
  rcases hRaw δ hδ hδRaw' R with
    ⟨Mg, K, hK, V, hV, J, Ω, mΩ, P, hP, e, ξ, W, Z0,
      hParseval, hstd, hWmeas, hW2, hWlim, hCov, hJoint,
      hZmeas, hZmem, hcoord, hZsecond, hNorm⟩
  letI : MeasurableSpace Ω := mΩ
  letI : IsProbabilityMeasure P := hP
  have hBundle : fp81s21_rawGaussianBundleSpec (P := P) p R hK V J e ξ W Z0 :=
    ⟨hV, hParseval, hstd, hWmeas, hW2, hWlim, hCov, hJoint,
      hZmeas, hZmem, hcoord, hZsecond⟩
  have hFeatureBound : ∀ t : ℝ, 0 ≤ t → ∃ B : ℝ, 0 ≤ B ∧
      ∀ ψ : Euc p.d → ℝ, IsOscTest (wholeSpaceIndex p.d : ℝ) ψ →
        ‖fp81s21_combinedFeature p R hK t ψ‖ ≤
          B * oscNorm (wholeSpaceIndex p.d : ℝ) ψ := by
    intro t ht
    let H : ℝ := t + 1
    have hH : 0 < H := by dsimp [H]; linarith
    obtain ⟨B, hB, hBound⟩ :=
      hHorizon δ hδ hδH' R hμ₀ H hH
    refine ⟨B, hB, ?_⟩
    intro ψ hψ
    exact hBound Mg K hK t ⟨ht, by dsimp [H]; linarith⟩ ψ hψ
  exact ⟨Mg, K, hK, V, J, Ω, mΩ, P, hP, e, ξ, W, Z0,
    hBundle, hNorm, hFeatureBound⟩

#print axioms fp81s21_realize_retained_bundle

end HRS.Fp81.S21

end
