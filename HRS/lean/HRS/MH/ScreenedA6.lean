import HRS.MH.ScreenedDefs

/-! Packet A6 of `B:lem:screened` (S.B.4): proof of the statement of `regularDensity_bounds` in `ScreenedSpec.lean`. -/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

theorem regularDensity_bounds_proof {m : ℕ} {Λ : ℝ} {μ : Euc d → ℝ} (hμ : IsRegularDensityW (m + 3) Λ μ)
    {j : ℕ} (hj : j ≤ m + 1) (idx : Fin j → Fin d) :
    Continuous (partialDeriv idx μ) ∧ ∀ y, jbracket y ^ ((d : ℝ) + 3) * |partialDeriv idx μ y| ≤ max Λ 0 := by
  obtain ⟨hC, -, hW⟩ := hμ
  constructor
  · have h1 : Continuous (fun x => iteratedFDeriv ℝ j μ x) :=
      hC.continuous_iteratedFDeriv (by exact_mod_cast (by omega : j ≤ m + 3))
    unfold partialDeriv
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ
      (fun l => EuclideanSpace.single (idx l) (1 : ℝ))).continuous.comp h1
  · intro y
    have hle : ENNReal.ofReal (jbracket y ^ ((d : ℝ) + 3) * |partialDeriv idx μ y|) ≤
        ENNReal.ofReal Λ := by
      refine le_trans ?_ (le_trans le_add_self hW)
      unfold weightedSupE derivSupE
      refine le_trans ?_ (le_iSup _ (⟨j, by omega⟩ : Fin (m + 3 + 1)))
      refine le_trans ?_ (le_iSup _ idx)
      exact le_iSup (fun x => ENNReal.ofReal (jbracket x ^ ((d : ℝ) + 3) * |partialDeriv idx μ x|)) y
    have hnn : 0 ≤ jbracket y ^ ((d : ℝ) + 3) * |partialDeriv idx μ y| := by
      unfold jbracket; positivity
    calc _ = (ENNReal.ofReal (jbracket y ^ ((d : ℝ) + 3) * |partialDeriv idx μ y|)).toReal := by
          rw [ENNReal.toReal_ofReal hnn]
      _ ≤ (ENNReal.ofReal Λ).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = max Λ 0 := by rw [ENNReal.toReal_ofReal']

end HRS.MH.Screened
