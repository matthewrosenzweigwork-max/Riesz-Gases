import HRS.Commutator.Whole.INHOMAux23

/-!
# CMX-INHOM auxiliary 24: Lemma 4.2 for real Schwartz `a`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

theorem inhom_schwartz (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
      ∀ (φ : SchwartzMap (Euc d) ℂ) (a : Euc d → ℝ), (∀ x, φ x = ((a x : ℝ) : ℂ)) →
        ENNReal.ofReal |CcommFun (ghiForce s) v a| ≤
          ENNReal.ofReal (C * K) * inhom_Sob (-alphaE d s) φ := by
  obtain ⟨C1, hC1, h1⟩ := inhom_a1_bound hd hs0 hsd
  obtain ⟨C2, hC2, h2⟩ := inhom_cross hd hs0 hsd
  refine ⟨C1 + C2, by positivity, fun v K hv φ a hφ => ?_⟩
  have hK0 := inhom_subTransport_nonneg hv
  obtain ⟨a₀, φ₀, φ₁, ha₀, hφ₀, hφ₁, hF₀, hF₁⟩ := inhom_split hφ
  set a₁ : Euc d → ℝ := fun x => a x - a₀ x with ha₁def
  have e1 := h1 v K hv φ φ₁ a₁ hφ₁ hF₁
  have e2 := h2 v K hv φ φ₀ φ₁ a a₀ a₁ hφ hφ₀ hφ₁ (fun x => rfl) ha₀ hF₀ hF₁
  set S := inhom_Sob (-alphaE d s) φ with hS
  have hle : |CcommFun (ghiForce s) v a| ≤ |CcommFun (ghiForce s) v a₁| +
      |CcommFun (ghiForce s) v a - CcommFun (ghiForce s) v a₁| := by
    calc |CcommFun (ghiForce s) v a| =
        |CcommFun (ghiForce s) v a₁ + (CcommFun (ghiForce s) v a - CcommFun (ghiForce s) v a₁)| := by
          ring_nf
      _ ≤ _ := abs_add_le _ _
  calc ENNReal.ofReal |CcommFun (ghiForce s) v a|
      ≤ ENNReal.ofReal (|CcommFun (ghiForce s) v a₁| +
          |CcommFun (ghiForce s) v a - CcommFun (ghiForce s) v a₁|) := ENNReal.ofReal_le_ofReal hle
    _ ≤ ENNReal.ofReal |CcommFun (ghiForce s) v a₁| +
          ENNReal.ofReal |CcommFun (ghiForce s) v a - CcommFun (ghiForce s) v a₁| :=
        ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal (C1 * K) * S + ENNReal.ofReal (C2 * K) * S := add_le_add e1 e2
    _ = ENNReal.ofReal ((C1 + C2) * K) * S := by
        rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 2; ring

end HRS.Commutator.Whole
