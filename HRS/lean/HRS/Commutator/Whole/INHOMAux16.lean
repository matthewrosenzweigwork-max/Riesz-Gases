import HRS.Commutator.Whole.INHOMAux15

/-!
# CMX-INHOM auxiliary 16: the bound for the high-frequency part `a₁` (`(4.a1bound)`)
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

theorem inhom_a1_bound (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
      ∀ (φ ψ : SchwartzMap (Euc d) ℂ) (b : Euc d → ℝ), (∀ x, ψ x = ((b x : ℝ) : ℂ)) →
        (∀ ξ, 𝓕 (⇑ψ) ξ = (1 - cmxFB_gL d (1 / 16) ξ) * 𝓕 (⇑φ) ξ) →
        ENNReal.ofReal |CcommFun (ghiForce s) v b| ≤
          ENNReal.ofReal (C * K) * inhom_Sob (-alphaE d s) φ := by
  obtain ⟨C1, hC1, h1⟩ := inhom_T_nrs hd hs0 hsd
  obtain ⟨C2, hC2, h2⟩ := inhom_T_low hd hs0 hsd
  obtain ⟨C3, hC3, h3⟩ := inhom_T_prod hd hs0 hsd
  refine ⟨C1 + C2 + C3, by positivity, fun v K hv φ ψ b hψ hF => ?_⟩
  have hK0 := inhom_subTransport_nonneg hv
  obtain ⟨hac, hai, ⟨M, hM⟩, ha1, ha2⟩ := inhom_schw_props hψ
  obtain ⟨L, F, hF0, hL, -, hK⟩ := id hv
  have hsplit := inhom_a1_split hd hs0 hsd hL hac hai hM ha1.norm (by simpa using ha2)
  have e1 := h1 v K hv φ ψ b hψ hF
  have e2 := h2 v K hv φ ψ b hψ hF
  have e3 := h3 v K hv φ ψ b hψ hF
  set S := inhom_Sob (-alphaE d s) φ with hS
  rw [hsplit]
  have hle : |CcommFun (kernGrad s) v b - CcommFun (gloForce s) (Pleq 1 v) b -
      CcommFun (gloForce s) (Pgt 1 v) b| ≤ |CcommFun (kernGrad s) v b| +
      |CcommFun (gloForce s) (Pleq 1 v) b| + |CcommFun (gloForce s) (Pgt 1 v) b| := by
    calc _ ≤ |CcommFun (kernGrad s) v b - CcommFun (gloForce s) (Pleq 1 v) b| +
          |CcommFun (gloForce s) (Pgt 1 v) b| := abs_sub _ _
      _ ≤ _ := by gcongr; exact abs_sub _ _
  calc ENNReal.ofReal |CcommFun (kernGrad s) v b - CcommFun (gloForce s) (Pleq 1 v) b -
        CcommFun (gloForce s) (Pgt 1 v) b|
      ≤ ENNReal.ofReal (|CcommFun (kernGrad s) v b| + |CcommFun (gloForce s) (Pleq 1 v) b| +
          |CcommFun (gloForce s) (Pgt 1 v) b|) := ENNReal.ofReal_le_ofReal hle
    _ ≤ ENNReal.ofReal |CcommFun (kernGrad s) v b| + ENNReal.ofReal |CcommFun (gloForce s) (Pleq 1 v) b| +
          ENNReal.ofReal |CcommFun (gloForce s) (Pgt 1 v) b| := by
        refine (ENNReal.ofReal_add_le).trans ?_
        gcongr
        exact ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal (C1 * K) * S + ENNReal.ofReal (C2 * K) * S + ENNReal.ofReal (C3 * K) * S := by
        gcongr
    _ = ENNReal.ofReal ((C1 + C2 + C3) * K) * S := by
        rw [← add_mul, ← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 2; ring

end HRS.Commutator.Whole
