import HRS.PDE.ToolboxRd.Defs
import HRS.PDE.ToolboxRd.Fourier
import HRS.PDE.ToolboxRd.Levy
import HRS.PDE.ToolboxRd.Weighted
import HRS.PDE.ToolboxRd.PV
import HRS.PDE.ToolboxRd.Bilinear

/-!
# Lemma C.3 on `ℝ^d` (`B:lem:quadratic-toolbox`, lines 12253–12268)

The `ℝ^d` analogues of the torus theorems `quadratic_toolbox_*` of `HRS/PDE/Toolbox.lean`; definitions
are in `HRS/PDE/ToolboxRd/Defs.lean`.  Hypotheses follow the source: real, even symbol `m ≥ 0`
vanishing at `0`, homogeneous of degree `θ ∈ (0,2)` and smooth away from `0`; `u, v ∈ H¹ ∩ C^{0,1}`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.ToolboxRd

variable {d : ℕ}

/-- The symbols `𝔪_q` of `B:eq:Kl-def` on `ℝ^d` belong to the symbol class of Lemma C.3 with
`θ = s + 2 - d ∈ (0,2)` (for `d - 2 < s < d` and the standing assumption `0 ≤ s`). -/
theorem symbolK_isHomogSymbol (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : (d : ℝ) - 2 < s)
    (hsd : s < d) (q : Euc d) : IsHomogSymbol (thetaOrder d s) (symbolKRd d s q) := by
  have h : symbolKRd d s q = SymAux.symExt d s q := rfl
  rw [h]
  refine ⟨SymAux.symExt_contDiffOn d s q, SymAux.symExt_neg d s q,
    SymAux.symExt_nonneg hd hs0 hsd q, fun c hc ξ => SymAux.symExt_smul d s q c hc ξ, ?_⟩
  simp [SymAux.symExt]

/-- Lemma C.3(i) on `ℝ^d` (line 12256): `B` is symmetric, positive semidefinite, and
`B(u,u) ≤ C ‖u‖²_{H^{θ/2}}` (all forms finite for `u, v ∈ H^{θ/2}`). -/
theorem quadratic_toolbox_basic (θ : ℝ) (hθ0 : 0 < θ) (hθ2 : θ < 2) (m : Euc d → ℝ)
    (hm : IsHomogSymbol θ m) :
    ∃ C : ℝ, ∀ u v : Euc d → ℝ, MemSobolev (θ / 2) u → MemSobolev (θ / 2) v →
      Integrable (fun ξ => m ξ * ‖fourierL2 u ξ‖ ^ 2) ∧ Integrable (fun ξ => m ξ * ‖fourierL2 v ξ‖ ^ 2) ∧
      Integrable (fun ξ => ((m ξ : ℝ) : ℂ) * (fourierL2 u ξ * conj (fourierL2 v ξ))) ∧
      symbolForm m u v = symbolForm m v u ∧ 0 ≤ symbolForm m u u ∧
      symbolForm m u u ≤ C * sobolevNormSq (θ / 2) u :=
  FourierAux.form_basic hθ0 hm

/-- Lemma C.3(ii) on `ℝ^d` (lines 12257–12261): the Lévy kernel `𝔨` exists (`IsLevyKernel`). -/
theorem quadratic_toolbox_kernel (hd : 1 ≤ d) (θ : ℝ) (hθ0 : 0 < θ) (hθ2 : θ < 2)
    (m : Euc d → ℝ) (hm : IsHomogSymbol θ m) : ∃ 𝔨 : Euc d → ℝ, IsLevyKernel θ m 𝔨 := by
  obtain ⟨𝔨, hev, hsm, hb, hs⟩ := LevyAux.levy_core hd hθ0 hθ2 hm
  have hmeas : Measurable 𝔨 := WeightAux.measurable_of_smooth hsm
  exact ⟨𝔨, ⟨hev, hsm, hb, hs, PVAux.pv_core hd hθ0 hθ2 hm 𝔨 hev hmeas hb hs,
    BilinAux.bilinear_core hd hθ0 hθ2 hm 𝔨 hev hmeas hb hs⟩⟩

/-- Lemma C.3(iii) on `ℝ^d` (lines 12262–12264), weighted symmetrization: for `0 ≤ a ∈ C^{1,1}_b`
with `m = √a` Lipschitz and `w ∈ H¹ ∩ C^{0,1}`,
`B(aw,w) = B(mw,mw) + E`, `E = -½ ∬ 𝔨(z) w(x) w(x-z) (δ_z m(x))² dz dx`, and
`|E| ≤ C (‖∇m‖²_∞ + ‖m‖²_∞) ‖w‖²_{L²}` with `C` depending on the kernel only. -/
theorem quadratic_toolbox_weighted (hd : 1 ≤ d) (θ : ℝ) (hθ0 : 0 < θ) (hθ2 : θ < 2)
    (m𝔪 : Euc d → ℝ) (hm𝔪 : IsHomogSymbol θ m𝔪) (𝔨 : Euc d → ℝ) (h𝔨 : IsLevyKernel θ m𝔪 𝔨) :
    ∃ C : ℝ, ∀ (L La Lm Lw : ℝ) (a w : Euc d → ℝ), (∀ x, 0 ≤ a x) → IsC11 L a →
      IsLipschitz La a → IsLipschitz Lm (fun x => Real.sqrt (a x)) →
      IsLipschitz Lw w → MemSobolev 1 w →
      let m := fun x => Real.sqrt (a x)
      let E := symbolForm m𝔪 (fun x => a x * w x) w -
        symbolForm m𝔪 (fun x => m x * w x) (fun x => m x * w x)
      Integrable (fun p : Euc d × Euc d => 𝔨 p.2 * w p.1 * w (p.1 - p.2) * (m p.1 - m (p.1 - p.2)) ^ 2) ∧
      E = -(1 / 2) * ∫ p : Euc d × Euc d, 𝔨 p.2 * w p.1 * w (p.1 - p.2) * (m p.1 - m (p.1 - p.2)) ^ 2 ∧
      |E| ≤ C * (Lm ^ 2 + (⨆ x, |m x|) ^ 2) * l2NormSq w := by
  exact WeightAux.weighted_core hd θ hθ0 hθ2 m𝔪 𝔨 h𝔨
    (fun w _ hw h2 => FourierAux.bdd_of_lipschitz_memLp hw h2)
    (fun _ _ _ hb hbb hh => FourierAux.memSobolev_one_mul hb hbb hh)

/-- Lemma C.3(iv) on `ℝ^d` (line 12265), weighted comparison: if moreover `a ≥ λ₀ > 0`, then
`B(w,w) ≤ λ₀⁻¹ B(mw,mw) + C(1+λ₀⁻¹)(‖√a‖²_{C^{0,1}} + ‖√(a/λ₀-1)‖²_{C^{0,1}} + 1) ‖w‖²_{L²}`. -/
theorem quadratic_toolbox_compare (hd : 1 ≤ d) (θ : ℝ) (hθ0 : 0 < θ) (hθ2 : θ < 2)
    (m𝔪 : Euc d → ℝ) (hm𝔪 : IsHomogSymbol θ m𝔪) :
    ∃ C : ℝ, ∀ (L lam0 Lm Lm' Lw : ℝ) (a w : Euc d → ℝ), 0 < lam0 → (∀ x, lam0 ≤ a x) → IsC11 L a →
      IsLipschitz Lm (fun x => Real.sqrt (a x)) →
      IsLipschitz Lm' (fun x => Real.sqrt (a x / lam0 - 1)) → IsLipschitz Lw w → MemSobolev 1 w →
      let m := fun x => Real.sqrt (a x)
      symbolForm m𝔪 w w ≤ lam0⁻¹ * symbolForm m𝔪 (fun x => m x * w x) (fun x => m x * w x) +
        C * (1 + lam0⁻¹) * (c01Norm m ^ 2 +
          c01Norm (fun x => Real.sqrt (a x / lam0 - 1)) ^ 2 + 1) * l2NormSq w := by
  obtain ⟨𝔨, h𝔨⟩ := quadratic_toolbox_kernel hd θ hθ0 hθ2 m𝔪 hm𝔪
  exact WeightAux.compare_core hd θ hθ0 hθ2 m𝔪 hm𝔪 𝔨 h𝔨
    (fun w _ hw h2 => FourierAux.bdd_of_lipschitz_memLp hw h2)
    (fun _ _ _ hb hbb hh => FourierAux.memSobolev_one_mul hb hbb hh)

/-- Lemma C.3(v) on `ℝ^d` (line 12266), Cauchy–Schwarz for the form. -/
theorem quadratic_toolbox_cauchySchwarz (θ : ℝ) (hθ0 : 0 < θ) (hθ2 : θ < 2) (m : Euc d → ℝ)
    (hm : IsHomogSymbol θ m) (u v : Euc d → ℝ) (hu : MemSobolev (θ / 2) u)
    (hv : MemSobolev (θ / 2) v) :
    |symbolForm m u v| ≤ Real.sqrt (symbolForm m u u) * Real.sqrt (symbolForm m v v) :=
  FourierAux.form_cauchySchwarz hθ0 hm hu hv

end HRS.PDE.ToolboxRd
