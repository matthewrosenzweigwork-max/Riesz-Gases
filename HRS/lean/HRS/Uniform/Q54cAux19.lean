import HRS.Uniform.Q54cAux18

/-!
# Q54c, part 19: the flow for `t ∈ [0,T]` (including `t = 0`) and its linear structure
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54c

open HRS HRS.PDE

variable {d : ℕ}

theorem isSmooth_comb {f g : Torus d → ℝ} (hf : Torus.IsSmooth f) (hg : Torus.IsSmooth g) (α β : ℝ) :
    Torus.IsSmooth (fun x => α * f x + β * g x) := by
  unfold Torus.IsSmooth Torus.IsCk at *
  exact (contDiff_const.mul hf).add (contDiff_const.mul hg)

theorem forwardGen_isReal' (D : DynData d) (ρ : Torus d → ℝ) (hρ : IsRealCoeff (coeffOf ρ))
    (hV : IsRealCoeff (coeffOf D.V)) {F : Coeff d} (hF : IsRealCoeff F) :
    IsRealCoeff (forwardGen D ρ F) := by
  rw [isRealCoeff_iff_reflConj] at hF ⊢
  rw [← forwardGen_reflConj D ρ hρ hV F, hF]

namespace PdeSetup

variable {P : PdeSetup d} {D : DynData d} {ν₀ : ℝ} {μ : ℝ → Torus d → ℝ} (h : P.Data D ν₀ μ)

include h

theorem Data.mem0 {r : ℝ} (hr : r ∈ Set.Icc 0 P.T) :
    MemHs 0 (coeffOf (μ r)) ∧ ∀ j, MemHs 0 (driftCoeff D (μ r) j) :=
  HRS.PDE.ET.coeff_memHs_zero_of_data D (μ r) (h.hA.hμ.smooth r hr) h.hA.hV

theorem Data.flow_zero {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    P.flow D μ 0 φ 0 = coeffOf φ :=
  HRS.PDE.StabAux.propagatorCoeff_zero D μ P.lev (coeffOf φ)
    (h.memHsφ (HRS.Uniform.Q54.dom_smooth hφ)) (by exact_mod_cast P.hJ1)

omit h in
theorem coeffOf_adm {φ : Torus d → ℝ} (hφ : HRS.Uniform.Q54.Dom (P.n + 4) φ) {j : ℝ} (hj : j ≤ P.lev) :
    Adm j (coeffOf φ) := by
  have hm := (hsNormSq_coeffOf P.lev φ hφ.2).1
  exact ⟨isRealCoeff_coeffOf φ (hφ.2.1.integrable one_le_two),
    summable_norm_of_memHs P.lev P.hJd _ hm, memHs_mono_q hj hm⟩

theorem Data.flow_adm0 {t : ℝ} (ht : t ∈ Set.Icc 0 P.T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 t) {j : ℝ} (hj : j ≤ P.lev) : Adm j (P.flow D μ t φ τ) := by
  have hD := HRS.Uniform.Q54.dom_smooth (J := P.n + 4) hφ
  by_cases h0 : t = 0
  · subst h0
    have : τ = 0 := le_antisymm hτ.2 hτ.1
    subst this
    rw [h.flow_zero hφ]
    exact coeffOf_adm hD hj
  · exact h.flow_adm ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), ht.2⟩ hD hτ hj

theorem Data.gen_adm0 {t : ℝ} (ht : t ∈ Set.Icc 0 P.T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 t) {j : ℕ} (hj : j + 2 ≤ P.n + 4) (hjd : (d : ℝ) / 2 < j) :
    Adm (j : ℝ) (P.gen D μ t φ τ) := by
  have hr : t - τ ∈ Set.Icc 0 P.T := ⟨by linarith [hτ.2], by linarith [hτ.1, ht.2]⟩
  have hA := h.flow_adm0 ht hφ hτ (j := (j : ℝ) + 2) (by exact_mod_cast hj)
  have hmem := (P.c.gen D ν₀ μ h.hA h.hν (t - τ) hr j hj _ hA.2.2).1
  have hreal : IsRealCoeff (P.gen D μ t φ τ) :=
    forwardGen_isReal' D (μ (t - τ)) (isRealCoeff_coeffOf_density h.hA.hμ hr)
      (isRealCoeff_coeffOf_V h.hA.hV) hA.1
  exact ⟨hreal, summable_norm_of_memHs (j : ℝ) hjd _ hmem, hmem⟩

end PdeSetup

end HRS.Uniform.Q54c
