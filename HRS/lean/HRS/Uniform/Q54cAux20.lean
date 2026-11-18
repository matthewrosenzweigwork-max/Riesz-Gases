import HRS.Uniform.Q54cAux19

/-!
# Q54c, part 20: linear structure of the flow and of the generator path (`t ∈ [0,T]`)
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54c

open HRS HRS.PDE

variable {d : ℕ}

theorem hasDerivWithinAt_Icc_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (f' : E) : HasDerivWithinAt f f' (Set.Icc 0 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  simp

theorem coeffOf_const_eq (c : ℝ) :
    coeffOf (fun _ : Torus d => c) = (c : ℂ) • deltaCoeff (0 : Lattice d) := by
  funext j
  rw [HRS.PDE.coeffOf_const]
  rfl

theorem toFun_coeffOf_const (c : ℝ) : toFun (coeffOf (fun _ : Torus d => c)) = fun _ => c := by
  apply HRS.PDE.toFun_coeffOf (fun _ : Torus d => c) continuous_const
  rw [coeffOf_const_eq]
  refine summable_of_ne_finset_zero (s := {0}) fun k hk => ?_
  have : k ≠ 0 := by simpa using hk
  simp [deltaCoeff, this]

namespace PdeSetup

variable {P : PdeSetup d} {D : DynData d} {ν₀ : ℝ} {μ : ℝ → Torus d → ℝ} (h : P.Data D ν₀ μ)

include h

theorem Data.U_facts {t : ℝ} (ht : t ∈ Set.Icc 0 P.T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    {σ : ℝ} (hσ : σ ∈ Set.Icc 0 t) :
    propagator D μ σ t φ = toFun (P.flow D μ t φ (t - σ)) ∧
      coeffOf (propagator D μ σ t φ) = P.flow D μ t φ (t - σ) ∧
      HRS.Uniform.Q54.Dom (P.n + 4) (propagator D μ σ t φ) := by
  have hD := HRS.Uniform.Q54.dom_smooth (J := P.n + 4) hφ
  by_cases h0 : t = 0
  · subst h0
    have hσ0 : σ = 0 := le_antisymm hσ.2 hσ.1
    subst hσ0
    have e := HRS.Uniform.Q54.prop_self_zero P.hd P.s P.hs0 P.hsd (P.n + 4) P.R P.MB P.Λ P.VB D ν₀ P.T μ
      h.hA hφ
    have hz : P.flow D μ 0 φ (0 - 0) = coeffOf φ := by rw [sub_self]; exact h.flow_zero hφ
    rw [e, hz]
    have hA := coeffOf_adm hD (j := P.lev) le_rfl
    have : toFun (coeffOf φ) = φ := HRS.PDE.toFun_coeffOf φ hD.1 hA.2.1
    exact ⟨this.symm, rfl, hD⟩
  · have ht' : t ∈ Set.Ioc 0 P.T := ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), ht.2⟩
    obtain ⟨h1, h2⟩ := h.flow_prop ht' hD hσ
    exact ⟨h1, h2, HRS.Uniform.Q54.prop_dom P.hd P.s P.hs0 P.hsd (P.n + 4) P.hn P.R P.MB P.Λ P.VB D ν₀
      P.T μ h.hA ht' hD hσ⟩

theorem Data.flow_comb {t : ℝ} (ht : t ∈ Set.Icc 0 P.T) {φ ψ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    (hψ : Torus.IsSmooth ψ) (α β : ℝ) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 t) :
    P.flow D μ t (fun x => α * φ x + β * ψ x) τ =
      fun k => (α : ℂ) * P.flow D μ t φ τ k + (β : ℂ) * P.flow D μ t ψ τ k := by
  have hDφ := HRS.Uniform.Q54.dom_smooth (J := P.n + 4) hφ
  have hDψ := HRS.Uniform.Q54.dom_smooth (J := P.n + 4) hψ
  have hc := HRS.Uniform.Q54.coeffOf_lin hDφ.1 hDψ.1 α β
  by_cases h0 : t = 0
  · subst h0
    have : τ = 0 := le_antisymm hτ.2 hτ.1
    subst this
    rw [h.flow_zero (isSmooth_comb hφ hψ α β), h.flow_zero hφ, h.flow_zero hψ, hc]
  · have ht' : t ∈ Set.Ioc 0 P.T := ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), ht.2⟩
    unfold PdeSetup.flow
    rw [hc]
    exact HRS.Uniform.Q54.propagatorCoeff_lin P.hd P.hs0 P.hsd P.hJ1 h.hA ht'
      (h.memHsφ hDφ) (h.memHsφ hDψ) α β hτ

end PdeSetup

end HRS.Uniform.Q54c
