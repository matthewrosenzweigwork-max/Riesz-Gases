import HRS.Uniform.Q54cAux21

/-!
# Q54c, part 22: Lipschitz dependence of the flow on the terminal time (cocycle)
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54c

open HRS HRS.PDE

variable {d : ℕ}

namespace PdeSetup

variable {P : PdeSetup d} {D : DynData d} {ν₀ : ℝ} {μ : ℝ → Torus d → ℝ} (h : P.Data D ν₀ μ)

include h

/-- the flow at `τ = 0` is the datum. -/
theorem Data.flow_at_zero {t : ℝ} (ht : t ∈ Set.Icc 0 P.T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    P.flow D μ t φ 0 = coeffOf φ := by
  by_cases h0 : t = 0
  · subst h0; exact h.flow_zero hφ
  · have ht' : t ∈ Set.Ioc 0 P.T := ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), ht.2⟩
    have hu : t ∈ Set.Icc 0 t := ⟨ht'.1.le, le_rfl⟩
    obtain ⟨-, h2, -⟩ := h.U_facts ht hφ hu
    rw [sub_self] at h2
    rw [← h2, HRS.Uniform.Q54.prop_self_pos P.hd P.s P.hs0 P.hsd (P.n + 4) P.hn P.R P.MB P.Λ P.VB D ν₀ P.T μ
      h.hA ht' (HRS.Uniform.Q54.dom_smooth hφ)]

theorem Data.flow_comb' {t : ℝ} (ht : t ∈ Set.Ioc 0 P.T) {φ ψ : Torus d → ℝ}
    (hφ : HRS.Uniform.Q54.Dom (P.n + 4) φ) (hψ : HRS.Uniform.Q54.Dom (P.n + 4) ψ) (α β : ℝ) {τ : ℝ}
    (hτ : τ ∈ Set.Icc 0 t) :
    P.flow D μ t (fun x => α * φ x + β * ψ x) τ =
      fun k => (α : ℂ) * P.flow D μ t φ τ k + (β : ℂ) * P.flow D μ t ψ τ k := by
  have hc := HRS.Uniform.Q54.coeffOf_lin hφ.1 hψ.1 α β
  unfold PdeSetup.flow
  rw [hc]
  exact HRS.Uniform.Q54.propagatorCoeff_lin P.hd P.hs0 P.hsd P.hJ1 h.hA ht
    (h.memHsφ hφ) (h.memHsφ hψ) α β hτ

theorem Data.flow_lip_hs {t : ℝ} (ht : t ∈ Set.Ioc 0 P.T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    {j : ℕ} (hj : j + 2 ≤ P.n + 4) {τ τ' : ℝ} (hτ : τ ∈ Set.Icc 0 t) (hτ' : τ' ∈ Set.Icc 0 t) :
    HRS.PDE.hsNorm (j : ℝ) (P.flow D μ t φ τ' - P.flow D μ t φ τ) ≤
      2 * (P.c.Cg j * (P.c.Cop (j + 2) * sobolevNorm ((j : ℝ) + 2) φ)) * |τ' - τ| := by
  have hD := HRS.Uniform.Q54.dom_smooth (J := P.n + 4) hφ
  have hjl : (j : ℝ) ≤ P.lev := by
    have : (j : ℝ) ≤ ((P.n + 4 : ℕ) : ℝ) := by exact_mod_cast (by omega : j ≤ P.n + 4)
    exact this
  have ht0 : t ∈ Set.Icc 0 P.T := ⟨ht.1.le, ht.2⟩
  have a1 := h.flow_adm0 ht0 hφ hτ' hjl
  have a2 := h.flow_adm0 ht0 hφ hτ hjl
  have hAd : Adm (j : ℝ) (P.flow D μ t φ τ' - P.flow D μ t φ τ) := by
    have := a1.comb a2 1 (-1)
    convert this using 1
    funext k; simp [sub_eq_add_neg]
  have hSv : Sv (j : ℝ) (P.flow D μ t φ τ' - P.flow D μ t φ τ) =
      Sv (j : ℝ) (P.flow D μ t φ τ') - Sv (j : ℝ) (P.flow D μ t φ τ) := by
    have := Sv_comb a1 a2 1 (-1)
    have e : (fun k => ((1 : ℝ) : ℂ) * P.flow D μ t φ τ' k + ((-1 : ℝ) : ℂ) * P.flow D μ t φ τ k) =
        P.flow D μ t φ τ' - P.flow D μ t φ τ := by
      funext k; simp [sub_eq_add_neg]
    rw [e] at this
    rw [this]; simp [sub_eq_add_neg]
  have hl := h.flow_lip ht hD hj hτ hτ'
  calc _ ≤ 2 * ‖Sv (j : ℝ) (P.flow D μ t φ τ' - P.flow D μ t φ τ)‖ := hAd.hsNorm_le_Sv
    _ ≤ 2 * ((P.c.Cg j * (P.c.Cop (j + 2) * sobolevNorm ((j : ℝ) + 2) φ)) * |τ' - τ|) := by
        rw [hSv]; exact mul_le_mul_of_nonneg_left hl (by norm_num)
    _ = _ := by ring

/-- Lipschitz dependence on the terminal time at level `j`. -/
theorem Data.lip_flow {t t' : ℝ} (ht : t ∈ Set.Icc 0 P.T) (htt : t' ≤ t) (ht' : 0 ≤ t')
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) {σ : ℝ} (hσ : σ ∈ Set.Icc 0 t') {j : ℕ} (hj1 : 1 ≤ j)
    (hj : j + 2 ≤ P.n + 4) :
    HRS.PDE.hsNorm (j : ℝ) (P.flow D μ t φ (t - σ) - P.flow D μ t' φ (t' - σ)) ≤
      2 * (P.c.Cop j + 1) * (P.c.Cg j * (P.c.Cop (j + 2) * sobolevNorm ((j : ℝ) + 2) φ)) * (t - t') := by
  have hD := HRS.Uniform.Q54.dom_smooth (J := P.n + 4) hφ
  have hLn : 0 ≤ P.c.Cg j * (P.c.Cop (j + 2) * sobolevNorm ((j : ℝ) + 2) φ) :=
    mul_nonneg (P.c.Cg_nonneg j) (mul_nonneg (P.c.Cop_nonneg _) (sobolevNorm_nonneg' _ _))
  set Lj := P.c.Cg j * (P.c.Cop (j + 2) * sobolevNorm ((j : ℝ) + 2) φ) with hLj
  have hc1 : 0 ≤ P.c.Cop j := P.c.Cop_nonneg j
  have hjn : j ≤ P.n + 4 := by omega
  have htt0 : 0 ≤ t - t' := by linarith
  have h0hs : HRS.PDE.hsNorm (j : ℝ) (0 : Coeff d) = 0 := by
    simp [HRS.PDE.hsNorm, hsNormSq]
  rcases htt.eq_or_lt with heq | hlt
  · subst heq
    rw [sub_self, h0hs]
    have : (t' - t') = 0 := sub_self _
    rw [this, mul_zero]
  · have htpos : 0 < t := by linarith
    have htI : t ∈ Set.Ioc 0 P.T := ⟨htpos, ht.2⟩
    have ht'I : t' ∈ Set.Icc 0 P.T := ⟨ht', by linarith [ht.2]⟩
    by_cases h0 : t' = 0
    · subst h0
      have hσ0 : σ = 0 := le_antisymm hσ.2 hσ.1
      subst hσ0
      rw [sub_zero, sub_zero, h.flow_zero hφ, ← h.flow_at_zero ht hφ]
      have := h.flow_lip_hs htI hφ (j := j) hj (τ := 0) (τ' := t) ⟨le_rfl, htpos.le⟩ ⟨htpos.le, le_rfl⟩
      refine this.trans ?_
      rw [sub_zero, abs_of_pos htpos]
      nlinarith [mul_nonneg hLn htpos.le]
    · have ht'pos : 0 < t' := lt_of_le_of_ne ht' (Ne.symm h0)
      have ht'I' : t' ∈ Set.Ioc 0 P.T := ⟨ht'pos, ht'I.2⟩
      have hσt : σ ∈ Set.Icc 0 t := ⟨hσ.1, hσ.2.trans htt⟩
      have ht'm : t' ∈ Set.Icc 0 t := ⟨ht', htt⟩
      obtain ⟨hp1, hp2, hpD⟩ := h.U_facts ht hφ ht'm
      set ψ := propagator D μ t' t φ with hψdef
      obtain ⟨-, hq2, -⟩ := h.U_facts ht hφ hσt
      obtain ⟨-, hr2⟩ := h.flow_prop ht'I' hpD hσ
      have hsg := HRS.PDE.propagator_semigroup P.hd P.s P.hs0 P.hsd (P.n + 4) P.hn P.R P.MB P.Λ P.VB D ν₀
        P.T μ h.hA t htI φ hD.1 hD.2 σ t' hσ.1 hσ.2 hlt
      have eq1 : P.flow D μ t φ (t - σ) = P.flow D μ t' ψ (t' - σ) := by
        rw [← hq2, ← hr2, hsg]
      have hτσ : t' - σ ∈ Set.Icc 0 t' := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
      have eq2 := h.flow_comb' ht'I' hpD hD 1 (-1) hτσ
      have hχD := HRS.Uniform.Q54.dom_closed hpD hD 1 (-1)
      set χ : Torus d → ℝ := fun x => 1 * ψ x + (-1) * φ x with hχ
      have eq3 : P.flow D μ t φ (t - σ) - P.flow D μ t' φ (t' - σ) = P.flow D μ t' χ (t' - σ) := by
        rw [eq1, eq2]; funext k; simp [sub_eq_add_neg]
      rw [eq3]
      refine (h.flow_hsNorm ht'I' hχD hτσ hj1 hjn).trans ?_
      -- the norm of χ
      have hcoef : coeffOf χ = P.flow D μ t φ (t - t') - P.flow D μ t φ 0 := by
        rw [HRS.Uniform.Q54.coeffOf_lin hpD.1 hD.1 1 (-1), hp2, h.flow_at_zero ht hφ]
        funext k; simp [sub_eq_add_neg]
      have hms : MemSobolev (j : ℝ) χ :=
        HRS.PDE.MFAdjoint.memSobolev_mono_idx hχD.2 (by exact_mod_cast hjn)
      have hnorm : sobolevNorm (j : ℝ) χ ≤ 2 * Lj * (t - t') := by
        rw [HRS.PDE.ClassicalPart.sobolevNorm_eq_hsNorm hms, hcoef]
        have := h.flow_lip_hs htI hφ (j := j) hj (τ := 0) (τ' := t - t') ⟨le_rfl, htpos.le⟩
          ⟨htt0, by linarith⟩
        refine this.trans ?_
        rw [sub_zero, abs_of_nonneg htt0]
      calc P.c.Cop j * sobolevNorm (j : ℝ) χ ≤ P.c.Cop j * (2 * Lj * (t - t')) :=
            mul_le_mul_of_nonneg_left hnorm hc1
        _ ≤ 2 * (P.c.Cop j + 1) * Lj * (t - t') := by
            nlinarith [mul_nonneg hLn htt0]

end PdeSetup

end HRS.Uniform.Q54c
