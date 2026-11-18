import HRS.MS.SA12V5

/-!
# S.A.12 C17: `periodic_weak_identity`

The exact test identity of a smooth periodic classical solution against `C_c^∞` tests, with the centered-box
indicator on the nonlocal test term.  Contract fix (not a frozen-statement edit): the Pro statement lacks the time
regularity `hTime : PeriodicTimeSmooth T μ`, without which `IsWeakSol.integrable_σ` is not provable
(the slices `μ σ`, `b σ` of `PerSmooth` are otherwise arbitrary in `σ`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd

variable {d : ℕ}

-- BEGIN SA12.C17
/-- C17: exact test identity with the centered-box indicator (with the time regularity hypothesis). -/
theorem periodic_weak_identity (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (T : ℝ) (L : ℝ)
    (γ : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (μ : ℝ → Euc d → ℝ) (V : Euc d → ℝ)
    (b : ℝ → Euc d → Euc d) (hP : PerSmooth s T L γ M ν μ V b) (hTime : PeriodicTimeSmooth T μ)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) (F : ℝ → Euc d → ℝ)
    (hF : IsPerSol 2 L γ M ν μ b (fun _ _ => 0) t F) :
    IsWeakSol (weakOpPer L γ M ν μ b) t (F 0) F := by
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hP.hL
  obtain ⟨hbC1, hbcont⟩ := sa12v_drift hd hs0 hsd hP hTime
  have hsol := hF.sol
  have hIcc : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := Icc_subset_Icc_right ht.2
  have hFs : ∀ σ ∈ Icc (0 : ℝ) t, ContDiff ℝ ∞ (F σ) := fun σ hσ => (hsol.smooth σ hσ).1
  obtain ⟨R, hR⟩ : ∃ R : ℝ → Euc d → ℝ, ∀ σ x, R σ x = ν * Laplacian.laplacian (F σ) x +
      inner ℝ (b σ x) (gradient (F σ) x) + (-perNonlocal L γ M (μ σ) (F σ) x + 0) :=
    ⟨fun σ x => ν * Laplacian.laplacian (F σ) x +
      inner ℝ (b σ x) (gradient (F σ) x) + (-perNonlocal L γ M (μ σ) (F σ) x + 0), fun _ _ => rfl⟩
  have hRc : ContinuousOn (fun p : ℝ × Euc d => R p.1 p.2) (Icc (0 : ℝ) t ×ˢ univ) :=
    (sa12v_R_cont hsol (hbcont.mono (prod_mono hIcc subset_rfl))).congr fun p _ => hR p.1 p.2
  have hslice : ∀ σ ∈ Icc (0 : ℝ) t, ∀ ψ : Euc d → ℝ, IsCcInfty ψ →
      Integrable (fun x => F σ x * weakOpPer L γ M ν μ b σ ψ x) ∧
      ∫ x, F σ x * weakOpPer L γ M ν μ b σ ψ x = ∫ x, ψ x * R σ x := by
    intro σ hσ ψ hψ
    have h := sa12v_slice hd hs0 hsd hL0 hP.hγ M ν (hP.μ_smooth σ (hIcc hσ))
      (hP.μ_periodic σ (hIcc hσ)) (hFs σ hσ) (hF.periodic σ hσ) (hbC1 σ (hIcc hσ)) hψ
    refine ⟨h.1, h.2.trans ?_⟩
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hR, add_zero]
  refine ⟨?_, ?_, ?_⟩
  · intro ψ hψ σ hσ
    refine ⟨?_, (hslice σ hσ ψ hψ).1⟩
    exact Continuous.integrable_of_hasCompactSupport
      ((hFs σ hσ).continuous.mul hψ.1.continuous) hψ.2.mul_left
  · intro ψ hψ
    have hJ := sa12v_J_cont hRc hψ
    refine (hJ.integrableOn_Icc).congr_fun (fun σ hσ => ?_) measurableSet_Icc
    exact ((hslice σ hσ ψ hψ).2).symm
  · intro ψ hψ τ hτ
    have hτ' : τ ∈ Icc (0 : ℝ) t := hτ
    have hsub : Icc (0 : ℝ) τ ⊆ Icc (0 : ℝ) t := Icc_subset_Icc_right hτ.2
    -- pointwise fundamental theorem of calculus
    have hFjoint : ContinuousOn (fun p : ℝ × Euc d => F p.1 p.2) (Icc (0 : ℝ) t ×ˢ univ) := by
      have := hsol.contF 0 (fun i => i.elim0)
      simpa [sa12v_pd0] using this
    have hftc : ∀ x : Euc d, F τ x - F 0 x = ∫ σ in (0 : ℝ)..τ, R σ x := by
      intro x
      have hmaps : ∀ σ ∈ Icc (0 : ℝ) t, (σ, x) ∈ Icc (0 : ℝ) t ×ˢ (univ : Set (Euc d)) :=
        fun σ hσ => ⟨hσ, mem_univ _⟩
      refine sa12v_ftc (φ := fun σ => F σ x) (r := fun σ => R σ x) ?_ ?_ ?_ τ hτ'
      · exact hFjoint.comp (continuous_id.prodMk continuous_const).continuousOn hmaps
      · exact hRc.comp (continuous_id.prodMk continuous_const).continuousOn hmaps
      · intro σ hσ
        have h := hsol.deriv_t 0 (by norm_num) (fun i : Fin 0 => i.elim0) x σ hσ
        simp only [sa12v_pd0] at h
        refine h.congr_deriv ?_
        rw [hR]
    -- integrability of the two boundary terms
    have hI : ∀ σ ∈ Icc (0 : ℝ) t, Integrable (fun x => ψ x * F σ x) := fun σ hσ =>
      Continuous.integrable_of_hasCompactSupport (hψ.1.continuous.mul (hFs σ hσ).continuous) hψ.2.mul_right
    have h1 : ∫ x, ψ x * (F τ x - F 0 x) = (∫ x, ψ x * F τ x) - ∫ x, ψ x * F 0 x := by
      have := integral_sub (hI τ hτ') (hI 0 ⟨le_rfl, ht.1.le⟩)
      simp only [mul_sub]
      exact this
    have h2 : ∫ x, ψ x * (F τ x - F 0 x) = ∫ σ in Icc (0 : ℝ) τ, ∫ x, ψ x * R σ x := by
      simp_rw [hftc]
      exact sa12v_time_fubini hRc hψ hτ'
    have h3 : ∫ σ in Icc (0 : ℝ) τ, ∫ x, ψ x * R σ x =
        ∫ σ in Icc (0 : ℝ) τ, ∫ x, F σ x * weakOpPer L γ M ν μ b σ ψ x := by
      refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
      exact ((hslice σ (hsub hσ) ψ hψ).2).symm
    have h4 : ∫ x, F τ x * ψ x = ∫ x, ψ x * F τ x :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
    have h5 : ∫ x, F 0 x * ψ x = ∫ x, ψ x * F 0 x :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
    show ∫ x, F τ x * ψ x = (∫ x, F 0 x * ψ x) + _
    rw [h4, h5, ← h3, ← h2, h1]
    ring
-- END SA12.C17

end HRS.MH.AdjointRd.Phase2SA12Construction
