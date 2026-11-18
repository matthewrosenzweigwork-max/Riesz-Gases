import HRS.PDE.MovFAux8

/-!
# MOVF Aux9: bridge A, `IsSmoothPositiveTrajectory ⇒ MovTraj` (from Proposition 5.1)
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movf_isC12_empty {T : ℝ} (hT : T < 0) (ρ : ℝ → Torus d → ℝ) :
    IsC12Test T ρ (fun _ _ => 0) := by
  haveI : IsEmpty (Set.Icc (0 : ℝ) T) := ⟨fun r => by have := r.2; linarith [this.1, this.2]⟩
  refine ⟨fun r hr => absurd (hr.1.trans hr.2) (not_le.2 hT), fun j _ => ?_,
    fun x r hr => absurd (hr.1.trans hr.2).le (not_le.2 hT), ?_⟩
  · exact (continuous_const (y := (0 : ContinuousMultilinearMap ℝ (fun _ : Fin j => Euc d) ℝ))).congr
      (fun p => isEmptyElim p)
  · exact (continuous_const (y := (0 : ℝ))).congr (fun p => isEmptyElim p)

theorem movf_traj_of_global (s β : ℝ) (V ρ₀ : Torus d → ℝ) (ρ : ℝ → Torus d → ℝ) (hs0 : 0 ≤ s)
    (hsd : s < d) (hβ : 0 < β) (hV : Torus.IsSmooth V) (hρ₀ : SmoothPosDensity ρ₀)
    (hglobal : ∀ K : ℕ, (d : ℝ) / 2 + 6 < K →
      ∃ ρc : ℝ → (Lattice d → ℂ), PDE.IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc ∧
        ∀ t, 0 ≤ t → PDE.mfPath ρc t = ρ t)
    (T : ℝ) : MovTraj (PDE.mfData d s hs0 hsd V β hβ) T ρ := by
  have hd1 : 1 ≤ d := by
    have : (0 : ℝ) < d := lt_of_le_of_lt hs0 hsd
    exact_mod_cast this
  set K : ℕ := ⌊(d : ℝ) / 2 + 6⌋₊ + 1 with hKdef
  have hK := movf_K_spec d
  have H := movf_finiteRegHyp hs0 hsd hβ hV hρ₀ K hK
  obtain ⟨ρc, hρc, hρ⟩ := hglobal K hK
  obtain ⟨Ce, hCe⟩ := PDE.toFun_isCk_le (d := d) 2 (K : ℝ) (by
    have : (d : ℝ) / 2 + 6 < K := hK
    linarith)
  have hβm : β ∈ Set.Icc β β := ⟨le_rfl, le_rfl⟩
  have hreal : ∀ t, 0 ≤ t → PDE.IsRealCoeff (ρc t) := fun t ht =>
    PDE.MFGlobal.isRealCoeff_of_isMFSolutionHK hd1 s β β K V ρ₀ H β hβm ρc hρc t ht
  have hmem : ∀ t, 0 ≤ t → PDE.MemHs (K : ℝ) (ρc t) := fun t ht => hρc.cont.1 t ht
  have hKd : (d : ℝ) / 2 < K := by have : (d : ℝ) / 2 + 6 < K := hK; linarith
  have hck : ∀ t, 0 ≤ t → Torus.IsCk 2 (ρ t) := fun t ht => by
    rw [← hρ t ht]; exact (hCe (ρc t) (hmem t ht) (hreal t ht)).1
  obtain ⟨c₀, Λ₂, hc₀, hbound⟩ := movf_traj_uniform s β V ρ₀ ρ hs0 hsd hβ hV hρ₀ hglobal
  have hmf : IsMeanFieldSolution (PDE.mfData d s hs0 hsd V β hβ) T ρ := by
    have hT' : 0 < max T 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have := PDE.finite_reg_isMeanFieldSolution hd1 s β β K V ρ₀ H β hβm ρc hρc (max T 1) hT'
    exact movf_mf_congr (le_max_left _ _) (fun t ht => hρ t ht.1) this
  refine ⟨rfl, inv_pos.2 hβ, ?_, hmf, fun r hr => hck r hr.1, ⟨Λ₂, fun r hr => (hbound r hr.1).2⟩,
    fun r hr x => lt_of_lt_of_le hc₀ ((hbound r hr.1).1 x), ?_⟩
  · exact mova_isCk_two_of_smooth hV
  · rcases lt_or_ge T 0 with hT | hT
    · exact ⟨_, movf_isC12_empty hT ρ⟩
    · refine movf_isC12_core _ rfl (mova_isCk_two_of_smooth hV) hT hmf (fun r hr => hck r hr.1) ?_
      have hrate : ∀ r₀ : Set.Icc (0 : ℝ) T, Tendsto (fun r : Set.Icc (0 : ℝ) T =>
          Torus.cbNorm 2 (fun x => ρ r.1 x - ρ r₀.1 x)) (𝓝 r₀) (𝓝 0) := by
        intro r₀
        have h1 := hρc.cont.2 r₀.1 r₀.2.1
        have h2 : Tendsto (fun r : Set.Icc (0 : ℝ) T => (r.1 : ℝ)) (𝓝 r₀) (𝓝[Set.Ici 0] r₀.1) :=
          tendsto_nhdsWithin_iff.2 ⟨continuous_subtype_val.tendsto _, Eventually.of_forall fun r => r.2.1⟩
        have h3 := ((h1.comp h2).const_mul Ce)
        rw [mul_zero] at h3
        refine squeeze_zero (fun r => KernelGrad.cbNorm_nonneg' _ 2) (fun r => ?_) h3
        have hr0 := r.2.1
        have e : (fun x => ρ r.1 x - ρ r₀.1 x) = PDE.toFun (ρc r.1 - ρc r₀.1) := by
          funext x
          rw [PDE.MFApriori.Aux.toFun_sub _ _ (PDE.summable_norm_of_memHs (K : ℝ) hKd _ (hmem _ hr0))
            (PDE.summable_norm_of_memHs (K : ℝ) hKd _ (hmem _ r₀.2.1)), ← hρ _ hr0, ← hρ _ r₀.2.1]
          rfl
        rw [e]
        exact (hCe _ (PDE.MFApriori.Aux.memHs_sub (hmem _ hr0) (hmem _ r₀.2.1))
          (PDE.MFVelocity.isRealCoeff_sub' (hreal _ hr0) (hreal _ r₀.2.1))).2
      exact fun j hj => movf_joint_cont (fun r hr => hck r hr.1) hrate j hj

end HRS

end
