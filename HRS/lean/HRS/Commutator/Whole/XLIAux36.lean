import HRS.Commutator.Whole.XLIAux35

/-!
# X-LI part 36: square function bounds for all `p > 1` for the Bessel and `ρ̃` dyadic families
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- uniform derivative bounds for a jointly smooth family of profiles supported in `|η| ≤ 2` -/
lemma param_bound (G : ℝ × 𝔼 → ℂ) (hgd : ContDiff ℝ ∞ G) (hs : ∀ (ε : ℝ) (η : 𝔼), 2 < ‖η‖ → G (ε, η) = 0)
    (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ 4 → ∀ η : 𝔼,
      ‖iteratedFDeriv ℝ n (fun η : 𝔼 => G (ε, η)) η‖ ≤ B := by
  have hK : IsCompact (Set.Icc (0 : ℝ) 4 ×ˢ closedBall (0 : 𝔼) 2) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hcont : Continuous (iteratedFDeriv ℝ n G) :=
    hgd.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  refine ⟨max C 0, hC0, fun ε hε0 hε4 η => ?_⟩
  by_cases hη : ‖η‖ ≤ 2
  · have e : (fun η : 𝔼 => G (ε, η)) = (fun z : ℝ × 𝔼 => G ((ε, (0 : 𝔼)) + z)) ∘
        (ContinuousLinearMap.inr ℝ ℝ 𝔼) := by
      funext η'
      simp
    have hfd : ContDiff ℝ ∞ (fun z : ℝ × 𝔼 => G ((ε, (0 : 𝔼)) + z)) :=
      hgd.comp (contDiff_const.add contDiff_id)
    rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _ hfd η (by exact_mod_cast le_top)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have h1 : ∏ i : Fin n, ‖ContinuousLinearMap.inr ℝ ℝ 𝔼‖ ≤ 1 := by
      rw [Finset.prod_const]
      exact pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_inr_le_one ℝ ℝ 𝔼)
    have h2 : ‖iteratedFDeriv ℝ n (fun z : ℝ × 𝔼 => G ((ε, (0 : 𝔼)) + z))
        (ContinuousLinearMap.inr ℝ ℝ 𝔼 η)‖ ≤ max C 0 := by
      rw [iteratedFDeriv_comp_add_left]
      have hmem : (ε, (0 : 𝔼)) + (ContinuousLinearMap.inr ℝ ℝ 𝔼 η) ∈
          Set.Icc (0 : ℝ) 4 ×ˢ closedBall (0 : 𝔼) 2 := by
        refine ⟨⟨by simpa using hε0, by simpa using hε4⟩, ?_⟩
        simpa using hη
      exact (hC _ hmem).trans (le_max_left _ _)
    calc _ ≤ ‖iteratedFDeriv ℝ n (fun z : ℝ × 𝔼 => G ((ε, (0 : 𝔼)) + z))
          (ContinuousLinearMap.inr ℝ ℝ 𝔼 η)‖ * ∏ i : Fin n, ‖ContinuousLinearMap.inr ℝ ℝ 𝔼‖ := by
          exact le_rfl
      _ ≤ max C 0 * 1 := by gcongr
      _ = max C 0 := mul_one _
  · push Not at hη
    have : (fun η : 𝔼 => G (ε, η)) =ᶠ[𝓝 η] fun _ => (0 : ℂ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hη] with y hy
      exact hs ε y hy
    have h2 := (this.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds
    rw [h2, iteratedFDeriv_fun_zero]
    simpa using hC0

/-- the jointly smooth gradient profile of the Bessel family in direction `m` -/
def thBgrad (s : ℝ) (m : 𝔼) (p : ℝ × 𝔼) : ℂ :=
  (2 * Real.pi * Complex.I * ((inner ℝ p.2 m : ℝ) : ℂ)) * thB s p.1 p.2

lemma thBgrad_contDiff (s : ℝ) (m : 𝔼) : ContDiff ℝ ∞ (thBgrad s m) := by
  unfold thBgrad
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × 𝔼 => ((inner ℝ p.2 m : ℝ) : ℂ)) := by
    have : ContDiff ℝ ∞ (fun p : ℝ × 𝔼 => (inner ℝ p.2 m : ℝ)) :=
      (((innerSL ℝ).flip m).contDiff).comp contDiff_snd
    exact Complex.ofRealCLM.contDiff.comp this
  exact (contDiff_const.mul h1).mul (thBj_contDiff s)

lemma symFam_grad_Ths (s : ℝ) (m : 𝔼) : SymFam 2 (gradS (Ths s : ℤ → 𝔼 → ℂ) m) := by
  choose B hB0 hB using fun n : ℕ => param_bound (d := d) (thBgrad s m) (thBgrad_contDiff s m)
    (fun ε η h => by unfold thBgrad; rw [thB_supp s ε h, mul_zero]) n
  refine ⟨fun j => ?_, fun j η h => ?_, ∑ n ∈ Finset.range (d + 2), B n,
    Finset.sum_nonneg fun n _ => hB0 n, fun j i hi η => ?_⟩
  · have : (gradS (Ths s : ℤ → 𝔼 → ℂ) m j) = fun η => thBgrad s m (epsj j, η) := rfl
    rw [this]
    exact (thBgrad_contDiff s m).comp ((contDiff_const (c := epsj j)).prodMk
      (contDiff_id (𝕜 := ℝ) (E := 𝔼)))
  · show (2 * Real.pi * Complex.I * ((inner ℝ η m : ℝ) : ℂ)) * thB s (epsj j) η = 0
    rw [thB_supp s _ h, mul_zero]
  · have : (gradS (Ths s : ℤ → 𝔼 → ℂ) m j) = fun η => thBgrad s m (epsj j, η) := rfl
    rw [this]
    refine (hB i _ (epsj_nonneg j) (epsj_le j) η).trans ?_
    exact Finset.single_le_sum (f := B) (fun n _ => hB0 n) (by simpa [Nat.lt_succ_iff] using hi)

lemma symFam_grad_rhoT (m : 𝔼) : SymFam 4 (gradS (fun _ : ℤ => (rhoT : 𝔼 → ℂ)) m) := by
  have h := SymFam.const (d := d) (R := 4)
    (θ := fun η : 𝔼 => (2 * Real.pi * Complex.I * ((inner ℝ η m : ℝ) : ℂ)) * rhoT η)
    (by
      have h1 : ContDiff ℝ ∞ (fun η : 𝔼 => ((inner ℝ η m : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp (((innerSL ℝ).flip m).contDiff)
      exact (contDiff_const.mul h1).mul rhoT_contDiff)
    (fun η hη => by rw [rhoT_eq_zero_of_ge hη.le, mul_zero])
  exact h

/-- **square function bound for the Bessel dyadic family, all `p = 2s > 1`** -/
theorem E1At_Ths (hd : 1 ≤ d) (α : ℝ) {s : ℝ} (hs : 1 / 2 < s) :
    E1At (fun j => dK (Ths α : ℤ → 𝔼 → ℂ) j) s := by
  by_cases h2 : 2 ≤ s
  · exact E1_gt hd (isLPRep_Ths α) (by linarith)
  · push Not at h2
    have h4 : E1At (fun j => dK (Ths α : ℤ → 𝔼 → ℂ) j) 2 :=
      E1_gt hd (isLPRep_Ths α) (by norm_num)
    obtain ⟨H, hH, hHorm⟩ := hormK_dK (symFam_Ths α)
      (fun l => symFam_grad_Ths α (EuclideanSpace.single l (1 : ℝ)))
    exact E1At_of_horm hd (fun j => (dK_continuous (symFam_Ths α) j).measurable)
      (fun j => dK_integrable (symFam_Ths α) j) h4 hH hHorm hs h2

/-- **square function bound for the `ρ̃`-dyadic family, all `p = 2s > 1`** -/
theorem E1At_rhoT (hd : 1 ≤ d) {s : ℝ} (hs : 1 / 2 < s) :
    E1At (fun j => symK (rhoT : 𝔼 → ℂ) j) s := by
  by_cases h2 : 2 ≤ s
  · exact E1_gt hd isLPRep_rhoT (by linarith)
  · push Not at h2
    have h4 : E1At (fun j => symK (rhoT : 𝔼 → ℂ) j) 2 := E1_gt hd isLPRep_rhoT (by norm_num)
    obtain ⟨H, hH, hHorm⟩ := hormK_dK (symFam_rhoT (d := d))
      (fun l => symFam_grad_rhoT (EuclideanSpace.single l (1 : ℝ)))
    exact E1At_of_horm hd
      (fun j => (symK_continuous rhoT_contDiff rhoT_cs j).measurable)
      (fun j => symK_integrable rhoT_contDiff rhoT_cs j) h4 hH hHorm hs h2

end HRS.Commutator.Whole.XLI
