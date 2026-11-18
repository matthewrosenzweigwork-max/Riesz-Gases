import HRS.Equilibrium.Parametrix.PX3aAuxR

/-!
# Packet PX3a auxiliaries S: transposition of conormal kernels
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

theorem conormalL_mono_b {σ : ℝ} {b b'' : ℕ → ℕ} {m : ℕ} {B : ℝ} {F : Torus d → Torus d → ℝ}
    (hB : 0 ≤ B) (h : ∀ c, b c ≤ b'' c) (hF : ConormalL σ b m B F) : ConormalL σ b'' m B F where
  smooth := hF.smooth
  near a c hac X z hz hzr := by
    refine (hF.near a c hac X z hz hzr).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hB
    have h1 : (1 + |Real.log ‖z‖|) ^ b c ≤ (1 + |Real.log ‖z‖|) ^ b'' c :=
      pow_le_pow_right₀ (by linarith [abs_nonneg (Real.log ‖z‖)]) (h c)
    have h2 : 0 ≤ ‖z‖ ^ (-(σ + (c : ℝ))) := Real.rpow_nonneg (norm_nonneg _) _
    nlinarith
  far := hF.far

/-- Transposition of a kernel. -/
def swapK (F : Torus d → Torus d → ℝ) : Torus d → Torus d → ℝ := fun x y => F y x

/-- The swap on `ℝ^d × ℝ^d` as a continuous linear map. -/
def swapCLM (d : ℕ) : Euc d × Euc d →L[ℝ] Euc d × Euc d :=
  (ContinuousLinearMap.snd ℝ (Euc d) (Euc d)).prod (ContinuousLinearMap.fst ℝ (Euc d) (Euc d))

lemma swapCLM_apply (p : Euc d × Euc d) : swapCLM d p = (p.2, p.1) := rfl

lemma norm_swapCLM_le : ‖swapCLM d‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p => ?_
  simp [swapCLM_apply, Prod.norm_def, max_comm]

/-- The reflection `(X, z) ↦ (X, -z)`. -/
def reflCLM (d : ℕ) : Euc d × Euc d →L[ℝ] Euc d × Euc d :=
  (ContinuousLinearMap.fst ℝ (Euc d) (Euc d)).prod (-(ContinuousLinearMap.snd ℝ (Euc d) (Euc d)))

lemma reflCLM_apply (p : Euc d × Euc d) : reflCLM d p = (p.1, -p.2) := rfl

lemma norm_reflCLM_le : ‖reflCLM d‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p => ?_
  simp [reflCLM_apply, Prod.norm_def]

lemma pat_refl {a c : ℕ} (u : Fin a → Euc d) (v : Fin c → Euc d) :
    (fun k => reflCLM d (pat u v k)) = pat u (fun j => -(v j)) := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp [pat, reflCLM_apply]
  · simp [pat, reflCLM_apply]

lemma toChart_swapK (F : Torus d → Torus d → ℝ) (p : Euc d × Euc d) :
    toChart (swapK F) p = toChart F (reflCLM d p) := by
  simp only [toChart, swapK, reflCLM_apply, smul_neg, ← sub_eq_add_neg, sub_neg_eq_add]

lemma lift2_swapK (F : Torus d → Torus d → ℝ) : lift2 (swapK F) = lift2 F ∘ swapCLM d := rfl

lemma norm_comp_clm_open {n : WithTop ℕ∞} {G : Euc d × Euc d → ℝ} {U : Set (Euc d × Euc d)}
    (hU : IsOpen U) (hG : ContDiffOn ℝ n G U) (L : Euc d × Euc d →L[ℝ] Euc d × Euc d) (hL : ‖L‖ ≤ 1)
    {p : Euc d × Euc d} (hp : L p ∈ U) {k : ℕ} (hk : (k : WithTop ℕ∞) ≤ n) :
    ‖iteratedFDeriv ℝ k (G ∘ L) p‖ ≤ ‖iteratedFDeriv ℝ k G (L p)‖ := by
  rw [iteratedFDeriv_comp_clm_of_open_n hU hG L hp hk]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have : ∏ _j : Fin k, ‖L‖ ≤ 1 := by
    rw [Finset.prod_const]; exact pow_le_one₀ (norm_nonneg _) hL
  calc _ ≤ ‖iteratedFDeriv ℝ k G (L p)‖ * 1 :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = _ := mul_one _

lemma eucDist_comm (x y : Torus d) : Torus.eucDist x y = Torus.eucDist y x := by
  unfold Torus.eucDist
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_sub_rev]

theorem conormalL_swap {σ : ℝ} {b : ℕ → ℕ} {m : ℕ} {B : ℝ} {F : Torus d → Torus d → ℝ}
    (hF : ConormalL σ b m B F) : ConormalL σ b m B (swapK F) where
  smooth := by
    rw [lift2_swapK]
    exact hF.smooth.comp (swapCLM d).contDiff.contDiffOn (fun p hp => (Ne.symm hp : _))
  near a c hac X z hz hzr := by
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hzr' : ‖z‖ < 1 / 8 := by unfold r0 at hzr; exact hzr
    have hcd := toChart_contDiffOn_chartU hF
    have hcdac : ContDiffOn ℝ ((a + c : ℕ) : WithTop ℕ∞) (toChart F)
        {p : Euc d × Euc d | 0 < ‖p.2‖ ∧ ‖p.2‖ < 1 / 8} := hcd.of_le (by exact_mod_cast hac)
    have hq : ((X, -z) : Euc d × Euc d) ∈ {p : Euc d × Euc d | 0 < ‖p.2‖ ∧ ‖p.2‖ < 1 / 8} :=
      ⟨by simpa using hzpos, by simpa using hzr'⟩
    have hq' : ((X, z) : Euc d × Euc d) ∈ {p : Euc d × Euc d | 0 < ‖p.2‖ ∧ ‖p.2‖ < 1 / 8} :=
      ⟨hzpos, hzr'⟩
    have hnear := hF.near a c hac X (-z) (neg_ne_zero.mpr hz) (by unfold r0; simpa using hzr')
    rw [norm_neg] at hnear
    have hTB : TB (toChart F) (X, -z) a c (B * (1 + ‖z‖ ^ (-(σ + (c : ℝ))) * (1 + |Real.log ‖z‖|) ^ b c)) :=
      tb_of_norm_le isOpen_chartU hcdac hq (by simpa using hnear)
    have hfun : toChart (swapK F) = toChart F ∘ reflCLM d := funext (toChart_swapK F)
    have hmem : reflCLM d (X, z) ∈ {p : Euc d × Euc d | 0 < ‖p.2‖ ∧ ‖p.2‖ < 1 / 8} := by
      rw [reflCLM_apply]; exact hq
    have hcd' : ContDiffOn ℝ ((a + c : ℕ) : WithTop ℕ∞) (toChart F ∘ reflCLM d)
        {p : Euc d × Euc d | 0 < ‖p.2‖ ∧ ‖p.2‖ < 1 / 8} :=
      hcdac.comp (reflCLM d).contDiff.contDiffOn (fun p hp => by
        rw [reflCLM_apply]; exact ⟨by simpa using hp.1, by simpa using hp.2⟩)
    have hTB' : TB (toChart F ∘ reflCLM d) (X, z) a c
        (B * (1 + ‖z‖ ^ (-(σ + (c : ℝ))) * (1 + |Real.log ‖z‖|) ^ b c)) := by
      intro u v
      rw [iteratedFDeriv_comp_clm_of_open_n isOpen_chartU hcdac (reflCLM d)
        hmem (le_refl _)]
      rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
      have e : (fun k => reflCLM d (pat u v k)) = pat u (fun j => -(v j)) := pat_refl u v
      simp only [e]
      have := hTB u (fun j => -(v j))
      simpa [reflCLM_apply, norm_neg] using this
    rw [hfun]
    have hW0 : 0 ≤ B * (1 + ‖z‖ ^ (-(σ + (c : ℝ))) * (1 + |Real.log ‖z‖|) ^ b c) :=
      (norm_nonneg (mixedDeriv a c (toChart F) X (-z))).trans hnear
    exact norm_le_of_tb isOpen_chartU hcd' hq' hW0 hTB'
  far k hk p hp hdist := by
    rw [lift2_swapK]
    have hmem : swapCLM d p ∈ offDiag d := (Ne.symm hp : _)
    refine (norm_comp_clm_open px2_isOpen_offDiag
      (hF.smooth.of_le (by exact_mod_cast hk)) (swapCLM d) norm_swapCLM_le hmem le_rfl).trans ?_
    refine hF.far k hk (swapCLM d p) hmem ?_
    rw [swapCLM_apply]
    simpa [eucDist_comm] using hdist

end HRS.Parx

end
