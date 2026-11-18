import HRS.Equilibrium.Parametrix.PX4aAuxO

/-!
# Packet PX4a auxiliaries P: the `z`-derivative of the three potentials at a point `z0 ≠ 0`
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

section Deriv

variable {s : ℝ} {k : Euc d → ℝ}

lemma dirD_zero_of_far {g : Euc d × Euc d → ℝ} (hz : ∀ X w : Euc d, 1 / 32 < ‖w‖ → g (X, w) = 0)
    (e : Euc d) (X w : Euc d) (hw : 1 / 32 < ‖w‖) : dirD ((0 : Euc d), e) g (X, w) = 0 := by
  have hev : g =ᶠ[𝓝 (X, w)] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_norm.comp continuous_snd)).mem_nhds
      (show (1 / 32 : ℝ) < ‖((X, w) : Euc d × Euc d).2‖ from hw)] with p hp
    exact hz p.1 p.2 hp
  unfold dirD
  rw [hev.fderiv_eq]
  simp

lemma kPot_slice_deriv (hd : 2 ≤ d) (hk : LocKer d s k) {σ : ℝ} (hσ : σ < (d : ℝ) - 1) {b m : ℕ}
    {A : ℝ} (hA : 0 ≤ A) {g : Euc d × Euc d → ℝ} (h : SrcCls d σ b (m + 1) A g)
    (hz : ∀ X w : Euc d, 1 / 32 < ‖w‖ → g (X, w) = 0) (Y z0 : Euc d) (hz0 : z0 ≠ 0) :
    ∃ D : Euc d →L[ℝ] ℝ, HasFDerivAt (fun z => kPot d k g (Y, z)) D z0 ∧
      ∀ e : Euc d, D e = kPot d k (dirD ((0 : Euc d), e) g) (Y, z0) := by
  have hd1 : 1 ≤ d := by omega
  have hσd : σ < d := by linarith
  by_cases hzr : ‖z0‖ < 1 / 8
  · have hpos : 0 < ‖z0‖ := norm_pos_iff.mpr hz0
    have hcd := kPot_contDiffOn hd1 hk hσd hA h
    have hq : ((Y, z0) : Euc d × Euc d) ∈ {p : Euc d × Euc d | 0 < ‖p.2‖ ∧ ‖p.2‖ < 1 / 8} := ⟨hpos, hzr⟩
    have hcat : ContDiffAt ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (kPot d k g) (Y, z0) :=
      hcd.contDiffAt (isOpen_chartU.mem_nhds hq)
    have hdiff : DifferentiableAt ℝ (kPot d k g) (Y, z0) :=
      hcat.differentiableAt (by exact_mod_cast (Nat.succ_ne_zero m))
    have hsl : HasFDerivAt (fun z => kPot d k g (Y, z))
        ((fderiv ℝ (kPot d k g) (Y, z0)).comp ((0 : Euc d →L[ℝ] Euc d).prod (ContinuousLinearMap.id ℝ (Euc d)))) z0 :=
      hdiff.hasFDerivAt.comp z0 ((hasFDerivAt_const Y z0).prodMk (hasFDerivAt_id z0))
    refine ⟨_, hsl, fun e => ?_⟩
    have e1 : ((fderiv ℝ (kPot d k g) (Y, z0)).comp ((0 : Euc d →L[ℝ] Euc d).prod (ContinuousLinearMap.id ℝ (Euc d)))) e =
        dirD ((0 : Euc d), e) (kPot d k g) (Y, z0) := by simp [dirD]
    rw [e1]
    exact kPot_dirD hd hk hσ hA h hpos hzr Y z0 rfl e
  · push_neg at hzr
    have hev : (fun z => kPot d k g (Y, z)) =ᶠ[𝓝 z0] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds
        (show (1 / 16 : ℝ) < ‖z0‖ by linarith)] with z hz'
      exact kPot_zero_of_far hk (fun X w hw => hz X w hw) Y z (by
        have : (1 / 16 : ℝ) < ‖z‖ := hz'
        linarith)
    refine ⟨0, (hasFDerivAt_const (0 : ℝ) z0).congr_of_eventuallyEq hev, fun e => ?_⟩
    simp only [ContinuousLinearMap.zero_apply]
    symm
    unfold kPot
    refine integral_eq_zero_of_ae (Eventually.of_forall fun w => ?_)
    exact kernel_mul_src_zero hk (fun X w' hw' => dirD_zero_of_far hz e X w' hw') Y z0 (by linarith) w

lemma Lam_deriv (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {σ : ℝ} (hσ : σ < (d : ℝ) - 1) {b m : ℕ}
    {A : ℝ} (hA : 0 ≤ A) {g : Euc d × Euc d → ℝ} (h : SrcCls d σ b (m + 1) A g) (Y z0 : Euc d) :
    ∃ D : Euc d →L[ℝ] ℝ, HasFDerivAt (fun z => kPot d (Lam d s) g (Y, z)) D z0 ∧
      ∀ e : Euc d, D e = kPot d (Lam d s) (dirD ((0 : Euc d), e) g) (Y, z0) := by
  have hd1 : 1 ≤ d := by omega
  have hσd : σ < d := by linarith
  have hΛ : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (Lam d s) := by
    exact_mod_cast Lam_contDiff hd hs0 hsd ((m + 1 : ℕ) : ℕ∞)
  have hΛb : ∀ i ≤ m + 1, ∃ B : ℝ, ∀ y, ‖iteratedFDeriv ℝ i (Lam d s) y‖ ≤ B := fun i _ => by
    obtain ⟨M0, -, hM0⟩ := Lam_bdd hd hs0 hsd i
    exact ⟨M0, hM0⟩
  obtain ⟨hcd, -, -⟩ := kPot_far_FL hd1 hΛ hΛb hσd h
  have hdiff : DifferentiableAt ℝ (kPot d (Lam d s) g) (Y, z0) :=
    (hcd.differentiable (by exact_mod_cast (Nat.succ_ne_zero m))) _
  have hsl : HasFDerivAt (fun z => kPot d (Lam d s) g (Y, z))
      ((fderiv ℝ (kPot d (Lam d s) g) (Y, z0)).comp ((0 : Euc d →L[ℝ] Euc d).prod (ContinuousLinearMap.id ℝ (Euc d)))) z0 :=
    hdiff.hasFDerivAt.comp z0 ((hasFDerivAt_const Y z0).prodMk (hasFDerivAt_id z0))
  refine ⟨_, hsl, fun e => ?_⟩
  have e1 : ((fderiv ℝ (kPot d (Lam d s) g) (Y, z0)).comp ((0 : Euc d →L[ℝ] Euc d).prod (ContinuousLinearMap.id ℝ (Euc d)))) e =
      dirD ((0 : Euc d), e) (kPot d (Lam d s) g) (Y, z0) := by simp [dirD]
  rw [e1]
  exact kPot_far_dirD hd hΛ hΛb hσ hA h Y z0 e

lemma farConv_deriv (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {M : ℕ} {S : Euc d × Euc d → ℝ}
    (hS : ContDiff ℝ ((M + 1 : ℕ) : WithTop ℕ∞) S) {N : ℕ → ℝ}
    (hN : ∀ j ≤ M + 1, ∀ p : Euc d × Euc d, ‖iteratedFDeriv ℝ j S p‖ ≤ N j) (Y z0 : Euc d) :
    ∃ D : Euc d →L[ℝ] ℝ, HasFDerivAt (fun z => farConv d s S (Y, z)) D z0 ∧
      ∀ e : Euc d, D e = farConv d s (dirD ((0 : Euc d), e) S) (Y, z0) := by
  obtain ⟨hcd, -, hform, hint⟩ := farConv_smooth hd hs0 hsd hS hN
  have hdiff : DifferentiableAt ℝ (farConv d s S) (Y, z0) :=
    (hcd.differentiable (by exact_mod_cast (Nat.succ_ne_zero M))) _
  have hsl : HasFDerivAt (fun z => farConv d s S (Y, z))
      ((fderiv ℝ (farConv d s S) (Y, z0)).comp ((0 : Euc d →L[ℝ] Euc d).prod (ContinuousLinearMap.id ℝ (Euc d)))) z0 :=
    hdiff.hasFDerivAt.comp z0 ((hasFDerivAt_const Y z0).prodMk (hasFDerivAt_id z0))
  refine ⟨_, hsl, fun e => ?_⟩
  have e1 : ((fderiv ℝ (farConv d s S) (Y, z0)).comp ((0 : Euc d →L[ℝ] Euc d).prod (ContinuousLinearMap.id ℝ (Euc d)))) e =
      dirD ((0 : Euc d), e) (farConv d s S) (Y, z0) := by simp [dirD]
  rw [e1]
  have hL : iteratedFDeriv ℝ (0 + 1) (farConv d s S) (Y, z0)
      (pat (Fin.elim0 : Fin 0 → Euc d) (fun _ : Fin 1 => e)) = dirD ((0 : Euc d), e) (farConv d s S) (Y, z0) :=
    iteratedFDeriv_one_pat _ _ _
  rw [← hL, hform (0 + 1) (by omega) (Y, z0)]
  have hI := hint (0 + 1) (by omega) (Y, z0)
  rw [ContinuousMultilinearMap.integral_apply hI]
  unfold farConv
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [iteratedFDeriv_one_pat]

end Deriv

end HRS.Parx

end
