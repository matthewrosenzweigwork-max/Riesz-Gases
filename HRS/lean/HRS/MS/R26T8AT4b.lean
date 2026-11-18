import HRS.MS.R26T8AT4a

/-!
# S8.2 T8A T4b: linearity in `f` of `HSource` and of the iterated defect terms (off the diagonal)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_T4_hSource_lin {f g : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (c : ℝ) :
    hSource (f + c • g) = fun x y => hSource f x y + c * hSource g x y := by
  funext x y
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hgr : ∀ z, gradient (f + c • g) z = gradient f z + c • gradient g z := fun z => by
    have h := r26t8a_V1_gradient_add (f := f) (g := fun w => c * g w) (x := z) (hfd z)
      ((hgd z).const_mul c)
    rw [r26t8a_T3_gradient_smul (hgd z) c] at h
    exact h
  unfold hSource commutatorKernel
  rw [hgr x, hgr y]
  have : gradient f x + c • gradient g x - (gradient f y + c • gradient g y) =
      (gradient f x - gradient f y) + c • (gradient g x - gradient g y) := by module
  rw [this, inner_add_left, inner_smul_left]
  simp

theorem r26t8a_T4_HSource_lin (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (rho : Euc d → ℝ)
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi)
    {f g : Euc d → ℝ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hf : TestBound (testOrder d) A f)
    (hg : TestBound (testOrder d) B g) (c : ℝ) (x y : Euc d) :
    HSource (HRS.Whole.withDensityReal rho) (f + c • g) x y =
      HSource (HRS.Whole.withDensityReal rho) f x y + c * HSource (HRS.Whole.withDensityReal rho) g x y := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : criticalS d < d := by unfold criticalS; linarith
  obtain ⟨Ch, hCh0, hCh⟩ := r26t8a_p17_h_conormal hd 0
  have hf' : TestBound (0 + 2) A f := ⟨hf.1, fun j hj hjk x => hf.2 j hj (by unfold testOrder; omega) x⟩
  have hg' : TestBound (0 + 2) B g := ⟨hg.1, fun j hj hjk x => hg.2 j hj (by unfold testOrder; omega) x⟩
  obtain ⟨r1, c1, a1⟩ := r26t8a_T1_integrability hd a beta 0 (criticalS d) ha hbeta le_rfl hsd rho hrho hchi
    (mul_nonneg hCh0 hA) (hCh A hA f hf')
  obtain ⟨r2, c2, a2⟩ := r26t8a_T1_integrability hd a beta 0 (criticalS d) ha hbeta le_rfl hsd rho hrho hchi
    (mul_nonneg hCh0 hB) (hCh B hB g hg')
  unfold HSource
  rw [r26t8a_T4_hSource_lin hf.1 hg.1 c, r26t8a_T1_center_lin _ c r1 r2 c1 c2 a1 a2 x y]
  ring

theorem r26t8a_T4_localNewton_congr (hd : 2 ≤ d) (rho : Euc d → ℝ) (nu : ℝ) (chi : Euc d → ℝ)
    {F1 F2 : Euc d → Euc d → ℝ} (h : ∀ x y, x ≠ y → F1 x y = F2 x y) {x y : Euc d} (hxy : x ≠ y) :
    localNewton (HRS.Whole.withDensityReal rho) nu chi F1 x y = localNewton (HRS.Whole.withDensityReal rho) nu chi F2 x y := by
  unfold localNewton
  exact r26t8a_T1_center_congr hd rho (fun x y _ => r26t8a_T2_rawNewton_congr hd nu chi h x y) hxy

set_option maxHeartbeats 6400000 in
theorem r26t8a_T4_term_lin (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (chi : Euc d → ℝ)
    (hchi : NewtonCutoff chi) (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    {f g : Euc d → ℝ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hf : TestBound (testOrder d) A f)
    (hg : TestBound (testOrder d) B g) (c : ℝ) :
    ∀ j : ℕ, j ≤ iterationCount d → ∀ x y : Euc d, x ≠ y →
      r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi (f + c • g) j x y =
        r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f j x y +
          c * r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi g j x y := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hcrit_lt : criticalS d < d := by unfold criticalS; linarith
  have hcrit_nn : 0 ≤ criticalS d := by unfold criticalS; linarith
  choose Cn hCn0 hCn using r26t8a_T4_iter d hd a beta ha hbeta chi hchi
  have hnu : (critCoeff d a beta rho).ν = beta⁻¹ := r26t8a_critCoeff_nu a beta rho
  intro j
  induction j with
  | zero => intro _ x y _; exact r26t8a_T4_HSource_lin hd a beta ha hbeta rho hrho hchi hA hB hf hg c x y
  | succ j ih =>
    intro hj x y hxy
    have hjL : j < iterationCount d := hj
    have ih' := ih (by omega)
    obtain ⟨-, hTf⟩ := hCn j hjL.le rho hrho f A hA hf
    obtain ⟨-, hTg⟩ := hCn j hjL.le rho hrho g B hB hg
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hσd : criticalS d - (j : ℝ) / 2 < d := by linarith
    obtain ⟨CZ, hCZ0, hCZ⟩ := r26t8a_local_newton_bound_same d hd 8 0 a beta (2 * (j : ℝ))
      (criticalS d - (j : ℝ) / 2) ha hbeta (by linarith) hσd chi hchi
    have hT8f := r26t8a_conormal_mono (k := 8) (by omega) hTf
    have hT8g := r26t8a_conormal_mono (k := 8) (by omega) hTg
    obtain ⟨-, -, hQf⟩ := hCZ rho hrho _ (Cn j * A) (mul_nonneg (hCn0 j) hA) hT8f
    obtain ⟨-, -, hQg⟩ := hCZ rho hrho _ (Cn j * B) (mul_nonneg (hCn0 j) hB) hT8g
    have hQf2 : Conormal 2 1 (2 * (j : ℝ)) (criticalS d - (j : ℝ) / 2 - 2) (CZ * (Cn j * A))
        (localNewton (HRS.Whole.withDensityReal rho) beta⁻¹ chi
          (r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f j)) :=
      r26t8a_conormal_mono (by norm_num) hQf
    have hQg2 : Conormal 2 1 (2 * (j : ℝ)) (criticalS d - (j : ℝ) / 2 - 2) (CZ * (Cn j * B))
        (localNewton (HRS.Whole.withDensityReal rho) beta⁻¹ chi
          (r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi g j)) :=
      r26t8a_conormal_mono (by norm_num) hQg
    have e1 : ∀ h : Euc d → ℝ, r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi h (j + 1) =
        newtonDefect (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi
          (r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi h j) := fun h =>
      Function.iterate_succ_apply' _ _ _
    rw [e1, e1 f, e1 g]
    show _ + pairA _ _ (localNewton _ (critCoeff d a beta rho).ν chi _) x y = (_ + pairA _ _ (localNewton _ (critCoeff d a beta rho).ν chi _) x y) +
      c * (_ + pairA _ _ (localNewton _ (critCoeff d a beta rho).ν chi _) x y)
    rw [hnu, ih' x y hxy]
    have hloc : ∀ x y : Euc d, x ≠ y →
        localNewton (HRS.Whole.withDensityReal rho) beta⁻¹ chi
          (r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi (f + c • g) j) x y =
        localNewton (HRS.Whole.withDensityReal rho) beta⁻¹ chi
          (r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f j) x y +
        c * localNewton (HRS.Whole.withDensityReal rho) beta⁻¹ chi
          (r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi g j) x y := by
      intro x y hxy
      rw [r26t8a_T4_localNewton_congr hd rho beta⁻¹ chi
        (F2 := fun x y => r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f j x y +
          c * r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi g j x y)
        (fun x y hxy => ih' x y hxy) hxy]
      exact r26t8a_T2_localNewton_lin hd a beta (2 * (j : ℝ)) (criticalS d - (j : ℝ) / 2) ha hbeta (by linarith) hσd
        _ _ rho hrho hchi (mul_nonneg (hCn0 j) hA) (mul_nonneg (hCn0 j) hB) hTf hTg c hxy
    rw [r26t8a_U1_pairA_congr hd (critCoeff d a beta rho) rho hloc hxy,
      r26t8a_T3_pairA_lin hd a beta (2 * (j : ℝ)) (criticalS d - (j : ℝ) / 2) ha hbeta (by linarith) hσd rho hrho hchi
        (mul_nonneg hCZ0 (mul_nonneg (hCn0 j) hA)) (mul_nonneg hCZ0 (mul_nonneg (hCn0 j) hB)) hQf2 hQg2 c hxy]
    ring

end HRS.MS.R26T8A
