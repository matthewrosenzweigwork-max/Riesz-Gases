import HRS.MS.R2SeAux38
import HRS.MS.R2SeAux31

/-!
# S9.9 `r2_static_edgeworth`, packet 39: the uniform limit of the quadratic series

Worker S99, namespace `S99`.  `s99_ULimB`: `∑_j E[B_j ∂_jf(W_N)] → ∑_j ½ ∑_{l,q} Q_j(l,q) E[∂_q∂_l∂_jf(G)]` uniformly over
the Stein class (Tannery over `j` with the weights `K b_j`, `s99_Bkernel` for each `j`).
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

section LimB

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a)
  (hβ : 0 < β) (hγ : 0 < γ) {C c BU Cs : ℝ} (hT : ThermalData d s a β C c BU)
  (hS : ∀ N : ℕ, 2 ≤ N → S46.S46Static d s a β γ Cs N)
  {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily (J1 d) φ) (F : FamData d s a β γ φ)

include hd hs0 hs ha hβ hγ hT hS hφ F

theorem s99_hj_bdd (j : ℕ) :
    ∃ B : ℝ, IsBoundedPairKernel s B (commutatorKernel d s (gradient (F.χ j))) := by
  have hwf := F.feat hT hγ j
  have hB20 : 0 ≤ F.K * cbNorm (J1 d) (φ j) := (norm_nonneg _).trans (hwf.B2 0)
  have hv1 : ContDiff ℝ 1 (gradient (F.χ j)) := s45_contDiff_gradient hwf.smooth
  have hvd : Differentiable ℝ (gradient (F.χ j)) := hv1.differentiable one_ne_zero
  set Λ : ℝ≥0 := ⟨F.K * cbNorm (J1 d) (φ j), hB20⟩ with hΛdef
  have hLip : LipschitzWith Λ (gradient (F.χ j)) := lipschitzWith_of_nnnorm_fderiv_le hvd (fun x => by
    have := hwf.B2 x
    rw [← NNReal.coe_le_coe, coe_nnnorm]; exact this)
  exact ⟨_, s99_comm_isBounded (d := d) hs0 Λ hLip⟩

set_option maxHeartbeats 2000000 in
theorem s99_ULimB {G : Measure SeqL2} [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianSeq G (fun i j => susceptibilityCov (rieszKernel d s)
      (thermalMeasure d s a β) γ (φ i) (φ j))) :
    ULim (fun N f => if 2 ≤ N then ∑' j, Bterm d s a β γ φ N (commutatorKernel d s (gradient (F.χ j)))
        (pd f j) else 0)
      (fun f => ∑' j, (1 / 2) * ∑' l, ∑' q, Qk d s a β γ φ (commutatorKernel d s (gradient (F.χ j))) l q *
        ∫ z, pd (pd (pd f j) l) q z ∂G) := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  haveI hμ : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  obtain ⟨KB, hKB0, hKB⟩ := s99_Bq_bound hd hs0 hs ha hβ hγ hT hS
  set b : ℕ → ℝ := fun j => cbNorm (J1 d) (φ j) with hbdef
  have hb0 : ∀ j, 0 ≤ b j := fun j => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hbs : Summable b := hφ.2
  have hFK0 := F.hK
  have hJ1 : 1 ≤ J1 d := by unfold J1; omega
  -- the bound on `Bterm`
  have hBt : ∀ N : ℕ, 2 ≤ N → ∀ j : ℕ, ∀ ψ : SeqL2 → ℝ, Bd 4 ψ →
      |Bterm d s a β γ φ N (commutatorKernel d s (gradient (F.χ j))) ψ| ≤ KB * (F.K * b j) := by
    intro N hN j ψ hψ
    have hN1 : 1 ≤ N := by omega
    haveI hP : IsProbabilityMeasure (S46.s46_P d s a β γ N) := (hS N hN).prob
    haveI hν : IsProbabilityMeasure (S46.s46_nu d s a β γ N) := s99_nu_prob hN1
    have hwf := F.feat hT hγ j
    obtain ⟨-, -, hBi, hB1⟩ := hKB N hN hwf.smooth hwf.B2
    have hWc : Continuous (fun X : EucConfig d N => featureVec φ (S46.s46_nu d s a β γ N) X) :=
      (s99_W_contDiff hN1 hJ1 hφ).continuous
    unfold Bterm
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine le_trans ?_ hB1
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun X => norm_nonneg _) hBi.abs
      (Filter.Eventually.of_forall fun X => ?_)
    show ‖Bh d s a β γ N (commutatorKernel d s (gradient (F.χ j))) X *
      ψ (featureVec φ (S46.s46_nu d s a β γ N) X)‖ ≤ |Bq d s a β γ N (F.χ j) X|
    rw [Real.norm_eq_abs, abs_mul]
    calc |Bh d s a β γ N (commutatorKernel d s (gradient (F.χ j))) X| *
          |ψ (featureVec φ (S46.s46_nu d s a β γ N) X)|
        ≤ |Bh d s a β γ N (commutatorKernel d s (gradient (F.χ j))) X| * 1 :=
          mul_le_mul_of_nonneg_left (hψ.abs_le _) (abs_nonneg _)
      _ = _ := by rw [mul_one]; rfl
  -- the limit coefficients, `ULim` for each `j`
  have hlimj : ∀ j, ULim (fun N f => if 2 ≤ N then Bterm d s a β γ φ N
        (commutatorKernel d s (gradient (F.χ j))) (pd f j) else 0)
      (fun f => (1 / 2) * ∑' l, ∑' q, Qk d s a β γ φ (commutatorKernel d s (gradient (F.χ j))) l q *
        ∫ z, pd (pd (pd f j) l) q z ∂G) := by
    intro j
    obtain ⟨Bj, hj⟩ := s99_hj_bdd hd hs0 hs ha hβ hγ hT hS hφ F j
    have hBk := s99_Bkernel hd hs0 hs ha hβ hγ hT hS hφ F hG hj
    intro ε hε
    obtain ⟨N0, hN0⟩ := hBk ε hε
    refine ⟨max N0 2, fun N hN f hf => ?_⟩
    have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
    simp only [hN2, ite_true]
    exact hN0 N ((le_max_left _ _).trans hN) hN2 (hf.pd j)
  have hMs : Summable fun j => KB * (F.K * b j) := (hbs.mul_left F.K).mul_left KB
  have hu : ∀ j N f, SteinCl f → |(fun (j : ℕ) (N : ℕ) (f : SeqL2 → ℝ) => if 2 ≤ N then Bterm d s a β γ φ N
      (commutatorKernel d s (gradient (F.χ j))) (pd f j) else 0) j N f| ≤ KB * (F.K * b j) := by
    intro j N f hf
    by_cases hN : 2 ≤ N
    · simp only [hN, ite_true]; exact hBt N hN j _ (hf.pd j)
    · simp only [hN, ite_false, abs_zero]
      have := hb0 j; positivity
  have hL : ∀ j f, SteinCl f → |(fun (j : ℕ) (f : SeqL2 → ℝ) => (1 / 2) * ∑' l, ∑' q, Qk d s a β γ φ
      (commutatorKernel d s (gradient (F.χ j))) l q * ∫ z, pd (pd (pd f j) l) q z ∂G) j f| ≤
      KB * (F.K * b j) := by
    intro j f hf
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨N0, hN0⟩ := hlimj j ε hε
    have := hN0 (max N0 2) (le_max_left _ _) f hf
    have hN2 : 2 ≤ max N0 2 := le_max_right _ _
    simp only [hN2, ite_true] at this
    have h2 := hBt (max N0 2) hN2 j (pd f j) (hf.pd j)
    have : |(1 / 2) * ∑' l, ∑' q, Qk d s a β γ φ (commutatorKernel d s (gradient (F.χ j))) l q *
        ∫ z, pd (pd (pd f j) l) q z ∂G| ≤ |Bterm d s a β γ φ (max N0 2)
          (commutatorKernel d s (gradient (F.χ j))) (pd f j)| + ε := by
      have h3 := abs_sub_abs_le_abs_sub ((1 / 2) * ∑' l, ∑' q, Qk d s a β γ φ
        (commutatorKernel d s (gradient (F.χ j))) l q * ∫ z, pd (pd (pd f j) l) q z ∂G)
        (Bterm d s a β γ φ (max N0 2) (commutatorKernel d s (gradient (F.χ j))) (pd f j))
      rw [abs_sub_comm] at h3
      linarith
    linarith
  refine ULim.congr (fun N f hf => ?_) (s99_ULim_tsum hMs hu hL hlimj)
  by_cases hN : 2 ≤ N
  · simp only [hN, ite_true]
  · simp [hN]

end LimB

end S99

end
