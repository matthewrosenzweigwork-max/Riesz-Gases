import HRS.MS.R2SeAux45

/-!
# S9.9 `r2_static_edgeworth`, packet 46: the vector `ℓ_x ∈ B_m` and its regularity

Worker S99, namespace `S99`.  `s99_ell_eq`: `r2EllPt x = Ψ⁻¹ (ellv x)`; `s99_ellv_norm`, `s99_ellv_cont`: `ℓ_x` is bounded and continuous in `x`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

section Ell

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a)
  (hβ : 0 < β) (hγ : 0 < γ) {C c BU : ℝ} (hT : ThermalData d s a β C c BU)
  {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily (J1 d) φ) (F : FamData d s a β γ φ)

include hd hs0 hs ha hβ hγ hT hφ F

theorem s99_ellv_norm (x : Euc d) :
    ‖ellv d s a β γ φ x‖ ≤ F.K * ∑' j, cbNorm (J1 d) (φ j) := by
  have h := s99_coord_hasSum (ellv d s a β γ φ x)
  have hb : ∀ j, ‖SeqL2.coord (ellv d s a β γ φ x) j • s45_e1 j (1 : ℝ)‖ ≤ F.K * cbNorm (J1 d) (φ j) := fun j => by
    rw [norm_smul, s99_e1_norm, mul_one, Real.norm_eq_abs, s99_ellv_coord hd hs0 hs ha hβ hγ hT hφ F x j]
    exact (s99_ua hd hs0 hs ha hβ hγ hT hφ F j).2.1 x
  have hg : HasSum (fun j => F.K * cbNorm (J1 d) (φ j)) (F.K * ∑' j, cbNorm (J1 d) (φ j)) :=
    hφ.2.hasSum.mul_left _
  have := tsum_of_norm_bounded hg hb
  rw [h.tsum_eq] at this
  exact this

theorem s99_ellv_cont : Continuous (ellv d s a β γ φ) := by
  have hfun : ellv d s a β γ φ = fun x => ∑' j, aRep d s a β γ (φ j) x • s45_e1 j (1 : ℝ) := by
    funext x
    have h := s99_coord_hasSum (ellv d s a β γ φ x)
    rw [← h.tsum_eq]
    exact tsum_congr fun j => by rw [s99_ellv_coord hd hs0 hs ha hβ hγ hT hφ F x j]
  rw [hfun]
  refine continuous_tsum (u := fun j => F.K * cbNorm (J1 d) (φ j)) (fun j =>
    ((s99_ua hd hs0 hs ha hβ hγ hT hφ F j).1.continuous).smul continuous_const) (hφ.2.mul_left _) ?_
  intro j x
  rw [norm_smul, s99_e1_norm, mul_one, Real.norm_eq_abs]
  exact (s99_ua hd hs0 hs ha hβ hγ hT hφ F j).2.1 x

end Ell

section EllEq

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a)
  (hβ : 0 < β) (hγ : 0 < γ) {C c BU : ℝ} (hT : ThermalData d s a β C c BU) (m : ℕ) (e : ℕ ≃ MultiIndex d)
  (hφ : IsSummableFeatureFamily (J1 d) (fun j : ℕ => oscTestFun (m : ℝ) (e j)))
  (F : FamData d s a β γ (fun j : ℕ => oscTestFun (m : ℝ) (e j)))

include hd hs0 hs ha hβ hγ hT hφ F

theorem s99_ell_eq (x : Euc d) :
    r2EllPt (rieszKernel d s) (thermalMeasure d s a β) γ m x =
      (s45_Psi (m : ℝ) e).symm (ellv d s a β γ (fun j : ℕ => oscTestFun (m : ℝ) (e j)) x) := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  apply (s45_Psi (m : ℝ) e).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  have hc : ∀ α : MultiIndex d, oscEigenvalue d α ^ (-((m : ℝ) / 2)) *
      responseRepW (rieszKernel d s) (thermalMeasure d s a β) γ (hermiteFunD α) x =
      aRep d s a β γ (oscTestFun (m : ℝ) α) x := by
    intro α
    have hmem : MemCb (J1 d) (oscTestFun (m : ℝ) α) := by
      have := hφ.1 (e.symm α)
      simpa using this
    have hlin := s99_resp_smul hd hs0 hsd ha hβ hγ hmem (oscEigenvalue d α ^ ((m : ℝ) / 2)) x
    have hfun : (fun y => oscEigenvalue d α ^ ((m : ℝ) / 2) * oscTestFun (m : ℝ) α y) = hermiteFunD α := by
      funext y
      unfold oscTestFun
      rw [← mul_assoc, mul_comm (oscEigenvalue d α ^ ((m : ℝ) / 2)), rpow_neg_half_mul _ _ (oscEv_pos α), one_mul]
    rw [hfun] at hlin
    rw [hlin, ← mul_assoc, rpow_neg_half_mul _ _ (oscEv_pos α), one_mul]
    rfl
  have hmemN : Memℓp (fun j => aRep d s a β γ (oscTestFun (m : ℝ) (e j)) x) 2 := s99_ellv_memlp hd hs0 hs ha hβ hγ hT hφ F x
  have hmemA : Memℓp (fun α : MultiIndex d => oscEigenvalue d α ^ (-((m : ℝ) / 2)) *
      responseRepW (rieszKernel d s) (thermalMeasure d s a β) γ (hermiteFunD α) x) 2 := by
    have hf : (fun α : MultiIndex d => oscEigenvalue d α ^ (-((m : ℝ) / 2)) *
        responseRepW (rieszKernel d s) (thermalMeasure d s a β) γ (hermiteFunD α) x) =
        fun α => aRep d s a β γ (oscTestFun (m : ℝ) α) x := funext hc
    rw [hf, memℓp_gen_iff (by norm_num)]
    have := (memℓp_gen_iff (by norm_num)).1 hmemN
    exact (e.summable_iff (f := fun α => ‖aRep d s a β γ (oscTestFun (m : ℝ) α) x‖ ^ (2 : ENNReal).toReal)).1 this
  refine lp.ext (funext fun j => ?_)
  show SeqL2.coord (s45_Psi (m : ℝ) e (r2EllPt (rieszKernel d s) (thermalMeasure d s a β) γ m x)) j =
    SeqL2.coord (ellv d s a β γ (fun j : ℕ => oscTestFun (m : ℝ) (e j)) x) j
  rw [s45_Psi_coord, s99_ellv_coord hd hs0 hs ha hβ hγ hT hφ F x j, ← hc (e j)]
  have hco : ∀ (c' : MultiIndex d → ℝ), Memℓp (fun α => oscEigenvalue d α ^ (-((m : ℝ) / 2)) * c' α) 2 →
      ∀ α, OscDual.coord (OscDual.ofSeq (m : ℝ) c') α = oscEigenvalue d α ^ (-((m : ℝ) / 2)) * c' α := by
    intro c' h α
    simp [OscDual.ofSeq, h, OscDual.coord]
  exact hco _ hmemA (e j)

end EllEq

end S99

end
