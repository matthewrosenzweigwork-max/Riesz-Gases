import HRS.MS.SA12Z3NearN1
import HRS.MS.UniqN0d
import HRS.MS.UniqN3cB

/-!
# S.A.12 N7 (SA12Z3), part A: ordered partial derivatives and convolution

* `sa12z3_pd_cons`: `∂^{(i,idx)} f = ∂_i ∂^{idx} f` for `C^{n+1}` `f`;
* smoothness and compact support of `∂^{idx} f`; commutation `∂^{idx} ∂_j f = ∂_j ∂^{idx} f`;
* `sa12z3_pd_conv`: `∂^{idx} (g * Q) = g * ∂^{idx} Q` for `Q ∈ C^n_c`, `g` the Riesz kernel.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

/-- The vector family of an index tuple. -/
abbrev sa12z3_ev {n : ℕ} (idx : Fin n → Fin d) : Fin n → Euc d := fun l => EuclideanSpace.single (idx l) 1

theorem sa12z3_pd_zero (f : Euc d → ℝ) (x : Euc d) (idx : Fin 0 → Fin d) :
    partialDeriv idx f x = f x := by
  unfold partialDeriv
  rw [iteratedFDeriv_zero_apply]

theorem sa12z3_pd_zero_fun (f : Euc d → ℝ) (idx : Fin 0 → Fin d) : partialDeriv idx f = f :=
  funext fun x => sa12z3_pd_zero f x idx

theorem sa12z3_cd_of_inf {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ) : ContDiff ℝ k f :=
  hf.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))

theorem sa12z3_pd_cons {n : ℕ} (idx : Fin n → Fin d) (i : Fin d) {f : Euc d → ℝ}
    (hf : ContDiff ℝ (n + 1) f) (x : Euc d) :
    partialDeriv (Fin.cons i idx : Fin (n + 1) → Fin d) f x = D1 i (partialDeriv idx f) x := by
  have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) x :=
    (hf.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self n)) x
  have h1 := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Euc d) ℝ
    (sa12z3_ev idx)).hasFDerivAt).comp x hdiff.hasFDerivAt
  have h2 : D1 i (partialDeriv idx f) x = fderiv ℝ (iteratedFDeriv ℝ n f) x
      (EuclideanSpace.single i 1) (sa12z3_ev idx) := by
    unfold D1 partialDeriv
    have : (fun y => iteratedFDeriv ℝ n f y (fun l => EuclideanSpace.single (idx l) (1 : ℝ))) =
        (fun y => ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Euc d) ℝ (sa12z3_ev idx)
          (iteratedFDeriv ℝ n f y)) := rfl
    have h1' : HasFDerivAt (fun y => ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Euc d) ℝ
        (sa12z3_ev idx) (iteratedFDeriv ℝ n f y))
        ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Euc d) ℝ (sa12z3_ev idx)).comp
          (fderiv ℝ (iteratedFDeriv ℝ n f) x)) x := h1
    rw [this, h1'.fderiv]
    rfl
  rw [h2]
  unfold partialDeriv
  rw [iteratedFDeriv_succ_apply_left]
  simp only [Fin.cons_zero]
  congr 1

theorem sa12z3_pd_contDiff {k n : ℕ} {f : Euc d → ℝ} (hf : ContDiff ℝ k f) (hnk : n ≤ k)
    (idx : Fin n → Fin d) : ContDiff ℝ ((k - n : ℕ) : WithTop ℕ∞) (partialDeriv idx f) := by
  have h := hf.iteratedFDeriv_right (i := n) (m := ((k - n : ℕ) : WithTop ℕ∞)) (by
    rw [← Nat.cast_add]; exact_mod_cast (by omega : k - n + n ≤ k))
  have h2 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Euc d) ℝ
    (sa12z3_ev idx)).contDiff.comp h
  exact h2

theorem sa12z3_pd_compact {n : ℕ} {f : Euc d → ℝ} (hfc : HasCompactSupport f) (idx : Fin n → Fin d) :
    HasCompactSupport (partialDeriv idx f) :=
  (hfc.iteratedFDeriv (𝕜 := ℝ) n).comp_left (g := fun L : ContinuousMultilinearMap ℝ (fun _ : Fin n => Euc d) ℝ =>
    L (sa12z3_ev idx)) (by simp)

theorem sa12z3_pd_support {n : ℕ} {f : Euc d → ℝ} (idx : Fin n → Fin d) :
    Function.support (partialDeriv idx f) ⊆ tsupport f := by
  intro x hx
  have : iteratedFDeriv ℝ n f x ≠ 0 := fun h0 => hx (by simp [partialDeriv, h0])
  exact support_iteratedFDeriv_subset (𝕜 := ℝ) n (Function.mem_support.2 this)

/-- Mixed partials commute: `∂^{idx} ∂_j f = ∂_j ∂^{idx} f` for `f ∈ C^{n+1}`, `|idx| = n`. -/
theorem sa12z3_pd_D1_comm (j : Fin d) :
    ∀ (n : ℕ) (f : Euc d → ℝ), ContDiff ℝ (n + 1) f → ∀ (idx : Fin n → Fin d) (x : Euc d),
      partialDeriv idx (D1 j f) x = D1 j (partialDeriv idx f) x := by
  intro n
  induction n with
  | zero =>
    intro f hf idx x
    simp only [sa12z3_pd_zero_fun]
  | succ n ih =>
    intro f hf idx x
    obtain ⟨i, idx', rfl⟩ : ∃ i idx', idx = (Fin.cons i idx' : Fin (n + 1) → Fin d) :=
      ⟨idx 0, Fin.tail idx, (Fin.cons_self_tail idx).symm⟩
    have hf' : ContDiff ℝ (n + 1 + 1) f := hf
    have hDf : ContDiff ℝ (n + 1) (D1 j f) :=
      (hf.fderiv_right (m := (n + 1 : ℕ)) (by push_cast; rfl)).clm_apply contDiff_const
    have hfn : ContDiff ℝ (n + 1) f := hf.of_le (by exact_mod_cast Nat.le_succ (n + 1))
    have e1 : partialDeriv (Fin.cons i idx' : Fin (n + 1) → Fin d) (D1 j f) x =
        D1 i (partialDeriv idx' (D1 j f)) x := sa12z3_pd_cons idx' i hDf x
    have e2 : partialDeriv (Fin.cons i idx' : Fin (n + 1) → Fin d) f =
        D1 i (partialDeriv idx' f) := funext fun y => sa12z3_pd_cons idx' i hfn y
    have e3 : D1 i (partialDeriv idx' (D1 j f)) = D1 i (D1 j (partialDeriv idx' f)) :=
      congrArg (D1 i) (funext fun y => ih f hfn idx' y)
    have hP : ContDiff ℝ 2 (partialDeriv idx' f) := by
      have := sa12z3_pd_contDiff (k := n + 2) (n := n) hf' (by omega) idx'
      simpa using this
    rw [e1, e3, e2]
    exact HRS.MS.UniqN3c.n3c_hess_symm hP j i x

/-- `∂^{idx}` of the convolution with the Riesz kernel. -/
theorem sa12z3_pd_conv {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∀ (n : ℕ) (Q : Euc d → ℝ), ContDiff ℝ n Q → HasCompactSupport Q → ∀ (idx : Fin n → Fin d) (x : Euc d),
      partialDeriv idx (HRS.Whole.convFun (rieszKernel d s) Q) x =
        HRS.Whole.convFun (rieszKernel d s) (partialDeriv idx Q) x := by
  have hK : LocallyIntegrable (rieszKernel d s) (volume : Measure (Euc d)) :=
    rieszKernel_locallyIntegrable hs0 hsd
  have hfun : ∀ Q : Euc d → ℝ, HRS.Whole.convFun (rieszKernel d s) Q =
      rieszKernel d s ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] Q := by
    intro Q
    funext x'
    have h := integral_sub_left_eq_self (μ := volume) (fun t => rieszKernel d s t * Q (x' - t)) x'
    simp only [sub_sub_cancel] at h
    simpa [convolution_def, HRS.Whole.convFun] using h
  have hcd : ∀ (n : ℕ) (Q : Euc d → ℝ), ContDiff ℝ n Q → HasCompactSupport Q →
      ContDiff ℝ n (HRS.Whole.convFun (rieszKernel d s) Q) := by
    intro n Q hQ hQc
    rw [hfun]
    exact hQc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hK hQ
  intro n
  induction n with
  | zero =>
    intro Q hQ hQc idx x
    simp only [sa12z3_pd_zero_fun]
  | succ n ih =>
    intro Q hQ hQc idx x
    obtain ⟨i, idx', rfl⟩ : ∃ i idx', idx = (Fin.cons i idx' : Fin (n + 1) → Fin d) :=
      ⟨idx 0, Fin.tail idx, (Fin.cons_self_tail idx).symm⟩
    have hQn : ContDiff ℝ n Q := hQ.of_le (by exact_mod_cast Nat.le_succ n)
    have e1 : partialDeriv (Fin.cons i idx' : Fin (n + 1) → Fin d) (HRS.Whole.convFun (rieszKernel d s) Q) x =
        D1 i (partialDeriv idx' (HRS.Whole.convFun (rieszKernel d s) Q)) x :=
      sa12z3_pd_cons idx' i (hcd (n + 1) Q hQ hQc) x
    have e2 : D1 i (partialDeriv idx' (HRS.Whole.convFun (rieszKernel d s) Q)) =
        D1 i (HRS.Whole.convFun (rieszKernel d s) (partialDeriv idx' Q)) :=
      congrArg (D1 i) (funext fun y => ih Q hQn hQc idx' y)
    have hPQ : ContDiff ℝ 1 (partialDeriv idx' Q) := by
      have := sa12z3_pd_contDiff (k := n + 1) (n := n) hQ (by omega) idx'
      simpa using this
    have e3 : D1 i (HRS.Whole.convFun (rieszKernel d s) (partialDeriv idx' Q)) x =
        HRS.Whole.convFun (rieszKernel d s) (D1 i (partialDeriv idx' Q)) x :=
      convFun_D1 hK hPQ (sa12z3_pd_compact hQc idx') i x
    have e4 : partialDeriv (Fin.cons i idx' : Fin (n + 1) → Fin d) Q x = D1 i (partialDeriv idx' Q) x :=
      sa12z3_pd_cons idx' i hQ x
    rw [e1, e2, e3]
    unfold HRS.Whole.convFun
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [sa12z3_pd_cons idx' i hQ y]

end HRS.MH.AdjointRd.Phase2SA12Near
