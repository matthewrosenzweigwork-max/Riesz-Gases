import HRS.Sections.QuenchAux16
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# Packet QUENCH (Q27), part 17: Bernstein interpolation on the path space `𝒳_T = C([0,T];E_m)`

`Π_n w = ∑_k b_{n,k}(·/T) ⊗ w(t_k)` is a finite-rank contraction `𝒳_T → 𝒳_T` converging strongly to the
identity (Mathlib `bernsteinApproximation_uniform`, valid for any locally convex target).  The bilinear
form `M ↦ (u,v) ↦ M ![u,v]` as a continuous bilinear map.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators unitInterval

namespace HRS

namespace Qch

/-- A bounded bilinear form on `G` (given as a continuous 2-linear map) as a curried continuous bilinear map. -/
def bilinOfMulti {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (M : G [×2]→L[ℝ] ℝ) :
    G →L[ℝ] G →L[ℝ] ℝ :=
  ((continuousMultilinearCurryFin1 ℝ G ℝ).toLinearIsometry.toContinuousLinearMap).comp M.curryLeft

lemma bilinOfMulti_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (M : G [×2]→L[ℝ] ℝ)
    (u v : G) : bilinOfMulti M u v = M ![u, v] := by
  simp [bilinOfMulti, continuousMultilinearCurryFin1_apply]

lemma abs_multi_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (M : G [×2]→L[ℝ] ℝ)
    (u v : G) : |M ![u, v]| ≤ ‖M‖ * ‖u‖ * ‖v‖ := by
  have := M.le_opNorm ![u, v]
  rw [Real.norm_eq_abs, Fin.prod_univ_two] at this
  simpa [mul_assoc] using this

variable {d : ℕ} {m T : ℝ}

section Bern

/-- `t ↦ t/T`, `[0,T] → [0,1]`. -/
def bphi (hT : 0 < T) : C(Set.Icc (0 : ℝ) T, I) where
  toFun t := ⟨t.1 / T, div_nonneg t.2.1 hT.le, (div_le_one hT).2 t.2.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.div_const T

/-- `x ↦ T x`, `[0,1] → [0,T]`. -/
def bpsi (hT : 0 < T) : C(I, Set.Icc (0 : ℝ) T) where
  toFun x := ⟨T * x.1, mul_nonneg hT.le x.2.1, by nlinarith [x.2.2]⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_const.mul continuous_subtype_val

lemma bpsi_bphi (hT : 0 < T) (t : Set.Icc (0 : ℝ) T) : bpsi hT (bphi hT t) = t := by
  apply Subtype.ext
  simp [bpsi, bphi]
  field_simp

/-- The Bernstein weight `t ↦ b_{n,k}(t/T)` as a continuous function on `[0,T]`. -/
def bcoef (hT : 0 < T) (n k : ℕ) : C(Set.Icc (0 : ℝ) T, ℝ) := (bernstein n k).comp (bphi hT)

lemma bcoef_nonneg (hT : 0 < T) (n k : ℕ) (t : Set.Icc (0 : ℝ) T) : 0 ≤ bcoef hT n k t := by
  simp only [bcoef, ContinuousMap.comp_apply]
  exact bernstein_nonneg

lemma sum_bcoef (hT : 0 < T) (n : ℕ) (t : Set.Icc (0 : ℝ) T) : ∑ k : Fin (n + 1), bcoef hT n k t = 1 := by
  simp only [bcoef, ContinuousMap.comp_apply]
  exact bernstein.probability n _

lemma bcoef_le_one (hT : 0 < T) (n : ℕ) (k : Fin (n + 1)) (t : Set.Icc (0 : ℝ) T) : bcoef hT n k t ≤ 1 := by
  rw [← sum_bcoef hT n t]
  exact Finset.single_le_sum (f := fun k : Fin (n + 1) => bcoef hT n k t)
    (fun k _ => bcoef_nonneg hT n k t) (Finset.mem_univ k)

/-- The interpolation node `t_k = T k/n`. -/
def bnode (hT : 0 < T) (n : ℕ) (k : Fin (n + 1)) : Set.Icc (0 : ℝ) T := bpsi hT (bernstein.z k)

/-- `x ↦ b_{n,k}(·/T) • x` as a path. -/
def bembFun (hT : 0 < T) (n : ℕ) (k : Fin (n + 1)) (x : NegSobolev d m) : PathSpace d m T :=
  (⟨fun t => bcoef hT n k t • x, (bcoef hT n k).continuous.smul continuous_const⟩ :
    C(Set.Icc (0 : ℝ) T, NegSobolev d m))

lemma bembFun_at (hT : 0 < T) (n : ℕ) (k : Fin (n + 1)) (x : NegSobolev d m) (t : Set.Icc (0 : ℝ) T) :
    (bembFun hT n k x).at' t = bcoef hT n k t • x := rfl

lemma norm_bembFun_le (hT : 0 < T) (n : ℕ) (k : Fin (n + 1)) (x : NegSobolev d m) :
    ‖bembFun hT n k x‖ ≤ ‖x‖ := by
  refine (ContinuousMap.norm_le (bembFun hT n k x : C(Set.Icc (0 : ℝ) T, NegSobolev d m)) (norm_nonneg _)).2 fun t => ?_
  show ‖bcoef hT n k t • x‖ ≤ ‖x‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (bcoef_nonneg hT n k t)]
  exact mul_le_of_le_one_left (norm_nonneg _) (bcoef_le_one hT n k t)

/-- The embedding `E → 𝒳_T`, `x ↦ b_{n,k}(·/T) x`, as a continuous linear map. -/
def bemb (hT : 0 < T) (n : ℕ) (k : Fin (n + 1)) : NegSobolev d m →L[ℝ] PathSpace d m T :=
  LinearMap.mkContinuous
    { toFun := bembFun hT n k
      map_add' := fun x y => by
        refine ContinuousMap.ext fun t => ?_
        show bcoef hT n k t • (x + y) = bcoef hT n k t • x + bcoef hT n k t • y
        rw [smul_add]
      map_smul' := fun c x => by
        refine ContinuousMap.ext fun t => ?_
        show bcoef hT n k t • (c • x) = c • (bcoef hT n k t • x)
        rw [smul_comm] }
    1 (fun x => by
      show ‖bembFun hT n k x‖ ≤ 1 * ‖x‖
      rw [one_mul]; exact norm_bembFun_le hT n k x)

lemma bemb_at (hT : 0 < T) (n : ℕ) (k : Fin (n + 1)) (x : NegSobolev d m) (t : Set.Icc (0 : ℝ) T) :
    (bemb hT n k x : PathSpace d m T).at' t = bcoef hT n k t • x := rfl

/-- The Bernstein interpolation `Π_n w = ∑_k b_{n,k} ⊗ w(t_k)`. -/
def bInterp (hT : 0 < T) (n : ℕ) (w : PathSpace d m T) : PathSpace d m T :=
  ∑ k : Fin (n + 1), bemb hT n k (w.at' (bnode hT n k))

lemma at'_sum {ι : Type*} (s : Finset ι) (f : ι → PathSpace d m T) (t : Set.Icc (0 : ℝ) T) :
    (∑ k ∈ s, f k).at' t = ∑ k ∈ s, (f k).at' t := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

lemma bInterp_at (hT : 0 < T) (n : ℕ) (w : PathSpace d m T) (t : Set.Icc (0 : ℝ) T) :
    (bInterp hT n w).at' t = ∑ k : Fin (n + 1), bcoef hT n k t • w.at' (bnode hT n k) := by
  unfold bInterp
  rw [at'_sum]
  rfl

lemma norm_bInterp_le (hT : 0 < T) (n : ℕ) (w : PathSpace d m T) : ‖bInterp hT n w‖ ≤ ‖w‖ := by
  refine (ContinuousMap.norm_le (bInterp hT n w : C(Set.Icc (0 : ℝ) T, NegSobolev d m)) (norm_nonneg _)).2
    fun t => ?_
  show ‖(bInterp hT n w).at' t‖ ≤ ‖w‖
  rw [bInterp_at]
  calc ‖∑ k : Fin (n + 1), bcoef hT n k t • w.at' (bnode hT n k)‖
      ≤ ∑ k : Fin (n + 1), ‖bcoef hT n k t • w.at' (bnode hT n k)‖ := norm_sum_le _ _
    _ ≤ ∑ k : Fin (n + 1), bcoef hT n k t * ‖w‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (bcoef_nonneg hT n k t)]
        exact mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm
          (w : C(Set.Icc (0 : ℝ) T, NegSobolev d m)) _) (bcoef_nonneg hT n k t)
    _ = ‖w‖ := by rw [← Finset.sum_mul, sum_bcoef, one_mul]

theorem bInterp_tendsto (hT : 0 < T) (w : PathSpace d m T) :
    Tendsto (fun n => bInterp hT n w) atTop (𝓝 w) := by
  set w' : C(Set.Icc (0 : ℝ) T, NegSobolev d m) := w with hw'
  set wt : C(I, NegSobolev d m) := w'.comp (bpsi hT) with hwt
  have h1 := bernsteinApproximation_uniform wt
  rw [tendsto_iff_norm_sub_tendsto_zero] at h1 ⊢
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h1
  refine (ContinuousMap.norm_le ((bInterp hT n w - w : PathSpace d m T) :
    C(Set.Icc (0 : ℝ) T, NegSobolev d m)) (norm_nonneg _)).2 fun t => ?_
  have e1 : (bInterp hT n w).at' t = (bernsteinApproximation n wt) (bphi hT t) := by
    rw [bInterp_at, bernsteinApproximation.apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rfl
  have e2 : w.at' t = wt (bphi hT t) := by
    show w'  t = (w'.comp (bpsi hT)) (bphi hT t)
    rw [ContinuousMap.comp_apply, bpsi_bphi]
  show ‖(bInterp hT n w).at' t - w.at' t‖ ≤ _
  rw [e1, e2]
  exact (ContinuousMap.norm_coe_le_norm (bernsteinApproximation n wt - wt) (bphi hT t))

end Bern

end Qch

end HRS
