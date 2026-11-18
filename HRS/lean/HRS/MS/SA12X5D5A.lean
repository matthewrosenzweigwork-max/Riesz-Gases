import HRS.MS.SA12CellC8B
import HRS.MS.SA12X5Defs

/-!
# S.A.12 X5 D5A: calculus of jointly continuous jets (`sa12x5_PJC`)

`sa12x5_PJC t u`: each `u τ` (`τ ∈ [0,t]`) is `C^∞` and every partial derivative `∂^{idx} u τ x` is jointly continuous on
`[0,t] × ℝ^d`.  Closed under sums, scalar multiples, `D1 i`, products, Laplacian, and `τ`-independent smooth functions.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

/-- Smooth in `x` with all partial derivatives jointly continuous on the slab `[0,t] × ℝ^d`. -/
def sa12x5_PJC (t : ℝ) (u : ℝ → Euc d → ℝ) : Prop :=
  (∀ τ ∈ Icc (0 : ℝ) t, ContDiff ℝ ∞ (u τ)) ∧
    ∀ (n : ℕ) (idx : Fin n → Fin d),
      ContinuousOn (fun p : ℝ × Euc d => partialDeriv idx (u p.1) p.2) (Icc (0 : ℝ) t ×ˢ univ)

theorem sa12x5_iter_dirD {f : Euc d → ℝ} {x : Euc d} {n : ℕ} (hf : ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f x)
    (h : Euc d) (w : Fin n → Euc d) :
    iteratedFDeriv ℝ n (fun y => fderiv ℝ f y h) x w = iteratedFDeriv ℝ (n + 1) f x (Fin.snoc w h) := by
  rw [iteratedFDeriv_succ_apply_right]
  simp only [Fin.init_snoc, Fin.snoc_last]
  have hd : ContDiffAt ℝ n (fderiv ℝ f) x := hf.fderiv_right (m := n) (by norm_num)
  have := (ContinuousLinearMap.apply ℝ ℝ h).iteratedFDeriv_comp_left hd (i := n) le_rfl
  have h2 : (fun y => fderiv ℝ f y h) = (ContinuousLinearMap.apply ℝ ℝ h) ∘ fderiv ℝ f := rfl
  rw [h2, this]
  rfl

theorem sa12x5_pd_snoc {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) {n : ℕ} (idx : Fin n → Fin d) (i : Fin d)
    (x : Euc d) :
    partialDeriv (Fin.snoc idx i : Fin (n + 1) → Fin d) f x =
      partialDeriv idx (HRS.MS.UniqT3.D1 i f) x := by
  unfold partialDeriv
  have := sa12x5_iter_dirD (f := f) (x := x) (n := n) (hf.contDiffAt.of_le (by exact_mod_cast le_top))
    (EuclideanSpace.single i 1) (fun l => EuclideanSpace.single (idx l) 1)
  have e : (fun l : Fin (n + 1) => (EuclideanSpace.single ((Fin.snoc idx i : Fin (n + 1) → Fin d) l) (1 : ℝ) : Euc d)) =
      Fin.snoc (fun l => (EuclideanSpace.single (idx l) (1 : ℝ) : Euc d)) (EuclideanSpace.single i (1 : ℝ)) := by
    funext l
    refine Fin.lastCases ?_ (fun k => ?_) l <;> simp [Fin.snoc]
  rw [e, ← this]
  rfl

theorem sa12x5_pd_zero (idx : Fin 0 → Fin d) (f : Euc d → ℝ) (x : Euc d) : partialDeriv idx f x = f x := by
  simp [partialDeriv, iteratedFDeriv_zero_apply]

theorem sa12x5_pd_add {f g : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {n : ℕ}
    (idx : Fin n → Fin d) (x : Euc d) :
    partialDeriv idx (fun y => f y + g y) x = partialDeriv idx f x + partialDeriv idx g x := by
  unfold partialDeriv
  have := iteratedFDeriv_add_apply (i := n) (x := x) (f := f) (g := g)
    (hf.contDiffAt.of_le (by exact_mod_cast le_top)) (hg.contDiffAt.of_le (by exact_mod_cast le_top))
  have e : (fun y => f y + g y) = f + g := rfl
  rw [e, this]
  rfl

theorem sa12x5_pd_sub {f g : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {n : ℕ}
    (idx : Fin n → Fin d) (x : Euc d) :
    partialDeriv idx (fun y => f y - g y) x = partialDeriv idx f x - partialDeriv idx g x := by
  unfold partialDeriv
  have := iteratedFDeriv_sub_apply (i := n) (x := x) (f := f) (g := g)
    (hf.contDiffAt.of_le (by exact_mod_cast le_top)) (hg.contDiffAt.of_le (by exact_mod_cast le_top))
  have e : (fun y => f y - g y) = f - g := rfl
  rw [e, this]
  rfl

theorem sa12x5_pd_smul {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℝ) {n : ℕ}
    (idx : Fin n → Fin d) (x : Euc d) :
    partialDeriv idx (fun y => c * f y) x = c * partialDeriv idx f x := by
  unfold partialDeriv
  have := iteratedFDeriv_const_smul_apply' (i := n) (x := x) (a := c) (f := f)
    (hf.contDiffAt.of_le (by exact_mod_cast le_top))
  have e : (fun y => c * f y) = fun x => c • f x := rfl
  rw [e, this]
  simp

theorem sa12x5_PJC_congr {t : ℝ} {u v : ℝ → Euc d → ℝ} (h : ∀ τ ∈ Icc (0 : ℝ) t, u τ = v τ)
    (hu : sa12x5_PJC t u) : sa12x5_PJC t v := by
  refine ⟨fun τ hτ => (h τ hτ) ▸ hu.1 τ hτ, fun n idx => ?_⟩
  refine (hu.2 n idx).congr fun p hp => ?_
  show partialDeriv idx (v p.1) p.2 = partialDeriv idx (u p.1) p.2
  rw [h p.1 hp.1]

theorem sa12x5_PJC_const {t : ℝ} {u : Euc d → ℝ} (hu : ContDiff ℝ ∞ u) : sa12x5_PJC t (fun _ => u) := by
  refine ⟨fun _ _ => hu, fun n idx => ?_⟩
  have h : Continuous (fun x : Euc d => partialDeriv idx u x) := by
    unfold partialDeriv
    exact (continuous_eval_const (fun l : Fin n => (EuclideanSpace.single (idx l) (1 : ℝ) : Euc d))).comp
      (hu.continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top))
  exact (h.comp continuous_snd).continuousOn

theorem sa12x5_PJC_add {t : ℝ} {u v : ℝ → Euc d → ℝ} (hu : sa12x5_PJC t u) (hv : sa12x5_PJC t v) :
    sa12x5_PJC t (fun τ x => u τ x + v τ x) := by
  refine ⟨fun τ hτ => (hu.1 τ hτ).add (hv.1 τ hτ), fun n idx => ?_⟩
  refine ((hu.2 n idx).add (hv.2 n idx)).congr fun p hp => ?_
  exact sa12x5_pd_add (hu.1 p.1 hp.1) (hv.1 p.1 hp.1) idx p.2

theorem sa12x5_PJC_sub {t : ℝ} {u v : ℝ → Euc d → ℝ} (hu : sa12x5_PJC t u) (hv : sa12x5_PJC t v) :
    sa12x5_PJC t (fun τ x => u τ x - v τ x) := by
  refine ⟨fun τ hτ => (hu.1 τ hτ).sub (hv.1 τ hτ), fun n idx => ?_⟩
  refine ((hu.2 n idx).sub (hv.2 n idx)).congr fun p hp => ?_
  exact sa12x5_pd_sub (hu.1 p.1 hp.1) (hv.1 p.1 hp.1) idx p.2

theorem sa12x5_PJC_smul {t : ℝ} {u : ℝ → Euc d → ℝ} (hu : sa12x5_PJC t u) (c : ℝ) :
    sa12x5_PJC t (fun τ x => c * u τ x) := by
  refine ⟨fun τ hτ => contDiff_const.mul (hu.1 τ hτ), fun n idx => ?_⟩
  refine ((hu.2 n idx).const_smul c).congr fun p hp => ?_
  exact sa12x5_pd_smul (hu.1 p.1 hp.1) c idx p.2

theorem sa12x5_PJC_sum {ι : Type*} {t : ℝ} (s : Finset ι) (u : ι → ℝ → Euc d → ℝ)
    (h : ∀ i ∈ s, sa12x5_PJC t (u i)) : sa12x5_PJC t (fun τ x => ∑ i ∈ s, u i τ x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (sa12x5_PJC_const (t := t) (u := fun _ : Euc d => (0 : ℝ)) contDiff_const)
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact sa12x5_PJC_add (h i (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem sa12x5_PJC_D1 {t : ℝ} {u : ℝ → Euc d → ℝ} (hu : sa12x5_PJC t u) (i : Fin d) :
    sa12x5_PJC t (fun τ => HRS.MS.UniqT3.D1 i (u τ)) := by
  refine ⟨fun τ hτ => sa12y_D1_contDiff (hu.1 τ hτ) i, fun n idx => ?_⟩
  refine (hu.2 (n + 1) (Fin.snoc idx i)).congr fun p hp => ?_
  exact (sa12x5_pd_snoc (hu.1 p.1 hp.1) idx i p.2).symm

theorem sa12x5_D1_mul {f g : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (i : Fin d) :
    HRS.MS.UniqT3.D1 i (fun y => f y * g y) =
      fun y => f y * HRS.MS.UniqT3.D1 i g y + HRS.MS.UniqT3.D1 i f y * g y := by
  funext y
  unfold HRS.MS.UniqT3.D1
  have hfd : DifferentiableAt ℝ f y := (hf.differentiable (by simp)) y
  have hgd : DifferentiableAt ℝ g y := (hg.differentiable (by simp)) y
  have h := hfd.hasFDerivAt.mul hgd.hasFDerivAt
  have h' : HasFDerivAt (fun y => f y * g y) (f y • fderiv ℝ g y + g y • fderiv ℝ f y) y := h
  rw [h'.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem sa12x5_cont_mul (t : ℝ) : ∀ (n : ℕ) (u v : ℝ → Euc d → ℝ), sa12x5_PJC t u → sa12x5_PJC t v →
    ∀ idx : Fin n → Fin d, ContinuousOn (fun p : ℝ × Euc d => partialDeriv idx (fun y => u p.1 y * v p.1 y) p.2)
      (Icc (0 : ℝ) t ×ˢ univ) := by
  intro n
  induction n with
  | zero =>
    intro u v hu hv idx
    refine ((hu.2 0 idx).mul (hv.2 0 idx)).congr fun p hp => ?_
    simp only [Pi.mul_apply, sa12x5_pd_zero]
  | succ n ih =>
    intro u v hu hv idx
    obtain ⟨idx', i, rfl⟩ : ∃ (idx' : Fin n → Fin d) (i : Fin d), idx = Fin.snoc idx' i :=
      ⟨Fin.init idx, idx (Fin.last n), (Fin.snoc_init_self idx).symm⟩
    have h1 := ih u (fun τ => HRS.MS.UniqT3.D1 i (v τ)) hu (sa12x5_PJC_D1 hv i) idx'
    have h2 := ih (fun τ => HRS.MS.UniqT3.D1 i (u τ)) v (sa12x5_PJC_D1 hu i) hv idx'
    refine (h1.add h2).congr fun p hp => ?_
    have hu1 := hu.1 p.1 hp.1
    have hv1 := hv.1 p.1 hp.1
    rw [sa12x5_pd_snoc (hu1.mul hv1) idx' i p.2]
    rw [show (fun y => u p.1 y * v p.1 y) = fun y => u p.1 y * v p.1 y from rfl]
    rw [sa12x5_D1_mul hu1 hv1 i]
    exact sa12x5_pd_add (hu1.mul (sa12y_D1_contDiff hv1 i)) ((sa12y_D1_contDiff hu1 i).mul hv1) idx' p.2

theorem sa12x5_PJC_mul {t : ℝ} {u v : ℝ → Euc d → ℝ} (hu : sa12x5_PJC t u) (hv : sa12x5_PJC t v) :
    sa12x5_PJC t (fun τ x => u τ x * v τ x) :=
  ⟨fun τ hτ => (hu.1 τ hτ).mul (hv.1 τ hτ), fun n idx => sa12x5_cont_mul t n u v hu hv idx⟩

/-- The Laplacian of a jointly regular family is jointly regular. -/
theorem sa12x5_PJC_lap {t : ℝ} {u : ℝ → Euc d → ℝ} (hu : sa12x5_PJC t u) :
    sa12x5_PJC t (fun τ y => Laplacian.laplacian (u τ) y) := by
  have h := sa12x5_PJC_sum (t := t) (Finset.univ : Finset (Fin d))
    (fun i τ => HRS.MS.UniqT3.D1 i (HRS.MS.UniqT3.D1 i (u τ)))
    (fun i _ => sa12x5_PJC_D1 (sa12x5_PJC_D1 hu i) i)
  refine sa12x5_PJC_congr (fun τ hτ => ?_) h
  funext y
  rw [HRS.MS.UniqT3.lap_eq ((hu.1 τ hτ).of_le (by simp)) y]

end HRS.MH.AdjointRd.Phase2SA12X5
