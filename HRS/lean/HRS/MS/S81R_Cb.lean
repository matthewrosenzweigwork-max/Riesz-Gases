import HRS.MS.MfeConfAux105
import HRS.MS.Ker1Aux4

/-!
# S81R, packet R6: bounded derivatives of the truncated Riesz kernel and closure lemmas

* `s81r_Bd f`: `f` is `C^∞` and all its derivatives of order `≥ 1` are bounded;
* closure under composition with a continuous linear map, constant multiples, finite sums, additive constants;
* `s81r_Bd_kM`: `sb1kM d s M` satisfies `s81r_Bd` (inside the ball: compactness; outside: `ker1_E_bound`,
  the kernel equals the Riesz kernel there).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff NNReal
open HRS HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl HRS.MS.MfeConf

namespace HRS.MS.S81R

/-- `C^∞` with all derivatives of positive order bounded -/
def s81r_Bd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ j : ℕ, 1 ≤ j → ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ j f y‖ ≤ C

section Closure

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem s81r_Bd_comp {k : F → ℝ} (hk : s81r_Bd k) (A : E →L[ℝ] F) : s81r_Bd (fun y => k (A y)) := by
  refine ⟨hk.1.comp A.contDiff, fun j hj => ?_⟩
  obtain ⟨C, hC⟩ := hk.2 j hj
  refine ⟨C * ‖A‖ ^ j, fun y => ?_⟩
  have hkj : ContDiff ℝ j k := contDiff_infty.1 hk.1 j
  have e := A.iteratedFDeriv_comp_right hkj y (i := j) le_rfl
  have e' : (fun y => k (A y)) = k ∘ A := rfl
  rw [e', e]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul_of_nonneg_right (hC _) (by positivity)

theorem s81r_Bd_smul (c : ℝ) {f : E → ℝ} (hf : s81r_Bd f) : s81r_Bd (fun y => c * f y) := by
  refine ⟨contDiff_const.mul hf.1, fun j hj => ?_⟩
  obtain ⟨C, hC⟩ := hf.2 j hj
  refine ⟨|c| * C, fun y => ?_⟩
  have hfj : ContDiffAt ℝ j f y := (contDiff_infty.1 hf.1 j).contDiffAt
  have e := iteratedFDeriv_const_smul_apply' (a := c) hfj
  simp only [smul_eq_mul] at e
  rw [e, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hC y) (abs_nonneg _)

theorem s81r_Bd_add_const {f : E → ℝ} (hf : s81r_Bd f) (c : ℝ) : s81r_Bd (fun y => f y + c) := by
  refine ⟨hf.1.add contDiff_const, fun j hj => ?_⟩
  obtain ⟨C, hC⟩ := hf.2 j hj
  refine ⟨C, fun y => ?_⟩
  have hfj : ContDiffAt ℝ j f y := (contDiff_infty.1 hf.1 j).contDiffAt
  have e : iteratedFDeriv ℝ j (f + fun _ => c) y =
      iteratedFDeriv ℝ j f y + iteratedFDeriv ℝ j (fun _ : E => c) y :=
    iteratedFDeriv_add_apply hfj contDiffAt_const
  have e0 := iteratedFDeriv_const_of_ne (𝕜 := ℝ) (E := E) (by omega : j ≠ 0) c
  have e1 : (fun y => f y + c) = f + fun _ => c := rfl
  rw [e1, e, e0]
  simpa using hC y

theorem s81r_Bd_sum {ι : Type*} (u : Finset ι) (f : ι → E → ℝ) (h : ∀ i ∈ u, s81r_Bd (f i)) :
    s81r_Bd (fun y => ∑ i ∈ u, f i y) := by
  refine ⟨ContDiff.sum fun i hi => (h i hi).1, fun j hj => ?_⟩
  choose! C hC using fun i (hi : i ∈ u) => (h i hi).2 j hj
  refine ⟨∑ i ∈ u, |C i|, fun y => ?_⟩
  have hs : ∀ i ∈ u, ContDiff ℝ j (f i) := fun i hi => contDiff_infty.1 (h i hi).1 j
  have e : iteratedFDeriv ℝ j (fun y => ∑ i ∈ u, f i y) y = ∑ i ∈ u, iteratedFDeriv ℝ j (f i) y := by
    have := congrFun (iteratedFDeriv_sum (𝕜 := ℝ) (i := j) (u := u) (f := f) hs) y
    simpa using this
  rw [e]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  exact (hC i hi y).trans (le_abs_self _)

end Closure

variable {d : ℕ}

theorem s81r_kM_smooth (d : ℕ) (s : ℝ) (M : ℕ) : ContDiff ℝ ∞ (sb1kM d s M) := by
  have h := p4k_h_contDiff s (a := (1 / ((M : ℝ) + 1)) ^ 2) (by positivity)
  exact h.comp (contDiff_norm_sq ℝ)

theorem s81r_Bd_kM {s : ℝ} (hs : 0 ≤ s) (M : ℕ) : s81r_Bd (sb1kM d s M) := by
  refine ⟨s81r_kM_smooth d s M, fun m hm => ?_⟩
  set k := sb1kM d s M with hk
  set r : ℝ := 1 / ((M : ℝ) + 1) with hr
  have hr0 : 0 < r := by positivity
  have hker := sb1kM_isKernel (d := d) s hs M
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨C0, hC0, hC⟩ := HRS.MS.Ker1.ker1_E_bound (d := d) hs m (by linarith)
  have hkm : ContDiff ℝ m k := contDiff_infty.1 (s81r_kM_smooth d s M) m
  have hcont : Continuous (iteratedFDeriv ℝ m k) := hkm.continuous_iteratedFDeriv le_rfl
  obtain ⟨C1, hC1⟩ := (isCompact_closedBall (0 : Euc d) (2 * r)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max C1 (C0 * (2 * r) ^ (-s - (m : ℝ))), fun x => ?_⟩
  by_cases hx : ‖x‖ ≤ 2 * r
  · exact (hC1 x (mem_closedBall_zero_iff.2 hx)).trans (le_max_left _ _)
  · push_neg at hx
    have hxr : r < ‖x‖ := by linarith
    have hev : k =ᶠ[𝓝 x] Whole.rieszKernel d s := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hxr] with y hy
      exact hker.eq_far y hy.le
    have hit : iteratedFDeriv ℝ m k x = iteratedFDeriv ℝ m (Whole.rieszKernel d s) x := by
      have := Filter.EventuallyEq.iteratedFDerivWithin_eq (𝕜 := ℝ) (s := Set.univ) (x := x)
        (f₁ := k) (f := Whole.rieszKernel d s) (by rwa [nhdsWithin_univ]) hev.eq_of_nhds m
      simpa [iteratedFDerivWithin_univ] using this
    rw [hit]
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hx
      linarith
    refine (hC x hx0).trans ?_
    refine le_trans ?_ (le_max_right _ _)
    refine mul_le_mul_of_nonneg_left ?_ hC0
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hx.le (by linarith)

end HRS.MS.S81R
