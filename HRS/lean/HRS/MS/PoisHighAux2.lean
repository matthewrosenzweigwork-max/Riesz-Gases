import Mathlib
import HRS.MS.PoisHighAux1

/-!
# POIS-HIGHSM (part 2): the induction step for the higher derivative bounds (compactly supported data)

Setting: `q > 0`, a smooth drift `B` (`HasCbBound k M_k B` for every `k`) with `HasCbBound m Mb B`, a Brownian
filtration, and the class `HsData` of smooth data all of whose derivatives are bounded.

`HsBound R P W q B j C` says: for data `g ∈ HsData` in the class `R` and `K` bounding `‖D^i g‖` for
`1 ≤ i < j` (and `‖g‖` if `j = 1`), `‖D^j P_t g‖ ≤ C K / √t` for `0 < t ≤ 1`.

`hs_core`: if `HsBound` holds (for all data) at the orders `1 ≤ l < j` then it holds at order `j` for
compactly supported data, with a constant depending only on `q, Mb, j` and the constants at the lower orders.
This is the commutator Duhamel formula `hs_cd1` differentiated `j - 1` times in `x` (differentiation under the
integral sign, `sg_iteratedFDeriv_integral`); the lower order bound is applied to the data `∂_e f` and
`F_s = Du_s · (-q e + DB e)`, and the singular kernel `(s (t - s))^{-1/2}` is integrated.

Helper lemmas carry the prefix `hs_`.
-/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Interval RealInnerProductSpace ContDiff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.PoisFlow HRS.MS.PoisSg
  HRS.MS.PoisMarkov HRS.MS.PoisKolm HRS.MS.PoisGrad HRS.MS.PoisMax HRS.MS.PoisMoll
  HRS.MS.PoisHigh
open HRS.MS.FlowB (clampT continuous_clampT clampT_mem clampT_of_mem)

noncomputable section

universe u

namespace HRS.MS.PoisHigh

variable {d : ℕ}

/-- Smooth data all of whose derivatives are bounded. -/
def HsData (g : Euc d → ℝ) : Prop :=
  ContDiff ℝ ∞ g ∧ ∀ k : ℕ, ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ k g y‖ ≤ C

/-- The bound `‖D^j P_t g‖ ≤ C K / √t` for data `g` of the class `R`. -/
def HsBound {Ω : Type u} [MeasurableSpace Ω] (R : (Euc d → ℝ) → Prop) (P : Measure Ω)
    (W : ℝ≥0 → Ω → Fin d → ℝ) (q : ℝ) (B : Euc d → Euc d) (j : ℕ) (C : ℝ) : Prop :=
  ∀ g : Euc d → ℝ, HsData g → R g → ∀ K : ℝ,
    (∀ i < j, (1 ≤ i ∨ j = 1) → ∀ y, ‖iteratedFDeriv ℝ i g y‖ ≤ K) →
    ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ j (sg P W q B t g) x‖ ≤ C * K / Real.sqrt t

section Basic

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → Fin d → ℝ}

/-- `sg_s g` is again in the class, with bounds uniform in `s ∈ [0,1]`. -/
theorem hs_sg_unif [IsProbabilityMeasure P] (hW : SgNoise W) {q : ℝ} (hq : 0 < q) {B : Euc d → Euc d}
    (hBall : ∀ k, ∃ M : ℝ, HasCbBound k M B) {g : Euc d → ℝ} (hg : HsData g) (k : ℕ) :
    ∃ C : ℝ, ∀ s ∈ Icc (0 : ℝ) 1, ContDiff ℝ (k : WithTop ℕ∞) (sg P W q B s g) ∧
      ∀ y, ‖iteratedFDeriv ℝ k (sg P W q B s g) y‖ ≤ C := by
  obtain ⟨M, hM⟩ := hBall (max k 2)
  choose Cg hCg using hg.2
  set M' : ℝ := ∑ i ∈ Finset.range (k + 1), |Cg i| with hM'
  have hM'b : ∀ i ≤ k, ∀ y, ‖iteratedFDeriv ℝ i g y‖ ≤ M' := fun i hi y =>
    (hCg i y).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |Cg i|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (by omega))))
  obtain ⟨C, -, hC⟩ := sg_contDiff (d := d) q M hq (max k 2) (le_max_right _ _) 1 zero_le_one k
    (le_max_left _ _)
  refine ⟨C * M', fun s hs => ?_⟩
  obtain ⟨h1, -, h3⟩ := hC P W hW B hM g (hg.1.of_le (by exact_mod_cast le_top)) M' hM'b s hs
  exact ⟨h1, fun y => h3 k le_rfl y⟩

theorem hs_sg_hsdata [IsProbabilityMeasure P] (hW : SgNoise W) {q : ℝ} (hq : 0 < q) {B : Euc d → Euc d}
    (hBall : ∀ k, ∃ M : ℝ, HasCbBound k M B) {g : Euc d → ℝ} (hg : HsData g) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : HsData (sg P W q B s g) := by
  refine ⟨contDiff_infty.2 fun n => ?_, fun k => ?_⟩
  · obtain ⟨C, hC⟩ := hs_sg_unif (P := P) (W := W) hW hq hBall hg n
    exact (hC s hs).1
  · obtain ⟨C, hC⟩ := hs_sg_unif (P := P) (W := W) hW hq hBall hg k
    exact ⟨C, (hC s hs).2⟩

end Basic

/-- Leibniz bound for `F = Du · (-q e + DB e)`. -/
theorem hs_F_bound {u : Euc d → ℝ} {B : Euc d → Euc d} (hu : ContDiff ℝ ∞ u) (hB : ContDiff ℝ ∞ B)
    (e : Euc d) (he : ‖e‖ = 1) {q : ℝ} (hq : 0 ≤ q) {n : ℕ} {N Mb' : ℝ}
    (hN : ∀ l, 1 ≤ l → l ≤ n + 1 → ∀ y, ‖iteratedFDeriv ℝ l u y‖ ≤ N)
    (hMb : ∀ k ≤ n, ∀ y, ‖iteratedFDeriv ℝ (k + 1) B y‖ ≤ Mb') (y : Euc d) :
    ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ u y (-q • e + fderiv ℝ B y e)) y‖ ≤
      (q + 2 ^ n * Mb') * N := by
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 1 le_rfl (by omega) y)
  have hMb0 : 0 ≤ Mb' := (norm_nonneg _).trans (hMb 0 (by omega) y)
  have hfu : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hfB : ContDiff ℝ ∞ (fderiv ℝ B) := hB.fderiv_right (by simp)
  have hβ : ContDiff ℝ ∞ (fun y => fderiv ℝ B y e) := hfB.clm_apply contDiff_const
  have hsplit : (fun y => fderiv ℝ u y (-q • e + fderiv ℝ B y e)) =
      (fun y => fderiv ℝ u y (-q • e)) + (fun y => fderiv ℝ u y (fderiv ℝ B y e)) := by
    funext y; simp [map_add]
  have hn : ((n : ℕ) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by exact_mod_cast le_top
  have c1 : ContDiff ℝ ∞ (fun y => fderiv ℝ u y (-q • e)) := hfu.clm_apply contDiff_const
  have c2 : ContDiff ℝ ∞ (fun y => fderiv ℝ u y (fderiv ℝ B y e)) := hfu.clm_apply hβ
  rw [hsplit, iteratedFDeriv_add_apply (c1.contDiffAt.of_le hn) (c2.contDiffAt.of_le hn)]
  refine (norm_add_le _ _).trans ?_
  have t1 : ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ u y (-q • e)) y‖ ≤ q * N := by
    have := norm_iteratedFDeriv_clm_apply_const (c := -q • e) (x := y) (n := n) (N := (n : WithTop ℕ∞))
      (hfu.contDiffAt.of_le hn) le_rfl
    rw [norm_iteratedFDeriv_fderiv] at this
    refine this.trans ?_
    rw [norm_smul, norm_neg, Real.norm_of_nonneg hq, he, mul_one]
    exact mul_le_mul_of_nonneg_left (hN (n + 1) (by omega) le_rfl y) hq
  have t2 : ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ u y (fderiv ℝ B y e)) y‖ ≤ 2 ^ n * Mb' * N := by
    have := (ContinuousLinearMap.id ℝ (Euc d →L[ℝ] ℝ)).norm_iteratedFDeriv_le_of_bilinear
      (f := fderiv ℝ u) (g := fun y => fderiv ℝ B y e) (N := (n : WithTop ℕ∞))
      (hfu.of_le hn) (hβ.of_le hn) y le_rfl
    simp only [ContinuousLinearMap.id_apply] at this
    refine this.trans ?_
    have hid : ‖ContinuousLinearMap.id ℝ (Euc d →L[ℝ] ℝ)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have key : ∀ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fderiv ℝ u) y‖ *
        ‖iteratedFDeriv ℝ (n - i) (fun y => fderiv ℝ B y e) y‖ ≤ (n.choose i : ℝ) * N * Mb' := by
      intro i hi
      have hi' : i ≤ n := by simpa [Nat.lt_succ_iff] using hi
      have a1 : ‖iteratedFDeriv ℝ i (fderiv ℝ u) y‖ ≤ N := by
        rw [norm_iteratedFDeriv_fderiv]; exact hN (i + 1) (by omega) (by omega) y
      have a2 : ‖iteratedFDeriv ℝ (n - i) (fun y => fderiv ℝ B y e) y‖ ≤ Mb' := by
        have := norm_iteratedFDeriv_clm_apply_const (c := e) (x := y) (n := n - i)
          (N := (n : WithTop ℕ∞)) (f := fderiv ℝ B) (hfB.contDiffAt.of_le hn)
          (by exact_mod_cast Nat.sub_le n i)
        rw [norm_iteratedFDeriv_fderiv, he, one_mul] at this
        exact this.trans (hMb (n - i) (Nat.sub_le n i) y)
      have hc : (0 : ℝ) ≤ n.choose i := Nat.cast_nonneg _
      gcongr
    have hsum : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * N * Mb' = 2 ^ n * Mb' * N := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      have : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) = 2 ^ n := by
        exact_mod_cast Nat.sum_range_choose n
      rw [this]; ring
    have h1 := mul_le_mul hid (Finset.sum_le_sum key) (Finset.sum_nonneg fun i _ => by positivity)
      zero_le_one
    rw [hsum, one_mul] at h1
    exact h1
  nlinarith

/-- Aggregation of directions: bounds on `D^{j-1}(∂_e φ)` for unit `e` bound `D^j φ`. -/
theorem hs_dir_agg {φ : Euc d → ℝ} {j : ℕ} (hj : 1 ≤ j) (hφ : ContDiff ℝ (j : WithTop ℕ∞) φ)
    {x : Euc d} {A : ℝ} (hA : 0 ≤ A)
    (h : ∀ e : Euc d, ‖e‖ = 1 → ‖iteratedFDeriv ℝ (j - 1) (gsD e φ) x‖ ≤ A) :
    ‖iteratedFDeriv ℝ j φ x‖ ≤ A := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  replace h : ∀ e : Euc d, ‖e‖ = 1 → ‖iteratedFDeriv ℝ n (gsD e φ) x‖ ≤ A := by simpa using h
  have hfd : ContDiff ℝ (n : WithTop ℕ∞) (fderiv ℝ φ) :=
    hφ.fderiv_right (m := n) (by exact_mod_cast le_refl _)
  rw [← norm_iteratedFDeriv_fderiv]
  set T := iteratedFDeriv ℝ n (fderiv ℝ φ) x with hT
  have hTe : ∀ (e : Euc d) (m : Fin n → Euc d), iteratedFDeriv ℝ n (gsD e φ) x m = T m e := by
    intro e m
    have := (ContinuousLinearMap.apply ℝ ℝ e).iteratedFDeriv_comp_left (f := fderiv ℝ φ)
      (x := x) (n := (n : WithTop ℕ∞)) hfd.contDiffAt (i := n) le_rfl
    have e1 : gsD e φ = ⇑(ContinuousLinearMap.apply ℝ ℝ e) ∘ fderiv ℝ φ := by
      funext y; rfl
    rw [e1, this]
    rfl
  refine ContinuousMultilinearMap.opNorm_le_bound hA (fun m => ?_)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun e => ?_)
  by_cases he : e = 0
  · subst he; simp
  have hne : 0 < ‖e‖ := norm_pos_iff.2 he
  set e' : Euc d := ‖e‖⁻¹ • e with he'
  have h1 : ‖iteratedFDeriv ℝ n (gsD e' φ) x‖ ≤ A :=
    h e' (by rw [he', norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hne.ne'])
  have h2 : ‖T m e'‖ ≤ ‖iteratedFDeriv ℝ n (gsD e' φ) x‖ * ∏ i, ‖m i‖ := by
    have := (iteratedFDeriv ℝ n (gsD e' φ) x).le_opNorm m
    rwa [hTe] at this
  have hp : 0 ≤ ∏ i, ‖m i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
  have h4 : ‖T m e'‖ ≤ A * ∏ i, ‖m i‖ := h2.trans (mul_le_mul_of_nonneg_right h1 hp)
  have h3 : T m e' = ‖e‖⁻¹ • T m e := by rw [he']; exact map_smul _ _ _
  rw [h3, norm_smul, norm_inv, norm_norm] at h4
  have h5 : ‖T m e‖ ≤ ‖e‖ * (A * ∏ i, ‖m i‖) := by
    have := mul_le_mul_of_nonneg_left h4 hne.le
    rwa [← mul_assoc, mul_inv_cancel₀ hne.ne', one_mul] at this
  calc ‖T m e‖ ≤ ‖e‖ * (A * ∏ i, ‖m i‖) := h5
    _ = (A * ∏ i, ‖m i‖) * ‖e‖ := by ring

/-! ### The singular kernel -/

/-- A dominating function for `s^{-1/2} (t - s)^{-1/2}` on `(0,t)` with integral at most `6`. -/
theorem hs_kernel {t : ℝ} (ht : 0 < t) :
    ∃ g : ℝ → ℝ, IntegrableOn g (Ioo 0 t) volume ∧
      (∀ s ∈ Ioo (0 : ℝ) t, (Real.sqrt s)⁻¹ * (Real.sqrt (t - s))⁻¹ ≤ g s) ∧
      ∫ s in Ioo 0 t, g s ≤ 6 := by
  set c : ℝ := Real.sqrt (2 / t) with hc
  refine ⟨fun s => c * (s ^ (-(1 / 2 : ℝ)) + (t - s) ^ (-(1 / 2 : ℝ))), ?_, ?_, ?_⟩
  · have h1 : IntervalIntegrable (fun s : ℝ => s ^ (-(1 / 2 : ℝ))) volume 0 t :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have h2 : IntervalIntegrable (fun s : ℝ => (t - s) ^ (-(1 / 2 : ℝ))) volume 0 t := by
      have := h1.comp_sub_left t
      rw [sub_self, sub_zero] at this
      exact this.symm
    have := (h1.add h2).const_mul c
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).1 this
  · intro s hs
    have hs0 : 0 < s := hs.1
    have hts : 0 < t - s := by linarith [hs.2]
    have e1 : s ^ (-(1 / 2 : ℝ)) = (Real.sqrt s)⁻¹ := by
      rw [Real.rpow_neg hs0.le, Real.sqrt_eq_rpow]
    have e2 : (t - s) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (t - s))⁻¹ := by
      rw [Real.rpow_neg hts.le, Real.sqrt_eq_rpow]
    beta_reduce
    rw [e1, e2]
    have hinv : ∀ a : ℝ, 0 < a → t / 2 ≤ a → (Real.sqrt a)⁻¹ ≤ c := by
      intro a ha hta
      rw [hc, ← Real.sqrt_inv]
      refine Real.sqrt_le_sqrt ?_
      rw [inv_eq_one_div, div_le_div_iff₀ ha ht]
      linarith
    have p1 : 0 < (Real.sqrt s)⁻¹ := by positivity
    have p2 : 0 < (Real.sqrt (t - s))⁻¹ := by positivity
    rcases le_total (t / 2) s with h | h
    · have := hinv s hs0 h
      nlinarith
    · have := hinv (t - s) hts (by linarith)
      nlinarith
  · have hI : ∫ s in Ioo 0 t, c * (s ^ (-(1 / 2 : ℝ)) + (t - s) ^ (-(1 / 2 : ℝ))) =
        c * (2 * Real.sqrt t + 2 * Real.sqrt t) := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.le,
        intervalIntegral.integral_const_mul]
      congr 1
      have h1 : IntervalIntegrable (fun s : ℝ => s ^ (-(1 / 2 : ℝ))) volume 0 t :=
        intervalIntegral.intervalIntegrable_rpow' (by norm_num)
      have h2 : IntervalIntegrable (fun s : ℝ => (t - s) ^ (-(1 / 2 : ℝ))) volume 0 t := by
        have := h1.comp_sub_left t
        rw [sub_self, sub_zero] at this
        exact this.symm
      rw [intervalIntegral.integral_add h1 h2]
      have i1 : ∫ s in (0 : ℝ)..t, s ^ (-(1 / 2 : ℝ)) = 2 * Real.sqrt t := by
        rw [integral_rpow (Or.inl (by norm_num))]
        rw [Real.sqrt_eq_rpow, Real.zero_rpow (by norm_num)]
        norm_num; ring
      have i2 : ∫ s in (0 : ℝ)..t, (t - s) ^ (-(1 / 2 : ℝ)) = 2 * Real.sqrt t := by
        rw [intervalIntegral.integral_comp_sub_left (fun s : ℝ => s ^ (-(1 / 2 : ℝ))) t]
        simpa using i1
      rw [i1, i2]
    rw [hI]
    have h2 : c * (2 * Real.sqrt t + 2 * Real.sqrt t) = 4 * Real.sqrt 2 := by
      have : Real.sqrt (2 / t) * Real.sqrt t = Real.sqrt 2 := by
        rw [← Real.sqrt_mul (by positivity)]
        congr 1; field_simp
      rw [hc]
      linear_combination 4 * this
    rw [h2]
    have : Real.sqrt 2 ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    linarith

/-! ### Joint continuity and boundedness of the forcing -/

section Fc

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → Fin d → ℝ}

set_option maxHeartbeats 1000000 in
theorem hs_Fc [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {q M3 : ℝ} (hq : 0 < q)
    {B : Euc d → Euc d} (hB : HasCbBound 3 M3 B) {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (e : Euc d) :
    Continuous (fun p : ℝ × Euc d =>
      fderiv ℝ (sg P W q B (clampT 1 p.1) f) p.2 (-q • e + fderiv ℝ B p.2 e)) ∧
    ∃ KF : ℝ, ∀ r y, |fderiv ℝ (sg P W q B (clampT 1 r) f) y (-q • e + fderiv ℝ B y e)| ≤ KF := by
  have hWs := sgNoise_of_brownian hW
  obtain ⟨C, -, hC⟩ := hfc.exists_bound_iteratedFDeriv hf 3
  have hM0 : ∀ y, ‖f y‖ ≤ C := fun y => by
    have := hC 0 (by norm_num) y; rwa [norm_iteratedFDeriv_zero] at this
  have hM1 : ∀ y, ‖fderiv ℝ f y‖ ≤ C := fun y => by
    have := hC 1 (by norm_num) y; rwa [norm_iteratedFDeriv_one] at this
  have hM2 : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ C := fun y => hC 2 (by norm_num) y
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hKf := pois_kolmogorov hq (m := 3) (by norm_num) hB hW hf2 hM1 hM2
  have hI1 := hKf.2.2.2 1 one_pos
  have hB2 : ContDiff ℝ 2 B := hB.1.of_le (by norm_num)
  have hB1 : ∀ y, ‖fderiv ℝ B y‖ ≤ M3 := fun y => by
    have := hB.2 1 (by norm_num) y; rwa [norm_iteratedFDeriv_one] at this
  have hcl : Continuous fun p : ℝ × Euc d => ((clampT 1 p.1, p.2) : ℝ × Euc d) :=
    ((continuous_clampT 1).comp continuous_fst).prodMk continuous_snd
  have hclm : ∀ p : ℝ × Euc d,
      ((clampT 1 p.1, p.2) : ℝ × Euc d) ∈ Icc (0 : ℝ) 1 ×ˢ (univ : Set (Euc d)) :=
    fun p => ⟨clampT_mem zero_le_one _, mem_univ _⟩
  refine ⟨?_, ⟨Real.exp (q + M3) * C * (q * ‖e‖ + M3 * ‖e‖), fun r y => ?_⟩⟩
  · have hb : Continuous fun y : Euc d => -q • e + fderiv ℝ B y e :=
      continuous_const.add ((hB2.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    have h1 : ContinuousOn (fun p : ℝ × Euc d =>
        fderiv ℝ (sg P W q B p.1 f) p.2 (-q • e + fderiv ℝ B p.2 e)) (Icc 0 1 ×ˢ univ) :=
      hI1.cont_fderiv.clm_apply (hb.comp continuous_snd).continuousOn
    exact h1.comp_continuous hcl hclm
  · have hDf := hs_D_bd (P := P) hWs hq (by norm_num) hB hf2 hM0 hM1 (clampT_mem zero_le_one r) y
    have h1 := (fderiv ℝ (sg P W q B (clampT 1 r) f) y).le_opNorm (-q • e + fderiv ℝ B y e)
    rw [Real.norm_eq_abs] at h1
    have h2 : ‖-q • e + fderiv ℝ B y e‖ ≤ q * ‖e‖ + M3 * ‖e‖ := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, norm_neg, Real.norm_of_nonneg hq.le]
      · exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hB1 y) (norm_nonneg _))
    exact h1.trans (mul_le_mul hDf h2 (norm_nonneg _)
      ((norm_nonneg _).trans (hs_D_bd (P := P) hWs hq (by norm_num) hB hf2 hM0 hM1
        (⟨le_rfl, zero_le_one⟩ : (0 : ℝ) ∈ Icc (0 : ℝ) 1) 0)))

end Fc

/-! ### The forcing family -/

section Family

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → Fin d → ℝ}

theorem hs_gsD_hsdata {g : Euc d → ℝ} (hg : HsData g) (e : Euc d) : HsData (gsD e g) := by
  refine ⟨?_, fun k => ?_⟩
  · have := hg.1.fderiv_right (m := ∞) (by simp)
    exact this.clm_apply contDiff_const
  · obtain ⟨C, hC⟩ := hg.2 (k + 1)
    refine ⟨‖e‖ * C, fun y => (hs_gsD_norm ?_ e y).trans
      (mul_le_mul_of_nonneg_left (hC y) (norm_nonneg _))⟩
    exact hg.1.of_le (by exact_mod_cast le_top)

theorem hs_F_hsdata {u : Euc d → ℝ} (hu : HsData u) {B : Euc d → Euc d}
    (hBall : ∀ k, ∃ M : ℝ, HasCbBound k M B) (e : Euc d) (he : ‖e‖ = 1) {q : ℝ} (hq : 0 ≤ q) :
    HsData (fun y => fderiv ℝ u y (-q • e + fderiv ℝ B y e)) := by
  have hBc : ContDiff ℝ ∞ B := contDiff_infty.2 fun n => (hBall n).elim fun M h => h.1
  refine ⟨?_, fun k => ?_⟩
  · exact (hu.1.fderiv_right (by simp)).clm_apply
      (contDiff_const.add ((hBc.fderiv_right (by simp)).clm_apply contDiff_const))
  · choose Cu hCu using hu.2
    obtain ⟨M, hM⟩ := hBall (k + 1)
    refine ⟨(q + 2 ^ k * M) * ∑ l ∈ Finset.range (k + 2), |Cu l|, fun y => ?_⟩
    refine hs_F_bound hu.1 hBc e he hq (fun l _ hl y' => ?_) (fun k' hk' y' => ?_) y
    · exact (hCu l y').trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun l => |Cu l|)
        (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (by omega))))
    · exact hM.2 (k' + 1) (by omega) y'

theorem hs_Fam_unif [IsProbabilityMeasure P] (hW : SgNoise W) {q : ℝ} (hq : 0 < q)
    {B : Euc d → Euc d} (hBall : ∀ k, ∃ M : ℝ, HasCbBound k M B) {f : Euc d → ℝ} (hf : HsData f)
    (e : Euc d) (he : ‖e‖ = 1) (n : ℕ) :
    ∃ M : ℝ, ∀ s ∈ Icc (0 : ℝ) 1, ∀ l ≤ n, ∀ y,
      ‖iteratedFDeriv ℝ l (fun y => fderiv ℝ (sg P W q B s f) y (-q • e + fderiv ℝ B y e)) y‖ ≤ M := by
  have hBc : ContDiff ℝ ∞ B := contDiff_infty.2 fun n => (hBall n).elim fun M h => h.1
  choose Cu hCu using fun l => hs_sg_unif (P := P) hW hq hBall hf l
  obtain ⟨M, hM⟩ := hBall (n + 1)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM.2 0 (by omega) 0)
  have hN : ∀ s ∈ Icc (0 : ℝ) 1, ∀ l, 1 ≤ l → l ≤ n + 1 → ∀ y,
      ‖iteratedFDeriv ℝ l (sg P W q B s f) y‖ ≤ ∑ l ∈ Finset.range (n + 2), |Cu l| := by
    intro s hs l _ hl y
    exact ((hCu l s hs).2 y).trans ((le_abs_self _).trans (Finset.single_le_sum
      (f := fun l => |Cu l|) (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (by omega))))
  have hN0 : 0 ≤ ∑ l ∈ Finset.range (n + 2), |Cu l| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨(q + 2 ^ n * M) * ∑ l ∈ Finset.range (n + 2), |Cu l|, fun s hs l hl y => ?_⟩
  have hu : ContDiff ℝ ∞ (sg P W q B s f) :=
    (hs_sg_hsdata (P := P) hW hq hBall hf hs).1
  refine (hs_F_bound hu hBc e he hq.le (n := l) (fun l' h1 h2 y' => hN s hs l' h1 (by omega) y')
    (fun k' hk' y' => hM.2 (k' + 1) (by omega) y') y).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ hN0
  have : (2 : ℝ) ^ l ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hl
  nlinarith

end Family

/-! ### The induction step -/

/-- the constant `A = (q + 2^j Mb) (e^{q+Mb} + ∑ |C_l|)` -/
def hsA (q Mb : ℝ) (j : ℕ) (Cs : ℕ → ℝ) : ℝ :=
  (q + 2 ^ j * Mb) * (Real.exp (q + Mb) + ∑ l ∈ Finset.range j, |Cs l|)

/-- the constant of the induction step -/
def hsC (q Mb : ℝ) (j : ℕ) (Cs : ℕ → ℝ) : ℝ := |Cs (j - 1)| * (1 + 6 * hsA q Mb j Cs)

section Core

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → Fin d → ℝ}

set_option maxHeartbeats 4000000 in
/-- Per-direction bound on `D^{j-1} ∂_e u_t`. -/
theorem hs_core_dir [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {q Mb : ℝ}
    (hq : 0 < q) {m j : ℕ} (hj : 2 ≤ j) (hjm : j ≤ m) {B : Euc d → Euc d}
    (hBm : HasCbBound m Mb B) (hBall : ∀ k, ∃ M : ℝ, HasCbBound k M B) (Cs : ℕ → ℝ)
    (hIH : ∀ l, 1 ≤ l → l < j → HsBound (fun _ => True) P W q B l (Cs l))
    {f : Euc d → ℝ} (hf : HsData f) (hfc : HasCompactSupport f) {K : ℝ}
    (hK : ∀ i < j, (1 ≤ i ∨ j = 1) → ∀ y, ‖iteratedFDeriv ℝ i f y‖ ≤ K)
    (e : Euc d) (he : ‖e‖ = 1) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (x : Euc d) :
    ‖iteratedFDeriv ℝ (j - 1) (gsD e (sg P W q B t f)) x‖ ≤
      hsC q Mb j Cs * K / Real.sqrt t := by
  have hWs := sgNoise_of_brownian hW
  have hm2 : 2 ≤ m := by omega
  have hMb : 0 ≤ Mb := (norm_nonneg _).trans (by simpa using hBm.2 0 (Nat.zero_le _) 0)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 1 (by omega) (Or.inl le_rfl) 0)
  obtain ⟨M3, hB3⟩ := hBall 3
  have hBc : ContDiff ℝ ∞ B := contDiff_infty.2 fun n => (hBall n).elim fun M h => h.1
  have hsq : ∀ s : ℝ, 0 < s → s ≤ 1 → 1 ≤ (Real.sqrt s)⁻¹ := fun s hs0 hs1 => by
    rw [one_le_inv₀ (Real.sqrt_pos.2 hs0)]
    exact Real.sqrt_le_one.2 hs1
  set Cmax : ℝ := Real.exp (q + Mb) + ∑ l ∈ Finset.range j, |Cs l| with hCmax
  have hCmax0 : 0 ≤ Cmax := by positivity
  set A : ℝ := hsA q Mb j Cs with hAdef
  have hA0 : 0 ≤ A := by
    have : 0 ≤ q + 2 ^ j * Mb := by positivity
    exact mul_nonneg this hCmax0
  -- bounds on `D^l u_s`
  have hDu : ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ l, 1 ≤ l → l ≤ j - 1 → ∀ y,
      ‖iteratedFDeriv ℝ l (sg P W q B s f) y‖ ≤ Cmax * K / Real.sqrt s := by
    intro s hs0 hs1 l hl1 hl2 y
    have hsqs := hsq s hs0 hs1
    have hdiv : ∀ c : ℝ, 0 ≤ c → c * K ≤ c * K / Real.sqrt s := fun c hc => by
      rw [div_eq_mul_inv]
      exact le_mul_of_one_le_right (mul_nonneg hc hK0) hsqs
    rcases Nat.eq_or_lt_of_le hl1 with h1 | h1
    · subst h1
      obtain ⟨M0, hM0⟩ := hf.2 0
      have hh : ContDiff ℝ 2 f := hf.1.of_le (by norm_num)
      have hM1 : ∀ y, ‖fderiv ℝ f y‖ ≤ K := fun y => by
        have := hK 1 (by omega) (Or.inl le_rfl) y
        rwa [norm_iteratedFDeriv_one] at this
      have := hs_D_bd (P := P) hWs hq hm2 hBm hh (fun y => by simpa using hM0 y) hM1
        (⟨hs0.le, hs1⟩ : s ∈ Icc (0 : ℝ) 1) y
      rw [norm_iteratedFDeriv_one]
      refine this.trans ((mul_le_mul_of_nonneg_right ?_ hK0).trans (hdiv _ hCmax0))
      rw [hCmax]
      have : 0 ≤ ∑ l ∈ Finset.range j, |Cs l| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith
    · have := hIH l (by omega) (by omega) f hf trivial K
        (fun i hi hi' => hK i (by omega) (Or.inl (by omega))) s hs0 hs1 y
      refine this.trans ?_
      have hc : Cs l ≤ Cmax := by
        refine (le_abs_self _).trans ?_
        rw [hCmax]
        have := Finset.single_le_sum (f := fun l => |Cs l|) (fun _ _ => abs_nonneg _)
          (Finset.mem_range.2 (show l < j by omega))
        have := Real.exp_pos (q + Mb)
        linarith
      rw [div_le_div_iff_of_pos_right (Real.sqrt_pos.2 hs0)]
      exact mul_le_mul_of_nonneg_right hc hK0
  have hAeq : A = (q + 2 ^ j * Mb) * Cmax := by rw [hAdef, hsA]
  -- bounds on `D^i F_s`
  have hFs : ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ i, i + 1 ≤ j - 1 → ∀ y,
      ‖iteratedFDeriv ℝ i (fun y => fderiv ℝ (sg P W q B s f) y (-q • e + fderiv ℝ B y e)) y‖ ≤
        A * K / Real.sqrt s := by
    intro s hs0 hs1 i hi y
    have hu := (hs_sg_hsdata (P := P) hWs hq hBall hf ⟨hs0.le, hs1⟩).1
    have h1 := hs_F_bound hu hBc e he hq.le (n := i) (N := Cmax * K / Real.sqrt s) (Mb' := Mb)
      (fun l hl1 hl2 y' => hDu s hs0 hs1 l hl1 (by omega) y')
      (fun k' hk' y' => hBm.2 (k' + 1) (by omega) y') y
    refine h1.trans ?_
    have h2 : (q + 2 ^ i * Mb) ≤ q + 2 ^ j * Mb := by
      have : (2 : ℝ) ^ i ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith
    have h3 : 0 ≤ Cmax * K / Real.sqrt s := by positivity
    calc (q + 2 ^ i * Mb) * (Cmax * K / Real.sqrt s)
        ≤ (q + 2 ^ j * Mb) * (Cmax * K / Real.sqrt s) := mul_le_mul_of_nonneg_right h2 h3
      _ = A * K / Real.sqrt s := by rw [hAeq]; ring
  -- the forcing family and the commutator formula
  obtain ⟨hFcc, KF, hKF⟩ := hs_Fc hW hq hB3 hf.1 hfc e
  obtain ⟨Fc, hFc⟩ : ∃ Fc : ℝ → Euc d → ℝ, ∀ r y,
      Fc r y = fderiv ℝ (sg P W q B (clampT 1 r) f) y (-q • e + fderiv ℝ B y e) :=
    ⟨fun r y => _, fun _ _ => rfl⟩
  have hFcc' : Continuous fun p : ℝ × Euc d => Fc p.1 p.2 :=
    hFcc.congr fun p => (hFc _ _).symm
  have hKF' : ∀ r y, |Fc r y| ≤ KF := fun r y => by rw [hFc]; exact hKF r y
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → Euc d → ℝ, ∀ s x,
      G s x = sg P W q B (t - clampT t s) (Fc (clampT t s)) x := ⟨fun s x => _, fun _ _ => rfl⟩
  have hclt : ∀ s, clampT t s ∈ Icc (0 : ℝ) t := fun s => clampT_mem ht0.le s
  have hGc : Continuous fun p : ℝ × Euc d => G p.1 p.2 := by
    have h := hs_cont_sg hW hq hm2 hBm (T := 1) zero_le_one hFcc' hKF'
    have hψ : Continuous fun p : ℝ × Euc d =>
        ((clampT t p.1, t - clampT t p.1, p.2) : ℝ × ℝ × Euc d) := by
      have : Continuous fun p : ℝ × Euc d => clampT t p.1 := (continuous_clampT t).comp continuous_fst
      exact (this.prodMk ((continuous_const.sub this).prodMk continuous_snd))
    have := h.comp_continuous hψ (fun p => ⟨by linarith [(hclt p.1).2], by linarith [(hclt p.1).1]⟩)
    exact this.congr fun p => (hGdef _ _).symm
  have hGIoo : ∀ s ∈ Ioo (0 : ℝ) t, ∀ x, G s x = sg P W q B (t - s)
      (fun y => fderiv ℝ (sg P W q B s f) y (-q • e + fderiv ℝ B y e)) x := by
    intro s hs x
    rw [hGdef, clampT_of_mem (⟨hs.1.le, hs.2.le⟩ : s ∈ Icc (0 : ℝ) t)]
    congr 1
    funext y
    rw [hFc, clampT_of_mem (⟨hs.1.le, by linarith [hs.2]⟩ : s ∈ Icc (0 : ℝ) 1)]
  have hfun : gsD e (sg P W q B t f) =
      fun x => sg P W q B t (gsD e f) x + ∫ s in Ioo 0 t, G s x := by
    funext x
    have h1 := hs_cd1 hW hq hB3 hf.1 hfc e ⟨ht0.le, ht1⟩ x
    have h2 : ∫ s in (0 : ℝ)..t, sg P W q B (t - s)
        (fun y => fderiv ℝ (sg P W q B s f) y (-q • e + fderiv ℝ B y e)) x =
        ∫ s in Ioo 0 t, G s x := by
      rw [intervalIntegral.integral_of_le ht0.le, integral_Ioc_eq_integral_Ioo]
      exact setIntegral_congr_fun measurableSet_Ioo (fun s hs => (hGIoo s hs x).symm)
    rw [← h2]
    exact h1
  -- differentiation under the integral sign
  have hle : ((j - 1 : ℕ) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
    generalize j - 1 = n
    exact_mod_cast le_top
  have hFdata : ∀ s ∈ Icc (0 : ℝ) 1,
      HsData (fun y => fderiv ℝ (sg P W q B s f) y (-q • e + fderiv ℝ B y e)) := fun s hs =>
    hs_F_hsdata (hs_sg_hsdata (P := P) hWs hq hBall hf hs) hBall e he hq.le
  have hGsm : ∀ s, ContDiff ℝ ((j - 1 : ℕ) : WithTop ℕ∞) (G s) := by
    intro s
    have hs1 : clampT 1 (clampT t s) ∈ Icc (0 : ℝ) 1 := clampT_mem zero_le_one _
    have hFd : HsData (Fc (clampT t s)) := by
      have : Fc (clampT t s) = fun y => fderiv ℝ (sg P W q B (clampT 1 (clampT t s)) f) y
          (-q • e + fderiv ℝ B y e) := funext fun y => hFc _ _
      rw [this]; exact hFdata _ hs1
    have hτ : t - clampT t s ∈ Icc (0 : ℝ) 1 :=
      ⟨by linarith [(hclt s).2], by linarith [(hclt s).1]⟩
    have hGs : G s = sg P W q B (t - clampT t s) (Fc (clampT t s)) := funext fun x => hGdef s x
    rw [hGs]
    exact (hs_sg_hsdata (P := P) hWs hq hBall hFd hτ).1.of_le hle
  obtain ⟨Mf, hMf⟩ := hs_Fam_unif (P := P) hWs hq hBall hf e he (j - 1)
  obtain ⟨Csg, -, hCsg⟩ := sg_contDiff (d := d) q Mb hq m hm2 1 zero_le_one (j - 1) (by omega)
  have hbd : ∀ i ≤ j - 1, ∃ M : ℝ, ∀ s y, ‖iteratedFDeriv ℝ i (G s) y‖ ≤ M := by
    intro i hi
    refine ⟨Csg * Mf, fun s y => ?_⟩
    have hs1 : clampT 1 (clampT t s) ∈ Icc (0 : ℝ) 1 := clampT_mem zero_le_one _
    have hFeq : Fc (clampT t s) = fun y => fderiv ℝ (sg P W q B (clampT 1 (clampT t s)) f) y
        (-q • e + fderiv ℝ B y e) := funext fun y => hFc _ _
    have hFd : HsData (Fc (clampT t s)) := by rw [hFeq]; exact hFdata _ hs1
    have hτ : t - clampT t s ∈ Icc (0 : ℝ) 1 :=
      ⟨by linarith [(hclt s).2], by linarith [(hclt s).1]⟩
    have hGs : G s = sg P W q B (t - clampT t s) (Fc (clampT t s)) := funext fun x => hGdef s x
    obtain ⟨-, -, h3⟩ := hCsg P W hWs B hBm (Fc (clampT t s))
      (hFd.1.of_le hle) Mf
      (fun l hl y' => by rw [hFeq]; exact hMf _ hs1 l (by omega) y') (t - clampT t s) hτ
    rw [hGs]
    exact h3 i hi y
  have hmeas : ∀ i ≤ j - 1, ∀ y, AEStronglyMeasurable (fun s => iteratedFDeriv ℝ i (G s) y)
      (volume.restrict (Ioo (0 : ℝ) t)) := by
    intro i hi y
    have := sg_stronglyMeasurable_iteratedFDeriv G hGc.stronglyMeasurable i
      (fun s => (hGsm s).of_le (by exact_mod_cast hi))
    exact (this.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  obtain ⟨hΦcd, hΦform⟩ := sg_iteratedFDeriv_integral (μ := volume.restrict (Ioo (0 : ℝ) t)) G
    (j - 1) hGsm hbd hmeas
  -- bound for the integral term
  have hAK : 0 ≤ A * K := mul_nonneg hA0 hK0
  have hΦbd : ‖iteratedFDeriv ℝ (j - 1) (fun x => ∫ s in Ioo 0 t, G s x) x‖ ≤
      6 * (|Cs (j - 1)| * (A * K)) := by
    rw [hΦform (j - 1) le_rfl x]
    obtain ⟨g, hgi, hgle, hgint⟩ := hs_kernel ht0
    have hcc : 0 ≤ |Cs (j - 1)| * (A * K) := mul_nonneg (abs_nonneg _) hAK
    have h1 := norm_integral_le_of_norm_le (μ := volume.restrict (Ioo (0 : ℝ) t))
      (f := fun s => iteratedFDeriv ℝ (j - 1) (G s) x)
      (g := fun s => |Cs (j - 1)| * (A * K) * g s) (hgi.const_mul _) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
        have hGs : G s = sg P W q B (t - s)
            (fun y => fderiv ℝ (sg P W q B s f) y (-q • e + fderiv ℝ B y e)) :=
          funext fun y => hGIoo s hs y
        rw [hGs]
        have hs1 : s ≤ 1 := by linarith [hs.2]
        have hts : 0 < t - s := by linarith [hs.2]
        have h2 := hIH (j - 1) (by omega) (by omega) _
          (hFdata s ⟨hs.1.le, hs1⟩) trivial (A * K / Real.sqrt s)
          (fun i hi _ y => hFs s hs.1 hs1 i (by omega) y) (t - s) hts (by linarith [hs.1, ht1]) x
        refine h2.trans ?_
        have hss : 0 < Real.sqrt s := Real.sqrt_pos.2 hs.1
        have hst : 0 < Real.sqrt (t - s) := Real.sqrt_pos.2 hts
        have e1 : Cs (j - 1) * (A * K / Real.sqrt s) / Real.sqrt (t - s) =
            Cs (j - 1) * (A * K) * ((Real.sqrt s)⁻¹ * (Real.sqrt (t - s))⁻¹) := by
          field_simp
        rw [e1]
        calc Cs (j - 1) * (A * K) * ((Real.sqrt s)⁻¹ * (Real.sqrt (t - s))⁻¹)
            ≤ |Cs (j - 1)| * (A * K) * ((Real.sqrt s)⁻¹ * (Real.sqrt (t - s))⁻¹) := by
              gcongr
              exact le_abs_self _
          _ ≤ |Cs (j - 1)| * (A * K) * g s := mul_le_mul_of_nonneg_left (hgle s hs) hcc)
    refine h1.trans ?_
    rw [integral_const_mul]
    nlinarith [mul_le_mul_of_nonneg_left hgint hcc]
  -- bound for the semigroup term
  have hT1 : ‖iteratedFDeriv ℝ (j - 1) (sg P W q B t (gsD e f)) x‖ ≤
      Cs (j - 1) * K / Real.sqrt t := by
    refine hIH (j - 1) (by omega) (by omega) (gsD e f) (hs_gsD_hsdata hf e) trivial K
      (fun i hi hi' y => ?_) t ht0 ht1 x
    have h1 := hs_gsD_norm (n := i) (φ := f) (hf.1.of_le (by generalize i + 1 = n; exact_mod_cast le_top)) e y
    rw [he, one_mul] at h1
    exact h1.trans (hK (i + 1) (by omega) (Or.inl (by omega)) y)
  -- assembly
  have hc1 : ContDiff ℝ ((j - 1 : ℕ) : WithTop ℕ∞) (sg P W q B t (gsD e f)) :=
    (hs_sg_hsdata (P := P) hWs hq hBall (hs_gsD_hsdata hf e) ⟨ht0.le, ht1⟩).1.of_le hle
  have hsum : iteratedFDeriv ℝ (j - 1) (gsD e (sg P W q B t f)) x =
      iteratedFDeriv ℝ (j - 1) (sg P W q B t (gsD e f)) x +
        iteratedFDeriv ℝ (j - 1) (fun x => ∫ s in Ioo 0 t, G s x) x := by
    rw [hfun]
    exact iteratedFDeriv_add_apply hc1.contDiffAt hΦcd.contDiffAt
  rw [hsum]
  refine (norm_add_le _ _).trans ?_
  have hst : 1 ≤ (Real.sqrt t)⁻¹ := hsq t ht0 ht1
  have hCs : Cs (j - 1) * K / Real.sqrt t ≤ |Cs (j - 1)| * K / Real.sqrt t := by
    gcongr
    exact le_abs_self _
  have h6 : 6 * (|Cs (j - 1)| * (A * K)) ≤ 6 * (|Cs (j - 1)| * (A * K)) / Real.sqrt t := by
    rw [div_eq_mul_inv]
    exact le_mul_of_one_le_right (by positivity) hst
  calc _ ≤ |Cs (j - 1)| * K / Real.sqrt t + 6 * (|Cs (j - 1)| * (A * K)) / Real.sqrt t :=
        add_le_add (hT1.trans hCs) (hΦbd.trans h6)
    _ = hsC q Mb j Cs * K / Real.sqrt t := by
        rw [hsC, ← hAdef]; ring

theorem hs_core [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {q Mb : ℝ}
    (hq : 0 < q) {m j : ℕ} (hj : 2 ≤ j) (hjm : j ≤ m) {B : Euc d → Euc d}
    (hBm : HasCbBound m Mb B) (hBall : ∀ k, ∃ M : ℝ, HasCbBound k M B) (Cs : ℕ → ℝ)
    (hIH : ∀ l, 1 ≤ l → l < j → HsBound (fun _ => True) P W q B l (Cs l)) :
    HsBound HasCompactSupport P W q B j (hsC q Mb j Cs) := by
  intro f hf hfc K hK t ht0 ht1 x
  have hMb : 0 ≤ Mb := (norm_nonneg _).trans (by simpa using hBm.2 0 (Nat.zero_le _) 0)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 1 (by omega) (Or.inl le_rfl) 0)
  have hA0 : 0 ≤ hsA q Mb j Cs := by
    unfold hsA
    have : 0 ≤ ∑ l ∈ Finset.range j, |Cs l| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have := Real.exp_pos (q + Mb)
    positivity
  have hC0 : 0 ≤ hsC q Mb j Cs := by unfold hsC; positivity
  have hWs := sgNoise_of_brownian hW
  refine hs_dir_agg (by omega) ?_ (by positivity) (fun e he => hs_core_dir hW hq hj hjm hBm hBall Cs
    hIH hf hfc hK e he ht0 ht1 x)
  exact (hs_sg_hsdata (P := P) hWs hq hBall hf ⟨ht0.le, ht1⟩).1.of_le
    (by generalize j = n; exact_mod_cast le_top)

end Core

end HRS.MS.PoisHigh
