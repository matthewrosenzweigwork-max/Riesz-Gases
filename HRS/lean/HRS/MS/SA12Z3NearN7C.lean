import HRS.MS.SA12Z3NearN7B
import HRS.MS.SA16JetSchwartz

/-!
# S.A.12 N7 (SA12Z3), part C: the three-term decomposition and the Leibniz remainder

* `sa12z3_pd_G_decomp`: `∂^{idx} eucNonlocal = ∑ M_{ji}(hessRiesz_{ij}(a u) - T_i((∂_j a) u) + T_i R_j)`;
* `sa12z3_leib_diff`: pointwise `|∂^{idx}(a h) - a ∂^{idx} h| ≤ ∑_{k ≥ 1} C(n,k) ‖D^k a‖ ‖D^{n-k} h‖`
  (apply `norm_iteratedFDeriv_mul_le` to `(a - a(x)) h`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

theorem sa12z3_hess_firstRiesz {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i j : Fin d) {v : Euc d → ℝ}
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) (x : Euc d) :
    hessRiesz d s i j v x = firstRiesz d s i (D1 j v) x := by
  rw [sa12z3_hess_eq hs0 hsd i j hv hvc x]
  rfl

theorem sa12z3_firstRiesz_eq' {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i : Fin d) {v : Euc d → ℝ}
    (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v) (x : Euc d) :
    firstRiesz d s i v x = ∫ y, rieszKernel d s (x - y) * D1 i v y := by
  have hK : LocallyIntegrable (rieszKernel d s) (volume : Measure (Euc d)) :=
    rieszKernel_locallyIntegrable hs0 hsd
  have := convFun_D1 hK hv hvc i x
  exact this

theorem sa12z3_firstRiesz_lin {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i : Fin d)
    {v1 v2 v3 : Euc d → ℝ} (h1 : ContDiff ℝ 1 v1) (c1 : HasCompactSupport v1)
    (h2 : ContDiff ℝ 1 v2) (c2 : HasCompactSupport v2)
    (h3 : ContDiff ℝ 1 v3) (c3 : HasCompactSupport v3) (x : Euc d) :
    firstRiesz d s i (fun y => v1 y - v2 y + v3 y) x =
      firstRiesz d s i v1 x - firstRiesz d s i v2 x + firstRiesz d s i v3 x := by
  have hw : ContDiff ℝ 1 (fun y => v1 y - v2 y + v3 y) := (h1.sub h2).add h3
  have hwc : HasCompactSupport (fun y => v1 y - v2 y + v3 y) :=
    (c1.sub c2).add c3
  rw [sa12z3_firstRiesz_eq' hs0 hsd i hw hwc x, sa12z3_firstRiesz_eq' hs0 hsd i h1 c1 x,
    sa12z3_firstRiesz_eq' hs0 hsd i h2 c2 x, sa12z3_firstRiesz_eq' hs0 hsd i h3 c3 x]
  have hint : ∀ {v : Euc d → ℝ}, ContDiff ℝ 1 v → HasCompactSupport v →
      Integrable (fun y => rieszKernel d s (x - y) * D1 i v y) volume := by
    intro v hv hvc
    exact HRS.MS.UniqN1b.n1b_convFun_integrable hs0 hsd
      ((hv.continuous_fderiv one_ne_zero).clm_apply continuous_const) (D1_supp hvc i) x
  have hpt : ∀ y, rieszKernel d s (x - y) * D1 i (fun y => v1 y - v2 y + v3 y) y =
      rieszKernel d s (x - y) * D1 i v1 y - rieszKernel d s (x - y) * D1 i v2 y +
        rieszKernel d s (x - y) * D1 i v3 y := by
    intro y
    have d1 := (h1.differentiable one_ne_zero) y
    have d2 := (h2.differentiable one_ne_zero) y
    have d3 := (h3.differentiable one_ne_zero) y
    unfold D1
    rw [fderiv_fun_add (d1.fun_sub d2) d3, fderiv_fun_sub d1 d2]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
    ring
  simp_rw [hpt]
  have hI12 : Integrable (fun y => rieszKernel d s (x - y) * D1 i v1 y -
      rieszKernel d s (x - y) * D1 i v2 y) volume := (hint h1 c1).sub (hint h2 c2)
  rw [integral_add hI12 (hint h3 c3), integral_sub (hint h1 c1) (hint h2 c2)]

theorem sa12z3_pd_contDiff_inf {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) {n : ℕ} (idx : Fin n → Fin d) :
    ContDiff ℝ ∞ (partialDeriv idx f) := by
  have h := hf.iteratedFDeriv_right (i := n) (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by exact_mod_cast (le_top : ((⊤ : ℕ∞) + (n : ℕ∞)) ≤ ⊤))
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Euc d) ℝ (sa12z3_ev idx)).contDiff.comp h

/-- The remainder `R_j`. -/
def sa12z3_Rj (a F : Euc d → ℝ) {n : ℕ} (idx : Fin n → Fin d) (j : Fin d) (y : Euc d) : ℝ :=
  partialDeriv idx (fun y' => a y' * D1 j F y') y - a y * D1 j (partialDeriv idx F) y

theorem sa12z3_pd_G_decomp {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M : Matrix (Fin d) (Fin d) ℝ) {m : ℕ}
    (hm : 1 ≤ m) {a F : Euc d → ℝ} (ha : ContDiff ℝ (m + 1) a) (hac : HasCompactSupport a)
    (hF : ContDiff ℝ ∞ F) {n : ℕ} (hn : n ≤ m) (idx : Fin n → Fin d) (x : Euc d) :
    partialDeriv idx (eucNonlocal s M a F) x = ∑ i, ∑ j, M j i *
      (hessRiesz d s i j (fun y => a y * partialDeriv idx F y) x -
        firstRiesz d s i (fun y => D1 j a y * partialDeriv idx F y) x +
        firstRiesz d s i (sa12z3_Rj a F idx j) x) := by
  rw [sa12z3_pd_eucNL hs0 hsd M ha hac hF hn idx x]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  set u : Euc d → ℝ := partialDeriv idx F with hu
  have hu_inf : ContDiff ℝ ∞ u := sa12z3_pd_contDiff_inf hF idx
  have ha2 : ContDiff ℝ 2 a := ha.of_le (by exact_mod_cast (by omega : 2 ≤ m + 1))
  have ha1 : ContDiff ℝ 1 a := ha.of_le (by exact_mod_cast (by omega : 1 ≤ m + 1))
  have huc1 : ContDiff ℝ 2 u := sa12z3_cd_of_inf hu_inf 2
  have hDa : ContDiff ℝ 1 (D1 j a) :=
    (ha2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hDu : ContDiff ℝ 1 (D1 j u) :=
    ((sa12z3_cd_of_inf hu_inf 2).fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hau2 : ContDiff ℝ 2 (fun y => a y * u y) := ha2.mul huc1
  have hDF : ContDiff ℝ (m + 1) (D1 j F) :=
    ((sa12z3_cd_of_inf hF (m + 2)).fderiv_right (m := (m + 1 : ℕ)) (by push_cast; rfl)).clm_apply contDiff_const
  have hP : ContDiff ℝ (m + 1) (fun y => a y * D1 j F y) := ha.mul hDF
  have hPc : HasCompactSupport (fun y => a y * D1 j F y) := hac.mul_right
  set Φ : Euc d → ℝ := partialDeriv idx (fun y => a y * D1 j F y) with hΦ
  have hΦ1 : ContDiff ℝ 1 Φ := by
    have := sa12z3_pd_contDiff (k := m + 1) (n := n) hP (by omega) idx
    exact this.of_le (by norm_cast; omega)
  have hΦc : HasCompactSupport Φ := sa12z3_pd_compact hPc idx
  have hauc : HasCompactSupport (fun y => a y * u y) := hac.mul_right
  have hR1 : ContDiff ℝ 1 (sa12z3_Rj a F idx j) := hΦ1.sub (ha1.mul hDu)
  have hRc : HasCompactSupport (sa12z3_Rj a F idx j) := hΦc.sub hac.mul_right
  have hv1 : ContDiff ℝ 1 (D1 j (fun y => a y * u y)) :=
    (hau2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hv1c : HasCompactSupport (D1 j (fun y => a y * u y)) := D1_supp hauc j
  have hv2 : ContDiff ℝ 1 (fun y => D1 j a y * u y) := hDa.mul (sa12z3_cd_of_inf hu_inf 1)
  have hv2c : HasCompactSupport (fun y => D1 j a y * u y) := (D1_supp hac j).mul_right
  have hpt : Φ = fun y => D1 j (fun y => a y * u y) y - D1 j a y * u y + sa12z3_Rj a F idx j y := by
    funext y
    have hprod : D1 j (fun y => a y * u y) y = a y * D1 j u y + u y * D1 j a y := by
      unfold D1
      rw [fderiv_fun_mul (ha1.differentiable one_ne_zero y) ((sa12z3_cd_of_inf hu_inf 1).differentiable one_ne_zero y)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hprod]
    unfold sa12z3_Rj
    simp only [hΦ]
    ring
  rw [hpt, sa12z3_firstRiesz_lin hs0 hsd i hv1 hv1c hv2 hv2c hR1 hRc x,
    sa12z3_hess_firstRiesz hs0 hsd i j hau2 hauc x]

/-- `‖D^l g‖` as a sum of coordinate derivatives. -/
theorem sa12z3_norm_iter_le (g : Euc d → ℝ) (x : Euc d) (l : ℕ) :
    ‖iteratedFDeriv ℝ l g x‖ ≤ ∑ r : Fin l → Fin d, |partialDeriv r g x| :=
  HRS.Whole.AppendixA.Phase2SA16.sa16j_norm_iter_le g x l

theorem sa12z3_pd_le_norm {n : ℕ} (g : Euc d → ℝ) (x : Euc d) (idx : Fin n → Fin d) :
    |partialDeriv idx g x| ≤ ‖iteratedFDeriv ℝ n g x‖ := by
  unfold partialDeriv
  have h := (iteratedFDeriv ℝ n g x).le_opNorm (fun l => EuclideanSpace.single (idx l) (1 : ℝ))
  simp only [PiLp.norm_single, norm_one, Finset.prod_const_one, mul_one] at h
  simpa [Real.norm_eq_abs] using h

/-- The Leibniz remainder, pointwise. -/
theorem sa12z3_leib_diff {n : ℕ} {a h : Euc d → ℝ} (ha : ContDiff ℝ n a) (hh : ContDiff ℝ n h)
    (idx : Fin n → Fin d) (x : Euc d) :
    |partialDeriv idx (fun y => a y * h y) x - a x * partialDeriv idx h x| ≤
      ∑ k ∈ Finset.range (n + 1), (if k = 0 then 0 else
        (n.choose k : ℝ) * ‖iteratedFDeriv ℝ k a x‖ * ‖iteratedFDeriv ℝ (n - k) h x‖) := by
  set c : ℝ := a x with hc
  have hf : ContDiff ℝ n (fun y => a y - c) := ha.sub contDiff_const
  have hsplit : partialDeriv idx (fun y => a y * h y) x - a x * partialDeriv idx h x =
      partialDeriv idx (fun y => (a y - c) * h y) x := by
    have e1 : iteratedFDeriv ℝ n (fun y => a y * h y) x =
        iteratedFDeriv ℝ n (fun y => (a y - c) * h y) x + c • iteratedFDeriv ℝ n h x := by
      have e : (fun y => a y * h y) = (fun y => (a y - c) * h y + c • h y) := by
        funext y; simp only [smul_eq_mul]; ring
      rw [e]
      change iteratedFDeriv ℝ n ((fun y => (a y - c) * h y) + (fun y => c • h y)) x = _
      rw [iteratedFDeriv_add_apply (f := fun y => (a y - c) * h y) (g := fun y => c • h y)
        (hf.mul hh).contDiffAt (contDiff_const.mul hh : ContDiff ℝ n (fun y => c * h y)).contDiffAt,
        iteratedFDeriv_const_smul_apply' hh.contDiffAt]
    unfold partialDeriv
    rw [e1]
    simp [hc]
  rw [hsplit]
  refine (sa12z3_pd_le_norm _ x idx).trans ?_
  refine (norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := (n : WithTop ℕ∞)) (n := n) hf hh x
    (le_refl _)).trans ?_
  refine le_of_eq (Finset.sum_congr rfl fun k hkr => ?_)
  by_cases hk : k = 0
  · subst hk
    simp [hc]
  · rw [if_neg hk]
    have hkn : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hkr)
    have h1 : iteratedFDeriv ℝ k (fun y => a y - c) x = iteratedFDeriv ℝ k a x := by
      have hh1 := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := k) (x := x) (f := a) (g := fun _ : Euc d => c)
        (ha.of_le (by exact_mod_cast hkn)).contDiffAt contDiffAt_const
      rw [iteratedFDeriv_const_of_ne hk] at hh1
      have e2 : (fun y => a y - c) = a - fun _ => c := rfl
      rw [e2]
      simpa using hh1
    rw [h1]

end HRS.MH.AdjointRd.Phase2SA12Near
