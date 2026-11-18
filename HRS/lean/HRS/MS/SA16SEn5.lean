import HRS.MS.SA16SEn4

/-!
# S.A.16 (SA16S) En5: the unregularized diffusion and transport identities (packet P7, step 6)

For `W = (W_a)` of class `C_c^∞`, `p ≥ 2`, `|W| = vnorm (W_a)`:
* `sa16sy_diffusion`: `∫ ∑_a |W|^{p-2} W_a ∂_e∂_e W_a ≤ 0`;
* `sa16sy_transport`: `∫ ∑_a |W|^{p-2} W_a (c ∂_e W_a) = -(1/p) ∫ (∂_e c) |W|^p`  (`c` smooth).
Both follow from the `η`-regularized identities by dominated convergence as `η → 0+`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.BreakdownSA16

section En5
variable {d : ℕ} {ι : Type*} [Fintype ι]

lemma sa16sy_dct {F : ℝ → Euc d → ℝ} {f bnd : Euc d → ℝ} (hbnd : Integrable bnd)
    (hmeas : ∀ η, 0 < η → AEStronglyMeasurable (F η) volume)
    (hb : ∀ η, 0 < η → η ≤ 1 → ∀ x, ‖F η x‖ ≤ bnd x)
    (hlim : ∀ x, Tendsto (fun η => F η x) (𝓝[>] 0) (𝓝 (f x))) :
    Tendsto (fun η => ∫ x, F η x) (𝓝[>] 0) (𝓝 (∫ x, f x)) := by
  refine tendsto_integral_filter_of_dominated_convergence bnd ?_ ?_ hbnd (Eventually.of_forall hlim)
  · filter_upwards [self_mem_nhdsWithin] with η hη using hmeas η hη
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with η hη
    exact Eventually.of_forall fun x => hb η hη.1 hη.2.le x

lemma sa16sy_s_tendsto (W : ι → Euc d → ℝ) (x : Euc d) {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun η : ℝ => sa16sy_s W η x ^ r) (𝓝[>] 0) (𝓝 ((∑ a, W a x ^ 2) ^ r)) := by
  have h := sa16bd_cont_rpow (x := ∑ a, W a x ^ 2) (r := r) (Finset.sum_nonneg fun a _ => sq_nonneg _) hr
  have h2 : Tendsto (fun η : ℝ => (∑ a, W a x ^ 2 + η ^ 2) ^ r) (𝓝 0) (𝓝 ((∑ a, W a x ^ 2 + 0 ^ 2) ^ r)) :=
    h.tendsto
  simpa [sa16sy_s] using h2.mono_left nhdsWithin_le_nhds

lemma sa16sy_s_le {W : ι → Euc d → ℝ} {η : ℝ} (hη1 : η ≤ 1) (hη0 : 0 < η) (x : Euc d) :
    sa16sy_s W η x ≤ ∑ a, W a x ^ 2 + 1 := by
  unfold sa16sy_s
  nlinarith

lemma sa16sy_T_nonneg (W : ι → Euc d → ℝ) (x : Euc d) : 0 ≤ ∑ a, W a x ^ 2 :=
  Finset.sum_nonneg fun a _ => sq_nonneg _

lemma sa16sy_vnorm_pow (W : ι → Euc d → ℝ) (x : Euc d) (q : ℝ) :
    vnorm (fun b => W b x) ^ q = (∑ a, W a x ^ 2) ^ (q / 2) := sa16bd_vnorm_rpow _ q

lemma sa16sy_diffusion {W : ι → Euc d → ℝ} (hW : ∀ a, IsCcInfty (W a)) {p : ℝ} (hp : 2 ≤ p) (e : Euc d) :
    ∫ x, ∑ a, vnorm (fun b => W b x) ^ (p - 2) * W a x *
      fderiv ℝ (fun y => fderiv ℝ (W a) y e) x e ≤ 0 := by
  set r : ℝ := p / 2 - 1 with hr
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  set D : ι → Euc d → ℝ := fun a x => fderiv ℝ (fun y => fderiv ℝ (W a) y e) x e with hD
  have hDcc : ∀ a, IsCcInfty (D a) := fun a => sa16s_cc_fderiv (sa16sy_dir_cont hW a e) e
  set T : Euc d → ℝ := fun x => ∑ a, W a x ^ 2 with hT
  set TD : Euc d → ℝ := fun x => ∑ a, D a x ^ 2 with hTD
  have hTc : IsCcInfty T := sa16sy_T_cc hW
  have hTDc : IsCcInfty TD := sa16sy_T_cc hDcc
  set F : ℝ → Euc d → ℝ := fun η x => ∑ a, sa16sy_s W η x ^ r * W a x * D a x with hF
  set bnd : Euc d → ℝ := fun x => (T x + 1) ^ r * (T x + TD x) with hbnd
  have hbc : Continuous bnd := by
    have : Continuous (fun x => (T x + 1) ^ r) :=
      (hTc.1.continuous.add continuous_const).rpow_const (fun x => Or.inl (by
        have := sa16sy_T_nonneg W x
        show T x + 1 ≠ 0
        linarith))
    exact this.mul (hTc.1.continuous.add hTDc.1.continuous)
  have hbs : HasCompactSupport (fun x => T x + TD x) := hTc.2.add hTDc.2
  have hbint : Integrable bnd := hbc.integrable_of_hasCompactSupport hbs.mul_left
  have hFc : ∀ η, 0 < η → Continuous (F η) := by
    intro η hη
    exact continuous_finsetSum _ fun a _ =>
      (((sa16sy_rpow_smooth hW hη r).continuous).mul (hW a).1.continuous).mul (hDcc a).1.continuous
  have hfin : ∀ η, 0 < η → ∫ x, F η x = ∑ a, ∫ x, sa16sy_s W η x ^ r * W a x * D a x := by
    intro η hη
    refine integral_finsetSum _ (fun a _ => ?_)
    have hc : Continuous (fun x => sa16sy_s W η x ^ r * W a x * D a x) :=
      (((sa16sy_rpow_smooth hW hη r).continuous).mul (hW a).1.continuous).mul (hDcc a).1.continuous
    exact hc.integrable_of_hasCompactSupport ((hW a).2.mul_left.mul_right)
  have hle : ∀ η, 0 < η → ∫ x, F η x ≤ 0 := by
    intro η hη
    rw [hfin η hη]
    exact sa16sy_diff_eta hW hp hη e
  have hlim := sa16sy_dct (F := F) (f := fun x => ∑ a, (T x) ^ r * W a x * D a x) hbint
    (fun η hη => (hFc η hη).aestronglyMeasurable)
    (fun η hη hη1 x => by
      have hspos := sa16sy_s_pos W hη x
      have hsle := sa16sy_s_le (W := W) hη1 hη x
      have hs0 : 0 ≤ sa16sy_s W η x ^ r := Real.rpow_nonneg hspos.le _
      have hsr : sa16sy_s W η x ^ r ≤ (T x + 1) ^ r := Real.rpow_le_rpow hspos.le hsle hr0
      rw [Real.norm_eq_abs]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have h1 : ∀ a, |sa16sy_s W η x ^ r * W a x * D a x| ≤ sa16sy_s W η x ^ r * (W a x ^ 2 + D a x ^ 2) := by
        intro a
        rw [abs_mul, abs_mul, abs_of_nonneg hs0]
        have := two_mul_le_add_sq |W a x| |D a x|
        rw [sq_abs, sq_abs] at this
        have h2 := abs_nonneg (W a x)
        have h3 := abs_nonneg (D a x)
        nlinarith [mul_nonneg h2 h3, mul_nonneg hs0 (mul_nonneg h2 h3), mul_nonneg hs0 (sq_nonneg (W a x)),
          mul_nonneg hs0 (sq_nonneg (D a x))]
      refine (Finset.sum_le_sum fun a _ => h1 a).trans ?_
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      exact mul_le_mul hsr (by simp [hT, hTD]) (add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)) (Real.rpow_nonneg (by have := sa16sy_T_nonneg W x; linarith) _))
    (fun x => tendsto_finset_sum _ fun a _ => ((sa16sy_s_tendsto W x hr0).mul_const _).mul_const _)
  have hfin2 : ∫ x, ∑ a, vnorm (fun b => W b x) ^ (p - 2) * W a x * D a x =
      ∫ x, ∑ a, (T x) ^ r * W a x * D a x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sa16sy_vnorm_pow, show (p - 2) / 2 = r by rw [hr]; ring]
  rw [hfin2]
  exact le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun η hη => hle η hη)

end En5

end HRS.Whole.AppendixA.Phase2SA16R
