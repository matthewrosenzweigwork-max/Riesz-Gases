import HRS.MS.SA16SEn5

/-!
# S.A.16 (SA16S) En6: the transport identity (packet P7, step 7)

`sa16sy_transport_eta`: `∑_a ∫ s_η^{p/2-1} W_a (c ∂_e W_a) = -(1/p) ∫ (∂_e c) θ_η`;
`sa16sy_transport`: `∫ ∑_a |W|^{p-2} W_a (c ∂_e W_a) = -(1/p) ∫ (∂_e c) |W|^p` (`c` smooth, `W_a ∈ C_c^∞`, `p ≥ 2`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.BreakdownSA16

section En6
variable {d : ℕ} {ι : Type*} [Fintype ι]

lemma sa16sy_transport_eta {W : ι → Euc d → ℝ} (hW : ∀ a, IsCcInfty (W a)) {p : ℝ} (hp : 2 ≤ p) {η : ℝ}
    (hη : 0 < η) {c : Euc d → ℝ} (hc : ContDiff ℝ ∞ c) (e : Euc d) :
    ∑ a, ∫ x, sa16sy_s W η x ^ (p / 2 - 1) * W a x * (c x * fderiv ℝ (W a) x e) =
      -(1 / p) * ∫ x, fderiv ℝ c x e * (sa16sy_s W η x ^ (p / 2) - η ^ p) := by
  have hp0 : 0 < p := by linarith
  set r : ℝ := p / 2 - 1 with hr
  set θ : Euc d → ℝ := fun x => sa16sy_s W η x ^ (p / 2) - η ^ p with hθ
  have hθcc : IsCcInfty θ := sa16sy_theta_cc hW hη hp0
  have hint : ∀ a, Integrable (fun x => sa16sy_s W η x ^ r * W a x * (c x * fderiv ℝ (W a) x e)) := by
    intro a
    have hcn : Continuous (fun x => sa16sy_s W η x ^ r * W a x * (c x * fderiv ℝ (W a) x e)) :=
      (((sa16sy_rpow_smooth hW hη r).continuous).mul (hW a).1.continuous).mul
        (hc.continuous.mul (sa16sy_dir_cont hW a e).1.continuous)
    exact hcn.integrable_of_hasCompactSupport ((hW a).2.mul_left.mul_right)
  rw [← integral_finsetSum _ (fun a _ => hint a)]
  -- identify the integrand with `(1/p) c ∂_e θ`
  have hdθ : ∀ x, fderiv ℝ θ x e = p * sa16sy_s W η x ^ r * ∑ a, W a x * fderiv ℝ (W a) x e := by
    intro x
    have h1 := (sa16sy_rpow_fderiv hW hη (p / 2) x e)
    have h2 : fderiv ℝ θ x e = fderiv ℝ (fun y => sa16sy_s W η y ^ (p / 2)) x e := by
      rw [hθ, fderiv_sub_const]
    rw [h2, h1]
    have : p / 2 - 1 = r := rfl
    rw [this]
    ring
  have hrw : ∀ x, ∑ a, sa16sy_s W η x ^ r * W a x * (c x * fderiv ℝ (W a) x e) =
      (1 / p) * (c x * fderiv ℝ θ x e) := by
    intro x
    rw [hdθ x, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    field_simp
  simp_rw [hrw]
  rw [integral_const_mul]
  have hibp := sa16sw_ibp hc hθcc e
  rw [show (∫ x, c x * fderiv ℝ θ x e) = -∫ x, fderiv ℝ c x e * θ x by linarith]
  ring

lemma sa16sy_transport {W : ι → Euc d → ℝ} (hW : ∀ a, IsCcInfty (W a)) {p : ℝ} (hp : 2 ≤ p)
    {c : Euc d → ℝ} (hc : ContDiff ℝ ∞ c) (e : Euc d) :
    ∫ x, ∑ a, vnorm (fun b => W b x) ^ (p - 2) * W a x * (c x * fderiv ℝ (W a) x e) =
      -(1 / p) * ∫ x, fderiv ℝ c x e * vnorm (fun b => W b x) ^ p := by
  have hp0 : 0 < p := by linarith
  set r : ℝ := p / 2 - 1 with hr
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  set q : ℝ := p / 2 with hq
  have hq1 : 1 ≤ q := by rw [hq]; linarith
  set Q : ι → Euc d → ℝ := fun a x => fderiv ℝ (W a) x e with hQ
  have hQcc : ∀ a, IsCcInfty (Q a) := fun a => sa16sy_dir_cont hW a e
  set T : Euc d → ℝ := fun x => ∑ a, W a x ^ 2 with hT
  set TQ : Euc d → ℝ := fun x => ∑ a, Q a x ^ 2 with hTQ
  have hTc : IsCcInfty T := sa16sy_T_cc hW
  have hTQc : IsCcInfty TQ := sa16sy_T_cc hQcc
  -- first integral
  set F : ℝ → Euc d → ℝ := fun η x => ∑ a, sa16sy_s W η x ^ r * W a x * (c x * Q a x) with hF
  set bnd : Euc d → ℝ := fun x => (T x + 1) ^ r * (|c x| * (T x + TQ x)) with hbnd
  have hpos : ∀ x, T x + 1 ≠ 0 := fun x => by have := sa16sy_T_nonneg W x; show T x + 1 ≠ 0; linarith
  have hbc : Continuous bnd :=
    ((hTc.1.continuous.add continuous_const).rpow_const (fun x => Or.inl (hpos x))).mul
      (hc.continuous.abs.mul (hTc.1.continuous.add hTQc.1.continuous))
  have hbs : HasCompactSupport (fun x => |c x| * (T x + TQ x)) := (hTc.2.add hTQc.2).mul_left
  have hbint : Integrable bnd := hbc.integrable_of_hasCompactSupport hbs.mul_left
  have hFc : ∀ η, 0 < η → Continuous (F η) := by
    intro η hη
    exact continuous_finsetSum _ fun a _ =>
      (((sa16sy_rpow_smooth hW hη r).continuous).mul (hW a).1.continuous).mul
        (hc.continuous.mul (hQcc a).1.continuous)
  have hlim1 := sa16sy_dct (F := F) (f := fun x => ∑ a, (T x) ^ r * W a x * (c x * Q a x)) hbint
    (fun η hη => (hFc η hη).aestronglyMeasurable)
    (fun η hη hη1 x => by
      have hspos := sa16sy_s_pos W hη x
      have hsle := sa16sy_s_le (W := W) hη1 hη x
      have hs0 : 0 ≤ sa16sy_s W η x ^ r := Real.rpow_nonneg hspos.le _
      have hsr : sa16sy_s W η x ^ r ≤ (T x + 1) ^ r := Real.rpow_le_rpow hspos.le hsle hr0
      rw [Real.norm_eq_abs]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have h1 : ∀ a, |sa16sy_s W η x ^ r * W a x * (c x * Q a x)| ≤
          sa16sy_s W η x ^ r * (|c x| * (W a x ^ 2 + Q a x ^ 2)) := by
        intro a
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hs0]
        have := two_mul_le_add_sq |W a x| |Q a x|
        rw [sq_abs, sq_abs] at this
        have h2 := abs_nonneg (W a x)
        have h3 := abs_nonneg (Q a x)
        have h4 := abs_nonneg (c x)
        have h5 : |W a x| * |Q a x| ≤ W a x ^ 2 + Q a x ^ 2 := by nlinarith
        calc sa16sy_s W η x ^ r * |W a x| * (|c x| * |Q a x|)
            = sa16sy_s W η x ^ r * (|c x| * (|W a x| * |Q a x|)) := by ring
          _ ≤ sa16sy_s W η x ^ r * (|c x| * (W a x ^ 2 + Q a x ^ 2)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 h4) hs0
      refine (Finset.sum_le_sum fun a _ => h1 a).trans ?_
      rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib]
      have hTn := sa16sy_T_nonneg W x
      have hTQn : 0 ≤ ∑ a, Q a x ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      calc sa16sy_s W η x ^ r * (|c x| * (∑ a, W a x ^ 2 + ∑ a, Q a x ^ 2))
          ≤ (T x + 1) ^ r * (|c x| * (∑ a, W a x ^ 2 + ∑ a, Q a x ^ 2)) :=
            mul_le_mul_of_nonneg_right hsr (mul_nonneg (abs_nonneg _) (add_nonneg hTn hTQn))
        _ = bnd x := rfl)
    (fun x => tendsto_finset_sum _ fun a _ => ((sa16sy_s_tendsto W x hr0).mul_const _).mul_const _)
  -- second integral
  set K : Set (Euc d) := tsupport T with hK
  have hKc : IsCompact K := hTc.2
  set g : Euc d → ℝ := fun x => |fderiv ℝ c x e| * (T x + 1) ^ q with hg
  have hgc : Continuous g :=
    (((hc.continuous_fderiv (by simp)).clm_apply continuous_const).abs).mul
      ((hTc.1.continuous.add continuous_const).rpow_const (fun x => Or.inl (hpos x)))
  have hbnd2 : Integrable (K.indicator g) :=
    (integrable_indicator_iff hKc.measurableSet).2 (hgc.continuousOn.integrableOn_compact hKc)
  set G : ℝ → Euc d → ℝ := fun η x => fderiv ℝ c x e * (sa16sy_s W η x ^ q - η ^ p) with hG
  have hGc : ∀ η, 0 < η → Continuous (G η) := by
    intro η hη
    exact ((hc.continuous_fderiv (by simp)).clm_apply continuous_const).mul
      (((sa16sy_rpow_smooth hW hη q).continuous).sub continuous_const)
  have hTzero : ∀ x, x ∉ K → T x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hlim2 := sa16sy_dct (F := G) (f := fun x => fderiv ℝ c x e * ((T x) ^ q - 0)) hbnd2
    (fun η hη => (hGc η hη).aestronglyMeasurable)
    (fun η hη hη1 x => by
      by_cases hx : x ∈ K
      · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, hG, abs_mul]
        simp only [hg]
        have hspos := sa16sy_s_pos W hη x
        have hsle := sa16sy_s_le (W := W) hη1 hη x
        have hsq : sa16sy_s W η x ^ q ≤ (T x + 1) ^ q := Real.rpow_le_rpow hspos.le hsle (by linarith)
        have hη2 : (η ^ 2) ^ q = η ^ p := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hη.le]; push_cast
          rw [show (2 : ℝ) * q = p by rw [hq]; ring]
        have hge : η ^ p ≤ sa16sy_s W η x ^ q := by
          rw [← hη2]
          exact Real.rpow_le_rpow (by positivity) (by unfold sa16sy_s; have := sa16sy_T_nonneg W x; linarith)
            (by linarith)
        have hηp : 0 ≤ η ^ p := Real.rpow_nonneg hη.le _
        rw [abs_of_nonneg (by linarith : 0 ≤ sa16sy_s W η x ^ q - η ^ p)]
        exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      · rw [Set.indicator_of_notMem hx, hG]
        have : sa16sy_s W η x ^ q - η ^ p = 0 := by
          have hT0 := hTzero x hx
          have : sa16sy_s W η x = η ^ 2 := by unfold sa16sy_s; simp only [hT, hT0] at *; linarith
          rw [this, ← Real.rpow_natCast, ← Real.rpow_mul hη.le]; push_cast
          rw [show (2 : ℝ) * q = p by rw [hq]; ring]; ring
        simp [this])
    (fun x => by
      have h := sa16sy_s_tendsto W x (r := q) (by linarith)
      have h2 : Tendsto (fun η : ℝ => η ^ p) (𝓝[>] 0) (𝓝 0) := by
        have := (Real.continuousAt_rpow_const (0 : ℝ) p (Or.inr hp0.le)).tendsto
        rw [Real.zero_rpow hp0.ne'] at this
        exact this.mono_left nhdsWithin_le_nhds
      exact (h.sub h2).const_mul _)
  -- assemble
  have heta : ∀ η, 0 < η → ∫ x, F η x = -(1 / p) * ∫ x, G η x := by
    intro η hη
    have := sa16sy_transport_eta hW hp hη hc e
    rw [← integral_finsetSum] at this
    · exact this
    · intro a _
      have hcn : Continuous (fun x => sa16sy_s W η x ^ r * W a x * (c x * fderiv ℝ (W a) x e)) :=
        (((sa16sy_rpow_smooth hW hη r).continuous).mul (hW a).1.continuous).mul
          (hc.continuous.mul (sa16sy_dir_cont hW a e).1.continuous)
      exact hcn.integrable_of_hasCompactSupport ((hW a).2.mul_left.mul_right)
  have hlim3 : Tendsto (fun η => ∫ x, F η x) (𝓝[>] 0)
      (𝓝 (-(1 / p) * ∫ x, fderiv ℝ c x e * ((T x) ^ q - 0))) := by
    have := hlim2.const_mul (-(1 / p))
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact (heta η hη).symm
  have hu := tendsto_nhds_unique hlim1 hlim3
  have e1 : ∫ x, ∑ a, vnorm (fun b => W b x) ^ (p - 2) * W a x * (c x * fderiv ℝ (W a) x e) =
      ∫ x, ∑ a, (T x) ^ r * W a x * (c x * Q a x) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sa16sy_vnorm_pow, show (p - 2) / 2 = r by rw [hr]; ring]
  have e2 : ∫ x, fderiv ℝ c x e * vnorm (fun b => W b x) ^ p = ∫ x, fderiv ℝ c x e * ((T x) ^ q - 0) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show fderiv ℝ c x e * vnorm (fun b => W b x) ^ p = fderiv ℝ c x e * ((T x) ^ q - 0)
    rw [sa16sy_vnorm_pow W x p, sub_zero]
  rw [e1, e2, hu]

end En6

end HRS.Whole.AppendixA.Phase2SA16R
