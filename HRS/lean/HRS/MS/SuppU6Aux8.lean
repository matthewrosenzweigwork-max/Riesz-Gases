import HRS.MS.SuppU6Aux7

/-!
# U6 aux 8: summability of `⟨x_j⟩^{-2p}` by comparison with an integral
-/

noncomputable section

open scoped RealInnerProductSpace ContDiff
open MeasureTheory Metric Filter Topology Finset

namespace HRS.U6

variable {d : ℕ}

lemma continuous_u6j : Continuous (u6j (d := d)) := by
  unfold u6j u6w
  fun_prop

lemma u6j_integrable {p : ℝ} (hp : (d : ℝ) + 1 < 2 * p) :
    Integrable (fun y : EuclideanSpace ℝ (Fin d) => (u6j y) ^ (1 - 2 * p)) := by
  have h1 : ((Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℕ) : ℝ) < 2 * p - 1 := by
    rw [finrank_euclideanSpace_fin]; linarith
  have h2 := (integrable_one_add_norm (μ := (volume : Measure (EuclideanSpace ℝ (Fin d)))) h1).const_mul
    (((2 : ℝ) ^ (1 - 2 * p))⁻¹)
  refine h2.mono' ?_ (Filter.Eventually.of_forall (fun y => ?_))
  · exact (continuous_u6j.rpow_const (fun x => Or.inl (u6j_pos x).ne')).aestronglyMeasurable
  · have hj : (1 + ‖y‖) / 2 ≤ u6j y := by
      have h := u6j_sq y
      have : ((1 + ‖y‖) / 2) ^ 2 ≤ u6j y ^ 2 := by
        rw [h]; nlinarith [sq_nonneg (1 - ‖y‖)]
      exact le_of_sq_le_sq this (u6j_pos y).le
    have hpos : 0 < (1 + ‖y‖) / 2 := by positivity
    have hz : 1 - 2 * p ≤ 0 := by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    have h3 := Real.rpow_le_rpow_of_nonpos hpos hj hz
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (u6j_pos y).le _)]
    refine h3.trans (le_of_eq ?_)
    rw [Real.div_rpow (by positivity) (by norm_num), show -(2 * p - 1) = 1 - 2 * p by ring,
      div_eq_inv_mul]

lemma u6_summable_jbracket {S : Set (EuclideanSpace ℝ (Fin d))}
    (hS : S.Pairwise (u6Sep (1 / 16 : ℝ))) {p : ℝ} (hp : (d : ℝ) + 1 < 2 * p) :
    Summable (fun k : S => (u6j k.1) ^ (-(2 * p))) := by
  set ρ : ℝ := 1 / 128 with hρ
  have hρ0 : 0 < ρ := by norm_num [hρ]
  set V := volume.real (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) with hV
  have hVpos : 0 < V := u6_ballvol_pos
  set e : ℝ := 1 - 2 * p with he
  have he0 : e ≤ 0 := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    rw [he]; linarith
  have hint := u6j_integrable (d := d) hp
  set I : ℝ := ∫ y, (u6j y) ^ e with hI
  let B : S → Set (EuclideanSpace ℝ (Fin d)) := fun k => u6F k.1 '' closedBall 0 ρ
  have hBcomp : ∀ k, IsCompact (B k) := fun k =>
    (isCompact_closedBall _ _).image (continuous_u6F k.1)
  have hdisj : Pairwise (Function.onFun Disjoint B) := by
    intro k k' hne
    rw [Function.onFun, Set.disjoint_left]
    rintro y ⟨u, hu, rfl⟩ ⟨v, hv, hyv⟩
    have hu' : ‖u‖ ≤ ρ := by simpa using hu
    have hv' : ‖v‖ ≤ ρ := by simpa using hv
    exact u6_not_sep_of_overlap (ε := 1 / 16) (ρ := ρ) (by rw [hρ]; norm_num)
      (by rw [hρ]; norm_num) hyv.symm hu' hv'
      (hS k.2 k'.2 (fun h => hne (Subtype.ext h)))
  set c0 : ℝ := ((1 + ρ) ^ e) * (ρ ^ d * V) with hc0
  have hc0pos : 0 < c0 := by positivity
  have hlow : ∀ k : S, c0 * (u6j k.1) ^ (-(2 * p)) ≤ ∫ y in B k, (u6j y) ^ e := by
    intro k
    have hk := u6j_pos k.1
    have hbd : ∀ y ∈ B k, ((1 + ρ) * u6j k.1) ^ e ≤ (u6j y) ^ e := by
      rintro y ⟨v, hv, rfl⟩
      have hv' : ‖v‖ ≤ ρ := by simpa using hv
      have h1 : u6j (u6F k.1 v) ≤ (1 + ρ) * u6j k.1 := by
        refine (u6j_le_mul _ k.1).trans ?_
        refine mul_le_mul_of_nonneg_right ?_ hk.le
        have := norm_u6F_sub_le k.1 v
        linarith
      exact Real.rpow_le_rpow_of_nonpos (u6j_pos _) h1 he0
    have h2 := setIntegral_ge_of_const_le_real (μ := volume) (f := fun y => (u6j y) ^ e)
      (hBcomp k).isClosed.measurableSet (hBcomp k).measure_lt_top.ne hbd hint.integrableOn
    refine le_trans (le_of_eq ?_) h2
    show _ = ((1 + ρ) * u6j k.1) ^ e * volume.real (u6F k.1 '' closedBall 0 ρ)
    rw [u6_vol_real k.1 hρ0.le, Real.mul_rpow (by positivity) hk.le, hc0]
    have h3 : (u6j k.1) ^ (-(2 * p)) = (u6j k.1) ^ e * (1 / u6j k.1) := by
      rw [he, one_div, ← Real.rpow_neg_one, ← Real.rpow_add hk]
      congr 1; ring
    rw [h3]; ring
  have hsum : ∀ T : Finset S, ∑ k ∈ T, c0 * (u6j k.1) ^ (-(2 * p)) ≤ I := by
    intro T
    calc ∑ k ∈ T, c0 * (u6j k.1) ^ (-(2 * p)) ≤ ∑ k ∈ T, ∫ y in B k, (u6j y) ^ e :=
          Finset.sum_le_sum (fun k _ => hlow k)
      _ = ∫ y in ⋃ k ∈ T, B k, (u6j y) ^ e :=
          (integral_biUnion_finset T (fun k _ => (hBcomp k).isClosed.measurableSet)
            (fun k _ k' _ hne => hdisj hne) (fun k _ => hint.integrableOn)).symm
      _ ≤ I := setIntegral_le_integral hint
          (Filter.Eventually.of_forall (fun y => Real.rpow_nonneg (u6j_pos y).le _))
  have hsm : Summable (fun k : S => c0 * (u6j k.1) ^ (-(2 * p))) :=
    summable_of_sum_le (c := I) (fun k => by have := u6j_pos k.1; positivity) hsum
  simpa [mul_comm] using (summable_mul_left_iff hc0pos.ne').mp hsm

end HRS.U6
