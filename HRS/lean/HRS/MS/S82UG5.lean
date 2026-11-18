import HRS.MS.S82UG4

/-!
# S8.2 A04 (S82U), part 5: tame functions (polynomial-pole envelopes) are in `L²(canonicalP)`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82U
open HRS HRS.Whole HRS.MS.Phase2S82

section tame
variable {d N : ℕ}

/-- a function dominated off collisions by `C · u4Env p q`. -/
def u4Tame (g : EucConfig d N → ℝ) : Prop :=
  ∃ C p q : ℝ, 0 ≤ C ∧ 0 ≤ p ∧ 0 ≤ q ∧ ∀ X : EucConfig d N, X ∉ eucCollisionSet d N → |g X| ≤ C * u4Env p q X

lemma u4Env_ge_one {p q : ℝ} (hp : 0 ≤ p) (X : EucConfig d N) : 1 ≤ u4Env p q X := by
  unfold u4Env
  have h1 : 1 ≤ (1 + ‖X‖) ^ p := Real.one_le_rpow (by linarith [norm_nonneg X]) hp
  have h2 : 1 ≤ ∏ i, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-q)) := by
    refine u4_one_le_prod _ fun i => ?_
    have := Finset.prod_le_prod_of_subset_of_one_le₀ (f := fun j => 1 + ‖X i - X j‖ ^ (-q))
      (s := ∅) (t := Finset.univ.erase i) (Finset.empty_subset _)
      (fun j _ => by linarith [Real.rpow_nonneg (norm_nonneg (X i - X j)) (-q)])
      (fun j _ _ => by linarith [Real.rpow_nonneg (norm_nonneg (X i - X j)) (-q)])
    simpa using this
  nlinarith

lemma u4_pair_mono {q q' : ℝ} (hq : 0 ≤ q) (hqq : q ≤ q') {r : ℝ} (hr : 0 < r) :
    1 + r ^ (-q) ≤ 2 * (1 + r ^ (-q')) := by
  by_cases h : r < 1
  · have : r ^ (-q) ≤ r ^ (-q') := Real.rpow_le_rpow_of_exponent_ge hr h.le (by linarith)
    have : 0 ≤ r ^ (-q') := Real.rpow_nonneg hr.le _
    linarith
  · push_neg at h
    have h1 : r ^ (-q) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h (by linarith)
    have : 0 ≤ r ^ (-q') := Real.rpow_nonneg hr.le _
    linarith

lemma u4_pair_mul {q q' : ℝ} (hq : 0 ≤ q) (hq' : 0 ≤ q') {r : ℝ} (hr : 0 < r) :
    (1 + r ^ (-q)) * (1 + r ^ (-q')) ≤ 4 * (1 + r ^ (-(q + q'))) := by
  have e : r ^ (-(q + q')) = r ^ (-q) * r ^ (-q') := by
    rw [neg_add, Real.rpow_add hr]
  rw [e]
  have a := Real.rpow_nonneg hr.le (-q)
  have b := Real.rpow_nonneg hr.le (-q')
  by_cases h : r < 1
  · have a1 : 1 ≤ r ^ (-q) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr h.le (by linarith)
    have b1 : 1 ≤ r ^ (-q') := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr h.le (by linarith)
    nlinarith [mul_nonneg a b, mul_nonneg (sub_nonneg.2 a1) (sub_nonneg.2 b1)]
  · push_neg at h
    have a1 : r ^ (-q) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h (by linarith)
    have b1 : r ^ (-q') ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h (by linarith)
    nlinarith [mul_nonneg a b]


lemma u4_prod2_pos (c : ℝ) : ∀ X : EucConfig d N, 0 ≤ ∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, (|c| : ℝ) :=
  fun _ => Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => abs_nonneg c

lemma u4Env_nonneg {p q : ℝ} (hp : 0 ≤ p) (X : EucConfig d N) : 0 ≤ u4Env p q X := by
  linarith [u4Env_ge_one (q := q) hp X]

lemma u4Env_mono {p p' q q' : ℝ} (hp : 0 ≤ p) (hpp : p ≤ p') (hq : 0 ≤ q) (hqq : q ≤ q')
    (X : EucConfig d N) (hX : X ∉ eucCollisionSet d N) :
    u4Env p q X ≤ (∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, (2 : ℝ)) * u4Env p' q' X := by
  have hne : ∀ i j : Fin N, i ≠ j → 0 < ‖X i - X j‖ := fun i j hij =>
    norm_pos_iff.2 (sub_ne_zero.2 (fun h => hX ⟨i, j, hij, h⟩))
  unfold u4Env
  have h1 : (1 + ‖X‖) ^ p ≤ (1 + ‖X‖) ^ p' := Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg X]) hpp
  have h2 : ∏ i, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-q)) ≤
      ∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, (2 * (1 + ‖X i - X j‖ ^ (-q'))) := by
    refine Finset.prod_le_prod₀ (fun i _ => Finset.prod_nonneg fun j _ => by
      linarith [Real.rpow_nonneg (norm_nonneg (X i - X j)) (-q)]) fun i _ => ?_
    refine Finset.prod_le_prod₀ (fun j _ => by
      linarith [Real.rpow_nonneg (norm_nonneg (X i - X j)) (-q)]) fun j hj => ?_
    exact u4_pair_mono hq hqq (hne i j (Finset.ne_of_mem_erase hj).symm)
  have h3 : ∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, (2 * (1 + ‖X i - X j‖ ^ (-q'))) =
      (∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, (2 : ℝ)) *
        ∏ i, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-q')) := by
    simp only [Finset.prod_mul_distrib]
  have hK : 0 ≤ ∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, (2 : ℝ) :=
    Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => by norm_num
  have hP0 : 0 ≤ ∏ i, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-q)) :=
    Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => by
      linarith [Real.rpow_nonneg (norm_nonneg (X i - X j)) (-q)]
  have hA0 : 0 ≤ (1 + ‖X‖) ^ p := Real.rpow_nonneg (by linarith [norm_nonneg X]) _
  calc (1 + ‖X‖) ^ p * ∏ i, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-q))
      ≤ (1 + ‖X‖) ^ p' * ((∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, (2 : ℝ)) *
        ∏ i, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-q'))) := by
        rw [← h3]
        exact mul_le_mul h1 h2 hP0 (Real.rpow_nonneg (by linarith [norm_nonneg X]) _)
    _ = _ := by ring

lemma u4Env_mul {p p' q q' : ℝ} (hp : 0 ≤ p) (hp' : 0 ≤ p') (hq : 0 ≤ q) (hq' : 0 ≤ q')
    (X : EucConfig d N) (hX : X ∉ eucCollisionSet d N) :
    u4Env p q X * u4Env p' q' X ≤
      (∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, (4 : ℝ)) * u4Env (p + p') (q + q') X := by
  have hne : ∀ i j : Fin N, i ≠ j → 0 < ‖X i - X j‖ := fun i j hij =>
    norm_pos_iff.2 (sub_ne_zero.2 (fun h => hX ⟨i, j, hij, h⟩))
  unfold u4Env
  have hA : (1 + ‖X‖) ^ p * (1 + ‖X‖) ^ p' = (1 + ‖X‖) ^ (p + p') := by
    rw [Real.rpow_add (by linarith [norm_nonneg X])]
  have h2 : (∏ i, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-q))) *
      (∏ i, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-q'))) ≤
      ∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, (4 * (1 + ‖X i - X j‖ ^ (-(q + q')))) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun i _ => mul_nonneg
      (Finset.prod_nonneg fun j _ => by linarith [Real.rpow_nonneg (norm_nonneg (X i - X j)) (-q)])
      (Finset.prod_nonneg fun j _ => by linarith [Real.rpow_nonneg (norm_nonneg (X i - X j)) (-q')])) fun i _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun j _ => by
      have := Real.rpow_nonneg (norm_nonneg (X i - X j)) (-q)
      have := Real.rpow_nonneg (norm_nonneg (X i - X j)) (-q')
      positivity) fun j hj => ?_
    exact u4_pair_mul hq hq' (hne i j (Finset.ne_of_mem_erase hj).symm)
  have h3 : ∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, (4 * (1 + ‖X i - X j‖ ^ (-(q + q')))) =
      (∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, (4 : ℝ)) *
        ∏ i, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-(q + q'))) := by
    simp only [Finset.prod_mul_distrib]
  calc (1 + ‖X‖) ^ p * (∏ i, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-q))) *
        ((1 + ‖X‖) ^ p' * ∏ i, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-q')))
      = ((1 + ‖X‖) ^ p * (1 + ‖X‖) ^ p') * ((∏ i, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-q))) *
      (∏ i, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-q')))) := by ring
    _ ≤ (1 + ‖X‖) ^ (p + p') * ((∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, (4 : ℝ)) *
        ∏ i, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-(q + q')))) := by
        rw [hA, ← h3]
        exact mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (by linarith [norm_nonneg X]) _)
    _ = _ := by ring

lemma u4Tame_add {f g : EucConfig d N → ℝ} (hf : u4Tame f) (hg : u4Tame g) : u4Tame (fun X => f X + g X) := by
  obtain ⟨C, p, q, hC, hp, hq, hf⟩ := hf
  obtain ⟨C', p', q', hC', hp', hq', hg⟩ := hg
  set K := ∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, (2 : ℝ) with hK
  have hK0 : 0 ≤ K := Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => by norm_num
  refine ⟨(C + C') * K, max p p', max q q', by positivity, le_max_of_le_left hp, le_max_of_le_left hq,
    fun X hX => ?_⟩
  have e1 := u4Env_mono (p' := max p p') (q' := max q q') hp (le_max_left _ _) hq (le_max_left _ _) X hX
  have e2 := u4Env_mono (p' := max p p') (q' := max q q') hp' (le_max_right _ _) hq' (le_max_right _ _) X hX
  have := hf X hX
  have := hg X hX
  calc |f X + g X| ≤ |f X| + |g X| := abs_add_le _ _
    _ ≤ C * u4Env p q X + C' * u4Env p' q' X := add_le_add (hf X hX) (hg X hX)
    _ ≤ C * (K * u4Env (max p p') (max q q') X) + C' * (K * u4Env (max p p') (max q q') X) :=
        add_le_add (mul_le_mul_of_nonneg_left e1 hC) (mul_le_mul_of_nonneg_left e2 hC')
    _ = (C + C') * K * u4Env (max p p') (max q q') X := by ring

lemma u4Tame_mul {f g : EucConfig d N → ℝ} (hf : u4Tame f) (hg : u4Tame g) : u4Tame (fun X => f X * g X) := by
  obtain ⟨C, p, q, hC, hp, hq, hf⟩ := hf
  obtain ⟨C', p', q', hC', hp', hq', hg⟩ := hg
  set K := ∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, (4 : ℝ) with hK
  have hK0 : 0 ≤ K := Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => by norm_num
  refine ⟨C * C' * K, p + p', q + q', by positivity, by linarith, by linarith, fun X hX => ?_⟩
  have e := u4Env_mul hp hp' hq hq' X hX
  have h1 := hf X hX
  have h2 := hg X hX
  have a0 := u4Env_nonneg (q := q) hp X
  have b0 := u4Env_nonneg (q := q') hp' X
  calc |f X * g X| = |f X| * |g X| := abs_mul _ _
    _ ≤ (C * u4Env p q X) * (C' * u4Env p' q' X) :=
        mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hC a0)
    _ = C * C' * (u4Env p q X * u4Env p' q' X) := by ring
    _ ≤ C * C' * (K * u4Env (p + p') (q + q') X) := mul_le_mul_of_nonneg_left e (mul_nonneg hC hC')
    _ = C * C' * K * u4Env (p + p') (q + q') X := by ring

lemma u4Tame_const (c : ℝ) : u4Tame (fun _ : EucConfig d N => c) := by
  refine ⟨|c|, 0, 0, abs_nonneg _, le_rfl, le_rfl, fun X _ => ?_⟩
  have := u4Env_ge_one (q := 0) (le_refl (0:ℝ)) X
  nlinarith [abs_nonneg c]

lemma u4Tame_norm : u4Tame (fun X : EucConfig d N => ‖X‖) := by
  refine ⟨1, 1, 0, zero_le_one, zero_le_one, le_rfl, fun X _ => ?_⟩
  unfold u4Env
  have h2 : 1 ≤ ∏ i, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-(0:ℝ))) := by
    refine u4_one_le_prod _ fun i => ?_
    have := Finset.prod_le_prod_of_subset_of_one_le₀ (f := fun j => 1 + ‖X i - X j‖ ^ (-(0:ℝ)))
      (s := ∅) (t := Finset.univ.erase i) (Finset.empty_subset _)
      (fun j _ => by linarith [Real.rpow_nonneg (norm_nonneg (X i - X j)) (-(0:ℝ))])
      (fun j _ _ => by linarith [Real.rpow_nonneg (norm_nonneg (X i - X j)) (-(0:ℝ))])
    simpa using this
  rw [abs_of_nonneg (norm_nonneg X), Real.rpow_one]
  nlinarith [norm_nonneg X]

lemma u4Tame_pole {k l : Fin N} (hkl : k ≠ l) {e : ℝ} (he : 0 ≤ e) :
    u4Tame (fun X : EucConfig d N => ‖X k - X l‖ ^ (-e)) := by
  refine ⟨1, 0, e, zero_le_one, le_rfl, he, fun X hX => ?_⟩
  have hne : 0 < ‖X k - X l‖ := norm_pos_iff.2 (sub_ne_zero.2 (fun h => hX ⟨k, l, hkl, h⟩))
  unfold u4Env
  rw [Real.rpow_zero, one_mul, one_mul, abs_of_nonneg (Real.rpow_nonneg hne.le _)]
  have hf : ∀ i j, 1 ≤ 1 + ‖X i - X j‖ ^ (-e) := fun i j => by
    linarith [Real.rpow_nonneg (norm_nonneg (X i - X j)) (-e)]
  have h1 : 1 + ‖X k - X l‖ ^ (-e) ≤ ∏ j ∈ Finset.univ.erase k, (1 + ‖X k - X j‖ ^ (-e)) := by
    have := Finset.prod_le_prod_of_subset_of_one_le₀ (f := fun j => 1 + ‖X k - X j‖ ^ (-e))
      (s := {l}) (t := Finset.univ.erase k) (by simpa using hkl.symm)
      (fun j _ => by linarith [hf k j]) (fun j _ _ => hf k j)
    simpa using this
  have h2 : ∏ j ∈ Finset.univ.erase k, (1 + ‖X k - X j‖ ^ (-e)) ≤
      ∏ i, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-e)) := by
    refine u4_single_le_prod (fun i => ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-e))) (fun i => ?_) k
    have := Finset.prod_le_prod_of_subset_of_one_le₀ (f := fun j => 1 + ‖X i - X j‖ ^ (-e))
      (s := ∅) (t := Finset.univ.erase i) (Finset.empty_subset _)
      (fun j _ => by linarith [hf i j]) (fun j _ _ => hf i j)
    simpa using this
  linarith [Real.rpow_nonneg hne.le (-e)]

lemma u4Tame_sum {ι : Type*} (s : Finset ι) (g : ι → EucConfig d N → ℝ) (hg : ∀ i ∈ s, u4Tame (g i)) :
    u4Tame (fun X => ∑ i ∈ s, g i X) := by
  have := Finset.sum_induction g (fun h : EucConfig d N → ℝ => u4Tame h)
    (fun a b ha hb => u4Tame_add ha hb) (u4Tame_const (d := d) (N := N) 0) hg
  convert this using 1
  ext X
  simp [Finset.sum_apply]

lemma u4Tame_const_mul (c : ℝ) {f : EucConfig d N → ℝ} (hf : u4Tame f) : u4Tame (fun X => c * f X) :=
  u4Tame_mul (u4Tame_const c) hf

lemma u4Tame_memLp (hd : 2 ≤ d) (hN : 0 < N) {a beta : ℝ} (ha : 0 < a) (hbeta : 0 < beta)
    {g : EucConfig d N → ℝ} (hg : u4Tame g) (hm : AEStronglyMeasurable g (canonicalP d N a beta)) :
    MemLp g 2 (canonicalP d N a beta) := by
  obtain ⟨C, p, q, hC, hp, hq, hb⟩ := hg
  have hint := (u4_env_L2 hd hN ha hbeta hp hq).const_mul (C ^ 2)
  refine (memLp_two_iff_integrable_sq hm).2 ?_
  refine Integrable.mono' hint (hm.pow 2) ?_
  have hae : ∀ᵐ X ∂(canonicalP d N a beta), X ∉ eucCollisionSet d N := by
    rw [ae_iff]; simpa using u4_P_coll hd N a beta
  filter_upwards [hae] with X hX
  rw [Real.norm_eq_abs, abs_pow]
  calc |g X| ^ 2 ≤ (C * u4Env p q X) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hb X hX) 2
    _ = C ^ 2 * u4Env p q X ^ 2 := by ring

end tame

end HRS.MS.S82U
