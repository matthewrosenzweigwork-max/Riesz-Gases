import HRS.MS.S82WK5

/-!
# S8.2 A04 (S82W), part 9: the derivative of the canonical Hamiltonian off collisions
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82W
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82U

section ham
variable {d N : ℕ}

lemma w_riesz_hasFDerivAt (s : ℝ) {z : Euc d} (hz : z ≠ 0) :
    HasFDerivAt (rieszKernel d s) (innerSL ℝ (rieszKernelGrad d s z)) z := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hu : 0 < ‖z‖ ^ 2 + (0 : ℝ) ^ 2 := by positivity
  have h := movtr_gEps_hasFDerivAt (d := d) s 0 z hu
  rw [movtr_gEps_zero] at h
  convert h using 1
  rw [movtr_rieszKernelGrad_eq s hz, movtr_u0 (s := s) z hz]
  ext w
  simp only [innerSL_apply_apply, real_inner_smul_left, ContinuousLinearMap.smul_apply, smul_eq_mul]
  congr 2
  ring_nf

lemma w_riesz_even (s : ℝ) (x : Euc d) : rieszKernel d s (-x) = rieszKernel d s x := by
  unfold rieszKernel; simp [norm_neg]

lemma w_rieszGrad_odd (s : ℝ) {z : Euc d} (hz : z ≠ 0) :
    rieszKernelGrad d s (-z) = - rieszKernelGrad d s z := by
  rw [movtr_rieszKernelGrad_eq s hz, movtr_rieszKernelGrad_eq s (neg_ne_zero.2 hz), norm_neg, smul_neg]

lemma w_pair_sum_sym (f : Fin N → Fin N → ℝ) (hf : ∀ j k, f j k = f k j) :
    ∑ j, ∑ k ∈ Finset.univ.filter (fun k => j < k), f j k =
      (1 / 2) * ∑ j, ∑ k ∈ Finset.univ.erase j, f j k := by
  have h1 : ∀ j, ∑ k ∈ Finset.univ.erase j, f j k =
      ∑ k ∈ Finset.univ.filter (fun k => j < k), f j k + ∑ k ∈ Finset.univ.filter (fun k => k < j), f j k := by
    intro j
    have : Finset.univ.erase j = Finset.univ.filter (fun k => j < k) ∪ Finset.univ.filter (fun k => k < j) := by
      ext k; simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_filter, true_and]
      constructor
      · intro h; rcases lt_or_gt_of_ne h with h | h
        · exact Or.inr h
        · exact Or.inl h
      · intro h; rcases h with h | h
        · exact ne_of_gt h
        · exact ne_of_lt h
    rw [this, Finset.sum_union]
    rw [Finset.disjoint_filter]
    intro k _ h1 h2; exact absurd (h1.trans h2) (lt_irrefl _)
  have h2 : ∑ j, ∑ k ∈ Finset.univ.filter (fun k => k < j), f j k =
      ∑ j, ∑ k ∈ Finset.univ.filter (fun k => j < k), f j k := by
    have : ∀ j, ∑ k ∈ Finset.univ.filter (fun k => k < j), f j k =
        ∑ k, if k < j then f j k else 0 := fun j => by rw [Finset.sum_filter]
    simp_rw [this]
    have h3 : ∀ j, ∑ k ∈ Finset.univ.filter (fun k => j < k), f j k = ∑ k, if j < k then f j k else 0 :=
      fun j => by rw [Finset.sum_filter]
    simp_rw [h3]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : k < j
    · simp [h, hf j k]
    · simp [h]
  simp_rw [h1, Finset.sum_add_distrib, h2]
  ring

lemma w_H_sym (hd : 2 ≤ d) (a : ℝ) (X : EucConfig d N) :
    HRS.Whole.canonicalHamiltonian (rieszKernel d (criticalS d)) (confinement a) X =
      ∑ j, confinement a (X j) + (1 / (2 * (N : ℝ))) *
        ∑ j, ∑ k ∈ Finset.univ.erase j, rieszKernel d (criticalS d) (X j - X k) := by
  unfold HRS.Whole.canonicalHamiltonian
  rw [w_pair_sum_sym (fun j k => rieszKernel d (criticalS d) (X j - X k)) (fun j k => by
    rw [← w_riesz_even (criticalS d) (X k - X j), neg_sub])]
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · subst h0; simp
  · field_simp

lemma w_u4L_apply (i j : Fin N) (v : Euc d) : u4L d N i v j = if j = i then v else 0 := by
  simp only [u4L, ContinuousLinearMap.pi_apply, Pi.single_apply]
  split_ifs <;> simp

lemma w_Hs_hasFDerivAt (hd : 2 ≤ d) (a : ℝ) {X : EucConfig d N} (hX : X ∉ eucCollisionSet d N) :
    ∃ Hd : EucConfig d N →L[ℝ] ℝ,
      HasFDerivAt (HRS.Whole.canonicalHamiltonian (rieszKernel d (criticalS d)) (confinement a)) Hd X ∧
      ∀ (i : Fin N) (v : Euc d), Hd (u4L d N i v) =
        inner ℝ (a • X i + (1 / (N : ℝ)) • ∑ k ∈ Finset.univ.erase i, rieszKernelGrad d (criticalS d) (X i - X k)) v := by
  have hconf : ∀ j : Fin N, HasFDerivAt (fun Y : EucConfig d N => confinement a (Y j))
      ((a / 2) • ((2 : ℝ) • (innerSL ℝ (X j)).comp (wP d N j))) X := by
    intro j
    have h1 := (hasStrictFDerivAt_norm_sq (X j)).hasFDerivAt.comp X (wP d N j).hasFDerivAt
    have h2 := h1.const_mul (a / 2)
    have e : (fun Y : EucConfig d N => confinement a (Y j)) =
        fun Y => (a / 2) * ((fun x : Euc d => ‖x‖ ^ 2) ∘ (wP d N j)) Y := by
      funext Y; simp only [confinement, Function.comp, wP_apply]; ring
    rw [e]
    convert h2 using 2
    ext w
    simp [two_smul]
  have hpair : ∀ j : Fin N, ∀ k ∈ Finset.univ.erase j, HasFDerivAt
      (fun Y : EucConfig d N => rieszKernel d (criticalS d) (Y j - Y k))
      ((innerSL ℝ (rieszKernelGrad d (criticalS d) (X j - X k))).comp (wL d N j k)) X := by
    intro j k hk
    have hne : X j - X k ≠ 0 := sub_ne_zero.2 (fun h => hX ⟨j, k, (Finset.ne_of_mem_erase hk).symm, h⟩)
    exact (w_riesz_hasFDerivAt (criticalS d) hne).comp X (wL d N j k).hasFDerivAt
  set Hd : EucConfig d N →L[ℝ] ℝ := ∑ j, (a / 2) • ((2 : ℝ) • (innerSL ℝ (X j)).comp (wP d N j)) +
    (1 / (2 * (N : ℝ))) • ∑ j, ∑ k ∈ Finset.univ.erase j,
      (innerSL ℝ (rieszKernelGrad d (criticalS d) (X j - X k))).comp (wL d N j k) with hHd
  have hHs : HasFDerivAt (fun Y : EucConfig d N => ∑ j, confinement a (Y j) + (1 / (2 * (N : ℝ))) *
        ∑ j, ∑ k ∈ Finset.univ.erase j, rieszKernel d (criticalS d) (Y j - Y k)) Hd X := by
    refine (HasFDerivAt.fun_sum fun j _ => hconf j).add (HasFDerivAt.const_mul ?_ _)
    exact HasFDerivAt.fun_sum fun j _ => HasFDerivAt.fun_sum fun k hk => hpair j k hk
  refine ⟨Hd, ?_, ?_⟩
  · have : HRS.Whole.canonicalHamiltonian (rieszKernel d (criticalS d)) (confinement a) =
        fun Y : EucConfig d N => ∑ j, confinement a (Y j) + (1 / (2 * (N : ℝ))) *
          ∑ j, ∑ k ∈ Finset.univ.erase j, rieszKernel d (criticalS d) (Y j - Y k) := by
      funext Y; exact w_H_sym hd a Y
    rw [this]; exact hHs
  · intro i v
    rw [hHd]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply, wP_apply, wL_apply, w_u4L_apply, smul_eq_mul]
    set G := rieszKernelGrad d (criticalS d) with hG
    have e1 : ∑ x : Fin N, a / 2 * (2 * inner ℝ (X x) (if x = i then v else 0)) = a * inner ℝ (X i) v := by
      have : ∀ x : Fin N, a / 2 * (2 * inner ℝ (X x) (if x = i then v else 0)) =
          if x = i then a * inner ℝ (X i) v else 0 := by
        intro x; split_ifs with h
        · subst h; ring
        · simp
      simp_rw [this]; simp
    set c : Fin N → Fin N → ℝ := fun j k => inner ℝ (G (X j - X k)) v with hc
    have eterm : ∀ j k : Fin N, inner ℝ (G (X j - X k)) ((if j = i then v else 0) - if k = i then v else 0) =
        (if j = i then c j k else 0) - (if k = i then c j k else 0) := by
      intro j k
      by_cases h1 : j = i <;> by_cases h2 : k = i <;> simp [h1, h2, hc, inner_sub_right]
    have e2a : ∑ j : Fin N, ∑ k ∈ Finset.univ.erase j, (if j = i then c j k else 0) =
        ∑ k ∈ Finset.univ.erase i, c i k := by
      have : ∀ j : Fin N, ∑ k ∈ Finset.univ.erase j, (if j = i then c j k else 0) =
          if j = i then ∑ k ∈ Finset.univ.erase j, c j k else 0 := by
        intro j; split_ifs <;> simp
      simp_rw [this]; simp
    have e2b : ∑ j : Fin N, ∑ k ∈ Finset.univ.erase j, (if k = i then c j k else 0) =
        ∑ j ∈ Finset.univ.erase i, c j i := by
      have : ∀ j : Fin N, ∑ k ∈ Finset.univ.erase j, (if k = i then c j k else 0) =
          if i ≠ j then c j i else 0 := by
        intro j
        rw [Finset.sum_ite_eq']
        simp [Finset.mem_erase, eq_comm]
      simp_rw [this]
      rw [← Finset.sum_filter, Finset.filter_ne]
    have eodd : ∀ j ∈ Finset.univ.erase i, c j i = - c i j := by
      intro j hj
      have hne : X j - X i ≠ 0 := sub_ne_zero.2 (fun h => hX ⟨j, i, Finset.ne_of_mem_erase hj, h⟩)
      simp only [hc, hG]
      rw [← neg_sub (X j) (X i), w_rieszGrad_odd (criticalS d) hne, inner_neg_left, neg_neg]
    simp_rw [eterm]
    simp only [Finset.sum_sub_distrib]
    rw [e2a, e2b, Finset.sum_congr rfl eodd, Finset.sum_neg_distrib, e1]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, sum_inner]
    simp only [hc]
    ring

end ham

end HRS.MS.S82W
