import HRS.MS.R2IidAux1

/-!
# S11P, helper file 1: cosine expansion of continuous functions on `[0,T]`

`s11p_cos_expand`: if `g` is continuous on `[0,T]` and `b_n = (1+n²)^{3/8} ∫_0^T e_n g` is summable (`e_n` the cosine basis
`r2CosBasis`), then `g(t) = ∑_n (1+n²)^{-3/8} e_n(t) b_n` for all `t ∈ [0,T]`.  The proof uses Stone-Weierstrass for the
algebra spanned by `cos(nπt/T)`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

set_option linter.unusedSectionVars false

namespace HRS.Whole

section Kap

/-- `κ_n = (1+n²)^{-3/8}`. -/
def s11p_kap (n : ℕ) : ℝ := (1 + (n : ℝ) ^ 2) ^ (-(3 : ℝ) / 8)

theorem s11p_kap_pos (n : ℕ) : 0 < s11p_kap n := Real.rpow_pos_of_pos (by positivity) _

theorem s11p_kap_mul (n : ℕ) : s11p_kap n * (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) = 1 := by
  unfold s11p_kap
  rw [← Real.rpow_add (by positivity)]
  norm_num

theorem s11p_kap_le_one (n : ℕ) : s11p_kap n ≤ 1 := by
  unfold s11p_kap
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · have : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
    linarith
  · norm_num

theorem s11p_kap_sq_summable : Summable fun n : ℕ => s11p_kap n ^ 2 := by
  have h1 : Summable fun n : ℕ => 2 * (((n + 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2))⁻¹ :=
    ((summable_nat_add_iff 1).2 (Real.summable_nat_rpow_inv.2 (by norm_num))).mul_left 2
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) h1
  have hp : (0 : ℝ) < 1 + (n : ℝ) ^ 2 := by positivity
  have e1 : s11p_kap n ^ 2 = ((1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 4))⁻¹ := by
    unfold s11p_kap
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le, ← Real.rpow_neg hp.le]
    congr 1
    norm_num
  rw [e1]
  have h2 : ((n + 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 2 * (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 4) := by
    have h3 : ((n + 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) = (((n + 1 : ℕ) : ℝ) ^ 2) ^ ((3 : ℝ) / 4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1; norm_num
    rw [h3]
    have h4 : (((n + 1 : ℕ) : ℝ) ^ 2) ≤ 2 * (1 + (n : ℝ) ^ 2) := by
      push_cast; nlinarith [sq_nonneg ((n : ℝ) - 1)]
    calc (((n + 1 : ℕ) : ℝ) ^ 2) ^ ((3 : ℝ) / 4) ≤ (2 * (1 + (n : ℝ) ^ 2)) ^ ((3 : ℝ) / 4) :=
          Real.rpow_le_rpow (by positivity) h4 (by norm_num)
      _ = 2 ^ ((3 : ℝ) / 4) * (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 4) :=
          Real.mul_rpow (by norm_num) hp.le
      _ ≤ 2 * (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 4) := by
          gcongr
          calc (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
  have hpos : 0 < ((n + 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos (by positivity) _
  have hpos2 : 0 < (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hp _
  calc ((1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 4))⁻¹
      = 2 * (2 * (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 4))⁻¹ := by field_simp
    _ ≤ 2 * (((n + 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2))⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_anti₀ hpos h2) (by norm_num)

end Kap

section Cos

variable {T : ℝ}

/-- The amplitude of the cosine basis: `e_n(t) = A_n cos(nπt/T)`. -/
def s11p_amp (T : ℝ) (n : ℕ) : ℝ := if n = 0 then 1 / Real.sqrt T else Real.sqrt (2 / T)

theorem s11p_cos_eq (T : ℝ) (n : ℕ) (t : ℝ) :
    r2CosBasis T n t = s11p_amp T n * Real.cos (n * Real.pi * t / T) := by
  unfold r2CosBasis s11p_amp
  by_cases h : n = 0
  · simp [h]
  · simp [h]

theorem s11p_amp_le (hT : 0 < T) (n : ℕ) : |s11p_amp T n| ≤ Real.sqrt (2 / T) := by
  unfold s11p_amp
  split_ifs
  · rw [abs_of_nonneg (by positivity), one_div, ← Real.sqrt_inv]
    apply Real.sqrt_le_sqrt
    rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_right (by norm_num) hT.le
  · rw [abs_of_nonneg (Real.sqrt_nonneg _)]

theorem s11p_cos_bound (hT : 0 < T) (n : ℕ) (t : ℝ) : |r2CosBasis T n t| ≤ Real.sqrt (2 / T) := by
  rw [s11p_cos_eq, abs_mul]
  calc |s11p_amp T n| * |Real.cos _| ≤ Real.sqrt (2 / T) * 1 :=
        mul_le_mul (s11p_amp_le hT n) (Real.abs_cos_le_one _) (abs_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := mul_one _

theorem s11p_cos_continuous (T : ℝ) (n : ℕ) : Continuous (r2CosBasis T n) := by
  have : r2CosBasis T n = fun t => s11p_amp T n * Real.cos (n * Real.pi * t / T) :=
    funext (s11p_cos_eq T n)
  rw [this]; fun_prop

/-- `∫_0^T cos(jπt/T) dt = T [j = 0]` for integers `j`. -/
theorem s11p_integral_cos_int (hT : 0 < T) (j : ℤ) :
    ∫ t in (0 : ℝ)..T, Real.cos ((j : ℝ) * Real.pi * t / T) = if j = 0 then T else 0 := by
  by_cases hj : j = 0
  · subst hj
    simp
  · rw [if_neg hj]
    have hc : ((j : ℝ) * Real.pi / T) ≠ 0 := by
      have : (j : ℝ) ≠ 0 := by exact_mod_cast hj
      positivity
    have e : (fun t : ℝ => Real.cos ((j : ℝ) * Real.pi * t / T)) =
        fun t => Real.cos (((j : ℝ) * Real.pi / T) * t) := by
      funext t; congr 1; ring
    rw [e, intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc, integral_cos]
    have : ((j : ℝ) * Real.pi / T) * T = (j : ℝ) * Real.pi := by field_simp
    simp [this, Real.sin_int_mul_pi]

theorem s11p_cos_mul_cos (x y : ℝ) :
    Real.cos x * Real.cos y = (Real.cos (x - y) + Real.cos (x + y)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]; ring

/-- Orthonormality of the cosine basis on `[0,T]`. -/
theorem s11p_cos_orth (hT : 0 < T) (n k : ℕ) :
    ∫ t in Set.Icc (0 : ℝ) T, r2CosBasis T n t * r2CosBasis T k t = if n = k then 1 else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT.le]
  have e : ∀ t : ℝ, r2CosBasis T n t * r2CosBasis T k t =
      (s11p_amp T n * s11p_amp T k / 2) *
        (Real.cos (((n : ℤ) - k : ℤ) * Real.pi * t / T) + Real.cos (((n : ℤ) + k : ℤ) * Real.pi * t / T)) := by
    intro t
    rw [s11p_cos_eq, s11p_cos_eq]
    have := s11p_cos_mul_cos (n * Real.pi * t / T) (k * Real.pi * t / T)
    have h1 : (n * Real.pi * t / T - k * Real.pi * t / T) = ((((n : ℤ) - k : ℤ) : ℝ)) * Real.pi * t / T := by
      push_cast; ring
    have h2 : (n * Real.pi * t / T + k * Real.pi * t / T) = ((((n : ℤ) + k : ℤ) : ℝ)) * Real.pi * t / T := by
      push_cast; ring
    rw [h1, h2] at this
    calc _ = s11p_amp T n * s11p_amp T k * (Real.cos (n * Real.pi * t / T) * Real.cos (k * Real.pi * t / T)) := by ring
      _ = _ := by rw [this]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add]
  · rw [s11p_integral_cos_int hT, s11p_integral_cos_int hT]
    have hsq : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT.le
    have hsq2 : Real.sqrt (2 / T) * Real.sqrt (2 / T) = 2 / T := Real.mul_self_sqrt (by positivity)
    have hr : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
    have h1 : (((n : ℤ) - k = 0)) ↔ n = k := by omega
    have h2 : ((n : ℤ) + k = 0) ↔ (n = 0 ∧ k = 0) := by omega
    simp only [h1, h2]
    unfold s11p_amp
    by_cases hn : n = 0 <;> by_cases hk : k = 0
    · subst hn; subst hk
      simp only [if_true, and_self]
      field_simp
      rw [Real.sq_sqrt hT.le]; ring
    · subst hn
      simp [hk, Ne.symm hk]
    · subst hk
      simp [hn]
    · by_cases hnk : n = k
      · subst hnk
        simp [hn]
        field_simp
        rw [Real.sq_sqrt hT.le, Real.sq_sqrt (by norm_num)]; ring
      · simp [hn, hk, hnk]
  · exact (by fun_prop : Continuous fun t : ℝ => Real.cos ((((n : ℤ) - k : ℤ) : ℝ) * Real.pi * t / T)).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun t : ℝ => Real.cos ((((n : ℤ) + k : ℤ) : ℝ) * Real.pi * t / T)).intervalIntegrable _ _

end Cos

section Unique

variable {T : ℝ}

/-- `t ↦ cos(nπt/T)` as a continuous function on `[0,T]`. -/
def s11p_cosC (T : ℝ) (n : ℕ) : C(Set.Icc (0 : ℝ) T, ℝ) :=
  ⟨fun t => Real.cos (n * Real.pi * (t : ℝ) / T), by fun_prop⟩

theorem s11p_cosC_apply (T : ℝ) (n : ℕ) (t : Set.Icc (0 : ℝ) T) :
    s11p_cosC T n t = Real.cos (n * Real.pi * (t : ℝ) / T) := rfl

theorem s11p_cos_int_natAbs (j : ℤ) (a : ℝ) : Real.cos ((j : ℝ) * a) = Real.cos ((j.natAbs : ℝ) * a) := by
  rw [show ((j.natAbs : ℕ) : ℝ) = |(j : ℝ)| by simp]
  rcases abs_choice (j : ℝ) with h | h <;> rw [h]
  rw [neg_mul, Real.cos_neg]

theorem s11p_cosC_mul (T : ℝ) (n k : ℕ) :
    s11p_cosC T n * s11p_cosC T k =
      (1 / 2 : ℝ) • s11p_cosC T (n + k) + (1 / 2 : ℝ) • s11p_cosC T (((n : ℤ) - k).natAbs) := by
  ext t
  simp only [ContinuousMap.mul_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply, s11p_cosC_apply,
    smul_eq_mul]
  rw [s11p_cos_mul_cos]
  have h1 : (n * Real.pi * (t : ℝ) / T - k * Real.pi * (t : ℝ) / T) =
      (((n : ℤ) - k : ℤ) : ℝ) * (Real.pi * (t : ℝ) / T) := by push_cast; ring
  have h2 : (n * Real.pi * (t : ℝ) / T + k * Real.pi * (t : ℝ) / T) =
      ((n + k : ℕ) : ℝ) * Real.pi * (t : ℝ) / T := by push_cast; ring
  rw [h1, h2, s11p_cos_int_natAbs]
  have h3 : (((((n : ℤ) - k).natAbs : ℕ) : ℝ)) * (Real.pi * (t : ℝ) / T) =
      ((((n : ℤ) - k).natAbs : ℕ) : ℝ) * Real.pi * (t : ℝ) / T := by ring
  rw [h3]; ring

/-- The span of the cosines. -/
def s11p_S (T : ℝ) : Submodule ℝ C(Set.Icc (0 : ℝ) T, ℝ) :=
  Submodule.span ℝ (Set.range (s11p_cosC T))

theorem s11p_cosC_mem (T : ℝ) (n : ℕ) : s11p_cosC T n ∈ s11p_S T := Submodule.subset_span ⟨n, rfl⟩

theorem s11p_one_mem (T : ℝ) : (1 : C(Set.Icc (0 : ℝ) T, ℝ)) ∈ s11p_S T := by
  have : s11p_cosC T 0 = 1 := by ext t; simp [s11p_cosC_apply]
  rw [← this]; exact s11p_cosC_mem T 0

theorem s11p_S_mul (T : ℝ) (x y : C(Set.Icc (0 : ℝ) T, ℝ)) (hx : x ∈ s11p_S T) (hy : y ∈ s11p_S T) :
    x * y ∈ s11p_S T := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      rw [s11p_cosC_mul]
      exact add_mem (Submodule.smul_mem _ _ (s11p_cosC_mem T _)) (Submodule.smul_mem _ _ (s11p_cosC_mem T _))
    | zero => simpa using Submodule.zero_mem _
    | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
    | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ha
  | zero => simpa using Submodule.zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ ha

/-- The algebra of cosine polynomials. -/
def s11p_A (T : ℝ) : Subalgebra ℝ C(Set.Icc (0 : ℝ) T, ℝ) :=
  Submodule.toSubalgebra (s11p_S T) (s11p_one_mem T) (s11p_S_mul T)

theorem s11p_A_sep (hT : 0 < T) : (s11p_A T).SeparatesPoints := by
  intro x y hxy
  refine ⟨_, ⟨s11p_cosC T 1, s11p_cosC_mem T 1, rfl⟩, ?_⟩
  simp only [s11p_cosC_apply, Nat.cast_one, one_mul]
  intro h
  have hx := x.2
  have hy := y.2
  have hm : ∀ z : ℝ, z ∈ Set.Icc (0 : ℝ) T → Real.pi * z / T ∈ Set.Icc (0 : ℝ) Real.pi := by
    intro z hz
    constructor
    · have := hz.1; positivity
    · rw [div_le_iff₀ hT]; nlinarith [Real.pi_pos, hz.2]
  have := Real.injOn_cos (hm _ hx) (hm _ hy) h
  apply hxy
  apply Subtype.ext
  have hT' : T ≠ 0 := hT.ne'
  field_simp at this
  nlinarith [Real.pi_pos]

/-- Uniqueness of cosine coefficients for continuous functions. -/
theorem s11p_cos_unique (hT : 0 < T) (u : ℝ → ℝ) (hu : ContinuousOn u (Set.Icc 0 T))
    (h : ∀ n : ℕ, ∫ t in Set.Icc (0 : ℝ) T, r2CosBasis T n t * u t = 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, u t = 0 := by
  -- approximation
  have htop : (s11p_A T).topologicalClosure = ⊤ :=
    ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _ (s11p_A_sep hT)
  set uC : C(Set.Icc (0 : ℝ) T, ℝ) := ⟨fun t => u t, hu.restrict⟩ with huC
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hu
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hT.le⟩)
  -- orthogonality to the span
  have horth : ∀ s ∈ s11p_S T, ∃ s' : ℝ → ℝ, Continuous s' ∧ (∀ t : Set.Icc (0 : ℝ) T, s t = s' t) ∧
      ∫ t in Set.Icc (0 : ℝ) T, s' t * u t = 0 := by
    intro s hs
    obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hs
    refine ⟨fun t => ∑ n ∈ c.support, c n * Real.cos (n * Real.pi * t / T), by fun_prop, fun t => ?_, ?_⟩
    · rw [← hc, Finsupp.sum]
      simp [ContinuousMap.sum_apply, s11p_cosC_apply]
    · simp_rw [Finset.sum_mul]
      rw [integral_finset_sum]
      · refine Finset.sum_eq_zero fun n hn => ?_
        have hA : s11p_amp T n ≠ 0 := by
          unfold s11p_amp
          split_ifs
          · have : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
            positivity
          · have : 0 < Real.sqrt (2 / T) := Real.sqrt_pos.mpr (by positivity)
            positivity
        have h0 := h n
        simp_rw [s11p_cos_eq, mul_assoc] at h0
        rw [integral_const_mul] at h0
        have h0' := (mul_eq_zero.1 h0).resolve_left hA
        simp_rw [mul_assoc]
        rw [integral_const_mul, h0', mul_zero]
      · intro n hn
        exact (((by fun_prop : Continuous fun t : ℝ => c n * Real.cos (n * Real.pi * t / T)).continuousOn).mul
          hu).integrableOn_Icc
  have key : ∀ ε > 0, ∫ t in Set.Icc (0 : ℝ) T, u t ^ 2 ≤ M * ε * T := by
    intro ε hε
    have hmem : uC ∈ closure ((s11p_A T : Subalgebra ℝ C(Set.Icc (0 : ℝ) T, ℝ)) : Set C(Set.Icc (0 : ℝ) T, ℝ)) := by
      rw [← Subalgebra.topologicalClosure_coe, htop]; trivial
    obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.1 hmem ε hε
    obtain ⟨s', hs'c, hs', hint⟩ := horth b hb
    have hsu : IntegrableOn (fun t => s' t * u t) (Set.Icc 0 T) :=
      (hs'c.continuousOn.mul hu).integrableOn_Icc
    have huu : IntegrableOn (fun t => u t * (u t - s' t)) (Set.Icc 0 T) :=
      (hu.mul (hu.sub hs'c.continuousOn)).integrableOn_Icc
    have e1 : ∫ t in Set.Icc (0 : ℝ) T, u t ^ 2 = ∫ t in Set.Icc (0 : ℝ) T, u t * (u t - s' t) := by
      have : ∫ t in Set.Icc (0 : ℝ) T, (u t * (u t - s' t) + s' t * u t) = ∫ t in Set.Icc (0 : ℝ) T, u t ^ 2 := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        simp only; ring
      rw [← this, integral_add huu hsu, hint, add_zero]
    rw [e1]
    have hb' : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖u t * (u t - s' t)‖ ≤ M * ε := by
      intro t ht
      rw [norm_mul]
      have h1 : ‖u t‖ ≤ M := hM t ht
      have h2 : ‖u t - s' t‖ ≤ ε := by
        have := ContinuousMap.dist_apply_le_dist (f := uC) (g := b) ⟨t, ht⟩
        rw [Real.dist_eq] at this
        have e : uC ⟨t, ht⟩ - b ⟨t, ht⟩ = u t - s' t := by rw [hs' ⟨t, ht⟩]; rfl
        rw [Real.norm_eq_abs, ← e]
        exact this.trans hdist.le
      exact mul_le_mul h1 h2 (norm_nonneg _) hM0
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc (0 : ℝ) T)
      (f := fun t => u t * (u t - s' t)) (C := M * ε) (by simp) hb'
    have hv : volume.real (Set.Icc (0 : ℝ) T) = T := by simp [Measure.real, hT.le]
    rw [hv] at this
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)
  have hz : ∫ t in Set.Icc (0 : ℝ) T, u t ^ 2 = 0 := by
    refine le_antisymm (le_of_forall_pos_le_add fun ε' hε' => ?_) (integral_nonneg fun t => sq_nonneg _)
    have hpos : 0 < (M + 1) * T := by positivity
    have := key (ε' / ((M + 1) * T)) (by positivity)
    refine this.trans ?_
    rw [zero_add]
    calc M * (ε' / ((M + 1) * T)) * T ≤ (M + 1) * (ε' / ((M + 1) * T)) * T := by gcongr; linarith
      _ = ε' := by field_simp
  have hae := (setIntegral_eq_zero_iff_of_nonneg_ae (μ := volume) (s := Set.Icc (0 : ℝ) T)
    (f := fun t => u t ^ 2) (Filter.Eventually.of_forall fun t => sq_nonneg (u t))
    (hu.pow 2).integrableOn_Icc).1 hz
  have heq := Measure.eqOn_Icc_of_ae_eq volume hT.ne (f := fun t => u t ^ 2) (g := fun _ => (0 : ℝ)) hae
    (hu.pow 2) continuousOn_const
  intro t ht
  exact pow_eq_zero_iff (two_ne_zero) |>.1 (heq ht)

end Unique

section Expand

variable {T : ℝ}

theorem s11p_summand_summable (hT : 0 < T) (b : ℕ → ℝ) (hb : Summable b) (t : ℝ) :
    Summable fun n => s11p_kap n * r2CosBasis T n t * b n := by
  refine Summable.of_norm_bounded (hb.norm.mul_left (Real.sqrt (2 / T))) fun n => ?_
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (s11p_kap_pos n)]
  have h1 := s11p_cos_bound hT n t
  have h2 := s11p_kap_le_one n
  have h3 := s11p_kap_pos n
  calc s11p_kap n * |r2CosBasis T n t| * ‖b n‖ ≤ 1 * Real.sqrt (2 / T) * ‖b n‖ := by
        gcongr
    _ = _ := by ring

/-- **Cosine expansion.** -/
theorem s11p_cos_expand (hT : 0 < T) (g : ℝ → ℝ) (hg : ContinuousOn g (Set.Icc 0 T)) (b : ℕ → ℝ)
    (hb : Summable b)
    (hbn : ∀ n, b n = (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) * ∫ t in Set.Icc (0 : ℝ) T, r2CosBasis T n t * g t) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, HasSum (fun n => s11p_kap n * r2CosBasis T n t * b n) (g t) := by
  set B := Real.sqrt (2 / T) with hB
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  set F : ℕ → ℝ → ℝ := fun n t => s11p_kap n * r2CosBasis T n t * b n with hF
  have hFc : ∀ n, Continuous (F n) := fun n => by
    simp only [hF]
    exact (continuous_const.mul (s11p_cos_continuous T n)).mul continuous_const
  have hFb : ∀ n t, ‖F n t‖ ≤ B * ‖b n‖ := by
    intro n t
    simp only [hF]
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (s11p_kap_pos n)]
    have h1 := s11p_cos_bound hT n t
    have h2 := s11p_kap_le_one n
    have h3 := s11p_kap_pos n
    calc s11p_kap n * |r2CosBasis T n t| * ‖b n‖ ≤ 1 * B * ‖b n‖ := by
          gcongr
      _ = _ := by ring
  set h : ℝ → ℝ := fun t => ∑' n, F n t with hh
  have hhc : Continuous h := continuous_tsum hFc (hb.norm.mul_left B) hFb
  -- orthogonality of `g - h` to the cosines
  have hort : ∀ k : ℕ, ∫ t in Set.Icc (0 : ℝ) T, r2CosBasis T k t * (g t - h t) = 0 := by
    intro k
    have hint1 : IntegrableOn (fun t => r2CosBasis T k t * g t) (Set.Icc 0 T) :=
      ((s11p_cos_continuous T k).continuousOn.mul hg).integrableOn_Icc
    have hint2 : IntegrableOn (fun t => r2CosBasis T k t * h t) (Set.Icc 0 T) :=
      ((s11p_cos_continuous T k).continuousOn.mul hhc.continuousOn).integrableOn_Icc
    have e1 : ∫ t in Set.Icc (0 : ℝ) T, r2CosBasis T k t * (g t - h t) =
        (∫ t in Set.Icc (0 : ℝ) T, r2CosBasis T k t * g t) - ∫ t in Set.Icc (0 : ℝ) T, r2CosBasis T k t * h t := by
      refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)) (integral_sub hint1 hint2)
      simp only; ring
    have e2 : ∫ t in Set.Icc (0 : ℝ) T, r2CosBasis T k t * h t = s11p_kap k * b k := by
      have hFi : ∀ n, Integrable (fun t => r2CosBasis T k t * F n t) (volume.restrict (Set.Icc 0 T)) := fun n =>
        (((s11p_cos_continuous T k).mul (hFc n)).continuousOn).integrableOn_Icc
      have hsum : Summable fun n => ∫ t in Set.Icc (0 : ℝ) T, ‖r2CosBasis T k t * F n t‖ := by
        refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _) (fun n => ?_)
          ((hb.norm.mul_left (B * B * T)))
        have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc (0 : ℝ) T)
          (f := fun t => ‖r2CosBasis T k t * F n t‖) (C := B * (B * ‖b n‖)) (by simp) (fun t ht => by
            rw [norm_norm, norm_mul]
            have h1 := s11p_cos_bound hT k t
            rw [Real.norm_eq_abs]
            exact mul_le_mul h1 (hFb n t) (norm_nonneg _) hB0)
        have hv : volume.real (Set.Icc (0 : ℝ) T) = T := by simp [Measure.real, hT.le]
        rw [hv, Real.norm_of_nonneg (integral_nonneg fun t => norm_nonneg _)] at this
        calc _ ≤ B * (B * ‖b n‖) * T := this
          _ = _ := by ring
      have := integral_tsum_of_summable_integral_norm hFi hsum
      have e3 : ∫ t in Set.Icc (0 : ℝ) T, r2CosBasis T k t * h t =
          ∫ t in Set.Icc (0 : ℝ) T, ∑' n, r2CosBasis T k t * F n t := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        simp only [hh]
        rw [tsum_mul_left]
      rw [e3, ← this]
      rw [tsum_eq_single k]
      · simp only [hF]
        have : ∀ t, r2CosBasis T k t * (s11p_kap k * r2CosBasis T k t * b k) =
            s11p_kap k * b k * (r2CosBasis T k t * r2CosBasis T k t) := fun t => by ring
        simp_rw [this]
        rw [integral_const_mul, s11p_cos_orth hT k k]
        simp
      · intro n hn
        simp only [hF]
        have : ∀ t, r2CosBasis T k t * (s11p_kap n * r2CosBasis T n t * b n) =
            s11p_kap n * b n * (r2CosBasis T k t * r2CosBasis T n t) := fun t => by ring
        simp_rw [this]
        rw [integral_const_mul, s11p_cos_orth hT k n, if_neg (Ne.symm hn)]
        simp
    have e4 : ∫ t in Set.Icc (0 : ℝ) T, r2CosBasis T k t * g t = s11p_kap k * b k := by
      rw [hbn k, ← mul_assoc, mul_comm (s11p_kap k), mul_assoc, ← mul_assoc]
      rw [mul_comm ((1 + (k : ℝ) ^ 2) ^ ((3 : ℝ) / 8)), s11p_kap_mul, one_mul]
    rw [e1, e2, e4, sub_self]
  have hz := s11p_cos_unique hT (fun t => g t - h t) (hg.sub hhc.continuousOn) hort
  intro t ht
  have := hz t ht
  have hs : Summable fun n => F n t := s11p_summand_summable hT b hb t
  have e : h t = g t := by linarith
  rw [← e]
  exact hs.hasSum

end Expand

end HRS.Whole
