import HRS.MS.MainRdFieldAux4
import HRS.Prob.HilbertMartingale

/-!
# S.A.6, packet P5a: covariance forms of a kernel family and trace-norm duality (abstract)

For a bounded measurable family `k_j : ℝ^d → H` (`Sa6KBdd`), the bilinear form
`(x,y) ↦ ∫ Σ_j ⟨k_j(z),x⟩⟨k_j(z),y⟩ dν(z)` is a continuous symmetric nonnegative trace-class form `sa6Form k hk ν`.

`sa6_traceNorm_le`: if `|⟨h, μ₁ - μ₂⟩| ≤ A 𝒩(h)` for every `h` of finite `𝒩` and the `𝒩`-norm of
`h_B = Σ_j ⟨B k_j, k_j⟩` is `≤ C_k` for every self-adjoint contraction `B` (S.A.20(4)), then
`‖c(Form(μ₁) - Form(μ₂))‖_{𝔖₁} ≤ |c| A C_k` (trace-norm duality: `Σ_i |C(e_i,f_i)| = Tr(B C)` with the contraction
`B = Σ ε_i f_i ⊗ e_i`, symmetrised).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdField

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

section Forms

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

def sa6Fn (k : Fin d → Euc d → H) (x y : H) (z : Euc d) : ℝ :=
  ∑ j, inner ℝ (k j z) x * inner ℝ (k j z) y

structure Sa6KBdd (k : Fin d → Euc d → H) (K : ℝ) : Prop where
  nonneg : 0 ≤ K
  bdd : ∀ j z, ‖k j z‖ ≤ K
  meas : ∀ j, Measurable (k j)

variable {k : Fin d → Euc d → H} {K : ℝ}

lemma sa6Fn_abs_le (hk : Sa6KBdd k K) (x y : H) (z : Euc d) :
    |sa6Fn k x y z| ≤ d * K ^ 2 * (‖x‖ * ‖y‖) := by
  unfold sa6Fn
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j, |inner ℝ (k j z) x * inner ℝ (k j z) y| ≤ ∑ _j : Fin d, K ^ 2 * (‖x‖ * ‖y‖) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        have h1 : |inner ℝ (k j z) x| ≤ K * ‖x‖ :=
          (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hk.bdd j z) (norm_nonneg _))
        have h2 : |inner ℝ (k j z) y| ≤ K * ‖y‖ :=
          (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hk.bdd j z) (norm_nonneg _))
        calc |inner ℝ (k j z) x| * |inner ℝ (k j z) y| ≤ (K * ‖x‖) * (K * ‖y‖) :=
              mul_le_mul h1 h2 (abs_nonneg _) (by have := hk.nonneg; positivity)
          _ = K ^ 2 * (‖x‖ * ‖y‖) := by ring
    _ = d * K ^ 2 * (‖x‖ * ‖y‖) := by simp [mul_assoc]

lemma sa6Fn_meas (hk : Sa6KBdd k K) (x y : H) : Measurable (sa6Fn k x y) :=
  Finset.measurable_sum _ fun j _ =>
    ((hk.meas j).inner measurable_const).mul ((hk.meas j).inner measurable_const)

lemma sa6Fn_integrable (hk : Sa6KBdd k K) (ν : Measure (Euc d)) [IsFiniteMeasure ν] (x y : H) :
    Integrable (sa6Fn k x y) ν :=
  Integrable.of_bound (sa6Fn_meas hk x y).aestronglyMeasurable (d * K ^ 2 * (‖x‖ * ‖y‖))
    (ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using sa6Fn_abs_le hk x y z)

lemma sa6Fn_add_left (x x' y : H) (z : Euc d) :
    sa6Fn k (x + x') y z = sa6Fn k x y z + sa6Fn k x' y z := by
  unfold sa6Fn
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_add_right]; ring

lemma sa6Fn_smul_left (c : ℝ) (x y : H) (z : Euc d) :
    sa6Fn k (c • x) y z = c * sa6Fn k x y z := by
  unfold sa6Fn
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_right]; ring

lemma sa6Fn_comm (x y : H) (z : Euc d) : sa6Fn k x y z = sa6Fn k y x z := by
  unfold sa6Fn
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

lemma sa6Fn_add_right (x y y' : H) (z : Euc d) :
    sa6Fn k x (y + y') z = sa6Fn k x y z + sa6Fn k x y' z := by
  rw [sa6Fn_comm, sa6Fn_add_left, sa6Fn_comm, sa6Fn_comm (x := y')]

lemma sa6Fn_smul_right (c : ℝ) (x y : H) (z : Euc d) :
    sa6Fn k x (c • y) z = c * sa6Fn k x y z := by
  rw [sa6Fn_comm, sa6Fn_smul_left, sa6Fn_comm]

lemma sa6Fn_nonneg (x : H) (z : Euc d) : 0 ≤ sa6Fn k x x z :=
  Finset.sum_nonneg fun j _ => by rw [← sq]; positivity

/-- The covariance form of a kernel family against a finite measure. -/
def sa6Form (k : Fin d → Euc d → H) (hk : Sa6KBdd k K) (ν : Measure (Euc d)) [IsFiniteMeasure ν] :
    H →L[ℝ] H →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun x y => ∫ z, sa6Fn k x y z ∂ν)
      (fun x x' y => by
        simp only [sa6Fn_add_left]
        exact integral_add (sa6Fn_integrable hk ν x y) (sa6Fn_integrable hk ν x' y))
      (fun c x y => by
        simp only [sa6Fn_smul_left, smul_eq_mul]
        exact integral_const_mul c _)
      (fun x y y' => by
        simp only [sa6Fn_add_right]
        exact integral_add (sa6Fn_integrable hk ν x y) (sa6Fn_integrable hk ν x y'))
      (fun c x y => by
        simp only [sa6Fn_smul_right, smul_eq_mul]
        exact integral_const_mul c _))
    (d * K ^ 2 * ν.real Set.univ) (fun x y => by
      show ‖∫ z, sa6Fn k x y z ∂ν‖ ≤ _
      have := norm_integral_le_of_norm_le_const (μ := ν) (f := sa6Fn k x y)
        (C := d * K ^ 2 * (‖x‖ * ‖y‖))
        (ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using sa6Fn_abs_le hk x y z)
      refine this.trans (le_of_eq ?_)
      ring)

lemma sa6Form_apply (hk : Sa6KBdd k K) (ν : Measure (Euc d)) [IsFiniteMeasure ν] (x y : H) :
    sa6Form k hk ν x y = ∫ z, sa6Fn k x y z ∂ν := rfl

lemma sa6Form_isTraceClass (hk : Sa6KBdd k K) (ν : Measure (Euc d)) [IsFiniteMeasure ν] :
    IsTraceClassCov (sa6Form k hk ν) := by
  refine ⟨fun x y => ?_, fun x => ?_, ?_⟩
  · rw [sa6Form_apply, sa6Form_apply]
    exact integral_congr_ae (ae_of_all _ fun z => sa6Fn_comm x y z)
  · rw [sa6Form_apply]
    exact integral_nonneg fun z => sa6Fn_nonneg x z
  · obtain ⟨ι, -, b, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := H)
    refine ⟨ι, b, ?_⟩
    refine summable_of_sum_le (c := d * K ^ 2 * ν.real Set.univ)
      (fun i => by rw [sa6Form_apply]; exact integral_nonneg fun z => sa6Fn_nonneg _ z) fun u => ?_
    simp only [sa6Form_apply]
    rw [← integral_finset_sum _ fun i _ => sa6Fn_integrable hk ν (b i) (b i)]
    have hb := integral_mono (f := fun z => ∑ i ∈ u, sa6Fn k (b i) (b i) z)
      (g := fun _ => (d * K ^ 2 : ℝ))
      (integrable_finset_sum _ fun i _ => sa6Fn_integrable hk ν (b i) (b i))
      (integrable_const _) (fun z => ?_)
    · simpa [mul_comm] using hb
    · beta_reduce
      unfold sa6Fn
      rw [Finset.sum_comm]
      calc ∑ j : Fin d, ∑ i ∈ u, inner ℝ (k j z) (b i) * inner ℝ (k j z) (b i)
          ≤ ∑ _j : Fin d, K ^ 2 := by
            refine Finset.sum_le_sum fun j _ => ?_
            have h1 := b.orthonormal.sum_inner_products_le (k j z) (s := u)
            have h2 : ∑ i ∈ u, inner ℝ (k j z) (b i) * inner ℝ (k j z) (b i) =
                ∑ i ∈ u, ‖inner ℝ (b i) (k j z)‖ ^ 2 := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Real.norm_eq_abs, sq_abs, real_inner_comm, sq]
            rw [h2]
            refine h1.trans ?_
            exact pow_le_pow_left₀ (norm_nonneg _) (hk.bdd j z) 2
        _ = d * K ^ 2 := by simp

/-- Trace-norm duality for the discrepancy of two covariance forms. -/
theorem sa6_traceNorm_le (hk : Sa6KBdd k K) (μ₁ μ₂ : Measure (Euc d)) [IsFiniteMeasure μ₁]
    [IsFiniteMeasure μ₂] (c : ℝ) (χ : Euc d → ℝ) {Ck A : ℝ} (hA : 0 ≤ A) (hCk : 0 ≤ Ck)
    (hcN : ∀ B : H →L[ℝ] H, (∀ u v, inner ℝ (B u) v = inner ℝ u (B v)) → ‖B‖ ≤ 1 →
      cNormE χ (fun z => ∑ j, inner ℝ (B (k j z)) (k j z)) ≤ ENNReal.ofReal Ck)
    (htc : ∀ h : Euc d → ℝ, cNormE χ h < ⊤ → |HRS.Whole.pair μ₁ h - HRS.Whole.pair μ₂ h| ≤ A * (cNormE χ h).toReal) :
    traceNormForm (c • (sa6Form k hk μ₁ - sa6Form k hk μ₂)) ≤ |c| * A * Ck := by
  classical
  refine Real.iSup_le (fun p => ?_) (by positivity)
  obtain ⟨⟨n, e, f⟩, he, hf⟩ := p
  have he' : Orthonormal ℝ e := he
  have hf' : Orthonormal ℝ f := hf
  show ∑ i : Fin n, |(c • (sa6Form k hk μ₁ - sa6Form k hk μ₂)) (e i) (f i)| ≤ |c| * A * Ck
  set C : H →L[ℝ] H →L[ℝ] ℝ := c • (sa6Form k hk μ₁ - sa6Form k hk μ₂) with hC
  have hCapp : ∀ x y, C x y = c * ((∫ z, sa6Fn k x y z ∂μ₁) - ∫ z, sa6Fn k x y z ∂μ₂) := by
    intro x y; simp [hC, sa6Form_apply]
  let ε : Fin n → ℝ := fun i => if 0 ≤ C (e i) (f i) then 1 else -1
  have hε : ∀ i, |C (e i) (f i)| = ε i * C (e i) (f i) := by
    intro i
    by_cases h : 0 ≤ C (e i) (f i)
    · simp [ε, h, abs_of_nonneg h]
    · simp [ε, h, abs_of_neg (not_le.1 h)]
  have hε2 : ∀ i, ε i ^ 2 ≤ 1 := by
    intro i; by_cases h : 0 ≤ C (e i) (f i) <;> simp [ε, h]
  let Bop : H →L[ℝ] H := ∑ i, ε i • (innerSL ℝ (e i)).smulRight (f i)
  have hBapp : ∀ u, Bop u = ∑ i, (ε i * inner ℝ (e i) u) • f i := by
    intro u
    simp [Bop, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul]
  have hBnorm : ‖Bop‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => ?_
    have h1 : ‖Bop u‖ ^ 2 = ∑ i, (ε i * inner ℝ (e i) u) ^ 2 := by
      have h2 := fun i : Fin n => hf'.inner_right_sum (fun j => ε j * inner ℝ (e j) u)
        (s := Finset.univ) (Finset.mem_univ i)
      calc ‖Bop u‖ ^ 2 = inner ℝ (Bop u) (Bop u) := (real_inner_self_eq_norm_sq _).symm
        _ = ∑ i, (ε i * inner ℝ (e i) u) * inner ℝ (f i) (Bop u) := by
            have hsi := sum_inner (𝕜 := ℝ) Finset.univ (fun i => (ε i * inner ℝ (e i) u) • f i) (Bop u)
            rw [← hBapp u] at hsi
            rw [hsi]
            simp only [inner_smul_left, conj_trivial]
        _ = _ := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hBapp u, h2 i]; ring
    have h3 : ∑ i, (ε i * inner ℝ (e i) u) ^ 2 ≤ ‖u‖ ^ 2 := by
      calc ∑ i, (ε i * inner ℝ (e i) u) ^ 2 ≤ ∑ i, ‖inner ℝ (e i) u‖ ^ 2 := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [mul_pow, Real.norm_eq_abs, sq_abs]
            nlinarith [hε2 i, sq_nonneg (inner ℝ (e i) u)]
        _ ≤ ‖u‖ ^ 2 := he'.sum_inner_products_le u
    have h4 : ‖Bop u‖ ^ 2 ≤ ‖u‖ ^ 2 := h1 ▸ h3
    have h5 : ‖Bop u‖ ≤ ‖u‖ := by
      by_contra h
      push Not at h
      nlinarith [norm_nonneg u, norm_nonneg (Bop u)]
    simpa using h5
  let Bs : H →L[ℝ] H := (1 / 2 : ℝ) • (Bop + ContinuousLinearMap.adjoint Bop)
  have hBs_sym : ∀ u v, inner ℝ (Bs u) v = inner ℝ u (Bs v) := by
    intro u v
    simp only [Bs, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, inner_smul_left,
      inner_smul_right, inner_add_left, inner_add_right, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right]
    simp only [conj_trivial]
    ring
  have hBs_norm : ‖Bs‖ ≤ 1 := by
    have h1 : ‖ContinuousLinearMap.adjoint Bop‖ = ‖Bop‖ :=
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H)).norm_map Bop
    calc ‖Bs‖ ≤ ‖(1 / 2 : ℝ)‖ * ‖Bop + ContinuousLinearMap.adjoint Bop‖ :=
          norm_smul_le (1 / 2 : ℝ) (Bop + ContinuousLinearMap.adjoint Bop)
      _ ≤ (1 / 2) * (‖Bop‖ + ‖ContinuousLinearMap.adjoint Bop‖) := by
          rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
      _ ≤ 1 := by rw [h1]; linarith
  have hquad : ∀ u : H, inner ℝ (Bs u) u = ∑ i, ε i * (inner ℝ (e i) u * inner ℝ (f i) u) := by
    intro u
    have h1 : inner ℝ (Bop u) u = ∑ i, ε i * (inner ℝ (e i) u * inner ℝ (f i) u) := by
      rw [hBapp u, sum_inner]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [inner_smul_left]; simp; ring
    have h2 : inner ℝ (ContinuousLinearMap.adjoint Bop u) u = inner ℝ (Bop u) u := by
      rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
    simp only [Bs, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, inner_smul_left,
      inner_add_left, h2, h1]
    simp only [conj_trivial]
    ring
  set hB : Euc d → ℝ := fun z => ∑ j, inner ℝ (Bs (k j z)) (k j z) with hBdef
  have hBeq : ∀ z, hB z = ∑ i, ε i * sa6Fn k (e i) (f i) z := by
    intro z
    simp only [hBdef, hquad, sa6Fn]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_comm (e i), real_inner_comm (f i)]
  have hpair : ∀ (μ : Measure (Euc d)) [IsFiniteMeasure μ],
      HRS.Whole.pair μ hB = ∑ i, ε i * ∫ z, sa6Fn k (e i) (f i) z ∂μ := by
    intro μ _
    unfold HRS.Whole.pair
    simp_rw [hBeq]
    rw [integral_finset_sum _ fun i _ => (sa6Fn_integrable hk μ (e i) (f i)).const_mul _]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  have hsum : ∑ i, |C (e i) (f i)| = c * (HRS.Whole.pair μ₁ hB - HRS.Whole.pair μ₂ hB) := by
    rw [hpair μ₁, hpair μ₂, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hε i, hCapp]; ring
  have hcn := hcN Bs hBs_sym hBs_norm
  have hlt : cNormE χ hB < ⊤ := lt_of_le_of_lt hcn ENNReal.ofReal_lt_top
  have hn : (cNormE χ hB).toReal ≤ Ck := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcn
    rwa [ENNReal.toReal_ofReal hCk] at this
  calc ∑ i, |C (e i) (f i)| = c * (HRS.Whole.pair μ₁ hB - HRS.Whole.pair μ₂ hB) := hsum
    _ ≤ |c * (HRS.Whole.pair μ₁ hB - HRS.Whole.pair μ₂ hB)| := le_abs_self _
    _ = |c| * |HRS.Whole.pair μ₁ hB - HRS.Whole.pair μ₂ hB| := abs_mul _ _
    _ ≤ |c| * (A * (cNormE χ hB).toReal) :=
        mul_le_mul_of_nonneg_left (htc hB hlt) (abs_nonneg _)
    _ ≤ |c| * (A * Ck) := by gcongr
    _ = |c| * A * Ck := by ring

lemma sa6_traceClass_smul {C : H →L[ℝ] H →L[ℝ] ℝ} (hC : IsTraceClassCov C) {c : ℝ} (hc : 0 ≤ c) :
    IsTraceClassCov (c • C) := by
  refine ⟨fun x y => ?_, fun x => ?_, ?_⟩
  · simp [hC.symm x y]
  · simpa using mul_nonneg hc (hC.nonneg x)
  · obtain ⟨ι, b, hs⟩ := hC.trace
    exact ⟨ι, b, by simpa using hs.mul_left c⟩

/-- Trace norm of one covariance form. -/
theorem sa6_traceNorm_single (hk : Sa6KBdd k K) (ν : Measure (Euc d)) [IsFiniteMeasure ν] (c : ℝ) :
    traceNormForm (c • sa6Form k hk ν) ≤ |c| * (d * K ^ 2 * ν.real Set.univ) := by
  have hK := hk.nonneg
  refine Real.iSup_le (fun p => ?_) (by positivity)
  obtain ⟨⟨n, e, f⟩, he, hf⟩ := p
  have he' : Orthonormal ℝ e := he
  have hf' : Orthonormal ℝ f := hf
  show ∑ i : Fin n, |(c • sa6Form k hk ν) (e i) (f i)| ≤ _
  have hpt : ∀ z, ∑ i, |sa6Fn k (e i) (f i) z| ≤ d * K ^ 2 := by
    intro z
    calc ∑ i, |sa6Fn k (e i) (f i) z|
        ≤ ∑ i, ∑ j, |inner ℝ (k j z) (e i)| * |inner ℝ (k j z) (f i)| := by
          refine Finset.sum_le_sum fun i _ => ?_
          unfold sa6Fn
          refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
          exact abs_mul _ _
      _ = ∑ j, ∑ i, |inner ℝ (k j z) (e i)| * |inner ℝ (k j z) (f i)| := Finset.sum_comm
      _ ≤ ∑ _j : Fin d, K ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          have h1 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => |inner ℝ (k j z) (e i)|)
            (fun i => |inner ℝ (k j z) (f i)|)
          have hb : ∀ (v : Fin n → H), Orthonormal ℝ v →
              ∑ i, |inner ℝ (k j z) (v i)| ^ 2 ≤ ‖k j z‖ ^ 2 := fun v hv => by
            have := hv.sum_inner_products_le (k j z) (s := Finset.univ)
            refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)) this
            rw [Real.norm_eq_abs, real_inner_comm]
          have h2 := Real.sqrt_le_sqrt (hb e he')
          have h3 := Real.sqrt_le_sqrt (hb f hf')
          rw [Real.sqrt_sq (norm_nonneg _)] at h2 h3
          refine h1.trans ?_
          calc √(∑ i, |inner ℝ (k j z) (e i)| ^ 2) * √(∑ i, |inner ℝ (k j z) (f i)| ^ 2)
              ≤ ‖k j z‖ * ‖k j z‖ := mul_le_mul h2 h3 (Real.sqrt_nonneg _) (norm_nonneg _)
            _ ≤ K * K := mul_le_mul (hk.bdd j z) (hk.bdd j z) (norm_nonneg _) hK
            _ = K ^ 2 := by ring
      _ = d * K ^ 2 := by simp
  calc ∑ i, |(c • sa6Form k hk ν) (e i) (f i)|
      = |c| * ∑ i, |∫ z, sa6Fn k (e i) (f i) z ∂ν| := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [sa6Form_apply, abs_mul]
    _ ≤ |c| * ∑ i, ∫ z, |sa6Fn k (e i) (f i) z| ∂ν := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (abs_nonneg _)
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := ν) (sa6Fn k (e i) (f i))
    _ = |c| * ∫ z, ∑ i, |sa6Fn k (e i) (f i) z| ∂ν := by
        rw [integral_finset_sum _ fun i _ => (sa6Fn_integrable hk ν _ _).abs]
    _ ≤ |c| * ∫ _z, (d * K ^ 2 : ℝ) ∂ν := by
        refine mul_le_mul_of_nonneg_left (integral_mono
          (integrable_finset_sum _ fun i _ => (sa6Fn_integrable hk ν _ _).abs)
          (integrable_const _) hpt) (abs_nonneg _)
    _ = |c| * (d * K ^ 2 * ν.real Set.univ) := by
        rw [integral_const, smul_eq_mul]; ring

end Forms

end HRS.MS.MainRdField
