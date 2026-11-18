import HRS.Main.MixEnt5

/-!
# MIXENT 6: moments of the mixture density (lemma M5, first half)

TeX L6952-6962: "Every fixed moment of `r_N` is uniformly bounded, because each product factor is
`1 + O(N^{-1/2})` with mean one."  We prove, for `1 ≤ r ≤ 2` and `|a₀ b| ≤ √N/2`,
`∫ R^r dπ ≤ exp(r² a₀² ∫ b² dμ)` for the density `R = (r₊ + r₋)/2` of the mixture preparation
against `π = μ^{⊗N}`, uniformly in `N`.
-/

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

/-- Second-order bound `(1+u)^r ≤ 1 + r u + r² u²` for `|u| ≤ 1/2`, `0 ≤ r ≤ 2`. -/
theorem mx_rpow_one_add_le {u r : ℝ} (hu : |u| ≤ 1 / 2) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) :
    (1 + u) ^ r ≤ 1 + r * u + r ^ 2 * u ^ 2 := by
  have hpos : 0 < 1 + u := by have := abs_le.1 hu; linarith [this.1]
  have h1 : (1 + u) ^ r = Real.exp (r * Real.log (1 + u)) := by
    rw [Real.rpow_def_of_pos hpos]; ring_nf
  have h2 : r * Real.log (1 + u) ≤ r * u := by
    have := Real.log_le_sub_one_of_pos hpos
    exact mul_le_mul_of_nonneg_left (by linarith) hr0
  have h3 : |r * u| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hr0]
    nlinarith [abs_nonneg u]
  have h4 := Real.abs_exp_sub_one_sub_id_le h3
  rw [h1]
  calc Real.exp (r * Real.log (1 + u)) ≤ Real.exp (r * u) := Real.exp_le_exp.2 h2
    _ ≤ 1 + r * u + (r * u) ^ 2 := by linarith [(abs_le.1 h4).2]
    _ = 1 + r * u + r ^ 2 * u ^ 2 := by ring

/-- One-coordinate moment: for `μ(b) = 0`, `|t b| ≤ 1/2`, `0 ≤ r ≤ 2`:
`∫ (1 + t b)^r dμ ≤ 1 + r² t² ∫ b² dμ`. -/
theorem mx_moment_one {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {b : Torus d → ℝ}
    (hb : Measurable b) {M : ℝ} (hM : ∀ x, |b x| ≤ M) (hb0 : ∫ x, b x ∂μ = 0) (t r : ℝ)
    (htb : ∀ x, |t * b x| ≤ 1 / 2) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) :
    ∫ x, (1 + t * b x) ^ r ∂μ ≤ 1 + r ^ 2 * t ^ 2 * ∫ x, b x ^ 2 ∂μ := by
  have hbi : Integrable b μ :=
    Integrable.of_bound hb.aestronglyMeasurable M (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hM x)
  have hb2i : Integrable (fun x => b x ^ 2) μ :=
    Integrable.of_bound (hb.pow_const 2).aestronglyMeasurable (M ^ 2) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hM x) 2)
  have hrhs : Integrable (fun x => 1 + r * t * b x + r ^ 2 * t ^ 2 * b x ^ 2) μ :=
    ((integrable_const (1 : ℝ)).add (hbi.const_mul (r * t))).add (hb2i.const_mul (r ^ 2 * t ^ 2))
  have hmono : ∫ x, (1 + t * b x) ^ r ∂μ ≤ ∫ x, (1 + r * t * b x + r ^ 2 * t ^ 2 * b x ^ 2) ∂μ := by
    refine integral_mono_of_nonneg (ae_of_all _ fun x => ?_) hrhs (ae_of_all _ fun x => ?_)
    · have hpos : 0 < 1 + t * b x := by have := abs_le.1 (htb x); linarith [this.1]
      exact (Real.rpow_pos_of_pos hpos r).le
    · have := mx_rpow_one_add_le (htb x) hr0 hr2
      calc (1 + t * b x) ^ r ≤ 1 + r * (t * b x) + r ^ 2 * (t * b x) ^ 2 := this
        _ = _ := by ring
  refine hmono.trans (le_of_eq ?_)
  have i1 : Integrable (fun x => 1 + r * t * b x) μ :=
    (integrable_const (1 : ℝ)).add (hbi.const_mul (r * t))
  have h1 := integral_add (μ := μ) (f := fun x => 1 + r * t * b x)
    (g := fun x => r ^ 2 * t ^ 2 * b x ^ 2) i1 (hb2i.const_mul _)
  have h2 := integral_add (μ := μ) (f := fun _ => (1 : ℝ)) (g := fun x => r * t * b x)
    (integrable_const (1 : ℝ)) (hbi.const_mul (r * t))
  beta_reduce at h1 h2
  rw [h1, h2, integral_const_mul, integral_const_mul, hb0]
  simp

/-- Moment of a product density: for `μ(b) = 0`, `|t b| ≤ 1/2`, `0 ≤ r ≤ 2`,
`∫ (∏ᵢ (1 + t b(xᵢ)))^r dμ^{⊗N} ≤ exp(N r² t² ∫ b² dμ)` (integrable). -/
theorem mx_moment_prod {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {b : Torus d → ℝ}
    (hb : Measurable b) {M : ℝ} (hM : ∀ x, |b x| ≤ M) (hb0 : ∫ x, b x ∂μ = 0) (t r : ℝ)
    (htb : ∀ x, |t * b x| ≤ 1 / 2) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (N : ℕ) :
    Integrable (fun X : Config d N => (∏ i, (1 + t * b (X i))) ^ r)
        (Measure.pi fun _ : Fin N => μ) ∧
      ∫ X : Config d N, (∏ i, (1 + t * b (X i))) ^ r ∂(Measure.pi fun _ : Fin N => μ) ≤
        Real.exp (N * (r ^ 2 * t ^ 2 * ∫ x, b x ^ 2 ∂μ)) := by
  have hpos : ∀ x, 0 < 1 + t * b x := fun x => by
    have := abs_le.1 (htb x); linarith [this.1]
  have hfm : Measurable fun x => (1 + t * b x) ^ r := by fun_prop
  have hfi : Integrable (fun x => (1 + t * b x) ^ r) μ := by
    refine Integrable.of_bound hfm.aestronglyMeasurable (3 / 2 + 1) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (hpos x) r)]
    have h1 : 1 + t * b x ≤ 3 / 2 := by have := abs_le.1 (htb x); linarith [this.2]
    calc (1 + t * b x) ^ r ≤ (3 / 2 : ℝ) ^ r :=
          Real.rpow_le_rpow (hpos x).le h1 hr0
      _ ≤ (3 / 2 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hr2
      _ ≤ 3 / 2 + 1 := by norm_num [Real.rpow_two]
  have hprod : ∀ X : Config d N, (∏ i, (1 + t * b (X i))) ^ r = ∏ i, (1 + t * b (X i)) ^ r :=
    fun X => (Real.finset_prod_rpow Finset.univ _ (fun i _ => (hpos (X i)).le) r).symm
  simp_rw [hprod]
  refine ⟨Integrable.fintype_prod (μ := fun _ : Fin N => μ) (f := fun _ => fun x => (1 + t * b x) ^ r)
    (fun _ => hfi), ?_⟩
  rw [integral_fintype_prod_eq_pow (fun x => (1 + t * b x) ^ r)]
  simp only [Fintype.card_fin]
  have h1 := mx_moment_one hb hM hb0 t r htb hr0 hr2
  set x : ℝ := r ^ 2 * t ^ 2 * ∫ x, b x ^ 2 ∂μ with hx
  have hx0 : 0 ≤ x := by
    have : 0 ≤ ∫ x, b x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    positivity
  have h0 : 0 ≤ ∫ y, (1 + t * b y) ^ r ∂μ := integral_nonneg fun y =>
    (Real.rpow_pos_of_pos (hpos y) r).le
  calc (∫ y, (1 + t * b y) ^ r ∂μ) ^ N ≤ (1 + x) ^ N := pow_le_pow_left₀ h0 h1 N
    _ ≤ (Real.exp x) ^ N := pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) N
    _ = Real.exp (N * x) := by rw [← Real.exp_nat_mul]

/-- **M5 (moment of the mixture density)**, TeX L6958-6960 ("every fixed moment of `r_N` is uniformly
bounded"): for `1 ≤ r ≤ 2`, `μ(b) = 0`, `|a₀ b| ≤ √N/2`,
`∫ R^r dμ^{⊗N} ≤ exp(r² a₀² ∫ b² dμ)`, uniformly in `N ≥ 1`. -/
theorem mx_lintegral_R_rpow_le (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    {b : Torus d → ℝ} (hb : Measurable b) {M : ℝ} (hM : ∀ x, |b x| ≤ M)
    (hb0 : ∫ x, b x ∂μ = 0) (a₀ : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (hB : ∀ x, |a₀ * b x| ≤ Real.sqrt N / 2) {r : ℝ} (hr1 : 1 ≤ r) (hr2 : r ≤ 2) :
    ∫⁻ X : Config d N, ENNReal.ofReal (mxR b a₀ N X) ^ r ∂(Measure.pi fun _ : Fin N => μ) ≤
      ENNReal.ofReal (Real.exp (r ^ 2 * a₀ ^ 2 * ∫ x, b x ^ 2 ∂μ)) := by
  have hN0 : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hr0 : 0 ≤ r := by linarith
  have htb : ∀ x, |(a₀ / Real.sqrt N) * b x| ≤ 1 / 2 := fun x => by
    rw [← mul_div_right_comm, abs_div, abs_of_pos hN0, div_le_iff₀ hN0]
    linarith [hB x]
  have htb' : ∀ x, |(-(a₀ / Real.sqrt N)) * b x| ≤ 1 / 2 := fun x => by
    rw [neg_mul, abs_neg]; exact htb x
  obtain ⟨Ip, Vp⟩ := mx_moment_prod hb hM hb0 (a₀ / Real.sqrt N) r htb hr0 hr2 N
  obtain ⟨Im, Vm⟩ := mx_moment_prod hb hM hb0 (-(a₀ / Real.sqrt N)) r htb' hr0 hr2 N
  have ep : ∀ X : Config d N, mxRp b a₀ N X = ∏ i, (1 + (a₀ / Real.sqrt N) * b (X i)) := fun X => by
    unfold mxRp; refine Finset.prod_congr rfl fun i _ => by ring
  have em : ∀ X : Config d N, mxRm b a₀ N X = ∏ i, (1 + (-(a₀ / Real.sqrt N)) * b (X i)) := fun X => by
    unfold mxRm; refine Finset.prod_congr rfl fun i _ => by ring
  simp_rw [← ep] at Ip Vp
  simp_rw [← em] at Im Vm
  set π : Measure (Config d N) := Measure.pi fun _ : Fin N => μ with hπ
  have hpt : ∀ X : Config d N, mxR b a₀ N X ^ r ≤
      ((mxRp b a₀ N X) ^ r + (mxRm b a₀ N X) ^ r) / 2 := fun X => by
    have h := convexOn_rpow hr1
    have := h.2 (Set.mem_Ici.2 (mx_Rp_pos hN hB X).le) (Set.mem_Ici.2 (mx_Rm_pos hN hB X).le)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at this
    unfold mxR
    calc ((mxRp b a₀ N X + mxRm b a₀ N X) / 2) ^ r
        = (1 / 2 * mxRp b a₀ N X + 1 / 2 * mxRm b a₀ N X) ^ r := by ring_nf
      _ ≤ _ := by linarith
  have hint : Integrable (fun X : Config d N =>
      ((mxRp b a₀ N X) ^ r + (mxRm b a₀ N X) ^ r) / 2) π := (Ip.add Im).div_const 2
  calc ∫⁻ X, ENNReal.ofReal (mxR b a₀ N X) ^ r ∂π
      = ∫⁻ X, ENNReal.ofReal (mxR b a₀ N X ^ r) ∂π := by
        refine lintegral_congr fun X => ?_
        rw [ENNReal.ofReal_rpow_of_nonneg (mx_R_pos hN hB X).le hr0]
    _ ≤ ∫⁻ X, ENNReal.ofReal (((mxRp b a₀ N X) ^ r + (mxRm b a₀ N X) ^ r) / 2) ∂π :=
        lintegral_mono fun X => ENNReal.ofReal_le_ofReal (hpt X)
    _ = ENNReal.ofReal (∫ X, ((mxRp b a₀ N X) ^ r + (mxRm b a₀ N X) ^ r) / 2 ∂π) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun X => by
          have := Real.rpow_nonneg (mx_Rp_pos hN hB X).le r
          have := Real.rpow_nonneg (mx_Rm_pos hN hB X).le r
          positivity)]
    _ ≤ ENNReal.ofReal (Real.exp (r ^ 2 * a₀ ^ 2 * ∫ x, b x ^ 2 ∂μ)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_div, integral_add Ip Im]
        have hNn : (N : ℝ) ≠ 0 := by positivity
        have hsq : (N : ℝ) * (r ^ 2 * (a₀ / Real.sqrt N) ^ 2 * ∫ x, b x ^ 2 ∂μ) =
            r ^ 2 * a₀ ^ 2 * ∫ x, b x ^ 2 ∂μ := by
          rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; field_simp
        have hsq' : (N : ℝ) * (r ^ 2 * (-(a₀ / Real.sqrt N)) ^ 2 * ∫ x, b x ^ 2 ∂μ) =
            r ^ 2 * a₀ ^ 2 * ∫ x, b x ^ 2 ∂μ := by rw [neg_sq]; exact hsq
        rw [hsq] at Vp
        rw [hsq'] at Vm
        linarith

end Main

end HRS
