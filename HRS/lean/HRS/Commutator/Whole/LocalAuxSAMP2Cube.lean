import HRS.Commutator.Whole.Defs
import HRS.Commutator.Whole.YoungAux
import HRS.Commutator.Whole.LocalAuxFC

/-!
# CMX-SAMP (`usample`): cubes, lattice weights, Young-type inequalities

Helpers (all in the namespace `HRS.Commutator.Whole.SAMP2`) for the proof of `usample`
(`[N] (3.usample)`, L441-446, proof L486): the unit cubes `Q_j` partition `ℝ^d`, the product weight
`wt m = ∏_k (1+|m_k|)^{-2}` on `ℤ^d` is summable, the weighted Hölder inequality on a measure
space and on a sum, and the cube estimate for a function represented as `a = K ⋆ a` with a
Schwartz kernel.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole.SAMP2

variable {d : ℕ}

/-! ### The unit cubes -/

lemma cube_eq (j : Fin d → ℤ) :
    cube j = ⋂ i, (fun x : Euc d => x i) ⁻¹' Set.Ico (j i : ℝ) (j i + 1) := by
  ext x
  simp [cube, Set.mem_iInter, Set.mem_Ico]

lemma measurableSet_cube (j : Fin d → ℤ) : MeasurableSet (cube j) := by
  rw [cube_eq]
  refine MeasurableSet.iInter fun i => ?_
  have hm : Measurable (fun x : Euc d => x i) :=
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.measurable
  exact hm measurableSet_Ico

lemma cube_disjoint : Pairwise (Function.onFun Disjoint (cube (d := d))) := by
  intro j k hjk
  rw [Function.onFun, Set.disjoint_left]
  intro x hxj hxk
  apply hjk
  funext i
  have h1 := hxj i
  have h2 := hxk i
  have h3 : (j i : ℝ) < (k i : ℝ) + 1 := lt_of_le_of_lt h1.1 h2.2
  have h4 : (k i : ℝ) < (j i : ℝ) + 1 := lt_of_le_of_lt h2.1 h1.2
  have h5 : j i < k i + 1 := by exact_mod_cast h3
  have h6 : k i < j i + 1 := by exact_mod_cast h4
  omega

lemma iUnion_cube : (⋃ j : Fin d → ℤ, cube j) = (Set.univ : Set (Euc d)) := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨fun i => ⌊x i⌋, fun i => ⟨Int.floor_le _, Int.lt_floor_add_one _⟩⟩

lemma enorm_ofReal_c (r : ℝ) : ‖((r : ℝ) : ℂ)‖ₑ = ‖r‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]

lemma lintegral_eq_tsum_cube (f : Euc d → ℝ≥0∞) :
    ∫⁻ z, f z = ∑' j : Fin d → ℤ, ∫⁻ z in cube j, f z := by
  rw [← lintegral_iUnion (fun j => measurableSet_cube j) cube_disjoint f, iUnion_cube,
    Measure.restrict_univ]

lemma volume_cube (j : Fin d → ℤ) : volume (cube j) = 1 := by
  have h : cube j = (@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹'
      (Set.pi Set.univ fun i => Set.Ico (j i : ℝ) (j i + 1)) := by
    ext x
    simp [cube, Set.mem_pi, Set.mem_Ico]
  have hm : MeasurableSet (Set.pi Set.univ fun i => Set.Ico (j i : ℝ) (j i + 1)) :=
    MeasurableSet.univ_pi fun i => measurableSet_Ico
  rw [h, (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage hm.nullMeasurableSet,
    Real.volume_pi_Ico]
  simp

/-! ### Weights on `ℤ^d` -/

/-- `wt m = ∏_k (1+|m_k|)^{-2}`. -/
def wt (m : Fin d → ℤ) : ℝ := ∏ k, ((1 + |(m k : ℝ)|) ^ 2)⁻¹

lemma wt_nonneg (m : Fin d → ℤ) : 0 ≤ wt m :=
  Finset.prod_nonneg fun k _ => by positivity

lemma summable_int_inv_sq : Summable fun n : ℤ => ((1 + |(n : ℝ)|) ^ 2)⁻¹ := by
  have h : Summable fun n : ℕ => ((1 + |((n : ℤ) : ℝ)|) ^ 2)⁻¹ := by
    have := (summable_nat_add_iff 1).2
      (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))
    refine this.congr fun n => ?_
    simp only [Int.cast_natCast, Nat.abs_cast, Nat.cast_add, Nat.cast_one, one_div]
    rw [add_comm]
  refine Summable.of_nat_of_neg h (h.congr fun n => ?_)
  simp

lemma summable_wt : Summable (wt (d := d)) := by
  have hs : ∀ k : Fin d, Summable fun n : ℤ => |((1 + |(n : ℝ)|) ^ 2)⁻¹| := by
    intro k
    exact summable_int_inv_sq.congr fun n => (abs_of_nonneg (by positivity)).symm
  exact (HRS.KernelAux.pi_hasSum_real d (fun _ n => ((1 + |(n : ℝ)|) ^ 2)⁻¹) hs).summable

/-- Schwartz kernels are bounded by the product weight. -/
lemma schwartz_prod_bound (K : SchwartzMap (Euc d) ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : Euc d, ‖K w‖ ≤ C * ∏ k, ((1 + |w k|) ^ 2)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := cmxFB_decay K (2 * d)
  refine ⟨C, hC0, fun w => ?_⟩
  have hprod : ∏ k : Fin d, (1 + |w k|) ^ 2 ≤ (1 + ‖w‖) ^ (2 * d) := by
    have h1 : ∀ k : Fin d, (1 + |w k|) ^ 2 ≤ (1 + ‖w‖) ^ 2 := by
      intro k
      have : |w k| ≤ ‖w‖ := by simpa using PiLp.norm_apply_le w k
      gcongr
    calc ∏ k : Fin d, (1 + |w k|) ^ 2 ≤ ∏ _k : Fin d, (1 + ‖w‖) ^ 2 :=
          Finset.prod_le_prod₀ (fun k _ => by positivity) (fun k _ => h1 k)
      _ = (1 + ‖w‖) ^ (2 * d) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]
  have hpos : 0 < ∏ k : Fin d, (1 + |w k|) ^ 2 := Finset.prod_pos fun k _ => by positivity
  have hinv : ∏ k : Fin d, ((1 + |w k|) ^ 2)⁻¹ = (∏ k : Fin d, (1 + |w k|) ^ 2)⁻¹ := by
    rw [Finset.prod_inv_distrib]
  rw [hinv, ← div_eq_mul_inv, le_div_iff₀ hpos]
  calc ‖K w‖ * ∏ k : Fin d, (1 + |w k|) ^ 2 ≤ ‖K w‖ * (1 + ‖w‖) ^ (2 * d) :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = (1 + ‖w‖) ^ (2 * d) * ‖K w‖ := by ring
    _ ≤ C := hC w

/-- The coordinatewise separation of two cubes. -/
lemma cube_sep {j l : Fin d → ℤ} {x z : Euc d} (hx : x ∈ cube j) (hz : z ∈ cube l) (k : Fin d) :
    (1 + |((l k - j k : ℤ) : ℝ)|) / 2 ≤ 1 + |z k - x k| := by
  have h1 := hx k
  have h2 := hz k
  have h3 : |((l k - j k : ℤ) : ℝ)| - |z k - x k| ≤ |((l k - j k : ℤ) : ℝ) - (z k - x k)| :=
    abs_sub_abs_le_abs_sub _ _
  have h4 : |((l k - j k : ℤ) : ℝ) - (z k - x k)| ≤ 1 := by
    rw [abs_le]
    push_cast
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have h5 := abs_nonneg (z k - x k)
  have h6 := abs_nonneg (((l k - j k : ℤ) : ℝ))
  linarith

/-- Kernel bound between two cubes. -/
lemma kernel_cube_bound {K : SchwartzMap (Euc d) ℂ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ w : Euc d, ‖K w‖ ≤ C * ∏ k, ((1 + |w k|) ^ 2)⁻¹)
    {j l : Fin d → ℤ} {x z : Euc d} (hx : x ∈ cube j) (hz : z ∈ cube l) :
    ‖K (z - x)‖ ≤ C * 4 ^ d * wt (l - j) := by
  refine (hC (z - x)).trans ?_
  have hprod : ∏ k : Fin d, ((1 + |(z - x) k|) ^ 2)⁻¹ ≤ 4 ^ d * wt (l - j) := by
    have : ∀ k : Fin d, ((1 + |(z - x) k|) ^ 2)⁻¹ ≤ 4 * ((1 + |((l k - j k : ℤ) : ℝ)|) ^ 2)⁻¹ := by
      intro k
      have h : (1 + |((l k - j k : ℤ) : ℝ)|) / 2 ≤ 1 + |(z - x) k| := by
        simpa [PiLp.sub_apply] using cube_sep hx hz k
      have h0 : 0 < (1 + |((l k - j k : ℤ) : ℝ)|) := by positivity
      have h1 : ((1 + |((l k - j k : ℤ) : ℝ)|) / 2) ^ 2 ≤ (1 + |(z - x) k|) ^ 2 := by
        gcongr
      have h2 : ((1 + |(z - x) k|) ^ 2)⁻¹ ≤ (((1 + |((l k - j k : ℤ) : ℝ)|) / 2) ^ 2)⁻¹ :=
        inv_anti₀ (by positivity) h1
      refine h2.trans (le_of_eq ?_)
      field_simp
      norm_num
    calc ∏ k : Fin d, ((1 + |(z - x) k|) ^ 2)⁻¹
        ≤ ∏ k : Fin d, (4 * ((1 + |((l k - j k : ℤ) : ℝ)|) ^ 2)⁻¹) :=
          Finset.prod_le_prod₀ (fun k _ => by positivity) (fun k _ => this k)
      _ = 4 ^ d * wt (l - j) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          rfl
  calc C * ∏ k : Fin d, ((1 + |(z - x) k|) ^ 2)⁻¹ ≤ C * (4 ^ d * wt (l - j)) :=
        mul_le_mul_of_nonneg_left hprod hC0
    _ = C * 4 ^ d * wt (l - j) := by ring

/-! ### Hölder with a weight -/

/-- Weighted Hölder (Jensen): `(∫ w f)^p ≤ (∫ w)^{p-1} ∫ w f^p`. -/
lemma lintegral_weight_rpow_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {p : ℝ}
    (hp : 1 < p) {w f : α → ℝ≥0∞} (hw : AEMeasurable w μ) (hf : AEMeasurable f μ) :
    (∫⁻ x, w x * f x ∂μ) ^ p ≤ (∫⁻ x, w x ∂μ) ^ (p - 1) * ∫⁻ x, w x * f x ^ p ∂μ := by
  have hq : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp
  set q : ℝ := p.conjExponent with hqdef
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := hq.symm.pos
  have hpinv : p⁻¹ + q⁻¹ = 1 := hq.inv_add_inv_eq_one
  have hsplit : ∀ x, w x * f x = (w x ^ q⁻¹) * (w x ^ p⁻¹ * f x) := by
    intro x
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (inv_nonneg.2 hq0.le) (inv_nonneg.2 hp0.le),
      add_comm, hpinv, ENNReal.rpow_one]
  have h1 : ∫⁻ x, w x * f x ∂μ ≤ (∫⁻ x, (w x ^ q⁻¹) ^ q ∂μ) ^ (1 / q) *
      (∫⁻ x, (w x ^ p⁻¹ * f x) ^ p ∂μ) ^ (1 / p) := by
    calc ∫⁻ x, w x * f x ∂μ = ∫⁻ x, (w x ^ q⁻¹) * (w x ^ p⁻¹ * f x) ∂μ := by
          simp_rw [← hsplit]
      _ ≤ _ := by
          refine ENNReal.lintegral_mul_le_Lp_mul_Lq μ hq.symm (hw.pow_const _) ?_
          exact (hw.pow_const _).mul hf
  have e1 : ∀ x, (w x ^ q⁻¹) ^ q = w x := by
    intro x
    rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one]
  have e2 : ∀ x, (w x ^ p⁻¹ * f x) ^ p = w x * f x ^ p := by
    intro x
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, inv_mul_cancel₀ hp0.ne',
      ENNReal.rpow_one]
  simp_rw [e1, e2] at h1
  calc (∫⁻ x, w x * f x ∂μ) ^ p
      ≤ ((∫⁻ x, w x ∂μ) ^ (1 / q) * (∫⁻ x, w x * f x ^ p ∂μ) ^ (1 / p)) ^ p :=
        ENNReal.rpow_le_rpow h1 hp0.le
    _ = (∫⁻ x, w x ∂μ) ^ (p - 1) * ∫⁻ x, w x * f x ^ p ∂μ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        have e3 : 1 / q * p = p - 1 := by
          have : 1 / p + 1 / q = 1 := by simpa [one_div] using hpinv
          field_simp at this ⊢
          linarith
        have e4 : 1 / p * p = 1 := by field_simp
        rw [e3, e4, ENNReal.rpow_one]

/-- The sequence version: `∑_j (∑_ℓ A(ℓ-j) n_ℓ)^p ≤ (∑ A)^p ∑_ℓ n_ℓ^p`. -/
lemma young_seq {ι : Type*} [AddCommGroup ι] {p : ℝ} (hp : 1 ≤ p) (A n : ι → ℝ≥0∞) :
    ∑' j, (∑' ℓ, A (ℓ - j) * n ℓ) ^ p ≤ (∑' m, A m) ^ p * ∑' ℓ, n ℓ ^ p := by
  have hp0 : 0 < p := by linarith
  set S := ∑' m, A m with hSdef
  have hj : ∀ j, (∑' ℓ, A (ℓ - j) * n ℓ) ^ p ≤ S ^ (p - 1) * ∑' ℓ, A (ℓ - j) * n ℓ ^ p := by
    intro j
    have hshift : ∑' ℓ, A (ℓ - j) = S := (Equiv.subRight j).tsum_eq A
    have hfin : ∀ s : Finset ι, ∑ ℓ ∈ s, A (ℓ - j) * n ℓ ≤
        S ^ (1 - p⁻¹) * (∑' ℓ, A (ℓ - j) * n ℓ ^ p) ^ p⁻¹ := by
      intro s
      refine (ENNReal.inner_le_weight_mul_Lp_of_nonneg s hp _ _).trans ?_
      have e1 : ∑ ℓ ∈ s, A (ℓ - j) ≤ S :=
        (ENNReal.sum_le_tsum s).trans (le_of_eq hshift)
      have e2 : ∑ ℓ ∈ s, A (ℓ - j) * n ℓ ^ p ≤ ∑' ℓ, A (ℓ - j) * n ℓ ^ p :=
        ENNReal.sum_le_tsum s
      have hq : 0 ≤ 1 - p⁻¹ := by
        have : p⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp
        linarith
      exact mul_le_mul (ENNReal.rpow_le_rpow e1 hq)
        (ENNReal.rpow_le_rpow e2 (inv_nonneg.2 hp0.le)) zero_le zero_le
    have h1 : ∑' ℓ, A (ℓ - j) * n ℓ ≤ S ^ (1 - p⁻¹) * (∑' ℓ, A (ℓ - j) * n ℓ ^ p) ^ p⁻¹ := by
      rw [ENNReal.tsum_eq_iSup_sum]
      exact iSup_le hfin
    calc (∑' ℓ, A (ℓ - j) * n ℓ) ^ p
        ≤ (S ^ (1 - p⁻¹) * (∑' ℓ, A (ℓ - j) * n ℓ ^ p) ^ p⁻¹) ^ p :=
          ENNReal.rpow_le_rpow h1 hp0.le
      _ = S ^ (p - 1) * ∑' ℓ, A (ℓ - j) * n ℓ ^ p := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
          have e1 : (1 - p⁻¹) * p = p - 1 := by field_simp
          have e2 : p⁻¹ * p = 1 := by field_simp
          rw [e1, e2, ENNReal.rpow_one]
  calc ∑' j, (∑' ℓ, A (ℓ - j) * n ℓ) ^ p
      ≤ ∑' j, S ^ (p - 1) * ∑' ℓ, A (ℓ - j) * n ℓ ^ p := ENNReal.tsum_le_tsum hj
    _ = S ^ (p - 1) * ∑' j, ∑' ℓ, A (ℓ - j) * n ℓ ^ p := by rw [ENNReal.tsum_mul_left]
    _ = S ^ (p - 1) * ∑' ℓ, ∑' j, A (ℓ - j) * n ℓ ^ p := by rw [ENNReal.tsum_comm]
    _ = S ^ (p - 1) * ∑' ℓ, S * n ℓ ^ p := by
        congr 1
        refine tsum_congr fun ℓ => ?_
        rw [ENNReal.tsum_mul_right]
        congr 1
        exact (Equiv.subLeft ℓ).tsum_eq A
    _ = S ^ p * ∑' ℓ, n ℓ ^ p := by
        rw [ENNReal.tsum_mul_left, ← mul_assoc]
        congr 1
        have hp1 : 0 ≤ p - 1 := by linarith
        calc S ^ (p - 1) * S = S ^ (p - 1) * S ^ (1 : ℝ) := by rw [ENNReal.rpow_one]
          _ = S ^ (p - 1 + 1) := (ENNReal.rpow_add_of_nonneg _ _ hp1 zero_le_one).symm
          _ = S ^ p := by congr 1; ring

/-! ### The cube estimate for `a = K ⋆ a` -/

/-- Pointwise bound for `x ∈ Q_j` of a function with `a = K ⋆ a`. -/
lemma pt_cube_le {K : SchwartzMap (Euc d) ℂ} {A : (Fin d → ℤ) → ℝ≥0∞}
    (hA : ∀ {j l : Fin d → ℤ} {x z : Euc d}, x ∈ cube j → z ∈ cube l → ‖K (z - x)‖ₑ ≤ A (l - j))
    {a : Euc d → ℂ} (hrep : ∀ y, a y = ∫ t, K t * a (y + t))
    {Φ : Euc d → ℝ≥0∞} (hΦ : Measurable Φ) (hΦa : ∀ z, ‖a z‖ₑ ≤ Φ z)
    {j : Fin d → ℤ} {x : Euc d} (hx : x ∈ cube j) :
    ‖a x‖ₑ ≤ ∑' l, A (l - j) * ∫⁻ z in cube l, Φ z := by
  have h1 : ‖a x‖ₑ ≤ ∫⁻ t, ‖K t‖ₑ * ‖a (x + t)‖ₑ := by
    rw [hrep x]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    simp_rw [enorm_mul]
  have h2 : ∫⁻ t, ‖K t‖ₑ * ‖a (x + t)‖ₑ = ∫⁻ z, ‖K (z - x)‖ₑ * ‖a z‖ₑ := by
    rw [← lintegral_add_left_eq_self (fun z => ‖K (z - x)‖ₑ * ‖a z‖ₑ) x]
    simp
  have h3 : ∫⁻ z, ‖K (z - x)‖ₑ * ‖a z‖ₑ ≤ ∫⁻ z, ‖K (z - x)‖ₑ * Φ z :=
    lintegral_mono fun z => by gcongr; exact hΦa z
  have h4 : ∀ l, ∫⁻ z in cube l, ‖K (z - x)‖ₑ * Φ z ≤ A (l - j) * ∫⁻ z in cube l, Φ z := by
    intro l
    calc ∫⁻ z in cube l, ‖K (z - x)‖ₑ * Φ z ≤ ∫⁻ z in cube l, A (l - j) * Φ z :=
          setLIntegral_mono' (measurableSet_cube l) fun z hz => by gcongr; exact hA hx hz
      _ = A (l - j) * ∫⁻ z in cube l, Φ z := lintegral_const_mul _ hΦ
  calc ‖a x‖ₑ ≤ ∫⁻ z, ‖K (z - x)‖ₑ * Φ z := h1.trans (h2 ▸ h3)
    _ = ∑' l, ∫⁻ z in cube l, ‖K (z - x)‖ₑ * Φ z := lintegral_eq_tsum_cube _
    _ ≤ ∑' l, A (l - j) * ∫⁻ z in cube l, Φ z := ENNReal.tsum_le_tsum h4

/-- On a unit cube: `∫ Φ ≤ (∫ Φ^p)^{1/p}`. -/
lemma lintegral_cube_le {p : ℝ} (hp : 1 < p) {Φ : Euc d → ℝ≥0∞} (hΦ : Measurable Φ)
    (l : Fin d → ℤ) :
    ∫⁻ z in cube l, Φ z ≤ (∫⁻ z in cube l, Φ z ^ p) ^ (1 / p) := by
  have hq : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (cube l)) hq (f := Φ)
    (g := fun _ => (1 : ℝ≥0∞)) hΦ.aemeasurable aemeasurable_const
  simpa [setLIntegral_const, volume_cube] using h

lemma norm_le_sum_abs (x : Euc d) : ‖x‖ ≤ ∑ i, |x i| := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.mpr ⟨Finset.sum_nonneg (fun i _ => abs_nonneg _), ?_⟩
  have := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i => |x i|)
    (fun i _ => abs_nonneg _)
  simpa [sq_abs] using this

lemma enorm_le_sum_enorm (x : Euc d) : ‖x‖ₑ ≤ ∑ i, ‖x i‖ₑ := by
  rw [← ofReal_norm]
  calc ENNReal.ofReal ‖x‖ ≤ ENNReal.ofReal (∑ i, |x i|) := ENNReal.ofReal_le_ofReal (norm_le_sum_abs x)
    _ = ∑ i, ENNReal.ofReal |x i| := ENNReal.ofReal_sum_of_nonneg fun i _ => abs_nonneg _
    _ = ∑ i, ‖x i‖ₑ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← ofReal_norm, Real.norm_eq_abs]

/-- The cube sums of a continuous vector function represented componentwise by `K ⋆`. -/
theorem cubeSup_le (hd : 1 ≤ d) {p : ℝ} (hp : 1 < p) (K : SchwartzMap (Euc d) ℂ) :
    ∃ S : ℝ≥0∞, S ≠ ⊤ ∧ ∀ u : Euc d → Euc d, Continuous u →
      (∀ (i : Fin d) (y : Euc d), ((u y i : ℝ) : ℂ) = ∫ t, K t * ((u (y + t) i : ℝ) : ℂ)) →
      cubeSupNorm p u ≤ (d : ℝ≥0∞) * S *
        eLpNorm (fun x => ‖u x‖) (ENNReal.ofReal p) volume := by
  obtain ⟨C0, hC00, hC0⟩ := schwartz_prod_bound K
  set A : (Fin d → ℤ) → ℝ≥0∞ := fun l => ENNReal.ofReal (C0 * 4 ^ d * wt l) with hAdef
  have hA : ∀ {j l : Fin d → ℤ} {x z : Euc d}, x ∈ cube j → z ∈ cube l →
      ‖K (z - x)‖ₑ ≤ A (l - j) := by
    intro j l x z hx hz
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (kernel_cube_bound hC00 hC0 hx hz)
  have hSsum : Summable fun l : Fin d → ℤ => C0 * 4 ^ d * wt l :=
    (summable_wt (d := d)).mul_left _
  have hSne : ∑' l, A l ≠ ⊤ := by
    rw [hAdef]
    simp only
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun l => mul_nonneg (by positivity) (wt_nonneg l)) hSsum]
    exact ENNReal.ofReal_ne_top
  refine ⟨∑' l, A l, hSne, fun u hu hrep => ?_⟩
  have hp0 : 0 < p := by linarith
  set Φ : Euc d → ℝ≥0∞ := fun z => ‖u z‖ₑ with hΦdef
  have hΦm : Measurable Φ := hu.measurable.enorm
  set n : (Fin d → ℤ) → ℝ≥0∞ := fun l => (∫⁻ z in cube l, Φ z ^ p) ^ (1 / p) with hndef
  -- pointwise cube bound
  have hpt : ∀ (j : Fin d → ℤ) (x : Euc d), x ∈ cube j →
      ‖u x‖ₑ ≤ (d : ℝ≥0∞) * ∑' l, A (l - j) * n l := by
    intro j x hx
    have hcomp : ∀ i : Fin d, ‖u x i‖ₑ ≤ ∑' l, A (l - j) * n l := by
      intro i
      have h1 := pt_cube_le (K := K) (A := A) hA (a := fun y => ((u y i : ℝ) : ℂ)) (hrep i)
        hΦm (fun z => by
          simp only [hΦdef, enorm_ofReal_c]
          have : |u z i| ≤ ‖u z‖ := by simpa using PiLp.norm_apply_le (u z) i
          rw [← ofReal_norm, ← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (by simpa using this)) hx
      refine le_trans ?_ (h1.trans (ENNReal.tsum_le_tsum fun l => ?_))
      · simp [enorm_ofReal_c]
      · gcongr
        exact lintegral_cube_le hp hΦm l
    calc ‖u x‖ₑ ≤ ∑ i, ‖u x i‖ₑ := enorm_le_sum_enorm _
      _ ≤ ∑ _i : Fin d, ∑' l, A (l - j) * n l := Finset.sum_le_sum fun i _ => hcomp i
      _ = (d : ℝ≥0∞) * ∑' l, A (l - j) * n l := by simp
  -- the sum over cubes
  have hsup : ∀ j : Fin d → ℤ, (⨆ x ∈ cube j, ‖u x‖ₑ) ≤ (d : ℝ≥0∞) * ∑' l, A (l - j) * n l :=
    fun j => iSup₂_le fun x hx => hpt j x hx
  have hY := young_seq (p := p) hp.le A n
  have hnp : ∀ l, n l ^ p = ∫⁻ z in cube l, Φ z ^ p := by
    intro l
    rw [hndef]
    simp only
    rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
  have hsum_n : ∑' l, n l ^ p = ∫⁻ z, Φ z ^ p := by
    rw [lintegral_eq_tsum_cube]
    exact tsum_congr hnp
  have hnorm : eLpNorm (fun x => ‖u x‖) (ENNReal.ofReal p) volume = (∫⁻ z, Φ z ^ p) ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top
      (hu.norm.aestronglyMeasurable), ENNReal.toReal_ofReal hp0.le]
    simp [hΦdef]
  unfold cubeSupNorm
  rw [hnorm]
  calc (∑' j : Fin d → ℤ, (⨆ x ∈ cube j, ‖u x‖ₑ) ^ p) ^ (1 / p)
      ≤ (∑' j : Fin d → ℤ, ((d : ℝ≥0∞) * ∑' l, A (l - j) * n l) ^ p) ^ (1 / p) := by
        gcongr with j
        exact hsup j
    _ = ((d : ℝ≥0∞) ^ p * ∑' j : Fin d → ℤ, (∑' l, A (l - j) * n l) ^ p) ^ (1 / p) := by
        congr 1
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun j => ?_
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
    _ ≤ ((d : ℝ≥0∞) ^ p * ((∑' m, A m) ^ p * ∑' l, n l ^ p)) ^ (1 / p) := by
        gcongr
    _ = (d : ℝ≥0∞) * (∑' l, A l) * (∫⁻ z, Φ z ^ p) ^ (1 / p) := by
        rw [hsum_n, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          mul_one_div_cancel hp0.ne', ENNReal.rpow_one, ENNReal.rpow_one, mul_assoc]


end HRS.Commutator.Whole.SAMP2
