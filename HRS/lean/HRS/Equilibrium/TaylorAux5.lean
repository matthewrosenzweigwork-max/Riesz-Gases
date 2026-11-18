/-
# HRS.Equilibrium.TaylorAux5 — the integrated tail sum `λ ∑_j T(y_j)` in `L^{2q}(μ^{⊗n})`
(Lemma 4.7, packet TAYLOR)

Abstract bound (`taylor_sum_bound`): for a measurable `T : α → [0,∞]` with `∫ T ≤ m₁` and
`∫ T^{6q} ≤ C_T`, the sum `λ ∑_{j∈J} T(y_j)` over i.i.d. coordinates satisfies
`‖λ ∑ T(y_j)‖_{2q} ≤ λ|J| m₁ + λ kb_q √(|J| M m₁ + M²) + λ |J| max(C_T,1)/M²`
for every cap `M > 0`.  Proof: split `T ≤ min(T,M) + T³/M²`; the capped part is a bounded
summand (mean `≤ m₁`, second moment `≤ M m₁`) to which the Bernstein inequality of `TaylorAux1`
applies, and the remainder is handled by Minkowski and the `6q`-th moment.  This replaces the
even-moment inequality `R:eq:even-moment` and the tail moments `R:eq:tail-moments` of the source
(lines 4328, 4349) by a cap at level `M ≈ N^{3/8}`.
-/
import HRS.Equilibrium.TaylorAux4

open MeasureTheory
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.TaylorAux

theorem taylor_real_integral_le' {α : Type*} [MeasurableSpace α] {μ : Measure α} {F : α → ℝ}
    (hF0 : ∀ a, 0 ≤ F a) (hFm : AEStronglyMeasurable F μ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∫⁻ a, ENNReal.ofReal (F a) ∂μ ≤ ENNReal.ofReal B) : ∫ a, F a ∂μ ≤ B := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hF0) hFm]
  exact ENNReal.toReal_le_of_le_ofReal hB h

section SumBound

variable {α : Type*} [MeasurableSpace α]

theorem taylor_T_split (t m : ℝ≥0∞) (hm0 : m ≠ 0) (hmt : m ≠ ∞) :
    t ≤ min t m + t ^ 3 * (m ^ 2)⁻¹ := by
  by_cases h : t ≤ m
  · rw [min_eq_left h]; exact le_self_add
  · push Not at h
    have h1 : m ^ 2 ≤ t ^ 2 := pow_le_pow_left' h.le 2
    have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
    have hm2t : m ^ 2 ≠ ∞ := ENNReal.pow_ne_top hmt
    have h2 : 1 ≤ t ^ 2 * (m ^ 2)⁻¹ := by
      calc (1 : ℝ≥0∞) = m ^ 2 * (m ^ 2)⁻¹ := (ENNReal.mul_inv_cancel hm2 hm2t).symm
        _ ≤ t ^ 2 * (m ^ 2)⁻¹ := mul_le_mul' h1 le_rfl
    calc t = t * 1 := (mul_one t).symm
      _ ≤ t * (t ^ 2 * (m ^ 2)⁻¹) := mul_le_mul' le_rfl h2
      _ = t ^ 3 * (m ^ 2)⁻¹ := by ring
      _ ≤ _ := le_add_self

theorem taylor_sum_bound {μ : Measure α} [IsProbabilityMeasure μ] {n : ℕ} (J : Finset (Fin n))
    (T : α → ℝ≥0∞) (hT : Measurable T) (q : ℕ) (hq : 1 ≤ q) {m1 CT M lam : ℝ} (hm1 : 0 ≤ m1)
    (hint : ∫⁻ z, T z ∂μ ≤ ENNReal.ofReal m1)
    (hCT : ∫⁻ z, T z ^ (6 * q) ∂μ ≤ ENNReal.ofReal CT) (hM : 0 < M) (hlam : 0 ≤ lam) :
    taylorLp (Measure.pi fun _ : Fin n => μ) ((2 * q : ℕ) : ℝ)
        (fun Y => ENNReal.ofReal lam * ∑ j ∈ J, T (Y j)) ≤
      ENNReal.ofReal (lam * J.card * m1 + lam * taylor_kb q * Real.sqrt (J.card * (M * m1) + M ^ 2) +
        lam * J.card * max CT 1 / M ^ 2) := by
  set Pm : Measure (Fin n → α) := Measure.pi fun _ : Fin n => μ with hPm
  have hp0 : (0 : ℝ) < ((2 * q : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * q)
  have hp1 : (1 : ℝ) ≤ ((2 * q : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * q)
  have hkb1 := taylor_kb_one_le q
  -- the capped variable
  set Tc : α → ℝ≥0∞ := fun z => min (T z) (ENNReal.ofReal M) with hTc
  have hTcm : Measurable Tc := hT.min measurable_const
  have hTcfin : ∀ z, Tc z ≠ ∞ := fun z => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_right _ _)
  set t' : α → ℝ := fun z => (Tc z).toReal with ht'
  have ht'm : Measurable t' := ENNReal.measurable_toReal.comp hTcm
  have ht'0 : ∀ z, 0 ≤ t' z := fun z => ENNReal.toReal_nonneg
  have ht'M : ∀ z, t' z ≤ M := fun z => by
    have : Tc z ≤ ENNReal.ofReal M := min_le_right _ _
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top this).trans (by rw [ENNReal.toReal_ofReal hM.le])
  have ht'int : Integrable t' μ := taylor_integrable_of_bdd ht'm (B := M) fun z => by
    rw [abs_of_nonneg (ht'0 z)]; exact ht'M z
  set m : ℝ := ∫ z, t' z ∂μ with hm
  have hm0 : 0 ≤ m := integral_nonneg ht'0
  have hmM : m ≤ M := by
    calc m ≤ ∫ z, M ∂μ := integral_mono ht'int (integrable_const _) ht'M
      _ = M := by simp
  have hmm1 : m ≤ m1 := by
    have h1 : ∫⁻ z, ENNReal.ofReal (t' z) ∂μ ≤ ENNReal.ofReal m1 := by
      calc ∫⁻ z, ENNReal.ofReal (t' z) ∂μ = ∫⁻ z, Tc z ∂μ :=
            lintegral_congr fun z => by simp only [ht']; rw [ENNReal.ofReal_toReal (hTcfin z)]
        _ ≤ ∫⁻ z, T z ∂μ := lintegral_mono fun z => min_le_left _ _
        _ ≤ _ := hint
    exact taylor_real_integral_le' ht'0 ht'm.aestronglyMeasurable hm1 h1
  -- the centered summand
  set X : α → ℝ := fun z => t' z - m with hX
  have hXm : Measurable X := ht'm.sub_const _
  have hXb : ∀ z, |X z| ≤ M := fun z => by
    rw [abs_le]; constructor <;> simp only [hX] <;> linarith [ht'0 z, ht'M z]
  have hX0 : ∫ z, X z ∂μ = 0 := by
    simp only [hX]; rw [integral_sub ht'int (integrable_const _)]; simp [hm]
  have hXv : ∫ z, X z ^ 2 ∂μ ≤ M * m1 := by
    have e : ∀ z, X z ^ 2 = t' z ^ 2 - 2 * m * t' z + m ^ 2 := fun z => by simp only [hX]; ring
    have hsq : Integrable (fun z => t' z ^ 2) μ :=
      taylor_integrable_of_bdd (ht'm.pow_const 2) (B := M ^ 2) fun z => by
        rw [abs_of_nonneg (by positivity)]; exact pow_le_pow_left₀ (ht'0 z) (ht'M z) 2
    have hlin : Integrable (fun z => 2 * m * t' z) μ := ht'int.const_mul _
    have hsub : Integrable (fun z => t' z ^ 2 - 2 * m * t' z) μ := hsq.sub hlin
    have h1 : ∫ z, X z ^ 2 ∂μ = ∫ z, t' z ^ 2 ∂μ - m ^ 2 := by
      simp_rw [e]
      rw [integral_add hsub (integrable_const _), integral_sub hsq hlin, integral_const_mul]
      simp [hm]; ring
    have h2 : ∫ z, t' z ^ 2 ∂μ ≤ M * m := by
      calc ∫ z, t' z ^ 2 ∂μ ≤ ∫ z, M * t' z ∂μ :=
            integral_mono hsq (ht'int.const_mul _) fun z => by
              have := ht'M z; have := ht'0 z; nlinarith
        _ = M * m := integral_const_mul _ _
    rw [h1]
    nlinarith [sq_nonneg m, mul_le_mul_of_nonneg_left hmm1 hM.le]
  -- Bernstein
  have hbern := taylor_bernstein_pi μ n X hXm (M := M) (σ2 := M * m1) hM (mul_nonneg hM.le hm1) hXb
    hX0 hXv q J
  set S : (Fin n → α) → ℝ := fun Y => ∑ j ∈ J, X (Y j) with hS
  have hSm : Measurable S := Finset.measurable_sum _ fun j _ => hXm.comp (measurable_pi_apply j)
  -- the pointwise decomposition
  set cc : ℝ≥0∞ := (ENNReal.ofReal M ^ 2)⁻¹ with hcc
  have hMne : ENNReal.ofReal M ≠ 0 := by simpa using hM
  have hpt : ∀ Y : Fin n → α, ENNReal.ofReal lam * ∑ j ∈ J, T (Y j) ≤
      (ENNReal.ofReal (lam * J.card * m) + ENNReal.ofReal lam * ENNReal.ofReal |S Y|) +
        ENNReal.ofReal lam * ∑ j ∈ J, (T (Y j) ^ 3 * cc) := by
    intro Y
    have h1 : ∑ j ∈ J, T (Y j) ≤ ENNReal.ofReal (J.card * m + |S Y|) +
        ∑ j ∈ J, (T (Y j) ^ 3 * cc) := by
      calc ∑ j ∈ J, T (Y j) ≤ ∑ j ∈ J, (Tc (Y j) + T (Y j) ^ 3 * cc) :=
            Finset.sum_le_sum fun j _ => taylor_T_split _ _ hMne ENNReal.ofReal_ne_top
        _ = ∑ j ∈ J, Tc (Y j) + ∑ j ∈ J, (T (Y j) ^ 3 * cc) := Finset.sum_add_distrib
        _ ≤ _ := by
          gcongr
          have e1 : ∑ j ∈ J, Tc (Y j) = ENNReal.ofReal (∑ j ∈ J, t' (Y j)) := by
            rw [ENNReal.ofReal_sum_of_nonneg fun j _ => ht'0 _]
            refine Finset.sum_congr rfl fun j _ => ?_
            simp only [ht']; rw [ENNReal.ofReal_toReal (hTcfin _)]
          rw [e1]
          refine ENNReal.ofReal_le_ofReal ?_
          have : ∑ j ∈ J, t' (Y j) = J.card * m + S Y := by
            simp only [hS, hX, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]; ring
          rw [this]; linarith [le_abs_self (S Y)]
    calc ENNReal.ofReal lam * ∑ j ∈ J, T (Y j)
        ≤ ENNReal.ofReal lam * (ENNReal.ofReal (J.card * m + |S Y|) + ∑ j ∈ J, (T (Y j) ^ 3 * cc)) :=
          mul_le_mul' le_rfl h1
      _ = (ENNReal.ofReal (lam * J.card * m) + ENNReal.ofReal lam * ENNReal.ofReal |S Y|) +
            ENNReal.ofReal lam * ∑ j ∈ J, (T (Y j) ^ 3 * cc) := by
          rw [mul_add, ENNReal.ofReal_add (by positivity) (abs_nonneg _), mul_add,
            ← ENNReal.ofReal_mul hlam, ← ENNReal.ofReal_mul hlam]
          rw [mul_assoc]
  -- Lp bounds of the three pieces
  set p : ℝ := ((2 * q : ℕ) : ℝ) with hp
  have hSint : Integrable (fun Y => |S Y| ^ (2 * q)) Pm :=
    taylor_integrable_of_bdd (hSm.abs.pow_const _) (B := ((J.card : ℝ) * M) ^ (2 * q)) fun Y => by
      rw [abs_pow, abs_abs]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ _
      simp only [hS]
      calc |∑ j ∈ J, X (Y j)| ≤ ∑ j ∈ J, |X (Y j)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j ∈ J, M := Finset.sum_le_sum fun j _ => hXb _
        _ = _ := by simp
  have hSlp : taylorLp Pm p (fun Y => ENNReal.ofReal |S Y|) ≤
      ENNReal.ofReal (taylor_kb q * Real.sqrt (J.card * (M * m1) + M ^ 2)) := by
    refine taylorLp_le_of_lintegral_le hp0 _ ?_
    have hu : 0 ≤ (J.card : ℝ) * (M * m1) + M ^ 2 := by positivity
    have e1 : ∀ Y, ENNReal.ofReal |S Y| ^ p = ENNReal.ofReal (|S Y| ^ (2 * q)) := fun Y => by
      rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le, hp, Real.rpow_natCast]
    simp_rw [e1]
    rw [← ofReal_integral_eq_lintegral_ofReal hSint (Filter.Eventually.of_forall fun Y => by positivity)]
    have hev : ∀ Y, |S Y| ^ (2 * q) = S Y ^ (2 * q) := fun Y => by
      rw [pow_mul, pow_mul, sq_abs]
    simp_rw [hev]
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le, hp, Real.rpow_natCast]
    refine ENNReal.ofReal_le_ofReal (hbern.trans ?_)
    rw [mul_pow, pow_mul (Real.sqrt _) 2 q, Real.sq_sqrt hu]
    have : (taylor_kb q) ^ (2 * q) ≥ taylor_kb q := by
      calc taylor_kb q = taylor_kb q ^ 1 := (pow_one _).symm
        _ ≤ taylor_kb q ^ (2 * q) := pow_le_pow_right₀ hkb1 (by omega)
    have h2 : 0 ≤ ((J.card : ℝ) * (M * m1) + M ^ 2) ^ q := by positivity
    nlinarith
  have hTj : ∀ j : Fin n, taylorLp Pm p (fun Y => T (Y j) ^ 3) ≤ ENNReal.ofReal (max CT 1) := by
    intro j
    refine taylorLp_le_of_lintegral_le hp0 _ ?_
    have e1 : ∀ Y : Fin n → α, (T (Y j) ^ 3) ^ p = (fun z => T z ^ (6 * q)) (Y j) := fun Y => by
      simp only [hp]
      rw [ENNReal.rpow_natCast, ← pow_mul]; ring_nf
    simp_rw [e1]
    rw [taylor_lintegral_eval μ n j (hT.pow_const _)]
    refine hCT.trans ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le, hp, Real.rpow_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : (1 : ℝ) ≤ max CT 1 := le_max_right _ _
    calc CT ≤ max CT 1 := le_max_left _ _
      _ = max CT 1 ^ 1 := (pow_one _).symm
      _ ≤ max CT 1 ^ (2 * q) := pow_le_pow_right₀ h1 (by omega)
  -- assemble the Minkowski chain
  have hSme : Measurable fun Y : Fin n → α => ENNReal.ofReal |S Y| := hSm.abs.ennreal_ofReal
  have hTjm : ∀ j : Fin n, Measurable fun Y : Fin n → α => T (Y j) ^ 3 := fun j =>
    (hT.comp (measurable_pi_apply j)).pow_const 3
  have hRsm : Measurable fun Y : Fin n → α => ∑ j ∈ J, T (Y j) ^ 3 :=
    Finset.measurable_sum _ fun j _ => hTjm j
  have hBb : taylorLp Pm p (fun Y => ENNReal.ofReal lam * ENNReal.ofReal |S Y|) ≤
      ENNReal.ofReal lam * ENNReal.ofReal (taylor_kb q * Real.sqrt (J.card * (M * m1) + M ^ 2)) := by
    rw [taylorLp_const_mul hp0 _ hSme]
    exact mul_le_mul' le_rfl hSlp
  have hRs : taylorLp Pm p (fun Y => ENNReal.ofReal lam * ∑ j ∈ J, (T (Y j) ^ 3 * cc)) ≤
      (ENNReal.ofReal lam * cc) * (J.card * ENNReal.ofReal (max CT 1)) := by
    have e : (fun Y : Fin n → α => ENNReal.ofReal lam * ∑ j ∈ J, (T (Y j) ^ 3 * cc)) =
        fun Y => (ENNReal.ofReal lam * cc) * ∑ j ∈ J, T (Y j) ^ 3 := by
      funext Y; rw [← Finset.sum_mul]; ring
    rw [e, taylorLp_const_mul hp0 _ hRsm]
    refine mul_le_mul' le_rfl ?_
    refine (taylorLp_sum hp1 J hTjm).trans ?_
    calc ∑ j ∈ J, taylorLp Pm p (fun Y => T (Y j) ^ 3) ≤ ∑ _j ∈ J, ENNReal.ofReal (max CT 1) :=
          Finset.sum_le_sum fun j _ => hTj j
      _ = _ := by simp
  have hcc' : cc = ENNReal.ofReal (1 / M ^ 2) := by
    rw [hcc, ← ENNReal.ofReal_pow hM.le, one_div, ENNReal.ofReal_inv_of_pos (by positivity)]
  have hAm : Measurable fun _ : Fin n → α => ENNReal.ofReal (lam * J.card * m) := measurable_const
  have hBbm : Measurable fun Y : Fin n → α => ENNReal.ofReal lam * ENNReal.ofReal |S Y| :=
    hSme.const_mul _
  have hRsm' : Measurable fun Y : Fin n → α => ENNReal.ofReal lam * ∑ j ∈ J, (T (Y j) ^ 3 * cc) :=
    (Finset.measurable_sum _ fun j _ => (hTjm j).mul_const _).const_mul _
  calc taylorLp Pm p (fun Y => ENNReal.ofReal lam * ∑ j ∈ J, T (Y j))
      ≤ taylorLp Pm p (fun Y => (ENNReal.ofReal (lam * J.card * m) +
          ENNReal.ofReal lam * ENNReal.ofReal |S Y|) +
          ENNReal.ofReal lam * ∑ j ∈ J, (T (Y j) ^ 3 * cc)) := taylorLp_mono hp0.le hpt
    _ ≤ taylorLp Pm p (fun Y => ENNReal.ofReal (lam * J.card * m) +
          ENNReal.ofReal lam * ENNReal.ofReal |S Y|) +
        taylorLp Pm p (fun Y => ENNReal.ofReal lam * ∑ j ∈ J, (T (Y j) ^ 3 * cc)) :=
        taylorLp_add hp1 (hAm.add hBbm).aemeasurable hRsm'.aemeasurable
    _ ≤ (taylorLp Pm p (fun _ => ENNReal.ofReal (lam * J.card * m)) +
          taylorLp Pm p (fun Y => ENNReal.ofReal lam * ENNReal.ofReal |S Y|)) +
        taylorLp Pm p (fun Y => ENNReal.ofReal lam * ∑ j ∈ J, (T (Y j) ^ 3 * cc)) := by
        gcongr
        exact taylorLp_add hp1 hAm.aemeasurable hBbm.aemeasurable
    _ ≤ (ENNReal.ofReal (lam * J.card * m) +
          ENNReal.ofReal lam * ENNReal.ofReal (taylor_kb q * Real.sqrt (J.card * (M * m1) + M ^ 2))) +
        (ENNReal.ofReal lam * cc) * (J.card * ENNReal.ofReal (max CT 1)) := by
        rw [taylorLp_const hp0]
        gcongr
    _ ≤ _ := by
        rw [hcc']
        have hl1 : 0 ≤ lam * J.card * m := by positivity
        have hl2 : 0 ≤ lam * (taylor_kb q * Real.sqrt (J.card * (M * m1) + M ^ 2)) := by positivity
        have e3 : ENNReal.ofReal lam * ENNReal.ofReal (1 / M ^ 2) * ((J.card : ℝ≥0∞) * ENNReal.ofReal (max CT 1)) =
            ENNReal.ofReal (lam * J.card * max CT 1 / M ^ 2) := by
          rw [← ENNReal.ofReal_mul hlam, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1; field_simp
        rw [e3, ← ENNReal.ofReal_mul hlam, ← ENNReal.ofReal_add hl1 hl2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have : lam * J.card * m ≤ lam * J.card * m1 := by gcongr
        nlinarith [this, show lam * (taylor_kb q * Real.sqrt (J.card * (M * m1) + M ^ 2)) =
          lam * taylor_kb q * Real.sqrt (J.card * (M * m1) + M ^ 2) by ring]

end SumBound

end HRS.TaylorAux
