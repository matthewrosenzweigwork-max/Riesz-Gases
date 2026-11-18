import Mathlib
import HRS.MS.SuppU5Aux3

/-!
# Packet U5 (aux 4): nets in `ℝ^d` and the tail estimate for the feature map
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace Matrix

noncomputable section

namespace HRS.U5

abbrev Eu (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Grid net of the ball of radius `R` with mesh `δ`: cardinality and covering property. -/
lemma u5_net {d : ℕ} {δ : ℝ} (hδ : 0 < δ) {R : ℝ} (hR0 : 0 ≤ R) :
    ∃ F : Finset (Eu d), ((F.card : ℝ) ≤ (2 * (R / δ + 2) + 1) ^ d + 1) ∧
      ∀ x : Eu d, ‖x‖ ≤ R → ∃ y ∈ F, ‖x - y‖ ≤ δ * Real.sqrt d := by
  classical
  set M : ℤ := ⌈R / δ⌉ + 1 with hM
  have hRδ : 0 ≤ R / δ := div_nonneg hR0 hδ.le
  have hM1 : (1 : ℤ) ≤ M := by
    have : (0 : ℤ) ≤ ⌈R / δ⌉ := Int.ceil_nonneg hRδ
    omega
  have hMr : (M : ℝ) ≤ R / δ + 2 := by
    have := Int.ceil_lt_add_one (R / δ)
    rw [hM]; push_cast; linarith
  let box : Finset (Fin d → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-M) M
  let F : Finset (Eu d) := insert 0 (box.image fun m => (WithLp.toLp 2 fun i => δ * (m i : ℝ) : Eu d))
  refine ⟨F, ?_, fun x hx => ?_⟩
  · have hc1 : F.card ≤ box.card + 1 := by
      refine (Finset.card_insert_le _ _).trans ?_
      exact Nat.succ_le_succ Finset.card_image_le
    have hc2 : (box.card : ℝ) = (2 * (M : ℝ) + 1) ^ d := by
      simp only [box, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      have : ((M + 1 - -M).toNat : ℝ) = 2 * (M : ℝ) + 1 := by
        have h : (0 : ℤ) ≤ M + 1 - -M := by omega
        have : (((M + 1 - -M).toNat : ℤ) : ℝ) = ((M + 1 - -M : ℤ) : ℝ) := by rw [Int.toNat_of_nonneg h]
        push_cast at this ⊢
        linarith
      rw [Nat.cast_pow, this]
    have hc3 : (F.card : ℝ) ≤ (box.card : ℝ) + 1 := by exact_mod_cast hc1
    refine hc3.trans ?_
    rw [hc2]
    gcongr
  · set m : Fin d → ℤ := fun i => ⌊x i / δ⌋ with hm
    have hmem : m ∈ box := by
      simp only [box, Fintype.mem_piFinset, Finset.mem_Icc]
      intro i
      have hxi : |x i| ≤ R := by
        have := PiLp.norm_apply_le x i
        rw [Real.norm_eq_abs] at this
        linarith
      have hc : R / δ ≤ ⌈R / δ⌉ := Int.le_ceil _
      have hxd : |x i / δ| ≤ R / δ := by
        rw [abs_div, abs_of_pos hδ]; exact div_le_div_of_nonneg_right hxi hδ.le
      have hlo := (abs_le.1 hxd).1
      have hhi := (abs_le.1 hxd).2
      constructor
      · rw [hm]; show -M ≤ ⌊x i / δ⌋
        rw [Int.le_floor]
        push_cast
        rw [hM]; push_cast
        linarith
      · have := Int.floor_le (x i / δ)
        have h2 : (⌊x i / δ⌋ : ℝ) ≤ M := by rw [hM]; push_cast; linarith
        exact_mod_cast h2
    refine ⟨(WithLp.toLp 2 fun i => δ * (m i : ℝ) : Eu d), Finset.mem_insert_of_mem
      (Finset.mem_image.2 ⟨m, hmem, rfl⟩), ?_⟩
    rw [EuclideanSpace.norm_eq]
    have hc : ∀ i : Fin d, (x i - δ * (m i : ℝ)) ^ 2 ≤ δ ^ 2 := fun i => by
      have a1 := Int.floor_le (x i / δ)
      have a2 := Int.lt_floor_add_one (x i / δ)
      rw [le_div_iff₀ hδ] at a1
      rw [div_lt_iff₀ hδ] at a2
      have b1 : 0 ≤ x i - δ * (m i : ℝ) := by simp only [hm]; nlinarith
      have b2 : x i - δ * (m i : ℝ) ≤ δ := by simp only [hm]; nlinarith
      nlinarith
    calc Real.sqrt (∑ i, ‖(x - (WithLp.toLp 2 fun i => δ * (m i : ℝ) : Eu d)) i‖ ^ 2)
        ≤ Real.sqrt (∑ _i : Fin d, δ ^ 2) := by
          refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
          simpa [Real.norm_eq_abs, sq_abs] using hc i
      _ = δ * Real.sqrt d := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Real.sqrt_mul (by positivity), Real.sqrt_sq hδ.le, mul_comm]

/-- The finite-dimensional core with an explicit net: tail estimate, projection onto the span of
the net values. -/
theorem u5_core3 {d k N : ℕ} (hd : 1 ≤ d) (hN : 1 ≤ N) (μ : Measure (Eu d)) [IsProbabilityMeasure μ]
    {m₂ : ℝ} (hm2 : Integrable (fun x : Eu d => ‖x‖ ^ 2) μ) (hm : ∫ x, ‖x‖ ^ 2 ∂μ ≤ m₂)
    (J : Eu d → Ek k) (hJm : Measurable J) {b Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hb : ∀ x, ‖J x‖ ≤ b)
    (hΛ : ∀ x y, ‖J x - J y‖ ≤ Λ * ‖x - y‖) (h0 : ∀ c, ∫ x, J x c ∂μ = 0)
    {R ρ : ℝ} (hR : 1 ≤ R) (hρ : 0 < ρ) :
    ∃ n : ℕ, 1 ≤ n ∧ (n : ℝ) ≤ (2 * (R / (ρ / Real.sqrt d) + 2) + 1) ^ d + 1 ∧
      ∀ ε : ℝ, 0 < ε →
        wassersteinE 1 ((Measure.pi fun _ : Fin N => μ.map J).map
            (fun ω => (Real.sqrt N)⁻¹ • ∑ i, ω i))
          (multivariateGaussian (0 : Ek k) (Yurinskii.momentMatrix (μ.map J))) ≤
        ENNReal.ofReal (2 * (Λ * ρ + b * Real.sqrt m₂ / R) + (2 * ε * Real.sqrt n +
          2 / ε ^ 2 * ((2 + Yurinskii.c4 / 2) * (b ^ 3 / Real.sqrt N)))) := by
  have hdpos : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hd1 : (1 : ℝ) ≤ Real.sqrt d := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hd)
  have hδ : 0 < ρ / Real.sqrt d := div_pos hρ hdpos
  obtain ⟨F, hFc, hFcov⟩ := u5_net (d := d) hδ (by linarith : (0 : ℝ) ≤ R)
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0)
  have hm0 : 0 ≤ m₂ := (integral_nonneg fun _ => by positivity).trans hm
  set V : Submodule ℝ (Ek k) := Submodule.span ℝ (J '' (F : Set (Eu d))) with hV
  haveI : V.HasOrthogonalProjection := inferInstance
  set P := V.starProjection with hP
  have hVr : Module.finrank ℝ V ≤ F.card := by
    have h1 : V = Submodule.span ℝ ((F.image J : Finset (Ek k)) : Set (Ek k)) := by
      rw [hV, Finset.coe_image]
    rw [h1]
    exact (finrank_span_finset_le_card _).trans Finset.card_image_le
  refine ⟨max F.card 1, le_max_right _ _, ?_, fun ε hε => ?_⟩
  · have : (((max F.card 1 : ℕ)) : ℝ) = max (F.card : ℝ) 1 := by push_cast; rfl
    rw [this]
    refine max_le hFc ?_
    have : (0 : ℝ) ≤ (2 * (R / (ρ / Real.sqrt d) + 2) + 1) ^ d := by
      have : 0 ≤ R / (ρ / Real.sqrt d) := div_nonneg (by linarith) hδ.le
      positivity
    linarith
  · -- tail estimate
    have hρJ : IsProbabilityMeasure (μ.map J) := inferInstance
    have hptw : ∀ x, ‖J x - P (J x)‖ ^ 2 ≤ (Λ * ρ) ^ 2 + b ^ 2 * ‖x‖ ^ 2 / R ^ 2 := by
      intro x
      by_cases hx : ‖x‖ ≤ R
      · obtain ⟨y, hyF, hxy⟩ := hFcov x hx
        have hyV : J y ∈ V := Submodule.subset_span ⟨y, hyF, rfl⟩
        have h1 : ‖J x - P (J x)‖ ≤ ‖J x - J y‖ := u5_proj_le V (J x) (J y) hyV
        have h2 : ‖J x - J y‖ ≤ Λ * ρ := by
          refine (hΛ x y).trans (mul_le_mul_of_nonneg_left ?_ hΛ0)
          refine hxy.trans (le_of_eq ?_)
          field_simp
        have : ‖J x - P (J x)‖ ^ 2 ≤ (Λ * ρ) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2
        have : 0 ≤ b ^ 2 * ‖x‖ ^ 2 / R ^ 2 := by positivity
        linarith
      · push Not at hx
        have h1 : ‖J x - P (J x)‖ ≤ b := by
          have := u5_proj_le V (J x) 0 V.zero_mem
          rw [sub_zero] at this
          exact this.trans (hb x)
        have h2 : b ≤ b * ‖x‖ / R := by
          rw [le_div_iff₀ (by linarith)]
          nlinarith
        have : ‖J x - P (J x)‖ ^ 2 ≤ (b * ‖x‖ / R) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2
        rw [div_pow, mul_pow] at this
        have : 0 ≤ (Λ * ρ) ^ 2 := sq_nonneg _
        linarith
    have htail : ∫ y, ‖y - P y‖ ^ 2 ∂(μ.map J) ≤
        (Λ * ρ + b * Real.sqrt m₂ / R) ^ 2 := by
      rw [integral_map hJm.aemeasurable (by fun_prop : Measurable fun y : Ek k => ‖y - P y‖ ^ 2).aestronglyMeasurable]
      have hint : Integrable (fun x : Eu d => (Λ * ρ) ^ 2 + b ^ 2 * ‖x‖ ^ 2 / R ^ 2) μ :=
        (integrable_const _).add ((hm2.const_mul (b ^ 2)).div_const _)
      have hmeas : Measurable fun x : Eu d => ‖J x - P (J x)‖ ^ 2 :=
        ((hJm.sub (P.continuous.measurable.comp hJm)).norm).pow_const 2
      have hi2 : Integrable (fun x : Eu d => ‖J x - P (J x)‖ ^ 2) μ :=
        hint.mono' hmeas.aestronglyMeasurable (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hptw x)
      calc ∫ x, ‖J x - P (J x)‖ ^ 2 ∂μ ≤ ∫ x, ((Λ * ρ) ^ 2 + b ^ 2 * ‖x‖ ^ 2 / R ^ 2) ∂μ :=
            integral_mono hi2 hint hptw
        _ = (Λ * ρ) ^ 2 + b ^ 2 * (∫ x, ‖x‖ ^ 2 ∂μ) / R ^ 2 := by
            rw [integral_add (integrable_const _) ((hm2.const_mul (b ^ 2)).div_const _),
              integral_div, integral_const_mul]
            simp
        _ ≤ (Λ * ρ) ^ 2 + b ^ 2 * m₂ / R ^ 2 := by
            gcongr
        _ ≤ (Λ * ρ + b * Real.sqrt m₂ / R) ^ 2 := by
            have hsq : Real.sqrt m₂ ^ 2 = m₂ := Real.sq_sqrt hm0
            have : b ^ 2 * m₂ / R ^ 2 = (b * Real.sqrt m₂ / R) ^ 2 := by
              rw [div_pow, mul_pow, hsq]
            rw [this]
            have : 0 ≤ Λ * ρ * (b * Real.sqrt m₂ / R) := by positivity
            nlinarith
    have hmean : ∀ c, ∫ y, y c ∂(μ.map J) = 0 := fun c => by
      rw [integral_map hJm.aemeasurable (by fun_prop : Measurable fun y : Ek k => y c).aestronglyMeasurable]
      exact h0 c
    have hbae : ∀ᵐ y ∂(μ.map J), ‖y‖ ≤ b := by
      rw [ae_map_iff hJm.aemeasurable (measurableSet_le measurable_norm measurable_const)]
      exact ae_of_all _ hb
    have hδ0 : 0 ≤ Λ * ρ + b * Real.sqrt m₂ / R := by positivity
    have := u5_core2 (N := N) hN (μ.map J) hbae hmean V (n := max F.card 1)
      (hVr.trans (le_max_left _ _)) hδ0 htail hε
    exact this

/-- The constant of the finite-dimensional core. -/
def u5_C0 (d : ℕ) (m₂ : ℝ) : ℝ :=
  2 + 2 * Real.sqrt m₂ + (6 + Yurinskii.c4) * (2 * (2 * Real.sqrt d + 5) ^ d) ^ ((1 : ℝ) / 3)

lemma u5_C0_nonneg (d : ℕ) (m₂ : ℝ) : 0 ≤ u5_C0 d m₂ := by
  unfold u5_C0
  have := Yurinskii.c4_nonneg
  positivity

set_option maxHeartbeats 1000000 in
/-- Optimised finite-dimensional core: the rate `N^{-1/(4d+10)}` (no logarithm). -/
theorem u5_core_final {d k N : ℕ} (hd : 1 ≤ d) (hN : 1 ≤ N) (μ : Measure (Eu d))
    [IsProbabilityMeasure μ]
    {m₂ : ℝ} (hm2 : Integrable (fun x : Eu d => ‖x‖ ^ 2) μ) (hm : ∫ x, ‖x‖ ^ 2 ∂μ ≤ m₂)
    (J : Eu d → Ek k) (hJm : Measurable J) {b Λ : ℝ} (hbpos : 0 < b) (hΛ0 : 0 ≤ Λ)
    (hb : ∀ x, ‖J x‖ ≤ b)
    (hΛ : ∀ x y, ‖J x - J y‖ ≤ Λ * ‖x - y‖) (h0 : ∀ c, ∫ x, J x c ∂μ = 0) :
    wassersteinE 1 ((Measure.pi fun _ : Fin N => μ.map J).map
        (fun ω => (Real.sqrt N)⁻¹ • ∑ i, ω i))
      (multivariateGaussian (0 : Ek k) (Yurinskii.momentMatrix (μ.map J))) ≤
    ENNReal.ofReal (u5_C0 d m₂ * (Λ + b) * (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10)))) := by
  set a : ℝ := 1 / (4 * (d : ℝ) + 10) with ha
  have hapos : 0 < a := by rw [ha]; positivity
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  set R : ℝ := (N : ℝ) ^ a with hR
  have hR1 : 1 ≤ R := Real.one_le_rpow hNr hapos.le
  have hRpos : 0 < R := by linarith
  have hRinv : R⁻¹ = (N : ℝ) ^ (-a) := by rw [hR, Real.rpow_neg hNpos.le]
  obtain ⟨n, hn1, hn, hbound⟩ := u5_core3 (N := N) hd hN μ hm2 hm J hJm hΛ0 hb hΛ h0 (R := R)
    (ρ := R⁻¹) hR1 (inv_pos.2 hRpos)
  have hdpos : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hd1 : (1 : ℝ) ≤ Real.sqrt d := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hd)
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < n := by linarith
  -- the cardinality bound
  have hnR : (n : ℝ) ≤ 2 * (2 * Real.sqrt d + 5) ^ d * R ^ (2 * d) := by
    refine hn.trans ?_
    have h1 : R / (R⁻¹ / Real.sqrt d) = R ^ 2 * Real.sqrt d := by
      field_simp
    rw [h1]
    have h2 : 2 * (R ^ 2 * Real.sqrt d + 2) + 1 ≤ (2 * Real.sqrt d + 5) * R ^ 2 := by
      nlinarith [sq_nonneg R, mul_nonneg (sq_nonneg R) (by linarith : (0 : ℝ) ≤ Real.sqrt d - 1)]
    have h3 : (2 * (R ^ 2 * Real.sqrt d + 2) + 1) ^ d ≤ ((2 * Real.sqrt d + 5) * R ^ 2) ^ d :=
      pow_le_pow_left₀ (by positivity) h2 d
    have h4 : 1 ≤ ((2 * Real.sqrt d + 5) * R ^ 2) ^ d := by
      refine one_le_pow₀ ?_
      nlinarith [sq_nonneg R]
    calc (2 * (R ^ 2 * Real.sqrt d + 2) + 1) ^ d + 1 ≤ 2 * ((2 * Real.sqrt d + 5) * R ^ 2) ^ d := by
          linarith
      _ = 2 * (2 * Real.sqrt d + 5) ^ d * R ^ (2 * d) := by
          rw [mul_pow, ← pow_mul, mul_assoc]
  -- the choice of ε
  set sN : ℝ := Real.sqrt N with hsN
  have hsNpos : 0 < sN := Real.sqrt_pos.2 hNpos
  set m : ℝ := Real.sqrt n with hm_
  have hmpos : 0 < m := Real.sqrt_pos.2 hnpos
  set α : ℝ := (m * sN) ^ ((1 : ℝ) / 3) with hα
  have hαpos : 0 < α := Real.rpow_pos_of_pos (by positivity) _
  have hα3 : α ^ 3 = m * sN := by
    rw [hα, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  set ε : ℝ := b / α with hε
  have hεpos : 0 < ε := by positivity
  have hmain := hbound ε hεpos
  -- E = m / α
  set E : ℝ := m / α with hE
  have hE0 : 0 ≤ E := by positivity
  have hE3 : E ^ 3 = n / sN := by
    rw [hE, div_pow, hα3]
    have : m ^ 3 = (n : ℝ) * m := by
      have : m ^ 2 = n := Real.sq_sqrt hnpos.le
      nlinarith
    rw [this]
    field_simp
  have hterm1 : 2 * ε * m = 2 * b * E := by rw [hε, hE]; ring
  have hterm2 : 2 / ε ^ 2 * ((2 + Yurinskii.c4 / 2) * (b ^ 3 / sN)) = (4 + Yurinskii.c4) * b * E := by
    have hαE : α ^ 2 / sN = E := by
      rw [hE]
      field_simp
      nlinarith [hα3]
    rw [hε]
    field_simp
    rw [← hαE]
    field_simp
    ring
  -- the bound on E
  have hE3le : E ^ 3 ≤ 2 * (2 * Real.sqrt d + 5) ^ d * (N : ℝ) ^ (-(3 * a)) := by
    rw [hE3]
    have h1 : (n : ℝ) / sN ≤ 2 * (2 * Real.sqrt d + 5) ^ d * R ^ (2 * d) / sN :=
      div_le_div_of_nonneg_right hnR hsNpos.le
    refine h1.trans ?_
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have e1 : R ^ (2 * d) = (N : ℝ) ^ (a * (2 * d : ℕ)) := by
      rw [hR, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    have e2 : sN = (N : ℝ) ^ ((1 : ℝ) / 2) := by rw [hsN, Real.sqrt_eq_rpow]
    rw [e1, e2, ← Real.rpow_sub hNpos]
    refine Real.rpow_le_rpow_of_exponent_le hNr ?_
    have ht : 0 < 4 * (d : ℝ) + 10 := by positivity
    have key : a * (2 * (d : ℝ) + 3) ≤ 1 / 2 := by
      rw [ha, one_div, inv_mul_le_iff₀ ht]; linarith
    push_cast
    nlinarith [key]
  -- cube root
  have hc0 : 0 ≤ 2 * (2 * Real.sqrt d + 5) ^ d := by positivity
  have hEle : E ≤ (2 * (2 * Real.sqrt d + 5) ^ d) ^ ((1 : ℝ) / 3) * (N : ℝ) ^ (-a) := by
    have hcube : ((2 * (2 * Real.sqrt d + 5) ^ d) ^ ((1 : ℝ) / 3) * (N : ℝ) ^ (-a)) ^ 3 =
        2 * (2 * Real.sqrt d + 5) ^ d * (N : ℝ) ^ (-(3 * a)) := by
      have e1 : ((2 * (2 * Real.sqrt d + 5) ^ d) ^ ((1 : ℝ) / 3)) ^ 3 = 2 * (2 * Real.sqrt d + 5) ^ d := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hc0]; norm_num
      have e2 : ((N : ℝ) ^ (-a)) ^ 3 = (N : ℝ) ^ (-(3 * a)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; congr 1; push_cast; ring
      rw [mul_pow, e1, e2]
    refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by positivity) ?_
    rw [hcube]; exact hE3le
  -- assemble
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [hterm1, hterm2]
  set X : ℝ := (N : ℝ) ^ (-a) with hX
  have hX0 : 0 ≤ X := by positivity
  have hs0 : 0 ≤ Real.sqrt m₂ := Real.sqrt_nonneg _
  have hc13 : 0 ≤ (2 * (2 * Real.sqrt d + 5) ^ d) ^ ((1 : ℝ) / 3) := by positivity
  have hc4 := Yurinskii.c4_nonneg
  have hkey : (6 + Yurinskii.c4) * b * E ≤
      (6 + Yurinskii.c4) * b * ((2 * (2 * Real.sqrt d + 5) ^ d) ^ ((1 : ℝ) / 3) * X) := by
    refine mul_le_mul_of_nonneg_left hEle (by positivity)
  have hdiv : b * Real.sqrt m₂ / R = b * Real.sqrt m₂ * X := by
    rw [div_eq_mul_inv, hRinv]
  rw [hRinv, hdiv]
  unfold u5_C0
  have h1 : 0 ≤ b * X := by positivity
  have h2 : 0 ≤ Real.sqrt m₂ * Λ * X := by positivity
  have h3 : 0 ≤ (6 + Yurinskii.c4) * (2 * (2 * Real.sqrt d + 5) ^ d) ^ ((1 : ℝ) / 3) * Λ * X := by positivity
  nlinarith [h1, h2, h3, hkey]

end HRS.U5
