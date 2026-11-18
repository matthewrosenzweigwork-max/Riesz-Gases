import HRS.MS.R2ChaosAux21

/-!
# HRS.MS.R2ChaosAux22 -- the diagonal correction `R_N` is small in `L²(P ⊗ dt)`

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

variable {d : ℕ}

section Resid

variable {n : ℕ}

/-- The diagonal function `g_t(x) = ∑ C_ab(t) ũ_a(x) ũ_b(x)`. -/
def s94gt (C : ℝ → Fin n → Fin n → ℝ) (u : Fin n → Euc d → ℝ) (t : ℝ) (x : Euc d) : ℝ :=
  ∑ a, ∑ b, C t a b * u a x * u b x

/-- `G_N(t, X) = μ_N(g_t)`. -/
def s94Gt {Ω0 : Type*} {N : ℕ} (X0 : ℝ≥0 → Ω0 → EucConfig d N) (C : ℝ → Fin n → Fin n → ℝ)
    (u : Fin n → Euc d → ℝ) (t : ℝ) (ζ : Ω0) : ℝ :=
  Whole.pair (Whole.empirical (X0 t.toNNReal ζ)) (s94gt C u t)

/-- The residual `R_N(t) = (1/2)(G_N(t) - E G_N(t))`. -/
def s94Rt {Ω0 : Type*} [MeasurableSpace Ω0] {N : ℕ} (X0 : ℝ≥0 → Ω0 → EucConfig d N) (P0 : Measure Ω0)
    (C : ℝ → Fin n → Fin n → ℝ) (u : Fin n → Euc d → ℝ) (t : ℝ) (ζ : Ω0) : ℝ :=
  (1 / 2) * (s94Gt X0 C u t ζ - ∫ ζ', s94Gt X0 C u t ζ' ∂P0)

theorem s94gt_measurable {C : ℝ → Fin n → Fin n → ℝ} (hC : ∀ a b, Measurable fun t => C t a b)
    {u : Fin n → Euc d → ℝ} (hu : ∀ a, IsR2Test (u a)) :
    Measurable fun q : ℝ × Euc d => s94gt C u q.1 q.2 := by
  unfold s94gt
  refine Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_
  exact (((hC a b).comp measurable_fst).mul ((s94_test_continuous (hu a)).measurable.comp measurable_snd)).mul
    ((s94_test_continuous (hu b)).measurable.comp measurable_snd)

theorem s94gt_abs_le {C : ℝ → Fin n → Fin n → ℝ} {K0 : ℝ} (hK : 0 ≤ K0) (hCb : ∀ t a b, |C t a b| ≤ K0)
    {u : Fin n → Euc d → ℝ} (hu : ∀ a, IsR2Test (u a)) :
    ∃ Ag : ℝ, 0 ≤ Ag ∧ ∀ t x, |s94gt C u t x| ≤ Ag := by
  choose A hA using fun a => s94_test_bounded (hu a)
  refine ⟨∑ a, ∑ b, K0 * A a * A b, ?_, fun t x => ?_⟩
  · refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
    have h1 : 0 ≤ A a := (abs_nonneg _).trans (hA a (0 : Euc d))
    have h2 : 0 ≤ A b := (abs_nonneg _).trans (hA b (0 : Euc d))
    positivity
  · unfold s94gt
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [abs_mul, abs_mul]
    have h1 := hA a x
    have h2 := hA b x
    have h3 : 0 ≤ |u a x| := abs_nonneg _
    have h5 : 0 ≤ A a := h3.trans h1
    calc |C t a b| * |u a x| * |u b x| ≤ K0 * A a * A b := by
          gcongr
          exact hCb t a b

theorem s94Gt_measurable {N : ℕ} (hN : 0 < N) {Ω0 : Type*} [MeasurableSpace Ω0] (X0 : ℝ≥0 → Ω0 → EucConfig d N)
    (hX : Measurable fun q : ℝ≥0 × Ω0 => X0 q.1 q.2) {C : ℝ → Fin n → Fin n → ℝ}
    (hC : ∀ a b, Measurable fun t => C t a b) {u : Fin n → Euc d → ℝ} (hu : ∀ a, IsR2Test (u a)) :
    Measurable fun q : ℝ × Ω0 => s94Gt X0 C u q.1 q.2 := by
  have hq : Measurable fun q : ℝ × Ω0 => (q.1.toNNReal, q.2) :=
    (measurable_fst.real_toNNReal).prodMk measurable_snd
  have hXq : Measurable fun q : ℝ × Ω0 => X0 q.1.toNNReal q.2 := hX.comp hq
  have hg := s94gt_measurable hC hu
  have e : (fun q : ℝ × Ω0 => s94Gt X0 C u q.1 q.2) =
      fun q => (N : ℝ)⁻¹ * ∑ i, s94gt C u q.1 (X0 q.1.toNNReal q.2 i) := by
    funext q; unfold s94Gt; rw [Whole.pair_empirical hN]
  rw [e]
  refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
  exact Measurable.comp (g := fun r : ℝ × Euc d => s94gt C u r.1 r.2)
    (f := fun q : ℝ × Ω0 => (q.1, X0 q.1.toNNReal q.2 i)) hg
    (measurable_fst.prodMk ((measurable_pi_apply i).comp hXq))

theorem s94Rt_measurable {N : ℕ} (hN : 0 < N) {Ω0 : Type*} [MeasurableSpace Ω0] (X0 : ℝ≥0 → Ω0 → EucConfig d N)
    (hX : Measurable fun q : ℝ≥0 × Ω0 => X0 q.1 q.2) (P0 : Measure Ω0) [IsProbabilityMeasure P0]
    {C : ℝ → Fin n → Fin n → ℝ} (hC : ∀ a b, Measurable fun t => C t a b) {u : Fin n → Euc d → ℝ}
    (hu : ∀ a, IsR2Test (u a)) : Measurable fun q : ℝ × Ω0 => s94Rt X0 P0 C u q.1 q.2 := by
  have hG := s94Gt_measurable hN X0 hX hC hu
  have hI : Measurable fun t : ℝ => ∫ ζ', s94Gt X0 C u t ζ' ∂P0 :=
    (hG.stronglyMeasurable.integral_prod_right' (ν := P0)).measurable
  unfold s94Rt
  exact (hG.sub (hI.comp measurable_fst)).const_mul _

theorem s94_var_le_shift {Ω0 : Type*} [MeasurableSpace Ω0] {P0 : Measure Ω0} [IsProbabilityMeasure P0]
    {G : Ω0 → ℝ} (hGm : Measurable G) {Ag : ℝ} (hGb : ∀ ζ, |G ζ| ≤ Ag) (c : ℝ) :
    ∫ ζ, (G ζ - ∫ ζ', G ζ' ∂P0) ^ 2 ∂P0 ≤ ∫ ζ, (G ζ - c) ^ 2 ∂P0 := by
  have hGi : Integrable G P0 := Integrable.of_bound hGm.aestronglyMeasurable Ag
    (ae_of_all _ fun ζ => by simpa using hGb ζ)
  have hmem : MemLp (fun ζ => G ζ - c) 2 P0 := by
    refine MemLp.of_bound (hGm.sub measurable_const).aestronglyMeasurable (Ag + |c|) (ae_of_all _ fun ζ => ?_)
    rw [Real.norm_eq_abs]
    exact (abs_sub _ _).trans (by linarith [hGb ζ])
  have hvar := s94_var_le hmem
  have hshift : ∫ ζ, ((G ζ - c) - ∫ ζ', (G ζ' - c) ∂P0) ^ 2 ∂P0 = ∫ ζ, (G ζ - ∫ ζ', G ζ' ∂P0) ^ 2 ∂P0 := by
    refine integral_congr_ae (ae_of_all _ fun ζ => ?_)
    rw [integral_sub hGi (integrable_const _)]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    ring
  rw [← hshift]
  exact hvar

theorem s94_Rt_sq_le {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {N : ℕ} (hN : 2 ≤ N) {Ω0 : Type*}
    [MeasurableSpace Ω0] (X0 : ℝ≥0 → Ω0 → EucConfig d N) (hX : Measurable fun q : ℝ≥0 × Ω0 => X0 q.1 q.2)
    (P0 : Measure Ω0) [IsProbabilityMeasure P0] {C : ℝ → Fin n → Fin n → ℝ}
    (hC : ∀ a b, Measurable fun t => C t a b) {u : Fin n → Euc d → ℝ} (hu : ∀ a, IsR2Test (u a)) {t : ℝ}
    {C1 Ag : ℝ} (hAg : ∀ x, |s94gt C u t x| ≤ Ag)
    (hLM : eLpNorm (fun ζ => r2EmpFluct μ (s94gt C u t) X0 ζ t) (ENNReal.ofReal 2) P0 ≤ ENNReal.ofReal (C1 * Ag)) :
    ∫ ζ, (s94Rt X0 P0 C u t ζ) ^ 2 ∂P0 ≤ (|C1 * Ag|) ^ 2 / (4 * N) := by
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hGm : Measurable fun ζ => s94Gt X0 C u t ζ :=
    Measurable.comp (g := fun q : ℝ × Ω0 => s94Gt X0 C u q.1 q.2) (f := fun ζ : Ω0 => (t, ζ))
      (s94Gt_measurable hN0 X0 hX hC hu) measurable_prodMk_left
  have hGb : ∀ ζ, |s94Gt X0 C u t ζ| ≤ Ag := fun ζ => by
    unfold s94Gt
    exact s94_abs_pair_empirical_le hN0 (X0 t.toNNReal ζ) hAg
  have hxi : Measurable fun ζ => r2EmpFluct μ (s94gt C u t) X0 ζ t :=
    measurable_const.mul (hGm.sub measurable_const)
  have hsq : ∫ ζ, (s94Gt X0 C u t ζ - Whole.pair μ (s94gt C u t)) ^ 2 ∂P0 =
      (N : ℝ)⁻¹ * ∫ ζ, (r2EmpFluct μ (s94gt C u t) X0 ζ t) ^ 2 ∂P0 := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun ζ => ?_)
    show _ = (N : ℝ)⁻¹ * (Real.sqrt N * (s94Gt X0 C u t ζ - Whole.pair μ (s94gt C u t))) ^ 2
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    field_simp
  have hint2 : ∫ ζ, (r2EmpFluct μ (s94gt C u t) X0 ζ t) ^ 2 ∂P0 ≤ (|C1 * Ag|) ^ 2 := by
    have h2 : ENNReal.ofReal 2 = 2 := by norm_num
    rw [h2] at hLM
    exact s94_integral_sq_le_of_eLpNorm hxi.aestronglyMeasurable (abs_nonneg _)
      (hLM.trans (ENNReal.ofReal_le_ofReal (le_abs_self _)))
  have hvar := s94_var_le_shift (P0 := P0) hGm hGb (Whole.pair μ (s94gt C u t))
  have hR : ∀ ζ, (s94Rt X0 P0 C u t ζ) ^ 2 = (1 / 4) * (s94Gt X0 C u t ζ - ∫ ζ', s94Gt X0 C u t ζ' ∂P0) ^ 2 :=
    fun ζ => by unfold s94Rt; ring
  simp_rw [hR]
  rw [integral_const_mul]
  calc (1 / 4) * ∫ ζ, (s94Gt X0 C u t ζ - ∫ ζ', s94Gt X0 C u t ζ' ∂P0) ^ 2 ∂P0
      ≤ (1 / 4) * ∫ ζ, (s94Gt X0 C u t ζ - Whole.pair μ (s94gt C u t)) ^ 2 ∂P0 := by gcongr
    _ = (1 / 4) * ((N : ℝ)⁻¹ * ∫ ζ, (r2EmpFluct μ (s94gt C u t) X0 ζ t) ^ 2 ∂P0) := by rw [hsq]
    _ ≤ (1 / 4) * ((N : ℝ)⁻¹ * (|C1 * Ag|) ^ 2) := by gcongr
    _ = (|C1 * Ag|) ^ 2 / (4 * N) := by field_simp

theorem s94Rt_abs_le {N : ℕ} (hN0 : 0 < N) {Ω0 : Type*}
    [MeasurableSpace Ω0] (X0 : ℝ≥0 → Ω0 → EucConfig d N) (P0 : Measure Ω0) [IsProbabilityMeasure P0]
    {C : ℝ → Fin n → Fin n → ℝ} {u : Fin n → Euc d → ℝ} {Ag : ℝ} (hAg : ∀ t x, |s94gt C u t x| ≤ Ag) (t : ℝ) (ζ : Ω0) :
    |s94Rt X0 P0 C u t ζ| ≤ Ag := by
  have hbdG : ∀ ζ, |s94Gt X0 C u t ζ| ≤ Ag := fun ζ => by
    unfold s94Gt; exact s94_abs_pair_empirical_le hN0 (X0 t.toNNReal ζ) (hAg t)
  have hbdI : |∫ ζ', s94Gt X0 C u t ζ' ∂P0| ≤ Ag := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := Ag) (ae_of_all _ fun ζ => ?_)).trans (by simp)
    simpa using hbdG ζ
  unfold s94Rt
  rw [abs_mul]
  have : |s94Gt X0 C u t ζ - ∫ ζ', s94Gt X0 C u t ζ' ∂P0| ≤ 2 * Ag :=
    (abs_sub _ _).trans (by linarith [hbdG ζ])
  have h2 : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
  rw [h2]; linarith

theorem s94_R_small {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {T : ℝ} (hT : 0 ≤ T) {Ω0 : ℕ → Type}
    [∀ N, MeasurableSpace (Ω0 N)] {P0 : ∀ N, Measure (Ω0 N)} [∀ N, IsProbabilityMeasure (P0 N)]
    {X0 : ∀ N, ℝ≥0 → Ω0 N → EucConfig d N} (hX : ∀ N, Measurable fun q : ℝ≥0 × Ω0 N => X0 N q.1 q.2)
    {C : ℝ → Fin n → Fin n → ℝ} (hC : ∀ a b, Measurable fun t => C t a b) {K0 : ℝ} (hK0 : 0 ≤ K0)
    (hCb : ∀ t a b, |C t a b| ≤ K0) {u : Fin n → Euc d → ℝ} (hu : ∀ a, IsR2Test (u a)) {C1 : ℝ}
    (hLM : ∀ N : ℕ, 2 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (a : Euc d → ℝ) (A : ℝ), Measurable a →
      (∀ x, |a x| ≤ A) → eLpNorm (fun ζ => r2EmpFluct μ a (X0 N) ζ t) (ENNReal.ofReal 2) (P0 N) ≤
        ENNReal.ofReal (C1 * A)) :
    ∃ Kr : ℝ, ∀ N : ℕ, 2 ≤ N → ∫⁻ ζ, ∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal ((s94Rt (X0 N) (P0 N) C u t ζ) ^ 2)
      ∂volume ∂(P0 N) ≤ ENNReal.ofReal (Kr / N) := by
  obtain ⟨Ag, hAg0, hAg⟩ := s94gt_abs_le (C := C) hK0 hCb hu
  refine ⟨T * (|C1 * Ag|) ^ 2 / 4, fun N hN => ?_⟩
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hRm := s94Rt_measurable hN0 (X0 N) (hX N) (P0 N) hC hu
  have hF : Measurable fun q : Ω0 N × ℝ => ENNReal.ofReal ((s94Rt (X0 N) (P0 N) C u q.2 q.1) ^ 2) :=
    ENNReal.measurable_ofReal.comp (((hRm.comp measurable_swap).pow_const 2))
  rw [lintegral_lintegral_swap hF.aemeasurable]
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫⁻ ζ, ENNReal.ofReal ((s94Rt (X0 N) (P0 N) C u t ζ) ^ 2) ∂(P0 N) ≤
      ENNReal.ofReal ((|C1 * Ag|) ^ 2 / (4 * N)) := by
    intro t ht
    have hRt : Measurable fun ζ => s94Rt (X0 N) (P0 N) C u t ζ :=
      Measurable.comp (g := fun q : ℝ × Ω0 N => s94Rt (X0 N) (P0 N) C u q.1 q.2) (f := fun ζ : Ω0 N => (t, ζ))
        hRm measurable_prodMk_left
    have hbdG : ∀ ζ, |s94Gt (X0 N) C u t ζ| ≤ Ag := fun ζ => by
      unfold s94Gt; exact s94_abs_pair_empirical_le hN0 (X0 N t.toNNReal ζ) (hAg t)
    have hbdI : |∫ ζ', s94Gt (X0 N) C u t ζ' ∂(P0 N)| ≤ Ag := by
      rw [← Real.norm_eq_abs]
      refine (norm_integral_le_of_norm_le_const (C := Ag) (ae_of_all _ fun ζ => ?_)).trans (by simp)
      simpa using hbdG ζ
    have hRb : ∀ ζ, |s94Rt (X0 N) (P0 N) C u t ζ| ≤ Ag := fun ζ => by
      unfold s94Rt
      rw [abs_mul]
      have : |s94Gt (X0 N) C u t ζ - ∫ ζ', s94Gt (X0 N) C u t ζ' ∂(P0 N)| ≤ 2 * Ag :=
        (abs_sub _ _).trans (by linarith [hbdG ζ])
      have h2 : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
      rw [h2]; linarith
    have hint : Integrable (fun ζ => (s94Rt (X0 N) (P0 N) C u t ζ) ^ 2) (P0 N) :=
      Integrable.of_bound (hRt.pow_const 2).aestronglyMeasurable (Ag ^ 2)
        (ae_of_all _ fun ζ => by
          rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hRb ζ) 2)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ζ => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (s94_Rt_sq_le hN (X0 N) (hX N) (P0 N) hC hu (t := t) (Ag := Ag)
      (hAg t) (hLM N hN t ht _ Ag (s94gt_measurable hC hu |>.comp measurable_prodMk_left) (hAg t)))
  calc ∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ ζ, ENNReal.ofReal ((s94Rt (X0 N) (P0 N) C u t ζ) ^ 2) ∂(P0 N)
      ≤ ∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal ((|C1 * Ag|) ^ 2 / (4 * N)) :=
        setLIntegral_mono measurable_const hpt
    _ = ENNReal.ofReal (T * (|C1 * Ag|) ^ 2 / 4 / N) := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; field_simp

end Resid

end HRS.MS.R2Chaos
