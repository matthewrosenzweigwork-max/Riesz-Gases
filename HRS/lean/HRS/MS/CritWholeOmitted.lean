import HRS.MS.CritWholeFullDensity
import HRS.MS.CritWholeCondKernel
import HRS.MS.CritWholeOmittedNum

/-!
# S8.1 XS (S81c), CR04: `L^1` bound of the omitted field `v_Y(y)` under the pole law

Capped decomposition `g = g_H + tail_H`, `H = 2 √N`: the centred capped sum has variance `≤ C N log H` (pole variance +
truncation rows), the tails and the mean are controlled by the bounded relative marginal density of CR02.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole HRS.MS.Wr

namespace HRS.Whole.S81b

variable {d : ℕ} {M βm βp : ℝ}

/-- `E|X - EX| ≤ √Var X` for a bounded measurable variable on a probability space. -/
theorem s81c_L1_var {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) {B : ℝ} (hB : ∀ ω, |X ω| ≤ B) :
    ∫ ω, |X ω - ∫ ω', X ω' ∂P| ∂P ≤ Real.sqrt (variance X P) := by
  have hXm : MemLp X 2 P := MemLp.of_bound hX.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hB ω)
  set Z : Ω → ℝ := fun ω => X ω - ∫ ω', X ω' ∂P with hZ
  have hZm : MemLp Z 2 P := hXm.sub (memLp_const _)
  have hZa : MemLp (fun ω => |Z ω|) 2 P := hZm.abs
  have h1 := variance_eq_sub hZa
  have h2 := variance_nonneg (fun ω => |Z ω|) P
  have h3 : variance X P = ∫ ω, Z ω ^ 2 ∂P := variance_eq_integral hX.aemeasurable
  have h4 : P[(fun ω => |Z ω|) ^ 2] = ∫ ω, Z ω ^ 2 ∂P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp [sq_abs]
  rw [h4] at h1
  have h5 : (∫ ω, |Z ω| ∂P) ^ 2 ≤ variance X P := by
    rw [h3]; linarith
  rw [← Real.sqrt_sq (integral_nonneg fun ω => abs_nonneg (Z ω))]
  exact Real.sqrt_le_sqrt h5

/-- Abstract `L^1` estimate of an affine functional of `n-1` capped-plus-tail variables. -/
theorem s81c_affine_l1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (i : Fin n) (Hh Tt : Fin n → Ω → ℝ) (hHm : ∀ j, Measurable (Hh j)) (hTm : ∀ j, Measurable (Tt j))
    {H : ℝ} (hH : 0 ≤ H) (hH0 : ∀ j ω, 0 ≤ Hh j ω) (hHle : ∀ j ω, Hh j ω ≤ H) (hT0 : ∀ j ω, 0 ≤ Tt j ω)
    (hTi : ∀ j, Integrable (Tt j) P) {mh mt : ℝ} (hmh : ∀ j, ∫ ω, Hh j ω ∂P = mh)
    (hmt : ∀ j, ∫ ω, Tt j ω ∂P = mt) {V : ℝ} (hV : variance (fun ω => ∑ j, Hh j ω) P ≤ V)
    {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    Integrable (fun ω => a * ∑ j ∈ Finset.univ.erase i, (Hh j ω + Tt j ω) - b) P ∧
      ∫ ω, |a * ∑ j ∈ Finset.univ.erase i, (Hh j ω + Tt j ω) - b| ∂P ≤
        a * (Real.sqrt V + H) + 2 * a * ((n - 1 : ℕ) : ℝ) * mt +
          |a * (((n - 1 : ℕ) : ℝ) * (mh + mt)) - b| := by
  set J : Finset (Fin n) := Finset.univ.erase i with hJ
  have hcard : (J.card : ℝ) = ((n - 1 : ℕ) : ℝ) := by
    rw [hJ, Finset.card_erase_of_mem (Finset.mem_univ i)]; simp
  have hHi : ∀ j, Integrable (Hh j) P := fun j =>
    Integrable.of_bound (C := H) (hHm j).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hH0 j ω)]; exact hHle j ω)
  have hmh0 : 0 ≤ mh ∧ mh ≤ H := by
    have h := hmh i
    refine ⟨?_, ?_⟩
    · rw [← h]; exact integral_nonneg (hH0 i)
    · rw [← h]
      calc ∫ ω, Hh i ω ∂P ≤ ∫ _ω, H ∂P := integral_mono (hHi i) (integrable_const H) (hHle i)
        _ = H := by simp
  have hmt0 : 0 ≤ mt := by rw [← hmt i]; exact integral_nonneg (hT0 i)
  set S : Ω → ℝ := fun ω => ∑ j, Hh j ω with hS
  have hSm : Measurable S := Finset.measurable_sum _ fun j _ => hHm j
  have hSb : ∀ ω, |S ω| ≤ n * H := fun ω => by
    rw [abs_of_nonneg (Finset.sum_nonneg fun j _ => hH0 j ω)]
    calc S ω ≤ ∑ _j : Fin n, H := Finset.sum_le_sum fun j _ => hHle j ω
      _ = n * H := by simp
  have hSint : ∫ ω, S ω ∂P = n * mh := by
    rw [hS]; simp only
    rw [integral_finset_sum _ fun j _ => hHi j]
    simp [hmh]
  set U : Ω → ℝ := fun ω => a * ∑ j ∈ J, (Hh j ω - mh) with hU
  set W : Ω → ℝ := fun ω => a * ∑ j ∈ J, Tt j ω with hW
  set c0 : ℝ := a * ((J.card : ℝ) * mh) - b with hc0
  have hdec : ∀ ω, a * ∑ j ∈ J, (Hh j ω + Tt j ω) - b = U ω + W ω + c0 := fun ω => by
    simp only [hU, hW, hc0, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  have hUi : Integrable U P := by
    refine Integrable.const_mul (integrable_finset_sum _ fun j _ => (hHi j).sub (integrable_const _)) _
  have hWi : Integrable W P := Integrable.const_mul (integrable_finset_sum _ fun j _ => hTi j) _
  have hint : Integrable (fun ω => a * ∑ j ∈ J, (Hh j ω + Tt j ω) - b) P := by
    have : (fun ω => a * ∑ j ∈ J, (Hh j ω + Tt j ω) - b) = fun ω => U ω + W ω + c0 := funext hdec
    rw [this]; exact (hUi.add hWi).add (integrable_const _)
  refine ⟨hint, ?_⟩
  have hW0 : ∀ ω, 0 ≤ W ω := fun ω => mul_nonneg ha (Finset.sum_nonneg fun j _ => hT0 j ω)
  -- the bound on ∫ |U|
  have hUbd : ∫ ω, |U ω| ∂P ≤ a * (Real.sqrt V + H) := by
    have hpt : ∀ ω, |U ω| ≤ a * |S ω - ∫ ω', S ω' ∂P| + a * H := fun ω => by
      have e : ∑ j ∈ J, (Hh j ω - mh) = (S ω - ∫ ω', S ω' ∂P) - (Hh i ω - mh) := by
        rw [hSint, hJ, Finset.sum_erase_eq_sub (Finset.mem_univ i), Finset.sum_sub_distrib, hS]
        simp
      have h1 : |Hh i ω - mh| ≤ H := by
        rw [abs_le]; constructor <;> linarith [hH0 i ω, hHle i ω, hmh0.1, hmh0.2]
      simp only [hU, e]
      rw [abs_mul, abs_of_nonneg ha]
      calc a * |S ω - ∫ ω', S ω' ∂P - (Hh i ω - mh)| ≤ a * (|S ω - ∫ ω', S ω' ∂P| + |Hh i ω - mh|) :=
            mul_le_mul_of_nonneg_left (abs_sub _ _) ha
        _ ≤ _ := by nlinarith [abs_nonneg (S ω - ∫ ω', S ω' ∂P)]
    have hSL1 := s81c_L1_var P hSm hSb
    have hSL1' : ∫ ω, |S ω - ∫ ω', S ω' ∂P| ∂P ≤ Real.sqrt V :=
      hSL1.trans (Real.sqrt_le_sqrt hV)
    have hSi : Integrable (fun ω => |S ω - ∫ ω', S ω' ∂P|) P :=
      (Integrable.of_bound (C := n * H) hSm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
        simpa [Real.norm_eq_abs] using hSb ω)).sub (integrable_const _) |>.abs
    calc ∫ ω, |U ω| ∂P ≤ ∫ ω, (a * |S ω - ∫ ω', S ω' ∂P| + a * H) ∂P :=
          integral_mono hUi.abs ((hSi.const_mul a).add (integrable_const _)) hpt
      _ = a * ∫ ω, |S ω - ∫ ω', S ω' ∂P| ∂P + a * H := by
          rw [integral_add (hSi.const_mul a) (integrable_const _), integral_const_mul]; simp
      _ ≤ a * Real.sqrt V + a * H := by gcongr
      _ = _ := by ring
  have hWint : ∫ ω, W ω ∂P = a * (J.card * mt) := by
    simp only [hW]
    rw [integral_const_mul, integral_finset_sum _ fun j _ => hTi j]
    simp [hmt]
  have hmain : ∫ ω, |a * ∑ j ∈ J, (Hh j ω + Tt j ω) - b| ∂P ≤ ∫ ω, (|U ω| + W ω + |c0|) ∂P := by
    refine integral_mono hint.abs ((hUi.abs.add hWi).add (integrable_const _)) fun ω => ?_
    rw [hdec ω]
    calc |U ω + W ω + c0| ≤ |U ω + W ω| + |c0| := abs_add_le _ _
      _ ≤ |U ω| + |W ω| + |c0| := by gcongr; exact abs_add_le _ _
      _ = _ := by rw [abs_of_nonneg (hW0 ω)]
  refine hmain.trans ?_
  rw [integral_add (f := fun ω => |U ω| + W ω) (g := fun _ => |c0|) (hUi.abs.add hWi) (integrable_const _),
    integral_add (f := fun ω => |U ω|) (g := W) hUi.abs hWi, hWint]
  have hcc : ∫ _ω, |c0| ∂P = |c0| := by simp
  rw [hcc]
  have hc0b : |c0| ≤ |a * (((n - 1 : ℕ) : ℝ) * (mh + mt)) - b| + a * ((n - 1 : ℕ) : ℝ) * mt := by
    have : c0 = (a * (((n - 1 : ℕ) : ℝ) * (mh + mt)) - b) - a * ((n - 1 : ℕ) : ℝ) * mt := by
      rw [hc0, hcard]; ring
    rw [this]
    calc |(a * (((n - 1 : ℕ) : ℝ) * (mh + mt)) - b) - a * ((n - 1 : ℕ) : ℝ) * mt| ≤
        |a * (((n - 1 : ℕ) : ℝ) * (mh + mt)) - b| + |a * ((n - 1 : ℕ) : ℝ) * mt| := abs_sub _ _
      _ = _ := by rw [abs_of_nonneg (mul_nonneg (mul_nonneg ha (Nat.cast_nonneg _)) hmt0)]
  rw [hcard]
  nlinarith [hUbd, hc0b]

theorem s81c_delta_eq (hd : 1 ≤ d) {N : ℕ} (hN : 2 ≤ N) :
    deltaN d ((d : ℝ) / 2) N = (N : ℝ)⁻¹ * (1 + Real.log N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hδ : deltaN d ((d : ℝ) / 2) N = (N : ℝ)⁻¹ * Real.log (Real.exp 1 * N) := by
    simp only [deltaN, lt_self_iff_false, if_false, if_true]
  rw [hδ, Real.log_mul (Real.exp_pos _).ne' hN0.ne', Real.log_exp]

/-- Numerical facts relating `δ_N`, `H = 2 √N` and `log H`. -/
theorem s81c_num_facts (hd : 1 ≤ d) {N : ℕ} (hN : 2 ≤ N) :
    (N : ℝ)⁻¹ ≤ deltaN d ((d : ℝ) / 2) N ∧ deltaN d ((d : ℝ) / 2) N ≤ 1 ∧
      Real.log (2 * Real.sqrt N) / N ≤ deltaN d ((d : ℝ) / 2) N ∧
      Real.log (2 * Real.sqrt N) * deltaN d ((d : ℝ) / 2) N ≤ 5 ∧ 0 ≤ Real.log (2 * Real.sqrt N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  obtain ⟨h1, h2⟩ := s81b_delta_facts hd hN
  rw [one_div] at h1
  have hδ := s81c_delta_eq hd hN
  have hsq : Real.sqrt N ≤ N := by
    rw [Real.sqrt_le_left hN0.le]; nlinarith
  have hsq0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hL1 : Real.log (2 * Real.sqrt N) ≤ 1 + Real.log N := by
    rw [Real.log_mul (by norm_num) hsq0.ne', Real.log_sqrt hN0.le]
    have : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9; linarith
    linarith
  have hL0 : 0 ≤ Real.log (2 * Real.sqrt N) := by
    refine Real.log_nonneg ?_
    have : 1 ≤ Real.sqrt N := by rw [Real.one_le_sqrt]; linarith
    linarith
  have hδ1 : deltaN d ((d : ℝ) / 2) N ≤ 1 := by
    rw [hδ, ← div_eq_inv_mul, div_le_one hN0]
    have := Real.log_le_sub_one_of_pos hN0
    linarith
  refine ⟨h1, hδ1, ?_, ?_, hL0⟩
  · rw [hδ, ← div_eq_inv_mul]
    exact div_le_div_of_nonneg_right hL1 hN0.le
  · calc Real.log (2 * Real.sqrt N) * deltaN d ((d : ℝ) / 2) N ≤ (1 + Real.log N) * deltaN d ((d : ℝ) / 2) N :=
          mul_le_mul_of_nonneg_right hL1 (h1.trans' (by positivity))
      _ = deltaN d ((d : ℝ) / 2) N + deltaN d ((d : ℝ) / 2) N * Real.log N := by ring
      _ ≤ 5 := by linarith

/-- Every coordinate of the pole law has the first marginal as its law. -/
theorem s81c_marg_coord (hd : 1 ≤ d) (D : Data d M βm βp) (hβ0 : 0 ≤ D.beta) {N : ℕ} (hN : 2 ≤ N) (x : Euc d)
    {t : ℝ} (ht : 0 ≤ t) (j : Fin (N - 1)) :
    (pole D N x t).map (fun Y => Y j) = firstMarginal (pole D N x t) := by
  haveI := s81c_prob D
  have hpos : 0 < N - 1 := by omega
  have hex := wr13b_poleLaw_exchangeable (s81c_hs0 hd) (s81c_conv_le hd D) hβ0 ht N x
  unfold firstMarginal
  simp only [hpos, dite_true]
  exact hex.marginal_eq j ⟨0, hpos⟩

/-- Pole variance of the capped sum `∑_j g_H(y - Y_j)`. -/
theorem s81c_var_cap (hd : 2 ≤ d) (M βm βp : ℝ) (hβm : 0 < βm) (hβ : βm ≤ βp) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D : Data d M βm βp, ∀ N : ℕ, 2 ≤ N → ∀ x : Euc d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ y : Euc d, ∀ H : ℝ, 2 ≤ H →
        variance (fun Y : EucConfig d (N - 1) => ∑ j, truncKernel d ((d : ℝ) / 2) H (y - Y j)) (pole D N x t) ≤
          C * ((N - 1 : ℕ) : ℝ) * Real.log H := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Cv, hCv0, hCv⟩ := wr13b_pole_variance hd (s81c_hs0 hd1) (s81c_hsd hd1) βp M
  obtain ⟨Cr, hCr0, hCr⟩ := s81b_critical_truncation_rows hd M
  refine ⟨Cv * Cr, by positivity, fun D N hN x t ht y H hH => ?_⟩
  haveI := s81c_prob D
  have hβ0 : 0 < D.beta := hβm.trans_le D.beta_mem.1
  have hH0 : 0 < H := by linarith
  set f : Euc d → ℝ := fun z => truncKernel d ((d : ℝ) / 2) H (y - z) with hf
  have hfm : Measurable f := (s81b_trunc_meas hd1 H).comp (measurable_const.sub measurable_id)
  have hf0 : ∀ z, 0 ≤ f z := fun z => le_min (s81b_critG_nonneg hd1 _) hH0.le
  have hev := hCv D.rho D.prob D.bound D.beta hβ0 D.beta_mem.2 N hN x t ht f hfm
  obtain ⟨-, hTr2, -, hSq⟩ := hCr D.rho D.prob D.bound H hH y
  have hint : ∫⁻ z, ‖f z‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-(t * (D.beta / N)) * rieszKernel d ((d : ℝ) / 2) (x - z)))
      ∂(withDensityReal D.rho) ≤ ENNReal.ofReal (Cr * Real.log H) := by
    calc _ ≤ ∫⁻ z, ENNReal.ofReal (f z ^ 2) ∂(withDensityReal D.rho) := by
          refine lintegral_mono fun z => ?_
          have h1 : ENNReal.ofReal (Real.exp (-(t * (D.beta / N)) * rieszKernel d ((d : ℝ) / 2) (x - z))) ≤ 1 := by
            rw [ENNReal.ofReal_le_one]
            exact s81c_poleFactor_le_one hd1 D hβ0.le N x ht.1 z
          calc ‖f z‖ₑ ^ 2 * ENNReal.ofReal _ ≤ ‖f z‖ₑ ^ 2 * 1 := by gcongr
            _ = ENNReal.ofReal (f z ^ 2) := by
                rw [mul_one, ← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
      _ = ENNReal.ofReal (∫ z, f z ^ 2 ∂(withDensityReal D.rho)) :=
          (ofReal_integral_eq_lintegral_ofReal hTr2 (Filter.Eventually.of_forall fun z => sq_nonneg _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hSq
  haveI := s81c_pole_prob hd1 D hβ0.le N x ht.1
  have hmem : MemLp (fun Y : EucConfig d (N - 1) => ∑ j, f (Y j)) 2 (pole D N x t) := by
    refine MemLp.of_bound (Finset.measurable_sum _ fun j _ => hfm.comp (measurable_pi_apply j)).aestronglyMeasurable
      ((N - 1 : ℕ) * H) (Filter.Eventually.of_forall fun Y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun j _ => hf0 _)]
    calc ∑ j, f (Y j) ≤ ∑ _j : Fin (N - 1), H := Finset.sum_le_sum fun j _ => min_le_right _ _
      _ = _ := by simp
  have hv := hmem.evariance_ne_top
  have hle : evariance (fun Y : EucConfig d (N - 1) => ∑ j, f (Y j)) (pole D N x t) ≤
      ENNReal.ofReal (Cv * ((N - 1 : ℕ) : ℝ) * (Cr * Real.log H)) := by
    rw [ENNReal.ofReal_mul (by positivity)]
    exact hev.trans (mul_le_mul' le_rfl hint)
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rw [ENNReal.toReal_ofReal (by
    have : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
    positivity)] at this
  unfold variance
  calc _ ≤ _ := this
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
theorem s81c_omitted_field_L1 (hd : 2 ≤ d) (M βm βp : ℝ) (hβm : 0 < βm) (hβ : βm ≤ βp) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D : Data d M βm βp, ∀ N : ℕ, 2 ≤ N →
      ∀ i : Fin (N - 1), ∀ x : Euc d, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y : Euc d,
        Integrable (fun Y => field D N i Y y) (pole D N x t) ∧
        (∫ Y, |field D N i Y y| ∂(pole D N x t)) ≤ C * Real.sqrt (deltaN d ((d : ℝ) / 2) N) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Cq, hCq1, hCq⟩ := s81b_cavity_relative_L2 hd M βm βp hβm hβ
  obtain ⟨Cr, hCr0, hCr⟩ := s81b_critical_truncation_rows hd M
  obtain ⟨Cv, hCv0, hCv⟩ := s81c_var_cap hd M βm βp hβm hβ
  obtain ⟨Cc, hCc0, hCc⟩ := s81b_conv_L2_bound hd M
  set Mg : ℝ := |potentialBound d ((d : ℝ) / 2) M| with hMg
  have hβp : 0 < βp := hβm.trans_le hβ
  refine ⟨βp * (Real.sqrt Cv + 2 + Cq * Cr + Real.sqrt Cc * Cq * Real.sqrt 5 + (Cq + 1) * Cc / 2 + 2 * Mg),
    by positivity, fun D N hN i x t ht y => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  haveI := s81c_prob D
  have hβ0 : 0 < D.beta := hβm.trans_le D.beta_mem.1
  have hββp : D.beta ≤ βp := D.beta_mem.2
  obtain ⟨P, hP⟩ : ∃ P : Measure (EucConfig d (m + 1)), P = pole D (m + 2) x t := ⟨_, rfl⟩
  rw [← hP]
  have hPprob : IsProbabilityMeasure P := by rw [hP]; exact s81c_pole_prob hd1 D hβ0.le _ x ht.1
  -- numerical constants
  obtain ⟨hn1, hn2, hn3, hn4, hn5⟩ := s81c_num_facts hd1 hN
  set δ : ℝ := deltaN d ((d : ℝ) / 2) (m + 2) with hδ
  set H : ℝ := 2 * Real.sqrt ((m + 2 : ℕ) : ℝ) with hH
  set L : ℝ := Real.log H with hL
  have hN0 : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
  have hsq0 : 0 < Real.sqrt ((m + 2 : ℕ) : ℝ) := Real.sqrt_pos.2 hN0
  have hH2 : 2 ≤ H := by
    have : 1 ≤ Real.sqrt ((m + 2 : ℕ) : ℝ) := by
      rw [Real.one_le_sqrt]; exact_mod_cast (by omega : 1 ≤ m + 2)
    rw [hH]; linarith
  have hH0 : 0 < H := by linarith
  -- the density of the first marginal
  obtain ⟨q, -, -, -, -, -, -, -, hpole⟩ := hCq D (m + 2) hN
  obtain ⟨φ, hφm, hφeq, hφ0, hφL2, hφn⟩ := hpole x t ht
  have hcoord : ∀ j : Fin (m + 1), P.map (fun Y => Y j) = (mu D).withDensity (fun z => ENNReal.ofReal (φ z)) := by
    intro j
    have h := s81c_marg_coord hd1 D hβ0.le hN x ht.1 j
    rw [hP]
    exact h.trans hφeq
  have hcoordint : ∀ (j : Fin (m + 1)) (ψ : Euc d → ℝ), Measurable ψ →
      ∫ Y, ψ (Y j) ∂P = ∫ z, φ z * ψ z ∂(mu D) := by
    intro j ψ hψ
    rw [← integral_map (measurable_pi_apply j).aemeasurable hψ.aestronglyMeasurable, hcoord j,
      s81b_integral_withDensity hφm (fun z => (hφ0 z).1)]
  -- capped and tail variables
  set Hh : Fin (m + 1) → EucConfig d (m + 1) → ℝ := fun j Y => truncKernel d ((d : ℝ) / 2) H (y - Y j) with hHh
  set Tt : Fin (m + 1) → EucConfig d (m + 1) → ℝ := fun j Y => tailG d H (y - Y j) with hTt
  have hHm : ∀ j, Measurable (Hh j) := fun j =>
    (s81b_trunc_meas hd1 H).comp (measurable_const.sub (measurable_pi_apply j))
  have hTm : ∀ j, Measurable (Tt j) := fun j =>
    (s81b_tailG_meas hd1 H).comp (measurable_const.sub (measurable_pi_apply j))
  have hg0 : ∀ z, 0 ≤ critG d z := s81b_critG_nonneg hd1
  have hHnn : ∀ j Y, 0 ≤ Hh j Y := fun j Y => le_min (hg0 _) hH0.le
  have hHle : ∀ j Y, Hh j Y ≤ H := fun j Y => min_le_right _ _
  have hT0 : ∀ j Y, 0 ≤ Tt j Y := fun j Y => s81b_tailG_nonneg hd1 H hH0.le _
  obtain ⟨hTailI, hSqI, hTail, hSq⟩ := hCr D.rho D.prob D.bound H hH2 y
  have hνle : (mu D).withDensity (fun z => ENNReal.ofReal (φ z)) ≤ ENNReal.ofReal Cq • mu D := by
    have : (mu D).withDensity (fun z => ENNReal.ofReal (φ z)) ≤ (mu D).withDensity (fun _ => ENNReal.ofReal Cq) :=
      withDensity_mono (Filter.Eventually.of_forall fun z => ENNReal.ofReal_le_ofReal (hφ0 z).2)
    rwa [withDensity_const] at this
  have hTi : ∀ j, Integrable (Tt j) P := fun j => by
    have hI : Integrable (fun z => tailG d H (y - z)) ((mu D).withDensity (fun z => ENNReal.ofReal (φ z))) :=
      (hTailI.smul_measure (c := ENNReal.ofReal Cq) ENNReal.ofReal_ne_top).mono_measure hνle
    rw [← hcoord j] at hI
    exact (integrable_map_measure ((s81b_tailG_meas hd1 H).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      (measurable_pi_apply j).aemeasurable).1 hI
  set mh : ℝ := ∫ z, φ z * truncKernel d ((d : ℝ) / 2) H (y - z) ∂(mu D) with hmhdef
  set mt : ℝ := ∫ z, φ z * tailG d H (y - z) ∂(mu D) with hmtdef
  have hmh : ∀ j, ∫ Y, Hh j Y ∂P = mh := fun j =>
    hcoordint j (fun z => truncKernel d ((d : ℝ) / 2) H (y - z))
      ((s81b_trunc_meas hd1 H).comp (measurable_const.sub measurable_id))
  have hmt : ∀ j, ∫ Y, Tt j Y ∂P = mt := fun j =>
    hcoordint j (fun z => tailG d H (y - z))
      ((s81b_tailG_meas hd1 H).comp (measurable_const.sub measurable_id))
  have hvar : variance (fun Y : EucConfig d (m + 1) => ∑ j, Hh j Y) P ≤ Cv * ((m + 1 : ℕ) : ℝ) * L := by
    rw [hP]; exact hCv D (m + 2) hN x t ht y H hH2
  have hlam : 0 ≤ D.beta / ((m + 2 : ℕ) : ℝ) := by positivity
  have hA := s81c_affine_l1 P i Hh Tt hHm hTm hH0.le hHnn hHle hT0 hTi hmh hmt hvar hlam
    (D.beta * convMeasure (critG d) (mu D) y)
  have hfield : ∀ Y : EucConfig d (m + 1), field D (m + 2) i Y y =
      D.beta / ((m + 2 : ℕ) : ℝ) * ∑ j ∈ Finset.univ.erase i, (Hh j Y + Tt j Y) -
        D.beta * convMeasure (critG d) (mu D) y := by
    intro Y
    unfold field
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hHh, hTt, tailG]; ring
  have hI : Integrable (fun Y : EucConfig d (m + 1) => field D (m + 2) i Y y) P := by
    simp only [hfield]; exact hA.1
  have hJ : ∫ Y : EucConfig d (m + 1), |field D (m + 2) i Y y| ∂P ≤
      D.beta / ((m + 2 : ℕ) : ℝ) * (Real.sqrt (Cv * ((m + 1 : ℕ) : ℝ) * L) + H) +
        2 * (D.beta / ((m + 2 : ℕ) : ℝ)) * ((m + 1 - 1 : ℕ) : ℝ) * mt +
        |D.beta / ((m + 2 : ℕ) : ℝ) * (((m + 1 - 1 : ℕ) : ℝ) * (mh + mt)) -
          D.beta * convMeasure (critG d) (mu D) y| := by
    simp only [hfield]; exact hA.2
  refine ⟨hI, hJ.trans ?_⟩
  -- the mean and tail estimates
  have hgI : Integrable (fun z => critG d (y - z)) (mu D) :=
    (wr13a_potential_bound hd1 (s81c_hs0 hd1) (s81c_hsd hd1) D.prob D.bound y).1
  have hφb : ∀ z, |φ z| ≤ Cq := fun z => by rw [abs_of_nonneg (hφ0 z).1]; exact (hφ0 z).2
  have hφtail : Integrable (fun z => φ z * tailG d H (y - z)) (mu D) := by
    refine Integrable.mono' (hTailI.const_mul Cq)
      (hφm.mul ((s81b_tailG_meas hd1 H).comp (measurable_const.sub measurable_id))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (s81b_tailG_nonneg hd1 H hH0.le _)]
    exact mul_le_mul_of_nonneg_right (hφb z) (s81b_tailG_nonneg hd1 H hH0.le _)
  have hφtrunc : Integrable (fun z => φ z * truncKernel d ((d : ℝ) / 2) H (y - z)) (mu D) := by
    refine Integrable.of_bound (C := Cq * H)
      (hφm.mul ((s81b_trunc_meas hd1 H).comp (measurable_const.sub measurable_id))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg
      (show 0 ≤ truncKernel d ((d : ℝ) / 2) H (y - z) from le_min (hg0 _) hH0.le)]
    exact mul_le_mul (hφb z) (min_le_right _ _) (le_min (hg0 _) hH0.le) (by linarith)
  have hmt0 : 0 ≤ mt := integral_nonneg fun z => mul_nonneg (hφ0 z).1 (s81b_tailG_nonneg hd1 H hH0.le _)
  have hmtb : mt ≤ Cq * (Cr / H) := by
    calc mt ≤ ∫ z, Cq * tailG d H (y - z) ∂(mu D) :=
          integral_mono hφtail (hTailI.const_mul Cq) fun z =>
            mul_le_mul_of_nonneg_right (hφ0 z).2 (s81b_tailG_nonneg hd1 H hH0.le _)
      _ = Cq * ∫ z, tailG d H (y - z) ∂(mu D) := integral_const_mul _ _
      _ ≤ Cq * (Cr / H) := mul_le_mul_of_nonneg_left hTail (by linarith)
  have hS : |(mh + mt) - convMeasure (critG d) (mu D) y| ≤
      Real.sqrt (Cc * L) * (Cq * δ) + (Cq + 1) * (Cc / H) := by
    have e : (mh + mt) - convMeasure (critG d) (mu D) y = ∫ z, critG d (y - z) * (φ z - 1) ∂(mu D) := by
      have h1 : mh + mt = ∫ z, (φ z * truncKernel d ((d : ℝ) / 2) H (y - z) + φ z * tailG d H (y - z)) ∂(mu D) :=
        (integral_add hφtrunc hφtail).symm
      have h2 := integral_sub (f := fun z => φ z * truncKernel d ((d : ℝ) / 2) H (y - z) + φ z * tailG d H (y - z))
        (g := fun z => critG d (y - z)) (hφtrunc.add hφtail) hgI
      have h3 : ∫ z, critG d (y - z) * (φ z - 1) ∂(mu D) =
          ∫ z, ((φ z * truncKernel d ((d : ℝ) / 2) H (y - z) + φ z * tailG d H (y - z)) - critG d (y - z)) ∂(mu D) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [tailG]; ring
      rw [h3, h2, h1]
      rfl
    rw [e]
    have hB : ∀ z, |φ z - 1| ≤ Cq + 1 := fun z => by
      rw [abs_le]; constructor <;> linarith [(hφ0 z).1, (hφ0 z).2]
    have := hCc D.rho D.prob D.bound H hH2 y (fun z => φ z - 1) (hφm.sub_const 1) (Cq + 1) hB
    refine this.trans ?_
    have hl : l2Norm (mu D) (fun z => φ z - 1) ≤ Cq * δ := hφn
    have := mul_le_mul_of_nonneg_left hl (Real.sqrt_nonneg (Cc * Real.log H))
    exact add_le_add this le_rfl
  have hc0 : 0 ≤ convMeasure (critG d) (mu D) y := wr13a_conv_nonneg (s81c_hs0 hd1) (mu D) y
  have hcMg : convMeasure (critG d) (mu D) y ≤ Mg := (s81c_conv_le hd1 D y).trans (le_abs_self _)
  exact s81c_omitted_numeric (m := m) hβ0 hββp hCv0 hCr0 hCq1 hCc0 hc0 hcMg hmt0 hmtb hS hn1 hn2 hn3 hn4 hn5

end HRS.Whole.S81b
