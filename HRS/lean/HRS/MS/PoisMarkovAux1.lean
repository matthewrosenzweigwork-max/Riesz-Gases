import HRS.MS.PoisSgAux2
import HRS.MD.EQLawPath1

/-!
# POIS-MARKOV, part 1: the cocycle identity and locality of the pathwise flow

Setting (`PoisFlowAux1`): `flowMap q B w t x` is the pathwise flow of
`X_t = x + ∫_0^t (-q X_s + B X_s) ds + √2 w_t`, defined by choice of a global solution of the random ODE
for `Z = X - √2 U`.  Nothing below unfolds that choice: every identity is obtained from
`pf_flowMap_isPathSolution` and the pathwise uniqueness `ode_additive_unique`.

* `mkShift w a`: the shifted noise path `u ↦ w (a + u) - w a`.
* `mk_cocycle`: `flowMap w (a + b) x = flowMap (mkShift w a) b (flowMap w a x)` for `a : ℝ≥0`, `b ≥ 0`
  (under `PfHyp`).
* `mk_flow_stopped`: `flowMap` at time `t ≤ c` only depends on the noise on `[0, c]`:
  `flowMap (fun u => w (min u c)) t x = flowMap w t x` for `0 ≤ t ≤ c`.

Helper lemmas carry the prefix `mk_`.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.PoisFlow

noncomputable section

namespace HRS.MS.PoisMarkov

variable {d : ℕ}

/-- The shifted noise path `u ↦ w (a + u) - w a`. -/
def mkShift (w : ℝ≥0 → Fin d → ℝ) (a : ℝ≥0) : ℝ≥0 → Fin d → ℝ := fun u => w (a + u) - w a

theorem mk_shift_cont {w : ℝ≥0 → Fin d → ℝ} (hw : Continuous w) (a : ℝ≥0) :
    Continuous (mkShift w a) :=
  (hw.comp (continuous_const.add continuous_id)).sub continuous_const

theorem mk_shift_zero (w : ℝ≥0 → Fin d → ℝ) (a : ℝ≥0) : mkShift w a 0 = 0 := by
  simp [mkShift]

theorem mk_pfHyp_shift {q Mb : ℝ} {m : ℕ} {B : Euc d → Euc d} {w : ℝ≥0 → Fin d → ℝ}
    (H : PfHyp q Mb m B w) (a : ℝ≥0) : PfHyp q Mb m B (mkShift w a) :=
  ⟨H.hq, H.hm, H.hB, mk_shift_cont H.hw a, mk_shift_zero w a⟩

/-- The drift `y ↦ -q y + B y` is globally Lipschitz and continuous. -/
theorem mk_isLocLipschitz {q Mb : ℝ} {m : ℕ} {B : Euc d → Euc d} {w : ℝ≥0 → Fin d → ℝ}
    (H : PfHyp q Mb m B w) :
    IsLocLipschitzDrift Set.univ (fun (_ : ℝ) (y : Euc d) => -q • y + B y) where
  cont := by
    have : Continuous fun p : ℝ × Euc d => -q • p.2 + B p.2 :=
      (continuous_snd.const_smul (-q)).add (H.hB.1.continuous.comp continuous_snd)
    exact this.continuousOn
  lip K _ _ T := ⟨(q + |Mb|).toNNReal, fun t _ => (LipschitzWith.of_dist_le_mul fun z z' => by
    have hq := H.hq
    beta_reduce
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
    have e : (-q • z + B z) - (-q • z' + B z') = -q • (z - z') + (B z - B z') := by module
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖-q • (z - z')‖ = q * ‖z - z'‖ := by
      rw [norm_smul, norm_neg, Real.norm_of_nonneg hq]
    have h2 := pf_lip_of_cb H.hm H.hB z z'
    have h3 : Mb * ‖z - z'‖ ≤ |Mb| * ‖z - z'‖ :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
    nlinarith).lipschitzOnWith⟩

/-- `∫_{[0,a+b]} F - ∫_{[0,a]} F = ∫_{[0,b]} F(a + ·)` (with integrability). -/
theorem mk_shift_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hF : IntegrableOn F (Set.Icc 0 (a + b))) :
    IntegrableOn (fun r => F (a + r)) (Set.Icc 0 b) ∧
      (∫ r in Set.Icc (0 : ℝ) (a + b), F r) - (∫ r in Set.Icc (0 : ℝ) a, F r) =
        ∫ r in Set.Icc (0 : ℝ) b, F (a + r) := by
  have hab : (0 : ℝ) ≤ a + b := by linarith
  have hI : IntervalIntegrable F volume 0 (a + b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hF
  have hI1 : IntervalIntegrable F volume 0 a :=
    hI.mono_set (by
      rw [Set.uIcc_of_le hab, Set.uIcc_of_le ha]
      exact Set.Icc_subset_Icc le_rfl (by linarith))
  have hI2 : IntervalIntegrable F volume a (a + b) :=
    hI.mono_set (by
      rw [Set.uIcc_of_le hab, Set.uIcc_of_le (by linarith)]
      exact Set.Icc_subset_Icc ha le_rfl)
  have hI3 : IntervalIntegrable (fun r => F (a + r)) volume 0 b := by
    have := hI2.comp_add_left a
    simpa using this
  have hc : ∀ c : ℝ, 0 ≤ c → (∫ r in Set.Icc (0 : ℝ) c, F r) = ∫ r in (0 : ℝ)..c, F r := by
    intro c hc
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hc]
  have hc' : (∫ r in Set.Icc (0 : ℝ) b, F (a + r)) = ∫ r in (0 : ℝ)..b, F (a + r) := by
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hb]
  refine ⟨?_, ?_⟩
  · exact (integrableOn_Icc_iff_integrableOn_Ioc).2
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb).1 hI3)
  · rw [hc _ hab, hc _ ha, hc', intervalIntegral.integral_comp_add_left (fun r => F r) a]
    rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2]
    simp

/-- The time-shifted flow is a pathwise solution for the shifted noise, started at the flow at the
shift time. -/
theorem mk_shifted_isPathSolution {q Mb : ℝ} {m : ℕ} {B : Euc d → Euc d} {w : ℝ≥0 → Fin d → ℝ}
    (H : PfHyp q Mb m B w) (a : ℝ≥0) (x : Euc d) :
    IsPathSolution (fun (_ : ℝ) (y : Euc d) => -q • y + B y) (pfSigma d) (mkShift w a)
      (flowMap q B w (a : ℝ) x) ⊤ (fun u => flowMap q B w ((a : ℝ) + u) x) := by
  have hP := pf_flowMap_isPathSolution H x
  have ha0 : (0 : ℝ) ≤ a := a.coe_nonneg
  refine ⟨by simp, fun u hu _ => ?_⟩
  have hau : (0 : ℝ) ≤ (a : ℝ) + u := by linarith
  obtain ⟨hc1, hi1, he1⟩ := hP.2 ((a : ℝ) + u) hau (WithTop.coe_lt_top _)
  obtain ⟨hc2, hi2, he2⟩ := hP.2 (a : ℝ) ha0 (WithTop.coe_lt_top _)
  obtain ⟨hi3, hint⟩ := mk_shift_integral
    (fun r => -q • flowMap q B w r x + B (flowMap q B w r x)) ha0 hu hi1
  refine ⟨?_, hi3, ?_⟩
  · refine hc1.comp (continuous_const.add continuous_id).continuousOn fun r hr => ?_
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  · have hn1 : (((a : ℝ) + u).toNNReal) = a + u.toNNReal := by
      rw [Real.toNNReal_add ha0 hu, Real.toNNReal_coe]
    have hn2 : ((a : ℝ).toNNReal) = a := Real.toNNReal_coe
    rw [hn1] at he1
    rw [hn2] at he2
    simp only [mkShift, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
    beta_reduce at he1 he2
    rw [← hint, he1, he2]
    abel

/-- **Cocycle identity.**  `flowMap w (a + b) x = flowMap (θ_a w) b (flowMap w a x)`. -/
theorem mk_cocycle {q Mb : ℝ} {m : ℕ} {B : Euc d → Euc d} {w : ℝ≥0 → Fin d → ℝ}
    (H : PfHyp q Mb m B w) (a : ℝ≥0) {b : ℝ} (hb : 0 ≤ b) (x : Euc d) :
    flowMap q B w ((a : ℝ) + b) x = flowMap q B (mkShift w a) b (flowMap q B w (a : ℝ) x) := by
  have hX := mk_shifted_isPathSolution H a x
  have hY := pf_flowMap_isPathSolution (mk_pfHyp_shift H a) (flowMap q B w (a : ℝ) x)
  have := ode_additive_unique Set.univ isOpen_univ _ (mk_isLocLipschitz H) (pfSigma d) (mkShift w a)
    (mk_shift_cont H.hw a) _ hX hY (fun _ _ _ => Set.mem_univ _) (fun _ _ _ => Set.mem_univ _)
    b hb (by rw [min_self]; exact WithTop.coe_lt_top _)
  exact this

/-! ### Locality: the flow up to time `c` only sees the noise on `[0, c]` -/

theorem mk_stopped_cont {w : ℝ≥0 → Fin d → ℝ} (hw : Continuous w) (c : ℝ≥0) :
    Continuous fun u : ℝ≥0 => w (min u c) :=
  hw.comp (continuous_id.min continuous_const)

theorem mk_stopped_zero (w : ℝ≥0 → Fin d → ℝ) (hw0 : w 0 = 0) (c : ℝ≥0) :
    (fun u : ℝ≥0 => w (min u c)) 0 = 0 := by
  simp [hw0]

theorem mk_pfHyp_stopped {q Mb : ℝ} {m : ℕ} {B : Euc d → Euc d} {w : ℝ≥0 → Fin d → ℝ}
    (H : PfHyp q Mb m B w) (c : ℝ≥0) : PfHyp q Mb m B (fun u => w (min u c)) :=
  ⟨H.hq, H.hm, H.hB, mk_stopped_cont H.hw c, mk_stopped_zero w H.hw0 c⟩

theorem mk_flow_stopped {q Mb : ℝ} {m : ℕ} {B : Euc d → Euc d} {w : ℝ≥0 → Fin d → ℝ}
    (H : PfHyp q Mb m B w) (c : ℝ≥0) {t : ℝ} (ht0 : 0 ≤ t) (htc : t ≤ c) (x : Euc d) :
    flowMap q B (fun u => w (min u c)) t x = flowMap q B w t x := by
  have H' := mk_pfHyp_stopped H c
  have hP := pf_flowMap_isPathSolution H x
  have hP' := pf_flowMap_isPathSolution H' x
  -- the flow of `w` is a solution for the stopped noise on the horizon `c`
  have hP2 : IsPathSolution (fun (_ : ℝ) (y : Euc d) => -q • y + B y) (pfSigma d)
      (fun u => w (min u c)) x ((c : ℝ) : WithTop ℝ) (fun s => flowMap q B w s x) := by
    refine ⟨hP.1, fun s hs hsc => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hP.2 s hs (WithTop.coe_lt_top _)
    refine ⟨h1, h2, ?_⟩
    have hsc' : s < c := by exact_mod_cast hsc
    have : min (Real.toNNReal s) c = Real.toNNReal s := by
      refine min_eq_left ?_
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs]
      exact hsc'.le
    rw [h3]
    simp only [this]
  have hU := mk_isLocLipschitz H
  have hP3 : IsPathSolution (fun (_ : ℝ) (y : Euc d) => -q • y + B y) (pfSigma d)
      (fun u => w (min u c)) x ((c : ℝ) : WithTop ℝ) (fun s => flowMap q B (fun u => w (min u c)) s x) :=
    ⟨hP'.1, fun s hs _ => hP'.2 s hs (WithTop.coe_lt_top _)⟩
  have heq := ode_additive_unique Set.univ isOpen_univ _ hU (pfSigma d) (fun u => w (min u c))
    (mk_stopped_cont H.hw c) x hP3 hP2 (fun _ _ _ => Set.mem_univ _) (fun _ _ _ => Set.mem_univ _)
  rcases lt_or_eq_of_le htc with hlt | hEq
  · exact heq t ht0 (by rw [min_self]; exact_mod_cast hlt)
  · -- endpoint `t = c`
    rcases eq_or_lt_of_le ht0 with h0 | hpos
    · subst h0
      have e1 : flowMap q B w 0 x = x := hP.1
      have e2 : flowMap q B (fun u => w (min u c)) 0 x = x := hP'.1
      rw [e1, e2]
    · have hc1 : ContinuousOn (fun s => flowMap q B (fun u => w (min u c)) s x) (Icc 0 t) :=
        (hP'.2 t ht0 (WithTop.coe_lt_top _)).1
      have hc2 : ContinuousOn (fun s => flowMap q B w s x) (Icc 0 t) :=
        (hP.2 t ht0 (WithTop.coe_lt_top _)).1
      have hEqOn : EqOn (fun s => flowMap q B (fun u => w (min u c)) s x)
          (fun s => flowMap q B w s x) (Ico 0 t) := fun s hs =>
        heq s hs.1 (by rw [min_self]; exact_mod_cast hs.2.trans_eq hEq)
      have := hEqOn.of_subset_closure hc1 hc2 Ico_subset_Icc_self (by rw [closure_Ico hpos.ne])
      exact this ⟨ht0, le_rfl⟩

end HRS.MS.PoisMarkov
