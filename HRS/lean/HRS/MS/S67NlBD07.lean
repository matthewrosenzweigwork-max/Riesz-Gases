import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovThermAux2
import HRS.MS.S67NlBD03
import HRS.MS.S67NlBD04
import HRS.MS.S67NlBD05
import HRS.MS.S67NlBD06

/-!
# S6.7nl.07: `Σ²` time continuity of the actual weighted solution
Source pin `b66ab61cf3f03a9c6f5a899ef5de61f2b34c5e44`.

For `r0 ∈ [0,T]` the difference `ψ_r - ψ_{r0} = √ρ₀ · G_r` with
`G_r = (f_r - f_{r0}) - (m_r - m_{r0})`; the Leibniz bound gives the pointwise envelope
`4 C_w e^{-c|x|²} δ(r,x)` for all jets of order `≤ 2`, where `δ(r,·) → 0` pointwise (`hf.cont_c2`
and dominated convergence for the mean) and is uniformly bounded (`hf.bdd`).  The polynomially
weighted envelope `(1+|x|)² · 4 C_w e^{-c|x|²} δ` tends to `0` in `L²` by dominated convergence;
the integer converse ladder (packet 03/09 through 05) turns this into `oscNorm 2 (ψ_r - ψ_{r0}) → 0`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

/-- `‖g‖_{L²} = √(∫ g²)` for square-integrable `g`. -/
theorem s67bd_c07_eLpNorm_two {g : Euc d → ℝ} (hg : MemLp g 2 (volume : Measure (Euc d))) :
    eLpNorm g 2 (volume : Measure (Euc d)) = ENNReal.ofReal (Real.sqrt (∫ x, g x ^ 2)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hg.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  have e : ∀ x : ℝ, ‖x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (x ^ 2) := fun x => by
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
      Real.rpow_two, sq_abs]
  simp_rw [e]
  rw [← ofReal_integral_eq_lintegral_ofReal hg.integrable_sq
      (Filter.Eventually.of_forall fun x => sq_nonneg (g x)),
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun x => sq_nonneg _) (by norm_num),
    Real.sqrt_eq_rpow]

/-- Pointwise Leibniz bound through order two. -/
theorem s67bd_c07_prod_pt {w g : Euc d → ℝ} (hw : ContDiff ℝ 2 w) (hg : ContDiff ℝ 2 g)
    {c Cw G : ℝ} (x : Euc d) (hCw : 0 ≤ Cw) (hG : 0 ≤ G)
    (hwb : ∀ k ≤ 2, ‖iteratedFDeriv ℝ k w x‖ ≤ Cw * Real.exp (-c * ‖x‖ ^ 2))
    (hgb : ∀ k ≤ 2, ‖iteratedFDeriv ℝ k g x‖ ≤ G) (k : ℕ) (hk : k ≤ 2) :
    ‖iteratedFDeriv ℝ k (fun y => w y * g y) x‖ ≤ 4 * Cw * G * Real.exp (-c * ‖x‖ ^ 2) := by
  have h1 := norm_iteratedFDeriv_mul_le hw hg x (n := k) (by exact_mod_cast hk)
  refine h1.trans ?_
  have hE := (Real.exp_pos (-c * ‖x‖ ^ 2)).le
  have hterm : ∀ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i w x‖ *
      ‖iteratedFDeriv ℝ (k - i) g x‖ ≤ (k.choose i : ℝ) * (Cw * G * Real.exp (-c * ‖x‖ ^ 2)) := by
    intro i hi
    have hik : i ≤ 2 := by have := Finset.mem_range.1 hi; omega
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    calc ‖iteratedFDeriv ℝ i w x‖ * ‖iteratedFDeriv ℝ (k - i) g x‖
        ≤ (Cw * Real.exp (-c * ‖x‖ ^ 2)) * G :=
          mul_le_mul (hwb i hik) (hgb (k - i) (by omega)) (norm_nonneg _)
            (mul_nonneg hCw hE)
      _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  have hsum : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) = 2 ^ k := by
    exact_mod_cast Nat.sum_range_choose k
  rw [← Finset.sum_mul, hsum]
  have hX : 0 ≤ Cw * G * Real.exp (-c * ‖x‖ ^ 2) := mul_nonneg (mul_nonneg hCw hG) hE
  have h2k : (2 : ℝ) ^ k ≤ 4 := by
    interval_cases k <;> norm_num
  calc (2 : ℝ) ^ k * (Cw * G * Real.exp (-c * ‖x‖ ^ 2))
      ≤ 4 * (Cw * G * Real.exp (-c * ‖x‖ ^ 2)) := mul_le_mul_of_nonneg_right h2k hX
    _ = _ := by ring

/-- Gaussian data for `√ρ₀` and integrability of `ρ₀`. -/
theorem s67bd_c07_data (H : Mov2dTh d s β q ρ₀) :
    ∃ c Cw : ℝ, 0 < c ∧ 0 ≤ Cw ∧ ContDiff ℝ 2 (fun y => Real.sqrt (ρ₀ y)) ∧
      (∀ k ≤ 2, ∀ x, ‖iteratedFDeriv ℝ k (fun y => Real.sqrt (ρ₀ y)) x‖ ≤
        Cw * Real.exp (-c * ‖x‖ ^ 2)) ∧
      (∀ x, 0 ≤ ρ₀ x) ∧ Continuous ρ₀ ∧ Integrable ρ₀ volume := by
  obtain ⟨hws, -, c, hc, hk⟩ :=
    HRS.MS.Mov0.mv0_sqrt_gauss_thermal H.hd H.hs0 H.hsd H.hq H.hβ H.hρ
  obtain ⟨Bq, -, hR, -⟩ := HRS.MS.Mov0.mv0_gapref H.hd H.hs0 H.hsd H.hq H.hβ H.hρ
  obtain ⟨C0, h0⟩ := hk 0
  obtain ⟨C1, h1⟩ := hk 1
  obtain ⟨C2, h2⟩ := hk 2
  obtain ⟨Cw, hCw0, hCw⟩ : ∃ Cw : ℝ, 0 ≤ Cw ∧ |C0| ≤ Cw ∧ |C1| ≤ Cw ∧ |C2| ≤ Cw :=
    ⟨|C0| + |C1| + |C2|, by positivity, by linarith [abs_nonneg C1, abs_nonneg C2],
      by linarith [abs_nonneg C0, abs_nonneg C2], by linarith [abs_nonneg C0, abs_nonneg C1]⟩
  have hwb : ∀ k ≤ 2, ∀ x, ‖iteratedFDeriv ℝ k (fun y => Real.sqrt (ρ₀ y)) x‖ ≤
      Cw * Real.exp (-c * ‖x‖ ^ 2) := by
    intro k hk x
    have hE := (Real.exp_pos (-c * ‖x‖ ^ 2)).le
    interval_cases k
    · exact (h0 x).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans hCw.1) hE)
    · exact (h1 x).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans hCw.2.1) hE)
    · exact (h2 x).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans hCw.2.2) hE)
  have hρnn : ∀ x, 0 ≤ ρ₀ x := fun x => (hR.pos x).le
  have hρint : Integrable ρ₀ volume := by
    refine Integrable.mono' ((s67bd_poly_gauss_integrable d 0 (c := 2 * c)
      (by linarith)).const_mul (Cw ^ 2)) hR.smooth.continuous.aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    have hs := hwb 0 (by norm_num) x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hs
    have hsq : ρ₀ x = Real.sqrt (ρ₀ x) ^ 2 := (Real.sq_sqrt (hρnn x)).symm
    have hE2 : Real.exp (-c * ‖x‖ ^ 2) ^ 2 = Real.exp (-(2 * c) * ‖x‖ ^ 2) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [Real.norm_of_nonneg (hρnn x), hsq, pow_zero, one_mul, ← hE2, ← mul_pow]
    have hb0 : 0 ≤ Cw * Real.exp (-c * ‖x‖ ^ 2) := mul_nonneg hCw0 (Real.exp_pos _).le
    have ha0 : 0 ≤ Real.sqrt (ρ₀ x) := Real.sqrt_nonneg _
    exact sq_le_sq' (by linarith) (le_trans (le_abs_self _) hs)
  exact ⟨c, Cw, hc, hCw0, hws.of_le (by simp), hwb, hρnn, hR.smooth.continuous, hρint⟩

theorem s67bd_classical_sigma2_cont (H : Mov2dTh d s β q ρ₀)
    (ρ : ℝ → Euc d → ℝ) (T : ℝ) (φ : Euc d → ℝ)
    (f : ℝ → Euc d → ℝ) (hT : 0 ≤ T)
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff ρ) T φ f) :
    ContinuousOn (fun r => OscSpace.ofFun 2 (s67psi ρ₀ (f r))) (Icc (0 : ℝ) T) := by
  obtain ⟨c, Cw, hc, hCw0, hw2, hwb, hρnn, hρc, hρint⟩ := s67bd_c07_data H
  obtain ⟨_, -, hmem6⟩ := s67bd_classical_sigma2 H ρ T φ f hT hf
  obtain ⟨CI, hCI0, hCI⟩ := s67bd_integer_converse d 2
  -- uniform classical bounds
  obtain ⟨B0, hB0⟩ := hf.bdd 0 (by norm_num)
  obtain ⟨B1, hB1⟩ := hf.bdd 1 (by norm_num)
  obtain ⟨B2, hB2⟩ := hf.bdd 2 (by norm_num)
  obtain ⟨Ff, hFf0, hfb⟩ : ∃ Ff : ℝ, 0 ≤ Ff ∧ ∀ r ∈ Icc (0 : ℝ) T, ∀ k ≤ 2, ∀ x,
      ‖iteratedFDeriv ℝ k (f r) x‖ ≤ Ff := by
    refine ⟨|B0| + |B1| + |B2|, by positivity, fun r hr k hk x => ?_⟩
    interval_cases k
    · exact (hB0 r hr x).trans ((le_abs_self _).trans (by linarith [abs_nonneg B1, abs_nonneg B2]))
    · exact (hB1 r hr x).trans ((le_abs_self _).trans (by linarith [abs_nonneg B0, abs_nonneg B2]))
    · exact (hB2 r hr x).trans ((le_abs_self _).trans (by linarith [abs_nonneg B0, abs_nonneg B1]))
  obtain ⟨P, hP0, hPdef⟩ : ∃ P : ℝ, 0 ≤ P ∧ P = ∫ y, ρ₀ y := ⟨_, integral_nonneg hρnn, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : ℝ → ℝ, ∀ r, m r = ∫ y, f r y * ρ₀ y := ⟨_, fun _ => rfl⟩
  have hfc : ∀ r ∈ Icc (0 : ℝ) T, ContDiff ℝ 2 (f r) := hf.c2
  have hmb : ∀ r ∈ Icc (0 : ℝ) T, |m r| ≤ Ff * P := by
    intro r hr
    rw [hm, ← Real.norm_eq_abs]
    have hb : ‖∫ y, f r y * ρ₀ y‖ ≤ ∫ y, Ff * ρ₀ y := by
      refine norm_integral_le_of_norm_le (hρint.const_mul Ff) (ae_of_all _ fun y => ?_)
      rw [norm_mul, Real.norm_of_nonneg (hρnn y)]
      have := hfb r hr 0 (by norm_num) y
      rw [norm_iteratedFDeriv_zero] at this
      exact mul_le_mul_of_nonneg_right this (hρnn y)
    rwa [integral_const_mul, ← hPdef] at hb
  -- continuity in time of the jets (pointwise in `x`)
  have hjc : ∀ j ≤ 2, ∀ x : Euc d,
      ContinuousOn (fun r => iteratedFDeriv ℝ j (f r) x) (Icc (0 : ℝ) T) := by
    intro j hj x
    have h1 := hf.cont_c2 j hj
    have h2 : Continuous fun t : Icc (0 : ℝ) T => iteratedFDeriv ℝ j (f t) x :=
      h1.comp (continuous_id.prodMk continuous_const)
    exact continuousOn_iff_continuous_domRestrict.2 h2
  intro r0 hr0
  rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
  set l : Filter ℝ := 𝓝[Icc (0 : ℝ) T] r0 with hl
  have hlI : ∀ᶠ r in l, r ∈ Icc (0 : ℝ) T := self_mem_nhdsWithin
  -- the mean is continuous in time
  have hmc : Tendsto m l (𝓝 (m r0)) := by
    have hdom := tendsto_integral_filter_of_dominated_convergence (μ := volume)
      (F := fun r y => f r y * ρ₀ y) (f := fun y => f r0 y * ρ₀ y) (l := l)
      (bound := fun y => Ff * ρ₀ y)
      (hlI.mono fun r hr => ((hfc r hr).continuous.mul hρc).aestronglyMeasurable)
      (hlI.mono fun r hr => ae_of_all _ fun y => by
        rw [norm_mul, Real.norm_of_nonneg (hρnn y)]
        have := hfb r hr 0 (by norm_num) y
        rw [norm_iteratedFDeriv_zero] at this
        exact mul_le_mul_of_nonneg_right this (hρnn y))
      (hρint.const_mul Ff)
      (ae_of_all _ fun y => by
        have h0 := (hjc 0 (by norm_num) y r0 hr0)
        have hap := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => Euc d) ℝ
          (fun l => l.elim0)).continuous.tendsto _).comp h0
        have h0' : Tendsto (fun r => f r y) l (𝓝 (f r0 y)) := by
          simpa [Function.comp_def, iteratedFDeriv_zero_apply] using hap
        exact h0'.mul_const _)
    rw [show m = fun r => ∫ y, f r y * ρ₀ y from funext hm]
    exact hdom
  -- pointwise envelope `δ`
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ → Euc d → ℝ, ∀ r x, δ r x =
      ‖iteratedFDeriv ℝ 0 (f r) x - iteratedFDeriv ℝ 0 (f r0) x‖ +
      ‖iteratedFDeriv ℝ 1 (f r) x - iteratedFDeriv ℝ 1 (f r0) x‖ +
      ‖iteratedFDeriv ℝ 2 (f r) x - iteratedFDeriv ℝ 2 (f r0) x‖ + |m r - m r0| :=
    ⟨_, fun _ _ => rfl⟩
  have hδ0 : ∀ r x, 0 ≤ δ r x := by intro r x; rw [hδ]; positivity
  obtain ⟨Δ0, hΔ0⟩ : ∃ Δ0 : ℝ, Δ0 = 6 * Ff + 2 * (Ff * P) := ⟨_, rfl⟩
  have hΔ00 : 0 ≤ Δ0 := by rw [hΔ0]; positivity
  have hδb : ∀ r ∈ Icc (0 : ℝ) T, ∀ x, δ r x ≤ Δ0 := by
    intro r hr x
    have hj : ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (f r) x - iteratedFDeriv ℝ j (f r0) x‖ ≤ 2 * Ff :=
      fun j hj => (norm_sub_le _ _).trans (by
        linarith [hfb r hr j hj x, hfb r0 hr0 j hj x])
    have hmm : |m r - m r0| ≤ 2 * (Ff * P) :=
      (abs_sub _ _).trans (by linarith [hmb r hr, hmb r0 hr0])
    rw [hδ, hΔ0]
    linarith [hj 0 (by norm_num), hj 1 (by norm_num), hj 2 (by norm_num)]
  have hδt : ∀ x, Tendsto (fun r => δ r x) l (𝓝 0) := by
    intro x
    have hjt : ∀ j ≤ 2, Tendsto (fun r => ‖iteratedFDeriv ℝ j (f r) x -
        iteratedFDeriv ℝ j (f r0) x‖) l (𝓝 0) := by
      intro j hj
      have h0 := hjc j hj x r0 hr0
      have := (h0.sub_const (iteratedFDeriv ℝ j (f r0) x)).norm
      simpa using this
    have hmt : Tendsto (fun r => |m r - m r0|) l (𝓝 0) := by
      have := (hmc.sub_const (m r0)).abs
      simpa using this
    have := (((hjt 0 (by norm_num)).add (hjt 1 (by norm_num))).add (hjt 2 (by norm_num))).add hmt
    simpa [hδ] using this
  have hδc : ∀ r ∈ Icc (0 : ℝ) T, Continuous (δ r) := by
    intro r hr
    have hj : ∀ j ≤ 2, Continuous fun x => ‖iteratedFDeriv ℝ j (f r) x -
        iteratedFDeriv ℝ j (f r0) x‖ := fun j hj =>
      (((hfc r hr).continuous_iteratedFDeriv (by exact_mod_cast hj)).sub
        ((hfc r0 hr0).continuous_iteratedFDeriv (by exact_mod_cast hj))).norm
    have : δ r = fun x => ‖iteratedFDeriv ℝ 0 (f r) x - iteratedFDeriv ℝ 0 (f r0) x‖ +
      ‖iteratedFDeriv ℝ 1 (f r) x - iteratedFDeriv ℝ 1 (f r0) x‖ +
      ‖iteratedFDeriv ℝ 2 (f r) x - iteratedFDeriv ℝ 2 (f r0) x‖ + |m r - m r0| :=
      funext (hδ r)
    rw [this]
    exact (((hj 0 (by norm_num)).add (hj 1 (by norm_num))).add (hj 2 (by norm_num))).add
      continuous_const
  -- jets of the difference factor
  have hGcd : ∀ r ∈ Icc (0 : ℝ) T,
      ContDiff ℝ 2 (fun y => (f r y - f r0 y) - (m r - m r0)) := fun r hr =>
    ((hfc r hr).sub (hfc r0 hr0)).sub contDiff_const
  have hGb : ∀ r ∈ Icc (0 : ℝ) T, ∀ k ≤ 2, ∀ x,
      ‖iteratedFDeriv ℝ k (fun y => (f r y - f r0 y) - (m r - m r0)) x‖ ≤ δ r x := by
    intro r hr k hk x
    have h1 := s67bd_sig2_const_sub ((hfc r hr).sub (hfc r0 hr0)) (m r - m r0) k hk x
    have h2 : iteratedFDeriv ℝ k (fun y => f r y - f r0 y) x =
        iteratedFDeriv ℝ k (f r) x - iteratedFDeriv ℝ k (f r0) x := by
      have hsub : (fun y => f r y - f r0 y) = f r - f r0 := rfl
      rw [hsub]
      exact iteratedFDeriv_sub_apply (((hfc r hr).of_le (by exact_mod_cast hk)).contDiffAt)
        (((hfc r0 hr0).of_le (by exact_mod_cast hk)).contDiffAt)
    rw [h2] at h1
    refine h1.trans ?_
    rw [hδ]
    interval_cases k <;> linarith [norm_nonneg (iteratedFDeriv ℝ 0 (f r) x - iteratedFDeriv ℝ 0 (f r0) x),
      norm_nonneg (iteratedFDeriv ℝ 1 (f r) x - iteratedFDeriv ℝ 1 (f r0) x),
      norm_nonneg (iteratedFDeriv ℝ 2 (f r) x - iteratedFDeriv ℝ 2 (f r0) x)]
  have hdiff : ∀ r, (fun z => s67psi ρ₀ (f r) z - s67psi ρ₀ (f r0) z) =
      fun y => Real.sqrt (ρ₀ y) * ((f r y - f r0 y) - (m r - m r0)) := by
    intro r
    funext y
    simp only [s67psi, ← hm]
    ring
  have hujet : ∀ r ∈ Icc (0 : ℝ) T, ∀ k ≤ 2, ∀ x,
      ‖iteratedFDeriv ℝ k (fun z => s67psi ρ₀ (f r) z - s67psi ρ₀ (f r0) z) x‖ ≤
        4 * Cw * δ r x * Real.exp (-c * ‖x‖ ^ 2) := by
    intro r hr k hk x
    rw [hdiff r]
    exact s67bd_c07_prod_pt hw2 (hGcd r hr) x hCw0 (hδ0 r x) (fun j hj => hwb j hj x)
      (fun j hj => hGb r hr j hj x) k hk
  have hucd : ∀ r ∈ Icc (0 : ℝ) T,
      ContDiff ℝ 2 (fun z => s67psi ρ₀ (f r) z - s67psi ρ₀ (f r0) z) := by
    intro r hr
    rw [hdiff r]
    exact hw2.mul (hGcd r hr)
  -- the weighted envelope
  obtain ⟨e, he⟩ : ∃ e : ℝ → Euc d → ℝ, ∀ r x,
      e r x = 4 * Cw * (1 + ‖x‖) ^ 2 * Real.exp (-c * ‖x‖ ^ 2) * δ r x := ⟨_, fun _ _ => rfl⟩
  have hE0 : ∀ x : Euc d, 0 ≤ Real.exp (-c * ‖x‖ ^ 2) := fun x => (Real.exp_pos _).le
  have he0 : ∀ r x, 0 ≤ e r x := by
    intro r x; rw [he]
    have := hE0 x
    have := hδ0 r x
    positivity
  have hec : ∀ r ∈ Icc (0 : ℝ) T, Continuous (e r) := by
    intro r hr
    have : e r = fun x => 4 * Cw * (1 + ‖x‖) ^ 2 * Real.exp (-c * ‖x‖ ^ 2) * δ r x :=
      funext (he r)
    rw [this]
    exact ((continuous_const.mul (by fun_prop)).mul (by fun_prop)).mul (hδc r hr)
  obtain ⟨CL, -, hCL⟩ := s67bd_gaussian_L2 d 2 c hc
  have hebd : ∀ r ∈ Icc (0 : ℝ) T, ∀ x, e r x ≤
      (4 * Cw * Δ0) * (1 + ‖x‖) ^ 2 * Real.exp (-c * ‖x‖ ^ 2) := by
    intro r hr x
    rw [he]
    have h1 := hδb r hr x
    have h2 : 0 ≤ 4 * Cw * (1 + ‖x‖) ^ 2 * Real.exp (-c * ‖x‖ ^ 2) := by
      have := hE0 x; positivity
    calc 4 * Cw * (1 + ‖x‖) ^ 2 * Real.exp (-c * ‖x‖ ^ 2) * δ r x
        ≤ 4 * Cw * (1 + ‖x‖) ^ 2 * Real.exp (-c * ‖x‖ ^ 2) * Δ0 :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = _ := by ring
  have hmemE : ∀ r ∈ Icc (0 : ℝ) T, MemLp (e r) 2 (volume : Measure (Euc d)) := by
    intro r hr
    refine (hCL (4 * Cw * Δ0) (by positivity) (e r) (hec r hr).aestronglyMeasurable
      (fun x => ?_)).1
    rw [abs_of_nonneg (he0 r x)]
    exact hebd r hr x
  -- `L²` convergence of the envelope
  have hint : Tendsto (fun r => ∫ x, e r x ^ 2) l (𝓝 0) := by
    have hdom := tendsto_integral_filter_of_dominated_convergence (μ := volume)
      (F := fun r x => e r x ^ 2) (f := fun _ => (0 : ℝ)) (l := l)
      (bound := fun x : Euc d => (4 * Cw * Δ0) ^ 2 *
        ((1 + ‖x‖) ^ 4 * Real.exp (-(2 * c) * ‖x‖ ^ 2)))
      (hlI.mono fun r hr => ((hec r hr).pow 2).aestronglyMeasurable)
      (hlI.mono fun r hr => ae_of_all _ fun x => by
        have hE2 : Real.exp (-c * ‖x‖ ^ 2) ^ 2 = Real.exp (-(2 * c) * ‖x‖ ^ 2) := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        have h1 := hebd r hr x
        have h2 := sq_le_sq' (by linarith [he0 r x, mul_nonneg (mul_nonneg
          (mul_nonneg (by positivity : (0:ℝ) ≤ 4 * Cw) hΔ00) (sq_nonneg (1 + ‖x‖))) (hE0 x)]) h1
        refine h2.trans (le_of_eq ?_)
        rw [mul_pow, mul_pow, hE2.symm]
        ring)
      (((s67bd_poly_gauss_integrable d 4 (c := 2 * c) (by linarith)).const_mul
        ((4 * Cw * Δ0) ^ 2)))
      (ae_of_all _ fun x => by
        have : Tendsto (fun r => e r x) l (𝓝 0) := by
          have h0 := (hδt x).const_mul (4 * Cw * (1 + ‖x‖) ^ 2 * Real.exp (-c * ‖x‖ ^ 2))
          simpa [he] using h0
        simpa using this.pow 2)
    simpa using hdom
  have hA : ∀ r ∈ Icc (0 : ℝ) T,
      (eLpNorm (e r) 2 (volume : Measure (Euc d))).toReal = Real.sqrt (∫ x, e r x ^ 2) := by
    intro r hr
    rw [s67bd_c07_eLpNorm_two (hmemE r hr), ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  have hAt : Tendsto (fun r => CI * Real.sqrt (∫ x, e r x ^ 2)) l (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hint
    simpa using this.const_mul CI
  -- the oscillator bound
  have hmain : ∀ r ∈ Icc (0 : ℝ) T,
      dist (OscSpace.ofFun 2 (s67psi ρ₀ (f r))) (OscSpace.ofFun 2 (s67psi ρ₀ (f r0))) ≤
        CI * Real.sqrt (∫ x, e r x ^ 2) := by
    intro r hr
    have hu := hucd r hr
    obtain ⟨hmo, hno⟩ := hCI (fun z => s67psi ρ₀ (f r) z - s67psi ρ₀ (f r0) z)
      (Real.sqrt (∫ x, e r x ^ 2)) (Real.sqrt_nonneg _) (by exact_mod_cast hu) (by
        intro k a γ hk
        have hkn : k ≤ 2 := by omega
        have hcont : Continuous (fun x => s67bd_xpow a x * s67bd_jet k γ
            (fun z => s67psi ρ₀ (f r) z - s67psi ρ₀ (f r0) z) x) := by
          refine Continuous.mul ?_ ?_
          · unfold s67bd_xpow
            exact continuous_finsetProd _ fun l _ =>
              ((EuclideanSpace.proj (𝕜 := ℝ) l : Euc d →L[ℝ] ℝ).continuous).pow _
          · unfold s67bd_jet
            exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Euc d) ℝ
              (fun l => (EuclideanSpace.single (γ l) (1 : ℝ) : Euc d))).continuous.comp
              (hu.continuous_iteratedFDeriv (by exact_mod_cast hkn))
        have hbd : ∀ x, ‖s67bd_xpow a x * s67bd_jet k γ
            (fun z => s67psi ρ₀ (f r) z - s67psi ρ₀ (f r0) z) x‖ ≤ ‖e r x‖ := by
          intro x
          rw [Real.norm_of_nonneg (he0 r x), Real.norm_eq_abs, abs_mul]
          have h1 := s67bd_abs_xpow_le a x
          have h2 := (s67bd_abs_jet_le k γ _ x).trans (hujet r hr k hkn x)
          have h3 : (1 + ‖x‖) ^ MultiIndex.degree a ≤ (1 + ‖x‖) ^ 2 :=
            pow_le_pow_right₀ (by linarith [norm_nonneg x]) (by omega)
          have h4 : 0 ≤ 4 * Cw * δ r x * Real.exp (-c * ‖x‖ ^ 2) := by
            have := hE0 x; have := hδ0 r x; positivity
          calc |s67bd_xpow a x| * |s67bd_jet k γ _ x|
              ≤ (1 + ‖x‖) ^ 2 * (4 * Cw * δ r x * Real.exp (-c * ‖x‖ ^ 2)) :=
                mul_le_mul (h1.trans h3) h2 (abs_nonneg _) (by positivity)
            _ = _ := by rw [he]; ring
        refine ⟨(hmemE r hr).of_le hcont.aestronglyMeasurable (ae_of_all _ hbd), ?_⟩
        rw [← hA r hr]
        exact ENNReal.toReal_mono (hmemE r hr).eLpNorm_ne_top (eLpNorm_mono hcont.aestronglyMeasurable hbd))
    have e2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [e2] at hmo hno
    rw [dist_eq_norm, ← mov2d_ofFun_sub (hmem6 r hr).1 (hmem6 r0 hr0).1,
      OscSpace.norm_ofFun _ hmo]
    exact hno
  refine squeeze_zero' (Eventually.of_forall fun r => dist_nonneg) ?_ hAt
  exact hlI.mono fun r hr => hmain r hr

end HRS.MS.BreakdownS67
