import HRS.MS.LcKolmAux1
import HRS.MS.LcMarkovAux2
import HRS.MS.LcWtAux1
import HRS.Whole.Adjoint

/-!
# LC-6 (part 2): the backward equation for `lcSg` (S4.11, step 6)

`lc_backward`: for `LcHyp Q 2 Λc ΛB c B` (the flow is `C^3`), `IsBrownianFiltration P ℱ W`, `ν` continuous with
`0 ≤ ν ≤ ν*`, `t ≥ 0` and `f ∈ C²` with `f, Df, D²f` bounded, the function `u r = lcSg P W ν Q c B r t f` is
an `IsLocalBackwardSolution` for the drift `b r x = -(Qx) - c r + B r x` with terminal datum `f`.

Route (no Ito formula).  `lc_markov`: `u(a) = E u(b, Φ^{a,b})`, so for `a < b` near `r`
`u(a,x) - u(b,x) = E[u(b, x + Δ + w) - u(b,x)]` with `Δ = G_b - G_a` the Gaussian noise increment and
`w = ∫_a^b b_s(Φ^{a,s}x) ds` the drift part.  The second-order Taylor expansion of `u(b,·)` with the Gaussian
moments of `Δ` is `lc6_expansion` (LcKolmAux1, an abstract statement), whose hypotheses are verified here:
the derivatives `Du, D²u` are jointly continuous in `(r,x)` (differentiation under `E`, dominated
convergence, and `lc6_flow_deriv_cont`, the pathwise continuity of the flow derivatives in the initial time).

Adjustment w.r.t. the sketch: the hypothesis is `LcHyp Q 2 …` and bounded `f, Df, D²f` (instead of the
decay class of `lc_engine`); `LC-F` derives the bounds from `decayNormE`.  Helpers carry the prefix `lc6_`.
-/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

noncomputable section

set_option synthInstance.maxHeartbeats 400000

universe u

namespace HRS.MS.Lc

section Main

variable {d : ℕ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → Fin d → ℝ} {ν : ℝ → ℝ} {Q : Matrix (Fin d) (Fin d) ℝ}
  {Λc ΛB : ℝ} {c : ℝ → Euc d} {B : ℝ → Euc d → Euc d} {f : Euc d → ℝ} {M K t : ℝ}
  (hW : IsBrownianFiltration P ℱ W) (hν : Continuous ν) (H : LcHyp Q 2 Λc ΛB c B)
  (hf : ContDiff ℝ 2 f) (hM : ∀ i ≤ 2, ∀ y, ‖iteratedFDeriv ℝ i f y‖ ≤ M) (hK1 : 1 ≤ K)
  (hK : ∀ {g : ℝ → Euc d}, Continuous g → ∀ {r : ℝ}, 0 ≤ r → r ≤ t → ∀ (x : Euc d) (j : ℕ),
    1 ≤ j → j ≤ 3 → ‖iteratedFDeriv ℝ j (lcFlow Q c B g r t) x‖ ≤ K)

include hW hν H hf hM hK1 hK

/-- Regularity and bounds of `u r = lcSg … r t f`. -/
theorem lc6_reg {r : ℝ} (hr : r ∈ Icc 0 t) :
    ContDiff ℝ 2 (lcSg P W ν Q c B r t f) ∧
      (∀ j ≤ 2, ∀ x, iteratedFDeriv ℝ j (lcSg P W ν Q c B r t f) x =
        ∫ ω, iteratedFDeriv ℝ j (fun y => f (lcFlow Q c B (fun v => lcNoiseE W ν v ω) r t y)) x ∂P) ∧
      ∀ j ≤ 2, ∀ x, ‖iteratedFDeriv ℝ j (lcSg P W ν Q c B r t f) x‖ ≤ 2 * M * K ^ 2 := by
  have hGm : ∀ v, Measurable fun ω => lcNoiseE W ν v ω := fun v => lc_noiseE_measurable hW v
  have hGc : ∀ ω, Continuous (fun v => lcNoiseE W ν v ω) := fun ω => lc_noiseE_cont hW hν ω
  have := HRS.MS.PoisSg.sg_family (P := P)
    (φ := fun ω y => lcFlow Q c B (fun v => lcNoiseE W ν v ω) r t y) (k := 2)
    (lc4_meas_flow H hGm hGc hr.1 hr.2)
    (fun ω => (lcFlow_contDiff H (hGc ω) hr.1 hr.2).of_le (by norm_cast))
    hf hM hK1 (fun ω x j h1 h2 => hK (hGc ω) hr.1 hr.2 x j h1 (by omega))
  have e : lcSg P W ν Q c B r t f =
      fun x => ∫ ω, f (lcFlow Q c B (fun v => lcNoiseE W ν v ω) r t x) ∂P := rfl
  rw [e]
  simpa using this

/-- Pointwise bounds of the integrand `f ∘ Φ^r_ω`. -/
theorem lc6_pt {r : ℝ} (hr : r ∈ Icc 0 t) (ω : Ω) {j : ℕ} (hj : j ≤ 2) (x : Euc d) :
    ‖iteratedFDeriv ℝ j (fun y => f (lcFlow Q c B (fun v => lcNoiseE W ν v ω) r t y)) x‖ ≤
      2 * M * K ^ 2 := by
  have hGc : Continuous (fun v => lcNoiseE W ν v ω) := lc_noiseE_cont hW hν ω
  have hφ : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (lcFlow Q c B (fun v => lcNoiseE W ν v ω) r t) :=
    (lcFlow_contDiff H hGc hr.1 hr.2).of_le (by norm_cast)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by norm_num) 0)
  have h1 : ‖iteratedFDeriv ℝ j (f ∘ lcFlow Q c B (fun v => lcNoiseE W ν v ω) r t) x‖ ≤
      (j.factorial : ℝ) * M * K ^ j :=
    norm_iteratedFDeriv_comp_le (N := ((2 : ℕ) : WithTop ℕ∞)) hf hφ (by exact_mod_cast hj) x
      (fun i hi => hM i (hi.trans hj) _)
      (fun i hi1 hi2 => (hK hGc hr.1 hr.2 x i hi1 (by omega)).trans (le_self_pow₀ hK1 (by omega)))
  refine h1.trans ?_
  have hf2 : (j.factorial : ℝ) ≤ 2 := by
    interval_cases j <;> norm_num [Nat.factorial]
  have hp : K ^ j ≤ K ^ 2 := pow_le_pow_right₀ hK1 hj
  calc (j.factorial : ℝ) * M * K ^ j ≤ 2 * M * K ^ 2 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hf2 hM0) hp (by positivity) (by positivity)

/-- Continuity of the evaluations of the derivatives of `u` in `(r, x)`. -/
theorem lc6_eval_cont (ht : 0 ≤ t) {j : ℕ} (hj : j ≤ 2) (m : Fin j → Euc d)
    (hpath : ∀ ω, ContinuousOn (fun p : ℝ × Euc d =>
      iteratedFDeriv ℝ j (fun y => f (lcFlow Q c B (fun v => lcNoiseE W ν v ω) p.1 t y)) p.2 m)
      (Icc 0 t ×ˢ univ)) :
    ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ j (lcSg P W ν Q c B p.1 t f) p.2 m)
      (Icc 0 t ×ˢ univ) := by
  have hGm : ∀ v, Measurable fun ω => lcNoiseE W ν v ω := fun v => lc_noiseE_measurable hW v
  have hGc : ∀ ω, Continuous (fun v => lcNoiseE W ν v ω) := fun ω => lc_noiseE_cont hW hν ω
  have hmeas : ∀ r ∈ Icc 0 t, ∀ x, AEStronglyMeasurable (fun ω =>
      iteratedFDeriv ℝ j (fun y => f (lcFlow Q c B (fun v => lcNoiseE W ν v ω) r t y)) x) P := by
    intro r hr x
    have hjoint : StronglyMeasurable (fun p : Ω × Euc d =>
        f (lcFlow Q c B (fun v => lcNoiseE W ν v p.1) r t p.2)) :=
      (hf.continuous.measurable.comp (lc4_meas_flow H hGm hGc hr.1 hr.2)).stronglyMeasurable
    have := HRS.MS.PoisSg.sg_stronglyMeasurable_iteratedFDeriv
      (fun ω y => f (lcFlow Q c B (fun v => lcNoiseE W ν v ω) r t y)) hjoint j (fun ω =>
        (hf.comp ((lcFlow_contDiff H (hGc ω) hr.1 hr.2).of_le (by norm_cast))).of_le
          (by exact_mod_cast hj))
    exact (this.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have heval : ∀ p ∈ (Icc 0 t ×ˢ univ : Set (ℝ × Euc d)),
      iteratedFDeriv ℝ j (lcSg P W ν Q c B p.1 t f) p.2 m =
        ∫ ω, iteratedFDeriv ℝ j (fun y => f (lcFlow Q c B (fun v => lcNoiseE W ν v ω) p.1 t y)) p.2 m ∂P := by
    intro p hp
    rw [(lc6_reg hW hν H hf hM hK1 hK hp.1).2.1 j hj p.2]
    have hint : Integrable (fun ω => iteratedFDeriv ℝ j
        (fun y => f (lcFlow Q c B (fun v => lcNoiseE W ν v ω) p.1 t y)) p.2) P :=
      Integrable.of_bound (hmeas p.1 hp.1 p.2) (2 * M * K ^ 2)
        (Eventually.of_forall fun ω => lc6_pt hW hν H hf hM hK1 hK hp.1 ω hj p.2)
    exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ m).integral_comp_comm hint).symm
  refine ContinuousOn.congr (f := fun p : ℝ × Euc d => ∫ ω, iteratedFDeriv ℝ j
    (fun y => f (lcFlow Q c B (fun v => lcNoiseE W ν v ω) p.1 t y)) p.2 m ∂P) ?_ heval
  refine continuousOn_of_dominated (bound := fun _ => 2 * M * K ^ 2 * ∏ i, ‖m i‖) ?_ ?_ (integrable_const _)
    (Eventually.of_forall hpath)
  · intro p hp
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ m).continuous.comp_aestronglyMeasurable
      (hmeas p.1 hp.1 p.2)
  · intro p hp
    refine Eventually.of_forall fun ω => ?_
    refine (ContinuousMultilinearMap.le_opNorm _ m).trans ?_
    exact mul_le_mul_of_nonneg_right (lc6_pt hW hν H hf hM hK1 hK hp.1 ω hj p.2) (by positivity)

/-- `u` and its first and second derivatives are jointly continuous in `(r, x)` on `[0,t] × ℝ^d`. -/
theorem lc6_u_cont (ht : 0 ≤ t) :
    ContinuousOn (fun p : ℝ × Euc d => lcSg P W ν Q c B p.1 t f p.2) (Icc 0 t ×ˢ univ) ∧
    ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (lcSg P W ν Q c B p.1 t f) p.2) (Icc 0 t ×ˢ univ) ∧
    ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (fderiv ℝ (lcSg P W ν Q c B p.1 t f)) p.2)
      (Icc 0 t ×ˢ univ) := by
  have hGc : ∀ ω, Continuous (fun v => lcNoiseE W ν v ω) := fun ω => lc_noiseE_cont hW hν ω
  have hP : ∀ ω, _ := fun ω => lc6_integrand_cont H (hGc ω) ht (fun r hr0 hrt x j h1 h2 =>
    hK (hGc ω) hr0 hrt x j h1 h2) hf
  refine ⟨?_, ?_, ?_⟩
  · have := lc6_eval_cont hW hν H hf hM hK1 hK ht (j := 0) (by norm_num) (fun _ => 0) (fun ω => by
      simpa [iteratedFDeriv_zero_apply] using (hP ω).1)
    simpa [iteratedFDeriv_zero_apply] using this
  · refine continuousOn_clm_apply.2 fun v => ?_
    have := lc6_eval_cont hW hν H hf hM hK1 hK ht (j := 1) (by norm_num) (fun _ => v) (fun ω => by
      simpa [iteratedFDeriv_one_apply] using (hP ω).2.1 v)
    simpa [iteratedFDeriv_one_apply] using this
  · refine continuousOn_clm_apply.2 fun v => continuousOn_clm_apply.2 fun w => ?_
    have := lc6_eval_cont hW hν H hf hM hK1 hK ht (j := 2) (by norm_num) ![v, w] (fun ω => by
      simpa [iteratedFDeriv_two_apply] using (hP ω).2.2 v w)
    simpa [iteratedFDeriv_two_apply] using this

end Main

/-! ### The drift part of the displacement -/

section Drift

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {Λc ΛB : ℝ} {c : ℝ → Euc d} {B : ℝ → Euc d → Euc d}
  {g : ℝ → Euc d}

theorem lc6_drift_repr (H : LcHyp Q 2 Λc ΛB c B) (hg : Continuous g) {a : ℝ} (ha : 0 ≤ a) {h : ℝ}
    (hh : 0 ≤ h) (x : Euc d) :
    lcFlow Q c B g a (a + h) x = x + (∫ s in Icc 0 h, lcB Q c B a s (lcFlow Q c B g a (a + s) x)) +
      (g (a + h) - g a) := by
  have hy := (lcFlow_isPathSolution H hg ha x).2 h hh (WithTop.coe_lt_top h)
  have := hy.2.2
  rw [lc1_noise_sum g a hh] at this
  simpa using this

theorem lc6_w_bound (Q : Matrix (Fin d) (Fin d) ℝ) (Λc ΛB T : ℝ) (x : Euc d) :
    ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ {c : ℝ → Euc d} {B : ℝ → Euc d → Euc d}, LcHyp Q 2 Λc ΛB c B →
      ∀ {g : ℝ → Euc d}, Continuous g → ∀ {a h : ℝ}, 0 ≤ a → 0 ≤ h → a + h ≤ T →
      ‖∫ s in Icc 0 h, lcB Q c B a s (lcFlow Q c B g a (a + s) x)‖ ≤
        h * C1 * (1 + ⨆ v ∈ Icc (0 : ℝ) T, ‖g v‖) := by
  obtain ⟨Cu, hCu0, hCu⟩ := lc_U_bound Q T
  set Λ : ℝ := lcLam Q Λc ΛB with hΛ
  refine ⟨|Λ| * max 1 Cu * Real.exp (|Λ| * T) * (1 + ‖x‖), by positivity,
    fun {c B} H {g} hg {a h} ha hh haT => ?_⟩
  set S : ℝ := ⨆ v ∈ Icc (0 : ℝ) T, ‖g v‖ with hS
  have hS0 : 0 ≤ S := lc3_sup_nonneg T
  have hΛ0 : 0 ≤ Λ := H.lam_nonneg
  have hpt : ∀ s ∈ Icc 0 h, ‖lcB Q c B a s (lcFlow Q c B g a (a + s) x)‖ ≤
      |Λ| * max 1 Cu * Real.exp (|Λ| * T) * (1 + ‖x‖) * (1 + S) := by
    intro s hs
    set y := lcFlow Q c B g a (a + s) x with hy
    have hκ : ∀ u ∈ Icc a (a + s), ‖lcU Q g a u‖ ≤ Cu * S := fun u hu =>
      hCu hg a u ha hu.1 (by linarith [hu.2, hs.2])
    obtain ⟨h1, -⟩ := lc2_flow_comp H hg ha (by linarith [hs.1] : a ≤ a + s) hκ x
    have hE : Real.exp (Λ * (a + s - a)) ≤ Real.exp (|Λ| * T) := by
      refine Real.exp_le_exp.2 ?_
      rw [abs_of_nonneg hΛ0]; exact mul_le_mul_of_nonneg_left (by linarith [hs.2]) hΛ0
    have hv : 0 ≤ a + s := by linarith [hs.1]
    have hlcB : ‖lcB Q c B a s y‖ ≤ Λ * (1 + ‖y‖) := by
      have hB0 : ‖B (a + s) y‖ ≤ ΛB := by
        have := H.B_bd _ hv 0 (Nat.zero_le _) y; rwa [norm_iteratedFDeriv_zero] at this
      have hQ : ‖lcQ Q y‖ ≤ ‖lcQ Q‖ * ‖y‖ := (lcQ Q).le_opNorm y
      have hc := H.c_bd _ hv
      have hΛc := H.Λc_nonneg
      have hΛB := H.ΛB_nonneg
      have : ‖lcB Q c B a s y‖ ≤ ‖lcQ Q y‖ + ‖c (a + s)‖ + ‖B (a + s) y‖ := by
        unfold lcB
        refine (norm_add_le _ _).trans ?_
        have := norm_sub_le (-(lcQ Q y)) (c (a + s))
        rw [norm_neg] at this
        linarith
      simp only [hΛ, lcLam]
      nlinarith [norm_nonneg y, norm_nonneg (lcQ Q), mul_nonneg hΛc (norm_nonneg y),
        mul_nonneg hΛB (norm_nonneg y)]
    have hA : 1 + Cu * S ≤ max 1 Cu * (1 + S) := by
      have := le_max_left 1 Cu
      have := le_max_right 1 Cu
      nlinarith
    calc ‖lcB Q c B a s y‖ ≤ Λ * (1 + ‖y‖) := hlcB
      _ ≤ |Λ| * ((1 + Cu * S) * Real.exp (|Λ| * T) * (1 + ‖x‖)) := by
          refine mul_le_mul (le_abs_self Λ) (h1.trans ?_) (by positivity) (abs_nonneg _)
          have : (1 + Cu * S) * Real.exp (Λ * (a + s - a)) ≤ (1 + Cu * S) * Real.exp (|Λ| * T) :=
            mul_le_mul_of_nonneg_left hE (by positivity)
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ ≤ |Λ| * ((max 1 Cu * (1 + S)) * Real.exp (|Λ| * T) * (1 + ‖x‖)) := by gcongr
      _ = _ := by ring
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc 0 h)
    (f := fun s => lcB Q c B a s (lcFlow Q c B g a (a + s) x)) (by simp) hpt
  refine this.trans ?_
  simp [Real.volume_real_Icc, hh]
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg Λ) (le_trans zero_le_one (le_max_left 1 Cu)))
    (Real.exp_pos (|Λ| * T)).le) (add_nonneg zero_le_one (norm_nonneg x)), hS0]

theorem lc6_drift_cont (H : LcHyp Q 2 Λc ΛB c B) (hg : Continuous g) {r : ℝ} (hr : 0 ≤ r)
    (x : Euc d) : ContinuousWithinAt (fun p : ℝ × ℝ =>
      lcB Q c B p.1 p.2 (lcFlow Q c B g p.1 (p.1 + p.2) x)) {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} (r, 0) := by
  set S : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2} with hS
  have hr0 : ((r, (0 : ℝ)) : ℝ × ℝ) ∈ S := ⟨hr, le_rfl⟩
  have hsum : Continuous fun p : ℝ × ℝ => p.1 + p.2 := continuous_fst.add continuous_snd
  have hsumS : MapsTo (fun p : ℝ × ℝ => p.1 + p.2) S (Ici 0) := fun p hp => add_nonneg hp.1 hp.2
  have hflow : ContinuousWithinAt (fun p : ℝ × ℝ => lcFlow Q c B g p.1 (p.1 + p.2) x) S (r, 0) := by
    have h1 := lc_flow_continuous H hg
    have h2 : Continuous (fun p : ℝ × ℝ => ((p.1, p.1 + p.2, x) : ℝ × ℝ × Euc d)) :=
      continuous_fst.prodMk ((continuous_fst.add continuous_snd).prodMk continuous_const)
    have hm : MapsTo (fun p : ℝ × ℝ => ((p.1, p.1 + p.2, x) : ℝ × ℝ × Euc d)) S
        {p : ℝ × ℝ × Euc d | 0 ≤ p.1 ∧ p.1 ≤ p.2.1} := fun p hp => ⟨hp.1, by simpa using hp.2⟩
    have := (h1.comp (f := fun p : ℝ × ℝ => ((p.1, p.1 + p.2, x) : ℝ × ℝ × Euc d))
      h2.continuousOn hm) (r, 0) hr0
    exact this
  have hc : ContinuousWithinAt (fun p : ℝ × ℝ => c (p.1 + p.2)) S (r, 0) :=
    (H.c_cont.comp hsum.continuousOn hsumS) (r, 0) hr0
  have hB : ContinuousWithinAt (fun p : ℝ × ℝ => B (p.1 + p.2) (lcFlow Q c B g p.1 (p.1 + p.2) x))
      S (r, 0) := by
    have hm : MapsTo (fun p : ℝ × ℝ => ((p.1 + p.2, lcFlow Q c B g p.1 (p.1 + p.2) x) : ℝ × Euc d)) S
        (Ici 0 ×ˢ univ) := fun p hp => ⟨add_nonneg hp.1 hp.2, mem_univ _⟩
    have h2 : ContinuousWithinAt (fun p : ℝ × ℝ =>
        ((p.1 + p.2, lcFlow Q c B g p.1 (p.1 + p.2) x) : ℝ × Euc d)) S (r, 0) :=
      (hsum.continuousWithinAt).prodMk hflow
    have hBc := H.B_cont (r + 0, lcFlow Q c B g r (r + 0) x) ⟨by simpa using hr, mem_univ _⟩
    exact ContinuousWithinAt.comp (f := fun p : ℝ × ℝ =>
      ((p.1 + p.2, lcFlow Q c B g p.1 (p.1 + p.2) x) : ℝ × Euc d)) hBc h2 hm
  unfold lcB
  exact ((((lcQ Q).continuous.continuousAt.comp_continuousWithinAt hflow).neg).sub hc).add hB

theorem lc6_drift_lim (H : LcHyp Q 2 Λc ΛB c B) (hg : Continuous g) {r : ℝ} (hr : 0 ≤ r)
    (x : Euc d) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ a h : ℝ, 0 ≤ a → |a - r| < δ → 0 < h → h < δ →
      ‖h⁻¹ • (∫ s in Icc 0 h, lcB Q c B a s (lcFlow Q c B g a (a + s) x)) - lcB Q c B r 0 x‖ ≤ ε := by
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.1 (lc6_drift_cont H hg hr x) ε hε
  refine ⟨δ, hδ, fun a h ha har hh hhδ => ?_⟩
  set Ψ : ℝ → Euc d := fun s => lcB Q c B a s (lcFlow Q c B g a (a + s) x) with hΨ
  have hint : IntegrableOn Ψ (Icc 0 h) :=
    ((lcFlow_isPathSolution H hg ha x).2 h hh.le (WithTop.coe_lt_top h)).2.1
  have hpt : ∀ s ∈ Icc 0 h, ‖Ψ s - lcB Q c B r 0 x‖ ≤ ε := by
    intro s hs
    have := hδ' (x := (a, s)) ⟨ha, hs.1⟩ (by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
      exact max_lt har (lt_of_le_of_lt hs.2 hhδ))
    have e : lcB Q c B r 0 x = lcB Q c B r 0 (lcFlow Q c B g r (r + 0) x) := by
      rw [add_zero, lcFlow_self H hg hr]
    rw [dist_eq_norm] at this
    rw [e]
    exact this.le
  have hI : ∫ s in Icc 0 h, (Ψ s - lcB Q c B r 0 x) = (∫ s in Icc 0 h, Ψ s) - h • lcB Q c B r 0 x := by
    rw [integral_sub hint (integrableOn_const (by simp)), setIntegral_const]
    simp [Real.volume_real_Icc, hh.le]
  have hn := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc 0 h)
    (f := fun s => Ψ s - lcB Q c B r 0 x) (by simp) hpt
  rw [hI] at hn
  simp only [Real.volume_real_Icc, sub_zero, max_eq_left hh.le] at hn
  have : h⁻¹ • (∫ s in Icc 0 h, Ψ s) - lcB Q c B r 0 x =
      h⁻¹ • ((∫ s in Icc 0 h, Ψ s) - h • lcB Q c B r 0 x) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hh.ne', one_smul]
  rw [this, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hh.le)]
  calc h⁻¹ * ‖(∫ s in Icc 0 h, Ψ s) - h • lcB Q c B r 0 x‖ ≤ h⁻¹ * (ε * h) :=
        mul_le_mul_of_nonneg_left hn (inv_nonneg.2 hh.le)
    _ = ε := by field_simp

end Drift

/-! ### Gaussian moments of the noise increment -/

section Gauss

variable {d : ℕ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → Fin d → ℝ} {ν : ℝ → ℝ}

theorem lc6_gauss4 (hW : IsBrownianFiltration P ℱ W) (hν : Continuous ν) (hν0 : ∀ x, 0 ≤ ν x)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (i : Fin d) :
    Integrable (fun ω => (lcNoise W ν b ω i - lcNoise W ν a ω i) ^ 4) P ∧
    ∫ ω, (lcNoise W ν b ω i - lcNoise W ν a ω i) ^ 4 ∂P = 3 * (lcTau ν b - lcTau ν a) ^ 2 := by
  have law := (lc_noise_law hW hν hν0 ha hab).2.1 i
  have hg4 : Integrable (fun x : ℝ => x ^ 4)
      (gaussianReal 0 (lcTau ν b - lcTau ν a).toNNReal) := by
    have := (memLp_id_gaussianReal' (μ := 0) (v := (lcTau ν b - lcTau ν a).toNNReal)
      ((4 : ℕ) : ENNReal) (by simp)).integrable_norm_pow (p := 4) (by norm_num)
    have e : (fun x : ℝ => ‖id x‖ ^ 4) = fun x => x ^ 4 := by
      funext x; simp only [id, Real.norm_eq_abs]; exact Even.pow_abs (by decide) x
    rwa [e] at this
  refine ⟨law.integrable_comp hg4, ?_⟩
  have := law.integral_comp (f := fun x : ℝ => x ^ 4) (by fun_prop)
  simp only [Function.comp_def] at this
  rw [this, integral_pow_four_gaussianReal_zero, Real.coe_toNNReal _
    (sub_nonneg.2 (lcTau_mono hν hν0 hab))]

theorem lc6_gauss (hW : IsBrownianFiltration P ℱ W) (hν : Continuous ν) (hν0 : ∀ x, 0 ≤ ν x)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∀ i, ∫ ω, (lcNoiseE W ν b ω - lcNoiseE W ν a ω) i ∂P = 0) ∧
    (∀ i j, ∫ ω, (lcNoiseE W ν b ω - lcNoiseE W ν a ω) i * (lcNoiseE W ν b ω - lcNoiseE W ν a ω) j ∂P =
      if i = j then lcTau ν b - lcTau ν a else 0) ∧
    Integrable (fun ω => ‖lcNoiseE W ν b ω - lcNoiseE W ν a ω‖ ^ 4) P ∧
    ∫ ω, ‖lcNoiseE W ν b ω - lcNoiseE W ν a ω‖ ^ 4 ∂P ≤ 3 * d ^ 2 * (lcTau ν b - lcTau ν a) ^ 2 := by
  have hc : ∀ ω i, (lcNoiseE W ν b ω - lcNoiseE W ν a ω) i = lcNoise W ν b ω i - lcNoise W ν a ω i :=
    fun ω i => rfl
  simp only [hc]
  have hσ := sub_nonneg.2 (lcTau_mono hν hν0 hab)
  refine ⟨fun i => ?_, fun i j => lc_noise_cov hW hν hν0 ha hab i j, ?_, ?_⟩
  · have law := (lc_noise_law hW hν hν0 ha hab).2.1 i
    have := law.integral_comp (f := fun x : ℝ => x) (by fun_prop)
    simp only [Function.comp_def, integral_id_gaussianReal] at this
    exact this
  all_goals
    have hpt : ∀ ω, ‖lcNoiseE W ν b ω - lcNoiseE W ν a ω‖ ^ 4 ≤
        d * ∑ i, (lcNoise W ν b ω i - lcNoise W ν a ω i) ^ 4 := by
      intro ω
      have h2 : ‖lcNoiseE W ν b ω - lcNoiseE W ν a ω‖ ^ 2 =
          ∑ i, (lcNoise W ν b ω i - lcNoise W ν a ω i) ^ 2 := by
        rw [lc6_norm_sq_eq]; simp only [hc]
      have : ‖lcNoiseE W ν b ω - lcNoiseE W ν a ω‖ ^ 4 =
          (∑ i, (lcNoise W ν b ω i - lcNoise W ν a ω i) ^ 2) ^ 2 := by rw [← h2]; ring
      rw [this]
      have := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun i => (lcNoise W ν b ω i - lcNoise W ν a ω i) ^ 2)
      simpa [← pow_mul] using this
    have hI : Integrable (fun ω => d * ∑ i, (lcNoise W ν b ω i - lcNoise W ν a ω i) ^ 4) P :=
      (integrable_finset_sum _ fun i _ => (lc6_gauss4 hW hν hν0 ha hab i).1).const_mul _
  · refine hI.mono' ?_ (Eventually.of_forall fun ω => ?_)
    · exact ((lc_noiseE_measurable hW b).sub (lc_noiseE_measurable hW a)).norm.pow_const 4
        |>.aestronglyMeasurable
    · rw [Real.norm_of_nonneg (by positivity)]; exact hpt ω
  · have hint4 : Integrable (fun ω => ‖lcNoiseE W ν b ω - lcNoiseE W ν a ω‖ ^ 4) P := by
      refine hI.mono' ?_ (Eventually.of_forall fun ω => ?_)
      · exact ((lc_noiseE_measurable hW b).sub (lc_noiseE_measurable hW a)).norm.pow_const 4
          |>.aestronglyMeasurable
      · rw [Real.norm_of_nonneg (by positivity)]; exact hpt ω
    calc _ ≤ ∫ ω, d * ∑ i, (lcNoise W ν b ω i - lcNoise W ν a ω i) ^ 4 ∂P :=
          integral_mono hint4 hI hpt
      _ = 3 * d ^ 2 * (lcTau ν b - lcTau ν a) ^ 2 := by
          rw [integral_const_mul, integral_finset_sum _ fun i _ => (lc6_gauss4 hW hν hν0 ha hab i).1]
          simp only [(lc6_gauss4 hW hν hν0 ha hab _).2, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          ring

end Gauss

/-! ### The time derivative -/

section Time

variable {d : ℕ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → Fin d → ℝ} {ν : ℝ → ℝ}

/-- The viscosity part: `(τ b - τ a)/(b - a) → 2 ν r`. -/
theorem lc6_tau_lim (hν : Continuous ν) (r : ℝ) :
    Tendsto (fun p : ℝ × ℝ => (lcTau ν p.2 - lcTau ν p.1) / (p.2 - p.1))
      ((𝓝 r ×ˢ 𝓝 r) ⊓ 𝓟 {p : ℝ × ℝ | p.1 < p.2}) (𝓝 (2 * ν r)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 (hν.continuousAt (x := r)) (ε / 4) (by positivity)
  have h1 : Tendsto Prod.fst ((𝓝 r ×ˢ 𝓝 r) ⊓ 𝓟 {p : ℝ × ℝ | p.1 < p.2}) (𝓝 r) :=
    tendsto_fst.mono_left inf_le_left
  have h2 : Tendsto Prod.snd ((𝓝 r ×ˢ 𝓝 r) ⊓ 𝓟 {p : ℝ × ℝ | p.1 < p.2}) (𝓝 r) :=
    tendsto_snd.mono_left inf_le_left
  filter_upwards [h1.eventually (Metric.ball_mem_nhds r hδ), h2.eventually (Metric.ball_mem_nhds r hδ),
    eventually_inf_principal.2 (Eventually.of_forall fun p hp => hp)] with p hp1 hp2 hp3
  have hab : 0 < p.2 - p.1 := sub_pos.2 hp3
  rw [lcTau_sub hν, Real.dist_eq]
  have hb : ‖∫ s in p.1..p.2, (2 * ν s - 2 * ν r)‖ ≤ (ε / 2) * |p.2 - p.1| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
    rw [Set.uIoc_of_le hp3.le] at hs
    have hs1 : dist s r < δ := by
      rw [Real.dist_eq, abs_lt]
      rw [Real.dist_eq, abs_lt] at hp1 hp2
      constructor <;> linarith [hs.1, hs.2]
    have := hδ' hs1
    rw [Real.dist_eq] at this
    rw [Real.norm_eq_abs, show 2 * ν s - 2 * ν r = 2 * (ν s - ν r) by ring, abs_mul]
    norm_num
    linarith
  rw [intervalIntegral.integral_sub (lc3_integrable hν _ _) intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul] at hb
  rw [abs_of_pos hab] at hb
  have e : (∫ x in p.1..p.2, 2 * ν x) / (p.2 - p.1) - 2 * ν r =
      ((∫ x in p.1..p.2, 2 * ν x) - (p.2 - p.1) * (2 * ν r)) / (p.2 - p.1) := by
    field_simp
  rw [e, abs_div, abs_of_pos hab, div_lt_iff₀ hab]
  rw [Real.norm_eq_abs] at hb
  nlinarith

end Time

theorem lc6_inner_gradient {d : ℕ} (h : Euc d → ℝ) (x v : Euc d) :
    inner ℝ v (gradient h x) = fderiv ℝ h x v := by
  rw [real_inner_comm]
  unfold gradient
  exact InnerProductSpace.toDual_symm_apply

theorem lc6_laplacian_eq {d : ℕ} (h : Euc d → ℝ) (y : Euc d) :
    Laplacian.laplacian h y = ∑ i : Fin d, fderiv ℝ (fderiv ℝ h) y (EuclideanSpace.single i 1)
      (EuclideanSpace.single i 1) := by
  have := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (f := h)
    (EuclideanSpace.basisFun (Fin d) ℝ)) y
  rw [this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  simp [EuclideanSpace.basisFun_apply]

theorem lc6_tendsto_snd {X V α : Type*} [TopologicalSpace X] [TopologicalSpace V] {F : ℝ × X → V}
    {r : ℝ} {x : X} (hF : ContinuousAt F (r, x)) {ℓ : Filter α} {q : α → ℝ} (hq : Tendsto q ℓ (𝓝 r)) :
    Tendsto (fun a => F (q a, x)) ℓ (𝓝 (F (r, x))) :=
  hF.tendsto.comp (hq.prodMk_nhds tendsto_const_nhds)

section Assembly

variable {d : ℕ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → Fin d → ℝ} {ν : ℝ → ℝ} {Q : Matrix (Fin d) (Fin d) ℝ}
  {Λc ΛB : ℝ} {c : ℝ → Euc d} {B : ℝ → Euc d → Euc d} {f : Euc d → ℝ} {M K t νs : ℝ}
  (hW : IsBrownianFiltration P ℱ W) (hν : Continuous ν) (hν0 : ∀ x, 0 ≤ ν x) (hνs : ∀ x, ν x ≤ νs)
  (H : LcHyp Q 2 Λc ΛB c B)
  (hf : ContDiff ℝ 2 f) (hM : ∀ i ≤ 2, ∀ y, ‖iteratedFDeriv ℝ i f y‖ ≤ M) (hK1 : 1 ≤ K)
  (hK : ∀ {g : ℝ → Euc d}, Continuous g → ∀ {r : ℝ}, 0 ≤ r → r ≤ t → ∀ (x : Euc d) (j : ℕ),
    1 ≤ j → j ≤ 3 → ‖iteratedFDeriv ℝ j (lcFlow Q c B g r t) x‖ ≤ K) (ht : 0 ≤ t)

include hW hν hν0 hνs H hf hM hK1 hK ht

theorem lc6_timederiv {r : ℝ} (hr : r ∈ Ioo 0 t) (x : Euc d) :
    HasDerivAt (fun r' => lcSg P W ν Q c B r' t f x)
      (-(ν r * Laplacian.laplacian (lcSg P W ν Q c B r t f) x +
        inner ℝ (-(Torus.matVec Q x) - c r + B r x) (gradient (lcSg P W ν Q c B r t f) x))) r := by
  have hGm : ∀ v, Measurable fun ω => lcNoiseE W ν v ω := fun v => lc_noiseE_measurable hW v
  have hGc : ∀ ω, Continuous (fun v => lcNoiseE W ν v ω) := fun ω => lc_noiseE_cont hW hν ω
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by norm_num) 0)
  have hνs0 : 0 ≤ νs := (hν0 0).trans (hνs 0)
  obtain ⟨-, hu1, hu2⟩ := lc6_u_cont hW hν H hf hM hK1 hK ht
  have hmemS : Icc 0 t ×ˢ (univ : Set (Euc d)) ∈ 𝓝 (r, x) :=
    prod_mem_nhds (Icc_mem_nhds hr.1 hr.2) univ_mem
  set ℓ : Filter (ℝ × ℝ) := (𝓝 r ×ˢ 𝓝 r) ⊓ 𝓟 {p : ℝ × ℝ | p.1 ≤ r ∧ r ≤ p.2 ∧ p.1 < p.2} with hℓ
  have hℓ1 : Tendsto Prod.fst ℓ (𝓝 r) := tendsto_fst.mono_left inf_le_left
  have hℓ2 : Tendsto Prod.snd ℓ (𝓝 r) := tendsto_snd.mono_left inf_le_left
  have hℓ3 : ∀ᶠ p in ℓ, p.1 ≤ r ∧ r ≤ p.2 ∧ p.1 < p.2 :=
    eventually_inf_principal.2 (Eventually.of_forall fun p hp => hp)
  have hdom : ∀ᶠ p in ℓ, 0 < p.1 ∧ p.2 < t :=
    (hℓ1.eventually (Ioi_mem_nhds hr.1)).and (hℓ2.eventually (Iio_mem_nhds hr.2))
  have hh : Tendsto (fun p : ℝ × ℝ => p.2 - p.1) ℓ (𝓝 0) := by simpa using hℓ2.sub hℓ1
  have hh0 : ∀ᶠ p in ℓ, 0 < p.2 - p.1 := hℓ3.mono fun p hp => sub_pos.2 hp.2.2
  have hgood : ∀ᶠ p in ℓ, (0 < p.1 ∧ p.2 < t) ∧ (p.1 ≤ r ∧ r ≤ p.2 ∧ p.1 < p.2) := hdom.and hℓ3
  -- the noise supremum
  obtain ⟨C1, hC1, hwb⟩ := lc6_w_bound Q Λc ΛB t x
  set s : Ω → ℝ := fun ω => 1 + ⨆ v ∈ Icc (0 : ℝ) t, ‖lcNoiseE W ν v ω‖ with hs
  have hs1 : ∀ ω, 1 ≤ s ω := fun ω => by
    have := lc3_sup_nonneg (g := fun v => lcNoiseE W ν v ω) t
    simp only [hs]; linarith
  have hsm : Measurable s := measurable_const.add (lc_noise_sup_measurable hW hν t)
  obtain ⟨Cm, hCm⟩ := lc_sup_moment.{u} d 4 t νs
  have hs4 : Integrable (fun ω => s ω ^ 4) P := (hCm P ℱ W ν hW hν fun r => ⟨hν0 r, hνs r⟩).1
  -- the hypotheses of `lc6_expansion`
  have hΔm : ∀ᶠ p in ℓ, Measurable (fun ω => lcNoiseE W ν p.2 ω - lcNoiseE W ν p.1 ω) :=
    Eventually.of_forall fun p => (hGm _).sub (hGm _)
  have hwm : ∀ᶠ p in ℓ, Measurable (fun ω => lcFlow Q c B (fun v => lcNoiseE W ν v ω) p.1 p.2 x - x -
      (lcNoiseE W ν p.2 ω - lcNoiseE W ν p.1 ω)) := by
    filter_upwards [hgood] with p hp
    have hab : p.1 ≤ p.2 := hp.2.2.2.le
    have := (lc4_meas_flow H hGm hGc hp.1.1.le hab).comp (measurable_id.prodMk (measurable_const (a := x)))
    exact (this.sub_const x).sub ((hGm _).sub (hGm _))
  have hgauss : ∀ᶠ p in ℓ, (∀ i, ∫ ω, (lcNoiseE W ν p.2 ω - lcNoiseE W ν p.1 ω) i ∂P = 0) ∧
      (∀ i j, ∫ ω, (lcNoiseE W ν p.2 ω - lcNoiseE W ν p.1 ω) i *
        (lcNoiseE W ν p.2 ω - lcNoiseE W ν p.1 ω) j ∂P =
        if i = j then lcTau ν p.2 - lcTau ν p.1 else 0) ∧
      Integrable (fun ω => ‖lcNoiseE W ν p.2 ω - lcNoiseE W ν p.1 ω‖ ^ 4) P ∧
      ∫ ω, ‖lcNoiseE W ν p.2 ω - lcNoiseE W ν p.1 ω‖ ^ 4 ∂P ≤
        3 * d ^ 2 * (lcTau ν p.2 - lcTau ν p.1) ^ 2 := by
    filter_upwards [hgood] with p hp
    exact lc6_gauss hW hν hν0 hp.1.1.le hp.2.2.2.le
  have hσ : ∀ᶠ p in ℓ, 0 ≤ lcTau ν p.2 - lcTau ν p.1 ∧ lcTau ν p.2 - lcTau ν p.1 ≤ 2 * νs * (p.2 - p.1) := by
    filter_upwards [hℓ3] with p hp
    exact ⟨sub_nonneg.2 (lcTau_mono hν hν0 hp.2.2.le), lcTau_sub_le hν hνs hp.2.2.le⟩
  have hσlim : Tendsto (fun p : ℝ × ℝ => (lcTau ν p.2 - lcTau ν p.1) / (p.2 - p.1)) ℓ (𝓝 (2 * ν r)) :=
    (lc6_tau_lim hν r).mono_left (inf_le_inf_left _ (principal_mono.2 fun p hp => hp.2.2))
  have hw : ∀ᶠ p in ℓ, ∀ ω, ‖lcFlow Q c B (fun v => lcNoiseE W ν v ω) p.1 p.2 x - x -
      (lcNoiseE W ν p.2 ω - lcNoiseE W ν p.1 ω)‖ ≤ (p.2 - p.1) * C1 * s ω := by
    filter_upwards [hgood, hh0] with p hp hp0 ω
    have hrepr := lc6_drift_repr H (hGc ω) hp.1.1.le hp0.le x
    rw [add_sub_cancel] at hrepr
    have e : lcFlow Q c B (fun v => lcNoiseE W ν v ω) p.1 p.2 x - x -
        (lcNoiseE W ν p.2 ω - lcNoiseE W ν p.1 ω) =
        ∫ s in Icc 0 (p.2 - p.1), lcB Q c B p.1 s
          (lcFlow Q c B (fun v => lcNoiseE W ν v ω) p.1 (p.1 + s) x) := by
      rw [hrepr]; abel
    rw [e]
    exact hwb H (hGc ω) hp.1.1.le hp0.le (by linarith [hp.1.2])
  have hwlim : ∀ ω, Tendsto (fun p : ℝ × ℝ => (p.2 - p.1)⁻¹ • (lcFlow Q c B (fun v => lcNoiseE W ν v ω) p.1 p.2 x - x -
      (lcNoiseE W ν p.2 ω - lcNoiseE W ν p.1 ω))) ℓ (𝓝 (lcB Q c B r 0 x)) := by
    intro ω
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := lc6_drift_lim H (hGc ω) hr.1.le x (half_pos hε)
    filter_upwards [hgood, hh0, hℓ1.eventually (Metric.ball_mem_nhds r hδ),
      hh.eventually (Iio_mem_nhds hδ)] with p hp hp0 hp1 hp2
    have hrepr := lc6_drift_repr H (hGc ω) hp.1.1.le hp0.le x
    rw [add_sub_cancel] at hrepr
    have e : lcFlow Q c B (fun v => lcNoiseE W ν v ω) p.1 p.2 x - x -
        (lcNoiseE W ν p.2 ω - lcNoiseE W ν p.1 ω) =
        ∫ s in Icc 0 (p.2 - p.1), lcB Q c B p.1 s
          (lcFlow Q c B (fun v => lcNoiseE W ν v ω) p.1 (p.1 + s) x) := by
      rw [hrepr]; abel
    rw [e, dist_eq_norm]
    have := hδ' p.1 (p.2 - p.1) hp.1.1.le (by simpa [Real.dist_eq] using hp1) hp0 hp2
    linarith
  have hgI : ∀ᶠ p in ℓ, p.2 ∈ Icc 0 t := hgood.mono fun p hp =>
    ⟨by linarith [hp.2.2.1, hr.1], hp.1.2.le⟩
  have hg : ∀ᶠ p in ℓ, ContDiff ℝ 2 (lcSg P W ν Q c B p.2 t f) :=
    hgI.mono fun p hp => (lc6_reg hW hν H hf hM hK1 hK hp).1
  have hgb : ∀ᶠ p in ℓ, ∀ y, ‖lcSg P W ν Q c B p.2 t f y‖ ≤ 2 * M * K ^ 2 :=
    hgI.mono fun p hp y => by
      have := (lc6_reg hW hν H hf hM hK1 hK hp).2.2 0 (by norm_num) y
      rwa [norm_iteratedFDeriv_zero] at this
  have hg2 : ∀ᶠ p in ℓ, ∀ y, ‖fderiv ℝ (fderiv ℝ (lcSg P W ν Q c B p.2 t f)) y‖ ≤ 2 * M * K ^ 2 :=
    hgI.mono fun p hp y => by
      rw [lc6_norm_fd2]; exact (lc6_reg hW hν H hf hM hK1 hK hp).2.2 2 le_rfl y
  have hξ : Tendsto (fun p : ℝ × ℝ => fderiv ℝ (lcSg P W ν Q c B p.2 t f) x) ℓ
      (𝓝 (fderiv ℝ (lcSg P W ν Q c B r t f) x)) :=
    lc6_tendsto_snd (F := fun q : ℝ × Euc d => fderiv ℝ (lcSg P W ν Q c B q.1 t f) q.2)
      (hu1.continuousAt hmemS) hℓ2
  have hHc : ContinuousAt (fun q : ℝ × Euc d => fderiv ℝ (fderiv ℝ (lcSg P W ν Q c B q.1 t f)) q.2) (r, x) :=
    hu2.continuousAt hmemS
  have hH : Tendsto (fun p : ℝ × ℝ => fderiv ℝ (fderiv ℝ (lcSg P W ν Q c B p.2 t f)) x) ℓ
      (𝓝 (fderiv ℝ (fderiv ℝ (lcSg P W ν Q c B r t f)) x)) :=
    lc6_tendsto_snd (F := fun q : ℝ × Euc d => fderiv ℝ (fderiv ℝ (lcSg P W ν Q c B q.1 t f)) q.2)
      hHc hℓ2
  have hmod : ∀ ε > 0, ∃ δ > 0, ∀ᶠ p in ℓ, ∀ y, ‖y - x‖ < δ →
      ‖fderiv ℝ (fderiv ℝ (lcSg P W ν Q c B p.2 t f)) y -
        fderiv ℝ (fderiv ℝ (lcSg P W ν Q c B p.2 t f)) x‖ ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := (Metric.continuousAt_iff (f := fun q : ℝ × Euc d =>
      fderiv ℝ (fderiv ℝ (lcSg P W ν Q c B q.1 t f)) q.2) (a := (r, x))).1 hHc (ε / 2) (half_pos hε)
    refine ⟨δ, hδ, ?_⟩
    filter_upwards [hℓ2.eventually (Metric.ball_mem_nhds r hδ)] with p hp y hy
    have h1 := hδ' (x := (p.2, y)) (by
      rw [Prod.dist_eq]; exact max_lt hp (by simpa [dist_eq_norm] using hy))
    have h2 := hδ' (x := (p.2, x)) (by
      rw [Prod.dist_eq, dist_self]; exact max_lt hp hδ)
    have h3 := dist_triangle (fderiv ℝ (fderiv ℝ (lcSg P W ν Q c B p.2 t f)) y)
      (fderiv ℝ (fderiv ℝ (lcSg P W ν Q c B r t f)) x)
      (fderiv ℝ (fderiv ℝ (lcSg P W ν Q c B p.2 t f)) x)
    have h4 := dist_comm (fderiv ℝ (fderiv ℝ (lcSg P W ν Q c B r t f)) x)
      (fderiv ℝ (fderiv ℝ (lcSg P W ν Q c B p.2 t f)) x)
    calc _ = dist (fderiv ℝ (fderiv ℝ (lcSg P W ν Q c B p.2 t f)) y)
          (fderiv ℝ (fderiv ℝ (lcSg P W ν Q c B p.2 t f)) x) :=
        (dist_eq_norm (fderiv ℝ (fderiv ℝ (lcSg P W ν Q c B p.2 t f)) y)
          (fderiv ℝ (fderiv ℝ (lcSg P W ν Q c B p.2 t f)) x)).symm
      _ ≤ ε := by linarith
  have key := lc6_expansion (P := P) (ℓ := ℓ) x (fun p => p.2 - p.1)
    (fun p => lcTau ν p.2 - lcTau ν p.1) (fun p ω => lcNoiseE W ν p.2 ω - lcNoiseE W ν p.1 ω)
    (fun p ω => lcFlow Q c B (fun v => lcNoiseE W ν v ω) p.1 p.2 x - x -
      (lcNoiseE W ν p.2 ω - lcNoiseE W ν p.1 ω)) (fun p => lcSg P W ν Q c B p.2 t f) (s := s)
    (fderiv ℝ (lcSg P W ν Q c B r t f) x) (fderiv ℝ (fderiv ℝ (lcSg P W ν Q c B r t f)) x)
    (lcB Q c B r 0 x) (ν r) (C1 := C1) (m2 := 2 * M * K ^ 2) (νs := νs) (M0 := 2 * M * K ^ 2)
    (by positivity) hh0 hh hΔm hwm (hgauss.mono fun p h => h.1) (hgauss.mono fun p h => h.2.1)
    (hgauss.mono fun p h => ⟨h.2.2.1, h.2.2.2⟩) hσ hνs0 hσlim hs1 hsm hs4 hw hC1 hwlim hg hgb hg2
    hξ hH hmod
  -- Markov property: `u a - u b = E[u_b(x + Δ + w) - u_b(x)]`
  have hbdf : ∀ y, ‖f y‖ ≤ M := fun y => by
    simpa [norm_iteratedFDeriv_zero] using hM 0 (by norm_num) y
  have hmark : ∀ᶠ p in ℓ, (∫ ω, (lcSg P W ν Q c B p.2 t f (x + ((lcNoiseE W ν p.2 ω - lcNoiseE W ν p.1 ω) +
      (lcFlow Q c B (fun v => lcNoiseE W ν v ω) p.1 p.2 x - x -
        (lcNoiseE W ν p.2 ω - lcNoiseE W ν p.1 ω)))) - lcSg P W ν Q c B p.2 t f x) ∂P) / (p.2 - p.1) =
      (lcSg P W ν Q c B p.1 t f x - lcSg P W ν Q c B p.2 t f x) / (p.2 - p.1) := by
    filter_upwards [hgood] with p hp
    congr 1
    have hab : p.1 ≤ p.2 := hp.2.2.2.le
    have hm := lc_markov hW hν hν0 H hf.continuous hbdf hp.1.1.le hab hp.1.2.le x
    have hIc : p.2 ∈ Icc 0 t := ⟨by linarith [hp.2.2.1, hr.1], hp.1.2.le⟩
    have hucont : Continuous (lcSg P W ν Q c B p.2 t f) :=
      ((lc6_reg hW hν H hf hM hK1 hK hIc).1).continuous
    have hint : Integrable (fun ω => lcSg P W ν Q c B p.2 t f
        (lcFlow Q c B (fun v => lcNoiseE W ν v ω) p.1 p.2 x)) P := by
      refine Integrable.of_bound (C := 2 * M * K ^ 2) (hucont.measurable.comp
        ((lc4_meas_flow H hGm hGc hp.1.1.le hab).comp
          (measurable_id.prodMk (measurable_const (a := x))))).aestronglyMeasurable
        (Eventually.of_forall fun ω => ?_)
      have := (lc6_reg hW hν H hf hM hK1 hK hIc).2.2 0 (by norm_num)
        (lcFlow Q c B (fun v => lcNoiseE W ν v ω) p.1 p.2 x)
      rwa [norm_iteratedFDeriv_zero] at this
    have e : ∀ ω, x + ((lcNoiseE W ν p.2 ω - lcNoiseE W ν p.1 ω) +
        (lcFlow Q c B (fun v => lcNoiseE W ν v ω) p.1 p.2 x - x -
          (lcNoiseE W ν p.2 ω - lcNoiseE W ν p.1 ω))) =
        lcFlow Q c B (fun v => lcNoiseE W ν v ω) p.1 p.2 x := fun ω => by abel
    simp_rw [e]
    rw [integral_sub hint (integrable_const _), integral_const, hm]
    simp [lcSg]
  have hN := key.congr' hmark
  -- the slope
  rw [hasDerivAt_iff_tendsto_slope]
  have hq : Tendsto (fun r' : ℝ => ((min r r', max r r') : ℝ × ℝ)) (𝓝[≠] r) ℓ := by
    rw [hℓ]
    refine tendsto_inf.2 ⟨?_, tendsto_principal.2 ?_⟩
    · have h0 : Tendsto (fun r' : ℝ => ((min r r', max r r') : ℝ × ℝ)) (𝓝 r) (𝓝 (r, r)) := by
        have := ((continuous_const.min continuous_id).prodMk
          (continuous_const.max continuous_id) : Continuous fun r' : ℝ => ((min r r', max r r') : ℝ × ℝ))
        simpa using this.tendsto r
      rw [← nhds_prod_eq]
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r' hr'
      exact ⟨min_le_left _ _, le_max_left _ _, min_lt_max.2 (Ne.symm hr')⟩
  have hmain := (hN.comp hq).neg
  have hξβ : fderiv ℝ (lcSg P W ν Q c B r t f) x (lcB Q c B r 0 x) =
      inner ℝ (-(Torus.matVec Q x) - c r + B r x) (gradient (lcSg P W ν Q c B r t f) x) := by
    rw [lc6_inner_gradient]
    simp [lcB, lcQ_apply]
  rw [lc6_laplacian_eq, ← hξβ]
  have htarget : -(ν r * ∑ i, fderiv ℝ (fderiv ℝ (lcSg P W ν Q c B r t f)) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) +
        fderiv ℝ (lcSg P W ν Q c B r t f) x (lcB Q c B r 0 x)) =
      -(fderiv ℝ (lcSg P W ν Q c B r t f) x (lcB Q c B r 0 x) + ν r * ∑ i,
        fderiv ℝ (fderiv ℝ (lcSg P W ν Q c B r t f)) x (EuclideanSpace.single i 1)
          (EuclideanSpace.single i 1)) := by ring
  rw [htarget]
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r' hr'
  have hr'' : r' ≠ r := hr'
  simp only [Function.comp, slope_def_field]
  rcases lt_or_gt_of_ne hr'' with hlt | hgt
  · rw [min_eq_right hlt.le, max_eq_left hlt.le]
    have : r - r' ≠ 0 := by linarith
    have : r' - r ≠ 0 := by linarith
    field_simp
    ring
  · rw [min_eq_left hgt.le, max_eq_right hgt.le]
    have : r' - r ≠ 0 := by linarith
    field_simp
    ring

end Assembly

/-! ### The main statements -/

section Final

variable {d : ℕ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → Fin d → ℝ} {ν : ℝ → ℝ} {Q : Matrix (Fin d) (Fin d) ℝ}
  {Λc ΛB : ℝ} {c : ℝ → Euc d} {B : ℝ → Euc d → Euc d} {f : Euc d → ℝ} {M νs t : ℝ}

/-- **LC-6 (backward equation, derivative form).**  For `LcHyp Q 2 Λc ΛB c B`, `0 ≤ ν ≤ ν*` continuous,
`f ∈ C²` with `f, Df, D²f` bounded by `M`, `0 ≤ t` and `r ∈ (0,t)`:
`∂_r u + ν_r Δu + b_r·∇u = 0` at `(r,x)` for `u = lcSg P W ν Q c B · t f`,
`b_r(x) = -Qx - c_r + B_r(x)`. -/
theorem lc_backward_hasDerivAt (hW : IsBrownianFiltration P ℱ W) (hν : Continuous ν)
    (hν0 : ∀ x, 0 ≤ ν x) (hνs : ∀ x, ν x ≤ νs) (H : LcHyp Q 2 Λc ΛB c B) (ht : 0 ≤ t)
    (hf : ContDiff ℝ 2 f) (hM : ∀ i ≤ 2, ∀ y, ‖iteratedFDeriv ℝ i f y‖ ≤ M) {r : ℝ}
    (hr : r ∈ Ioo 0 t) (x : Euc d) :
    HasDerivAt (fun r' => lcSg P W ν Q c B r' t f x)
      (-(ν r * Laplacian.laplacian (lcSg P W ν Q c B r t f) x +
        inner ℝ (-(Torus.matVec Q x) - c r + B r x) (gradient (lcSg P W ν Q c B r t f) x))) r := by
  obtain ⟨K, hK1, hK⟩ := lc6_flow_bound Q Λc ΛB t ht
  exact lc6_timederiv hW hν hν0 hνs H hf hM hK1
    (fun {g} hg {r} hr0 hrt x j h1 h2 => hK H hg hr0 hrt le_rfl x j h1 h2) ht hr x

/-- **LC-6 (backward equation).**  `u r = lcSg P W ν Q c B r t f` is a bounded classical backward solution
of `∂_r u + ν_r Δu + b_r·∇u = 0`, `u t = f` in the sense of `IsLocalBackwardSolution`, under the
hypotheses of `lc_backward_hasDerivAt`. -/
theorem lc_backward (hW : IsBrownianFiltration P ℱ W) (hν : Continuous ν)
    (hν0 : ∀ x, 0 ≤ ν x) (hνs : ∀ x, ν x ≤ νs) (H : LcHyp Q 2 Λc ΛB c B) (ht : 0 ≤ t)
    (hf : ContDiff ℝ 2 f) (hM : ∀ i ≤ 2, ∀ y, ‖iteratedFDeriv ℝ i f y‖ ≤ M) :
    IsLocalBackwardSolution ν (fun r x => -(Torus.matVec Q x) - c r + B r x) t f
      (fun r => lcSg P W ν Q c B r t f) := by
  obtain ⟨K, hK1, hK⟩ := lc6_flow_bound Q Λc ΛB t ht
  have hK' : ∀ {g : ℝ → Euc d}, Continuous g → ∀ {r : ℝ}, 0 ≤ r → r ≤ t → ∀ (x : Euc d) (j : ℕ),
      1 ≤ j → j ≤ 3 → ‖iteratedFDeriv ℝ j (lcFlow Q c B g r t) x‖ ≤ K :=
    fun {g} hg {r} hr0 hrt x j h1 h2 => hK H hg hr0 hrt le_rfl x j h1 h2
  have hGc : ∀ ω, Continuous (fun v => lcNoiseE W ν v ω) := fun ω => lc_noiseE_cont hW hν ω
  refine ⟨fun r hr => (lc6_reg hW hν H hf hM hK1 hK' hr).1, ⟨2 * M * K ^ 2, fun r hr x => ?_⟩, ?_, ?_,
    fun x r hr => lc_backward_hasDerivAt hW hν hν0 hνs H ht hf hM hr x⟩
  · have := (lc6_reg hW hν H hf hM hK1 hK' hr).2.2 0 (by norm_num) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  · obtain ⟨h1, -, -⟩ := lc6_u_cont hW hν H hf hM hK1 hK' ht
    exact h1.comp_continuous (f := fun p : Icc (0 : ℝ) t × Euc d => ((p.1 : ℝ), p.2))
      (by fun_prop) fun p => ⟨p.1.2, mem_univ _⟩
  · funext x
    simp [lcSg, lcFlow_self H (hGc _) ht]

end Final



end HRS.MS.Lc
