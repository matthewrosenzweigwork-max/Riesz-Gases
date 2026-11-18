import HRS.MS.LcNoiseAux2
import HRS.MS.LcWtAux4
import HRS.MS.PoisSgAux2

/-!
# LC-4, part 1: the semigroup `lcSg` and joint measurability of the pathwise flow

Setting (supplement S4.11/S4.12, "engine").  For a Brownian filtration `(P, ℱ, W)`, a continuous
viscosity `ν`, a matrix `Q` and data `c, B`, the semigroup of the time-dependent drift
`b_v(y) = -Q y - c_v + B_v(y)` with the time-changed noise `G = lcNoiseE W ν` is
`lcSg P W ν Q c B r t g x = ∫ g (lcFlow Q c B (G · ω) r t x) dP(ω)` (`lcSg`).

This file proves the joint measurability of `(ω, x) ↦ lcFlow Q c B (G ω) r t x` for any family of
continuous noise paths `G ω` that is measurable in `ω` (`lc4_meas_flow`).  Route (as for `sg_measurable_flowMap`
of `PoisSgAux1`): the flow is a pointwise limit of Picard iterates of the random ODE, each of which is
jointly measurable by the Caratheodory lemma and measurability of parametric integrals.  The drift is
clamped to times `τ ≥ 0` (`max τ 0`) inside the iterates, so that the joint continuity on `Ici 0 × ℝ^d`
of `LcHyp` suffices.

Helper lemmas carry the prefix `lc4_`.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

noncomputable section

namespace HRS.MS.Lc

variable {d : ℕ}

/-! ### Definition of the semigroup -/

/-- The engine semigroup `lcSg P W ν Q c B r t g x = ∫ g (X_t^{r,x}) dP`, where `X^{r,x} =
lcFlow Q c B (G · ω) r · x` is the pathwise flow driven by the time-changed noise
`G v ω = lcNoiseE W ν v ω`. -/
def lcSg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : ℝ≥0 → Ω → Fin d → ℝ) (ν : ℝ → ℝ)
    (Q : Matrix (Fin d) (Fin d) ℝ) (c : ℝ → Euc d) (B : ℝ → Euc d → Euc d) (r t : ℝ)
    (g : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∫ ω, g (lcFlow Q c B (fun v => lcNoiseE W ν v ω) r t x) ∂P

section Meas

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Measurability of the noise functionals -/

section Noise

variable (Q : Matrix (Fin d) (Fin d) ℝ) {G : Ω → ℝ → Euc d}

theorem lc4_meas_G (hGm : ∀ v, Measurable fun ω => G ω v) (hGc : ∀ ω, Continuous (G ω)) :
    Measurable (fun p : ℝ × Ω => G p.2 p.1) :=
  measurable_uncurry_of_continuous_of_measurable (u := fun (v : ℝ) (ω : Ω) => G ω v)
    (fun ω => hGc ω) hGm

theorem lc4_meas_lcU_fixed (hGm : ∀ v, Measurable fun ω => G ω v)
    (hGc : ∀ ω, Continuous (G ω)) (r v : ℝ) : Measurable (fun ω => lcU Q (G ω) r v) := by
  have hG := lc4_meas_G hGm hGc
  unfold lcU
  have h1 : Continuous fun u : ℝ => NormedSpace.exp ((-(v - u)) • lcQ Q) :=
    NormedSpace.exp_continuous.comp ((continuous_const.sub continuous_id).neg.smul continuous_const)
  have hf : Measurable (fun p : ℝ × Ω =>
      (NormedSpace.exp ((-(v - p.1)) • lcQ Q)) (lcQ Q (G p.2 p.1 - G p.2 r))) := by
    have hA : Measurable fun p : ℝ × Ω => NormedSpace.exp ((-(v - p.1)) • lcQ Q) :=
      h1.measurable.comp measurable_fst
    have hv : Measurable fun p : ℝ × Ω => lcQ Q (G p.2 p.1 - G p.2 r) :=
      (lcQ Q).continuous.measurable.comp (hG.sub ((hGm r).comp measurable_snd))
    exact (continuous_fst.clm_apply continuous_snd).measurable.comp (hA.prodMk hv)
  have hI := PoisSg.sg_meas_intervalIntegral (f := fun (u : ℝ) (ω : Ω) =>
    (NormedSpace.exp ((-(v - u)) • lcQ Q)) (lcQ Q (G ω u - G ω r))) hf.stronglyMeasurable r v
  exact ((hGm v).sub (hGm r)).sub hI.measurable

theorem lc4_meas_lcU (hGm : ∀ v, Measurable fun ω => G ω v)
    (hGc : ∀ ω, Continuous (G ω)) (r : ℝ) :
    Measurable (fun p : ℝ × Ω => lcU Q (G p.2) r p.1) :=
  measurable_uncurry_of_continuous_of_measurable (u := fun (v : ℝ) (ω : Ω) => lcU Q (G ω) r v)
    (fun ω => lcU_continuous_v Q (hGc ω) r) (lc4_meas_lcU_fixed Q hGm hGc r)

end Noise

/-! ### Picard iterates of a family of ODEs -/

/-- Picard iterates of `Z' = D ω (τ, Z)`, `Z_0 = x` (time clamped to `τ ≥ 0` inside the drift). -/
def lc4Pic (D : Ω → ℝ → Euc d → Euc d) : ℕ → ℝ → Ω → Euc d → Euc d
  | 0, _, _, x => x
  | n + 1, s, ω, x => x + ∫ τ in (0 : ℝ)..s, D ω (max τ 0) (lc4Pic D n τ ω x)

theorem lc4_pic_cont {D : Ω → ℝ → Euc d → Euc d} (ω : Ω)
    (hDc : Continuous fun p : ℝ × Euc d => D ω (max p.1 0) p.2) (n : ℕ) (x : Euc d) :
    Continuous fun s => lc4Pic D n s ω x := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have hc : Continuous fun r => D ω (max r 0) (lc4Pic D n r ω x) :=
      hDc.comp (continuous_id.prodMk ih)
    exact continuous_const.add (intervalIntegral.continuous_primitive
      (fun a b => hc.intervalIntegrable a b) 0)

theorem lc4_pic_meas {D : Ω → ℝ → Euc d → Euc d}
    (hDc : ∀ ω, Continuous fun p : ℝ × Euc d => D ω (max p.1 0) p.2)
    (hDm : Measurable fun p : ℝ × (Ω × Euc d) => D p.2.1 (max p.1 0) p.2.2) (n : ℕ) (s : ℝ) :
    Measurable (fun p : Ω × Euc d => lc4Pic D n s p.1 p.2) := by
  induction n generalizing s with
  | zero => exact measurable_snd
  | succ n ih =>
    have hj : Measurable (fun p : ℝ × (Ω × Euc d) => lc4Pic D n p.1 p.2.1 p.2.2) :=
      measurable_uncurry_of_continuous_of_measurable
        (u := fun (r : ℝ) (p : Ω × Euc d) => lc4Pic D n r p.1 p.2)
        (fun p => lc4_pic_cont p.1 (hDc p.1) n p.2) ih
    have hg : Measurable (fun p : ℝ × (Ω × Euc d) =>
        D p.2.1 (max p.1 0) (lc4Pic D n p.1 p.2.1 p.2.2)) := by
      have : Measurable (fun p : ℝ × (Ω × Euc d) =>
          (((p.1, p.2.1, lc4Pic D n p.1 p.2.1 p.2.2)) : ℝ × (Ω × Euc d))) :=
        measurable_fst.prodMk (measurable_fst.comp measurable_snd |>.prodMk hj)
      exact hDm.comp this
    have hI := PoisSg.sg_meas_intervalIntegral (f := fun r (p : Ω × Euc d) =>
      D p.1 (max r 0) (lc4Pic D n r p.1 p.2)) hg.stronglyMeasurable 0 s
    exact measurable_snd.add hI.measurable

/-- Pointwise convergence of the Picard iterates to the chosen solution `lcZ` (`t ≥ 0`). -/
theorem lc4_pic_tendsto {D : Ω → ℝ → Euc d → Euc d} (ω : Ω) (hD : IsLipschitzDrift (D ω))
    (hDc : Continuous fun p : ℝ × Euc d => D ω (max p.1 0) p.2) (x : Euc d) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => lc4Pic D n t ω x) atTop (𝓝 (lcZ (D ω) x t)) := by
  set Z := lcZ (D ω) x with hZdef
  have hZc : ContinuousOn Z (Icc 0 t) := lcZ_cont hD x ht
  obtain ⟨L, hL⟩ := hD.lip t
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn
    ((continuousOn_const (c := x)).sub hZc)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 ⟨le_rfl, ht⟩)
  have hZeq : ∀ r ∈ Icc (0 : ℝ) t, Z r = x + ∫ s in (0 : ℝ)..r, D ω (max s 0) (Z s) := by
    intro r hr
    show lcZ (D ω) x r = _
    rw [lcZ_eq hD x hr.1, setIntegral_Icc_eq_interval hr.1]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hr.1] at hs
    simp only [max_eq_left hs.1]
    rfl
  have hYc : ∀ n : ℕ, Continuous fun s => lc4Pic D n s ω x :=
    fun n => lc4_pic_cont ω hDc n x
  have hbd : ∀ n : ℕ, ∀ r ∈ Icc (0 : ℝ) t,
      ‖lc4Pic D n r ω x - Z r‖ ≤ K * (L * r) ^ n / (n.factorial : ℝ) := by
    intro n
    induction n with
    | zero =>
      intro r hr
      simpa [lc4Pic] using hK r hr
    | succ n ih =>
      intro r hr
      have hr0 : 0 ≤ r := hr.1
      have hsub : Icc (0 : ℝ) r ⊆ Icc 0 t := Icc_subset_Icc_right hr.2
      have h1 : Continuous fun s => D ω (max s 0) (lc4Pic D n s ω x) :=
        hDc.comp (continuous_id.prodMk (hYc n))
      have h2 : ContinuousOn (fun s => D ω (max s 0) (Z s)) (Icc 0 t) :=
        hDc.comp_continuousOn (continuousOn_id.prodMk hZc)
      have h2i : IntervalIntegrable (fun s => D ω (max s 0) (Z s)) volume 0 r :=
        (h2.mono hsub).intervalIntegrable_of_Icc hr0
      have h1i := h1.intervalIntegrable (μ := volume) 0 r
      have e : lc4Pic D (n + 1) r ω x - Z r = ∫ s in (0 : ℝ)..r,
          (D ω (max s 0) (lc4Pic D n s ω x) - D ω (max s 0) (Z s)) := by
        rw [intervalIntegral.integral_sub h1i h2i, hZeq r hr]
        simp only [lc4Pic]
        abel
      rw [e]
      have hg : Continuous fun s : ℝ => (L : ℝ) * (K * (L * s) ^ n / (n.factorial : ℝ)) := by
        fun_prop
      refine (intervalIntegral.norm_integral_le_of_norm_le hr0 (g := fun s : ℝ =>
        (L : ℝ) * (K * (L * s) ^ n / (n.factorial : ℝ))) (Eventually.of_forall fun s hs => ?_)
        (hg.intervalIntegrable 0 r)).trans ?_
      · have hs' : s ∈ Icc (0 : ℝ) t := ⟨hs.1.le, hs.2.trans hr.2⟩
        have := (hL s hs').dist_le_mul (lc4Pic D n s ω x) (Z s)
        rw [dist_eq_norm, dist_eq_norm] at this
        simp only [max_eq_left hs.1.le]
        exact this.trans (mul_le_mul_of_nonneg_left (ih s hs') (NNReal.coe_nonneg _))
      · have hint : ∫ s in (0 : ℝ)..r, (L : ℝ) * (K * (L * s) ^ n / (n.factorial : ℝ)) =
            (L : ℝ) * (K * L ^ n / (n.factorial : ℝ)) * (r ^ (n + 1) / (n + 1)) := by
          have : ∀ s : ℝ, (L : ℝ) * (K * (L * s) ^ n / (n.factorial : ℝ)) =
              ((L : ℝ) * (K * L ^ n / (n.factorial : ℝ))) * s ^ n := fun s => by
            rw [mul_pow]; ring
          simp_rw [this]
          rw [intervalIntegral.integral_const_mul, integral_pow]
          simp
        rw [hint, Nat.factorial_succ]
        have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
        push_cast
        apply le_of_eq
        field_simp
        ring
  have hlim : Tendsto (fun n : ℕ => K * ((L * t) ^ n / (n.factorial : ℝ))) atTop (𝓝 (K * 0)) :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop ((L : ℝ) * t)).const_mul K
  rw [mul_zero] at hlim
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
  have := hbd n t ⟨ht, le_rfl⟩
  rwa [mul_div_assoc] at this

theorem lc4_meas_Z {D : Ω → ℝ → Euc d → Euc d} (hD : ∀ ω, IsLipschitzDrift (D ω))
    (hDc : ∀ ω, Continuous fun p : ℝ × Euc d => D ω (max p.1 0) p.2)
    (hDm : Measurable fun p : ℝ × (Ω × Euc d) => D p.2.1 (max p.1 0) p.2.2) {t : ℝ} (ht : 0 ≤ t) :
    Measurable (fun p : Ω × Euc d => lcZ (D p.1) p.2 t) := by
  refine measurable_of_tendsto_metrizable (f := fun n (p : Ω × Euc d) => lc4Pic D n t p.1 p.2)
    (fun n => lc4_pic_meas hDc hDm n t) (tendsto_pi_nhds.2 fun p => ?_)
  exact lc4_pic_tendsto p.1 (hD p.1) (hDc p.1) p.2 ht

/-! ### The drift of the engine flow -/

section Drift

variable {Q : Matrix (Fin d) (Fin d) ℝ} {k : ℕ} {Λc ΛB : ℝ} {c : ℝ → Euc d}
  {B : ℝ → Euc d → Euc d} {G : Ω → ℝ → Euc d}

theorem lc4_drift_cont (H : LcHyp Q k Λc ΛB c B) {g : ℝ → Euc d} (hg : Continuous g) {r : ℝ}
    (hr : 0 ≤ r) :
    Continuous fun p : ℝ × Euc d => lcDrift Q c B g r (max p.1 0) p.2 := by
  exact (lcDrift_continuousOn H hg hr).comp_continuous
    (f := fun p : ℝ × Euc d => (max p.1 0, p.2)) (by fun_prop)
    fun p => ⟨(show (0 : ℝ) ≤ max p.1 0 from le_max_right _ _), mem_univ _⟩

theorem lc4_drift_meas (H : LcHyp Q k Λc ΛB c B) (hGm : ∀ v, Measurable fun ω => G ω v)
    (hGc : ∀ ω, Continuous (G ω)) {r : ℝ} (hr : 0 ≤ r) :
    Measurable fun p : ℝ × (Ω × Euc d) => lcDrift Q c B (G p.2.1) r (max p.1 0) p.2.2 := by
  have hcc : Continuous fun τ : ℝ => c (r + max τ 0) :=
    H.c_cont.comp_continuous (by fun_prop) fun τ => by
      simpa using add_nonneg hr (le_max_right τ 0)
  have hBc : Continuous fun p : ℝ × Euc d => B (r + max p.1 0) p.2 :=
    H.B_cont.comp_continuous (f := fun p : ℝ × Euc d => (r + max p.1 0, p.2)) (by fun_prop)
      fun p => ⟨by simpa using add_nonneg hr (le_max_right p.1 0), mem_univ _⟩
  have hU : Measurable fun p : ℝ × (Ω × Euc d) => lcU Q (G p.2.1) r (r + max p.1 0) :=
    (lc4_meas_lcU Q hGm hGc r).comp
      ((measurable_const.add (measurable_fst.max measurable_const)).prodMk
        (measurable_fst.comp measurable_snd))
  unfold lcDrift
  have hz : Measurable fun p : ℝ × (Ω × Euc d) => p.2.2 := measurable_snd.comp measurable_snd
  refine (((lcQ Q).continuous.measurable.comp hz).neg.sub
    (hcc.measurable.comp measurable_fst)).add ?_
  exact hBc.measurable.comp (measurable_fst.prodMk (hz.add hU))

end Drift

/-! ### Joint measurability of the flow -/

/-- **Joint measurability.**  If `G ω` are continuous noise paths, measurable in `ω`, then
`(ω, x) ↦ lcFlow Q c B (G ω) r t x` is jointly measurable for `0 ≤ r ≤ t`. -/
theorem lc4_meas_flow {Q : Matrix (Fin d) (Fin d) ℝ} {k : ℕ} {Λc ΛB : ℝ} {c : ℝ → Euc d}
    {B : ℝ → Euc d → Euc d} (H : LcHyp Q k Λc ΛB c B) {G : Ω → ℝ → Euc d}
    (hGm : ∀ v, Measurable fun ω => G ω v) (hGc : ∀ ω, Continuous (G ω)) {r t : ℝ} (hr : 0 ≤ r)
    (hrt : r ≤ t) :
    Measurable (fun p : Ω × Euc d => lcFlow Q c B (G p.1) r t p.2) := by
  have hZ := lc4_meas_Z (D := fun ω => lcDrift Q c B (G ω) r)
    (fun ω => lcDrift_isLipschitz H (hGc ω) hr) (fun ω => lc4_drift_cont H (hGc ω) hr)
    (lc4_drift_meas H hGm hGc hr) (sub_nonneg.2 hrt)
  have hU : Measurable fun p : Ω × Euc d => lcU Q (G p.1) r t :=
    (lc4_meas_lcU_fixed Q hGm hGc r t).comp measurable_fst
  exact hZ.add hU

end Meas

end HRS.MS.Lc
