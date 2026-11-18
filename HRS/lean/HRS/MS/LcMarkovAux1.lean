import HRS.MS.LcEngAux1
import HRS.MS.LcFlowAux2
import HRS.MS.LcNoiseAux1

/-!
# LC-5, part 1: locality of the pathwise flow `lcFlow` and the restarted noise path

Setting (supplement S4.11, step 5; template `PoisMarkovAux1`).  The Markov property
`lcSg r t g = lcSg r v (lcSg v t g)` (part 2) is obtained from the pathwise cocycle
`lc_flow_cocycle`, the independence of the noise after time `v` from the noise up to time `v`
(`lc_noise_indep`, in the path form `mk_indep`) and Fubini.  This file prepares the two locality
statements and the path-space description of the restarted noise.

* `lc5_flow_congr_future`: `lcFlow g v t y` only depends on the increments `g (v + ·) - g v`
  (`lcW g v = lcW g' v`), by `lc_flow_unique`.
* `lc5_flow_congr_past`: `lcFlow g r v x` only depends on `g` on `[r, v]`, by `ode_additive_unique`
  on the horizon `v - r`.
* `lc5Path ν v ψ`: for a path `ψ ∈ C(ℝ≥0, Fin d → ℝ)` the noise path `u ↦ lcNoiseE W₀ ν(v + ·) (u - v)`
  with `W₀ s ψ = ψ s - ψ 0`; it is continuous (`lc5Path_cont`), measurable in `ψ` (`lc5Path_meas`),
  equals `0` for `u ≤ v` and, for `ψ = bfPath` of the Brownian motion `W_{τ(v)+·} - W_{τ(v)}`, equals
  `G_u - G_v` for `u ≥ v` (`lc5Path_eq`), where `G = lcNoiseE W ν`.
* `lc5_meas_Psi`: joint measurability of `(ψ, y) ↦ lcFlow (lc5Path ν v ψ) v t y`.
* `lc5_measurable_V`: `ω ↦ lcFlow (G ω) r v x` is `ℱ_{τ(v)}`-measurable.

Helper lemmas carry the prefix `lc5_`.
-/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MD.EQLawPath

noncomputable section

namespace HRS.MS.Lc

variable {d : ℕ}

/-! ### Locality of the pathwise flow -/

section Locality

variable {Q : Matrix (Fin d) (Fin d) ℝ} {k : ℕ} {Λc ΛB : ℝ} {c : ℝ → Euc d}
  {B : ℝ → Euc d → Euc d} {g g' : ℝ → Euc d}

/-- The flow from time `v` only depends on the increments of the noise after `v`. -/
theorem lc5_flow_congr_future (H : LcHyp Q k Λc ΛB c B) (hg : Continuous g) (hg' : Continuous g')
    {v : ℝ} (hv : 0 ≤ v) (hw : lcW g v = lcW g' v) {t : ℝ} (ht : v ≤ t) (y : Euc d) :
    lcFlow Q c B g v t y = lcFlow Q c B g' v t y := by
  have hy := lcFlow_isPathSolution H hg' hv y
  rw [← hw] at hy
  have h := lc_flow_unique H hg hv hy (t - v) (sub_nonneg.2 ht)
  have e : v + (t - v) = t := by ring
  simp only [e] at h
  exact h.symm

/-- The flow from `r` to `v` only depends on the noise path on `[r, v]`. -/
theorem lc5_flow_congr_past (H : LcHyp Q k Λc ΛB c B) (hg : Continuous g) (hg' : Continuous g')
    {r v : ℝ} (hr : 0 ≤ r) (hrv : r ≤ v) (hgg : ∀ u ∈ Icc r v, g u = g' u) (x : Euc d) :
    lcFlow Q c B g r v x = lcFlow Q c B g' r v x := by
  have hP := lcFlow_isPathSolution H hg hr x
  have hP' := lcFlow_isPathSolution H hg' hr x
  set h : ℝ := v - r with hh
  have hh0 : 0 ≤ h := sub_nonneg.2 hrv
  have hrh : r + h = v := by rw [hh]; ring
  have hsol : IsPathSolution (lcB Q c B r) (lcSigma d) (lcW g r) x ((h : ℝ) : WithTop ℝ)
      (fun τ => lcFlow Q c B g' r (r + τ) x) := by
    refine ⟨hP'.1, fun t ht htlt => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hP'.2 t ht (WithTop.coe_lt_top _)
    refine ⟨h1, h2, ?_⟩
    have htlt' : t < h := by exact_mod_cast htlt
    have hu : r + t ∈ Icc r v := ⟨by linarith, by linarith⟩
    have hr' : r ∈ Icc r v := ⟨le_rfl, hrv⟩
    rw [h3, lc1_noise_sum g' r ht, lc1_noise_sum g r ht, hgg _ hu, hgg _ hr']
  have heq : ∀ t : ℝ, 0 ≤ t → t < h →
      lcFlow Q c B g r (r + t) x = lcFlow Q c B g' r (r + t) x := fun t ht hth =>
    ode_additive_unique univ isOpen_univ (lcB Q c B r) (lcB_locLip H hr) (lcSigma d) (lcW g r)
      (lcW_continuous hg r) x hP hsol (fun _ _ _ => mem_univ _) (fun _ _ _ => mem_univ _) t ht
      (by rw [min_eq_right le_top]; exact_mod_cast hth)
  rw [← hrh]
  rcases eq_or_lt_of_le hh0 with h0 | hpos
  · have e1 : lcFlow Q c B g r (r + 0) x = x := hP.1
    have e2 : lcFlow Q c B g' r (r + 0) x = x := hP'.1
    rw [← h0, e1, e2]
  · have hc1 : ContinuousOn (fun τ => lcFlow Q c B g r (r + τ) x) (Icc 0 h) :=
      (hP.2 h hh0 (WithTop.coe_lt_top _)).1
    have hc2 : ContinuousOn (fun τ => lcFlow Q c B g' r (r + τ) x) (Icc 0 h) :=
      (hP'.2 h hh0 (WithTop.coe_lt_top _)).1
    have hEqOn : EqOn (fun τ => lcFlow Q c B g r (r + τ) x)
        (fun τ => lcFlow Q c B g' r (r + τ) x) (Ico 0 h) := fun τ hτ => heq τ hτ.1 hτ.2
    have := hEqOn.of_subset_closure hc1 hc2 Ico_subset_Icc_self (by rw [closure_Ico hpos.ne])
    exact this ⟨hh0, le_rfl⟩

end Locality

/-! ### The restarted noise path on path space -/

/-- The noise `ψ ↦ ψ s - ψ 0` on path space `C(ℝ≥0, Fin d → ℝ)`. -/
def lc5W0 (d : ℕ) : ℝ≥0 → C(ℝ≥0, Fin d → ℝ) → Fin d → ℝ := fun s ψ => ψ s - ψ 0

/-- The noise path restarted at `v`, built from a path `ψ`: `u ↦ lcNoiseE W₀ ν(v + ·) (max (u - v) 0) ψ`.
It vanishes for `u ≤ v`. -/
def lc5Path (ν : ℝ → ℝ) (v : ℝ) (ψ : C(ℝ≥0, Fin d → ℝ)) (u : ℝ) : Euc d :=
  lcNoiseE (lc5W0 d) (fun x => ν (v + x)) (max (u - v) 0) ψ

theorem lc5Path_meas (ν : ℝ → ℝ) (v u : ℝ) :
    Measurable fun ψ : C(ℝ≥0, Fin d → ℝ) => lc5Path ν v ψ u :=
  (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable.comp
    ((ContinuousMap.measurable_eval _).sub (ContinuousMap.measurable_eval 0))

theorem lc5Path_cont {ν : ℝ → ℝ} (hν : Continuous ν) (v : ℝ) (ψ : C(ℝ≥0, Fin d → ℝ)) :
    Continuous (lc5Path ν v ψ) := by
  have hν' : Continuous fun x => ν (v + x) := hν.comp (continuous_const.add continuous_id)
  have hc : Continuous fun s : ℝ≥0 => lc5W0 d s ψ :=
    ψ.continuous.sub continuous_const
  have h1 : Continuous fun s : ℝ => lcNoise (lc5W0 d) (fun x => ν (v + x)) s ψ :=
    continuous_pi fun k => (continuous_apply k).comp
      ((continuous_ofNNRealTime (lc5W0 d) ψ hc).comp (lcTau_continuous hν'))
  have h2 : Continuous fun s : ℝ => lcNoiseE (lc5W0 d) (fun x => ν (v + x)) s ψ :=
    (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp h1
  exact h2.comp ((continuous_id.sub continuous_const).max continuous_const)

theorem lc5Path_of_le (ν : ℝ → ℝ) {v u : ℝ} (hu : u ≤ v) (ψ : C(ℝ≥0, Fin d → ℝ)) :
    lc5Path ν v ψ u = 0 := by
  have : max (u - v) 0 = 0 := max_eq_right (by linarith)
  unfold lc5Path
  rw [this]
  ext k
  simp [lcNoiseE, lcNoise, lcTau_zero, lc5W0]

theorem lc5Path_self (ν : ℝ → ℝ) (v : ℝ) (ψ : C(ℝ≥0, Fin d → ℝ)) : lc5Path ν v ψ v = 0 :=
  lc5Path_of_le ν le_rfl ψ

section Brownian

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → Fin d → ℝ} {ν : ℝ → ℝ}

/-- For the path of the shifted Brownian motion `W_{τ(v)+·} - W_{τ(v)}`, `lc5Path` is the increment
`G_u - G_v` of the time-changed noise, `u ≥ v`. -/
theorem lc5Path_eq (hW : IsBrownianFiltration P ℱ W) (hν : Continuous ν) (hν0 : ∀ x, 0 ≤ ν x)
    {v : ℝ} (hv : 0 ≤ v) (ω : Ω) {u : ℝ} (hu : v ≤ u) :
    lc5Path ν v (bfPath (isBrownianFiltration_shift hW (lcTau ν v).toNNReal) ω) u =
      lcNoiseE W ν u ω - lcNoiseE W ν v ω := by
  have hs : 0 ≤ u - v := sub_nonneg.2 hu
  have h1 := (lc_noise_shift hW hν hν0 hv).2 (u - v) hs ω
  have e : v + (u - v) = u := by ring
  rw [e] at h1
  have e2 : lcNoise (lc5W0 d) (fun x => ν (v + x)) (u - v)
      (bfPath (isBrownianFiltration_shift hW (lcTau ν v).toNNReal) ω) =
      lcNoise (shiftProc W (lcTau ν v).toNNReal) (fun x => ν (v + x)) (u - v) ω := by
    funext k
    simp [lcNoise, lc5W0, bfPath, shiftProc]
  have e3 : lcNoise W ν u ω - lcNoise W ν v ω = lcNoise W ν u ω - lcNoise W ν v ω := rfl
  unfold lc5Path lcNoiseE
  rw [max_eq_left hs, e2, h1]
  rfl

/-- The restarted noise has the same increments after `v` as the original one. -/
theorem lc5_lcW_eq (hW : IsBrownianFiltration P ℱ W) (hν : Continuous ν) (hν0 : ∀ x, 0 ≤ ν x)
    {v : ℝ} (hv : 0 ≤ v) (ω : Ω) :
    lcW (fun u => lcNoiseE W ν u ω) v =
      lcW (lc5Path ν v (bfPath (isBrownianFiltration_shift hW (lcTau ν v).toNNReal) ω)) v := by
  funext τ k
  have hu : v ≤ v + (τ : ℝ) := by linarith [τ.coe_nonneg]
  simp only [lcW, lc5Path_eq hW hν hν0 hv ω hu, lc5Path_self, PiLp.sub_apply, PiLp.zero_apply,
    sub_zero]

/-- Measurability of `ω ↦ lcFlow (G ω) r v x` for measurable families of continuous paths. -/
theorem lc5_meas_flow_comp {Ω : Type*} [MeasurableSpace Ω] {Q : Matrix (Fin d) (Fin d) ℝ} {k : ℕ}
    {Λc ΛB : ℝ} {c : ℝ → Euc d} {B : ℝ → Euc d → Euc d} (H : LcHyp Q k Λc ΛB c B)
    (G : Ω → ℝ → Euc d) (hGm : ∀ u, Measurable fun ω => G ω u) (hGc : ∀ ω, Continuous (G ω))
    {r v : ℝ} (hr : 0 ≤ r) (hrv : r ≤ v) (x : Euc d) :
    Measurable fun ω => lcFlow Q c B (G ω) r v x := by
  have h1 := lc4_meas_flow H hGm hGc hr hrv
  have h2 : Measurable (fun ω : Ω => (ω, x)) := measurable_id.prodMk measurable_const
  have h3 := h1.comp h2
  exact h3

/-- `ω ↦ lcFlow (G ω) r v x` is `ℱ_{τ(v)}`-measurable. -/
theorem lc5_measurable_V {Q : Matrix (Fin d) (Fin d) ℝ} {k : ℕ} {Λc ΛB : ℝ} {c : ℝ → Euc d}
    {B : ℝ → Euc d → Euc d} (H : LcHyp Q k Λc ΛB c B) (hW : IsBrownianFiltration P ℱ W)
    (hν : Continuous ν) (hν0 : ∀ x, 0 ≤ ν x) {r v : ℝ} (hr : 0 ≤ r) (hrv : r ≤ v) (x : Euc d) :
    Measurable[ℱ (((lcTau ν v).toNNReal : ℝ≥0) : ℝ)]
      (fun ω => lcFlow Q c B (fun u => lcNoiseE W ν u ω) r v x) := by
  have key : Measurable[ℱ (((lcTau ν v).toNNReal : ℝ≥0) : ℝ)]
      (fun ω => lcFlow Q c B (fun u => lcNoiseE W ν (min u v) ω) r v x) := by
    have hGm : ∀ u, Measurable[ℱ (((lcTau ν v).toNNReal : ℝ≥0) : ℝ)]
        fun ω => lcNoiseE W ν (min u v) ω := fun u =>
      (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable.comp
        (lc_noise_adapted hW hν hν0 (min_le_right u v))
    have hGc : ∀ ω, Continuous fun u => lcNoiseE W ν (min u v) ω := fun ω =>
      (lc_noiseE_cont hW hν ω).comp (continuous_id.min continuous_const)
    exact @lc5_meas_flow_comp d Ω (ℱ (((lcTau ν v).toNNReal : ℝ≥0) : ℝ)) Q k Λc ΛB c B H
      (fun ω u => lcNoiseE W ν (min u v) ω) hGm hGc r v hr hrv x
  have e : (fun ω => lcFlow Q c B (fun u => lcNoiseE W ν u ω) r v x) =
      fun ω => lcFlow Q c B (fun u => lcNoiseE W ν (min u v) ω) r v x := by
    funext ω
    refine lc5_flow_congr_past H (lc_noiseE_cont hW hν ω)
      ((lc_noiseE_cont hW hν ω).comp (continuous_id.min continuous_const)) hr hrv
      (fun u hu => ?_) x
    simp [min_eq_left hu.2]
  rw [e]
  exact key

end Brownian

/-- Joint measurability of `(ψ, y) ↦ lcFlow (lc5Path ν v ψ) v t y` on path space. -/
theorem lc5_meas_Psi {Q : Matrix (Fin d) (Fin d) ℝ} {k : ℕ} {Λc ΛB : ℝ} {c : ℝ → Euc d}
    {B : ℝ → Euc d → Euc d} (H : LcHyp Q k Λc ΛB c B) {ν : ℝ → ℝ} (hν : Continuous ν) {v t : ℝ}
    (hv : 0 ≤ v) (hvt : v ≤ t) :
    Measurable fun p : C(ℝ≥0, Fin d → ℝ) × Euc d => lcFlow Q c B (lc5Path ν v p.1) v t p.2 :=
  lc4_meas_flow H (G := fun ψ => lc5Path ν v ψ) (fun u => lc5Path_meas ν v u)
    (fun ψ => lc5Path_cont hν v ψ) hv hvt

end HRS.MS.Lc
