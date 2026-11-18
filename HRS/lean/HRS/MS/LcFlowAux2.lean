import HRS.MS.PoisFlowAux2
import HRS.MS.LcFlowAux1

/-!
# LC-1, part 2: regularity in `x`, flow property, uniqueness and continuity of `lcFlow`

Main theorems (namespace `HRS.MS.Lc`; hypotheses `LcHyp Q k Λc ΛB c B`, a continuous noise path
`g : ℝ → Euc d`, starting time `r ≥ 0`, `Λ = lcLam Q Λc ΛB = ‖Q‖ + Λc + ΛB`):

* `lc_flow` : with `Λ = lcLam Q Λc ΛB` (independent of `g`, `r`, `v`, `x`),
  (a) `lcFlow Q c B g r (r + ·) x` is a pathwise solution (`IsPathSolution`, time shifted by `r`,
      noise path `lcW g r`, directions `lcSigma d`) of `X_τ = x + ∫_0^τ (-Q X - c_{r+s} + B_{r+s}(X)) ds
      + (g (r+τ) - g r)` on all of `[0, ∞)`;
  (b) `lcFlow Q c B g r v` is `C^{k+1}` for `v ≥ r`;
  (c) `‖fderiv ℝ (lcFlow Q c B g r v) x‖ ≤ exp (Λ (v - r))` for `v ≥ r`;
* `lc_flow_cocycle` : `lcFlow r t x = lcFlow v t (lcFlow r v x)` for `0 ≤ r ≤ v ≤ t`;
* `lc_flow_unique` : every pathwise solution of the same equation from `x` equals `lcFlow`;
* `lc_flow_continuous` : `(r, v, x) ↦ lcFlow Q c B g r v x` is continuous on `{0 ≤ r ≤ v}`;
* `lcHyp_clamp`, `lcB_clamp_eq` : data given on `[0,T]` only (as in `local_decay`) are extended by
  `c (min v T)`, `B (min v T)`, which satisfy `LcHyp` and have the same drift on `[0,T]`.

Helper lemmas carry the prefix `lc2_`.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

noncomputable section

namespace HRS.MS.Lc

variable {d : ℕ}

section Bounds

variable {Q : Matrix (Fin d) (Fin d) ℝ} {k : ℕ} {Λc ΛB : ℝ} {c : ℝ → Euc d}
  {B : ℝ → Euc d → Euc d} {g : ℝ → Euc d}

theorem lc2_negDrift_eq (Q : Matrix (Fin d) (Fin d) ℝ) (c : ℝ → Euc d) (B : ℝ → Euc d → Euc d)
    (g : ℝ → Euc d) (r τ : ℝ) (z : Euc d) :
    -lcDrift Q c B g r τ z =
      (lcQ Q z - B (r + τ) (z + lcU Q g r (r + τ))) + c (r + τ) := by
  unfold lcDrift; abel

/-- The negated drift satisfies the drift bounds of order `k` with `Λ = ‖Q‖ + Λc + ΛB`, for every
continuous noise path. -/
theorem lcDrift_isDriftBounds (H : LcHyp Q k Λc ΛB c B) (hg : Continuous g) {r : ℝ} (hr : 0 ≤ r)
    (T : ℝ) : IsDriftBounds T k (lcLam Q Λc ΛB) (fun τ z => -lcDrift Q c B g r τ z) where
  cont := ((lcDrift_continuousOn H hg hr).neg).mono (prod_mono Icc_subset_Ici_self le_rfl)
  smooth τ hτ := by
    have hv : 0 ≤ r + τ := add_nonneg hr hτ.1
    have h : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞)
        (fun z : Euc d => (lcQ Q z - B (r + τ) (z + lcU Q g r (r + τ))) + c (r + τ)) :=
      ((lcQ Q).contDiff.sub ((H.B_smooth _ hv).comp (contDiff_id.add contDiff_const))).add
        contDiff_const
    convert h using 2 with z
    exact lc2_negDrift_eq Q c B g r τ z
  deriv_bound τ hτ j hj1 hj2 x := by
    have hv : 0 ≤ r + τ := add_nonneg hr hτ.1
    have hΛc := H.Λc_nonneg
    have hΛB := H.ΛB_nonneg
    have hshift : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞)
        (fun z : Euc d => B (r + τ) (z + lcU Q g r (r + τ))) :=
      (H.B_smooth _ hv).comp (contDiff_id.add contDiff_const)
    have hsub : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞)
        (fun z : Euc d => lcQ Q z - B (r + τ) (z + lcU Q g r (r + τ))) :=
      (lcQ Q).contDiff.sub hshift
    have e : (fun z : Euc d => -lcDrift Q c B g r τ z) =
        fun z => (lcQ Q z - B (r + τ) (z + lcU Q g r (r + τ))) + c (r + τ) := by
      funext z; exact lc2_negDrift_eq Q c B g r τ z
    rw [e, HRS.MS.PoisFlow.pf_iter_add_const _ hsub (by omega) hj2 x]
    have hBj : ContDiffAt ℝ (j : WithTop ℕ∞) (fun z : Euc d => B (r + τ) (z + lcU Q g r (r + τ))) x :=
      (hshift.of_le (by exact_mod_cast hj2)).contDiffAt
    have hLj : ContDiffAt ℝ (j : WithTop ℕ∞) (fun z : Euc d => lcQ Q z) x :=
      (lcQ Q).contDiff.contDiffAt.of_le (by exact_mod_cast le_top)
    have e0 : (fun z : Euc d => lcQ Q z - B (r + τ) (z + lcU Q g r (r + τ))) =
        (fun z : Euc d => lcQ Q z) - fun z => B (r + τ) (z + lcU Q g r (r + τ)) := rfl
    rw [e0, iteratedFDeriv_sub_apply hLj hBj, iteratedFDeriv_comp_add_right]
    refine (norm_sub_le _ _).trans ?_
    have h2 : ‖iteratedFDeriv ℝ j (B (r + τ)) (x + lcU Q g r (r + τ))‖ ≤ ΛB :=
      H.B_bd _ hv j hj2 _
    unfold lcLam
    by_cases hj : j = 1
    · subst hj
      have h1 : ‖iteratedFDeriv ℝ 1 (fun z : Euc d => lcQ Q z) x‖ ≤ ‖lcQ Q‖ := by
        rw [norm_iteratedFDeriv_one]
        rw [(lcQ Q).fderiv]
      linarith
    · have e : iteratedFDeriv ℝ j (fun z : Euc d => lcQ Q z) x = 0 :=
        HRS.MS.PoisFlow.pf_iter_clm_zero (lcQ Q) (by omega) x
      rw [e, norm_zero]
      linarith [norm_nonneg (lcQ Q)]
  growth τ hτ z := by
    have hv : 0 ≤ r + τ := add_nonneg hr hτ.1
    have hΛc := H.Λc_nonneg
    have hΛB := H.ΛB_nonneg
    have hB0 : ‖B (r + τ) (z + lcU Q g r (r + τ))‖ ≤ ΛB := by
      have := H.B_bd _ hv 0 (Nat.zero_le _) (z + lcU Q g r (r + τ))
      rwa [norm_iteratedFDeriv_zero] at this
    have hc := H.c_bd _ hv
    have hQ : ‖lcQ Q z‖ ≤ ‖lcQ Q‖ * ‖z‖ := (lcQ Q).le_opNorm z
    rw [lc2_negDrift_eq]
    calc ‖(lcQ Q z - B (r + τ) (z + lcU Q g r (r + τ))) + c (r + τ)‖
        ≤ ‖lcQ Q z‖ + ‖B (r + τ) (z + lcU Q g r (r + τ))‖ + ‖c (r + τ)‖ := by
          refine (norm_add_le _ _).trans ?_
          have := norm_sub_le (lcQ Q z) (B (r + τ) (z + lcU Q g r (r + τ)))
          linarith
      _ ≤ lcLam Q Λc ΛB * (1 + ‖z‖) := by
          unfold lcLam
          nlinarith [norm_nonneg z, norm_nonneg (lcQ Q), mul_nonneg hΛc (norm_nonneg z),
            mul_nonneg hΛB (norm_nonneg z)]

end Bounds


section Reg

variable {Q : Matrix (Fin d) (Fin d) ℝ} {k : ℕ} {Λc ΛB : ℝ} {c : ℝ → Euc d}
  {B : ℝ → Euc d → Euc d} {g : ℝ → Euc d}

theorem lc2_isNegDriftFlow (H : LcHyp Q k Λc ΛB c B) (hg : Continuous g) {r : ℝ} (hr : 0 ≤ r)
    {T : ℝ} (hT : 0 ≤ T) :
    IsNegDriftFlow T (fun τ z => -lcDrift Q c B g r τ z)
      (fun τ x => lcZ (lcDrift Q c B g r) x τ) :=
  lcZ_isNegDriftFlow (lcDrift_isLipschitz H hg hr) hT

theorem lcFlow_contDiff (H : LcHyp Q k Λc ΛB c B) (hg : Continuous g) {r : ℝ} (hr : 0 ≤ r)
    {v : ℝ} (hv : r ≤ v) :
    ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (lcFlow Q c B g r v) := by
  have hT : 0 ≤ v - r := sub_nonneg.2 hv
  have := FlowB.flow_contDiff hT (lcDrift_isDriftBounds H hg hr (v - r))
    (lc2_isNegDriftFlow H hg hr hT) (v - r) ⟨hT, le_rfl⟩
  exact this.add contDiff_const

theorem lcFlow_fderiv_le (H : LcHyp Q k Λc ΛB c B) (hg : Continuous g) {r : ℝ} (hr : 0 ≤ r)
    {v : ℝ} (hv : r ≤ v) (x : Euc d) :
    ‖fderiv ℝ (lcFlow Q c B g r v) x‖ ≤ Real.exp (lcLam Q Λc ΛB * (v - r)) := by
  have hT : 0 ≤ v - r := sub_nonneg.2 hv
  have := FlowB.flow_fderiv_bound hT (lcDrift_isDriftBounds H hg hr (v - r))
    (lc2_isNegDriftFlow H hg hr hT) (v - r) ⟨hT, le_rfl⟩ x
  have e : lcFlow Q c B g r v = fun x => lcZ (lcDrift Q c B g r) x (v - r) + lcU Q g r v := rfl
  rw [e, fderiv_add_const]
  exact this

theorem lcFlow_lipschitz (H : LcHyp Q k Λc ΛB c B) (hg : Continuous g) {r : ℝ} (hr : 0 ≤ r)
    {v : ℝ} (hv : r ≤ v) (x y : Euc d) :
    ‖lcFlow Q c B g r v x - lcFlow Q c B g r v y‖ ≤
      Real.exp (lcLam Q Λc ΛB * (v - r)) * ‖x - y‖ := by
  have hT : 0 ≤ v - r := sub_nonneg.2 hv
  have := FlowA.flow_lipschitz hT (lcDrift_isDriftBounds H hg hr (v - r))
    (lc2_isNegDriftFlow H hg hr hT) (v - r) ⟨hT, le_rfl⟩ x y
  have e : lcFlow Q c B g r v x - lcFlow Q c B g r v y =
      lcZ (lcDrift Q c B g r) x (v - r) - lcZ (lcDrift Q c B g r) y (v - r) := by
    unfold lcFlow; abel
  rw [e]
  exact this

end Reg

/-! ### Restart, uniqueness and the flow property -/

section Restart

variable {Q : Matrix (Fin d) (Fin d) ℝ} {k : ℕ} {Λc ΛB : ℝ} {c : ℝ → Euc d}
  {B : ℝ → Euc d → Euc d} {g : ℝ → Euc d}

/-- Restarting a pathwise solution at time `a ≥ 0`. -/
theorem lc2_restart {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {b : ℝ → E → E} {σ : ι → E} {w : ℝ≥0 → ι → ℝ} {x : E} {y : ℝ → E}
    (hy : IsPathSolution b σ w x ⊤ y) {a : ℝ} (ha : 0 ≤ a) :
    IsPathSolution (fun τ z => b (a + τ) z) σ
      (fun τ i => w (a.toNNReal + τ) i - w a.toNNReal i) (y a) ⊤ (fun τ => y (a + τ)) := by
  refine ⟨by simp, fun t ht _ => ?_⟩
  obtain ⟨hc, hi, he⟩ := hy.2 (a + t) (add_nonneg ha ht) (WithTop.coe_lt_top _)
  obtain ⟨hca, _, hea⟩ := hy.2 a ha (WithTop.coe_lt_top _)
  have hsub : Icc a (a + t) ⊆ Icc 0 (a + t) := Icc_subset_Icc ha le_rfl
  have hsub0 : Icc 0 a ⊆ Icc 0 (a + t) := Icc_subset_Icc le_rfl (by linarith)
  have hcy : ContinuousOn y (Icc a (a + t)) := hc.mono hsub
  have hint : IntervalIntegrable (fun s => b s (y s)) volume a (a + t) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
    exact hi.mono_set hsub
  have hint0 : IntervalIntegrable (fun s => b s (y s)) volume 0 a := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ha]
    exact hi.mono_set hsub0
  have hint' : IntervalIntegrable (fun s => b (a + s) (y (a + s))) volume 0 t := by
    have := hint.comp_add_left a
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · have : ContinuousOn (fun τ : ℝ => a + τ) (Icc 0 t) := continuousOn_const.add continuousOn_id
    exact hc.comp this (fun τ hτ => ⟨by linarith [hτ.1], by linarith [hτ.2]⟩)
  · rw [← intervalIntegrable_iff_integrableOn_Icc_of_le ht]
    exact hint'
  · have hsplit : ∫ s in Icc 0 (a + t), b s (y s) =
        (∫ s in Icc 0 a, b s (y s)) + ∫ s in Icc 0 t, b (a + s) (y (a + s)) := by
      rw [setIntegral_Icc_eq_interval (add_nonneg ha ht), setIntegral_Icc_eq_interval ha,
        setIntegral_Icc_eq_interval ht, ← intervalIntegral.integral_add_adjacent_intervals
          hint0 hint]
      congr 1
      rw [intervalIntegral.integral_comp_add_left (fun s => b s (y s)) a]
      simp
    have hnn : (a + t).toNNReal = a.toNNReal + t.toNNReal := Real.toNNReal_add ha ht
    simp only [add_zero] at he ⊢
    rw [hnn] at he
    have : ∑ i, (w (a.toNNReal + t.toNNReal) i - w a.toNNReal i) • σ i =
        ∑ i, w (a.toNNReal + t.toNNReal) i • σ i - ∑ i, w a.toNNReal i • σ i := by
      simp [sub_smul, Finset.sum_sub_distrib]
    have hy0 : y a = x + (∫ s in Icc 0 a, b s (y s)) + ∑ i, w a.toNNReal i • σ i := hea
    rw [this, he, hy0, hsplit]
    abel

end Restart


section Unique

variable {Q : Matrix (Fin d) (Fin d) ℝ} {k : ℕ} {Λc ΛB : ℝ} {c : ℝ → Euc d}
  {B : ℝ → Euc d → Euc d} {g : ℝ → Euc d}

theorem lcB_continuousOn_prod (H : LcHyp Q k Λc ΛB c B) {r : ℝ} (hr : 0 ≤ r) :
    ContinuousOn (fun p : ℝ × Euc d => lcB Q c B r p.1 p.2) (Ici 0 ×ˢ univ) := by
  unfold lcB
  have hS : ∀ p ∈ (Ici 0 ×ˢ univ : Set (ℝ × Euc d)), 0 ≤ p.1 := fun p hp => hp.1
  have hmap : ∀ p ∈ (Ici 0 ×ˢ univ : Set (ℝ × Euc d)),
      (r + p.1, p.2) ∈ Ici (0 : ℝ) ×ˢ (univ : Set (Euc d)) :=
    fun p hp => ⟨by simpa using add_nonneg hr (hS p hp), mem_univ _⟩
  have h1 : ContinuousOn (fun p : ℝ × Euc d => c (r + p.1)) (Ici 0 ×ˢ univ) :=
    H.c_cont.comp (continuousOn_const.add continuousOn_fst) (fun p hp => by
      simpa using add_nonneg hr (hS p hp))
  have h2 : ContinuousOn (fun p : ℝ × Euc d => B (r + p.1) p.2) (Ici 0 ×ˢ univ) :=
    H.B_cont.comp ((continuousOn_const.add continuousOn_fst).prodMk continuousOn_snd) hmap
  exact (((lcQ Q).continuous.comp_continuousOn continuousOn_snd).neg.sub h1).add h2

theorem lcB_isLipschitz (H : LcHyp Q k Λc ΛB c B) {r : ℝ} (hr : 0 ≤ r) :
    IsLipschitzDrift (lcB Q c B r) where
  cont := lcB_continuousOn_prod H hr
  lip T := ⟨(‖lcQ Q‖ + ΛB).toNNReal, fun t ht => LipschitzWith.of_dist_le_mul fun z z' => by
    have hΛ : 0 ≤ ‖lcQ Q‖ + ΛB := by have := H.ΛB_nonneg; positivity
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hΛ]
    have e : lcB Q c B r t z - lcB Q c B r t z' =
        -(lcQ Q (z - z')) + (B (r + t) z - B (r + t) z') := by
      unfold lcB; simp only [map_sub]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖-(lcQ Q (z - z'))‖ ≤ ‖lcQ Q‖ * ‖z - z'‖ := by
      rw [norm_neg]; exact (lcQ Q).le_opNorm _
    have h2 := lc1_B_lip H (by simpa using add_nonneg hr ht.1) z z'
    nlinarith⟩

theorem lcB_locLip (H : LcHyp Q k Λc ΛB c B) {r : ℝ} (hr : 0 ≤ r) :
    IsLocLipschitzDrift (univ : Set (Euc d)) (lcB Q c B r) where
  cont := (lcB_isLipschitz H hr).cont.mono (prod_mono subset_rfl (subset_univ _))
  lip K _ _ T := by
    obtain ⟨L, hL⟩ := (lcB_isLipschitz H hr).lip T
    exact ⟨L, fun t ht => (hL t ht).lipschitzOnWith⟩

theorem lcW_continuous (hg : Continuous g) (r : ℝ) : Continuous (lcW g r) := by
  refine continuous_pi fun i => ?_
  have h : Continuous fun y : Euc d => y i := (EuclideanSpace.proj i).continuous
  exact (h.comp (hg.comp (continuous_const.add NNReal.continuous_coe))).sub continuous_const

/-- **Uniqueness.**  Every pathwise solution of the equation with data `lcB` and noise `lcW g r` from
`x` coincides with `lcFlow`. -/
theorem lc_flow_unique (H : LcHyp Q k Λc ΛB c B) (hg : Continuous g) {r : ℝ} (hr : 0 ≤ r)
    {x : Euc d} {y : ℝ → Euc d}
    (hy : IsPathSolution (lcB Q c B r) (lcSigma d) (lcW g r) x ⊤ y) :
    ∀ τ : ℝ, 0 ≤ τ → y τ = lcFlow Q c B g r (r + τ) x := by
  intro τ hτ
  exact ode_additive_unique univ isOpen_univ (lcB Q c B r) (lcB_locLip H hr) (lcSigma d)
    (lcW g r) (lcW_continuous hg r) x hy (lcFlow_isPathSolution H hg hr x)
    (fun _ _ _ => mem_univ _) (fun _ _ _ => mem_univ _) τ hτ (by simp)

/-- **Flow property** (cocycle). -/
theorem lc_flow_cocycle (H : LcHyp Q k Λc ΛB c B) (hg : Continuous g) {r v t : ℝ} (hr : 0 ≤ r)
    (hrv : r ≤ v) (hvt : v ≤ t) (x : Euc d) :
    lcFlow Q c B g r t x = lcFlow Q c B g v t (lcFlow Q c B g r v x) := by
  have hv : 0 ≤ v := hr.trans hrv
  have ha : 0 ≤ v - r := sub_nonneg.2 hrv
  have hy := lc2_restart (lcFlow_isPathSolution H hg hr x) ha
  have e2 : r + (v - r) = v := by ring
  have hb : (fun (τ : ℝ) (z : Euc d) => lcB Q c B r ((v - r) + τ) z) = lcB Q c B v := by
    funext τ z
    unfold lcB
    have : r + ((v - r) + τ) = v + τ := by ring
    rw [this]
  have hw : (fun (τ : ℝ≥0) (i : Fin d) =>
      lcW g r ((v - r).toNNReal + τ) i - lcW g r (v - r).toNNReal i) = lcW g v := by
    funext τ i
    have e1 : r + ((v - r) + (τ : ℝ)) = v + τ := by ring
    simp only [lcW, NNReal.coe_add, Real.coe_toNNReal _ ha, e1, e2]
    ring
  rw [hb, hw] at hy
  simp only [← add_assoc, e2] at hy
  have := lc_flow_unique H hg hv hy (t - v) (sub_nonneg.2 hvt)
  have e3 : v + (t - v) = t := by ring
  simp only [e3] at this
  exact this

end Unique


/-! ### Continuity in `(r, v, x)` -/

section Cont

variable {Q : Matrix (Fin d) (Fin d) ℝ} {k : ℕ} {Λc ΛB : ℝ} {c : ℝ → Euc d}
  {B : ℝ → Euc d → Euc d} {g : ℝ → Euc d}

theorem lc2_gb (K M τ : ℝ) (hK : 0 ≤ K) :
    gronwallBound 0 K (K * M) τ = M * (Real.exp (K * τ) - 1) := by
  unfold gronwallBound
  split_ifs with h
  · subst h; simp
  · field_simp
    ring

theorem lc2_exp_sub_one_le {y : ℝ} (hy : 0 ≤ y) : Real.exp y - 1 ≤ y * Real.exp y := by
  have h := Real.add_one_le_exp (-y)
  have h2 : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos y, mul_le_mul_of_nonneg_left h (Real.exp_pos y).le]

/-- A priori bound on the displacement of the flow over a short time. -/
theorem lc2_move (H : LcHyp Q k Λc ΛB c B) (hg : Continuous g) {r : ℝ} (hr : 0 ≤ r) {s : ℝ}
    (hs : r ≤ s) (x : Euc d) :
    ‖lcFlow Q c B g r s x - x‖ ≤
      (1 + ‖x‖) * (Real.exp (lcLam Q Λc ΛB * (s - r)) - 1) + ‖lcU Q g r s‖ := by
  have hT : 0 ≤ s - r := sub_nonneg.2 hs
  have hD := lcDrift_isLipschitz H hg hr
  have hb := lcDrift_isDriftBounds H hg hr (s - r)
  have hΨ := lc2_isNegDriftFlow H hg hr hT
  have hΛ := H.lam_nonneg
  set Λ := lcLam Q Λc ΛB with hΛdef
  set D := lcDrift Q c B g r with hDdef
  set f : ℝ → Euc d := fun τ => lcZ D x τ - x with hfdef
  have hf : ContinuousOn f (Icc 0 (s - r)) := (lcZ_cont hD x hT).sub continuousOn_const
  have hf' : ∀ τ ∈ Ico 0 (s - r), HasDerivWithinAt f (D τ (lcZ D x τ)) (Ici τ) τ := by
    intro τ hτ
    have := hΨ.eqn x τ ⟨hτ.1, hτ.2.le⟩
    simp only [neg_neg] at this
    exact (this.sub_const x).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hτ)
  have hbound : ∀ τ ∈ Ico 0 (s - r), ‖D τ (lcZ D x τ)‖ ≤ Λ * ‖f τ‖ + Λ * (1 + ‖x‖) := by
    intro τ hτ
    have h1 := hb.growth τ ⟨hτ.1, hτ.2.le⟩ (lcZ D x τ)
    simp only [norm_neg] at h1
    have h2 : ‖lcZ D x τ‖ ≤ ‖f τ‖ + ‖x‖ := by
      have := norm_add_le (f τ) x
      simpa [hfdef] using this
    calc ‖D τ (lcZ D x τ)‖ ≤ Λ * (1 + ‖lcZ D x τ‖) := h1
      _ ≤ Λ * (1 + (‖f τ‖ + ‖x‖)) := by gcongr
      _ = Λ * ‖f τ‖ + Λ * (1 + ‖x‖) := by ring
  have := norm_le_gronwallBound_of_norm_deriv_right_le (δ := 0) (K := Λ)
    (ε := Λ * (1 + ‖x‖)) hf hf'
    (by simp [hfdef, lcZ_zero hD]) hbound (s - r) ⟨hT, le_rfl⟩
  rw [sub_zero, lc2_gb Λ (1 + ‖x‖) (s - r) hΛ] at this
  have e : lcFlow Q c B g r s x - x = f (s - r) + lcU Q g r s := by
    simp only [lcFlow, hfdef, hDdef]; abel
  rw [e]
  exact (norm_add_le _ _).trans (by linarith)


/-- The flow extended to `v ≤ r` by the identity (`v ↦ max v r`). -/
def lcFlowExt (Q : Matrix (Fin d) (Fin d) ℝ) (c : ℝ → Euc d) (B : ℝ → Euc d → Euc d)
    (g : ℝ → Euc d) (r v : ℝ) (x : Euc d) : Euc d := lcFlow Q c B g r (max v r) x

theorem lcFlow_self (H : LcHyp Q k Λc ΛB c B) (hg : Continuous g) {r : ℝ} (hr : 0 ≤ r)
    (x : Euc d) : lcFlow Q c B g r r x = x := by
  simp [lcFlow, lcZ_zero (lcDrift_isLipschitz H hg hr), lcU_self]

theorem lcFlowExt_of_le (H : LcHyp Q k Λc ΛB c B) (hg : Continuous g) {r : ℝ} (hr : 0 ≤ r)
    {v : ℝ} (hv : v ≤ r) (x : Euc d) : lcFlowExt Q c B g r v x = x := by
  simp [lcFlowExt, max_eq_right hv, lcFlow_self H hg hr]

theorem lcFlowExt_of_ge {r v : ℝ} (hv : r ≤ v) (x : Euc d) :
    lcFlowExt Q c B g r v x = lcFlow Q c B g r v x := by
  simp [lcFlowExt, max_eq_left hv]

theorem lc2_Z_continuousOn (H : LcHyp Q k Λc ΛB c B) (hg : Continuous g) {r : ℝ} (hr : 0 ≤ r)
    (x : Euc d) : ContinuousOn (lcZ (lcDrift Q c B g r) x) (Ici 0) := by
  intro τ hτ
  have h := lcZ_cont (lcDrift_isLipschitz H hg hr) x (t := τ + 1) (by
    have : (0 : ℝ) ≤ τ := hτ
    linarith)
  have hτ' : τ ∈ Icc 0 (τ + 1) := ⟨hτ, by linarith⟩
  refine (h τ hτ').mono_of_mem_nhdsWithin ?_
  exact mem_nhdsWithin.2 ⟨Iio (τ + 1), isOpen_Iio, by simp, fun y hy => ⟨hy.2, hy.1.le⟩⟩

theorem lcFlowExt_continuous_v (H : LcHyp Q k Λc ΛB c B) (hg : Continuous g) {r : ℝ} (hr : 0 ≤ r)
    (x : Euc d) : Continuous fun v => lcFlowExt Q c B g r v x := by
  have hm : Continuous fun v : ℝ => max v r := continuous_id.max continuous_const
  have h1 : Continuous fun v : ℝ => lcZ (lcDrift Q c B g r) x (max v r - r) := by
    refine continuousOn_univ.1 ?_
    exact (lc2_Z_continuousOn H hg hr x).comp (hm.sub continuous_const).continuousOn
      (fun v _ => mem_Ici.2 (sub_nonneg.2 (le_max_right _ _)))
  have h2 : Continuous fun v : ℝ => lcU Q g r (max v r) := (lcU_continuous_v Q hg r).comp hm
  exact h1.add h2

/-- Two flows started at nearby times, compared at a common later time `v`. -/
theorem lc2_close (H : LcHyp Q k Λc ΛB c B) (hg : Continuous g) (x0 : Euc d) {r r1 T η : ℝ}
    (hr : 0 ≤ r) (hrr1 : r ≤ r1) (h1 : r1 - r ≤ 1) (hT : 0 ≤ T)
    (hη : ∀ s ∈ Icc r r1, ‖lcU Q g r s‖ ≤ η) {v : ℝ} (hv : v ≤ T) :
    ‖lcFlowExt Q c B g r v x0 - lcFlowExt Q c B g r1 v x0‖ ≤
      Real.exp (lcLam Q Λc ΛB * T) *
        ((1 + ‖x0‖) * (lcLam Q Λc ΛB * Real.exp (lcLam Q Λc ΛB) * (r1 - r)) + η) := by
  have hr1 : 0 ≤ r1 := hr.trans hrr1
  have hΛ := H.lam_nonneg
  set Λ := lcLam Q Λc ΛB with hΛdef
  have hη0 : 0 ≤ η := (norm_nonneg _).trans (hη r ⟨le_rfl, hrr1⟩)
  set Br := (1 + ‖x0‖) * (Λ * Real.exp Λ * (r1 - r)) + η with hBr
  have hBr0 : 0 ≤ Br := by
    have : 0 ≤ r1 - r := sub_nonneg.2 hrr1
    positivity
  have hE : 1 ≤ Real.exp (Λ * T) := Real.one_le_exp (mul_nonneg hΛ hT)
  have hmove : ∀ s ∈ Icc r r1, ‖lcFlow Q c B g r s x0 - x0‖ ≤ Br := by
    intro s hs
    have h := lc2_move H hg hr hs.1 x0
    have ht0 : 0 ≤ s - r := sub_nonneg.2 hs.1
    have ht1 : s - r ≤ r1 - r := by linarith [hs.2]
    have hexp : Real.exp (Λ * (s - r)) - 1 ≤ Λ * Real.exp Λ * (r1 - r) := by
      have h2 := lc2_exp_sub_one_le (mul_nonneg hΛ ht0)
      have h3 : Real.exp (Λ * (s - r)) ≤ Real.exp Λ :=
        Real.exp_le_exp.2 (by nlinarith)
      calc Real.exp (Λ * (s - r)) - 1 ≤ Λ * (s - r) * Real.exp (Λ * (s - r)) := h2
        _ ≤ Λ * (r1 - r) * Real.exp Λ := by
            gcongr
        _ = Λ * Real.exp Λ * (r1 - r) := by ring
    have h4 : (1 + ‖x0‖) * (Real.exp (Λ * (s - r)) - 1) ≤
        (1 + ‖x0‖) * (Λ * Real.exp Λ * (r1 - r)) := by gcongr
    have h5 := hη s hs
    linarith
  by_cases hvr1 : v ≤ r1
  · rw [lcFlowExt_of_le H hg hr1 hvr1]
    by_cases hvr : v ≤ r
    · rw [lcFlowExt_of_le H hg hr hvr]
      simp only [sub_self, norm_zero]
      positivity
    · replace hvr := not_le.1 hvr
      rw [lcFlowExt_of_ge hvr.le]
      calc _ ≤ Br := hmove v ⟨hvr.le, hvr1⟩
        _ ≤ Real.exp (Λ * T) * Br := le_mul_of_one_le_left hBr0 hE
  · replace hvr1 := not_le.1 hvr1
    rw [lcFlowExt_of_ge (hrr1.trans hvr1.le), lcFlowExt_of_ge hvr1.le,
      lc_flow_cocycle H hg hr hrr1 hvr1.le x0]
    have hL := lcFlow_lipschitz H hg hr1 hvr1.le (lcFlow Q c B g r r1 x0) x0
    have hexp : Real.exp (Λ * (v - r1)) ≤ Real.exp (Λ * T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) hΛ)
    calc _ ≤ Real.exp (Λ * (v - r1)) * ‖lcFlow Q c B g r r1 x0 - x0‖ := hL
      _ ≤ Real.exp (Λ * T) * Br := by
          gcongr
          exact hmove r1 ⟨hrr1, le_rfl⟩


/-- Symmetric form of `lc2_close`. -/
theorem lc2_close_sym (H : LcHyp Q k Λc ΛB c B) (hg : Continuous g) (x0 : Euc d) {r r1 T η : ℝ}
    (hr : 0 ≤ r) (hr1 : 0 ≤ r1) (h1 : |r - r1| ≤ 1) (hT : 0 ≤ T)
    (hη : ∀ s ∈ Icc (min r r1) (max r r1), ‖lcU Q g (min r r1) s‖ ≤ η) {v : ℝ} (hv : v ≤ T) :
    ‖lcFlowExt Q c B g r v x0 - lcFlowExt Q c B g r1 v x0‖ ≤
      Real.exp (lcLam Q Λc ΛB * T) *
        ((1 + ‖x0‖) * (lcLam Q Λc ΛB * Real.exp (lcLam Q Λc ΛB) * |r - r1|) + η) := by
  rcases le_total r r1 with h | h
  · rw [min_eq_left h, max_eq_right h] at hη
    rw [abs_of_nonpos (sub_nonpos.2 h), neg_sub]
    rw [abs_of_nonpos (sub_nonpos.2 h), neg_sub] at h1
    exact lc2_close H hg x0 hr h h1 hT hη hv
  · rw [min_eq_right h, max_eq_left h] at hη
    rw [abs_of_nonneg (sub_nonneg.2 h)]
    rw [abs_of_nonneg (sub_nonneg.2 h)] at h1
    rw [norm_sub_rev]
    exact lc2_close H hg x0 hr1 h h1 hT hη hv

/-- Continuity of `(r, v) ↦ lcFlowExt r v x0` (epsilon-delta form). -/
theorem lc2_ext_cont_at (H : LcHyp Q k Λc ΛB c B) (hg : Continuous g) (x0 : Euc d) {r0 v0 : ℝ}
    (hr0 : 0 ≤ r0) :
    ∀ ε > 0, ∃ δ > 0, ∀ r v : ℝ, 0 ≤ r → |r - r0| < δ → |v - v0| < δ →
      ‖lcFlowExt Q c B g r v x0 - lcFlowExt Q c B g r0 v0 x0‖ < ε := by
  intro ε hε
  have hΛ := H.lam_nonneg
  set Λ := lcLam Q Λc ΛB with hΛdef
  set T : ℝ := |v0| + 1 with hTdef
  have hT : 0 ≤ T := by positivity
  set E := Real.exp (Λ * T) with hEdef
  have hE : 1 ≤ E := Real.one_le_exp (mul_nonneg hΛ hT)
  have hE0 : 0 < E := by linarith
  set C1 := (1 + ‖x0‖) * (Λ * Real.exp Λ) with hC1
  have hC10 : 0 ≤ C1 := by positivity
  set η := ε / (8 * E) with hηdef
  have hη0 : 0 < η := by positivity
  -- continuity of lcU at (r0, r0)
  have hUc := (lcU_continuous Q hg).continuousAt (x := (r0, r0))
  rw [Metric.continuousAt_iff] at hUc
  obtain ⟨δU, hδU, hU⟩ := hUc η hη0
  -- continuity in v
  have hvc := (lcFlowExt_continuous_v H hg hr0 x0).continuousAt (x := v0)
  rw [Metric.continuousAt_iff] at hvc
  obtain ⟨δv, hδv, hv⟩ := hvc (ε / 2) (half_pos hε)
  set δa := ε / (8 * E * (C1 + 1)) with hδa
  have hδa0 : 0 < δa := by positivity
  refine ⟨min (min δa δU) (min δv 1), by positivity, fun r v hr hrd hvd => ?_⟩
  have hδ1 : min (min δa δU) (min δv 1) ≤ δa := (min_le_left _ _).trans (min_le_left _ _)
  have hδ2 : min (min δa δU) (min δv 1) ≤ δU := (min_le_left _ _).trans (min_le_right _ _)
  have hδ3 : min (min δa δU) (min δv 1) ≤ δv := (min_le_right _ _).trans (min_le_left _ _)
  have hδ4 : min (min δa δU) (min δv 1) ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hrd' : |r - r0| < δa := lt_of_lt_of_le hrd hδ1
  have hvT : v ≤ T := by
    have := abs_lt.1 (lt_of_lt_of_le hvd hδ4)
    have := le_abs_self v0
    linarith [abs_lt.1 (lt_of_lt_of_le hvd hδ4)]
  have hrr0 : |r - r0| ≤ 1 := by linarith
  have hη : ∀ s ∈ Icc (min r r0) (max r r0), ‖lcU Q g (min r r0) s‖ ≤ η := by
    intro s hs
    have h1 : |min r r0 - r0| ≤ |r - r0| := by
      rcases le_total r r0 with h | h
      · rw [min_eq_left h]
      · rw [min_eq_right h]; simp
    have h2 : |s - r0| ≤ |r - r0| := by
      rw [abs_le]
      rcases le_total r r0 with h | h
      · rw [min_eq_left h, max_eq_right h] at hs
        rw [abs_of_nonpos (sub_nonpos.2 h)]; constructor <;> linarith [hs.1, hs.2]
      · rw [min_eq_right h, max_eq_left h] at hs
        rw [abs_of_nonneg (sub_nonneg.2 h)]; constructor <;> linarith [hs.1, hs.2]
    have hd : dist (min r r0, s) (r0, r0) < δU := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact max_lt (lt_of_le_of_lt h1 (lt_of_lt_of_le hrd hδ2))
        (lt_of_le_of_lt h2 (lt_of_lt_of_le hrd hδ2))
    have := hU hd
    rw [dist_eq_norm, lcU_self] at this
    simp only [sub_zero] at this
    exact this.le
  have hclose := lc2_close_sym H hg x0 hr hr0 hrr0 hT hη hvT
  have hv' : ‖lcFlowExt Q c B g r0 v x0 - lcFlowExt Q c B g r0 v0 x0‖ < ε / 2 := by
    have := hv (x := v) (by rw [Real.dist_eq]; exact lt_of_lt_of_le hvd hδ3)
    rwa [dist_eq_norm] at this
  have hb : E * ((1 + ‖x0‖) * (Λ * Real.exp Λ * |r - r0|) + η) < ε / 2 := by
    have h1 : E * ((1 + ‖x0‖) * (Λ * Real.exp Λ * |r - r0|)) ≤ E * (C1 * δa) := by
      have : (1 + ‖x0‖) * (Λ * Real.exp Λ * |r - r0|) = C1 * |r - r0| := by rw [hC1]; ring
      rw [this]
      gcongr
    have h2 : E * (C1 * δa) ≤ ε / 8 := by
      rw [hδa]
      have : E * (C1 * (ε / (8 * E * (C1 + 1)))) = ε / 8 * (C1 / (C1 + 1)) := by
        field_simp
      rw [this]
      have : C1 / (C1 + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      nlinarith
    have h3 : E * η = ε / 8 := by rw [hηdef]; field_simp
    nlinarith
  calc _ ≤ ‖lcFlowExt Q c B g r v x0 - lcFlowExt Q c B g r0 v x0‖ +
        ‖lcFlowExt Q c B g r0 v x0 - lcFlowExt Q c B g r0 v0 x0‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε := by linarith

/-- **Continuity** of `(r, v, x) ↦ lcFlow Q c B g r v x` on `{0 ≤ r ≤ v}`. -/
theorem lc_flow_continuous (H : LcHyp Q k Λc ΛB c B) (hg : Continuous g) :
    ContinuousOn (fun p : ℝ × ℝ × Euc d => lcFlow Q c B g p.1 p.2.1 p.2.2)
      {p : ℝ × ℝ × Euc d | 0 ≤ p.1 ∧ p.1 ≤ p.2.1} := by
  rintro ⟨r0, v0, x0⟩ ⟨hr0, hv0⟩
  simp only at hr0 hv0
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hΛ := H.lam_nonneg
  set Λ := lcLam Q Λc ΛB with hΛdef
  obtain ⟨δ1, hδ1, h1⟩ := lc2_ext_cont_at H hg x0 (r0 := r0) (v0 := v0) hr0 (ε / 2) (half_pos hε)
  set T : ℝ := |v0| + 1 with hTdef
  have hT : 0 ≤ T := by positivity
  set E := Real.exp (Λ * T) with hEdef
  have hE0 : 0 < E := Real.exp_pos _
  refine ⟨min (min δ1 (ε / (2 * E))) 1, by positivity, ?_⟩
  rintro ⟨r, v, x⟩ ⟨hr, hrv⟩ hd
  simp only at hr hrv
  rw [Prod.dist_eq, Prod.dist_eq, max_lt_iff, max_lt_iff] at hd
  have hdr := hd.1
  have hdv := hd.2.1
  have hdx := hd.2.2
  rw [Real.dist_eq] at hdr hdv
  have hδa : min (min δ1 (ε / (2 * E))) 1 ≤ δ1 := (min_le_left _ _).trans (min_le_left _ _)
  have hδb : min (min δ1 (ε / (2 * E))) 1 ≤ ε / (2 * E) :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hδc : min (min δ1 (ε / (2 * E))) 1 ≤ 1 := min_le_right _ _
  have hvT : v - r ≤ T := by
    have := abs_lt.1 (lt_of_lt_of_le hdv hδc)
    have := le_abs_self v0
    linarith [abs_lt.1 (lt_of_lt_of_le hdv hδc)]
  have hL := lcFlow_lipschitz H hg hr hrv x x0
  have hL' : ‖lcFlow Q c B g r v x - lcFlow Q c B g r v x0‖ ≤ E * ‖x - x0‖ := by
    exact hL.trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hvT hΛ)) (norm_nonneg _))
  have hxd : ‖x - x0‖ < ε / (2 * E) := by
    rw [← dist_eq_norm]; exact lt_of_lt_of_le hdx hδb
  have h2 : E * ‖x - x0‖ < ε / 2 := by
    have := mul_lt_mul_of_pos_left hxd hE0
    calc E * ‖x - x0‖ < E * (ε / (2 * E)) := this
      _ = ε / 2 := by field_simp
  have h3 := h1 r v hr (lt_of_lt_of_le hdr hδa) (lt_of_lt_of_le hdv hδa)
  rw [lcFlowExt_of_ge hrv, lcFlowExt_of_ge hv0] at h3
  rw [dist_eq_norm]
  calc _ ≤ ‖lcFlow Q c B g r v x - lcFlow Q c B g r v x0‖ +
        ‖lcFlow Q c B g r v x0 - lcFlow Q c B g r0 v0 x0‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε := by linarith

end Cont

/-! ### Main theorem and the time clamp -/

section Main

variable {Q : Matrix (Fin d) (Fin d) ℝ} {k : ℕ} {Λc ΛB : ℝ} {c : ℝ → Euc d}
  {B : ℝ → Euc d → Euc d}

/-- **LC-1 (pathwise flow).**  Under `LcHyp Q k Λc ΛB c B`, for every continuous noise path `g` and
every starting time `r ≥ 0`, with `Λ = lcLam Q Λc ΛB = ‖Q‖ + Λc + ΛB` (independent of `g`, `r`, `x`, `v`):
(a) for every `x`, `τ ↦ lcFlow Q c B g r (r + τ) x` is a pathwise solution on `[0, ∞)` of
`X_τ = x + ∫_0^τ (-Q X_s - c_{r+s} + B_{r+s}(X_s)) ds + (g (r+τ) - g r)` (noise directions `lcSigma d`,
noise path `lcW g r`);
(b) `lcFlow Q c B g r v` is `C^{k+1}` for `v ≥ r`; (c) `‖D lcFlow Q c B g r v‖ ≤ exp (Λ (v - r))`.
The flow property, uniqueness and continuity in `(r, v, x)` are `lc_flow_cocycle`, `lc_flow_unique`,
`lc_flow_continuous`. -/
theorem lc_flow (Q : Matrix (Fin d) (Fin d) ℝ) (k : ℕ) (Λc ΛB : ℝ) (c : ℝ → Euc d)
    (B : ℝ → Euc d → Euc d) (H : LcHyp Q k Λc ΛB c B) (g : ℝ → Euc d) (hg : Continuous g)
    (r : ℝ) (hr : 0 ≤ r) :
    (∀ x : Euc d, IsPathSolution (fun τ y => -(Torus.matVec Q y) - c (r + τ) + B (r + τ) y)
      (lcSigma d) (lcW g r) x ⊤ (fun τ => lcFlow Q c B g r (r + τ) x)) ∧
    (∀ v, r ≤ v → ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (lcFlow Q c B g r v)) ∧
    (∀ v, r ≤ v → ∀ x : Euc d,
      ‖fderiv ℝ (lcFlow Q c B g r v) x‖ ≤ Real.exp (lcLam Q Λc ΛB * (v - r))) :=
  ⟨fun x => lcFlow_isPathSolution H hg hr x, fun _ hv => lcFlow_contDiff H hg hr hv,
    fun _ hv x => lcFlow_fderiv_le H hg hr hv x⟩

/-- Clamping the time makes data given on `[0,T]` only satisfy `LcHyp` (the hypotheses of the
supplement lemma `local_decay`, with `T ≥ 0`). -/
theorem lcHyp_clamp {T : ℝ} (hT : 0 ≤ T) (hc : ContinuousOn c (Icc 0 T))
    (hB : ContinuousOn (fun p : ℝ × Euc d => B p.1 p.2) (Icc 0 T ×ˢ univ))
    (hcb : ∀ t ∈ Icc 0 T, ‖c t‖ ≤ Λc)
    (hBs : ∀ t ∈ Icc 0 T, ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (B t) ∧
      ∀ j : ℕ, j ≤ k + 1 → ∀ x, ‖iteratedFDeriv ℝ j (B t) x‖ ≤ ΛB) :
    LcHyp Q k Λc ΛB (fun v => c (min v T)) (fun v => B (min v T)) where
  c_cont := hc.comp (continuous_id.min continuous_const).continuousOn
    (fun v hv => ⟨le_min hv hT, min_le_right _ _⟩)
  B_cont := hB.comp ((continuous_fst.min continuous_const).prodMk continuous_snd).continuousOn
    (fun p hp => ⟨⟨le_min hp.1 hT, min_le_right _ _⟩, mem_univ _⟩)
  c_bd v hv := hcb _ ⟨le_min hv hT, min_le_right _ _⟩
  B_smooth v hv := (hBs _ ⟨le_min hv hT, min_le_right _ _⟩).1
  B_bd v hv j hj x := (hBs _ ⟨le_min hv hT, min_le_right _ _⟩).2 j hj x

/-- On `[0,T]` the clamped data agree with the original data. -/
theorem lcB_clamp_eq (Q : Matrix (Fin d) (Fin d) ℝ) (c : ℝ → Euc d) (B : ℝ → Euc d → Euc d)
    {T r τ : ℝ} (h : r + τ ≤ T) (y : Euc d) :
    lcB Q (fun v => c (min v T)) (fun v => B (min v T)) r τ y = lcB Q c B r τ y := by
  simp [lcB, min_eq_left h]

end Main

end HRS.MS.Lc
