import HRS.MS.FlowC
import HRS.Whole.Thermal

/-!
# POIS-FLOW, part 1: the OU shift and the pathwise flow map (definitions, ODE and SDE identities)

Setting.  `d`-dimensional noise path `w : ℝ≥0 → Fin d → ℝ` (continuous, `w 0 = 0`), `σ k = √2 e_k`
(`pfSigma`), `b y = -q y + B y`.  The pathwise equation `X_t = x + ∫_0^t b(X_s) ds + √2 w_t` is solved
through the Ornstein-Uhlenbeck shift
`U_t = w_t - q ∫_0^t e^{-q(t-s)} w_s ds` (`ouShift`; `w_t` is read as the vector `toLp 2 (w t)`):

* `U` is continuous and satisfies `U_t = w_t - q ∫_0^t U_s ds` (`pf_ou_integral`);
* `Z = X - √2 U` solves the random ODE `Z' = -q Z + B(Z + √2 U_t)`, `Z_0 = x`
  (`pfDrift`, `pfZ`), whose drift is globally Lipschitz in `z`, so a global solution exists
  (`exists_ode_additive_global` with zero noise);
* `flowMap q B w t x := Z_t(x) + √2 U_t` (`flowMap`) is then a pathwise solution
  (`pf_flowMap_isPathSolution`).

`pfZ`/`flowMap` are defined by choice of a global pathwise solution (junk value `x`, resp. `x + √2 U_t`,
if none exists, which is excluded under the hypotheses of the theorems).  The regularity in `x` and the
uniform derivative bounds (the theorem `pois_flow`) are in `PoisFlowAux2`.  Helper lemmas carry the
prefix `pf_`.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

noncomputable section

namespace HRS.MS.PoisFlow

variable {d : ℕ}

/-- The noise directions `σ k = √2 e_k`. -/
def pfSigma (d : ℕ) : Fin d → Euc d := fun k => Real.sqrt 2 • EuclideanSpace.single k (1 : ℝ)

/-- The noise path as a vector of `Euc d`, read at real time (negative times read `w 0`). -/
def pfPath (w : ℝ≥0 → Fin d → ℝ) (t : ℝ) : Euc d := WithLp.toLp 2 (w t.toNNReal)

/-- The Ornstein-Uhlenbeck shift `U_t = w_t - q ∫_0^t e^{-q(t-s)} w_s ds`. -/
def ouShift (q : ℝ) (w : ℝ≥0 → Fin d → ℝ) (t : ℝ) : Euc d :=
  pfPath w t - q • ∫ s in (0 : ℝ)..t, Real.exp (-q * (t - s)) • pfPath w s

/-- Drift of the random ODE for `Z = X - √2 U`: `-q z + B(z + √2 U_t)`. -/
def pfDrift (q : ℝ) (B : Euc d → Euc d) (w : ℝ≥0 → Fin d → ℝ) (t : ℝ) (z : Euc d) : Euc d :=
  -q • z + B (z + Real.sqrt 2 • ouShift q w t)

open scoped Classical in
/-- A global solution `Z_·(x)` of the random ODE `Z' = pfDrift`, `Z_0 = x` (chosen). -/
def pfZ (q : ℝ) (B : Euc d → Euc d) (w : ℝ≥0 → Fin d → ℝ) (x : Euc d) : ℝ → Euc d :=
  if h : ∃ y : ℝ → Euc d, IsPathSolution (pfDrift q B w) (pfSigma d)
      (0 : ℝ≥0 → Fin d → ℝ) x ⊤ y then h.choose else fun _ => x

/-- The pathwise flow map `x ↦ Z_t(x) + √2 U_t`. -/
def flowMap (q : ℝ) (B : Euc d → Euc d) (w : ℝ≥0 → Fin d → ℝ) (t : ℝ) (x : Euc d) : Euc d :=
  pfZ q B w x t + Real.sqrt 2 • ouShift q w t

/-! ### The noise path and the OU shift -/

theorem pf_addNoise (w : ℝ≥0 → Fin d → ℝ) (t : ℝ) :
    addNoise (pfSigma d) w t = Real.sqrt 2 • pfPath w t := by
  ext i
  simp [addNoise, pfSigma, pfPath, Pi.single_apply, Finset.sum_apply, mul_comm]

theorem pf_continuous_path {w : ℝ≥0 → Fin d → ℝ} (hw : Continuous w) : Continuous (pfPath w) :=
  (PiLp.continuous_toLp 2 _).comp (hw.comp continuous_real_toNNReal)

theorem pf_path_zero {w : ℝ≥0 → Fin d → ℝ} (hw0 : w 0 = 0) : pfPath w 0 = 0 := by
  simp [pfPath, hw0]

/-- The primitive `A_t = ∫_0^t e^{qs} w_s ds`. -/
def pfA (q : ℝ) (w : ℝ≥0 → Fin d → ℝ) (t : ℝ) : Euc d :=
  ∫ s in (0 : ℝ)..t, Real.exp (q * s) • pfPath w s

theorem pf_ou_eq (q : ℝ) (w : ℝ≥0 → Fin d → ℝ) (t : ℝ) :
    ouShift q w t = pfPath w t - (q * Real.exp (-q * t)) • pfA q w t := by
  unfold ouShift pfA
  have : ∫ s in (0 : ℝ)..t, Real.exp (-q * (t - s)) • pfPath w s =
      Real.exp (-q * t) • ∫ s in (0 : ℝ)..t, Real.exp (q * s) • pfPath w s := by
    rw [← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [smul_smul, ← Real.exp_add]
    congr 2; ring
  rw [this, smul_smul]

theorem pf_hasDerivAt_A {q : ℝ} {w : ℝ≥0 → Fin d → ℝ} (hw : Continuous w) (t : ℝ) :
    HasDerivAt (pfA q w) (Real.exp (q * t) • pfPath w t) t := by
  have hc : Continuous fun s => Real.exp (q * s) • pfPath w s :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul (pf_continuous_path hw)
  exact (hc.integral_hasStrictDerivAt 0 t).hasDerivAt

theorem pf_continuous_A {q : ℝ} {w : ℝ≥0 → Fin d → ℝ} (hw : Continuous w) :
    Continuous (pfA q w) :=
  continuous_iff_continuousAt.2 fun t => (pf_hasDerivAt_A hw t).continuousAt

theorem pf_continuous_ou {q : ℝ} {w : ℝ≥0 → Fin d → ℝ} (hw : Continuous w) :
    Continuous (ouShift q w) := by
  have : ouShift q w = fun t => pfPath w t - (q * Real.exp (-q * t)) • pfA q w t :=
    funext (pf_ou_eq q w)
  rw [this]
  exact (pf_continuous_path hw).sub
    ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).smul
      (pf_continuous_A hw))

theorem pf_ou_zero {q : ℝ} {w : ℝ≥0 → Fin d → ℝ} (hw0 : w 0 = 0) : ouShift q w 0 = 0 := by
  simp [ouShift, pf_path_zero hw0]

/-- The integral equation `U_t = w_t - q ∫_0^t U_s ds` (for every real `t`). -/
theorem pf_ou_integral {q : ℝ} {w : ℝ≥0 → Fin d → ℝ} (hw : Continuous w) (t : ℝ) :
    ouShift q w t = pfPath w t - q • ∫ s in (0 : ℝ)..t, ouShift q w s := by
  set P := pfPath w with hPdef
  have hP : Continuous P := pf_continuous_path hw
  set Y : ℝ → Euc d := fun s => (q * Real.exp (-q * s)) • pfA q w s with hYdef
  have hou : ∀ s, ouShift q w s = P s - Y s := fun s => pf_ou_eq q w s
  have hY : ∀ s, HasDerivAt Y (q • P s - q • Y s) s := by
    intro s
    have h1 : HasDerivAt (fun x : ℝ => Real.exp (-q * x)) (Real.exp (-q * s) * (-q * 1)) s :=
      ((hasDerivAt_id' s).const_mul (-q)).exp
    have h2 := (h1.const_mul q).smul (pf_hasDerivAt_A (q := q) hw s)
    refine h2.congr_deriv ?_
    have e1 : (q * Real.exp (-q * s)) * Real.exp (q * s) = q := by
      rw [mul_assoc, ← Real.exp_add]; simp
    have e2 : (q * Real.exp (-q * s)) • (Real.exp (q * s) • pfPath w s) = q • pfPath w s := by
      rw [smul_smul, e1]
    rw [e2, hYdef]
    simp only [smul_smul]
    rw [show q * (Real.exp (-q * s) * (-q * 1)) = -(q * (q * Real.exp (-q * s))) by ring,
      sub_eq_add_neg, ← neg_smul]
  have hYc : Continuous Y := continuous_iff_continuousAt.2 fun s => (hY s).continuousAt
  have hY0 : Y 0 = 0 := by simp [hYdef, pfA]
  have hPi : IntervalIntegrable (fun s => q • P s) volume 0 t :=
    (hP.const_smul q).intervalIntegrable _ _
  have hYi : IntervalIntegrable (fun s => q • Y s) volume 0 t :=
    (hYc.const_smul q).intervalIntegrable _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hY s) (hPi.sub hYi)
  rw [hY0, sub_zero, intervalIntegral.integral_sub hPi hYi, intervalIntegral.integral_smul,
    intervalIntegral.integral_smul] at hftc
  have hP1 : IntervalIntegrable P volume 0 t := hP.intervalIntegrable _ _
  have hY1 : IntervalIntegrable Y volume 0 t := hYc.intervalIntegrable _ _
  have h3 : ∫ s in (0 : ℝ)..t, ouShift q w s = ∫ s in (0 : ℝ)..t, (P s - Y s) :=
    intervalIntegral.integral_congr fun s _ => hou s
  rw [h3, intervalIntegral.integral_sub hP1 hY1, smul_sub, hftc]
  exact hou t

/-! ### The random ODE `Z' = pfDrift` -/

/-- Standing hypotheses of the pathwise construction. -/
structure PfHyp (q Mb : ℝ) (m : ℕ) (B : Euc d → Euc d) (w : ℝ≥0 → Fin d → ℝ) : Prop where
  hq : 0 ≤ q
  hm : 1 ≤ m
  hB : HasCbBound m Mb B
  hw : Continuous w
  hw0 : w 0 = 0

theorem pf_lip_of_cb {m : ℕ} (hm : 1 ≤ m) {Mb : ℝ} {B : Euc d → Euc d}
    (hB : HasCbBound m Mb B) : ∀ x y, ‖B x - B y‖ ≤ Mb * ‖x - y‖ := by
  have hd : Differentiable ℝ B := hB.1.differentiable (by exact_mod_cast (by omega : m ≠ 0))
  intro x y
  exact (convex_univ (𝕜 := ℝ) (E := Euc d)).norm_image_sub_le_of_norm_fderiv_le
    (f := B) (C := Mb) (fun x _ => hd x)
    (fun x _ => by rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]; exact hB.2 1 hm x)
    (mem_univ y) (mem_univ x)

theorem pf_continuous_drift {q : ℝ} {B : Euc d → Euc d} (hBc : Continuous B)
    {w : ℝ≥0 → Fin d → ℝ} (hw : Continuous w) :
    Continuous (fun p : ℝ × Euc d => pfDrift q B w p.1 p.2) := by
  unfold pfDrift
  exact (Continuous.const_smul continuous_snd (-q)).add
    (hBc.comp (continuous_snd.add (((pf_continuous_ou hw).comp continuous_fst).const_smul (Real.sqrt 2))))

theorem pf_isLipschitzDrift {q Mb : ℝ} {m : ℕ} {B : Euc d → Euc d} {w : ℝ≥0 → Fin d → ℝ}
    (H : PfHyp q Mb m B w) : IsLipschitzDrift (pfDrift q B w) where
  cont := (pf_continuous_drift H.hB.1.continuous H.hw).continuousOn
  lip _ := ⟨(q + |Mb|).toNNReal, fun t _ => LipschitzWith.of_dist_le_mul fun z z' => by
    have hq := H.hq
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
    have e : pfDrift q B w t z - pfDrift q B w t z' = -q • (z - z') +
        (B (z + Real.sqrt 2 • ouShift q w t) - B (z' + Real.sqrt 2 • ouShift q w t)) := by
      unfold pfDrift; module
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖-q • (z - z')‖ = q * ‖z - z'‖ := by
      rw [norm_smul, norm_neg, Real.norm_of_nonneg hq]
    have h2 := pf_lip_of_cb H.hm H.hB (z + Real.sqrt 2 • ouShift q w t)
      (z' + Real.sqrt 2 • ouShift q w t)
    rw [add_sub_add_right_eq_sub] at h2
    have h3 : Mb * ‖z - z'‖ ≤ |Mb| * ‖z - z'‖ :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
    nlinarith⟩

theorem pf_exists_Z {q Mb : ℝ} {m : ℕ} {B : Euc d → Euc d} {w : ℝ≥0 → Fin d → ℝ}
    (H : PfHyp q Mb m B w) (x : Euc d) :
    ∃ y : ℝ → Euc d, IsPathSolution (pfDrift q B w) (pfSigma d) (0 : ℝ≥0 → Fin d → ℝ) x ⊤ y :=
  exists_ode_additive_global _ (pf_isLipschitzDrift H) (pfSigma d) 0 continuous_const rfl x

theorem pf_Z_spec {q Mb : ℝ} {m : ℕ} {B : Euc d → Euc d} {w : ℝ≥0 → Fin d → ℝ}
    (H : PfHyp q Mb m B w) (x : Euc d) :
    IsPathSolution (pfDrift q B w) (pfSigma d) (0 : ℝ≥0 → Fin d → ℝ) x ⊤ (pfZ q B w x) := by
  unfold pfZ
  rw [dif_pos (pf_exists_Z H x)]
  exact (pf_exists_Z H x).choose_spec

theorem pf_Z_zero {q Mb : ℝ} {m : ℕ} {B : Euc d → Euc d} {w : ℝ≥0 → Fin d → ℝ}
    (H : PfHyp q Mb m B w) (x : Euc d) : pfZ q B w x 0 = x :=
  (pf_Z_spec H x).1

theorem pf_Z_cont {q Mb : ℝ} {m : ℕ} {B : Euc d → Euc d} {w : ℝ≥0 → Fin d → ℝ}
    (H : PfHyp q Mb m B w) (x : Euc d) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousOn (pfZ q B w x) (Icc 0 t) :=
  ((pf_Z_spec H x).2 t ht (WithTop.coe_lt_top t)).1

theorem pf_Z_eq {q Mb : ℝ} {m : ℕ} {B : Euc d → Euc d} {w : ℝ≥0 → Fin d → ℝ}
    (H : PfHyp q Mb m B w) (x : Euc d) {t : ℝ} (ht : 0 ≤ t) :
    pfZ q B w x t = x + ∫ s in Icc 0 t, pfDrift q B w s (pfZ q B w x s) := by
  have := ((pf_Z_spec H x).2 t ht (WithTop.coe_lt_top t)).2.2
  simpa using this

theorem pf_continuousOn_drift_of {q Mb : ℝ} {m : ℕ} {B : Euc d → Euc d}
    {w : ℝ≥0 → Fin d → ℝ} (H : PfHyp q Mb m B w) {z : ℝ → Euc d} {S : Set ℝ}
    (hz : ContinuousOn z S) : ContinuousOn (fun s => pfDrift q B w s (z s)) S := by
  have h1 : ContinuousOn (fun s => (s, z s)) S := continuousOn_id.prodMk hz
  exact (pf_continuous_drift H.hB.1.continuous H.hw).comp_continuousOn h1

theorem pf_continuousOn_drift {q Mb : ℝ} {m : ℕ} {B : Euc d → Euc d} {w : ℝ≥0 → Fin d → ℝ}
    (H : PfHyp q Mb m B w) (x : Euc d) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousOn (fun s => pfDrift q B w s (pfZ q B w x s)) (Icc 0 t) :=
  pf_continuousOn_drift_of H (pf_Z_cont H x ht)

/-- A function given by `Z t = x + ∫_{[0,t]} F` with `F` continuous on `[0,T]` has right derivative
`F` on `[0,T]`. -/
theorem pf_hasDerivWithinAt_of_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {T : ℝ} {F Z : ℝ → E} {x : E} (hF : ContinuousOn F (Icc 0 T))
    (hZ : ∀ t ∈ Icc (0 : ℝ) T, Z t = x + ∫ s in Icc 0 t, F s) :
    ∀ τ ∈ Icc (0 : ℝ) T, HasDerivWithinAt Z (F τ) (Icc 0 T) τ := by
  intro τ hτ
  have hT0 : 0 ≤ T := hτ.1.trans hτ.2
  set c : ℝ → ℝ := fun s => max 0 (min s T) with hcdef
  have hcc : Continuous c := continuous_const.max (continuous_id.min continuous_const)
  have hc : ∀ s ∈ Icc (0 : ℝ) T, c s = s := fun s hs => by
    simp [hcdef, min_eq_left hs.2, max_eq_right hs.1]
  have hG : Continuous fun s => F (c s) :=
    hF.comp_continuous hcc fun s => ⟨le_max_left _ _, max_le hT0 (min_le_right _ _)⟩
  have h1 : HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, F (c s)) (F (c τ)) τ :=
    (hG.integral_hasStrictDerivAt 0 τ).hasDerivAt
  have h2 : HasDerivWithinAt (fun u => x + ∫ s in (0 : ℝ)..u, F (c s)) (F (c τ)) (Icc 0 T) τ :=
    (h1.const_add x).hasDerivWithinAt
  rw [hc τ hτ] at h2
  refine h2.congr (fun t ht => ?_) ?_
  · rw [hZ t ht, setIntegral_Icc_eq_interval ht.1]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le ht.1] at hs
    rw [hc s ⟨hs.1, hs.2.trans ht.2⟩]
  · rw [hZ τ hτ, setIntegral_Icc_eq_interval hτ.1]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le hτ.1] at hs
    rw [hc s ⟨hs.1, hs.2.trans hτ.2⟩]

theorem pf_isNegDriftFlow {q Mb : ℝ} {m : ℕ} {B : Euc d → Euc d} {w : ℝ≥0 → Fin d → ℝ}
    (H : PfHyp q Mb m B w) {T : ℝ} (hT : 0 ≤ T) :
    IsNegDriftFlow T (fun τ z => -pfDrift q B w τ z) (fun τ x => pfZ q B w x τ) where
  init x := pf_Z_zero H x
  eqn x τ hτ := by
    have := pf_hasDerivWithinAt_of_integral (pf_continuousOn_drift H x hT)
      (fun t ht => pf_Z_eq H x ht.1) τ hτ
    simpa using this

/-! ### `flowMap` is a pathwise solution of `X_t = x + ∫ b(X) + √2 w_t` -/

theorem pf_flowMap_isPathSolution {q Mb : ℝ} {m : ℕ} {B : Euc d → Euc d}
    {w : ℝ≥0 → Fin d → ℝ} (H : PfHyp q Mb m B w) (x : Euc d) :
    IsPathSolution (fun _ y => -q • y + B y) (pfSigma d) w x ⊤
      (fun t => flowMap q B w t x) := by
  have hBc : Continuous B := H.hB.1.continuous
  have hV : Continuous fun s => Real.sqrt 2 • ouShift q w s :=
    (pf_continuous_ou H.hw).const_smul (Real.sqrt 2)
  refine ⟨by simp [flowMap, pf_Z_zero H, pf_ou_zero H.hw0], fun t ht _ => ?_⟩
  have hX : ContinuousOn (fun s => flowMap q B w s x) (Icc 0 t) :=
    (pf_Z_cont H x ht).add hV.continuousOn
  have hF : ContinuousOn (fun s => -q • flowMap q B w s x + B (flowMap q B w s x)) (Icc 0 t) :=
    (hX.const_smul (-q)).add (hBc.comp_continuousOn hX)
  refine ⟨hX, hF.integrableOn_Icc, ?_⟩
  have hD := pf_continuousOn_drift H x ht
  have hq : ContinuousOn (fun s => (-q) • (Real.sqrt 2 • ouShift q w s)) (Icc 0 t) :=
    (hV.const_smul (-q)).continuousOn
  have hsplit : ∀ s, -q • flowMap q B w s x + B (flowMap q B w s x) =
      pfDrift q B w s (pfZ q B w x s) + (-q) • (Real.sqrt 2 • ouShift q w s) := by
    intro s
    unfold flowMap pfDrift
    rw [smul_add]
    abel
  have hI : ∫ s in Icc 0 t, (-q • flowMap q B w s x + B (flowMap q B w s x)) =
      (∫ s in Icc 0 t, pfDrift q B w s (pfZ q B w x s)) +
        (-q) • (Real.sqrt 2 • ∫ s in (0 : ℝ)..t, ouShift q w s) := by
    simp_rw [hsplit]
    rw [integral_add hD.integrableOn_Icc hq.integrableOn_Icc, integral_smul,
      setIntegral_Icc_eq_interval (f := fun s => Real.sqrt 2 • ouShift q w s) ht,
      intervalIntegral.integral_smul]
  have hN : ∑ k, w (Real.toNNReal t) k • pfSigma d k = Real.sqrt 2 • pfPath w t :=
    pf_addNoise w t
  rw [hI, hN]
  have hZ := pf_Z_eq H x ht
  have hU := pf_ou_integral (q := q) H.hw t
  simp only [flowMap]
  rw [hZ, hU]
  module

end HRS.MS.PoisFlow
