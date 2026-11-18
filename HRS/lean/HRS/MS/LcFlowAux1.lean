import HRS.MS.PoisFlowAux1

/-!
# LC-1, part 1: the shift `lcU` and the pathwise flow `lcFlow` (definitions, ODE and SDE identities)

Setting (supplement S4.11/S4.12, "engine").  `Q` is a real `d × d` matrix (read as the continuous
linear map `lcQ Q`), `c : ℝ → Euc d`, `B : ℝ → Euc d → Euc d` the time-dependent data,
`b_v(y) = -Q y - c_v + B_v(y)`, and `g : ℝ → Euc d` a continuous noise path.  For `r ≥ 0` the pathwise
equation
`X_v = x + ∫_r^v b_u(X_u) du + (g v - g r)`,  `v ≥ r`,
is solved through the shift (a general-matrix Ornstein-Uhlenbeck shift)
`U_v = (g v - g r) - ∫_r^v e^{-(v-u)Q} Q (g u - g r) du`  (`lcU Q g r v`),
which satisfies `U_v = (g v - g r) - Q ∫_r^v U_s ds` (`lcU_integral`).  Then `Y = X - U` solves the
random ODE `Y' = -QY - c_v + B_v(Y + U_v)` (`lcDrift`, `lcZ`), whose drift is globally Lipschitz in
`Y` (so a global solution exists) and has bounds that are uniform in the path `g`
(`IsDriftBounds` in `LcFlowAux2`).  `lcFlow Q c B g r v x := lcZ .. x (v - r) + lcU Q g r v`.

Statement adjustments relative to the plan sketch (`docs/S4_PLAN.md`, step 1): the noise directions
are the unit vectors `lcSigma d` (the plan's `pfSigma = √2 e_k` would force a rescaled path; the
time-changed noise of LC-3 has unit directions), the noise path `g` is a continuous map
`ℝ → Euc d` (a consumer with values in `Fin d → ℝ` composes with `WithLp.toLp 2`), the data `c`, `B`
and their bounds are assumed for ALL times `v ≥ 0` (a consumer with data on `[0,T]` only replaces
`c v, B v` by `c (min v T), B (min v T)`, which does not change the drift on `[0,T]`), and the starting
time `r` is `≥ 0`.  Helper lemmas carry the prefix `lc1_`.  The flow is defined by choice of a global
pathwise solution (junk value `x + lcU` if none exists, excluded under `LcHyp`).
-/

open MeasureTheory Set Filter Topology
open scoped NNReal
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

noncomputable section

namespace HRS.MS.Lc

variable {d : ℕ}

instance lc1_normedAlgebraRat : NormedAlgebra ℚ (Euc d →L[ℝ] Euc d) :=
  NormedAlgebra.restrictScalars ℚ ℝ _

instance lc1_completeSpace : CompleteSpace (Euc d →L[ℝ] Euc d) := FiniteDimensional.complete ℝ _

/-- The matrix `Q` as a continuous linear map of `Euc d`. -/
def lcQ (Q : Matrix (Fin d) (Fin d) ℝ) : Euc d →L[ℝ] Euc d :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Q)

theorem lcQ_apply (Q : Matrix (Fin d) (Fin d) ℝ) (y : Euc d) : lcQ Q y = Torus.matVec Q y := rfl

/-- The noise directions `σ k = e_k`. -/
def lcSigma (d : ℕ) : Fin d → Euc d := fun k => EuclideanSpace.single k (1 : ℝ)

/-- The noise path started at time `r`, as a function `ℝ≥0 → Fin d → ℝ` (the form used by
`IsPathSolution`): `w τ = g (r + τ) - g r`. -/
def lcW (g : ℝ → Euc d) (r : ℝ) : ℝ≥0 → Fin d → ℝ := fun τ k => g (r + (τ : ℝ)) k - g r k

/-- The shift `U_v = (g v - g r) - ∫_r^v e^{-(v-u)Q} Q (g u - g r) du`. -/
def lcU (Q : Matrix (Fin d) (Fin d) ℝ) (g : ℝ → Euc d) (r v : ℝ) : Euc d :=
  (g v - g r) - ∫ u in r..v, (NormedSpace.exp ((-(v - u)) • lcQ Q)) (lcQ Q (g u - g r))

/-- The drift of the random ODE for `Y = X - U` in time `τ = v - r`:
`-Q y - c_{r+τ} + B_{r+τ}(y + U_{r+τ})`. -/
def lcDrift (Q : Matrix (Fin d) (Fin d) ℝ) (c : ℝ → Euc d) (B : ℝ → Euc d → Euc d)
    (g : ℝ → Euc d) (r τ : ℝ) (z : Euc d) : Euc d :=
  -(lcQ Q z) - c (r + τ) + B (r + τ) (z + lcU Q g r (r + τ))

open scoped Classical in
/-- A global solution `Z_·(x)` of an ODE `Z' = D(τ, Z)`, `Z_0 = x` (chosen). -/
def lcZ (D : ℝ → Euc d → Euc d) (x : Euc d) : ℝ → Euc d :=
  if h : ∃ y : ℝ → Euc d, IsPathSolution D (lcSigma d) (0 : ℝ≥0 → Fin d → ℝ) x ⊤ y then h.choose
  else fun _ => x

/-- The pathwise flow `x ↦ Z_{v-r}(x) + U_v` from time `r` to time `v`. -/
def lcFlow (Q : Matrix (Fin d) (Fin d) ℝ) (c : ℝ → Euc d) (B : ℝ → Euc d → Euc d)
    (g : ℝ → Euc d) (r v : ℝ) (x : Euc d) : Euc d :=
  lcZ (lcDrift Q c B g r) x (v - r) + lcU Q g r v

/-- Standing hypotheses on the data (all times `v ≥ 0`): `c` continuous and bounded by `Λc`, `B`
jointly continuous, `B v ∈ C^{k+1}` with all derivatives of order `≤ k+1` (including `0`) bounded by
`ΛB`. -/
structure LcHyp (Q : Matrix (Fin d) (Fin d) ℝ) (k : ℕ) (Λc ΛB : ℝ) (c : ℝ → Euc d)
    (B : ℝ → Euc d → Euc d) : Prop where
  c_cont : ContinuousOn c (Ici 0)
  B_cont : ContinuousOn (fun p : ℝ × Euc d => B p.1 p.2) (Ici 0 ×ˢ univ)
  c_bd : ∀ v, 0 ≤ v → ‖c v‖ ≤ Λc
  B_smooth : ∀ v, 0 ≤ v → ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (B v)
  B_bd : ∀ v, 0 ≤ v → ∀ j : ℕ, j ≤ k + 1 → ∀ x, ‖iteratedFDeriv ℝ j (B v) x‖ ≤ ΛB

/-- The flow constant `Λ = ‖Q‖ + Λc + ΛB`. -/
def lcLam (Q : Matrix (Fin d) (Fin d) ℝ) (Λc ΛB : ℝ) : ℝ := ‖lcQ Q‖ + Λc + ΛB

theorem LcHyp.Λc_nonneg {Q : Matrix (Fin d) (Fin d) ℝ} {k : ℕ} {Λc ΛB : ℝ} {c : ℝ → Euc d}
    {B : ℝ → Euc d → Euc d} (H : LcHyp Q k Λc ΛB c B) : 0 ≤ Λc :=
  (norm_nonneg _).trans (H.c_bd 0 le_rfl)

theorem LcHyp.ΛB_nonneg {Q : Matrix (Fin d) (Fin d) ℝ} {k : ℕ} {Λc ΛB : ℝ} {c : ℝ → Euc d}
    {B : ℝ → Euc d → Euc d} (H : LcHyp Q k Λc ΛB c B) : 0 ≤ ΛB :=
  (norm_nonneg _).trans (H.B_bd 0 le_rfl 0 (Nat.zero_le _) 0)

theorem LcHyp.lam_nonneg {Q : Matrix (Fin d) (Fin d) ℝ} {k : ℕ} {Λc ΛB : ℝ} {c : ℝ → Euc d}
    {B : ℝ → Euc d → Euc d} (H : LcHyp Q k Λc ΛB c B) : 0 ≤ lcLam Q Λc ΛB := by
  have := H.Λc_nonneg; have := H.ΛB_nonneg
  unfold lcLam; positivity

/-! ### The shift `lcU` -/

section U

variable (Q : Matrix (Fin d) (Fin d) ℝ) {g : ℝ → Euc d}

theorem lc1_commute (A : Euc d →L[ℝ] Euc d) (a b : ℝ) : Commute (a • A) (b • A) := by
  unfold Commute SemiconjBy
  ext x
  simp only [mul_apply_eq_comp, ContinuousLinearMap.smul_apply, map_smul]
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

theorem lc1_exp_split (v u : ℝ) :
    NormedSpace.exp ((-(v - u)) • lcQ Q) =
      NormedSpace.exp ((-v) • lcQ Q) * NormedSpace.exp (u • lcQ Q) := by
  rw [← NormedSpace.exp_add_of_commute (lc1_commute _ _ _)]
  congr 1
  module

theorem lc1_exp_cancel (v : ℝ) :
    NormedSpace.exp ((-v) • lcQ Q) * NormedSpace.exp (v • lcQ Q) = 1 := by
  rw [← NormedSpace.exp_add_of_commute (lc1_commute _ _ _),
    show (-v) • lcQ Q + v • lcQ Q = 0 by module, NormedSpace.exp_zero]

/-- The integrand `u ↦ e^{uQ} Q (g u - g r)` is continuous. -/
theorem lc1_cont_integrand (hg : Continuous g) (r : ℝ) :
    Continuous fun u : ℝ => NormedSpace.exp (u • lcQ Q) (lcQ Q (g u - g r)) := by
  have h1 : Continuous fun u : ℝ => NormedSpace.exp (u • lcQ Q) :=
    NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
  exact h1.clm_apply ((lcQ Q).continuous.comp (hg.sub continuous_const))

/-- `lcU` in terms of the primitive `∫_r^v e^{uQ} Q (g u - g r) du`. -/
theorem lcU_eq (hg : Continuous g) (r v : ℝ) :
    lcU Q g r v = (g v - g r) - NormedSpace.exp ((-v) • lcQ Q)
      (∫ u in r..v, NormedSpace.exp (u • lcQ Q) (lcQ Q (g u - g r))) := by
  unfold lcU
  congr 1
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm _
    ((lc1_cont_integrand Q hg r).intervalIntegrable r v)]
  refine intervalIntegral.integral_congr fun u _ => ?_
  rw [lc1_exp_split, mul_apply_eq_comp]

theorem lcU_self (r : ℝ) : lcU Q g r r = 0 := by simp [lcU]

/-- The function `v ↦ e^{-vQ} ∫_r^v e^{uQ} Q (g u - g r) du` is differentiable with derivative
`-Q (·) + Q (g v - g r)`. -/
theorem lc1_hasDerivAt_phi (hg : Continuous g) (r v : ℝ) :
    HasDerivAt (fun v => NormedSpace.exp ((-v) • lcQ Q)
        (∫ u in r..v, NormedSpace.exp (u • lcQ Q) (lcQ Q (g u - g r))))
      (-(lcQ Q (NormedSpace.exp ((-v) • lcQ Q)
        (∫ u in r..v, NormedSpace.exp (u • lcQ Q) (lcQ Q (g u - g r))))) +
        lcQ Q (g v - g r)) v := by
  have hE : HasDerivAt (fun v : ℝ => NormedSpace.exp ((-v) • lcQ Q))
      (-(lcQ Q * NormedSpace.exp ((-v) • lcQ Q))) v := by
    have h1 := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (lcQ Q) (-v)
    have h2 := h1.scomp v (hasDerivAt_neg v)
    refine h2.congr_deriv ?_
    simp only [neg_smul, one_smul]
    congr 3
    module
  have hA : HasDerivAt (fun v => ∫ u in r..v, NormedSpace.exp (u • lcQ Q) (lcQ Q (g u - g r)))
      (NormedSpace.exp (v • lcQ Q) (lcQ Q (g v - g r))) v :=
    ((lc1_cont_integrand Q hg r).integral_hasStrictDerivAt r v).hasDerivAt
  have h := hE.clm_apply hA
  refine h.congr_deriv ?_
  have e1 : NormedSpace.exp ((-v) • lcQ Q) (NormedSpace.exp (v • lcQ Q) (lcQ Q (g v - g r))) =
      lcQ Q (g v - g r) := by
    rw [← mul_apply_eq_comp, lc1_exp_cancel, one_apply_eq_self]
  rw [e1]
  simp [mul_apply_eq_comp]

theorem lcU_continuous_v (hg : Continuous g) (r : ℝ) : Continuous (lcU Q g r) := by
  have : lcU Q g r = fun v => (g v - g r) - NormedSpace.exp ((-v) • lcQ Q)
      (∫ u in r..v, NormedSpace.exp (u • lcQ Q) (lcQ Q (g u - g r))) := funext (lcU_eq Q hg r)
  rw [this]
  refine (hg.sub continuous_const).sub (continuous_iff_continuousAt.2 fun v => ?_)
  exact (lc1_hasDerivAt_phi Q hg r v).continuousAt

/-- Joint continuity of `(r, v) ↦ lcU Q g r v`. -/
theorem lcU_continuous (hg : Continuous g) : Continuous fun p : ℝ × ℝ => lcU Q g p.1 p.2 := by
  have hf : Continuous (Function.uncurry fun (p : ℝ × ℝ) (u : ℝ) =>
      (NormedSpace.exp ((-(p.2 - u)) • lcQ Q)) (lcQ Q (g u - g p.1))) := by
    have h1 : Continuous fun q : (ℝ × ℝ) × ℝ => NormedSpace.exp ((-(q.1.2 - q.2)) • lcQ Q) :=
      NormedSpace.exp_continuous.comp
        ((((continuous_snd.comp continuous_fst).sub continuous_snd).neg).smul continuous_const)
    exact h1.clm_apply ((lcQ Q).continuous.comp
      ((hg.comp continuous_snd).sub (hg.comp (continuous_fst.comp continuous_fst))))
  have h0 : Continuous fun p : ℝ × ℝ =>
      ∫ u in (0 : ℝ)..p.2, (NormedSpace.exp ((-(p.2 - u)) • lcQ Q)) (lcQ Q (g u - g p.1)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hf continuous_snd
  have h1 : Continuous fun p : ℝ × ℝ =>
      ∫ u in (0 : ℝ)..p.1, (NormedSpace.exp ((-(p.2 - u)) • lcQ Q)) (lcQ Q (g u - g p.1)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hf continuous_fst
  have hsplit : ∀ p : ℝ × ℝ, (∫ u in p.1..p.2,
      (NormedSpace.exp ((-(p.2 - u)) • lcQ Q)) (lcQ Q (g u - g p.1))) =
      (∫ u in (0 : ℝ)..p.2, (NormedSpace.exp ((-(p.2 - u)) • lcQ Q)) (lcQ Q (g u - g p.1))) -
      ∫ u in (0 : ℝ)..p.1, (NormedSpace.exp ((-(p.2 - u)) • lcQ Q)) (lcQ Q (g u - g p.1)) := by
    intro p
    have hc : Continuous fun u : ℝ =>
        (NormedSpace.exp ((-(p.2 - u)) • lcQ Q)) (lcQ Q (g u - g p.1)) :=
      hf.comp (continuous_const.prodMk continuous_id)
    rw [← intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
  have : (fun p : ℝ × ℝ => lcU Q g p.1 p.2) = fun p => (g p.2 - g p.1) -
      ((∫ u in (0 : ℝ)..p.2, (NormedSpace.exp ((-(p.2 - u)) • lcQ Q)) (lcQ Q (g u - g p.1))) -
      ∫ u in (0 : ℝ)..p.1, (NormedSpace.exp ((-(p.2 - u)) • lcQ Q)) (lcQ Q (g u - g p.1))) := by
    funext p; unfold lcU; rw [hsplit p]
  rw [this]
  exact ((hg.comp continuous_snd).sub (hg.comp continuous_fst)).sub (h0.sub h1)

/-- The integral equation `U_v = (g v - g r) - Q ∫_r^v U_s ds` (every real `v`). -/
theorem lcU_integral (hg : Continuous g) (r v : ℝ) :
    lcU Q g r v = (g v - g r) - lcQ Q (∫ s in r..v, lcU Q g r s) := by
  set Φ : ℝ → Euc d := fun v => NormedSpace.exp ((-v) • lcQ Q)
      (∫ u in r..v, NormedSpace.exp (u • lcQ Q) (lcQ Q (g u - g r))) with hΦ
  have hU : ∀ s, lcU Q g r s = (g s - g r) - Φ s := fun s => lcU_eq Q hg r s
  have hd : ∀ s, HasDerivAt Φ (-(lcQ Q (Φ s)) + lcQ Q (g s - g r)) s :=
    fun s => lc1_hasDerivAt_phi Q hg r s
  have hΦc : Continuous Φ := continuous_iff_continuousAt.2 fun s => (hd s).continuousAt
  have hG : Continuous fun s => g s - g r := hg.sub continuous_const
  have hi1 : IntervalIntegrable (fun s => -(lcQ Q (Φ s)) + lcQ Q (g s - g r)) volume r v :=
    (((lcQ Q).continuous.comp hΦc).neg.add ((lcQ Q).continuous.comp hG)).intervalIntegrable _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hi1
  have hΦr : Φ r = 0 := by simp [hΦ]
  rw [hΦr, sub_zero] at hftc
  have hi2 : IntervalIntegrable (fun s => lcQ Q (Φ s)) volume r v :=
    ((lcQ Q).continuous.comp hΦc).intervalIntegrable _ _
  have hi3 : IntervalIntegrable (fun s => lcQ Q (g s - g r)) volume r v :=
    ((lcQ Q).continuous.comp hG).intervalIntegrable _ _
  have hi2' : IntervalIntegrable (fun s => -(lcQ Q (Φ s))) volume r v := hi2.neg
  rw [intervalIntegral.integral_add hi2' hi3, intervalIntegral.integral_neg,
    ContinuousLinearMap.intervalIntegral_comp_comm _ (hΦc.intervalIntegrable r v),
    ContinuousLinearMap.intervalIntegral_comp_comm _ (hG.intervalIntegrable r v)] at hftc
  have hint : ∫ s in r..v, lcU Q g r s = (∫ s in r..v, (g s - g r)) - ∫ s in r..v, Φ s := by
    rw [← intervalIntegral.integral_sub (hG.intervalIntegrable r v) (hΦc.intervalIntegrable r v)]
    exact intervalIntegral.integral_congr fun s _ => hU s
  rw [hint, map_sub, hU v, ← hftc]
  abel

end U


/-! ### The random ODE and the flow -/

/-- The full drift in time `τ` after the shift by `r`: `y ↦ -Q y - c_{r+τ} + B_{r+τ}(y)`. -/
def lcB (Q : Matrix (Fin d) (Fin d) ℝ) (c : ℝ → Euc d) (B : ℝ → Euc d → Euc d) (r τ : ℝ)
    (y : Euc d) : Euc d :=
  -(lcQ Q y) - c (r + τ) + B (r + τ) y

theorem lcDrift_eq (Q : Matrix (Fin d) (Fin d) ℝ) (c : ℝ → Euc d) (B : ℝ → Euc d → Euc d)
    (g : ℝ → Euc d) (r τ : ℝ) (z : Euc d) :
    lcDrift Q c B g r τ z = lcB Q c B r τ (z + lcU Q g r (r + τ)) + lcQ Q (lcU Q g r (r + τ)) := by
  unfold lcDrift lcB
  simp only [map_add]
  abel

section Flow

variable {Q : Matrix (Fin d) (Fin d) ℝ} {k : ℕ} {Λc ΛB : ℝ} {c : ℝ → Euc d}
  {B : ℝ → Euc d → Euc d} {g : ℝ → Euc d}

theorem lc1_B_lip (H : LcHyp Q k Λc ΛB c B) {v : ℝ} (hv : 0 ≤ v) (x y : Euc d) :
    ‖B v x - B v y‖ ≤ ΛB * ‖x - y‖ := by
  have hd : Differentiable ℝ (B v) :=
    (H.B_smooth v hv).differentiable (by exact_mod_cast Nat.succ_ne_zero k)
  exact (convex_univ (𝕜 := ℝ) (E := Euc d)).norm_image_sub_le_of_norm_fderiv_le
    (f := B v) (C := ΛB) (fun x _ => hd x)
    (fun x _ => by
      rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]; exact H.B_bd v hv 1 (by omega) x)
    (mem_univ y) (mem_univ x)

theorem lcB_continuous (H : LcHyp Q k Λc ΛB c B) {r : ℝ} (hr : 0 ≤ r) {z : ℝ → Euc d} {S : Set ℝ}
    (hS : ∀ τ ∈ S, 0 ≤ τ) (hz : ContinuousOn z S) :
    ContinuousOn (fun τ => lcB Q c B r τ (z τ)) S := by
  unfold lcB
  have hmap : ∀ τ ∈ S, (r + τ, z τ) ∈ Ici (0 : ℝ) ×ˢ (univ : Set (Euc d)) :=
    fun τ hτ => ⟨by simpa using add_nonneg hr (hS τ hτ), mem_univ _⟩
  have h1 : ContinuousOn (fun τ => c (r + τ)) S :=
    H.c_cont.comp (continuousOn_const.add continuousOn_id) (fun τ hτ => by
      simpa using add_nonneg hr (hS τ hτ))
  have h2 : ContinuousOn (fun τ => B (r + τ) (z τ)) S :=
    H.B_cont.comp ((continuousOn_const.add continuousOn_id).prodMk hz) hmap
  exact (((lcQ Q).continuous.comp_continuousOn hz).neg.sub h1).add h2

theorem lcDrift_continuousOn (H : LcHyp Q k Λc ΛB c B) (hg : Continuous g) {r : ℝ} (hr : 0 ≤ r) :
    ContinuousOn (fun p : ℝ × Euc d => lcDrift Q c B g r p.1 p.2) (Ici 0 ×ˢ univ) := by
  have hU : Continuous fun p : ℝ × Euc d => lcU Q g r (r + p.1) :=
    (lcU_continuous Q hg).comp (continuous_const.prodMk (continuous_const.add continuous_fst))
  have : (fun p : ℝ × Euc d => lcDrift Q c B g r p.1 p.2) =
      fun p => lcB Q c B r p.1 (p.2 + lcU Q g r (r + p.1)) + lcQ Q (lcU Q g r (r + p.1)) := by
    funext p; exact lcDrift_eq Q c B g r p.1 p.2
  rw [this]
  have hS : ∀ p ∈ (Ici 0 ×ˢ univ : Set (ℝ × Euc d)), 0 ≤ p.1 := fun p hp => hp.1
  have h1 : ContinuousOn (fun p : ℝ × Euc d => lcB Q c B r (p.1) (p.2 + lcU Q g r (r + p.1)))
      (Ici 0 ×ˢ univ) := by
    unfold lcB
    have hmap : ∀ p ∈ (Ici 0 ×ˢ univ : Set (ℝ × Euc d)),
        (r + p.1, p.2 + lcU Q g r (r + p.1)) ∈ Ici (0 : ℝ) ×ˢ (univ : Set (Euc d)) :=
      fun p hp => ⟨by simpa using add_nonneg hr (hS p hp), mem_univ _⟩
    have h1 : ContinuousOn (fun p : ℝ × Euc d => c (r + p.1)) (Ici 0 ×ˢ univ) :=
      H.c_cont.comp (continuousOn_const.add continuousOn_fst) (fun p hp => by
        simpa using add_nonneg hr (hS p hp))
    have h2 : ContinuousOn (fun p : ℝ × Euc d => B (r + p.1) (p.2 + lcU Q g r (r + p.1)))
        (Ici 0 ×ˢ univ) :=
      H.B_cont.comp ((continuousOn_const.add continuousOn_fst).prodMk
        (continuousOn_snd.add hU.continuousOn)) hmap
    exact (((lcQ Q).continuous.comp_continuousOn
      (continuousOn_snd.add hU.continuousOn)).neg.sub h1).add h2
  exact h1.add (((lcQ Q).continuous.comp hU).continuousOn)

theorem lcDrift_isLipschitz (H : LcHyp Q k Λc ΛB c B) (hg : Continuous g) {r : ℝ} (hr : 0 ≤ r) :
    IsLipschitzDrift (lcDrift Q c B g r) where
  cont := lcDrift_continuousOn H hg hr
  lip T := ⟨(‖lcQ Q‖ + ΛB).toNNReal, fun t ht => LipschitzWith.of_dist_le_mul fun z z' => by
    have hΛ : 0 ≤ ‖lcQ Q‖ + ΛB := by have := H.ΛB_nonneg; positivity
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hΛ]
    have e : lcDrift Q c B g r t z - lcDrift Q c B g r t z' =
        -(lcQ Q (z - z')) + (B (r + t) (z + lcU Q g r (r + t)) -
          B (r + t) (z' + lcU Q g r (r + t))) := by
      unfold lcDrift; simp only [map_sub]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖-(lcQ Q (z - z'))‖ ≤ ‖lcQ Q‖ * ‖z - z'‖ := by
      rw [norm_neg]; exact (lcQ Q).le_opNorm _
    have h2 := lc1_B_lip H (by simpa using add_nonneg hr ht.1) (z + lcU Q g r (r + t))
      (z' + lcU Q g r (r + t))
    rw [add_sub_add_right_eq_sub] at h2
    nlinarith⟩

end Flow

/-! ### Generic facts on `lcZ` -/

section Z

variable {D : ℝ → Euc d → Euc d}

theorem lcZ_exists (hD : IsLipschitzDrift D) (x : Euc d) :
    ∃ y : ℝ → Euc d, IsPathSolution D (lcSigma d) (0 : ℝ≥0 → Fin d → ℝ) x ⊤ y :=
  exists_ode_additive_global _ hD (lcSigma d) 0 continuous_const rfl x

theorem lcZ_spec (hD : IsLipschitzDrift D) (x : Euc d) :
    IsPathSolution D (lcSigma d) (0 : ℝ≥0 → Fin d → ℝ) x ⊤ (lcZ D x) := by
  unfold lcZ
  rw [dif_pos (lcZ_exists hD x)]
  exact (lcZ_exists hD x).choose_spec

theorem lcZ_zero (hD : IsLipschitzDrift D) (x : Euc d) : lcZ D x 0 = x := (lcZ_spec hD x).1

theorem lcZ_cont (hD : IsLipschitzDrift D) (x : Euc d) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousOn (lcZ D x) (Icc 0 t) :=
  ((lcZ_spec hD x).2 t ht (WithTop.coe_lt_top t)).1

theorem lcZ_eq (hD : IsLipschitzDrift D) (x : Euc d) {t : ℝ} (ht : 0 ≤ t) :
    lcZ D x t = x + ∫ s in Icc 0 t, D s (lcZ D x s) := by
  have := ((lcZ_spec hD x).2 t ht (WithTop.coe_lt_top t)).2.2
  simpa using this

theorem lcZ_drift_continuousOn (hD : IsLipschitzDrift D) (x : Euc d) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousOn (fun s => D s (lcZ D x s)) (Icc 0 t) := by
  have h1 : ContinuousOn (fun s => (s, lcZ D x s)) (Icc 0 t) :=
    continuousOn_id.prodMk (lcZ_cont hD x ht)
  exact hD.cont.comp h1 (fun s hs => ⟨hs.1, mem_univ _⟩)

theorem lcZ_isNegDriftFlow (hD : IsLipschitzDrift D) {T : ℝ} (hT : 0 ≤ T) :
    IsNegDriftFlow T (fun τ z => -D τ z) (fun τ x => lcZ D x τ) where
  init x := lcZ_zero hD x
  eqn x τ hτ := by
    have := HRS.MS.PoisFlow.pf_hasDerivWithinAt_of_integral (lcZ_drift_continuousOn hD x hT)
      (fun t ht => lcZ_eq hD x ht.1) τ hτ
    simpa using this

end Z


/-! ### `lcFlow` is a pathwise solution -/

section PathSol

variable {Q : Matrix (Fin d) (Fin d) ℝ} {k : ℕ} {Λc ΛB : ℝ} {c : ℝ → Euc d}
  {B : ℝ → Euc d → Euc d} {g : ℝ → Euc d}

theorem lcFlow_add (Q : Matrix (Fin d) (Fin d) ℝ) (c : ℝ → Euc d) (B : ℝ → Euc d → Euc d)
    (g : ℝ → Euc d) (r τ : ℝ) (x : Euc d) :
    lcFlow Q c B g r (r + τ) x = lcZ (lcDrift Q c B g r) x τ + lcU Q g r (r + τ) := by
  simp [lcFlow]

theorem lc1_noise_sum (g : ℝ → Euc d) (r : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ∑ k, lcW g r t.toNNReal k • lcSigma d k = g (r + t) - g r := by
  ext i
  simp [lcW, lcSigma, Real.coe_toNNReal t ht, Pi.single_apply]

theorem lcFlow_isPathSolution (H : LcHyp Q k Λc ΛB c B) (hg : Continuous g) {r : ℝ} (hr : 0 ≤ r)
    (x : Euc d) :
    IsPathSolution (lcB Q c B r) (lcSigma d) (lcW g r) x ⊤
      (fun τ => lcFlow Q c B g r (r + τ) x) := by
  have hD := lcDrift_isLipschitz H hg hr
  have hUc : Continuous fun τ : ℝ => lcU Q g r (r + τ) :=
    (lcU_continuous_v Q hg r).comp (continuous_const.add continuous_id)
  refine ⟨by simp [lcFlow, lcZ_zero hD, lcU_self], fun t ht _ => ?_⟩
  have hX : ContinuousOn (fun τ => lcFlow Q c B g r (r + τ) x) (Icc 0 t) := by
    have : (fun τ => lcFlow Q c B g r (r + τ) x) =
        fun τ => lcZ (lcDrift Q c B g r) x τ + lcU Q g r (r + τ) :=
      funext fun τ => lcFlow_add Q c B g r τ x
    rw [this]; exact (lcZ_cont hD x ht).add hUc.continuousOn
  have hF : ContinuousOn (fun τ => lcB Q c B r τ (lcFlow Q c B g r (r + τ) x)) (Icc 0 t) :=
    lcB_continuous H hr (fun τ hτ => hτ.1) hX
  refine ⟨hX, hF.integrableOn_Icc, ?_⟩
  have hDc := lcZ_drift_continuousOn hD x ht
  have hQU : ContinuousOn (fun s => lcQ Q (lcU Q g r (r + s))) (Icc 0 t) :=
    ((lcQ Q).continuous.comp hUc).continuousOn
  have hsplit : ∀ s, lcB Q c B r s (lcFlow Q c B g r (r + s) x) =
      lcDrift Q c B g r s (lcZ (lcDrift Q c B g r) x s) - lcQ Q (lcU Q g r (r + s)) := by
    intro s
    rw [lcFlow_add, lcDrift_eq]; abel
  have hI : ∫ s in Icc 0 t, lcB Q c B r s (lcFlow Q c B g r (r + s) x) =
      (∫ s in Icc 0 t, lcDrift Q c B g r s (lcZ (lcDrift Q c B g r) x s)) -
        lcQ Q (∫ s in r..(r + t), lcU Q g r s) := by
    simp_rw [hsplit]
    rw [integral_sub hDc.integrableOn_Icc hQU.integrableOn_Icc,
      setIntegral_Icc_eq_interval (f := fun s => lcQ Q (lcU Q g r (r + s))) ht,
      ContinuousLinearMap.intervalIntegral_comp_comm _ ((hUc.intervalIntegrable 0 t)),
      intervalIntegral.integral_comp_add_left (fun s => lcU Q g r s) r]
    simp
  beta_reduce
  rw [hI, lc1_noise_sum g r ht, lcFlow_add, lcZ_eq hD x ht, lcU_integral Q hg r (r + t)]
  abel

end PathSol

end HRS.MS.Lc
