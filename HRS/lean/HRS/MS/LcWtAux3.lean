import HRS.MS.LcWtAux1
import HRS.MS.LcWtAux2

/-!
# LC-2, part 3: operator norms from partial derivatives, and weighted bounds along the trajectory

* `lc2_ml_bound`, `lc2_op_bound`, `lc2_decay_op`: the weighted norm hypothesis
  `decayNormVecE (k+1) σ (B v) ≤ ofReal ΛB` (all partial derivatives of all components, weight
  `⟨x⟩^{σ+j}`) gives the operator-norm bound `⟨x⟩^{σ+j} ‖D^j B_v(x)‖ ≤ d^{j+1} ΛB`, `j ≤ k+1`.
* `lc2_iter_negDrift`: for `k ≥ 2` the `k`-th derivative of the drift of the random ODE is
  `-D^k B_v(· + U_v)`.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

noncomputable section

namespace HRS.MS.Lc

variable {d : ℕ}

/-! ### Operator norm from partial derivatives -/

theorem lc2_decomp (w : Euc d) : w = ∑ i, w i • EuclideanSpace.single i (1 : ℝ) := by
  ext j
  simp [Pi.single_apply]

theorem lc2_norm_le_sum (w : Euc d) : ‖w‖ ≤ ∑ i, |w i| := by
  conv_lhs => rw [lc2_decomp w]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_smul, Real.norm_eq_abs]
  simp

theorem lc2_ml_bound {j : ℕ} (M : (Euc d) [×j]→L[ℝ] ℝ) {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ idx : Fin j → Fin d, |M (fun l => EuclideanSpace.single (idx l) 1)| ≤ a) :
    ‖M‖ ≤ (d : ℝ) ^ j * a := by
  classical
  refine M.opNorm_le_bound (by positivity) fun v => ?_
  have hv : v = fun l => ∑ i, v l i • EuclideanSpace.single i (1 : ℝ) := funext fun l => lc2_decomp (v l)
  have hMv : M v = ∑ idx : Fin j → Fin d, (∏ l, v l (idx l)) *
      M (fun l => EuclideanSpace.single (idx l) 1) := by
    have h1 : M v = M (fun l => ∑ i, v l i • EuclideanSpace.single i (1 : ℝ)) :=
      congrArg M hv
    rw [h1]
    rw [show M (fun l => ∑ i, v l i • EuclideanSpace.single i (1 : ℝ)) =
        ∑ idx : Fin j → Fin d, M (fun l => v l (idx l) • EuclideanSpace.single (idx l) (1 : ℝ)) from
      M.toMultilinearMap.map_sum (fun l i => v l i • EuclideanSpace.single i (1 : ℝ))]
    refine Finset.sum_congr rfl fun idx _ => ?_
    exact M.toMultilinearMap.map_smul_univ (fun l => v l (idx l))
      (fun l => EuclideanSpace.single (idx l) (1 : ℝ))
  rw [hMv]
  have hP : 0 ≤ ∏ l, ‖v l‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ idx : Fin j → Fin d,
      |(∏ l, v l (idx l)) * M (fun l => EuclideanSpace.single (idx l) 1)| ≤ (∏ l, ‖v l‖) * a := by
    intro idx
    rw [abs_mul, Finset.abs_prod]
    refine mul_le_mul (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun l _ => ?_) (h idx)
      (abs_nonneg _) hP
    have := PiLp.norm_apply_le (v l) (idx l)
    simpa using this
  calc ∑ idx : Fin j → Fin d, |(∏ l, v l (idx l)) * M (fun l => EuclideanSpace.single (idx l) 1)|
      ≤ ∑ _idx : Fin j → Fin d, (∏ l, ‖v l‖) * a := Finset.sum_le_sum fun idx _ => hterm idx
    _ = (d : ℝ) ^ j * a * ∏ l, ‖v l‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

theorem lc2_op_bound {j : ℕ} (M : (Euc d) [×j]→L[ℝ] (Euc d)) {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ (i : Fin d) (idx : Fin j → Fin d),
      |M (fun l => EuclideanSpace.single (idx l) 1) i| ≤ a) :
    ‖M‖ ≤ (d : ℝ) ^ (j + 1) * a := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  refine M.opNorm_le_bound (by positivity) fun v => ?_
  have hcomp : ∀ i : Fin d, ‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).compContinuousMultilinearMap M‖
      ≤ (d : ℝ) ^ j * a := fun i =>
    lc2_ml_bound _ ha fun idx => by simpa using h i idx
  have hP : 0 ≤ ∏ l, ‖v l‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  refine (lc2_norm_le_sum (M v)).trans ?_
  calc ∑ i, |M v i| ≤ ∑ _i : Fin d, ((d : ℝ) ^ j * a) * ∏ l, ‖v l‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).compContinuousMultilinearMap M).le_opNorm v
        simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
          Real.norm_eq_abs] at this
        exact this.trans (mul_le_mul_of_nonneg_right (hcomp i) hP)
    _ = (d : ℝ) ^ (j + 1) * a * ∏ l, ‖v l‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- From the weighted norm `decayNormVecE m σ f ≤ ofReal Λ'` to operator-norm bounds. -/
theorem lc2_decay_op {m : ℕ} {σ Λ' : ℝ} {f : Euc d → Euc d} (hΛ' : 0 ≤ Λ')
    (hf : ContDiff ℝ (m : WithTop ℕ∞) f) (h : decayNormVecE m σ f ≤ ENNReal.ofReal Λ')
    (j : ℕ) (hj : j ≤ m) (x : Euc d) :
    jbracket x ^ (σ + (j : ℝ)) * ‖iteratedFDeriv ℝ j f x‖ ≤ (d : ℝ) ^ (j + 1) * Λ' := by
  have hw : 0 < jbracket x ^ (σ + (j : ℝ)) := Real.rpow_pos_of_pos (lc2_jb_pos x) _
  set w := jbracket x ^ (σ + (j : ℝ)) with hwdef
  have hcomp : ∀ (i : Fin d) (idx : Fin j → Fin d),
      |iteratedFDeriv ℝ j f x (fun l => EuclideanSpace.single (idx l) 1) i| ≤ Λ' / w := by
    intro i idx
    have e1 : (fun y => f y i) = (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) ∘ f := rfl
    have e2 : partialDeriv idx (fun y => f y i) x =
        iteratedFDeriv ℝ j f x (fun l => EuclideanSpace.single (idx l) 1) i := by
      unfold partialDeriv
      rw [e1, ContinuousLinearMap.iteratedFDeriv_comp_left _ (hf.contDiffAt)
        (by exact_mod_cast hj)]
      rfl
    rw [← e2, le_div_iff₀ hw, mul_comm]
    have hle : ENNReal.ofReal (w * |partialDeriv idx (fun y => f y i) x|) ≤ ENNReal.ofReal Λ' := by
      refine le_trans ?_ h
      refine le_trans ?_ (le_iSup _ i)
      unfold decayNormE derivSupE
      refine le_trans ?_ (le_iSup _ ⟨j, by omega⟩)
      refine le_trans ?_ (le_iSup _ idx)
      refine le_trans ?_ (le_iSup _ x)
      exact le_rfl
    exact (ENNReal.ofReal_le_ofReal_iff hΛ').1 hle
  have hM := lc2_op_bound (iteratedFDeriv ℝ j f x) (div_nonneg hΛ' hw.le) hcomp
  calc w * ‖iteratedFDeriv ℝ j f x‖ ≤ w * ((d : ℝ) ^ (j + 1) * (Λ' / w)) :=
        mul_le_mul_of_nonneg_left hM hw.le
    _ = (d : ℝ) ^ (j + 1) * Λ' := by field_simp

/-! ### The derivatives of the drift of the random ODE -/

section Drift

variable {Q : Matrix (Fin d) (Fin d) ℝ} {k : ℕ} {Λc ΛB : ℝ} {c : ℝ → Euc d}
  {B : ℝ → Euc d → Euc d} {g : ℝ → Euc d}

/-- For `kk ≥ 2` the `kk`-th derivative of `z ↦ -lcDrift .. s z` is `-D^kk B_{r+s}(z + U_{r+s})`. -/
theorem lc2_iter_negDrift (H : LcHyp Q k Λc ΛB c B) {r s : ℝ} (hrs : 0 ≤ r + s) {kk : ℕ}
    (hk2 : 2 ≤ kk) (hkk : kk ≤ k + 1) (z : Euc d) :
    ‖iteratedFDeriv ℝ kk (fun z => -lcDrift Q c B g r s z) z‖ =
      ‖iteratedFDeriv ℝ kk (B (r + s)) (z + lcU Q g r (r + s))‖ := by
  have hshift : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞)
      (fun z : Euc d => B (r + s) (z + lcU Q g r (r + s))) :=
    (H.B_smooth _ hrs).comp (contDiff_id.add contDiff_const)
  have hsub : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞)
      (fun z : Euc d => lcQ Q z - B (r + s) (z + lcU Q g r (r + s))) :=
    (lcQ Q).contDiff.sub hshift
  have e : (fun z : Euc d => -lcDrift Q c B g r s z) =
      fun z => (lcQ Q z - B (r + s) (z + lcU Q g r (r + s))) + c (r + s) := by
    funext z; exact lc2_negDrift_eq Q c B g r s z
  rw [e, HRS.MS.PoisFlow.pf_iter_add_const _ hsub (by omega) hkk z]
  have hBj : ContDiffAt ℝ (kk : WithTop ℕ∞) (fun z : Euc d => B (r + s) (z + lcU Q g r (r + s))) z :=
    (hshift.of_le (by exact_mod_cast hkk)).contDiffAt
  have hLj : ContDiffAt ℝ (kk : WithTop ℕ∞) (fun z : Euc d => lcQ Q z) z :=
    (lcQ Q).contDiff.contDiffAt.of_le (by exact_mod_cast le_top)
  have e0 : (fun z : Euc d => lcQ Q z - B (r + s) (z + lcU Q g r (r + s))) =
      (fun z : Euc d => lcQ Q z) - fun z => B (r + s) (z + lcU Q g r (r + s)) := rfl
  rw [e0, iteratedFDeriv_sub_apply hLj hBj, iteratedFDeriv_comp_add_right,
    HRS.MS.PoisFlow.pf_iter_clm_zero (lcQ Q) hk2, zero_sub, norm_neg]

end Drift

/-! ### Weighted bounds along the trajectory and the higher derivatives of the flow -/

section Traj

variable {Q : Matrix (Fin d) (Fin d) ℝ} {k : ℕ} {Λc ΛB : ℝ} {c : ℝ → Euc d}
  {B : ℝ → Euc d → Euc d} {g : ℝ → Euc d}

/-- Pointwise bound of `D^kk` of the drift along the trajectory `Y_{s'}(x)`, `2 ≤ kk ≤ k+1`:
`‖D^kk (-lcDrift)(Y_{s'})‖ ⟨x⟩^{σ+kk} ≤ (d+1)^{k+2} ΛB (A (1+κ))^{σ+kk}`, `A = 2 e^{ΛT}`. -/
theorem lc2_traj_bound (H : LcHyp Q k Λc ΛB c B) (hg : Continuous g) {σ : ℝ} (hσ : 0 ≤ σ)
    (hdec : ∀ v, 0 ≤ v → decayNormVecE (k + 1) σ (B v) ≤ ENNReal.ofReal ΛB)
    {r v T κ : ℝ} (hr : 0 ≤ r) (hrv : r ≤ v) (hvT : v - r ≤ T)
    (hκ : ∀ u ∈ Icc r v, ‖lcU Q g r u‖ ≤ κ) {s' : ℝ} (hs' : s' ∈ Icc 0 (v - r)) (x : Euc d)
    {kk : ℕ} (hk2 : 2 ≤ kk) (hkk : kk ≤ k + 1) :
    ‖iteratedFDeriv ℝ kk (fun z => -lcDrift Q c B g r s' z) (lcZ (lcDrift Q c B g r) x s')‖ *
        jbracket x ^ (σ + (kk : ℝ)) ≤
      ((d : ℝ) + 1) ^ (k + 2) * ΛB *
        ((2 * Real.exp (lcLam Q Λc ΛB * T)) * (1 + κ)) ^ (σ + (kk : ℝ)) := by
  have hv'0 : 0 ≤ r + s' := add_nonneg hr hs'.1
  have hrv' : r ≤ r + s' := by linarith [hs'.1]
  have hκ' : ∀ u ∈ Icc r (r + s'), ‖lcU Q g r u‖ ≤ κ := fun u hu =>
    hκ u ⟨hu.1, hu.2.trans (by linarith [hs'.2])⟩
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ v ⟨hrv, le_rfl⟩)
  have hcomp := (lc2_jb_comp H hg hr hrv' (T := T) (by linarith [hs'.2]) hκ' x).2
  set X' := lcFlow Q c B g r (r + s') x with hX'
  have hX'e : X' = lcZ (lcDrift Q c B g r) x s' + lcU Q g r (r + s') := by
    rw [hX', lc2_flow_eq, add_sub_cancel_left]
  have hiter := lc2_iter_negDrift (g := g) H hv'0 hk2 hkk (lcZ (lcDrift Q c B g r) x s')
  rw [← hX'e] at hiter
  have hΛB := H.ΛB_nonneg
  have hop := lc2_decay_op hΛB (H.B_smooth _ hv'0) (hdec _ hv'0) kk hkk X'
  set e : ℝ := σ + (kk : ℝ) with he
  have he0 : 0 ≤ e := by positivity
  set A : ℝ := (2 * Real.exp (lcLam Q Λc ΛB * T)) * (1 + κ) with hA
  have hA0 : 0 ≤ A := by positivity
  have h1 : jbracket x ^ e ≤ A ^ e * jbracket X' ^ e := by
    rw [← Real.mul_rpow hA0 (lc2_jb_pos X').le]
    exact Real.rpow_le_rpow (lc2_jb_pos x).le hcomp he0
  have hd : (d : ℝ) ^ (kk + 1) ≤ ((d : ℝ) + 1) ^ (k + 2) := by
    have h0 : (d : ℝ) ≤ (d : ℝ) + 1 := by linarith
    calc (d : ℝ) ^ (kk + 1) ≤ ((d : ℝ) + 1) ^ (kk + 1) :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) h0 _
      _ ≤ ((d : ℝ) + 1) ^ (k + 2) :=
          pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]) (by omega)
  rw [hiter]
  set D := ‖iteratedFDeriv ℝ kk (B (r + s')) X'‖ with hDdef
  have hD0 : 0 ≤ D := norm_nonneg _
  calc D * jbracket x ^ e ≤ D * (A ^ e * jbracket X' ^ e) := by gcongr
    _ = A ^ e * (jbracket X' ^ e * D) := by ring
    _ ≤ A ^ e * ((d : ℝ) ^ (kk + 1) * ΛB) := by gcongr
    _ ≤ A ^ e * (((d : ℝ) + 1) ^ (k + 2) * ΛB) := by gcongr
    _ = ((d : ℝ) + 1) ^ (k + 2) * ΛB * A ^ e := by ring

/-- Evaluation at `τ` of the path parametrisation does not increase the norm of the derivatives. -/
theorem lc2_transfer {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ξ : E → (ℝ →ᵇ E)}
    {m : ℕ} (hΞ : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) Ξ) {Ψ : ℝ → E → E} {τ : ℝ}
    (hΞΨ : ∀ y, Ξ y τ = Ψ τ y) {j : ℕ} (hj : j ≤ m + 1) (x : E) :
    ‖iteratedFDeriv ℝ j (Ψ τ) x‖ ≤ ‖iteratedFDeriv ℝ j Ξ x‖ := by
  have hfun : Ψ τ = (BoundedContinuousFunction.evalCLM (β := E) ℝ τ) ∘ Ξ :=
    funext fun y => (hΞΨ y).symm
  have hjn : (j : WithTop ℕ∞) ≤ ((m + 1 : ℕ) : WithTop ℕ∞) := by exact_mod_cast hj
  have hL : ‖BoundedContinuousFunction.evalCLM (β := E) ℝ τ‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun γ => by
      simpa using γ.norm_coe_le_norm τ
  rw [hfun]
  refine (ContinuousLinearMap.norm_iteratedFDeriv_comp_left _ (hΞ.contDiffAt) hjn).trans ?_
  calc _ ≤ 1 * ‖iteratedFDeriv ℝ j Ξ x‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ j Ξ x‖ := one_mul _

end Traj

section Main

variable {Q : Matrix (Fin d) (Fin d) ℝ}

/-- **Statement (ii) of `lc_weights`** (all derivative orders `2 ≤ j ≤ k+1`). -/
theorem lc2_weights_deriv (Q : Matrix (Fin d) (Fin d) ℝ) (k : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (T Λc ΛB : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ N : ℕ, ∀ (c : ℝ → Euc d) (B : ℝ → Euc d → Euc d),
      LcHyp Q k Λc ΛB c B →
      (∀ v, 0 ≤ v → decayNormVecE (k + 1) (s + 1) (B v) ≤ ENNReal.ofReal ΛB) →
      ∀ g : ℝ → Euc d, Continuous g → ∀ r v κ : ℝ, 0 ≤ r → r ≤ v → v ≤ T →
      (∀ u ∈ Icc r v, ‖lcU Q g r u‖ ≤ κ) →
      ∀ j : ℕ, 2 ≤ j → j ≤ k + 1 → ∀ x : Euc d,
        jbracket x ^ (s + 1 + (j : ℝ)) * ‖iteratedFDeriv ℝ j (lcFlow Q c B g r v) x‖ ≤
          C * (1 + κ) ^ N := by
  classical
  set Λ0 := lcLam Q Λc ΛB with hΛ0
  set σ : ℝ := s + 1 with hσdef
  have hσ : 0 ≤ σ := by linarith
  obtain ⟨C0, hC01, P, hP⟩ := lc2_induction (E := Euc d) k T Λ0 (k + 1) le_rfl
  set M : ℕ := ⌈σ⌉₊ + (k + 1) with hM
  set A : ℝ := 2 * Real.exp (Λ0 * T) with hA
  set Cdec : ℝ := ((d : ℝ) + 1) ^ (k + 2) * ΛB with hCdec
  set K0 : ℝ := 1 + |T| * |Cdec| * A ^ M with hK0
  have hAp : 0 < A := by positivity
  have hK01 : 1 ≤ K0 := by
    have : 0 ≤ |T| * |Cdec| * A ^ M := by positivity
    linarith
  refine ⟨C0 * K0 ^ P, one_le_mul_of_one_le_of_one_le hC01 (one_le_pow₀ hK01), M * P, ?_⟩
  intro c B H hdec g hg r v κ hr hrv hvT hκ j hj2 hjk x
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ v ⟨hrv, le_rfl⟩)
  have hT0 : 0 ≤ T := hr.trans (hrv.trans hvT)
  have hΛ0nn : 0 ≤ Λ0 := H.lam_nonneg
  have hΛB := H.ΛB_nonneg
  have hA1 : 1 ≤ A := by
    have : 1 ≤ Real.exp (Λ0 * T) := Real.one_le_exp (mul_nonneg hΛ0nn hT0)
    rw [hA]; linarith
  have hS : 0 ≤ v - r := sub_nonneg.2 hrv
  have hST : v - r ≤ T := by linarith
  have hCdec0 : 0 ≤ Cdec := by rw [hCdec]; positivity
  -- the parametrisation of the flow
  have hdb := lcDrift_isDriftBounds H hg hr (v - r)
  have hb : FlowB.DB (v - r) k Λ0 (fun τ z => -lcDrift Q c B g r τ z) := FlowB.db_of_drift hdb
  have hflow := lc2_isNegDriftFlow H hg hr hS
  obtain ⟨Ξ, hΞ, hG, hΞΨ⟩ := FlowC.fc_exists_param hS hb hflow.init
    (fun y => FlowA.sol_of_flow hflow y)
  set κ1 : ℝ := 1 + κ with hκ1
  have hκ11 : 1 ≤ κ1 := by linarith
  have hAκ : 1 ≤ A * κ1 := one_le_mul_of_one_le_of_one_le hA1 hκ11
  set Bt : ℝ := 1 + T * Cdec * (A * κ1) ^ M with hBt
  have hBt1 : 1 ≤ Bt := by
    have : 0 ≤ T * Cdec * (A * κ1) ^ M := by positivity
    linarith
  have hjb := lc2_jb_pos x
  set ω : ℝ := (jbracket x)⁻¹ with hω
  have hω0 : 0 < ω := inv_pos.2 hjb
  have hω1 : ω ≤ 1 := inv_le_one_of_one_le₀ (lc2_jb_ge_one x)
  -- trajectory bound for the Nemytskii derivatives
  have htay : ∀ kk : ℕ, 2 ≤ kk → kk ≤ k + 1 →
      ‖FlowB.tay (v - r) (fun τ z => -lcDrift Q c B g r τ z) (Ξ x) kk‖ ≤ Bt * ω ^ (σ + (kk : ℝ)) := by
    intro kk hk2 hkk
    set e : ℝ := σ + (kk : ℝ) with he
    have he0 : 0 ≤ e := by positivity
    have heM : e ≤ (M : ℝ) := by
      rw [hM, he]
      have h1 : σ ≤ (⌈σ⌉₊ : ℝ) := Nat.le_ceil σ
      have h2 : (kk : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hkk
      push_cast at h2 ⊢
      linarith
    have hAe : (A * κ1) ^ e ≤ (A * κ1) ^ M := by
      calc (A * κ1) ^ e ≤ (A * κ1) ^ (M : ℝ) := Real.rpow_le_rpow_of_exponent_le hAκ heM
        _ = (A * κ1) ^ M := Real.rpow_natCast _ _
    have hwe : 0 < jbracket x ^ e := Real.rpow_pos_of_pos hjb _
    have hωe : ω ^ e = (jbracket x ^ e)⁻¹ := Real.inv_rpow hjb.le e
    have hD : ∀ s' ∈ Icc (0 : ℝ) (v - r),
        ‖iteratedFDeriv ℝ kk ((fun τ z => -lcDrift Q c B g r τ z) s') (Ξ x s')‖ ≤
          Cdec * (A * κ1) ^ M * ω ^ e := by
      intro s' hs'
      have hxs : Ξ x s' = lcZ (lcDrift Q c B g r) x s' := hΞΨ x s' hs'
      rw [hxs]
      have := lc2_traj_bound H hg hσ hdec hr hrv hST hκ hs' x hk2 hkk
      have h3 : ‖iteratedFDeriv ℝ kk (fun z => -lcDrift Q c B g r s' z)
          (lcZ (lcDrift Q c B g r) x s')‖ ≤ Cdec * (A * κ1) ^ e * ω ^ e := by
        rw [hωe, ← div_eq_mul_inv, le_div_iff₀ hwe]
        simpa only [hCdec, hA, hκ1, mul_assoc] using this
      refine h3.trans ?_
      gcongr
    have := lc2_tay_norm hS hb (Ξ x) hkk hD
    refine this.trans ?_
    have hωe0 : 0 ≤ ω ^ e := Real.rpow_nonneg hω0.le _
    calc Cdec * (A * κ1) ^ M * ω ^ e * (v - r) ≤ Cdec * (A * κ1) ^ M * ω ^ e * T := by gcongr
      _ = (T * Cdec * (A * κ1) ^ M) * ω ^ e := by ring
      _ ≤ Bt * ω ^ e := by
          gcongr
          rw [hBt]; linarith
  have hind := hP (v - r) hS hST _ hb Ξ hΞ hG x σ ω Bt hσ hω0 hω1 hBt1 htay j (by omega) hjk
  have hj1 : j ≠ 1 := by omega
  rw [lc2_e_of_ne hj1] at hind
  -- transfer to the flow
  have hshift : lcFlow Q c B g r v = fun y => lcZ (lcDrift Q c B g r) y (v - r) + lcU Q g r v := rfl
  have hLD : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞)
      (fun y => lcZ (lcDrift Q c B g r) y (v - r)) := by
    have := FlowB.flow_contDiff hS hdb hflow (v - r) ⟨hS, le_rfl⟩
    exact this
  have hiter : iteratedFDeriv ℝ j (lcFlow Q c B g r v) x =
      iteratedFDeriv ℝ j (fun y => lcZ (lcDrift Q c B g r) y (v - r)) x := by
    rw [hshift]
    exact HRS.MS.PoisFlow.pf_iter_add_const _ hLD (by omega) hjk x
  have htr := lc2_transfer (Ψ := fun τ y => lcZ (lcDrift Q c B g r) y τ) hΞ
    (τ := v - r) (fun y => hΞΨ y (v - r) ⟨hS, le_rfl⟩) hjk x
  have hnorm : ‖iteratedFDeriv ℝ j (lcFlow Q c B g r v) x‖ ≤ C0 * Bt ^ P * ω ^ (σ + (j : ℝ)) := by
    rw [hiter]
    exact htr.trans hind
  have hwj : 0 < jbracket x ^ (σ + (j : ℝ)) := Real.rpow_pos_of_pos hjb _
  have hωj : jbracket x ^ (σ + (j : ℝ)) * ω ^ (σ + (j : ℝ)) = 1 := by
    rw [hω, Real.inv_rpow hjb.le, mul_inv_cancel₀ hwj.ne']
  have hBtK : Bt ≤ K0 * κ1 ^ M := by
    have hk1M : 1 ≤ κ1 ^ M := one_le_pow₀ hκ11
    have hTC : T * Cdec ≤ |T| * |Cdec| := by
      rw [← abs_of_nonneg (mul_nonneg hT0 hCdec0), ← abs_mul]
    have hAM : 0 ≤ A ^ M := by positivity
    have e1 : K0 * κ1 ^ M = κ1 ^ M + |T| * |Cdec| * A ^ M * κ1 ^ M := by rw [hK0]; ring
    have e2 : Bt = 1 + T * Cdec * A ^ M * κ1 ^ M := by rw [hBt, mul_pow]; ring
    rw [e1, e2]
    have : T * Cdec * A ^ M * κ1 ^ M ≤ |T| * |Cdec| * A ^ M * κ1 ^ M := by
      gcongr
    linarith
  have hBtP : Bt ^ P ≤ K0 ^ P * κ1 ^ (M * P) := by
    calc Bt ^ P ≤ (K0 * κ1 ^ M) ^ P := pow_le_pow_left₀ (by linarith) hBtK _
      _ = K0 ^ P * κ1 ^ (M * P) := by rw [mul_pow, ← pow_mul]
  calc jbracket x ^ (σ + (j : ℝ)) * ‖iteratedFDeriv ℝ j (lcFlow Q c B g r v) x‖
      ≤ jbracket x ^ (σ + (j : ℝ)) * (C0 * Bt ^ P * ω ^ (σ + (j : ℝ))) :=
        mul_le_mul_of_nonneg_left hnorm hwj.le
    _ = C0 * Bt ^ P * (jbracket x ^ (σ + (j : ℝ)) * ω ^ (σ + (j : ℝ))) := by ring
    _ = C0 * Bt ^ P := by rw [hωj, mul_one]
    _ ≤ C0 * (K0 ^ P * κ1 ^ (M * P)) := by gcongr
    _ = C0 * K0 ^ P * (1 + κ) ^ (M * P) := by rw [hκ1]; ring

end Main

end HRS.MS.Lc
