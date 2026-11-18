import HRS.MS.MovOpAux5

/-!
# MOV-C2 (3): the far part of `B` and the proof of `mov_operators_B`

Namespace `HRS.MS.MovC2`, helper prefix `movc2_`.  Depends on the MOV-C1 file `MovOpAux1` (through `MovOpAux4`).

* `movc2_conv_far`: `κ * h` for a kernel with `‖D^kκ(z)‖(1+‖z‖) ≤ K` is smooth with `‖D^k(κ*h)(x)‖(1+‖x‖) ≤ K ∫(1+‖y‖)|h|`
  (derivatives fall on the kernel, by induction on the order with the target space `E ↦ (ℝ^d →L E)`).
* `movc2_Phi` (`Φ_i = (∂_i g_far) * h`), `movc2_Phi_bound`, `movc2_Phi_Q`, `movc2_thetaFar_Q`: the far force and the far
  source `θ_far = ∑ ∂_iΦ_i + ∑ (-q'/2) x_iΦ_i + ∑ (1/2) B_iΦ_i` are `C_b^N` multipliers with norms `≲ ‖w‖_{Σ^m}`.
* `movc2_hF`, `movc2_hG`, `movc2_B_decomp`: `B = L + Fa` pointwise (integration by parts `movb2_ibp` for the far Laplacian).
* `movc2_far`: `B3` (`mo_mult_cb`) gives the far part in `Σ^{m-1} ⊂ Σ^{m-a}`.
* `mov_operators_B_proof`: **the frozen statement** `HRS.Whole.mov_operators_B` (tie checked by `type_of%`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovC2

open HRS.Whole HRS.MS.MovOsc HRS.MS.Mov0 HRS.MS.MovForce HRS.MS.MovC1 HRS.PDE.ToolboxRd
  HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

/-! ### Convolution with a kernel with decaying derivatives -/

lemma movc2_far_pt {E : Type} [NormedAddCommGroup E] {κ : Euc d → E} {K : ℝ}
    (hκ : ∀ z, ‖κ z‖ * (1 + ‖z‖) ≤ K) (x y : Euc d) :
    (1 + ‖x‖) * ‖κ (x - y)‖ ≤ K * (1 + ‖y‖) := by
  have h1 : 1 + ‖x‖ ≤ (1 + ‖x - y‖) * (1 + ‖y‖) := by
    have : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
      calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
    nlinarith [norm_nonneg (x - y), norm_nonneg y]
  calc (1 + ‖x‖) * ‖κ (x - y)‖ ≤ ((1 + ‖x - y‖) * (1 + ‖y‖)) * ‖κ (x - y)‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = (‖κ (x - y)‖ * (1 + ‖x - y‖)) * (1 + ‖y‖) := by ring
    _ ≤ K * (1 + ‖y‖) := mul_le_mul_of_nonneg_right (hκ _) (by positivity)

lemma movc2_far_int {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {κ : Euc d → E}
    (hκc : Continuous κ) {K : ℝ} (hκ : ∀ z, ‖κ z‖ * (1 + ‖z‖) ≤ K) {h : Euc d → ℝ}
    (hh : AEStronglyMeasurable h volume) (hI : Integrable (fun y => (1 + ‖y‖) * |h y|) volume)
    (x : Euc d) : Integrable (fun y => h y • κ (x - y)) volume ∧
      Integrable (fun y => (1 + ‖x‖) * ‖h y • κ (x - y)‖) volume := by
  have hK : 0 ≤ K := by
    have := hκ 0
    simp only [norm_zero, add_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  have hsm : AEStronglyMeasurable (fun y => h y • κ (x - y)) volume :=
    hh.smul (hκc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hbd : ∀ y, ‖h y • κ (x - y)‖ ≤ K * |h y| := fun y => by
    rw [norm_smul, Real.norm_eq_abs]
    have : ‖κ (x - y)‖ ≤ K := by
      have := hκ (x - y)
      nlinarith [norm_nonneg (κ (x - y)), norm_nonneg (x - y)]
    nlinarith [abs_nonneg (h y)]
  have hI0 : Integrable (fun y => |h y|) volume := by
    refine hI.mono' hh.norm (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_abs]
    nlinarith [abs_nonneg (h y), norm_nonneg y]
  refine ⟨(hI0.const_mul K).mono' hsm (Eventually.of_forall hbd), ?_⟩
  refine (hI.const_mul K).mono' (hsm.norm.const_mul _) (Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  rw [norm_smul, Real.norm_eq_abs]
  have := movc2_far_pt hκ x y
  calc (1 + ‖x‖) * (|h y| * ‖κ (x - y)‖) = |h y| * ((1 + ‖x‖) * ‖κ (x - y)‖) := by ring
    _ ≤ |h y| * (K * (1 + ‖y‖)) := mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = K * ((1 + ‖y‖) * |h y|) := by ring

lemma movc2_far_bound0 {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {κ : Euc d → E}
    (hκc : Continuous κ) {K : ℝ} (hκ : ∀ z, ‖κ z‖ * (1 + ‖z‖) ≤ K) {h : Euc d → ℝ}
    (hh : AEStronglyMeasurable h volume) (hI : Integrable (fun y => (1 + ‖y‖) * |h y|) volume)
    (x : Euc d) :
    ‖∫ y, h y • κ (x - y)‖ * (1 + ‖x‖) ≤ K * ∫ y, (1 + ‖y‖) * |h y| := by
  obtain ⟨hi1, hi2⟩ := movc2_far_int hκc hκ hh hI x
  have h1 : ‖∫ y, h y • κ (x - y)‖ ≤ ∫ y, ‖h y • κ (x - y)‖ := norm_integral_le_integral_norm _
  have h2 : (1 + ‖x‖) * ∫ y, ‖h y • κ (x - y)‖ ≤ K * ∫ y, (1 + ‖y‖) * |h y| := by
    rw [← integral_const_mul, ← integral_const_mul]
    refine integral_mono hi2 (hI.const_mul K) fun y => ?_
    rw [norm_smul, Real.norm_eq_abs]
    have := movc2_far_pt hκ x y
    calc (1 + ‖x‖) * (|h y| * ‖κ (x - y)‖) = |h y| * ((1 + ‖x‖) * ‖κ (x - y)‖) := by ring
      _ ≤ |h y| * (K * (1 + ‖y‖)) := mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = K * ((1 + ‖y‖) * |h y|) := by ring
  calc ‖∫ y, h y • κ (x - y)‖ * (1 + ‖x‖) ≤ (∫ y, ‖h y • κ (x - y)‖) * (1 + ‖x‖) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (1 + ‖x‖) * ∫ y, ‖h y • κ (x - y)‖ := by ring
    _ ≤ _ := h2

/-- **Smoothness and decay of `κ * h` for a kernel with decaying derivatives** (derivatives fall on the kernel). -/
theorem movc2_conv_far (n : ℕ) : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (κ : Euc d → E)
    (K : ℝ) (h : Euc d → ℝ), ContDiff ℝ (n : WithTop ℕ∞) κ →
    (∀ k ≤ n, ∀ z, ‖iteratedFDeriv ℝ k κ z‖ * (1 + ‖z‖) ≤ K) → AEStronglyMeasurable h volume →
    Integrable (fun y => (1 + ‖y‖) * |h y|) volume →
    ContDiff ℝ (n : WithTop ℕ∞) (fun x => ∫ y, h y • κ (x - y)) ∧ ∀ k ≤ n, ∀ x,
      ‖iteratedFDeriv ℝ k (fun x => ∫ y, h y • κ (x - y)) x‖ * (1 + ‖x‖) ≤
        K * ∫ y, (1 + ‖y‖) * |h y| := by
  induction n with
  | zero =>
    intro E _ _ κ K h hκ hb hh hI
    have hb0 : ∀ z, ‖κ z‖ * (1 + ‖z‖) ≤ K := fun z => by
      simpa using hb 0 le_rfl z
    have hκc : Continuous κ := by simpa using hκ.continuous
    have hK : 0 ≤ K := by
      have := hb0 0
      simp only [norm_zero, add_zero, mul_one] at this
      exact (norm_nonneg _).trans this
    have hI0 : Integrable (fun y => |h y|) volume := by
      refine hI.mono' hh.norm (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_abs]
      nlinarith [abs_nonneg (h y), norm_nonneg y]
    refine ⟨?_, fun k hk x => ?_⟩
    · have hc : Continuous (fun x => ∫ y, h y • κ (x - y)) := by
        refine continuous_of_dominated (bound := fun y => K * |h y|) (fun x => ?_) (fun x => ?_)
          (hI0.const_mul K) (Eventually.of_forall fun y => ?_)
        · exact hh.smul (hκc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
        · refine Eventually.of_forall fun y => ?_
          rw [norm_smul, Real.norm_eq_abs]
          have : ‖κ (x - y)‖ ≤ K := by
            have := hb0 (x - y)
            nlinarith [norm_nonneg (κ (x - y)), norm_nonneg (x - y)]
          nlinarith [abs_nonneg (h y)]
        · exact continuous_const.smul (hκc.comp (continuous_id.sub continuous_const))
      exact_mod_cast contDiff_zero.2 hc
    · have hk0 : k = 0 := by omega
      subst hk0
      rw [norm_iteratedFDeriv_zero]
      exact movc2_far_bound0 hκc hb0 hh hI x
  | succ n ih =>
    intro E _ _ κ K h hκ hb hh hI
    have hb0 : ∀ z, ‖κ z‖ * (1 + ‖z‖) ≤ K := fun z => by
      simpa using hb 0 (Nat.zero_le _) z
    have hκ1 : ContDiff ℝ 1 κ := hκ.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
    have hκc : Continuous κ := hκ1.continuous
    have hκd : Differentiable ℝ κ := hκ1.differentiable one_ne_zero
    have hfd : ContDiff ℝ (n : WithTop ℕ∞) (fderiv ℝ κ) := by
      have := hκ.fderiv_right (m := (n : WithTop ℕ∞)) (by push_cast; exact le_rfl)
      exact this
    have hb' : ∀ k ≤ n, ∀ z, ‖iteratedFDeriv ℝ k (fderiv ℝ κ) z‖ * (1 + ‖z‖) ≤ K := fun k hk z => by
      rw [norm_iteratedFDeriv_fderiv]
      exact hb (k + 1) (by omega) z
    have hb1 : ∀ z, ‖fderiv ℝ κ z‖ * (1 + ‖z‖) ≤ K := fun z => by
      simpa using hb' 0 (Nat.zero_le _) z
    have hfc : Continuous (fderiv ℝ κ) := by simpa using hfd.continuous
    obtain ⟨ih1, ih2⟩ := ih (Euc d →L[ℝ] E) (fderiv ℝ κ) K h hfd hb' hh hI
    have hK : 0 ≤ K := by
      have := hb0 0
      simp only [norm_zero, add_zero, mul_one] at this
      exact (norm_nonneg _).trans this
    have hI0 : Integrable (fun y => |h y|) volume := by
      refine hI.mono' hh.norm (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_abs]
      nlinarith [abs_nonneg (h y), norm_nonneg y]
    -- the derivative of the convolution
    have hD : ∀ x, HasFDerivAt (fun x => ∫ y, h y • κ (x - y)) (∫ y, h y • fderiv ℝ κ (x - y)) x := by
      intro x₀
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x y => h y • κ (x - y))
        (F' := fun x y => h y • fderiv ℝ κ (x - y)) (bound := fun y => K * |h y|) Filter.univ_mem
        (Eventually.of_forall fun x => hh.smul (hκc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
        (movc2_far_int hκc hb0 hh hI x₀).1
        (hh.smul (hfc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
        (Eventually.of_forall fun y x _ => ?_) (hI0.const_mul K) (Eventually.of_forall fun y x _ => ?_)
      · rw [norm_smul, Real.norm_eq_abs]
        have : ‖fderiv ℝ κ (x - y)‖ ≤ K := by
          have := hb1 (x - y)
          nlinarith [norm_nonneg (fderiv ℝ κ (x - y)), norm_nonneg (x - y)]
        nlinarith [abs_nonneg (h y)]
      · have h1 : HasFDerivAt (fun x : Euc d => x - y) (ContinuousLinearMap.id ℝ (Euc d)) x :=
          (hasFDerivAt_id x).sub_const y
        have h2 := ((hκd (x - y)).hasFDerivAt).comp x h1
        have h3 := h2.const_smul (h y)
        simp only [ContinuousLinearMap.comp_id] at h3
        exact h3
    have hfun : fderiv ℝ (fun x => ∫ y, h y • κ (x - y)) = fun x => ∫ y, h y • fderiv ℝ κ (x - y) :=
      funext fun x => (hD x).fderiv
    refine ⟨?_, fun k hk x => ?_⟩
    · have : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (fun x => ∫ y, h y • κ (x - y)) := by
        rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
        exact ⟨fun x => ∫ y, h y • fderiv ℝ κ (x - y), ih1, hD⟩
      exact this
    · rcases k with _ | k
      · rw [norm_iteratedFDeriv_zero]
        exact movc2_far_bound0 hκc hb0 hh hI x
      · rw [← norm_iteratedFDeriv_fderiv, hfun]
        exact ih2 k (by omega) x

/-! ### The far force `Φ_i = (∂_i g_far) * h` -/

variable {s : ℝ}

/-- The far part of the force `F_i = (θ g) * ∂_i h + Φ_i`, `Φ_i = (∂_i g_far) * h`. -/
def movc2_Phi (s : ℝ) (ρ : Euc d → ℝ) (w : 𝓢R) (i : Fin d) : Euc d → ℝ :=
  movb2_T (movb2_kfar d s i) (movc2_h ρ w)

lemma movc2_T_eq (κ f : Euc d → ℝ) : movb2_T κ f = fun x => ∫ y, f y • κ (x - y) := by
  funext x
  unfold movb2_T
  rw [← integral_sub_left_eq_self (fun z => κ z * f (x - z)) volume x]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [mul_comm]

lemma movc2_kfar_smooth (i : Fin d) : ContDiff ℝ ∞ (movb2_kfar d s i) :=
  mova3b2_contDiff_Dj i (mv1_gfar_smooth (d := d) s)

lemma movc2_kfar_iter (hs0 : 0 ≤ s) (N : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : Fin d) (k : ℕ), k ≤ N →
    ∀ z : Euc d, ‖iteratedFDeriv ℝ k (movb2_kfar d s i) z‖ * (1 + ‖z‖) ≤ K := by
  choose C hC0 hC using fun k : ℕ => mv1_gfar_bound (d := d) hs0 (k + 1) (by omega)
  refine ⟨∑ k ∈ Finset.range (N + 1), C k, Finset.sum_nonneg fun k _ => hC0 k, fun i k hk z => ?_⟩
  have hgs : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (movb2_gfar d s) :=
    (mv1_gfar_smooth (d := d) s).of_le (by exact_mod_cast le_top)
  have h1 := movb2_norm_iter_partial hgs (EuclideanSpace.single i (1 : ℝ)) z
  have hn : ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := by simp
  rw [hn, one_mul] at h1
  have e : (movb2_kfar d s i) = fun z => fderiv ℝ (movb2_gfar d s) z (EuclideanSpace.single i (1 : ℝ)) := rfl
  rw [e]
  have hpos : 0 < 1 + ‖z‖ := by positivity
  have h2 : (1 + ‖z‖) ^ (-s - ((k + 1 : ℕ) : ℝ)) * (1 + ‖z‖) ≤ 1 := by
    rw [← Real.rpow_add_one hpos.ne']
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg z]) (by push_cast; linarith)
  have hCk : C k ≤ ∑ k ∈ Finset.range (N + 1), C k :=
    Finset.single_le_sum (f := C) (fun k _ => hC0 k) (Finset.mem_range.2 (by omega))
  calc ‖iteratedFDeriv ℝ k (fun z => fderiv ℝ (movb2_gfar d s) z (EuclideanSpace.single i (1 : ℝ))) z‖ * (1 + ‖z‖)
      ≤ (C k * (1 + ‖z‖) ^ (-s - ((k + 1 : ℕ) : ℝ))) * (1 + ‖z‖) :=
        mul_le_mul_of_nonneg_right (h1.trans (hC k z)) hpos.le
    _ = C k * ((1 + ‖z‖) ^ (-s - ((k + 1 : ℕ) : ℝ)) * (1 + ‖z‖)) := by ring
    _ ≤ C k * 1 := mul_le_mul_of_nonneg_left h2 (hC0 k)
    _ ≤ _ := by linarith

lemma movc2_h_weight {ρ : Euc d → ℝ} {q' : ℝ} {B : Euc d → Euc d} (D : MovC2Data d ρ q' B) (hd : 1 ≤ d)
    {m : ℝ} (hm : (d : ℝ) / 2 + 1 ≤ m) :
    ∃ M0 : ℝ, 0 ≤ M0 ∧ ∀ w : 𝓢R, Integrable (fun y => (1 + ‖y‖) * |movc2_h ρ w y|) volume ∧
      ∫ y, (1 + ‖y‖) * |movc2_h ρ w y| ≤ M0 * oscNorm m w := by
  obtain ⟨hψs, c, hc, hk⟩ := D.psiG
  obtain ⟨Cψ, hCψ⟩ := hk 0
  have hCψ0 : 0 ≤ Cψ := movc1_G_nonneg hCψ
  set n : ℕ := ⌊(d : ℝ) / 2⌋₊ + 1 with hn
  have hnm : (n : ℝ) ≤ m := by
    have : (⌊(d : ℝ) / 2⌋₊ : ℝ) ≤ (d : ℝ) / 2 := Nat.floor_le (by positivity)
    rw [hn]; push_cast; linarith
  have hnd : ((0 : ℕ) : ℝ) + (d : ℝ) / 2 < n := by
    rw [hn]; push_cast
    simpa using Nat.lt_floor_add_one ((d : ℝ) / 2)
  obtain ⟨Ce, hCe0, hCe⟩ := mo_sobolev_emb (d := d) 0 n hnd
  refine ⟨Cψ * Ce * movb2_A1 d c, by have := movb2_A1_nonneg (d := d) hc; positivity, fun w => ?_⟩
  have ow : 0 ≤ oscNorm m w := Real.sqrt_nonneg _
  have hw : ∀ y, |w y| ≤ Ce * oscNorm m w := fun y => by
    have := hCe w y
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hCe0)
    exact (mo_mono hnm (memOsc_schwartz m w)).2
  have hψb : ∀ y, |Real.sqrt (ρ y)| ≤ Cψ * Real.exp (-c * ‖y‖ ^ 2) := fun y => by
    have := hCψ y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hpt : ∀ y, (1 + ‖y‖) * |movc2_h ρ w y| ≤
      (Cψ * (Ce * oscNorm m w)) * ((1 + ‖y‖) * Real.exp (-c * ‖y‖ ^ 2)) := fun y => by
    unfold movc2_h
    rw [abs_mul]
    have h1 := mul_le_mul (hψb y) (hw y) (abs_nonneg _) (by positivity)
    calc (1 + ‖y‖) * (|Real.sqrt (ρ y)| * |w y|) = (1 + ‖y‖) * (|Real.sqrt (ρ y)| * |w y|) := rfl
      _ ≤ (1 + ‖y‖) * ((Cψ * Real.exp (-c * ‖y‖ ^ 2)) * (Ce * oscNorm m w)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  have hmaj := (movb2_A1_integrable hd hc).const_mul (Cψ * (Ce * oscNorm m w))
  have hcont : Continuous (fun y => (1 + ‖y‖) * |movc2_h ρ w y|) := by
    unfold movc2_h
    exact (continuous_const.add continuous_norm).mul
      ((hψs.continuous.mul w.continuous).abs)
  have hint : Integrable (fun y => (1 + ‖y‖) * |movc2_h ρ w y|) volume := by
    refine hmaj.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact hpt y
  refine ⟨hint, ?_⟩
  calc ∫ y, (1 + ‖y‖) * |movc2_h ρ w y| ≤ ∫ y, (Cψ * (Ce * oscNorm m w)) * ((1 + ‖y‖) * Real.exp (-c * ‖y‖ ^ 2)) :=
        integral_mono hint hmaj hpt
    _ = (Cψ * (Ce * oscNorm m w)) * movb2_A1 d c := by rw [integral_const_mul]; rfl
    _ = _ := by ring

/-- **The far force is a `C_b^N` function, uniformly:** `‖D^k Φ_i(x)‖ (1 + ‖x‖) ≤ C ‖w‖_{Σ^m}`. -/
theorem movc2_Phi_bound {ρ : Euc d → ℝ} {q' : ℝ} {B : Euc d → Euc d} (D : MovC2Data d ρ q' B)
    (hd : 1 ≤ d) (hs0 : 0 ≤ s) {m : ℝ} (hm : (d : ℝ) / 2 + 1 ≤ m) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : 𝓢R) (i : Fin d), ContDiff ℝ ∞ (movc2_Phi s ρ w i) ∧
      ∀ k ≤ N, ∀ x : Euc d, ‖iteratedFDeriv ℝ k (movc2_Phi s ρ w i) x‖ * (1 + ‖x‖) ≤ C * oscNorm m w := by
  obtain ⟨M0, hM0, hh⟩ := movc2_h_weight D hd hm
  obtain ⟨KN, hKN, hK⟩ := movc2_kfar_iter (s := s) hs0 N
  refine ⟨KN * M0, mul_nonneg hKN hM0, fun w i => ?_⟩
  have hhm : AEStronglyMeasurable (movc2_h ρ w) volume :=
    (D.psiG.1.continuous.mul w.continuous).aestronglyMeasurable
  obtain ⟨hint, hJ⟩ := hh w
  have hΦ : movc2_Phi s ρ w i = fun x => ∫ y, movc2_h ρ w y • movb2_kfar d s i (x - y) :=
    movc2_T_eq _ _
  rw [hΦ]
  refine ⟨contDiff_infty.2 fun n => ?_, fun k hk x => ?_⟩
  · obtain ⟨Kn, -, hKn⟩ := movc2_kfar_iter (s := s) hs0 n
    exact (movc2_conv_far n ℝ (movb2_kfar d s i) Kn _
      ((movc2_kfar_smooth i).of_le (by exact_mod_cast le_top)) (fun k hk z => hKn i k hk z) hhm hint).1
  · have := (movc2_conv_far N ℝ (movb2_kfar d s i) KN _
      ((movc2_kfar_smooth i).of_le (by exact_mod_cast le_top)) (fun k hk z => hK i k hk z) hhm hint).2 k hk x
    refine this.trans ?_
    calc KN * ∫ y, (1 + ‖y‖) * |movc2_h ρ w y| ≤ KN * (M0 * oscNorm m w) :=
          mul_le_mul_of_nonneg_left hJ hKN
      _ = _ := by ring

/-! ### The decomposition of `B` into local and far parts -/

lemma movc2_GA {ρ : Euc d → ℝ} (hρ : MovRhoData d ρ) (w : 𝓢R) (k : ℕ) :
    ∃ c E : ℝ, 0 < c ∧ 0 ≤ E ∧ movb2_GA k c E (movc2_h ρ w) := by
  obtain ⟨c, hc, hj⟩ := mv1_gauss_common (ψ := movc2_h ρ w) (mv1_h_gauss hρ w).2 k
  choose! C hC using hj
  refine ⟨c, ∑ j ∈ Finset.range (k + 1), |C j|, hc, Finset.sum_nonneg fun j _ => abs_nonneg _,
    fun i hi y => ?_⟩
  refine (hC i hi y).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  exact (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg _)
    (Finset.mem_range.2 (by omega)))

lemma movc2_h_smooth {ρ : Euc d → ℝ} (hρ : MovRhoData d ρ) (w : 𝓢R) : ContDiff ℝ ∞ (movc2_h ρ w) :=
  (mv1_h_gauss hρ w).1

lemma movc2_convFun_eq_T (f : Euc d → ℝ) :
    HRS.Whole.convFun (rieszKernel d s) f = movb2_T (fun z => rieszKernel d s z) f := by
  funext x; rw [mv1_convFun_eq]; rfl

/-- The force splits: `F_i = (θ g) * ∂_i h + Φ_i`. -/
lemma movc2_hF {ρ : Euc d → ℝ} (hρ : MovRhoData d ρ) (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (w : 𝓢R)
    (i : Fin d) (x : Euc d) :
    HRS.Whole.convFun (rieszKernel d s) (fun y => gradient (fun z => Real.sqrt (ρ z) * w z) y i) x =
      movc2_Fl s ρ w i x + movc2_Phi s ρ w i x := by
  obtain ⟨c, E, hc, hE, hga⟩ := movc2_GA hρ w 1
  have hh1 : ContDiff ℝ 1 (movc2_h ρ w) := (movc2_h_smooth hρ w).of_le (by exact_mod_cast le_top)
  obtain ⟨h0, h1⟩ := movb2_GA_01 hga
  have e1 := mv1_force_eq_conv_grad hd hs0 hsd hc hE hh1 h0 h1 x i
  have e2 := movb2_force_split hd hs0 hsd hc hh1 hga i x
  have e3 : (fun y => gradient (fun z => Real.sqrt (ρ z) * w z) y i) =
      mova3b1_Dj i (movc2_h ρ w) := funext fun y => movtr_gradient_apply _ y i
  rw [e3]
  rw [e1] at e2
  unfold movc2_Fl movc2_Phi
  rw [movc1_convFun_eq_T]
  exact e2

/-- Gaussian bound of `∂_i ∂_i h`. -/
lemma movc2_DD_bound {ρ : Euc d → ℝ} (hρ : MovRhoData d ρ) (w : 𝓢R) :
    ∃ c E : ℝ, 0 < c ∧ 0 ≤ E ∧ movb2_GA 2 c E (movc2_h ρ w) ∧
      ∀ (i : Fin d) (y : Euc d), |mova3b1_Dj i (mova3b1_Dj i (movc2_h ρ w)) y| ≤
        E * Real.exp (-c * ‖y‖ ^ 2) := by
  obtain ⟨c, E, hc, hE, hga⟩ := movc2_GA hρ w 2
  refine ⟨c, E, hc, hE, hga, fun i y => ?_⟩
  have hh2 : ContDiff ℝ ((1 + 1 : ℕ) : WithTop ℕ∞) (movc2_h ρ w) :=
    (movc2_h_smooth hρ w).of_le (movb2_le_infty (1 + 1))
  set e : Euc d := EuclideanSpace.single i (1 : ℝ) with he
  have hn : ‖e‖ = 1 := by simp [he]
  have g1 := movb2_GA_partial (k := 1) hh2 hga e
  have hh1 : ContDiff ℝ ((0 + 1 : ℕ) : WithTop ℕ∞) (fun y => fderiv ℝ (movc2_h ρ w) y e) := by
    have := movb2_partial_contDiff (k := 1) hh2 e
    simpa using this
  have g0 := movb2_GA_partial (k := 0) hh1 (by simpa using g1) e
  have := g0 0 le_rfl y
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, hn] at this
  show |fderiv ℝ (fun y => fderiv ℝ (movc2_h ρ w) y e) y e| ≤ _
  simpa using this

/-- The Laplacian splits: `g * Δh = (θ g) * Δh + ∑_i ∂_i Φ_i`. -/
lemma movc2_hG {ρ : Euc d → ℝ} (hρ : MovRhoData d ρ) (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (w : 𝓢R)
    (x : Euc d) :
    HRS.Whole.convFun (rieszKernel d s) (fun y => Laplacian.laplacian (fun z => Real.sqrt (ρ z) * w z) y) x =
      movc2_Gl s ρ w x + ∑ i, mova3b1_Dj i (movc2_Phi s ρ w i) x := by
  obtain ⟨c, E, hc, hE, hga2, hDD⟩ := movc2_DD_bound hρ w
  have hh : ContDiff ℝ ∞ (movc2_h ρ w) := movc2_h_smooth hρ w
  have hh1 : ContDiff ℝ 1 (movc2_h ρ w) := hh.of_le (by exact_mod_cast le_top)
  have hga1 : movb2_GA 1 c E (movc2_h ρ w) := movb2_GA_mono (by norm_num) hga2
  have hh2 : ContDiff ℝ 2 (movc2_h ρ w) := hh.of_le (movb2_le_infty 2)
  -- the profile `u2 = ∑_i ∂_i ∂_i h`
  set u2 : Euc d → ℝ := fun y => ∑ i, mova3b1_Dj i (mova3b1_Dj i (movc2_h ρ w)) y with hu2
  have hlap : (fun y => Laplacian.laplacian (fun z => Real.sqrt (ρ z) * w z) y) = u2 := by
    funext y
    exact mv1_laplacian_eq hh2 y
  rw [hlap]
  have hDDc : ∀ i : Fin d, Continuous (mova3b1_Dj i (mova3b1_Dj i (movc2_h ρ w))) := fun i =>
    (mova3b2_contDiff_Dj i (mova3b2_contDiff_Dj i hh)).continuous
  have hu2c : Continuous u2 := continuous_finsetSum _ fun i _ => hDDc i
  have hu2b : ∀ y, |u2 y| ≤ ((d : ℝ) * E) * Real.exp (-c * ‖y‖ ^ 2) := fun y => by
    calc |u2 y| ≤ ∑ i, |mova3b1_Dj i (mova3b1_Dj i (movc2_h ρ w)) y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin d, E * Real.exp (-c * ‖y‖ ^ 2) := Finset.sum_le_sum fun i _ => hDD i y
      _ = _ := by simp [mul_assoc]
  have hdE : 0 ≤ (d : ℝ) * E := mul_nonneg (Nat.cast_nonneg _) hE
  have hint : ∀ {κ : Euc d → ℝ}, MovKer d s κ → Integrable (fun z => κ z * u2 (x - z)) volume :=
    fun hκ => movb2_T_integrable hd hs0 hsd hκ hc hdE hu2c hu2b x
  rw [movc2_convFun_eq_T]
  have hsplit : movb2_T (fun z => rieszKernel d s z) u2 x =
      movb2_T (movb2_gloc d s) u2 x + movb2_T (movb2_gfar d s) u2 x := by
    unfold movb2_T
    rw [← integral_add (hint (movb2_gloc_ker hd hs0 hsd)) (hint (movb2_gfar_ker hd hs0 hsd))]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    rw [← add_mul, movb2_gloc_add_gfar]
  rw [hsplit]
  congr 1
  · unfold movc2_Gl
    rw [movc1_convFun_eq_T]
  · -- the far part: integrate by parts
    have hperi : ∀ i : Fin d, Integrable (fun z => movb2_gfar d s z *
        mova3b1_Dj i (mova3b1_Dj i (movc2_h ρ w)) (x - z)) volume := fun i =>
      movb2_T_integrable hd hs0 hsd (movb2_gfar_ker hd hs0 hsd) hc hE (hDDc i) (hDD i) x
    have e1 : movb2_T (movb2_gfar d s) u2 x =
        ∑ i, movb2_T (movb2_gfar d s) (mova3b1_Dj i (mova3b1_Dj i (movc2_h ρ w))) x := by
      unfold movb2_T
      rw [← integral_finsetSum _ (fun i _ => hperi i)]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [hu2, Finset.mul_sum]
    rw [e1]
    refine Finset.sum_congr rfl fun i _ => ?_
    -- ibp with `u = ∂_i h`, then the derivative of `Φ_i`
    have hu : ContDiff ℝ 1 (mova3b1_Dj i (movc2_h ρ w)) :=
      (mova3b2_contDiff_Dj i hh).of_le (by exact_mod_cast le_top)
    have hgaD : movb2_GA 1 c (E * ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖) (mova3b1_Dj i (movc2_h ρ w)) := by
      have hh2' : ContDiff ℝ ((1 + 1 : ℕ) : WithTop ℕ∞) (movc2_h ρ w) := by simpa using hh2
      exact movb2_GA_partial (k := 1) hh2' hga2 _
    have hibp := movb2_ibp hd hs0 hsd hc hu hgaD i x
    have hfd := (movb2_T_fderiv hd hs0 hsd (movb2_kfar_ker (d := d) hs0 i) hc hh1 hga1 x).2
      (EuclideanSpace.single i (1 : ℝ))
    have hHas := (movb2_T_fderiv hd hs0 hsd (movb2_kfar_ker (d := d) hs0 i) hc hh1 hga1 x).1
    have hPhi : mova3b1_Dj i (movc2_Phi s ρ w i) x =
        movb2_T (movb2_kfar d s i) (mova3b1_Dj i (movc2_h ρ w)) x := by
      unfold mova3b1_Dj movc2_Phi
      rw [hHas.fderiv]
      exact hfd
    rw [hPhi, ← hibp]
    rfl

/-- The far part of the source `A`: `∑_i ∂_iΦ_i + ∑_i (-q'/2) x_i Φ_i + ∑_i (1/2) B_i Φ_i`. -/
def movc2_thetaFar (s : ℝ) (ρ : Euc d → ℝ) (q' : ℝ) (B : Euc d → Euc d) (w : 𝓢R) (x : Euc d) : ℝ :=
  ((∑ i, mova3b1_Dj i (movc2_Phi s ρ w i) x) + ∑ i, (-q' / 2) * (x i * movc2_Phi s ρ w i x)) +
    ∑ i, (1 / 2) * (B x i * movc2_Phi s ρ w i x)

/-- The far part of `B(v,w)`. -/
def movc2_Fa (s : ℝ) (ρ : Euc d → ℝ) (q' : ℝ) (B : Euc d → Euc d) (v w : 𝓢R) (x : Euc d) : ℝ :=
  (∑ i, mova3b1_Dj i (⇑v) x * movc2_Phi s ρ w i x) + v x * movc2_thetaFar s ρ q' B w x

lemma movc2_alg_id {n : ℕ} (a Fl Ph dPh X Bi : Fin n → ℝ) (V G q : ℝ) :
    ∑ i, a i * (Fl i + Ph i) + V * ((G + ∑ i, dPh i) + (1 / 2) * ∑ i, (-q * X i + Bi i) * (Fl i + Ph i)) =
    ((∑ i, a i * Fl i) + V * G) + ((∑ i, (-q / 2) * (V * (X i * Fl i))) +
      ∑ i, (1 / 2) * ((Bi i * V) * Fl i)) +
    ((∑ i, a i * Ph i) + V * (((∑ i, dPh i) + ∑ i, (-q / 2) * (X i * Ph i)) +
      ∑ i, (1 / 2) * (Bi i * Ph i))) := by
  simp only [mul_add, add_mul, Finset.mul_sum, Finset.sum_add_distrib]
  ring_nf

/-- **`B = local + far`** (pointwise, for Schwartz `v`, `w`). -/
theorem movc2_B_decomp {ρ : Euc d → ℝ} {q' : ℝ} {B : Euc d → Euc d} (D : MovC2Data d ρ q' B)
    (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (v w : 𝓢R) (x : Euc d) :
    movB d s ρ (⇑v) (⇑w) x = movc2_Lloc s ρ q' B v w x + movc2_Fa s ρ q' B v w x := by
  have hv : Differentiable ℝ (⇑v) := (v.smooth ⊤).differentiable (by simp)
  rw [mv1_B_formula hd hs0 hsd D.rho hv w x]
  have hF := fun i => movc2_hF D.rho hd hs0 hsd w i x
  have hG := movc2_hG D.rho hd hs0 hsd w x
  have hb : ∀ i : Fin d, gradient (fun y => Real.log (ρ y)) x i = -q' * x i + B x i := fun i => by
    rw [D.grad x]; simp
  have hgv : ∀ i : Fin d, gradient (⇑v) x i = mova3b1_Dj i (⇑v) x := fun i =>
    movtr_gradient_apply _ x i
  simp only [hF, hG, hb, hgv, movc2_Lloc, movc2_Fa, movc2_thetaFar]
  exact movc2_alg_id (fun i => mova3b1_Dj i (⇑v) x) (fun i => movc2_Fl s ρ w i x)
    (fun i => movc2_Phi s ρ w i x) (fun i => mova3b1_Dj i (movc2_Phi s ρ w i) x) (fun i => x i)
    (fun i => B x i) (v x) (movc2_Gl s ρ w x) q'

/-! ### The far part is a bounded multiplier acting on `Σ^s` -/

lemma movc2_Q_sum {ι : Type*} (S : Finset ι) {n m : ℕ} {A : ι → ℝ} {f : ι → Euc d → ℝ}
    (hs : ∀ i ∈ S, ContDiff ℝ ∞ (f i)) (h0 : ∀ i ∈ S, 0 ≤ A i)
    (h : ∀ i ∈ S, mova3b2_Q n m (A i) (f i)) :
    mova3b2_Q n m (∑ i ∈ S, A i) (fun x => ∑ i ∈ S, f i x) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact mova3b2_Q_zero (d := d) (K := n) (m := m) (A := 0) le_rfl
  | insert a S ha ih =>
    have hS : ContDiff ℝ ∞ (fun x => ∑ i ∈ S, f i x) :=
      ContDiff.sum fun i hi => hs i (Finset.mem_insert_of_mem hi)
    have := mova3b2_Q_add (hs a (Finset.mem_insert_self _ _)) hS (h a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hs i (Finset.mem_insert_of_mem hi)) (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
        (fun i hi => h i (Finset.mem_insert_of_mem hi)))
    have e : (fun x => ∑ i ∈ insert a S, f i x) = f a + fun x => ∑ i ∈ S, f i x := by
      funext x; simp [Finset.sum_insert ha]
    rw [e, Finset.sum_insert ha]
    exact this

lemma movc2_Bi_frechet {ρ : Euc d → ℝ} {q' : ℝ} {B : Euc d → Euc d} (D : MovC2Data d ρ q' B) (i : Fin d)
    (N : ℕ) : ∃ Mb : ℝ, 0 ≤ Mb ∧ ∀ k ≤ N, ∀ x, ‖iteratedFDeriv ℝ k (fun x => B x i) x‖ ≤ Mb := by
  have hBs := movc2_B_smooth D
  obtain ⟨Mb, hMb⟩ := D.cb N
  refine ⟨Mb, (norm_nonneg _).trans (hMb.2 0 (Nat.zero_le _) 0), fun k hk x => ?_⟩
  have hBk : ContDiff ℝ (k : WithTop ℕ∞) B := hBs.of_le (by exact_mod_cast le_top)
  have h := (EuclideanSpace.proj (𝕜 := ℝ) i : Euc d →L[ℝ] ℝ).norm_iteratedFDeriv_comp_left
    (f := B) (x := x) hBk.contDiffAt (n := k) le_rfl
  have h1 : ‖(EuclideanSpace.proj (𝕜 := ℝ) i : Euc d →L[ℝ] ℝ)‖ ≤ 1 := movb2_norm_proj_le i
  refine (show ‖iteratedFDeriv ℝ k (fun x => B x i) x‖ ≤ _ from h).trans ?_
  exact (mul_le_of_le_one_left (norm_nonneg _) h1).trans (hMb.2 k hk x)

lemma movc2_Phi_tg {ρ : Euc d → ℝ} {q' : ℝ} {B : Euc d → Euc d} (D : MovC2Data d ρ q' B) (hd : 1 ≤ d)
    (hs0 : 0 ≤ s) {m : ℝ} (hm : (d : ℝ) / 2 + 1 ≤ m) (w : 𝓢R) (i : Fin d) :
    (movc2_Phi s ρ w i).HasTemperateGrowth := by
  refine ⟨(movc2_Phi_bound D hd hs0 hm 0).choose_spec.2 w i |>.1, fun n => ?_⟩
  obtain ⟨C, hC0, hC⟩ := movc2_Phi_bound (s := s) D hd hs0 hm n
  refine ⟨0, C * oscNorm m w, fun x => ?_⟩
  have := (hC w i).2 n le_rfl x
  have h1 : ‖iteratedFDeriv ℝ n (movc2_Phi s ρ w i) x‖ ≤
      ‖iteratedFDeriv ℝ n (movc2_Phi s ρ w i) x‖ * (1 + ‖x‖) :=
    le_mul_of_one_le_right (norm_nonneg _) (by linarith [norm_nonneg x])
  simpa using h1.trans this

lemma movc2_tg_fderiv {f : Euc d → ℝ} (hf : f.HasTemperateGrowth) : (fderiv ℝ f).HasTemperateGrowth := by
  refine ⟨hf.1.fderiv_right (m := ∞) (by simp), fun n => ?_⟩
  obtain ⟨k, C, h⟩ := hf.2 (n + 1)
  exact ⟨k, C, fun x => by rw [norm_iteratedFDeriv_fderiv]; exact h x⟩

lemma movc2_tg_Dj (i : Fin d) {f : Euc d → ℝ} (hf : f.HasTemperateGrowth) :
    (mova3b1_Dj i f).HasTemperateGrowth := by
  have := (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ) : Euc d)).hasTemperateGrowth.comp
    (movc2_tg_fderiv hf)
  exact this

/-- `Φ_i` is a `C_b^N` multiplier with decay `(1+‖x‖)^{-1}`, with constants `C ‖w‖_{Σ^m}`. -/
lemma movc2_Phi_Q {ρ : Euc d → ℝ} {q' : ℝ} {B : Euc d → Euc d} (D : MovC2Data d ρ q' B) (hd : 1 ≤ d)
    (hs0 : 0 ≤ s) {m : ℝ} (hm : (d : ℝ) / 2 + 1 ≤ m) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : 𝓢R) (i : Fin d), ContDiff ℝ ∞ (movc2_Phi s ρ w i) ∧
      (movc2_Phi s ρ w i).HasTemperateGrowth ∧
      mova3b2_Q (N + 1) 1 (C * oscNorm m w) (movc2_Phi s ρ w i) ∧
      ∀ k ≤ N + 1, ∀ x : Euc d, ‖iteratedFDeriv ℝ k (movc2_Phi s ρ w i) x‖ ≤ C * oscNorm m w := by
  obtain ⟨C, hC0, hC⟩ := movc2_Phi_bound (s := s) D hd hs0 hm (N + 1)
  refine ⟨C, hC0, fun w i => ⟨(hC w i).1, movc2_Phi_tg D hd hs0 hm w i, ?_, fun k hk x => ?_⟩⟩
  · exact mova3b2_Q_of_iter (hC w i).1 fun k hk x => by simpa using (hC w i).2 k hk x
  · have h2 := (hC w i).2 k hk x
    have h3 : ‖iteratedFDeriv ℝ k (movc2_Phi s ρ w i) x‖ ≤
        ‖iteratedFDeriv ℝ k (movc2_Phi s ρ w i) x‖ * (1 + ‖x‖) :=
      le_mul_of_one_le_right (norm_nonneg _) (by linarith [norm_nonneg x])
    exact h3.trans h2

/-- **The far source `θ_far` is a `C_b^N` multiplier**, with constants `C ‖w‖_{Σ^m}`. -/
lemma movc2_thetaFar_Q {ρ : Euc d → ℝ} {q' : ℝ} {B : Euc d → Euc d} (D : MovC2Data d ρ q' B)
    (hd : 1 ≤ d) (hs0 : 0 ≤ s) {m : ℝ} (hm : (d : ℝ) / 2 + 1 ≤ m) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : 𝓢R, ContDiff ℝ ∞ (movc2_thetaFar s ρ q' B w) ∧
      (movc2_thetaFar s ρ q' B w).HasTemperateGrowth ∧
      mova3b2_Q N 0 (C * oscNorm m w) (movc2_thetaFar s ρ q' B w) := by
  obtain ⟨CΦ, hCΦ0, hΦ⟩ := movc2_Phi_Q (s := s) D hd hs0 hm N
  choose hBsm hBtg hBdum using fun i : Fin d => movc2_Bi D i N
  choose Mb hMb0 hMb using fun i : Fin d => movc2_Bi_frechet D i N
  set Msum : ℝ := ∑ i, Mb i with hMsum
  have hMs0 : 0 ≤ Msum := Finset.sum_nonneg fun i _ => hMb0 i
  have hMbs : ∀ i, Mb i ≤ Msum := fun i =>
    Finset.single_le_sum (f := Mb) (fun i _ => hMb0 i) (Finset.mem_univ i)
  set c1 : ℝ := (d : ℝ) * 1 + (d : ℝ) * (|-q' / 2| * ((N : ℝ) + 1)) +
    (d : ℝ) * (|(1 : ℝ) / 2| * (2 ^ N * Msum)) with hc1
  have hc10 : 0 ≤ c1 := by positivity
  refine ⟨c1 * CΦ, mul_nonneg hc10 hCΦ0, fun w => ?_⟩
  have ow : 0 ≤ oscNorm m w := Real.sqrt_nonneg _
  set A0 : ℝ := CΦ * oscNorm m w with hA0
  have hA00 : 0 ≤ A0 := mul_nonneg hCΦ0 ow
  obtain hΦs := fun i => (hΦ w i).1
  obtain hΦt := fun i => (hΦ w i).2.1
  obtain hΦq := fun i => (hΦ w i).2.2.1
  obtain hΦf := fun i => (hΦ w i).2.2.2
  have hΦq0 : ∀ i, mova3b2_Q (N + 1) 0 A0 (movc2_Phi s ρ w i) := fun i =>
    mova3b2_Q_mono_m (Nat.zero_le 1) (hΦq i)
  have hΦqN1 : ∀ i, mova3b2_Q N 1 A0 (movc2_Phi s ρ w i) := fun i =>
    mova3b2_Q_mono_K (Nat.le_succ N) (hΦq i)
  -- (a) `∂_i Φ_i`
  have Qa : ∀ i : Fin d, mova3b2_Q N 0 A0 (mova3b1_Dj i (movc2_Phi s ρ w i)) := fun i => (hΦq0 i).2 i
  have Qa' : mova3b2_Q N 0 (∑ _i : Fin d, A0) (fun x => ∑ i, mova3b1_Dj i (movc2_Phi s ρ w i) x) :=
    movc2_Q_sum Finset.univ (fun i _ => mova3b2_contDiff_Dj i (hΦs i)) (fun _ _ => hA00) (fun i _ => Qa i)
  -- (b) `x_i Φ_i`
  have Qb : ∀ i : Fin d, mova3b2_Q N 0 (|-q' / 2| * (((N : ℝ) + 1) * A0))
      (fun x => (-q' / 2) * (x i * movc2_Phi s ρ w i x)) := fun i =>
    movc2_Q_smul _ ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.mul (hΦs i))
      (mova3b2_Q_xmul i hA00 (hΦs i) (hΦqN1 i))
  have Qb' : mova3b2_Q N 0 (∑ _i : Fin d, |-q' / 2| * (((N : ℝ) + 1) * A0))
      (fun x => ∑ i, (-q' / 2) * (x i * movc2_Phi s ρ w i x)) :=
    movc2_Q_sum Finset.univ (fun i _ => (contDiff_const.mul
      ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.mul (hΦs i))))
      (fun _ _ => by positivity) (fun i _ => Qb i)
  -- (c) `B_i Φ_i`
  have Qc0 : ∀ i : Fin d, mova3b2_Q N 0 (2 ^ N * (Mb i * A0)) (fun x => B x i * movc2_Phi s ρ w i x) := by
    intro i
    refine mova3b2_Q_of_iter ((hBsm i).mul (hΦs i)) fun k hk x => ?_
    have h1 := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := (⊤ : ℕ∞)) (hBsm i) (hΦs i) x (n := k)
      (by exact_mod_cast le_top)
    simp only [pow_zero, mul_one]
    refine h1.trans ?_
    have hbd : ∀ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * ‖iteratedFDeriv ℝ j (fun x => B x i) x‖ *
        ‖iteratedFDeriv ℝ (k - j) (movc2_Phi s ρ w i) x‖ ≤ (k.choose j : ℝ) * (Mb i * A0) := by
      intro j hj
      have hj' : j ≤ k := by simpa [Nat.lt_succ_iff] using hj
      have b1 := hMb i j (hj'.trans hk) x
      have b2 := hΦf i (k - j) (by omega) x
      calc (k.choose j : ℝ) * ‖iteratedFDeriv ℝ j (fun x => B x i) x‖ *
          ‖iteratedFDeriv ℝ (k - j) (movc2_Phi s ρ w i) x‖
          ≤ (k.choose j : ℝ) * Mb i * A0 :=
            mul_le_mul (mul_le_mul_of_nonneg_left b1 (Nat.cast_nonneg _)) b2 (norm_nonneg _)
              (mul_nonneg (Nat.cast_nonneg _) (hMb0 i))
        _ = _ := by ring
    refine (Finset.sum_le_sum hbd).trans ?_
    rw [← Finset.sum_mul]
    have hsum : (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ)) = 2 ^ k := by
      exact_mod_cast Nat.sum_range_choose k
    rw [hsum]
    have h2 : (2 : ℝ) ^ k ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hk
    have h3 : 0 ≤ Mb i * A0 := mul_nonneg (hMb0 i) hA00
    exact mul_le_mul_of_nonneg_right h2 h3
  have Qc : ∀ i : Fin d, mova3b2_Q N 0 (|(1 : ℝ) / 2| * (2 ^ N * Msum * A0))
      (fun x => (1 / 2) * (B x i * movc2_Phi s ρ w i x)) := fun i =>
    movc2_Q_smul _ ((hBsm i).mul (hΦs i)) (mova3b2_Q_mono_A (by
      have : Mb i ≤ Msum := hMbs i
      have h4 : (0 : ℝ) ≤ 2 ^ N := by positivity
      calc 2 ^ N * (Mb i * A0) ≤ 2 ^ N * (Msum * A0) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this hA00) h4
        _ = 2 ^ N * Msum * A0 := by ring) (Qc0 i))
  have Qc' : mova3b2_Q N 0 (∑ _i : Fin d, |(1 : ℝ) / 2| * (2 ^ N * Msum * A0))
      (fun x => ∑ i, (1 / 2) * (B x i * movc2_Phi s ρ w i x)) :=
    movc2_Q_sum Finset.univ (fun i _ => contDiff_const.mul ((hBsm i).mul (hΦs i)))
      (fun _ _ => by positivity) (fun i _ => Qc i)
  -- smoothness and temperate growth
  have hs_a : ContDiff ℝ ∞ (fun x => ∑ i, mova3b1_Dj i (movc2_Phi s ρ w i) x) :=
    ContDiff.sum fun i _ => mova3b2_contDiff_Dj i (hΦs i)
  have hs_b : ContDiff ℝ ∞ (fun x => ∑ i : Fin d, (-q' / 2) * (x i * movc2_Phi s ρ w i x)) :=
    ContDiff.sum fun i _ => contDiff_const.mul ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.mul (hΦs i))
  have hs_c : ContDiff ℝ ∞ (fun x => ∑ i : Fin d, (1 / 2 : ℝ) * (B x i * movc2_Phi s ρ w i x)) :=
    ContDiff.sum fun i _ => contDiff_const.mul ((hBsm i).mul (hΦs i))
  have hs_ab := hs_a.add hs_b
  have hQ1 := mova3b2_Q_add hs_a hs_b Qa' Qb'
  have hQ2 := mova3b2_Q_add hs_ab hs_c hQ1 Qc'
  have hfun : movc2_thetaFar s ρ q' B w = ((fun x => ∑ i, mova3b1_Dj i (movc2_Phi s ρ w i) x) +
      (fun x => ∑ i : Fin d, (-q' / 2) * (x i * movc2_Phi s ρ w i x))) +
      (fun x => ∑ i : Fin d, (1 / 2 : ℝ) * (B x i * movc2_Phi s ρ w i x)) := rfl
  have hconst : (∑ _i : Fin d, A0) + (∑ _i : Fin d, |-q' / 2| * (((N : ℝ) + 1) * A0)) +
      (∑ _i : Fin d, |(1 : ℝ) / 2| * (2 ^ N * Msum * A0)) = c1 * CΦ * oscNorm m w := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hc1, hA0]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]; exact hs_ab.add hs_c
  · have ta : (fun x => ∑ i : Fin d, mova3b1_Dj i (movc2_Phi s ρ w i) x).HasTemperateGrowth :=
      Function.HasTemperateGrowth.sum fun i _ => movc2_tg_Dj i (hΦt i)
    have tb : (fun x => ∑ i : Fin d, (-q' / 2) * (x i * movc2_Phi s ρ w i x)).HasTemperateGrowth :=
      Function.HasTemperateGrowth.sum fun i _ => (Function.HasTemperateGrowth.const (-q' / 2)).mul
        ((ContinuousLinearMap.hasTemperateGrowth (EuclideanSpace.proj (𝕜 := ℝ) i : Euc d →L[ℝ] ℝ)).mul (hΦt i))
    have tc : (fun x => ∑ i : Fin d, (1 / 2 : ℝ) * (B x i * movc2_Phi s ρ w i x)).HasTemperateGrowth :=
      Function.HasTemperateGrowth.sum fun i _ => (Function.HasTemperateGrowth.const (1 / 2 : ℝ)).mul
        ((hBtg i).mul (hΦt i))
    rw [hfun]
    exact (ta.add tb).add tc
  · rw [hfun, ← hconst]
    exact hQ2

/-- **The far part of `B` is bounded `Σ^m × Σ^m → Σ^{m-a}`** (indeed into `Σ^{m-1}`), by `B3`. -/
theorem movc2_far {ρ : Euc d → ℝ} {q' : ℝ} {B : Euc d → Euc d} (D : MovC2Data d ρ q' B)
    (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {m : ℝ} (hm : (d : ℝ) / 2 + 3 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v w : 𝓢R, MemOsc (m - movA d s) (movc2_Fa s ρ q' B v w) ∧
      oscNorm (m - movA d s) (movc2_Fa s ρ q' B v w) ≤ C * oscNorm m v * oscNorm m w := by
  set σ : ℝ := m - movA d s with hσdef
  have hA1 : 1 ≤ movA d s := le_max_left _ _
  have hσ1 : σ ≤ m - 1 := by linarith
  have hdpos : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hm1 : (d : ℝ) / 2 + 1 ≤ m := by linarith
  have hmpos : 1 ≤ m := by linarith
  set N : ℕ := ⌈m⌉₊ with hN
  have hmN : m ≤ N := Nat.le_ceil m
  obtain ⟨CΦ, hCΦ0, hΦ⟩ := movc2_Phi_Q (s := s) D hd hs0 hm1 N
  obtain ⟨Cθ, hCθ0, hθ⟩ := movc2_thetaFar_Q (s := s) D hd hs0 hm1 N
  obtain ⟨C1, hC10, hB3a⟩ := mo_mult_cb (d := d) (m - 1) N (by rw [abs_of_nonneg (by linarith)]; linarith)
  obtain ⟨C2, hC20, hB3b⟩ := mo_mult_cb (d := d) m N (by rw [abs_of_nonneg (by linarith)]; exact hmN)
  obtain ⟨Cd, hCd, hosc⟩ := movc2_osc_D (d := d) (m - 1)
  have e1 : m - 1 + 1 = m := by ring
  refine ⟨(d : ℝ) * (C1 * CΦ * Cd) + C2 * Cθ, by positivity, fun v w => ?_⟩
  have ov : 0 ≤ oscNorm m v := Real.sqrt_nonneg _
  have ow : 0 ≤ oscNorm m w := Real.sqrt_nonneg _
  have hA0 : 0 ≤ CΦ * oscNorm m w := mul_nonneg hCΦ0 ow
  -- the terms `∂_i v · Φ_i`
  have T1 : ∀ i : Fin d, MemOsc σ (fun x => mova3b1_Dj i (⇑v) x * movc2_Phi s ρ w i x) ∧
      oscNorm σ (fun x => mova3b1_Dj i (⇑v) x * movc2_Phi s ρ w i x) ≤
        C1 * CΦ * Cd * oscNorm m v * oscNorm m w := by
    intro i
    obtain ⟨hs_, ht_, hq_, -⟩ := hΦ w i
    have hQ : mova3b2_Q N 0 (CΦ * oscNorm m w) (movc2_Phi s ρ w i) :=
      mova3b2_Q_mono_m (Nat.zero_le 1) (mova3b2_Q_mono_K (Nat.le_succ N) hq_)
    have hf : MemOsc (m - 1) (mova3b1_Dj i (⇑v)) := by
      rw [← movc2_coe_D]; exact memOsc_schwartz _ _
    obtain ⟨h1, h2⟩ := hB3a _ hA0 _ ht_ hQ _ hf
    have e : (fun x => mova3b1_Dj i (⇑v) x * movc2_Phi s ρ w i x) =
        fun x => movc2_Phi s ρ w i x * mova3b1_Dj i (⇑v) x := by funext x; ring
    rw [e]
    obtain ⟨h3, h4⟩ := mo_mono hσ1 h1
    refine ⟨h3, h4.trans (h2.trans ?_)⟩
    have hDv : oscNorm (m - 1) (mova3b1_Dj i (⇑v)) ≤ Cd * oscNorm m v := by
      rw [← movc2_coe_D]
      have := hosc i v
      rwa [e1] at this
    calc C1 * (CΦ * oscNorm m w) * oscNorm (m - 1) (mova3b1_Dj i (⇑v))
        ≤ C1 * (CΦ * oscNorm m w) * (Cd * oscNorm m v) :=
          mul_le_mul_of_nonneg_left hDv (mul_nonneg hC10 hA0)
      _ = _ := by ring
  -- the term `v · θ_far`
  have T2 : MemOsc σ (fun x => v x * movc2_thetaFar s ρ q' B w x) ∧
      oscNorm σ (fun x => v x * movc2_thetaFar s ρ q' B w x) ≤ C2 * Cθ * oscNorm m v * oscNorm m w := by
    obtain ⟨hs_, ht_, hq_⟩ := hθ w
    have hA1' : 0 ≤ Cθ * oscNorm m w := mul_nonneg hCθ0 ow
    obtain ⟨h1, h2⟩ := hB3b _ hA1' _ ht_ hq_ (⇑v) (memOsc_schwartz m v)
    have e : (fun x => v x * movc2_thetaFar s ρ q' B w x) =
        fun x => movc2_thetaFar s ρ q' B w x * v x := by funext x; ring
    rw [e]
    obtain ⟨h3, h4⟩ := mo_mono (show σ ≤ m by linarith) h1
    refine ⟨h3, h4.trans (h2.trans (le_of_eq ?_))⟩
    ring
  have hsum := movc1_osc_sum σ (Finset.univ : Finset (Fin d)) (fun i _ => (T1 i).1)
  have htot := movc1_osc_add σ hsum.1 T2.1
  refine ⟨htot.1, htot.2.trans ?_⟩
  have hsum2 : ∑ i : Fin d, oscNorm σ (fun x => mova3b1_Dj i (⇑v) x * movc2_Phi s ρ w i x) ≤
      ∑ _i : Fin d, C1 * CΦ * Cd * oscNorm m v * oscNorm m w := Finset.sum_le_sum fun i _ => (T1 i).2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum2
  calc oscNorm σ (fun x => ∑ i, mova3b1_Dj i (⇑v) x * movc2_Phi s ρ w i x) +
        oscNorm σ (fun x => v x * movc2_thetaFar s ρ q' B w x)
      ≤ (d : ℝ) * (C1 * CΦ * Cd * oscNorm m v * oscNorm m w) + C2 * Cθ * oscNorm m v * oscNorm m w :=
        add_le_add (hsum.2.trans hsum2) T2.2
    _ = _ := by ring

/-! ### The frozen statement -/

/-- **`mov_operators_B_proof`**: the frozen statement `HRS.Whole.mov_operators_B` (S6.1, second assertion):
`‖B(v,w)‖_{Σ^{m-a}} ≤ C_m ‖v‖_{Σ^m} ‖w‖_{Σ^m}` for `m > d/2 + 3` real. -/
theorem mov_operators_B_proof {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ)
    (hβ : 0 < β) (hq : 0 < q) (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ)
    (m : ℝ) (hm : (d : ℝ) / 2 + 3 < m) :
    ∃ C : ℝ, ∀ v w : SchwartzMap (Euc d) ℝ,
      MemOsc (m - movA d s) (movB d s ρ v w) ∧
        oscNorm (m - movA d s) (movB d s ρ v w) ≤ C * oscNorm m v * oscNorm m w := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨B, D⟩ := movc2_data hd hs0 hsd hq hβ hρ
  obtain ⟨CL, hCL0, hL⟩ := movc2_local D hs0 hsd hm
  obtain ⟨CF, hCF0, hF⟩ := movc2_far D hd1 hs0 hsd hm
  refine ⟨CL + CF, fun v w => ?_⟩
  have hdec : movB d s ρ (⇑v) (⇑w) =
      fun x => movc2_Lloc s ρ (β * q) B v w x + movc2_Fa s ρ (β * q) B v w x :=
    funext (movc2_B_decomp D hd1 hs0 hsd v w)
  rw [hdec]
  obtain ⟨hL1, hL2⟩ := hL v w
  obtain ⟨hF1, hF2⟩ := hF v w
  obtain ⟨h1, h2⟩ := movc1_osc_add (m - movA d s) hL1 hF1
  refine ⟨h1, h2.trans ?_⟩
  calc oscNorm (m - movA d s) (movc2_Lloc s ρ (β * q) B v w) +
        oscNorm (m - movA d s) (movc2_Fa s ρ (β * q) B v w)
      ≤ CL * oscNorm m v * oscNorm m w + CF * oscNorm m v * oscNorm m w := add_le_add hL2 hF2
    _ = _ := by ring

end HRS.MS.MovC2

/-- Tie: `mov_operators_B_proof` has exactly the type of the frozen statement. -/
example := (@HRS.MS.MovC2.mov_operators_B_proof : type_of% @HRS.Whole.mov_operators_B)
