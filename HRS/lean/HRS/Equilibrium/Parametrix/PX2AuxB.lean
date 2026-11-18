import HRS.Equilibrium.Parametrix.PX2AuxC
import HRS.Equilibrium.LocalDivMain

/-!
# Packet PX2b auxiliaries: smoothness of parametric integrals

`contDiff_integral_param`: if `x ↦ K x w` is `C^m` for a.e. `w`, all derivatives up to order `m` are
measurable in `w` and dominated by integrable functions (uniformly in `x`), then `x ↦ ∫ K x w dν`
is `C^m` and its derivatives are the integrals of the derivatives.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

universe u

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

section Param

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Hypotheses for differentiation under the integral up to order `m`. -/
structure ParamHyp (m : ℕ) (K : E → α → F) (ν : Measure α) : Prop where
  smooth : ∀ᵐ w ∂ν, ContDiff ℝ m (fun x => K x w)
  meas : ∀ k : ℕ, k ≤ m → ∀ x, AEStronglyMeasurable (fun w => iteratedFDeriv ℝ k (fun x' => K x' w) x) ν
  bound : ∀ k : ℕ, k ≤ m → ∃ bd : α → ℝ, Integrable bd ν ∧
    ∀ᵐ w ∂ν, ∀ x, ‖iteratedFDeriv ℝ k (fun x' => K x' w) x‖ ≤ bd w

theorem ParamHyp.meas_zero {m : ℕ} {K : E → α → F} (h : ParamHyp m K ν) (x : E) :
    AEStronglyMeasurable (fun w => K x w) ν := by
  have h0 := h.meas 0 (Nat.zero_le _) x
  have : (fun w => K x w) = fun w => (continuousMultilinearCurryFin0 ℝ E F)
      (iteratedFDeriv ℝ 0 (fun x' => K x' w) x) := by
    funext w
    simp [iteratedFDeriv_zero_eq_comp]
  rw [this]
  exact (continuousMultilinearCurryFin0 ℝ E F).continuous.comp_aestronglyMeasurable h0

theorem ParamHyp.succ {m : ℕ} {K : E → α → F} (h : ParamHyp (m + 1) K ν) :
    ParamHyp m (fun x w => fderiv ℝ (fun y => K y w) x) ν where
  smooth := by
    filter_upwards [h.smooth] with w hw
    exact hw.fderiv_right (by norm_cast)
  meas := by
    intro k hk x
    have h1 := h.meas (k + 1) (by omega) x
    have : (fun w => iteratedFDeriv ℝ k (fun x' => fderiv ℝ (fun y => K y w) x') x) =
        fun w => (continuousMultilinearCurryRightEquiv' ℝ k E F)
          (iteratedFDeriv ℝ (k + 1) (fun x' => K x' w) x) := by
      funext w
      rw [iteratedFDeriv_succ_eq_comp_right]
      simp
    rw [this]
    exact (continuousMultilinearCurryRightEquiv' ℝ k E F).continuous.comp_aestronglyMeasurable h1
  bound := by
    intro k hk
    obtain ⟨bd, hbd, hb⟩ := h.bound (k + 1) (by omega)
    refine ⟨bd, hbd, ?_⟩
    filter_upwards [hb] with w hw x
    rw [norm_iteratedFDeriv_fderiv]
    exact hw x

end Param

section ParamMain

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem integrable_zeroth {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {m : ℕ} {K : E → α → F} (h : ParamHyp m K ν) (x : E) : Integrable (fun w => K x w) ν := by
  obtain ⟨bd, hbd, hb⟩ := h.bound 0 (Nat.zero_le _)
  refine hbd.mono' (h.meas_zero x) ?_
  filter_upwards [hb] with w hw
  have := hw x
  rwa [norm_iteratedFDeriv_zero] at this

theorem contDiff_integral_param_aux : ∀ (m : ℕ) {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (K : E → α → F), ParamHyp m K ν →
    ContDiff ℝ m (fun x => ∫ w, K x w ∂ν) ∧ ∀ k : ℕ, k ≤ m → ∀ x,
      iteratedFDeriv ℝ k (fun x' => ∫ w, K x' w ∂ν) x =
        ∫ w, iteratedFDeriv ℝ k (fun x' => K x' w) x ∂ν
  | 0, F, _, _, _, K, h => by
    have hk0 : ∀ x, iteratedFDeriv ℝ 0 (fun x' => ∫ w, K x' w ∂ν) x =
        ∫ w, iteratedFDeriv ℝ 0 (fun x' => K x' w) x ∂ν := by
      intro x
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
      exact ((continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.integral_comp_comm (fun w => K x w)).symm
    refine ⟨?_, fun k hk x => ?_⟩
    · rw [Nat.cast_zero, contDiff_zero]
      obtain ⟨bd, hbd, hb⟩ := h.bound 0 (Nat.zero_le _)
      refine continuous_of_dominated (bound := bd) (fun x => h.meas_zero x) (fun x => ?_) hbd ?_
      · filter_upwards [hb] with w hw
        have := hw x
        rwa [norm_iteratedFDeriv_zero] at this
      · filter_upwards [h.smooth] with w hw
        exact (contDiff_zero (𝕜 := ℝ)).mp (by simpa using hw)
    · have : k = 0 := by omega
      subst this
      exact hk0 x
  | m + 1, F, _, _, _, K, h => by
    have hK' := h.succ
    obtain ⟨ih1, ih2⟩ := contDiff_integral_param_aux m (fun x w => fderiv ℝ (fun y => K y w) x) hK'
    have hderiv : ∀ x, HasFDerivAt (fun x' => ∫ w, K x' w ∂ν)
        (∫ w, fderiv ℝ (fun y => K y w) x ∂ν) x := by
      intro x
      obtain ⟨bd, hbd, hb⟩ := h.bound 1 (by omega)
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Set.univ) (bound := bd)
        (F' := fun x w => fderiv ℝ (fun y => K y w) x)
        Filter.univ_mem (Filter.Eventually.of_forall fun x' => h.meas_zero x')
        (integrable_zeroth h x) (hK'.meas_zero x) ?_ hbd ?_
      · filter_upwards [hb] with w hw x' _
        have := hw x'
        have e : ‖iteratedFDeriv ℝ 1 (fun x'' => K x'' w) x'‖ =
            ‖fderiv ℝ (fun y => K y w) x'‖ := by
          have := (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := fun x'' => K x'' w) (x := x') (n := 0)).symm
          rw [this, norm_iteratedFDeriv_zero]
        rwa [e] at this
      · filter_upwards [h.smooth] with w hw x' _
        exact ((hw.differentiable (by simp)) x').hasFDerivAt
    have hfd : fderiv ℝ (fun x' => ∫ w, K x' w ∂ν) = fun x => ∫ w, fderiv ℝ (fun y => K y w) x ∂ν := by
      funext x; exact (hderiv x).fderiv
    refine ⟨?_, fun k hk x => ?_⟩
    · rw [Nat.cast_succ]
      exact contDiff_succ_iff_hasFDerivAt.mpr ⟨_, ih1, hderiv⟩
    · rcases k with _ | j
      · simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
        exact ((continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.integral_comp_comm (fun w => K x w)).symm
      · rw [iteratedFDeriv_succ_eq_comp_right]
        simp only [Function.comp_apply]
        rw [hfd, ih2 j (by omega) x]
        have e := (continuousMultilinearCurryRightEquiv' ℝ j E F).symm.toContinuousLinearEquiv.integral_comp_comm (μ := ν)
          (fun w => iteratedFDeriv ℝ j (fun x' => fderiv ℝ (fun y => K y w) x') x)
        simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv] at e
        rw [← e]
        refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
        simp only [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]

end ParamMain

/-! ### Bounded derivatives of smooth torus functions -/

variable {d : ℕ}

theorem isCompact_box : IsCompact {w : Euc d | ∀ i, |w i| ≤ 1 / 2} := by
  have hc1 : IsClosed {w : Euc d | ∀ i, |w i| ≤ 1 / 2} := by
    have : {w : Euc d | ∀ i, |w i| ≤ 1 / 2} = ⋂ i, {w : Euc d | |w i| ≤ 1 / 2} := by
      ext w; simp
    rw [this]
    exact isClosed_iInter fun i => isClosed_le
      ((continuous_apply i).comp (PiLp.continuous_ofLp 2 _) |>.abs) continuous_const
  refine (isCompact_closedBall (0 : Euc d) (d : ℝ)).of_isClosed_subset hc1 ?_
  intro w hw
  rw [mem_closedBall_zero_iff]
  exact KernelGrad.norm_le_card_of_box hw

theorem bdd_iteratedFDeriv_lift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H₀ : Torus d → E) (n : ℕ) (h : ContDiff ℝ n (Torus.lift H₀)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : Euc d, ‖iteratedFDeriv ℝ n (Torus.lift H₀) y‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_box (d := d)).exists_bound_of_continuousOn
    (h.continuous_iteratedFDeriv (m := n) le_rfl).continuousOn
  refine ⟨max M 0, le_max_right _ _, fun y => ?_⟩
  obtain ⟨w, hw, hwb⟩ := KernelGrad.exists_mk_box (Torus.mk y)
  rw [iteratedFDeriv_lift_eq_of_mk_eq H₀ n hw.symm]
  exact (hM w hwb).trans (le_max_left _ _)

/-! ### Logarithmic envelopes -/

theorem log_pow_le (b : ℕ) {ε : ℝ} (hε : 0 < ε) {T : ℝ} (hT : 1 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ T → (1 + |Real.log t|) ^ b ≤ C * t ^ (-ε) := by
  set δ : ℝ := ε / (b + 1) with hδ
  have hb1 : (0 : ℝ) < b + 1 := by positivity
  have hδ0 : 0 < δ := div_pos hε hb1
  have hδb : δ * b ≤ ε := by
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ hb1]
    nlinarith [hε.le, (Nat.cast_nonneg b : (0:ℝ) ≤ b)]
  set C1 : ℝ := (1 + 1 / δ) ^ b with hC1
  set C2 : ℝ := (1 + Real.log T) ^ b * T ^ ε with hC2
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  refine ⟨max C1 C2, le_trans (by positivity) (le_max_left _ _), fun t ht htT => ?_⟩
  have htp : 0 ≤ t ^ (-ε) := Real.rpow_nonneg ht.le _
  by_cases ht1 : t ≤ 1
  · have hlog : Real.log t ≤ 0 := Real.log_nonpos ht.le ht1
    have habs : |Real.log t| = Real.log (1 / t) := by
      rw [abs_of_nonpos hlog, one_div, Real.log_inv]
    have h1 : Real.log (1 / t) ≤ (1 / t) ^ δ / δ := Real.log_le_rpow_div (by positivity) hδ0
    have h2 : (1 / t) ^ δ = t ^ (-δ) := by
      rw [one_div, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]
    have h3 : 1 ≤ t ^ (-δ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1 (by linarith)
    have h4 : 1 + |Real.log t| ≤ (1 + 1 / δ) * t ^ (-δ) := by
      rw [habs]
      have h5 : Real.log (1 / t) ≤ t ^ (-δ) / δ := by rw [← h2]; exact h1
      have h6 : (1 + 1 / δ) * t ^ (-δ) = t ^ (-δ) + t ^ (-δ) / δ := by ring
      rw [h6]; linarith
    calc (1 + |Real.log t|) ^ b ≤ ((1 + 1 / δ) * t ^ (-δ)) ^ b :=
          pow_le_pow_left₀ (by positivity) h4 b
      _ = C1 * (t ^ (-δ)) ^ b := by rw [mul_pow]
      _ = C1 * t ^ (-δ * b) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
      _ ≤ C1 * t ^ (-ε) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
      _ ≤ max C1 C2 * t ^ (-ε) := mul_le_mul_of_nonneg_right (le_max_left _ _) htp
  · push Not at ht1
    have hlog : |Real.log t| ≤ Real.log T := by
      rw [abs_of_nonneg (Real.log_nonneg ht1.le)]
      exact Real.log_le_log ht htT
    have h1 : (1 + |Real.log t|) ^ b ≤ (1 + Real.log T) ^ b :=
      pow_le_pow_left₀ (by positivity) (by linarith) b
    have h2 : T ^ (-ε) ≤ t ^ (-ε) := Real.rpow_le_rpow_of_nonpos ht htT (by linarith)
    have h3 : (1 + Real.log T) ^ b = C2 * T ^ (-ε) := by
      rw [hC2, mul_assoc, ← Real.rpow_add (by linarith)]
      simp
    calc (1 + |Real.log t|) ^ b ≤ (1 + Real.log T) ^ b := h1
      _ = C2 * T ^ (-ε) := h3
      _ ≤ C2 * t ^ (-ε) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ max C1 C2 * t ^ (-ε) := mul_le_mul_of_nonneg_right (le_max_right _ _) htp

/-- The singular weight of the conormal bound at `c = 0`. -/
def envW (d : ℕ) (σ : ℝ) (b : ℕ) (w : Euc d) : ℝ :=
  1 + ‖w‖ ^ (-σ) * (1 + |Real.log ‖w‖|) ^ b

theorem measurable_envW (σ : ℝ) (b : ℕ) : Measurable (envW d σ b) := by
  unfold envW
  have h1 : Measurable fun w : Euc d => ‖w‖ ^ (-σ) := measurable_norm.pow_const _
  have h2 : Measurable fun w : Euc d => (1 + |Real.log ‖w‖|) ^ b :=
    (measurable_const.add (Real.measurable_log.comp measurable_norm).abs).pow_const _
  exact measurable_const.add (h1.mul h2)

theorem one_le_envW (σ : ℝ) (b : ℕ) (w : Euc d) : 1 ≤ envW d σ b w := by
  unfold envW
  have : 0 ≤ ‖w‖ ^ (-σ) * (1 + |Real.log ‖w‖|) ^ b := by positivity
  linarith

theorem integrableOn_cube_envW (hd : 2 ≤ d) {σ : ℝ} (hσ : σ < d) (b : ℕ) :
    IntegrableOn (envW d σ b) (LocalDivAux.cube d) := by
  set ε : ℝ := ((d : ℝ) - σ) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨C, hC0, hC⟩ := log_pow_le b hε0 (T := (d : ℝ) + 1) (by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith)
  have hcb : Bornology.IsBounded (LocalDivAux.cube d) :=
    (Metric.isBounded_closedBall (x := (0 : Euc d)) (r := (d : ℝ))).subset (fun w hw => by
      rw [mem_closedBall_zero_iff]; exact LocalDivAux.cube_norm_le hw)
  have hfin : (volume : Measure (Euc d)) (LocalDivAux.cube d) ≠ ⊤ := hcb.measure_lt_top.ne
  have hint : IntegrableOn (fun w : Euc d => 1 + C * ‖w‖ ^ (-(σ + ε))) (LocalDivAux.cube d) :=
    (integrableOn_const hfin).add
      ((LocalDivAux.integrableOn_cube_rpow (by omega) (a := σ + ε) (by rw [hε]; linarith)).const_mul C)
  refine Integrable.mono' hint (measurable_envW σ b).aestronglyMeasurable ?_
  have hnt : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have h0 : ∀ᵐ w ∂(volume : Measure (Euc d)), w ≠ 0 :=
    (Set.countable_singleton (0 : Euc d)).ae_notMem _
  filter_upwards [ae_restrict_mem LocalDivAux.measurableSet_cube, ae_restrict_of_ae h0] with w hw hw0
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hwT : ‖w‖ ≤ (d : ℝ) + 1 := (LocalDivAux.cube_norm_le hw).trans (by linarith)
  have h1 := hC ‖w‖ hwpos hwT
  have e : ‖w‖ ^ (-σ) * ‖w‖ ^ (-ε) = ‖w‖ ^ (-(σ + ε)) := by
    rw [← Real.rpow_add hwpos]; congr 1; ring
  have hp : 0 ≤ ‖w‖ ^ (-σ) := Real.rpow_nonneg (norm_nonneg _) _
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [one_le_envW (d := d) σ b w])]
  unfold envW
  have := mul_le_mul_of_nonneg_left h1 hp
  have e2 : ‖w‖ ^ (-σ) * (C * ‖w‖ ^ (-ε)) = C * ‖w‖ ^ (-(σ + ε)) := by
    rw [← e]; ring
  rw [e2] at this
  linarith

/-! ### Slices `x ↦ H(x, x - w)` -/

theorem px2_isOpen_offDiag : IsOpen (offDiag d) := by
  have h1 : Continuous fun p : Euc d × Euc d => Torus.mk p.1 :=
    continuous_pi fun i => (AddCircle.continuous_mk' _).comp
      ((continuous_apply i).comp ((PiLp.continuous_ofLp 2 _).comp continuous_fst))
  have h2 : Continuous fun p : Euc d × Euc d => Torus.mk p.2 :=
    continuous_pi fun i => (AddCircle.continuous_mk' _).comp
      ((continuous_apply i).comp ((PiLp.continuous_ofLp 2 _).comp continuous_snd))
  exact isOpen_ne_fun h1 h2

/-- the diagonal embedding `x ↦ (x, x)` -/
def diagCLM (d : ℕ) : Euc d →L[ℝ] Euc d × Euc d :=
  ContinuousLinearMap.prod (ContinuousLinearMap.id ℝ _) (ContinuousLinearMap.id ℝ _)

theorem diagCLM_apply (x : Euc d) : diagCLM d x = (x, x) := rfl

theorem norm_diagCLM_le : ‖diagCLM d‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  simp [diagCLM_apply, Prod.norm_def]

theorem iteratedFDeriv_comp_clm_of_open' {E G F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {n : WithTop ℕ∞} {f : E → F} (hf : ContDiffOn ℝ n f U)
    (L : G →L[ℝ] E) {x : G} (hx : L x ∈ U) {i : ℕ} (hi : (i : WithTop ℕ∞) ≤ n) :
    iteratedFDeriv ℝ i (f ∘ L) x = (iteratedFDeriv ℝ i f (L x)).compContinuousLinearMap fun _ => L := by
  have h1 := L.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn
    (hU.preimage L.continuous).uniqueDiffOn hx (i := i) hi
  have e1 := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f ∘ L) i (hU.preimage L.continuous)
    (show x ∈ L ⁻¹' U from hx)
  have e2 := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f) i hU hx
  rw [e1, e2] at h1
  exact h1

theorem iteratedFDeriv_slice {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : WithTop ℕ∞} {H : Euc d × Euc d → F} (hH : ContDiffOn ℝ n H (offDiag d))
    {w x : Euc d} (hw : Torus.mk w ≠ 0) {i : ℕ} (hi : (i : WithTop ℕ∞) ≤ n) :
    iteratedFDeriv ℝ i (fun x' => H (x', x' - w)) x =
      (iteratedFDeriv ℝ i H (x, x - w)).compContinuousLinearMap fun _ => diagCLM d := by
  set c : Euc d × Euc d := (0, -w) with hc
  have hfun : (fun x' : Euc d => H (x', x' - w)) = (fun p => H (p + c)) ∘ diagCLM d := by
    funext x'
    simp only [Function.comp_apply, diagCLM_apply, hc, Prod.mk_add_mk, add_zero]
    rw [sub_eq_add_neg]
  have hU : IsOpen {p : Euc d × Euc d | p + c ∈ offDiag d} :=
    px2_isOpen_offDiag.preimage (continuous_id.add continuous_const)
  have hmem : diagCLM d x + c = (x, x - w) := by
    simp only [diagCLM_apply, hc, Prod.mk_add_mk, add_zero]
    rw [sub_eq_add_neg]
  have hxU : diagCLM d x ∈ {p : Euc d × Euc d | p + c ∈ offDiag d} := by
    show diagCLM d x + c ∈ offDiag d
    rw [hmem, px2_mem_offDiag_iff]
    simp only [sub_sub_cancel]
    exact hw
  have hf : ContDiffOn ℝ n (fun p => H (p + c)) {p : Euc d × Euc d | p + c ∈ offDiag d} :=
    hH.comp (contDiff_id.add contDiff_const).contDiffOn (fun p hp => hp)
  rw [hfun, iteratedFDeriv_comp_clm_of_open' hU hf (diagCLM d) hxU hi]
  rw [iteratedFDeriv_comp_add_right (f := H) i c, hmem]

/-! ### Pointwise bounds of the slices of a conormal kernel -/

theorem lift2_slice_eq_chart (F : Torus d → Torus d → ℝ) (w x' : Euc d) :
    lift2 F (x', x' - w) = toChart F (x' - (1 / 2 : ℝ) • w, w) := by
  simp only [lift2, toChart]
  congr 2 <;> module

theorem norm_slice_le {σ : ℝ} {b m : ℕ} {B : ℝ} {F : Torus d → Torus d → ℝ} (hB : 0 ≤ B)
    (hF : Conormal σ b m B F) {w : Euc d} (hw : Torus.mk w ≠ 0) (hwb : ∀ i, |w i| ≤ 1 / 2)
    (x : Euc d) {i : ℕ} (hi : i ≤ m) :
    ‖iteratedFDeriv ℝ i (fun x' => lift2 F (x', x' - w)) x‖ ≤ B * envW d σ b w := by
  have hw0 : w ≠ 0 := by
    rintro rfl; apply hw; funext j; simp [Torus.mk]
  have hE : 1 ≤ envW d σ b w := one_le_envW σ b w
  by_cases hnear : ‖w‖ < r0
  · have hfun : (fun x' : Euc d => lift2 F (x', x' - w)) =
        fun x' => toChart F (x' - (1 / 2 : ℝ) • w, w) := by
      funext x'; exact lift2_slice_eq_chart F w x'
    have e := iteratedFDeriv_comp_sub (𝕜 := ℝ) (f := fun X' => toChart F (X', w)) i
      ((1 / 2 : ℝ) • w) x
    rw [hfun, e]
    rw [← norm_mixedDeriv_zero]
    have := hF.near i 0 (by omega) (x - (1 / 2 : ℝ) • w) w hw0 hnear
    simpa [envW] using this
  · push Not at hnear
    have hH : ContDiffOn ℝ (m : WithTop ℕ∞) (lift2 F) (offDiag d) := hF.smooth
    rw [iteratedFDeriv_slice hH hw (i := i) (by exact_mod_cast hi)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have hp : (x, x - w) ∈ offDiag d := by
      rw [px2_mem_offDiag_iff]; simp only [sub_sub_cancel]; exact hw
    have hdist : r0 ≤ Torus.eucDist (Torus.mk (x, x - w).1) (Torus.mk (x, x - w).2) := by
      have : Torus.eucDist (Torus.mk x) (Torus.mk (x - w)) = ‖w‖ :=
        eucDist_mk_sub_eq (by rw [mk_sub_eq]; abel) hwb
      simpa [this] using hnear
    have h1 := hF.far i hi (x, x - w) hp hdist
    have h2 : ∏ _j : Fin i, ‖diagCLM d‖ ≤ 1 := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact pow_le_one₀ (norm_nonneg _) norm_diagCLM_le
    calc ‖iteratedFDeriv ℝ i (lift2 F) (x, x - w)‖ * ∏ _j : Fin i, ‖diagCLM d‖
        ≤ B * 1 := mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) hB
      _ ≤ B * envW d σ b w := by rw [mul_one]; nlinarith

/-! ### The row integral in the cube -/

theorem row_eq_cube {ρ : Torus d → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (F : Torus d → Torus d → ℝ) (x₀ : Euc d) :
    ∫ y, F (Torus.mk x₀) y ∂(withDensityReal ρ) =
      ∫ w in LocalDivAux.cube d, lift2 F (x₀, x₀ - w) * Torus.lift ρ (x₀ - w) := by
  rw [integral_withDensityReal_eq ρ hρm hρ0]
  haveI : (volume : Measure (Torus d)).IsNegInvariant :=
    Measure.pi.isNegInvariant (fun _ : Fin d => (volume : Measure UnitAddCircle))
  have h1 := integral_sub_left_eq_self (fun y => ρ y * F (Torus.mk x₀) y)
    (volume : Measure (Torus d)) (Torus.mk x₀)
  rw [← h1, KernelAux.integral_torus_box]
  have hmp := PiLp.volume_preserving_ofLp (Fin d)
  have hemb : MeasurableEmbedding (@WithLp.ofLp 2 (Fin d → ℝ)) :=
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding
  have h2 := hmp.setIntegral_preimage_emb hemb
    (fun y : Fin d → ℝ => ρ (Torus.mk x₀ - KernelAux.boxPt y) *
      F (Torus.mk x₀) (Torus.mk x₀ - KernelAux.boxPt y)) (KernelAux.Box d)
  have h3 : ∫ y in KernelAux.Box d, ρ (Torus.mk x₀ - KernelAux.boxPt y) *
      F (Torus.mk x₀) (Torus.mk x₀ - KernelAux.boxPt y) =
      ∫ w in (@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹' (KernelAux.Box d),
        ρ (Torus.mk x₀ - KernelAux.boxPt w.ofLp) *
          F (Torus.mk x₀) (Torus.mk x₀ - KernelAux.boxPt w.ofLp) := h2.symm
  rw [h3]
  have hc : (@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹' (KernelAux.Box d) = LocalDivAux.cube d := by
    ext w; simp [KernelAux.Box, LocalDivAux.cube]
  rw [hc]
  refine setIntegral_congr_fun LocalDivAux.measurableSet_cube fun w _ => ?_
  have e : Torus.mk x₀ - KernelAux.boxPt w.ofLp = Torus.mk (x₀ - w) := by
    rw [mk_sub_eq]; rfl
  simp only [e, lift2, Torus.lift, Function.comp_apply]
  ring

/-! ### Smoothness of the rows of a conormal kernel -/

theorem ae_cube_mk_ne_zero (hd : 2 ≤ d) :
    ∀ᵐ w ∂((volume : Measure (Euc d)).restrict (LocalDivAux.cube d)), Torus.mk w ≠ 0 := by
  have hnt : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have h0 : ∀ᵐ w ∂(volume : Measure (Euc d)), w ≠ 0 :=
    (Set.countable_singleton (0 : Euc d)).ae_notMem _
  filter_upwards [ae_restrict_mem LocalDivAux.measurableSet_cube, ae_restrict_of_ae h0] with w hwc hw0
  exact box_ne_zero hw0 (fun i => LocalDivAux.abs_le_half_of_cube hwc i)

theorem conormal_row_smooth_aux (hd : 2 ≤ d) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
    {σ : ℝ} (hσ : σ < d) (b m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → Conormal σ b m B F →
      Torus.IsCk (m : WithTop ℕ∞) (fun x => ∫ y, F x y ∂(withDensityReal ρ)) ∧
      Torus.cbNorm m (fun x => ∫ y, F x y ∂(withDensityReal ρ)) ≤ C * B := by
  have hρs : ContDiff ℝ ∞' (Torus.lift ρ) := hρ.smooth
  have hbd : ∀ n : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ y, ‖iteratedFDeriv ℝ n (Torus.lift ρ) y‖ ≤ M :=
    fun n => bdd_iteratedFDeriv_lift ρ n (hρs.of_le (by exact_mod_cast le_top))
  choose Mρ hMρ0 hMρ using hbd
  set S : ℕ → ℝ := fun k => ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Mρ (k - i) with hS
  have hS0 : ∀ k, 0 ≤ S k := fun k =>
    Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hMρ0 _)
  set ν : Measure (Euc d) := (volume : Measure (Euc d)).restrict (LocalDivAux.cube d) with hν
  set Cint : ℝ := ∫ w, envW d σ b w ∂ν with hCint
  have hCint0 : 0 ≤ Cint :=
    integral_nonneg fun w => (show (0 : ℝ) ≤ envW d σ b w by linarith [one_le_envW (d := d) σ b w])
  have henv : Integrable (envW d σ b) ν := integrableOn_cube_envW hd hσ b
  refine ⟨∑ k ∈ Finset.range (m + 1), S k * Cint,
    Finset.sum_nonneg fun k _ => mul_nonneg (hS0 k) hCint0, fun B F hB hF => ?_⟩
  set K : Euc d → Euc d → ℝ := fun x' w => lift2 F (x', x' - w) * Torus.lift ρ (x' - w) with hK
  have hH : ContDiffOn ℝ (m : WithTop ℕ∞) (lift2 F) (offDiag d) := hF.smooth
  have hKfull : ContDiffOn ℝ (m : WithTop ℕ∞)
      (fun p : Euc d × Euc d => lift2 F p * Torus.lift ρ p.2) (offDiag d) :=
    hH.mul ((hρs.of_le (by exact_mod_cast le_top)).comp contDiff_snd).contDiffOn
  -- smoothness of the slices
  have hPsm : ∀ w : Euc d, Torus.mk w ≠ 0 → ContDiff ℝ (m : WithTop ℕ∞) (fun x' : Euc d => lift2 F (x', x' - w)) := by
    intro w hw
    have hA : ContDiff ℝ (m : WithTop ℕ∞) (fun x' : Euc d => (x', x' - w)) :=
      contDiff_id.prodMk (contDiff_id.sub contDiff_const)
    have := hH.comp (hA.contDiffOn (s := Set.univ)) (fun x' _ => by
      show (x', x' - w) ∈ offDiag d
      rw [px2_mem_offDiag_iff]; simp only [sub_sub_cancel]; exact hw)
    exact contDiffOn_univ.mp this
  have hQsm : ∀ w : Euc d, ContDiff ℝ (m : WithTop ℕ∞) (fun x' : Euc d => Torus.lift ρ (x' - w)) := fun w =>
    ((hρs.of_le (by exact_mod_cast le_top)).comp (contDiff_id.sub contDiff_const))
  -- pointwise bound
  have hbound : ∀ k : ℕ, k ≤ m → ∀ᵐ w ∂ν, ∀ x, ‖iteratedFDeriv ℝ k (fun x' => K x' w) x‖ ≤
      B * S k * envW d σ b w := by
    intro k hk
    filter_upwards [ae_restrict_mem LocalDivAux.measurableSet_cube, ae_cube_mk_ne_zero hd] with w hwc hw
    intro x
    have hwb : ∀ i, |w i| ≤ 1 / 2 := fun i => LocalDivAux.abs_le_half_of_cube hwc i
    have h1 := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (hPsm w hw) (hQsm w) x (n := k) (by exact_mod_cast hk)
    refine h1.trans ?_
    calc ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun x' : Euc d => lift2 F (x', x' - w)) x‖ *
          ‖iteratedFDeriv ℝ (k - i) (fun x' : Euc d => Torus.lift ρ (x' - w)) x‖
        ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (B * envW d σ b w) * Mρ (k - i) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i ≤ m := by have := Finset.mem_range.mp hi; omega
          have e1 := norm_slice_le hB hF hw hwb x hi'
          have e2 : ‖iteratedFDeriv ℝ (k - i) (fun x' : Euc d => Torus.lift ρ (x' - w)) x‖ ≤ Mρ (k - i) := by
            rw [iteratedFDeriv_comp_sub (f := Torus.lift ρ) (k - i) w x]
            exact hMρ _ _
          have hc : (0 : ℝ) ≤ (k.choose i : ℝ) := Nat.cast_nonneg _
          have hE : 0 ≤ B * envW d σ b w := mul_nonneg hB (by linarith [one_le_envW (d := d) σ b w])
          exact mul_le_mul (mul_le_mul_of_nonneg_left e1 hc) e2 (norm_nonneg _) (mul_nonneg hc hE)
      _ = B * S k * envW d σ b w := by
          rw [hS]; simp only
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
  -- hypotheses of the parametric lemma
  have hparam : ParamHyp m K ν := by
    refine ⟨?_, ?_, ?_⟩
    · filter_upwards [ae_cube_mk_ne_zero hd] with w hw
      exact (hPsm w hw).mul (hQsm w)
    · intro k hk x
      -- continuity on the open set `{mk w ≠ 0}`
      have hU : IsOpen {w : Euc d | Torus.mk w ≠ 0} := isOpen_mk_ne_zero'
      have hcont : ContinuousOn (fun w : Euc d => iteratedFDeriv ℝ k (fun x' => K x' w) x)
          {w : Euc d | Torus.mk w ≠ 0} := by
        have h1 : ContinuousOn (iteratedFDeriv ℝ k (fun p : Euc d × Euc d => lift2 F p * Torus.lift ρ p.2))
            (offDiag d) := by
          have := hKfull.continuousOn_iteratedFDerivWithin (m := k) (by exact_mod_cast hk)
            px2_isOpen_offDiag.uniqueDiffOn
          exact this.congr (iteratedFDerivWithin_of_isOpen k px2_isOpen_offDiag).symm
        have h2 : ContinuousOn (fun w : Euc d => iteratedFDeriv ℝ k
            (fun p : Euc d × Euc d => lift2 F p * Torus.lift ρ p.2) (x, x - w))
            {w : Euc d | Torus.mk w ≠ 0} := by
          refine h1.comp (continuous_const.prodMk (continuous_const.sub continuous_id)).continuousOn ?_
          intro w hw
          show (x, x - w) ∈ offDiag d
          rw [px2_mem_offDiag_iff]; simp only [sub_sub_cancel]; exact hw
        have h3 := (ContinuousMultilinearMap.compContinuousLinearMapL
          (fun _ : Fin k => diagCLM d) : ContinuousMultilinearMap ℝ (fun _ : Fin k => Euc d × Euc d) ℝ →L[ℝ]
            ContinuousMultilinearMap ℝ (fun _ : Fin k => Euc d) ℝ).continuous.comp_continuousOn h2
        refine h3.congr fun w hw => ?_
        have := iteratedFDeriv_slice (H := fun p : Euc d × Euc d => lift2 F p * Torus.lift ρ p.2)
          hKfull (w := w) (x := x) hw (i := k) (by exact_mod_cast hk)
        simpa [hK] using this
      have hmeas : AEStronglyMeasurable (fun w : Euc d => iteratedFDeriv ℝ k (fun x' => K x' w) x)
          (ν.restrict {w : Euc d | Torus.mk w ≠ 0}) :=
        hcont.aestronglyMeasurable hU.measurableSet
      have hres : ν.restrict {w : Euc d | Torus.mk w ≠ 0} = ν :=
        Measure.restrict_eq_self_of_ae_mem (ae_cube_mk_ne_zero hd)
      rwa [hres] at hmeas
    · intro k hk
      refine ⟨fun w => B * S k * envW d σ b w, henv.const_mul _, hbound k hk⟩
  obtain ⟨hcd, hform⟩ := contDiff_integral_param_aux m K hparam
  have hrow : (fun x₀ : Euc d => ∫ y, F (Torus.mk x₀) y ∂(withDensityReal ρ)) =
      fun x₀ => ∫ w, K x₀ w ∂ν := by
    funext x₀
    exact row_eq_cube hρ.density.measurable hρ.density.nonneg F x₀
  have hlift : Torus.lift (fun x => ∫ y, F x y ∂(withDensityReal ρ)) =
      fun x₀ => ∫ w, K x₀ w ∂ν := hrow
  refine ⟨?_, ?_⟩
  · unfold Torus.IsCk
    rw [hlift]; exact hcd
  · unfold Torus.cbNorm
    rw [hlift]
    have hk : ∀ k ∈ Finset.range (m + 1), ⨆ x : Euc d, ‖iteratedFDeriv ℝ k (fun x₀ => ∫ w, K x₀ w ∂ν) x‖ ≤
        B * (S k * Cint) := by
      intro k hk'
      have hkm : k ≤ m := by have := Finset.mem_range.mp hk'; omega
      refine ciSup_le fun x => ?_
      rw [hform k hkm x]
      have hint : ∫ w, B * S k * envW d σ b w ∂ν = B * (S k * Cint) := by
        rw [integral_const_mul, hCint]; ring
      rw [← hint]
      exact norm_integral_le_of_norm_le (henv.const_mul _) ((hbound k hkm).mono fun w hw => hw x)
    calc _ ≤ ∑ k ∈ Finset.range (m + 1), B * (S k * Cint) := Finset.sum_le_sum hk
      _ = (∑ k ∈ Finset.range (m + 1), S k * Cint) * B := by
          rw [← Finset.mul_sum]; ring

end HRS.Parx

end
