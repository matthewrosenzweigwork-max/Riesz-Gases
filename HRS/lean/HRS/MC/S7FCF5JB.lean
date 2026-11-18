import HRS.MC.S7FCF5F6a
import HRS.MC.S7FCW12E

/-!
# Proof of F6b (`fcf5_F6b_toL2_moment`): `L^q` bound of the `L²_t E_r` norm of `ℬ_N^{a+·}`

Route.  Let `Fp` be the jointly measurable modification of `t ↦ ℬ_N^{a+t}(ω)` on `[0,T]` (Carathéodory,
`s7fcw12_caratheodory`, and the centring with the Bochner mean, as in `s7fcw12_centred_aemeasurable`); it agrees with
`quadFieldAt` off a fixed null set, so `toL2` is unchanged.  For `q' = max q 3 > 2`:

* `‖toL2 Z‖ₑ² ≤ ∫⁻_{[0,T]} ‖Z t‖ₑ²` for every path `Z` (junk `0` only lowers the norm);
* Jensen-Hölder in `t` on `μ = vol|_{[0,T]}`: `(∫⁻ K)^p ≤ μ(univ)^{p-1} ∫⁻ K^p` with `p = q'/2 > 1`;
* Tonelli (`lintegral_lintegral_swap`) and F6a at the times `a + t ≥ 0` (its constant does not depend on `a`, `t`, `N`,
  the realisation), giving `∫⁻_ω ‖toL2‖ₑ^{q'} ≤ T^{p-1} · C₀ · T`;
* `x^q ≤ 1 + x^{q'}` transfers the bound to `q`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCF5J

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.FCF5Plan

variable {d : ℕ}

/-! ## Elementary helpers -/

theorem S7FCF5J_pow_two (x : ℝ≥0∞) (q : ℝ) : (x ^ (2 : ℝ)) ^ (q / 2) = x ^ q := by
  rw [← ENNReal.rpow_mul]
  congr 1
  ring

/-- The `L²(0,T)`-norm of `toL2` is at most the lintegral (the junk value `0` only lowers the norm). -/
theorem S7FCF5J_toL2_enorm_rpow_le (r T : ℝ) (Z : ℝ → NegSobolev d r) :
    ‖HRS.Sec7.toL2 r T Z‖ₑ ^ (2 : ℝ) ≤ ∫⁻ t in Set.Icc (0 : ℝ) T, ‖Z t‖ₑ ^ (2 : ℝ) := by
  unfold HRS.Sec7.toL2
  by_cases h : MemLp Z 2 (volume.restrict (Set.Icc (0 : ℝ) T))
  · rw [dif_pos h, Lp.enorm_def, eLpNorm_congr_ae (MemLp.coeFn_toLp h),
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) ENNReal.ofNat_ne_top h.aestronglyMeasurable,
      ← ENNReal.rpow_mul]
    norm_num
  · rw [dif_neg h]
    simp

/-- Jensen-Hölder on an arbitrary measure: `(∫⁻ K)^p ≤ μ(univ)^{p-1} ∫⁻ K^p` for `p > 1`. -/
theorem S7FCF5J_jensen_gen {α : Type*} [MeasurableSpace α] (μ : Measure α) {K : α → ℝ≥0∞} (hK : Measurable K)
    {p : ℝ} (hp : 1 < p) :
    (∫⁻ a, K a ∂μ) ^ p ≤ μ Set.univ ^ (p - 1) * ∫⁻ a, K a ^ p ∂μ := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hpq : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent hp
  have hinv := hpq.inv_add_inv_eq_one
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hK.aemeasurable
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul] at hh
  have hexp : (1 / Real.conjExponent p) * p = p - 1 := by
    have h1 : (1 / Real.conjExponent p) = 1 - p⁻¹ := by
      rw [one_div]
      linarith [hinv]
    rw [h1, sub_mul, one_mul, inv_mul_cancel₀ hp0.ne']
  calc (∫⁻ a, K a ∂μ) ^ p
      ≤ ((∫⁻ a, K a ^ p ∂μ) ^ (1 / p) * μ Set.univ ^ (1 / Real.conjExponent p)) ^ p :=
        ENNReal.rpow_le_rpow hh hp0.le
    _ = ((∫⁻ a, K a ^ p ∂μ) ^ (1 / p)) ^ p * (μ Set.univ ^ (1 / Real.conjExponent p)) ^ p :=
        ENNReal.mul_rpow_of_nonneg _ _ hp0.le
    _ = μ Set.univ ^ (p - 1) * ∫⁻ a, K a ^ p ∂μ := by
        rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hexp, one_div_mul_cancel hp0.ne', ENNReal.rpow_one,
          mul_comm]

/-! ## The Carathéodory modification of the centred quadratic field -/

theorem S7FCF5J_joint_modif (R : Regime d) (r : ℝ) (a T : ℝ) (hT : 0 < T) (ha : 0 ≤ a)
    {Ω : Type} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → Config d N) (hadapt : ∀ t : ℝ≥0, Measurable (X t))
    (hcont : ∀ᵐ ω ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ω i) :
    ∃ Fp : ℝ → Ω → NegSobolev d r, Measurable (Function.uncurry Fp) ∧
      ∃ N0 : Set Ω, MeasurableSet N0 ∧ P N0 = 0 ∧
        ∀ ω ∉ N0, ∀ t ∈ Set.Icc (0 : ℝ) T,
          Fp t ω = quadFieldAt r R.D.s (fun t => withDensityReal (R.ρ t)) P X (a + t) ω := by
  have hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => X (a + t).toNNReal ω) (Set.Icc 0 T) :=
    hcont.mono fun ω hω =>
      (continuous_pi fun i => (hω i).comp
        (continuous_real_toNNReal.comp (continuous_const.add continuous_id))).continuousOn
  have hfq : Measurable fun q : ℝ × Config d N => ((a + q.1, q.2) : ℝ × Config d N) :=
    (measurable_const.add measurable_fst).prodMk measurable_snd
  -- the integrand, made opaque so that no unifier unfolds the particle field
  obtain ⟨Psi, hPsi_def⟩ : ∃ Psi : ℝ × Config d N → NegSobolev d r, Psi = fun q =>
      quadFieldTilde r R.D.s (withDensityReal fun y => HRS.MC.Sec7.S7FCW12.s7fcw12_rhoPos R (a + q.1, y)) q.2 :=
    ⟨_, rfl⟩
  have hPsi : Measurable Psi := by
    have key := (HRS.MC.Sec7.S7FCW12.s7fcw12_quadTilde_measurable R r (N := N)).comp hfq
    rw [hPsi_def]
    exact key
  obtain ⟨V, hVm, N0, hN0m, hN0, hVN⟩ := HRS.MC.Sec7.S7FCW12.s7fcw12_caratheodory P hT.le
    (fun t ω => X (a + t).toNNReal ω) (fun t => hadapt _) hc (fun _ => 0)
  obtain ⟨G, hG_def⟩ : ∃ G : ℝ × Ω → NegSobolev d r, G = fun q => Psi (q.1, V q.1 q.2) := ⟨_, rfl⟩
  have hGm : Measurable G := by
    rw [hG_def]
    exact hPsi.comp (measurable_fst.prodMk hVm)
  obtain ⟨M, hM_def⟩ : ∃ M : ℝ → NegSobolev d r, M = fun t => ∫ ω', G (t, ω') ∂P := ⟨_, rfl⟩
  have hMm : Measurable M := by
    rw [hM_def]
    exact (hGm.stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  refine ⟨fun t ω => G (t, ω) - M t, ?_, N0, hN0m, hN0, ?_⟩
  · show Measurable fun q : ℝ × Ω => G (q.1, q.2) - M q.1
    exact (hGm.comp (measurable_fst.prodMk measurable_snd)).sub (hMm.comp measurable_fst)
  intro ω hω t ht
  have hμ : withDensityReal (R.ρ (a + t)) =
      withDensityReal fun y => HRS.MC.Sec7.S7FCW12.s7fcw12_rhoPos R (a + t, y) := by
    congr 1
    funext y
    rw [HRS.MC.Sec7.S7FCW12.s7fcw12_rhoPos_eq R (add_nonneg ha ht.1) y]
  have hint : ∫ ω', G (t, ω') ∂P = ∫ ω', Psi (t, X (a + t).toNNReal ω') ∂P := by
    apply integral_congr_ae
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω' hω'
    rw [hG_def]
    show Psi (t, V t ω') = _
    rw [hVN ω' hω' t ht]
  have hVω : G (t, ω) = Psi (t, X (a + t).toNNReal ω) := by
    rw [hG_def]
    show Psi (t, V t ω) = _
    rw [hVN ω hω t ht]
  show G (t, ω) - M t = _
  rw [hM_def]
  show G (t, ω) - ∫ ω', G (t, ω') ∂P = _
  rw [hint, hVω]
  simp only [quadFieldAt, hμ, hPsi_def]

/-! ## Tonelli and the moment bound for the exponent `q > 2` -/

theorem S7FCF5J_main {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (r T q : ℝ)
    (hq : 2 < q) (Fp : ℝ → Ω → NegSobolev d r) (hFp : Measurable (Function.uncurry Fp)) (C : ℝ) (hC : 0 ≤ C)
    (hbd : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫⁻ ω, ‖Fp t ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal C) (hT : 0 < T) :
    ∫⁻ ω, ‖HRS.Sec7.toL2 r T (fun t => Fp t ω)‖ₑ ^ q ∂P ≤
      ENNReal.ofReal (T ^ (q / 2 - 1) * (C * T)) := by
  set μT : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμT
  have hp : 1 < q / 2 := by linarith
  have hmu : μT Set.univ = ENNReal.ofReal T := by
    rw [hμT, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
  have hexp_nonneg : (0 : ℝ) ≤ q / 2 - 1 := by linarith
  have hF2 : ∀ ω, ‖HRS.Sec7.toL2 r T (fun t => Fp t ω)‖ₑ ^ q ≤
      μT Set.univ ^ (q / 2 - 1) * ∫⁻ t, ‖Fp t ω‖ₑ ^ q ∂μT := by
    intro ω
    have hK : Measurable fun t => ‖Fp t ω‖ₑ ^ (2 : ℝ) :=
      (hFp.comp (measurable_id.prodMk measurable_const)).enorm.pow_const _
    calc ‖HRS.Sec7.toL2 r T (fun t => Fp t ω)‖ₑ ^ q
        = (‖HRS.Sec7.toL2 r T (fun t => Fp t ω)‖ₑ ^ (2 : ℝ)) ^ (q / 2) := (S7FCF5J_pow_two _ q).symm
      _ ≤ (∫⁻ t in Set.Icc (0 : ℝ) T, ‖Fp t ω‖ₑ ^ (2 : ℝ)) ^ (q / 2) :=
          ENNReal.rpow_le_rpow (S7FCF5J_toL2_enorm_rpow_le r T _) (by linarith)
      _ ≤ μT Set.univ ^ (q / 2 - 1) * ∫⁻ t, (‖Fp t ω‖ₑ ^ (2 : ℝ)) ^ (q / 2) ∂μT :=
          S7FCF5J_jensen_gen μT hK hp
      _ = μT Set.univ ^ (q / 2 - 1) * ∫⁻ t, ‖Fp t ω‖ₑ ^ q ∂μT := by
          simp only [S7FCF5J_pow_two]
  have hTon : ∫⁻ ω, ∫⁻ t, ‖Fp t ω‖ₑ ^ q ∂μT ∂P = ∫⁻ t, ∫⁻ ω, ‖Fp t ω‖ₑ ^ q ∂P ∂μT := by
    apply lintegral_lintegral_swap
    exact ((hFp.comp measurable_swap).enorm.pow_const q).aemeasurable
  have hfin : μT Set.univ ^ (q / 2 - 1) ≠ ⊤ := by
    rw [hmu]
    exact ENNReal.rpow_ne_top_of_nonneg hexp_nonneg ENNReal.ofReal_ne_top
  have hslice : ∫⁻ t, ∫⁻ ω, ‖Fp t ω‖ₑ ^ q ∂P ∂μT ≤ ∫⁻ _t, ENNReal.ofReal C ∂μT := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hbd t ht
  calc ∫⁻ ω, ‖HRS.Sec7.toL2 r T (fun t => Fp t ω)‖ₑ ^ q ∂P
      ≤ ∫⁻ ω, μT Set.univ ^ (q / 2 - 1) * ∫⁻ t, ‖Fp t ω‖ₑ ^ q ∂μT ∂P := lintegral_mono hF2
    _ = μT Set.univ ^ (q / 2 - 1) * ∫⁻ ω, ∫⁻ t, ‖Fp t ω‖ₑ ^ q ∂μT ∂P :=
        lintegral_const_mul' _ _ hfin
    _ = μT Set.univ ^ (q / 2 - 1) * ∫⁻ t, ∫⁻ ω, ‖Fp t ω‖ₑ ^ q ∂P ∂μT := by rw [hTon]
    _ ≤ μT Set.univ ^ (q / 2 - 1) * ∫⁻ _t, ENNReal.ofReal C ∂μT :=
        mul_le_mul_of_nonneg_left hslice zero_le
    _ = ENNReal.ofReal (T ^ (q / 2 - 1)) * (ENNReal.ofReal C * ENNReal.ofReal T) := by
        rw [lintegral_const, hmu, ENNReal.ofReal_rpow_of_nonneg hT.le hexp_nonneg]
    _ = ENNReal.ofReal (T ^ (q / 2 - 1) * (C * T)) := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hT.le _), ENNReal.ofReal_mul hC]

/-! ## Assembly: F6b -/

theorem fcf5_F6b_toL2_moment_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T) (q : ℝ)
    (hq : 1 ≤ q) :
    ∃ C : ℝ, ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
      (X : ℝ≥0 → Ω → Config d N), FCPrepared R P X₀ W X →
        ∫⁻ ω, ‖(pairN r T a R.D.s R.ρ P X ω).2‖ₑ ^ q ∂P ≤ ENNReal.ofReal C := by
  have hq3 : (3 : ℝ) ≤ max q 3 := le_max_right _ _
  have hq0 : (0 : ℝ) ≤ q := by linarith
  obtain ⟨C0, hC0⟩ := HRS.MC.Sec7.S7FCF5F.fcf5_F6a_B_section_moment_proof R r hr (max q 3) (by linarith)
  refine ⟨1 + T ^ (max q 3 / 2 - 1) * (max C0 0 * T), ?_⟩
  intro a ha N hN Ω _ P _ X₀ W X hprep
  have hS := hprep.solution T
  obtain ⟨Fp, hFp, N0, hN0m, hN0, hkey⟩ :=
    S7FCF5J_joint_modif R r a T hT ha P X hS.adapted hS.cont
  have hbd : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫⁻ ω, ‖Fp t ω‖ₑ ^ (max q 3) ∂P ≤ ENNReal.ofReal (max C0 0) := by
    intro t ht
    have h1 : ∫⁻ ω, ‖Fp t ω‖ₑ ^ (max q 3) ∂P =
        ∫⁻ ω, ‖quadFieldAt r R.D.s (fun t => withDensityReal (R.ρ t)) P X (a + t) ω‖ₑ ^ (max q 3) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
      rw [hkey ω hω t ht]
    rw [h1]
    exact (hC0 N hN P X₀ W X hprep (a + t) (add_nonneg ha ht.1)).trans
      (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hmain := S7FCF5J_main P r T (max q 3) (by linarith) Fp hFp (max C0 0) (le_max_right _ _) hbd hT
  have hcongr : ∀ᵐ ω ∂P, HRS.Sec7.toL2 r T
      (fun t => quadFieldAt r R.D.s (fun t => withDensityReal (R.ρ t)) P X (a + t) ω) =
      HRS.Sec7.toL2 r T (fun t => Fp t ω) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
    exact HRS.MC.Sec7.S7FCW12.s7fcw12_toL2_congr r T _ _ fun t ht => (hkey ω hω t ht).symm
  have hpair : ∫⁻ ω, ‖(pairN r T a R.D.s R.ρ P X ω).2‖ₑ ^ q ∂P =
      ∫⁻ ω, ‖HRS.Sec7.toL2 r T (fun t => Fp t ω)‖ₑ ^ q ∂P := by
    apply lintegral_congr_ae
    filter_upwards [hcongr] with ω hω
    show ‖HRS.Sec7.toL2 r T
      (fun t => quadFieldAt r R.D.s (fun t => withDensityReal (R.ρ t)) P X (a + t) ω)‖ₑ ^ q = _
    rw [hω]
  have hKq : 0 ≤ T ^ (max q 3 / 2 - 1) * (max C0 0 * T) :=
    mul_nonneg (Real.rpow_nonneg hT.le _) (mul_nonneg (le_max_right _ _) hT.le)
  rw [hpair]
  calc ∫⁻ ω, ‖HRS.Sec7.toL2 r T (fun t => Fp t ω)‖ₑ ^ q ∂P
      ≤ ∫⁻ ω, (1 + ‖HRS.Sec7.toL2 r T (fun t => Fp t ω)‖ₑ ^ (max q 3)) ∂P :=
        lintegral_mono fun ω => HRS.MC.Sec7.S7FCF5F.S7FCF5F_rpow_le_one_add _ hq0 (le_max_left _ _)
    _ = 1 + ∫⁻ ω, ‖HRS.Sec7.toL2 r T (fun t => Fp t ω)‖ₑ ^ (max q 3) ∂P := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ 1 + ENNReal.ofReal (T ^ (max q 3 / 2 - 1) * (max C0 0 * T)) := add_le_add le_rfl hmain
    _ = ENNReal.ofReal (1 + T ^ (max q 3 / 2 - 1) * (max C0 0 * T)) := by
        rw [ENNReal.ofReal_add zero_le_one hKq, ENNReal.ofReal_one]

end HRS.MC.Sec7.S7FCF5J

end
