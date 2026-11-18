import HRS.MS.WrPressAux1

/-!
# HRS.MS.WrPressAux2 -- perturbed weak kernel and the generic pressure core (WR-8, part 2)

Packet WR-8 of `docs/SUPP_FOUND_PACKETS.md` (Track D), namespace `HRS.MS.Wr`.

* `wr8_gwd_congr`: kernels agreeing off the diagonal (atomless `μ`) have the same `GibbsWellDefined` status and
  the same Bochner normaliser.
* `wr8_ht`: the kernel `h` with its diagonal values set to `0` (`IsBoundedPairKernel` only bounds `h` off the
  diagonal); `wr8_qth`: the perturbation `q_θ(x,y) = q(x-y) - θ h̃(x,y) + |θ| D`.
* `wr8_conv_*`: row integrals of `f(x - ·)` against a density `ρ ≤ M`.
* `Wr8Split`: the data of a heat splitting `rieszKernel = q + P` off the origin (`q ≥ 0` small integrable,
  `P` the positive definite part with diagonal bound), used for both `s > 0` and `s = 0`.

Helper lemmas carry the prefix `wr8_`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

open HRS.Whole

variable {d N : ℕ}

/-! ### Congruence off the diagonal -/

theorem wr8_gwd_congr {μ : Measure (Euc d)} [IsProbabilityMeasure μ] (hμ : ∀ x, μ {x} = 0)
    {G K : Euc d → Euc d → ℝ} (hGK : ∀ x y, x ≠ y → K x y = G x y) {β : ℝ}
    (hG : GibbsWellDefined G N β μ) :
    GibbsWellDefined K N β μ ∧ pairNormalizer K N β μ = pairNormalizer G N β μ := by
  have hae : ∀ x, ∀ᵐ y ∂μ, K x y = G x y := fun x => by
    have : ∀ᵐ y ∂μ, y ≠ x := by
      rw [ae_iff]; simpa using hμ x
    filter_upwards [this] with y hy using hGK x y hy.symm
  have hdiag : ∀ᵐ p ∂(μ.prod μ), p.1 ≠ p.2 := by
    have h0 := diag_null_Euc hμ
    rw [ae_iff]
    simpa using h0
  have hEq : ∀ᵐ X ∂(Measure.pi fun _ : Fin N => μ), pairEnergy K X μ = pairEnergy G X μ := by
    filter_upwards [ae_injective_pi_Euc (N := N) hμ] with X hX
    exact pairEnergy_congr_offdiag hμ hGK X hX
  have hW : (fun X : EucConfig d N => Real.exp (-β * N * pairEnergy K X μ)) =ᵐ[Measure.pi fun _ : Fin N => μ]
      fun X => Real.exp (-β * N * pairEnergy G X μ) := by
    filter_upwards [hEq] with X hX
    rw [hX]
  have hnorm : pairNormalizer K N β μ = pairNormalizer G N β μ := integral_congr_ae hW
  refine ⟨⟨fun x => (hG.conv_integrable x).congr (hae x |>.mono fun y hy => hy.symm),
    hG.pair_integrable.congr ?_, hG.weight_integrable.congr hW.symm, hnorm ▸ hG.normalizer_pos⟩, hnorm⟩
  filter_upwards [hdiag] with p hp
  exact (hGK p.1 p.2 hp).symm

/-! ### The perturbed kernel -/

open Classical in
/-- `h` with the diagonal values replaced by `0`. -/
def wr8_ht (h : Euc d → Euc d → ℝ) (x y : Euc d) : ℝ := if x = y then 0 else h x y

theorem wr8_ht_of_ne {h : Euc d → Euc d → ℝ} {x y : Euc d} (hxy : x ≠ y) : wr8_ht h x y = h x y := by
  unfold wr8_ht; rw [if_neg hxy]

theorem wr8_ht_symm {h : Euc d → Euc d → ℝ} (hs : ∀ x y, h x y = h y x) (x y : Euc d) :
    wr8_ht h x y = wr8_ht h y x := by
  unfold wr8_ht
  by_cases hxy : x = y
  · subst hxy; rfl
  · rw [if_neg hxy, if_neg (Ne.symm hxy), hs]

theorem wr8_ht_meas {h : Euc d → Euc d → ℝ} (hm : Measurable fun p : Euc d × Euc d => h p.1 p.2) :
    Measurable (Function.uncurry (wr8_ht h)) := by
  classical
  have : Function.uncurry (wr8_ht h) = fun p : Euc d × Euc d => if p.1 = p.2 then 0 else h p.1 p.2 := by
    funext p; rfl
  rw [this]
  exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const hm

/-- The perturbed kernel `q_θ(x,y) = q(x-y) - θ h̃(x,y) + |θ| D`. -/
def wr8_qth (q : Euc d → ℝ) (h : Euc d → Euc d → ℝ) (θ D : ℝ) (x y : Euc d) : ℝ :=
  q (x - y) - θ * wr8_ht h x y + |θ| * D

section Kernel

variable {q : Euc d → ℝ} {h : Euc d → Euc d → ℝ} {B' D θ : ℝ}

theorem wr8_qth_nonneg (hq0 : ∀ z, 0 ≤ q z) (hbd : ∀ x y, |wr8_ht h x y| ≤ B' * q (x - y) + D)
    (hθB : |θ| * B' ≤ 1 / 2) (x y : Euc d) : 0 ≤ wr8_qth q h θ D x y := by
  unfold wr8_qth
  have h1 := hbd x y
  have h2 : |θ * wr8_ht h x y| ≤ |θ| * (B' * q (x - y) + D) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have h3 := le_abs_self (θ * wr8_ht h x y)
  have h4 := hq0 (x - y)
  have h5 : 0 ≤ q (x - y) * (1 - |θ| * B') := mul_nonneg h4 (by linarith)
  nlinarith [h5]

theorem wr8_qth_le (hq0 : ∀ z, 0 ≤ q z) (hbd : ∀ x y, |wr8_ht h x y| ≤ B' * q (x - y) + D)
    (x y : Euc d) :
    wr8_qth q h θ D x y ≤ (1 + |θ| * B') * q (x - y) + 2 * (|θ| * D) := by
  unfold wr8_qth
  have h1 := hbd x y
  have h2 : -(θ * wr8_ht h x y) ≤ |θ| * (B' * q (x - y) + D) := by
    calc -(θ * wr8_ht h x y) ≤ |θ * wr8_ht h x y| := neg_le_abs _
      _ = |θ| * |wr8_ht h x y| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  nlinarith

end Kernel

/-! ### Row integrals against a bounded density -/

theorem wr8_withDensity_le {ρ : Euc d → ℝ} {M0 : ℝ} (hρ : ∀ x, ρ x ≤ M0) :
    HRS.Whole.withDensityReal ρ ≤ ENNReal.ofReal M0 • (volume : Measure (Euc d)) := by
  unfold HRS.Whole.withDensityReal
  rw [← withDensity_const]
  exact withDensity_mono (Filter.Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (hρ x))

theorem wr8_conv_integrable {ρ : Euc d → ℝ} {M0 : ℝ} (hρ : ∀ x, ρ x ≤ M0) {f : Euc d → ℝ}
    (hf : Integrable f) (x : Euc d) : Integrable (fun y => f (x - y)) (HRS.Whole.withDensityReal ρ) :=
  ((hf.comp_sub_left x).smul_measure ENNReal.ofReal_ne_top).mono_measure (wr8_withDensity_le hρ)

theorem wr8_conv_le {ρ : Euc d → ℝ} {M0 : ℝ} (hρ : ∀ x, ρ x ≤ M0) (hM0 : 0 ≤ M0) {f : Euc d → ℝ}
    (hf : Integrable f) (hf0 : ∀ z, 0 ≤ f z) (x : Euc d) :
    ∫ y, f (x - y) ∂(HRS.Whole.withDensityReal ρ) ≤ M0 * ∫ z, f z := by
  have hfx : Integrable (fun y => f (x - y)) (volume : Measure (Euc d)) := hf.comp_sub_left x
  calc ∫ y, f (x - y) ∂(HRS.Whole.withDensityReal ρ)
      ≤ ∫ y, f (x - y) ∂(ENNReal.ofReal M0 • (volume : Measure (Euc d))) :=
        integral_mono_measure (wr8_withDensity_le hρ) (Filter.Eventually.of_forall fun y => hf0 _)
          (hfx.smul_measure ENNReal.ofReal_ne_top)
    _ = M0 * ∫ y, f (x - y) := by
        rw [integral_smul_measure, ENNReal.toReal_ofReal hM0, smul_eq_mul]
    _ = M0 * ∫ z, f z := by rw [integral_sub_left_eq_self f volume x]


theorem wr8_one_le_mul_deltaN {s : ℝ} (hs0 : 0 ≤ s) (N : ℕ) (hN : 1 ≤ N) :
    1 ≤ (N : ℝ) * deltaN d s N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  unfold deltaN
  split_ifs with h1 h2
  · rw [mul_inv_cancel₀ hNpos.ne']
  · rw [← mul_assoc, mul_inv_cancel₀ hNpos.ne', one_mul, Real.log_mul (Real.exp_pos _).ne' hNpos.ne',
      Real.log_exp]
    have := Real.log_nonneg hN1
    linarith
  · have hspos : 0 < s := by
      push Not at h1
      have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
      rcases lt_or_eq_of_le h1 with h | h
      · linarith
      · exact absurd h.symm h2
    have hs2 : (d : ℝ) / 2 < s := by
      push Not at h1
      exact lt_of_le_of_ne h1 (Ne.symm h2)
    have hds : (d : ℝ) / s ≤ 2 := by
      rw [div_le_iff₀ hspos]; linarith
    calc (1 : ℝ) ≤ (N : ℝ) ^ (2 - (d : ℝ) / s) := Real.one_le_rpow hN1 (by linarith)
      _ = (N : ℝ) * (N : ℝ) ^ (1 - (d : ℝ) / s) := by
          rw [show (2 - (d : ℝ) / s) = 1 + (1 - (d : ℝ) / s) by ring,
            Real.rpow_add hNpos, Real.rpow_one]

/-! ### Splitting data and the main step -/

/-- Data of a heat splitting `rieszKernel d s = q + P` off the origin: `q ≥ 0` even integrable with `∫ q ≤ ε`
and the envelope `q ≤ E0 (1 + W_s)`, `W_s ≤ q + Kw`; `P` the positive definite part (`Wr8Ok`, diagonal bound
`N F^P ≥ -κ/2`, `∬ P ≥ -m`) for every probability measure with the logarithmic moment if `s = 0`. -/
structure Wr8Split (d : ℕ) (s L E0 ε : ℝ) (q P : Euc d → ℝ) (Kw κ m : ℝ) : Prop where
  qm : Measurable q
  qe : ∀ z, q (-z) = q z
  q0 : ∀ z, 0 ≤ q z
  qint : Integrable q
  qε : ∫ z, q z ≤ ε
  split : ∀ z, z ≠ 0 → rieszKernel d s z = q z + P z
  env : ∀ z, z ≠ 0 → q z ≤ E0 * (1 + rieszWeight s z)
  wle : ∀ z, z ≠ 0 → rieszWeight s z ≤ q z + Kw
  Kw0 : 0 ≤ Kw
  Pok : ∀ (μ : Measure (Euc d)) [IsProbabilityMeasure μ], (s = 0 → HasLogMoment μ L) →
    Wr8Ok μ (fun x y => P (x - y))
  Plow : ∀ (μ : Measure (Euc d)) [IsProbabilityMeasure μ], (s = 0 → HasLogMoment μ L) →
    -m ≤ ∫ p : Euc d × Euc d, P (p.1 - p.2) ∂(μ.prod μ)
  Pdiag : ∀ (μ : Measure (Euc d)) [IsProbabilityMeasure μ], (s = 0 → HasLogMoment μ L) →
    ∀ N : ℕ, 1 ≤ N → ∀ X : EucConfig d N,
      -(κ / 2) ≤ (N : ℝ) * pairEnergy (fun x y => P (x - y)) X μ

set_option maxHeartbeats 1600000 in
/-- The main step of Proposition S3.1 for fixed constants (all constants chosen before `ρ, h, N, b, θ`). -/
theorem wr8_main (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s)
    {M L bm bp B E0 ε Kw κ m a0 Cw θ0 B' D M0 C : ℝ} {q P : Euc d → ℝ}
    (hbm : 0 < bm) (hS : Wr8Split d s L E0 ε q P Kw κ m)
    (hM0 : 0 ≤ M0) (hMM0 : M ≤ M0) (hB' : 0 ≤ B') (hBB' : B ≤ B') (hE0 : 0 ≤ E0)
    (hDdef : D = B' * (1 + Kw)) (ha0 : 0 < a0)
    (hθ1 : θ0 ≤ 1) (hθB : θ0 * B' ≤ 1 / 2) (hθD : θ0 * D ≤ 1) (hθD2 : 2 * (θ0 * D) ≤ a0 / 4)
    (hMε : 3 / 2 * (M0 * ε) ≤ a0 / 4) (hC : |bp| * (|κ| + |m| + 1) / 2 + |Cw| ≤ C)
    (hweak : ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ qq : Euc d → Euc d → ℝ, Measurable (Function.uncurry qq) → (∀ x y, qq x y = qq y x) →
        (∀ x y, 0 ≤ qq x y) →
        (∀ x y, x ≠ y → qq x y ≤ (E0 + B' + 1) * (1 + rieszWeight s (x - y))) →
      ∀ a : ℝ, 0 ≤ a → a < a0 →
        (∀ x, ∫⁻ y, ENNReal.ofReal (qq x y) ∂(HRS.Whole.withDensityReal ρ) ≤ ENNReal.ofReal a) →
      ∀ N : ℕ, 2 ≤ N → ∀ β ∈ Set.Icc bm bp,
        GibbsWellDefined qq N β (HRS.Whole.withDensityReal ρ) ∧
        Real.exp (-(Cw * N * deltaN d s N)) ≤ pairNormalizer qq N β (HRS.Whole.withDensityReal ρ) ∧
        pairNormalizer qq N β (HRS.Whole.withDensityReal ρ) ≤ Real.exp (Cw * N * deltaN d s N) ∧
        |Real.log (pairNormalizer qq N β (HRS.Whole.withDensityReal ρ))| ≤ Cw * N * deltaN d s N) :
    ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      (s = 0 → HasLogMoment (HRS.Whole.withDensityReal ρ) L) →
      ∀ h : Euc d → Euc d → ℝ, IsBoundedPairKernel s B h →
      ∀ N, 2 ≤ N → ∀ b ∈ Set.Icc bm bp, ∀ θ : ℝ, |θ| ≤ θ0 →
        GibbsWellDefined (fun x y => rieszKernel d s (x - y) - θ * h x y) N b (HRS.Whole.withDensityReal ρ) ∧
        |Real.log (pairNormalizer (fun x y => rieszKernel d s (x - y) - θ * h x y) N b
          (HRS.Whole.withDensityReal ρ))| ≤ C * N * deltaN d s N := by
  intro ρ hρ hρM hlog h hh N hN b hb θ hθ
  have hd1 : 1 ≤ d := by omega
  have hN1 : 1 ≤ N := by omega
  haveI hμprob : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := Q34.isProbabilityMeasure_nu hρ
  haveI hnull : NullSingletonClass (HRS.Whole.withDensityReal ρ) := Q34.noAtoms_nu (ρ := ρ) hd1
  have hμ0 : ∀ x, HRS.Whole.withDensityReal ρ {x} = 0 := fun x => measure_singleton x
  set μ : Measure (Euc d) := HRS.Whole.withDensityReal ρ with hμdef
  have hρM0 : ∀ x, ρ x ≤ M0 := fun x => (hρM x).trans hMM0
  have hb0 : 0 ≤ b := (hbm.trans_le hb.1).le
  have hθB' : |θ| * B' ≤ 1 / 2 := (mul_le_mul_of_nonneg_right hθ hB').trans hθB
  have hθD' : |θ| * D ≤ 1 := (mul_le_mul_of_nonneg_right hθ (by rw [hDdef]; have := hS.Kw0; positivity)).trans hθD
  have hD0 : 0 ≤ D := by rw [hDdef]; have := hS.Kw0; positivity
  have hθ' : |θ| ≤ 1 := hθ.trans hθ1
  -- envelope of `h`
  have hhb : ∀ x y, x ≠ y → |h x y| ≤ B' * q (x - y) + D := by
    intro x y hxy
    have h1 := hh.bound x y hxy
    have hW0 : 0 ≤ rieszWeight s (x - y) := wr3_rieszWeight_nonneg s _
    have h2 := hS.wle (x - y) (sub_ne_zero.2 hxy)
    have h3 : B * (1 + rieszWeight s (x - y)) ≤ B' * (1 + rieszWeight s (x - y)) :=
      mul_le_mul_of_nonneg_right hBB' (by linarith)
    have h4 : B' * (1 + rieszWeight s (x - y)) ≤ B' * (1 + (q (x - y) + Kw)) :=
      mul_le_mul_of_nonneg_left (by linarith) hB'
    rw [hDdef]; nlinarith
  have hbd : ∀ x y, |wr8_ht h x y| ≤ B' * q (x - y) + D := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      have : wr8_ht h x x = 0 := by unfold wr8_ht; simp
      rw [this, abs_zero]
      exact add_nonneg (mul_nonneg hB' (hS.q0 _)) hD0
    · rw [wr8_ht_of_ne hxy]; exact hhb x y hxy
  set qθ : Euc d → Euc d → ℝ := wr8_qth q h θ D with hqθdef
  have hqθ0 : ∀ x y, 0 ≤ qθ x y := wr8_qth_nonneg hS.q0 hbd hθB'
  have hqθs : ∀ x y, qθ x y = qθ y x := by
    intro x y
    simp only [hqθdef, wr8_qth]
    rw [wr8_ht_symm hh.symm x y, show x - y = -(y - x) from (neg_sub y x).symm, hS.qe]
  have hqθm : Measurable (Function.uncurry qθ) := by
    have h1 : Measurable (Function.uncurry (wr8_ht h)) := wr8_ht_meas hh.measurable
    have : Function.uncurry qθ = fun p : Euc d × Euc d =>
        q (p.1 - p.2) - θ * Function.uncurry (wr8_ht h) p + |θ| * D := rfl
    rw [this]
    exact ((hS.qm.comp (measurable_fst.sub measurable_snd)).sub (measurable_const.mul h1)).add
      measurable_const
  have hqθA : ∀ x y, x ≠ y → qθ x y ≤ (E0 + B' + 1) * (1 + rieszWeight s (x - y)) := by
    intro x y hxy
    have h1 := hS.env (x - y) (sub_ne_zero.2 hxy)
    have h2 := hhb x y hxy
    have hW0 : 0 ≤ rieszWeight s (x - y) := wr3_rieszWeight_nonneg s _
    have h3 := hS.wle (x - y) (sub_ne_zero.2 hxy)
    have h4 : |θ * h x y| ≤ B' * (1 + rieszWeight s (x - y)) := by
      have hh' := hh.bound x y hxy
      have : |h x y| ≤ B' * (1 + rieszWeight s (x - y)) :=
        hh'.trans (mul_le_mul_of_nonneg_right hBB' (by linarith))
      rw [abs_mul]
      calc |θ| * |h x y| ≤ 1 * |h x y| := mul_le_mul_of_nonneg_right hθ' (abs_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact this
    have h5 := neg_abs_le (θ * h x y)
    have : qθ x y = q (x - y) - θ * h x y + |θ| * D := by
      simp only [hqθdef, wr8_qth]; rw [wr8_ht_of_ne hxy]
    rw [this]
    nlinarith
  -- row integrability and row bound
  have hqrow : ∀ x, Integrable (fun y => q (x - y)) μ := fun x => wr8_conv_integrable hρM0 hS.qint x
  have hhrow : ∀ x, Integrable (fun y => wr8_ht h x y) μ := by
    intro x
    have hm : Measurable (fun y => wr8_ht h x y) :=
      (wr8_ht_meas hh.measurable).comp (measurable_const.prodMk measurable_id)
    refine Integrable.mono' (((hqrow x).const_mul B').add (integrable_const D)) hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    exact hbd x y
  have hqθrow : ∀ x, Integrable (fun y => qθ x y) μ := by
    intro x
    have : (fun y => qθ x y) = fun y => q (x - y) - θ * wr8_ht h x y + |θ| * D := rfl
    rw [this]
    exact ((hqrow x).sub ((hhrow x).const_mul θ)).add (integrable_const _)
  have hrow : ∀ x, ∫⁻ y, ENNReal.ofReal (qθ x y) ∂μ ≤ ENNReal.ofReal (a0 / 2) := by
    intro x
    rw [← ofReal_integral_eq_lintegral_ofReal (hqθrow x) (Filter.Eventually.of_forall fun y => hqθ0 x y)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : ∫ y, qθ x y ∂μ ≤ ∫ y, ((1 + |θ| * B') * q (x - y) + 2 * (|θ| * D)) ∂μ :=
      integral_mono (hqθrow x) (((hqrow x).const_mul _).add (integrable_const _))
        (fun y => wr8_qth_le hS.q0 hbd x y)
    have h2 : ∫ y, ((1 + |θ| * B') * q (x - y) + 2 * (|θ| * D)) ∂μ =
        (1 + |θ| * B') * ∫ y, q (x - y) ∂μ + 2 * (|θ| * D) := by
      rw [integral_add ((hqrow x).const_mul _) (integrable_const _), integral_const_mul]
      simp [Measure.real]
    have h3 := wr8_conv_le hρM0 hM0 hS.qint hS.q0 x
    have h4 : ∫ y, q (x - y) ∂μ ≤ M0 * ε :=
      h3.trans (mul_le_mul_of_nonneg_left hS.qε hM0)
    have h5 : 0 ≤ ∫ y, q (x - y) ∂μ := integral_nonneg fun y => hS.q0 _
    have h6 : (1 + |θ| * B') ≤ 3 / 2 := by linarith
    have h7 : 2 * (|θ| * D) ≤ 2 * (θ0 * D) := by
      have : |θ| * D ≤ θ0 * D := mul_le_mul_of_nonneg_right hθ (by rw [hDdef]; have := hS.Kw0; positivity)
      linarith
    nlinarith [mul_le_mul h6 h4 h5 (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  -- weak reference bound for `q_θ`
  have hweak' := hweak ρ hρ hρM qθ hqθm hqθs hqθ0 hqθA (a0 / 2) (by positivity) (by linarith) hrow N hN b hb
  have hK : EWeakKernel μ (a0 / 2) qθ := ⟨hqθm, hqθs, hqθ0, hrow⟩
  obtain ⟨hqW, hqlo, hqup, -⟩ := hweak'
  -- abstract pressure lemma
  have hc' : 0 ≤ |θ| * D := mul_nonneg (abs_nonneg _) hD0
  obtain ⟨hGW, hGlo, hGup⟩ := wr8_pressure_abstract (N := N) (μ := μ) (P := fun x y => P (x - y)) (q := qθ)
    (κ := κ) (m := m) (c' := |θ| * D) (β := b) (hS.Pok μ hlog) hK (by positivity) hc' hN1 hb0
    (hS.Pdiag μ hlog N hN1) (hS.Plow μ hlog)
  -- transfer to the original kernel
  have hoff : ∀ x y, x ≠ y → (rieszKernel d s (x - y) - θ * h x y) =
      (P (x - y) + qθ x y) + (-(|θ| * D)) := by
    intro x y hxy
    have h1 := hS.split (x - y) (sub_ne_zero.2 hxy)
    simp only [hqθdef, wr8_qth]
    rw [wr8_ht_of_ne hxy, h1]; ring
  obtain ⟨hGW', hnorm⟩ := wr8_gwd_congr (N := N) hμ0 hoff hGW
  refine ⟨hGW', ?_⟩
  rw [hnorm]
  -- the real-logarithm bound
  have hδ : 1 ≤ (N : ℝ) * deltaN d s N := wr8_one_le_mul_deltaN hs0 N hN1
  have hKpos : 0 < pairNormalizer (fun x y => (P (x - y) + qθ x y) + (-(|θ| * D))) N b μ :=
    hGW.normalizer_pos
  set KG := pairNormalizer (fun x y => (P (x - y) + qθ x y) + (-(|θ| * D))) N b μ with hKG
  have hCnn : 0 ≤ C := le_trans (by positivity) hC
  have hb' : b ≤ |bp| := hb.2.trans (le_abs_self _)
  have hCw1 : Cw * N * deltaN d s N ≤ |Cw| * ((N : ℝ) * deltaN d s N) := by
    have : Cw * N * deltaN d s N = Cw * ((N : ℝ) * deltaN d s N) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
  have hupper : Real.log KG ≤ C * N * deltaN d s N := by
    have h1 : KG ≤ Real.exp (b * κ / 2 + Cw * N * deltaN d s N) := by
      rw [Real.exp_add]
      exact hGup.trans (mul_le_mul_of_nonneg_left hqup (Real.exp_pos _).le)
    have h2 := (Real.log_le_log hKpos h1).trans_eq (Real.log_exp _)
    have h3 : b * κ / 2 ≤ |bp| * (|κ| + |m| + 1) / 2 := by
      have : b * κ ≤ |bp| * |κ| := by
        calc b * κ ≤ |b * κ| := le_abs_self _
          _ = |b| * |κ| := abs_mul _ _
          _ ≤ |bp| * |κ| := mul_le_mul_of_nonneg_right
              ((abs_of_nonneg hb0).le.trans hb') (abs_nonneg _)
      nlinarith [abs_nonneg κ, abs_nonneg m, abs_nonneg bp]
    have h4 : (|bp| * (|κ| + |m| + 1) / 2 + |Cw|) * 1 ≤
        (|bp| * (|κ| + |m| + 1) / 2 + |Cw|) * ((N : ℝ) * deltaN d s N) :=
      mul_le_mul_of_nonneg_left hδ (by positivity)
    have h5 : C * 1 ≤ C * ((N : ℝ) * deltaN d s N) := mul_le_mul_of_nonneg_left hδ hCnn
    have h6 : C * N * deltaN d s N = C * ((N : ℝ) * deltaN d s N) := by ring
    have h7 : (|bp| * (|κ| + |m| + 1) / 2 + |Cw|) * ((N : ℝ) * deltaN d s N) ≤
        C * ((N : ℝ) * deltaN d s N) := mul_le_mul_of_nonneg_right hC (by linarith)
    have hT0 : 0 ≤ |bp| * (|κ| + |m| + 1) / 2 := by positivity
    have h8 : |bp| * (|κ| + |m| + 1) / 2 ≤ |bp| * (|κ| + |m| + 1) / 2 * ((N : ℝ) * deltaN d s N) := by
      nlinarith
    nlinarith
  have hlower : -(C * N * deltaN d s N) ≤ Real.log KG := by
    have h1 : -(b * (m + |θ| * D) / 2) ≤ Real.log KG := by
      have := Real.log_le_log (Real.exp_pos _) hGlo
      rwa [Real.log_exp] at this
    have h2 : b * (m + |θ| * D) / 2 ≤ |bp| * (|κ| + |m| + 1) / 2 := by
      have : b * (m + |θ| * D) ≤ |bp| * (|m| + 1) := by
        calc b * (m + |θ| * D) ≤ |b * (m + |θ| * D)| := le_abs_self _
          _ = |b| * |m + |θ| * D| := abs_mul _ _
          _ ≤ |bp| * (|m| + 1) := by
              refine mul_le_mul ((abs_of_nonneg hb0).le.trans hb') ?_ (abs_nonneg _) (abs_nonneg _)
              calc |m + |θ| * D| ≤ |m| + |(|θ| * D)| := abs_add_le _ _
                _ ≤ |m| + 1 := by rw [abs_of_nonneg hc']; linarith
      nlinarith [abs_nonneg κ, abs_nonneg m, abs_nonneg bp]
    have h4 : (|bp| * (|κ| + |m| + 1) / 2 + |Cw|) * 1 ≤
        (|bp| * (|κ| + |m| + 1) / 2 + |Cw|) * ((N : ℝ) * deltaN d s N) :=
      mul_le_mul_of_nonneg_left hδ (by positivity)
    have h6 : C * N * deltaN d s N = C * ((N : ℝ) * deltaN d s N) := by ring
    have h7 : (|bp| * (|κ| + |m| + 1) / 2 + |Cw|) * ((N : ℝ) * deltaN d s N) ≤
        C * ((N : ℝ) * deltaN d s N) := mul_le_mul_of_nonneg_right hC (by linarith)
    have hT0 : 0 ≤ |bp| * (|κ| + |m| + 1) / 2 := by positivity
    have h8 : |bp| * (|κ| + |m| + 1) / 2 ≤ |bp| * (|κ| + |m| + 1) / 2 * ((N : ℝ) * deltaN d s N) := by
      nlinarith
    have h9 : |Cw| ≤ |Cw| * ((N : ℝ) * deltaN d s N) := by nlinarith [abs_nonneg Cw]
    nlinarith [abs_nonneg Cw]
  rw [abs_le]
  exact ⟨hlower, hupper⟩


/-- **Generic pressure core.**  Given a family of splitting data for every `ε > 0` (with the envelope constant
`E0` independent of `ε`), the conclusion of `euclidean_pressure` holds.  Constant order: `A → (a₀, C_w) → ε
→ splitting → D → θ₀ → C`. -/
theorem wr8_core (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M L bm bp B E0 : ℝ)
    (hbm : 0 < bm) (hE0 : 0 ≤ E0)
    (fam : ∀ ε : ℝ, 0 < ε → ∃ (q P : Euc d → ℝ) (Kw κ m : ℝ), Wr8Split d s L E0 ε q P Kw κ m) :
    ∃ θ₀ > 0, ∃ C : ℝ, ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      (s = 0 → HasLogMoment (HRS.Whole.withDensityReal ρ) L) →
      ∀ h : Euc d → Euc d → ℝ, IsBoundedPairKernel s B h →
      ∀ N, 2 ≤ N → ∀ b ∈ Set.Icc bm bp, ∀ θ : ℝ, |θ| ≤ θ₀ →
        GibbsWellDefined (fun x y => rieszKernel d s (x - y) - θ * h x y) N b
          (HRS.Whole.withDensityReal ρ) ∧
        |Real.log (pairNormalizer (fun x y => rieszKernel d s (x - y) - θ * h x y) N b
          (HRS.Whole.withDensityReal ρ))| ≤ C * N * deltaN d s N := by
  obtain ⟨B', hB'def⟩ : ∃ B' : ℝ, B' = max B 0 := ⟨_, rfl⟩
  have hB' : 0 ≤ B' := by rw [hB'def]; exact le_max_right _ _
  have hBB' : B ≤ B' := by rw [hB'def]; exact le_max_left _ _
  obtain ⟨a0, Cw, ha0, -, hW⟩ := weak_reference_pressure_pairNormalizer_E (by omega : 1 ≤ d) s hs0 hsd bm bp
    hbm M (E0 + B' + 1)
  obtain ⟨M0, hM0def⟩ : ∃ M0 : ℝ, M0 = max M 0 := ⟨_, rfl⟩
  have hM0 : 0 ≤ M0 := by rw [hM0def]; exact le_max_right _ _
  have hMM0 : M ≤ M0 := by rw [hM0def]; exact le_max_left _ _
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = a0 / (8 * (M0 + 1)) := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; positivity
  obtain ⟨q, P, Kw, κ, m, hS⟩ := fam ε hε
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = B' * (1 + Kw) := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hDdef]; have := hS.Kw0; positivity
  obtain ⟨θ0, hθ0def⟩ : ∃ θ0 : ℝ, θ0 = min 1 (min (1 / (2 * B' + 1))
      (min (1 / (D + 1)) (a0 / (8 * (D + 1))))) := ⟨_, rfl⟩
  have hθ0pos : 0 < θ0 := by
    rw [hθ0def]
    exact lt_min one_pos (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hθ1 : θ0 ≤ 1 := by rw [hθ0def]; exact min_le_left _ _
  have hθB : θ0 * B' ≤ 1 / 2 := by
    have : θ0 ≤ 1 / (2 * B' + 1) := by
      rw [hθ0def]; exact (min_le_right _ _).trans (min_le_left _ _)
    calc θ0 * B' ≤ (1 / (2 * B' + 1)) * B' := mul_le_mul_of_nonneg_right this hB'
      _ ≤ 1 / 2 := by
          rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  have hθD : θ0 * D ≤ 1 := by
    have : θ0 ≤ 1 / (D + 1) := by
      rw [hθ0def]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    calc θ0 * D ≤ (1 / (D + 1)) * D := mul_le_mul_of_nonneg_right this hD0
      _ ≤ 1 := by
          rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
          linarith
  have hθD2 : 2 * (θ0 * D) ≤ a0 / 4 := by
    have : θ0 ≤ a0 / (8 * (D + 1)) := by
      rw [hθ0def]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    calc 2 * (θ0 * D) ≤ 2 * ((a0 / (8 * (D + 1))) * D) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this hD0) (by norm_num)
      _ ≤ 2 * ((a0 / (8 * (D + 1))) * (D + 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) (by norm_num)
      _ = a0 / 4 := by field_simp; ring
  have hMε : 3 / 2 * (M0 * ε) ≤ a0 / 4 := by
    have : M0 * ε ≤ a0 / 8 := by
      rw [hεdef]
      calc M0 * (a0 / (8 * (M0 + 1))) = a0 / 8 * (M0 / (M0 + 1)) := by field_simp
        _ ≤ a0 / 8 * 1 := mul_le_mul_of_nonneg_left (by rw [div_le_one (by positivity)]; linarith) (by positivity)
        _ = a0 / 8 := mul_one _
    linarith
  refine ⟨θ0, hθ0pos, |bp| * (|κ| + |m| + 1) / 2 + |Cw|, ?_⟩
  exact wr8_main hd hs0 hbm hS hM0 hMM0 hB' hBB' hE0 hDdef ha0 hθ1 hθB hθD hθD2 hMε le_rfl hW

end HRS.MS.Wr
