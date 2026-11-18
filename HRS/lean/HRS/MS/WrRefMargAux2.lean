import HRS.MS.WrRefMargAux1

/-!
# HRS.MS.WrRefMargAux2 -- calibrated reference marginal, part 2: cavity correction and comparisons (WR-13e)

Packet WR-13e (T11 of `docs/WR_B_PLAN.md`), second helper file.  Euclidean port of
`HRS/Equilibrium/ReferenceMarginal.lean` lines 1496-1667 (`cavD_torus`), 1813-2019 (`cavity_equation`),
2135-2290 (`event_pi_nu`, `cv_identity`), 2824-2923 (`field_event_comparison`, `tv_RN_R0`),
3062-3124 and 1341-1467 (`absorption`).

* `wr13e_cavD`: the cavity correction `D = log u + λ n ∫ q dν` satisfies `0 ≤ D ≤ C δ_N` pointwise, for every
  weak potential `V` with kernel `q_τ(x-y)`; the torus weak-`L^p` second-moment/tail estimates are replaced by
  the row bounds `wr3_row_bounds_real_integral` of `WrRowAux3` (level-set bounds at the levels `N` and `N/P`);
* `wr13e_cavity_equation`: the exact cavity equation `log θ + β K_g(θ - 1) = D + β (q*θ - q*ν) + λ q*ν + c`;
* `wr13e_event_pi_nu`, `wr13e_tv_RN_R0`: `|π_N(A) - ν_n(A)| ≤ κ/N` and the comparison with `R0`;
* `wr13e_absorption`: `‖θ - 1‖₂ ≤ C ‖Φ‖₂` from `K_g ≥ 0` (here `⟨K_g z, z⟩ ≥ 0` is a hypothesis).

All constants are uniform in `β ∈ (0, βp]` (monotone replacement `β ↦ βp`).
Helper lemmas carry the prefix `wr13e_`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

open HRS.External HRS.MS.Psd

variable {d : ℕ}

/-! ### Elementary facts on `qTau` -/

theorem wr13e_g_eq_weight {s : ℝ} (hs : 0 < s) (z : Euc d) :
    HRS.Whole.rieszKernel d s z = HRS.Whole.rieszWeight s z := by
  rw [HRS.Whole.Q34.rieszKernel_eq hs.ne']
  simp [HRS.Whole.rieszWeight, hs.ne']

theorem wr13e_qTau_le_g {s : ℝ} (hs : 0 < s) {τ : ℝ} (hτ : 0 < τ) {z : Euc d} (hz : z ≠ 0) :
    qTau d s τ z ≤ HRS.Whole.rieszKernel d s z := by
  rw [riesz_heat_split hs hτ hz]
  have := kTau_nonneg hs hτ z
  linarith

theorem wr13e_qTau_envelope {s : ℝ} (hs : 0 < s) {τ : ℝ} (hτ : 0 < τ) {z : Euc d} (hz : z ≠ 0) :
    qTau d s τ z ≤ 1 * (1 + HRS.Whole.rieszWeight s z) := by
  have h1 := wr13e_qTau_le_g hs hτ hz
  rw [wr13e_g_eq_weight hs] at h1
  have := wr3_rieszWeight_nonneg (d := d) s z
  linarith

/-! ### Integrals against a measure dominated by `C μ` -/

theorem wr13e_integral_le_of_le_smul {α : Type*} [MeasurableSpace α] {ν μ : Measure α} {C : ℝ}
    (hν : ν ≤ ENNReal.ofReal C • μ) (hC : 0 ≤ C) {f : α → ℝ} (hf0 : ∀ y, 0 ≤ f y)
    (hfi : Integrable f μ) : ∫ y, f y ∂ν ≤ C * ∫ y, f y ∂μ := by
  have h1 : Integrable f (ENNReal.ofReal C • μ) := hfi.smul_measure ENNReal.ofReal_ne_top
  calc ∫ y, f y ∂ν ≤ ∫ y, f y ∂(ENNReal.ofReal C • μ) :=
        integral_mono_measure hν (Filter.Eventually.of_forall hf0) h1
    _ = C * ∫ y, f y ∂μ := by
        rw [integral_smul_measure, ENNReal.toReal_ofReal hC, smul_eq_mul]

theorem wr13e_min_le {Q lam P N : ℝ} (hQ : 0 ≤ Q) (hlam : lam ≤ P / N) (hP : 1 ≤ P) (hN : 0 < N) :
    min (lam * Q) 1 ≤ P / N * min Q N := by
  rcases le_total Q N with h | h
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hlam hQ)
  · rw [min_eq_right h]
    refine (min_le_right _ _).trans ?_
    have : P / N * N = P := by field_simp
    linarith

theorem wr13e_max_le {Q lam P N : ℝ} (hQ : 0 ≤ Q) (hlam : lam ≤ P / N) (hP : 1 ≤ P) (hN : 0 < N) :
    max (lam * Q - 1) 0 ≤ P / N * max (Q - N / P) 0 := by
  have hP0 : 0 < P := by linarith
  have hc : 0 ≤ P / N := div_nonneg hP0.le hN.le
  rcases le_total (lam * Q - 1) 0 with h | h
  · rw [max_eq_right h]
    exact mul_nonneg hc (le_max_right _ _)
  · rw [max_eq_left h]
    have h1 : lam * Q ≤ P / N * Q := mul_le_mul_of_nonneg_right hlam hQ
    have e : P / N * (Q - N / P) = P / N * Q - 1 := by field_simp
    calc lam * Q - 1 ≤ P / N * Q - 1 := by linarith
      _ = P / N * (Q - N / P) := e.symm
      _ ≤ P / N * max (Q - N / P) 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hc

/-! ### The cavity correction -/

section CavD

/-- **Cavity correction** (TeX `euc-cavity`, torus `cavD_torus`): for a weak potential `V` with kernel `q_τ`,
`0 ≤ D(x) := log u(x) + λ n ∫ q_τ(y,x) dν_n(y) ≤ C δ_N`, uniformly in the densities `ρ ≤ M`, in `β ∈ (0, βp]` and
in `n ≤ N`. -/
theorem wr13e_cavD (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) (βp M : ℝ)
    {Cν : ℝ} (hCν : 1 ≤ Cν) :
    ∃ CD : ℝ, 0 ≤ CD ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ V : WeakPotential (HRS.Whole.withDensityReal ρ),
      (∀ x y, V.q x y = qTau d s τ (x - y)) → V.γ ≤ wr13e_a d s τ M →
      ∀ β : ℝ, 0 < β → β ≤ βp → Real.exp (V.M + V.M' + β * V.γ) ≤ Cν → weakKappa V β ≤ 1 / 2 →
      ∀ (N n : ℕ) [NeZero n], n ≤ N → ∀ x : Euc d,
        0 ≤ Real.log (RefMarg.cavU V (β / N) n (fun e : Empty => e.elim) x) +
          β / N * n * ∫ y, V.q y x ∂(RefMarg.cavMarg V (β / N) n) ∧
        Real.log (RefMarg.cavU V (β / N) n (fun e : Empty => e.elim) x) +
          β / N * n * ∫ y, V.q y x ∂(RefMarg.cavMarg V (β / N) n) ≤ CD * deltaN d s N := by
  obtain ⟨Ca, Cb, hCa, hCb, hrow⟩ := wr3_row_bounds_real_integral hd hs.le hsd 1 (max M 0)
  set P : ℝ := max βp 1 with hP
  have hP1 : 1 ≤ P := le_max_right _ _
  have hP0 : 0 < P := by linarith
  set a : ℝ := wr13e_a d s τ M with ha_def
  have ha : 0 ≤ a := wr13e_a_nonneg hs hsd hτ M
  have hCν0 : 0 ≤ Cν := by linarith
  set σ : ℝ := HRS.WeakRef.sigmaOf d s with hσ
  set e : ℝ := 1 - (d : ℝ) / σ with he
  set mb : ℝ := βp * (Cν * a) with hmb
  refine ⟨Real.exp mb * Cν * Cb * P ^ 2 + Cν * Ca * (P * P ^ (-e)), by positivity, ?_⟩
  intro ρ hρ hM V hVq hVγ β hβ hβp hVC hκ N n _ hn x
  have hprob := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have hM' : ∀ y, ρ y ≤ max M 0 := fun y => (hM y).trans (le_max_left _ _)
  have hN0 : 0 < N := lt_of_lt_of_le (Nat.pos_of_ne_zero (NeZero.ne n)) hn
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN0
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn
  set lam : ℝ := β / N with hlam
  have hlam0 : 0 ≤ lam := by positivity
  have hβP : β ≤ P := hβp.trans (le_max_left _ _)
  have hlamP : lam ≤ P / N := div_le_div_of_nonneg_right hβP hNpos.le
  have hcN0 : 0 ≤ P / N := by positivity
  have hVqx : ∀ y, V.q y x = qTau d s τ (x - y) := fun y => by
    rw [hVq, ← wr12_qTau_even (d := d) (s := s) (τ := τ) (x - y), neg_sub]
  set ν := RefMarg.cavMarg V lam n with hν
  have hνle : ν ≤ ENNReal.ofReal Cν • (HRS.Whole.withDensityReal ρ) := by
    have h1 := RefMarg.marginal_le_smul (B := Empty) V hβ.le hN0 (n := n) (by simpa using hn)
      (fun e : Empty => e.elim) 0
    refine h1.trans ?_
    intro A
    simp only [Measure.smul_apply, smul_eq_mul]
    gcongr
  -- the kernel row at `x`
  have hK := wr13e_weak hd hs hsd hτ hρ hM
  have hqx : Measurable fun y : Euc d => qTau d s τ (x - y) :=
    (wr12_qTau_meas (d := d) (s := s) (τ := τ)).comp (measurable_const.sub measurable_id)
  have hq0 : ∀ y : Euc d, 0 ≤ qTau d s τ (x - y) := fun y => qTau_nonneg hs _
  have hVm : Measurable fun y : Euc d => V.q y x := by
    simp_rw [hVqx]; exact hqx
  have hV0 : ∀ y, 0 ≤ V.q y x := fun y => V.q_nonneg _ _
  -- first-moment bound
  have hVi : Integrable (fun y => V.q y x) (HRS.Whole.withDensityReal ρ) :=
    (V.integrable_q x).congr (Filter.Eventually.of_forall fun y => V.q_symm x y)
  have hI1 : ∫ y, V.q y x ∂ν ≤ Cν * a := by
    calc ∫ y, V.q y x ∂ν ≤ Cν * ∫ y, V.q y x ∂(HRS.Whole.withDensityReal ρ) :=
          wr13e_integral_le_of_le_smul hνle hCν0 hV0 hVi
      _ ≤ Cν * a := by
          refine mul_le_mul_of_nonneg_left ?_ hCν0
          calc ∫ y, V.q y x ∂(HRS.Whole.withDensityReal ρ) = ∫ y, V.q x y ∂(HRS.Whole.withDensityReal ρ) :=
                integral_congr_ae (Filter.Eventually.of_forall fun y => V.q_symm y x)
            _ ≤ V.γ := V.row_le x
            _ ≤ a := hVγ
  have hI0 : 0 ≤ ∫ y, V.q y x ∂ν := integral_nonneg hV0
  have hlamn : lam * n ≤ βp := by
    calc lam * n ≤ lam * N := by gcongr
      _ = β := by rw [hlam]; field_simp
      _ ≤ βp := hβp
  have hm : lam * n * ∫ y, V.q y x ∂ν ≤ mb :=
    calc lam * n * ∫ y, V.q y x ∂ν ≤ βp * (Cν * a) :=
          mul_le_mul hlamn hI1 hI0 (by have := hβ; have := hβp; nlinarith [hlam0, hn0, mul_nonneg hlam0 hn0])
      _ = mb := rfl
  obtain ⟨h1, h2⟩ := RefMarg.cavD_bounds V hβ.le hN0 hn hκ x hm
  refine ⟨h1, h2.trans ?_⟩
  -- the second-moment term
  obtain ⟨-, hrow2⟩ := hrow ρ hρ hM' (fun x y : Euc d => qTau d s τ (x - y)) hK.meas
    (fun x y => qTau_nonneg hs _) (fun x y hxy => wr13e_qTau_envelope hs hτ (sub_ne_zero.2 hxy)) x
  obtain ⟨hrow1, -⟩ := hrow ρ hρ hM' (fun x y : Euc d => qTau d s τ (x - y)) hK.meas
    (fun x y => qTau_nonneg hs _) (fun x y hxy => wr13e_qTau_envelope hs hτ (sub_ne_zero.2 hxy)) x
  have hδ0 : 0 ≤ deltaN d s N := HRS.deltaN_nonneg s hN0
  have hNδ : (N : ℝ) * deltaN d s N = HRS.WeakRef.psi2 d s N :=
    HRS.WeakRef.mul_deltaN_eq_psi2 s hN0
  obtain ⟨hi2, hb2⟩ := hrow2 (N : ℝ) hN1
  have hf1 : ∀ y, (min (lam * V.q y x) 1) ^ 2 ≤ (P / N) ^ 2 * (min (qTau d s τ (x - y)) N) ^ 2 := by
    intro y
    rw [hVqx y, ← mul_pow]
    refine pow_le_pow_left₀ (le_min (mul_nonneg hlam0 (hq0 y)) zero_le_one) ?_ 2
    exact wr13e_min_le (hq0 y) hlamP hP1 hNpos
  have hf1i : Integrable (fun y => (min (lam * V.q y x) 1) ^ 2) (HRS.Whole.withDensityReal ρ) := by
    refine Integrable.of_bound ((hVm.const_mul lam).min measurable_const |>.pow_const 2).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun y => ?_)
    have h0 : 0 ≤ min (lam * V.q y x) 1 := le_min (mul_nonneg hlam0 (hV0 y)) zero_le_one
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have : min (lam * V.q y x) 1 ≤ 1 := min_le_right _ _
    nlinarith
  have hA : ∫ y, (min (lam * V.q y x) 1) ^ 2 ∂ν ≤
      Cν * ((P / N) ^ 2 * (Cb * (N * deltaN d s N))) := by
    calc ∫ y, (min (lam * V.q y x) 1) ^ 2 ∂ν
        ≤ Cν * ∫ y, (min (lam * V.q y x) 1) ^ 2 ∂(HRS.Whole.withDensityReal ρ) :=
          wr13e_integral_le_of_le_smul hνle hCν0 (fun y => sq_nonneg _) hf1i
      _ ≤ Cν * ∫ y, (P / N) ^ 2 * (min (qTau d s τ (x - y)) N) ^ 2 ∂(HRS.Whole.withDensityReal ρ) := by
          refine mul_le_mul_of_nonneg_left (integral_mono hf1i (hi2.const_mul _) hf1) hCν0
      _ = Cν * ((P / N) ^ 2 * ∫ y, (min (qTau d s τ (x - y)) N) ^ 2 ∂(HRS.Whole.withDensityReal ρ)) := by
          rw [integral_const_mul]
      _ ≤ Cν * ((P / N) ^ 2 * (Cb * (N * deltaN d s N))) := by
          rw [hNδ]
          gcongr
  -- the tail term
  have hLpos : 0 < (N : ℝ) / P := by positivity
  obtain ⟨hi1, hb1⟩ := hrow1 ((N : ℝ) / P) hLpos
  have hf2 : ∀ y, max (lam * V.q y x - 1) 0 ≤ P / N * max (qTau d s τ (x - y) - N / P) 0 := by
    intro y
    rw [hVqx y]
    exact wr13e_max_le (hq0 y) hlamP hP1 hNpos
  have hf2i : Integrable (fun y => max (lam * V.q y x - 1) 0) (HRS.Whole.withDensityReal ρ) := by
    refine Integrable.mono' (hi1.const_mul (P / N))
      (((hVm.const_mul lam).sub_const 1).max measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact hf2 y
  have hB : ∫ y, max (lam * V.q y x - 1) 0 ∂ν ≤
      Cν * ((P / N) * (Ca * ((N : ℝ) / P) ^ e)) := by
    calc ∫ y, max (lam * V.q y x - 1) 0 ∂ν
        ≤ Cν * ∫ y, max (lam * V.q y x - 1) 0 ∂(HRS.Whole.withDensityReal ρ) :=
          wr13e_integral_le_of_le_smul hνle hCν0 (fun y => le_max_right _ _) hf2i
      _ ≤ Cν * ∫ y, P / N * max (qTau d s τ (x - y) - N / P) 0 ∂(HRS.Whole.withDensityReal ρ) :=
          mul_le_mul_of_nonneg_left (integral_mono hf2i (hi1.const_mul _) hf2) hCν0
      _ = Cν * ((P / N) * ∫ y, max (qTau d s τ (x - y) - N / P) 0 ∂(HRS.Whole.withDensityReal ρ)) := by
          rw [integral_const_mul]
      _ ≤ Cν * ((P / N) * (Ca * ((N : ℝ) / P) ^ e)) := by
          gcongr
  -- the power of the level
  have hpow : ((N : ℝ) / P) ^ e ≤ P ^ (-e) * deltaN d s N := by
    rw [Real.div_rpow hNpos.le hP0.le, Real.rpow_neg hP0.le, div_eq_mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_left (HRS.WeakRef.rpow_le_deltaN hd hs.le hsd hN0) (by positivity)
  -- assemble
  have hE1 : (n : ℝ) * ∫ y, (min (lam * V.q y x) 1) ^ 2 ∂ν ≤ Cν * Cb * P ^ 2 * deltaN d s N := by
    calc (n : ℝ) * ∫ y, (min (lam * V.q y x) 1) ^ 2 ∂ν
        ≤ n * (Cν * ((P / N) ^ 2 * (Cb * (N * deltaN d s N)))) := mul_le_mul_of_nonneg_left hA hn0
      _ = (Cν * Cb * P ^ 2 * deltaN d s N) * ((n : ℝ) / N) := by
          field_simp
      _ ≤ (Cν * Cb * P ^ 2 * deltaN d s N) * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_one hNpos]; exact hnN
      _ = _ := mul_one _
  have hE2 : (n : ℝ) * ∫ y, max (lam * V.q y x - 1) 0 ∂ν ≤ Cν * Ca * (P * P ^ (-e)) * deltaN d s N := by
    calc (n : ℝ) * ∫ y, max (lam * V.q y x - 1) 0 ∂ν
        ≤ n * (Cν * ((P / N) * (Ca * ((N : ℝ) / P) ^ e))) := mul_le_mul_of_nonneg_left hB hn0
      _ ≤ n * (Cν * ((P / N) * (Ca * (P ^ (-e) * deltaN d s N)))) := by
          gcongr
      _ = (Cν * Ca * (P * P ^ (-e)) * deltaN d s N) * ((n : ℝ) / N) := by
          field_simp
      _ ≤ (Cν * Ca * (P * P ^ (-e)) * deltaN d s N) * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_one hNpos]; exact hnN
      _ = _ := mul_one _
  have hexp : 0 < Real.exp mb := Real.exp_pos _
  calc Real.exp mb * (n * ∫ y, (min (lam * V.q y x) 1) ^ 2 ∂ν) + n * ∫ y, max (lam * V.q y x - 1) 0 ∂ν
      ≤ Real.exp mb * (Cν * Cb * P ^ 2 * deltaN d s N) + Cν * Ca * (P * P ^ (-e)) * deltaN d s N :=
        add_le_add (mul_le_mul_of_nonneg_left hE1 hexp.le) hE2
    _ = _ := by ring

end CavD

/-! ### The exact cavity equation -/

section CavEq

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {a : ℝ} {Ψ : Euc d → H} {β : ℝ} {n : ℕ}

/-- **The exact cavity equation for the reference marginal** (TeX `euc-cavity-equation`; torus
`cavity_equation`): with `θ = dπ_N/dμ`, `ν` the cavity marginal, `D = log u + λ n ∫ q dν` the cavity
correction and `λ = β/N`,
`log θ + β K_{k+q}(θ - 1) = D + β (q*θ - q*ν) + λ q*ν + c` for a constant `c`. -/
theorem wr13e_cavity_equation {k q0 : Euc d → ℝ} (hΨ : FeatHyp Ψ k)
    (hK : EWeakKernel μ a (fun x y => q0 (x - y))) (ha : 0 ≤ a) (hqe : ∀ z, q0 (-z) = q0 z)
    (hβ : 0 < β) {K : ℝ}
    (ht : ∀ x, |inner ℝ (tN (fun x y => q0 (x - y)) μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ K) [NeZero n]
    {Cz : ℝ} (hCz : ∀ᵐ y ∂μ, |wr13e_theta
      (wr13e_weakPotK hK ha hβ.le (wr13e_calFeat hΨ) (tN (fun x y => q0 (x - y)) μ Ψ β (n + 1)) ht)
      (β / ((n + 1 : ℕ) : ℝ)) n y - 1| ≤ Cz) :
    ∃ c : ℝ, ∀ x,
      Real.log (wr13e_theta
        (wr13e_weakPotK hK ha hβ.le (wr13e_calFeat hΨ) (tN (fun x y => q0 (x - y)) μ Ψ β (n + 1)) ht)
        (β / ((n + 1 : ℕ) : ℝ)) n x) +
      β * wr13e_Kt (fun w => k w + q0 w) μ (fun y => wr13e_theta
        (wr13e_weakPotK hK ha hβ.le (wr13e_calFeat hΨ) (tN (fun x y => q0 (x - y)) μ Ψ β (n + 1)) ht)
        (β / ((n + 1 : ℕ) : ℝ)) n y - 1) x =
      (Real.log (RefMarg.cavU
          (wr13e_weakPotK hK ha hβ.le (wr13e_calFeat hΨ) (tN (fun x y => q0 (x - y)) μ Ψ β (n + 1)) ht)
          (β / ((n + 1 : ℕ) : ℝ)) n (fun e : Empty => e.elim) x) +
        β / ((n + 1 : ℕ) : ℝ) * n *
          ∫ y, (wr13e_weakPotK hK ha hβ.le (wr13e_calFeat hΨ)
              (tN (fun x y => q0 (x - y)) μ Ψ β (n + 1)) ht).q y x
            ∂(RefMarg.cavMarg (wr13e_weakPotK hK ha hβ.le (wr13e_calFeat hΨ)
              (tN (fun x y => q0 (x - y)) μ Ψ β (n + 1)) ht) (β / ((n + 1 : ℕ) : ℝ)) n)) +
      β * ((∫ y, q0 (x - y) * wr13e_theta
          (wr13e_weakPotK hK ha hβ.le (wr13e_calFeat hΨ) (tN (fun x y => q0 (x - y)) μ Ψ β (n + 1)) ht)
          (β / ((n + 1 : ℕ) : ℝ)) n y ∂μ) -
        ∫ y, q0 (x - y) ∂(RefMarg.cavMarg (wr13e_weakPotK hK ha hβ.le (wr13e_calFeat hΨ)
          (tN (fun x y => q0 (x - y)) μ Ψ β (n + 1)) ht) (β / ((n + 1 : ℕ) : ℝ)) n)) +
      β / ((n + 1 : ℕ) : ℝ) *
        ∫ y, q0 (x - y) ∂(RefMarg.cavMarg (wr13e_weakPotK hK ha hβ.le (wr13e_calFeat hΨ)
          (tN (fun x y => q0 (x - y)) μ Ψ β (n + 1)) ht) (β / ((n + 1 : ℕ) : ℝ)) n) + c := by
  have hcal := wr13e_calFeat hΨ
  set V := wr13e_weakPotK hK ha hβ.le hcal (tN (fun x y => q0 (x - y)) μ Ψ β (n + 1)) ht with hV
  set lam : ℝ := β / ((n + 1 : ℕ) : ℝ) with hlam
  have hlam0 : 0 ≤ lam := div_nonneg hβ.le (Nat.cast_nonneg _)
  set θ := wr13e_theta V lam n with hθdef
  have hθ0 : ∀ x, 0 < θ x := wr13e_theta_pos V hlam0 n
  have hθ1 : ∫ x, θ x ∂μ = 1 := wr13e_integral_theta V hlam0 n
  have hθi : Integrable θ μ := wr13e_integrable_theta V hlam0 n
  have hθm : Measurable θ := wr13e_measurable_theta V hlam0 n
  obtain ⟨c₀, hc₀⟩ := wr13e_hh_eq hΨ hK ha hβ ht (n := n)
  have hlamn : lam * (n + 1 : ℕ) = β := by
    rw [hlam]; field_simp
  have hVqx : ∀ x y, V.q y x = q0 (x - y) := fun x y => by
    show q0 (y - x) = q0 (x - y)
    rw [← hqe (x - y), neg_sub]
  refine ⟨c₀ - Real.log (∫ x', RefMarg.cavTheta V lam n (fun e : Empty => e.elim) x' ∂μ), fun x => ?_⟩
  have e0 := wr13e_log_theta_eq V hlam0 n x
  have e1 : V.φ x = β * ∫ y, q0 (x - y) ∂μ + inner ℝ (tN (fun x y => q0 (x - y)) μ Ψ β (n + 1)) (Xi μ Ψ x) :=
    rfl
  have e2 := hc₀ x
  have hzi : Integrable (fun y => θ y - 1) μ := hθi.sub (integrable_const _)
  have hkm : Measurable fun y => k (x - y) :=
    hΨ.k_continuous.measurable.comp (measurable_const.sub measurable_id)
  have hgi : Integrable (fun y => k (x - y) * (θ y - 1)) μ := by
    refine Integrable.bdd_mul (c := k 0) hzi hkm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]; exact hΨ.k_abs_le _
  have hzb : ∀ᵐ y ∂μ, ‖θ y - 1‖ ≤ Cz := hCz.mono fun y hy => by rwa [Real.norm_eq_abs]
  have hq1 : Integrable (fun y => q0 (x - y)) μ := hK.wr1_integrable_row x
  have hqi : Integrable (fun y => q0 (x - y) * (θ y - 1)) μ := by
    have := Integrable.bdd_mul (c := Cz) hq1 hzi.aestronglyMeasurable hzb
    exact this.congr (Filter.Eventually.of_forall fun y => by simp [mul_comm])
  have hqθ : Integrable (fun y => q0 (x - y) * θ y) μ := by
    have := hqi.add hq1
    exact this.congr (Filter.Eventually.of_forall fun y => by simp only [Pi.add_apply]; ring)
  have hKt : wr13e_Kt (fun w => k w + q0 w) μ (fun y => θ y - 1) x =
      wr13e_Kt k μ (fun y => θ y - 1) x +
        ((∫ y, q0 (x - y) * θ y ∂μ) - ∫ y, q0 (x - y) ∂μ) := by
    unfold wr13e_Kt
    simp_rw [add_mul]
    rw [integral_add hgi hqi]
    congr 1
    simp_rw [mul_sub, mul_one]
    rw [integral_sub hqθ hq1]
  rw [hKt]
  have hm : (∫ y, V.q y x ∂(RefMarg.cavMarg V lam n)) = ∫ y, q0 (x - y) ∂(RefMarg.cavMarg V lam n) := by
    simp_rw [hVqx x]
  rw [hm, e0, e1, e2]
  have hn1 : lam * n = β - lam := by
    have : lam * ((n : ℝ) + 1) = β := by exact_mod_cast hlamn
    linarith
  have : lam * ↑n * ∫ y, q0 (x - y) ∂(RefMarg.cavMarg V lam n) =
      (β - lam) * ∫ y, q0 (x - y) ∂(RefMarg.cavMarg V lam n) := by rw [hn1]
  linarith

end CavEq

/-! ### Cavity versus full marginal, and the comparison with `R0` -/

section Event

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {a : ℝ} {q : Euc d → Euc d → ℝ}
  {Ψ : Euc d → H} {B β : ℝ} {n : ℕ}

/-- **Cavity versus full marginal** (`A:eq:weak-pin-comparison`; torus `event_pi_nu`):
`|π_N(A) - ν_n(A)| ≤ κ/N`. -/
theorem wr13e_event_pi_nu (hK : EWeakKernel μ a q) (ha : 0 ≤ a) (hβ : 0 < β) (h : CalFeat Ψ B)
    {K : ℝ} (ht : ∀ x, |inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ K) [NeZero n]
    (hκ : weakKappa (wr13e_weakPotK hK ha hβ.le h (tN q μ Ψ β (n + 1)) ht) β ≤ 1 / 2)
    {A : Set (Euc d)} (hA : MeasurableSet A) :
    |(HRS.Whole.firstMarginal (RN q μ Ψ β (n + 1))).real A -
        (RefMarg.cavMarg (wr13e_weakPotK hK ha hβ.le h (tN q μ Ψ β (n + 1)) ht)
          (β / ((n + 1 : ℕ) : ℝ)) n).real A| ≤
      weakKappa (wr13e_weakPotK hK ha hβ.le h (tN q μ Ψ β (n + 1)) ht) β / ((n + 1 : ℕ) : ℝ) := by
  set V := wr13e_weakPotK hK ha hβ.le h (tN q μ Ψ β (n + 1)) ht with hV
  have hRN := wr13e_RN_eq_fieldLawK hK ha hβ.le h (Nat.succ_pos n) ht
  rw [← hV] at hRN
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have h1 := rvh_pin_removed (B := Empty) V hβ.le (N := n + 1) (n := n) (Nat.succ_pos n) (by simp)
    (fun e : Empty => e.elim) hκ (Fin.last n) ⟨0, hn⟩ hA
  rw [RefMarg.pinnedLaw_empty, RefMarg.pinnedLaw_empty] at h1
  have e : (Fin.last n).succAbove (⟨0, hn⟩ : Fin n) = ⟨0, Nat.succ_pos n⟩ := by
    ext; simp [Fin.succAbove, Fin.lt_def]; omega
  rw [e] at h1
  unfold HRS.Whole.firstMarginal RefMarg.cavMarg
  rw [dif_pos (Nat.succ_pos n), hRN, RefMarg.pinnedLaw_empty]
  exact h1

/-- **`R_N` versus `R⁰_N`** (`A:eq:disagreement`; torus `tv_RN_R0`): the first marginals differ by at most
`4 e^{2βa + K} ε_h` in event distance, where `|⟪t_N, Ξ⟫| ≤ ε_h`. -/
theorem wr13e_tv_RN_R0 (hK : EWeakKernel μ a q) (ha : 0 ≤ a) (hβ : 0 < β) (h : CalFeat Ψ B)
    {K : ℝ} (ht : ∀ x, |inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ K)
    (hκ : weakKappa (wr13e_weakPotK hK ha hβ.le h (tN q μ Ψ β (n + 1)) ht) β ≤ 1 / 2) {εh : ℝ}
    (hεh : ∀ x, |inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ εh) {A : Set (Euc d)}
    (hA : MeasurableSet A) :
    |(HRS.Whole.firstMarginal (RN q μ Ψ β (n + 1))).real A -
        ((pairGibbsLawE q (n + 1) β μ).map (fun X => X ⟨0, Nat.succ_pos n⟩)).real A| ≤
      4 * Real.exp ((β * a + K) + 0 + β * a) * εh := by
  set V := wr13e_weakPotK hK ha hβ.le h (tN q μ Ψ β (n + 1)) ht with hV
  have hVq : V.q = q := rfl
  have hRN := wr13e_RN_eq_fieldLawK hK ha hβ.le h (Nat.succ_pos n) ht
  rw [← hV] at hRN
  have hR0 := wr13e_R0_eq_fieldLaw hK ha hβ.le (Nat.succ_pos n) V hVq
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (ht 0)
  have hψ : IsField μ V.φ V.M V.M' := ⟨V.measurable_φ, V.φ_le, V.integrable_φ, V.neg_le_integral_φ⟩
  have hbd : ∀ x, β * rowIntE q μ x ≤ V.M := fun x => by
    have h1 : β * rowIntE q μ x ≤ β * a := mul_le_mul_of_nonneg_left (hK.wr1_rowInt_le ha x) hβ.le
    show β * rowIntE q μ x ≤ β * a + K
    linarith
  have hψ' : IsField μ (fun x => β * rowIntE q μ x) V.M V.M' := by
    refine ⟨hK.wr1_measurable_rowInt.const_mul β, hbd, ?_, ?_⟩
    · exact Integrable.of_bound (hK.wr1_measurable_rowInt.const_mul β).aestronglyMeasurable (β * a)
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hβ.le (hK.wr1_rowInt_nonneg x))]
          exact mul_le_mul_of_nonneg_left (hK.wr1_rowInt_le ha x) hβ.le)
    · have : 0 ≤ ∫ x, β * rowIntE q μ x ∂μ :=
        integral_nonneg fun x => mul_nonneg hβ.le (hK.wr1_rowInt_nonneg x)
      show -(0 : ℝ) ≤ _
      simpa using this
  have hD : ∫ z, |V.φ z - β * rowIntE q μ z| ∂μ ≤ εh := by
    have hb : ∀ z, |V.φ z - β * rowIntE q μ z| ≤ εh := fun z => by
      have : V.φ z - β * rowIntE q μ z = inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ z) := by
        show β * rowIntE q μ z + inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ z) - β * rowIntE q μ z = _
        ring
      rw [this]; exact hεh z
    calc ∫ z, |V.φ z - β * rowIntE q μ z| ∂μ ≤ ∫ _z, εh ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _)
            (integrable_const _) (Filter.Eventually.of_forall hb)
      _ = εh := by simp
  have h1 := RefMarg.field_event_comparison V hβ.le (N := n + 1) (n := n + 1) (Nat.succ_pos n) le_rfl hψ hψ'
    hκ hD ⟨0, Nat.succ_pos n⟩ hA
  have e1 : HRS.Whole.firstMarginal (RN q μ Ψ β (n + 1)) =
      (fieldLaw V V.φ (β / ((n + 1 : ℕ) : ℝ)) (n + 1)).map (fun y => y ⟨0, Nat.succ_pos n⟩) := by
    unfold HRS.Whole.firstMarginal; rw [dif_pos (Nat.succ_pos n), hRN]
  have e2 : (pairGibbsLawE q (n + 1) β μ).map (fun X => X ⟨0, Nat.succ_pos n⟩) =
      (fieldLaw V (fun x => β * rowIntE q μ x) (β / ((n + 1 : ℕ) : ℝ)) (n + 1)).map
        (fun y => y ⟨0, Nat.succ_pos n⟩) := by
    rw [hR0]
  rw [e1, e2]
  exact h1

end Event

/-! ### Convolution estimates for `q * (ρ (θ - θ'))` -/

section Conv

open HRS.Whole.Q34 in
theorem wr13e_integral_nu {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (F : Euc d → ℝ) :
    ∫ y, F y ∂(HRS.Whole.withDensityReal ρ) = ∫ y, ρ y * F y := by
  unfold HRS.Whole.withDensityReal
  rw [integral_withDensity_eq_integral_toReal_smul (f := fun x => ENNReal.ofReal (ρ x))
    (ENNReal.measurable_ofReal.comp hρ.measurable)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [ENNReal.toReal_ofReal (hρ.nonneg y)]

/-- `q*θ - q*ν = q * (ρ (θ - θ'))` for the measures `μ = ρ dx` (density `θ`) and `ν = θ' μ` with bounded
densities (torus `cv_identity`). -/
theorem wr13e_cv_identity {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M)
    {q0 : Euc d → ℝ} (hqm : Measurable q0) (hq0 : ∀ z, 0 ≤ q0 z) (hqi : Integrable q0)
    {θ θ' : Euc d → ℝ} (hθm : Measurable θ) (hθ'm : Measurable θ') (hθ0 : ∀ x, 0 ≤ θ x)
    (hθ'0 : ∀ x, 0 ≤ θ' x) {Cb : ℝ} (hθb : ∀ x, θ x ≤ Cb) (hθ'b : ∀ x, θ' x ≤ Cb) (x : Euc d) :
    (∫ y, q0 (x - y) * θ y ∂(HRS.Whole.withDensityReal ρ)) -
        ∫ y, q0 (x - y) ∂((HRS.Whole.withDensityReal ρ).withDensity fun y => ENNReal.ofReal (θ' y)) =
      ∫ y, q0 (x - y) * (ρ y * (θ y - θ' y)) := by
  haveI : (volume : Measure (Euc d)).IsNegInvariant := inferInstance
  have hq1 : Integrable (fun y => q0 (x - y)) volume := hqi.comp_sub_left x
  have hρm := hρ.measurable
  have hb : ∀ (f : Euc d → ℝ), Measurable f → (∀ y, 0 ≤ f y) → (∀ y, f y ≤ Cb) →
      Integrable (fun y => q0 (x - y) * (ρ y * f y)) volume := by
    intro f hf hf0 hfb
    refine Integrable.mono' (hq1.mul_const (M * Cb))
      ((hqm.comp (measurable_const.sub measurable_id)).mul (hρm.mul hf)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hq0 _) (mul_nonneg (hρ.nonneg y) (hf0 y)))]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (hM y) (hfb y) (hf0 y) (le_trans (hρ.nonneg y) (hM y))) (hq0 _) |>.trans_eq (by ring)
  have e1 : ∫ y, q0 (x - y) * θ y ∂(HRS.Whole.withDensityReal ρ) = ∫ y, q0 (x - y) * (ρ y * θ y) := by
    rw [wr13e_integral_nu hρ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  have e2 : ∫ y, q0 (x - y) ∂((HRS.Whole.withDensityReal ρ).withDensity fun y => ENNReal.ofReal (θ' y)) =
      ∫ y, q0 (x - y) * (ρ y * θ' y) := by
    rw [integral_withDensity_eq_integral_toReal_smul (f := fun y => ENNReal.ofReal (θ' y))
      (ENNReal.measurable_ofReal.comp hθ'm) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp_rw [ENNReal.toReal_ofReal (hθ'0 _), smul_eq_mul]
    rw [wr13e_integral_nu hρ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  rw [e1, e2, ← integral_sub (hb θ hθm hθ0 hθb) (hb θ' hθ'm hθ'0 hθ'b)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  ring

/-- **`L²(μ)` estimate of the weak part of the convolution** (TeX `euc-convolution-L2`, torus `cv_L2_rate`):
for `|f| ≤ B`, `f ∈ L¹`, `‖f‖₁ ≤ K0 √(δ_N/N)` and `N ≥ N0`, the function `x ↦ ∫ q_τ(x - y) f(y) dy`
is in `L²(μ)` with norm `≤ C δ_N`, uniformly in the densities `ρ ≤ M`. -/
theorem wr13e_cv_L2 (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ)
    (B M K0 : ℝ) :
    ∃ (C : ℝ) (N0 : ℕ), 0 ≤ C ∧ ∀ N : ℕ, N0 ≤ N → ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ →
      (∀ x, ρ x ≤ M) → ∀ f : Euc d → ℝ, Measurable f → (∀ x, |f x| ≤ B) → Integrable f →
        ∫ x, |f x| ≤ K0 * Real.sqrt (deltaN d s N / N) →
        (∀ x, Integrable (fun y => qTau d s τ (x - y) * f y)) ∧
        MemLp (fun x => ∫ y, qTau d s τ (x - y) * f y) 2 (HRS.Whole.withDensityReal ρ) ∧
        eLpNorm (fun x => ∫ y, qTau d s τ (x - y) * f y) 2 (HRS.Whole.withDensityReal ρ) ≤
          ENNReal.ofReal (C * deltaN d s N) := by
  obtain ⟨C1, N1, hC1, h1⟩ := wr13c_conv_L2_delta hd hs hsd B M K0
  obtain ⟨C2, N2, hC2, h2⟩ := wr13c_sup_conv_delta hd hs hsd B K0
  refine ⟨C1, max N1 N2, hC1, fun N hN ρ hρ hM f hf hB hfi hε => ?_⟩
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have hfa_m : Measurable fun y => |f y| := hf.abs
  have hfa_b : ∀ x, |(|f x|)| ≤ B := fun x => by rw [abs_abs]; exact hB x
  have hfa_i : Integrable fun y => |f y| := hfi.abs
  have hfa_ε : ∫ x, |(|f x|)| ≤ K0 * Real.sqrt (deltaN d s N / N) := by
    simp_rw [abs_abs]; exact hε
  obtain ⟨hGm, hGb⟩ := h1 N (le_trans (le_max_left _ _) hN) (fun y => |f y|) hfa_m hfa_b hfa_i hfa_ε ρ hρ hM
  obtain ⟨hGi, -, -⟩ := h2 N (le_trans (le_max_right _ _) hN) (fun y => |f y|) hfa_m hfa_b hfa_i hfa_ε
  have hGi' : ∀ x, Integrable (fun y => ‖x - y‖ ^ (-s) * |f y|) := fun x => by
    have := hGi x
    simp_rw [HRS.Whole.Q34.rieszKernel_eq hs.ne'] at this
    exact this
  set G : Euc d → ℝ := fun x => ∫ y, ‖x - y‖ ^ (-s) * |f y| with hG
  set F : Euc d → ℝ := fun x => ∫ y, qTau d s τ (x - y) * f y with hF
  have hae : ∀ x : Euc d, ∀ᵐ y ∂(volume : Measure (Euc d)), y ≠ x := by
    intro x
    have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
    rw [ae_iff]
    simpa using measure_singleton (μ := (volume : Measure (Euc d))) x
  have hpt : ∀ x y : Euc d, y ≠ x → ‖qTau d s τ (x - y) * f y‖ ≤ ‖x - y‖ ^ (-s) * |f y| := by
    intro x y hy
    have hz : x - y ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
    have h1 := wr13e_qTau_le_g hs hτ hz
    rw [HRS.Whole.Q34.rieszKernel_eq hs.ne'] at h1
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (qTau_nonneg hs _), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have hqm : ∀ x : Euc d, Measurable fun y : Euc d => qTau d s τ (x - y) := fun x =>
    (wr12_qTau_meas (d := d) (s := s) (τ := τ)).comp (measurable_const.sub measurable_id)
  have hint : ∀ x, Integrable (fun y => qTau d s τ (x - y) * f y) := by
    intro x
    refine Integrable.mono' (hGi' x) ((hqm x).mul hf).aestronglyMeasurable ?_
    filter_upwards [hae x] with y hy
    exact hpt x y hy
  have hFG : ∀ x, ‖F x‖ ≤ ‖G x‖ := by
    intro x
    have hG0 : 0 ≤ G x := integral_nonneg fun y => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (abs_nonneg _)
    calc ‖F x‖ ≤ ∫ y, ‖qTau d s τ (x - y) * f y‖ := norm_integral_le_integral_norm _
      _ ≤ G x := by
          refine integral_mono_ae (hint x).norm (hGi' x) ?_
          filter_upwards [hae x] with y hy
          exact hpt x y hy
      _ = ‖G x‖ := by rw [Real.norm_eq_abs, abs_of_nonneg hG0]
  have hFm : Measurable F := RefMarg.measurable_integral_kernel (F := fun p : Euc d × Euc d =>
    qTau d s τ (p.1 - p.2) * f p.2)
    (((wr12_qTau_meas (d := d) (s := s) (τ := τ)).comp (measurable_fst.sub measurable_snd)).mul
      (hf.comp measurable_snd))
  have hFmem : MemLp F 2 (HRS.Whole.withDensityReal ρ) :=
    hGm.mono hFm.aestronglyMeasurable (Filter.Eventually.of_forall hFG)
  refine ⟨hint, hFmem, ?_⟩
  have h3 : eLpNorm F 2 (HRS.Whole.withDensityReal ρ) ≤ eLpNorm G 2 (HRS.Whole.withDensityReal ρ) :=
    eLpNorm_mono_ae hFm.aestronglyMeasurable (Filter.Eventually.of_forall hFG)
  refine h3.trans ?_
  have hsq := RefMarg.integral_mul_self_eq hGm
  have hfin : eLpNorm G 2 (HRS.Whole.withDensityReal ρ) ≠ ⊤ := hGm.eLpNorm_ne_top
  rw [← ENNReal.ofReal_toReal hfin]
  refine ENNReal.ofReal_le_ofReal ?_
  have h4 : (eLpNorm G 2 (HRS.Whole.withDensityReal ρ)).toReal =
      Real.sqrt (∫ x, G x ^ 2 ∂(HRS.Whole.withDensityReal ρ)) := by
    rw [← Real.sqrt_sq ENNReal.toReal_nonneg, ← hsq]
    congr 2; funext x; ring
  rw [h4]
  exact hGb

end Conv

/-! ### Absorption -/

section Absorb

/-- **Absorption** (TeX `euc-absorption`; torus `absorption`): if `log θ + β K z = Φ + c` with `z = θ - 1`,
`0 < θ ≤ C`, `∫ θ dμ = 1`, `K z ∈ L²(μ)` and `⟨K z, z⟩ ≥ 0` (positive definiteness of the kernel), then
`‖θ - 1‖_{L²(μ)} ≤ C ‖Φ‖_{L²(μ)}`. -/
theorem wr13e_absorption {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {β : ℝ} (hβ : 0 ≤ β)
    {θ : Euc d → ℝ} (hθm : Measurable θ) (hθ0 : ∀ x, 0 < θ x) {C : ℝ} (hC : 1 ≤ C)
    (hθC : ∀ᵐ x ∂μ, θ x ≤ C) (hθ1 : ∫ x, θ x ∂μ = 1) {Φ : Euc d → ℝ} (hΦ : MemLp Φ 2 μ) {c : ℝ}
    {Kz : Euc d → ℝ} (hKz2 : MemLp Kz 2 μ) (hnn : 0 ≤ ∫ x, Kz x * (θ x - 1) ∂μ)
    (heq : ∀ x, Real.log (θ x) + β * Kz x = Φ x + c) :
    eLpNorm (fun x => θ x - 1) 2 μ ≤ ENNReal.ofReal C * eLpNorm Φ 2 μ := by
  set z : Euc d → ℝ := fun x => θ x - 1 with hz
  have hzm : Measurable z := hθm.sub_const 1
  have hzb : ∀ᵐ x ∂μ, ‖z x‖ ≤ C := hθC.mono fun x hx => by
    rw [Real.norm_eq_abs, abs_le]
    have := hθ0 x
    constructor <;> simp only [hz] <;> linarith
  have hz2 : MemLp z 2 μ := MemLp.of_bound hzm.aestronglyMeasurable C hzb
  have hz1 : Integrable z μ := hz2.integrable one_le_two
  have hzint : ∫ x, z x ∂μ = 0 := by
    simp only [hz]
    rw [integral_sub (hz1.add (integrable_const 1) |>.congr (Filter.Eventually.of_forall fun x => by simp [hz]))
      (integrable_const _), hθ1]
    simp
  have hlog : ∀ x, Real.log (θ x) = Φ x + c - β * Kz x := fun x => by
    have := heq x; linarith
  have i1 : Integrable (fun x => z x * Φ x) μ := MemLp.integrable_mul hz2 hΦ
  have i2 : Integrable (fun x => z x * Kz x) μ := MemLp.integrable_mul hz2 hKz2
  have i3 : Integrable (fun x => z x * c) μ := hz1.mul_const c
  have hid : ∀ x, z x * Real.log (θ x) = z x * Φ x + z x * c - β * (z x * Kz x) := fun x => by
    rw [hlog x]; ring
  have hi : Integrable (fun x => z x * Real.log (θ x)) μ := by
    have := (i1.add i3).sub (i2.const_mul β)
    exact this.congr (Filter.Eventually.of_forall fun x => by simp only [Pi.add_apply, Pi.sub_apply]; rw [hid x])
  have hsq : Integrable (fun x => (z x) ^ 2 / C) μ := (hz2.integrable_sq.div_const C)
  have hmono := integral_mono_ae hsq hi (hθC.mono fun x hx => RefMarg.mul_log_ge (hθ0 x) hC hx)
  have hrhs : ∫ x, z x * Real.log (θ x) ∂μ = ∫ x, z x * Φ x ∂μ - β * ∫ x, Kz x * z x ∂μ := by
    simp_rw [hid]
    have i13 : Integrable (fun x => z x * Φ x + z x * c) μ := i1.add i3
    have i2' : Integrable (fun x => β * (z x * Kz x)) μ := i2.const_mul β
    rw [integral_sub i13 i2', integral_add i1 i3, integral_mul_const, hzint,
      integral_const_mul]
    simp_rw [mul_comm (Kz _) (z _)]
    ring
  have hK0 : 0 ≤ β * ∫ x, Kz x * z x ∂μ := mul_nonneg hβ hnn
  set a := (eLpNorm z 2 μ).toReal with ha
  set b := (eLpNorm Φ 2 μ).toReal with hb
  have hzz : ∫ x, z x * z x ∂μ = a ^ 2 := RefMarg.integral_mul_self_eq hz2
  have hCS : ∫ x, z x * Φ x ∂μ ≤ a * b := RefMarg.integral_mul_le_eLpNorm hz2 hΦ
  have hlhs : ∫ x, (z x) ^ 2 / C ∂μ = a ^ 2 / C := by
    rw [integral_div]
    congr 1
    rw [← hzz]; congr 1; funext x; ring
  have key : a ^ 2 / C ≤ a * b := by
    calc a ^ 2 / C = ∫ x, (z x) ^ 2 / C ∂μ := hlhs.symm
      _ ≤ _ := hmono
      _ = _ := hrhs
      _ ≤ ∫ x, z x * Φ x ∂μ := by linarith
      _ ≤ a * b := hCS
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
  have hC0 : 0 < C := by linarith
  have hab : a ≤ C * b := by
    rcases ha0.eq_or_lt with h | h
    · rw [← h]; positivity
    · have : a / C ≤ b := by
        have h2 : a ^ 2 / C / a ≤ a * b / a := div_le_div_of_nonneg_right key h.le
        have e1 : a ^ 2 / C / a = a / C := by field_simp
        have e2 : a * b / a = b := by field_simp
        rwa [e1, e2] at h2
      rw [div_le_iff₀ hC0] at this
      linarith
  have hzfin : eLpNorm z 2 μ ≠ ⊤ := hz2.eLpNorm_ne_top
  have hΦfin : eLpNorm Φ 2 μ ≠ ⊤ := hΦ.eLpNorm_ne_top
  rw [← ENNReal.ofReal_toReal hzfin, ← ENNReal.ofReal_toReal hΦfin, ← ENNReal.ofReal_mul hC0.le]
  exact ENNReal.ofReal_le_ofReal hab

end Absorb

end HRS.MS.Wr
