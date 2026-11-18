import HRS.Whole.AppendixA
import HRS.Whole.AppendixALemmas
import HRS.MH.DualityRdFinal
import HRS.MH.CommSuperCS10
import HRS.MH.CoercTestW7e
import HRS.MP.RdRemainder
import HRS.MP.RdMartingale
import HRS.MS.GenPathAux12
import HRS.MS.SuppU15Aux1
import HRS.Main.A8PAux2
import HRS.Main.A8PAux10
import HRS.Main.A8PAux53
import HRS.MS.UlocCb
import HRS.MS.UlocWeighted

/-!
# SA2, packet 1: S.A.2 `main_rd_stat` and S.A.3 `fourier_statistics_rd` (plan and standing-assumption lemmas)

Worker SA2, 2026-10-24.  The full per-row plan (verdict on the restated statement, junk-value audit, merged inputs, packets,
missing pieces) is in `docs/SA2_PLAN.md` (copy of the scratch plan) and summarised here.

## Verdict

The frozen `main_rd_stat` (M3 restatement: `AdjointInputRd (ulocClass m_*) (ulocClass m_*) 2 (S.coeff N) S.T Kad` for all `N ≥ 1`,
explicit `Kad` before `∃ C₀min`) is true and non-vacuous.  Points of the audit that shape the proof:

* `t_a = 0` needs NO separate lemma: `AdjointInputRd` quantifies `0 ≤ r ≤ t`, so `∃ f, IsClassicalAdjointW C 0 φ f` is part of the hypothesis.
* `RdStatParts` asks `Continuous φ ∧ ulocNormE m_* χ φ < ⊤` but not `C²`; `AdjointInputRd` has the guard `ContDiff ℝ 2 φ`.  Bridge by
  `uloc_embedding_cb` (the continuous `φ` equals its `C_b^2` representative everywhere).
* `Λ < 1` is possible in the hypotheses (`ρ ≤ Λ` on `ℝ^d`); the merged S.B.5(i), coercivity and test lemmas need `1 ≤ Λ`.  Resolution (this file):
  `Λ̂ = max Λ 1`, and `oNΛ d s C₀ᶜ Λ̂ N ≤ oNΛ d s C₀ Λ N` for `C₀ ≥ sa2C0min` (the threshold may depend on `Λ`, it is quantified after it).
* `s ≥ max{0, d-2}` gives `(d-s)/2 ≤ 1`: the coercivity test bound is applied at the Sobolev index `1` (packet 5), so the uloc `H^{m_*-1}` algebra is not needed.

## Packets (namespace `HRS.MS.MainRdStat`, helpers `sa2_`)

`MainRdStatAux1` (this file: standing-assumption monotonicity, `Λ̂`/`C₀min`, energy comparison, collision a.e. for the two branches that carry an
occupation bound), `Aux2` (adjoint-input consequences, `y0Norm`), `Aux3` (Itô decomposition `Z = I_emp + M + R`), `Aux4` (remainder),
`Aux5` (index-1 test bound for `∇f_a·∇f_b`), `Aux6` (deterministic covariance density, covariance cost), `Aux7` (null contact, case (c)),
`Aux8` (per-`N` smooth / `W₁` / `W₂`), `MainRdStatTie` (assembly, ties, S.A.3).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Whole HRS.Whole.AppendixA
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MainRdStat

variable {d : ℕ}

/-! ### Monotonicity of the regularity assumptions -/

theorem sa2_cbNorm_mono {r r' : ℕ} (h : r' ≤ r) (f : Euc d → ℝ) : cbNorm r' f ≤ cbNorm r f := by
  unfold cbNorm
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ h)) ?_
  intro j _ _
  exact Real.iSup_nonneg fun z => norm_nonneg _

theorem sa2_memCb_mono {r r' : ℕ} (h : r' ≤ r) {f : Euc d → ℝ} (hf : MemCb r f) : MemCb r' f :=
  ⟨hf.1.of_le (by exact_mod_cast h), fun j hj => hf.2 j (hj.trans h)⟩

theorem sa2_weightedSupE_mono {r r' : ℕ} (h : r' ≤ r) (L : ℝ) (f : Euc d → ℝ) :
    weightedSupE r' L f ≤ weightedSupE r L f := by
  unfold weightedSupE derivSupE
  refine iSup_le fun j => ?_
  refine le_iSup_of_le (⟨(j : ℕ), by omega⟩ : Fin (r + 1)) ?_
  exact le_rfl

theorem sa2_regular_mono {s : ℝ} {r r' : ℕ} {Λ Λ' T : ℝ} {ρ : ℝ → Euc d → ℝ} (h : IsRegularMFRd s r Λ T ρ)
    (hr : r' ≤ r) (hΛ : Λ ≤ Λ') : IsRegularMFRd s r' Λ' T ρ := by
  refine ⟨fun t ht => ?_, fun hs t ht x => (h.2 hs t ht x).trans hΛ⟩
  obtain ⟨hmem, hw, hle⟩ := h.1 t ht
  have hw' : weightedSupE r' ((d : ℝ) + 3) (ρ t) < ⊤ :=
    lt_of_le_of_lt (sa2_weightedSupE_mono hr _ _) hw
  refine ⟨sa2_memCb_mono hr hmem, hw', ?_⟩
  have h1 := sa2_cbNorm_mono hr (ρ t)
  have h2 : (weightedSupE r' ((d : ℝ) + 3) (ρ t)).toReal ≤ (weightedSupE r ((d : ℝ) + 3) (ρ t)).toReal :=
    ENNReal.toReal_mono hw.ne (sa2_weightedSupE_mono hr _ _)
  linarith

theorem sa2_vhyp_mono {mV m' : ℕ} {ΛV G₀ : ℝ} {V : Euc d → ℝ} (h : VHypRd mV ΛV G₀ V) (hm : m' ≤ mV) :
    VHypRd m' ΛV G₀ V :=
  ⟨h.1, fun j hj hjm x => h.2.1 j hj (hjm.trans hm) x, h.2.2⟩

/-! ### The case `Λ < 1`: `Λ̂ = max Λ 1` and the completion constant -/

/-- The threshold on `C₀` guaranteeing `oNΛ d s C₀ᶜ (max Λ 1) N ≤ oNΛ d s C₀ Λ N`. -/
def sa2C0min (d : ℕ) (s Λ C₀c : ℝ) : ℝ :=
  C₀c * max 1 (Λ ^ (-(s / d))) + max 0 (Real.log (1 / Λ)) / (2 * d)

theorem sa2_oN_le (hd : 1 ≤ d) {s Λ C₀c C₀ : ℝ} (hs0 : 0 ≤ s) (hΛ : 0 < Λ) (hC₀c : 0 ≤ C₀c)
    (hC₀ : sa2C0min d s Λ C₀c ≤ C₀) {N : ℕ} (hN : 1 ≤ N) :
    oNΛ d s C₀c (max Λ 1) N ≤ oNΛ d s C₀ Λ N := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hNp : 0 ≤ (N : ℝ) ^ (s / d - 1) := Real.rpow_nonneg hN0.le _
  have hlog0 : 0 ≤ max 0 (Real.log (1 / Λ)) / (2 * d) := by positivity
  have hC₀' : C₀c * max 1 (Λ ^ (-(s / d))) ≤ C₀ := by
    have := hC₀; unfold sa2C0min at this; linarith
  have hsd0 : 0 ≤ s / d := by positivity
  unfold oNΛ
  by_cases hΛ1 : 1 ≤ Λ
  · rw [max_eq_left hΛ1]
    have hmax : max 1 (Λ ^ (-(s / d))) = 1 :=
      max_eq_left (Real.rpow_le_one_of_one_le_of_nonpos hΛ1 (neg_nonpos.2 hsd0))
    rw [hmax, mul_one] at hC₀'
    have hLp : 0 ≤ Λ ^ (s / d) := Real.rpow_nonneg hΛ.le _
    have : C₀c * Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1) ≤ C₀ * Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1) := by
      gcongr
    linarith
  · push Not at hΛ1
    rw [max_eq_right hΛ1.le]
    have hΛp : 0 < Λ ^ (s / d) := Real.rpow_pos_of_pos hΛ _
    have h1 : C₀c ≤ C₀ * Λ ^ (s / d) := by
      have hm : C₀c * Λ ^ (-(s / d)) ≤ C₀ := (mul_le_mul_of_nonneg_left (le_max_right _ _) hC₀c).trans hC₀'
      have e : Λ ^ (-(s / d)) * Λ ^ (s / d) = 1 := by
        rw [← Real.rpow_add hΛ]; simp
      calc C₀c = C₀c * (Λ ^ (-(s / d)) * Λ ^ (s / d)) := by rw [e, mul_one]
        _ = (C₀c * Λ ^ (-(s / d))) * Λ ^ (s / d) := by ring
        _ ≤ C₀ * Λ ^ (s / d) := mul_le_mul_of_nonneg_right hm hΛp.le
    by_cases hs : s = 0
    · subst hs
      have hlg : Real.log ((N : ℝ) * Λ) = Real.log N + Real.log Λ := Real.log_mul hN0.ne' hΛ.ne'
      have hlogΛ : Real.log (1 / Λ) = - Real.log Λ := by
        rw [one_div, Real.log_inv]
      have hC : C₀c + max 0 (-Real.log Λ) / (2 * d) ≤ C₀ := by
        have := hC₀
        unfold sa2C0min at this
        simpa [hlogΛ] using this
      have hmaxge : -Real.log Λ ≤ max 0 (-Real.log Λ) := le_max_right _ _
      simp only [if_true, mul_one, zero_div, zero_sub, Real.rpow_neg_one, Real.rpow_zero, one_mul]
      have e1 : -Real.log Λ / (2 * d * N) ≤ (C₀ - C₀c) * (N : ℝ)⁻¹ := by
        have h2 : -Real.log Λ / (2 * d) ≤ C₀ - C₀c := by
          have := div_le_div_of_nonneg_right hmaxge (by positivity : (0 : ℝ) ≤ 2 * d)
          linarith
        calc -Real.log Λ / (2 * d * N) = (-Real.log Λ / (2 * d)) * (N : ℝ)⁻¹ := by
              field_simp
          _ ≤ (C₀ - C₀c) * (N : ℝ)⁻¹ := mul_le_mul_of_nonneg_right h2 (by positivity)
      have e3 : Real.log (N * Λ) / (2 * d * N) = Real.log N / (2 * d * N) - (-Real.log Λ / (2 * d * N)) := by
        rw [hlg]; ring
      rw [e3]
      nlinarith [e1]
    · simp only [hs, if_false, zero_add]
      have : C₀c * (1 : ℝ) ^ (s / d) * (N : ℝ) ^ (s / d - 1) ≤ C₀ * Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1) := by
        rw [Real.one_rpow, mul_one]
        exact mul_le_mul_of_nonneg_right h1 hNp
      simpa using this

/-! ### Facts from the standing assumptions -/

section Standing

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {r mV : ℕ}
  {𝔈 : ℕ → ℝ}

/-- `ρ_N^t ≤ Λ` on `[0,T]`. -/
theorem sa2_rho_le (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) {N : ℕ} (hN : 1 ≤ N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) S.T) : ∀ x, S.ρ N t x ≤ Λ := by
  obtain ⟨hmem, -, hle⟩ := (hS.mean_field.regular N hN).1 t ht
  exact fun x => ((le_abs_self _).trans (HRS.MP.RdRem.mrr_abs_le_cbNorm hmem x)).trans
    (le_trans (le_add_of_nonneg_right ENNReal.toReal_nonneg) hle)

/-- `Λ > 0`: a probability density bounded by `Λ`. -/
theorem sa2_Lam_pos (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) : 0 < Λ := by
  have hρ := (hS.mean_field.solution 1 le_rfl).density 0 ⟨le_rfl, S.hT.le⟩
  have hle := sa2_rho_le hS (N := 1) le_rfl (t := 0) ⟨le_rfl, S.hT.le⟩
  by_contra hneg
  push Not at hneg
  have hzero : ∀ x, S.ρ 1 0 x = 0 := fun x => le_antisymm ((hle x).trans hneg) (hρ.nonneg x)
  have h1 := hρ.integral_one
  simp only [hzero, integral_zero] at h1
  exact zero_ne_one h1

/-- the weighted sup bound at `r = 0` (`⟨x⟩^{d+3}ρ ≤ Λ`). -/
theorem sa2_weighted_bound (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) :
    ∀ x, jbracket x ^ ((d : ℝ) + 3) * |S.ρ N t x| ≤ max Λ 0 := by
  obtain ⟨-, hw, hle⟩ := (hS.mean_field.regular N hN).1 t ht
  have hcb : 0 ≤ cbNorm r (S.ρ N t) := Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun z => norm_nonneg _
  have h1 : weightedSupE r ((d : ℝ) + 3) (S.ρ N t) ≤ ENNReal.ofReal Λ := by
    rw [← ENNReal.ofReal_toReal hw.ne]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  exact fun x => HRS.MS.SuppU15.u15_weighted_zero h1 x

/-- the log-moment bound `L(d,Λ)` of the densities `ρ_N^t`. -/
theorem sa2_logmoment (d : ℕ) (Λ : ℝ) : ∃ Lm : ℝ, ∀ {S : WholeMainData d} {R : ∀ N, RealizationRd d N}
    {MB ΛV G₀ m20 C₀ : ℝ} {r mV : ℕ} {𝔈 : ℕ → ℝ},
    RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈 → ∀ {N : ℕ}, 1 ≤ N → ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) S.T →
      HasLogMoment (HRS.Whole.withDensityReal (S.ρ N t)) Lm := by
  obtain ⟨Lm, hLm⟩ := HRS.MS.SuppU15.u15_logmoment (d := d) (L := (d : ℝ) + 3) (by linarith) Λ
  exact ⟨Lm, fun hS N hN t ht =>
    hLm _ ((hS.mean_field.solution N hN).density t ht) (sa2_weighted_bound hS hN ht)⟩

/-- the pointwise comparison of corrected energies -/
theorem sa2_corrected_le (hd : 1 ≤ d) (hs0 : 0 ≤ S.s) {C₀c : ℝ} (hΛ : 0 < Λ) (hC₀c : 0 ≤ C₀c)
    (hC₀ : sa2C0min d S.s Λ C₀c ≤ C₀) {N : ℕ} (hN : 1 ≤ N) (X : EucConfig d N) (t : ℝ) :
    rieszModulatedEnergy d S.s X (HRS.Whole.withDensityReal (S.ρ N t)) + oNΛ d S.s C₀c (max Λ 1) N ≤
      correctedEnergyRd S C₀ Λ N X t := by
  unfold correctedEnergyRd
  have := sa2_oN_le hd hs0 hΛ hC₀c hC₀ hN
  linarith

/-- Moments `E ofReal(F + o(C₀ᶜ, Λ̂)) ≤ 𝔈_N`. -/
theorem sa2_energy_bound (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) (hd : 1 ≤ d) {C₀c : ℝ}
    (hC₀c : 0 ≤ C₀c) (hC₀ : sa2C0min d S.s Λ C₀c ≤ C₀) {N : ℕ} (hN : 1 ≤ N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) S.T) :
    ∫⁻ ζ, ENNReal.ofReal (rieszModulatedEnergy d S.s ((R N).X (Real.toNNReal t) ζ)
        (HRS.Whole.withDensityReal (S.ρ N t)) + oNΛ d S.s C₀c (max Λ 1) N) ∂(R N).P ≤ ENNReal.ofReal (𝔈 N) := by
  refine le_trans (lintegral_mono fun ζ => ?_) (hS.energy.bound N hN t ht)
  exact ENNReal.ofReal_le_ofReal
    (sa2_corrected_le hd S.hs0 (sa2_Lam_pos hS) hC₀c hC₀ hN _ t)

/-! ### The scales -/

theorem sa2_sigma_nonneg (S : WholeMainData d) (N : ℕ) : 0 ≤ S.sigma N :=
  HRS.MP.RdRem.mrr_sigma_nonneg S N

theorem sa2_q_eq (S : WholeMainData d) (N : ℕ) : S.qN N = S.sigma N ^ 2 * S.invβ N / N := by
  unfold WholeMainData.qN qScale
  by_cases h : S.invβ N = 0
  · simp [h]
  · rw [if_neg h]; rfl

theorem sa2_q_nonneg (S : WholeMainData d) (N : ℕ) : 0 ≤ S.qN N := by
  rw [sa2_q_eq]
  have := S.hinvβ N
  positivity

theorem sa2_AN_mul (S : WholeMainData d) (N : ℕ) : S.AN N * S.κ N = S.sigma N := by
  unfold WholeMainData.AN Ascale
  have hκ := (S.hκ N).ne'
  by_cases h : S.invβ N = 0
  · have : S.sigma N = S.κ N := by
      unfold WholeMainData.sigma sigmaScale; rw [if_pos h]
    rw [if_pos h, this, one_mul]
  · rw [if_neg h]
    unfold WholeMainData.sigma
    field_simp

theorem sa2_AN_nonneg (S : WholeMainData d) (N : ℕ) : 0 ≤ S.AN N := by
  have h := sa2_AN_mul S N
  have hκ := S.hκ N
  have hσ := sa2_sigma_nonneg S N
  by_contra hneg
  push Not at hneg
  nlinarith

theorem sa2_AN_le_one (S : WholeMainData d) (N : ℕ) : S.AN N ≤ 1 := by
  unfold WholeMainData.AN Ascale
  have hκ := S.hκ N
  by_cases h : S.invβ N = 0
  · rw [if_pos h]
  · rw [if_neg h, div_le_one hκ]
    unfold sigmaScale
    rw [if_neg h]
    exact min_le_left _ _

end Standing

theorem sa2_wN_nonneg {N : ℕ} {E m₂ : ℝ} (hE : 0 ≤ E) (hm : 0 ≤ m₂) : 0 ≤ wN d N E m₂ := by
  unfold wN
  refine Real.iInf_nonneg fun R => ?_
  have hR := R.2
  have h1 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / d) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have h2 : 0 ≤ E ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hE _
  have h3 : 0 ≤ R.1 ^ ((d : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
  have h4 : 0 ≤ m₂ / R.1 ^ 2 := by have : 0 < R.1 := by linarith
                                   positivity
  positivity

theorem sa2_wN_le {N : ℕ} {E m₂ : ℝ} (hE : 0 ≤ E) (hm : 0 ≤ m₂) {R : ℝ} (hR : 1 ≤ R) :
    wN d N E m₂ ≤ R ^ ((d : ℝ) / 2) * ((N : ℝ) ^ (-(1 : ℝ) / d) + E ^ ((1 : ℝ) / 2)) + m₂ / R ^ 2 := by
  unfold wN
  refine ciInf_le (f := fun R : {R : ℝ // 1 ≤ R} =>
    R.1 ^ ((d : ℝ) / 2) * ((N : ℝ) ^ (-(1 : ℝ) / d) + E ^ ((1 : ℝ) / 2)) + m₂ / R.1 ^ 2) ⟨0, ?_⟩ ⟨R, hR⟩
  rintro _ ⟨R', rfl⟩
  have hR' := R'.2
  have h1 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / d) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have h2 : 0 ≤ E ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hE _
  have h3 : 0 ≤ R'.1 ^ ((d : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
  have h4 : 0 ≤ m₂ / R'.1 ^ 2 := by have : 0 < R'.1 := by linarith
                                    positivity
  show 0 ≤ _
  positivity

/-! ### Collision-free a.e. in `(r, ζ)` from an occupation bound -/

theorem sa2_inj_ae_of_occ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {N : ℕ} {T : ℝ}
    (X : ℝ≥0 → Ω → EucConfig d N)
    (h : ∀ᵐ ζ ∂P, volume {s : ℝ | s ∈ Set.Icc (0 : ℝ) T ∧ X (Real.toNNReal s) ζ ∈ eucCollisionSet d N} = 0) :
    ∀ᵐ ζ ∂P, ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) T)), Function.Injective (X (Real.toNNReal r) ζ) := by
  filter_upwards [h] with ζ hζ
  rw [ae_restrict_iff' measurableSet_Icc]
  have h1 := (measure_eq_zero_iff_ae_notMem.1 hζ)
  filter_upwards [h1] with r hr hrI
  intro i j hij
  by_contra hne
  exact hr ⟨hrI, i, j, hne, hij⟩

end HRS.MS.MainRdStat
