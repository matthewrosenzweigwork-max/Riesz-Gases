import HRS.Sections.Sec7Fields
import HRS.PDE.MovSpec
import HRS.PDE.MovFFinal
import HRS.PDE.MeanFieldDecayHr

/-!
# ALLTIME: Lemma 7.8 `alltime_Lp` (`M:U:lem:alltime-Lp`, TeX L8399-8444)

Files: `AllTimeAux1.lean` (this file: chain plan, regime-to-MOV bridges, relaxation without `Regime.relax`),
`AllTimeAux2.lean` (items 2 and 3: product-relative Gibbs moments and the exponential pair estimate, uniform in `t`),
`AllTimeFinal.lean` (`alltime_Lp_proof`, statement verbatim, tied by `type_of%`).

## Chain plan (all names `alltime_*`, namespace `HRS.Sec7`)

Notation: `R : Regime d`, `s = R.D.s < d/2`, `β = R.β`, `ρ = R.ρ`, `ρβ = R.ρβ`, `Nδ_N = 1` for `s < d/2`, `N ≥ 1`.

Item 1 (`‖h_N^t‖_{L^{p_∞}(Q_N^t)} ≤ C`, `f_N^t ≪ Q_N^t`).  TeX proof: bounded initial `L^{p₀}` norm, source
exponential bound with `L(t) = ‖∇u^t‖_∞`, variable exponent, `∫_0^∞ L < ∞`.  Formalisation: `mov_lp_bound` (MOV glue,
used as stated) with `βm = βp = β`, applied at horizon `T = t` for each `t ≥ 0`, with constants independent of `T`:
 1. (`alltime_hyp`) `MovTraj D T ρ` for every `T` from `movT_traj_of_global_proof` (bridge A), after `R.D = PDE.mfData …`
    (as `Regime.mf`); `MovHyp P D N T ρ X₀ W X` from `PreparedRealization` (brownian, indep, solution, filtered).
 2. (`movT_traj_uniform_proof`, A′) uniform `c₀ ≤ ρ^t`, `‖ρ^t‖_{C²} ≤ Λ₂` for all `t ≥ 0`.
 3. (`alltime_relax2`) `‖ρ^t - ρ_β‖_{C²} ≤ C e^{-ct}` WITHOUT `Regime.relax` (sorried): `PDE.finite_reg_decay` at
    `r = K - 1` (`K = ⌊d/2+6⌋+1`), `ρ^t - ρ_β = toFun(ρ̂^t - ρ̂_β)` and `PDE.toFun_isCk_le` (the coefficient form of
    `cbNorm_le_sobolevNorm`, as in `movf_traj_uniform`); `Regime.thermal` (proved) supplies `ρ_β` smooth, thermal.
 4. (`alltime_L`) bridge B `movT_relaxation_L_proof_reg` (needs `IsCk 2 ρβ`, from `Regime.thermal`) gives `L₀ ≥ 0`,
    `∫_{[0,∞)} L₀ < ∞`, `IsLipschitzVF (L₀ t) (mfeTransport D (ρ t))`; then `L t = L₀ t + e^{-t}` (positive lower
    bound `e^{-T}` on `[0,T]`, `∫_0^T L ≤ ∫_0^∞ L₀ + 1 =: Λ₁` independent of `T`).
 5. (`alltime_init`) bridge C: `movT_prepared_initial_Lp_proof` (`β₀ > 0`, `p₀ = 1 + min 1 (β₀/(2β))`, so that
    `p₀β₀ - (p₀-1)β > 0`) or `movT_prepared_initial_Lp_iid_proof` (`β₀ = 0`, `s = 0`): `Q_{N,β₀}(ρ₀) ≪ Q_{N,β}(ρ₀)` and
    `‖dQ_{N,β₀}/dQ_{N,β}‖_{L^{p₀}} ≤ exp(C N δ_N) = e^C`.  `ρ 0 = ρ₀` (`R.init`), `P.map X₀ = Q_{N,β₀}(ρ₀)` (`law_init`).
 6. (`alltime_item1`) `mov_lp_bound` with `Λ₁`, `p₀`, then `log ‖h_0‖ ≤ C` and `Nδ_N = 1`; `movT_Q_eq_beta`
    identifies `movT_Q (periodicRiesz d s) D N ρ t` with `modulatedGibbs … β (withDensityReal (ρ t))`.
 `P` is a probability measure because `P.map X₀ = Q_{N,β₀}(ρ₀)` is.

Item 2 (`AllTimeAux2`): `dQ_{N,β}/dπ = e^{-βNF}/K_β`, `π = (ρ^t dx)^{⊗N}`; `movf_lp_tilted` with base `b = 0` gives
`‖·‖_{L^q(π)} = (K_0^{q-1} K_β^{-q} K_{qβ})^{1/q}`, `K_0 = 1`, and the two-sided pressure bound (`movT_pressure_two_sided_C2_proof`
at `θ = 0`, `h = 0`, `β ∈ [β, qβ]`) uniform over the family `{ρ^t}` (`c₀`, `Λ₂` from step 2) bounds `K_β^{-1}, K_{qβ}` by
`e^{CNδ_N}`; `q → q+1` and monotonicity of `L^q` norms on a probability space for `q ≥ 1`.

Item 3 (`AllTimeAux2`): `moments_of_pressure` with `hP` from `movT_pressure_two_sided_C2_proof` (`β ∈ {β}`), `RowOK`
from `rowOK_g_h`; the diagonal repair: `h' = h` off the diagonal, `0` on it (`|h'| ≤ B' w'` everywhere with
`w' = g + max c (1 - g 0) ≥ 1`), and `modulatedEnergy h = modulatedEnergy h'` Gibbs-a.e. by
`modulatedEnergy_congr_offdiag` and `ae_injective_pi` (`Gibbs ≪ π`).  `c_B = β θ₀`, `C_B = e^{(2C+1)}` (`Nδ_N = 1`).

Regime fields `Regime.reg`, `Regime.relax` (sorried) are NOT used: everything is derived from `R.sol` through
`movT_traj_of_global_proof`, `movT_traj_uniform_proof`, `alltime_relax2`.

Expected sorried MOV declarations reached (via `mov_lp_bound`, `mov_lp_ineq`): `movT_source_exp_scaled_uniform`,
`movT_regSeq_exists`, `movT_lp_init_limsup`, `movT_lp_lsc`, `movT_lp_reg_bound`, `movT_Q_tendsto_weak`,
`movT_pressure_two_sided_C2`, and what they use (the final axiom check lists exactly which).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Sec7

variable {d : ℕ}

theorem alltime_K_spec (d : ℕ) : (d : ℝ) / 2 + 6 < (⌊(d : ℝ) / 2 + 6⌋₊ + 1 : ℕ) := movf_K_spec d

/-- `‖ρ^t - ρ_β‖_{C²} ≤ C e^{-ct}`, i.e. `Regime.relax 2` bypassing the sorried lemma. -/
theorem alltime_relax2 (R : Regime d) : ∃ C c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 ≤ t →
    Torus.cbNorm 2 (fun x => R.ρ t x - R.ρβ x) ≤ C * Real.exp (-c * t) := by
  have hd1 : 1 ≤ d := by have := R.hd; omega
  set K : ℕ := ⌊(d : ℝ) / 2 + 6⌋₊ + 1 with hKdef
  have hK := alltime_K_spec d
  have H := R.finiteRegHyp K hK
  obtain ⟨ρc, hρc0, hρ⟩ := R.sol K hK
  have hρc : PDE.IsMFSolutionHK d R.D.s R.D.V R.β⁻¹ (K : ℝ) R.ρ₀ ρc := by
    rw [R.hDβ] at hρc0; exact hρc0
  have hKd : (d : ℝ) / 2 < K := by have : (d : ℝ) / 2 + 6 < K := hK; linarith
  obtain ⟨hth, hsm, hpos⟩ := R.thermal
  have hcont : Continuous R.ρβ := mova_continuous_of_isCk (mova_isCk_two_of_smooth hsm)
  have hSob : MemSobolev (K : ℝ) R.ρβ := PDE.MFSemigroup.memSobolev_of_isSmooth hsm _
  set r : ℝ := (K : ℝ) - 1 with hr
  have hr0 : 0 ≤ r := by have : (d : ℝ) / 2 + 6 < K := hK; have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  have hrK : r < K := by rw [hr]; linarith
  obtain ⟨Cr, cr, hCr, hcr, hdec⟩ := PDE.finite_reg_decay hd1 R.D.s R.β R.β K R.D.V R.ρ₀ H r hr0 hrK
  obtain ⟨Ce, hCe⟩ := PDE.toFun_isCk_le (d := d) 2 r (by
    have : (d : ℝ) / 2 + 6 < K := hK
    rw [hr]; linarith)
  have hβm : R.β ∈ Set.Icc R.β R.β := ⟨le_rfl, le_rfl⟩
  have hmemβ : PDE.MemHs (K : ℝ) (PDE.coeffOf R.ρβ) := (PDE.hsNormSq_coeffOf (K : ℝ) R.ρβ hSob).1
  have hsumβ : Summable fun k => ‖PDE.coeffOf R.ρβ k‖ := PDE.summable_norm_of_memHs (K : ℝ) hKd _ hmemβ
  have hrealβ : PDE.IsRealCoeff (PDE.coeffOf R.ρβ) :=
    PDE.isRealCoeff_coeffOf _ (mova_int_cont hcont)
  have htoβ : PDE.toFun (PDE.coeffOf R.ρβ) = R.ρβ := PDE.MFThermalReg.toFun_coeffOf hcont hsumβ
  refine ⟨max Ce 0 * Cr, cr, hcr, fun t ht => ?_⟩
  obtain ⟨hmr, hnorm⟩ := hdec R.β hβm ρc hρc R.ρβ hth hcont hpos hSob t ht
  have hreal := PDE.MFGlobal.isRealCoeff_of_isMFSolutionHK hd1 R.D.s R.β R.β K R.D.V R.ρ₀ H R.β hβm ρc hρc t ht
  have hmem : PDE.MemHs (K : ℝ) (ρc t) := hρc.cont.1 t ht
  have e : (fun x => R.ρ t x - R.ρβ x) = PDE.toFun (ρc t - PDE.coeffOf R.ρβ) := by
    funext x
    rw [PDE.MFApriori.Aux.toFun_sub _ _ (PDE.summable_norm_of_memHs (K : ℝ) hKd _ hmem) hsumβ, htoβ,
      hρ t ht]
    rfl
  rw [e]
  have := (hCe _ hmr (PDE.MFVelocity.isRealCoeff_sub' hreal hrealβ)).2
  calc Torus.cbNorm 2 (PDE.toFun (ρc t - PDE.coeffOf R.ρβ))
      ≤ Ce * PDE.hsNorm r (ρc t - PDE.coeffOf R.ρβ) := this
    _ ≤ max Ce 0 * PDE.hsNorm r (ρc t - PDE.coeffOf R.ρβ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
    _ ≤ max Ce 0 * (Cr * Real.exp (-cr * t)) := mul_le_mul_of_nonneg_left hnorm (le_max_right _ _)
    _ = max Ce 0 * Cr * Real.exp (-cr * t) := by ring


/-- `R.D` is the mean-field data `PDE.mfData` (as in `Regime.mf`). -/
theorem alltime_D_eq (R : Regime d) :
    R.D = PDE.mfData d R.D.s R.D.hs0 R.D.hsd R.D.V R.β R.hβ := by
  have key : ∀ D : DynData d, D.M = -1 → D.invβ = R.β⁻¹ →
      D = PDE.mfData d D.s D.hs0 D.hsd D.V R.β R.hβ := by
    rintro ⟨s, M, V, iβ, h1, h2, h3⟩ h4 h5
    simp only at h4 h5
    subst h4 h5
    rfl
  exact key R.D R.hM R.hDβ

theorem alltime_glob (R : Regime d) : ∀ K : ℕ, (d : ℝ) / 2 + 6 < K →
    ∃ ρc : ℝ → (Lattice d → ℂ), PDE.IsMFSolutionHK d R.D.s R.D.V R.β⁻¹ K R.ρ₀ ρc ∧
      ∀ t, 0 ≤ t → PDE.mfPath ρc t = R.ρ t := by
  intro K hK
  obtain ⟨ρc, h1, h2⟩ := R.sol K hK
  refine ⟨ρc, by rw [R.hDβ] at h1; exact h1, fun t ht => (h2 t ht).symm⟩

theorem alltime_hs0 (R : Regime d) : 0 ≤ R.D.s := R.D.hs0

theorem alltime_hsd (R : Regime d) : R.D.s < d := R.D.hsd

/-- `MovTraj` for every horizon (bridge A). -/
theorem alltime_traj (R : Regime d) (T : ℝ) : MovTraj R.D T R.ρ := by
  have := movT_traj_of_global_proof R.D.s R.β R.D.V R.ρ₀ R.ρ R.D.hs0 R.D.hsd R.hβ R.hV R.hρ₀
    (alltime_glob R) T
  rwa [← alltime_D_eq R] at this

/-- `N δ_N = 1` for `s < d/2`, `N > 0`. -/
theorem alltime_Ndelta {s : ℝ} (hs : s < (d : ℝ) / 2) {N : ℕ} (hN : 0 < N) :
    (N : ℝ) * deltaN d s N = 1 := by
  unfold deltaN
  rw [if_pos hs]
  have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- A prepared realisation has a probability law `P` (since `P.map X₀` is a probability measure). -/
theorem alltime_isProb {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℕ} {X₀ : Ω → Config d N}
    (hae : AEMeasurable X₀ P) (h : IsProbabilityMeasure (P.map X₀)) : IsProbabilityMeasure P := by
  refine ⟨?_⟩
  have := h.measure_univ
  rwa [Measure.map_apply_of_aemeasurable hae MeasurableSet.univ, preimage_univ] at this

/-- The physical reference measure is a probability measure for a continuous probability density. -/
theorem alltime_gibbs_prob (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρ : IsProbDensity ρ) (hc : Continuous ρ) {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : 0 ≤ b) :
    IsProbabilityMeasure (modulatedGibbs (periodicRiesz d s) N b (withDensityReal ρ)) := by
  haveI := isProb_withDensityReal hρ
  obtain ⟨hm, C, hC⟩ := movf_energy_facts hd hs0 hsd hρ hc hN (N := N)
  rw [movf_modGibbs_eq_tilted hd hs0 hsd hρ hc hN hb]
  refine isProbabilityMeasure_tilted ?_
  have := movf_exp_integrable (Measure.pi fun _ : Fin N => withDensityReal ρ)
    (F := fun X : Config d N => N * modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ))
    (measurable_const.mul hm) (c := N * C) (fun X => by
      have := hC X
      have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      nlinarith) hb
  refine this.congr (Eventually.of_forall fun X => ?_)
  simp only; ring_nf

/-- Bridge C in the regime: an exponent `p₀ > 1` and `‖dQ_{N,β₀}(ρ₀)/dQ_{N,β}(ρ₀)‖_{L^{p₀}} ≤ e^C`. -/
theorem alltime_init (R : Regime d) : ∃ p₀ C : ℝ, 1 < p₀ ∧ 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
    modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀) ≪
      modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal R.ρ₀) ∧
    eLpNorm ((modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)).rnDeriv
        (modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal R.ρ₀))) (ENNReal.ofReal p₀)
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal R.ρ₀)) ≤
      ENNReal.ofReal (Real.exp C) := by
  have hd1 : 1 ≤ d := by have := R.hd; omega
  have hck : Torus.IsCk 2 R.ρ₀ := mova_isCk_two_of_smooth R.hρ₀.smooth
  have hsd2 : R.D.s < (d : ℝ) / 2 := R.hs
  rcases R.hβ₀ with hb | ⟨hs, hb0⟩
  · set p₀ : ℝ := 1 + min 1 (R.β₀ / (2 * R.β)) with hp₀
    have hm : 0 < min 1 (R.β₀ / (2 * R.β)) := lt_min one_pos (by have := R.hβ; positivity)
    have hp1 : 1 < p₀ := by rw [hp₀]; linarith
    have hcoef : 0 < p₀ * R.β₀ - (p₀ - 1) * R.β := by
      have h1 : min 1 (R.β₀ / (2 * R.β)) ≤ R.β₀ / (2 * R.β) := min_le_right _ _
      have hβ0 : R.β ≠ 0 := R.hβ.ne'
      have h2 : min 1 (R.β₀ / (2 * R.β)) * R.β ≤ R.β₀ / 2 := by
        calc min 1 (R.β₀ / (2 * R.β)) * R.β ≤ R.β₀ / (2 * R.β) * R.β :=
              mul_le_mul_of_nonneg_right h1 R.hβ.le
          _ = R.β₀ / 2 := by field_simp
      have h3 : p₀ * R.β₀ - (p₀ - 1) * R.β =
          R.β₀ + min 1 (R.β₀ / (2 * R.β)) * R.β₀ - min 1 (R.β₀ / (2 * R.β)) * R.β := by
        rw [hp₀]; ring
      rw [h3]
      nlinarith [mul_pos hm hb]
    obtain ⟨C, hC⟩ := movT_prepared_initial_Lp_proof hd1 R.D.hs0 R.D.hsd R.hρ₀.density hck R.hρ₀.pos hb
      R.hβ hp1 hcoef
    refine ⟨p₀, max C 0, hp1, le_max_right _ _, fun N hN => ?_⟩
    obtain ⟨h1, h2⟩ := hC N hN
    refine ⟨h1, h2.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))⟩
    rw [mul_assoc, alltime_Ndelta hsd2 (by omega), mul_one]
    exact le_max_left _ _
  · obtain ⟨p₀, C, hp1, hC⟩ := movT_prepared_initial_Lp_iid_proof R.hd R.hρ₀.density hck R.hρ₀.pos R.hβ
    refine ⟨p₀, max C 0, hp1, le_max_right _ _, fun N hN => ?_⟩
    obtain ⟨h1, h2⟩ := hC N hN
    have hd0 : (0 : ℝ) < (d : ℝ) / 2 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast R.hd
      linarith
    rw [hs, hb0]
    refine ⟨h1, h2.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))⟩
    rw [mul_assoc, alltime_Ndelta hd0 (by omega), mul_one]
    exact le_max_left _ _

/-- The all-time Lipschitz bound `L` (bridge B + a positive lower bound), with `∫_0^T L ≤ Λ₁` for all `T ≥ 0`. -/
theorem alltime_L (R : Regime d) : ∃ Λ₁ : ℝ, 0 ≤ Λ₁ ∧ ∃ L : ℝ → ℝ,
    (∀ T : ℝ, ∃ ℓ : ℝ, 0 < ℓ ∧ ∀ r ∈ Set.Icc (0 : ℝ) T, ℓ ≤ L r) ∧
    (∀ T : ℝ, IntegrableOn L (Set.Icc (0 : ℝ) T)) ∧
    (∀ T : ℝ, ∀ r ∈ Set.Icc (0 : ℝ) T, IsLipschitzVF (L r) (mfeTransport R.D (R.ρ r))) ∧
    (∀ T : ℝ, ∫ r in Set.Icc (0 : ℝ) T, L r ≤ Λ₁) := by
  obtain ⟨C, c, hc, hrel⟩ := alltime_relax2 R
  obtain ⟨hth, hsm, hpos⟩ := R.thermal
  have hβinv : R.D.invβ⁻¹ = R.β := by rw [R.hDβ, inv_inv]
  have hth' : IsThermalDensity (periodicRiesz d R.D.s) R.D.V R.D.invβ⁻¹ R.ρβ := by
    rw [hβinv]; exact hth
  have hinvpos : 0 < R.D.invβ := by rw [R.hDβ]; exact inv_pos.2 R.hβ
  obtain ⟨L₀, hL0, hL0i, hL0l⟩ := movT_relaxation_L_proof_reg R.hM hinvpos hth'
    (mova_isCk_two_of_smooth hsm) (alltime_traj R) hc hrel
  have hexpI : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Set.Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    simpa using exp_neg_integrableOn_Ioi 0 one_pos
  have hexpI1 : ∫ t in Set.Ici (0 : ℝ), Real.exp (-t) = 1 := by
    rw [integral_Ici_eq_integral_Ioi]; exact integral_exp_neg_Ioi_zero
  refine ⟨(∫ t in Set.Ici (0 : ℝ), L₀ t) + 1, ?_, fun t => L₀ t + Real.exp (-t), ?_, ?_, ?_, ?_⟩
  · have := setIntegral_nonneg (μ := volume) measurableSet_Ici (f := L₀) (fun t ht => hL0 t ht)
    linarith
  · intro T
    refine ⟨Real.exp (-T), Real.exp_pos _, fun r hr => ?_⟩
    have := hL0 r hr.1
    have : Real.exp (-T) ≤ Real.exp (-r) := Real.exp_le_exp.2 (by linarith [hr.2])
    linarith
  · intro T
    exact (hL0i.mono_set Set.Icc_subset_Ici_self).add
      (Continuous.integrableOn_Icc (by fun_prop))
  · intro T r hr x y
    have h := hL0l r hr.1 x y
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (KernelGrad.tdist_nonneg x y))
    have := Real.exp_pos (-r)
    linarith
  · intro T
    have hi1 : IntegrableOn L₀ (Set.Icc (0 : ℝ) T) := hL0i.mono_set Set.Icc_subset_Ici_self
    have hi2 : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Set.Icc (0 : ℝ) T) :=
      Continuous.integrableOn_Icc (by fun_prop)
    rw [integral_add hi1 hi2]
    have a1 : ∫ t in Set.Icc (0 : ℝ) T, L₀ t ≤ ∫ t in Set.Ici (0 : ℝ), L₀ t :=
      setIntegral_mono_set hL0i (by
        filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht using hL0 t ht)
        (Eventually.of_forall Set.Icc_subset_Ici_self)
    have a2 : ∫ t in Set.Icc (0 : ℝ) T, Real.exp (-t) ≤ ∫ t in Set.Ici (0 : ℝ), Real.exp (-t) :=
      setIntegral_mono_set hexpI (Eventually.of_forall fun t => (Real.exp_pos _).le)
        (Eventually.of_forall Set.Icc_subset_Ici_self)
    linarith


/-- Item 1 of Lemma 7.8, from `mov_lp_bound` (MOV glue), bridges A, A', B, C. -/
theorem alltime_item1 (R : Regime d) :
    ∃ p : ℝ, 1 < p ∧ ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X₀ : Ω → Config d N)
        (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        PreparedRealization R.D P (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀))
          X₀ W X →
        ∀ t : ℝ, 0 ≤ t →
          (P.map (X t.toNNReal)) ≪ modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t)) ∧
          eLpNorm ((P.map (X t.toNNReal)).rnDeriv
              (modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t))))
            (ENNReal.ofReal p)
            (modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t))) ≤ ENNReal.ofReal C := by
  have hd1 : 1 ≤ d := by have := R.hd; omega
  have hs0 := alltime_hs0 R
  have hsd := alltime_hsd R
  have hsd2 : R.D.s < (d : ℝ) / 2 := R.hs
  obtain ⟨p₀, Ci, hp₀, hCi, hinit⟩ := alltime_init R
  obtain ⟨c₀, Λ₂, hc₀, hunif⟩ := movT_traj_uniform_proof R.D.s R.β R.D.V R.ρ₀ R.ρ hs0 hsd R.hβ R.hV
    R.hρ₀ (alltime_glob R)
  obtain ⟨Λ₁, hΛ₁, L, hLl, hLi, hLlip, hLint⟩ := alltime_L R
  obtain ⟨pInf, C₁, hp, hC₁, H⟩ := mov_lp_bound hd1 hs0 hsd R.β R.β R.hβ c₀ hc₀ Λ₂ p₀ hp₀ Λ₁ hΛ₁
  have hβ₀ : 0 ≤ R.β₀ := by
    rcases R.hβ₀ with h | ⟨-, h⟩
    · exact h.le
    · exact h.ge
  have hcont0 : Continuous R.ρ₀ := mova_continuous_of_isCk (mova_isCk_two_of_smooth R.hρ₀.smooth)
  refine ⟨pInf, hp, Real.exp (C₁ * (2 + Ci)), fun N hN Ω _ P X₀ W X hprep t ht => ?_⟩
  have hN0 : 0 < N := by omega
  have hQ0eq : ∀ r : ℝ, movT_Q (periodicRiesz d R.D.s) R.D N R.ρ r =
      modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ r)) :=
    fun r => movT_Q_eq_beta R.hDβ N R.ρ r
  have hprobQ0 := alltime_gibbs_prob hd1 hs0 hsd R.hρ₀.density hcont0 hN0 hβ₀
  have hmapprob : IsProbabilityMeasure (P.map X₀) := by rw [hprep.law_init]; exact hprobQ0
  have hae : AEMeasurable X₀ P :=
    ((hprep.solution 0).adapted 0).aemeasurable.congr (hprep.solution 0).init
  haveI : IsProbabilityMeasure P := alltime_isProb hae hmapprob
  have hMov : MovHyp P R.D N t R.ρ X₀ W X :=
    ⟨alltime_traj R t, hprep.brownian, hprep.indep, hprep.solution t, hprep.filtered⟩
  obtain ⟨ρt, hρt⟩ := (alltime_traj R t).classical
  obtain ⟨ℓ, hℓ, hLℓ⟩ := hLl t
  obtain ⟨hinit1, hinit2⟩ := hinit N hN
  have hac : P.map X₀ ≪ movT_Q (periodicRiesz d R.D.s) R.D N R.ρ 0 := by
    rw [hprep.law_init, hQ0eq 0, R.init]; exact hinit1
  have hfin : eLpNorm ((P.map X₀).rnDeriv (movT_Q (periodicRiesz d R.D.s) R.D N R.ρ 0))
      (ENNReal.ofReal p₀) (movT_Q (periodicRiesz d R.D.s) R.D N R.ρ 0) < ⊤ := by
    rw [hprep.law_init, hQ0eq 0, R.init]
    exact lt_of_le_of_lt hinit2 ENNReal.ofReal_lt_top
  have key := H N hN P X₀ W X hMov hρt rfl
    (by rw [R.hDβ, inv_inv]; exact ⟨le_rfl, le_rfl⟩)
    (fun r hr x => (hunif r hr.1).1 x) (fun r hr => (hunif r hr.1).2) L ⟨ℓ, hℓ, hLℓ⟩ (hLi t)
    (hLlip t) (hLint t) hac hfin t ⟨ht, le_rfl⟩
  obtain ⟨hacT, hle⟩ := key
  rw [hQ0eq t] at hacT hle
  refine ⟨hacT, hle.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))⟩
  rw [hQ0eq 0, hprep.law_init, R.init, alltime_Ndelta hsd2 hN0]
  refine mul_le_mul_of_nonneg_left ?_ hC₁
  have hlog : Real.log (eLpNorm ((modulatedGibbs (periodicRiesz d R.D.s) N R.β₀
      (withDensityReal R.ρ₀)).rnDeriv (modulatedGibbs (periodicRiesz d R.D.s) N R.β
        (withDensityReal R.ρ₀))) (ENNReal.ofReal p₀) (modulatedGibbs (periodicRiesz d R.D.s) N R.β
          (withDensityReal R.ρ₀))).toReal ≤ Ci := by
    set a := eLpNorm ((modulatedGibbs (periodicRiesz d R.D.s) N R.β₀
      (withDensityReal R.ρ₀)).rnDeriv (modulatedGibbs (periodicRiesz d R.D.s) N R.β
        (withDensityReal R.ρ₀))) (ENNReal.ofReal p₀) (modulatedGibbs (periodicRiesz d R.D.s) N R.β
          (withDensityReal R.ρ₀)) with ha
    have h1 : a.toReal ≤ Real.exp Ci := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hinit2
      rwa [ENNReal.toReal_ofReal (Real.exp_pos _).le] at this
    rcases (ENNReal.toReal_nonneg (a := a)).eq_or_lt with h0 | h0
    · rw [← h0]; simpa using hCi
    · exact (Real.log_le_iff_le_exp h0).2 h1
  linarith

end Sec7

end HRS

end
