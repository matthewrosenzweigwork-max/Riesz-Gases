import HRS.Sections.Sec5
import HRS.PDE.MovSpec
import HRS.PDE.MovFFinal
import HRS.PDE.MeanFieldDecayHr

/-!
# MOVLOG: Lemma 5.8 `moving_log_moment` (`M:P:lem:moving-moments`, TeX M L6641-6726)

Files: `MovLogAux1.lean` (this file: chain plan, relaxation and the all-time Lipschitz bound for
`IsSmoothPositiveTrajectory`), `MovLogFinal.lean` (`moving_log_moment_proof`, statement verbatim, assembly from `mov_lp_bound`, tied by `type_of%`).

## Statement check
`moving_log_moment` has NO explicit relaxation input and no thermal density, but it does not need one as a hypothesis:
`IsSmoothPositiveTrajectory` carries a global `H^K` mean-field solution for every `K > d/2 + 6` with smooth `V`, smooth positive
initial density, and `hd : 2 ≤ d`, so `PDE.thermal_exists_unique_smooth` gives the thermal density and
`PDE.finite_reg_decay` gives `‖ρ^t - ρ_β‖_{H^r} ≤ C e^{-ct}` (this is Regime-style, as `alltime_relax2`, which bypasses the sorried
`Regime.relax`).  So `∫_0^∞ L < ∞` (TeX L6660-6661 "the relaxation input") is derivable; the statement is sufficient.

## Chain plan (all names `movlog_*`, namespace `HRS.MovLog`)
1. (`movlog_relax2`, here) thermal `ρ_β` (smooth, positive) and `‖ρ^t - ρ_β‖_{C²} ≤ C e^{-ct}` from `movf_finiteRegHyp`,
   `PDE.finite_reg_decay` (`r = K-1`, `K = ⌊d/2+6⌋+1`) and `PDE.toFun_isCk_le`.
2. (`movlog_L`, here) bridge B `movT_relaxation_L_proof_reg` + `η = e^{-t}`: `L = L₀ + e^{-t}`, positive lower bound `e^{-T}` on `[0,T]`,
   `∫_0^T L ≤ Λ₁ := ∫_0^∞ L₀ + 1` independent of `T`.
3. (`MovLogFinal`) for each `t ≥ 0`, `mov_lp_bound` at horizon `T = t` with `c₀, Λ₂` from `movT_traj_uniform_proof`, `MovTraj` from
   `movT_traj_of_global_proof` (bridge A), `MovHyp` from `IsParticleSystem` + filtered solution, `movT_Q_eq_beta`.
Sorried MOV declarations reached: those of `mov_lp_bound` (listed by the final axiom check).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace MovLog

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem movlog_relax2 (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) :
    ∃ ρβ : Torus d → ℝ, IsThermalDensity (periodicRiesz d s) V β ρβ ∧ Torus.IsSmooth ρβ ∧
      (∀ x, 0 < ρβ x) ∧ ∃ C c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 ≤ t →
        Torus.cbNorm 2 (fun x => ρ t x - ρβ x) ≤ C * Real.exp (-c * t) := by
  have hd1 : 1 ≤ d := by omega
  set K : ℕ := ⌊(d : ℝ) / 2 + 6⌋₊ + 1 with hKdef
  have hK := movf_K_spec d
  have H := movf_finiteRegHyp htr.hs0 htr.hsd htr.hβ htr.V_smooth htr.init K hK
  obtain ⟨ρc, hρc, hρ⟩ := htr.global K hK
  have hKd : (d : ℝ) / 2 < K := by have : (d : ℝ) / 2 + 6 < K := hK; linarith
  obtain ⟨ρβ, hth, hsm, hpos, -⟩ :=
    PDE.thermal_exists_unique_smooth hd s htr.hs0 htr.hsd β htr.hβ V htr.V_smooth
  refine ⟨ρβ, hth, hsm, hpos, ?_⟩
  have hcont : Continuous ρβ := mova_continuous_of_isCk (mova_isCk_two_of_smooth hsm)
  have hSob : MemSobolev (K : ℝ) ρβ := PDE.MFSemigroup.memSobolev_of_isSmooth hsm _
  set r : ℝ := (K : ℝ) - 1 with hr
  have hr0 : 0 ≤ r := by
    have : (d : ℝ) / 2 + 6 < K := hK
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hrK : r < K := by rw [hr]; linarith
  obtain ⟨Cr, cr, hCr, hcr, hdec⟩ := PDE.finite_reg_decay hd1 s β β K V ρ₀ H r hr0 hrK
  obtain ⟨Ce, hCe⟩ := PDE.toFun_isCk_le (d := d) 2 r (by
    have : (d : ℝ) / 2 + 6 < K := hK
    rw [hr]; linarith)
  have hβm : β ∈ Set.Icc β β := ⟨le_rfl, le_rfl⟩
  have hmemβ : PDE.MemHs (K : ℝ) (PDE.coeffOf ρβ) := (PDE.hsNormSq_coeffOf (K : ℝ) ρβ hSob).1
  have hsumβ : Summable fun k => ‖PDE.coeffOf ρβ k‖ := PDE.summable_norm_of_memHs (K : ℝ) hKd _ hmemβ
  have hrealβ : PDE.IsRealCoeff (PDE.coeffOf ρβ) :=
    PDE.isRealCoeff_coeffOf _ (mova_int_cont hcont)
  have htoβ : PDE.toFun (PDE.coeffOf ρβ) = ρβ := PDE.MFThermalReg.toFun_coeffOf hcont hsumβ
  refine ⟨max Ce 0 * Cr, cr, hcr, fun t ht => ?_⟩
  obtain ⟨hmr, hnorm⟩ := hdec β hβm ρc hρc ρβ hth hcont hpos hSob t ht
  have hreal := PDE.MFGlobal.isRealCoeff_of_isMFSolutionHK hd1 s β β K V ρ₀ H β hβm ρc hρc t ht
  have hmem : PDE.MemHs (K : ℝ) (ρc t) := hρc.cont.1 t ht
  have e : (fun x => ρ t x - ρβ x) = PDE.toFun (ρc t - PDE.coeffOf ρβ) := by
    funext x
    rw [PDE.MFApriori.Aux.toFun_sub _ _ (PDE.summable_norm_of_memHs (K : ℝ) hKd _ hmem) hsumβ, htoβ,
      ← hρ t ht]
    rfl
  rw [e]
  have := (hCe _ hmr (PDE.MFVelocity.isRealCoeff_sub' hreal hrealβ)).2
  calc Torus.cbNorm 2 (PDE.toFun (ρc t - PDE.coeffOf ρβ))
      ≤ Ce * PDE.hsNorm r (ρc t - PDE.coeffOf ρβ) := this
    _ ≤ max Ce 0 * PDE.hsNorm r (ρc t - PDE.coeffOf ρβ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
    _ ≤ max Ce 0 * (Cr * Real.exp (-cr * t)) := mul_le_mul_of_nonneg_left hnorm (le_max_right _ _)
    _ = max Ce 0 * Cr * Real.exp (-cr * t) := by ring

/-- `MovTraj` for every horizon (bridge A). -/
theorem movlog_traj (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (T : ℝ) : MovTraj htr.dyn T ρ :=
  movT_traj_of_global_proof s β V ρ₀ ρ htr.hs0 htr.hsd htr.hβ htr.V_smooth htr.init htr.global T

/-- The all-time Lipschitz bound `L` (bridge B + a positive lower bound), with `∫_0^T L ≤ Λ₁` for all `T ≥ 0`. -/
theorem movlog_L (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) :
    ∃ Λ₁ : ℝ, 0 ≤ Λ₁ ∧ ∃ L : ℝ → ℝ,
    (∀ T : ℝ, ∃ ℓ : ℝ, 0 < ℓ ∧ ∀ r ∈ Set.Icc (0 : ℝ) T, ℓ ≤ L r) ∧
    (∀ T : ℝ, IntegrableOn L (Set.Icc (0 : ℝ) T)) ∧
    (∀ T : ℝ, ∀ r ∈ Set.Icc (0 : ℝ) T, IsLipschitzVF (L r) (mfeTransport htr.dyn (ρ r))) ∧
    (∀ T : ℝ, ∫ r in Set.Icc (0 : ℝ) T, L r ≤ Λ₁) := by
  obtain ⟨ρβ, hth, hsm, hpos, C, c, hc, hrel⟩ := movlog_relax2 hd htr
  have hth' : IsThermalDensity (periodicRiesz d htr.dyn.s) htr.dyn.V htr.dyn.invβ⁻¹ ρβ := by
    have : htr.dyn.invβ⁻¹ = β := inv_inv β
    rw [this]; exact hth
  have hinvpos : 0 < htr.dyn.invβ := inv_pos.2 htr.hβ
  obtain ⟨L₀, hL0, hL0i, hL0l⟩ := movT_relaxation_L_proof_reg (D := htr.dyn) rfl hinvpos hth'
    (mova_isCk_two_of_smooth hsm) (movlog_traj htr) hc hrel
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

end MovLog

end HRS

end
