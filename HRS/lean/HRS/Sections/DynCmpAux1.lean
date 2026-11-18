import HRS.Sections.DynEntFinal

/-!
# DYNCMP: Theorem 5.4 `dynamic_comparison`, step (1): the adjoint package

TeX: `HRS_periodic_main_20261008T010000Z.tex` (M) `N:thm:dynamic`, second display `N:eq:dynamic-bound` (L6086-6091),
proof L6470-6530.

## Chain plan for `dynamic_comparison` (files `DynCmpAux1` ... `DynCmpFinal`)

1. (`DynCmpAux1`, this file) Packaged adjoint existence with uniform `C²` bounds for a smooth positive trajectory:
   `dyncmp_adjoint_package` (regularity `IsRegularMF 3 Λ T ρ`, classical adjoint solutions for all `t ∈ (0,T]`, uniform
   `cbNorm 2` bound of `U^{r,t}φ`, `U^{0,0} = id`, joint continuity of `ρ`).  Route: `finiteReg_hypotheses` +
   `adjoint_torus_classical` (regime R1 / R3), transferred from `mfPath ρc` to `ρ` (`AdjointData` only sees `[0,T]`).
2. (`DynCmpAux2`) Identification `flucInteraction D ψ X ρ = - modulatedEnergy (commKernel ∇g ∇ψ) X μ` (gradient dynamics,
   `D.M = -1`) and the `r`-uniform remainder bound `E_{f^r}[N |F^{h_{∇f^r}}|] ≤ C B_N`.
3. (`DynCmpAux3`) The Hoeffding / Donsker-Varadhan linear-entropy bound `N:eq:linear-entropy`.
4. (`DynCmpAux4`...) The enlargement `Ω × ℝ^p` making `G` independent of `ℱ_T`, the vector martingale
   `M_a = √N M_{N,a}` with covariation `Σ_r`, `IsDetCovMatrix` for `Σ̄`.
5. (`DynCmpFinal`) `smoothDist 2` assembly and `dynamic_comparison_proof` (statement verbatim).

Status: ALL STEPS DONE.  (1) `DynCmpAux1` (this file); (2) `DynCmpAux2`; (3) `DynCmpAux3`; (4a) `DynCmpAux4` (generic enlargement +
`dyncmp_gaussian_comparison`); (4b) `DynCmpAux5` (duality identity for `linCoord`, remainder `L¹` bound), `DynCmpAux6` (bracket error on
`[0,T]`, a copy of `q40b_cov_bound` with a finite-horizon entropy hypothesis); (5a) `DynCmpAux7` (`dyncmp_master`, one particle system);
(5b) `DynCmpFinal` (`dynamic_comparison_proof`, statement verbatim, tied by `example := (@dynamic_comparison_proof : type_of% @HRS.dynamic_comparison)`).
Reused from Q40b (Prop 5.14): `qPhi`, `Br`, `qsb`, `q40b_isDet`, `q40b_integratedCov`, `q40b_ito_stop`, `Fm`, `q40b_Fm_meas`,
`q40b_integrable_prod`, `q40b_rho_bounds`, `q40b_jointCont`, `q40b_regular`.
`#print axioms HRS.dynamic_comparison_proof`: `propext, Classical.choice, Quot.sound, sorryAx`; the `sorryAx` comes only from the 15 MOV
statements reached via `dynamic_entropy_proof` (`movT_traj_bounds, movT_source_exp, movT_pressure_two_sided_C2, movT_cond_narrow,
movT_cond_hyp, movT_reg_ineq, movT_lp_init_limsup, movT_source_exp_uniform, movT_lp_reg_bound, movT_regSeq_exists, movT_Q_tendsto_weak,
movT_source_limit_bdd, movT_init_tendsto, movT_cond_entropy_limit, movT_source_limit_cond`); no sorry in any `DynCmp*` file.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d : ℕ}

/-- `CoeffHyp` only sees `[0,T]`. -/
theorem dyncmp_coeffHyp_congr {m : ℕ} {Λ T : ℝ} {μ μ' : ℝ → Torus d → ℝ} (h : PDE.CoeffHyp m Λ T μ)
    (hag : ∀ r ∈ Set.Icc 0 T, μ' r = μ r) : PDE.CoeffHyp m Λ T μ' where
  prob r hr := by rw [hag r hr]; exact h.prob r hr
  smooth r hr := by rw [hag r hr]; exact h.smooth r hr
  bound r hr := by rw [hag r hr]; exact h.bound r hr
  cont ψ hψ := (h.cont ψ hψ).congr fun r hr => by simp only [hag r hr]

/-- `Regime.Holds` only sees `μ` on `[0,T]`. -/
theorem dyncmp_regime_congr {R : PDE.Regime} {s : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {invβ ν₀ T : ℝ}
    {μ μ' : ℝ → Torus d → ℝ} (h : R.Holds d s M invβ ν₀ T μ) (hag : ∀ r ∈ Set.Icc 0 T, μ' r = μ r) :
    R.Holds d s M invβ ν₀ T μ' := by
  cases R with
  | R1 => exact h
  | R2a => exact h
  | R2b lam0 =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨h1, h2, h3, fun r hr x => by rw [hag r hr]; exact h4 r hr x⟩
  | R2c => exact h
  | R3 => exact h

theorem dyncmp_adjointData_congr {s : ℝ} {m : ℕ} {R : PDE.Regime} {MB Λ VB : ℝ} {D : DynData d} {ν₀ T : ℝ}
    {μ μ' : ℝ → Torus d → ℝ} (h : PDE.AdjointData s m R MB Λ VB D ν₀ T μ)
    (hag : ∀ r ∈ Set.Icc 0 T, μ' r = μ r) : PDE.AdjointData s m R MB Λ VB D ν₀ T μ' :=
  ⟨h.hs, h.hM, h.hV, dyncmp_coeffHyp_congr h.hμ hag, h.hT, dyncmp_regime_congr h.regime hag⟩

/-- The propagator (as a function of `r`) is the classical adjoint solution whenever one exists. -/
theorem dyncmp_propagator_classical {D : DynData d} {ρ : ℝ → Torus d → ℝ} {t : ℝ} {φ : Torus d → ℝ}
    (hex : ∃ f, IsClassicalAdjointSolution D ρ t φ f) :
    IsClassicalAdjointSolution D ρ t φ (fun r => propagator D ρ r t φ) := by
  have hp : (fun r => propagator D ρ r t φ) = hex.choose := by
    funext r
    unfold propagator
    rw [dif_pos hex]
  rw [hp]
  exact hex.choose_spec

/-- **Step (1)**: for the smooth positive trajectory, `ρ` is `(3,Λ)`-regular on `[0,T]`, jointly continuous, and for every
smooth test `φ` the classical adjoint solution exists for all `t ∈ (0,T]` with a `t`-uniform `C²` bound
(`U^{0,0} = id`).  -/
theorem dyncmp_adjoint_package (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (T : ℝ) :
    ∃ Λ : ℝ, IsRegularMF 3 Λ T ρ ∧
      ContinuousOn (fun p : ℝ × Torus d => ρ p.1 p.2) (Set.Icc 0 T ×ˢ Set.univ) ∧
      ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
        ∃ Cφ : ℝ, ∀ t ∈ Set.Icc 0 T,
          IsClassicalAdjointSolution htr.dyn ρ t φ (fun r => propagator htr.dyn ρ r t φ) ∧
          ∀ r ∈ Set.Icc 0 t, Torus.cbNorm 2 (propagator htr.dyn ρ r t φ) ≤ Cφ := by
  have hd1 : 1 ≤ d := by omega
  set j : ℕ := ⌊(d : ℝ) / 2⌋₊ + 5 with hjdef
  have hj : (d : ℝ) / 2 + 4 < j := by
    have := Nat.lt_floor_add_one ((d : ℝ) / 2)
    rw [hjdef]; push_cast; linarith
  set K : ℕ := 2 * j + 4 * d + 20 with hKdef
  have hK6 : (d : ℝ) / 2 + 6 < K := by
    rw [hKdef]; push_cast
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have H := movf_finiteRegHyp htr.hs0 htr.hsd htr.hβ htr.V_smooth htr.init K hK6
  obtain ⟨ρc, hρc, hρ⟩ := htr.global K hK6
  obtain ⟨ρβ, hρβ, hρC, hpos, -⟩ := PDE.finite_reg_thermal hd1 s β β K V ρ₀ H β ⟨le_rfl, le_rfl⟩
  obtain ⟨R, Λ, Λ₀, c₀, Cd, κ, hc₀, hκ, hall⟩ :=
    PDE.MFAdjoint.finiteReg_hypotheses hd1 s β β K V ρ₀ H j hj le_rfl
  obtain ⟨hFz, hAD, -⟩ := hall β ⟨le_rfl, le_rfl⟩ ρc hρc ρβ hρβ hρC hpos
  set T' : ℝ := max T 1 with hT'
  have hT'pos : 0 < T' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hTT' : T ≤ T' := le_max_left _ _
  have hag : ∀ r ∈ Set.Icc (0 : ℝ) T', ρ r = PDE.mfPath ρc r := fun r hr => (hρ r hr.1).symm
  have hA := dyncmp_adjointData_congr (hAD T' hT'pos) hag
  have hmj : PDE.mStar d + 2 ≤ j := PDE.MFAdjoint.mStar_add_two_le_of_gt hj
  have hm3 : 3 ≤ PDE.mStar d := by unfold PDE.mStar; omega
  -- regularity
  have hreg : IsRegularMF 3 Λ T ρ := fun r hr =>
    ⟨mova_isCk_of_le (by exact_mod_cast (by omega : 3 ≤ j + 3)) (hA.hμ.smooth r ⟨hr.1, hr.2.trans hTT'⟩),
      (KernelGrad.cbNorm_mono (by omega : 3 ≤ j + 3)).trans (hA.hμ.bound r ⟨hr.1, hr.2.trans hTT'⟩)⟩
  -- joint continuity
  have hK2 : (d : ℝ) / 2 + 2 < K := by linarith
  have hreal := PDE.MFGlobal.isRealCoeff_of_isMFSolutionHK hd1 s β β K V ρ₀ H β ⟨le_rfl, le_rfl⟩ ρc hρc
  have hSol : ∀ T, PDE.MFApriori.MFSolRealOn d s V β⁻¹ (K : ℝ) ρ₀ ρc T := fun T =>
    ⟨PDE.MFApriori.IsMFSolutionHK.toSolOn hρc T, fun τ hτ => hreal τ hτ.1⟩
  have hjc := (PDE.MFApriori.continuousOn_mfPath_prod_on hd1 s H.hs0 H.hsd K hK2 V ρ₀ H.hV β⁻¹ ρc
    (hSol T)).1
  refine ⟨Λ, hreg, hjc.congr fun p hp => ?_, ?_⟩
  · show ρ p.1 p.2 = PDE.mfPath ρc p.1 p.2
    rw [hρ p.1 hp.1.1]
  intro φ hφ
  have hφc : Continuous φ := PDE.MFLinear.continuous_of_isSmooth hφ
  have hφS : MemSobolev (j : ℝ) φ := PDE.MFSemigroup.memSobolev_of_isSmooth hφ _
  obtain ⟨C, Cs, hC, hCs, hmain⟩ := PDE.adjoint_torus_classical hd1 s htr.hs0 htr.hsd j
    (by omega) R 1 Λ (Torus.cbNorm (j + 3) V)
  have hKf := PDE.ClassicalAux.convKernelFacts hd1 htr.dyn
  have hV2 : Torus.IsCk 2 htr.dyn.V := mova_isCk_two_of_smooth htr.V_smooth
  have hp0 : propagator htr.dyn ρ 0 0 φ = φ :=
    PDE.MFSemigroup.propagator_zero htr.dyn hKf (mova_isCk_one_of_two hV2) ρ
      (mova_isCk_of_le (by exact_mod_cast (by omega : 1 ≤ j + 3))
        (hA.hμ.smooth 0 ⟨le_rfl, hT'pos.le⟩)) (mova_isCk_two_of_smooth hφ)
  set lam : ℝ := R.lambdaM (Cs (PDE.mStar d)) β⁻¹ (PDE.thetaOrder d s) with hlam
  refine ⟨max (C * Real.exp (|lam| * T') * sobolevNorm (PDE.mStar d : ℝ) φ) (Torus.cbNorm 2 φ),
    fun t ht => ?_⟩
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0
    have hex : ∃ f, IsClassicalAdjointSolution htr.dyn ρ 0 φ f :=
      ⟨_, PDE.MFSemigroup.isClassical_zero htr.dyn hKf (mova_isCk_one_of_two hV2) ρ
        (mova_isCk_of_le (by exact_mod_cast (by omega : 1 ≤ j + 3))
          (hA.hμ.smooth 0 ⟨le_rfl, hT'pos.le⟩)) (mova_isCk_two_of_smooth hφ)⟩
    refine ⟨dyncmp_propagator_classical hex, fun r hr => ?_⟩
    have hr0 : r = 0 := le_antisymm hr.2 hr.1
    subst hr0
    rw [hp0]
    exact le_max_right _ _
  have htT' : t ∈ Set.Ioc 0 T' := ⟨hpos, ht.2.trans hTT'⟩
  obtain ⟨hcl, hprop, -, hbd⟩ := hmain htr.dyn β⁻¹ T' ρ hA t htT' φ hφc hφS
  refine ⟨dyncmp_propagator_classical ⟨_, hcl⟩, fun r hr => ?_⟩
  refine (hbd r hr).trans (le_trans ?_ (le_max_left _ _))
  have hn0 : 0 ≤ sobolevNorm (PDE.mStar d : ℝ) φ := Real.sqrt_nonneg _
  have h1 : Real.exp (lam * (t - r)) ≤ Real.exp (|lam| * T') := by
    refine Real.exp_le_exp.2 ?_
    calc lam * (t - r) ≤ |lam| * (t - r) := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith [hr.2])
      _ ≤ |lam| * T' := mul_le_mul_of_nonneg_left (by linarith [hr.1, ht.2, hTT']) (abs_nonneg _)
  calc C * Real.exp (lam * (t - r)) * sobolevNorm (PDE.mStar d : ℝ) φ
      ≤ C * Real.exp (|lam| * T') * sobolevNorm (PDE.mStar d : ℝ) φ := by gcongr
    _ = _ := rfl
end HRS

end
