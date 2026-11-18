import HRS.Appendix.B15BAux3
import HRS.Appendix.B15DAux5
import HRS.PDE.TorusFPEntropyMeasure
import HRS.PDE.TorusFPExist

/-!
# Packet B15E: assembly of Proposition B.15 (strong branch) -- PLAN and part 1 (infrastructure)

Target: `b15_sde_entropy_law_free_proof` (HRS/Appendix/B15Final.lean), a relocated proof of
`b15_sde_entropy_law_free` (B15Aux1.lean:95); TeX M L12153-12235 (Steps 1-4), plus the dispatcher
`b15_sde_entropy_law_of_free_proof` for the strong branch.  Only `_proof` versions of the packet
B/C/D2/D3 results are used (the frozen sorried copies are never referenced, in particular the
Step-4 assembly of B15BAux1 is re-assembled downstream in B15EAux6).

## Mathematical route (two limits, `δ → 0` first, then `M → ∞`)

`V ∈ C²` only, but D1/D2/D3 (Fokker-Planck on `𝕋^{Nd}`, Ito duality, free-energy dissipation) need a smooth
potential.  Hence, at each fixed level `M ≥ 0` of the truncated kernel `g_M` (packet C):

* **Stage 1 (fixed `M`, `V_k → V` in `C¹`, `V_k ≤ V`).**  `d1_exists_C2_approx` (D1 existence packet,
  already proved: `|φ-ψ| ≤ ε`, `‖∇φ-∇ψ‖ ≤ ε`) gives smooth `ψ_k`; `V_k := ψ_k - ε_k ≤ V` (a constant shift
  changes neither drift nor Fisher integrand).  With `D_k := {D with V := V_k}` let `Y^k` be the global
  solution of the level-`M` regularised SDE for `V_k` (same `ℱ'`, `W'`, `Y₀`).  D2+D3 give, for each `k`,
  the exact dissipation inequality for `U_k^M` with right-hand side `𝓗_{U_k^M}(P_0) ≤ 𝓗_{U^M}(P_0)`
  (since `U_k^M ≤ U^M`).  A Gronwall estimate gives `Y^k → Y` (the level-`M` solution for `V`)
  uniformly on `[0,T]` a.s., hence narrow convergence of all time marginals; lower semicontinuity of the
  entropy (generic: potentials converge uniformly) and of the Fisher information (integrands converge
  uniformly) plus Fatou in `r` and the `EReal` bookkeeping of `b15b_step4_limit` give the level-`M`
  inequality for `V ∈ C²` (`b15e_regularised_entropy`).
* **Stage 2 (`M_n = n → ∞`).**  Exactly Step 4 of B.15 with the proved packet-B/C ingredients
  (`b15c_regularised_eq_strong_proof`, `b15b_*_proof`), then `b15c_gibbsEntropyGen_le_proof`
  (`𝓗_{U^M}(P_0) ≤ 𝓗_G(P_0)`).
* The conclusion's remaining conjuncts: density from finiteness of the entropy, FKE from
  `selected_law_fke`, `t = 0` trivial (`volume {0} = 0`).

## Sub-lemmas and sizes (file / names `b15e_*`)

* B15EAux1 (S-M): `b15e_withV`; filtration wrapper `ℱ' t := ℱ (max t 0)`
  (`IsBrownianFiltration`, adaptedness); measurability of `Torus.rep`; lift `Y₀ = rep ∘ X 0`; existence of
  the level-`M` regularised solution from `exists_sde_solution_global_nonneg` and
  `b15c_liftedDriftReg_isLipschitz_proof`.
* B15EAux2 (M): `b15e_gronwall_unif` (integral Gronwall, sup bound), a.s. pathwise stability of the two
  additive SDEs (drifts `b_k`, `b` with `‖b_k - b‖ ≤ ε`, `b` Lipschitz), `b15e_marginal_tendsto_unif`
  (narrow convergence of marginals from a.s. uniform convergence).
* B15EAux3 (M): weights: `b15e_entropyGen_mono` (`U₁ ≤ U₂ ⇒ 𝓗_{U₁} ≤ 𝓗_{U₂}`), generic entropy lsc for
  uniformly convergent potentials (`b15e_entropyGen_liminf_le`), constant-shift invariance.
* B15EAux4 (M-L): bridges to `𝕋^{Nd}`: `b15e_relEntropy_map` (`klDiv` of a measurable-equivalence push-forward),
  `b15e_gibbsMeasure_eq_map`, `b15e_gibbsEntropyGen_eq` (`𝓗_U = relEntropy(P.map e | d1_gibbsMeasure) - log Z`),
  `b15e_fisherInfoGen_le` (`b15_fisherInfoGen ≤ d1_fisherInfo`), `b15e_law_eq_fp` (downstream copy of
  `b15d_law_eq_fp` with the `_proof`s), `b15e_law_entropy` (D2 + D3 combined, in `b15c`/`b15_` language).
* B15EAux5 (M): `b15e_testField_bounded`, `b15e_fisherIntegrand_sub` (integrands for `U + ∑ g(x_i)`),
  Fisher lsc for uniformly convergent integrands (`b15e_fisherInfoGen_liminf_le_unif`), Fatou in `r`,
  `b15e_limit_core`, `b15e_measurable_fisherInfoGen_reg` (copy with `_proof`s).
* B15EAux6 (M): `b15e_smooth_approx_below` (from `d1_exists_C2_approx`), comparison of `D` and `D_k`,
  `b15e_reg_ineq_smooth` (D2 + D3 + bridges in the configuration language).
* B15EAux7 (L): Stage 1, `b15e_regularised_entropy`.
* B15EAux8 (S-M): Stage-2 copies `b15e_step4_limit` etc. with the `_proof`s.
* B15Final (S): `b15_sde_entropy_law_free_proof` verbatim statement + `type_of%` tie; dispatcher
  `b15_sde_entropy_law_of_free_proof` (the Cépa-Lépingle branch is `cepa_entropy_confined`, untouched).

STATUS: all of the above is proved (standard axioms only for the free lemma).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-! ### The dynamical data with a different one-body potential -/

/-- `D` with the one-body potential replaced by `V'` (everything else unchanged). -/
def b15e_withV (D : DynData d) (V' : Torus d → ℝ) : DynData d := { D with V := V' }

@[simp] theorem b15e_withV_V (D : DynData d) (V' : Torus d → ℝ) : (b15e_withV D V').V = V' := rfl
@[simp] theorem b15e_withV_invβ (D : DynData d) (V' : Torus d → ℝ) :
    (b15e_withV D V').invβ = D.invβ := rfl
@[simp] theorem b15e_withV_s (D : DynData d) (V' : Torus d → ℝ) : (b15e_withV D V').s = D.s := rfl
@[simp] theorem b15e_withV_M (D : DynData d) (V' : Torus d → ℝ) : (b15e_withV D V').M = D.M := rfl

/-! ### The filtration wrapper `ℱ' t := ℱ (max t 0)` -/

/-- `ℱ' t = ℱ (max t 0)`: a filtration indexed by all of `ℝ` that is constant (`= ℱ 0`) on `(-∞,0]`.
`IsFilteredSolution.adapted` only constrains `t : ℝ≥0`, while `exists_sde_solution_global` needs
`Y₀` to be `ℱ t`-measurable for every real `t`. -/
def b15e_shiftFil {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ mΩ) : Filtration ℝ mΩ where
  seq t := ℱ (max t 0)
  mono' := fun _ _ h => ℱ.mono (max_le_max h le_rfl)
  le' := fun _ => ℱ.le _

theorem b15e_shiftFil_apply {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ mΩ) (t : ℝ) :
    b15e_shiftFil ℱ t = ℱ (max t 0) := rfl

theorem b15e_shiftFil_nnreal {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ mΩ) (t : ℝ≥0) :
    b15e_shiftFil ℱ (t : ℝ) = ℱ (t : ℝ) := by
  rw [b15e_shiftFil_apply, max_eq_left t.coe_nonneg]

theorem b15e_shiftFil_brownian {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ mΩ} {ι : Type*} [Fintype ι] {W' : ℝ≥0 → Ω → ι → ℝ}
    (h : IsBrownianFiltration P ℱ W') : IsBrownianFiltration P (b15e_shiftFil ℱ) W' where
  complete := fun t s hs hP => h.complete (max t 0) s hs hP
  adapted := fun t => by rw [b15e_shiftFil_nnreal]; exact h.adapted t
  zero := h.zero
  cont := h.cont
  indep_incr := fun s t hst => by rw [b15e_shiftFil_nnreal]; exact h.indep_incr s t hst
  gaussian_incr := h.gaussian_incr

theorem b15e_measurable_rep (d : ℕ) : Measurable (Torus.rep : Torus d → Euc d) := by
  have h : Measurable (fun (x : Torus d) (i : Fin d) =>
      ((AddCircle.equivIco (1 : ℝ) 0 (x i) : Set.Ico (0 : ℝ) (0 + 1)) : ℝ)) :=
    measurable_pi_iff.2 fun i => measurable_subtype_coe.comp
      ((AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.comp (measurable_pi_apply i))
  exact (WithLp.measurable_toLp 2 _).comp h

/-! ### The initial lift and the level-`M` regularised solution -/

/-- The lift `Y₀ = rep ∘ X_0` of the initial configuration to the covering space. -/
def b15e_initLift {Ω : Type*} (X : ℝ≥0 → Ω → Config d N) : Ω → Fin N → Euc d :=
  fun ω i => Torus.rep (X 0 ω i)

theorem b15e_initLift_measurable {Ω : Type*} [mΩ : MeasurableSpace Ω] {ℱ : Filtration ℝ mΩ}
    {X : ℝ≥0 → Ω → Config d N} (h0 : Measurable[ℱ 0] (X 0)) (t : ℝ) :
    Measurable[b15e_shiftFil ℱ t] (b15e_initLift X) := by
  have h1 : Measurable[b15e_shiftFil ℱ t] (X 0) :=
    h0.mono (ℱ.mono (le_max_right t 0)) le_rfl
  have h2 : Measurable (fun x : Config d N => fun i => Torus.rep (x i)) :=
    measurable_pi_iff.2 fun i => (b15e_measurable_rep d).comp (measurable_pi_apply i)
  exact h2.comp h1

theorem b15e_mk_initLift {Ω : Type*} (X : ℝ≥0 → Ω → Config d N) (ω : Ω) :
    (fun i => Torus.mk (b15e_initLift X ω i)) = X 0 ω := by
  funext i; simp [b15e_initLift, Torus.mk_rep]

/-- The level-`M` regularised SDE has a global strong solution for the shifted filtration:
`exists_sde_solution_global_nonneg` with the proved Lipschitz property of the drift. -/
theorem b15e_exists_regularised {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ' : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hW' : IsBrownianFiltration P ℱ' W') (D : DynData d) (hV : Torus.IsCk 2 D.V) (M : ℝ)
    (Y₀ : Ω → Fin N → Euc d) (hY₀ : ∀ t : ℝ, Measurable[ℱ' t] Y₀) :
    ∃ Y : ℝ → Ω → (Fin N → Euc d),
      IsAdditiveSDESolution P ℱ' W' (fun _ => b15c_liftedDriftReg D M) (liftedNoise D) Y₀
        (fun _ => ⊤) Y :=
  (exists_sde_solution_global_nonneg hW' _ (b15c_liftedDriftReg_isLipschitz_proof D hV M)
    (liftedNoise D) Y₀ hY₀).imp fun _ h => h.1

/-- The time-`0` marginal of every regularised solution started at `rep ∘ X 0` is the time-`0` marginal of
`X`: `selectedLaw P (b15c_regProcess Y) 0 = selectedLaw P X 0`. -/
theorem b15e_selectedLaw_zero {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ' : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {b : ℝ → (Fin N → Euc d) → (Fin N → Euc d)} {σ : (Fin N × Fin d) → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} {Y : ℝ → Ω → (Fin N → Euc d)}
    (hY : IsAdditiveSDESolution P ℱ' W' b σ (b15e_initLift X) (fun _ => ⊤) Y) :
    selectedLaw P (b15c_regProcess Y) 0 = selectedLaw P X 0 := by
  unfold selectedLaw
  have : b15c_regProcess Y (Real.toNNReal 0) = X (Real.toNNReal 0) := by
    funext ω
    simp only [Real.toNNReal_zero]
    rw [← b15e_mk_initLift X ω]
    funext i
    simp [b15c_regProcess, projectPath, hY.init ω]
  rw [this]

end HRS
