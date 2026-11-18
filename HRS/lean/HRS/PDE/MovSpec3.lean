import HRS.PDE.MovSpec2b
import HRS.PDE.MeanFieldDefs
import HRS.Equilibrium.PoleCavity

/-!
# MOVSPEC (part 3): modulated free energy dissipation (Prop 3.41) and consumer bridges

TeX (M): Prop `B:prop:mfe-uniform` L3204-3217 and proof L3219-3236 (`B:eq:mfe-dissipation` L3221-3224);
exact source `N:eq:source` L6429-6441; relative entropy convention L455-457.

`mov_mfe_ineq` is the integrated form of `B:eq:mfe-dissipation` (Fisher term dropped):
`𝖤_N(f^t,μ^t) ≤ 𝖤_N(f^0,μ^0) - ½∫_0^t∫Comm_N(u_V^r;X,μ^r) f^r dr`, `𝖤_N(f,μ) = β⁻¹N⁻¹H(f|μ^{⊗N}) + ∫F_N f`
(`modulatedFreeEnergy`), `u_V = β⁻¹∇log μ + ∇g*μ + ∇V` (`mfeTransport`).

Route chosen (it makes the "diagonal-truncation lower semicontinuity of `E_N`", ISSUES MOV item 6, M L3220, unnecessary
as a separate packet): `𝖤_N(f,μ) = β⁻¹N⁻¹(H(f|Q_N) - log K_N(μ))` for finite entropy (`movT_relEntropy_split`: the
energy part of `H(f|μ^{⊗N})`-lsc is carried by the lsc of `H(·|Q^M)` proved in `movT_entropy_lsc`), so that
`mov_mfe_ineq` follows from `mov_ent_ineq` and the normaliser identity `movT_logK_integral`
(`d/dt log K_N = βN E_{Q_N}[C_N(u;μ)]`, which I checked by hand for the exact formulae of `N:eq:source`: the pair part
of `∂_t log w` integrates by parts against `Q_N` into `(2N²)⁻¹∑h_u`, the one-body parts into
`-N⁻¹∑∫h_u(x_i,y)dμ + ½∬h_u`; this is the sentence "the derivative of the normaliser subtracts its expectation",
M L6439).  The two packets are static (no process, no regularisation).

Chain plan (this file): `movT_relEntropy_split` (SPEC, M), `movT_logK_integral` (SPEC, M), glue `mov_mfe_ineq`
(proved), bridge `movT_traj_of_global` (SPEC, M).
Review 1 (D4): `MovTraj` now needs only `IsCk 2` densities with a `C²` bound, so `MFEHyp` (`C^{m_*+2}`) is covered by the
bridge `movT_hyp_of_mfeHyp` (with `movT_isC12Test_of_weak`); the pressure inputs are the `C²` versions
(`movT_pressure_two_sided_C2`, `movT_source_exp`).  The energy lsc packet of the first draft was deleted (D7).
Bridges A-D at the end of the file.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-- **SPEC (sorried, M): `H(f|Q_N) = H(f|μ^{⊗N}) + βN∫F_N f + log K_N`** (definition `H:eq:modulated-gibbs`,
M L446-452, `Q = K⁻¹e^{-βNF_N}μ^{⊗N}`; Mathlib `integral_llr_tilted_right`), with the finiteness bookkeeping:
for a positive `C²` probability density `ρ` (Review 1, D4) and a probability law `ν`, `H(ν|Q_N(ρ)) < ∞` iff `𝖤_N(ν,μ) < ∞`
(`MFEFinite`: finite `H(ν|μ^{⊗N})` and integrable `F_N`; `F_N ≥ -C` is bounded below and `F_N ≤ C(1 + ∑_{i≠j} g)`),
and then the identity holds for the real parts.  `K_N` is `gibbsNormalizer`, `∈ (0,∞)` (`perturbed_pressure`). -/
theorem movT_relEntropy_split (hN : 2 ≤ N) {D : DynData d} (hβ : 0 < D.invβ) {ρ : Torus d → ℝ}
    (hρ : IsProbDensity ρ) (hs : Torus.IsCk 2 ρ) (hpos : ∀ x, 0 < ρ x)
    {ν : Measure (Config d N)} [IsProbabilityMeasure ν] :
    (relEntropy ν (modulatedGibbs (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal ρ)) ≠ ⊤ ↔
      MFEFinite d D.s ν (withDensityReal ρ)) ∧
    (MFEFinite d D.s ν (withDensityReal ρ) →
      (relEntropy ν (modulatedGibbs (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal ρ))).toReal =
        (relEntropy ν (Measure.pi fun _ : Fin N => withDensityReal ρ)).toReal +
          D.invβ⁻¹ * N * ∫ X, rieszEnergy d D.s X (withDensityReal ρ) ∂ν +
          Real.log (gibbsNormalizer (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal ρ))) := by
  sorry

/-- **SPEC (sorried, M): the normaliser identity** `log K_N(μ^t) - log K_N(μ^0) = βN ∫_0^t E_{Q_N^r}[C_N(u^r;μ^r)] dr`
(`K_N = ∫e^{-βNF_N}dμ^{⊗N}`, `β = D.invβ⁻¹`, `u^r` the transport field of `N:eq:velocity`), with `r ↦ E_{Q^r}[C_N]`
integrable on `[0,T]` and `C_N` integrable under `Q_N^r` (`movT_source_exp`).  Differentiation of `log K_N(μ^r)`
(dominated by the nonnegative weak interaction, M L6328-6329 and L6403-6405), `∂_tμ = Div(μu)` from `MovTraj`
(`IsMeanFieldSolution` + `IsC12Test`), integration by parts in each variable (M L6436-6441).  Hand-checked: for `N = 1`
and in general `(log K_N)' = E_Q[-βN∂_tF_N + ∑_i ∂_t log ρ(x_i)] = βN E_Q[C_N(u;μ)]`. -/
theorem movT_logK_integral (hN : 2 ≤ N) {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : MovTraj D T ρ) :
    IntegrableOn (fun r => ∫ X, movT_comm D N ρ r X ∂(movT_Q (periodicRiesz d D.s) D N ρ r))
      (Set.Icc 0 T) ∧
    ∀ t ∈ Set.Icc 0 T,
      Real.log (gibbsNormalizer (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal (ρ t))) -
        Real.log (gibbsNormalizer (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal (ρ 0))) =
      D.invβ⁻¹ * N * ∫ r in Set.Icc 0 t,
        ∫ X, movT_comm D N ρ r X ∂(movT_Q (periodicRiesz d D.s) D N ρ r) := by
  sorry

/-- **`mov_mfe_ineq` (modulated free energy dissipation, Fisher term dropped).**  The integrated form of
`B:eq:mfe-dissipation` (M L3221-3224): for all `t ∈ [0,T]`, `𝖤_N(f_N^t,μ^t) < ∞`, `Comm_N(u_V^r;·,μ^r)` is
`f_N^r`-integrable, `r ↦ ∫Comm_N f_N^r` is integrable and
`𝖤_N(f_N^t,μ^t) ≤ 𝖤_N(f_N^0,μ^0) - ½∫_0^t∫Comm_N(u_V^r;X,μ^r) f_N^r(dX) dr`.
Standing assumptions: `MovHyp` (the hypotheses of `MFEHyp` on the process and the background, with the regularity of
`MovTraj`), `𝖤_N(f_N^0,μ^0) < ∞`.  Proof: `mov_ent_ineq` (the finite relative entropy `H(f^0|Q^0)` follows from
`MFEFinite` by `movT_relEntropy_split`), `movT_relEntropy_split` at times `0` and `t`, `movT_logK_integral`, and
`movT_commAt_eq_half`; the terms `∫E_Q C_N` cancel exactly.  Discharges the first sentence of the proof of Prop 3.41
(M L3220-3224: modulated free energy calculation for the regularised laws, passage to the selected law by lower
semicontinuity, discarding the Fisher information) for `mfe_uniform` (`Coercivity.lean:3395`). -/
theorem mov_mfe_ineq (hN : 2 ≤ N) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ} {X₀ : Ω → Config d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (h : MovHyp P D N T ρ X₀ W X)
    (hfin : MFEFinite d D.s (P.map X₀) (withDensityReal (ρ 0))) :
    ∀ t ∈ Set.Icc 0 T,
      MFEFinite d D.s (P.map (X t.toNNReal)) (withDensityReal (ρ t)) ∧
      (∀ r ∈ Set.Icc 0 t, Integrable
        (fun Z => commQuantity d D.s (mfeTransport D (ρ r)) Z (withDensityReal (ρ r)))
        (P.map (X r.toNNReal))) ∧
      IntegrableOn (fun r => ∫ Z, commQuantity d D.s (mfeTransport D (ρ r)) Z (withDensityReal (ρ r))
        ∂(P.map (X r.toNNReal))) (Set.Icc 0 t) ∧
      modulatedFreeEnergy d D.s D.invβ (P.map (X t.toNNReal)) (withDensityReal (ρ t)) ≤
        modulatedFreeEnergy d D.s D.invβ (P.map X₀) (withDensityReal (ρ 0)) -
          (1 / 2) * ∫ r in Set.Icc 0 t, ∫ Z, commQuantity d D.s (mfeTransport D (ρ r)) Z
            (withDensityReal (ρ r)) ∂(P.map (X r.toNNReal)) := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hS := h.sol
  have hβ := h.traj.pos_temp
  haveI : IsProbabilityMeasure (P.map X₀) := inferInstance
  haveI hfp : ∀ r : ℝ, IsProbabilityMeasure (P.map (X r.toNNReal)) := fun r =>
    inferInstance
  have hsplit : ∀ r ∈ Set.Icc 0 T, ∀ (ν : Measure (Config d N)) [IsProbabilityMeasure ν],
      (relEntropy ν (movT_Q (periodicRiesz d D.s) D N ρ r) ≠ ⊤ ↔ MFEFinite d D.s ν (withDensityReal (ρ r))) ∧
      (MFEFinite d D.s ν (withDensityReal (ρ r)) →
        modulatedFreeEnergy d D.s D.invβ ν (withDensityReal (ρ r)) =
          D.invβ / N * ((relEntropy ν (movT_Q (periodicRiesz d D.s) D N ρ r)).toReal -
            Real.log (gibbsNormalizer (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal (ρ r))))) := by
    intro r hr ν _
    obtain ⟨h1, h2⟩ := movT_relEntropy_split hN (D := D) hβ (h.traj.mf.density r hr)
      (h.traj.ck r hr) (h.traj.pos r hr) (ν := ν)
    refine ⟨h1, fun hfin' => ?_⟩
    have h3 := h2 hfin'
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    unfold modulatedFreeEnergy normRelEntropy
    rw [ENNReal.toReal_div, ENNReal.toReal_natCast]
    have hinv : D.invβ * D.invβ⁻¹ = 1 := mul_inv_cancel₀ hβ.ne'
    have h4 : (relEntropy ν (Measure.pi fun _ : Fin N => withDensityReal (ρ r))).toReal =
        (relEntropy ν (movT_Q (periodicRiesz d D.s) D N ρ r)).toReal -
          D.invβ⁻¹ * N * ∫ X, rieszEnergy d D.s X (withDensityReal (ρ r)) ∂ν -
          Real.log (gibbsNormalizer (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal (ρ r))) := by
      unfold movT_Q; linarith
    rw [h4]
    field_simp
    have : D.invβ * (D.invβ⁻¹ * (N : ℝ) * ∫ X, rieszEnergy d D.s X (withDensityReal (ρ r)) ∂ν) =
        N * ∫ X, rieszEnergy d D.s X (withDensityReal (ρ r)) ∂ν := by
      rw [← mul_assoc, ← mul_assoc, hinv, one_mul]
    nlinarith
  -- finiteness of the initial entropy and the entropy inequality
  have hfinQ : relEntropy (P.map X₀) (movT_Q (periodicRiesz d D.s) D N ρ 0) ≠ ⊤ :=
    ((hsplit 0 ⟨le_rfl, hT⟩ (P.map X₀)).1).2 hfin
  obtain ⟨hHt, hint, hintOn, hineq⟩ := (mov_ent_ineq hN P h hfinQ).1 t ht
  have hMFEt := ((hsplit t ht (P.map (X t.toNNReal))).1).1 hHt
  obtain ⟨hlogKint, hlogK⟩ := movT_logK_integral hN h.traj
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hβN : 0 < D.invβ⁻¹ * N := mul_pos (inv_pos.2 hβ) hNpos
  set f : ℝ → Measure (Config d N) := fun r => P.map (X r.toNNReal) with hf
  set Cf : ℝ → ℝ := fun r => ∫ Z, movT_comm D N ρ r Z ∂(f r) with hCf
  set EQ : ℝ → ℝ := fun r => ∫ Z, movT_comm D N ρ r Z ∂(movT_Q (periodicRiesz d D.s) D N ρ r) with hEQ
  set G : ℝ → ℝ := fun r => ∫ Z, movT_source D N ρ r Z ∂(f r) with hG
  have hsrc : ∀ r Z, movT_source D N ρ r Z = -(D.invβ⁻¹ * N) * (movT_comm D N ρ r Z - EQ r) :=
    fun r Z => rfl
  have hcomm_int : ∀ r ∈ Set.Icc 0 t, Integrable (movT_comm D N ρ r) (f r) := by
    intro r hr
    have h1 := hint r hr
    have h2 : Integrable (fun Z => EQ r - (D.invβ⁻¹ * N)⁻¹ * movT_source D N ρ r Z) (f r) :=
      (integrable_const _).sub (h1.const_mul _)
    refine h2.congr (Eventually.of_forall fun Z => ?_)
    simp only [hsrc]
    field_simp
    ring
  have hG_eq : ∀ r ∈ Set.Icc 0 t, G r = -(D.invβ⁻¹ * N) * (Cf r - EQ r) := by
    intro r hr
    haveI := hfp r
    simp only [hG, hCf, hsrc]
    rw [integral_const_mul, integral_sub (hcomm_int r hr) (integrable_const _)]
    simp
  have hCf_eq : ∀ r ∈ Set.Icc 0 t, Cf r = EQ r - (D.invβ⁻¹ * N)⁻¹ * G r := by
    intro r hr
    rw [hG_eq r hr]
    field_simp
    ring
  have hEQint : IntegrableOn EQ (Set.Icc 0 t) :=
    hlogKint.mono_set (Set.Icc_subset_Icc le_rfl ht.2)
  have hCfint : IntegrableOn Cf (Set.Icc 0 t) := by
    have : IntegrableOn (fun r => EQ r - (D.invβ⁻¹ * N)⁻¹ * G r) (Set.Icc 0 t) :=
      hEQint.sub (hintOn.const_mul _)
    exact this.congr_fun (fun r hr => (hCf_eq r hr).symm) measurableSet_Icc
  have hint_G : ∫ r in Set.Icc 0 t, G r = -(D.invβ⁻¹ * N) * ((∫ r in Set.Icc 0 t, Cf r) - ∫ r in Set.Icc 0 t, EQ r) := by
    rw [← integral_sub hCfint hEQint, ← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Icc fun r hr => hG_eq r hr
  have hq : ∀ r Z, commQuantity d D.s (mfeTransport D (ρ r)) Z (withDensityReal (ρ r)) =
      2 * movT_comm D N ρ r Z := by
    intro r Z
    have := movT_commAt_eq_half D N (ρ r) Z
    unfold movT_comm
    linarith
  refine ⟨hMFEt, fun r hr => ?_, ?_, ?_⟩
  · have := (hcomm_int r hr).const_mul 2
    exact this.congr (Eventually.of_forall fun Z => (hq r Z).symm)
  · have this : IntegrableOn (fun r => 2 * Cf r) (Set.Icc 0 t) := hCfint.const_mul 2
    refine this.congr_fun (fun r hr => ?_) measurableSet_Icc
    simp only [hCf]
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun Z => (hq r Z).symm)
  · have hE0 := (hsplit 0 ⟨le_rfl, hT⟩ (P.map X₀)).2 hfin
    have hEt := (hsplit t ht (P.map (X t.toNNReal))).2 hMFEt
    rw [hEt, hE0]
    have hK := hlogK t ht
    have hcq : ∫ r in Set.Icc 0 t, ∫ Z, commQuantity d D.s (mfeTransport D (ρ r)) Z
        (withDensityReal (ρ r)) ∂(P.map (X r.toNNReal)) = 2 * ∫ r in Set.Icc 0 t, Cf r := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Icc fun r _ => ?_
      simp only [hCf, hf]
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun Z => hq r Z)
    rw [hcq]
    have hH : (relEntropy (P.map (X t.toNNReal)) (movT_Q (periodicRiesz d D.s) D N ρ t)).toReal ≤
        (relEntropy (P.map X₀) (movT_Q (periodicRiesz d D.s) D N ρ 0)).toReal +
          ∫ r in Set.Icc 0 t, G r := hineq
    have hinvβ : D.invβ * D.invβ⁻¹ = 1 := mul_inv_cancel₀ hβ.ne'
    have hpos : 0 < D.invβ / N := div_pos hβ hNpos
    -- H_t - log K_t - (H_0 - log K_0) ≤ -βN ∫ Cf
    have key : (relEntropy (P.map (X t.toNNReal)) (movT_Q (periodicRiesz d D.s) D N ρ t)).toReal -
        Real.log (gibbsNormalizer (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal (ρ t))) ≤
        (relEntropy (P.map X₀) (movT_Q (periodicRiesz d D.s) D N ρ 0)).toReal -
        Real.log (gibbsNormalizer (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal (ρ 0))) -
          D.invβ⁻¹ * N * ∫ r in Set.Icc 0 t, Cf r := by
      rw [hint_G] at hH
      have hK' : Real.log (gibbsNormalizer (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal (ρ t))) =
          Real.log (gibbsNormalizer (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal (ρ 0))) +
            D.invβ⁻¹ * N * ∫ r in Set.Icc 0 t, EQ r := by
        have := hK; simp only [hEQ] at *; linarith
      rw [hK']
      nlinarith
    have := mul_le_mul_of_nonneg_left key hpos.le
    have h5 : D.invβ / N * (D.invβ⁻¹ * N * ∫ r in Set.Icc 0 t, Cf r) = ∫ r in Set.Icc 0 t, Cf r := by
      field_simp
    nlinarith

/-! ### Bridges from the consumers' hypotheses (Review 1, bridges A-D) -/

/-- **SPEC (sorried, M): `IsC12Test` from a weak solution** (Review 1, D4).  A weak mean-field solution with
`(m_*+2, Λ)`-regular, uniformly positive densities (the hypotheses of `MFEHyp`) is classical: `ρ ∈ C([0,T];C^{m_*+1})`
(interpolation between the uniform `C^{m_*+2}` bound and narrow continuity), `∂_tρ = κΔρ + div(ρ∇(V+g*ρ))` is continuous
and the weak formulation `IsMeanFieldSolution.weak` integrates by parts to the pointwise equation; hence
`IsC12Test T ρ ρt` with `ρt` that right-hand side. -/
theorem movT_isC12Test_of_weak {D : DynData d} {T Λ lam₀ : ℝ} {ρ : ℝ → Torus d → ℝ}
    (hM : D.M = -1) (hβ : 0 < D.invβ) (hV : Torus.IsCk (PDE.mStar d + 2) D.V)
    (hmf : IsMeanFieldSolution D T ρ) (hreg : IsRegularMF (PDE.mStar d + 2) Λ T ρ)
    (hpos : 0 < lam₀ ∧ ∀ t ∈ Set.Icc 0 T, ∀ x, lam₀ ≤ ρ t x) :
    ∃ ρt : ℝ → Torus d → ℝ, IsC12Test T ρ ρt := by
  sorry

/-- **Bridge D (proved): the particle-system hypotheses and a `MovTraj` give `MovHyp`** (`IsParticleSystem` has exactly the
fields `brownian`, `indep`, `sol`). -/
theorem movT_hyp_of_parts {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {D : DynData d} {T : ℝ}
    {ρ : ℝ → Torus d → ℝ} {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} (htr : MovTraj D T ρ) (hb : IsVectorBrownian P W)
    (hi : ProbabilityTheory.IndepFun X₀ (fun ω => fun t : ℝ≥0 => W t ω) P)
    (hs : IsStrongSolution P D T X₀ W X)
    (hf : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
      (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) :
    MovHyp P D N T ρ X₀ W X :=
  ⟨htr, hb, hi, hs, hf⟩

/-- **Bridge D (proved): `D.invβ = β⁻¹` rewriting.**  `movT_Q g D N ρ r` is the `ℚ_{N,β}(μ^r)` with `β` as in the consumers
(`dynamic_entropy` etc. write `modulatedGibbs g N β …` with `htr.dyn.invβ = β⁻¹`). -/
theorem movT_Q_eq_beta {g : Torus d → ℝ} {D : DynData d} {β : ℝ} (hβ : D.invβ = β⁻¹) (N : ℕ)
    (ρ : ℝ → Torus d → ℝ) (r : ℝ) :
    movT_Q g D N ρ r = modulatedGibbs g N β (withDensityReal (ρ r)) := by
  unfold movT_Q; rw [hβ, inv_inv]

/-- **SPEC (sorried, S-M): bridge D, `MFEHyp ⇒ MovHyp`** (hypotheses of `mfe_uniform`, `Coercivity.lean:3086`): `M = -I`,
`β < ∞`, `V ∈ C^{m_*+2} ⊂ C²`, weak solution, `C^{m_*+2}` regular with `inf ≥ lam₀ > 0` (so `C²` with a `C²` bound,
strictly positive), `IsC12Test` by `movT_isC12Test_of_weak`, and the particle-system fields. -/
theorem movT_hyp_of_mfeHyp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {D : DynData d}
    {T Λ lam₀ : ℝ} {ρ : ℝ → Torus d → ℝ} {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} (h : MFEHyp P D N T Λ lam₀ ρ X₀ W X) : MovHyp P D N T ρ X₀ W X := by
  sorry

/-- **SPEC (sorried, S-M): bridge A, `IsSmoothPositiveTrajectory ⇒ MovTraj`** on every `[0,T]` (stated with the fields of
`IsSmoothPositiveTrajectory` (`Sec5.lean:84`) spelled out, since `Sec5` imports this file).  The trajectory is the
`C([0,∞);H^K)` solution of `O:eq:mf-finite` for every `K > d/2 + 6`: on every `[0,T]` a weak solution with probability
densities, smooth, `C^2` bounds from `H^K ⊂ C^2` and continuity in `H^K`, strictly positive (Prop 5.1, M L5772-5773,
L738-745), and `C^{1,2}` jointly (`∂_tρ ∈ C(H^{K-2})`).  Existing inputs: `finite_reg_uniform_bounds`; `Regime.reg`,
`Regime.relax` are still sorried (Review 1). -/
theorem movT_traj_of_global (s β : ℝ) (V ρ₀ : Torus d → ℝ) (ρ : ℝ → Torus d → ℝ) (hs0 : 0 ≤ s)
    (hsd : s < d) (hβ : 0 < β) (hV : Torus.IsSmooth V) (hρ₀ : SmoothPosDensity ρ₀)
    (hglobal : ∀ K : ℕ, (d : ℝ) / 2 + 6 < K →
      ∃ ρc : ℝ → (Lattice d → ℂ), PDE.IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc ∧
        ∀ t, 0 ≤ t → PDE.mfPath ρc t = ρ t)
    (T : ℝ) : MovTraj (PDE.mfData d s hs0 hsd V β hβ) T ρ := by
  sorry

/-- **SPEC (sorried, M): bridge A', all-time uniform bounds** of the background (needed for `moving_log_moment`,
`alltime_Lp`, where the constants may not depend on `T`): there are `c₀ > 0`, `Λ₂` with `ρ^t ≥ c₀`, `‖ρ^t‖_{C²} ≤ Λ₂`
for all `t ≥ 0` (global a priori bounds of the smooth positive trajectory; relaxation to equilibrium and positivity of the
thermal density). -/
theorem movT_traj_uniform (s β : ℝ) (V ρ₀ : Torus d → ℝ) (ρ : ℝ → Torus d → ℝ) (hs0 : 0 ≤ s)
    (hsd : s < d) (hβ : 0 < β) (hV : Torus.IsSmooth V) (hρ₀ : SmoothPosDensity ρ₀)
    (hglobal : ∀ K : ℕ, (d : ℝ) / 2 + 6 < K →
      ∃ ρc : ℝ → (Lattice d → ℂ), PDE.IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc ∧
        ∀ t, 0 ≤ t → PDE.mfPath ρc t = ρ t) :
    ∃ c₀ Λ₂ : ℝ, 0 < c₀ ∧ ∀ t : ℝ, 0 ≤ t → (∀ x, c₀ ≤ ρ t x) ∧ Torus.cbNorm 2 (ρ t) ≤ Λ₂ := by
  sorry

/-- **SPEC (sorried, M): bridge B, relaxation ⇒ `∫_0^∞ L < ∞`** (M L6660-6661: "the relaxation input gives
`∫_0^∞ L(t) dt < ∞`", `L(t) = ‖∇u^t‖_∞`).  If `ρβ` is a thermal density (`IsThermalDensity`, so `u_eq = β⁻¹∇log ρβ +
∇g*ρβ + ∇V = 0`) and `‖ρ^t - ρβ‖_{C²} ≤ C e^{-λt}`, then `L(t) := C'‖ρ^t - ρβ‖_{C²} ≥ Lip(u^t)`
(`‖g * D²f‖ ≤ ‖g‖_{L¹}‖D²f‖`, `log` Lipschitz on the range `[c₀,Λ₂]`) is integrable on `[0,∞)`.  `mov_lp_bound` is then applied
to `L + η`, `η = e^{-r}` with `ℓ = e^{-T}` inside the `∀ T`. -/
theorem movT_relaxation_L {D : DynData d} {ρ : ℝ → Torus d → ℝ} {ρβ : Torus d → ℝ}
    (hM : D.M = -1) (hβ : 0 < D.invβ) (hth : IsThermalDensity (periodicRiesz d D.s) D.V D.invβ⁻¹ ρβ)
    (htr : ∀ T : ℝ, MovTraj D T ρ) {C₀ lam : ℝ} (hlam : 0 < lam)
    (hrelax : ∀ t : ℝ, 0 ≤ t → Torus.cbNorm 2 (fun x => ρ t x - ρβ x) ≤ C₀ * Real.exp (-lam * t)) :
    ∃ L : ℝ → ℝ, (∀ t, 0 ≤ t → 0 ≤ L t) ∧ IntegrableOn L (Set.Ici 0) ∧
      ∀ t : ℝ, 0 ≤ t → IsLipschitzVF (L t) (mfeTransport D (ρ t)) := by
  sorry

/-- **SPEC (sorried, M): bridge C, initial `L^{p₀}` bound for `alltime_Lp`** (M L8409-8413: "Choose `p₀ > 1` with
`p₀β₀ - (p₀-1)β > 0`.  The exact ratio of partition functions in `N:sec:pressure` gives a bounded initial `L^{p₀}` norm").
For a positive `C²` probability density `μ`, `0 < β₀`, `0 < β`, `p₀ > 1`, `p₀β₀ - (p₀-1)β > 0`:
`ℚ_{N,β₀}(μ) ≪ ℚ_{N,β}(μ)` and `‖dℚ_{N,β₀}/dℚ_{N,β}‖_{L^{p₀}(ℚ_{N,β})} ≤ e^{C Nδ_N}`, `C` uniform in `N ≥ 2`
(`pressure_two_sided` at the three temperatures `β₀`, `β`, `p₀β₀-(p₀-1)β`; `movT_pressure_two_sided_C2`).
The case `β₀ = 0` (iid preparation), `s = 0` is the separate packet `movT_prepared_initial_Lp_iid` below. -/
theorem movT_prepared_initial_Lp (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {μ : Torus d → ℝ}
    (hμ : IsProbDensity μ) (hck : Torus.IsCk 2 μ) (hpos : ∀ x, 0 < μ x) {β₀ β p₀ : ℝ} (hβ₀ : 0 < β₀)
    (hβ : 0 < β) (hp₀ : 1 < p₀) (hcoef : 0 < p₀ * β₀ - (p₀ - 1) * β) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      modulatedGibbs (periodicRiesz d s) N β₀ (withDensityReal μ) ≪
        modulatedGibbs (periodicRiesz d s) N β (withDensityReal μ) ∧
      eLpNorm ((modulatedGibbs (periodicRiesz d s) N β₀ (withDensityReal μ)).rnDeriv
          (modulatedGibbs (periodicRiesz d s) N β (withDensityReal μ))) (ENNReal.ofReal p₀)
        (modulatedGibbs (periodicRiesz d s) N β (withDensityReal μ)) ≤
        ENNReal.ofReal (Real.exp (C * N * deltaN d s N)) := by
  sorry

/-- **SPEC (sorried, M): bridge C, the iid logarithmic preparation `β₀ = 0`, `s = 0`** (M L8411-8412: "For the
logarithmic iid preparation, choose `p₀` close enough to one to use its small attractive preparation moment").  Added after
statement review 2 (ISSUES "MOVSPEC"): `movT_prepared_initial_Lp` needs `p₀β₀ - (p₀-1)β > 0`, vacuous at `β₀ = 0`.  For a positive
`C²` probability density `μ` and `β > 0` there are `p₀ > 1` and `C` with, for all `N ≥ 2`, `μ^{⊗N} = ℚ_{N,0}(μ) ≪ ℚ_{N,β}(μ)` and
`‖dμ^{⊗N}/dℚ_{N,β}‖_{L^{p₀}(ℚ_{N,β})} ≤ e^{C Nδ_N}`.  Route: `‖·‖^{p₀}_{L^{p₀}} = Z_β^{p₀-1} E_{μ^{⊗N}} e^{(p₀-1)βN F_N}` (exact ratio of
partition functions); the attractive exponential moment at the small coupling `(p₀-1)β` of the logarithmic interaction
(`∏_{i≠j}|x_i - x_j|^{-(p₀-1)β/N}`-type bound, integrable for `p₀ - 1` small) plus `pressure_two_sided` at `β`. -/
theorem movT_prepared_initial_Lp_iid (hd : 2 ≤ d) {μ : Torus d → ℝ} (hμ : IsProbDensity μ) (hck : Torus.IsCk 2 μ)
    (hpos : ∀ x, 0 < μ x) {β : ℝ} (hβ : 0 < β) :
    ∃ p₀ C : ℝ, 1 < p₀ ∧ ∀ N : ℕ, 2 ≤ N →
      modulatedGibbs (periodicRiesz d 0) N 0 (withDensityReal μ) ≪
        modulatedGibbs (periodicRiesz d 0) N β (withDensityReal μ) ∧
      eLpNorm ((modulatedGibbs (periodicRiesz d 0) N 0 (withDensityReal μ)).rnDeriv
          (modulatedGibbs (periodicRiesz d 0) N β (withDensityReal μ))) (ENNReal.ofReal p₀)
        (modulatedGibbs (periodicRiesz d 0) N β (withDensityReal μ)) ≤
        ENNReal.ofReal (Real.exp (C * N * deltaN d 0 N)) := by
  sorry

end HRS

end
