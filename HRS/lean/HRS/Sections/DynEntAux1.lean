import HRS.Sections.Sec5
import HRS.PDE.MovSXFinal
import HRS.PDE.MovFFinal
import HRS.PDE.MovSpec2b

/-!
# DYNENT: Theorem 5.4 `dynamic_entropy` (helpers)

TeX: `HRS_periodic_main_20261008T010000Z.tex` (M) `N:thm:dynamic`, first display `N:eq:entropy` (L6075-6107),
proof L6419-6469 (`N:eq:entropy-differential`, `N:eq:product-entropy`).

## Chain plan for `dynamic_entropy` (this file and `DynEntFinal.lean`)

Let `D = htr.dyn = PDE.mfData d s _ _ V β _` (`D.s = s`, `D.invβ = β⁻¹`, `D.M = -1`).

1. (bridge A) `movT_traj_of_global_proof` (hypothesis `htr.global`) gives `MovTraj D T ρ`.  The all-time bounds
   `movT_traj_uniform_proof` give `c₀ > 0`, `Λ₂` with `ρ^t ≥ c₀`, `‖ρ^t‖_{C²} ≤ Λ₂` for `t ≥ 0`
   (this avoids the sorried `movT_traj_bounds`).
2. (bridge D) `movT_hyp_of_parts` turns `IsParticleSystem` + the filtered solution into `MovHyp P D N T ρ X₀ W X`.
   `movT_Q_eq_beta` rewrites `movT_Q g D N ρ t` as `modulatedGibbs g N β (withDensityReal (ρ t))`.
3. (entropy half) `movT_entropy_bound` (from `mov_ent_ineq` + `movT_entropy_gronwall`): `H(f^t|Q^t) < ∞` and
   `H(f^t|Q^t) ≤ C₁ B_N`, `B_N = entropyScale = 1 + H(f^∘|Q^0) + Nδ_N`.
4. (product half, `N:eq:product-entropy`, M L6460-6464) lemma `dynent_product_bound` below, for a probability law
   `ν` with `H(ν|Q) < ∞`: `movT_relEntropy_split_proof` gives `H(ν|μ^{⊗N}) < ∞` (`MFEFinite`) and
   `H(ν|μ^N) = H(ν|Q) - βN E_ν F_N - log K_N`; `moments_of_pressure` (with `h = g`, hypotheses from
   `movT_pressure_two_sided_C2_proof`, `rowOK_g_h`, `one_le_mul_deltaN`) bounds `E_ν[N|F_N|] ≤ c (H(ν|Q) + Nδ_N)`;
   the lower pressure bound at `θ = 0` (`gibbs_facts`) gives `-log K_N ≤ C N δ_N`.
5. (assembly, `DynEntFinal.lean`) add the two halves: `≤ (2C₁ + c' ) B_N` with `Nδ_N ≤ B_N`; convert to `ℝ≥0∞` with
   `ENNReal.ofReal_add`/`ofReal_toReal`.

Sorried declarations reached by `dynamic_entropy_proof`: only through the MOV statements `mov_ent_ineq`'s inputs (see
`DynEntFinal.lean`, final `#print axioms` list in `docs/ISSUES.md`, entry DYNENT).

## `dynamic_comparison` (Sec5.lean:174): assessment (not proved here; estimated XL, 2500-3500 lines, over the 1000-line bar)

TeX M L6470-6530.  MOV supplies only the entropy bound (`dynamic_entropy_proof`: both `H(f^t|Q^t)` and `H(f^t|(μ^t)^{⊗N})`
`≤ C B_N`) and the exponential source bound.  Chain, with what exists and what is missing:

1. Gradient bounds of the adjoint flow: for smooth `φ_a` the classical adjoint solution `f_a^r = U^{r,t_a}φ_a` exists with
   `sup_{r ≤ t_a ≤ T} ‖f_a^r‖_{C^3} ≤ C_T`, `IsC12Test t_a f_a ft_a`.  Exists: `PDE.exists_adjoint_decay_abstract`
   (MeanFieldAdjointDuhamel), `classical_adjoint_unique(_of_two)`, `IsRegularMF 3 Λ T ρ` from `movT_traj_of_global_proof`
   plus `movT_isC12Test_of_weak_proof`-type bridges.  Missing: the packaged existence-with-uniform-`C³`-bound statement in
   the form `duality_identity_final` wants (`hex`, `IsRegularMF 3 Λ`), for `htr` (M).  Size M-L.
2. Duality / Itô (`N:eq:duality`): PROVED `duality_identity_final` (Stochastic/DualityProof.lean) with `hocc` from
   `nullContactOccupation_of_strong` (Main/GFSpec1, `IsStrongSolution` is collision-free), `IsContactStrongSolution` from
   `IsStrongSolution.toContact`, and `empiricalMartingale_cov`/`_qv` for the bracket `N:eq:bracket`.  Gives
   `⟨φ_a,η^{t_a}⟩ = ⟨f_a^0,η^∘⟩ + M_{N,a} + √N ∫_0^{t_a} flucInteraction`-type remainder (`fluc_pointwise`, `flucInteraction_eq`
   convert the remainder to `-√N ∫ C_N(∇f_a^r;μ^r) dr`).  Missing: the identification of `flucInteraction` with
   `N F^{h_{∇f}}` (`commKernel`), pointwise in `X` (M).
3. Remainder bound (`≤ C_T B_N/√N`): `moments_of_pressure` / `perturbed_pressure`-type pair-entropy bound for the time-
   dependent kernel `h_r = commKernel (∇f_a^r)`, `|h_r| ≤ B (g + c_*)` (`commKernel_bound`, Energy/Commutator/AbsConv.lean:42),
   uniformly in `r ∈ [0,T]`, integrated in `r`, with `H(f^r|Q^r) ≤ C B_N` (this packet) and `movT_pressure_two_sided_C2_proof`
   (exactly the machinery of `dynent_product_bound`; one more instance, `r`-uniform) plus measurability of
   `r ↦ ∫ N F^{h_r} df^r` (M-L).
4. Bracket error (`≤ C √(B_N/N)`): linear-statistic entropy bound `N:eq:linear-entropy` from the Hoeffding estimate for
   `μ^{⊗N}` (NOT in the repo: Mathlib has `ProbabilityTheory.HasSubgaussianMGF` and the Hoeffding lemma, so (M)) plus the
   Donsker-Varadhan inequality (`b15b_klDiv_liminf_le` family / `Real.add_pow_le`-free route in MovSpecAux), applied to
   `a = ∇f_a·∇f_b` and `H(f^r|(μ^r)^{⊗N}) ≤ C B_N` (this packet).  Size M-L.
5. Gaussian comparison: `conditional_gaussian_interpolation` (Prob/HilbertMartingale.lean:8323, proved) needs `G`
   independent of `ℱ_T`, while the statement only gives `IndepFun X₀ G`.  Since only laws enter, an enlargement
   `Ω × ℝ^p` (`exists_enlargement_indep_univ`, HilbertMartingale:7188; cf. packet `gf_init_enlargement`, GFSpec3) with the
   pulled-back filtration is needed, together with `law` transport (`law_comp_mp`) and the identification
   `law (X₀-part + G) ` on the enlarged space.  Also `IsVectorMartingaleWithCovariation` of
   `(M_{N,a})_a` (from `empiricalMartingale_cov`, `isHM_of_ito`-type lemma) and `IsDetCovMatrix` for `Σ̄` (`noiseCovMatrix`
   is `2q ∫∫ ∇f_a·∇f_b dμ^r dr`: continuity/integrability from step 1).  Size L-XL.
6. Assembly in `smoothDist 2`: `|E h(A) - E h(B + M)| ≤ ‖∇h‖ E|remainder|`, interpolation term from step 5 with the bracket
   error of step 4 (`E‖Σ_r - Σ̄_r‖_{S_1} ≤ C √(B/N)`), `smoothDist_le` / `smoothDist_succ_le` (Prob/Metrics.lean:339) to pass
   from the supremum over the `C_b^2` unit ball to a pointwise bound; the `linCoord` bookkeeping
   (`⟨φ,η⟩ = √N(μ_N(φ) - μ(φ))`, `flucPair`).  Size L.
Total: M-L + M + M-L + M-L + L-XL + L, i.e. well above 1000 lines; no step is blocked by a false statement.
Note the sorried inputs `movT_traj_bounds` etc. enter via `dynamic_entropy_proof` only.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d : ℕ}

/-- Product-entropy half of `N:eq:product-entropy` (M L6460-6464): along a `MovTraj`, for every probability law `ν`
of `N ≥ 2` particles with `H(ν|Q^t) < ∞`, `H(ν|(μ^t)^{⊗N}) < ∞` and
`H(ν|(μ^t)^{⊗N}) ≤ H(ν|Q^t) + C (Nδ_N + H(ν|Q^t))`, `C` uniform in `N` and `t ∈ [0,T]`. -/
theorem dynent_product_bound (hd : 1 ≤ d) {D : DynData d} {T c₀ Λ₂ : ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : MovTraj D T ρ) (hc₀ : 0 < c₀) (hlow : ∀ r ∈ Set.Icc 0 T, ∀ x, c₀ ≤ ρ r x)
    (hΛ : ∀ r ∈ Set.Icc 0 T, Torus.cbNorm 2 (ρ r) ≤ Λ₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ t ∈ Set.Icc 0 T,
      ∀ ν : Measure (Config d N), IsProbabilityMeasure ν →
        relEntropy ν (movT_Q (periodicRiesz d D.s) D N ρ t) ≠ ⊤ →
        relEntropy ν (Measure.pi fun _ : Fin N => withDensityReal (ρ t)) ≠ ⊤ ∧
        (relEntropy ν (Measure.pi fun _ : Fin N => withDensityReal (ρ t))).toReal ≤
          (relEntropy ν (movT_Q (periodicRiesz d D.s) D N ρ t)).toReal +
            C * (N * deltaN d D.s N + (relEntropy ν (movT_Q (periodicRiesz d D.s) D N ρ t)).toReal) := by
  have hβ : 0 < D.invβ⁻¹ := inv_pos.2 htr.pos_temp
  obtain ⟨Bg, hBg⟩ := b15_periodicRiesz_lower D
  set cs : ℝ := 2 * |Bg| + 1 with hcs
  have hBa := le_abs_self Bg
  have hBn := neg_abs_le Bg
  have hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d D.s z + cs := fun z _ => by
    have := hBg z; have := abs_nonneg Bg; linarith
  have hdom : ∀ x y : Torus d, |periodicRiesz d D.s (x - y)| ≤
      1 * (periodicRiesz d D.s (x - y) + cs) := by
    intro x y
    have := hBg (x - y)
    have := abs_nonneg Bg
    rw [abs_le]; constructor <;> linarith
  have hgm : Measurable (periodicRiesz d D.s) := CoercAux.measurable_periodicRiesz_one hd D.hs0 D.hsd
  have hhm : Measurable (Function.uncurry fun x y : Torus d => periodicRiesz d D.s (x - y)) :=
    hgm.comp (measurable_fst.sub measurable_snd)
  obtain ⟨θ₀, C, hθ₀, hC, hP⟩ := movT_pressure_two_sided_C2_proof hd D.s D.hs0 D.hsd cs hw D.invβ⁻¹
    D.invβ⁻¹ hβ c₀ hc₀ Λ₂ 1
  set Cp : ℝ := (D.invβ⁻¹ * θ₀)⁻¹ * (2 * C + 1) with hCp
  have hCp0 : 0 ≤ Cp := by rw [hCp]; positivity
  refine ⟨D.invβ⁻¹ * Cp + C, by positivity, ?_⟩
  intro N hN t ht ν hν hHfin
  have hρ := htr.mf.density t ht
  haveI := isProb_withDensityReal hρ
  have hcont : Continuous (ρ t) := b15_continuous_of_isCk (htr.ck t ht)
  obtain ⟨Mρ, hMρ0, hMρ⟩ := exists_abs_bound hcont
  have hρΛ : ∀ x, ρ t x ≤ Mρ := fun x => (le_abs_self _).trans (hMρ x)
  obtain ⟨hgR, hhR⟩ := rowOK_g_h hd D.s D.hs0 D.hsd cs hw 1 hMρ0 hρΛ
    (h := fun x y => periodicRiesz d D.s (x - y)) hhm hdom
  have hPt : ∀ θ : ℝ, |θ| ≤ θ₀ →
      ENNReal.ofReal (Real.exp (-(C * N * deltaN d D.s N))) ≤
          ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-D.invβ⁻¹ * N *
            modulatedEnergy (fun x y => periodicRiesz d D.s (x - y) - θ * periodicRiesz d D.s (x - y)) X
              (withDensityReal (ρ t)))) ∂(Measure.pi fun _ : Fin N => withDensityReal (ρ t)) ∧
        ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-D.invβ⁻¹ * N *
            modulatedEnergy (fun x y => periodicRiesz d D.s (x - y) - θ * periodicRiesz d D.s (x - y)) X
              (withDensityReal (ρ t)))) ∂(Measure.pi fun _ : Fin N => withDensityReal (ρ t)) ≤
          ENNReal.ofReal (Real.exp (C * N * deltaN d D.s N)) := fun θ hθ =>
    hP (ρ t) hρ (htr.ck t ht) (hlow t ht) (hΛ t ht) (fun x y => periodicRiesz d D.s (x - y)) hhm
      (fun x y => by rw [← neg_sub, periodicRiesz_neg]) hdom N hN D.invβ⁻¹ ⟨le_rfl, le_rfl⟩ θ hθ
  have hδ : 1 ≤ (N : ℝ) * deltaN d D.s N := one_le_mul_deltaN D.hs0 N (by omega)
  have hmom := moments_of_pressure (N := N) hgR hhR hδ hC hθ₀ hβ (le_refl _) hPt
  have hQeq : movT_Q (periodicRiesz d D.s) D N ρ t =
      modulatedGibbs (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal (ρ t)) := rfl
  rw [hQeq] at hHfin ⊢
  have hsplit := movT_relEntropy_split_proof hN htr.pos_temp hρ (htr.ck t ht) (htr.pos t ht) (ν := ν)
  have hMFE := hsplit.1.1 hHfin
  have hid := hsplit.2 hMFE
  -- lower bound on the normaliser
  have hP0 := (hPt 0 (by simp [hθ₀.le]))
  simp only [zero_mul, sub_zero] at hP0
  obtain ⟨hlowK, hupK⟩ := hP0
  have hK0 : ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-D.invβ⁻¹ * N *
      modulatedEnergy (fun x y => periodicRiesz d D.s (x - y)) X (withDensityReal (ρ t))))
      ∂(Measure.pi fun _ : Fin N => withDensityReal (ρ t)) ≠ 0 := by
    intro h0
    rw [h0] at hlowK
    simp at hlowK
    exact absurd hlowK (not_le.2 (Real.exp_pos _))
  have hKt : ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-D.invβ⁻¹ * N *
      modulatedEnergy (fun x y => periodicRiesz d D.s (x - y)) X (withDensityReal (ρ t))))
      ∂(Measure.pi fun _ : Fin N => withDensityReal (ρ t)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hupK
  have hKeq := (gibbs_facts hgR hK0 hKt).1
  have hKnn : 0 ≤ gibbsNormalizer (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal (ρ t)) :=
    integral_nonneg fun X => (Real.exp_pos _).le
  have hKge : Real.exp (-(C * N * deltaN d D.s N)) ≤
      gibbsNormalizer (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal (ρ t)) := by
    rw [← hKeq] at hlowK
    exact (ENNReal.ofReal_le_ofReal_iff hKnn).1 hlowK
  have hlogK : -(C * N * deltaN d D.s N) ≤
      Real.log (gibbsNormalizer (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal (ρ t))) := by
    have := Real.log_le_log (Real.exp_pos _) hKge
    rwa [Real.log_exp] at this
  -- moment bound
  have hm := hmom.2 ν hν (lt_top_iff_ne_top.2 hHfin)
  set Fm : Config d N → ℝ := fun X => modulatedEnergy (fun x y => periodicRiesz d D.s (x - y)) X
    (withDensityReal (ρ t)) with hFm
  have hFmeas : Measurable Fm := measurable_modulatedEnergy hhR
  have hJ : ∫ X, (N : ℝ) * |Fm X| ∂ν ≤ Cp * ((relEntropy ν (modulatedGibbs (periodicRiesz d D.s) N
      D.invβ⁻¹ (withDensityReal (ρ t)))).toReal + N * deltaN d D.s N) := by
    have hnn : 0 ≤ᵐ[ν] fun X => (N : ℝ) * |Fm X| := Eventually.of_forall fun X => by positivity
    have hae : AEStronglyMeasurable (fun X => (N : ℝ) * |Fm X|) ν :=
      (measurable_const.mul (hFmeas.norm)).aestronglyMeasurable
    rw [integral_eq_lintegral_of_nonneg_ae hnn hae]
    have hle := ENNReal.toReal_mono (by
      refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨hHfin, ENNReal.ofReal_ne_top⟩))
      hm
    refine hle.trans (le_of_eq ?_)
    have hNδ : 0 ≤ (N : ℝ) * deltaN d D.s N := by linarith
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCp0, ENNReal.toReal_add hHfin ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hNδ]
  have hFint : Integrable Fm ν := hMFE.2
  have hE : -((N : ℝ) * ∫ X, Fm X ∂ν) ≤ ∫ X, (N : ℝ) * |Fm X| ∂ν := by
    rw [integral_const_mul]
    have h1 : |∫ X, Fm X ∂ν| ≤ ∫ X, |Fm X| ∂ν := by
      simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := ν) Fm
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith [neg_abs_le (∫ X, Fm X ∂ν), mul_le_mul_of_nonneg_left h1 hN0]
  refine ⟨hMFE.1, ?_⟩
  have hH0 := ENNReal.toReal_nonneg (a := relEntropy ν (modulatedGibbs (periodicRiesz d D.s) N
      D.invβ⁻¹ (withDensityReal (ρ t))))
  have hid' : (relEntropy ν (Measure.pi fun _ : Fin N => withDensityReal (ρ t))).toReal =
      (relEntropy ν (modulatedGibbs (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal (ρ t)))).toReal
        - D.invβ⁻¹ * ((N : ℝ) * ∫ X, Fm X ∂ν) -
        Real.log (gibbsNormalizer (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal (ρ t))) := by
    have : ∫ X, rieszEnergy d D.s X (withDensityReal (ρ t)) ∂ν = ∫ X, Fm X ∂ν := rfl
    rw [this] at hid
    linarith
  rw [hid']
  have hNδ : 0 ≤ (N : ℝ) * deltaN d D.s N := by linarith
  have hb1 : -(D.invβ⁻¹ * ((N : ℝ) * ∫ X, Fm X ∂ν)) ≤ D.invβ⁻¹ * (Cp * ((relEntropy ν
      (modulatedGibbs (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal (ρ t)))).toReal +
      N * deltaN d D.s N)) := by
    rw [← mul_neg]
    exact mul_le_mul_of_nonneg_left (hE.trans hJ) hβ.le
  have hCH := mul_nonneg hC hH0
  have hbCp : 0 ≤ D.invβ⁻¹ * Cp := mul_nonneg hβ.le hCp0
  nlinarith [hlogK, hb1, hCH, mul_nonneg hbCp hH0, mul_nonneg hbCp hNδ]

end HRS

end
