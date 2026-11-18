import HRS.MS.PathFidiAux7
import HRS.Whole.AppendixALemmas2
import HRS.MP.HNegInfra

/-!
# SA26 packet P8: the tie `path_fidi_rd_proof` (S.A.26 on `ℝ^d`)

The statement of `HRS.Whole.AppendixALemmas.path_fidi_rd`, proved from the packets `PathFidiAux1`-`7`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.PathFidi

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

/-- **S.A.26 on `ℝ^d`**: `HRS.Whole.AppendixALemmas.path_fidi_rd` with the one extra hypothesis `AEMeasurable η₀ P'`
(the initial functional of the limit is a.e.-measurable).  Without it the identification `law Z = law U ∗ law G` of the
limit law has no proof: `Measure.map` of a non-a.e.-measurable map is a junk Dirac mass, not `0`, so `law P' η₀ = νη`
does not force `η₀` to be a.e.-measurable (compare the S.B.7 repair, `AEMeasurable η₁ P₁`). -/
theorem path_fidi_rd_aem_proof {d : ℕ} (s : ℝ) (fd : FieldDensityRd d s)
    (ν₀ MB Λ ΛV G₀ νbar T Cin m20 : ℝ)
    (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (Kad Kst : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ →
    ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) → fd.Holds S ν₀ →
    ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ),
      RdStanding S R MB Λ ΛV G₀ m20 (fd.Gamma + 5) (fd.Gamma + 5) C₀ 𝔈 →
      ∀ m₂ : ℝ, 0 ≤ m₂ → PropagatedSecondMoment S R m₂ →
      ∀ (p : ℕ) (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ), (∀ a, ts a ∈ Set.Icc (0 : ℝ) T) →
        (∀ a, ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = φ a) →
      ∀ (m₀ : ℕ) (ε : ℕ → ℝ), InitialFluctuationRd S R χ m₀ Cin ε (fun _ => ∅) →
      ∀ (εf : ℕ → ℝ) (Iemp I : ∀ N, ℝ → (R N).Ω → HNeg d (fd.Gamma : ℝ)),
        TransportedInitialFieldRd S R fd.Gamma Cin εf Iemp I →
        InitialFieldDist S R fd.Gamma εf Iemp I →
      ∀ L : LimitCoeffsRd d, fd.HoldsAt S.s S.M L.invβ ν₀ →
        CoeffConvergenceRd S L MB Λ ΛV G₀ νbar (fd.Gamma + 2) fd.Gamma →
        EmpiricalInitialVectorConverges S R L ts φ →
      ∀ K : ℝ, WeightedPathInput S (L.coeff S) (m₀ + 1) (fd.Gamma + 2) K →
      FieldAdjointInputRd fd S Kad →
        AdjointInputOneD (fd.Gamma : ℝ) (mStar d) (L.coeff S) S.T Kad →
        AdjointStabilityInputRd S L (fd.Gamma + 2) (mStar d) fd.Gamma Kst →
      Tendsto (fun N => εf N + S.sigma N * (𝔈 N + fd.eN N) + S.qN N * wN d N (𝔈 N) m₂) atTop (𝓝 0) →
      TransportedConvergesFixedTime S R L (fd.Gamma + 2) →
      ∀ νη : Measure ((Euc d → ℝ) → ℝ), (∀ N : ℕ, 1 ≤ N → law (R N).P (R N).η = νη) →
        ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
          (η₀ : Ω' → (Euc d → ℝ) → ℝ) (Y : ℝ → Ω' → HNeg d ((fd.Gamma + 2 : ℕ) : ℝ)),
        law P' η₀ = νη →
        AEMeasurable η₀ P' →
        IsAdjointDualityLimitW P' (L.coeff S) ((fd.Gamma + 2 : ℕ) : ℝ) L.A L.invβstar T η₀ Y →
        HRS.Main.ConvergesInLaw
          (fun N => fluctStatLawRd (R N).P (S.sigma N) (R N).X (S.ρ N) ts φ)
          (law P' (fun ζ => (WithLp.toLp 2 fun a => HNeg.pairing (φ a) (Y (ts a) ζ) :
            EuclideanSpace ℝ (Fin p)))) := by
  classical
  by_cases hgood : 1 ≤ d ∧ 0 ≤ s ∧ s < d
  swap
  · exact ⟨0, fun C₀ _ S hSs => absurd ⟨S.hd, hSs ▸ S.hs0, hSs ▸ S.hsd⟩ hgood⟩
  obtain ⟨hd, hs0, hsd⟩ := hgood
  obtain ⟨C₁B, hB5⟩ := sa26_B5 s fd ν₀ MB Λ ΛV G₀ Kad hd hs0 hsd
  obtain ⟨C₁e, hC₁e⟩ := sa26_energy_nonneg hd hs0 hsd Λ
  obtain ⟨C₁c, CT, hCT0, hcov⟩ := sa26_cov_bound hd hs0 hsd χ hχ Λ
  refine ⟨max (max C₁B C₁e) C₁c, ?_⟩
  intro C₀ hC₀ S hSs hST hν hHolds R 𝔈 hS m₂ hm₂ hm2 p ts φ hts hφ m₀ ε hinit εf Ie I hTI hdist L
    hHoldsAt hcoef hEmp K hW hFA hlimA hst hsmall hfix νη hνη Ω' mΩ' P' hP' η₀ Y hη₀ hη₀m hY
  subst hST
  have hΛ := sa26_Lam_pos hS
  have hCB : C₁B ≤ C₀ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hC₀
  have hCe : C₁e ≤ C₀ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC₀
  have hCc : C₁c ≤ C₀ := le_trans (le_max_right _ _) hC₀
  have hT0 : 0 ≤ S.T := S.hT.le
  -- the tests
  choose ψ hψ using hφ
  have hΓ : ∀ a, IsSobolevTest ((fd.Gamma : ℕ) : ℝ) (φ a) := fun a => by
    rw [← hψ a]; exact sa26_schwartz_sob (ψ a) fd.Gamma
  have hΓ2 : ∀ a, IsSobolevTest (((fd.Gamma + 2 : ℕ)) : ℝ) (φ a) := fun a => by
    rw [← hψ a]; exact sa26_schwartz_sob (ψ a) (fd.Gamma + 2)
  have hφc : ∀ a, Continuous (φ a) := fun a => by rw [← hψ a]; exact (ψ a).continuous
  -- the commutator input
  obtain ⟨K', hK'0, hsel⟩ := hB5 C₀ hCB S hSs hHolds R 𝔈 m20 (fd.Gamma + 5) (fd.Gamma + 5) hS hFA
  -- the uniform bounds of the orbits
  set Bd : Fin p → ℝ := fun a => (d : ℝ) ^ mStar d * (Kad * HRS.Whole.sobolevNorm (fd.Gamma : ℝ) (φ a))
    with hBd
  have hAdjN : ∀ N : ℕ, 1 ≤ N → ∀ a, ∀ r' ∈ Set.Icc (0 : ℝ) (ts a),
      (∃ f, IsClassicalAdjointW (S.coeff N) (ts a) (φ a) f) ∧
      ContDiff ℝ ((mStar d : ℕ) : WithTop ℕ∞) (propagatorW (S.coeff N) r' (ts a) (φ a)) ∧
      0 ≤ Kad * HRS.Whole.sobolevNorm (fd.Gamma : ℝ) (φ a) ∧
      ∀ l ≤ mStar d, ∀ x, ‖iteratedFDeriv ℝ l (propagatorW (S.coeff N) r' (ts a) (φ a)) x‖ ≤ Bd a :=
    fun N hN a r' hr' => sa26_adj_bounds hd (hFA.deriv N hN) hr'.1 hr'.2 (hts a).2 (hΓ a)
  have hAdjL : ∀ a, ∀ r' ∈ Set.Icc (0 : ℝ) (ts a),
      (∃ f, IsClassicalAdjointW (L.coeff S) (ts a) (φ a) f) ∧
      ContDiff ℝ ((mStar d : ℕ) : WithTop ℕ∞) (propagatorW (L.coeff S) r' (ts a) (φ a)) ∧
      0 ≤ Kad * HRS.Whole.sobolevNorm (fd.Gamma : ℝ) (φ a) ∧
      ∀ l ≤ mStar d, ∀ x, ‖iteratedFDeriv ℝ l (propagatorW (L.coeff S) r' (ts a) (φ a)) x‖ ≤ Bd a :=
    fun a r' hr' => sa26_adj_bounds hd hlimA hr'.1 hr'.2 (hts a).2 (hΓ a)
  have hBd0 : ∀ a, 0 ≤ Bd a := fun a =>
    mul_nonneg (by positivity) (hAdjN 1 le_rfl a 0 ⟨le_rfl, (hts a).1⟩).2.2.1
  have hexN : ∀ N : ℕ, 1 ≤ N → ∀ a, ∃ f, IsClassicalAdjointW (S.coeff N) (ts a) (φ a) f :=
    fun N hN a => (hAdjN N hN a 0 ⟨le_rfl, (hts a).1⟩).1
  have hexL : ∀ a, ∃ f, IsClassicalAdjointW (L.coeff S) (ts a) (φ a) f :=
    fun a => (hAdjL a 0 ⟨le_rfl, (hts a).1⟩).1
  have hmS1 : 1 ≤ mStar d := by unfold mStar; omega
  -- the smallness hypothesis
  obtain ⟨hs1, hs2⟩ := sa26_small_split S fd.eN 𝔈 εf m₂ hm₂ (fun N => HRS.MP.RdRem.mrr_eN_nonneg fd N)
    (fun N hN => hS.energy.pos N hN) (fun N hN => hTI.εf_nonneg N hN) hsmall
  -- the remainder constant
  set CR : ℝ := ∑ a, (max K' 0 / 2 * HRS.Whole.sobolevNorm (fd.Gamma : ℝ) (φ a) * S.T) with hCR
  have hCR0 : 0 ≤ CR := Finset.sum_nonneg fun a _ => by
    have : 0 ≤ HRS.Whole.sobolevNorm (fd.Gamma : ℝ) (φ a) := Real.sqrt_nonneg _
    have := hT0
    positivity
  -- energy nonnegativity at the constants of the statement
  have hnn : ∀ N : ℕ, 2 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ X : EucConfig d N, Function.Injective X →
      0 ≤ rieszModulatedEnergy d S.s X (HRS.Whole.withDensityReal (S.ρ N t)) + oNΛ d S.s C₀ Λ N := by
    intro N hN t ht X hX
    have hN1 : 1 ≤ N := by omega
    rw [hSs]
    exact hC₁e hΛ C₀ hCe N hN (S.ρ N t) ((hS.mean_field.solution N hN1).density t ht)
      (fun x => sa26_rho_le hS hN1 ht x) (fun _ => sa26_log_int hS hN1 ht) X
      (fun ⟨i, j, hij, h⟩ => hij (hX h))
  -- measurability of the statistics
  have hZmAll : ∀ N : ℕ, 1 ≤ N → Measurable (fluctStatRd (S.sigma N) (R N).X (S.ρ N) ts φ) := fun N hN =>
    sa26_fluct_meas (by omega) _ (fun t => HRS.Whole.Q09A.selectedFlow_measurable (hS.flow N hN) t) _ ts φ hφc
  have hcont0 : ∀ N : ℕ, 1 ≤ N → ∀ a, Continuous (propagatorW (S.coeff N) 0 (ts a) (φ a)) := fun N hN a =>
    ((HRS.MS.Fcau.propagatorW_isClassical (hexN N hN a)).c2 0 ⟨le_rfl, (hts a).1⟩).continuous
  have hIemAll : ∀ N : ℕ, 1 ≤ N → Measurable (sa26_Iemp S N ts φ (R N).X) := fun N hN =>
    sa26_Iemp_meas (by omega) S ts φ (HRS.Whole.Q09A.selectedFlow_measurable (hS.flow N hN) 0) (hcont0 N hN)
  -- one particle number
  have hfixed : ∀ N : ℕ, 2 ≤ N →
      smoothDist 2 (fluctStatLawRd (R N).P (S.sigma N) (R N).X (S.ρ N) ts φ)
        (law (R N).P (sa26_Iemp S N ts φ (R N).X) ∗
          multivariateGaussian 0 (sa26_Sig (S.coeff N) (S.qN N) ts φ)) ≤
      CR * (S.sigma N * (𝔈 N + fd.eN N)) +
        (1 / 2 * (CT * S.T * (∑ a, Bd a) ^ 2)) * (S.qN N * wN d N (𝔈 N) m₂) := by
    intro N hN
    have hN1 : 1 ≤ N := by omega
    have hN0 : 0 < N := by omega
    obtain ⟨ℱ, W', hF⟩ := hS.filtered N
    have hprog := hF.progressive
    have hex := hexN N hN1
    have hdec := sa26_decomp hS (r := fd.Gamma + 5) (mV := fd.Gamma + 5) (by omega) (by omega) hN1 ts φ hts hex hF
    have hKp := fun a => sa26_K_progL2 hS ts φ hts hex hprog a
    obtain ⟨hM, -⟩ := several_times_covariation (R N).P hF.brownian
      (fun a => sa26_K S N ts φ (R N).X a) hKp ts (fun a => (hts a).1) S.T (fun a => (hts a).2)
    have hinj := sa26_flow_inj_all hT0 (hS.flow N hN1) hF
    have hGc : ∀ a, ∀ r' ∈ Set.Icc (0 : ℝ) (ts a),
        ContDiff ℝ ((mStar d : ℕ) : WithTop ℕ∞) (propagatorW (S.coeff N) r' (ts a) (φ a)) ∧
          ∀ l ≤ mStar d, ∀ x, ‖iteratedFDeriv ℝ l (propagatorW (S.coeff N) r' (ts a) (φ a)) x‖ ≤ Bd a :=
      fun a r' hr' => ⟨(hAdjN N hN1 a r' hr').2.1, (hAdjN N hN1 a r' hr').2.2.2⟩
    have hcovb := hcov C₀ hCc S hSs R 𝔈 MB ΛV G₀ m20 (fd.Gamma + 5) (fd.Gamma + 5) hS m₂ hm₂ hm2 N hN
      ts φ hts Bd hBd0 hGc hex hprog hinj hM.sigma_meas
    -- the density and the bounds for the deterministic covariance density
    have hGb : ∀ a r x, ‖sa26_G S N ts φ a r x‖ ≤ ∑ c, Bd c := fun a r x =>
      (sa26_GC_norm_le (S.coeff N) ts φ a (hBd0 a)
        (fun r' hr' x' => (hAdjN N hN1 a r' hr').2.2.2 1 hmS1 x') r x).trans
        (Finset.single_le_sum (f := Bd) (fun c _ => hBd0 c) (Finset.mem_univ a))
    have hGm : ∀ a, Measurable fun q : ℝ × Euc d => sa26_G S N ts φ a q.1 q.2 := fun a =>
      sa26_G_meas ts φ a (hts a).1 (hex a)
    have hρm := HRS.MP.RdRem.mrr_rho_meas hS hN1
    have hρd : ∀ r, HRS.Whole.IsProbDensity (S.ρ N (HRS.MP.RdRem.mrrClamp S.T r)) := fun r =>
      (hS.mean_field.solution N hN1).density _ (HRS.MP.RdRem.mrrClamp_mem hT0 r)
    have hq0 : 0 ≤ 2 * S.qN N := by have := sa26_qN_nonneg S N; positivity
    have hsb := sa26_sigBar_isDet (ts := ts) (c := 2 * S.qN N) hGm hρm hGb (fun r x => (hρd r).nonneg x)
      (fun r => sa26_probDensity_integrable (hρd r)) (fun r => (hρd r).integral_one.le) hq0 S.T
    -- the pieces of the decomposition
    have hZm := hZmAll N hN1
    have hIem := hIemAll N hN1
    have hIe0 : Measurable[ℱ 0] (sa26_Iemp S N ts φ (R N).X) :=
      @sa26_Iemp_meas d (R N).Ω (ℱ 0) N hN0 S p ts φ (R N).X (HRS.Whole.Q09B.q09b_measurable_init hF 0)
        (hcont0 N hN1)
    set Z := fluctStatRd (S.sigma N) (R N).X (S.ρ N) ts φ with hZdef
    set M := vectorItoIntegral (R N).P ℱ W'
      (fun a => killAfter (sa26_K S N ts φ (R N).X a) (ts a)) with hMdef
    set Rr : (R N).Ω → EuclideanSpace ℝ (Fin p) := fun ζ => Z ζ - sa26_Iemp S N ts φ (R N).X ζ - M S.T ζ
      with hRr
    have hRae : ∀ᵐ ζ ∂(R N).P, Rr ζ = sa26_Rem S N ts φ (R N).X ζ := hdec.mono fun ζ h => by
      simp only [hRr]; rw [h]; abel
    have hRAEm : AEStronglyMeasurable Rr (R N).P := by
      have h1 : AEStronglyMeasurable (M S.T) (R N).P :=
        (hM.sq_int S.T ⟨hT0, le_rfl⟩).aestronglyMeasurable
      exact (hZm.aestronglyMeasurable.sub hIem.aestronglyMeasurable).sub h1
    have hremA : ∀ a, ∫⁻ ζ, ENNReal.ofReal |S.sigma N * ∫ r in Set.Icc (0 : ℝ) (ts a),
        flucInteractionRd (S.dyn N) (propagatorW (S.coeff N) r (ts a) (φ a))
          ((R N).X (Real.toNNReal r) ζ) (S.ρ N r)| ∂(R N).P ≤
        ENNReal.ofReal (S.sigma N * (max K' 0 / 2 * HRS.Whole.sobolevNorm (fd.Gamma : ℝ) (φ a) * S.T *
          (𝔈 N + fd.eN N))) := by
      intro a
      have h := sa26_rem_L1 hS (r := fd.Gamma + 5) (mV := fd.Gamma + 5) (by omega)
        (fun N => HRS.MP.RdRem.mrr_eN_nonneg fd N) hsel hnn hN (hts a) le_rfl (hΓ a)
      have hσ := HRS.MP.RdRem.mrr_sigma_nonneg S N
      calc ∫⁻ ζ, ENNReal.ofReal |S.sigma N * ∫ r in Set.Icc (0 : ℝ) (ts a),
            flucInteractionRd (S.dyn N) (propagatorW (S.coeff N) r (ts a) (φ a))
              ((R N).X (Real.toNNReal r) ζ) (S.ρ N r)| ∂(R N).P
          = ENNReal.ofReal (S.sigma N) * ∫⁻ ζ, ENNReal.ofReal |∫ r in Set.Icc (0 : ℝ) (ts a),
            flucInteractionRd (S.dyn N) (propagatorW (S.coeff N) r (ts a) (φ a))
              ((R N).X (Real.toNNReal r) ζ) (S.ρ N r)| ∂(R N).P := by
            rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            refine lintegral_congr fun ζ => ?_
            rw [abs_mul, abs_of_nonneg hσ, ENNReal.ofReal_mul hσ]
        _ ≤ ENNReal.ofReal (S.sigma N) * ENNReal.ofReal (max K' 0 / 2 *
              HRS.Whole.sobolevNorm (fd.Gamma : ℝ) (φ a) * S.T * (𝔈 N + fd.eN N)) :=
            mul_le_mul' le_rfl h
        _ = _ := (ENNReal.ofReal_mul hσ).symm
    have hRlint : ∫⁻ ζ, ENNReal.ofReal ‖Rr ζ‖ ∂(R N).P ≤
        ENNReal.ofReal (CR * (S.sigma N * (𝔈 N + fd.eN N))) := by
      have hcoordm : ∀ a, AEMeasurable (fun ζ => ENNReal.ofReal |Rr ζ a|) (R N).P := fun a =>
        (((by fun_prop : Measurable fun v : EuclideanSpace ℝ (Fin p) => v a).comp_aemeasurable
          hRAEm.aemeasurable).abs.ennreal_ofReal)
      calc ∫⁻ ζ, ENNReal.ofReal ‖Rr ζ‖ ∂(R N).P
          ≤ ∫⁻ ζ, ∑ a, ENNReal.ofReal |Rr ζ a| ∂(R N).P :=
            lintegral_mono fun ζ => (ENNReal.ofReal_le_ofReal (sa26_norm_le_sum_abs _)).trans_eq
              (ENNReal.ofReal_sum_of_nonneg fun a _ => abs_nonneg _)
        _ = ∑ a, ∫⁻ ζ, ENNReal.ofReal |Rr ζ a| ∂(R N).P := lintegral_finset_sum' _ fun a _ => hcoordm a
        _ ≤ ∑ a, ENNReal.ofReal (S.sigma N * (max K' 0 / 2 * HRS.Whole.sobolevNorm (fd.Gamma : ℝ) (φ a) *
              S.T * (𝔈 N + fd.eN N))) := by
            refine Finset.sum_le_sum fun a _ => ?_
            refine le_trans (le_of_eq (lintegral_congr_ae (hRae.mono fun ζ h => ?_))) (hremA a)
            show ENNReal.ofReal |Rr ζ a| = _
            rw [h]
            try rfl
        _ = ENNReal.ofReal (CR * (S.sigma N * (𝔈 N + fd.eN N))) := by
            have hσ := HRS.MP.RdRem.mrr_sigma_nonneg S N
            have h𝔈 : 0 ≤ 𝔈 N + fd.eN N :=
              add_nonneg (hS.energy.pos N hN1).le (HRS.MP.RdRem.mrr_eN_nonneg fd N)
            rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => by
              have : 0 ≤ HRS.Whole.sobolevNorm (fd.Gamma : ℝ) (φ a) := Real.sqrt_nonneg _
              positivity)]
            congr 1
            rw [hCR, Finset.sum_mul]
            refine Finset.sum_congr rfl fun a _ => ?_
            ring
    have hRint : Integrable Rr (R N).P := ⟨hRAEm, by
      have : ∫⁻ ζ, ‖Rr ζ‖ₑ ∂(R N).P ≤ ENNReal.ofReal (CR * (S.sigma N * (𝔈 N + fd.eN N))) := by
        simpa [ofReal_norm_eq_enorm] using hRlint
      exact lt_of_le_of_lt this ENNReal.ofReal_lt_top⟩
    have hRI : ∫ ζ, ‖Rr ζ‖ ∂(R N).P ≤ CR * (S.sigma N * (𝔈 N + fd.eN N)) := by
      refine sa26_integral_le_lintegral (fun ζ => norm_nonneg _) hRAEm.norm ?_ hRlint
      have := HRS.MP.RdRem.mrr_sigma_nonneg S N
      have h𝔈 : 0 ≤ 𝔈 N + fd.eN N :=
        add_nonneg (hS.energy.pos N hN1).le (HRS.MP.RdRem.mrr_eN_nonneg fd N)
      positivity
    have hLind := HRS.Main.A8P.a8p_smooth_abstract (R N).P ℱ S.T hT0 M
      (killedCovMatrix (fun a => sa26_K S N ts φ (R N).X a) ts) hM
      (sa26SigBar ts (sa26_G S N ts φ) (fun r' => S.ρ N (HRS.MP.RdRem.mrrClamp S.T r'))
        (2 * S.qN N)) hsb (sa26_Iemp S N ts φ (R N).X) hIe0 (sa26_Iemp S N ts φ (R N).X) hIem Z Rr hRint
      (Eventually.of_forall fun ζ => by simp only [hRr]; abel) (by simp)
    have e : integratedCov S.T (sa26SigBar ts (sa26_G S N ts φ)
        (fun r' => S.ρ N (HRS.MP.RdRem.mrrClamp S.T r')) (2 * S.qN N)) =
        sa26_Sig (S.coeff N) (S.qN N) ts φ := sa26_integratedCov_eq (S.coeff N) (S.qN N) ts φ hts
    rw [e] at hLind
    have h0 : ∫ ζ, ‖sa26_Iemp S N ts φ (R N).X ζ - sa26_Iemp S N ts φ (R N).X ζ‖ ∂(R N).P = 0 := by simp
    rw [h0] at hLind
    refine hLind.trans ?_
    have := hcovb
    nlinarith [hRI, hcovb]
  -- ===== the passage to the limit =====
  have hmeasP : ∀ n : ℕ, 2 ≤ n + 2 := fun n => by omega
  have hDt : Tendsto (fun N => coeffDiscrepancyRd S L fd.Gamma N) atTop (𝓝 0) := hcoef.tendsto
  have hfin : ∀ᶠ N : ℕ in atTop, coeffDiscrepancyRd S L fd.Gamma N ≠ ⊤ :=
    (hDt.eventually (gt_mem_nhds ENNReal.zero_lt_top)).mono fun N h => h.ne
  obtain ⟨Dl, hDl⟩ : ∃ Dl : ℕ → ℝ, ∀ N, Dl N = (coeffDiscrepancyRd S L fd.Gamma N).toReal :=
    ⟨fun N => (coeffDiscrepancyRd S L fd.Gamma N).toReal, fun N => rfl⟩
  obtain ⟨Ks, hKs⟩ : ∃ Ks : Fin p → ℝ, ∀ a,
      Ks a = max Kst 0 * HRS.Whole.sobolevNorm (((fd.Gamma + 2 : ℕ)) : ℝ) (φ a) :=
    ⟨fun a => max Kst 0 * HRS.Whole.sobolevNorm (((fd.Gamma + 2 : ℕ)) : ℝ) (φ a), fun a => rfl⟩
  have hDl0 : ∀ N, 0 ≤ Dl N := fun N => by rw [hDl N]; exact ENNReal.toReal_nonneg
  have hKs0 : ∀ a, 0 ≤ Ks a := fun a => by
    rw [hKs a]
    have : 0 ≤ HRS.Whole.sobolevNorm (((fd.Gamma + 2 : ℕ)) : ℝ) (φ a) := Real.sqrt_nonneg _
    exact mul_nonneg (le_max_right _ _) this
  have hDlt : Tendsto Dl atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hDt
    have e : Dl = (ENNReal.toReal ∘ fun N => coeffDiscrepancyRd S L fd.Gamma N) := funext hDl
    rw [e]
    simpa using this
  have hGN : ∀ N : ℕ, 1 ≤ N → ∀ a r x, ‖sa26_GC (S.coeff N) ts φ a r x‖ ≤ Bd a := fun N hN a r x =>
    sa26_GC_norm_le (S.coeff N) ts φ a (hBd0 a)
      (fun r' hr' x' => (hAdjN N hN a r' hr').2.2.2 1 hmS1 x') r x
  have hGL : ∀ a r x, ‖sa26_GC (L.coeff S) ts φ a r x‖ ≤ Bd a := fun a r x =>
    sa26_GC_norm_le (L.coeff S) ts φ a (hBd0 a)
      (fun r' hr' x' => (hAdjL a r' hr').2.2.2 1 hmS1 x') r x
  have hGst : ∀ᶠ N : ℕ in atTop, ∀ a r x,
      ‖sa26_GC (S.coeff N) ts φ a r x - sa26_GC (L.coeff S) ts φ a r x‖ ≤ Ks a * Dl N := by
    filter_upwards [hfin, eventually_ge_atTop 1] with N hfN hN1 a r x
    by_cases hr : r ∈ Set.Icc (0 : ℝ) (ts a)
    · obtain ⟨-, -, hmem, hle⟩ := hst N hN1 r (ts a) hr.1 hr.2 (hts a).2 (φ a) (hΓ2 a)
      have hne : ENNReal.ofReal (Kst * HRS.Whole.sobolevNorm (((fd.Gamma + 2 : ℕ)) : ℝ) (φ a)) *
          coeffDiscrepancyRd S L fd.Gamma N ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfN
      have hcb := (ENNReal.ofReal_le_iff_le_toReal hne).1 hle
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal'] at hcb
      have hn0 : 0 ≤ HRS.Whole.sobolevNorm (((fd.Gamma + 2 : ℕ)) : ℝ) (φ a) := Real.sqrt_nonneg _
      have hmx : max (Kst * HRS.Whole.sobolevNorm (((fd.Gamma + 2 : ℕ)) : ℝ) (φ a)) 0 ≤
          Ks a := by
        rw [hKs a]
        exact max_le (mul_le_mul_of_nonneg_right (le_max_left _ _) hn0)
          (mul_nonneg (le_max_right _ _) hn0)
      have hcN : ContDiff ℝ 1 (propagatorW (S.coeff N) r (ts a) (φ a)) :=
        ((hAdjN N hN1 a r hr).2.1).of_le (by exact_mod_cast hmS1)
      have hcL : ContDiff ℝ 1 (propagatorW (L.coeff S) r (ts a) (φ a)) :=
        ((hAdjL a r hr).2.1).of_le (by exact_mod_cast hmS1)
      have e : sa26_GC (S.coeff N) ts φ a r x - sa26_GC (L.coeff S) ts φ a r x =
          gradient (fun y => propagatorW (S.coeff N) r (ts a) (φ a) y -
            propagatorW (L.coeff S) r (ts a) (φ a) y) x := by
        simp only [sa26_GC, if_pos hr]
        exact (HRS.MS.Fcau.fcau_gradient_sub hcN hcL x).symm
      rw [e, sa26_norm_grad, hDl N]
      refine (sa26_iter_one_le_cbNorm hmS1 hmem x).trans ?_
      refine hcb.trans ?_
      exact mul_le_mul_of_nonneg_right hmx ENNReal.toReal_nonneg
    · simp only [sa26_GC, if_neg hr, sub_zero, norm_zero]
      exact mul_nonneg (hKs0 a) (hDl0 N)
  have hdensN : ∀ N : ℕ, 1 ≤ N → ∀ r ∈ Set.Icc (0 : ℝ) S.T, HRS.Whole.IsProbDensity ((S.coeff N).ρ r) :=
    fun N hN r hr => (hS.mean_field.solution N hN).density r hr
  have hdensL : ∀ r ∈ Set.Icc (0 : ℝ) S.T, HRS.Whole.IsProbDensity ((L.coeff S).ρ r) :=
    fun r hr => hcoef.limit_solution.density r hr
  have hρtmN : ∀ N : ℕ, 1 ≤ N → Measurable fun q : ℝ × Euc d =>
      (S.coeff N).ρ (HRS.MP.RdRem.mrrClamp S.T q.1) q.2 := fun N hN =>
    HRS.MP.RdRem.mrr_rho_meas hS hN
  have hρtmL : Measurable fun q : ℝ × Euc d => (L.coeff S).ρ (HRS.MP.RdRem.mrrClamp S.T q.1) q.2 :=
    hY.rho_meas.comp (((HRS.MP.RdRem.continuous_mrrClamp S.T).measurable.comp measurable_fst).prodMk
      measurable_snd)
  have hρst : ∀ᶠ N : ℕ in atTop, ∀ r ∈ Set.Icc (0 : ℝ) S.T, ∀ x,
      jbracket x ^ ((d : ℝ) + 3) * |(S.coeff N).ρ r x - (L.coeff S).ρ r x| ≤ Dl N := by
    filter_upwards [hfin] with N hfN r hr x
    rw [hDl N]
    exact (sa26_disc_parts S L fd.Gamma N hfN).2 r hr x
  have hqst : ∀ᶠ N : ℕ in atTop, |S.qN N - L.invβstar| ≤ Dl N := by
    filter_upwards [hfin] with N hfN
    rw [hDl N]
    have h1 := (sa26_disc_parts S L fd.Gamma N hfN).1
    have e : 2 * S.qN N - 2 * L.invβstar = 2 * (S.qN N - L.invβstar) := by ring
    rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h1
    linarith [abs_nonneg (S.qN N - L.invβstar)]
  have hSigT : Tendsto (fun N : ℕ => sa26_Sig (S.coeff N) (S.qN N) ts φ) atTop
      (𝓝 (sa26_Sig (L.coeff S) L.invβstar ts φ)) :=
    sa26_Sig_tendsto S L S.hT.le ts φ hts hBd0 hKs0 hDl0 hDlt hexN hexL hGN hGL hGst hρst hqst
      hdensN hdensL hρtmN hρtmL
  have hBu : ∀ c, Bd c ≤ ∑ c', Bd c' := fun c =>
    Finset.single_le_sum (f := Bd) (fun c _ => hBd0 c) (Finset.mem_univ c)
  have hpsdN : ∀ N : ℕ, 1 ≤ N → (sa26_Sig (S.coeff N) (S.qN N) ts φ).PosSemidef := fun N hN =>
    sa26_Sig_psd (S.coeff N) (sa26_qN_nonneg S N) S.hT.le ts φ hts (hexN N hN)
      (B := ∑ c', Bd c') (fun a r x => (hGN N hN a r x).trans (hBu a)) (hρtmN N hN) (hdensN N hN)
  have hpsdL : (sa26_Sig (L.coeff S) L.invβstar ts φ).PosSemidef :=
    sa26_Sig_psd (L.coeff S) L.hinvβstar S.hT.le ts φ hts hexL
      (B := ∑ c', Bd c') (fun a r x => (hGL a r x).trans (hBu a)) hρtmL hdensL
  -- the limit vectors
  set Z : Ω' → EuclideanSpace ℝ (Fin p) := fun ζ => WithLp.toLp 2 fun a =>
    HNeg.pairing (φ a) (Y (ts a) ζ) with hZdef
  set U : Ω' → EuclideanSpace ℝ (Fin p) := fun ζ => WithLp.toLp 2 fun a =>
    L.A * η₀ ζ (propagatorW (L.coeff S) 0 (ts a) (φ a)) with hUdef
  set G : Ω' → EuclideanSpace ℝ (Fin p) := fun ζ => WithLp.toLp 2 fun a =>
    HNeg.pairing (φ a) (Y (ts a) ζ) - L.A * η₀ ζ (propagatorW (L.coeff S) 0 (ts a) (φ a)) with hGdef
  have hZm : Measurable Z := (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun a =>
    (HRS.MP.HNegInfra.mhn_continuous_pairing (hΓ2 a)).measurable.comp (hY.meas (ts a)))
  have hZG : ∀ ζ, Z ζ = U ζ + G ζ := fun ζ => by
    ext a
    simp [hZdef, hUdef, hGdef]
  -- the initial statistics
  have hIeq : ∀ N : ℕ, 1 ≤ N → law (R N).P (sa26_Iemp S N ts φ (R N).X) =
      law (R N).P (fun ζ => (WithLp.toLp 2 fun a => S.AN N * (S.κ N *
        (HRS.Whole.pair (HRS.Whole.empirical ((R N).X₀ ζ)) (propagatorW (S.coeff N) 0 (ts a) (φ a)) -
          HRS.Whole.pair S.μ0 (propagatorW (S.coeff N) 0 (ts a) (φ a)))) : EuclideanSpace ℝ (Fin p))) := by
    intro N hN
    refine Measure.map_congr ?_
    filter_upwards [sa26_init_ae (hS.flow N hN)] with ζ hζ
    simp only [sa26_Iemp, hζ, hS.mean_field.datum N hN, sa26_sigma_eq, mul_assoc]
  have hEmp2 := (HRS.Main.A9.a9_conv_shift 2).1 (hEmp νη hνη P' η₀ hη₀ hη₀m)
  have hEmp3 : HRS.Main.ConvergesInLaw
      (fun n : ℕ => law (R (n + 2)).P (sa26_Iemp S (n + 2) ts φ (R (n + 2)).X)) (law P' U) := by
    have e : (fun n : ℕ => law (R (n + 2)).P (sa26_Iemp S (n + 2) ts φ (R (n + 2)).X)) =
        (fun n : ℕ => law (R (n + 2)).P (fun ζ => (WithLp.toLp 2 fun a => S.AN (n + 2) * (S.κ (n + 2) *
          (HRS.Whole.pair (HRS.Whole.empirical ((R (n + 2)).X₀ ζ))
              (propagatorW (S.coeff (n + 2)) 0 (ts a) (φ a)) -
            HRS.Whole.pair S.μ0 (propagatorW (S.coeff (n + 2)) 0 (ts a) (φ a)))) :
              EuclideanSpace ℝ (Fin p)))) :=
      funext fun n => hIeq (n + 2) (by omega)
    rw [e]
    exact hEmp2
  have hfU : Measurable (fun η : (Euc d → ℝ) → ℝ => (WithLp.toLp 2 fun a =>
      L.A * η (propagatorW (L.coeff S) 0 (ts a) (φ a)) : EuclideanSpace ℝ (Fin p))) :=
    (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun a =>
      (measurable_pi_apply _).const_mul _)
  have hUae : AEMeasurable U P' := hfU.comp_aemeasurable hη₀m
  have hIp : ∀ n : ℕ, IsProbabilityMeasure
      (law (R (n + 2)).P (sa26_Iemp S (n + 2) ts φ (R (n + 2)).X)) := fun n => inferInstance
  haveI := hIp
  obtain ⟨hind, hGlaw⟩ := hY.gaussian_part p ts φ hts hΓ2
  have hindUG : IndepFun U G P' := hind.symm.comp hfU measurable_id
  have hGae : AEMeasurable G P' := by
    refine (hZm.aemeasurable.sub hUae).congr (Eventually.of_forall fun ζ => ?_)
    rw [Pi.sub_apply, hZG ζ]
    abel
  have hlimlaw : law P' Z = law P' U ∗ multivariateGaussian 0 (sa26_Sig (L.coeff S) L.invβstar ts φ) := by
    refine (sa26_identify P' U G Z hUae hGae hindUG hZG).trans ?_
    exact congrArg (fun m => law P' U ∗ m) hGlaw
  -- Levy and transfer
  have hlev := sa26_levy
    (fun n : ℕ => law (R (n + 2)).P (sa26_Iemp S (n + 2) ts φ (R (n + 2)).X)) (law P' U) hEmp3
    (fun n => sa26_Sig (S.coeff (n + 2)) (S.qN (n + 2)) ts φ)
    (sa26_Sig (L.coeff S) L.invβstar ts φ) (fun n => hpsdN (n + 2) (by omega)) hpsdL
    ((tendsto_add_atTop_iff_nat 2).2 hSigT)
  have hsm0 : ∀ P Q : Measure (EuclideanSpace ℝ (Fin p)), 0 ≤ smoothDist 2 P Q := fun P Q => by
    unfold smoothDist
    exact Real.iSup_nonneg fun Φ => abs_nonneg _
  have hsq : Tendsto (fun n : ℕ => CR * (S.sigma (n + 2) * (𝔈 (n + 2) + fd.eN (n + 2))) +
      (1 / 2 * (CT * S.T * (∑ a, Bd a) ^ 2)) * (S.qN (n + 2) * wN d (n + 2) (𝔈 (n + 2)) m₂))
      atTop (𝓝 0) := by
    have h1 := (tendsto_add_atTop_iff_nat 2).2 hs1
    have h2 := (tendsto_add_atTop_iff_nat 2).2 hs2
    have := (h1.const_mul CR).add (h2.const_mul (1 / 2 * (CT * S.T * (∑ a, Bd a) ^ 2)))
    simpa using this
  have hsd : Tendsto (fun n : ℕ => smoothDist 2
      (fluctStatLawRd (R (n + 2)).P (S.sigma (n + 2)) (R (n + 2)).X (S.ρ (n + 2)) ts φ)
      (law (R (n + 2)).P (sa26_Iemp S (n + 2) ts φ (R (n + 2)).X) ∗
        multivariateGaussian 0 (sa26_Sig (S.coeff (n + 2)) (S.qN (n + 2)) ts φ))) atTop (𝓝 0) :=
    squeeze_zero (fun n => hsm0 _ _) (fun n => hfixed (n + 2) (by omega)) hsq
  haveI hμp : ∀ n : ℕ, IsProbabilityMeasure
      (fluctStatLawRd (R (n + 2)).P (S.sigma (n + 2)) (R (n + 2)).X (S.ρ (n + 2)) ts φ) := fun n => by
    unfold fluctStatLawRd
    infer_instance
  have hfinal : HRS.Main.ConvergesInLaw
      (fun n : ℕ => fluctStatLawRd (R (n + 2)).P (S.sigma (n + 2)) (R (n + 2)).X (S.ρ (n + 2)) ts φ)
      (law P' Z) := by
    rw [hlimlaw]
    exact HRS.MP.FidiF1.fi2_transfer _ _ _ hlev hsd
  exact (HRS.Main.A9.a9_conv_shift 2).2 hfinal

/-- Tie to the repaired frozen statement (S.A.26 repair `AEMeasurable η₀ P'`, approved 2026-10-24). -/
example := (@path_fidi_rd_aem_proof : type_of% @HRS.Whole.AppendixALemmas.path_fidi_rd)

end HRS.MS.PathFidi
