import HRS.Main.A9Aux14

/-!
# Packet A9, part 15: the core estimate: one test `Φ ∈ C_b²(E_γ)`, one finite set of modes, fixed `N`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A9

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

open HRS HRS.A33 HRS.PDE HRS.Main.A8P HRS.GF HRS.Uniform

variable {d : ℕ}

section Conv

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

theorem a9_fG_continuous (νG : Measure H) [IsProbabilityMeasure νG] {Φ : H → ℝ}
    (hΦ : Φ ∈ CbUnitBall H 2) : Continuous fun x : H => ∫ y, Φ (x + y) ∂νG := by
  have hΦc : Continuous Φ := hΦ.1.continuous
  have hiG : ∀ x : H, Integrable (fun y => Φ (x + y)) νG := fun x =>
    Integrable.of_bound (C := 1) (hΦc.comp (continuous_const.add continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun y => by simpa using a9_cbUnit_bdd hΦ (x + y))
  have hlip : ∀ x y : H, |(∫ z, Φ (x + z) ∂νG) - ∫ z, Φ (y + z) ∂νG| ≤ ‖x - y‖ := fun x y => by
    rw [← integral_sub (hiG x) (hiG y), ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := ‖x - y‖) (Eventually.of_forall fun z => ?_)).trans
      (by simp)
    have := a9_cbUnit_lip hΦ (x + z) (y + z)
    simpa [Real.norm_eq_abs, add_sub_add_right_eq_sub] using this
  have : LipschitzWith 1 fun x : H => ∫ y, Φ (x + y) ∂νG := LipschitzWith.of_dist_le_mul fun x y => by
    simpa [dist_eq_norm, Real.dist_eq] using hlip x y
  exact this.continuous

theorem a9_conv_integral (μ νG : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure νG]
    {Φ : H → ℝ} (hΦ : Φ ∈ CbUnitBall H 2) :
    ∫ x, Φ x ∂(μ ∗ νG) = ∫ x, (∫ y, Φ (x + y) ∂νG) ∂μ := by
  have hΦc : Continuous Φ := hΦ.1.continuous
  have hΦint : Integrable Φ (μ ∗ νG) :=
    Integrable.of_bound (C := 1) hΦc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using a9_cbUnit_bdd hΦ x)
  exact integral_conv hΦint

end Conv

section Core

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ C₀' Cq Cp cT : ℝ}

theorem a9_core_Phi (hP : A8Pack d S.s Rg MB Λ VB ν₀ C₀ Ca Λ₁ C₀' Cq Cp cT)
    {Ktr : ℝ} (hKtr0 : 0 ≤ Ktr)
    (hKtr : ∀ (D : DynData d) (ρ : ℝ → Torus d → ℝ),
      AdjointData S.s (gammaIdx d) Rg MB Λ VB D ν₀ S.T ρ → ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      ∀ F : NegSobolev d (gammaIdx d : ℝ), ‖transportField D ρ t (gammaIdx d : ℝ) F‖ ≤ ‖F‖ * Ktr)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈) {N : ℕ} (hN : 2 ≤ N)
    {Cin : ℝ} {εf : ℕ → ℝ} {ηF : ∀ N, (R N).Ω → NegSobolev d (gammaIdx d : ℝ)}
    {νin : Measure (NegSobolev d (gammaIdx d : ℝ))}
    (hfield : InitialFluctuationField S R (gammaIdx d) Cin εf ηF νin)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) {νG : Measure (NegSobolev d (gammaIdx d : ℝ))}
    (hνG : IsLinearFieldNoise (S.dyn N) (S.ρ N) (S.qN N) t (gammaIdx d : ℝ) νG)
    {q : ℕ} {k : Fin q → NonzeroLattice d} (hk : Function.Injective k)
    (Φ : NegSobolev d (gammaIdx d : ℝ) → ℝ) (hΦ : Φ ∈ CbUnitBall (NegSobolev d (gammaIdx d : ℝ)) 2) :
    |(∫ x, Φ x ∂(particleFieldLaw (R N).P (S.sigma N) (gammaIdx d : ℝ) (R N).X (S.ρ N) t)) -
      ∫ x, Φ x ∂(linearFieldLaw (R N).P (S.dyn N) (S.ρ N) (S.AN N) t (gammaIdx d : ℝ) (ηF N) νG)| ≤
    Ktr * εf N + ∑' j, a9bQ S N Ca Cq cT Λ₁ t (𝔈 N) k j +
      (1 / 2) * a8pCovCost S N Cq Cp Ca Λ₁ Λ (𝔈 N) (fun _ : Fin q => t) (fun a => a9phi d (k a)) +
      ∑' j, a9bG S N Ca Λ₁ t k j := by
  classical
  obtain ⟨hCa, hspec, hcom, hCq, hC, hCp0, hCp, hcT0, hcT⟩ := hP
  have hS' := a9_standing_mStar hS
  have hN1 : 1 ≤ N := by omega
  have hT0 : 0 ≤ S.T := S.hT.le
  have h𝔈 : 0 ≤ 𝔈 N := (hS.energy.pos N hN1).le
  obtain ⟨ℱ, W', hF⟩ := hS.filtered N hN1
  have hprob := hνG.1
  haveI := hprob
  set ts : Fin q → ℝ := fun _ => t with hts_def
  set φ : Fin q → Torus d → ℝ := fun a => a9phi d (k a) with hφ_def
  have hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T := fun _ => ht
  have hφc : ∀ a, Continuous (φ a) := fun a => a9phi_cont _
  have hφm : ∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a) := fun a => a9phi_mem _ _
  obtain ⟨hmart, -⟩ := a8p_vector_mart hspec hCa hS' hN1 hF ts hts φ hφc hφm
  set Mv := vectorItoIntegral (R N).P ℱ W'
    (fun a => killAfter (a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) (ts a))
    with hMv
  set b : Fin q → NegSobolev d (gammaIdx d : ℝ) := fun a => a9unit (gammaIdx d : ℝ) (k a) with hb
  have hbo : Orthonormal ℝ b := a9unit_orthonormal hk
  have hι := norm_embedCLM_le hbo
  haveI hγprob : IsProbabilityMeasure
      (multivariateGaussian (0 : ℝ^q) (integratedCov S.T (a8pSb S N ts φ))) := inferInstance
  have hνγ := a9_gauss_law hS' hN1 ht k hνG
  have hZm := a9_Z_meas hS hN1 ht hF
  have hXm0 := a9_I_meas hS hN1 ht hF
  have hXm : Measurable (a9I S R N t) := hXm0.mono (ℱ.le 0) le_rfl
  have hXtm := a9_Itil_meas hS hN1 ht hfield
  have hMt : AEMeasurable (fun ω => Mv S.T ω) (R N).P :=
    (hmart.sq_int S.T ⟨hT0, le_rfl⟩).aestronglyMeasurable.aemeasurable
  have hΦc : Continuous Φ := hΦ.1.continuous
  -- the two integrals
  have e1 : ∫ x, Φ x ∂(particleFieldLaw (R N).P (S.sigma N) (gammaIdx d : ℝ) (R N).X (S.ρ N) t) =
      ∫ ω, Φ (a9Z S R N t ω) ∂(R N).P := by
    unfold particleFieldLaw law
    exact integral_map (φ := a9Z S R N t) hZm.aemeasurable hΦc.aestronglyMeasurable
  have e2 : ∫ x, Φ x ∂(linearFieldLaw (R N).P (S.dyn N) (S.ρ N) (S.AN N) t (gammaIdx d : ℝ) (ηF N) νG) =
      ∫ ω, (∫ y, Φ (a9Itil S R N t ηF ω + y) ∂νG) ∂(R N).P := by
    haveI := InitialDataAux.negSobolev_secondCountable d (gammaIdx d : ℝ)
    haveI : IsProbabilityMeasure ((R N).P.map (a9Itil S R N t ηF)) :=
      (Measure.isProbabilityMeasure_map_iff hXtm.aemeasurable).2 inferInstance
    unfold linearFieldLaw law
    rw [a9_conv_integral _ νG hΦ]
    exact integral_map (φ := a9Itil S R N t ηF) hXtm.aemeasurable
      (a9_fG_continuous νG hΦ).aestronglyMeasurable
  rw [e1, e2]
  -- the four ingredients
  have hbQ0 : ∀ j, 0 ≤ a9bQ S N Ca Cq cT Λ₁ t (𝔈 N) k j :=
    fun j => a9bQ_nonneg hCa hCq hcT0 hN1 h𝔈 k j
  have hbQs : Summable (a9bQ S N Ca Cq cT Λ₁ t (𝔈 N) k) :=
    a9bQ_summable hCa hCq hcT0 hN1 h𝔈 k
  have hbG0 : ∀ j, 0 ≤ a9bG S N Ca Λ₁ t k j := fun j => by
    unfold a9bG; split_ifs
    · exact le_rfl
    · exact Real.sqrt_nonneg _
  have h1 : ∫⁻ ω, ENNReal.ofReal ‖a9Z S R N t ω - a9I S R N t ω - embedCLM b (Mv S.T ω)‖ ∂(R N).P ≤
      ENNReal.ofReal (∑' j, a9bQ S N Ca Cq cT Λ₁ t (𝔈 N) k j) := by
    refine a9_lintegral_norm_le (R N).P
      (fun ω => a9Z S R N t ω - a9I S R N t ω - embedCLM b (Mv S.T ω)) ?_
      (a9bQ S N Ca Cq cT Λ₁ t (𝔈 N) k) hbQ0 hbQs ?_
    · exact (hZm.aemeasurable.sub hXm.aemeasurable).sub
        ((embedCLM b).continuous.measurable.comp_aemeasurable hMt)
    · intro j
      by_cases hj : j ∈ Set.range k
      · obtain ⟨a, rfl⟩ := hj
        have hdec := a8p_decomp hspec hCa hS' hN hF ts hts φ hφc hφm
        have hrem := a9_rem_moment hspec hCa hS' hN hF hcom hCq hC hcT0 hcT ts hts φ hφc hφm a
        have hbQ : a9bQ S N Ca Cq cT Λ₁ t (𝔈 N) k (k a) =
            S.sigma N * ((1 / 2) * (Cq * (cT * a8pK Λ₁ (ts a) (φ a)))) * (S.T * 𝔈 N) := by
          simp only [a9bQ, if_pos (Set.mem_range_self a)]
          rfl
        rw [hbQ]
        refine le_trans (lintegral_mono_ae ?_) hrem
        filter_upwards [hdec] with ω h
        have ha := congrArg (fun v : EuclideanSpace ℝ (Fin q) => v a) h
        simp only [fluctStat, a8pIemp, PiLp.add_apply] at ha
        have hc : NegSobolev.coord (a9Z S R N t ω - a9I S R N t ω - embedCLM b (Mv S.T ω)) (k a) =
            a8pRem S R N ts φ ω a := by
          rw [a9_coord_sub_embed_mem hk, a9_coord_sub, a9_Z_coord hS' hN1 ht,
            a9_I_coord hS hN1 ht]
          have e : S.sigma N * flucPair ((R N).X (Real.toNNReal t) ω) (S.ρ N t) (a9phi d (k a)) =
              S.sigma N * (pair (empirical ((R N).X (Real.toNNReal t) ω)) (a9phi d (k a)) -
                pair (withDensityReal (S.ρ N t)) (a9phi d (k a))) := rfl
          rw [e]
          have hmv : Mv S.T ω a = (vectorItoIntegral (R N).P ℱ W'
              (fun a => killAfter (a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X)
                (ts a)) S.T ω) a := rfl
          rw [hmv]
          have ha' : S.sigma N * (pair (empirical ((R N).X (Real.toNNReal t) ω)) (a9phi d (k a)) -
              pair (withDensityReal (S.ρ N t)) (a9phi d (k a))) =
              S.sigma N * flucPair ((R N).X 0 ω) (S.ρ N 0)
                (propagator (S.dyn N) (S.ρ N) 0 t (a9phi d (k a))) +
              (vectorItoIntegral (R N).P ℱ W'
                (fun a => killAfter (a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X)
                  (ts a)) S.T ω) a + a8pRem S R N ts φ ω a := ha
          linarith
        rw [hc]
      · have hZI := a9_ZI_moment hspec hCa hS hN hF hcom hCq hC hcT0 hcT ht j
        have hbQ : a9bQ S N Ca Cq cT Λ₁ t (𝔈 N) k j =
            Real.sqrt (S.T * (2 * (S.sigma N ^ 2 * S.invβ N / N) *
              (d * (Ca * a8pK Λ₁ t (a9phi d j))) ^ 2)) +
            S.sigma N * ((1 / 2) * (Cq * (cT * a8pK Λ₁ t (a9phi d j)))) * (S.T * 𝔈 N) := by
          simp only [a9bQ, if_neg hj]
          rfl
        rw [hbQ]
        refine le_trans (lintegral_mono_ae (Eventually.of_forall fun ω => ?_)) hZI
        rw [a9_coord_sub_embed_nmem _ _ j hj, a9_coord_sub]
  have h2 : |(∫ ω, Φ (a9I S R N t ω + embedCLM b (Mv S.T ω)) ∂(R N).P) -
      ∫ ω, (∫ z, Φ (a9I S R N t ω + embedCLM b z)
        ∂(multivariateGaussian (0 : ℝ^q) (integratedCov S.T (a8pSb S N ts φ)))) ∂(R N).P| ≤
      (1 / 2) * a8pCovCost S N Cq Cp Ca Λ₁ Λ (𝔈 N) ts φ := by
    have hsb := a8p_sb_isDet hspec hCa hS' hN1 ts hts φ hφc hφm
    have hshift := a9_shift_H (R N).P ℱ S.T hT0 Mv
      (killedCovMatrix (fun a => a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) ts)
      hmart (a8pSb S N ts φ) hsb (embedCLM b) hι (a9I S R N t) hXm0 Φ hΦ
      (fun x => ∫ z, Φ (x + embedCLM b z)
        ∂(multivariateGaussian (0 : ℝ^q) (integratedCov S.T (a8pSb S N ts φ)))) (fun x => rfl)
    have hcost := a8p_cov_cost hspec hCa hS' hN hcom hCq hC hCp0 hCp ts hts φ hφc hφm
      hF.progressive (a8p_nullContact hS' hN1)
    refine hshift.trans ?_
    have : (∫ ω, (∫ σ in Set.Icc 0 S.T, s1Norm
        (killedCovMatrix (fun a => a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) ts σ ω -
          a8pSb S N ts φ σ)) ∂(R N).P) ≤ a8pCovCost S N Cq Cp Ca Λ₁ Λ (𝔈 N) ts φ := hcost
    linarith
  have h3 := a9_I_diff hKtr0 hKtr hS hN1 ht hfield
  have h4 := a9_gauss_tail hspec hCa hS' hN1 ht hk hνG
  have h4' : ∫⁻ y, ENNReal.ofReal ‖y - embedCLM b (hmCoordCLM b y)‖ ∂νG ≤
      ENNReal.ofReal (∑' j, a9bG S N Ca Λ₁ t k j) := h4
  have key := a9_chain (P := (R N).P) (embedCLM b) hι (fun y => hmCoordCLM b y)
    (hmCoordCLM b).continuous.measurable νG
    (multivariateGaussian (0 : ℝ^q) (integratedCov S.T (a8pSb S N ts φ))) hνγ Φ hΦ
    (a9Z S R N t) (a9I S R N t) (a9Itil S R N t ηF) hZm hXm hXtm (fun ω => Mv S.T ω) hMt
    (tsum_nonneg hbQ0) (mul_nonneg hKtr0 (hfield.εf_nonneg N hN1)) (tsum_nonneg hbG0)
    h1 h2 h3 h4'
  refine key.trans (le_of_eq ?_)
  ring

end Core

end HRS.Main.A9
