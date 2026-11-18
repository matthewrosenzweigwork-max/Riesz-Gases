import HRS.Main.GFFinal1

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS.Uniform

variable {d : ℕ}

/-- PROVED.  The initial term of the comparison: `‖Ξ⁰ - A η'‖_{L^p(P₁)} = A_N ε_{N,p}` (`σ = Aκ`, and `(X₀∘π₁, η')` has the law of
`(X₀, η°)`). -/
theorem gff_initial_term_eq (S : GeneralSetup d) {N : ℕ} {Ω Ω₁ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₁]
    {P : Measure Ω} {P₁ : Measure Ω₁} {π₁ : Ω₁ → Ω} (hπ₁ : MeasurePreserving π₁ P₁ P)
    (X₀ : Ω → Config d N) (X : ℝ≥0 → Ω → Config d N) (hX0 : ∀ᵐ ω ∂P, X 0 ω = X₀ ω)
    (hX₀m : AEMeasurable X₀ P) (η₀ : Ω → NegSobolev d (S.γ : ℝ)) (η' : Ω₁ → NegSobolev d (S.γ : ℝ))
    (hη₀ : Measurable η₀) (hη' : Measurable η')
    (hlaw : P₁.map (fun ω' => (X₀ (π₁ ω'), η' ω')) = P.map (fun ω => (X₀ ω, η₀ ω)))
    (hγm : (d : ℝ) / 2 < (S.γ : ℝ)) (p : ℝ) (hp : 0 < p) (hfin : S.InitialErrorFinite P N p X₀ η₀) :
    (∫⁻ ω, ‖flucProc (S.γ : ℝ) (sigN S N) (fun t ω => X t (π₁ ω)) (S.ρ N) 0 ω - AN S N • η' ω‖ₑ ^ p ∂P₁) ^
        (1 / p) = ENNReal.ofReal (AN S N * S.initialError P N p X₀ η₀) := by
  set Gf : Config d N × NegSobolev d (S.γ : ℝ) → ℝ≥0∞ := fun z =>
    ‖S.κ N • NegSobolev.ofMeasureDiff (S.γ : ℝ) (empirical z.1) (withDensityReal (S.ρ N 0)) - z.2‖ₑ ^ p with hGf
  have hGfm : Measurable Gf := by
    refine Measurable.pow_const ?_ p
    exact (((gf_measurable_ofMeasureDiff_proof (S.γ : ℝ) hγm (withDensityReal (S.ρ N 0))).comp measurable_fst).const_smul
      (S.κ N) |>.sub measurable_snd).enorm
  have hA := AN_nonneg S N
  -- step 1
  have h1 : ∫⁻ ω, ‖flucProc (S.γ : ℝ) (sigN S N) (fun t ω => X t (π₁ ω)) (S.ρ N) 0 ω - AN S N • η' ω‖ₑ ^ p ∂P₁ =
      ENNReal.ofReal (AN S N) ^ p * ∫⁻ ω, Gf (X₀ (π₁ ω), η' ω) ∂P₁ := by
    rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top)]
    refine lintegral_congr_ae ?_
    filter_upwards [hπ₁.quasiMeasurePreserving.ae hX0] with ω hω
    simp only [flucProc, hGf, Real.toNNReal_zero, hω, sigN_eq S N]
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hp.le, ← smul_smul, ← smul_sub, enorm_smul, Real.enorm_eq_ofReal hA]
  -- step 2
  have h2 : ∫⁻ ω, Gf (X₀ (π₁ ω), η' ω) ∂P₁ = ∫⁻ ω, Gf (X₀ ω, η₀ ω) ∂P := by
    have hm1 : AEMeasurable (fun ω' => (X₀ (π₁ ω'), η' ω')) P₁ :=
      (hX₀m.comp_quasiMeasurePreserving hπ₁.quasiMeasurePreserving).prodMk hη'.aemeasurable
    have hm2 : AEMeasurable (fun ω => (X₀ ω, η₀ ω)) P := hX₀m.prodMk hη₀.aemeasurable
    rw [← lintegral_map' hGfm.aemeasurable hm1, ← lintegral_map' hGfm.aemeasurable hm2, hlaw]
  -- step 3
  have h3 : ∫⁻ ω, Gf (X₀ ω, η₀ ω) ∂P =
      ENNReal.ofReal (∫ ω, ‖S.κ N • NegSobolev.ofMeasureDiff (S.γ : ℝ) (empirical (X₀ ω))
        (withDensityReal (S.ρ N 0)) - η₀ ω‖ ^ p ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal hfin (Filter.Eventually.of_forall fun ω => by positivity)]
    refine lintegral_congr fun ω => ?_
    simp only [hGf]
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le, ofReal_norm]
  rw [h1, h2, h3]
  have hI : 0 ≤ ∫ ω, ‖S.κ N • NegSobolev.ofMeasureDiff (S.γ : ℝ) (empirical (X₀ ω))
      (withDensityReal (S.ρ N 0)) - η₀ ω‖ ^ p ∂P := integral_nonneg fun ω => by positivity
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, mul_one_div_cancel hp.ne',
    ENNReal.rpow_one, ENNReal.ofReal_rpow_of_nonneg hI (by positivity), ← ENNReal.ofReal_mul hA]
  rfl

set_option maxHeartbeats 800000 in
/-- **Stage 1 of the assembly** (see the module docstring).  The constants: `C₀min` is that of `gff_remainder_bound`; `Cr` the remainder
constant. -/
theorem gff_stage1 (b : GeneralBounds d) (M : Matrix (Fin d) (Fin d) ℝ) (K : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ Cr : ℝ, 0 < Cr ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHypM M → ∀ N : ℕ, 2 ≤ N →
      ∀ m : ℝ, (S.γ : ℝ) ≤ m →
      ∀ EV : EvolData (NegSobolev d (S.γ : ℝ)) (NegSobolev d m), GFEvo S M N m K EV →
      ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsStrongSolution P (S.dynM M N) S.T X₀ W X →
        (∃ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        S.EnergyMomentFinite P N X →
        ∀ (η₀ : Ω → NegSobolev d (S.γ : ℝ)), Measurable η₀ →
        IndepFun (fun ω => (X₀ ω, η₀ ω)) (fun ω => fun t => W t ω) P →
        ∀ (Y₀ : Ω → NegSobolev d m), Measurable Y₀ → (∀ ω, Y₀ ω = EV.j (AN S N • η₀ ω)) →
        ∀ Y : ℝ → Ω → NegSobolev d m,
        IsLinearFluctuationSolution P (S.dynM M N) (S.ρ N) m (qN S N) S.T Y₀ Y →
        ∃ (Ω₁ : Type) (mΩ₁ : MeasurableSpace Ω₁) (P₁ : Measure Ω₁) (_ : IsProbabilityMeasure P₁)
          (π₁ : Ω₁ → Ω) (_ : MeasurePreserving π₁ P₁ P) (ℱ₁ : Filtration ℝ mΩ₁)
          (η' : Ω₁ → NegSobolev d (S.γ : ℝ)) (Mart : ℝ → Ω₁ → NegSobolev d (S.γ : ℝ))
          (Z : ℝ → Ω₁ → NegSobolev d m) (Bm : Ω₁ → ℝ≥0∞),
          Stage1 S M N m K EV P P₁ ℱ₁ (fun t ω => X t (π₁ ω)) η' Mart Z Bm Y₀ Y ∧
          IsStrongSolution P₁ (S.dynM M N) S.T (fun ω => X₀ (π₁ ω)) (fun t ω => W t (π₁ ω))
            (fun t ω => X t (π₁ ω)) ∧
          (∃ (ℱ' : Filtration ℝ mΩ₁) (W'' : ℝ≥0 → Ω₁ → (Fin N × Fin d) → ℝ),
            IsFilteredSolution P₁ ℱ' W'' (fun t ω => W t (π₁ ω)) (fun t ω => X t (π₁ ω))) ∧
          S.EnergyMomentFinite P₁ N (fun t ω => X t (π₁ ω)) ∧
          S.energyMoment P₁ N (fun t ω => X t (π₁ ω)) = S.energyMoment P N X ∧
          law P₁ (flucPath m S.T (sigN S N) (fun t ω => X t (π₁ ω)) (S.ρ N)) =
            law P (flucPath m S.T (sigN S N) X (S.ρ N)) ∧
          (∀ p : ℝ, (p = 1 ∨ p = 2) → S.InitialErrorFinite P N p X₀ η₀ →
            (∫⁻ ω, ‖flucProc (S.γ : ℝ) (sigN S N) (fun t ω => X t (π₁ ω)) (S.ρ N) 0 ω -
                AN S N • η' ω‖ₑ ^ p ∂P₁) ^ (1 / p) =
              ENNReal.ofReal (AN S N * S.initialError P N p X₀ η₀)) ∧
          ∫⁻ ω, Bm ω ∂P₁ ≤ ENNReal.ofReal (Cr * sigN S N * (S.T * S.energyMoment P N X)) ∧
          (S.EnergyMoment2Finite P N X →
            (∫⁻ ω, Bm ω ^ (2 : ℝ) ∂P₁) ^ (1 / (2 : ℝ)) ≤
              ENNReal.ofReal (Cr * sigN S N * (S.T * S.energyMoment2 P N X))) := by
  obtain ⟨C₀min, hrem⟩ := gff_remainder_bound b M K
  refine ⟨C₀min, fun C₀ hC₀ => ?_⟩
  obtain ⟨Cr, hCr, hrem'⟩ := hrem C₀ hC₀
  refine ⟨Cr, hCr, ?_⟩
  intro S hS hMF N hN m hm EV hEV Ω mΩ P _ X₀ W X hX hF hE η₀ hη hind Y₀ hY₀m hY₀ Y hY
  have hT : 0 ≤ S.T := S.hT.le
  obtain ⟨ℱ, W', hF'⟩ := hF
  obtain ⟨Ω₁, mΩ₁, P₁, hP₁, π₁, hπ₁, ℱ₁, η', hfilt, hF₁, hη'0, hlawI⟩ :=
    gf_init_enlargement_proof S N P X₀ W X ℱ W' hF' hX.init η₀ hη hind
  set X₁ : ℝ≥0 → Ω₁ → Config d N := fun t ω => X t (π₁ ω) with hX₁def
  set W₁ : ℝ≥0 → Ω₁ → (Fin N → Euc d) := fun t ω => W t (π₁ ω) with hW₁def
  set W'₁ : ℝ≥0 → Ω₁ → (Fin N × Fin d) → ℝ := fun t ω k => W' t (π₁ ω) k with hW'₁def
  have hX₁ : IsStrongSolution P₁ (S.dynM M N) S.T (fun ω => X₀ (π₁ ω)) W₁ X₁ :=
    isStrongSolution_comp hπ₁ hX
  obtain ⟨hE₁, hEeq⟩ := energyMoment_comp S hπ₁ X hE
  have hγm : (d : ℝ) / 2 < (S.γ : ℝ) := by
    have h1 : 2 * d + 10 < S.γ := S.hγ
    have h2 : ((2 * d + 10 : ℕ) : ℝ) < (S.γ : ℝ) := by exact_mod_cast h1
    push_cast at h2
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  -- energy integrals on `Ω₁`
  obtain ⟨hnn, hint, hmom, hmom2, hmeas⟩ :=
    gf_energy_integral_moment_proof S M hMF N hN P₁ (fun ω => X₀ (π₁ ω)) W₁ X₁ hX₁ ⟨ℱ₁, W'₁, hF₁⟩ hE₁
  -- the particle martingale and its stochastic convolution
  obtain ⟨Mart, hMartIto, hMartHM⟩ := gf_particle_martingale_proof S N (by omega) P₁ ℱ₁ W'₁ W₁ X₁ hF₁
  obtain ⟨Cm, hCm0, hmax⟩ := Q45.maximal_estimate_meas S.T K hT
  obtain ⟨Z₀, hZ₀, hZ₀c, hZ₀m, -⟩ := hmax Ω₁ P₁ ℱ₁ (NegSobolev d (S.γ : ℝ)) (NegSobolev d m) EV hEV.maxHyp
    Mart (fun r ω => covForm (S.γ : ℝ) (qN S N) (empirical (X₁ (Real.toNNReal r) ω))) hMartHM
  obtain ⟨Z, hZm, hZc, hZeq⟩ := gf_measurable_modification_proof P₁ S.T Z₀ hZ₀c hZ₀m
  have hZ : ∀ t ∈ Set.Icc (0 : ℝ) S.T, IsStochConv P₁ EV.VE EV.j Mart 0 t (Z t) :=
    fun t ht => isStochConv_congr_ae (hZ₀ t ht) (hZeq t ht).symm
  -- continuity of the fluctuation path
  obtain ⟨hΞc, hΞm⟩ := gf_fluc_continuous_proof S M hMF N m hm P₁ (fun ω => X₀ (π₁ ω)) W₁ X₁ hX₁ (sigN S N)
  obtain ⟨-, hΞmP⟩ := gf_fluc_continuous_proof S M hMF N m hm P X₀ W X hX (sigN S N)
  -- the remainder
  have hR := hrem' S hS hMF N hN m hm EV hEV P₁ (fun ω => X₀ (π₁ ω)) W₁ X₁ hX₁ ℱ₁ W'₁ hF₁ hE₁ Mart
    hMartIto Z hZ (fun t _ => hZm t) (Filter.Eventually.of_forall hZc) hΞc
  set Bm : Ω₁ → ℝ≥0∞ := fun ω => ENNReal.ofReal (Cr * sigN S N *
    ∫ r in Set.Icc (0 : ℝ) S.T, S.energyCompletion N (X₁ (Real.toNNReal r) ω) r) with hBm
  have hc0 : 0 ≤ Cr * sigN S N := mul_nonneg hCr.le (sigN_nonneg S N)
  have hbound : ∀ᵐ ω ∂P₁, ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      ‖flucProc m (sigN S N) X₁ (S.ρ N) t ω -
          EV.VE t 0 (EV.j (flucProc (S.γ : ℝ) (sigN S N) X₁ (S.ρ N) 0 ω)) - Z t ω‖ₑ ≤ Bm ω := by
    filter_upwards [hR, hnn, hint] with ω hω hn hi t ht
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ((hω t ht).trans ?_)
    refine mul_le_mul_of_nonneg_left ?_ hc0
    rw [intervalIntegral.integral_of_le ht.1]
    exact setIntegral_mono_set hi ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall hn))
      (HasSubset.Subset.eventuallyLE (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl ht.2)))
  have hBmm : AEMeasurable Bm P₁ :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hmeas.const_mul (Cr * sigN S N))
  have hBm1 : ∫⁻ ω, Bm ω ∂P₁ ≤ ENNReal.ofReal (Cr * sigN S N * (S.T * S.energyMoment P N X)) := by
    have e : ∀ ω, Bm ω = ENNReal.ofReal (Cr * sigN S N) * ENNReal.ofReal
        (∫ r in Set.Icc (0 : ℝ) S.T, S.energyCompletion N (X₁ (Real.toNNReal r) ω) r) :=
      fun ω => ENNReal.ofReal_mul hc0
    simp_rw [e]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul hc0]
    have := hmom
    rw [hEeq] at this
    gcongr
  have hBm2 : S.EnergyMoment2Finite P N X → (∫⁻ ω, Bm ω ^ (2 : ℝ) ∂P₁) ^ (1 / (2 : ℝ)) ≤
      ENNReal.ofReal (Cr * sigN S N * (S.T * S.energyMoment2 P N X)) := by
    intro hE2
    obtain ⟨hE2₁, hE2eq⟩ := energyMoment2_comp S hπ₁ X hE2
    have hm2 := (gf_energy_integral_moment_proof S M hMF N hN P₁ (fun ω => X₀ (π₁ ω)) W₁ X₁ hX₁ ⟨ℱ₁, W'₁, hF₁⟩ hE₁).2.2.2.1 hE2₁
    rw [hE2eq] at hm2
    have e : ∀ ω, Bm ω ^ (2 : ℝ) = ENNReal.ofReal (Cr * sigN S N) ^ (2 : ℝ) * (ENNReal.ofReal
        (∫ r in Set.Icc (0 : ℝ) S.T, S.energyCompletion N (X₁ (Real.toNNReal r) ω) r)) ^ (2 : ℝ) := by
      intro ω
      rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.ofReal_mul hc0]
    simp_rw [e]
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
      ENNReal.rpow_one, ENNReal.ofReal_mul hc0]
    simp_rw [ENNReal.rpow_two]
    gcongr
  -- the law of the initial value
  have hη'm : Measurable η' := hη'0.mono (ℱ₁.le 0) le_rfl
  have hX₀m : AEMeasurable X₀ P := (hX.adapted 0).aemeasurable.congr hX.init
  have hm1 : AEMeasurable (fun ω' => (X₀ (π₁ ω'), η' ω')) P₁ :=
    (hX₀m.comp_quasiMeasurePreserving hπ₁.quasiMeasurePreserving).prodMk hη'm.aemeasurable
  have hm2 : AEMeasurable (fun ω => (X₀ ω, η₀ ω)) P := hX₀m.prodMk hη.aemeasurable
  have hmapη : P.map η₀ = P₁.map η' := by
    have e1 : P₁.map η' = (P₁.map (fun ω' => (X₀ (π₁ ω'), η' ω'))).map Prod.snd := by
      rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hm1]; rfl
    have e2 : P.map η₀ = (P.map (fun ω => (X₀ ω, η₀ ω))).map Prod.snd := by
      rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hm2]; rfl
    rw [e1, hlawI, ← e2]
  have hg : Measurable (fun x : NegSobolev d (S.γ : ℝ) => EV.j (AN S N • x)) :=
    EV.j.continuous.measurable.comp (measurable_const_smul _)
  have hlawY : P.map Y₀ = P₁.map (fun ω => EV.j (AN S N • η' ω)) := by
    have e : Y₀ = fun ω => EV.j (AN S N • η₀ ω) := funext hY₀
    rw [e, show (fun ω => EV.j (AN S N • η₀ ω)) = (fun x => EV.j (AN S N • x)) ∘ η₀ from rfl,
      ← Measure.map_map hg hη, hmapη, Measure.map_map hg hη'm]
    rfl
  refine ⟨Ω₁, mΩ₁, P₁, hP₁, π₁, hπ₁, ℱ₁, η', Mart, Z, Bm, ⟨hF₁.adapted, hη'0,
    fun τ => (hMartIto.adapted τ).mono (ℱ₁.le τ) le_rfl, hMartHM,
    gf_detCovDensity_proof S M hMF N (qN S N) (qN_nonneg S N), hZ, Filter.Eventually.of_forall hZc, hZm, hΞc, hΞm,
    hBmm, hbound, hY₀m, hY, hlawY⟩, hX₁, ⟨ℱ₁, W'₁, hF₁⟩, hE₁, hEeq, ?_, ?_, hBm1, hBm2⟩
  · exact law_comp_mp hπ₁ hΞmP
  · intro p hp hfin
    exact gff_initial_term_eq S hπ₁ X₀ X hX.init hX₀m η₀ η' hη hη'm hlawI hγm p
      (by rcases hp with rfl | rfl <;> norm_num) hfin

/-- PROVED.  The energy moments are nonnegative (the completed energy is a.s. nonnegative). -/
theorem gff_energyMoment_nonneg (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (hMF : S.MFHypM M) (N : ℕ)
    (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hX : IsStrongSolution P (S.dynM M N) S.T X₀ W X)
    (hF : ∃ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X)
    (hE : S.EnergyMomentFinite P N X) : 0 ≤ S.energyMoment P N X := by
  have hnn := (gf_energy_integral_moment_proof S M hMF N hN P X₀ W X hX hF hE).1
  unfold GeneralSetup.energyMoment
  refine Real.iSup_nonneg fun t => integral_nonneg_of_ae ?_
  filter_upwards [hnn] with ω hω
  exact hω t.1 t.2

end HRS.GF
