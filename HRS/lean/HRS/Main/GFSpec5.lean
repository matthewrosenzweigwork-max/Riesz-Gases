import HRS.Main.GFSpec4
import HRS.Main.GFB4Aux3

/-!
# Packet GF-SPEC, part 5: the conditional assembly (stage 2: comparison on the coupling space)

PROVED glue of the assembly of Theorem 2.1 from the sub-packet statements of `GFSpec1`-`GFSpec3`:
`gf_stage2_smooth` carries out, conditionally on the sorried packets, the application of `smooth_path_comparison_proof` and of
`gf_law_identification` on the Gaussian-coupling enlargement of a first enlargement `Ω₁` (that of `gf_init_enlargement`), and moves all
integrals back to `Ω₁`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS.Uniform

variable {d : ℕ}

/-- PROVED.  A continuous process gives the corresponding continuous map as its window path. -/
theorem windowPath_eq_of_continuous {Ω : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (T : ℝ)
    (R : ℝ → Ω → E) (ω : Ω) (hc : Continuous fun t : Set.Icc (0 : ℝ) T => R (t : ℝ) ω) :
    windowPath 0 T R ω = (⟨fun t : Set.Icc (0 : ℝ) T => R (t : ℝ) ω, hc⟩ : C(Set.Icc (0 : ℝ) T, E)) := by
  unfold windowPath
  exact (dite_continuousMap_congr _ _ (funext fun t => by simp)).trans (dif_pos hc)

/-- PROVED.  A discontinuous process has the junk window path `0`. -/
theorem windowPath_eq_zero {Ω : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (T : ℝ)
    (R : ℝ → Ω → E) (ω : Ω) (hc : ¬ Continuous fun t : Set.Icc (0 : ℝ) T => R (t : ℝ) ω) :
    windowPath 0 T R ω = (0 : C(Set.Icc (0 : ℝ) T, E)) := by
  unfold windowPath
  exact (dite_continuousMap_congr _ _ (funext fun t => by simp)).trans (dif_neg hc)

/-- PROVED.  The sup-norm of a window path is bounded by a bound on the sections. -/
theorem windowPath_enorm_le {Ω : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (T : ℝ)
    (R : ℝ → Ω → E) (ω : Ω) (B : ℝ≥0∞) (h : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖R t ω‖ₑ ≤ B) :
    ‖windowPath 0 T R ω‖ₑ ≤ B := by
  by_cases hB : B = ⊤
  · rw [hB]; exact le_top
  have hb : 0 ≤ B.toReal := ENNReal.toReal_nonneg
  by_cases hc : Continuous fun t : Set.Icc (0 : ℝ) T => R (t : ℝ) ω
  · have key : ‖(⟨fun t : Set.Icc (0 : ℝ) T => R (t : ℝ) ω, hc⟩ : C(Set.Icc (0 : ℝ) T, E))‖ₑ ≤ B := by
      rw [← ofReal_norm, ← ENNReal.ofReal_toReal hB]
      refine ENNReal.ofReal_le_ofReal ((ContinuousMap.norm_le _ hb).2 fun t => ?_)
      have := h t.1 t.2
      rw [← ofReal_norm, ← ENNReal.ofReal_toReal hB, ENNReal.ofReal_le_ofReal_iff hb] at this
      exact this
    calc ‖windowPath 0 T R ω‖ₑ
        = ‖(⟨fun t : Set.Icc (0 : ℝ) T => R (t : ℝ) ω, hc⟩ : C(Set.Icc (0 : ℝ) T, E))‖ₑ := by
          rw [windowPath_eq_of_continuous T R ω hc]; rfl
      _ ≤ B := key
  · calc ‖windowPath 0 T R ω‖ₑ = ‖(0 : C(Set.Icc (0 : ℝ) T, E))‖ₑ := by
          rw [windowPath_eq_zero T R ω hc]; rfl
      _ ≤ B := by
          have : ‖(0 : C(Set.Icc (0 : ℝ) T, E))‖ₑ = 0 := by
            rw [← ofReal_norm, norm_zero, ENNReal.ofReal_zero]
          rw [this]; exact bot_le

/-- PROVED.  Moving an `ℝ≥0∞`-integral along a measure-preserving map. -/
theorem lintegral_comp_mp {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    {P' : Measure Ω'} {π : Ω' → Ω} (hπ : MeasurePreserving π P' P) {f : Ω → ℝ≥0∞}
    (hf : AEMeasurable f P) : ∫⁻ ω', f (π ω') ∂P' = ∫⁻ ω, f ω ∂P := by
  rw [← hπ.map_eq, lintegral_map' (by rwa [hπ.map_eq]) hπ.aemeasurable]

/-- PROVED.  The law of a composite with a measure-preserving map. -/
theorem law_comp_mp {Ω Ω' B : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace B]
    {P : Measure Ω} {P' : Measure Ω'} {π : Ω' → Ω} (hπ : MeasurePreserving π P' P) {F : Ω → B}
    (hF : AEMeasurable F P) : law P' (fun ω' => F (π ω')) = law P F := by
  have : AEMeasurable F (Measure.map π P') := by rwa [hπ.map_eq]
  rw [show (fun ω' => F (π ω')) = F ∘ π from rfl, law, law, ← AEMeasurable.map_map_of_aemeasurable this hπ.aemeasurable,
    hπ.map_eq]

/-- PROVED.  The covariance-discrepancy integral `ω ↦ ∫_0^T ‖Sg_r(ω) - Cb_r‖₁ dr` is measurable. -/
theorem measurable_trace_integral {Ω₁ : Type*} [MeasurableSpace Ω₁] {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁] {ℱ₁ : Filtration ℝ ‹MeasurableSpace Ω₁›} {T : ℝ}
    {Mart : ℝ → Ω₁ → H} {Sg : ℝ → Ω₁ → (H →L[ℝ] H →L[ℝ] ℝ)} {Cb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)}
    (hM : IsHilbertMartingaleWithCovariation P₁ ℱ₁ T Mart Sg) (hDet : IsDetCovDensity T Cb) :
    Measurable fun ω => ∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (Sg r ω - Cb r)) := by
  have h1 : Measurable (fun p : Ω₁ × ℝ => traceNormForm (Sg p.2 p.1 - Cb p.2)) := by
    refine measurable_traceNormForm (H := H) (α := Ω₁ × ℝ) (fun p => Sg p.2 p.1 - Cb p.2) (fun x y => ?_)
    simp only [ContinuousLinearMap.sub_apply]
    exact ((hM.sigma_meas x y).comp measurable_swap).sub ((hDet.meas x y).comp measurable_snd)
  have h2 : Measurable fun p : Ω₁ × ℝ => ENNReal.ofReal (traceNormForm (Sg p.2 p.1 - Cb p.2)) :=
    ENNReal.measurable_ofReal.comp h1
  exact h2.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) T))

/-- The data and the hypotheses of "stage 1" of the assembly (NEW structure; all fields are propositions, the data are
parameters): `Ω₁` is the first enlargement (that of `gf_init_enlargement`, `P₁`), `X₁` the adapted particle path on it, `η'` the
`ℱ₁_0`-measurable initial coupling, `Mart` the particle martingale, `Z` a measurable, continuous stochastic convolution of it,
`Bm` an `ℝ≥0∞`-valued a.e.-measurable pathwise bound of the remainder `R_t = Ξ^t - V(t,0) j Ξ^0 - Z_t`, and `Y` a solution of the linear
equation on `Ω` whose initial value `Y₀` has the law of `A_N j η'`. -/
structure Stage1 (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (N : ℕ) (m K : ℝ)
    (EV : EvolData (NegSobolev d (S.γ : ℝ)) (NegSobolev d m))
    {Ω Ω₁ : Type} [mΩ : MeasurableSpace Ω] [mΩ₁ : MeasurableSpace Ω₁]
    (P : Measure Ω) (P₁ : Measure Ω₁) (ℱ₁ : Filtration ℝ mΩ₁) (X₁ : ℝ≥0 → Ω₁ → Config d N)
    (η' : Ω₁ → NegSobolev d (S.γ : ℝ)) (Mart : ℝ → Ω₁ → NegSobolev d (S.γ : ℝ))
    (Z : ℝ → Ω₁ → NegSobolev d m) (Bm : Ω₁ → ℝ≥0∞) (Y₀ : Ω → NegSobolev d m)
    (Y : ℝ → Ω → NegSobolev d m) : Prop where
  adapted : ∀ t : ℝ≥0, Measurable[ℱ₁ t] (X₁ t)
  eta_meas : Measurable[ℱ₁ 0] η'
  mart_meas : ∀ τ, Measurable (Mart τ)
  mart : IsHilbertMartingaleWithCovariation P₁ ℱ₁ S.T Mart
    (fun r ω => covForm (S.γ : ℝ) (qN S N) (empirical (X₁ (Real.toNNReal r) ω)))
  det : IsDetCovDensity S.T (covDensT (S.γ : ℝ) (qN S N) S.T (S.ρ N))
  conv : ∀ t ∈ Set.Icc (0 : ℝ) S.T, IsStochConv P₁ EV.VE EV.j Mart 0 t (Z t)
  conv_cont : ∀ᵐ ω ∂P₁, ContinuousOn (fun t => Z t ω) (Set.Icc 0 S.T)
  conv_meas : ∀ t, Measurable (Z t)
  fluc_cont : ∀ᵐ ω ∂P₁, Continuous fun t : Set.Icc (0 : ℝ) S.T => flucProc m (sigN S N) X₁ (S.ρ N) t ω
  fluc_meas : AEMeasurable (flucPath m S.T (sigN S N) X₁ (S.ρ N)) P₁
  bound_meas : AEMeasurable Bm P₁
  bound : ∀ᵐ ω ∂P₁, ∀ t ∈ Set.Icc (0 : ℝ) S.T,
    ‖flucProc m (sigN S N) X₁ (S.ρ N) t ω -
        EV.VE t 0 (EV.j (flucProc (S.γ : ℝ) (sigN S N) X₁ (S.ρ N) 0 ω)) - Z t ω‖ₑ ≤ Bm ω
  Y₀_meas : Measurable Y₀
  Y_sol : IsLinearFluctuationSolution P (S.dynM M N) (S.ρ N) m (qN S N) S.T Y₀ Y
  law_init : P.map Y₀ = P₁.map (fun ω => EV.j (AN S N • η' ω))

set_option maxHeartbeats 800000 in
/-- **Stage 2 of the assembly: the three comparison estimates on the first enlargement** (PROVED, conditional on the sorried
packets `gf_measurable_modification`, `gf_law_identification`, `gf_wasserstein_comparison`, `gf_measurable_ofMeasureDiff`).
Given the stage-1 data and an adapted Gaussian coupling of the particle martingale with the deterministic covariation
`covDensT` and a cost `cost` (the trace-norm cost of `gf_adapted_coupling_trace` or the transport cost of
`gf_adapted_coupling_transport`), the second enlargement of the coupling carries the Gaussian surrogate, and
* `d₂(Law Ξ, Law Y) ≤ C E‖Ξ⁰ - A η'‖ + E Bm + C E ∫_0^T ‖C_N^r - C̄_N^r‖₁ dr`  (`smooth_path_comparison_proof`, any coupling),
* `W_p(Law Ξ, Law Y) ≤ C ‖Ξ⁰ - A η'‖_{L^p} + ‖Bm‖_{L^p} + C (E ∫_0^T cost_r dr)^{1/2}`, `p = 1, 2`  (`gf_wasserstein_comparison`),
with `C = C(T,K)`.  All integrals are over `Ω₁`; `Law Ξ` is the law of the particle path on `Ω₁`. -/
theorem gf_stage2 (T K : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : GeneralSetup d), S.T = T → ∀ (M : Matrix (Fin d) (Fin d) ℝ), S.MFHypM M → ∀ (N : ℕ), 2 ≤ N →
      ∀ (m : ℝ), (S.γ : ℝ) ≤ m →
      ∀ (EV : EvolData (NegSobolev d (S.γ : ℝ)) (NegSobolev d m)), GFEvo S M N m K EV →
      ∀ {Ω Ω₁ : Type} [mΩ : MeasurableSpace Ω] [mΩ₁ : MeasurableSpace Ω₁]
        (P : Measure Ω) [IsProbabilityMeasure P] (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
        (ℱ₁ : Filtration ℝ mΩ₁) (X₁ : ℝ≥0 → Ω₁ → Config d N)
        (η' : Ω₁ → NegSobolev d (S.γ : ℝ)) (Mart : ℝ → Ω₁ → NegSobolev d (S.γ : ℝ))
        (Z : ℝ → Ω₁ → NegSobolev d m) (Bm : Ω₁ → ℝ≥0∞) (Y₀ : Ω → NegSobolev d m)
        (Y : ℝ → Ω → NegSobolev d m),
        Stage1 S M N m K EV P P₁ ℱ₁ X₁ η' Mart Z Bm Y₀ Y →
        ∀ cost : ℝ → Ω₁ → ℝ,
        AdaptedGaussianCoupling P₁ ℱ₁ (ENNReal.ofReal S.T) ⟨ℱ₁ 0, le_rfl⟩ Mart
          (fun r ω => covForm (S.γ : ℝ) (qN S N) (empirical (X₁ (Real.toNNReal r) ω)))
          (covDensT (S.γ : ℝ) (qN S N) S.T (S.ρ N)) (· ≤ ·) cost →
        AEMeasurable (fun ω => ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (cost r ω)) P₁ →
        (ENNReal.ofReal (smoothDist 2 (law P₁ (flucPath m S.T (sigN S N) X₁ (S.ρ N)))
            (law P (toPath m S.T Y))) ≤
          ENNReal.ofReal C * ∫⁻ ω, ‖flucProc (S.γ : ℝ) (sigN S N) X₁ (S.ρ N) 0 ω - AN S N • η' ω‖ₑ ∂P₁ +
            ∫⁻ ω, Bm ω ∂P₁ +
            ENNReal.ofReal C * ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (traceNormForm
              (covForm (S.γ : ℝ) (qN S N) (empirical (X₁ (Real.toNNReal r) ω)) -
                covForm (S.γ : ℝ) (qN S N) (withDensityReal (S.ρ N r))))) ∂P₁) ∧
        (∀ p : ℝ, (p = 1 ∨ p = 2) →
          wassersteinE p (law P₁ (flucPath m S.T (sigN S N) X₁ (S.ρ N))) (law P (toPath m S.T Y)) ≤
            ENNReal.ofReal C * (∫⁻ ω, ‖flucProc (S.γ : ℝ) (sigN S N) X₁ (S.ρ N) 0 ω -
                AN S N • η' ω‖ₑ ^ p ∂P₁) ^ (1 / p) +
              (∫⁻ ω, Bm ω ^ p ∂P₁) ^ (1 / p) +
              ENNReal.ofReal C * (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (cost r ω)) ∂P₁) ^
                (1 / 2 : ℝ)) := by
  obtain ⟨Cs, hCs0, hsm⟩ := smooth_path_comparison_proof T K hT
  obtain ⟨Cm, hCm0, hmax⟩ := Q45.maximal_estimate_meas T K hT
  obtain ⟨Cw1, hCw10, hwp1⟩ := gf_wasserstein_comparison T K hT 1 (Or.inl rfl)
  obtain ⟨Cw2, hCw20, hwp2⟩ := gf_wasserstein_comparison T K hT 2 (Or.inr rfl)
  refine ⟨max Cs (max Cw1 Cw2), le_max_of_le_left hCs0, ?_⟩
  intro S hST M hMF N hN m hm EV hEV Ω Ω₁ mΩ mΩ₁ P _ P₁ _ ℱ₁ X₁ η' Mart Z Bm Y₀ Y h cost hcpl hcostm
  subst hST
  obtain ⟨hXad, hη', hMartM, hMart, hDet, hZ, hZc, hZm, hΞc, hΞm, hBm, hRb, hY₀m, hY, hlaw⟩ := h
  set σ := sigN S N with hσ
  set q := qN S N with hq
  set Cb := covDensT (S.γ : ℝ) q S.T (S.ρ N) with hCb
  set Sg : ℝ → Ω₁ → (NegSobolev d (S.γ : ℝ) →L[ℝ] NegSobolev d (S.γ : ℝ) →L[ℝ] ℝ) :=
    fun r ω => covForm (S.γ : ℝ) q (empirical (X₁ (Real.toNNReal r) ω)) with hSg
  have hγm : (d : ℝ) / 2 < (S.γ : ℝ) := by
    have h1 : 2 * d + 10 < S.γ := S.hγ
    have h2 : ((2 * d + 10 : ℕ) : ℝ) < (S.γ : ℝ) := by exact_mod_cast h1
    push_cast at h2
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hmm : (d : ℝ) / 2 < m := lt_of_lt_of_le hγm hm
  -- the Gaussian coupling on a second enlargement
  obtain ⟨Ω₂, mΩ₂, P₂, π, ℱ₂, Gb, Sd, hc⟩ := hcpl
  haveI : IsProbabilityMeasure (P₂ : Measure Ω₂) := inferInstance
  have hπ : MeasurePreserving π (P₂ : Measure Ω₂) P₁ := hc.preserving
  -- the Gaussian martingale, with the untruncated deterministic covariation
  have hGb : IsHilbertMartingaleWithCovariation (P₂ : Measure Ω₂) ℱ₂ S.T Gb (fun r _ => Cb r) := by
    have h1 := hc.gaussian S.T hT le_rfl
    have e : (fun (r : ℝ) (_ : Ω₂) => if ENNReal.ofReal r ≤ ENNReal.ofReal S.T then Cb r else 0) =
        fun r _ => Cb r := by
      funext r _
      exact covDensT_truncated hT _ r
    rw [e] at h1
    exact h1
  -- its stochastic convolution
  obtain ⟨Zb₀, hZb₀, hZbc₀, hZbm₀, -⟩ := hmax Ω₂ (P₂ : Measure Ω₂) ℱ₂ (NegSobolev d (S.γ : ℝ))
    (NegSobolev d m) EV hEV.maxHyp Gb (fun r _ => Cb r) hGb
  obtain ⟨Zb, hZbm, hZbc, hZbeq⟩ := gf_measurable_modification (P₂ : Measure Ω₂) S.T Zb₀ hZbc₀ hZbm₀
  have hZb : ∀ t ∈ Set.Icc (0 : ℝ) S.T, IsStochConv (P₂ : Measure Ω₂) EV.VE EV.j Gb 0 t (Zb t) :=
    fun t ht => isStochConv_congr_ae (hZb₀ t ht) (hZbeq t ht).symm
  -- measurability of the fluctuation process
  have hX₁m : ∀ t : ℝ≥0, Measurable (X₁ t) := fun t => (hXad t).mono (ℱ₁.le t) le_rfl
  have hflucm : ∀ (m' : ℝ), (d : ℝ) / 2 < m' → ∀ t : ℝ,
      Measurable (fun ω => flucProc m' σ X₁ (S.ρ N) t ω) := fun m' hm' t =>
    (gf_measurable_ofMeasureDiff m' hm' (withDensityReal (S.ρ N t))).const_smul σ |>.comp
      (hX₁m (Real.toNNReal t))
  -- the data on the second enlargement
  set X₀ : Ω₂ → NegSobolev d (S.γ : ℝ) := fun ω => flucProc (S.γ : ℝ) σ X₁ (S.ρ N) 0 (π ω) with hX₀
  set X₀' : Ω₂ → NegSobolev d (S.γ : ℝ) := fun ω => AN S N • η' (π ω) with hX₀'
  set Xp : ℝ → Ω₂ → NegSobolev d m := fun t ω => flucProc m σ X₁ (S.ρ N) t (π ω) with hXp
  set Zp : ℝ → Ω₂ → NegSobolev d m := fun t ω => Z t (π ω) with hZp
  set Rp : ℝ → Ω₂ → NegSobolev d m :=
    fun t ω => Xp t ω - EV.VE t 0 (EV.j (X₀ ω)) - Zp t ω with hRp
  set Xb : ℝ → Ω₂ → NegSobolev d m := fun t ω => EV.VE t 0 (EV.j (X₀' ω)) + Zb t ω with hXb
  have hπ0 : Measurable[ℱ₂ 0, ℱ₁ 0] π := Measurable.of_comap_le (hc.filtration 0)
  have hX0 : Measurable[ℱ₁ 0] (X₁ (Real.toNNReal 0)) :=
    (hXad (Real.toNNReal 0)).mono (ℱ₁.mono (by simp)) le_rfl
  have hX₀m : Measurable[ℱ₂ 0] X₀ := by
    have h1 : Measurable[ℱ₁ 0] (fun ω => flucProc (S.γ : ℝ) σ X₁ (S.ρ N) 0 ω) :=
      ((gf_measurable_ofMeasureDiff (S.γ : ℝ) hγm (withDensityReal (S.ρ N 0))).const_smul σ).comp hX0
    exact h1.comp hπ0
  have hX₀'m : Measurable[ℱ₂ 0] X₀' := (hη'.const_smul (AN S N)).comp hπ0
  have hM₂ := hc.martingale S.T hT le_rfl
  have hMπm : ∀ τ, Measurable (fun ω => Mart τ (π ω)) := fun τ => (hMartM τ).comp hπ.measurable
  have hGbm : ∀ τ, Measurable (Gb τ) := fun τ =>
    gfb4_measurable_of_weak fun x => (((hGb.martingale x).stronglyAdapted τ).mono (ℱ₂.le τ)).measurable
  have hMm : ∀ τ, AEMeasurable (fun ω => EV.j (Mart τ ω)) P₁ := fun τ =>
    (EV.j.continuous.measurable.comp (hMartM τ)).aemeasurable
  have hZpS : ∀ t ∈ Set.Icc (0 : ℝ) S.T, IsStochConv (P₂ : Measure Ω₂) EV.VE EV.j
      (fun τ ω => Mart τ (π ω)) 0 t (Zp t) :=
    fun t ht => isStochConv_comp hπ (hMm) (hZm t).aemeasurable (hZ t ht)
  have hZpc : ∀ᵐ ω ∂(P₂ : Measure Ω₂), ContinuousOn (fun t => Zp t ω) (Set.Icc 0 S.T) :=
    hπ.quasiMeasurePreserving.ae hZc
  have hZpm : ∀ t, Measurable (Zp t) := fun t => (hZm t).comp hπ.measurable
  have hRpc : ∀ᵐ ω ∂(P₂ : Measure Ω₂), ContinuousOn (fun t => Rp t ω) (Set.Icc 0 S.T) := by
    filter_upwards [hπ.quasiMeasurePreserving.ae hZc, hπ.quasiMeasurePreserving.ae hΞc] with ω hz hξ
    have h1 : ContinuousOn (fun t => flucProc m σ X₁ (S.ρ N) t (π ω)) (Set.Icc 0 S.T) :=
      continuousOn_iff_continuous_restrict.2 hξ
    have h2 : ContinuousOn (fun t : ℝ => EV.VE t 0 (EV.j (X₀ ω))) (Set.Icc 0 S.T) := by
      have hcE := hEV.maxHyp.1.cont_E (EV.j (X₀ ω))
      refine hcE.comp (continuousOn_id.prodMk continuousOn_const) fun t ht => ?_
      exact ⟨le_rfl, ht.1, ht.2⟩
    exact (h1.sub h2).sub hz
  have hRpm : ∀ t, Measurable (Rp t) := fun t =>
    (((hflucm m hmm t).comp hπ.measurable).sub
      ((EV.VE t 0).continuous.measurable.comp (EV.j.continuous.measurable.comp
        ((hflucm (S.γ : ℝ) hγm 0).comp hπ.measurable)))).sub (hZpm t)
  have hXform : ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ ω,
      Xp t ω = EV.VE t 0 (EV.j (X₀ ω)) + Zp t ω + Rp t ω := by
    intro t _ ω
    simp only [hRp]
    abel
  have hXbform : ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ ω, Xb t ω = EV.VE t 0 (EV.j (X₀' ω)) + Zb t ω :=
    fun _ _ _ => rfl
  have key := hsm Ω₂ (P₂ : Measure Ω₂) ℱ₂ (NegSobolev d (S.γ : ℝ)) (NegSobolev d m) EV hEV.maxHyp X₀ X₀'
    hX₀m hX₀'m (fun τ ω => Mart τ (π ω)) (fun r ω => Sg r (π ω)) hM₂ Gb Cb hDet hGb Zp Zb Rp hZpS hZb hZpc
    (Filter.Eventually.of_forall hZbc) hRpc hZpm hZbm hRpm Xp Xb hXform hXbform
  -- the law of the particle path
  have hFm : AEMeasurable (windowPath 0 S.T (flucProc m σ X₁ (S.ρ N))) P₁ := by
    have e : windowPath 0 S.T (flucProc m σ X₁ (S.ρ N)) = flucPath m S.T σ X₁ (S.ρ N) :=
      funext fun ω => (flucPath_eq_windowPath m S.T σ X₁ (S.ρ N) ω).symm
    rw [e]
    exact hΞm
  have hlaw1 : law (P₂ : Measure Ω₂) (windowPath 0 S.T Xp) =
      law P₁ (flucPath m S.T σ X₁ (S.ρ N)) := by
    have h1 := law_comp_mp hπ hFm
    have e : windowPath 0 S.T (flucProc m σ X₁ (S.ρ N)) = flucPath m S.T σ X₁ (S.ρ N) :=
      funext fun ω => (flucPath_eq_windowPath m S.T σ X₁ (S.ρ N) ω).symm
    rw [e] at h1
    have e2 : windowPath 0 S.T Xp = fun ω' => flucPath m S.T σ X₁ (S.ρ N) (π ω') :=
      funext fun ω' => (flucPath_eq_windowPath m S.T σ X₁ (S.ρ N) (π ω')).symm
    rw [e2]
    exact h1
  -- the law of the Gaussian surrogate
  have hη'm : Measurable η' := hη'.mono (ℱ₁.le 0) le_rfl
  have hX₀'meas : Measurable X₀' := ((hη'm.const_smul (AN S N))).comp hπ.measurable
  have hGind := gf_coupling_indep hc hT (fun ω => AN S N • η' ω) (hη'.const_smul (AN S N))
  have hlaw₂ : P.map Y₀ = (P₂ : Measure Ω₂).map (fun ω' => EV.j (X₀' ω')) := by
    rw [hlaw]
    exact (law_comp_mp hπ (F := fun ω => EV.j (AN S N • η' ω))
      (EV.j.continuous.measurable.comp (hη'm.const_smul (AN S N))).aemeasurable).symm
  have hL := gf_law_identification S M hMF N hN m K hm EV hEV P (P₂ : Measure Ω₂) ℱ₂ X₀' hX₀'meas Gb hGb
    hGind Zb hZb (Filter.Eventually.of_forall hZbc) hZbm Y₀ hY₀m hlaw₂ Y hY
  have hL' : law P (toPath m S.T Y) = law (P₂ : Measure Ω₂) (windowPath 0 S.T Xb) := hL
  -- the three terms, moved back to `Ω₁`
  have hI1 : ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂(P₂ : Measure Ω₂) =
      ∫⁻ ω, ‖flucProc (S.γ : ℝ) σ X₁ (S.ρ N) 0 ω - AN S N • η' ω‖ₑ ∂P₁ :=
    lintegral_comp_mp hπ (f := fun ω => ‖flucProc (S.γ : ℝ) σ X₁ (S.ρ N) 0 ω - AN S N • η' ω‖ₑ)
      (((hflucm (S.γ : ℝ) hγm 0).sub (hη'm.const_smul (AN S N))).enorm).aemeasurable
  have hI2 : ∫⁻ ω, ‖windowPath 0 S.T Rp ω‖ₑ ∂(P₂ : Measure Ω₂) ≤ ∫⁻ ω, Bm ω ∂P₁ := by
    calc ∫⁻ ω, ‖windowPath 0 S.T Rp ω‖ₑ ∂(P₂ : Measure Ω₂)
        ≤ ∫⁻ ω, Bm (π ω) ∂(P₂ : Measure Ω₂) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hπ.quasiMeasurePreserving.ae hRb] with ω hω
          exact windowPath_enorm_le S.T Rp ω (Bm (π ω)) hω
      _ = ∫⁻ ω, Bm ω ∂P₁ := lintegral_comp_mp hπ hBm
  have hgm : Measurable fun ω => ∫⁻ r in Set.Icc (0 : ℝ) S.T,
      ENNReal.ofReal (traceNormForm (Sg r ω - Cb r)) := measurable_trace_integral hMart hDet
  have hI3 : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal
        (traceNormForm (Sg r (π ω) - Cb r))) ∂(P₂ : Measure Ω₂) =
      ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (traceNormForm
        (covForm (S.γ : ℝ) (qN S N) (empirical (X₁ (Real.toNNReal r) ω)) -
          covForm (S.γ : ℝ) (qN S N) (withDensityReal (S.ρ N r))))) ∂P₁ := by
    rw [lintegral_comp_mp hπ (f := fun ω => ∫⁻ r in Set.Icc (0 : ℝ) S.T,
      ENNReal.ofReal (traceNormForm (Sg r ω - Cb r))) hgm.aemeasurable]
    refine lintegral_congr fun ω => ?_
    refine setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    simp only [hSg, hCb, covDensT, if_pos hr]
    rfl
  have hsmooth : ENNReal.ofReal (smoothDist 2 (law P₁ (flucPath m S.T σ X₁ (S.ρ N)))
      (law P (toPath m S.T Y))) ≤
      ENNReal.ofReal Cs * ∫⁻ ω, ‖flucProc (S.γ : ℝ) σ X₁ (S.ρ N) 0 ω - AN S N • η' ω‖ₑ ∂P₁ +
        ∫⁻ ω, Bm ω ∂P₁ +
        ENNReal.ofReal Cs * ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (traceNormForm
          (covForm (S.γ : ℝ) (qN S N) (empirical (X₁ (Real.toNNReal r) ω)) -
            covForm (S.γ : ℝ) (qN S N) (withDensityReal (S.ρ N r))))) ∂P₁ := by
    have key' := key
    rw [hlaw1, ← hL'] at key'
    refine key'.trans ?_
    rw [hI1]
    refine add_le_add (add_le_add le_rfl hI2) (le_of_eq ?_)
    rw [show (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal
        (traceNormForm ((fun r ω => Sg r (π ω)) r ω - Cb r))) ∂(P₂ : Measure Ω₂)) = _ from hI3]
  -- the Wasserstein estimates
  have hD := gf_coupling_difference hc hT
  have hSd := gf_coupling_cost_le hc hT
  have hconv : ∀ (p : ℝ), 0 < p → ∀ (Cw : ℝ) (A : ℝ≥0∞),
      A ≤ ENNReal.ofReal Cw * (∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ^ p ∂(P₂ : Measure Ω₂)) ^ (1 / p) +
          (∫⁻ ω, ‖windowPath 0 S.T Rp ω‖ₑ ^ p ∂(P₂ : Measure Ω₂)) ^ (1 / p) +
          ENNReal.ofReal Cw * (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T,
            ENNReal.ofReal (cost r (π ω))) ∂(P₂ : Measure Ω₂)) ^ (1 / 2 : ℝ) →
      A ≤ ENNReal.ofReal Cw * (∫⁻ ω, ‖flucProc (S.γ : ℝ) σ X₁ (S.ρ N) 0 ω - AN S N • η' ω‖ₑ ^ p ∂P₁) ^ (1 / p) +
          (∫⁻ ω, Bm ω ^ p ∂P₁) ^ (1 / p) +
          ENNReal.ofReal Cw * (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (cost r ω)) ∂P₁) ^
            (1 / 2 : ℝ) := by
    intro p hp Cw A hA
    refine hA.trans ?_
    have e1 : ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ^ p ∂(P₂ : Measure Ω₂) =
        ∫⁻ ω, ‖flucProc (S.γ : ℝ) σ X₁ (S.ρ N) 0 ω - AN S N • η' ω‖ₑ ^ p ∂P₁ :=
      lintegral_comp_mp hπ (f := fun ω => ‖flucProc (S.γ : ℝ) σ X₁ (S.ρ N) 0 ω - AN S N • η' ω‖ₑ ^ p)
        ((((hflucm (S.γ : ℝ) hγm 0).sub (hη'm.const_smul (AN S N))).enorm).pow_const p).aemeasurable
    have e2 : ∫⁻ ω, ‖windowPath 0 S.T Rp ω‖ₑ ^ p ∂(P₂ : Measure Ω₂) ≤ ∫⁻ ω, Bm ω ^ p ∂P₁ := by
      calc ∫⁻ ω, ‖windowPath 0 S.T Rp ω‖ₑ ^ p ∂(P₂ : Measure Ω₂)
          ≤ ∫⁻ ω, Bm (π ω) ^ p ∂(P₂ : Measure Ω₂) := by
            refine lintegral_mono_ae ?_
            filter_upwards [hπ.quasiMeasurePreserving.ae hRb] with ω hω
            exact ENNReal.rpow_le_rpow (windowPath_enorm_le S.T Rp ω (Bm (π ω)) hω) hp.le
        _ = ∫⁻ ω, Bm ω ^ p ∂P₁ := lintegral_comp_mp hπ (f := fun ω => Bm ω ^ p) (hBm.pow_const p)
    have e3 : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (cost r (π ω))) ∂(P₂ : Measure Ω₂) =
        ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (cost r ω)) ∂P₁ :=
      lintegral_comp_mp hπ (f := fun ω => ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (cost r ω)) hcostm
    rw [e1, e3]
    exact add_le_add (add_le_add le_rfl (ENNReal.rpow_le_rpow e2 (by positivity))) le_rfl
  have hmono : ∀ Cw : ℝ, Cw ≤ max Cs (max Cw1 Cw2) → ∀ a b c : ℝ≥0∞,
      ENNReal.ofReal Cw * a + b + ENNReal.ofReal Cw * c ≤
        ENNReal.ofReal (max Cs (max Cw1 Cw2)) * a + b + ENNReal.ofReal (max Cs (max Cw1 Cw2)) * c :=
    fun Cw hCw a b c => by gcongr
  refine ⟨hsmooth.trans (hmono Cs (le_max_left _ _) _ _ _), ?_⟩
  intro p hp
  rcases hp with rfl | rfl
  · have key1 := hwp1 Ω₂ (P₂ : Measure Ω₂) ℱ₂ (NegSobolev d (S.γ : ℝ)) (NegSobolev d m) EV hEV.maxHyp X₀ X₀' (hX₀m.mono (ℱ₂.le 0) le_rfl) hX₀'meas
      (fun τ ω => Mart τ (π ω)) Gb hMπm hGbm Sd (fun r ω => cost r (π ω)) hD hSd Zp Zb Rp hZpS hZb hZpc
      (Filter.Eventually.of_forall hZbc) hRpc hZpm hZbm hRpm Xp Xb hXform hXbform
    rw [hlaw1, ← hL'] at key1
    exact (hconv 1 one_pos Cw1 _ key1).trans
      (hmono Cw1 (le_trans (le_max_left _ _) (le_max_right _ _)) _ _ _)
  · have key2 := hwp2 Ω₂ (P₂ : Measure Ω₂) ℱ₂ (NegSobolev d (S.γ : ℝ)) (NegSobolev d m) EV hEV.maxHyp X₀ X₀' (hX₀m.mono (ℱ₂.le 0) le_rfl) hX₀'meas
      (fun τ ω => Mart τ (π ω)) Gb hMπm hGbm Sd (fun r ω => cost r (π ω)) hD hSd Zp Zb Rp hZpS hZb hZpc
      (Filter.Eventually.of_forall hZbc) hRpc hZpm hZbm hRpm Xp Xb hXform hXbform
    rw [hlaw1, ← hL'] at key2
    exact (hconv 2 two_pos Cw2 _ key2).trans
      (hmono Cw2 (le_trans (le_max_right _ _) (le_max_right _ _)) _ _ _)

end HRS.GF
