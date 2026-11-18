import HRS.MS.S81sGlueAux
import HRS.MS.S81pBlocks

/-!
# S8.1 (worker S81S): the product-space glue assembling `S81PBlocks`

Namespace `HRS.Whole.S81S`, prefix `s81s_`.

`S81SOld` is the interface of the INITIAL + OLD blocks (worker S81Q): on an enlargement `(Ω₁, Q₁, π₁, ℱ₁)` of the filtered canonical realization it
carries the physical initial term `Ip`, the physical old current `Op`, two independent Gaussian blocks `G0, G1` (measurable for `ℱ₁(u - b)`) with
positive semidefinite fdd covariances `S0, S1` summing to `Q(2b + t + t')`, the `L²` costs, and the identifications of `Ip`, `Op` with the
initial term and the Itô integral over `[0, u - b]` of the Duhamel kernel.

`s81s_blocks : S81SOld → (weighted_critical_forcing) → S81PBlocks`: the recent block (`s81s_recent_block`, fixed horizon `b + T`), the physical
identification of the recent current (`s81s_recent_phys`: shifted Itô integral), the Duhamel identity of the original system (`s81s_duhamel`) and the
forcing bound are combined on one product space; the forcing path is DEFINED as `Fp = Ip + Op + Rp - ζ`, so that the Duhamel decomposition of the
window is an identity, and its size is the size of the centered forcing of `weighted_critical_forcing`.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole HRS.Whole.S81P HRS.Whole.S81W2

namespace HRS.Whole.S81S

/-- The Duhamel kernel `K_{s,α}(r, i, a) = 1_{[0,s]}(r) √(2/(Nβ)) ∂_a U^{r,s} φ_α (X_i(r))`. -/
def s81s_kernel (d N : ℕ) (a β m : ℝ) (ρβ : Euc d → ℝ) {Ω : Type*} (X : ℝ≥0 → Ω → EucConfig d N)
    (s : ℝ) (α : MultiIndex d) : ℝ → Ω → (Fin N × Fin d) → ℝ :=
  fun r z ia => if r ∈ Set.Icc (0 : ℝ) s then Real.sqrt (2 / (N * β)) *
    gradComp ia.2 (propagatorW (critCoeff d a β ρβ) r s (oscTestFun m α)) (X (Real.toNNReal r) z ia.1) else 0

/-- **Interface of the initial and old blocks** (to be produced by S81Q). -/
def S81SOld : Prop :=
  ∀ {d : ℕ}, 2 ≤ d → ∀ (a β : ℝ), 0 < a → 0 < β → ∀ (m : ℝ), (wholeSpaceIndex d : ℝ) ≤ m →
    ∀ T : ℝ, 0 < T →
    ∃ (e : ℕ → Euc d → ℝ) (om : ℕ → ℝ) (b : ℝ),
      IsSpectralData d β (thermalDensity d ((d : ℝ) / 2) a β) e om ∧
      S81W2Coef d a β (thermalDensity d ((d : ℝ) / 2) a β) e om m ∧ 0 ≤ b ∧
      ∃ (C c u0 : ℝ), 0 < c ∧ b ≤ u0 ∧ ∀ N : ℕ, 2 ≤ N →
        ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
          IsCanonicalRealization d ((d : ℝ) / 2) a β N P X₀ W X →
          ∀ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
            IsCylindricalBrownian P ℱ (fun t z (ia : Fin N × Fin d) => W t z ia.1 ia.2) →
            IsWholeFilteredSolution P ℱ W' W X →
          ∀ u : ℝ, u0 ≤ u →
          ∃ (Ω₁ : Type) (mΩ₁ : MeasurableSpace Ω₁) (Q₁ : Measure Ω₁) (_ : IsProbabilityMeasure Q₁)
            (π₁ : Ω₁ → Ω) (ℱ₁ : Filtration ℝ mΩ₁) (W₁ : ℝ≥0 → Ω₁ → (Fin N × Fin d) → ℝ),
            MeasurePreserving π₁ Q₁ P ∧ (∀ t, (ℱ t).comap π₁ ≤ ℱ₁ t) ∧
            IsCylindricalBrownian Q₁ ℱ₁ (fun t z (ia : Fin N × Fin d) => W t (π₁ z) ia.1 ia.2) ∧
            IsWholeFilteredSolution Q₁ ℱ₁ W₁ (fun t z => W t (π₁ z)) (fun t z => X t (π₁ z)) ∧
            ∃ (Ip Op G0 G1 : ℝ → Ω₁ → OscDual d m)
              (S0 S1 : ∀ (p : ℕ), (Fin p → ℝ) → (Fin p → MultiIndex d) → Matrix (Fin p) (Fin p) ℝ)
              (ε₀ ε₁ : ℝ≥0∞),
              S81PProc Q₁ T Ip ∧ S81PProc Q₁ T Op ∧ S81PProc Q₁ T G0 ∧ S81PProc Q₁ T G1 ∧
              (∀ t, @Measurable Ω₁ (OscDual d m) (ℱ₁ (u - b)) _ (G0 t)) ∧
              (∀ t, @Measurable Ω₁ (OscDual d m) (ℱ₁ (u - b)) _ (G1 t)) ∧
              IndepFun (fun ζ (t : ℝ) => G0 t ζ) (fun ζ (t : ℝ) => G1 t ζ) Q₁ ∧
              (∀ (p : ℕ) (ts : Fin p → ℝ) (αs : Fin p → MultiIndex d), (∀ c, ts c ∈ Set.Icc (0 : ℝ) T) →
                (S0 p ts αs).PosSemidef ∧ (S1 p ts αs).PosSemidef ∧
                Q₁.map (s81p_vec G0 ts αs) = multivariateGaussian 0 (S0 p ts αs) ∧
                Q₁.map (s81p_vec G1 ts αs) = multivariateGaussian 0 (S1 p ts αs) ∧
                S0 p ts αs + S1 p ts αs = Matrix.of fun i j =>
                  s81w2_Q d β (thermalDensity d ((d : ℝ) / 2) a β) e om m (αs i) (αs j)
                    (2 * b + ts i + ts j)) ∧
              s81p_L2 Q₁ (fun ζ => processWindow m T 0 Ip ζ - processWindow m T 0 G0 ζ) ≤ ε₀ ∧
              s81p_L2 Q₁ (fun ζ => processWindow m T 0 Op ζ - processWindow m T 0 G1 ζ) ≤ ε₁ ∧
              ε₀ + ε₁ ≤ ENNReal.ofReal (C * (Real.exp (-c * u) + (N : ℝ) ^ (-(1 / 2 : ℝ)))) ∧
              (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ α : MultiIndex d, ∀ ζ : Ω₁,
                OscDual.coord (Ip t ζ) α = Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical (X₀ (π₁ ζ)))
                    (propagatorW (critCoeff d a β (thermalDensity d ((d : ℝ) / 2) a β)) 0 (u + t)
                      (oscTestFun m α)) -
                  ∫ x, propagatorW (critCoeff d a β (thermalDensity d ((d : ℝ) / 2) a β)) 0 (u + t)
                    (oscTestFun m α) x ∂(HRS.Whole.firstMarginal (law P X₀)))) ∧
              (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ α : MultiIndex d, ∀ᵐ ζ ∂Q₁,
                OscDual.coord (Op t ζ) α = itoIntegral Q₁ ℱ₁
                  (fun t z (ia : Fin N × Fin d) => W t (π₁ z) ia.1 ia.2)
                  (s81s_kernel d N a β m (thermalDensity d ((d : ℝ) / 2) a β)
                    (fun t z => X t (π₁ z)) (u + t) α) (u - b) ζ)

section Forcing

variable {d : ℕ}

/-- The supremum of the norms of a continuous-on-`[0,T]` process over a dense sequence of times bounds its window norm. -/
theorem s81s_sup_dense {m T : ℝ} (hT : 0 < T) {Ω : Type*} (Y : ℝ → Ω → OscDual d m) (ζ : Ω)
    (hc : ContinuousOn (fun t => Y t ζ) (Set.Icc 0 T)) (s : ℕ → Set.Icc (0 : ℝ) T) (hs : DenseRange s) :
    ‖processWindow m T 0 Y ζ‖ₑ ≤ ⨆ n : ℕ, ‖Y (s n) ζ‖ₑ := by
  set L : ℝ≥0∞ := ⨆ n : ℕ, ‖Y (s n) ζ‖ₑ with hL
  refine (s81s_window_enorm_le (m := m) (T := T) Y ζ hc).trans (iSup_le fun t => ?_)
  have hcont : Continuous fun t : Set.Icc (0 : ℝ) T => Y t ζ :=
    continuousOn_iff_continuous_domRestrict.1 hc
  have hclosed : IsClosed {t : Set.Icc (0 : ℝ) T | ‖Y t ζ‖ₑ ≤ L} :=
    isClosed_le (continuous_enorm.comp hcont) continuous_const
  exact hs.induction_on t hclosed (fun n => le_iSup (fun n : ℕ => ‖Y (s n) ζ‖ₑ) n)

/-- The centered forcing on the original space: Duhamel identity, measurability and the `L²` bound along any sequence of times. -/
theorem s81s_forcing_P (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (m : ℝ)
    (hm : (wholeSpaceIndex d : ℝ) ≤ m) (T : ℝ) (hT : 0 < T) {ρβ : Euc d → ℝ}
    (hρβ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hR : IsCanonicalRealization d ((d : ℝ) / 2) a β N P X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsWholeFilteredSolution P ℱ W' W X)
    {u : ℝ} (hu : 0 ≤ u) {CF : ℝ}
    (hbound : (∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) T, l2NormE (fun α : MultiIndex d =>
        ∫ r in Set.Icc (0 : ℝ) (u + t), (Real.sqrt N / 2) * (commForcing (critCoeff d a β ρβ) ((d : ℝ) / 2) m
            (HRS.Whole.withDensityReal ρβ) X α (u + t) r ζ -
          ∫ ζ', commForcing (critCoeff d a β ρβ) ((d : ℝ) / 2) m (HRS.Whole.withDensityReal ρβ) X α
            (u + t) r ζ' ∂P))) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (CF * (N : ℝ) ^ (-(1 / 2 : ℝ)))) :
    ∃ Fz : ℝ → Ω → OscDual d m, (∀ t, Measurable (Fz t)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ α : MultiIndex d,
        ∀ᵐ ζ ∂P, OscDual.coord (zetaB m (P.map (X (Real.toNNReal (u + t)))) (X (Real.toNNReal (u + t)) ζ)) α =
          Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical (X 0 ζ))
              (propagatorW (critCoeff d a β ρβ) 0 (u + t) (oscTestFun m α)) -
            ∫ x, propagatorW (critCoeff d a β ρβ) 0 (u + t) (oscTestFun m α) x
              ∂(HRS.Whole.firstMarginal (law P (X 0)))) +
          itoIntegral P ℱ W' (s81s_kernel d N a β m ρβ X (u + t) α) (u + t) ζ -
          OscDual.coord (Fz t ζ) α) ∧
      ∀ s : ℕ → Set.Icc (0 : ℝ) T, (∫⁻ ζ, (⨆ n : ℕ, ‖Fz (s n) ζ‖ₑ) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (CF * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨Fz, hFzm, hFz⟩ := s81s_duhamel hd ha hβ m hm T hT hρβ hN P X₀ W X hR ℱ W' hF hu
  refine ⟨Fz, hFzm, fun t ht α => (hFz t ht α).2, fun s => ?_⟩
  refine le_trans (ENNReal.rpow_le_rpow (lintegral_mono_ae ?_) (by norm_num)) hbound
  have h1 : ∀ n : ℕ, ∀ᵐ ζ ∂P, ∀ α : MultiIndex d, OscDual.coord (Fz (s n) ζ) α = ∫ r in Set.Icc (0 : ℝ) (u + (s n : ℝ)),
      (Real.sqrt N / 2) * (commForcing (critCoeff d a β ρβ) ((d : ℝ) / 2) m
          (HRS.Whole.withDensityReal ρβ) X α (u + (s n : ℝ)) r ζ -
        ∫ ζ', commForcing (critCoeff d a β ρβ) ((d : ℝ) / 2) m (HRS.Whole.withDensityReal ρβ) X α
          (u + (s n : ℝ)) r ζ' ∂P) := fun n => by
    rw [ae_all_iff]
    exact fun α => (hFz (s n) (s n).2 α).1
  have h2 : ∀ᵐ ζ ∂P, ∀ n : ℕ, ∀ α : MultiIndex d, OscDual.coord (Fz (s n) ζ) α = ∫ r in Set.Icc (0 : ℝ) (u + (s n : ℝ)),
      (Real.sqrt N / 2) * (commForcing (critCoeff d a β ρβ) ((d : ℝ) / 2) m
          (HRS.Whole.withDensityReal ρβ) X α (u + (s n : ℝ)) r ζ -
        ∫ ζ', commForcing (critCoeff d a β ρβ) ((d : ℝ) / 2) m (HRS.Whole.withDensityReal ρβ) X α
          (u + (s n : ℝ)) r ζ' ∂P) := ae_all_iff.2 h1
  filter_upwards [h2] with ζ hζ
  refine pow_le_pow_left' (iSup_le fun n => ?_) 2
  rw [HRS.MS.GenPath.s56_enorm_eq_l2NormE, show (fun α => OscDual.coord (Fz (s n) ζ) α) = _ from funext (hζ n)]
  exact le_iSup (fun t : Set.Icc (0 : ℝ) T => l2NormE (fun α : MultiIndex d =>
    ∫ r in Set.Icc (0 : ℝ) (u + t), (Real.sqrt N / 2) * (commForcing (critCoeff d a β ρβ) ((d : ℝ) / 2) m
        (HRS.Whole.withDensityReal ρβ) X α (u + t) r ζ -
      ∫ ζ', commForcing (critCoeff d a β ρβ) ((d : ℝ) / 2) m (HRS.Whole.withDensityReal ρβ) X α
        (u + t) r ζ' ∂P))) (s n)

/-- The Duhamel kernel is a progressive `L²` integrand. -/
theorem s81s_kernel_prog (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (m : ℝ)
    (hm : (wholeSpaceIndex d : ℝ) ≤ m) {ρβ : Euc d → ℝ}
    (hρβ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsWholeFilteredSolution P ℱ W' W X)
    {s : ℝ} (hs : 0 ≤ s) (α : MultiIndex d) :
    IsProgressiveL2 P ℱ (s81s_kernel d N a β m ρβ X s α) := by
  classical
  have hL : 0 < s + 1 := by linarith
  have hs1 : s ∈ Set.Icc (0 : ℝ) (s + 1) := ⟨hs, by linarith⟩
  obtain ⟨θ, Λ, K, C, S, hbv, -, -, -, hScoeff, -, -⟩ := s81s_setup hd ha hβ hρβ hm hL
  have hcl := HRS.MS.GenPath.s56_osc_classical (s81s_bounds d a β m (s + 1) θ Λ K C) hbv S N hs1 α
  have hcl' : IsClassicalAdjointW (critCoeff d a β ρβ) s (oscTestFun m α)
      (fun r => propagatorW (critCoeff d a β ρβ) r s (oscTestFun m α)) := by
    rw [← hScoeff N]; exact hcl
  have hprog := HRS.MH.DualityRd.isProgressiveL2_truncGrad_proof (P := P) hs hcl'.isC12TestRd hF.progressive
  set c0 : ℝ := Real.sqrt (2 / (N * β)) with hc0
  have e : s81s_kernel d N a β m ρβ X s α = fun r z => c0 • HRS.MH.DualityRd.truncGradIntegrand s
      (fun r => propagatorW (critCoeff d a β ρβ) r s (oscTestFun m α)) X r z := by
    funext r z ia
    by_cases hr : r ∈ Set.Icc (0 : ℝ) s
    · simp only [s81s_kernel, HRS.MH.DualityRd.truncGradIntegrand, if_pos hr, Pi.smul_apply, smul_eq_mul, hc0]
    · simp only [s81s_kernel, HRS.MH.DualityRd.truncGradIntegrand, if_neg hr, Pi.smul_apply, smul_eq_mul, mul_zero]
  rw [e]; exact hprog.smul c0

end Forcing

section Main

variable {d : ℕ}

theorem s81s_W0_coord {N : ℕ} {Ω : Type} (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) :
    (fun t z (ia : Fin N × Fin d) => s81s_W0 d N W' t z ia.1 ia.2) = W' := rfl

/-- Pull back of the `L²` size of a function of a measure-preserving map. -/
theorem s81s_L2_comp_fn {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    {Q : Measure Ω'} {π : Ω' → Ω} (hπ : MeasurePreserving π Q P) {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (f : Ω → E) (hf : AEMeasurable f P) :
    s81p_L2 Q (fun ζ => f (π ζ)) = s81p_L2 P f := by
  unfold s81p_L2
  congr 1
  have hae : AEMeasurable (fun ζ => ENNReal.ofReal (‖f ζ‖ ^ (2 : ℝ))) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hf.norm.pow_const (2 : ℝ))
  have hae' : AEMeasurable (fun ζ => ENNReal.ofReal (‖f ζ‖ ^ (2 : ℝ))) (Measure.map π Q) := by
    rw [hπ.map_eq]; exact hae
  have := lintegral_map' hae' (hπ.aemeasurable)
  rw [hπ.map_eq] at this
  exact this.symm

theorem s81s_meas_comap_proc {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₂] (𝒜 : MeasurableSpace Ω₁) (π : Ω₂ → Ω₁)
    {m : ℝ} (Y : ℝ → Ω₁ → OscDual d m) (hY : ∀ t, @Measurable Ω₁ (OscDual d m) 𝒜 _ (Y t)) :
    @Measurable Ω₂ (ℝ → OscDual d m) (𝒜.comap π) _ (fun ζ (t : ℝ) => Y t (π ζ)) := by
  refine @measurable_pi_lambda Ω₂ ℝ (fun _ => OscDual d m) (𝒜.comap π) _ _ (fun t => ?_)
  exact @Measurable.comp Ω₂ Ω₁ (OscDual d m) (𝒜.comap π) 𝒜 _ (Y t) π (hY t) (comap_measurable π)


/-- **The glue.**  `S81PBlocks` follows from the initial/old interface and `weighted_critical_forcing`. -/
theorem s81s_blocks (hOld : S81SOld) (hforce : type_of% @HRS.Whole.weighted_critical_forcing) :
    S81PBlocks := by
  classical
  intro d hd a β ha hβ m hm T hT
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) < (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < d := by linarith
  have hρth : IsThermalEquilibrium d ((d : ℝ) / 2) a β (thermalDensity d ((d : ℝ) / 2) a β) :=
    HRS.Whole.S71.s71_thermal_equilibrium hd hs0 hsd a β ha hβ
  obtain ⟨e, om, b, hdata, hcoef, hb, C, c, u0, hc, hbu0, hOldN⟩ := hOld hd a β ha hβ m hm T hT
  obtain ⟨CR, hCR⟩ := s81s_recent_block hd a β ha hβ m hm T b hT hb
  obtain ⟨CF, hCF⟩ := hforce hd a β ha hβ m hm T hT
  refine ⟨e, om, hdata, hcoef, max C 0 + max CR 0 + max CF 0, c, u0, hc, hb.trans hbu0, ?_⟩
  intro N hN Ω _ P _ X₀ W X hR u hu
  have hN1 : 1 ≤ N := by omega
  have hu0 : 0 ≤ u := (hb.trans hbu0).trans hu
  have hbu : b ≤ u := hbu0.trans hu
  obtain ⟨ℱ, W', hF⟩ := hR.filtered
  obtain ⟨hR0, hF0⟩ := s81s_canonical_W0 hR ℱ W' hF
  have hcyl : IsCylindricalBrownian P ℱ (fun t z (ia : Fin N × Fin d) => s81s_W0 d N W' t z ia.1 ia.2) := by
    rw [s81s_W0_coord]; exact HRS.GF.gfb3_isCylindricalBrownian_of_filtration hF.brownian
  obtain ⟨Ω₁, mΩ₁, Q₁, hQ₁, π₁, ℱ₁, W₁, hπ₁, hfil₁, hcyl₁, hF₁, Ip, Op, G0, G1, S0, S1, ε₀, ε₁, hIp, hOp,
    hG0, hG1, hm0, hm1, hind01, hS01, hb0, hb1, hεs, hIpc, hOpc⟩ :=
    hOldN N hN P X₀ (s81s_W0 d N W') X hR0 ℱ W' hcyl hF0 u hu
  haveI := hQ₁
  have hR1 := s81s_canonical_comp hπ₁ hR0 ℱ₁ W₁ hF₁
  obtain ⟨M, hM, Ω₂, mΩ₂, Q₂, hQ₂, π₂, Rp, G2, hπ₂, hRpdef, hRp, hG2, hind2, hfdd2, hL2R⟩ :=
    hCR (thermalDensity d ((d : ℝ) / 2) a β) hρth N hN Q₁ (fun z => X₀ (π₁ z))
      (fun t z => s81s_W0 d N W' t (π₁ z)) (fun t z => X t (π₁ z)) hR1 ℱ₁ W₁ hcyl₁ hF₁ (u - b).toNNReal
  haveI := hQ₂
  set h : ℝ≥0 := (u - b).toNNReal with hhdef
  have hh : (h : ℝ) = u - b := Real.coe_toNNReal _ (by linarith)
  have hπF : MeasurePreserving (fun ζ => π₁ (π₂ ζ)) Q₂ P := hπ₁.comp hπ₂
  have hmd : (d : ℝ) < m := by
    have : ((wholeSpaceIndex d : ℕ) : ℝ) = 24 * d + 240 := by unfold wholeSpaceIndex; push_cast; ring
    linarith
  -- the processes on the final space
  set Ip' : ℝ → Ω₂ → OscDual d m := fun t ζ => Ip t (π₂ ζ) with hIp'def
  set Op' : ℝ → Ω₂ → OscDual d m := fun t ζ => Op t (π₂ ζ) with hOp'def
  set G0' : ℝ → Ω₂ → OscDual d m := fun t ζ => G0 t (π₂ ζ) with hG0'def
  set G1' : ℝ → Ω₂ → OscDual d m := fun t ζ => G1 t (π₂ ζ) with hG1'def
  set A : ℝ → Ω₂ → OscDual d m := fun t ζ => zetaB m (P.map (X (Real.toNNReal (u + t))))
    (X (Real.toNNReal (u + t)) (π₁ (π₂ ζ))) with hAdef
  set Fp : ℝ → Ω₂ → OscDual d m := fun t ζ => Ip' t ζ + Op' t ζ + Rp t ζ - A t ζ with hFpdef
  have hIp' : S81PProc Q₂ T Ip' := s81s_proc_comp hπ₂ hIp
  have hOp' : S81PProc Q₂ T Op' := s81s_proc_comp hπ₂ hOp
  have hG0' : S81PProc Q₂ T G0' := s81s_proc_comp hπ₂ hG0
  have hG1' : S81PProc Q₂ T G1' := s81s_proc_comp hπ₂ hG1
  have hA : S81PProc Q₂ T A := s81s_proc_comp hπF (s81s_zeta_proc hd m hmd hN1 T u hu0 hR)
  have hFp : S81PProc Q₂ T Fp := ((hIp'.add hOp').add hRp).sub hA
  -- the Duhamel decomposition of the window
  have hduh : ∀ᵐ ζ ∂Q₂, zetaPathW m T u P X (π₁ (π₂ ζ)) = processWindow m T 0 Ip' ζ +
      processWindow m T 0 Op' ζ + processWindow m T 0 Rp ζ - processWindow m T 0 Fp ζ := by
    filter_upwards [hIp'.2, hOp'.2, hRp.2, hA.2] with ζ h1 h2 h3 h4
    have e1 : zetaPathW m T u P X (π₁ (π₂ ζ)) = processWindow m T 0 A ζ := by
      unfold zetaPathW processWindow
      refine HRS.Whole.S79.s79p_windowPathOf_congr T u 0 _ _ (fun t ht => ?_)
      simp only [hAdef, zero_add]
    have e2 : processWindow m T 0 Fp ζ = processWindow m T 0 Ip' ζ + processWindow m T 0 Op' ζ +
        processWindow m T 0 Rp ζ - processWindow m T 0 A ζ := by
      unfold processWindow
      simp only [hFpdef]
      rw [s81p_win_sub (f := fun t => Ip' t ζ + Op' t ζ + Rp t ζ) (g := fun t => A t ζ)
        ((h1.add h2).add h3) h4, s81p_win_add (f := fun t => Ip' t ζ + Op' t ζ) (g := fun t => Rp t ζ)
        (h1.add h2) h3, s81p_win_add (f := fun t => Ip' t ζ) (g := fun t => Op' t ζ) h1 h2]
    rw [e1, e2]
    abel
  -- independence of the three blocks
  set G2' : ℝ → Ω₂ → OscDual d m := G2 with hG2'
  set Gs : Fin 3 → ℝ → Ω₂ → OscDual d m := ![G0', G1', G2] with hGsdef
  have hGs : ∀ i, S81PProc Q₂ T (Gs i) := by
    intro i; fin_cases i
    · exact hG0'
    · exact hG1'
    · exact hG2
  have h𝒢 : (ℱ₁ (h : ℝ)).comap π₂ ≤ mΩ₂ :=
    (MeasurableSpace.comap_mono (ℱ₁.le _)).trans hπ₂.measurable.comap_le
  have hG0m : Measurable (fun ζ (t : ℝ) => G0 t ζ) := measurable_pi_iff.2 hG0.1
  have hG1m : Measurable (fun ζ (t : ℝ) => G1 t ζ) := measurable_pi_iff.2 hG1.1
  have hindep : iIndepFun (fun (i : Fin 3) (ζ : Ω₂) (t : ℝ) => Gs i t ζ) Q₂ := by
    refine s81s_iIndep3 ((ℱ₁ (h : ℝ)).comap π₂) (fun (i : Fin 3) (ζ : Ω₂) (t : ℝ) => Gs i t ζ) h𝒢 ?_ ?_
      (measurable_pi_iff.2 hG2.1) ?_ ?_
    · have := s81s_meas_comap_proc (ℱ₁ (h : ℝ)) π₂ G0 (by rw [hh]; exact hm0)
      exact this
    · have := s81s_meas_comap_proc (ℱ₁ (h : ℝ)) π₂ G1 (by rw [hh]; exact hm1)
      exact this
    · exact s81s_indepFun_comp hπ₂ hG0m hG1m hind01
    · have e := s81s_comap_proc G2
      show Indep _ (MeasurableSpace.comap (fun ζ (t : ℝ) => G2 t ζ) inferInstance) Q₂
      rw [e]; exact hind2
  -- finite-dimensional laws and covariances
  set S2 : ∀ (p : ℕ), (Fin p → ℝ) → (Fin p → MultiIndex d) → Matrix (Fin p) (Fin p) ℝ :=
    fun p ts αs => Matrix.of fun i j => noiseCovW (critCoeff d a β (thermalDensity d ((d : ℝ) / 2) a β))
      β⁻¹ (b + ts i) (b + ts j) (oscTestFun m (αs i)) (oscTestFun m (αs j)) with hS2
  set Ss : Fin 3 → ∀ (p : ℕ), (Fin p → ℝ) → (Fin p → MultiIndex d) → Matrix (Fin p) (Fin p) ℝ :=
    ![S0, S1, S2] with hSs
  have hpsd : ∀ (i : Fin 3) (p : ℕ) (ts : Fin p → ℝ) (αs : Fin p → MultiIndex d),
      (∀ c, ts c ∈ Set.Icc (0 : ℝ) T) → (Ss i p ts αs).PosSemidef := by
    intro i p ts αs hts
    fin_cases i
    · exact (hS01 p ts αs hts).1
    · exact (hS01 p ts αs hts).2.1
    · exact (hfdd2 p ts αs hts).1
  have hlaw : ∀ (i : Fin 3) (p : ℕ) (ts : Fin p → ℝ) (αs : Fin p → MultiIndex d),
      (∀ c, ts c ∈ Set.Icc (0 : ℝ) T) →
      Q₂.map (s81p_vec (Gs i) ts αs) = multivariateGaussian 0 (Ss i p ts αs) := by
    intro i p ts αs hts
    fin_cases i
    · have h1 := (hS01 p ts αs hts).2.2.1
      have h2 := s81s_map_comp hπ₂ (s81p_vec_meas hG0.1 ts αs)
      exact h2.trans h1
    · have h1 := (hS01 p ts αs hts).2.2.2.1
      have h2 := s81s_map_comp hπ₂ (s81p_vec_meas hG1.1 ts αs)
      exact h2.trans h1
    · exact (hfdd2 p ts αs hts).2
  have hsum : ∀ (p : ℕ) (ts : Fin p → ℝ) (αs : Fin p → MultiIndex d), (∀ c, ts c ∈ Set.Icc (0 : ℝ) T) →
      Ss 0 p ts αs + Ss 1 p ts αs + Ss 2 p ts αs =
        s81p_Qmat d β (thermalDensity d ((d : ℝ) / 2) a β) e om m ts αs := by
    intro p ts αs hts
    ext i j
    have h01 := congrFun (congrFun (hS01 p ts αs hts).2.2.2.2 i) j
    have hn := s81w2_noiseCov_spectral hd ha hβ hρth hm hdata hcoef (αs i) (αs j)
      (t := b + ts i) (t' := b + ts j) (by linarith [(hts i).1]) (by linarith [(hts j).1])
    have e1 : |(b + ts i) - (b + ts j)| = |ts i - ts j| := by congr 1; ring
    have e2 : (b + ts i) + (b + ts j) = 2 * b + ts i + ts j := by ring
    rw [e1, e2] at hn
    have g : (Ss 0 p ts αs + Ss 1 p ts αs + Ss 2 p ts αs) i j = S0 p ts αs i j + S1 p ts αs i j +
        noiseCovW (critCoeff d a β (thermalDensity d ((d : ℝ) / 2) a β)) β⁻¹ (b + ts i) (b + ts j)
          (oscTestFun m (αs i)) (oscTestFun m (αs j)) := rfl
    rw [g]
    have h01' : S0 p ts αs i j + S1 p ts αs i j =
        s81w2_Q d β (thermalDensity d ((d : ℝ) / 2) a β) e om m (αs i) (αs j) (2 * b + ts i + ts j) := by
      simpa only [Matrix.add_apply, Matrix.of_apply] using h01
    show _ = s81w2_Q d β (thermalDensity d ((d : ℝ) / 2) a β) e om m (αs i) (αs j) |ts i - ts j|
    linarith
  -- the recent block: Hilbert-Schmidt integrand and physical identification
  obtain ⟨Cin, hCin⟩ := s81s_linear_input hd ha hβ
  obtain ⟨Crec, hCrec⟩ := s81s_finite_noise hd a β ha hβ m hm (b + T) (by linarith) Cin
  have hR1h := HRS.Whole.BreakdownS81.s81b_isCanonical_shift hR1 h
  have hWh := s81s_cyl_shift_vec hcyl₁ h
  have hFh := HRS.Whole.BreakdownS81.s81b_filtered_shift hF₁ h
  have hprog : ∀ i : Fin N, IsProgressive (HRS.Whole.BreakdownS81.s81b_shiftFil ℱ₁ h)
      (fun r z => HRS.Whole.S79.s79p_shiftX h (fun t z => X t (π₁ z)) (Real.toNNReal r) z i) :=
    fun i => s81s_prog_coord hFh.progressive i
  have hlin : ∀ t ∈ Set.Icc (0 : ℝ) (b + T), LinearInputBounds d ((d : ℝ) / 2) N
      (HRS.Whole.withDensityReal (thermalDensity d ((d : ℝ) / 2) a β)) Cin Q₁
      (HRS.Whole.S79.s79p_shiftX h (fun t z => X t (π₁ z)) (Real.toNNReal t)) :=
    fun t _ => hCin _ hρth N hN Q₁ _ _ _ hR1h (Real.toNNReal t)
  obtain ⟨hHS, -⟩ := hCrec _ hρth N hN Q₁ (fun z => X h (π₁ z))
    (HRS.Whole.S79.s79p_shiftW h (fun t z => s81s_W0 d N W' t (π₁ z)))
    (HRS.Whole.S79.s79p_shiftX h (fun t z => X t (π₁ z))) hR1h
    (HRS.Whole.BreakdownS81.s81b_shiftFil ℱ₁ h) hWh hprog hlin
  have hphys := fun t (ht : t ∈ Set.Icc (0 : ℝ) T) (α : MultiIndex d) =>
    s81s_recent_phys hd ha hβ m hm T b hT hb hρth hN Q₁ (fun t z => s81s_W0 d N W' t (π₁ z))
      (fun t z => X t (π₁ z)) ℱ₁ W₁ hcyl₁ hF₁ h M hHS hM t ht α
  -- transport of the Itô integrals to the original space
  have hπ₁m : ∀ t, @Measurable Ω₁ Ω (ℱ₁ t) (ℱ t) π₁ := fun t => (measurable_iff_comap_le).2 (hfil₁ t)
  have hWbQ : IsBrownianFiltration Q₁ ℱ₁ (fun t z (k : Fin N × Fin d) => W' t (π₁ z) k) :=
    s81s_brownian_of_cyl hcyl₁
  have hcomp : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ α : MultiIndex d, ∀ᵐ ζ' ∂Q₁, ∀ s : ℝ,
      itoIntegral Q₁ ℱ₁ (fun t z (ia : Fin N × Fin d) => s81s_W0 d N W' t (π₁ z) ia.1 ia.2)
        (s81s_kernel d N a β m (thermalDensity d ((d : ℝ) / 2) a β) (fun t z => X t (π₁ z)) (u + t) α) s ζ' =
      itoIntegral P ℱ W' (s81s_kernel d N a β m (thermalDensity d ((d : ℝ) / 2) a β) X (u + t) α) s (π₁ ζ') :=
    fun t ht α => itoIntegral_comp_π hπ₁m hπ₁ hF.brownian hWbQ
      (s81s_kernel_prog hd ha hβ m hm hρth hN P W X ℱ W' hF (show 0 ≤ u + t by linarith [ht.1]) α)
  -- the forcing
  obtain ⟨-, -, -, hCFb⟩ := hCF _ hρth N hN P X₀ W X hR
  obtain ⟨Fz, hFzm, hFzid, hFzL2⟩ := s81s_forcing_P hd ha hβ m hm T hT hρth hN P X₀ (s81s_W0 d N W') X hR0
    ℱ W' hF0 hu0 (hCFb u hu0)
  have hX0 : ∀ᵐ ζ ∂P, X 0 ζ = X₀ ζ := (hR.solution 0).init
  have hlaw0 : law P (X 0) = law P X₀ := Measure.map_congr hX0
  have hneg : ∀ (x : OscDual d m) (α' : MultiIndex d), OscDual.coord (-x) α' = - OscDual.coord x α' := fun x α' => by
    rw [← neg_one_smul ℝ x, OscDual.coord_smul]; ring
  have hFid : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ α : MultiIndex d, ∀ᵐ ζ ∂Q₂,
      OscDual.coord (Fp t ζ) α = OscDual.coord (Fz t (π₁ (π₂ ζ))) α := by
    intro t ht α
    have ht0 : min t T = t := min_eq_left ht.2
    have ht1 : max 0 t = t := max_eq_right ht.1
    have hhe : (h : ℝ) + (b + t) = u + t := by rw [hh]; ring
    have f2 := hπ₂.quasiMeasurePreserving.ae (hOpc t ht α)
    have f3 := hπ₂.quasiMeasurePreserving.ae (hphys t ht α)
    have f5 := hπ₂.quasiMeasurePreserving.ae (hcomp t ht α)
    have f6 := hπF.quasiMeasurePreserving.ae (hFzid t ht α)
    have f7 := hπF.quasiMeasurePreserving.ae hX0
    filter_upwards [f2, f3, f5, f6, f7] with ζ g2 g3 g5 g6 g7
    have g1 := hIpc t ht α (π₂ ζ)
    have gR : OscDual.coord (Rp t ζ) α = OscDual.coord (reconstructPath m (b + T) M (π₂ ζ) (b + t)) α := by
      rw [hRpdef t ζ, ht0, ht1]; rfl
    have g3' : OscDual.coord (reconstructPath m (b + T) M (π₂ ζ) (b + t)) α =
        itoIntegral Q₁ ℱ₁ (fun t z (ia : Fin N × Fin d) => s81s_W0 d N W' t (π₁ z) ia.1 ia.2)
          (s81s_kernel d N a β m (thermalDensity d ((d : ℝ) / 2) a β) (fun t z => X t (π₁ z)) (u + t) α)
          (u + t) (π₂ ζ) -
        itoIntegral Q₁ ℱ₁ (fun t z (ia : Fin N × Fin d) => s81s_W0 d N W' t (π₁ z) ia.1 ia.2)
          (s81s_kernel d N a β m (thermalDensity d ((d : ℝ) / 2) a β) (fun t z => X t (π₁ z)) (u + t) α)
          (u - b) (π₂ ζ) := by
      rw [← hh, ← hhe]; exact g3
    have gF : OscDual.coord (Fp t ζ) α = OscDual.coord (Ip t (π₂ ζ)) α + OscDual.coord (Op t (π₂ ζ)) α +
        OscDual.coord (Rp t ζ) α - OscDual.coord (A t ζ) α := by
      show OscDual.coord (Ip' t ζ + Op' t ζ + Rp t ζ - A t ζ) α = _
      rw [sub_eq_add_neg, OscDual.coord_add, OscDual.coord_add, OscDual.coord_add, hneg]
      ring
    have gA : OscDual.coord (A t ζ) α = _ := g6
    rw [hlaw0, g7] at gA
    have g5' := g5 (u + t)
    rw [gF, gR, g3', g1, g2, gA, ← g5']
    ring
  haveI : Nonempty (Set.Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT.le⟩⟩
  obtain ⟨s, hs⟩ := TopologicalSpace.exists_dense_seq (Set.Icc (0 : ℝ) T)
  have hFseq : ∀ᵐ ζ ∂Q₂, ∀ n : ℕ, ‖Fp (s n) ζ‖ₑ = ‖Fz (s n) (π₁ (π₂ ζ))‖ₑ := by
    refine ae_all_iff.2 fun n => ?_
    filter_upwards [ae_all_iff.2 (hFid (s n) (s n).2)] with ζ hζ
    rw [HRS.MS.GenPath.s56_enorm_eq_l2NormE, HRS.MS.GenPath.s56_enorm_eq_l2NormE]
    congr 1
    funext α
    exact hζ α
  have hbF : s81p_L2 Q₂ (fun ζ => processWindow m T 0 Fp ζ) ≤
      ENNReal.ofReal (CF * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
    refine le_trans ?_ (hFzL2 s)
    rw [s81p_L2_eq]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    have hg : Measurable (fun ζ => (⨆ n : ℕ, ‖Fz (s n) ζ‖ₑ) ^ 2) :=
      (Measurable.iSup fun n => (hFzm _).enorm).pow_const 2
    rw [← hπF.lintegral_comp hg]
    refine lintegral_mono_ae ?_
    filter_upwards [hFp.2, hFseq] with ζ hc hq
    have h1 := s81s_sup_dense hT Fp ζ hc s hs
    rw [show (⨆ n : ℕ, ‖Fp (s n) ζ‖ₑ) = ⨆ n : ℕ, ‖Fz (s n) (π₁ (π₂ ζ))‖ₑ from iSup_congr hq] at h1
    calc ‖processWindow m T 0 Fp ζ‖ₑ ^ (2 : ℝ) ≤ (⨆ n : ℕ, ‖Fz (s n) (π₁ (π₂ ζ))‖ₑ) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow h1 (by norm_num)
      _ = (⨆ n : ℕ, ‖Fz (s n) (π₁ (π₂ ζ))‖ₑ) ^ 2 := ENNReal.rpow_two _
  -- the L² bounds
  have hf0 : AEMeasurable (fun ζ => processWindow m T 0 Ip ζ - processWindow m T 0 G0 ζ) Q₁ :=
    (hIp.aemeasurable hT.le).sub (hG0.aemeasurable hT.le)
  have hf1 : AEMeasurable (fun ζ => processWindow m T 0 Op ζ - processWindow m T 0 G1 ζ) Q₁ :=
    (hOp.aemeasurable hT.le).sub (hG1.aemeasurable hT.le)
  have hb0' : s81p_L2 Q₂ (fun ζ => processWindow m T 0 Ip' ζ - processWindow m T 0 G0' ζ) ≤ ε₀ :=
    le_trans (le_of_eq (s81s_L2_comp_fn hπ₂ _ hf0)) hb0
  have hb1' : s81p_L2 Q₂ (fun ζ => processWindow m T 0 Op' ζ - processWindow m T 0 G1' ζ) ≤ ε₁ :=
    le_trans (le_of_eq (s81s_L2_comp_fn hπ₂ _ hf1)) hb1
  have hE0 : 0 ≤ Real.exp (-c * u) := (Real.exp_pos _).le
  have hN0 : 0 ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have htot : ε₀ + ε₁ + ENNReal.ofReal (CR * (N : ℝ) ^ (-(1 / 2 : ℝ))) +
      ENNReal.ofReal (CF * (N : ℝ) ^ (-(1 / 2 : ℝ))) ≤ ENNReal.ofReal ((max C 0 + max CR 0 + max CF 0) *
        (Real.exp (-c * u) + (N : ℝ) ^ (-(1 / 2 : ℝ)))) := by
    have hE : 0 ≤ Real.exp (-c * u) + (N : ℝ) ^ (-(1 / 2 : ℝ)) := add_nonneg hE0 hN0
    have hnE : (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Real.exp (-c * u) + (N : ℝ) ^ (-(1 / 2 : ℝ)) :=
      le_add_of_nonneg_left hE0
    have a1 : ε₀ + ε₁ ≤ ENNReal.ofReal (max C 0 * (Real.exp (-c * u) + (N : ℝ) ^ (-(1 / 2 : ℝ)))) :=
      hεs.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hE))
    have a2 : ENNReal.ofReal (CR * (N : ℝ) ^ (-(1 / 2 : ℝ))) ≤
        ENNReal.ofReal (max CR 0 * (Real.exp (-c * u) + (N : ℝ) ^ (-(1 / 2 : ℝ)))) :=
      ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_right (le_max_left _ _) hN0).trans
        (mul_le_mul_of_nonneg_left hnE (le_max_right _ _)))
    have a3 : ENNReal.ofReal (CF * (N : ℝ) ^ (-(1 / 2 : ℝ))) ≤
        ENNReal.ofReal (max CF 0 * (Real.exp (-c * u) + (N : ℝ) ^ (-(1 / 2 : ℝ)))) :=
      ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_right (le_max_left _ _) hN0).trans
        (mul_le_mul_of_nonneg_left hnE (le_max_right _ _)))
    refine (add_le_add (add_le_add a1 a2) a3).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_add (mul_nonneg (le_max_right _ _) hE) (mul_nonneg (le_max_right _ _) hE),
      ← ENNReal.ofReal_add (add_nonneg (mul_nonneg (le_max_right _ _) hE) (mul_nonneg (le_max_right _ _) hE))
        (mul_nonneg (le_max_right _ _) hE)]
    congr 1
    ring
  refine ⟨Ω₂, mΩ₂, Q₂, hQ₂, fun ζ => π₁ (π₂ ζ), hπF, Ip', Op', Rp, Fp, Gs, Ss, ε₀, ε₁,
    ENNReal.ofReal (CR * (N : ℝ) ^ (-(1 / 2 : ℝ))), ENNReal.ofReal (CF * (N : ℝ) ^ (-(1 / 2 : ℝ))),
    hIp', hOp', hRp, hFp, hGs, hduh, hindep, hpsd, hlaw, hsum, hb0', hb1', hL2R, hbF, htot⟩

end Main

end HRS.Whole.S81S
