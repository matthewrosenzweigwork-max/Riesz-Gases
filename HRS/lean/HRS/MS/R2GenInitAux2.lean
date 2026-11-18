import HRS.MS.R2GenInitAux1

/-!
# S10.5 packet G0': the forcing remainder with the entropy bound `H_b` (`δ_N` replaced by `B_N/N`)

`s105_forcing_expect`: pushforward form of `s105_comm_expect`; `s105_partB`: part (b) of `r2_window_errors` with `δ_N` replaced by
`H_b/N + δ_N` (this is `Lemma 10.4` "with `δ_N` replaced by `B_N/N`", S L8472-8474), from `s104_partB_core`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal NNReal

namespace HRS.MS.R2GenInit

open HRS.Whole HRS.MS.Wr HRS.MS.PrepStat HRS.MS.R2WinErr

variable {d : ℕ}

theorem s105_forcing_expect (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (M L β : ℝ) (hβ : 0 < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      (s = 0 → HasLogMoment (HRS.Whole.withDensityReal ρ) L) → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (Z : Ω → EucConfig d N), Measurable Z → ∀ Hb : ℝ, 0 ≤ Hb →
      HRS.relEntropy (P.map Z) (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
        (HRS.Whole.withDensityReal ρ)) ≤ ENNReal.ofReal Hb →
      ∀ (v : Euc d → Euc d) (Λ : ℝ≥0), LipschitzWith Λ v →
        ∫⁻ ζ, ENNReal.ofReal |commN d s v (Z ζ) (HRS.Whole.withDensityReal ρ)| ∂P ≤
          ENNReal.ofReal (C * Λ * (Hb / N + deltaN d s N)) := by
  obtain ⟨C, hC0, hC⟩ := s105_comm_expect hd s hs0 hsd M L β hβ
  refine ⟨C, hC0, fun ρ hρ hρM hlog N hN Ω _ P _ Z hZ Hb hHb0 hH v Λ hv => ?_⟩
  haveI : IsProbabilityMeasure (P.map Z) := ⟨by rw [Measure.map_apply hZ MeasurableSet.univ]; simp⟩
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := Q34.isProbabilityMeasure_nu hρ
  obtain ⟨hint, hbd⟩ := hC ρ hρ hρM hlog N hN (P.map Z) inferInstance Hb hHb0 hH v Λ hv
  have hcm := HRS.MS.Comm.comm_meas (d := d) (s := s) v hv.continuous.measurable
  have hgm : Measurable (fun X : EucConfig d N => |commN d s v X (HRS.Whole.withDensityReal ρ)|) := by
    have e : (fun X : EucConfig d N => |commN d s v X (HRS.Whole.withDensityReal ρ)|) =
        fun X => |2 * pairEnergy (commutatorKernel d s v) X (HRS.Whole.withDensityReal ρ)| := by
      funext X; rw [s32_commN_eq]
    rw [e]
    exact continuous_abs.measurable.comp ((wr9_measurable_pairEnergy hcm).const_mul 2)
  rw [← lintegral_map (f := fun X : EucConfig d N =>
      ENNReal.ofReal |commN d s v X (HRS.Whole.withDensityReal ρ)|) hgm.ennreal_ofReal hZ,
    ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun X => abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hbd

theorem s105_partB (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (M L β : ℝ) (hβ : 0 < β) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ (C : WholeCoeff d) (ρ : ℝ → Euc d → ℝ) (m T b cdec Cs : ℝ) (k : ℕ), 1 ≤ k →
      0 < cdec → 0 ≤ Cs → 0 ≤ T → 0 ≤ b → ∀ bα : MultiIndex d → ℝ, (∀ α, 0 ≤ bα α) → Summable bα →
      (∀ α, ∀ t : ℝ, 0 ≤ t → R2OrbitGrad C k t (oscTestFun m α) (Cs * bα α) cdec) →
      (∀ α, ∀ t : ℝ, 0 ≤ t → R2OrbitGrad C k t (generatorW C t (oscTestFun m α)) (Cs * bα α) cdec) →
      ∀ N : ℕ, 2 ≤ N → ∀ Hb : ℝ, 0 ≤ Hb → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → EucConfig d N),
      (∀ r ∈ Set.Icc (0 : ℝ) (b + T), HRS.Whole.IsProbDensity (ρ r) ∧ (∀ x, ρ r x ≤ M) ∧
        (s = 0 → HasLogMoment (HRS.Whole.withDensityReal (ρ r)) L)) →
      (∀ r ∈ Set.Icc (0 : ℝ) (b + T), Measurable (X r.toNNReal)) →
      (∀ r ∈ Set.Icc (0 : ℝ) (b + T), HRS.relEntropy (P.map (X r.toNNReal))
        (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal (ρ r))) ≤
          ENNReal.ofReal Hb) →
      (∀ ζ : Ω, ∀ α : MultiIndex d, ∀ r t0 t : ℝ, 0 ≤ r → r ≤ t0 → t0 ≤ t → t ≤ b + T →
        ENNReal.ofReal |r2CommForcingMov C s m ρ X α t r ζ| ≤
          ENNReal.ofReal |r2CommForcingMov C s m ρ X α t0 r ζ| +
            ∫⁻ s' in Set.Ioc t0 t, ENNReal.ofReal |s104_F2 C s m ρ X α (s', r) ζ|) →
      (∀ α, AEMeasurable (fun p : Ω × ℝ => ENNReal.ofReal |r2CommForcingMov C s m ρ X α b p.2 p.1|)
        (P.prod (volume.restrict (Set.Icc (0 : ℝ) b)))) →
      (∀ α, AEMeasurable (fun p : Ω × ℝ => ENNReal.ofReal |r2CommForcingMov C s m ρ X α p.2 p.2 p.1|)
        (P.prod (volume.restrict (Set.Icc b (b + T))))) →
      (∀ α, AEMeasurable (fun p : Ω × (ℝ × ℝ) => ENNReal.ofReal |s104_F2 C s m ρ X α p.2 p.1|)
        (P.prod (volume.restrict ((Set.Icc b (b + T)) ×ˢ (Set.Icc (0 : ℝ) (b + T)))))) →
      ∫⁻ ζ, (⨆ u ∈ Set.Icc (0 : ℝ) T, HRS.Whole.l2NormE (fun α : MultiIndex d =>
          -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) (b + u),
            r2CommForcingMov C s m ρ X α (b + u) r ζ)) ∂P ≤
        ENNReal.ofReal ((Real.sqrt N / 2) * ((Cc * (Hb / N + deltaN d s N)) * Cs) *
          (1 / cdec + T + T * (1 / cdec)) * ∑' α, bα α) := by
  obtain ⟨Cc, hCc0, hCc⟩ := s105_forcing_expect hd s hs0 hsd M L β hβ
  refine ⟨Cc, hCc0, fun C ρ m T b cdec Cs k hk hc hCs hT hb bα hb0 hbS hG hG' N hN Hb hHb Ω _ P _ X
    hρ hXm hH hevol M0 M1 M2 => ?_⟩
  have hδ : 0 ≤ deltaN d s N := HRS.MS.S53.s53_deltaN_nonneg s (by omega)
  have hκ0 : 0 ≤ Cc * (Hb / N + deltaN d s N) := by positivity
  refine s104_partB_core P C ρ m T b cdec Cs (Cc * (Hb / N + deltaN d s N)) k hc hCs hT hb hκ0 bα hb0 hbS
    hG hG' N s X ?_ hevol M0 M1 M2
  intro t ψ A hA hR r hr hrt
  obtain ⟨hprob, hM, hlog⟩ := hρ r hr
  refine (hCc (ρ r) hprob hM hlog N hN P (X r.toNNReal) (hXm r hr) Hb hHb (hH r hr) _ _
    (s104_grad_lip C hk hA hR hrt)).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  show Cc * (A * Real.exp (-cdec * (t - r))) * (Hb / N + deltaN d s N) = _
  ring

end HRS.MS.R2GenInit
