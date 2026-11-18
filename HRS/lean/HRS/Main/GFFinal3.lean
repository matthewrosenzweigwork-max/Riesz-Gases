import HRS.Main.GFFinal2

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS.Uniform

variable {d : ℕ}

set_option maxHeartbeats 1600000 in
/-- **`gff_core`: the three estimates of Theorem 2.1 from the sub-packet statements** (PROVED, conditional on the sorried packets).
Parametrised by the matrix `M`, an extra hypothesis `Hyp` on the setup, the level `μ S ∈ {γ, γ+2}`, the embedding `embedY` of the
initial datum into `E_{μ S}`, and an evolution provider `hev` (`gf_ev_grad_proof` resp. `gf_ev_mat_proof`). -/
theorem gff_core (b : GeneralBounds d) (M : Matrix (Fin d) (Fin d) ℝ) (Hyp : GeneralSetup d → Prop)
    (μ : GeneralSetup d → ℝ) (hμ : ∀ S : GeneralSetup d, (S.γ : ℝ) ≤ μ S)
    (embedY : ∀ S : GeneralSetup d, NegSobolev d (S.γ : ℝ) → NegSobolev d (μ S)) (K : ℝ)
    (hev : ∀ S : GeneralSetup d, S.Within { b with C₀ := S.C₀ } → S.MFHypM M → Hyp S → ∀ N : ℕ,
      ∃ EV : EvolData (NegSobolev d (S.γ : ℝ)) (NegSobolev d (μ S)),
        GFEvo S M N (μ S) K EV ∧ ∀ x, EV.j x = embedY S x) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHypM M → Hyp S →
      ∀ (N : ℕ) (_ : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P]
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
      (X : ℝ≥0 → Ω → Config d N) (_ : IsStrongSolution P (S.dynM M N) S.T X₀ W X)
      (_ : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
        (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X)
      (_ : S.EnergyMomentFinite P N X)
      (η₀ : Ω → NegSobolev d (S.γ : ℝ)) (_ : Measurable η₀)
      (_ : ProbabilityTheory.IndepFun (fun ω => (X₀ ω, η₀ ω)) (fun ω => fun t => W t ω) P)
      (_ : S.InitialErrorFinite P N 1 X₀ η₀)
      (Y : ℝ → Ω → NegSobolev d (μ S))
      (_ : IsLinearFluctuationSolution P (S.dynM M N) (S.ρ N) (μ S) (qN S N) S.T
        (fun ω => AN S N • embedY S (η₀ ω)) Y),
      smoothDist 2 (law P (flucPath (μ S) S.T (sigN S N) X (S.ρ N))) (law P (toPath (μ S) S.T Y)) ≤
          C * (AN S N * S.initialError P N 1 X₀ η₀ + sigN S N * S.energyMoment P N X +
            qN S N * (Real.sqrt (S.energyMoment P N X) + (N : ℝ) ^ (-(2 : ℝ) / d))) ∧
      wassersteinE 1 (law P (flucPath (μ S) S.T (sigN S N) X (S.ρ N))) (law P (toPath (μ S) S.T Y)) ≤
        ENNReal.ofReal (C * (AN S N * S.initialError P N 1 X₀ η₀ + sigN S N * S.energyMoment P N X +
            Real.sqrt (qN S N) * (S.energyMoment P N X ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d)))) ∧
      (S.EnergyMoment2Finite P N X →
        Integrable (fun ω => ‖flucPath (μ S) S.T (sigN S N) X (S.ρ N) ω‖ ^ 2) P →
        S.InitialErrorFinite P N 2 X₀ η₀ →
        wassersteinE 2 (law P (flucPath (μ S) S.T (sigN S N) X (S.ρ N))) (law P (toPath (μ S) S.T Y)) ≤
          ENNReal.ofReal (C * (AN S N * S.initialError P N 2 X₀ η₀ +
            sigN S N * S.energyMoment2 P N X +
            Real.sqrt (qN S N) * (S.energyMoment P N X ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d))))) := by
  obtain ⟨C₀a, hs1⟩ := gff_stage1 b M K
  obtain ⟨C₀b, htr⟩ := gf_trace_moment_proof' b M
  refine ⟨max C₀a C₀b, fun C₀ hC₀ => ?_⟩
  by_cases hex : ∃ S₀ : GeneralSetup d, S₀.Within { b with C₀ := C₀ }
  swap
  · exact ⟨1, one_pos, fun S hS => absurd ⟨S, hS⟩ hex⟩
  obtain ⟨S₀, hS₀⟩ := hex
  have hbT : 0 ≤ b.T := by rw [← hS₀.2.1]; exact S₀.hT.le
  obtain ⟨Cr, hCr, hs1'⟩ := hs1 C₀ (le_trans (le_max_left _ _) hC₀)
  obtain ⟨Cte, hCte, hte⟩ := htr C₀ (le_trans (le_max_right _ _) hC₀)
  obtain ⟨C2, hC20, hs2⟩ := gff_stage2 b.T K hbT
  set C : ℝ := C2 + Cr * b.T + C2 * Cte + C2 * Real.sqrt Cte + 1 with hCdef
  have hCpos : 0 < C := by
    have : 0 ≤ C2 + Cr * b.T + C2 * Cte + C2 * Real.sqrt Cte := by positivity
    linarith
  refine ⟨C, hCpos, ?_⟩
  intro S hS hMF hHyp N hN Ω mΩ P _ X₀ W X hX hF hE η₀ hη hind hfin1 Y hY
  have hST : S.T = b.T := hS.2.1
  have hT' : 0 ≤ S.T := S.hT.le
  have hSw : S.Within { b with C₀ := S.C₀ } := by
    have hC : S.C₀ = C₀ := hS.2.2.2.2.2.1
    rw [hC]; exact hS
  obtain ⟨EV, hEV, hj⟩ := hev S hSw hMF hHyp N
  have hm := hμ S
  have hembY : Measurable (embedY S) := by
    have : embedY S = EV.j := funext fun x => (hj x).symm
    rw [this]; exact EV.j.continuous.measurable
  set Y₀ : Ω → NegSobolev d (μ S) := fun ω => AN S N • embedY S (η₀ ω) with hY₀def
  have hY₀m : Measurable Y₀ := (hembY.comp hη).const_smul (AN S N)
  have hY₀ : ∀ ω, Y₀ ω = EV.j (AN S N • η₀ ω) := fun ω => by
    simp only [hY₀def]
    rw [map_smul, hj]
  obtain ⟨Ω₁, mΩ₁, P₁, hP₁, π₁, hπ₁, ℱ₁, η', Mart, Z, Bm, hS1, hX₁, hF₁, hE₁, hEeq, hlaw, hinit, hBm1, hBm2⟩ :=
    hs1' S hS hMF N hN (μ S) hm EV hEV P X₀ W X hX hF hE η₀ hη hind Y₀ hY₀m hY₀ Y hY
  set X₁ : ℝ≥0 → Ω₁ → Config d N := fun t ω => X t (π₁ ω) with hX₁def
  have hq0 := qN_nonneg S N
  have hσ0 := sigN_nonneg S N
  have hA0 := AN_nonneg S N
  have hE0 := gff_energyMoment_nonneg S M hMF N hN P X₀ W X hX hF hE
  have hε1 := initialError_nonneg S P 1 X₀ η₀
  have hn0 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / d) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hn2 := rpow_neg_two_div d N (by omega)
  -- the trace-norm coupling and the comparison estimates on the first enlargement
  set Sg : ℝ → Ω₁ → (NegSobolev d (S.γ : ℝ) →L[ℝ] NegSobolev d (S.γ : ℝ) →L[ℝ] ℝ) :=
    fun r ω => covForm (S.γ : ℝ) (qN S N) (empirical (X₁ (Real.toNNReal r) ω)) with hSg
  set Cb := covDensT (S.γ : ℝ) (qN S N) S.T (S.ρ N) with hCb
  have hcpl := gff_adapted_coupling_trace P₁ ℱ₁ S.T hT' ⟨ℱ₁ 0, le_rfl⟩ Mart Sg hS1.mart Cb hS1.det
  have hcostm : AEMeasurable (fun ω => ∫⁻ r in Set.Icc (0 : ℝ) S.T,
      ENNReal.ofReal (traceNormForm (Sg r ω - Cb r))) P₁ :=
    (measurable_trace_integral hS1.mart hS1.det).aemeasurable
  obtain ⟨hsm, hW⟩ := hs2 S hST M hMF N hN (μ S) hm EV hEV P P₁ ℱ₁ X₁ η' Mart Z Bm Y₀ Y hS1
    (fun r ω => traceNormForm (Sg r ω - Cb r)) hcpl hcostm
  rw [hlaw] at hsm hW
  -- the covariance-error moment
  have hte' := hte S hS hMF N hN P₁ (fun ω => X₀ (π₁ ω)) (fun t ω => W t (π₁ ω)) X₁ hX₁ hF₁ hE₁
  rw [hEeq] at hte'
  have hconvc : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T,
      ENNReal.ofReal (traceNormForm (Sg r ω - Cb r))) ∂P₁ =
      ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (traceNormForm
        (covForm (S.γ : ℝ) (qN S N) (empirical (X₁ (Real.toNNReal r) ω)) -
          covForm (S.γ : ℝ) (qN S N) (withDensityReal (S.ρ N r))))) ∂P₁ := by
    refine lintegral_congr fun ω => ?_
    refine setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    simp only [hSg, hCb, covDensT, if_pos hr]
  have hinit1 : ∫⁻ ω, ‖flucProc (S.γ : ℝ) (sigN S N) X₁ (S.ρ N) 0 ω - AN S N • η' ω‖ₑ ∂P₁ =
      ENNReal.ofReal (AN S N * S.initialError P N 1 X₀ η₀) := by
    have := hinit 1 (Or.inl rfl) hfin1
    simpa using this
  have hcostB : (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (traceNormForm (Sg r ω - Cb r))) ∂P₁) ≤
      ENNReal.ofReal (Cte * qN S N * (Real.sqrt (S.energyMoment P N X) + (N : ℝ) ^ (-(2 : ℝ) / d))) := by
    rw [hconvc]; exact hte'
  refine ⟨?_, ?_, ?_⟩
  · -- the smooth estimate
    have hfin : ENNReal.ofReal (smoothDist 2 (law P (flucPath (μ S) S.T (sigN S N) X (S.ρ N)))
        (law P (toPath (μ S) S.T Y))) ≤ ENNReal.ofReal (C * (AN S N * S.initialError P N 1 X₀ η₀ +
          sigN S N * S.energyMoment P N X +
          qN S N * (Real.sqrt (S.energyMoment P N X) + (N : ℝ) ^ (-(2 : ℝ) / d)))) := by
      refine hsm.trans ?_
      rw [hinit1]
      have h3 : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (traceNormForm
          (covForm (S.γ : ℝ) (qN S N) (empirical (X₁ (Real.toNNReal r) ω)) -
            covForm (S.γ : ℝ) (qN S N) (withDensityReal (S.ρ N r))))) ∂P₁ ≤
          ENNReal.ofReal (Cte * qN S N * (Real.sqrt (S.energyMoment P N X) + (N : ℝ) ^ (-(2 : ℝ) / d))) := hte'
      have hz : 0 ≤ qN S N * (Real.sqrt (S.energyMoment P N X) + (N : ℝ) ^ (-(2 : ℝ) / d)) :=
        mul_nonneg hq0 (add_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg N) _))
      have hx : 0 ≤ AN S N * S.initialError P N 1 X₀ η₀ := mul_nonneg hA0 hε1
      have hy : 0 ≤ sigN S N * S.energyMoment P N X := mul_nonneg hσ0 hE0
      calc _ ≤ ENNReal.ofReal C2 * ENNReal.ofReal (AN S N * S.initialError P N 1 X₀ η₀) +
            ENNReal.ofReal (Cr * sigN S N * (b.T * S.energyMoment P N X)) +
            ENNReal.ofReal C2 * ENNReal.ofReal (Cte * qN S N *
              (Real.sqrt (S.energyMoment P N X) + (N : ℝ) ^ (-(2 : ℝ) / d))) := by
            gcongr
            · rw [← hST]; exact hBm1
        _ = ENNReal.ofReal (C2 * (AN S N * S.initialError P N 1 X₀ η₀) +
            (Cr * S.T) * (sigN S N * S.energyMoment P N X) +
            (C2 * Cte) * (qN S N * (Real.sqrt (S.energyMoment P N X) + (N : ℝ) ^ (-(2 : ℝ) / d)))) := by
            rw [← ENNReal.ofReal_mul hC20, ← ENNReal.ofReal_mul hC20, ← ENNReal.ofReal_add (by positivity)
              (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1
            rw [hST]
            ring
        _ ≤ _ := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [hST]
            have hsq := mul_nonneg hC20 (Real.sqrt_nonneg Cte)
            have hp1 := mul_nonneg hCr.le hbT
            have hp2 := mul_nonneg hC20 hCte.le
            have hCa : C2 ≤ C := by rw [hCdef]; linarith
            have hCb' : Cr * b.T ≤ C := by rw [hCdef]; linarith
            have hCc : C2 * Cte ≤ C := by rw [hCdef]; linarith
            exact lin3 hx hy hz hCa hCb' hCc
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hfin
  · -- the `W₁` estimate
    have hW1 := hW 1 (Or.inl rfl)
    have hinitp := hinit 1 (Or.inl rfl) hfin1
    have hB1 : (∫⁻ ω, Bm ω ^ (1 : ℝ) ∂P₁) ^ (1 / (1 : ℝ)) ≤
        ENNReal.ofReal (Cr * sigN S N * (S.T * S.energyMoment P N X)) := by
      simpa using hBm1
    have hcost' : (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T,
        ENNReal.ofReal (traceNormForm (Sg r ω - Cb r))) ∂P₁) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (Real.sqrt Cte * Real.sqrt (qN S N) *
          (S.energyMoment P N X ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d))) := by
      calc _ ≤ (ENNReal.ofReal (Cte * qN S N * (Real.sqrt (S.energyMoment P N X) +
              (N : ℝ) ^ (-(2 : ℝ) / d)))) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hcostB (by norm_num)
        _ = ENNReal.ofReal (Real.sqrt (Cte * qN S N * (Real.sqrt (S.energyMoment P N X) +
              (N : ℝ) ^ (-(1 : ℝ) / d) * (N : ℝ) ^ (-(1 : ℝ) / d)))) := by
            rw [← hn2, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
              show (1 / 2 : ℝ) = (1 : ℝ) / 2 from rfl, ← Real.sqrt_eq_rpow]
        _ ≤ _ := ENNReal.ofReal_le_ofReal (sqrt_cost_bound hCte.le hq0 hE0 hn0)
    have hx : 0 ≤ AN S N * S.initialError P N 1 X₀ η₀ := mul_nonneg hA0 hε1
    have hy : 0 ≤ sigN S N * S.energyMoment P N X := mul_nonneg hσ0 hE0
    have hz : 0 ≤ Real.sqrt (qN S N) * (S.energyMoment P N X ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d)) :=
      mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (Real.rpow_nonneg hE0 _) hn0)
    calc _ ≤ ENNReal.ofReal C2 * ENNReal.ofReal (AN S N * S.initialError P N 1 X₀ η₀) +
          ENNReal.ofReal (Cr * sigN S N * (S.T * S.energyMoment P N X)) +
          ENNReal.ofReal C2 * ENNReal.ofReal (Real.sqrt Cte * Real.sqrt (qN S N) *
            (S.energyMoment P N X ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d))) := by
          refine hW1.trans ?_
          rw [hinitp]
          gcongr
      _ = ENNReal.ofReal (C2 * (AN S N * S.initialError P N 1 X₀ η₀) +
          (Cr * S.T) * (sigN S N * S.energyMoment P N X) +
          (C2 * Real.sqrt Cte) * (Real.sqrt (qN S N) *
            (S.energyMoment P N X ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d)))) := by
          rw [← ENNReal.ofReal_mul hC20, ← ENNReal.ofReal_mul hC20, ← ENNReal.ofReal_add (by positivity)
            (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          rw [hST]
          ring
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hST]
          have hsq := mul_nonneg hC20 (Real.sqrt_nonneg Cte)
          have hp1 := mul_nonneg hCr.le hbT
          have hp2 := mul_nonneg hC20 hCte.le
          have hCa : C2 ≤ C := by rw [hCdef]; linarith
          have hCb' : Cr * b.T ≤ C := by rw [hCdef]; linarith
          have hCc : C2 * Real.sqrt Cte ≤ C := by rw [hCdef]; linarith
          exact lin3 hx hy hz hCa hCb' hCc
  · -- the `W₂` estimate
    intro hE2 _ hfin2
    have hW2 := hW 2 (Or.inr rfl)
    have hinitp := hinit 2 (Or.inr rfl) hfin2
    have hB2 := hBm2 hE2
    have hE20 : 0 ≤ S.energyMoment2 P N X := by
      unfold GeneralSetup.energyMoment2
      exact Real.iSup_nonneg fun t => Real.sqrt_nonneg _
    have hε2 := initialError_nonneg S P 2 X₀ η₀
    have hcost' : (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T,
        ENNReal.ofReal (traceNormForm (Sg r ω - Cb r))) ∂P₁) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (Real.sqrt Cte * Real.sqrt (qN S N) *
          (S.energyMoment P N X ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d))) := by
      calc _ ≤ (ENNReal.ofReal (Cte * qN S N * (Real.sqrt (S.energyMoment P N X) +
              (N : ℝ) ^ (-(2 : ℝ) / d)))) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hcostB (by norm_num)
        _ = ENNReal.ofReal (Real.sqrt (Cte * qN S N * (Real.sqrt (S.energyMoment P N X) +
              (N : ℝ) ^ (-(1 : ℝ) / d) * (N : ℝ) ^ (-(1 : ℝ) / d)))) := by
            rw [← hn2, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
              show (1 / 2 : ℝ) = (1 : ℝ) / 2 from rfl, ← Real.sqrt_eq_rpow]
        _ ≤ _ := ENNReal.ofReal_le_ofReal (sqrt_cost_bound hCte.le hq0 hE0 hn0)
    have hx : 0 ≤ AN S N * S.initialError P N 2 X₀ η₀ := mul_nonneg hA0 hε2
    have hy : 0 ≤ sigN S N * S.energyMoment2 P N X := mul_nonneg hσ0 hE20
    have hz : 0 ≤ Real.sqrt (qN S N) * (S.energyMoment P N X ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d)) :=
      mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (Real.rpow_nonneg hE0 _) hn0)
    calc _ ≤ ENNReal.ofReal C2 * ENNReal.ofReal (AN S N * S.initialError P N 2 X₀ η₀) +
          ENNReal.ofReal (Cr * sigN S N * (S.T * S.energyMoment2 P N X)) +
          ENNReal.ofReal C2 * ENNReal.ofReal (Real.sqrt Cte * Real.sqrt (qN S N) *
            (S.energyMoment P N X ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d))) := by
          refine hW2.trans ?_
          rw [hinitp]
          gcongr
      _ = ENNReal.ofReal (C2 * (AN S N * S.initialError P N 2 X₀ η₀) +
          (Cr * S.T) * (sigN S N * S.energyMoment2 P N X) +
          (C2 * Real.sqrt Cte) * (Real.sqrt (qN S N) *
            (S.energyMoment P N X ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d)))) := by
          rw [← ENNReal.ofReal_mul hC20, ← ENNReal.ofReal_mul hC20, ← ENNReal.ofReal_add (by positivity)
            (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          rw [hST]
          ring
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hST]
          have hsq := mul_nonneg hC20 (Real.sqrt_nonneg Cte)
          have hp1 := mul_nonneg hCr.le hbT
          have hp2 := mul_nonneg hC20 hCte.le
          have hCa : C2 ≤ C := by rw [hCdef]; linarith
          have hCb' : Cr * b.T ≤ C := by rw [hCdef]; linarith
          have hCc : C2 * Real.sqrt Cte ≤ C := by rw [hCdef]; linarith
          exact lin3 hx hy hz hCa hCb' hCc

end HRS.GF
