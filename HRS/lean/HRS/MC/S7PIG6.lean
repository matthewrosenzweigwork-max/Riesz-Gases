import HRS.MC.S7PIG6A
import HRS.MC.S7PIM1
import HRS.MC.S7PIM2
import HRS.MC.S7PIM3
import HRS.MC.S7PIG2
import HRS.MC.S7PIG4
import HRS.MC.S7PIG5
import HRS.MC.S7PIS2RS
import HRS.MC.S7FCW12B

/-!
# Packet piG6 (PI-G6): removal of the projection (`s7_PI_G_remove_projection_proof`)

Statement copied verbatim from `HRS/MC/S7PIPlan.lean` (`HRS.MC.Sec7.PIPlan.s7_PI_G_remove_projection`); the tie is in
`HRS/MC/S7PIG6Tie.lean`.  Route (see the docstring of the Plan statement): fix the a.s. event on which `ℬ_N ∈ L¹`, `η_N` is
bounded and measurable and the `IsRS` clauses of `hF L` hold for every `L`; there `s7_PIG_RS_drift` and `s7_PIG_RS_J`
(G4, G5; with `Jc` of G2) give limits `I, I'` of the Riemann-Stieltjes integrals of the projected sums, uniformly dominated;
by the uniqueness of Riemann-Stieltjes limits `A_L = I_L`, `J_L = I'_L`.  Then `A := lim A_L`, `J := lim J_L` are integrable,
`∫ A_L → ∫ A`, `∫ J_L → ∫ J` (dominated convergence), and the identity of `hF L` passes to the limit.

The hypothesis `∀ u, IsProbabilityMeasure (γ u)` needed by G4, G5 is arranged by replacing `γ` outside `[0,T]` by `δ_0`
(`S7PIG6_concl_congr`): `PathItoConcl` only sees `γ_u` for `u ∈ [0,T]`.
Namespace `HRS.MC.Sec7.S7PIG6`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIG6

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

section ProbG

variable (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
  (γ : ℝ → Measure (PathSpace d m T)) (hγ : ∀ u ∈ Set.Icc (0 : ℝ) T, IsFutureGaussian R.D R.ρ m T u (γ u))
  (N : ℕ) (hN : 1 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
  (hreal : PreparedRealization R.D P
    (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X)
  (Pj : ℕ → (PathSpace d m T →L[ℝ] PathSpace d m T))
  (hPj : ∀ L w, Pj L w = projPoly m T hT.le L w) (hP1 : ∀ L, ‖Pj L‖ ≤ 1)
  (hconv : ∀ w, Tendsto (fun L => Pj L w) atTop (𝓝 w))
  (hTconv : ∀ (j : ℕ) (v : TensorDual (PathSpace d m T) j), v ∈ projTensor (PathSpace d m T) j →
    Tendsto (fun L => tensorPow j (Pj L) v) atTop (𝓝 v))

include hm hT hγ hN hreal hPj hP1 hconv hTconv

/-- the core of G6, with the extra hypothesis `γ_u` probability for all `u` -/
theorem S7PIG6_core (hγp : ∀ u, IsProbabilityMeasure (γ u)) (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ)
    (hF : ∀ L, PathItoConcl R m T γ N P X Φ (Pj L)) :
    PathItoConcl R m T γ N P X Φ (ContinuousLinearMap.id ℝ (PathSpace d m T)) := by
  classical
  have hS := hreal.solution T
  obtain ⟨hB1, hBm, hBint⟩ := HRS.MC.Sec7.S7PIM.s7_PIM_B_integrable_proof R m hm T hT N hN P X₀ W X hreal
  obtain ⟨M, hM⟩ := HRS.MC.Sec7.S7PIM.s7_PIM_eta_bdd_proof R m hm T hT N hN P X₀ W X hreal
  obtain ⟨-, hzW⟩ := HRS.MC.Sec7.S7PIM.s7_PIM_zeta_path_proof R m hm T hT N hN P X₀ W X hreal
  obtain ⟨CJ, hCJ⟩ := HRS.MC.Sec7.S7PIG1.s7_PIG_J_measure_proof R m hm T hT
  obtain ⟨C4, hC4⟩ := HRS.MC.Sec7.S7PIG4.s7_PIG_RS_drift_proof R m hm T hT γ hγ hγp Pj hPj hP1 hconv
  unfold PathItoConcl at hF
  choose A J hA hJ hAR hJR hid using hF
  -- the drift part
  have hCb : Integrable (fun ω => C4 * cbNorm 5 Φ *
      ∫ u in Set.Ioc 0 T, ‖quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X u ω‖) P := by
    have : (fun ω => C4 * cbNorm 5 Φ *
        ∫ u in Set.Ioc 0 T, ‖quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X u ω‖) =
        fun ω => (C4 * cbNorm 5 Φ) *
          ∫ u in Set.Icc (0 : ℝ) T, ‖quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X u ω‖ := by
      funext ω
      rw [setIntegral_congr_set Ioc_ae_eq_Icc]
    rw [this]
    exact hBint.const_mul _
  have hAae : ∀ᵐ ω ∂P, ∃ I, IsRS T (fun τ a b =>
      fderiv ℝ (heatFn γ Φ τ) (predicted R.D R.ρ (zetaWin m T 0 P X ω) τ)
        (driftInc R.D R.ρ m T
          (fun u => quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X u ω) a b)) I ∧
      Tendsto (fun L => A L ω) atTop (𝓝 I) ∧ ∀ L, |A L ω| ≤ C4 * cbNorm 5 Φ *
        ∫ u in Set.Ioc 0 T, ‖quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X u ω‖ := by
    filter_upwards [hB1, ae_all_iff.2 hAR] with ω hb hR
    obtain ⟨I, hI, -, IL, hIL, hILb, hlim⟩ := hC4 Φ hΦ (zetaWin m T 0 P X ω) _ hb
    have hAeq : ∀ L, A L ω = IL L := fun L =>
      HRS.MC.Sec7.S7PIS2.S7PIS2_RS_unique T hT _ _ _ (hR L) (hIL L)
    refine ⟨I, hI, ?_, fun L => ?_⟩
    · simpa only [hAeq] using hlim
    · rw [hAeq]; exact hILb L
  obtain ⟨hAint, hAlim, hAtend⟩ := S7PIG6_lim (P := P) A (fun L => (hA L).aestronglyMeasurable) _ hCb
    (hAae.mono fun ω h => by obtain ⟨I, -, h1, h2⟩ := h; exact ⟨⟨I, h1⟩, h2⟩)
  -- the covariance part
  have hJae : ∀ᵐ ω ∂P, ∃ I, IsRS T (fun τ a b =>
      jPair R.D R.ρ m T (fun u => etaE m (X u.toNNReal ω) (withDensityReal (R.ρ u))) (Set.Ioc a b)
        (iteratedFDeriv ℝ 2 (heatFn γ Φ τ) (predicted R.D R.ρ (zetaWin m T 0 P X ω) τ))) I ∧
      Tendsto (fun L => J L ω) atTop (𝓝 I) ∧ ∀ L, |J L ω| ≤ cbNorm 5 Φ * (CJ * M * T) := by
    filter_upwards [hM, ae_all_iff.2 hJR] with ω hz hR
    obtain ⟨zr, hzr, hzM, hzeq⟩ := hz
    obtain ⟨Jc, hJc0, hJc⟩ := hCJ zr hzr M hzM
    have hjp : ∀ I : Set ℝ, jPair R.D R.ρ m T
        (fun u => etaE m (X u.toNNReal ω) (withDensityReal (R.ρ u))) I =
        jPair R.D R.ρ m T (fun u => NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k)) I :=
      fun I => S7PIG6_jPair_congr R.D R.ρ m T hzeq I
    obtain ⟨I, hI, -, IL, hIL, hILb, hlim⟩ := HRS.MC.Sec7.S7PIG5.s7_PIG_RS_J_proof R m hm T hT γ hγ hγp Pj
      hPj hP1 hconv hTconv hΦ (zetaWin m T 0 P X ω)
      (fun u => NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k)) Jc (CJ * M) hJc0
      (fun a b ha hab hb => (hJc a b ha hab hb).1) (fun a b ha hab hb => (hJc a b ha hab hb).2.1)
    have hAeq : ∀ L, J L ω = IL L := fun L => by
      refine HRS.MC.Sec7.S7PIS2.S7PIS2_RS_unique T hT _ _ _ ?_ (hIL L)
      refine S7PIG6_IsRS_congr (hR L) fun τ a b _ _ _ _ => ?_
      simp only [hjp]
    refine ⟨I, ?_, ?_, fun L => ?_⟩
    · refine S7PIG6_IsRS_congr hI fun τ a b _ _ _ _ => ?_
      simp only [hjp]
    · simpa only [hAeq] using hlim
    · rw [hAeq]; exact hILb L
  obtain ⟨hJint, hJlim, hJtend⟩ := S7PIG6_lim (P := P) J (fun L => (hJ L).aestronglyMeasurable) _
    (integrable_const (cbNorm 5 Φ * (CJ * M * T)))
    (hJae.mono fun ω h => by obtain ⟨I, -, h1, h2⟩ := h; exact ⟨⟨I, h1⟩, h2⟩)
  -- the identity: boundedness of `Φ`
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ x, |Φ x| ≤ K := by
    obtain ⟨K, hK⟩ := hΦ.2 0 (Nat.zero_le _)
    refine ⟨K, fun x => ?_⟩
    have := hK ⟨x, rfl⟩
    simpa [norm_iteratedFDeriv_zero] using this
  have hΦc : Continuous Φ := hΦ.1.continuous
  have hL1 : Tendsto (fun L => ∫ ω, Φ (Pj L (zetaWin m T 0 P X ω)) ∂P) atTop
      (𝓝 (∫ ω, Φ (zetaWin m T 0 P X ω) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => K) (fun L => ?_) (integrable_const K)
      (fun L => Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => ?_)
    · exact ((hΦc.comp (Pj L).continuous).measurable.comp_aemeasurable hzW).aestronglyMeasurable
    · simpa using hK _
    · exact (hΦc.tendsto _).comp (hconv _)
  have hy : Measurable fun ω => initProp R.D R.ρ m T (zetaAt m P X 0 ω) :=
    (S7PIG6_initProp_cont R m hm T hT).measurable.comp
      (HRS.MC.Sec7.S7FCW12.s7fcw12_zetaAt_measurable m P X hS.adapted hN 0)
  have hF1 : Tendsto (fun L => ∫ ω, heatFn γ (fun w => Φ (Pj L w)) 0
      (initProp R.D R.ρ m T (zetaAt m P X 0 ω)) ∂P) atTop
      (𝓝 (∫ ω, heatFn γ Φ 0 (initProp R.D R.ρ m T (zetaAt m P X 0 ω)) ∂P)) := by
    have := hγp 0
    have hcL : ∀ L, Continuous (heatFn γ (fun w => Φ (Pj L w)) 0) := fun L =>
      S7PIG6_heat_cont (γ 0) (hΦc.comp (Pj L).continuous) K (fun x => hK _)
    refine tendsto_integral_of_dominated_convergence (fun _ => K) (fun L => ?_) (integrable_const K)
      (fun L => Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => ?_)
    · exact ((hcL L).measurable.comp hy).aestronglyMeasurable
    · have := norm_integral_le_of_norm_le_const (μ := γ 0)
        (f := fun z => Φ (Pj L (initProp R.D R.ρ m T (zetaAt m P X 0 ω) + z))) (C := K)
        (Eventually.of_forall fun z => by simpa using hK _)
      simpa [heatFn] using this
    · unfold heatFn
      refine tendsto_integral_of_dominated_convergence (fun _ => K) (fun L => ?_) (integrable_const K)
        (fun L => Eventually.of_forall fun z => ?_) (Eventually.of_forall fun z => ?_)
      · exact (hΦc.comp ((Pj L).continuous.comp (continuous_const.add continuous_id))).aestronglyMeasurable
      · simpa using hK _
      · exact (hΦc.tendsto _).comp (hconv _)
  refine ⟨fun ω => limUnder atTop (fun L => A L ω), fun ω => limUnder atTop (fun L => J L ω),
    hAint, hJint, ?_, ?_, ?_⟩
  · filter_upwards [hAae, hAlim] with ω h ht'
    obtain ⟨I, hI, ht, -⟩ := h
    rw [tendsto_nhds_unique ht' ht]
    exact hI
  · filter_upwards [hJae, hJlim] with ω h ht'
    obtain ⟨I, hI, ht, -⟩ := h
    rw [tendsto_nhds_unique ht' ht]
    exact hI
  · have hfin : Tendsto (fun L => ∫ ω, Φ (Pj L (zetaWin m T 0 P X ω)) ∂P) atTop
        (𝓝 (∫ ω, heatFn γ Φ 0 (initProp R.D R.ρ m T (zetaAt m P X 0 ω)) ∂P -
          (Real.sqrt N)⁻¹ * ∫ ω, limUnder atTop (fun L => A L ω) ∂P +
          (1 / (2 * Real.sqrt N)) * ∫ ω, limUnder atTop (fun L => J L ω) ∂P)) := by
      have heq : (fun L => ∫ ω, Φ (Pj L (zetaWin m T 0 P X ω)) ∂P) = fun L =>
          ∫ ω, heatFn γ (fun w => Φ (Pj L w)) 0 (initProp R.D R.ρ m T (zetaAt m P X 0 ω)) ∂P -
            (Real.sqrt N)⁻¹ * ∫ ω, A L ω ∂P + (1 / (2 * Real.sqrt N)) * ∫ ω, J L ω ∂P := funext hid
      rw [heq]
      exact (hF1.sub (hAtend.const_mul _)).add (hJtend.const_mul _)
    simpa using tendsto_nhds_unique hL1 hfin

theorem s7_PI_G_remove_projection_proof (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ)
    (hF : ∀ L, PathItoConcl R m T γ N P X Φ (Pj L)) :
    PathItoConcl R m T γ N P X Φ (ContinuousLinearMap.id ℝ (PathSpace d m T)) := by
  classical
  -- replace `γ` outside `[0,T]` by `δ_0`, so that all `γ'_u` are probability measures
  set γ' : ℝ → Measure (PathSpace d m T) := fun u => if u ∈ Set.Icc (0 : ℝ) T then γ u else Measure.dirac 0
    with hγ'def
  have hγγ' : ∀ u ∈ Set.Icc (0 : ℝ) T, γ u = γ' u := fun u hu => by
    show γ u = if u ∈ Set.Icc (0 : ℝ) T then γ u else Measure.dirac 0
    rw [if_pos hu]
  have hγ'p : ∀ u, IsProbabilityMeasure (γ' u) := fun u => by
    by_cases hu : u ∈ Set.Icc (0 : ℝ) T
    · have := (hγ u hu).1.1
      rw [← hγγ' u hu]
      exact this.toIsProbabilityMeasure
    · show IsProbabilityMeasure (if u ∈ Set.Icc (0 : ℝ) T then γ u else Measure.dirac 0)
      rw [if_neg hu]
      infer_instance
  have hγ' : ∀ u ∈ Set.Icc (0 : ℝ) T, IsFutureGaussian R.D R.ρ m T u (γ' u) := fun u hu => by
    rw [← hγγ' u hu]
    exact hγ u hu
  have := S7PIG6_concl_congr R m T N P X hT.le (fun u hu => (hγγ' u hu).symm) Φ
    (ContinuousLinearMap.id ℝ (PathSpace d m T))
    (S7PIG6_core R m hm T hT γ' hγ' N hN P X₀ W X hreal Pj hPj hP1 hconv hTconv hγ'p Φ hΦ
      (fun L => S7PIG6_concl_congr R m T N P X hT.le hγγ' Φ (Pj L) (hF L)))
  exact this

end ProbG

end HRS.MC.Sec7.S7PIG6

end
