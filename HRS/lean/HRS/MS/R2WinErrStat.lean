import HRS.MS.R2WinErrAux24
import HRS.MS.R2WinOrbAux15

/-!
# S10.4 for the stationary trajectory: `r2_window_errors_stationary`

The statement of `HRS.Whole.r2_window_errors` for the trajectory `ρ = fun _ => ρ_β` (thermal equilibrium), PROVED from `s103_stationary`
(the stationary half of S10.3) and the inputs discharged in `R2WinErrAux17-24`: `hphi` (`s104_hphi`), the class bounds (`s104_hcls_bounds`),
`hobs` (`s104_hobs_stat`) and `hdyn` (`s104_hdyn_stat`).  Only the nonlinear trajectories remain (they need `S6.7` nonlinear and the
nonlinear analogues of the inputs).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinErr

open HRS.Whole HRS.Whole.AppendixA

set_option maxHeartbeats 1600000 in
theorem r2_window_errors_stationary {d : ℕ} (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < d) (a β : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (T : ℝ) (hT : 0 < T) :
    ∃ C₀ : ℝ,
      (∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t →
        ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
          0 ≤ rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ((fun _ : ℝ => ρβ) t)) + HRS.oN d s C₀ N) ∧
      ∀ CB : ℝ, ∃ CT : ℝ,
      ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ N : ℕ, 2 ≤ N →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
          IsR2Realization d s a β P X₀ W X →
          MovParticleBounds d s a β C₀ CB (fun _ => ρβ) N P X →
          (∀ b : ℝ, 0 ≤ b → ∫⁻ ζ, ⨆ t ∈ Set.Icc b (b + T),
            ENNReal.ofReal (movSecondMoment (X t.toNNReal ζ)) ∂P ≤ ENNReal.ofReal CB) →
          ∀ b : ℝ, 0 ≤ b →
            (∃ Bt : ℝ → Ω → (KSpace d (wholeSpaceIndex d) T →L[ℝ] KSpace d (wholeSpaceIndex d) T →L[ℝ] ℝ),
              (∀ r ∈ Set.Icc (0:ℝ) (b + T), ∀ ζ u v, Bt r ζ u v =
                featureForm (wholeSpaceIndex d) T β⁻¹
                  (fun (i : Fin d) (x : Euc d) => r2WindowFeature
                    ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ))
                    (wholeSpaceIndex d) T (gradComp i) b r x) (HRS.Whole.empirical (X r.toNNReal ζ)) u v -
                featureForm (wholeSpaceIndex d) T β⁻¹
                  (fun (i : Fin d) (x : Euc d) => r2WindowFeature
                    ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ))
                    (wholeSpaceIndex d) T (gradComp i) b r x) (HRS.Whole.withDensityReal ((fun _ : ℝ => ρβ) r)) u v) ∧
              ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) (b + T), ENNReal.ofReal (HRS.traceNormForm (Bt r ζ))) ∂P ≤
                ENNReal.ofReal (CT * HRS.Whole.localizationRate d s C₀ N)) ∧
            ∫⁻ ζ, ⨆ u ∈ Set.Icc (0 : ℝ) T, l2NormE (fun α : MultiIndex d =>
                -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) (b + u),
                  r2CommForcingMov ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ)) s (wholeSpaceIndex d)
                    (fun _ => ρβ) X α (b + u) r ζ) ∂P ≤
              ENNReal.ofReal (CT * Real.sqrt N * deltaN d s N) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Cs0, cdec, hcdec, hsum, hmain⟩ := HRS.MS.R2WinOrb.s103_stationary hd s hs0 hs a β ha hβ T hT
  obtain ⟨M, L, Mom, C₀c, hC₀c, hcl⟩ := s104_hcls_bounds hd hs0 hs ha hβ 1 1 1
  obtain ⟨Cphi, hCphi0, hphi'⟩ := s104_hphi hd1
  obtain ⟨C₀min, hC₀min0, hpA⟩ := s104_partA.{0} hd1 s hs0 hs M
  set C₀ : ℝ := max (max C₀min C₀c) 0 with hC₀
  have hC₀ge1 : C₀min ≤ C₀ := (le_max_left _ _).trans (le_max_left _ _)
  have hC₀ge2 : C₀c ≤ C₀ := (le_max_right _ _).trans (le_max_left _ _)
  have hC₀0 : 0 ≤ C₀ := le_max_right _ _
  set Cs : ℝ := max Cs0 Cphi with hCs
  have hCs0 : 0 ≤ Cs := (hCphi0).trans (le_max_right _ _)
  set k : ℕ := 4 * d + 42 with hk
  have hb0 : ∀ α : MultiIndex d, 0 ≤ s104_b d α := s104_b_nonneg
  have hbS : Summable (s104_b d) := hsum
  set bsum : ℝ := ∑' α, s104_b d α with hbsum
  refine ⟨C₀, ?_, ?_⟩
  · intro ρβ hρβ N hN t ht X hX
    have := (hcl ρβ hρβ (fun _ => ρβ) (Or.inl rfl)).2 N hN t ht X hX
    have h2 := s104_oN_mono d s hC₀ge2 N
    linarith
  intro CB
  set m : ℝ := ((wholeSpaceIndex d : ℕ) : ℝ) with hm
  set Kc : ℝ := (2 + (d : ℝ) ^ k * Real.sqrt T) * (Cs * bsum) with hKc
  set Mo : ℝ := max (max CB 0) Mom with hMo
  have hMo0 : 0 ≤ Mo := (le_max_right CB 0).trans (le_max_left _ _)
  obtain ⟨CTa, hCTa⟩ := hpA C₀ hC₀ge1 T cdec β⁻¹ (Kc ^ 2) (max CB 0) Mo hcdec hT.le
    (inv_nonneg.2 hβ.le) (sq_nonneg _) (le_max_right _ _) hMo0
  obtain ⟨Cc, hCc0, hpB⟩ := s104_partB hd s hs0 hs M L β hβ CB
  set CTb : ℝ := (1 / 2) * (Cc * Cs * (1 / cdec + T + T * (1 / cdec)) * bsum) with hCTb
  refine ⟨max CTa CTb, ?_⟩
  intro ρβ hρβ N hN Ω _ P _ X₀ W X hreal hMov _hwin b hb
  have hprob0 : HRS.Whole.IsProbDensity ρβ := hρβ.2.1
  have htraj : IsR2WindowTrajectory d s a β ρβ 1 1 1 (fun _ => ρβ) := Or.inl rfl
  obtain ⟨hρ, hcomp⟩ := hcl ρβ hρβ (fun _ => ρβ) htraj
  have hjm : ∀ T' : ℝ, 0 ≤ T' → Measurable fun p : ℝ × Euc d => (fun _ : ℝ => ρβ) (max 0 (min p.1 T')) p.2 :=
    fun T' _ => hprob0.measurable.comp measurable_snd
  set ρ : ℝ → Euc d → ℝ := fun _ => ρβ with hρdef
  obtain ⟨ℱ, W', hfilt⟩ := hreal.filtered
  have hXm : ∀ r : ℝ, Measurable (X r.toNNReal) := fun r => (hreal.solution (b + T)).adapted _
  obtain ⟨hevol, M0, M1, M2⟩ := s104_hdyn_stat hd hs0 hs ha hβ hT.le hρβ hN P hreal hb C₀
  set C : WholeCoeff d := (quadraticGradientDyn d s a β).coeff ρ with hC
  -- the orbit data of S10.3
  have horb : ∀ α : MultiIndex d,
      (∀ t : ℝ, 0 ≤ t → R2OrbitGrad C k t (oscTestFun m α) (Cs * s104_b d α) cdec) ∧
      (∀ t : ℝ, 0 ≤ t → R2OrbitGrad C k t (generatorW C t (oscTestFun m α)) (Cs * s104_b d α) cdec) := by
    intro α
    have hm' := hmain ρβ hρβ α
    dsimp only at hm'
    have hle : Cs0 * s104_b d α ≤ Cs * s104_b d α :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (s104_b_nonneg α)
    exact ⟨fun t ht => s104_R2OrbitGrad_mono _ (hm'.1 t ht).2.1 hle,
      fun t ht => s104_R2OrbitGrad_mono _ (hm'.1 t ht).2.2.2.1 hle⟩
  have hmS : mStar d - 1 ≤ k := by
    unfold mStar; omega
  have hfeat : ∀ r ∈ Set.Icc (0 : ℝ) (b + T), ∀ a' : Fin d,
      ContDiff ℝ k (fun x => r2WindowFeature C m T (gradComp a') b r x) ∧ ∀ j ≤ k, ∀ x,
        ‖iteratedFDeriv ℝ j (fun x => r2WindowFeature C m T (gradComp a') b r x) x‖ ≤
          Kc * s104_theta cdec b r := by
    intro r hr a'
    exact s104_window_feature hd1 C k m T cdec Cs hT.le hcdec.le hCs0 (s104_b d) hb0 hbS
      (fun α => (horb α).1) (fun α => (horb α).2)
      (fun α a'' => ⟨(hphi' α a'').1, fun j hj x => ((hphi' α a'').2 j hj x).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (s104_b_nonneg α))⟩) hb hr.1 a'
      (fun α x => s104_hobs_stat hd hs0 hs ha hβ hρβ T b r hT.le hb hr.1 a' α x)
  have hlr0 : 0 ≤ localizationRate d s C₀ N := by
    unfold localizationRate
    exact Real.rpow_nonneg (add_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.sqrt_nonneg _)) _
  have hoN0 := s104_oN_nonneg d s C₀ hC₀0 N
  refine ⟨?_, ?_⟩
  · -- part (a)
    have hinj : ∀ᵐ ζ ∂P, ∀ r ∈ Set.Icc (0 : ℝ) (b + T), Function.Injective (X r.toNNReal ζ) := by
      filter_upwards [(hreal.solution (b + T)).no_collision] with ζ hζ r hr
      refine s104_injective_of_not_collision (hζ r.toNNReal ?_)
      rw [Real.coe_toNNReal r hr.1]; exact hr.2
    have hE : ∀ r ∈ Set.Icc (0 : ℝ) (b + T), ∫⁻ ζ, ENNReal.ofReal (rieszModulatedEnergy d s
        (X r.toNNReal ζ) (HRS.Whole.withDensityReal (ρ r)) + HRS.oN d s C₀ N) ∂P ≤
        ENNReal.ofReal (max CB 0 * HRS.oN d s C₀ N) := by
      intro r hr
      have h4 := (hMov r hr.1).2.2.2.1
      rw [lintegral_map (s104_energy_meas N s C₀ (ρ r) (hρ r hr.1).1).ennreal_ofReal (hXm r)] at h4
      exact h4.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hoN0))
    have hM : ∀ r ∈ Set.Icc (0 : ℝ) (b + T), ∫⁻ ζ, ENNReal.ofReal
        (secondMomentOf (HRS.Whole.empirical (X r.toNNReal ζ))) ∂P ≤ ENNReal.ofReal Mo := by
      intro r hr
      have h5 := (hMov r hr.1).2.2.2.2
      simp_rw [s104_secondMoment_eq (by omega : 0 < N)]
      exact h5.trans (ENNReal.ofReal_le_ofReal ((le_max_left CB 0).trans (le_max_left _ _)))
    have hρ' : ∀ r ∈ Set.Icc (0 : ℝ) (b + T), HRS.Whole.IsProbDensity (ρ r) ∧ (∀ x, ρ r x ≤ M) ∧
        Integrable (fun x => ‖x‖ ^ 2 * ρ r x) ∧ secondMomentOf (HRS.Whole.withDensityReal (ρ r)) ≤ Mo :=
      fun r hr => by
        obtain ⟨h1, h2, h3, h4, -⟩ := hρ r hr.1
        exact ⟨h1, h2, h3, h4.trans (le_max_right _ _)⟩
    have hAE := s104_energy_aemeas P ℱ X hfilt.progressive s C₀ ρ (T' := b + T) (by linarith)
      (fun r hr => (hρ r hr.1).1) (hjm (b + T) (by linarith))
    have hAM := HRS.MS.GenPath.s56_mm_aemeas (by omega : 0 < N) P ℱ X hfilt.progressive
      (T := b + T) (by linarith)
    obtain ⟨Bt, hBt, hbound⟩ := hCTa m b hb N hN P X ρ hρ' hinj hAE hAM hE hM
      (fun r a' x => r2WindowFeature C m T (gradComp a') b r x) (fun r => Kc * s104_theta cdec b r)
      (fun r hr a' => (hfeat r hr a').1.of_le (by exact_mod_cast hmS))
      (fun r hr a' j hj x => (hfeat r hr a').2 j (hj.trans hmS) x)
      (fun r hr => by rw [mul_pow, ← s104_theta2_eq])
    exact ⟨Bt, hBt, hbound.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hlr0))⟩
  · -- part (b)
    have hδ : 0 ≤ deltaN d s N := HRS.MS.S53.s53_deltaN_nonneg s (by omega)
    have hρB : ∀ r ∈ Set.Icc (0 : ℝ) (b + T), HRS.Whole.IsProbDensity (ρ r) ∧ (∀ x, ρ r x ≤ M) ∧
        (s = 0 → HasLogMoment (HRS.Whole.withDensityReal (ρ r)) L) := fun r hr => by
      obtain ⟨h1, h2, -, -, h5⟩ := hρ r hr.1
      exact ⟨h1, h2, h5⟩
    have hres := hpB C ρ m T b cdec Cs k (by omega) hcdec hCs0 hT.le hb (s104_b d) hb0 hbS
      (fun α => (horb α).1) (fun α => (horb α).2) N hN P X hρB (fun r hr => hXm r)
      (fun r hr => (hMov r hr.1).1) hevol M0 M1 M2
    refine hres.trans (ENNReal.ofReal_le_ofReal ?_)
    have hsq : 0 ≤ Real.sqrt N * deltaN d s N := by positivity
    have e : Real.sqrt N / 2 * (Cc * Cs * deltaN d s N) * (1 / cdec + T + T * (1 / cdec)) * bsum =
        CTb * (Real.sqrt N * deltaN d s N) := by
      rw [hCTb]; ring
    rw [e]
    calc CTb * (Real.sqrt N * deltaN d s N) ≤ max CTa CTb * (Real.sqrt N * deltaN d s N) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hsq
      _ = _ := by ring

end HRS.MS.R2WinErr
