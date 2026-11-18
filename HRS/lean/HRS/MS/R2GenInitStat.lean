import HRS.MS.R2GenInitAux10
import HRS.MS.R2WinErrStat
import HRS.MS.R2WinOrbAux15

/-!
# S10.5 for the stationary trajectory: `r2_window_general_initial_stationary_of_hcmp`

The statement of `HRS.Whole.r2_window_general_initial` for `ρ = fun _ => ρ_β`, proved from `s103_stationary`, the S10.4 pieces
(`s104_hcls_bounds`, `s104_hphi`, `s104_hobs_stat`, `s104_hdyn_stat`), the entropy and moment propagation of the stationary dynamics
(`s105_hent_stat`, `s105_hmom_stat`) and ONE remaining input, the window comparison `S105CompareStat` (the window analogue of `general_paths`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d : ℕ}

open HRS.MS.R2GenInit HRS.MS.R2WinErr HRS.Whole.AppendixA

/-- The window comparison theorem (see the module docstring): given a bound `F` for the forcing remainder and a bound `W` for the covariance
error (as in `r2_window_errors`), the laws of the particle window `Ξ_{N,b}` and of the linear window `Y_{N,b}` are within
`C (ε_b + F + W)` (smooth) and `C (ε_b + F + √W)` (`W_1`), `ε_b` the coupling cost at start `b`. -/
def S105CompareStat (d : ℕ) (s a β T : ℝ) : Prop :=
  ∃ CTc : ℝ, 0 ≤ CTc ∧ ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ N : ℕ, 2 ≤ N → GibbsEntropyContraction d s a β N →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
    IsR2Realization d s a β P X₀ W X →
    relEntropy (law P X₀) (modulatedGibbs (rieszKernel d s) N β
      (withDensityReal ((fun _ : ℝ => ρβ) 0))) < ⊤ →
    ∀ η₀ : Ω → (Euc d → ℝ) → ℝ, ProbabilityTheory.IndepFun (fun ζ => (X₀ ζ, η₀ ζ)) (fun ζ t => W t ζ) P →
    ∀ Y : ℝ → Ω → OscDual d (wholeSpaceIndex d),
    (∀ T' : ℝ, IsLinearFluctuationSolutionW P ((quadraticGradientDyn d s a β).coeff (fun _ : ℝ => ρβ))
      (wholeSpaceIndex d) β⁻¹ T' η₀ Y) →
    (∀ b : ℝ, 0 ≤ b → ∀ᵐ ζ ∂P, Continuous fun u : Set.Icc (0 : ℝ) T =>
      r2InitCouplingFun ((quadraticGradientDyn d s a β).coeff (fun _ : ℝ => ρβ)) (wholeSpaceIndex d)
        (withDensityReal ((fun _ : ℝ => ρβ) 0)) b X₀ η₀ ζ u) →
    ∀ b : ℝ, 0 ≤ b → ∀ F Wt : ℝ≥0∞,
      (∫⁻ ζ, ⨆ u ∈ Set.Icc (0 : ℝ) T, l2NormE (fun α : MultiIndex d =>
          -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) (b + u),
            r2CommForcingMov ((quadraticGradientDyn d s a β).coeff (fun _ : ℝ => ρβ)) s (wholeSpaceIndex d) (fun _ : ℝ => ρβ) X α
              (b + u) r ζ) ∂P ≤ F) →
      (∃ Bt : ℝ → Ω → (KSpace d (wholeSpaceIndex d) T →L[ℝ] KSpace d (wholeSpaceIndex d) T →L[ℝ] ℝ),
        (∀ r ∈ Set.Icc (0 : ℝ) (b + T), ∀ ζ u v, Bt r ζ u v =
          featureForm (wholeSpaceIndex d) T β⁻¹
            (fun (i : Fin d) (x : Euc d) => r2WindowFeature ((quadraticGradientDyn d s a β).coeff (fun _ : ℝ => ρβ))
              (wholeSpaceIndex d) T (gradComp i) b r x) (empirical (X r.toNNReal ζ)) u v -
          featureForm (wholeSpaceIndex d) T β⁻¹
            (fun (i : Fin d) (x : Euc d) => r2WindowFeature ((quadraticGradientDyn d s a β).coeff (fun _ : ℝ => ρβ))
              (wholeSpaceIndex d) T (gradComp i) b r x) (withDensityReal ((fun _ : ℝ => ρβ) r)) u v) ∧
        ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) (b + T), ENNReal.ofReal (traceNormForm (Bt r ζ))) ∂P ≤ Wt) →
      AEMeasurable (flucPathW (wholeSpaceIndex d) T b (Real.sqrt N) X (fun _ : ℝ => ρβ)) P ∧
      AEMeasurable (processWindow (wholeSpaceIndex d) T b Y) P ∧
      ENNReal.ofReal (smoothDist 2 (law P (flucPathW (wholeSpaceIndex d) T b (Real.sqrt N) X (fun _ : ℝ => ρβ)))
          (law P (processWindow (wholeSpaceIndex d) T b Y))) ≤
        ENNReal.ofReal CTc * ((∫⁻ ζ, ENNReal.ofReal
          ‖r2InitCouplingPath ((quadraticGradientDyn d s a β).coeff (fun _ : ℝ => ρβ)) (wholeSpaceIndex d) T
            (withDensityReal ((fun _ : ℝ => ρβ) 0)) b X₀ η₀ ζ‖ ∂P) + F + Wt) ∧
      wassersteinE 1 (law P (flucPathW (wholeSpaceIndex d) T b (Real.sqrt N) X (fun _ : ℝ => ρβ)))
          (law P (processWindow (wholeSpaceIndex d) T b Y)) ≤
        ENNReal.ofReal CTc * ((∫⁻ ζ, ENNReal.ofReal
          ‖r2InitCouplingPath ((quadraticGradientDyn d s a β).coeff (fun _ : ℝ => ρβ)) (wholeSpaceIndex d) T
            (withDensityReal ((fun _ : ℝ => ρβ) 0)) b X₀ η₀ ζ‖ ∂P) + F + Wt ^ (1 / 2 : ℝ))


set_option maxHeartbeats 1600000 in
theorem r2_window_general_initial_stationary_of_hcmp (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < 2 * (d : ℝ) / 3) (a β : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (T : ℝ) (hT : 0 < T)
    (hcmp : S105CompareStat d s a β T) :
    ∃ C₀ : ℝ,
      (∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t →
        ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
          0 ≤ rieszModulatedEnergy d s X (withDensityReal ((fun _ : ℝ => ρβ) t)) + oN d s C₀ N) ∧
      ∃ CE CT : ℝ,
      ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ N : ℕ, 2 ≤ N →
        GibbsEntropyContraction d s a β N →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
          IsR2Realization d s a β P X₀ W X →
          relEntropy (law P X₀) (modulatedGibbs (rieszKernel d s) N β (withDensityReal ((fun _ : ℝ => ρβ) 0))) < ⊤ →
          ∀ η₀ : Ω → (Euc d → ℝ) → ℝ, ProbabilityTheory.IndepFun (fun ζ => (X₀ ζ, η₀ ζ)) (fun ζ t => W t ζ) P →
          ∀ Y : ℝ → Ω → OscDual d (wholeSpaceIndex d),
          (∀ T' : ℝ, IsLinearFluctuationSolutionW P ((quadraticGradientDyn d s a β).coeff (fun _ : ℝ => ρβ))
            (wholeSpaceIndex d) β⁻¹ T' η₀ Y) →
          (∀ b : ℝ, 0 ≤ b → ∀ᵐ ζ ∂P, Continuous fun u : Set.Icc (0 : ℝ) T =>
            r2InitCouplingFun ((quadraticGradientDyn d s a β).coeff (fun _ : ℝ => ρβ)) (wholeSpaceIndex d)
              (withDensityReal ((fun _ : ℝ => ρβ) 0)) b X₀ η₀ ζ u) →
          let BN : ℝ := 1 + (relEntropy (law P X₀)
            (modulatedGibbs (rieszKernel d s) N β (withDensityReal ((fun _ : ℝ => ρβ) 0)))).toReal + N * deltaN d s N
          let EN : ℝ := CE * (oN d s C₀ N + BN / N)
          let wEnt : ℝ := generalLocalizationRate d EN (BN / N) N
          let εN : ℝ≥0∞ := ⨆ b : {b : ℝ // 0 ≤ b}, ∫⁻ ζ, ENNReal.ofReal
            ‖r2InitCouplingPath ((quadraticGradientDyn d s a β).coeff (fun _ : ℝ => ρβ)) (wholeSpaceIndex d) T
              (withDensityReal ((fun _ : ℝ => ρβ) 0)) b X₀ η₀ ζ‖ ∂P
          ∀ b : ℝ, 0 ≤ b →
            AEMeasurable (flucPathW (wholeSpaceIndex d) T b (Real.sqrt N) X (fun _ : ℝ => ρβ)) P ∧
            AEMeasurable (processWindow (wholeSpaceIndex d) T b Y) P ∧
            ENNReal.ofReal (smoothDist 2 (law P (flucPathW (wholeSpaceIndex d) T b (Real.sqrt N) X (fun _ : ℝ => ρβ)))
                (law P (processWindow (wholeSpaceIndex d) T b Y))) ≤
              ENNReal.ofReal CT * (εN + ENNReal.ofReal (BN / Real.sqrt N + wEnt)) ∧
            wassersteinE 1 (law P (flucPathW (wholeSpaceIndex d) T b (Real.sqrt N) X (fun _ : ℝ => ρβ)))
                (law P (processWindow (wholeSpaceIndex d) T b Y)) ≤
              ENNReal.ofReal CT * (εN + ENNReal.ofReal (BN / Real.sqrt N + Real.sqrt wEnt)) := by
  have hd1 : 1 ≤ d := by omega
  have hsd : s < (d : ℝ) := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨Cs0, cdec, hcdec, hsum, hmain⟩ := HRS.MS.R2WinOrb.s103_stationary hd s hs0 hsd a β ha hβ T hT
  obtain ⟨M, L, Mom, C₀c, hC₀c, hcl⟩ := s104_hcls_bounds hd hs0 hsd ha hβ 1 1 1
  obtain ⟨Cphi, hCphi0, hphi'⟩ := s104_hphi hd1
  obtain ⟨C₀min, hpA⟩ := s105_partA hd1 s hs0 hsd M
  obtain ⟨Cent, hCent0, hentF⟩ : ∃ Cent : ℝ, 0 ≤ Cent ∧ ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ →
      ∀ N : ℕ, 2 ≤ N → GibbsEntropyContraction d s a β N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
      IsR2Realization d s a β P X₀ W X →
      relEntropy (law P X₀) (modulatedGibbs (rieszKernel d s) N β (withDensityReal ((fun _ : ℝ => ρβ) 0))) < ⊤ →
      ∀ t : ℝ, 0 ≤ t → relEntropy (P.map (X t.toNNReal))
        (modulatedGibbs (rieszKernel d s) N β (withDensityReal ((fun _ : ℝ => ρβ) t))) ≤
        ENNReal.ofReal (Cent * ((relEntropy (law P X₀)
          (modulatedGibbs (rieszKernel d s) N β (withDensityReal ((fun _ : ℝ => ρβ) 0)))).toReal +
            N * deltaN d s N)) :=
    ⟨1, zero_le_one, fun ρβ hρβ N hN hGib Ω _ P _ X₀ W X hreal hfin t ht =>
      s105_hent_stat hd hs0 hsd ha hβ hρβ hN hGib P hreal hfin t ht⟩
  obtain ⟨Cm, hCm0, hmomF⟩ := s105_hmom_stat hd hs0 hsd ha hβ
  obtain ⟨CTc, hCTc0, hcmpF⟩ := hcmp
  obtain ⟨Cen, hCen0, hEn⟩ := s105_energy_moment hd s hs0 hsd M L β hβ
  obtain ⟨Cc, hCc0, hpB⟩ := s105_partB hd s hs0 hsd M L β hβ
  set C₀ : ℝ := max (max C₀min C₀c) 0 with hC₀
  have hC₀ge1 : C₀min ≤ C₀ := (le_max_left _ _).trans (le_max_left _ _)
  have hC₀ge2 : C₀c ≤ C₀ := (le_max_right _ _).trans (le_max_left _ _)
  have hC₀0 : 0 ≤ C₀ := le_max_right _ _
  set Cs : ℝ := max Cs0 Cphi with hCs
  have hCs0 : 0 ≤ Cs := hCphi0.trans (le_max_right _ _)
  set k : ℕ := 4 * d + 42 with hk
  have hb0 : ∀ α : MultiIndex d, 0 ≤ s104_b d α := s104_b_nonneg
  have hbS : Summable (s104_b d) := hsum
  set bsum : ℝ := ∑' α, s104_b d α with hbsum
  set Kc : ℝ := (2 + (d : ℝ) ^ k * Real.sqrt T) * (Cs * bsum) with hKc
  set Mom' : ℝ := max Mom 0 with hMom'
  obtain ⟨CTa, hCTa0, hCTa⟩ := hpA C₀ hC₀ge1 T cdec β⁻¹ (Kc ^ 2) hcdec hT.le
    (inv_nonneg.2 hβ.le) (sq_nonneg _)
  set CE : ℝ := max 1 (Cen * (Cent + 1)) with hCE
  set K1 : ℝ := 1 + Mom' + Cm with hK1def
  set CF : ℝ := Cc * Cs * (Cent + 1) * (1 / cdec + T + T * (1 / cdec)) * bsum / 2 with hCF
  set CW : ℝ := CTa * K1 with hCW
  set Cmax : ℝ := max (max (max CF CW) (Real.sqrt CW)) 1 with hCmax
  refine ⟨C₀, ?_, CE, CTc * Cmax, ?_⟩
  · intro ρβ hρβ N hN t ht X hX
    have := (hcl ρβ hρβ (fun _ => ρβ) (Or.inl rfl)).2 N hN t ht X hX
    have h2 := s104_oN_mono d s hC₀ge2 N
    linarith
  intro ρβ hρβ N hN hGib
  have htraj : IsR2WindowTrajectory d s a β ρβ 1 1 1 (fun _ => ρβ) := Or.inl rfl
  have hprob0 : HRS.Whole.IsProbDensity ρβ := hρβ.2.1
  set ρ : ℝ → Euc d → ℝ := fun _ => ρβ with hρdef
  set C : WholeCoeff d := (quadraticGradientDyn d s a β).coeff ρ with hC
  set m : ℝ := ((wholeSpaceIndex d : ℕ) : ℝ) with hm
  intro Ω _ P _ X₀ W X hreal hfin η₀ hind Y hY hcont
  intro BN EN wEnt εN
  intro b hb
  obtain ⟨hρ, hcomp⟩ := hcl ρβ hρβ ρ htraj
  have hjm : ∀ T' : ℝ, 0 ≤ T' → Measurable fun p : ℝ × Euc d => ρ (max 0 (min p.1 T')) p.2 :=
    fun T' _ => hprob0.measurable.comp measurable_snd
  obtain ⟨ℱ, W', hfilt⟩ := hreal.filtered
  have hXm : ∀ r : ℝ, Measurable (X r.toNNReal) := fun r => (hreal.solution (b + T)).adapted _
  obtain ⟨hevol, M0, M1, M2⟩ := s104_hdyn_stat hd hs0 hsd ha hβ hT.le hρβ hN P hreal hb C₀
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
      (fun α x => s104_hobs_stat hd hs0 hsd ha hβ hρβ T b r hT.le hb hr.1 a' α x)
  -- the entropy and the constants
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hδ : 0 ≤ deltaN d s N := HRS.MS.S53.s53_deltaN_nonneg s (by omega)
  have hoN0 := s104_oN_nonneg d s C₀ hC₀0 N
  set h0 : ℝ := (relEntropy (HRS.law P X₀) (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
    (HRS.Whole.withDensityReal (ρ 0)))).toReal with hh0
  have hh00 : 0 ≤ h0 := ENNReal.toReal_nonneg
  have hBN : BN = 1 + h0 + N * deltaN d s N := rfl
  have hNδ : 0 ≤ (N : ℝ) * deltaN d s N := mul_nonneg hN0.le hδ
  have hBN1 : 1 ≤ BN := by rw [hBN]; linarith
  have hBN0 : 0 ≤ BN / N := by positivity
  have hδBN : deltaN d s N ≤ BN / N := by
    rw [le_div_iff₀ hN0]; rw [hBN]; nlinarith
  set Hb : ℝ := Cent * BN with hHb
  have hHb0 : 0 ≤ Hb := by positivity
  have hH : ∀ r ∈ Set.Icc (0 : ℝ) (b + T), relEntropy (P.map (X r.toNNReal))
      (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal (ρ r))) ≤
        ENNReal.ofReal Hb := fun r hr =>
    (hentF ρβ hρβ N hN hGib P X₀ W X hreal hfin r hr.1).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (by rw [hBN]; linarith) hCent0))
  -- the forcing remainder
  have hρB : ∀ r ∈ Set.Icc (0 : ℝ) (b + T), HRS.Whole.IsProbDensity (ρ r) ∧ (∀ x, ρ r x ≤ M) ∧
      (s = 0 → HasLogMoment (HRS.Whole.withDensityReal (ρ r)) L) := fun r hr => by
    obtain ⟨h1, h2, -, -, h5⟩ := hρ r hr.1
    exact ⟨h1, h2, h5⟩
  have hres := hpB C ρ m T b cdec Cs k (by omega) hcdec hCs0 hT.le hb (s104_b d) hb0 hbS
    (fun α => (horb α).1) (fun α => (horb α).2) N hN Hb hHb0 P X hρB (fun r hr => hXm r) hH
    hevol M0 M1 M2
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hkey : Real.sqrt N * (BN / N) = BN / Real.sqrt N := by
    have h2 := Real.sq_sqrt hN0.le
    field_simp
    nlinarith
  set Fb : ℝ≥0∞ := ENNReal.ofReal (CF * (BN / Real.sqrt N)) with hFb
  have hF : (∫⁻ ζ, ⨆ u ∈ Set.Icc (0 : ℝ) T, l2NormE (fun α : MultiIndex d =>
      -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) (b + u),
        r2CommForcingMov C s m ρ X α (b + u) r ζ) ∂P) ≤ Fb := by
    refine hres.trans (ENNReal.ofReal_le_ofReal ?_)
    have hΛ0 : 0 ≤ 1 / cdec + T + T * (1 / cdec) := by positivity
    have hbs0 : 0 ≤ bsum := tsum_nonneg hb0
    have h1 : Hb / N + deltaN d s N ≤ (Cent + 1) * (BN / N) := by
      rw [hHb]; nlinarith [hδBN, mul_div_assoc Cent BN (N : ℝ)]
    have h2 : (Real.sqrt N / 2) * ((Cc * (Hb / N + deltaN d s N)) * Cs) *
        (1 / cdec + T + T * (1 / cdec)) * bsum ≤
        (Real.sqrt N / 2) * ((Cc * ((Cent + 1) * (BN / N))) * Cs) *
        (1 / cdec + T + T * (1 / cdec)) * bsum := by
      gcongr
    refine h2.trans (le_of_eq ?_)
    rw [hCF]
    have : (Real.sqrt N / 2) * ((Cc * ((Cent + 1) * (BN / N))) * Cs) *
        (1 / cdec + T + T * (1 / cdec)) * bsum =
        (Cc * Cs * (Cent + 1) * (1 / cdec + T + T * (1 / cdec)) * bsum / 2) * (Real.sqrt N * (BN / N)) := by
      ring
    rw [this, hkey]
  -- the covariance error
  set Mq : ℝ := Cm * (1 + BN / N) + Mom' with hMq
  have hMq0 : 0 ≤ Mq := by positivity
  have hEN0 : 0 ≤ EN := by
    show 0 ≤ CE * (HRS.oN d s C₀ N + BN / N)
    exact mul_nonneg ((zero_le_one).trans (le_max_left _ _)) (add_nonneg hoN0 hBN0)
  have hinj : ∀ᵐ ζ ∂P, ∀ r ∈ Set.Icc (0 : ℝ) (b + T), Function.Injective (X r.toNNReal ζ) := by
    filter_upwards [(hreal.solution (b + T)).no_collision] with ζ hζ r hr
    refine s104_injective_of_not_collision (hζ r.toNNReal ?_)
    rw [Real.coe_toNNReal r hr.1]; exact hr.2
  have hE : ∀ r ∈ Set.Icc (0 : ℝ) (b + T), ∫⁻ ζ, ENNReal.ofReal (rieszModulatedEnergy d s
      (X r.toNNReal ζ) (HRS.Whole.withDensityReal (ρ r)) + HRS.oN d s C₀ N) ∂P ≤ ENNReal.ofReal EN := by
    intro r hr
    obtain ⟨hprob, hMr, -, -, hlog⟩ := hρ r hr.1
    haveI : IsProbabilityMeasure (P.map (X r.toNNReal)) :=
      ⟨by rw [Measure.map_apply (hXm r) MeasurableSet.univ]; simp⟩
    rw [← lintegral_map (s104_energy_meas N s C₀ (ρ r) hprob).ennreal_ofReal (hXm r)]
    refine (hEn (ρ r) hprob hMr hlog N hN (P.map (X r.toNNReal)) inferInstance Hb hHb0 (hH r hr) C₀
      hC₀0).trans (ENNReal.ofReal_le_ofReal ?_)
    show Cen * (Hb / N + deltaN d s N) + HRS.oN d s C₀ N ≤ CE * (HRS.oN d s C₀ N + BN / N)
    have h1 : Hb / N + deltaN d s N ≤ (Cent + 1) * (BN / N) := by
      rw [hHb]; nlinarith [hδBN, mul_div_assoc Cent BN (N : ℝ)]
    have h2 : Cen * (Hb / N + deltaN d s N) ≤ CE * (BN / N) :=
      (mul_le_mul_of_nonneg_left h1 hCen0).trans (by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) hBN0)
    have h3 : HRS.oN d s C₀ N ≤ CE * HRS.oN d s C₀ N :=
      le_mul_of_one_le_left hoN0 (le_max_left _ _)
    nlinarith
  have hM : ∀ r ∈ Set.Icc (0 : ℝ) (b + T), ∫⁻ ζ, ENNReal.ofReal
      (secondMomentOf (HRS.Whole.empirical (X r.toNNReal ζ))) ∂P ≤ ENNReal.ofReal Mq := by
    intro r hr
    have h5 := hmomF ρβ hρβ N hN hGib P X₀ W X hreal hfin r hr.1
    simp_rw [s104_secondMoment_eq (by omega : 0 < N)]
    refine h5.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hMq]; have : 0 ≤ Mom' := le_max_right _ _
    show Cm * (1 + BN / N) ≤ _
    linarith
  have hρ' : ∀ r ∈ Set.Icc (0 : ℝ) (b + T), HRS.Whole.IsProbDensity (ρ r) ∧ (∀ x, ρ r x ≤ M) ∧
      Integrable (fun x => ‖x‖ ^ 2 * ρ r x) ∧ secondMomentOf (HRS.Whole.withDensityReal (ρ r)) ≤ Mq :=
    fun r hr => by
      obtain ⟨h1, h2, h3, h4, -⟩ := hρ r hr.1
      refine ⟨h1, h2, h3, h4.trans ?_⟩
      have : 0 ≤ Cm * (1 + BN / N) := by positivity
      have h5 : Mom ≤ Mom' := le_max_left _ _
      rw [hMq]; linarith
  have hAE := s104_energy_aemeas P ℱ X hfilt.progressive s C₀ ρ (T' := b + T) (by linarith)
    (fun r hr => (hρ r hr.1).1) (hjm (b + T) (by linarith))
  have hAM := HRS.MS.GenPath.s56_mm_aemeas (by omega : 0 < N) P ℱ X hfilt.progressive
    (T := b + T) (by linarith)
  obtain ⟨Bt, hBt, hbound⟩ := hCTa m b hb N hN P X ρ EN Mq hEN0 hMq0 hρ' hinj hAE hAM hE hM
    (fun r a' x => r2WindowFeature C m T (gradComp a') b r x) (fun r => Kc * s104_theta cdec b r)
    (fun r hr a' => (hfeat r hr a').1.of_le (by exact_mod_cast hmS))
    (fun r hr a' j hj x => (hfeat r hr a').2 j (hj.trans hmS) x)
    (fun r hr => by rw [mul_pow, ← s104_theta2_eq])
  have hwEnt0 : 0 ≤ wEnt := by
    show 0 ≤ generalLocalizationRate d EN (BN / N) N
    unfold generalLocalizationRate
    haveI : Nonempty {R : ℝ // 1 ≤ R} := ⟨⟨1, le_rfl⟩⟩
    refine le_ciInf fun R => ?_
    have : 0 < R.1 := by linarith [R.2]
    positivity
  have hK1 : 1 ≤ K1 := by rw [hK1def]; have : 0 ≤ Mom' := le_max_right _ _; linarith
  have hglr : generalLocalizationRate d EN Mq N ≤ K1 * wEnt := by
    refine s105_glr_mono d N EN Mq (BN / N) K1 hEN0 hMq0 hBN0 hK1 ?_
    have : 0 ≤ Mom' := le_max_right _ _
    rw [hMq, hK1def]
    nlinarith [mul_nonneg hCm0 hBN0, mul_nonneg this hBN0]
  set Wt : ℝ≥0∞ := ENNReal.ofReal (CW * wEnt) with hWt
  have hW : (∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) (b + T),
      ENNReal.ofReal (traceNormForm (Bt r ζ))) ∂P) ≤ Wt := by
    refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hCW]
    calc CTa * generalLocalizationRate d EN Mq N ≤ CTa * (K1 * wEnt) :=
          mul_le_mul_of_nonneg_left hglr hCTa0
      _ = CTa * K1 * wEnt := by ring
  obtain ⟨hA1, hA2, hsm, hw1⟩ := hcmpF ρβ hρβ N hN hGib P X₀ W X hreal hfin η₀ hind Y hY hcont
    b hb Fb Wt hF ⟨Bt, hBt, hW⟩
  have hεle : (∫⁻ ζ, ENNReal.ofReal ‖r2InitCouplingPath C m T (HRS.Whole.withDensityReal (ρ 0)) b X₀ η₀ ζ‖ ∂P)
      ≤ εN :=
    le_iSup (fun b' : {b' : ℝ // 0 ≤ b'} => ∫⁻ ζ, ENNReal.ofReal
      ‖r2InitCouplingPath C m T (HRS.Whole.withDensityReal (ρ 0)) b'.1 X₀ η₀ ζ‖ ∂P) ⟨b, hb⟩
  set x : ℝ := BN / Real.sqrt N with hx
  have hx0 : 0 ≤ x := by positivity
  have hCmax1 : 1 ≤ Cmax := le_max_right _ _
  have hCF' : CF ≤ Cmax := (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hCW' : Real.sqrt CW ≤ Cmax := (le_max_right _ _).trans (le_max_left _ _)
  have hCW0 : 0 ≤ CW := mul_nonneg hCTa0 (by linarith)
  have hCWle : CW ≤ Cmax := (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hCmax0 : 0 ≤ Cmax := by linarith
  have key : ∀ (c1 c2 u v : ℝ), 0 ≤ u → 0 ≤ v → c1 ≤ Cmax → c2 ≤ Cmax →
      ENNReal.ofReal (c1 * u) + ENNReal.ofReal (c2 * v) ≤ ENNReal.ofReal Cmax * ENNReal.ofReal (u + v) := by
    intro c1 c2 u v hu hv h1 h2
    calc ENNReal.ofReal (c1 * u) + ENNReal.ofReal (c2 * v)
        ≤ ENNReal.ofReal (Cmax * u) + ENNReal.ofReal (Cmax * v) :=
          add_le_add (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right h1 hu))
            (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right h2 hv))
      _ = ENNReal.ofReal Cmax * ENNReal.ofReal (u + v) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hCmax0]
          congr 1; ring
  have hε1 : εN ≤ ENNReal.ofReal Cmax * εN :=
    le_mul_of_one_le_left zero_le (ENNReal.one_le_ofReal.2 hCmax1)
  have hCT : ENNReal.ofReal (CTc * Cmax) = ENNReal.ofReal CTc * ENNReal.ofReal Cmax :=
    ENNReal.ofReal_mul hCTc0
  refine ⟨hA1, hA2, ?_, ?_⟩
  · -- smooth distance
    refine hsm.trans ?_
    have hFW : Fb + Wt ≤ ENNReal.ofReal Cmax * ENNReal.ofReal (x + wEnt) :=
      key CF CW x wEnt hx0 hwEnt0 hCF' hCWle
    calc ENNReal.ofReal CTc * ((∫⁻ ζ, ENNReal.ofReal ‖r2InitCouplingPath C m T
            (HRS.Whole.withDensityReal (ρ 0)) b X₀ η₀ ζ‖ ∂P) + Fb + Wt)
        ≤ ENNReal.ofReal CTc * (εN + ENNReal.ofReal Cmax * ENNReal.ofReal (x + wEnt)) := by
          refine mul_le_mul' le_rfl ?_
          rw [add_assoc]
          exact add_le_add hεle hFW
      _ ≤ ENNReal.ofReal CTc * (ENNReal.ofReal Cmax * (εN + ENNReal.ofReal (x + wEnt))) := by
          refine mul_le_mul' le_rfl ?_
          rw [mul_add]
          exact add_le_add hε1 le_rfl
      _ = ENNReal.ofReal (CTc * Cmax) * (εN + ENNReal.ofReal (x + wEnt)) := by
          rw [hCT, mul_assoc]
  · -- W_1
    refine hw1.trans ?_
    have hWt12 : Wt ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt CW * Real.sqrt wEnt) := by
      rw [hWt, ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hCW0 hwEnt0) (by norm_num),
        ← Real.sqrt_eq_rpow, Real.sqrt_mul hCW0]
    have hFW : Fb + Wt ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal Cmax * ENNReal.ofReal (x + Real.sqrt wEnt) := by
      rw [hWt12]
      exact key CF (Real.sqrt CW) x (Real.sqrt wEnt) hx0 (Real.sqrt_nonneg _) hCF' hCW'
    calc ENNReal.ofReal CTc * ((∫⁻ ζ, ENNReal.ofReal ‖r2InitCouplingPath C m T
            (HRS.Whole.withDensityReal (ρ 0)) b X₀ η₀ ζ‖ ∂P) + Fb + Wt ^ (1 / 2 : ℝ))
        ≤ ENNReal.ofReal CTc * (εN + ENNReal.ofReal Cmax * ENNReal.ofReal (x + Real.sqrt wEnt)) := by
          refine mul_le_mul' le_rfl ?_
          rw [add_assoc]
          exact add_le_add hεle hFW
      _ ≤ ENNReal.ofReal CTc * (ENNReal.ofReal Cmax * (εN + ENNReal.ofReal (x + Real.sqrt wEnt))) := by
          refine mul_le_mul' le_rfl ?_
          rw [mul_add]
          exact add_le_add hε1 le_rfl
      _ = ENNReal.ofReal (CTc * Cmax) * (εN + ENNReal.ofReal (x + Real.sqrt wEnt)) := by
          rw [hCT, mul_assoc]

end HRS.Whole
