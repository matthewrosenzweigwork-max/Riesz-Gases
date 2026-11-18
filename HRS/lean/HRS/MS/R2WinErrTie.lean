import HRS.MS.R2WinErrAux16

/-!
# S10.4 tie: `r2_window_errors` from `r2_window_orbits` and explicit analytic inputs

`r2_window_errors_of_inputs` proves the frozen `HRS.Whole.r2_window_errors` (with the approved `Bt` repair ED12) from

* `h103 : type_of% @HRS.Whole.r2_window_orbits` (S10.3),
* `hcls : S104ClassInput` (uniform density / moment bounds, completion constant, measurability of the corrected energy for the class),
* `hphi : S104Phi` (the bound on `∂_aφ_α`, i.e. `s103_phi_cb`),
* `hobs` (`u`-measurability of the orbit slot, from the time-continuity of the orbits),
* `hdyn : S104RealInput` for every realization (joint measurability of the forcing families, and the integrated evolution inequality for the
  pair functional, from `∂_tU(r,t)φ = U(r,t)L_tφ`).  The joint measurability of the energy and of the empirical second moment is proved here
  (`s104_energy_aemeas`, `s56_mm_aemeas`) from the clamped joint measurability of the density in `S104ClassInput` and `hreal.filtered`.
The particle inputs (entropy, energy, second moment) are taken from `MovParticleBounds`, the absence of collisions from `IsR2Realization`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinErr

open HRS.Whole HRS.Whole.AppendixA

/-- The realization-dependent measurability and evolution inputs (see the module docstring). -/
def S104RealInput (d : ℕ) (s a β T : ℝ) (ρ : ℝ → Euc d → ℝ) (N : ℕ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig d N) (b C₀ : ℝ) : Prop :=
  (∀ ζ : Ω, ∀ α : MultiIndex d, ∀ r t0 t : ℝ, 0 ≤ r → r ≤ t0 → t0 ≤ t → t ≤ b + T →
    ENNReal.ofReal |r2CommForcingMov ((quadraticGradientDyn d s a β).coeff ρ) s
        ((wholeSpaceIndex d : ℕ) : ℝ) ρ X α t r ζ| ≤
      ENNReal.ofReal |r2CommForcingMov ((quadraticGradientDyn d s a β).coeff ρ) s
        ((wholeSpaceIndex d : ℕ) : ℝ) ρ X α t0 r ζ| +
        ∫⁻ s' in Set.Ioc t0 t, ENNReal.ofReal |s104_F2 ((quadraticGradientDyn d s a β).coeff ρ) s
          ((wholeSpaceIndex d : ℕ) : ℝ) ρ X α (s', r) ζ|) ∧
  (∀ α, AEMeasurable (fun p : Ω × ℝ => ENNReal.ofReal |r2CommForcingMov
      ((quadraticGradientDyn d s a β).coeff ρ) s ((wholeSpaceIndex d : ℕ) : ℝ) ρ X α b p.2 p.1|)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) b)))) ∧
  (∀ α, AEMeasurable (fun p : Ω × ℝ => ENNReal.ofReal |r2CommForcingMov
      ((quadraticGradientDyn d s a β).coeff ρ) s ((wholeSpaceIndex d : ℕ) : ℝ) ρ X α p.2 p.2 p.1|)
      (P.prod (volume.restrict (Set.Icc b (b + T))))) ∧
  (∀ α, AEMeasurable (fun p : Ω × (ℝ × ℝ) => ENNReal.ofReal |s104_F2
      ((quadraticGradientDyn d s a β).coeff ρ) s ((wholeSpaceIndex d : ℕ) : ℝ) ρ X α p.2 p.1|)
      (P.prod (volume.restrict ((Set.Icc b (b + T)) ×ˢ (Set.Icc (0 : ℝ) (b + T))))))

theorem r2_window_errors_of_inputs
    (h103 : type_of% @HRS.Whole.r2_window_orbits)
    (hcls : ∀ {d : ℕ}, 2 ≤ d → ∀ (s : ℝ), 0 ≤ s → s < d → ∀ (a β : ℝ), 0 < a → 0 < β →
      ∀ (εstar c₁ C₁ : ℝ), 0 < εstar → S104ClassInput d s a β εstar c₁ C₁)
    (hphi : ∀ {d : ℕ}, 2 ≤ d → S104Phi d)
    (hobs : ∀ {d : ℕ}, 2 ≤ d → ∀ (s a β T : ℝ) (ρβ : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ) (εstar c₁ C₁ : ℝ),
      IsThermalEquilibrium d s a β ρβ → IsR2WindowTrajectory d s a β ρβ εstar c₁ C₁ ρ →
      ∀ (b r : ℝ), 0 ≤ r → ∀ (a' : Fin d) (α : MultiIndex d) (x : Euc d),
        AEStronglyMeasurable (fun u : ℝ => if r < b + u then gradComp a' (propagatorW
          ((quadraticGradientDyn d s a β).coeff ρ) r (b + u) (generatorW
            ((quadraticGradientDyn d s a β).coeff ρ) (b + u)
            (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α))) x else 0)
          (volume.restrict (Set.Icc (0 : ℝ) T)))
    (hdyn : ∀ {d : ℕ}, 2 ≤ d → ∀ (s a β T : ℝ) (ρβ : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ) (εstar c₁ C₁ : ℝ),
      IsThermalEquilibrium d s a β ρβ → IsR2WindowTrajectory d s a β ρβ εstar c₁ C₁ ρ →
      ∀ (N : ℕ), 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
        IsR2Realization d s a β P X₀ W X → ∀ b C₀ : ℝ, 0 ≤ b → S104RealInput d s a β T ρ N P X b C₀) :
    type_of% @HRS.Whole.r2_window_errors := by
  intro d hd s hs0 hs a β ha hβ T hT c₁ C₁
  have hd1 : 1 ≤ d := by omega
  obtain ⟨εstar, hε, Cs0, cdec, hcdec, hsum, hmain⟩ :=
    h103 hd s hs0 hs a β ha hβ T hT c₁ C₁
  obtain ⟨M, L, Mom, C₀c, hC₀c, hcl⟩ := hcls hd s hs0 hs a β ha hβ εstar c₁ C₁ hε
  obtain ⟨Cphi, hCphi0, hphi'⟩ := hphi hd
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
  refine ⟨εstar, hε, C₀, ?_, ?_⟩
  · intro ρβ hρβ ρ htraj N hN t ht X hX
    have := (hcl ρβ hρβ ρ htraj).2.1 N hN t ht X hX
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
  intro ρβ hρβ ρ htraj N hN Ω _ P _ X₀ W X hreal hMov _hwin b hb
  obtain ⟨hρ, hcomp, hjm⟩ := hcl ρβ hρβ ρ htraj
  obtain ⟨ℱ, W', hfilt⟩ := hreal.filtered
  have hXm : ∀ r : ℝ, Measurable (X r.toNNReal) := fun r => (hreal.solution (b + T)).adapted _
  obtain ⟨hevol, M0, M1, M2⟩ := hdyn hd s a β T ρβ ρ εstar c₁ C₁ hρβ htraj N hN P X₀ W X
    hreal b C₀ hb
  set C : WholeCoeff d := (quadraticGradientDyn d s a β).coeff ρ with hC
  -- the orbit data of S10.3
  have horb : ∀ α : MultiIndex d,
      (∀ t : ℝ, 0 ≤ t → R2OrbitGrad C k t (oscTestFun m α) (Cs * s104_b d α) cdec) ∧
      (∀ t : ℝ, 0 ≤ t → R2OrbitGrad C k t (generatorW C t (oscTestFun m α)) (Cs * s104_b d α) cdec) := by
    intro α
    have hm' := hmain ρβ hρβ ρ htraj α
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
      (fun α x => hobs hd s a β T ρβ ρ εstar c₁ C₁ hρβ htraj b r hr.1 a' α x)
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
