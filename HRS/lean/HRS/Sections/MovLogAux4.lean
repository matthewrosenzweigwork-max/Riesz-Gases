import HRS.Sections.MovLogFinal
import HRS.Sections.MovLogAux3

/-!
# MOVLOG (part 4): `moving_pair_moments` for `D > 0` (TeX L6676-6690)

`movlog_pair_core`: the statement of `moving_pair_moments` with the extra hypothesis `0 < D`.  Route of the TeX proof:
exponential moment under `Q_N^t` (`movlog_expmoment`), Hölder against `‖h_N^t‖_{L^{p_∞}(Q_N^t)} ≤ e^{C J_N}`
(`moving_log_moment_proof`, `movlog_holder_exp`) giving `E e^{a N|F^h|/D} ≤ e^{A' J_N}`, then `movlog_tail_moment`.
The diagonal (junk value of `periodicRiesz d s 0`) is repaired by `h ↦ (x ≠ y ? D⁻¹ h : 0)`, the energies agreeing
a.s. since `X_t` is a.s. collision-free (through `ν ≪ Q ≪ π`).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace MovLog

variable {d : ℕ}

theorem movlog_pair_core (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (p₀ : ℝ) (hp₀ : 1 < p₀) (cstar : ℝ)
    (hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + cstar) (r : ℝ) (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        (∀ T : ℝ, 0 ≤ T → IsParticleSystem P htr.dyn T X₀ W X) →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        P.map X₀ ≪ modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0)) →
        eLpNorm ((P.map X₀).rnDeriv (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))))
          (ENNReal.ofReal p₀) (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) < ⊤ →
        ∀ (D : ℝ), 0 < D → ∀ h : Torus d → Torus d → ℝ, Measurable (Function.uncurry h) →
          (∀ x y, h x y = h y x) →
          (∀ x y, x ≠ y → |h x y| ≤ D * (periodicRiesz d s (x - y) + cstar)) →
          ∀ t : ℝ, 0 ≤ t →
            eLpNorm (fun ω => (N : ℝ) * modulatedEnergy h (X t.toNNReal ω) (withDensityReal (ρ t)))
              (ENNReal.ofReal r) P ≤
            ENNReal.ofReal (C * D * logMomentScale d s N p₀ (P.map X₀)
              (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0)))) := by
  have hd1 : 1 ≤ d := by omega
  have hs0 := htr.hs0
  have hsd := htr.hsd
  obtain ⟨pInf, C₁, hp, hC₁, Hlog⟩ := moving_log_moment_proof hd htr p₀ hp₀
  set cs : ℝ := max cstar (1 - periodicRiesz d s 0) with hcs
  have hcsc : cstar ≤ cs := le_max_left _ _
  have hw1 : ∀ z : Torus d, 1 ≤ periodicRiesz d s z + cs := fun z => by
    by_cases hz : z = 0
    · subst hz
      have : 1 - periodicRiesz d s 0 ≤ cs := le_max_right _ _
      linarith
    · have := hw z hz; linarith
  obtain ⟨c, C0, hc, hC0, Hexp⟩ := movlog_expmoment hd htr cs hw1
  obtain ⟨K, hK0, Htail⟩ := movlog_tail_moment r hr
  have hp0 : 0 < pInf := by linarith
  have hp1 : 0 < pInf - 1 := by linarith
  set a : ℝ := c * (pInf - 1) / pInf with ha
  have ha0 : 0 < a := by positivity
  set A' : ℝ := C₁ + C0 + 1 with hA'
  have hA'1 : 1 ≤ A' := by linarith
  refine ⟨K * A' / a, by positivity, fun N hN Ω _ P _ X₀ W X hps hfilt hac hfin D hD h hm hsym hdom t ht => ?_⟩
  have hN0 : 0 < N := by omega
  have hQ : ∀ r : ℝ, movT_Q (periodicRiesz d s) htr.dyn N ρ r =
      modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ r)) :=
    fun r => movT_Q_eq_beta (D := htr.dyn) (β := β) (by simp [IsSmoothPositiveTrajectory.dyn, PDE.mfData]) N ρ r
  -- notation
  set μt : Measure (Torus d) := withDensityReal (ρ t) with hμt
  set Q : Measure (Config d N) := modulatedGibbs (periodicRiesz d s) N β μt with hQdef
  set ν : Measure (Config d N) := P.map (X t.toNNReal) with hν
  set J : ℝ := logMomentScale d s N p₀ (P.map X₀)
    (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) with hJ
  have hXm : Measurable (X t.toNNReal) := (hps t ht).sol.adapted _
  have hae : AEMeasurable X₀ P := ((hps 0 le_rfl).sol.adapted 0).aemeasurable.congr (hps 0 le_rfl).sol.init
  haveI : IsProbabilityMeasure (P.map X₀) := (Measure.isProbabilityMeasure_map_iff hae).2 inferInstance
  haveI : IsProbabilityMeasure (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) := by
    rw [← hQ 0]; exact movT_Q_isProb hN (movlog_traj htr 0) ⟨le_rfl, le_rfl⟩
  -- J ≥ 1 + Nδ
  have hNδ1 : 1 ≤ (N : ℝ) * deltaN d s N := one_le_mul_deltaN hs0 N (by omega)
  have hJ2 : 1 + (N : ℝ) * deltaN d s N ≤ J := by
    have ha1 := movspec_one_le_eLpNorm_rnDeriv (P.map X₀)
      (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) hac hp₀.le
    have hat1 : 1 ≤ (eLpNorm ((P.map X₀).rnDeriv (modulatedGibbs (periodicRiesz d s) N β
        (withDensityReal (ρ 0)))) (ENNReal.ofReal p₀) (modulatedGibbs (periodicRiesz d s) N β
          (withDensityReal (ρ 0)))).toReal := by
      have := ENNReal.toReal_mono hfin.ne ha1
      simpa using this
    have := Real.log_nonneg hat1
    rw [hJ]; unfold logMomentScale; linarith
  have hJ1 : 1 ≤ J := by linarith
  obtain ⟨hνQ, hnorm⟩ := Hlog N hN P X₀ W X hps hfilt hac hfin t ht
  -- the repaired kernel
  set hk : Torus d → Torus d → ℝ := fun x y => if x = y then 0 else D⁻¹ * h x y with hhk
  have hkm : Measurable (Function.uncurry hk) := by
    have : Function.uncurry hk = fun p : Torus d × Torus d =>
        if p.1 = p.2 then 0 else D⁻¹ * Function.uncurry h p := by
      funext p; rfl
    rw [this]
    exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const
      (measurable_const.mul hm)
  have hks : ∀ x y, hk x y = hk y x := fun x y => by
    by_cases hxy : x = y
    · subst hxy; rfl
    · simp only [hhk, if_neg hxy, if_neg (Ne.symm hxy)]; rw [hsym x y]
  have hkd : ∀ x y, |hk x y| ≤ 1 * (periodicRiesz d s (x - y) + cs) := fun x y => by
    by_cases hxy : x = y
    · simp only [hhk, if_pos hxy, abs_zero]
      have := hw1 (x - y); linarith
    · simp only [hhk, if_neg hxy]
      have h1 := hdom x y hxy
      rw [abs_mul, abs_of_pos (inv_pos.2 hD)]
      calc D⁻¹ * |h x y| ≤ D⁻¹ * (D * (periodicRiesz d s (x - y) + cstar)) :=
            mul_le_mul_of_nonneg_left h1 (inv_pos.2 hD).le
        _ = periodicRiesz d s (x - y) + cstar := by field_simp
        _ ≤ 1 * (periodicRiesz d s (x - y) + cs) := by linarith
  obtain ⟨hEm, hEx⟩ := Hexp N hN t ht hk hkm hks hkd
  set Z : Config d N → ℝ := fun Y => (N : ℝ) * modulatedEnergy hk Y μt with hZ
  have hZm : Measurable Z := measurable_const.mul hEm
  have hEx' : ∫⁻ Y, ENNReal.ofReal (Real.exp (c * |Z Y|)) ∂Q ≤
      ENNReal.ofReal (Real.exp (C0 * ((N : ℝ) * deltaN d s N))) := by
    refine le_trans (le_of_eq ?_) hEx
    refine lintegral_congr fun Y => ?_
    have e : c * |Z Y| = c * N * |modulatedEnergy hk Y μt| := by
      simp only [hZ, abs_mul, abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]; ring
    rw [e]
  -- Hölder
  have hnorm' : eLpNorm (ν.rnDeriv Q) (ENNReal.ofReal pInf) Q ≤ ENNReal.ofReal (Real.exp (C₁ * J)) := by
    exact hnorm
  have hνQ' : ν ≪ Q := hνQ
  haveI : IsProbabilityMeasure Q := by
    rw [hQdef, ← hQ t]; exact movT_Q_isProb hN (movlog_traj htr t) ⟨ht, le_rfl⟩
  haveI : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff hXm.aemeasurable).2 inferInstance
  have hH := movlog_holder_exp hνQ' hp hZm hc hnorm' hEx'
  have hH2 : ∫⁻ Y, ENNReal.ofReal (Real.exp (a * |Z Y|)) ∂ν ≤ ENNReal.ofReal (Real.exp (A' * J)) := by
    refine hH.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
    have hq1 : (pInf - 1) / pInf ≤ 1 := by rw [div_le_one hp0]; linarith
    have hq0 : 0 ≤ (pInf - 1) / pInf := by positivity
    have hNJ : (N : ℝ) * deltaN d s N ≤ J := by linarith
    have : C0 * ((N : ℝ) * deltaN d s N) * ((pInf - 1) / pInf) ≤ C0 * J := by
      calc C0 * ((N : ℝ) * deltaN d s N) * ((pInf - 1) / pInf)
          ≤ C0 * ((N : ℝ) * deltaN d s N) * 1 :=
            mul_le_mul_of_nonneg_left hq1 (by positivity)
        _ ≤ C0 * J := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hNJ hC0
    have e : c * (pInf - 1) / pInf = a := rfl
    nlinarith
  -- transfer to P
  have hZP : ∫⁻ ω, ENNReal.ofReal (Real.exp (a * |Z (X t.toNNReal ω)|)) ∂P ≤
      ENNReal.ofReal (Real.exp (A' * J)) := by
    have hmeas : Measurable (fun Y : Config d N => ENNReal.ofReal (Real.exp (a * |Z Y|))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hZm.abs))
    rw [← lintegral_map' hmeas.aemeasurable hXm.aemeasurable]
    exact hH2
  have hT := Htail P (fun ω => Z (X t.toNNReal ω)) (hZm.comp hXm).aemeasurable a (A' * J) ha0
    (by nlinarith) hZP
  -- a.e. identification of the energies
  have hρd := (movlog_traj htr t).mf.density t ⟨ht, le_rfl⟩
  have hcont : Continuous (ρ t) :=
    mova_continuous_of_isCk ((movlog_traj htr t).ck t ⟨ht, le_rfl⟩)
  have hQπ : Q ≪ Measure.pi (fun _ : Fin N => μt) := by
    rw [hQdef, movf_modGibbs_eq_tilted hd1 hs0 hsd hρd hcont hN0 htr.hβ.le]
    exact tilted_absolutelyContinuous _ _
  haveI := isProb_withDensityReal hρd
  have hinj : ∀ᵐ ω ∂P, ∀ i j, i ≠ j → X t.toNNReal ω i ≠ X t.toNNReal ω j := by
    have h1 : ∀ᵐ Y ∂(Measure.pi (fun _ : Fin N => μt)), ∀ i j, i ≠ j → Y i ≠ Y j :=
      ae_injective_pi (withDensityReal_singleton hd1 (ρ t))
    have h2 : ∀ᵐ Y ∂ν, ∀ i j, i ≠ j → Y i ≠ Y j := hνQ'.ae_le (hQπ.ae_le h1)
    exact ae_of_ae_map hXm.aemeasurable h2
  have hcongr : (fun ω => (N : ℝ) * modulatedEnergy h (X t.toNNReal ω) μt) =ᵐ[P]
      fun ω => D • Z (X t.toNNReal ω) := by
    filter_upwards [hinj] with ω hω
    have e1 : modulatedEnergy hk (X t.toNNReal ω) μt =
        modulatedEnergy (fun x y => D⁻¹ * h x y) (X t.toNNReal ω) μt :=
      modulatedEnergy_congr_offdiag (withDensityReal_singleton hd1 (ρ t))
        (fun x y hxy => by simp only [hhk, if_neg hxy]) _ hω
    rw [movlog_modEnergy_smul] at e1
    simp only [hZ, smul_eq_mul, e1]
    field_simp
  have e5 : eLpNorm (fun ω => D • Z (X t.toNNReal ω)) (ENNReal.ofReal r) P =
      ENNReal.ofReal D * eLpNorm (fun ω => Z (X t.toNNReal ω)) (ENNReal.ofReal r) P := by
    have := eLpNorm_const_smul (μ := P) (p := ENNReal.ofReal r) D (fun ω => Z (X t.toNNReal ω))
    rw [Real.enorm_of_nonneg hD.le] at this
    exact this
  rw [eLpNorm_congr_ae hcongr, e5]
  calc ENNReal.ofReal D * eLpNorm (fun ω => Z (X t.toNNReal ω)) (ENNReal.ofReal r) P
      ≤ ENNReal.ofReal D * ENNReal.ofReal (K * (A' * J) / a) := by gcongr
    _ = ENNReal.ofReal (K * A' / a * D * J) := by
        rw [← ENNReal.ofReal_mul hD.le]
        congr 1
        field_simp

end MovLog

end HRS

end
