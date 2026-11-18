import HRS.PDE.MovFinal1
import HRS.PDE.MovFinal2
import HRS.PDE.MovFinal3
import HRS.Energy.MFEFinal
import HRS.Sections.DynEntFinal
import HRS.Sections.AllTimeFinal
import HRS.Sections.MovLogFinal2

/-!
# MOV-FINAL (consumers): the MOV consumers re-run with the sorry-free glue

Verbatim copies of `mfe_uniform_proof`, `dynamic_entropy_proof`, `alltime_Lp_proof` (with its helper `alltime_item1`),
`moving_log_moment_proof`, `moving_pair_moments_proof` (with its helper `movlog_pair_core`) with `mov_mfe_ineq`,
`movT_entropy_bound`, `mov_lp_bound` replaced by `mov_mfe_ineq_proof`, `movT_entropy_bound_proof`, `mov_lp_bound_proof`
(`MovFinal1-3`).  Each primed `_proof'` is tied by `type_of%` to the frozen statement.  Bridge B is not needed in its frozen
form: `alltime_item1` and `movlog_L` use `movT_relaxation_L_proof_reg` (with `IsCk 2 ρβ` from `Regime.thermal`).
-/

section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d : ℕ}

theorem mfe_uniform_proof' (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (D : DynData d), D.s = s → ∀ (N : ℕ), 2 ≤ N → ∀ (T Λ lam₀ : ℝ), 0 ≤ T →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ρ : ℝ → Torus d → ℝ) (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
        (X : ℝ≥0 → Ω → Config d N),
        MFEHyp P D N T Λ lam₀ ρ X₀ W X →
      ∀ K : ℝ → ℝ, IntegrableOn K (Set.Icc 0 T) →
        (∀ t ∈ Set.Icc 0 T, HasTransportBound d s (mfeTransport D (ρ t)) (K t)) →
      ∀ t ∈ Set.Icc 0 T,
        (P.map (X (Real.toNNReal t))).AbsolutelyContinuous volume ∧
        MFEFinite d s (P.map (X (Real.toNNReal t))) (withDensityReal (ρ t)) ∧
        modulatedFreeEnergy d s D.invβ (P.map (X (Real.toNNReal t))) (withDensityReal (ρ t)) +
            oNΛ d s C₀ Λ N ≤
          Real.exp (C * ∫ r in Set.Icc 0 T, K r) *
            (modulatedFreeEnergy d s D.invβ (P.map X₀) (withDensityReal (ρ 0)) + oNΛ d s C₀ Λ N) := by
  obtain ⟨A₀, A, hA₀, hA, hcomm⟩ := Commutator.commutator_estimate_of_packets hd hs0 hsd
  obtain ⟨B₀, hB₀, hnn⟩ := Commutator.energy_add_oN_nonneg hd hs0 hsd
  refine ⟨max A₀ B₀, A / 2, le_max_of_le_left hA₀, by positivity, ?_⟩
  intro D hDs N hN T Λ lam₀ hT Ω _ P _ ρ X₀ W X h K hKi hK
  subst hDs
  have hMov := movT_hyp_of_mfeHyp_proof h
  have key := mov_mfe_ineq_proof hN P hMov h.mfe_init
  have hΛ1 : 1 ≤ Λ := h.Λ_ge
  have hΛ0 : 0 ≤ Λ := by linarith
  have hβ : 0 < D.invβ := h.pos_temp
  set o : ℝ := oNΛ d D.s (max A₀ B₀) Λ N with ho
  have hoA : oNΛ d D.s A₀ Λ N ≤ o := oNΛ_mono_C₀ (le_max_left _ _) hΛ0 N
  have hoB : oNΛ d D.s B₀ Λ N ≤ o := oNΛ_mono_C₀ (le_max_right _ _) hΛ0 N
  have hK0 : ∀ r ∈ Set.Icc 0 T, 0 ≤ K r := fun r hr => (hK r hr).nonneg
  have hρΛ : ∀ r ∈ Set.Icc 0 T, ∀ x, ρ r x ≤ Λ := fun r hr x =>
    (le_abs_self _).trans ((PDE.R2Aux.abs_le_cbNorm (h.mf_reg r hr).1 x).trans (h.mf_reg r hr).2)
  -- general bounds for a probability measure ν of finite modulated free energy at time r
  have hbd : ∀ r ∈ Set.Icc 0 T, ∀ (ν : Measure (Config d N)) [IsProbabilityMeasure ν],
      MFEFinite d D.s ν (withDensityReal (ρ r)) →
      0 ≤ ∫ Z, rieszEnergy d D.s Z (withDensityReal (ρ r)) ∂ν + o ∧
      |∫ Z, commQuantity d D.s (mfeTransport D (ρ r)) Z (withDensityReal (ρ r)) ∂ν| ≤
        A * K r * (∫ Z, rieszEnergy d D.s Z (withDensityReal (ρ r)) ∂ν + o) ∧
      ∫ Z, rieszEnergy d D.s Z (withDensityReal (ρ r)) ∂ν + o ≤
        modulatedFreeEnergy d D.s D.invβ ν (withDensityReal (ρ r)) + o := by
    intro r hr ν _ hfin
    have hρ := h.mf.density r hr
    obtain ⟨-, hae⟩ := mfe41_ac hd hρ hfin.1
    have hnn' : ∀ᵐ Z ∂ν, 0 ≤ rieszEnergy d D.s Z (withDensityReal (ρ r)) + o := by
      filter_upwards [hae] with Z hZ
      have := hnn Λ hΛ1 N hN (ρ r) hρ (hρΛ r hr) Z hZ
      linarith
    have hc' : ∀ᵐ Z ∂ν, |commQuantity d D.s (mfeTransport D (ρ r)) Z (withDensityReal (ρ r))| ≤
        A * K r * (rieszEnergy d D.s Z (withDensityReal (ρ r)) + o) := by
      filter_upwards [hae] with Z hZ
      have h1 := (hcomm Λ hΛ1 N hN (ρ r) hρ (hρΛ r hr) Z hZ _ (K r) (hK r hr)).2
      refine h1.trans ?_
      have hAK : 0 ≤ A * K r := mul_nonneg hA.le (hK0 r hr)
      exact mul_le_mul_of_nonneg_left (by linarith) hAK
    obtain ⟨h1, h2⟩ := mfe41_int hfin.2 hnn' hc'
    refine ⟨h1, h2, ?_⟩
    unfold modulatedFreeEnergy
    have : 0 ≤ D.invβ * (normRelEntropy N ν (Measure.pi fun _ : Fin N => withDensityReal (ρ r))).toReal :=
      mul_nonneg hβ.le ENNReal.toReal_nonneg
    linarith
  -- Gronwall
  have hT' : T ∈ Set.Icc 0 T := ⟨hT, le_rfl⟩
  have hint := (key T hT').2.2.1
  have hgr := movspec_gronwall_var (T := T)
    (u0 := modulatedFreeEnergy d D.s D.invβ (P.map X₀) (withDensityReal (ρ 0)) + o)
    (a := fun r => A / 2 * K r)
    (G := fun r => -(1 / 2) * ∫ Z, commQuantity d D.s (mfeTransport D (ρ r)) Z (withDensityReal (ρ r))
        ∂(P.map (X r.toNNReal)))
    (u := fun r => modulatedFreeEnergy d D.s D.invβ (P.map (X r.toNNReal)) (withDensityReal (ρ r)) + o)
    (fun r hr => mul_nonneg (by positivity) (hK0 r hr)) (hKi.const_mul _) (hint.const_mul _)
    (fun t ht => by
      have := (key t ht).2.2.2
      rw [integral_const_mul]
      linarith)
    (fun r hr => by
      haveI : IsProbabilityMeasure (P.map (X r.toNNReal)) := inferInstance
      obtain ⟨-, h2, h3⟩ := hbd r hr (P.map (X r.toNNReal)) (key r hr).1
      have h4 := neg_abs_le (∫ Z, commQuantity d D.s (mfeTransport D (ρ r)) Z (withDensityReal (ρ r))
        ∂(P.map (X r.toNNReal)))
      have h5 : 0 ≤ A * K r := mul_nonneg hA.le (hK0 r hr)
      have h6 := mul_le_mul_of_nonneg_left h3 h5
      nlinarith)
  haveI : IsProbabilityMeasure (P.map X₀) := inferInstance
  obtain ⟨hu0, -, hu0'⟩ := hbd 0 ⟨le_rfl, hT⟩ (P.map X₀) h.mfe_init
  intro t ht
  refine ⟨?_, (key t ht).1, ?_⟩
  · have hρ := h.mf.density t ht
    exact (mfe41_ac hd hρ (key t ht).1.1).1
  · have h1 := hgr t ht
    refine h1.trans ?_
    have hu0n : 0 ≤ modulatedFreeEnergy d D.s D.invβ (P.map X₀) (withDensityReal (ρ 0)) + o := by
      linarith
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) hu0n
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact setIntegral_mono_set hKi (ae_restrict_of_forall_mem measurableSet_Icc (fun r hr => hK0 r hr))
      (Eventually.of_forall (Set.Icc_subset_Icc le_rfl ht.2))

example := (@mfe_uniform_proof' : type_of% @HRS.mfe_uniform)

end HRS

end

end

section
open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d : ℕ}

theorem dynamic_entropy_proof' (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsParticleSystem P htr.dyn T X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        relEntropy (P.map X₀)
          (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) ≠ ⊤ →
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          relEntropy (P.map (X t.toNNReal))
              (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ t))) +
            relEntropy (P.map (X t.toNNReal)) (Measure.pi fun _ => withDensityReal (ρ t)) ≤
          ENNReal.ofReal (C * entropyScale d s N (P.map X₀)
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0)))) := by
  have hd1 : 1 ≤ d := by omega
  have htr' : MovTraj htr.dyn T ρ :=
    movT_traj_of_global_proof s β V ρ₀ ρ htr.hs0 htr.hsd htr.hβ htr.V_smooth htr.init htr.global T
  obtain ⟨c₀, Λ₂, hc₀, hb⟩ :=
    movT_traj_uniform_proof s β V ρ₀ ρ htr.hs0 htr.hsd htr.hβ htr.V_smooth htr.init htr.global
  obtain ⟨C₁, hC₁0, hC₁⟩ := movT_entropy_bound_proof htr'
  obtain ⟨C₂, hC₂0, hC₂⟩ := dynent_product_bound hd1 htr' hc₀ (fun r hr x => (hb r hr.1).1 x)
    (fun r hr => (hb r hr.1).2)
  refine ⟨2 * C₁ + C₂ * (1 + C₁), by positivity, ?_⟩
  intro N hN Ω _ P _ X₀ W X hP hfilt hfin t ht
  have e : ∀ r, movT_Q (periodicRiesz d htr.dyn.s) htr.dyn N ρ r =
      modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ r)) := fun r =>
    movT_Q_eq_beta (g := periodicRiesz d s) rfl N ρ r
  have hMov : MovHyp P htr.dyn N T ρ X₀ W X :=
    movT_hyp_of_parts htr' hP.brownian hP.indep hP.sol hfilt
  have hfin' : relEntropy (P.map X₀) (movT_Q (periodicRiesz d htr.dyn.s) htr.dyn N ρ 0) ≠ ⊤ := by
    rw [e]; exact hfin
  obtain ⟨hfinT, hbd⟩ := hC₁ N hN P X₀ W X hMov hfin' t ht
  haveI : IsProbabilityMeasure (P.map (X t.toNNReal)) :=
    (Measure.isProbabilityMeasure_map_iff (hP.sol.adapted _).aemeasurable).2 inferInstance
  obtain ⟨hprodfin, hprodle⟩ := hC₂ N hN t ht (P.map (X t.toNNReal)) inferInstance hfinT
  rw [e] at hfinT hbd hprodle
  set B : ℝ := entropyScale d s N (P.map X₀)
    (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) with hB
  have hbd' : (relEntropy (P.map (X t.toNNReal))
      (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ t)))).toReal ≤ C₁ * B := by
    rw [e 0] at hbd; exact hbd
  have hδ : 1 ≤ (N : ℝ) * deltaN d s N := one_le_mul_deltaN htr.hs0 N (by omega)
  have hH0 : 0 ≤ (relEntropy (P.map X₀)
      (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0)))).toReal := ENNReal.toReal_nonneg
  have hBge : (N : ℝ) * deltaN d s N ≤ B := by rw [hB]; unfold entropyScale; linarith
  have hB1 : 1 ≤ B := by rw [hB]; unfold entropyScale; linarith
  have hHq0 := ENNReal.toReal_nonneg (a := relEntropy (P.map (X t.toNNReal))
      (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ t))))
  have hp0 := ENNReal.toReal_nonneg (a := relEntropy (P.map (X t.toNNReal))
      (Measure.pi fun _ : Fin N => withDensityReal (ρ t)))
  rw [← ENNReal.ofReal_toReal hfinT, ← ENNReal.ofReal_toReal hprodfin,
    ← ENNReal.ofReal_add hHq0 hp0]
  refine ENNReal.ofReal_le_ofReal ?_
  have hpr : (relEntropy (P.map (X t.toNNReal)) (Measure.pi fun _ : Fin N => withDensityReal (ρ t))).toReal ≤
      (relEntropy (P.map (X t.toNNReal))
        (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ t)))).toReal +
      C₂ * ((N : ℝ) * deltaN d s N + (relEntropy (P.map (X t.toNNReal))
        (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ t)))).toReal) := hprodle
  nlinarith [mul_le_mul_of_nonneg_left hBge hC₂0, mul_le_mul_of_nonneg_left hbd' hC₂0, hC₁0]

example := (@dynamic_entropy_proof' : type_of% @HRS.dynamic_entropy)

end HRS

end

end

section
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Sec7

variable {d : ℕ}

/-- Item 1 of Lemma 7.8, from `mov_lp_bound_proof` (MOV glue), bridges A, A', B, C. -/
theorem movfin_alltime_item1 (R : Regime d) :
    ∃ p : ℝ, 1 < p ∧ ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X₀ : Ω → Config d N)
        (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        PreparedRealization R.D P (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀))
          X₀ W X →
        ∀ t : ℝ, 0 ≤ t →
          (P.map (X t.toNNReal)) ≪ modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t)) ∧
          eLpNorm ((P.map (X t.toNNReal)).rnDeriv
              (modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t))))
            (ENNReal.ofReal p)
            (modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t))) ≤ ENNReal.ofReal C := by
  have hd1 : 1 ≤ d := by have := R.hd; omega
  have hs0 := alltime_hs0 R
  have hsd := alltime_hsd R
  have hsd2 : R.D.s < (d : ℝ) / 2 := R.hs
  obtain ⟨p₀, Ci, hp₀, hCi, hinit⟩ := alltime_init R
  obtain ⟨c₀, Λ₂, hc₀, hunif⟩ := movT_traj_uniform_proof R.D.s R.β R.D.V R.ρ₀ R.ρ hs0 hsd R.hβ R.hV
    R.hρ₀ (alltime_glob R)
  obtain ⟨Λ₁, hΛ₁, L, hLl, hLi, hLlip, hLint⟩ := alltime_L R
  obtain ⟨pInf, C₁, hp, hC₁, H⟩ := mov_lp_bound_proof hd1 hs0 hsd R.β R.β R.hβ c₀ hc₀ Λ₂ p₀ hp₀ Λ₁ hΛ₁
  have hβ₀ : 0 ≤ R.β₀ := by
    rcases R.hβ₀ with h | ⟨-, h⟩
    · exact h.le
    · exact h.ge
  have hcont0 : Continuous R.ρ₀ := mova_continuous_of_isCk (mova_isCk_two_of_smooth R.hρ₀.smooth)
  refine ⟨pInf, hp, Real.exp (C₁ * (2 + Ci)), fun N hN Ω _ P X₀ W X hprep t ht => ?_⟩
  have hN0 : 0 < N := by omega
  have hQ0eq : ∀ r : ℝ, movT_Q (periodicRiesz d R.D.s) R.D N R.ρ r =
      modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ r)) :=
    fun r => movT_Q_eq_beta R.hDβ N R.ρ r
  have hprobQ0 := alltime_gibbs_prob hd1 hs0 hsd R.hρ₀.density hcont0 hN0 hβ₀
  have hmapprob : IsProbabilityMeasure (P.map X₀) := by rw [hprep.law_init]; exact hprobQ0
  have hae : AEMeasurable X₀ P :=
    ((hprep.solution 0).adapted 0).aemeasurable.congr (hprep.solution 0).init
  haveI : IsProbabilityMeasure P := alltime_isProb hae hmapprob
  have hMov : MovHyp P R.D N t R.ρ X₀ W X :=
    ⟨alltime_traj R t, hprep.brownian, hprep.indep, hprep.solution t, hprep.filtered⟩
  obtain ⟨ρt, hρt⟩ := (alltime_traj R t).classical
  obtain ⟨ℓ, hℓ, hLℓ⟩ := hLl t
  obtain ⟨hinit1, hinit2⟩ := hinit N hN
  have hac : P.map X₀ ≪ movT_Q (periodicRiesz d R.D.s) R.D N R.ρ 0 := by
    rw [hprep.law_init, hQ0eq 0, R.init]; exact hinit1
  have hfin : eLpNorm ((P.map X₀).rnDeriv (movT_Q (periodicRiesz d R.D.s) R.D N R.ρ 0))
      (ENNReal.ofReal p₀) (movT_Q (periodicRiesz d R.D.s) R.D N R.ρ 0) < ⊤ := by
    rw [hprep.law_init, hQ0eq 0, R.init]
    exact lt_of_le_of_lt hinit2 ENNReal.ofReal_lt_top
  have key := H N hN P X₀ W X hMov hρt rfl
    (by rw [R.hDβ, inv_inv]; exact ⟨le_rfl, le_rfl⟩)
    (fun r hr x => (hunif r hr.1).1 x) (fun r hr => (hunif r hr.1).2) L ⟨ℓ, hℓ, hLℓ⟩ (hLi t)
    (hLlip t) (hLint t) hac hfin t ⟨ht, le_rfl⟩
  obtain ⟨hacT, hle⟩ := key
  rw [hQ0eq t] at hacT hle
  refine ⟨hacT, hle.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))⟩
  rw [hQ0eq 0, hprep.law_init, R.init, alltime_Ndelta hsd2 hN0]
  refine mul_le_mul_of_nonneg_left ?_ hC₁
  have hlog : Real.log (eLpNorm ((modulatedGibbs (periodicRiesz d R.D.s) N R.β₀
      (withDensityReal R.ρ₀)).rnDeriv (modulatedGibbs (periodicRiesz d R.D.s) N R.β
        (withDensityReal R.ρ₀))) (ENNReal.ofReal p₀) (modulatedGibbs (periodicRiesz d R.D.s) N R.β
          (withDensityReal R.ρ₀))).toReal ≤ Ci := by
    set a := eLpNorm ((modulatedGibbs (periodicRiesz d R.D.s) N R.β₀
      (withDensityReal R.ρ₀)).rnDeriv (modulatedGibbs (periodicRiesz d R.D.s) N R.β
        (withDensityReal R.ρ₀))) (ENNReal.ofReal p₀) (modulatedGibbs (periodicRiesz d R.D.s) N R.β
          (withDensityReal R.ρ₀)) with ha
    have h1 : a.toReal ≤ Real.exp Ci := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hinit2
      rwa [ENNReal.toReal_ofReal (Real.exp_pos _).le] at this
    rcases (ENNReal.toReal_nonneg (a := a)).eq_or_lt with h0 | h0
    · rw [← h0]; simpa using hCi
    · exact (Real.log_le_iff_le_exp h0).2 h1
  linarith


end Sec7

end HRS

end

end

section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Sec7

variable {d : ℕ}

theorem alltime_Lp_proof' (R : Regime d) (c : ℝ) (hc : EnvelopeConst (d := d) R.D.s c) :
    (∃ p : ℝ, 1 < p ∧ ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X₀ : Ω → Config d N)
        (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        PreparedRealization R.D P (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀))
          X₀ W X →
        ∀ t : ℝ, 0 ≤ t →
          (P.map (X t.toNNReal)) ≪ modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t)) ∧
          eLpNorm ((P.map (X t.toNNReal)).rnDeriv
              (modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t))))
            (ENNReal.ofReal p)
            (modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t))) ≤ ENNReal.ofReal C) ∧
    (∀ q : ℝ, 1 ≤ q → ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t →
      modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t)) ≪
          Measure.pi (fun _ : Fin N => withDensityReal (R.ρ t)) ∧
        eLpNorm ((modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t))).rnDeriv
            (Measure.pi (fun _ : Fin N => withDensityReal (R.ρ t)))) (ENNReal.ofReal q)
          (Measure.pi (fun _ : Fin N => withDensityReal (R.ρ t))) ≤ ENNReal.ofReal C) ∧
    (∀ B : ℝ, ∃ cB CB : ℝ, 0 < cB ∧ ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t →
      ∀ h : Torus d → Torus d → ℝ, Measurable (Function.uncurry h) → (∀ x y, h x y = h y x) →
        (∀ x y, x ≠ y → |h x y| ≤ B * (periodicRiesz d R.D.s (x - y) + c)) →
        ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (cB * N *
            |modulatedEnergy h X (withDensityReal (R.ρ t))|))
          ∂(modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t))) ≤
          ENNReal.ofReal CB) :=
  ⟨movfin_alltime_item1 R, alltime_item2 R, alltime_item3 R c hc⟩

example := (@alltime_Lp_proof' : type_of% @HRS.Sec7.alltime_Lp)

end Sec7

end HRS

end

end

section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d : ℕ}

theorem moving_log_moment_proof' (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (p₀ : ℝ) (hp₀ : 1 < p₀) :
    ∃ pInf C : ℝ, 1 < pInf ∧ 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        (∀ T : ℝ, 0 ≤ T → IsParticleSystem P htr.dyn T X₀ W X) →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        P.map X₀ ≪ modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0)) →
        eLpNorm ((P.map X₀).rnDeriv (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))))
          (ENNReal.ofReal p₀) (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) < ⊤ →
        ∀ t : ℝ, 0 ≤ t →
          P.map (X t.toNNReal) ≪ modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ t)) ∧
          eLpNorm ((P.map (X t.toNNReal)).rnDeriv
              (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ t))))
            (ENNReal.ofReal pInf) (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ t))) ≤
          ENNReal.ofReal (Real.exp (C * logMomentScale d s N p₀ (P.map X₀)
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))))) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨c₀, Λ₂, hc₀, hunif⟩ := movT_traj_uniform_proof s β V ρ₀ ρ htr.hs0 htr.hsd htr.hβ
    htr.V_smooth htr.init htr.global
  obtain ⟨Λ₁, hΛ₁, L, hLl, hLi, hLlip, hLint⟩ := MovLog.movlog_L hd htr
  obtain ⟨pInf, C₁, hp, hC₁, H⟩ := mov_lp_bound_proof hd1 htr.hs0 htr.hsd β β htr.hβ c₀ hc₀ Λ₂ p₀ hp₀ Λ₁ hΛ₁
  refine ⟨pInf, C₁, hp, hC₁, fun N hN Ω _ P _ X₀ W X hps hfilt hac hfin t ht => ?_⟩
  have hQ : ∀ r : ℝ, movT_Q (periodicRiesz d s) htr.dyn N ρ r =
      modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ r)) :=
    fun r => movT_Q_eq_beta (D := htr.dyn) (β := β) (by simp [IsSmoothPositiveTrajectory.dyn, PDE.mfData]) N ρ r
  have hMov : MovHyp P htr.dyn N t ρ X₀ W X :=
    ⟨MovLog.movlog_traj htr t, (hps t ht).brownian, (hps t ht).indep, (hps t ht).sol, hfilt⟩
  obtain ⟨ρt, hρt⟩ := (MovLog.movlog_traj htr t).classical
  obtain ⟨ℓ, hℓ, hLℓ⟩ := hLl t
  rw [← hQ 0] at hac hfin
  have key := H N hN P X₀ W X hMov hρt rfl
    (by simp [IsSmoothPositiveTrajectory.dyn, PDE.mfData])
    (fun r hr x => (hunif r hr.1).1 x) (fun r hr => (hunif r hr.1).2) L ⟨ℓ, hℓ, hLℓ⟩ (hLi t)
    (hLlip t) (hLint t) hac hfin t ⟨ht, le_rfl⟩
  rw [hQ t, hQ 0] at key
  exact key

example := (@moving_log_moment_proof' : type_of% @HRS.moving_log_moment)

end HRS

end

end

section
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace MovLog

variable {d : ℕ}

theorem movfin_movlog_pair_core (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
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
  obtain ⟨pInf, C₁, hp, hC₁, Hlog⟩ := moving_log_moment_proof' hd htr p₀ hp₀
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
    rw [← hQ 0]; exact movfin_movT_Q_isProb hN (movlog_traj htr 0) ⟨le_rfl, le_rfl⟩
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
    rw [hQdef, ← hQ t]; exact movfin_movT_Q_isProb hN (movlog_traj htr t) ⟨ht, le_rfl⟩
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

end

section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d : ℕ}

theorem moving_pair_moments_proof' (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
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
        ∀ (D : ℝ), 0 ≤ D → ∀ h : Torus d → Torus d → ℝ, Measurable (Function.uncurry h) →
          (∀ x y, h x y = h y x) →
          (∀ x y, x ≠ y → |h x y| ≤ D * (periodicRiesz d s (x - y) + cstar)) →
          ∀ t : ℝ, 0 ≤ t →
            eLpNorm (fun ω => (N : ℝ) * modulatedEnergy h (X t.toNNReal ω) (withDensityReal (ρ t)))
              (ENNReal.ofReal r) P ≤
            ENNReal.ofReal (C * D * logMomentScale d s N p₀ (P.map X₀)
              (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0)))) := by
  obtain ⟨C, hC, H⟩ := MovLog.movfin_movlog_pair_core hd htr p₀ hp₀ cstar hw r hr
  refine ⟨C, hC, fun N hN Ω _ P _ X₀ W X hps hfilt hac hfin D hD h hm hsym hdom t ht => ?_⟩
  rcases hD.eq_or_lt with h0 | hpos
  · subst h0
    set J : ℝ := logMomentScale d s N p₀ (P.map X₀)
      (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) with hJ
    have key : ∀ ε : ℝ, 0 < ε → eLpNorm (fun ω => (N : ℝ) *
        modulatedEnergy h (X t.toNNReal ω) (withDensityReal (ρ t))) (ENNReal.ofReal r) P ≤
        ENNReal.ofReal (C * ε * J) := fun ε hε =>
      H N hN P X₀ W X hps hfilt hac hfin ε hε h hm hsym (fun x y hxy => by
        have := hdom x y hxy
        have h1 := hw (x - y) (sub_ne_zero.2 hxy)
        rw [zero_mul] at this
        have h2 : 0 ≤ ε * (periodicRiesz d s (x - y) + cstar) := by nlinarith
        exact this.trans h2) t ht
    have tend : Tendsto (fun ε : ℝ => ENNReal.ofReal (C * ε * J)) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (ENNReal.ofReal (C * 0 * J))) :=
      ((ENNReal.continuous_ofReal.tendsto _).comp
        ((((continuous_const.mul continuous_id).mul continuous_const).tendsto 0))).mono_left
        nhdsWithin_le_nhds
    exact ge_of_tendsto tend (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)
  · exact H N hN P X₀ W X hps hfilt hac hfin D hpos h hm hsym hdom t ht

example := (@moving_pair_moments_proof' : type_of% @HRS.moving_pair_moments)

end HRS

end

end
