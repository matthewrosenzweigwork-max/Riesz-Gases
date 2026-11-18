import HRS.Main.EqMargU2

/-!
# EQ-MARG-U, part 3: uniform density-level bounds
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace EqMarg

open HRS.External HRS.PoleCavityAux HRS.MarginalAux

variable {d : ℕ} {s : ℝ}

theorem eqmarg_convAbs (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (Λ0 : ℝ) :
    ∃ Kg : ℝ, 0 ≤ Kg ∧ ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ0) →
      ∀ x : Torus d, ∫ y, |periodicRiesz d s (x - y)| ∂(withDensityReal ρ) ≤ Kg := by
  obtain ⟨B, Cc, hB0, hCc0, hKU⟩ := eqmarg_kerData hd hs0 hsd Λ0
  refine ⟨Cc + 2 * B, by positivity, fun ρ hρ hΛ x => ?_⟩
  have hμ := isProbabilityMeasure_mu hρ
  have hK := hKU ρ hρ hΛ
  have h1 : ∫ y, |periodicRiesz d s (x - y)| ∂(withDensityReal ρ) ≤
      ∫ y, (periodicRiesz d s (x - y) + 2 * B) ∂(withDensityReal ρ) := by
    refine integral_mono (hK.int x).abs ((hK.int x).add (integrable_const _)) fun y => ?_
    have := hK.lower (x - y)
    rcases le_total 0 (periodicRiesz d s (x - y)) with h | h
    · rw [abs_of_nonneg h]; linarith
    · rw [abs_of_nonpos h]; linarith
  rw [integral_add (hK.int x) (integrable_const _)] at h1
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h1
  have h2 := hK.conv x
  have h3 : ∫ y, periodicRiesz d s (x - y) ∂(withDensityReal ρ) ≤ Cc := (le_abs_self _).trans h2
  linarith

theorem eqmarg_uIns_abs_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) (Λ0 : ℝ) :
    ∃ Cu : ℝ, 0 ≤ Cu ∧ ∀ β : ℝ, βm ≤ β → β ≤ βp → ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ0) →
      ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d,
      |uIns (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x| ≤ Cu := by
  have hβp : 0 < βp := lt_of_lt_of_le hβm hββ
  obtain ⟨B, Cc, hB0, hCc0, hKU⟩ := eqmarg_kerData hd hs0 hsd Λ0
  obtain ⟨Kg, hKg0, hKgU⟩ := eqmarg_convAbs hd hs0 hsd Λ0
  obtain ⟨C, hC, hmargU⟩ := eqmarg_cavity_marginal_le hd hs0 hsd βm βp hβm hββ Λ0
  obtain ⟨Cd, hCdU⟩ := eqmarg_insDefect_le hd hs0 hsd βm βp hβm hββ Λ0
  obtain ⟨B', hB'0, hB'⟩ : ∃ B' : ℝ, 0 ≤ B' ∧ ∀ z : Torus d, -B' ≤ periodicRiesz d s z := rieszB hd hs0 hsd
  refine ⟨βp * Cc + βp * B' + βp * (C * Kg) + βp * Cc, by positivity,
    fun β hβ1 hβ2 ρ hρ hΛ N hN x => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβ1
  have hμ := isProbabilityMeasure_mu hρ
  have hK := hKU ρ hρ hΛ
  have hKg := hKgU ρ hρ hΛ
  have hmarg := hmargU β hβ1 hβ2 ρ hρ hΛ
  have hCd := hCdU β hβ1 hβ2 ρ hρ hΛ
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  have hln : β / N * ((N - 1 : ℕ) : ℝ) ≤ β := by
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
    have : β / N * ((N : ℝ) - 1) = β - β / N := by field_simp
    rw [this]; linarith
  haveI := cavity_isProb hd hs0 hsd β hρ (N - 1) (β / N) hlam
  set lam : ℝ := β / N with hlamdef
  set n : ℕ := N - 1 with hn
  set P0 := cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β with hP0
  have hconv := hK.conv x
  have hconv' : |β * convMeasure (periodicRiesz d s) (withDensityReal ρ) x| ≤ |β| * Cc := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hconv (abs_nonneg _)
  -- upper bound of the log
  have hphi := phiIns_pos hd hs0 hsd hρ hlam hln x
  have hup : Real.log (phiIns (periodicRiesz d s) (withDensityReal ρ) n lam β x) ≤ β * B' := by
    calc _ ≤ Real.log (Real.exp (β * B')) :=
          Real.log_le_log hphi (phiIns_le_of hd hs0 hsd hρ hlam hln hB'0 hB' x)
      _ = β * B' := Real.log_exp _
  -- lower bound of the log: `D ≥ 0` and `|E S| ≤ n C Kg`
  have hD := (hCd N hN x).1
  have hS : |∫ Y, ∑ j, periodicRiesz d s (x - Y j) ∂P0| ≤ n * (C * Kg) := by
    have hint : ∀ j : Fin n, Integrable (fun Y : Config d n => periodicRiesz d s (x - Y j)) P0 :=
      fun j => integrable_coord hd hs0 hsd hβ hρ hN x j
    rw [integral_finsetSum _ fun j _ => hint j]
    calc |∑ j, ∫ Y, periodicRiesz d s (x - Y j) ∂P0| ≤ ∑ j, |∫ Y, periodicRiesz d s (x - Y j) ∂P0| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin n, (C * Kg) := Finset.sum_le_sum fun j _ => by
          have h1 : |∫ Y, periodicRiesz d s (x - Y j) ∂P0| ≤ ∫ Y, |periodicRiesz d s (x - Y j)| ∂P0 :=
            abs_integral_le_integral_abs
          refine h1.trans ?_
          have hmeas : Measurable fun y : Torus d => |periodicRiesz d s (x - y)| :=
            (measurable_periodicRiesz hd hs0 hsd |>.comp (measurable_const.sub measurable_id)).abs
          have h2 : ∫ Y, |periodicRiesz d s (x - Y j)| ∂P0 = ∫ y, |periodicRiesz d s (x - y)| ∂(P0.map fun Y : Config d n => Y j) := by
            rw [integral_map (measurable_pi_apply j).aemeasurable hmeas.aestronglyMeasurable]
          rw [h2]
          have h3 : ∫ y, |periodicRiesz d s (x - y)| ∂(P0.map fun Y : Config d n => Y j) ≤
              ∫ y, |periodicRiesz d s (x - y)| ∂(ENNReal.ofReal C • withDensityReal ρ) :=
            integral_mono_measure (hmarg N hN j) (Filter.Eventually.of_forall fun y => abs_nonneg _)
              (((hK.int x).abs).smul_measure ENNReal.ofReal_ne_top)
          refine h3.trans ?_
          rw [integral_smul_measure, ENNReal.toReal_ofReal hC.le, smul_eq_mul]
          exact mul_le_mul_of_nonneg_left (hKg x) hC.le
      _ = n * (C * Kg) := by simp
  have hlow : -(β * (C * Kg)) ≤ Real.log (phiIns (periodicRiesz d s) (withDensityReal ρ) n lam β x) := by
    have h1 : 0 ≤ Real.log (phiIns (periodicRiesz d s) (withDensityReal ρ) n lam β x) +
        lam * ∫ Y, ∑ j, periodicRiesz d s (x - Y j) ∂P0 := hD
    have h2 : lam * ∫ Y, ∑ j, periodicRiesz d s (x - Y j) ∂P0 ≤ lam * (n * (C * Kg)) :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans hS) hlam
    have h3 : lam * (n * (C * Kg)) ≤ β * (C * Kg) := by
      have : lam * (n * (C * Kg)) = (lam * n) * (C * Kg) := by ring
      rw [this]; exact mul_le_mul_of_nonneg_right hln (by positivity)
    linarith
  unfold uIns
  rw [abs_le]
  have h4 := neg_abs_le (β * convMeasure (periodicRiesz d s) (withDensityReal ρ) x)
  have h5 := le_abs_self (β * convMeasure (periodicRiesz d s) (withDensityReal ρ) x)
  have q1 : β * B' ≤ βp * B' := mul_le_mul_of_nonneg_right hβ2 hB'0
  have q2 : β * (C * Kg) ≤ βp * (C * Kg) := mul_le_mul_of_nonneg_right hβ2 (by positivity)
  have q3 : |β| * Cc ≤ βp * Cc := by
    rw [abs_of_pos hβ]; exact mul_le_mul_of_nonneg_right hβ2 hCc0
  have p1 : 0 ≤ βp * B' := by positivity
  have p3 : 0 ≤ βp * Cc := by positivity
  have p2 : 0 ≤ βp * (C * Kg) := by positivity
  constructor <;> linarith [hconv', hup, hlow, h4, h5, q1, q2, q3, p1, p2, p3]

theorem eqmarg_pDens_bounds (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) (Λ0 : ℝ) :
    ∃ Mp : ℝ, 1 ≤ Mp ∧ ∀ β : ℝ, βm ≤ β → β ≤ βp → ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ0) →
      ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d,
      Real.exp (-Mp) ≤ pDens (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x ∧
      pDens (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x ≤ Mp := by
  obtain ⟨Cu, hCu0, hCuU⟩ := eqmarg_uIns_abs_le hd hs0 hsd βm βp hβm hββ Λ0
  refine ⟨Real.exp (2 * Cu), Real.one_le_exp (by positivity), fun β hβ1 hβ2 ρ hρ hΛ N hN x => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβ1
  have hμ := isProbabilityMeasure_mu hρ
  have hCu := hCuU β hβ1 hβ2 ρ hρ hΛ
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  have hln : β / N * ((N - 1 : ℕ) : ℝ) ≤ β := by
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
    have : β / N * ((N : ℝ) - 1) = β - β / N := by field_simp
    rw [this]; linarith
  have hum := measurable_uIns hd hs0 hsd hρ hlam hln
  set u := uIns (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β with hu
  have hint : Integrable (fun y => Real.exp (u y)) (withDensityReal ρ) :=
    Integrable.of_bound (C := Real.exp Cu) (Real.measurable_exp.comp hum).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 ((le_abs_self _).trans (hCu N hN y)))
  have hZ1 : Real.exp (-Cu) ≤ ∫ y, Real.exp (u y) ∂(withDensityReal ρ) := by
    have := integral_mono (integrable_const (Real.exp (-Cu))) hint (fun y =>
      Real.exp_le_exp.2 (neg_le_of_abs_le (hCu N hN y)))
    simpa using this
  have hZ2 : ∫ y, Real.exp (u y) ∂(withDensityReal ρ) ≤ Real.exp Cu := by
    have := integral_mono hint (integrable_const (Real.exp Cu)) (fun y =>
      Real.exp_le_exp.2 ((le_abs_self _).trans (hCu N hN y)))
    simpa using this
  have hZpos : 0 < ∫ y, Real.exp (u y) ∂(withDensityReal ρ) := integral_exp_pos hint
  have hc1 : -Cu ≤ Real.log (∫ y, Real.exp (u y) ∂(withDensityReal ρ)) := by
    calc -Cu = Real.log (Real.exp (-Cu)) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) hZ1
  have hc2 : Real.log (∫ y, Real.exp (u y) ∂(withDensityReal ρ)) ≤ Cu := by
    calc _ ≤ Real.log (Real.exp Cu) := Real.log_le_log hZpos hZ2
      _ = Cu := Real.log_exp _
  have hux := abs_le.1 (hCu N hN x)
  unfold pDens
  constructor
  · refine Real.exp_le_exp.2 ?_
    have : 2 * Cu ≤ Real.exp (2 * Cu) := by linarith [Real.add_one_le_exp (2 * Cu)]
    linarith
  · exact Real.exp_le_exp.2 (by linarith)

theorem eqmarg_qDens_bound (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) (Λ0 : ℝ) :
    ∃ Mq : ℝ, 0 < Mq ∧ ∀ β : ℝ, βm ≤ β → β ≤ βp → ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ0) →
      ∀ N : ℕ, 2 ≤ N →
    (firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β)) ≪ withDensityReal ρ ∧
    ∀ᵐ x ∂(withDensityReal ρ),
      qDens (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x ≤ Mq := by
  obtain ⟨C, hC, hmargU⟩ := eqmarg_cavity_marginal_le hd hs0 hsd βm βp hβm hββ Λ0
  refine ⟨C, hC, fun β hβ1 hβ2 ρ hρ hΛ N hN => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβ1
  have hμ := isProbabilityMeasure_mu hρ
  have hmarg := hmargU β hβ1 hβ2 ρ hρ hΛ
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  haveI := cavity_isProb hd hs0 hsd β hρ (N - 1) (β / N) hlam
  have hn1 : 0 < N - 1 := by omega
  have hfm : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β) =
      (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β).map
        (fun Y : Config d (N - 1) => Y ⟨0, hn1⟩) := by
    unfold firstMarginal; rw [dif_pos hn1]
  have h1 := hmarg N hN ⟨0, hn1⟩
  haveI : IsProbabilityMeasure (firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β)) := by
    rw [hfm]; infer_instance
  rw [← hfm, ← withDensity_const] at h1
  obtain ⟨hac, hle⟩ := rnDeriv_le_of_le_withDensity (withDensityReal ρ) _ _ h1
  refine ⟨hac, ?_⟩
  filter_upwards [hle] with x hx
  unfold qDens
  exact ENNReal.toReal_le_of_le_ofReal hC.le hx

theorem eqmarg_kt_pq_L2 (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) (Λ0 : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β : ℝ, βm ≤ β → β ≤ βp → ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ0) →
      ∀ n : ℕ, 0 < n → ∀ lam : ℝ, lam = β / ((n + 1 : ℕ) : ℝ) →
      ∫⁻ x, ENNReal.ofReal ((ResponseAux.Kt (periodicRiesz d s) (withDensityReal ρ)
          (fun y => pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y -
            qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y) x) ^ 2) ∂(withDensityReal ρ) ≤
        ENNReal.ofReal (C * deltaN d s (n + 1)) ^ 2 := by
  obtain ⟨Mp, hMp1, hMpU⟩ := eqmarg_pDens_bounds hd hs0 hsd βm βp hβm hββ Λ0
  obtain ⟨Mq, hMq0, hMqU⟩ := eqmarg_qDens_bound hd hs0 hsd βm βp hβm hββ Λ0
  obtain ⟨Ctv, hCtv0, hCtvU⟩ := eqmarg_cavity_tv hd hs0 hsd βm βp hβm hββ Λ0
  set Λ : ℝ := max Λ0 1 with hΛdef
  have hΛ0 : 0 < Λ := lt_max_of_lt_right one_pos
  obtain ⟨Cc, hCc0, hCc⟩ := conv_L2 hd hs0 hsd ((Mp + Mq) * Λ) (2 * Ctv) (by positivity) (by positivity)
  have hgm := measurable_periodicRiesz hd hs0 hsd
  refine ⟨Real.sqrt Λ * Cc, by positivity, fun β hβ1 hβ2 ρ hρ hΛρ n hn lam hlamdef => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβ1
  have hμ := isProbabilityMeasure_mu hρ
  have hΛ : ∀ x, ρ x ≤ Λ := fun x => (hΛρ x).trans (le_max_left _ _)
  have hMp := hMpU β hβ1 hβ2 ρ hρ hΛρ
  have hMq := hMqU β hβ1 hβ2 ρ hρ hΛρ
  have hCtv := hCtvU β hβ1 hβ2 ρ hρ hΛρ
  obtain ⟨hlam, hln, -⟩ := lam_facts hd hs0 hsd hβ hρ hn hlamdef
  have hN : 2 ≤ n + 1 := by omega
  have hN0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hpm := measurable_pDens hd hs0 hsd hρ hlam hln
  have hqm := qDens_measurable hd hs0 hsd hβ hρ hn hlamdef
  have hacq := (hMq (n + 1) hN)
  have hlam' : lam = β / ((n + 1 : ℕ) : ℝ) := hlamdef
  have hac : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) ≪ withDensityReal ρ := by
    subst hlam'; exact hacq.1
  have hqb : ∀ᵐ y ∂(withDensityReal ρ), qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mq := by
    subst hlam'; exact hacq.2
  have hpb : ∀ y, pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mp := by
    subst hlam'; exact fun y => (hMp (n + 1) hN y).2
  have hTV : ∀ A : Set (Torus d), MeasurableSet A →
      |(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (n + 1) lam β) A).toReal -
        (firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) A).toReal| ≤
        Ctv * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) := by
    intro A hA
    subst hlam'
    exact hCtv (n + 1) hN A hA
  have hl1 := l1_pq hd hs0 hsd hβ hρ hn hlamdef hac hTV hpb
  obtain ⟨hqi, hq1⟩ := integral_qDens hd hs0 hsd hβ hρ hn hlamdef hac
  set p := pDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hp
  set q := qDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hq
  set μ := withDensityReal ρ with hμdef
  set qb : Torus d → ℝ := fun y => min (q y) Mq with hqbdef
  have hqbm : Measurable qb := hqm.min measurable_const
  have hq0 : ∀ y, 0 ≤ q y := fun y => ENNReal.toReal_nonneg
  have hqbq : q =ᵐ[μ] qb := hqb.mono fun y hy => by simp only [hqbdef, min_eq_left hy]
  have hqb0 : ∀ y, 0 ≤ qb y := fun y => le_min (hq0 y) hMq0.le
  have hqbM : ∀ y, qb y ≤ Mq := fun y => min_le_right _ _
  set f : Torus d → ℝ := fun y => ρ y * (p y - qb y) with hf
  have hρm : Measurable ρ := hρ.density.measurable
  have hfm : Measurable f := hρm.mul (hpm.sub hqbm)
  have hfb : ∀ y, |f y| ≤ (Mp + Mq) * Λ := by
    intro y
    have h1 : |p y - qb y| ≤ Mp + Mq := by
      have := pDens_pos hd hs0 hsd hρ hlam hln y
      rw [abs_le]; constructor <;> linarith [hpb y, hqb0 y, hqbM y]
    have h2 : |ρ y| ≤ Λ := by rw [abs_of_pos (hρ.pos y)]; exact hΛ y
    rw [abs_mul, mul_comm]
    exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  -- the `L¹` norm of `f`
  have hpi : Integrable p μ := Integrable.of_bound (C := Mp) hpm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (pDens_pos hd hs0 hsd hρ hlam hln y)]; exact hpb y)
  have hl1f : ∫⁻ y, ‖f y‖ₑ ≤ ENNReal.ofReal (2 * Ctv * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ))) := by
    have e1 : ∀ y, ‖f y‖ₑ = ENNReal.ofReal (ρ y) * ‖p y - qb y‖ₑ := by
      intro y
      simp only [hf, enorm_mul, Real.enorm_of_nonneg (hρ.density.nonneg y)]
    simp_rw [e1]
    have hmρ : Measurable fun y => ENNReal.ofReal (ρ y) := ENNReal.measurable_ofReal.comp hρm
    have e2 : ∫⁻ y, ENNReal.ofReal (ρ y) * ‖p y - qb y‖ₑ = ∫⁻ y, ‖p y - qb y‖ₑ ∂μ := by
      show _ = ∫⁻ y, ‖p y - qb y‖ₑ ∂(volume.withDensity fun x => ENNReal.ofReal (ρ x))
      have hgm' : Measurable fun y => ‖p y - qb y‖ₑ := (hpm.sub hqbm).enorm
      rw [lintegral_withDensity_eq_lintegral_mul _ hmρ hgm']
      rfl
    rw [e2]
    have hdiff : Integrable (fun y => p y - qb y) μ :=
      hpi.sub (Integrable.of_bound (C := Mq) hqbm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hqb0 y)]; exact hqbM y))
    have e3 : ∫⁻ y, ‖p y - qb y‖ₑ ∂μ = ENNReal.ofReal (∫ y, |p y - qb y| ∂μ) := by
      rw [ofReal_integral_eq_lintegral_ofReal hdiff.abs (Filter.Eventually.of_forall fun y => abs_nonneg _)]
      refine lintegral_congr fun y => ?_
      rw [Real.enorm_eq_ofReal_abs]
    rw [e3]
    refine ENNReal.ofReal_le_ofReal ?_
    have e4 : ∫ y, |p y - qb y| ∂μ = ∫ y, |p y - q y| ∂μ := by
      refine integral_congr_ae (hqbq.mono fun y hy => ?_)
      simp only [← hy]
    rw [e4]; exact hl1.trans (le_of_eq (by ring))
  have hcv := hCc (n + 1) hN f hfm hfb hl1f
  -- pointwise comparison
  have hae : (fun y => p y - q y) =ᵐ[μ] fun y => p y - qb y :=
    hqbq.mono fun y hy => by simp only [← hy]
  have hKt : ResponseAux.Kt (periodicRiesz d s) μ (fun y => p y - q y) =
      ResponseAux.cv (periodicRiesz d s) f := by
    rw [ResponseAux.Kt_congr _ hae, ResponseAux.Kt_eq_cv hρ.density]
  have hpt : ∀ x : Torus d, ENNReal.ofReal ((ResponseAux.Kt (periodicRiesz d s) μ (fun y => p y - q y) x) ^ 2) ≤
      (∫⁻ y, ‖periodicRiesz d s (x - y)‖ₑ * ‖f y‖ₑ) ^ 2 := by
    intro x
    rw [hKt]
    unfold ResponseAux.cv
    have h1 : ENNReal.ofReal ((∫ y, periodicRiesz d s (x - y) * f y) ^ 2) = ‖∫ y, periodicRiesz d s (x - y) * f y‖ₑ ^ 2 := by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    rw [h1]
    gcongr
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun y => ?_
    rw [enorm_mul]
  calc ∫⁻ x, ENNReal.ofReal ((ResponseAux.Kt (periodicRiesz d s) μ (fun y => p y - q y) x) ^ 2) ∂μ
      ≤ ∫⁻ x, (∫⁻ y, ‖periodicRiesz d s (x - y)‖ₑ * ‖f y‖ₑ) ^ 2 ∂μ := lintegral_mono hpt
    _ ≤ ∫⁻ x, (∫⁻ y, ‖periodicRiesz d s (x - y)‖ₑ * ‖f y‖ₑ) ^ 2 ∂(ENNReal.ofReal Λ • (volume : Measure (Torus d))) :=
        lintegral_mono' (KernelAux2.withDensityReal_le ρ Λ hΛ) le_rfl
    _ = ENNReal.ofReal Λ * ∫⁻ x, (∫⁻ y, ‖periodicRiesz d s (x - y)‖ₑ * ‖f y‖ₑ) ^ 2 := by
        rw [lintegral_smul_measure, smul_eq_mul]
    _ ≤ ENNReal.ofReal Λ * ENNReal.ofReal ((Cc * deltaN d s (n + 1)) ^ 2) := by gcongr
    _ = ENNReal.ofReal (Real.sqrt Λ * Cc * deltaN d s (n + 1)) ^ 2 := by
        rw [← ENNReal.ofReal_mul hΛ0.le, ← ENNReal.ofReal_pow (by
          have : 0 ≤ deltaN d s (n + 1) := by
            have := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
            exact (inv_nonneg.2 hN0.le).trans this
          positivity)]
        congr 1
        have : (Real.sqrt Λ) ^ 2 = Λ := Real.sq_sqrt hΛ0.le
        nlinarith [this]

theorem eqmarg_w_L2 (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) (Λ0 : ℝ) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ β : ℝ, βm ≤ β → β ≤ βp → ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ0) →
      ∀ n : ℕ, 0 < n → ∀ lam : ℝ, lam = β / ((n + 1 : ℕ) : ℝ) →
      Integrable (fun x => (eFun (periodicRiesz d s) (withDensityReal ρ) n lam β x +
          insDefect (periodicRiesz d s) (withDensityReal ρ) n lam β x) ^ 2) (withDensityReal ρ) ∧
      ∫ x, (eFun (periodicRiesz d s) (withDensityReal ρ) n lam β x +
          insDefect (periodicRiesz d s) (withDensityReal ρ) n lam β x) ^ 2 ∂(withDensityReal ρ) ≤
        (Cw * deltaN d s (n + 1)) ^ 2 := by
  have hβp : 0 < βp := lt_of_lt_of_le hβm hββ
  obtain ⟨Ca, hCa0, hKtU⟩ := eqmarg_kt_pq_L2 hd hs0 hsd βm βp hβm hββ Λ0
  obtain ⟨Mq, hMq0, hMqU⟩ := eqmarg_qDens_bound hd hs0 hsd βm βp hβm hββ Λ0
  obtain ⟨Kg, hKg0, hKgU⟩ := eqmarg_convAbs hd hs0 hsd Λ0
  obtain ⟨Cd, hCdU⟩ := eqmarg_insDefect_le hd hs0 hsd βm βp hβm hββ Λ0
  have hgm := measurable_periodicRiesz hd hs0 hsd
  refine ⟨Real.sqrt (3 * βp ^ 2 * Ca ^ 2 + 3 * βp ^ 2 * (Mq ^ 2 * Kg ^ 2) + 3 * Cd ^ 2), Real.sqrt_nonneg _,
    fun β hβ1 hβ2 ρ hρ hΛ n hn lam hlamdef => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβ1
  have hμ := isProbabilityMeasure_mu hρ
  have hKt := hKtU β hβ1 hβ2 ρ hρ hΛ
  have hMq := hMqU β hβ1 hβ2 ρ hρ hΛ
  have hKg := hKgU ρ hρ hΛ
  have hCd := hCdU β hβ1 hβ2 ρ hρ hΛ
  obtain ⟨hlam, hln, hlam1⟩ := lam_facts hd hs0 hsd hβ hρ hn hlamdef
  have hN : 2 ≤ n + 1 := by omega
  have hN0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hlam' : lam = β / ((n + 1 : ℕ) : ℝ) := hlamdef
  have hacq := (hMq (n + 1) hN)
  have hac : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) ≪ withDensityReal ρ := by
    subst hlam'; exact hacq.1
  have hqb : ∀ᵐ y ∂(withDensityReal ρ), qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mq := by
    subst hlam'; exact hacq.2
  have hpm := measurable_pDens hd hs0 hsd hρ hlam hln
  have hqm := qDens_measurable hd hs0 hsd hβ hρ hn hlamdef
  have hδ0 : 0 ≤ deltaN d s (n + 1) := by
    have := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
    exact (inv_nonneg.2 hN0.le).trans this
  have hlamδ : lam ≤ β * deltaN d s (n + 1) := by
    have := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
    rw [hlam', div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left this hβ.le
  have hlamP : lam ≤ βp * deltaN d s (n + 1) := hlamδ.trans (mul_le_mul_of_nonneg_right hβ2 hδ0)
  set p := pDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hp
  set q := qDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hq
  set μ := withDensityReal ρ with hμdef
  set a : Torus d → ℝ := ResponseAux.Kt (periodicRiesz d s) μ (fun y => p y - q y) with ha
  set bq : Torus d → ℝ := ResponseAux.Kt (periodicRiesz d s) μ q with hbq
  set D : Torus d → ℝ := insDefect (periodicRiesz d s) μ n lam β with hD
  have ham : Measurable a := measurable_Kt hd hs0 hsd hβ hρ (hpm.sub hqm)
  have hbm : Measurable bq := measurable_Kt hd hs0 hsd hβ hρ hqm
  have hDm : Measurable D := by
    haveI := cavity_isProb hd hs0 hsd β hρ n lam hlam
    have hSm : Measurable fun x : Torus d => ∫ Y, ∑ j, periodicRiesz d s (x - Y j)
        ∂(cavityLaw (periodicRiesz d s) μ n lam β) := by
      have : StronglyMeasurable (Function.uncurry fun (x : Torus d) (Y : Config d n) =>
          ∑ j, periodicRiesz d s (x - Y j)) :=
        (Finset.measurable_sum _ fun j _ =>
          hgm.comp (measurable_fst.sub ((measurable_pi_apply j).comp measurable_snd))).stronglyMeasurable
      exact (this.integral_prod_right' (ν := cavityLaw (periodicRiesz d s) μ n lam β)).measurable
    rw [hD]; unfold insDefect
    exact (Real.measurable_log.comp (measurable_phiIns hd hs0 hsd hρ hlam hln)).add (hSm.const_mul _)
  have hA : Integrable (fun x => a x ^ 2) μ ∧ ∫ x, a x ^ 2 ∂μ ≤ (Ca * deltaN d s (n + 1)) ^ 2 := by
    refine integral_sq_le_of_lintegral ham (by positivity) ?_
    have := hKt n hn lam hlamdef
    rw [← ENNReal.ofReal_pow (by positivity)] at this
    exact this
  -- bounds on `bq` and `D`
  have hbb : ∀ x, |bq x| ≤ Mq * Kg := by
    intro x
    obtain ⟨B, Cc, hB0, hK⟩ := kerData_periodicRiesz hd hs0 hsd hρ
    have hgi := hK.int x
    have hqint : Integrable (fun y => periodicRiesz d s (x - y) * q y) μ :=
      hgi.mul_bdd hqm.aestronglyMeasurable (c := Mq) (hqb.mono fun y hy => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by simp only [hq, qDens]; exact ENNReal.toReal_nonneg)]; exact hy)
    show |∫ y, periodicRiesz d s (x - y) * q y ∂μ| ≤ Mq * Kg
    refine (abs_integral_le_integral_abs).trans ?_
    have hmeas : Measurable fun y : Torus d => |periodicRiesz d s (x - y)| :=
      (hgm.comp (measurable_const.sub measurable_id)).abs
    calc ∫ y, |periodicRiesz d s (x - y) * q y| ∂μ ≤ ∫ y, Mq * |periodicRiesz d s (x - y)| ∂μ := by
          refine integral_mono_ae hqint.abs ((hgi.abs).const_mul _) (hqb.mono fun y hy => ?_)
          show |periodicRiesz d s (x - y) * q y| ≤ Mq * |periodicRiesz d s (x - y)|
          rw [abs_mul, abs_of_nonneg (by simp only [hq, qDens]; exact ENNReal.toReal_nonneg : 0 ≤ q y)]
          nlinarith [abs_nonneg (periodicRiesz d s (x - y))]
      _ = Mq * ∫ y, |periodicRiesz d s (x - y)| ∂μ := integral_const_mul _ _
      _ ≤ Mq * Kg := mul_le_mul_of_nonneg_left (hKg x) hMq0.le
  have hDb : ∀ x, 0 ≤ D x ∧ D x ≤ Cd * deltaN d s (n + 1) := by
    intro x
    have := hCd (n + 1) hN x
    rw [← hlam'] at this
    exact ⟨this.1, this.2.1⟩
  -- pointwise bound
  set K : ℝ := 3 * ((βp * deltaN d s (n + 1) * (Mq * Kg)) ^ 2 + (Cd * deltaN d s (n + 1)) ^ 2) with hK
  have hpt : ∀ x, (β * a x + lam * bq x + D x) ^ 2 ≤ 3 * βp ^ 2 * a x ^ 2 + K := by
    intro x
    have h1 : (lam * bq x) ^ 2 ≤ (βp * deltaN d s (n + 1) * (Mq * Kg)) ^ 2 := by
      have h2 : |lam * bq x| ≤ βp * deltaN d s (n + 1) * (Mq * Kg) := by
        rw [abs_mul, abs_of_nonneg hlam]
        exact mul_le_mul hlamP (hbb x) (abs_nonneg _) (by positivity)
      calc (lam * bq x) ^ 2 = |lam * bq x| ^ 2 := (sq_abs _).symm
        _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) h2 2
    have h3 : D x ^ 2 ≤ (Cd * deltaN d s (n + 1)) ^ 2 :=
      pow_le_pow_left₀ (hDb x).1 (hDb x).2 2
    have h4 : (β * a x) ^ 2 ≤ βp ^ 2 * a x ^ 2 := by
      have := pow_le_pow_left₀ hβ.le hβ2 2
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    nlinarith [sq_nonneg (β * a x - lam * bq x), sq_nonneg (β * a x - D x), sq_nonneg (lam * bq x - D x)]
  have hmeasw : Measurable fun x => (β * a x + lam * bq x + D x) ^ 2 :=
    (((ham.const_mul β).add (hbm.const_mul lam)).add hDm).pow_const 2
  have hdom : Integrable (fun x => 3 * βp ^ 2 * a x ^ 2 + K) μ :=
    (hA.1.const_mul _).add (integrable_const _)
  have hI : Integrable (fun x => (β * a x + lam * bq x + D x) ^ 2) μ :=
    Integrable.mono' hdom hmeasw.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpt x)
  have hI2 : ∫ x, (β * a x + lam * bq x + D x) ^ 2 ∂μ ≤ 3 * βp ^ 2 * (Ca * deltaN d s (n + 1)) ^ 2 + K := by
    calc ∫ x, (β * a x + lam * bq x + D x) ^ 2 ∂μ ≤ ∫ x, (3 * βp ^ 2 * a x ^ 2 + K) ∂μ :=
          integral_mono hI hdom hpt
      _ = 3 * βp ^ 2 * ∫ x, a x ^ 2 ∂μ + K := by
          rw [integral_add (hA.1.const_mul _) (integrable_const _), integral_const_mul]
          simp
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left hA.2 (by positivity : 0 ≤ 3 * βp ^ 2)
          linarith
  refine ⟨?_, ?_⟩
  · exact hI
  · refine hI2.trans (le_of_eq ?_)
    have hsq : (Real.sqrt (3 * βp ^ 2 * Ca ^ 2 + 3 * βp ^ 2 * (Mq ^ 2 * Kg ^ 2) + 3 * Cd ^ 2) *
        deltaN d s (n + 1)) ^ 2 = (3 * βp ^ 2 * Ca ^ 2 + 3 * βp ^ 2 * (Mq ^ 2 * Kg ^ 2) + 3 * Cd ^ 2) *
          deltaN d s (n + 1) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    rw [hsq, hK]
    ring

end EqMarg

end HRS
