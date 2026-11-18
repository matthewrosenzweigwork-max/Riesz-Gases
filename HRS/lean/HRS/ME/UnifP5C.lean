import HRS.ME.UnifP5B

/-!
# Uniform Lemma 4.6 (cavity response), part C (packet P5)

Uniform `response_bound` (`HRS/Equilibrium/CavityResponse.lean`): the `L²(μ)` bound of the residual of the
linearised response equation for the density `p_n`, with a constant chosen after `d, s, βm, βp, Λ, c` and
before `β ∈ [βm, βp]` and the smooth density `ρ ≤ Λ` (`1 ≤ Λ`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.ME.Unif

open HRS HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp

variable {d : ℕ} {s c : ℝ}

set_option maxHeartbeats 1600000 in
/-- Uniform `response_bound`. -/
theorem response_bound_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (Λ : ℝ) (hΛ1 : 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ n : ℕ, 0 < n → ∀ lam : ℝ, lam = β / ((n + 1 : ℕ) : ℝ) →
      MemLp (fun x => (pDens (periodicRiesz d s) (withDensityReal ρ) n lam β x - 1) +
          β * Kop (periodicRiesz d s) (withDensityReal ρ)
            (fun y => pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y - 1) x -
          projMean (withDensityReal ρ)
            (insDefect (periodicRiesz d s) (withDensityReal ρ) n lam β) x) 2 (withDensityReal ρ) ∧
      Real.sqrt (∫ x, ((pDens (periodicRiesz d s) (withDensityReal ρ) n lam β x - 1) +
          β * Kop (periodicRiesz d s) (withDensityReal ρ)
            (fun y => pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y - 1) x -
          projMean (withDensityReal ρ)
            (insDefect (periodicRiesz d s) (withDensityReal ρ) n lam β) x) ^ 2
          ∂(withDensityReal ρ)) ≤
        C * (deltaN d s (n + 1) * Real.sqrt (deltaN d s (n + 1)) +
          Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) + 1 / ((n + 1 : ℕ) : ℝ)) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨Mp, hMp1, hMpU⟩ := pDens_bounds_unif hd hs0 hsd βm βp hβm hββ Λ
  obtain ⟨Mq, hMq0, hMqU⟩ := qDens_bound_unif hd hs0 hsd βm βp hβm hββ Λ
  obtain ⟨Kg, hKg0, hKgU⟩ := convAbs_bound_unif hd hs0 hsd Λ
  obtain ⟨C2, hC20, hC2U⟩ := L2_all_unif hd hs0 hsd βm βp hβm hββ Λ
  obtain ⟨CL, hCL0, hCLU⟩ := cavity_L2_unif hd hs0 hsd βm βp hβm hββ Λ
  obtain ⟨CS, hCS0, hCSU⟩ := Kt_L2_real_unif hd hcrit hc Λ hΛ1
  obtain ⟨Rr, hRr0, hRrU⟩ := sup_dev_rate_unif hd hcrit βm βp hβm hββ c hc Λ hΛ1
  obtain ⟨Cd, hCdU⟩ := insDefect_le_unif hd hs0 hsd βm βp hβm hββ Λ
  obtain ⟨B, Cck, hB0, hKU⟩ := NfU.kerData_periodicRiesz_unif hd hs0 hsd Λ
  have hgm := measurable_periodicRiesz hd hs0 hsd
  have hβp : 0 ≤ βp := hβm.le.trans hββ
  refine ⟨Real.exp Mp * Rr * C2 + βp * Real.sqrt CS * CL + βp * (Kg * Mq), by positivity, ?_⟩
  intro β hβI ρ hρ hΛ n hn lam hlamdef
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hμ := isProbabilityMeasure_mu hρ
  have hMp := hMpU β hβI ρ hρ hΛ
  have hMq := hMqU β hβI ρ hρ hΛ
  have hKg := hKgU ρ hρ hΛ
  have hC2 := hC2U β hβI ρ hρ hΛ
  have hCL := hCLU β hβI ρ hρ hΛ
  have hCS := hCSU ρ hρ hΛ
  have hRr := hRrU β hβI ρ hρ hΛ
  have hCd := hCdU β hβI ρ hρ hΛ
  have hK := hKU ρ hρ hΛ
  obtain ⟨hlam, hln, hlam1⟩ := lam_facts hd hs0 hsd hβ hρ hn hlamdef
  have hN : 2 ≤ n + 1 := by omega
  have hN0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hlam' : lam = β / ((n + 1 : ℕ) : ℝ) := hlamdef
  have hδ0 : 0 ≤ deltaN d s (n + 1) := by
    have := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
    exact (inv_nonneg.2 hN0.le).trans this
  have hacq := hMq (n + 1) hN
  have hac : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) ≪
      withDensityReal ρ := by
    subst hlam'; exact hacq.1
  have hqb : ∀ᵐ y ∂(withDensityReal ρ), qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mq := by
    subst hlam'; exact hacq.2
  have hpb : ∀ y, pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mp := by
    subst hlam'; exact fun y => (hMp (n + 1) hN y).2
  have hplow : ∀ y, Real.exp (-Mp) ≤ pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y := by
    subst hlam'; exact fun y => (hMp (n + 1) hN y).1
  have hpm := measurable_pDens hd hs0 hsd hρ hlam hln
  have hqm := qDens_measurable hd hs0 hsd hβ hρ hn hlamdef
  have hp1 := integral_pDens hd hs0 hsd hρ hlam hln
  have hcav := fun x => cavity_eq_z hd hs0 hsd hβ hρ hn hlamdef hac hpb hqb x
  set p := pDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hp
  set q := qDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hq
  set μ := withDensityReal ρ with hμdef
  set D := insDefect (periodicRiesz d s) μ n lam β with hD
  set Z0 : ℝ := ∫ y, Real.exp (uIns (periodicRiesz d s) μ n lam β y) ∂μ with hZ0
  have hp0 : ∀ y, 0 < p y := pDens_pos hd hs0 hsd hρ hlam hln
  have hq0 : ∀ y, 0 ≤ q y := fun y => ENNReal.toReal_nonneg
  set qb : Torus d → ℝ := fun y => min (q y) Mq with hqbdef
  have hqbm : Measurable qb := hqm.min measurable_const
  have hqbq : q =ᵐ[μ] qb := hqb.mono fun y hy => by simp only [hqbdef, min_eq_left hy]
  have hqb0 : ∀ y, 0 ≤ qb y := fun y => le_min (hq0 y) hMq0.le
  have hqbM : ∀ y, qb y ≤ Mq := fun y => min_le_right _ _
  set z : Torus d → ℝ := fun y => p y - 1 with hz
  have hzm : Measurable z := hpm.sub measurable_const
  have hzb : ∀ y, |z y| ≤ Mp := fun y => by
    rw [abs_le]; constructor <;> linarith [hp0 y, hpb y]
  have hRsup : ∀ y, |z y| ≤ Rr * Real.sqrt (deltaN d s (n + 1)) := fun y => hRr n hn lam hlamdef y
  have hgi := hK.int
  have hKgabs : ∀ x : Torus d, ∫ y, |periodicRiesz d s (x - y)| ∂μ ≤ Kg := hKg
  -- the three convolutions
  set Kz : Torus d → ℝ := ResponseAux.Kt (periodicRiesz d s) μ z with hKz
  set Kpq : Torus d → ℝ := ResponseAux.Kt (periodicRiesz d s) μ (fun y => p y - qb y) with hKpq
  set Kq : Torus d → ℝ := ResponseAux.Kt (periodicRiesz d s) μ qb with hKq
  have hKzm : Measurable Kz := measurable_Kt hd hs0 hsd hβ hρ hzm
  have hKpqm : Measurable Kpq := measurable_Kt hd hs0 hsd hβ hρ (hpm.sub hqbm)
  have hKqm : Measurable Kq := measurable_Kt hd hs0 hsd hβ hρ hqbm
  have hpqb : ∀ y, |p y - qb y| ≤ Mp + Mq := fun y => by
    rw [abs_le]; constructor <;> linarith [hp0 y, hpb y, hqb0 y, hqbM y]
  have hqbb : ∀ y, |qb y| ≤ Mq := fun y => by rw [abs_of_nonneg (hqb0 y)]; exact hqbM y
  have hKzb : ∀ x, |Kz x| ≤ Mp * Kg := fun x => Kt_bdd hgi hKgabs hzb hzm x
  have hKpqb : ∀ x, |Kpq x| ≤ (Mp + Mq) * Kg := fun x => Kt_bdd hgi hKgabs hpqb (hpm.sub hqbm) x
  have hKqb : ∀ x, |Kq x| ≤ Mq * Kg := fun x => Kt_bdd hgi hKgabs hqbb hqbm x
  have hKpq_eq : ResponseAux.Kt (periodicRiesz d s) μ (fun y => p y - q y) = Kpq :=
    ResponseAux.Kt_congr _ (hqbq.mono fun y hy => by simp only [← hy])
  have hKq_eq : ResponseAux.Kt (periodicRiesz d s) μ q = Kq :=
    ResponseAux.Kt_congr _ hqbq
  -- the cavity equation rewritten
  have hDeq : ∀ x, D x = Real.log (1 + z x) + β * Kz x - (β * Kpq x + lam * Kq x) + Real.log Z0 := by
    intro x
    have h := hcav x
    rw [hKpq_eq, hKq_eq] at h
    simp only [hz, hKz] at h ⊢
    linarith [h]
  have hbi : ∀ f : Torus d → ℝ, Measurable f → ∀ M : ℝ, (∀ x, |f x| ≤ M) → Integrable f μ :=
    fun f hf M hb => Integrable.of_bound hf.aestronglyMeasurable M
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)
  have hbm : ∀ f : Torus d → ℝ, Measurable f → ∀ M : ℝ, (∀ x, |f x| ≤ M) → MemLp f 2 μ :=
    fun f hf M hb => MemLp.of_bound hf.aestronglyMeasurable M
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)
  have hDm : Measurable D := by
    have : D = fun x => Real.log (1 + z x) + β * Kz x - (β * Kpq x + lam * Kq x) + Real.log Z0 :=
      funext hDeq
    rw [this]
    exact (((Real.measurable_log.comp (measurable_const.add hzm)).add (hKzm.const_mul β)).sub
      ((hKpqm.const_mul β).add (hKqm.const_mul lam))).add measurable_const
  have hDb : ∀ x, |D x| ≤ |Cd| * deltaN d s (n + 1) := by
    intro x
    have hD' : 0 ≤ D x ∧ D x ≤ Cd * deltaN d s (n + 1) := by
      have := hCd (n + 1) hN x
      rw [← hlam'] at this
      exact ⟨this.1, this.2.1⟩
    rw [abs_of_nonneg hD'.1]
    exact hD'.2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hδ0)
  -- the pieces `ΔL = z - log (1 + z)` and `eF`
  set ΔL : Torus d → ℝ := fun x => z x - Real.log (1 + z x) with hΔL
  set eF : Torus d → ℝ := fun x => β * Kpq x + lam * Kq x with heF
  have h1z : ∀ x, 1 + z x = p x := fun x => by simp only [hz]; ring
  have hΔLm : Measurable ΔL := hzm.sub (Real.measurable_log.comp (measurable_const.add hzm))
  have hΔLb : ∀ x, 0 ≤ ΔL x ∧ ΔL x ≤ Real.exp Mp * z x ^ 2 := by
    intro x
    have := log_sub_bound (p := p x) (Mp := Mp) (hplow x)
    simp only [hΔL, h1z]
    simpa [hz] using this
  have hΔLbb : ∀ x, |ΔL x| ≤ Real.exp Mp * Mp ^ 2 := by
    intro x
    rw [abs_of_nonneg (hΔLb x).1]
    refine (hΔLb x).2.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
    have := hzb x
    nlinarith [abs_nonneg (z x), sq_abs (z x)]
  have heFm : Measurable eF := (hKpqm.const_mul β).add (hKqm.const_mul lam)
  have heFb : ∀ x, |eF x| ≤ |β| * ((Mp + Mq) * Kg) + |lam| * (Mq * Kg) := by
    intro x
    simp only [heF]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hKpqb x) (abs_nonneg _)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hKqb x) (abs_nonneg _)
  set G : Torus d → ℝ := fun x => ΔL x + eF x with hG
  have hGm : Measurable G := hΔLm.add heFm
  have hGb : ∀ x, |G x| ≤ Real.exp Mp * Mp ^ 2 + (|β| * ((Mp + Mq) * Kg) + |lam| * (Mq * Kg)) :=
    fun x => (abs_add_le _ _).trans (add_le_add (hΔLbb x) (heFb x))
  have hGi : Integrable G μ := hbi G hGm _ hGb
  have hGmem : MemLp G 2 μ := hbm G hGm _ hGb
  -- the function `F` of the statement
  set m : ℝ := Real.log Z0 + β * ∫ x, Kz x ∂μ - ∫ x, D x ∂μ with hm
  have hKzi : Integrable Kz μ := hbi Kz hKzm _ hKzb
  have hDi : Integrable D μ := hbi D hDm _ hDb
  set F : Torus d → ℝ := fun x => z x + β * Kop (periodicRiesz d s) μ z x - projMean μ D x with hF
  have hFeq : ∀ x, F x = G x - m := by
    intro x
    have hKop : Kop (periodicRiesz d s) μ z x = Kz x - ∫ x', Kz x' ∂μ := rfl
    have hpm' : projMean μ D x = D x - ∫ x', D x' ∂μ := rfl
    simp only [hF, hKop, hpm', hG, hΔL, heF, hm]
    have := hDeq x
    linarith [this]
  have hzint : ∫ x, z x ∂μ = 0 := by
    have hpi : Integrable p μ := hbi p hpm (Mp) (fun x => by rw [abs_of_pos (hp0 x)]; exact hpb x)
    show ∫ x, (p x - 1) ∂μ = 0
    rw [integral_sub hpi (integrable_const _), hp1]; simp
  have hF0 : ∫ x, F x ∂μ = 0 := by
    have hzi : Integrable z μ := hbi z hzm Mp hzb
    have h1 : ∫ x, Kop (periodicRiesz d s) μ z x ∂μ = 0 := integral_projMean_zero hKzi
    have h2 : ∫ x, projMean μ D x ∂μ = 0 := integral_projMean_zero hDi
    have hKopi : Integrable (fun x => Kop (periodicRiesz d s) μ z x) μ := hKzi.sub (integrable_const _)
    have hpDi : Integrable (fun x => projMean μ D x) μ := hDi.sub (integrable_const _)
    simp only [hF]
    have e1 : ∫ x, (z x + β * Kop (periodicRiesz d s) μ z x - projMean μ D x) ∂μ =
        ∫ x, (z x + β * Kop (periodicRiesz d s) μ z x) ∂μ - ∫ x, projMean μ D x ∂μ :=
      integral_sub (hzi.add (hKopi.const_mul β)) hpDi
    have e2 : ∫ x, (z x + β * Kop (periodicRiesz d s) μ z x) ∂μ =
        ∫ x, z x ∂μ + ∫ x, β * Kop (periodicRiesz d s) μ z x ∂μ :=
      integral_add hzi (hKopi.const_mul β)
    rw [e1, e2, integral_const_mul, h1, h2, hzint]
    simp
  have hGint : ∫ x, G x ∂μ = m := by
    have : ∫ x, F x ∂μ = ∫ x, G x ∂μ - m := by
      have e : (fun x => F x) = fun x => G x - m := funext hFeq
      rw [e, integral_sub hGi (integrable_const _)]; simp
    linarith [hF0, this]
  have hF2 : ∫ x, F x ^ 2 ∂μ ≤ ∫ x, G x ^ 2 ∂μ := by
    have hG2i : Integrable (fun x => G x ^ 2) μ := hGmem.integrable_sq
    have e : ∫ x, F x ^ 2 ∂μ = ∫ x, G x ^ 2 ∂μ - m ^ 2 := by
      have e1 : (fun x => F x ^ 2) = fun x => G x ^ 2 + (-(2 * m) * G x + m ^ 2) := by
        funext x; rw [hFeq]; ring
      have e2 : ∫ x, (G x ^ 2 + (-(2 * m) * G x + m ^ 2)) ∂μ =
          ∫ x, G x ^ 2 ∂μ + ∫ x, (-(2 * m) * G x + m ^ 2) ∂μ :=
        integral_add hG2i ((hGi.const_mul _).add (integrable_const _))
      have e3 : ∫ x, (-(2 * m) * G x + m ^ 2) ∂μ =
          ∫ x, -(2 * m) * G x ∂μ + ∫ x, m ^ 2 ∂μ :=
        integral_add (hGi.const_mul _) (integrable_const _)
      rw [e1, e2, e3, integral_const_mul, hGint]
      simp; ring
    rw [e]; nlinarith [sq_nonneg m]
  -- the `L²` estimates
  set δ := deltaN d s (n + 1) with hδ
  have hz2 : ∫ x, z x ^ 2 ∂μ ≤ (C2 * δ) ^ 2 := hC2 n hn lam hlamdef
  have hzmem : MemLp z 2 μ := hbm z hzm Mp hzb
  have hΔmem : MemLp ΔL 2 μ := hbm ΔL hΔLm _ hΔLbb
  have heFmem : MemLp eF 2 μ := hbm eF heFm _ heFb
  have hΔ2 : ∫ x, ΔL x ^ 2 ∂μ ≤ (Real.exp Mp * (Rr * Real.sqrt δ) * (C2 * δ)) ^ 2 := by
    have hpt : ∀ x, ΔL x ^ 2 ≤ (Real.exp Mp * (Rr * Real.sqrt δ)) ^ 2 * z x ^ 2 := by
      intro x
      have h1 := hΔLb x
      have h2 : ΔL x ^ 2 ≤ (Real.exp Mp * z x ^ 2) ^ 2 := pow_le_pow_left₀ h1.1 h1.2 2
      have h3 : z x ^ 2 ≤ (Rr * Real.sqrt δ) ^ 2 := by
        have := hRsup x
        nlinarith [abs_nonneg (z x), sq_abs (z x)]
      calc ΔL x ^ 2 ≤ (Real.exp Mp * z x ^ 2) ^ 2 := h2
        _ = (Real.exp Mp) ^ 2 * z x ^ 2 * z x ^ 2 := by ring
        _ ≤ (Real.exp Mp) ^ 2 * (Rr * Real.sqrt δ) ^ 2 * z x ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
            exact mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
        _ = _ := by ring
    calc ∫ x, ΔL x ^ 2 ∂μ ≤ ∫ x, (Real.exp Mp * (Rr * Real.sqrt δ)) ^ 2 * z x ^ 2 ∂μ :=
          integral_mono hΔmem.integrable_sq (hzmem.integrable_sq.const_mul _) hpt
      _ = (Real.exp Mp * (Rr * Real.sqrt δ)) ^ 2 * ∫ x, z x ^ 2 ∂μ := integral_const_mul _ _
      _ ≤ (Real.exp Mp * (Rr * Real.sqrt δ)) ^ 2 * (C2 * δ) ^ 2 :=
          mul_le_mul_of_nonneg_left hz2 (sq_nonneg _)
      _ = _ := by ring
  have hT1 : Real.sqrt (∫ x, ΔL x ^ 2 ∂μ) ≤ Real.exp Mp * Rr * C2 * (δ * Real.sqrt δ) := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    refine hΔ2.trans (le_of_eq ?_)
    ring
  -- the forcing term
  have hpq2 : ∫ x, (p x - qb x) ^ 2 ∂μ ≤ (CL * Real.sqrt (δ / ((n + 1 : ℕ) : ℝ))) ^ 2 := by
    have e : ∫ x, (p x - qb x) ^ 2 ∂μ = ∫ x, (p x - q x) ^ 2 ∂μ :=
      integral_congr_ae (hqbq.mono fun y hy => by simp only [← hy])
    rw [e]
    exact (Real.sqrt_le_iff.1 (hCL n hn lam hlamdef)).2
  obtain ⟨-, hKpq2⟩ := hCS (fun y => p y - qb y) (hpm.sub hqbm) (Mp + Mq) hpqb
  have hKpq2' : ∫ x, Kpq x ^ 2 ∂μ ≤ CS * (CL * Real.sqrt (δ / ((n + 1 : ℕ) : ℝ))) ^ 2 :=
    hKpq2.trans (mul_le_mul_of_nonneg_left hpq2 hCS0)
  have hKpqmem : MemLp (fun x => β * Kpq x) 2 μ := hbm _ (hKpqm.const_mul β) _ (fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hKpqb x) (abs_nonneg _))
  have hKqmem : MemLp (fun x => lam * Kq x) 2 μ := hbm _ (hKqm.const_mul lam) _ (fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hKqb x) (abs_nonneg _))
  have hTa : Real.sqrt (∫ x, (β * Kpq x) ^ 2 ∂μ) ≤
      β * Real.sqrt CS * CL * Real.sqrt (δ / ((n + 1 : ℕ) : ℝ)) := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    calc ∫ x, (β * Kpq x) ^ 2 ∂μ = β ^ 2 * ∫ x, Kpq x ^ 2 ∂μ := by
          rw [← integral_const_mul]; exact integral_congr_ae (Eventually.of_forall fun x => by ring)
      _ ≤ β ^ 2 * (CS * (CL * Real.sqrt (δ / ((n + 1 : ℕ) : ℝ))) ^ 2) :=
          mul_le_mul_of_nonneg_left hKpq2' (sq_nonneg _)
      _ = (β * Real.sqrt CS * CL * Real.sqrt (δ / ((n + 1 : ℕ) : ℝ))) ^ 2 := by
          have := Real.sq_sqrt hCS0
          calc _ = β ^ 2 * (Real.sqrt CS) ^ 2 * (CL * Real.sqrt (δ / ((n + 1 : ℕ) : ℝ))) ^ 2 := by
                rw [this]; ring
            _ = _ := by ring
  have hTb : Real.sqrt (∫ x, (lam * Kq x) ^ 2 ∂μ) ≤ lam * (Mq * Kg) := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    calc ∫ x, (lam * Kq x) ^ 2 ∂μ ≤ ∫ _x, (lam * (Mq * Kg)) ^ 2 ∂μ := by
          refine integral_mono (hKqmem.integrable_sq) (integrable_const _) fun x => ?_
          have : |lam * Kq x| ≤ lam * (Mq * Kg) := by
            rw [abs_mul, abs_of_nonneg hlam]; exact mul_le_mul_of_nonneg_left (hKqb x) hlam
          nlinarith [abs_nonneg (lam * Kq x), sq_abs (lam * Kq x)]
      _ = _ := by simp
  have hT2 : Real.sqrt (∫ x, eF x ^ 2 ∂μ) ≤
      β * Real.sqrt CS * CL * Real.sqrt (δ / ((n + 1 : ℕ) : ℝ)) + lam * (Mq * Kg) := by
    have := sqrt_int_add_le hKpqmem hKqmem
    exact this.trans (add_le_add hTa hTb)
  have hTG : Real.sqrt (∫ x, G x ^ 2 ∂μ) ≤ Real.sqrt (∫ x, ΔL x ^ 2 ∂μ) + Real.sqrt (∫ x, eF x ^ 2 ∂μ) :=
    sqrt_int_add_le hΔmem heFmem
  have hfin : Real.sqrt (∫ x, F x ^ 2 ∂μ) ≤ Real.sqrt (∫ x, G x ^ 2 ∂μ) := Real.sqrt_le_sqrt hF2
  have hFmem : MemLp F 2 μ := by
    have : F = fun x => G x - m := funext hFeq
    rw [this]; exact hGmem.sub (memLp_const m)
  refine ⟨hFmem, hfin.trans (hTG.trans ?_)⟩
  have hCle : Real.exp Mp * Rr * C2 + β * Real.sqrt CS * CL + β * (Kg * Mq) ≤
      Real.exp Mp * Rr * C2 + βp * Real.sqrt CS * CL + βp * (Kg * Mq) := by
    have h1 := hβI.2
    have h2 : 0 ≤ Real.sqrt CS * CL := by positivity
    have h3 : 0 ≤ Kg * Mq := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h1 h2, mul_le_mul_of_nonneg_right h1 h3]
  have hst : 0 ≤ δ * Real.sqrt δ + Real.sqrt (δ / ((n + 1 : ℕ) : ℝ)) + 1 / ((n + 1 : ℕ) : ℝ) := by
    positivity
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hCle hst)
  have hlamE : lam * (Mq * Kg) = β * (Kg * Mq) * (1 / ((n + 1 : ℕ) : ℝ)) := by
    rw [hlam']; field_simp
  have hAB : 0 ≤ δ * Real.sqrt δ := by positivity
  have hBB : 0 ≤ Real.sqrt (δ / ((n + 1 : ℕ) : ℝ)) := Real.sqrt_nonneg _
  have hEE : 0 ≤ 1 / ((n + 1 : ℕ) : ℝ) := by positivity
  set c1 := Real.exp Mp * Rr * C2 with hc1
  set c2 := β * Real.sqrt CS * CL with hc2
  set c3 := β * (Kg * Mq) with hc3
  have hc10 : 0 ≤ c1 := by positivity
  have hc20 : 0 ≤ c2 := by positivity
  have hc30 : 0 ≤ c3 := by positivity
  have hexp : (c1 + c2 + c3) * (δ * Real.sqrt δ + Real.sqrt (δ / ((n + 1 : ℕ) : ℝ)) + 1 / ((n + 1 : ℕ) : ℝ)) -
      (c1 * (δ * Real.sqrt δ) + c2 * Real.sqrt (δ / ((n + 1 : ℕ) : ℝ)) + c3 * (1 / ((n + 1 : ℕ) : ℝ))) =
      c1 * Real.sqrt (δ / ((n + 1 : ℕ) : ℝ)) + c1 * (1 / ((n + 1 : ℕ) : ℝ)) + c2 * (δ * Real.sqrt δ) +
      c2 * (1 / ((n + 1 : ℕ) : ℝ)) + c3 * (δ * Real.sqrt δ) + c3 * Real.sqrt (δ / ((n + 1 : ℕ) : ℝ)) := by
    ring
  have hnn : 0 ≤ c1 * Real.sqrt (δ / ((n + 1 : ℕ) : ℝ)) + c1 * (1 / ((n + 1 : ℕ) : ℝ)) + c2 * (δ * Real.sqrt δ) +
      c2 * (1 / ((n + 1 : ℕ) : ℝ)) + c3 * (δ * Real.sqrt δ) + c3 * Real.sqrt (δ / ((n + 1 : ℕ) : ℝ)) := by
    positivity
  rw [hlamE] at hT2
  nlinarith [hT1, hT2, hexp, hnn]

end HRS.ME.Unif

end
