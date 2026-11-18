import HRS.ME.UnifP4A
import HRS.ME.UnifP2A
import HRS.ME.UnifP2B
import HRS.ME.NfUPU1aA
import HRS.Equilibrium.CavityMain

/-!
# Uniform Lemma 4.6 (cavity response), part A (packet P5)

Uniform versions (constants chosen after `d, s, βm, βp, Λ, c` and before `β ∈ [βm, βp]` and before the smooth
density `ρ ≤ Λ`) of the first pieces of the proof of `HRS.cavity_response_proof`
(`HRS/Equilibrium/Cavity{Response,Prefactor,Field,Psi,Main}.lean`):
`conv_gPlus`, `pole_dual`, `cavity_L2`.  The proofs are those of the pointwise versions, with the inputs
`pole_variance_clause`, `insDefect_le`, `pDens_bounds`, `qDens_bound` replaced by their uniform forms
(`HRS.ME.Unif.*_unif`, `UnifP2B`, `UnifP4A`).  The lower bound `c₀ ≤ ρ` is not needed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.ME.Unif

open HRS HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp

variable {d : ℕ} {s c : ℝ}

/-- Uniform `conv_gPlus`: `Cg` depends on `Λ` (and `c`) only. -/
theorem conv_gPlus_unif (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (Λ : ℝ) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ y, 0 ≤ convMeasure (gPlus d s c) (withDensityReal ρ) y ∧
        convMeasure (gPlus d s c) (withDensityReal ρ) y ≤ Cg := by
  obtain ⟨B, Cc, hB0, hK⟩ := NfU.kerData_periodicRiesz_unif hd hs0 hsd Λ
  refine ⟨|Cc| + |c|, by positivity, fun ρ hρ hΛ y => ⟨?_, ?_⟩⟩
  · exact integral_nonneg fun z => hc _
  · have hμ := isProbabilityMeasure_mu hρ
    have hK' := hK ρ hρ hΛ
    have hconv : convMeasure (gPlus d s c) (withDensityReal ρ) y =
        convMeasure (periodicRiesz d s) (withDensityReal ρ) y + c := by
      unfold convMeasure gPlus
      rw [integral_add (hK'.int y) (integrable_const _)]
      simp
    rw [hconv]
    have := (abs_le.1 (hK'.conv y)).2
    linarith [le_abs_self c, le_abs_self Cc]

/-- Uniform `pole_dual`. -/
theorem pole_dual_unif (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (Λ : ℝ) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ f : Torus d → ℝ, Measurable f → ∀ K : ℝ, (∀ y, |f y| ≤ K) →
        |∫ y, f y ∂(firstMarginal
              (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)) -
            ∫ y, f y ∂(firstMarginal
              (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β))| ≤
          Cd * Real.sqrt (∫ y, f y ^ 2 ∂(withDensityReal ρ)) * Real.sqrt (deltaN d s N / N) := by
  obtain ⟨C₁, hC₁, hvarU⟩ := pole_variance_clause_unif hd hs0 hsd βm βp hβm Λ
  obtain ⟨Cd, hCdU⟩ := insDefect_le_unif hd hs0 hsd βm βp hβm hββ Λ
  obtain ⟨B, hB0, hB⟩ := MarginalAux.rieszB hd hs0 hsd
  have hgm := measurable_periodicRiesz hd hs0 hsd
  set K1p : ℝ := C₁ * Real.exp (βp * B) with hK1pdef
  set K2 : ℝ := |Cd| * Real.exp |Cd| with hK2
  have hK1pp : 0 ≤ K1p := by positivity
  have hK2p : 0 ≤ K2 := by positivity
  refine ⟨2 * Real.sqrt (2 * (K1p * K2)), by positivity,
    fun β hβI ρ hρ hΛ N hN x t ht f hfm K hf => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hμ := isProbabilityMeasure_mu hρ
  have hvar := hvarU β hβI ρ hρ hΛ
  have hCd := hCdU β hβI ρ hρ hΛ
  set K1 : ℝ := C₁ * Real.exp (β * B) with hK1
  have hK1p : 0 ≤ K1 := by positivity
  have hK1le : K1 ≤ K1p :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hβI.2 hB0)) hC₁.le
  have hmono : 2 * Real.sqrt (2 * (K1 * K2)) ≤ 2 * Real.sqrt (2 * (K1p * K2)) := by
    gcongr
  refine le_trans ?_ (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hmono (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  have hn1 : 0 < N - 1 := by omega
  have hn0 : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by exact_mod_cast hn1
  have hnN : (N : ℝ) ≤ 2 * ((N - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hln : β / N * ((N - 1 : ℕ) : ℝ) ≤ β := by
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
    have : β / N * ((N : ℝ) - 1) = β - β / N := by field_simp
    rw [this]; linarith
  set n : ℕ := N - 1 with hn
  set lam : ℝ := β / N with hlamdef
  set L : ℝ := ∫ y, f y ^ 2 ∂(withDensityReal ρ) with hL
  have hL0 : 0 ≤ L := integral_nonneg fun y => sq_nonneg _
  haveI hP0 := cavity_isProb hd hs0 hsd β hρ n lam hlam
  set P0 := cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β with hP0def
  have hδ0 : 0 ≤ deltaN d s N := by
    have := inv_le_deltaN (d := d) hs0 N (by omega)
    exact (inv_nonneg.2 hN0.le).trans this
  have hδ1 : deltaN d s N ≤ 1 := deltaN_le_one hs0 hsd (by omega) N (by omega)
  have hRHS : 0 ≤ 2 * Real.sqrt (2 * (K1 * K2)) * Real.sqrt L * Real.sqrt (deltaN d s N / N) := by
    positivity
  rcases eq_or_lt_of_le ht.1 with h0 | htpos
  · rw [← h0, poleLaw_zero_eq hd hs0 hsd β hρ n lam hlam x, ← hP0def, sub_self, abs_zero]
    exact hRHS
  have hXm' : Measurable fun Y : Config d n => t * Xx (periodicRiesz d s) lam x Y :=
    (measurable_Xx hgm lam x).const_mul t
  have hbX := Xx_le hd hs0 hsd hlam hln hB0 hB x
  have hb' : ∀ Y : Config d n, t * Xx (periodicRiesz d s) lam x Y ≤ β * B := by
    intro Y
    have h1 := hbX Y
    have h2 : 0 ≤ β * B := by positivity
    nlinarith [ht.2]
  have hφm := measurable_fracF (n := n) hfm
  have htv := EF.ef_tv (P := P0) hXm' hb' hφm (abs_fracF_le hn1 hf)
  have e1 : P0.tilted (fun Y => t * Xx (periodicRiesz d s) lam x Y) =
      poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x t :=
    (poleLaw_eq_tilted_cavity hd hs0 hsd β hρ n lam hlam x t).symm
  have e0 : P0 = poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x 0 :=
    (poleLaw_zero_eq hd hs0 hsd β hρ n lam hlam x).symm
  haveI hPt := pole_isProb hd hs0 hsd β hρ n lam hlam x t ht.1
  have hint1 : ∫ Y, fracF f Y ∂(P0.tilted (fun Y => t * Xx (periodicRiesz d s) lam x Y)) =
      ∫ y, f y ∂(firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x t)) := by
    rw [e1]
    exact integral_fracF hn1 hfm hf _ (poleLaw_exchangeable hd hs0 hsd β hρ n lam hlam x t)
  have hint0 : ∫ Y, fracF f Y ∂P0 = ∫ y, f y ∂(firstMarginal P0) :=
    integral_fracF hn1 hfm hf P0 (cavityLaw_exchangeable hd hs0 hsd β hρ n lam)
  have hV0 : Var[fracF (n := n) f; P0] ≤ (K1 * L) / (n : ℝ) := by
    rw [e0]
    have := var_fracF_le hd hs0 hsd hβ hρ hC₁ hvar hB0 hB (N := N) hN x (t := 0) ⟨le_rfl, zero_le_one⟩
      hfm hf
    rw [hK1, hL]; simpa [mul_assoc] using this
  have hV1 : Var[fracF (n := n) f; P0.tilted (fun Y => t * Xx (periodicRiesz d s) lam x Y)] ≤
      (K1 * L) / (n : ℝ) := by
    rw [e1]
    have := var_fracF_le hd hs0 hsd hβ hρ hC₁ hvar hB0 hB (N := N) hN x ht hfm hf
    rw [hK1, hL]; simpa [mul_assoc] using this
  -- the second difference of the cumulant generating function
  obtain ⟨-, -, hΔ1⟩ := hCd N hN x
  have hXmx := measurable_Xx hgm lam x (n := n)
  have hmono := cgf_diff_mono (P := P0) hXmx hbX htpos ht.2
  have hc1 : cgf (fun Y => t * Xx (periodicRiesz d s) lam x Y) P0 1 =
      cgf (Xx (periodicRiesz d s) lam x) P0 t := by
    unfold cgf mgf; congr 2; funext Y; congr 1; ring
  have hc2 : cgf (fun Y => t * Xx (periodicRiesz d s) lam x Y) P0 (1 / 2) =
      cgf (Xx (periodicRiesz d s) lam x) P0 (t / 2) := by
    unfold cgf mgf; congr 2; funext Y; congr 1; ring
  have hΔ' : cgf (fun Y => t * Xx (periodicRiesz d s) lam x Y) P0 1 -
      2 * cgf (fun Y => t * Xx (periodicRiesz d s) lam x Y) P0 (1 / 2) ≤
      |Cd| * deltaN d s N := by
    rw [hc1, hc2]
    exact (hmono.trans hΔ1).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hδ0)
  have hee := exp_sub_one_le _ |Cd| (deltaN d s N) hδ0 hδ1 (abs_nonneg _) hΔ'
  rw [hint1, hint0] at htv
  refine htv.trans ?_
  have hch := sqrt_chain (n := (n : ℝ)) (N := (N : ℝ)) hn0 hN0 hnN (mul_nonneg hK1p hL0) hK2p hδ0
    hV0 hV1 hee
  refine hch.trans (le_of_eq ?_)
  rw [show 2 * (K1 * L * K2) = (2 * (K1 * K2)) * L by ring, Real.sqrt_mul (by positivity)]
  ring

/-- Uniform `cavity_L2`. -/
theorem cavity_L2_unif (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (Λ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ n : ℕ, 0 < n → ∀ lam : ℝ, lam = β / ((n + 1 : ℕ) : ℝ) →
      Real.sqrt (∫ y, (pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y -
          qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y) ^ 2 ∂(withDensityReal ρ)) ≤
        C * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) := by
  obtain ⟨Mp, hMp1, hMpU⟩ := pDens_bounds_unif hd hs0 hsd βm βp hβm hββ Λ
  obtain ⟨Mq, hMq0, hMqU⟩ := qDens_bound_unif hd hs0 hsd βm βp hβm hββ Λ
  obtain ⟨Cd, hCd0, hCdU⟩ := pole_dual_unif hd hs0 hsd βm βp hβm hββ Λ
  refine ⟨Real.sqrt 2 * Cd, by positivity, fun β hβI ρ hρ hΛ n hn lam hlamdef => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hμ := isProbabilityMeasure_mu hρ
  have hMp := hMpU β hβI ρ hρ hΛ
  have hMq := hMqU β hβI ρ hρ hΛ
  have hCd := hCdU β hβI ρ hρ hΛ
  obtain ⟨hlam, hln, -⟩ := lam_facts hd hs0 hsd hβ hρ hn hlamdef
  have hN : 2 ≤ n + 1 := by omega
  have hN0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hpm := measurable_pDens hd hs0 hsd hρ hlam hln
  have hqm := qDens_measurable hd hs0 hsd hβ hρ hn hlamdef
  have hacq := hMq (n + 1) hN
  have hlam' : lam = β / ((n + 1 : ℕ) : ℝ) := hlamdef
  have hac : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) ≪
      withDensityReal ρ := by
    subst hlam'; exact hacq.1
  have hqb : ∀ᵐ y ∂(withDensityReal ρ), qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mq := by
    subst hlam'; exact hacq.2
  have hpb : ∀ y, pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mp := by
    subst hlam'; exact fun y => (hMp (n + 1) hN y).2
  set p := pDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hp
  set q := qDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hq
  set μ := withDensityReal ρ with hμdef
  have hp0 : ∀ y, 0 ≤ p y := fun y => (pDens_pos hd hs0 hsd hρ hlam hln y).le
  have hq0 : ∀ y, 0 ≤ q y := fun y => ENNReal.toReal_nonneg
  set qb : Torus d → ℝ := fun y => min (q y) Mq with hqbdef
  have hqbm : Measurable qb := hqm.min measurable_const
  have hqbq : q =ᵐ[μ] qb := hqb.mono fun y hy => by simp only [hqbdef, min_eq_left hy]
  have hqb0 : ∀ y, 0 ≤ qb y := fun y => le_min (hq0 y) hMq0.le
  have hqbM : ∀ y, qb y ≤ Mq := fun y => min_le_right _ _
  set M : ℝ := Mp + Mq with hM
  have hMp0 : 0 ≤ Mp := (hp0 (Classical.arbitrary _)).trans (hpb _)
  have hpM : ∀ y, p y ≤ M := fun y => by linarith [hpb y]
  have hqM : ∀ y, qb y ≤ M := fun y => by linarith [hqbM y]
  set Bd : ℝ := Cd * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) with hBd
  have hBd0 : 0 ≤ Bd := by positivity
  -- the measures
  have hπeq := firstMarginal_eq_withDensity hd hs0 hsd hρ hlam hln
  have hνeq := nu_eq_withDensity hd hs0 hsd hβ hρ hn hlamdef hac
  haveI hP0 := cavity_isProb hd hs0 hsd β hρ n lam hlam
  haveI hQ := cavity_isProb hd hs0 hsd β hρ (n + 1) lam hlam
  haveI hπp := isProb_firstMarginal (Nat.succ_pos n) (cavityLaw (periodicRiesz d s) μ (n + 1) lam β)
  haveI hνp := isProb_firstMarginal hn (cavityLaw (periodicRiesz d s) μ n lam β)
  haveI hνx : ∀ x : Torus d, IsProbabilityMeasure
      (firstMarginal (poleLaw (periodicRiesz d s) μ n lam β x 1)) := fun x => by
    haveI := pole_isProb hd hs0 hsd β hρ n lam hlam x 1 zero_le_one
    exact isProb_firstMarginal hn _
  have hdual : ∀ f : Torus d → ℝ, Measurable f → (∀ y, 0 ≤ f y) → (∀ y, f y ≤ M) →
      |∫ y, f y * p y ∂μ - ∫ y, f y * qb y ∂μ| ≤ Bd * Real.sqrt (∫ y, f y ^ 2 ∂μ) := by
    intro f hfm hf0 hfM
    have hmixd := mixture_dual (π := firstMarginal (cavityLaw (periodicRiesz d s) μ (n + 1) lam β))
      (ν := firstMarginal (cavityLaw (periodicRiesz d s) μ n lam β))
      (fun x => firstMarginal (poleLaw (periodicRiesz d s) μ n lam β x 1))
      (fun A hA => by
        have hA' : MeasurableSet {Y : Config d n | Y ⟨0, hn⟩ ∈ A} := (measurable_pi_apply _) hA
        have := measurable_poleLaw_set hd hs0 hsd hρ hlam hln hA'
        convert this using 2 with x
        unfold firstMarginal; rw [dif_pos hn, Measure.map_apply (measurable_pi_apply (⟨0, hn⟩ : Fin n)) hA]; rfl)
      (fun A hA => by
        rw [firstMarginal_disint hd hs0 hsd hρ hlam hln hn hA]
        refine lintegral_congr fun x => ?_
        unfold firstMarginal; rw [dif_pos hn, Measure.map_apply (measurable_pi_apply (⟨0, hn⟩ : Fin n)) hA]; rfl)
      hfm hf0 hfM (Bd := Bd * Real.sqrt (∫ y, f y ^ 2 ∂μ)) (fun x => by
        have := hCd (n + 1) hN x 1 ⟨zero_le_one, le_rfl⟩ f hfm M (fun y => by
          rw [abs_of_nonneg (hf0 y)]; exact hfM y)
        have e : β / ((n + 1 : ℕ) : ℝ) = lam := hlamdef.symm
        rw [e] at this
        exact this.trans (le_of_eq (by simp only [hBd]; ring)))
    rw [hπeq, hνeq, integral_withDensity_real hpm hp0, integral_withDensity_real hqm hq0] at hmixd
    have e2 : ∫ y, q y * f y ∂μ = ∫ y, qb y * f y ∂μ :=
      integral_congr_ae (hqbq.mono fun y hy => by simp only [← hy])
    rw [e2] at hmixd
    simp_rw [mul_comm (p _) (f _), mul_comm (qb _) (f _)] at hmixd
    simpa [mul_comm] using hmixd
  have hl2 := l2_of_dual hpm hqbm hp0 hqb0 hpM hqM hBd0 hdual
  have e3 : ∫ y, (p y - q y) ^ 2 ∂μ = ∫ y, (p y - qb y) ^ 2 ∂μ :=
    integral_congr_ae (hqbq.mono fun y hy => by simp only [← hy])
  rw [e3]
  refine hl2.trans (le_of_eq ?_)
  simp only [hBd]; ring


end HRS.ME.Unif

end
