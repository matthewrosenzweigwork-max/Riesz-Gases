/-
# HRS.Equilibrium.CavityMain — Lemma 4.6 `M:R:lem:cavity` (`cavity_response_proof`)

Assembles `partA`, `cavity_L2`, `response_bound`, `pole_prefactor` and `sup_dev_rate` and converts
the `n`-form bounds (in `δ_N`, `δ_N/N`) to the stated `√(log N)/N` form.
-/
import HRS.Equilibrium.CavityPsi

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace CavResp

variable {d : ℕ} {s c : ℝ}

open HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer

theorem rate_facts (hcrit : s = (d : ℝ) / 2) {N : ℕ} (hN : 2 ≤ N) :
    Real.sqrt (deltaN d s N / (N : ℝ)) ≤ 2 * Real.sqrt (Real.log N) / N ∧
    deltaN d s N * Real.sqrt (deltaN d s N) ≤ 11 * Real.sqrt (Real.log N) / N ∧
    1 / (N : ℝ) ≤ 2 * Real.sqrt (Real.log N) / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNd := N_mul_deltaN_crit (d := d) hcrit (by omega : 1 ≤ N)
  set L : ℝ := Real.log N with hL
  have hL2 : (1 / 2 : ℝ) ≤ L := by
    have h1 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN2
    have := Real.log_two_gt_d9
    linarith
  have hL0 : 0 < L := by linarith
  set S : ℝ := Real.sqrt N with hS
  have hS0 : 0 < S := Real.sqrt_pos.2 hN0
  have hSS : S * S = N := Real.mul_self_sqrt hN0.le
  have hS1 : 1 ≤ S := Real.one_le_sqrt.2 (by linarith)
  have hLS : L ≤ 2 * S := by
    have h1 : Real.log S ≤ S - 1 := Real.log_le_sub_one_of_pos hS0
    have h2 : Real.log N = 2 * Real.log S := by
      rw [← hSS, Real.log_mul hS0.ne' hS0.ne']; ring
    linarith
  have hδ : deltaN d s N = (1 + L) / N := by
    rw [eq_div_iff hN0.ne', mul_comm]; exact hNd
  set q : ℝ := Real.sqrt (1 + L) with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqq : q * q = 1 + L := Real.mul_self_sqrt (by linarith)
  set r : ℝ := Real.sqrt L with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hL0
  have hrr : r * r = L := Real.mul_self_sqrt hL0.le
  have hqr : q ≤ (9 / 5) * r := by
    have : q ≤ Real.sqrt (3 * L) := Real.sqrt_le_sqrt (by linarith)
    refine this.trans ?_
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hsqδ : Real.sqrt (deltaN d s N) = q / S := by
    rw [hδ, Real.sqrt_div (by linarith), hq]
  have hr12 : (1 : ℝ) ≤ 2 * r := by
    have : (1 / 2 : ℝ) ≤ r * r := by rw [hrr]; exact hL2
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have e1 : Real.sqrt (deltaN d s N / (N : ℝ)) = q / N := by
      rw [hδ, show (1 + L) / (N : ℝ) / N = (1 + L) / (N : ℝ) ^ 2 by ring,
        Real.sqrt_div (by linarith), Real.sqrt_sq hN0.le]
    rw [e1]
    exact div_le_div_of_nonneg_right (by linarith) hN0.le
  · rw [hsqδ, hδ]
    have h1 : (1 + L) * q ≤ 11 * S * r := by
      have a1 : (1 + L) ≤ 3 * L := by linarith
      have a2 : (1 + L) * q ≤ (3 * L) * ((9 / 5) * r) :=
        mul_le_mul a1 hqr hq0 (by linarith)
      have a3 : L * r ≤ (2 * S) * r := mul_le_mul_of_nonneg_right hLS hr0.le
      nlinarith
    rw [show (1 + L) / (N : ℝ) * (q / S) = ((1 + L) * q) / ((N : ℝ) * S) by field_simp,
      div_le_div_iff₀ (by positivity) hN0]
    nlinarith [mul_le_mul_of_nonneg_right h1 hN0.le]
  · exact div_le_div_of_nonneg_right hr12 hN0.le

theorem eLpNorm_two_le {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {F : Torus d → ℝ}
    (hF : MemLp F 2 μ) {B : ℝ} (h : Real.sqrt (∫ x, F x ^ 2 ∂μ) ≤ B) :
    eLpNorm F 2 μ ≤ ENNReal.ofReal B := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hF]
  refine ENNReal.ofReal_le_ofReal (le_trans (le_of_eq ?_) h)
  have e1 : (2 : ℝ≥0∞).toReal = 2 := by simp
  rw [e1, Real.sqrt_eq_rpow]
  congr 1
  · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs]
    rw [Real.rpow_two, sq_abs]
  · norm_num

section Items

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
  (hρ : SmoothPosDensity ρ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)

include hd hcrit hβ hρ

theorem gibbs_dens {N : ℕ} (hN : 2 ≤ N) :
    firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≪ withDensityReal ρ ∧
    (∀ᵐ y ∂(withDensityReal ρ),
      ((firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))).rnDeriv
        (withDensityReal ρ) y).toReal =
        pDens (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β y) ∧
    firstMarginal (critCavity d s c β ρ N) ≪ withDensityReal ρ := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨Mq, hMq0, hMq⟩ := qDens_bound hd hs0 hsd hβ hρ
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 0 < n := by omega
  have hlamdef : β / ((n + 1 : ℕ) : ℝ) = β / ((n + 1 : ℕ) : ℝ) := rfl
  obtain ⟨hlam, hln, -⟩ := lam_facts hd hs0 hsd hβ hρ hn hlamdef
  have hmod := modulatedGibbs_eq_cavity hd hs0 hsd hβ hρ (n + 1) (Nat.succ_pos n)
  have hcav := critCavity_eq hd hs0 hsd c β hρ (n + 1)
  rw [hmod]
  refine ⟨?_, ?_, by rw [hcav]; exact (hMq (n + 1) hN).1⟩
  · rw [firstMarginal_eq_withDensity hd hs0 hsd hρ hlam hln]
    exact withDensity_absolutelyContinuous _ _
  · exact rnDeriv_pi_eq hd hs0 hsd hρ hlam hln

theorem item2 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      (firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≪
          withDensityReal ρ ∧
        firstMarginal (critCavity d s c β ρ N) ≪ withDensityReal ρ ∧
        eLpNorm (fun y =>
            ((firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))).rnDeriv
                (withDensityReal ρ) y).toReal -
              ((firstMarginal (critCavity d s c β ρ N)).rnDeriv (withDensityReal ρ) y).toReal)
            2 (withDensityReal ρ) ≤
          ENNReal.ofReal (C * Real.sqrt (Real.log N) / N)) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨CL, hCL0, hCL⟩ := cavity_L2 hd hs0 hsd hβ hρ
  obtain ⟨Mp, hMp1, hMp⟩ := pDens_bounds hd hs0 hsd hβ hρ
  obtain ⟨Mq, hMq0, hMq⟩ := qDens_bound hd hs0 hsd hβ hρ
  refine ⟨2 * CL, by positivity, fun N hN => ?_⟩
  obtain ⟨h1, h2, h3⟩ := gibbs_dens hd hcrit hβ hρ (c := c) hN
  refine ⟨h1, h3, ?_⟩
  have hcav := critCavity_eq hd hs0 hsd c β hρ N
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 0 < n := by omega
  have hlamdef : β / ((n + 1 : ℕ) : ℝ) = β / ((n + 1 : ℕ) : ℝ) := rfl
  obtain ⟨hlam, hln, -⟩ := lam_facts hd hs0 hsd hβ hρ hn hlamdef
  have hpm := measurable_pDens hd hs0 hsd hρ hlam hln
  have hqm := qDens_measurable hd hs0 hsd hβ hρ hn hlamdef
  have hqb : ∀ᵐ y ∂(withDensityReal ρ), qDens (periodicRiesz d s) (withDensityReal ρ) n
      (β / ((n + 1 : ℕ) : ℝ)) β y ≤ Mq := (hMq (n + 1) hN).2
  have hpb : ∀ y, pDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β y ≤ Mp :=
    fun y => (hMp (n + 1) hN y).2
  have hp0 : ∀ y, 0 ≤ pDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β y :=
    fun y => (pDens_pos hd hs0 hsd hρ hlam hln y).le
  have hq0 : ∀ y, 0 ≤ qDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β y :=
    fun y => ENNReal.toReal_nonneg
  have hmem : MemLp (fun y => pDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β y -
      qDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β y) 2 (withDensityReal ρ) :=
    MemLp.of_bound (hpm.sub hqm).aestronglyMeasurable (Mp + Mq) (by
      filter_upwards [hqb] with y hy
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hpb y, hp0 y, hq0 y])
  have hL2 := hCL n hn _ rfl
  obtain ⟨r1, -, -⟩ := rate_facts (d := d) hcrit hN
  have hbound : Real.sqrt (∫ y, (pDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β y -
      qDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β y) ^ 2
        ∂(withDensityReal ρ)) ≤ 2 * CL * Real.sqrt (Real.log ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ) := by
    refine hL2.trans ?_
    calc _ ≤ CL * (2 * Real.sqrt (Real.log ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left r1 hCL0
      _ = _ := by ring
  refine le_trans (le_of_eq ?_) (eLpNorm_two_le hmem hbound)
  refine eLpNorm_congr_ae ?_
  filter_upwards [h2] with y hy
  rw [hy, hcav]
  rfl

theorem item3 (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      eLpNorm (fun y =>
          (((firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))).rnDeriv
              (withDensityReal ρ) y).toReal - 1) +
            β * Kop (periodicRiesz d s) (withDensityReal ρ)
              (fun y' => ((firstMarginal (modulatedGibbs (periodicRiesz d s) N β
                (withDensityReal ρ))).rnDeriv (withDensityReal ρ) y').toReal - 1) y -
            projMean (withDensityReal ρ) (insertionDefect d s c β ρ N) y)
          2 (withDensityReal ρ) ≤
        ENNReal.ofReal (C * Real.sqrt (Real.log N) / N) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨Cr, hCr0, hCr⟩ := response_bound hd hcrit hβ hρ c hc
  refine ⟨15 * Cr, by positivity, fun N hN => ?_⟩
  obtain ⟨h1, h2, h3⟩ := gibbs_dens hd hcrit hβ hρ (c := c) hN
  have hDef : insertionDefect d s c β ρ N =
      insDefect (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β :=
    funext fun x => insertionDefect_eq_insDefect hd hs0 hsd c β hβ hρ hN x
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 0 < n := by omega
  obtain ⟨hmem, hsq⟩ := hCr n hn _ rfl
  obtain ⟨r1, r2, r3⟩ := rate_facts (d := d) hcrit hN
  have hbound : Real.sqrt (∫ x, ((pDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β x - 1) +
          β * Kop (periodicRiesz d s) (withDensityReal ρ)
            (fun y => pDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β y - 1) x -
          projMean (withDensityReal ρ)
            (insDefect (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β) x) ^ 2
          ∂(withDensityReal ρ)) ≤
      15 * Cr * Real.sqrt (Real.log ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ) := by
    refine hsq.trans ?_
    calc _ ≤ Cr * (11 * Real.sqrt (Real.log ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ) +
            2 * Real.sqrt (Real.log ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ) +
            2 * Real.sqrt (Real.log ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith) hCr0
      _ = _ := by ring
  refine le_trans (le_of_eq ?_) (eLpNorm_two_le hmem hbound)
  refine eLpNorm_congr_ae ?_
  have hKop : ∀ y, Kop (periodicRiesz d s) (withDensityReal ρ)
      (fun y' => ((firstMarginal (modulatedGibbs (periodicRiesz d s) (n + 1) β
        (withDensityReal ρ))).rnDeriv (withDensityReal ρ) y').toReal - 1) y =
      Kop (periodicRiesz d s) (withDensityReal ρ)
        (fun y' => pDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β y' - 1) y := by
    intro y
    unfold Kop
    have : (fun x => ∫ y', periodicRiesz d s (x - y') * (((firstMarginal (modulatedGibbs (periodicRiesz d s)
        (n + 1) β (withDensityReal ρ))).rnDeriv (withDensityReal ρ) y').toReal - 1) ∂(withDensityReal ρ)) =
        fun x => ∫ y', periodicRiesz d s (x - y') * (pDens (periodicRiesz d s) (withDensityReal ρ) n
          (β / ((n + 1 : ℕ) : ℝ)) β y' - 1) ∂(withDensityReal ρ) := by
      funext x
      refine integral_congr_ae ?_
      filter_upwards [h2] with y' hy'
      rw [hy']
      rfl
    rw [this]
  filter_upwards [h2] with y hy
  rw [hy, hKop y, hDef]
  rfl

theorem item5 (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ᵐ y ∂(withDensityReal ρ),
        |((firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))).rnDeriv
            (withDensityReal ρ) y).toReal - 1| ≤ C * Real.sqrt (deltaN d s N) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨Cs, hCs0, hCs⟩ := sup_dev_rate hd hcrit hβ hρ c hc
  refine ⟨Cs, hCs0, fun N hN => ?_⟩
  obtain ⟨h1, h2, h3⟩ := gibbs_dens hd hcrit hβ hρ (c := c) hN
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 0 < n := by omega
  filter_upwards [h2] with y hy
  rw [hy]
  exact hCs n hn _ rfl y

end Items

end CavResp

/-- Lemma 4.6 `M:R:lem:cavity` (restatement of `HRS.cavity_response`, proved here because the
inputs `perturbed_pressure`, the marginal-density and response estimates are downstream of
`PoleCavity.lean`). -/
theorem cavity_response_proof {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      (∀ x : Torus d,
        Integrable (fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i))
            (critCavity d s c β ρ N) ∧
          HasDerivWithinAt (insertionPressure d s c β ρ N x)
            (-((β / N) * ∫ Y, ∑ i, gPlus d s c (x - Y i) ∂(critCavity d s c β ρ N)))
            (Set.Ici 0) 0 ∧
          0 ≤ insertionDefect d s c β ρ N x ∧
          ENNReal.ofReal (insertionDefect d s c β ρ N x) =
            ∫⁻ t in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ((1 - t) * (β / N) ^ 2) *
              evariance (fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i))
                (critPole d s c β ρ N x t) ∧
          insertionDefect d s c β ρ N x ≤ C * deltaN d s N) ∧
      (firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≪
          withDensityReal ρ ∧
        firstMarginal (critCavity d s c β ρ N) ≪ withDensityReal ρ ∧
        eLpNorm (fun y =>
            ((firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))).rnDeriv
                (withDensityReal ρ) y).toReal -
              ((firstMarginal (critCavity d s c β ρ N)).rnDeriv (withDensityReal ρ) y).toReal)
            2 (withDensityReal ρ) ≤
          ENNReal.ofReal (C * Real.sqrt (Real.log N) / N)) ∧
      eLpNorm (fun y =>
          (((firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))).rnDeriv
              (withDensityReal ρ) y).toReal - 1) +
            β * Kop (periodicRiesz d s) (withDensityReal ρ)
              (fun y' => ((firstMarginal (modulatedGibbs (periodicRiesz d s) N β
                (withDensityReal ρ))).rnDeriv (withDensityReal ρ) y').toReal - 1) y -
            projMean (withDensityReal ρ) (insertionDefect d s c β ρ N) y)
          2 (withDensityReal ρ) ≤
        ENNReal.ofReal (C * Real.sqrt (Real.log N) / N) ∧
      (∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        firstMarginal (critPole d s c β ρ N x t) ≪ withDensityReal ρ ∧
          ∀ᵐ y ∂(withDensityReal ρ),
            |((firstMarginal (critPole d s c β ρ N x t)).rnDeriv (withDensityReal ρ) y).toReal -
                Real.exp (-(t * (β / N)) * gPlus d s c (x - y))| ≤
              C * Real.sqrt (deltaN d s N) * Real.exp (-(t * (β / N)) * gPlus d s c (x - y))) ∧
      (∀ᵐ y ∂(withDensityReal ρ),
        |((firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))).rnDeriv
            (withDensityReal ρ) y).toReal - 1| ≤ C * Real.sqrt (deltaN d s N)) := by
  obtain ⟨hs0, hsd⟩ := PoleCavityAux.hs_aux hd hcrit
  obtain ⟨CA, hA⟩ := CavResp.partA hd hs0 hsd β hβ hρ c hc
  obtain ⟨C2, hC20, h2⟩ := CavResp.item2 hd hcrit hβ hρ (c := c)
  obtain ⟨C3, hC30, h3⟩ := CavResp.item3 hd hcrit hβ hρ hc
  obtain ⟨C4, hC40, h4⟩ := CavResp.pole_prefactor hd hcrit hβ hρ hc
  obtain ⟨C5, hC50, h5⟩ := CavResp.item5 hd hcrit hβ hρ hc
  obtain ⟨Cm, hCm⟩ : ∃ Cm : ℝ, Cm = max (max (max CA C2) (max C3 C4)) C5 := ⟨_, rfl⟩
  have hCA : CA ≤ Cm := hCm ▸ ((le_max_left CA C2).trans ((le_max_left _ _).trans (le_max_left _ _)))
  have hC2 : C2 ≤ Cm := hCm ▸ ((le_max_right CA C2).trans ((le_max_left _ _).trans (le_max_left _ _)))
  have hC3 : C3 ≤ Cm := hCm ▸ ((le_max_left C3 C4).trans ((le_max_right _ _).trans (le_max_left _ _)))
  have hC4 : C4 ≤ Cm := hCm ▸ ((le_max_right C3 C4).trans ((le_max_right _ _).trans (le_max_left _ _)))
  have hC5 : C5 ≤ Cm := hCm ▸ (le_max_right _ _)
  refine ⟨Cm, fun N hN => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro x
    obtain ⟨a1, a2, a3, a4, a5⟩ := hA N hN x
    refine ⟨a1, a2, a3, a4, a5.trans ?_⟩
    have hδ : 0 ≤ deltaN d s N := (inv_nonneg.2 (by positivity : (0 : ℝ) ≤ N)).trans
      (MarginalAux.inv_le_deltaN (d := d) hs0 N (by omega))
    exact mul_le_mul_of_nonneg_right hCA hδ
  · obtain ⟨b1, b2, b3⟩ := h2 N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    refine ⟨b1, b2, b3.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC2 (Real.sqrt_nonneg _)) hN0.le
  · have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    refine (h3 N hN).trans (ENNReal.ofReal_le_ofReal ?_)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC3 (Real.sqrt_nonneg _)) hN0.le
  · intro x t ht
    obtain ⟨b1, b2⟩ := h4 N hN x t ht
    refine ⟨b1, b2.mono fun y hy => hy.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC4 (Real.sqrt_nonneg _))
      (Real.exp_pos _).le
  · exact (h5 N hN).mono fun y hy =>
      hy.trans (mul_le_mul_of_nonneg_right hC5 (Real.sqrt_nonneg _))

example := (@cavity_response_proof : type_of% @cavity_response)

end HRS

end
