import HRS.Main.MixEnt7
import HRS.Equilibrium.Preparation

/-!
# MIXENT 8: `h ∈ L^{p₀}(Q)` and `J_N ≤ C` for the mixture preparation when `s = 0` (lemma M5)

TeX L6957-6962: "For its logarithmic `L^p` assumption, let `r_N` be its density relative to `(μ°)^{⊗N}`.
Every fixed moment of `r_N` is uniformly bounded ... Choose `p₀ - 1` sufficiently small that the remaining
positive exponential of `N F_N` is covered by the same small-attractive logarithmic partition bound
(`log_prep_small_negative`). Thus `J_N = O(1)`."
-/

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

/-- **M5** (`s = 0`): there is `p₀ > 1` (depending only on the setting `S`) such that for every smooth
`b` with `μ°(b) = 0` and every `a₀` there is `C` with, for all `N ≥ 2` with `4 a₀² (⨆|b|)² ≤ N`:
`dmix/dQ_N^0 ∈ L^{p₀}(Q_N^0)` and `J_N ≤ C N δ_N` (indeed `N δ_N = 1` for `s = 0`). -/
theorem mx_Lp_mixture (S : PreparedData d) (hs : S.s = 0) :
    ∃ p₀ : ℝ, 1 < p₀ ∧ ∀ (b : Torus d → ℝ), Torus.IsSmooth b → pair S.μ0 b = 0 → ∀ a₀ : ℝ,
      ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → 4 * a₀ ^ 2 * (⨆ x, |b x|) ^ 2 ≤ (N : ℝ) →
        MemLp (fun Y => (((mixturePrep S.μ0 b a₀ N).rnDeriv (S.refMeasure N 0)) Y).toReal)
          (ENNReal.ofReal p₀) (S.refMeasure N 0) ∧
        S.J N (mixturePrep S.μ0 b a₀ N) p₀ ≤ C * ((N : ℝ) * deltaN d S.s N) := by
  haveI := isProb_withDensityReal S.hρ0.density
  haveI hprob : IsProbabilityMeasure S.μ0 := by unfold PreparedData.μ0; infer_instance
  have hcont : Continuous S.ρ0 := mova_continuous_of_isCk (mova_isCk_two_of_smooth S.hρ0.smooth)
  obtain ⟨Mρ, hMρ0, hMρ⟩ := exists_abs_bound hcont
  have hneg : ∃ a : ℝ, 0 < a ∧ ∀ B₀ : ℝ, ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ γ ∈ Set.Icc (-a) B₀,
      modNormalizerE (periodicRiesz d S.s) N γ S.μ0 ≤ ENNReal.ofReal C := by
    rw [hs]
    exact log_prep_small_negative S.hd S.ρ0 S.hρ0.density Mρ
      (fun x => (le_abs_self _).trans (hMρ x))
  obtain ⟨a, ha, hneg'⟩ := hneg
  obtain ⟨Cneg, hCneg⟩ := hneg' 0
  obtain ⟨Cp, hCp0, hCp⟩ := mx_pressure_data S
  set ε : ℝ := min (1 / 3) (a / (3 * S.β)) with hε
  have hε0 : 0 < ε := lt_min (by norm_num) (div_pos ha (by have := S.hβ; positivity))
  have hε1 : ε ≤ 1 / 3 := min_le_left _ _
  have hε2 : 3 * ε * S.β ≤ a := by
    have h1 : ε ≤ a / (3 * S.β) := min_le_right _ _
    have := S.hβ
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  refine ⟨1 + ε, by linarith, fun b hb hb0 a₀ => ?_⟩
  have hbc : Continuous b := therm_continuous_of_smooth hb
  have hbm : Measurable b := hbc.measurable
  have hb0' : ∫ x, b x ∂S.μ0 = 0 := hb0
  set r : ℝ := (1 + ε) * (3 / 2) with hr
  have hr1 : 1 ≤ r := by rw [hr]; nlinarith
  have hr2 : r ≤ 2 := by rw [hr]; nlinarith
  set σ2 : ℝ := ∫ x, b x ^ 2 ∂S.μ0 with hσ2
  set M1 : ℝ := Real.exp (r ^ 2 * a₀ ^ 2 * σ2) with hM1
  set Cn : ℝ := max Cneg 1 with hCn
  have hCn0 : 0 < Cn := lt_of_lt_of_le one_pos (le_max_right _ _)
  set Mf : ℝ := Real.exp Cp * M1 ^ (1 / (3 / 2 : ℝ)) * Cn ^ (1 / (3 : ℝ)) with hMf
  have hMf0 : 0 < Mf := by positivity
  refine ⟨2 + max 0 (Real.log Mf / (1 + ε)), by positivity, fun N hN hsup => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hB := mx_hB_of_sup hb hsup
  have hbM : ∀ x, |b x| ≤ ⨆ x, |b x| := mx_abs_le_iSup hb
  obtain ⟨hKi, hKl, hKu⟩ := hCp N hN
  -- N δ_N = 1 for s = 0
  have hδ1 : (N : ℝ) * deltaN d S.s N = 1 := by
    have hd2 : (0 : ℝ) < (d : ℝ) / 2 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast S.hd
      linarith
    unfold deltaN
    rw [if_pos (by rw [hs]; exact hd2)]
    have : (N : ℝ) ≠ 0 := by positivity
    field_simp
  -- the identity and the Hölder bound
  have hid := mx_lintegral_rnDeriv_rpow S hbm hbM hb0 a₀ hN hB hKi (p := 1 + ε) (by linarith)
  have hhol := mx_holder S hbm a₀ N ε
  have hRb := mx_lintegral_R_rpow_le S.μ0 hbm hbM hb0' a₀ hN1 hB hr1 hr2
  have hNb : modNormalizerE (periodicRiesz d S.s) N (-3 * ε * S.β) S.μ0 ≤ ENNReal.ofReal Cn :=
    (hCneg N hN (-3 * ε * S.β) ⟨by linarith, by nlinarith [S.hβ]⟩).trans
      (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hKb : mxK S N ^ ε ≤ Real.exp Cp := by
    have h1 : mxK S N ≤ Real.exp Cp := by
      have := hKu; rwa [show Cp * (N : ℝ) * deltaN d S.s N = Cp * ((N : ℝ) * deltaN d S.s N) by ring,
        hδ1, mul_one] at this
    have hKpos : 0 < mxK S N := lt_of_lt_of_le (Real.exp_pos _) hKl
    calc mxK S N ^ ε ≤ (Real.exp Cp) ^ ε := Real.rpow_le_rpow hKpos.le h1 hε0.le
      _ = Real.exp (Cp * ε) := by rw [← Real.exp_mul]
      _ ≤ Real.exp Cp := Real.exp_le_exp.2 (by nlinarith)
  have hmain : ∫⁻ X, ((mixturePrep S.μ0 b a₀ N).rnDeriv (S.refMeasure N 0) X) ^ (1 + ε)
      ∂(S.refMeasure N 0) ≤ ENNReal.ofReal Mf := by
    rw [hid]
    have e1 : (1 + ε) - 1 = ε := by ring
    simp only [e1] at hhol ⊢
    calc ENNReal.ofReal (mxK S N ^ ε) * ∫⁻ X, ENNReal.ofReal (mxR b a₀ N X) ^ (1 + ε) *
          ENNReal.ofReal (Real.exp (ε * (S.β * mxW S N X))) ∂(Measure.pi fun _ : Fin N => S.μ0)
        ≤ ENNReal.ofReal (Real.exp Cp) * ((ENNReal.ofReal M1) ^ (1 / (3 / 2 : ℝ)) *
            (ENNReal.ofReal Cn) ^ (1 / (3 : ℝ))) := by
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal hKb) (hhol.trans ?_)
          refine mul_le_mul' ?_ ?_
          · exact ENNReal.rpow_le_rpow hRb (by norm_num)
          · exact ENNReal.rpow_le_rpow hNb (by norm_num)
      _ = ENNReal.ofReal Mf := by
          have hM1pos : 0 < M1 := Real.exp_pos _
          rw [hMf, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_rpow_of_pos hM1pos, ENNReal.ofReal_rpow_of_pos hCn0, mul_assoc]
  obtain ⟨hMem, hlog⟩ := HRS.T25.t25_J_of_lintegral (S.refMeasure N 0) (mixturePrep S.μ0 b a₀ N)
    (p := 1 + ε) (by linarith) hMf0 hmain
  refine ⟨hMem, ?_⟩
  unfold PreparedData.J
  have hm0 : 0 ≤ max 0 (Real.log Mf / (1 + ε)) := le_max_left _ _
  rw [hδ1] at *
  nlinarith [hlog]

end Main

end HRS
