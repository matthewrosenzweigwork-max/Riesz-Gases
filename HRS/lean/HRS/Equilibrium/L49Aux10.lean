/-
# HRS.Equilibrium.L49Aux10 — Proposition 4.9, part 10: `E f_i²` against `J(tλ)`

`l49_Q_close`: for every coordinate `i`, `|E_{P_t} g(x - y_i)² - J(tλ)| ≤ C √δ_N J(tλ)`
(`R:eq:diagonal-reduction`; `R:eq:prefactor` plus exchangeability of the pole law).
-/
import HRS.Equilibrium.L49Aux9

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace L49

variable {d : ℕ} {s c : ℝ}

open HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp

set_option maxHeartbeats 1600000 in
theorem l49_Q_close (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) {c : ℝ} (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → β / N ≤ 1 → ∀ x : Torus d, ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ∀ i : Fin (N - 1),
      |∫ Y, gPlus d s c (x - Y i) ^ 2 ∂(critPole d s c β ρ N x t) -
          l49_J d s c ρ x (t * (β / N))| ≤
        C * Real.sqrt (deltaN d s N) * l49_J d s c ρ x (t * (β / N)) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨Cp, hCp0, hCp⟩ := CavResp.pole_prefactor hd hcrit hβ hρ hc
  obtain ⟨Csl, hCsl0, hsl⟩ := l49_sqlog hd hcrit hβ hρ hc
  have hgm := measurable_gPlus hd hs0 hsd c
  have hμ := isProbabilityMeasure_mu hρ
  refine ⟨Cp, hCp0, fun N hN hlamle x t ht i => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  have hn1 : 0 < N - 1 := by omega
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
  set u : ℝ := t * (β / N) with hu
  have hu0 : 0 < u := mul_pos ht.1 (by positivity)
  have hu1 : u ≤ 1 := by
    have : t * (β / N) ≤ 1 * (β / N) := mul_le_mul_of_nonneg_right ht.2 hlam
    linarith
  obtain ⟨hGe, hJ0, -⟩ := hsl u hu0 hu1 x
  obtain ⟨hac, hae⟩ := hCp N hN x t ht'
  haveI hPprob : IsProbabilityMeasure (critPole d s c β ρ N x t) := by
    rw [critPole_eq_poleLaw (c := c) hd hs0 hsd β hβ hρ hN x t]
    exact pole_isProb hd hs0 hsd β hρ (N - 1) (β / N) hlam x t ht.1.le
  -- the `i`-th marginal is the first marginal
  have hexch := MarginalAux.poleLaw_exchangeable hd hs0 hsd β hρ (N - 1) (β / N) hlam x t
  have hνt : (critPole d s c β ρ N x t).map (fun Y : Config d (N - 1) => Y i) =
      firstMarginal (critPole d s c β ρ N x t) := by
    rw [critPole_eq_poleLaw (c := c) hd hs0 hsd β hβ hρ hN x t]
    have : firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) =
        (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t).map
          (fun Y : Config d (N - 1) => Y ⟨0, hn1⟩) := by
      unfold firstMarginal; rw [dif_pos hn1]
    rw [this]
    exact hexch.marginal_eq i ⟨0, hn1⟩
  set G : Torus d → ℝ := fun y => gPlus d s c (x - y) ^ 2 with hG
  set e : Torus d → ℝ := fun y => Real.exp (-u * gPlus d s c (x - y)) with he
  have hGm : Measurable G := (hgm.comp (measurable_const.sub measurable_id)).pow_const 2
  have hem : Measurable e :=
    Real.measurable_exp.comp (measurable_const.mul (hgm.comp (measurable_const.sub measurable_id)))
  have hG0 : ∀ y, 0 ≤ G y := fun y => sq_nonneg _
  have he0 : ∀ y, 0 < e y := fun y => Real.exp_pos _
  set ν := firstMarginal (critPole d s c β ρ N x t) with hν
  haveI hνprob : IsProbabilityMeasure ν := CavResp.isProb_firstMarginal hn1 _
  set rn : Torus d → ℝ := fun y => (ν.rnDeriv (withDensityReal ρ) y).toReal with hrn
  have hrnm : Measurable rn := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hQ : ∫ Y, gPlus d s c (x - Y i) ^ 2 ∂(critPole d s c β ρ N x t) =
      ∫ y, rn y * G y ∂(withDensityReal ρ) := by
    have h1 : ∫ Y, G (Y i) ∂(critPole d s c β ρ N x t) =
        ∫ y, G y ∂((critPole d s c β ρ N x t).map (fun Y : Config d (N - 1) => Y i)) :=
      (integral_map (measurable_pi_apply i).aemeasurable hGm.aestronglyMeasurable).symm
    rw [hνt] at h1
    have h2 : ∫ y, rn y * G y ∂(withDensityReal ρ) = ∫ y, G y ∂ν := integral_toReal_rnDeriv_mul hac
    exact h1.trans h2.symm
  have hJ : l49_J d s c ρ x u = ∫ y, G y * e y ∂(withDensityReal ρ) := rfl
  set cc : ℝ := Cp * Real.sqrt (deltaN d s N) with hcc
  have hcc0 : 0 ≤ cc := by positivity
  have hdom : ∀ᵐ y ∂(withDensityReal ρ), ‖(rn y - e y) * G y‖ ≤ cc * (G y * e y) := by
    filter_upwards [hae] with y hy
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hG0 y)]
    have : |rn y - e y| ≤ cc * e y := hy
    calc |rn y - e y| * G y ≤ (cc * e y) * G y := mul_le_mul_of_nonneg_right this (hG0 y)
      _ = cc * (G y * e y) := by ring
  have hGe' : Integrable (fun y => G y * e y) (withDensityReal ρ) := hGe
  have hint1 : Integrable (fun y => (rn y - e y) * G y) (withDensityReal ρ) :=
    Integrable.mono' (hGe'.const_mul cc) ((hrnm.sub hem).mul hGm).aestronglyMeasurable hdom
  have hint2 : Integrable (fun y => rn y * G y) (withDensityReal ρ) := by
    have := hint1.add hGe'
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply]; ring
  rw [hQ, hJ, ← integral_sub hint2 hGe']
  have e1 : ∀ y, rn y * G y - G y * e y = (rn y - e y) * G y := fun y => by ring
  simp_rw [e1]
  rw [← Real.norm_eq_abs]
  have := norm_integral_le_of_norm_le (hGe'.const_mul cc) hdom
  refine this.trans (le_of_eq ?_)
  rw [integral_const_mul, hcc]

end L49

end HRS

end
