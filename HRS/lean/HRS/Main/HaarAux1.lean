import HRS.Energy.Modulated
import HRS.Energy.Coercivity

/-!
# Haar reference: the first marginal of the modulated Gibbs law (packet HAAR)

For the uniform reference `μ = volume` on `𝕋^d` the pair energy `F_N(·, volume)` depends only on
differences `X i - X j` (the one-body terms `∫ g(x - y) dy` do not depend on `x`).  Hence the
modulated Gibbs law `Q_{N,β}(volume)` is invariant under the diagonal translations `X ↦ X + a`,
its first marginal is a translation-invariant probability measure on the compact group `𝕋^d`, and
it equals `volume` by uniqueness of Haar measure.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-- The one-body integral `∫ g(x - y) dvol(y)` does not depend on `x`. -/
theorem haar_integral_sub_const (g : Torus d → ℝ) (x x' : Torus d) :
    ∫ y, g (x - y) ∂(volume : Measure (Torus d)) = ∫ y, g (x' - y) ∂(volume : Measure (Torus d)) := by
  have h := integral_add_right_eq_self (μ := (volume : Measure (Torus d)))
    (fun y => g (x' - y)) (x' - x)
  have e : ∀ y : Torus d, x' - (y + (x' - x)) = x - y := fun y => by abel
  simp only [e] at h
  exact h

/-- The common value `∫ g(0 - y) dvol(y)` of the one-body integrals. -/
def haar_const (g : Torus d → ℝ) : ℝ := ∫ y, g (0 - y) ∂(volume : Measure (Torus d))

theorem haar_integral_eq_const (g : Torus d → ℝ) (x : Torus d) :
    ∫ y, g (x - y) ∂(volume : Measure (Torus d)) = haar_const g :=
  haar_integral_sub_const g x 0

/-- Closed form of the modulated energy at the uniform reference. -/
theorem haar_energy_eq (hN : 1 ≤ N) (g : Torus d → ℝ) (X : Config d N) :
    modulatedEnergyKernel g X volume =
      (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, g (X i - X j)
        - (1 / 2) * haar_const g := by
  unfold modulatedEnergyKernel modulatedEnergy
  simp only [haar_integral_eq_const g]
  simp only [integral_const, probReal_univ, one_smul, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  field_simp
  ring

/-- The energy at the uniform reference is invariant under diagonal translations. -/
theorem haar_energy_shift (hN : 1 ≤ N) (g : Torus d → ℝ) (X : Config d N) (a : Torus d) :
    modulatedEnergyKernel g (fun i => X i + a) volume = modulatedEnergyKernel g X volume := by
  rw [haar_energy_eq hN, haar_energy_eq hN]
  simp only [add_sub_add_right_eq_sub]

/-- Lower bound for the pair sum when `g ≥ -B`, `B ≥ 0`. -/
theorem haar_pair_sum_lower (g : Torus d → ℝ) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x, -B ≤ g x)
    (X : Config d N) :
    -((N : ℝ) ^ 2 * B) ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, g (X i - X j) := by
  have hrow : ∀ i : Fin N, -((N : ℝ) * B) ≤ ∑ j ∈ Finset.univ.erase i, g (X i - X j) := by
    intro i
    have h1 : ∑ j ∈ Finset.univ.erase i, (-B) ≤ ∑ j ∈ Finset.univ.erase i, g (X i - X j) :=
      Finset.sum_le_sum fun j _ => hB _
    have h2 : ∑ j ∈ Finset.univ.erase i, (-B) = -(((Finset.univ.erase i).card : ℝ) * B) := by
      rw [Finset.sum_const, nsmul_eq_mul]; ring
    have h3 : (Finset.univ.erase i).card ≤ N := by
      simpa using Finset.card_le_univ (Finset.univ.erase i)
    have h3' : ((Finset.univ.erase i).card : ℝ) ≤ N := by exact_mod_cast h3
    have h4 : ((Finset.univ.erase i).card : ℝ) * B ≤ (N : ℝ) * B :=
      mul_le_mul_of_nonneg_right h3' hB0
    linarith
  calc -((N : ℝ) ^ 2 * B) = ∑ _i : Fin N, -((N : ℝ) * B) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    _ ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, g (X i - X j) := Finset.sum_le_sum fun i _ => hrow i

/-- Lower bound for the modulated energy at the uniform reference. -/
theorem haar_energy_lower (g : Torus d → ℝ) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x, -B ≤ g x)
    (hN : 1 ≤ N) (X : Config d N) :
    -(B / 2) - (1 / 2) * haar_const g ≤ modulatedEnergyKernel g X volume := by
  rw [haar_energy_eq hN]
  have hS := haar_pair_sum_lower (N := N) g hB0 hB X
  have hpos : (0 : ℝ) ≤ 1 / (2 * (N : ℝ) ^ 2) := by positivity
  have hm := mul_le_mul_of_nonneg_left hS hpos
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have e : 1 / (2 * (N : ℝ) ^ 2) * (-((N : ℝ) ^ 2 * B)) = -(B / 2) := by
    field_simp
  linarith

/-- Measurability of the modulated energy at the uniform reference. -/
theorem haar_measurable_energy {g : Torus d → ℝ} (hg : Measurable g) (hN : 1 ≤ N) :
    Measurable fun X : Config d N => modulatedEnergyKernel g X volume := by
  have e : (fun X : Config d N => modulatedEnergyKernel g X volume) = fun X =>
      (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, g (X i - X j)
        - (1 / 2) * haar_const g :=
    funext fun X => haar_energy_eq hN g X
  rw [e]
  refine Measurable.sub (Measurable.const_mul ?_ _) measurable_const
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    hg.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))

/-- The Boltzmann factor at the uniform reference is integrable (it is bounded). -/
theorem haar_boltz_integrable {g : Torus d → ℝ} (hg : Measurable g) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, -B ≤ g x) (β : ℝ) (hβ : 0 < β) (hN : 1 ≤ N) :
    Integrable (fun X : Config d N => Real.exp (-β * N * modulatedEnergyKernel g X volume))
      (Measure.pi fun _ : Fin N => (volume : Measure (Torus d))) := by
  have hmeas : Measurable fun X : Config d N => Real.exp (-β * N * modulatedEnergyKernel g X volume) :=
    Real.measurable_exp.comp (measurable_const.mul (haar_measurable_energy hg hN))
  refine Integrable.of_bound hmeas.aestronglyMeasurable
    (Real.exp (β * N * (B / 2 + (1 / 2) * haar_const g))) (Filter.Eventually.of_forall fun X => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hF := haar_energy_lower g hB0 hB hN X
  have hβN : (0 : ℝ) ≤ β * N := by positivity
  have := mul_le_mul_of_nonneg_left (show -modulatedEnergyKernel g X volume ≤
      B / 2 + (1 / 2) * haar_const g by linarith) hβN
  linarith [this]

/-- The diagonal translation `X ↦ X + a` of configurations is measurable. -/
theorem haar_shift_measurable (a : Torus d) :
    Measurable fun X : Config d N => fun i => X i + a :=
  measurable_pi_iff.mpr fun i => ((continuous_apply i).add continuous_const).measurable

/-- The product Haar measure is invariant under the diagonal translation. -/
theorem haar_pi_shift_map (a : Torus d) :
    (Measure.pi fun _ : Fin N => (volume : Measure (Torus d))).map
        (fun X : Config d N => fun i => X i + a) =
      Measure.pi fun _ : Fin N => (volume : Measure (Torus d)) := by
  have hmp := measurePreserving_pi (fun _ : Fin N => (volume : Measure (Torus d)))
    (fun _ : Fin N => (volume : Measure (Torus d)))
    (f := fun _ : Fin N => fun x : Torus d => x + a)
    (fun _ => measurePreserving_add_right (volume : Measure (Torus d)) a)
  exact hmp.map_eq

/-- The modulated Gibbs law at the uniform reference is invariant under diagonal translations. -/
theorem haar_gibbs_shift_invariant {g : Torus d → ℝ} (hg : Measurable g) (hN : 1 ≤ N) (β : ℝ)
    (a : Torus d) :
    (modulatedGibbs g N β (volume : Measure (Torus d))).map (fun X : Config d N => fun i => X i + a)
      = modulatedGibbs g N β (volume : Measure (Torus d)) := by
  have hTm := haar_shift_measurable (N := N) (d := d) a
  have hPT := haar_pi_shift_map (N := N) (d := d) a
  have hmp : MeasurePreserving (fun X : Config d N => fun i => X i + a)
      (Measure.pi fun _ : Fin N => (volume : Measure (Torus d)))
      (Measure.pi fun _ : Fin N => (volume : Measure (Torus d))) := ⟨hTm, hPT⟩
  have hwm : Measurable fun X : Config d N =>
      ENNReal.ofReal (Real.exp (-β * N * modulatedEnergyKernel g X volume)) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul (haar_measurable_energy hg hN)))
  have hwT : ∀ X : Config d N,
      ENNReal.ofReal (Real.exp (-β * N * modulatedEnergyKernel g (fun i => X i + a) volume)) =
        ENNReal.ofReal (Real.exp (-β * N * modulatedEnergyKernel g X volume)) := fun X => by
    rw [haar_energy_shift hN g X a]
  have key : Measure.map (fun X : Config d N => fun i => X i + a)
      ((Measure.pi fun _ : Fin N => (volume : Measure (Torus d))).withDensity
        fun X : Config d N => ENNReal.ofReal (Real.exp (-β * N * modulatedEnergyKernel g X volume))) =
      (Measure.pi fun _ : Fin N => (volume : Measure (Torus d))).withDensity
        fun X : Config d N => ENNReal.ofReal (Real.exp (-β * N * modulatedEnergyKernel g X volume)) := by
    ext A hA
    rw [Measure.map_apply hTm hA, withDensity_apply _ (hTm hA), withDensity_apply _ hA]
    calc ∫⁻ X in (fun X : Config d N => fun i => X i + a) ⁻¹' A,
          ENNReal.ofReal (Real.exp (-β * N * modulatedEnergyKernel g X volume))
            ∂(Measure.pi fun _ : Fin N => (volume : Measure (Torus d)))
        = ∫⁻ X in (fun X : Config d N => fun i => X i + a) ⁻¹' A,
            ENNReal.ofReal (Real.exp (-β * N * modulatedEnergyKernel g
              ((fun X : Config d N => fun i => X i + a) X) volume))
            ∂(Measure.pi fun _ : Fin N => (volume : Measure (Torus d))) := by
          simp only [hwT]
      _ = ∫⁻ X in A, ENNReal.ofReal (Real.exp (-β * N * modulatedEnergyKernel g X volume))
            ∂(Measure.pi fun _ : Fin N => (volume : Measure (Torus d))) :=
          hmp.setLIntegral_comp_preimage hA hwm
  unfold modulatedGibbs
  rw [Measure.map_smul, key]
  exact hTm.aemeasurable

/-- A translation-invariant probability law on configurations has Haar first marginal. -/
theorem haar_firstMarginal_of_invariant {Q : Measure (Config d N)} [IsProbabilityMeasure Q]
    (hN : 1 ≤ N) (hQ : ∀ a : Torus d, Q.map (fun X : Config d N => fun i => X i + a) = Q) :
    firstMarginal Q = (volume : Measure (Torus d)) := by
  have h0 : 0 < N := hN
  have he : Measurable (fun X : Config d N => X ⟨0, h0⟩) := measurable_pi_apply _
  have hfm : firstMarginal Q = Q.map (fun X : Config d N => X ⟨0, h0⟩) := by
    unfold firstMarginal
    rw [dif_pos h0]
  have hinv : ∀ a : Torus d,
      (firstMarginal Q).map (fun x : Torus d => x + a) = firstMarginal Q := by
    intro a
    have hcomp : ((fun x : Torus d => x + a) ∘ (fun X : Config d N => X ⟨0, h0⟩)) =
        (fun X : Config d N => X ⟨0, h0⟩) ∘ (fun X : Config d N => fun i => X i + a) := rfl
    rw [hfm, Measure.map_map (measurable_add_const a) he, hcomp,
      ← Measure.map_map he (haar_shift_measurable (N := N) (d := d) a), hQ a]
  have hprob : IsProbabilityMeasure (firstMarginal Q) := by
    rw [hfm]
    infer_instance
  haveI : Measure.IsAddLeftInvariant (firstMarginal Q) := ⟨fun a => by
    have e : (fun x : Torus d => a + x) = fun x => x + a := funext fun x => add_comm a x
    rw [e]
    exact hinv a⟩
  have hc := Measure.isAddInvariant_eq_smul_of_compactSpace (firstMarginal Q)
    (volume : Measure (Torus d))
  have hmass := congrArg (fun ν : Measure (Torus d) => ν Set.univ) hc
  have hc1 : (firstMarginal Q).addHaarScalarFactor (volume : Measure (Torus d)) = 1 := by
    simpa using hmass.symm
  rw [hc, hc1, one_smul]

/-- Proposition 2.10 `critical_haar_unbiased` at the level of the modulated Gibbs law: at the
uniform reference the first marginal of `Q_{N,β}(dx)` is `dx`, for `d ≥ 2`, `β > 0`, `N ≥ 1`. -/
theorem haar_firstMarginal_volume (hd : 2 ≤ d) (β : ℝ) (hβ : 0 < β) (N : ℕ) (hN : 1 ≤ N) :
    firstMarginal (modulatedGibbs (periodicRiesz d ((d : ℝ) / 2)) N β
      (volume : Measure (Torus d))) = volume := by
  have hd1 : 1 ≤ d := by omega
  have hs0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < d := by
    have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hg : Measurable (periodicRiesz d ((d : ℝ) / 2)) :=
    CoercAux.measurable_periodicRiesz_one hd1 hs0 hsd
  obtain ⟨B, hB⟩ := periodicRiesz_ge hd hs0 hsd
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  have hB' : ∀ x, -max B 0 ≤ periodicRiesz d ((d : ℝ) / 2) x := fun x =>
    (neg_le_neg (le_max_left B 0)).trans (hB x)
  have hint := haar_boltz_integrable hg hB0 hB' β hβ hN
  have hK : 0 < gibbsNormalizer (periodicRiesz d ((d : ℝ) / 2)) N β (volume : Measure (Torus d)) := by
    unfold gibbsNormalizer
    exact integral_exp_pos hint
  haveI : IsProbabilityMeasure (modulatedGibbs (periodicRiesz d ((d : ℝ) / 2)) N β
      (volume : Measure (Torus d))) :=
    modulatedGibbs_isProbabilityMeasure _ β _ hK hint
  exact haar_firstMarginal_of_invariant hN (fun a => haar_gibbs_shift_invariant hg hN β a)

end HRS
