import HRS.Uniform.Comparison
import HRS.Uniform.Q14Aux7
import HRS.Prob.Metrics
import HRS.Energy.Commutator.RenormSelf

/-!
# Q12, part W1: the torus Wasserstein distance: coupling bound and triangle inequality
-/

noncomputable section

open HRS MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q12

variable {d : ℕ}

lemma q12_tdist_nonneg (x y : Torus d) : 0 ≤ Torus.tdist x y := by
  unfold Torus.tdist; exact norm_nonneg _

lemma q12_ofReal_tdist_rpow (x y : Torus d) {p : ℝ} (hp : 0 ≤ p) :
    ENNReal.ofReal (Torus.tdist x y ^ p) = ENNReal.ofReal (Torus.tdist x y) ^ p :=
  (ENNReal.ofReal_rpow_of_nonneg (q12_tdist_nonneg x y) hp).symm

lemma q12_tdist_tri (x y z : Torus d) : Torus.tdist x z ≤ Torus.tdist x y + Torus.tdist y z :=
  HRS.Commutator.Renorm.tdist_tri x y z

/-- A coupling bounds `W_p` by its cost. -/
lemma q12_W_le_cost {p : ℝ} {μ ν : Measure (Torus d)} {π : Measure (Torus d × Torus d)}
    (h1 : π.map Prod.fst = μ) (h2 : π.map Prod.snd = ν) :
    torusWassersteinE p μ ν ≤ (∫⁻ z, ENNReal.ofReal (Torus.tdist z.1 z.2 ^ p) ∂π) ^ (1 / p) :=
  iInf_le (fun π : {π : Measure (Torus d × Torus d) // π.map Prod.fst = μ ∧ π.map Prod.snd = ν} =>
    (∫⁻ z, ENNReal.ofReal (Torus.tdist z.1 z.2 ^ p) ∂π.1) ^ (1 / p)) ⟨π, h1, h2⟩


lemma q12_measurable_tdist : Measurable fun p : Torus d × Torus d => Torus.tdist p.1 p.2 :=
  Uniform.Q14.q14_continuous_tdist.measurable

lemma q12_meas_f (p : ℝ) : Measurable fun z : Torus d × Torus d =>
    ENNReal.ofReal (Torus.tdist z.1 z.2) ^ p :=
  q12_measurable_tdist.ennreal_ofReal.pow_const p

lemma q12_meas_u : Measurable fun w : (Torus d × Torus d) × Torus d =>
    ENNReal.ofReal (Torus.tdist w.1.1 w.1.2) :=
  (q12_measurable_tdist.comp measurable_fst).ennreal_ofReal

lemma q12_meas_v : Measurable fun w : (Torus d × Torus d) × Torus d =>
    ENNReal.ofReal (Torus.tdist w.1.2 w.2) := by
  have hw : Measurable fun w : (Torus d × Torus d) × Torus d => (w.1.2, w.2) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have ht : Measurable ((fun p : Torus d × Torus d => Torus.tdist p.1 p.2) ∘
      (fun w : (Torus d × Torus d) × Torus d => (w.1.2, w.2))) :=
    Measurable.comp q12_measurable_tdist hw
  exact ht.ennreal_ofReal

lemma q12_coupling_prob {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    {π : Measure (Torus d × Torus d)} (h : π.map Prod.fst = μ) : IsProbabilityMeasure π :=
  Uniform.Q14.q14_coupling_prob h

/-- Triangle inequality for `W_p` on the torus (gluing). -/
theorem q12_W_triangle (p : ℝ) (hp : 1 ≤ p) (P Q R : Measure (Torus d))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure R] :
    torusWassersteinE p P R ≤ torusWassersteinE p P Q + torusWassersteinE p Q R := by
  have hp0 : 0 < p := by linarith
  have : Nonempty (Torus d) := ⟨0⟩
  have key : ∀ π₁ : Measure (Torus d × Torus d), π₁.map Prod.fst = P → π₁.map Prod.snd = Q →
      ∀ π₂ : Measure (Torus d × Torus d), π₂.map Prod.fst = Q → π₂.map Prod.snd = R →
      torusWassersteinE p P R ≤ (∫⁻ z, ENNReal.ofReal (Torus.tdist z.1 z.2 ^ p) ∂π₁) ^ (1 / p) +
        (∫⁻ z, ENNReal.ofReal (Torus.tdist z.1 z.2 ^ p) ∂π₂) ^ (1 / p) := by
    intro π₁ h₁1 h₁2 π₂ h₂1 h₂2
    have := q12_coupling_prob (μ := P) h₁1
    have := q12_coupling_prob (μ := Q) h₂1
    obtain ⟨ν, hν, hν1, hν2⟩ := exists_glue (Q := Q) h₁2 h₂1
    let g : (Torus d × Torus d) × Torus d → Torus d × Torus d := fun w => (w.1.1, w.2)
    have hg : Measurable g := by fun_prop
    have hπ1 : (ν.map g).map Prod.fst = P := by
      rw [Measure.map_map measurable_fst hg, ← h₁1, ← hν1, Measure.map_map measurable_fst
        measurable_fst]
      rfl
    have hπ2 : (ν.map g).map Prod.snd = R := by
      rw [Measure.map_map measurable_snd hg, ← h₂2, ← hν2, Measure.map_map measurable_snd
        (by fun_prop)]
      rfl
    refine (q12_W_le_cost hπ1 hπ2).trans ?_
    simp only [q12_ofReal_tdist_rpow _ _ hp0.le]
    have hf := q12_meas_f (d := d) p
    have hum := q12_meas_u (d := d)
    have hvm := q12_meas_v (d := d)
    have hcost1 : ∫⁻ w : (Torus d × Torus d) × Torus d, ENNReal.ofReal (Torus.tdist w.1.1 w.1.2) ^ p ∂ν =
        ∫⁻ z, ENNReal.ofReal (Torus.tdist z.1 z.2) ^ p ∂π₁ := by
      have h := lintegral_map (μ := ν) hf (measurable_fst (α := Torus d × Torus d) (β := Torus d))
      rw [hν1] at h
      exact h.symm
    have hcost2 : ∫⁻ w : (Torus d × Torus d) × Torus d, ENNReal.ofReal (Torus.tdist w.1.2 w.2) ^ p ∂ν =
        ∫⁻ z, ENNReal.ofReal (Torus.tdist z.1 z.2) ^ p ∂π₂ := by
      have h := lintegral_map (μ := ν) hf (g := fun w : (Torus d × Torus d) × Torus d => (w.1.2, w.2))
        (by fun_prop)
      rw [hν2] at h
      exact h.symm
    calc (∫⁻ z, ENNReal.ofReal (Torus.tdist z.1 z.2) ^ p ∂ν.map g) ^ (1 / p)
        ≤ (∫⁻ w, ENNReal.ofReal (Torus.tdist (g w).1 (g w).2) ^ p ∂ν) ^ (1 / p) :=
          ENNReal.rpow_le_rpow (lintegral_map_le _ hg.aemeasurable) (by positivity)
      _ ≤ (∫⁻ w : (Torus d × Torus d) × Torus d, (ENNReal.ofReal (Torus.tdist w.1.1 w.1.2) +
            ENNReal.ofReal (Torus.tdist w.1.2 w.2)) ^ p ∂ν) ^ (1 / p) := by
          refine ENNReal.rpow_le_rpow (lintegral_mono fun w => ?_) (by positivity)
          refine ENNReal.rpow_le_rpow ?_ hp0.le
          simp only [g]
          rw [← ENNReal.ofReal_add (q12_tdist_nonneg _ _) (q12_tdist_nonneg _ _)]
          exact ENNReal.ofReal_le_ofReal (q12_tdist_tri _ _ _)
      _ ≤ (∫⁻ w : (Torus d × Torus d) × Torus d, ENNReal.ofReal (Torus.tdist w.1.1 w.1.2) ^ p ∂ν) ^ (1 / p) +
          (∫⁻ w : (Torus d × Torus d) × Torus d, ENNReal.ofReal (Torus.tdist w.1.2 w.2) ^ p ∂ν) ^ (1 / p) :=
          ENNReal.lintegral_Lp_add_le hum.aemeasurable hvm.aemeasurable hp
      _ = _ := by rw [hcost1, hcost2]
  simp only [q12_ofReal_tdist_rpow _ _ hp0.le] at key
  rw [← tsub_le_iff_right]
  refine le_iInf fun π₁ => ?_
  rw [tsub_le_iff_right, ← tsub_le_iff_left]
  refine le_iInf fun π₂ => ?_
  rw [tsub_le_iff_left]
  simpa [q12_ofReal_tdist_rpow _ _ hp0.le] using key π₁.1 π₁.2.1 π₁.2.2 π₂.1 π₂.2.1 π₂.2.2

/-- A coupling realised by two random variables on one probability space bounds `W_p`. -/
theorem q12_W_le_of_coupling {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (p : ℝ) (hp : 1 ≤ p) (X Y : Ω → Torus d) (hX : Measurable X) (hY : Measurable Y) :
    torusWassersteinE p (P.map X) (P.map Y) ≤
      (∫⁻ ω, ENNReal.ofReal (Torus.tdist (X ω) (Y ω) ^ p) ∂P) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hm : Measurable fun ω => (X ω, Y ω) := hX.prodMk hY
  have h1 : (P.map fun ω => (X ω, Y ω)).map Prod.fst = P.map X := by
    rw [Measure.map_map measurable_fst hm]; rfl
  have h2 : (P.map fun ω => (X ω, Y ω)).map Prod.snd = P.map Y := by
    rw [Measure.map_map measurable_snd hm]; rfl
  refine (q12_W_le_cost h1 h2).trans ?_
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  exact lintegral_map_le (fun z : Torus d × Torus d => ENNReal.ofReal (Torus.tdist z.1 z.2 ^ p))
    hm.aemeasurable

end HRS.Uniform.Q12
