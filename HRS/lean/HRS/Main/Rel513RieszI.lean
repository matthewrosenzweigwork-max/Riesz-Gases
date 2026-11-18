import HRS.Main.Rel513RieszH

/-!
# HRS.Main.Rel513RieszI -- packet rel513, part 9: the quadratic part and measurability of the pieces

`quadStat h ν = 2 * modulatedEnergy h . ν`; `√N (F^h(X; m_N) - E F^h)` has `L²(Q_{N,β}(μ))` norm at most
`K B √δ_N` (`quadStat_variance`).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Main

variable {d : ℕ} {s : ℝ}

open HRS.PoleCavityAux

theorem rel513_quadStat_eq {N : ℕ} (h : Torus d → Torus d → ℝ) (ν : Measure (Torus d))
    (X : Config d N) : quadStat h ν X = 2 * modulatedEnergy h X ν := by
  unfold quadStat modulatedEnergy
  have hN : (N : ℝ) ≠ 0 ∨ (N : ℝ) = 0 := by tauto
  rcases hN with hN | hN
  · field_simp
  · simp [hN]

theorem rel513_measurable_lin {N : ℕ} {f : Torus d → ℝ} (hf : Measurable f) (c : ℝ) :
    Measurable (fun X : Config d N => Real.sqrt N * ((∫ y, f y ∂(empirical X)) - c)) := by
  simp only [rel513_integral_empirical]
  exact Measurable.const_mul (Measurable.sub (Measurable.const_mul
    (Finset.measurable_sum _ fun i _ => hf.comp (measurable_pi_apply i)) _) measurable_const) _

theorem rel513_measurable_quad {N : ℕ} {h : Torus d → Torus d → ℝ}
    (hm : Measurable (Function.uncurry h)) (ν : Measure (Torus d)) [SFinite ν] (c : ℝ) :
    Measurable (fun X : Config d N => Real.sqrt N * (modulatedEnergy h X ν - c)) := by
  have hH := Quad.measurable_Hc hm ν
  refine Measurable.const_mul (Measurable.sub ?_ measurable_const) _
  unfold modulatedEnergy
  refine Measurable.add (Measurable.sub ?_ ?_) measurable_const
  · exact Measurable.const_mul (Finset.measurable_sum _ fun i _ =>
      Finset.measurable_sum _ fun j _ => Quad.measurable_h_pair hm i j) _
  · exact Measurable.const_mul (Finset.measurable_sum _ fun i _ =>
      hH.comp (measurable_pi_apply i)) _

theorem rel513_quad_eLpNorm (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N → ∀ B : ℝ, 0 ≤ B → ∀ h : Torus d → Torus d → ℝ,
      Measurable (Function.uncurry h) → (∀ x y, h x y = h y x) →
      (∀ x y, x ≠ y → |h x y| ≤ B * singEnvelope s (Torus.eucDist x y)) →
      eLpNorm (fun X : Config d N => Real.sqrt N *
          (modulatedEnergy h X (firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)))
            - ∫ X', modulatedEnergy h X'
                (firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)))
              ∂(modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))))
        2 (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
        ENNReal.ofReal (K * B * Real.sqrt (deltaN d s N)) := by
  haveI hμ := isProbabilityMeasure_mu hρ
  obtain ⟨Cq, hCq⟩ := quadStat_variance hd hs0 hsd β hβ ρ hρ
  refine ⟨Real.sqrt |Cq| / 2, by positivity, fun N hN B hB h hm hsym hh => ?_⟩
  have hN0 : 0 < N := by omega
  set Q := modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ) with hQdef
  haveI hQ : IsProbabilityMeasure Q := rel513_modulatedGibbs_isProb hd hs0 hsd hβ hρ hN0
  set m := firstMarginal Q with hmdef
  haveI : IsFiniteMeasure m := rel513_firstMarginal_finite Q
  have hmem : m ∈ ({withDensityReal ρ, m} : Set (Measure (Torus d))) := by simp
  have hvar := hCq B h hm hsym hh N hN m hmem
  set Qd : Config d N → ℝ := fun X => quadStat h m X with hQd
  have hQdm : Measurable Qd := Quad.measurable_quadStat hm m
  have hfun : (fun X : Config d N => Real.sqrt N * (modulatedEnergy h X m -
      ∫ X', modulatedEnergy h X' m ∂Q)) =
      fun X => (Real.sqrt N / 2) * (Qd X - ∫ X', Qd X' ∂Q) := by
    funext X
    have e1 : ∀ X', Qd X' = 2 * modulatedEnergy h X' m := fun X' => rel513_quadStat_eq h m X'
    have e2 : ∫ X', Qd X' ∂Q = 2 * ∫ X', modulatedEnergy h X' m ∂Q := by
      simp_rw [e1]; exact integral_const_mul _ _
    rw [e1, e2]; ring
  rw [hfun]
  have hsq := rel513_eLpNorm_sq_centered Q Qd hQdm.aestronglyMeasurable (Real.sqrt N / 2)
  have hδ0 : 0 ≤ deltaN d s N := (Quad.deltaN_pos hd hs0 hsd (by omega : 1 ≤ N)).le
  have ha0 : 0 ≤ Real.sqrt |Cq| / 2 * B * Real.sqrt (deltaN d s N) := by positivity
  refine rel513_le_of_sq_le ha0 ?_
  rw [hsq]
  have h1 : ENNReal.ofReal ((Real.sqrt N / 2) ^ 2) =
      ENNReal.ofReal (1 / 4) * (N : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; ring
  rw [h1, mul_assoc]
  calc ENNReal.ofReal (1 / 4) * ((N : ℝ≥0∞) * evariance Qd Q)
      ≤ ENNReal.ofReal (1 / 4) * ENNReal.ofReal (Cq * B ^ 2 * deltaN d s N) := by
        gcongr
    _ = ENNReal.ofReal (1 / 4 * (Cq * B ^ 2 * deltaN d s N)) :=
        (ENNReal.ofReal_mul (by norm_num)).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have e := Real.sq_sqrt (abs_nonneg Cq)
        have e2 := Real.sq_sqrt hδ0
        have hB2 : 0 ≤ B ^ 2 * deltaN d s N := by positivity
        calc 1 / 4 * (Cq * B ^ 2 * deltaN d s N) ≤ 1 / 4 * (|Cq| * B ^ 2 * deltaN d s N) := by
              have := mul_le_mul_of_nonneg_right (le_abs_self Cq) hB2
              nlinarith
          _ = (Real.sqrt |Cq| / 2 * B * Real.sqrt (deltaN d s N)) ^ 2 := by
              rw [mul_pow, mul_pow, div_pow, e, e2]; ring

end HRS.Main

end
