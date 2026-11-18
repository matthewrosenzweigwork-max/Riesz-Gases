import HRS.Main.Lattice39FB1

/-!
# Example A.39 final form, packet `l39b`: assembly of `InitialFluctuation` from `I2` (D1')
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory BoundedContinuousFunction

namespace HRS

namespace Main

variable {d : ℕ}

/-- (l39b) `ψ · (-div a)` is integrable for `ψ ∈ H^m` (so in `L²`) and `a ∈ C¹`. -/
theorem l39b_integrable_mul_div (a : Torus d → Euc d) (ha : Torus.IsSmooth a) {m : ℝ}
    {ψ : Torus d → ℝ} (hψ : MemSobolev m ψ) :
    Integrable (fun x => ψ x * (-Torus.div a x)) := by
  have ha1 : Torus.IsCk 1 a := by
    unfold Torus.IsSmooth Torus.IsCk at *
    exact ha.of_le (by exact_mod_cast le_top)
  have hcont : Continuous (fun x => -Torus.div a x) := (InitialDataAux.continuous_div a ha1).neg
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
  exact (hψ.1.integrable one_le_two).mul_bdd (c := M) hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => hM x trivial)

theorem lattice39f_initialFluctuation_of_I2_proof (S : MainData d) (R : ∀ N, Realization d N)
    (a : Torus d → Euc d) (ha : Torus.IsSmooth a) (Cin : ℝ) (hCin : 1 ≤ Cin)
    (hη : ∀ (N : ℕ) (ω : (R N).Ω) (ψ : Torus d → ℝ), (R N).η ω ψ = ∫ x, ψ x * (-Torus.div a x))
    (hflow : SelectedFlows S R)
    (hI2 : ∀ N : ℕ, 1 ≤ N → ∀ ψ : Torus d → ℝ, MemSobolev ((PDE.mStar d : ℕ) : ℝ) ψ → Continuous ψ →
      ∫⁻ ω, ENNReal.ofReal ((S.κ N * (pair (empirical ((R N).X₀ ω)) ψ - pair S.μ0 ψ)) ^ 2)
          ∂(R N).P +
        ∫⁻ ω, ENNReal.ofReal (((R N).η ω ψ) ^ 2) ∂(R N).P ≤
      ENNReal.ofReal (Cin ^ 2 * sobolevNorm ((PDE.mStar d : ℕ) : ℝ) ψ ^ 2)) :
    InitialFluctuation S R (PDE.mStar d) Cin (fun _ => 0) (fun _ => ∅) := by
  have hη' : ∀ (N : ℕ) (ω : (R N).Ω), (R N).η ω = fun ψ => ∫ x, ψ x * (-Torus.div a x) :=
    fun N ω => funext (hη N ω)
  refine ⟨?_, le_rfl, hCin, antitone_const, tendsto_const_nhds, fun _ => Set.finite_empty,
    ?_, ?_, ?_, ?_, hI2, ?_⟩
  · unfold PDE.mStar; omega
  · intro N ω ψ χ c hψ hχ
    rw [hη, hη, hη]
    have e : (fun x => (c • ψ + χ) x * (-Torus.div a x)) =
        fun x => c * (ψ x * (-Torus.div a x)) + χ x * (-Torus.div a x) := by
      funext x; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e, integral_add ((l39b_integrable_mul_div a ha hψ).const_mul c)
      (l39b_integrable_mul_div a ha hχ), integral_const_mul]
  · intro N ψ
    simp only [hη']
    exact measurable_const
  · refine ⟨Measure.dirac (fun ψ => ∫ x, ψ x * (-Torus.div a x)), fun N _ => ?_⟩
    have : (R N).η = fun ω => fun ψ => ∫ x, ψ x * (-Torus.div a x) := funext (hη' N)
    rw [law, this, Measure.map_const]
    simp
  · intro N hN ψ hψ _
    have h0 : ψ = 0 := by simpa using hψ
    subst h0
    simp [hη, pair]
  · intro N hN
    have hind := (hflow N hN).indep
    have hmeas := (hflow N hN).init_meas
    have hg : Measurable (fun x : Config d N => (x, fun ψ : Torus d → ℝ => ∫ x, ψ x * (-Torus.div a x))) :=
      measurable_id.prodMk measurable_const
    have := hind.comp hg measurable_id
    have e : (fun ω => ((R N).X₀ ω, (R N).η ω)) =
        (fun x : Config d N => (x, fun ψ : Torus d → ℝ => ∫ x, ψ x * (-Torus.div a x))) ∘ (R N).X₀ := by
      funext ω; simp [hη' N ω]
    rw [e]
    exact this

example := (@lattice39f_initialFluctuation_of_I2_proof : type_of% @lattice39f_initialFluctuation_of_I2)

end Main

end HRS
