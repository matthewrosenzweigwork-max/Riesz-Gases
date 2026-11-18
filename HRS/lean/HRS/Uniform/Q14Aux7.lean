import HRS.Uniform.Q14Aux6

/-!
# Q14, part 7: from couplings to `W_2`
-/

noncomputable section

open HRS
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q14

section Wasserstein

variable {d : ℕ}

lemma q14_coupling_prob {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    {π : Measure (Torus d × Torus d)} (h : π.map Prod.fst = μ) : IsProbabilityMeasure π := by
  refine ⟨?_⟩
  have := congrArg (fun m : Measure (Torus d) => m Set.univ) h
  simp only [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ,
    measure_univ] at this
  exact this

/-- `(∫⁻ ofReal (|x-y|^2) dπ)^{1/2}` as the real number `(∫ |x-y|² dπ)^{1/2}`. -/
lemma q14_cost_toReal (π : Measure (Torus d × Torus d)) [IsFiniteMeasure π] :
    ((∫⁻ z, ENNReal.ofReal (Torus.tdist z.1 z.2 ^ (2 : ℝ)) ∂π) ^ (1 / (2 : ℝ))).toReal ^ 2 =
      ∫ z, Torus.tdist z.1 z.2 ^ 2 ∂π := by
  have hnn : 0 ≤ᵐ[π] fun z : Torus d × Torus d => Torus.tdist z.1 z.2 ^ 2 :=
    Filter.Eventually.of_forall fun z => sq_nonneg _
  have h1 : ∫⁻ z, ENNReal.ofReal (Torus.tdist z.1 z.2 ^ (2 : ℝ)) ∂π =
      ENNReal.ofReal (∫ z, Torus.tdist z.1 z.2 ^ 2 ∂π) := by
    rw [ofReal_integral_eq_lintegral_ofReal (q14_integrable_tdist_sq π) hnn]
    refine lintegral_congr fun z => ?_
    rw [Real.rpow_two]
  have h2 : 0 ≤ ∫ z, Torus.tdist z.1 z.2 ^ 2 ∂π := integral_nonneg fun z => sq_nonneg _
  rw [h1, ENNReal.ofReal_rpow_of_nonneg h2 (by norm_num), ENNReal.toReal_ofReal (by positivity),
    ← Real.rpow_natCast, ← Real.rpow_mul h2]
  norm_num

theorem q14_bures2_W2 {γ : ℝ} (hγ : (d : ℝ) / 2 + 2 < γ) {q : ℝ} (hq : 0 ≤ q)
    (μ ν : Measure (Torus d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Uniform.bures2 (covForm γ q μ) (covForm γ q ν) ≤
      4 * q * d * q14S d (γ - 2) * (torusWassersteinE 2 μ ν).toReal ^ 2 := by
  set K := 4 * q * d * q14S d (γ - 2) with hK
  have hK0 : 0 ≤ K := by
    have := q14S_nonneg d (γ - 2); positivity
  -- the cost of a coupling
  let cost : {π : Measure (Torus d × Torus d) // π.map Prod.fst = μ ∧ π.map Prod.snd = ν} → ℝ≥0∞ :=
    fun π => (∫⁻ z, ENNReal.ofReal (Torus.tdist z.1 z.2 ^ (2 : ℝ)) ∂π.1) ^ (1 / (2 : ℝ))
  have hW : torusWassersteinE 2 μ ν = ⨅ π, cost π := rfl
  have hcost : ∀ π, Uniform.bures2 (covForm γ q μ) (covForm γ q ν) ≤
      K * (cost π).toReal ^ 2 := by
    intro π
    haveI := q14_coupling_prob (μ := μ) π.2.1
    have := q14_bures2_coupling hγ hq π.1
    rw [π.2.1, π.2.2] at this
    refine this.trans (le_of_eq ?_)
    rw [hK, ← q14_cost_toReal π.1]
  -- the product coupling
  have hprod : ∃ π0 : {π : Measure (Torus d × Torus d) // π.map Prod.fst = μ ∧ π.map Prod.snd = ν},
      cost π0 < ⊤ := by
    refine ⟨⟨μ.prod ν, ?_, ?_⟩, ?_⟩
    · rw [Measure.map_fst_prod]; simp
    · rw [Measure.map_snd_prod]; simp
    · show (∫⁻ z, ENNReal.ofReal (Torus.tdist z.1 z.2 ^ (2 : ℝ)) ∂(μ.prod ν)) ^ (1 / (2 : ℝ)) < ⊤
      refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
      refine ne_of_lt (lt_of_le_of_lt (lintegral_mono (g := fun _ => ENNReal.ofReal ((d : ℝ) ^ 2))
        fun z => ?_) (by simp))
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Real.rpow_two]
      exact pow_le_pow_left₀ (by unfold Torus.tdist; exact norm_nonneg _) (q14_tdist_le _ _) 2
  obtain ⟨π0, hπ0⟩ := hprod
  have hWtop : torusWassersteinE 2 μ ν < ⊤ := lt_of_le_of_lt (hW ▸ iInf_le cost π0) hπ0
  set t := (torusWassersteinE 2 μ ν).toReal with ht
  have hε : ∀ ε : ℝ, 0 < ε → Uniform.bures2 (covForm γ q μ) (covForm γ q ν) ≤ K * (t + ε) ^ 2 := by
    intro ε hε
    have hlt : torusWassersteinE 2 μ ν < torusWassersteinE 2 μ ν + ENNReal.ofReal ε :=
      ENNReal.lt_add_right hWtop.ne (by simpa using hε)
    rw [hW] at hlt
    obtain ⟨π, hπ⟩ := iInf_lt_iff.1 hlt
    have h1 : (cost π).toReal ≤ t + ε := by
      have := ENNReal.toReal_mono (by
        rw [← hW]; exact ENNReal.add_ne_top.2 ⟨hWtop.ne, ENNReal.ofReal_ne_top⟩) hπ.le
      rw [ENNReal.toReal_add (by rw [← hW]; exact hWtop.ne) ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hε.le] at this
      simpa [ht, hW] using this
    refine (hcost π).trans ?_
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ENNReal.toReal_nonneg h1 2) hK0
  have hlim : Tendsto (fun ε : ℝ => K * (t + ε) ^ 2) (𝓝[>] 0) (𝓝 (K * t ^ 2)) := by
    have : Continuous fun ε : ℝ => K * (t + ε) ^ 2 := by fun_prop
    have h := this.tendsto 0
    simp only [add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε' => hε ε hε')

end Wasserstein

end HRS.Uniform.Q14
