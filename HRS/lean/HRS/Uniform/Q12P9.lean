import HRS.Uniform.Q12P8

/-!
# Q12, Peyre part 9: the abstract scheme theorem (`W_2 ≤ √a`)
-/

noncomputable section

open HRS MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q12

variable {d : ℕ}

lemma q12_tdist_torusMap_le {S : Euc d → Euc d} (x : Torus d) :
    Torus.tdist x (torusMap S x) ≤ ‖S (Torus.rep x) - Torus.rep x‖ := by
  have h1 : Torus.tdist x (torusMap S x) = KernelGrad.tdist x (torusMap S x) := rfl
  rw [h1, HRS.Commutator.EnergyAux.tdist_def]
  have : x - torusMap S x = Torus.mk (Torus.rep x - S (Torus.rep x)) := by
    unfold torusMap
    have e1 : Torus.mk (Torus.rep x - S (Torus.rep x)) =
        Torus.mk (Torus.rep x) - Torus.mk (S (Torus.rep x)) := by
      funext i; simp [Torus.mk]
    rw [e1, Torus.mk_rep]
  rw [this]
  have := HRS.Commutator.EnergyAux.tdist_mk_le (d := d) (Torus.rep x - S (Torus.rep x))
  rwa [norm_sub_rev] at this

theorem q12_integral_eq_lintegral_tdist (π : Measure (Torus d × Torus d)) [IsFiniteMeasure π] :
    ∫⁻ z, ENNReal.ofReal (Torus.tdist z.1 z.2 ^ (2 : ℝ)) ∂π =
      ENNReal.ofReal (∫ z, Torus.tdist z.1 z.2 ^ 2 ∂π) := by
  rw [ofReal_integral_eq_lintegral_ofReal (Uniform.Q14.q14_integrable_tdist_sq π)
    (Filter.Eventually.of_forall fun z => sq_nonneg _)]
  refine lintegral_congr fun z => ?_
  rw [Real.rpow_two]


set_option maxHeartbeats 1000000 in
/-- The abstract scheme theorem: a field with a weak continuity equation transports `μ 0` to `μ 1`
at `L²`-cost `a`. -/
theorem q12_scheme_coupling {w : ℝ → Euc d → Euc d} {μ : ℝ → Measure (Torus d)}
    {V V₁ V₂ δ Θ₂ a : ℝ}
    (hwc : ∀ t, ContDiff ℝ 2 (w t)) (hwp : ∀ t, Torus.Per (w t))
    (hV : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y, ‖w t y‖ ≤ V)
    (hV₁ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y, ‖fderiv ℝ (w t) y‖ ≤ V₁)
    (hV₂ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y, ‖fderiv ℝ (fderiv ℝ (w t)) y‖ ≤ V₂)
    (hprob : ∀ t ∈ Icc (0 : ℝ) 1, IsProbabilityMeasure (μ t)) (hδ : 0 ≤ δ)
    (hCE : ∀ t τ : ℝ, t ∈ Icc (0 : ℝ) 1 → 0 < τ → τ ≤ 1 → t + τ ≤ 1 → ∀ (Φ : Euc d → ℝ) (B : ℝ),
      Torus.Per Φ → C2b B Φ →
      |τ * ∫ x, fderiv ℝ Φ (Torus.rep x) (w t (Torus.rep x)) ∂(μ t) + (Iw (μ t) Φ - Iw (μ (t + τ)) Φ)|
        ≤ δ * τ ^ 2 * B)
    (hΘ : ∀ t ∈ Icc (0 : ℝ) 1, C2b Θ₂ (fun y => ‖w t y‖ ^ 2))
    (hkin : ∀ t ∈ Icc (0 : ℝ) 1, ∫ x, ‖w t (Torus.rep x)‖ ^ 2 ∂(μ t) ≤ a) :
    torusWassersteinE 2 (μ 0) (μ 1) ≤ ENNReal.ofReal (Real.sqrt a) := by
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1mem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  haveI := hprob 0 h0mem
  haveI := hprob 1 h1mem
  have hV0 : 0 ≤ V := le_trans (norm_nonneg _) (hV 0 h0mem 0)
  have hV₁0 : 0 ≤ V₁ := le_trans (norm_nonneg (fderiv ℝ (w 0) 0)) (hV₁ 0 h0mem 0)
  have hV₂0 : 0 ≤ V₂ := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ (w 0)) 0)) (hV₂ 0 h0mem 0)
  have hΘ0 : 0 ≤ Θ₂ := le_trans (abs_nonneg _) ((hΘ 0 h0mem).2 0).1
  have ha0 : 0 ≤ a := le_trans (integral_nonneg fun x => sq_nonneg _) (hkin 0 h0mem)
  set C₂ : ℝ := 2 * V₁ + V₁ ^ 2 + V₂ with hC₂
  have hC₂0 : 0 ≤ C₂ := by positivity
  set K : ℝ := (δ + V ^ 2) * Real.exp C₂ with hK
  have hK0 : 0 ≤ K := by positivity
  -- the sequence of schemes, indexed by `m = n - 1`
  obtain ⟨S, hSdef⟩ : ∃ S : ℕ → Euc d → Euc d,
      ∀ m, S m = schemeMap w (1 / ((m + 1 : ℕ) : ℝ)) (m + 1) := ⟨_, fun m => rfl⟩
  obtain ⟨π, hπdef⟩ : ∃ π : ℕ → Measure (Torus d × Torus d),
      ∀ m, π m = (μ 0).map (fun x => (x, torusMap (S m) x)) := ⟨_, fun m => rfl⟩
  have hSe : ∀ m, PerEquiv (S m) := fun m => by
    rw [hSdef]; exact q12_schemeMap_perEquiv hwp _ (m + 1)
  have hSc : ∀ m, Continuous (S m) := fun m => by
    rw [hSdef]; exact q12_schemeMap_continuous (fun t => (hwc t).continuous) _ (m + 1)
  have hmeasT : ∀ m, Measurable (torusMap (S m)) := fun m =>
    (q12_continuous_torusMap (hSe m) (hSc m)).measurable
  have hmeasP : ∀ m, Measurable (fun x : Torus d => (x, torusMap (S m) x)) := fun m =>
    measurable_id.prodMk (hmeasT m)
  have hπp : ∀ m, IsProbabilityMeasure (π m) := fun m => by
    rw [hπdef]; infer_instance
  have hfst : ∀ m, (π m).map Prod.fst = μ 0 := fun m => by
    rw [hπdef, Measure.map_map measurable_fst (hmeasP m)]
    exact Measure.map_id
  have hsnd' : ∀ m, (π m).map Prod.snd = (μ 0).map (torusMap (S m)) := fun m => by
    rw [hπdef, Measure.map_map measurable_snd (hmeasP m)]
    rfl
  -- weak closeness of the endpoint
  have hweak : ∀ m, WeakClose ((μ 0).map (torusMap (S m))) (μ 1) (K / ((m + 1 : ℕ) : ℝ)) := by
    intro m
    have hn : 0 < m + 1 := Nat.succ_pos m
    have h := q12_scheme_weak hwc hwp hV hV₁ hV₂ hprob hδ hCE hn (m + 1) le_rfl
    rw [← hSdef] at h
    have hnR : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hn
    have hnτ : ((m + 1 : ℕ) : ℝ) * (1 / ((m + 1 : ℕ) : ℝ)) = 1 := by field_simp
    rw [hnτ] at h
    refine q12_weakClose_mono ?_ h
    set τ : ℝ := 1 / ((m + 1 : ℕ) : ℝ) with hτ
    have hτ0 : 0 < τ := by positivity
    have hq : (1 + C₂ * τ) ^ (m + 1) ≤ Real.exp C₂ := by
      calc (1 + C₂ * τ) ^ (m + 1) ≤ (Real.exp (C₂ * τ)) ^ (m + 1) :=
            pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (C₂ * τ)]) _
        _ = Real.exp (C₂ * τ * ((m + 1 : ℕ) : ℝ)) := by
            rw [← Real.exp_nat_mul]; congr 1; ring
        _ = Real.exp C₂ := by
            congr 1
            have : τ * ((m + 1 : ℕ) : ℝ) = 1 := by rw [hτ]; field_simp
            calc C₂ * τ * ((m + 1 : ℕ) : ℝ) = C₂ * (τ * ((m + 1 : ℕ) : ℝ)) := by ring
              _ = C₂ := by rw [this, mul_one]
    have hK' : 0 ≤ (δ + V ^ 2) := by positivity
    calc (δ + V ^ 2) * τ ^ 2 * ((m + 1 : ℕ) : ℝ) * (1 + C₂ * τ) ^ (m + 1)
        = (δ + V ^ 2) * τ * (τ * ((m + 1 : ℕ) : ℝ)) * (1 + C₂ * τ) ^ (m + 1) := by ring
      _ = (δ + V ^ 2) * τ * (1 + C₂ * τ) ^ (m + 1) := by
          have : τ * ((m + 1 : ℕ) : ℝ) = 1 := by rw [hτ]; field_simp
          rw [this, mul_one]
      _ ≤ (δ + V ^ 2) * τ * Real.exp C₂ := by gcongr
      _ = K / ((m + 1 : ℕ) : ℝ) := by rw [hK, hτ]; field_simp
  have hb : Tendsto (fun m : ℕ => K / ((m + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have : Tendsto (fun m : ℕ => ((m + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    exact this.const_div_atTop K
  haveI : ∀ m, IsProbabilityMeasure ((μ 0).map (torusMap (S m))) := fun m =>
    inferInstance
  have hsnd : ∀ φ : Torus d → ℝ, Continuous φ →
      Tendsto (fun m => ∫ x, φ x ∂((π m).map Prod.snd)) atTop (𝓝 (∫ x, φ x ∂(μ 1))) := by
    intro φ hφ
    have := q12_tendsto_of_weakClose (ν := fun m => (μ 0).map (torusMap (S m))) hb hweak φ hφ
    simpa [hsnd'] using this
  -- cost
  have hcost : ∀ m, ∫ z, Torus.tdist z.1 z.2 ^ 2 ∂(π m) ≤ a + Θ₂ * (K / ((m + 1 : ℕ) : ℝ)) := by
    intro m
    have hn : 0 < m + 1 := Nat.succ_pos m
    have hc := q12_scheme_cost hwc hwp hV hV₁ hV₂ hprob hδ hCE hΘ hkin hn
    rw [← hSdef] at hc
    have e1 : ∫ z, Torus.tdist z.1 z.2 ^ 2 ∂(π m) = ∫ x, Torus.tdist x (torusMap (S m) x) ^ 2 ∂(μ 0) := by
      have hcc : Continuous fun z : Torus d × Torus d => Torus.tdist z.1 z.2 ^ 2 :=
        Uniform.Q14.q14_continuous_tdist.pow 2
      rw [hπdef, integral_map (hmeasP m).aemeasurable hcc.aestronglyMeasurable]
    rw [e1]
    have hcT : Continuous fun x : Torus d => Torus.tdist x (torusMap (S m) x) ^ 2 :=
      (Uniform.Q14.q14_continuous_tdist.comp (continuous_id.prodMk
        (q12_continuous_torusMap (hSe m) (hSc m)))).pow 2
    have hcF : Continuous fun x : Torus d => ‖S m (Torus.rep x) - Torus.rep x‖ ^ 2 := by
      have hper : Torus.Per (fun y => S m y - y) := fun y n => by
        show S m (y + Lattice.toEuc n) - (y + Lattice.toEuc n) = S m y - y
        rw [hSe m y n]; abel
      exact (Torus.continuous_descend hper ((hSc m).sub continuous_id)).norm.pow 2
    calc ∫ x, Torus.tdist x (torusMap (S m) x) ^ 2 ∂(μ 0)
        ≤ ∫ x, ‖S m (Torus.rep x) - Torus.rep x‖ ^ 2 ∂(μ 0) := by
          refine integral_mono (q12_integrable_cont hcT) (q12_integrable_cont hcF) fun x => ?_
          exact pow_le_pow_left₀ (by unfold Torus.tdist; exact norm_nonneg _)
            (q12_tdist_torusMap_le x) 2
      _ ≤ a + Θ₂ * ((δ + V ^ 2) * (1 / ((m + 1 : ℕ) : ℝ)) * Real.exp C₂) := hc
      _ = a + Θ₂ * (K / ((m + 1 : ℕ) : ℝ)) := by rw [hK]; ring
  have hcost' : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∫ z, Torus.tdist z.1 z.2 ^ 2 ∂(π m) ≤ a + ε := by
    intro ε hε
    have : Tendsto (fun m : ℕ => Θ₂ * (K / ((m + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
      simpa using hb.const_mul Θ₂
    filter_upwards [this.eventually (gt_mem_nhds hε)] with m hm
    linarith [hcost m]
  obtain ⟨π', hπ'p, hπ'1, hπ'2, hπ'c⟩ :=
    q12_weak_limit (μ 0) (μ 1) π hπp hfst hsnd a hcost'
  refine (q12_W_le_cost hπ'1 hπ'2).trans ?_
  rw [q12_integral_eq_lintegral_tdist π']
  have : ENNReal.ofReal (∫ z, Torus.tdist z.1 z.2 ^ 2 ∂π') ≤ ENNReal.ofReal a :=
    ENNReal.ofReal_le_ofReal hπ'c
  calc _ ≤ (ENNReal.ofReal a) ^ (1 / (2 : ℝ)) := ENNReal.rpow_le_rpow this (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt a) := by
        rw [ENNReal.ofReal_rpow_of_nonneg ha0 (by norm_num), Real.sqrt_eq_rpow]

end HRS.Uniform.Q12
