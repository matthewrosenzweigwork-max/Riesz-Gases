import HRS.MS.FldRemAux1

/-!
# S5.3 (`field_remainder`), part 2: orbit data and the pathwise Duhamel structure

* `S53Orbit`: the orbit input of S5.3 (identification of `propagatorW C r t φ_α` with the time-homogeneous orbit
  `G0 α (t - r)`, `C_b²` bounds `‖D²G_a‖ ≤ K b_α` with `b` summable, difference quotients in `C_b²`);
* continuity in the time parameter from the difference quotients, joint measurability of `(τ,x) ↦ ∇G_τ(x)` after
  clamping `τ` to `[0,T]`;
* the pathwise formula `D(G0 τ)(X) = D(G0 0)(X) + ∫_0^τ D(G1 σ)(X) dσ` for every configuration `X`;
* the measurable modification of a continuous adapted process.

Helper names carry the prefix `s53_`, namespace `HRS.MS.S53`.
-/

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S53

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d N : ℕ}

/-- The difference-quotient property in `C_b²` (clause of `ul_adjoint_orbit_bounds`). -/
def S53Diff (T : ℝ) (G G' : ℝ → Euc d → ℝ) : Prop :=
  ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, h ≠ 0 → |h| < δ → τ + h ∈ Set.Icc (0 : ℝ) T →
    ∀ j ≤ 2, ∀ x : Euc d, ‖iteratedFDeriv ℝ j (fun y => h⁻¹ * (G (τ + h) y - G τ y) - G' τ y) x‖ ≤ ε

/-- Continuity in the time parameter, in the `C_b²` norm. -/
def S53Cont (T : ℝ) (G : ℝ → Euc d → ℝ) : Prop :=
  ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ ε > 0, ∃ δ > 0, ∀ τ' ∈ Set.Icc (0 : ℝ) T, |τ' - τ| < δ →
    ∀ j ≤ 2, ∀ x : Euc d, ‖iteratedFDeriv ℝ j (fun y => G τ' y - G τ y) x‖ ≤ ε

lemma s53_bound3 {f : Euc d → ℝ} (hf : MemCb 2 f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j ≤ 2, ∀ x : Euc d, ‖iteratedFDeriv ℝ j f x‖ ≤ B := by
  have h : ∀ j ≤ 2, ∃ B : ℝ, ∀ x : Euc d, ‖iteratedFDeriv ℝ j f x‖ ≤ B := fun j hj => by
    obtain ⟨B, hB⟩ := hf.2 j hj
    exact ⟨B, fun x => hB ⟨x, rfl⟩⟩
  choose! B hB using h
  refine ⟨∑ j ∈ Finset.range 3, |B j|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun j hj x => ?_⟩
  refine (hB j hj x).trans ((le_abs_self _).trans ?_)
  exact Finset.single_le_sum (f := fun j => |B j|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.2 (by omega))

lemma s53_cont_of_diff {T : ℝ} {G G' : ℝ → Euc d → ℝ}
    (hG : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb 2 (G τ)) (hG' : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb 2 (G' τ))
    (hdiff : S53Diff T G G') : S53Cont T G := by
  intro τ hτ ε hε
  obtain ⟨B, hB0, hB⟩ := s53_bound3 (hG' τ hτ)
  obtain ⟨δ₁, hδ₁, hD⟩ := hdiff τ hτ 1 one_pos
  refine ⟨min δ₁ (ε / (B + 1)), lt_min hδ₁ (by positivity), fun τ' hτ' hd j hj x => ?_⟩
  by_cases hne : τ' = τ
  · subst hne
    simp only [sub_self]
    simp [hε.le]
  set h := τ' - τ with hh
  have hh0 : h ≠ 0 := sub_ne_zero.2 hne
  have hτ'h : τ + h = τ' := by rw [hh]; ring
  have hhd1 : |h| < δ₁ := lt_of_lt_of_le hd (min_le_left _ _)
  have hhd2 : |h| < ε / (B + 1) := lt_of_lt_of_le hd (min_le_right _ _)
  have hq := hD h hh0 hhd1 (by rw [hτ'h]; exact hτ')
  rw [hτ'h] at hq
  set q : Euc d → ℝ := fun z => h⁻¹ * (G τ' z - G τ z) - G' τ z with hqdef
  have hA : MemCb 2 (fun z => G τ' z - G τ z) :=
    HRS.MS.Fcau.fcau_memCb_sub (hG τ' hτ') (hG τ hτ)
  have hBm : MemCb 2 (fun z => h⁻¹ * (G τ' z - G τ z)) := s53_memCb_const_mul _ hA
  have hqc : ContDiff ℝ 2 q := (HRS.MS.Fcau.fcau_memCb_sub hBm (hG' τ hτ)).1
  have hGc : ContDiff ℝ 2 (G' τ) := (hG' τ hτ).1
  have hw : (fun y => G τ' y - G τ y) = h • (fun z => h⁻¹ * (G τ' z - G τ z)) := by
    funext y; simp [hh0]
  have hu : (fun z => h⁻¹ * (G τ' z - G τ z)) = q + G' τ := by
    funext y; simp [hqdef]
  have hjc : (j : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hj
  have e1 : iteratedFDeriv ℝ j (fun y => G τ' y - G τ y) x =
      h • iteratedFDeriv ℝ j (fun z => h⁻¹ * (G τ' z - G τ z)) x := by
    rw [hw]
    exact iteratedFDeriv_const_smul_apply (hBm.1.of_le hjc).contDiffAt
  have e2 : iteratedFDeriv ℝ j (fun z => h⁻¹ * (G τ' z - G τ z)) x =
      iteratedFDeriv ℝ j q x + iteratedFDeriv ℝ j (G' τ) x := by
    rw [hu]
    exact iteratedFDeriv_add_apply (hqc.of_le hjc).contDiffAt (hGc.of_le hjc).contDiffAt
  rw [e1, e2, norm_smul, Real.norm_eq_abs]
  have h3 : ‖iteratedFDeriv ℝ j q x + iteratedFDeriv ℝ j (G' τ) x‖ ≤ B + 1 :=
    (norm_add_le _ _).trans (by linarith [hq j hj x, hB j hj x])
  calc |h| * ‖iteratedFDeriv ℝ j q x + iteratedFDeriv ℝ j (G' τ) x‖ ≤ |h| * (B + 1) :=
        mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
    _ ≤ ε / (B + 1) * (B + 1) := by gcongr
    _ = ε := by field_simp


/-! ### Clamping the time parameter -/

/-- `τ` clamped to `[0,T]`. -/
def s53_clamp (T τ : ℝ) : ℝ := max 0 (min τ T)

lemma s53_clamp_mem {T : ℝ} (hT : 0 ≤ T) (τ : ℝ) : s53_clamp T τ ∈ Set.Icc (0 : ℝ) T :=
  ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

lemma s53_clamp_of_mem {T τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) T) : s53_clamp T τ = τ := by
  unfold s53_clamp
  rw [min_eq_left hτ.2, max_eq_right hτ.1]

lemma s53_clamp_lip (T : ℝ) : LipschitzWith 1 (s53_clamp T) :=
  (LipschitzWith.id.min_const T).const_max 0

lemma s53_norm_gradient (f : Euc d → ℝ) (x : Euc d) : ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  unfold gradient
  exact LinearIsometryEquiv.norm_map _ _

lemma s53_grad_continuous {T : ℝ} (hT : 0 ≤ T) {G : ℝ → Euc d → ℝ}
    (hG : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb 2 (G τ)) (hc : S53Cont T G) :
    Continuous fun p : ℝ × Euc d => gradient (G (s53_clamp T p.1)) p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨τ₀, x₀⟩
  rw [Metric.continuousAt_iff]
  intro ε hε
  set c0 := s53_clamp T τ₀ with hc0
  have hc0m := s53_clamp_mem hT τ₀
  obtain ⟨δ₁, hδ₁, hD⟩ := hc c0 hc0m (ε / 2) (by positivity)
  have hgc : Continuous (fun x => gradient (G c0) x) := by
    have h1 : Continuous (fderiv ℝ (G c0)) := (hG c0 hc0m).1.continuous_fderiv (by norm_num)
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp h1
  obtain ⟨δ₂, hδ₂, hx⟩ := Metric.continuousAt_iff.1 hgc.continuousAt (ε / 2) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun {p} hp => ?_⟩
  obtain ⟨τ, x⟩ := p
  rw [Prod.dist_eq, max_lt_iff] at hp
  obtain ⟨hp1, hp2⟩ := hp
  simp only [Real.dist_eq] at hp1
  simp only [dist_eq_norm] at hp2 ⊢
  have hcl : |s53_clamp T τ - c0| ≤ |τ - τ₀| := by
    have := (s53_clamp_lip T).dist_le_mul τ τ₀
    simpa [Real.dist_eq] using this
  have hcm := s53_clamp_mem hT τ
  have h1 : ‖gradient (G (s53_clamp T τ)) x - gradient (G c0) x‖ ≤ ε / 2 := by
    have e := HRS.MS.Fcau.fcau_gradient_sub (f := G (s53_clamp T τ)) (g := G c0)
      ((hG _ hcm).1.of_le (by norm_num)) ((hG _ hc0m).1.of_le (by norm_num)) x
    have := hD (s53_clamp T τ) hcm (lt_of_le_of_lt hcl (lt_of_lt_of_le hp1 (min_le_left _ _))) 1
      (by norm_num) x
    rw [norm_iteratedFDeriv_one] at this
    rw [← e, s53_norm_gradient]
    exact this
  have h2 : ‖gradient (G c0) x - gradient (G c0) x₀‖ < ε / 2 := by
    have := hx (lt_of_lt_of_le (by simpa [dist_eq_norm] using hp2) (min_le_right _ _) : dist x x₀ < δ₂)
    simpa [dist_eq_norm] using this
  have : gradient (G (s53_clamp T τ)) x - gradient (G (s53_clamp T τ₀)) x₀ =
      (gradient (G (s53_clamp T τ)) x - gradient (G c0) x) + (gradient (G c0) x - gradient (G c0) x₀) := by
    rw [← hc0]; abel
  rw [this]
  exact lt_of_le_of_lt (norm_add_le _ _) (by linarith)

lemma s53_grad_measurable {T : ℝ} (hT : 0 ≤ T) {G : ℝ → Euc d → ℝ}
    (hG : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb 2 (G τ)) (hc : S53Cont T G) :
    Measurable fun p : ℝ × Euc d => gradient (G (s53_clamp T p.1)) p.2 :=
  (s53_grad_continuous hT hG hc).measurable


/-! ### The pathwise Duhamel formula for `D` -/

section Ftc

variable {s : ℝ} {ρ : Euc d → ℝ} {Mρ : ℝ}

lemma s53_Dk_continuousOn (hs0 : 0 ≤ s) (hM0 : 0 ≤ Mρ) (hρ : HRS.Whole.IsProbDensity ρ)
    (hrow : ∀ x : Euc d, ∫⁻ y, ENNReal.ofReal (1 + rieszWeight s (x - y)) ∂(HRS.Whole.withDensityReal ρ) ≤
      ENNReal.ofReal Mρ) (hN : 0 < N) {T : ℝ} {G : ℝ → Euc d → ℝ}
    (hG : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb 2 (G τ)) (hc : S53Cont T G) (X : EucConfig d N) :
    ContinuousOn (fun τ => s53_Dk s ρ (G τ) X) (Set.Icc 0 T) := by
  intro τ hτ
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  set c : ℝ := (s + 1) * s53_cX s Mρ X + 1 with hcdef
  have hcX := s53_cX_nonneg (s := s) hM0 X
  have hc0 : 0 < c := by
    have : 0 ≤ (s + 1) * s53_cX s Mρ X := by positivity
    linarith
  obtain ⟨δ, hδ, hD⟩ := hc τ hτ (ε / (2 * c)) (by positivity)
  refine ⟨δ, hδ, fun {τ'} hτ' hd => ?_⟩
  have hlip := s53_Dk_lip hs0 hM0 hρ hrow hN (hG τ' hτ') (hG τ hτ) X
  have hsup : (⨆ x, ‖iteratedFDeriv ℝ 2 (fun x => G τ' x - G τ x) x‖) ≤ ε / (2 * c) :=
    ciSup_le fun x => hD τ' hτ' (by simpa [Real.dist_eq] using hd) 2 le_rfl x
  rw [Real.dist_eq]
  refine lt_of_le_of_lt (hlip.trans ?_) (by linarith : ε / 2 < ε)
  have hs1 : 0 ≤ s + 1 := by linarith
  calc (s + 1) * (⨆ x, ‖iteratedFDeriv ℝ 2 (fun x => G τ' x - G τ x) x‖) * s53_cX s Mρ X
      ≤ (s + 1) * (ε / (2 * c)) * s53_cX s Mρ X := by gcongr
    _ = ε / 2 * (((s + 1) * s53_cX s Mρ X) / c) := by field_simp
    _ ≤ ε / 2 * 1 := by
        gcongr
        rw [div_le_one hc0]; linarith
    _ = ε / 2 := by ring

lemma s53_ftc (hs0 : 0 ≤ s) (hM0 : 0 ≤ Mρ) (hρ : HRS.Whole.IsProbDensity ρ)
    (hrow : ∀ x : Euc d, ∫⁻ y, ENNReal.ofReal (1 + rieszWeight s (x - y)) ∂(HRS.Whole.withDensityReal ρ) ≤
      ENNReal.ofReal Mρ) (hN : 0 < N) {T : ℝ} {G G' : ℝ → Euc d → ℝ}
    (hG : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb 2 (G τ)) (hG' : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb 2 (G' τ))
    (hdiff : S53Diff T G G') (hc' : S53Cont T G') (X : EucConfig d N) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) T) :
    s53_Dk s ρ (G τ) X = s53_Dk s ρ (G 0) X + ∫ σ in Set.Ioc 0 τ, s53_Dk s ρ (G' σ) X := by
  have hder : ∀ y ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun τ => s53_Dk s ρ (G τ) X) (s53_Dk s ρ (G' y) X) (Set.Icc 0 T) y :=
    fun y hy => s53_Dk_hasDerivWithinAt hs0 hM0 hρ hrow hN hG hG' hdiff X hy
  have hsub : Set.Icc (0 : ℝ) τ ⊆ Set.Icc 0 T := Set.Icc_subset_Icc_right hτ.2
  have hcont : ContinuousOn (fun τ => s53_Dk s ρ (G τ) X) (Set.Icc 0 τ) :=
    (show ContinuousOn (fun τ => s53_Dk s ρ (G τ) X) (Set.Icc 0 T) from
      fun y hy => (hder y hy).continuousWithinAt).mono hsub
  have hint : IntervalIntegrable (fun σ => s53_Dk s ρ (G' σ) X) volume 0 τ := by
    have := (s53_Dk_continuousOn hs0 hM0 hρ hrow hN hG' hc' X).mono hsub
    exact this.intervalIntegrable_of_Icc hτ.1
  have key := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hτ.1 hcont
    (fun y hy => by
      have hyT : y ∈ Set.Ioo (0 : ℝ) T := ⟨hy.1, lt_of_lt_of_le hy.2 hτ.2⟩
      exact ((hder y ⟨hy.1.le, hyT.2.le⟩).hasDerivAt (Icc_mem_nhds hyT.1 hyT.2)).hasDerivWithinAt) hint
  rw [intervalIntegral.integral_of_le hτ.1] at key
  linarith

end Ftc


/-! ### A jointly measurable modification of a continuous adapted process -/

open Classical in
lemma s53_modify {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig d N)
    (hcont : ∀ᵐ ζ ∂P, ∀ i, Continuous fun t => X t ζ i) (hmeas : ∀ t, Measurable (X t)) :
    ∃ (X' : ℝ≥0 → Ω → EucConfig d N) (Gs : Set Ω), MeasurableSet Gs ∧ P Gsᶜ = 0 ∧
      (∀ ζ ∈ Gs, ∀ t, X' t ζ = X t ζ) ∧ (∀ t, Measurable (X' t)) ∧
      Measurable (fun p : ℝ × Ω => X' (Real.toNNReal p.1) p.2) := by
  set B : Set Ω := {ζ | ¬ ∀ i, Continuous fun t => X t ζ i} with hB
  have hB0 : P B = 0 := ae_iff.1 hcont
  set N0 := toMeasurable P B with hN0
  have hN0m : MeasurableSet N0 := measurableSet_toMeasurable P B
  have hN00 : P N0 = 0 := by rw [hN0, measure_toMeasurable]; exact hB0
  set Gs : Set Ω := N0ᶜ with hGs
  have hGsm : MeasurableSet Gs := hN0m.compl
  refine ⟨fun t ζ => if ζ ∈ Gs then X t ζ else 0, Gs, hGsm, by rwa [hGs, compl_compl], ?_, ?_, ?_⟩
  · intro ζ hζ t
    simp [hζ]
  · intro t
    exact Measurable.ite hGsm (hmeas t) measurable_const
  · have hm : Measurable (Function.uncurry fun (t : ℝ≥0) (ζ : Ω) => if ζ ∈ Gs then X t ζ else 0) := by
      refine measurable_uncurry_of_continuous_of_measurable (fun ζ => ?_) (fun t => ?_)
      · by_cases hζ : ζ ∈ Gs
        · have : ζ ∉ B := fun h => hζ (subset_toMeasurable P B h) |>.elim
          have hc : ∀ i, Continuous fun t => X t ζ i := by
            by_contra hcon
            exact this hcon
          simp only [hζ, ite_true]
          exact continuous_pi hc
        · simp only [hζ, ite_false]
          exact continuous_const
      · exact Measurable.ite hGsm (hmeas t) measurable_const
    exact hm.comp ((measurable_fst.real_toNNReal).prodMk measurable_snd)


/-! ### The coefficient context -/

/-- The data under which the commutator functional is linear and bounded on `C_b²`. -/
structure S53Ctx (s : ℝ) (ρ : Euc d → ℝ) (Mρ : ℝ) : Prop where
  hs0 : 0 ≤ s
  hM0 : 0 ≤ Mρ
  hρ : HRS.Whole.IsProbDensity ρ
  hrow : ∀ x : Euc d, ∫⁻ y, ENNReal.ofReal (1 + rieszWeight s (x - y)) ∂(HRS.Whole.withDensityReal ρ) ≤
    ENNReal.ofReal Mρ

lemma s53_ctx_of_schwartz (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : IsSchwartzDensity ρ) : ∃ Mρ, S53Ctx s ρ Mρ := by
  obtain ⟨hρp, ψ, hψ⟩ := hρ
  have hM : ∀ x, ρ x ≤ ‖ψ.toBoundedContinuousFunction‖ := fun x => by
    rw [← hψ]
    exact (le_abs_self _).trans (by
      have := ψ.toBoundedContinuousFunction.norm_coe_le_norm x
      simpa using this)
  obtain ⟨Mρ, hM0, hrow⟩ := s53_rowConst (by omega : 1 ≤ d) hs0 hsd hρp hM
  exact ⟨Mρ, ⟨hs0, hM0, hρp, hrow⟩⟩

lemma s53_deltaN_nonneg (s : ℝ) (hN : 0 < N) : 0 ≤ deltaN d s N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold deltaN
  split_ifs
  · positivity
  · have : 1 ≤ Real.exp 1 * N := by
      have h1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      have h2 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith
    have := Real.log_nonneg this
    positivity
  · positivity

/-! ### The `ℓ²` norm is dominated by the `ℓ¹` norm -/

lemma s53_l2NormE_le {ι : Type*} (c : ι → ℝ) :
    l2NormE c ≤ ∑' i, ENNReal.ofReal |c i| := by
  unfold l2NormE
  set S := ∑' i, ENNReal.ofReal |c i| with hS
  have h1 : ∑' i, ENNReal.ofReal (c i ^ 2) ≤ S ^ 2 := by
    calc ∑' i, ENNReal.ofReal (c i ^ 2) ≤ ∑' i, ENNReal.ofReal |c i| * S := by
          refine ENNReal.tsum_le_tsum fun i => ?_
          have : ENNReal.ofReal (c i ^ 2) = ENNReal.ofReal |c i| * ENNReal.ofReal |c i| := by
            rw [← ENNReal.ofReal_mul (abs_nonneg _), ← sq, sq_abs]
          rw [this]
          exact mul_le_mul_right (ENNReal.le_tsum (f := fun i => ENNReal.ofReal |c i|) i) _
      _ = S * S := ENNReal.tsum_mul_right
      _ = S ^ 2 := (sq S).symm
  calc (∑' i, ENNReal.ofReal (c i ^ 2)) ^ (1 / 2 : ℝ) ≤ (S ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow h1 (by norm_num)
    _ = S := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num


/-! ### The pathwise bound -/

/-- The dominating function `‖D G_0‖ + ∫_0^T ‖D G_1(σ)‖ dσ` of a configuration. -/
def s53_Hb (s : ℝ) (ρ : Euc d → ℝ) (T : ℝ) (G G' : ℝ → Euc d → ℝ) (Y : EucConfig d N) : ℝ≥0∞ :=
  ‖s53_Dk s ρ (G 0) Y‖ₑ + ∫⁻ σ in Set.Icc (0 : ℝ) T, ‖s53_Dk s ρ (G' (s53_clamp T σ)) Y‖ₑ

lemma s53_path_bound {s : ℝ} {ρ : Euc d → ℝ} {Mρ : ℝ} (ctx : S53Ctx s ρ Mρ) (hN : 0 < N) {T : ℝ}
    {G G' : ℝ → Euc d → ℝ} (hG : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb 2 (G τ))
    (hG' : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb 2 (G' τ)) (hdiff : S53Diff T G G') (hc' : S53Cont T G')
    (Y : EucConfig d N) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) T) :
    ‖s53_Dk s ρ (G τ) Y‖ₑ ≤ s53_Hb s ρ T G G' Y := by
  rw [s53_ftc ctx.hs0 ctx.hM0 ctx.hρ ctx.hrow hN hG hG' hdiff hc' Y hτ]
  unfold s53_Hb
  refine (enorm_add_le _ _).trans (add_le_add le_rfl ?_)
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  calc ∫⁻ σ in Set.Ioc 0 τ, ‖s53_Dk s ρ (G' σ) Y‖ₑ
      = ∫⁻ σ in Set.Ioc 0 τ, ‖s53_Dk s ρ (G' (s53_clamp T σ)) Y‖ₑ := by
        refine setLIntegral_congr_fun measurableSet_Ioc fun σ hσ => ?_
        rw [s53_clamp_of_mem ⟨hσ.1.le, hσ.2.trans hτ.2⟩]
    _ ≤ ∫⁻ σ in Set.Icc (0 : ℝ) T, ‖s53_Dk s ρ (G' (s53_clamp T σ)) Y‖ₑ :=
        lintegral_mono_set (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc_right hτ.2))


lemma s53_Hb_measurable {s : ℝ} {ρ : Euc d → ℝ} {Mρ : ℝ} (ctx : S53Ctx s ρ Mρ) (T : ℝ)
    {G G' : ℝ → Euc d → ℝ} (hG0 : Measurable fun x : Euc d => gradient (G 0) x)
    (hG1 : Measurable fun p : ℝ × Euc d => gradient (G' (s53_clamp T p.1)) p.2) :
    Measurable (s53_Hb (N := N) s ρ T G G') := by
  have m0 : Measurable fun p : ℝ × EucConfig d N => s53_Dk s ρ ((fun _ : ℝ => G 0) p.1) p.2 :=
    s53_Dk_measurable ctx.hρ (F := fun _ => G 0) (hG0.comp measurable_snd)
  have m1 : Measurable fun p : ℝ × EucConfig d N =>
      s53_Dk s ρ ((fun τ : ℝ => G' (s53_clamp T τ)) p.1) p.2 :=
    s53_Dk_measurable ctx.hρ (F := fun τ => G' (s53_clamp T τ)) hG1
  have h0 : Measurable fun Y : EucConfig d N => ‖s53_Dk s ρ (G 0) Y‖ₑ := by
    have hpr : Measurable fun Y : EucConfig d N => ((0 : ℝ), Y) :=
      measurable_const.prodMk measurable_id
    exact (m0.comp hpr).enorm
  have h1 : Measurable fun q : EucConfig d N × ℝ => ‖s53_Dk s ρ (G' (s53_clamp T q.2)) q.1‖ₑ :=
    (m1.comp measurable_swap).enorm
  exact h0.add (h1.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) T)))


/-! ### Expectations -/

section Exp

variable {s : ℝ} {ρ : Euc d → ℝ} {Mρ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma s53_exp_single [IsProbabilityMeasure P] {T CA δ : ℝ} (hδ : 0 ≤ δ)
    {X X' : ℝ≥0 → Ω → EucConfig d N}
    (hyp : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ f : Euc d → ℝ, MemCb 2 f →
      Integrable (fun ζ => |s53_Dk s ρ f (X (Real.toNNReal r) ζ)|) P ∧
        ∫ ζ, |s53_Dk s ρ f (X (Real.toNNReal r) ζ)| ∂P ≤ CA * δ * ⨆ x, ‖iteratedFDeriv ℝ 2 f x‖)
    (hae : ∀ t, ∀ᵐ ζ ∂P, X' t ζ = X t ζ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) {f : Euc d → ℝ}
    (hf : MemCb 2 f) {L : ℝ} (hL : (⨆ x, ‖iteratedFDeriv ℝ 2 f x‖) ≤ L) :
    ∫⁻ ζ, ‖s53_Dk s ρ f (X' (Real.toNNReal r) ζ)‖ₑ ∂P ≤ ENNReal.ofReal (max CA 0 * δ * L) := by
  obtain ⟨hi, hb⟩ := hyp r hr f hf
  have hsup0 := s53_cbSup_nonneg f
  have e1 : ∫⁻ ζ, ‖s53_Dk s ρ f (X' (Real.toNNReal r) ζ)‖ₑ ∂P =
      ∫⁻ ζ, ENNReal.ofReal |s53_Dk s ρ f (X (Real.toNNReal r) ζ)| ∂P := by
    refine lintegral_congr_ae ((hae (Real.toNNReal r)).mono fun ζ hζ => ?_)
    beta_reduce
    rw [hζ, ← ofReal_norm, Real.norm_eq_abs]
  rw [e1, ← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun _ => abs_nonneg _)]
  refine ENNReal.ofReal_le_ofReal (hb.trans ?_)
  have h1 : CA * δ * (⨆ x, ‖iteratedFDeriv ℝ 2 f x‖) ≤ max CA 0 * δ * (⨆ x, ‖iteratedFDeriv ℝ 2 f x‖) := by
    gcongr
    exact le_max_left _ _
  refine h1.trans ?_
  gcongr

lemma s53_exp_Hb [IsProbabilityMeasure P] (ctx : S53Ctx s ρ Mρ) {T CA δ : ℝ} (hδ : 0 ≤ δ) (hT : 0 ≤ T)
    {X X' : ℝ≥0 → Ω → EucConfig d N} (hX'm : ∀ t, Measurable (X' t))
    (hyp : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ f : Euc d → ℝ, MemCb 2 f →
      Integrable (fun ζ => |s53_Dk s ρ f (X (Real.toNNReal r) ζ)|) P ∧
        ∫ ζ, |s53_Dk s ρ f (X (Real.toNNReal r) ζ)| ∂P ≤ CA * δ * ⨆ x, ‖iteratedFDeriv ℝ 2 f x‖)
    (hae : ∀ t, ∀ᵐ ζ ∂P, X' t ζ = X t ζ) {G G' : ℝ → Euc d → ℝ}
    (hG : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb 2 (G τ)) (hG' : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb 2 (G' τ))
    (hG0m : Measurable fun x : Euc d => gradient (G 0) x)
    (hG1m : Measurable fun p : ℝ × Euc d => gradient (G' (s53_clamp T p.1)) p.2)
    {L : ℝ} (hL0 : (⨆ x, ‖iteratedFDeriv ℝ 2 (G 0) x‖) ≤ L)
    (hL1 : ∀ σ ∈ Set.Icc (0 : ℝ) T, (⨆ x, ‖iteratedFDeriv ℝ 2 (G' σ) x‖) ≤ L)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) :
    ∫⁻ ζ, s53_Hb s ρ T G G' (X' (Real.toNNReal r) ζ) ∂P ≤
      ENNReal.ofReal (max CA 0 * δ * L) * (1 + ENNReal.ofReal T) := by
  have m1 : Measurable fun p : ℝ × EucConfig d N =>
      s53_Dk s ρ ((fun τ : ℝ => G' (s53_clamp T τ)) p.1) p.2 :=
    s53_Dk_measurable ctx.hρ (F := fun τ => G' (s53_clamp T τ)) hG1m
  have m0 : Measurable fun p : ℝ × EucConfig d N => s53_Dk s ρ ((fun _ : ℝ => G 0) p.1) p.2 :=
    s53_Dk_measurable ctx.hρ (F := fun _ => G 0) (hG0m.comp measurable_snd)
  have hXr := hX'm (Real.toNNReal r)
  have ha0 : Measurable fun ζ => ‖s53_Dk s ρ (G 0) (X' (Real.toNNReal r) ζ)‖ₑ := by
    have hpr : Measurable fun ζ => ((0 : ℝ), X' (Real.toNNReal r) ζ) :=
      measurable_const.prodMk hXr
    exact (m0.comp hpr).enorm
  have ha1 : Measurable fun q : Ω × ℝ =>
      ‖s53_Dk s ρ (G' (s53_clamp T q.2)) (X' (Real.toNNReal r) q.1)‖ₑ := by
    have hpr : Measurable fun q : Ω × ℝ => (q.2, X' (Real.toNNReal r) q.1) :=
      measurable_snd.prodMk (hXr.comp measurable_fst)
    exact (m1.comp hpr).enorm
  unfold s53_Hb
  rw [lintegral_add_left ha0]
  have hswap : ∫⁻ ζ, (∫⁻ σ in Set.Icc (0 : ℝ) T,
      ‖s53_Dk s ρ (G' (s53_clamp T σ)) (X' (Real.toNNReal r) ζ)‖ₑ) ∂P =
      ∫⁻ σ in Set.Icc (0 : ℝ) T, ∫⁻ ζ,
        ‖s53_Dk s ρ (G' (s53_clamp T σ)) (X' (Real.toNNReal r) ζ)‖ₑ ∂P :=
    lintegral_lintegral_swap ha1.aemeasurable
  rw [hswap]
  have h0 := s53_exp_single (P := P) (s := s) (ρ := ρ) hδ hyp hae hr (hG 0 ⟨le_rfl, hT⟩) hL0
  have h1 : ∫⁻ σ in Set.Icc (0 : ℝ) T, ∫⁻ ζ,
      ‖s53_Dk s ρ (G' (s53_clamp T σ)) (X' (Real.toNNReal r) ζ)‖ₑ ∂P ≤
      ∫⁻ σ in Set.Icc (0 : ℝ) T, ENNReal.ofReal (max CA 0 * δ * L) := by
    refine setLIntegral_mono' measurableSet_Icc fun σ hσ => ?_
    rw [s53_clamp_of_mem hσ]
    exact s53_exp_single (P := P) (s := s) (ρ := ρ) hδ hyp hae hr (hG' σ hσ) (hL1 σ hσ)
  rw [setLIntegral_const, Real.volume_Icc, sub_zero] at h1
  calc ∫⁻ ζ, ‖s53_Dk s ρ (G 0) (X' (Real.toNNReal r) ζ)‖ₑ ∂P +
        ∫⁻ σ in Set.Icc (0 : ℝ) T, ∫⁻ ζ,
          ‖s53_Dk s ρ (G' (s53_clamp T σ)) (X' (Real.toNNReal r) ζ)‖ₑ ∂P
      ≤ ENNReal.ofReal (max CA 0 * δ * L) +
          ENNReal.ofReal (max CA 0 * δ * L) * ENNReal.ofReal T := add_le_add h0 h1
    _ = ENNReal.ofReal (max CA 0 * δ * L) * (1 + ENNReal.ofReal T) := by ring

end Exp


/-! ### One Hermite coordinate -/

lemma s53_gradient_measurable {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) :
    Measurable fun x => gradient f x := by
  have h1 : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  exact ((InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp h1).measurable

lemma s53_comm_eq {Ω : Type*} (C : WholeCoeff d) (s m : ℝ) (ρ : Euc d → ℝ)
    (X : ℝ≥0 → Ω → EucConfig d N) (α : MultiIndex d) (t r : ℝ) (ζ : Ω) :
    commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ =
      s53_Dk s ρ (propagatorW C r t (oscTestFun m α)) (X (Real.toNNReal r) ζ) := rfl

section Alpha

variable {s : ℝ} {ρ : Euc d → ℝ} {Mρ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma s53_alpha [IsProbabilityMeasure P] (ctx : S53Ctx s ρ Mρ) (hN : 0 < N) {T CA δ : ℝ} (hδ : 0 ≤ δ)
    (hT : 0 ≤ T) {C : WholeCoeff d} {m : ℝ} {α : MultiIndex d} {G G' G'' : ℝ → Euc d → ℝ}
    (hom : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → propagatorW C r t (oscTestFun m α) = G (t - r))
    (hG : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb 2 (G τ)) (hG' : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb 2 (G' τ))
    (hG'' : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb 2 (G'' τ))
    (hd0 : S53Diff T G G') (hd1 : S53Diff T G' G'') {L : ℝ}
    (hL0 : ∀ τ ∈ Set.Icc (0 : ℝ) T, (⨆ x, ‖iteratedFDeriv ℝ 2 (G τ) x‖) ≤ L)
    (hL1 : ∀ τ ∈ Set.Icc (0 : ℝ) T, (⨆ x, ‖iteratedFDeriv ℝ 2 (G' τ) x‖) ≤ L)
    {X X' : ℝ≥0 → Ω → EucConfig d N} {Gs : Set Ω}
    (hX'm : ∀ t, Measurable (X' t))
    (hX'j : Measurable fun p : ℝ × Ω => X' (Real.toNNReal p.1) p.2)
    (hGs : ∀ ζ ∈ Gs, ∀ t, X' t ζ = X t ζ) (hGsae : ∀ᵐ ζ ∂P, ζ ∈ Gs)
    (hyp : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ f : Euc d → ℝ, MemCb 2 f →
      Integrable (fun ζ => |s53_Dk s ρ f (X (Real.toNNReal r) ζ)|) P ∧
        ∫ ζ, |s53_Dk s ρ f (X (Real.toNNReal r) ζ)| ∂P ≤ CA * δ * ⨆ x, ‖iteratedFDeriv ℝ 2 f x‖) :
    ∃ g : Ω → ℝ≥0∞, Measurable g ∧
      ∫⁻ ζ, g ζ ∂P ≤ (ENNReal.ofReal (max CA 0 * δ * L) * (1 + ENNReal.ofReal T)) *
        ENNReal.ofReal T ∧
      ∀ ζ ∈ Gs, ∀ t ∈ Set.Icc (0 : ℝ) T,
        (∫⁻ r in Set.Icc (0 : ℝ) t, ‖commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ‖ₑ ≤ g ζ) ∧
        AEStronglyMeasurable (fun r => commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ)
          (volume.restrict (Set.Icc (0 : ℝ) t)) := by
  have hc0 : S53Cont T G := s53_cont_of_diff hG hG' hd0
  have hc1 : S53Cont T G' := s53_cont_of_diff hG' hG'' hd1
  have hG0m : Measurable fun x : Euc d => gradient (G 0) x :=
    s53_gradient_measurable ((hG 0 ⟨le_rfl, hT⟩).1.of_le (by norm_num))
  have hG1m := s53_grad_measurable hT hG' hc1
  have hF0m := s53_grad_measurable hT hG hc0
  have hae : ∀ t, ∀ᵐ ζ ∂P, X' t ζ = X t ζ := fun t => hGsae.mono fun ζ hζ => hGs ζ hζ t
  have hHb := s53_Hb_measurable (N := N) ctx T hG0m hG1m
  have hjoint : Measurable fun q : Ω × ℝ =>
      s53_Hb s ρ T G G' (X' (Real.toNNReal q.2) q.1) :=
    hHb.comp (hX'j.comp measurable_swap)
  refine ⟨fun ζ => ∫⁻ r in Set.Icc (0 : ℝ) T, s53_Hb s ρ T G G' (X' (Real.toNNReal r) ζ),
    hjoint.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) T)), ?_, ?_⟩
  · rw [lintegral_lintegral_swap hjoint.aemeasurable]
    calc ∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ ζ, s53_Hb s ρ T G G' (X' (Real.toNNReal r) ζ) ∂P
        ≤ ∫⁻ r in Set.Icc (0 : ℝ) T,
            ENNReal.ofReal (max CA 0 * δ * L) * (1 + ENNReal.ofReal T) := by
          refine setLIntegral_mono' measurableSet_Icc fun r hr => ?_
          exact s53_exp_Hb ctx hδ hT hX'm hyp hae hG hG' hG0m hG1m (hL0 0 ⟨le_rfl, hT⟩) hL1 hr
      _ = _ := by
          rw [setLIntegral_const, Real.volume_Icc, sub_zero]
  · intro ζ hζ t ht
    have hpt : ∀ r ∈ Set.Icc (0 : ℝ) t,
        ‖commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ‖ₑ ≤
          s53_Hb s ρ T G G' (X' (Real.toNNReal r) ζ) := by
      intro r hr
      rw [s53_comm_eq, hom r t hr.1 hr.2 ht.2, ← hGs ζ hζ]
      exact s53_path_bound ctx hN hG hG' hd0 hc1 _ ⟨by linarith [hr.2], by linarith [hr.1, ht.2]⟩
    refine ⟨?_, ?_⟩
    · calc ∫⁻ r in Set.Icc (0 : ℝ) t, ‖commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ‖ₑ
          ≤ ∫⁻ r in Set.Icc (0 : ℝ) t, s53_Hb s ρ T G G' (X' (Real.toNNReal r) ζ) :=
            setLIntegral_mono' measurableSet_Icc hpt
        _ ≤ ∫⁻ r in Set.Icc (0 : ℝ) T, s53_Hb s ρ T G G' (X' (Real.toNNReal r) ζ) :=
            lintegral_mono_set (Set.Icc_subset_Icc_right ht.2)
    · have m0 : Measurable fun p : ℝ × EucConfig d N =>
          s53_Dk s ρ (G (s53_clamp T p.1)) p.2 :=
        s53_Dk_measurable ctx.hρ (F := fun τ => G (s53_clamp T τ)) hF0m
      have hpr : Measurable fun r : ℝ => (t - r, X' (Real.toNNReal r) ζ) :=
        (measurable_const.sub measurable_id).prodMk
          (hX'j.comp (measurable_id.prodMk measurable_const))
      have hm : Measurable fun r : ℝ =>
          s53_Dk s ρ (G (s53_clamp T (t - r))) (X' (Real.toNNReal r) ζ) :=
        Measurable.comp (f := fun r : ℝ => (t - r, X' (Real.toNNReal r) ζ)) m0 hpr
      refine hm.aestronglyMeasurable.congr ?_
      refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun r hr => ?_)
      beta_reduce
      rw [s53_comm_eq, hom r t hr.1 hr.2 ht.2, hGs ζ hζ,
        s53_clamp_of_mem (show t - r ∈ Set.Icc (0 : ℝ) T from
          ⟨by linarith [hr.2], by linarith [hr.1, ht.2]⟩)]

end Alpha


/-! ### The conditional assembly -/

/-- The orbit input of S5.3: the (time-homogeneous) orbit `G0 α τ = U_τ φ_α`, `G1 α τ = U_τ L φ_α`,
`G2 α τ = U_τ L² φ_α` in `C_b²`, the identification `propagatorW C r t φ_α = G0 α (t - r)`, uniform bounds
`‖D²G_a‖_∞ ≤ K b_α` (`a = 0,1`) with `b` summable, and the difference quotients of `G0, G1` in `C_b²`. -/
structure S53Orbit (C : WholeCoeff d) (m T K : ℝ) (b : MultiIndex d → ℝ)
    (G0 G1 G2 : MultiIndex d → ℝ → Euc d → ℝ) : Prop where
  hom : ∀ α, ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → propagatorW C r t (oscTestFun m α) = G0 α (t - r)
  mem0 : ∀ α, ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb 2 (G0 α τ)
  mem1 : ∀ α, ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb 2 (G1 α τ)
  mem2 : ∀ α, ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb 2 (G2 α τ)
  bound0 : ∀ α, ∀ τ ∈ Set.Icc (0 : ℝ) T, (⨆ x, ‖iteratedFDeriv ℝ 2 (G0 α τ) x‖) ≤ K * b α
  bound1 : ∀ α, ∀ τ ∈ Set.Icc (0 : ℝ) T, (⨆ x, ‖iteratedFDeriv ℝ 2 (G1 α τ) x‖) ≤ K * b α
  cb0 : ∀ α, ∀ τ ∈ Set.Icc (0 : ℝ) T, cbNorm 2 (G0 α τ) ≤ K * b α
  cb1 : ∀ α, ∀ τ ∈ Set.Icc (0 : ℝ) T, cbNorm 2 (G1 α τ) ≤ K * b α
  hK : 0 ≤ K
  b_nonneg : ∀ α, 0 ≤ b α
  b_summable : Summable b
  diff0 : ∀ α, S53Diff T (G0 α) (G1 α)
  diff1 : ∀ α, S53Diff T (G1 α) (G2 α)

lemma s53_ennreal_arith {a B T : ℝ} (ha : 0 ≤ a) (hB : 0 ≤ B) (hT : 0 ≤ T) :
    ENNReal.ofReal a * ((ENNReal.ofReal B * (1 + ENNReal.ofReal T)) * ENNReal.ofReal T) =
      ENNReal.ofReal (a * (B * (1 + T) * T)) := by
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hT, ← ENNReal.ofReal_mul hB,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul ha]


/-- **`field_remainder`, conditional on the orbit input.**  All of the proof of S5.3 (first assertion) except the
construction of `S53Orbit` for the fixed-viscosity coefficients. -/
theorem s53_field_remainder_of_orbit (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m T : ℝ)
    (hT : 0 ≤ T) {ρ : Euc d → ℝ} (hρ : IsSchwartzDensity ρ) (D : WholeDyn d) (C : WholeCoeff d)
    {b : MultiIndex d → ℝ} {K : ℝ} {G0 G1 G2 : MultiIndex d → ℝ → Euc d → ℝ}
    (O : S53Orbit C m T K b G0 G1 G2) (CA : ℝ) :
    ∃ CT : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
      (X : ℝ≥0 → Ω → EucConfig d N), IsVectorBrownian P W →
      IsWholeStrongSolution P D T X₀ W X →
      (∀ r ∈ Set.Icc (0 : ℝ) T, ∀ f : Euc d → ℝ, MemCb 2 f →
        Integrable (fun ζ => |centeredPairFunctional (commutatorKernel d s (fun x => gradient f x))
            (X (Real.toNNReal r) ζ) (HRS.Whole.withDensityReal ρ)|) P ∧
        ∫ ζ, |centeredPairFunctional (commutatorKernel d s (fun x => gradient f x))
            (X (Real.toNNReal r) ζ) (HRS.Whole.withDensityReal ρ)| ∂P ≤
          CA * deltaN d s N * ⨆ x, ‖iteratedFDeriv ℝ 2 f x‖) →
      (∀ᵐ ζ ∂P, ∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) T,
        IntegrableOn (fun r => commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ)
          (Set.Icc 0 t)) ∧
      ∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) T, l2NormE (fun α : MultiIndex d =>
          -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) t,
            commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ)) ∂P ≤
        ENNReal.ofReal (CT * Real.sqrt N * deltaN d s N) := by
  obtain ⟨Mρ, ctx⟩ := s53_ctx_of_schwartz hd hs0 hsd hρ
  refine ⟨(1 / 2) * T * (1 + T) * max CA 0 * K * ∑' α, b α, ?_⟩
  intro N hN Ω _ P _ X₀ W X _ hX hyp0
  have hNpos : 0 < N := by omega
  have hδ := s53_deltaN_nonneg (d := d) (N := N) s hNpos
  have hyp : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ f : Euc d → ℝ, MemCb 2 f →
      Integrable (fun ζ => |s53_Dk s ρ f (X (Real.toNNReal r) ζ)|) P ∧
        ∫ ζ, |s53_Dk s ρ f (X (Real.toNNReal r) ζ)| ∂P ≤ CA * deltaN d s N * ⨆ x, ‖iteratedFDeriv ℝ 2 f x‖ :=
    hyp0
  obtain ⟨X', Gs, hGsm, hGs0, hGs, hX'm, hX'j⟩ := s53_modify P X hX.cont hX.adapted
  have hGsae : ∀ᵐ ζ ∂P, ζ ∈ Gs := by
    rw [ae_iff]
    exact hGs0
  choose g hgm hgint hgpath using fun α : MultiIndex d =>
    s53_alpha (P := P) (X := X) (X' := X') (Gs := Gs) ctx hNpos hδ hT (C := C) (m := m) (α := α)
      (O.hom α) (O.mem0 α) (O.mem1 α) (O.mem2 α) (O.diff0 α) (O.diff1 α)
      (L := K * b α) (O.bound0 α) (O.bound1 α) hX'm hX'j hGs hGsae hyp
  have hsq : 0 ≤ Real.sqrt N / 2 := by positivity
  have hB : ∀ α, 0 ≤ max CA 0 * deltaN d s N * (K * b α) := fun α => by
    have := O.b_nonneg α
    have := O.hK
    positivity
  constructor
  · -- integrability in `r`
    have hfin : ∀ α, ∀ᵐ ζ ∂P, g α ζ < ⊤ := fun α => by
      refine ae_lt_top (hgm α) (ne_top_of_le_ne_top ?_ (hgint α))
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.ofReal_ne_top⟩)) ENNReal.ofReal_ne_top
    have hall : ∀ᵐ ζ ∂P, ∀ α, g α ζ < ⊤ := ae_all_iff.2 hfin
    filter_upwards [hall, hGsae] with ζ hζ hζs α t ht
    obtain ⟨h1, h2⟩ := hgpath α ζ hζs t ht
    exact ⟨h2, lt_of_le_of_lt h1 (hζ α)⟩
  · -- the maximal estimate
    have hpath : ∀ ζ ∈ Gs, (⨆ t : Set.Icc (0 : ℝ) T, l2NormE (fun α : MultiIndex d =>
        -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) t,
          commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ)) ≤
        ∑' α, ENNReal.ofReal (Real.sqrt N / 2) * g α ζ := by
      intro ζ hζ
      refine iSup_le fun t => (s53_l2NormE_le _).trans (ENNReal.tsum_le_tsum fun α => ?_)
      have h1 := (hgpath α ζ hζ t t.2).1
      rw [abs_mul, abs_neg, abs_of_nonneg hsq, ENNReal.ofReal_mul hsq]
      refine mul_le_mul_right ?_ _
      rw [← Real.norm_eq_abs, ofReal_norm]
      exact (enorm_integral_le_lintegral_enorm _).trans h1
    calc ∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) T, l2NormE (fun α : MultiIndex d =>
          -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) t,
            commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ)) ∂P
        ≤ ∫⁻ ζ, ∑' α, ENNReal.ofReal (Real.sqrt N / 2) * g α ζ ∂P :=
          lintegral_mono_ae (hGsae.mono fun ζ hζ => hpath ζ hζ)
      _ = ∑' α, ENNReal.ofReal (Real.sqrt N / 2) * ∫⁻ ζ, g α ζ ∂P := by
          rw [lintegral_tsum fun α => ((hgm α).const_mul _).aemeasurable]
          exact tsum_congr fun α => lintegral_const_mul _ (hgm α)
      _ ≤ ∑' α, ENNReal.ofReal (Real.sqrt N / 2) *
            ((ENNReal.ofReal (max CA 0 * deltaN d s N * (K * b α)) * (1 + ENNReal.ofReal T)) *
              ENNReal.ofReal T) := ENNReal.tsum_le_tsum fun α => mul_le_mul_right (hgint α) _
      _ = ∑' α, ENNReal.ofReal ((Real.sqrt N / 2) *
            ((max CA 0 * deltaN d s N * (K * b α)) * (1 + T) * T)) :=
          tsum_congr fun α => s53_ennreal_arith hsq (hB α) hT
      _ = ENNReal.ofReal (∑' α, (Real.sqrt N / 2) *
            ((max CA 0 * deltaN d s N * (K * b α)) * (1 + T) * T)) := by
          rw [ENNReal.ofReal_tsum_of_nonneg]
          · intro α; have := hB α; positivity
          · refine Summable.mul_left _ ?_
            have := O.b_summable.mul_left (max CA 0 * deltaN d s N * K * (1 + T) * T)
            refine this.congr fun α => by ring
      _ = ENNReal.ofReal ((1 / 2) * T * (1 + T) * max CA 0 * K * (∑' α, b α) * Real.sqrt N *
            deltaN d s N) := by
          congr 1
          have : ∀ α, (Real.sqrt N / 2) * ((max CA 0 * deltaN d s N * (K * b α)) * (1 + T) * T) =
              ((Real.sqrt N / 2) * (max CA 0 * deltaN d s N * K * (1 + T) * T)) * b α :=
            fun α => by ring
          simp only [this]
          rw [tsum_mul_left]
          ring

end HRS.MS.S53
