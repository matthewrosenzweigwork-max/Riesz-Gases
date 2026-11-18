import HRS.MC.S7PIF4E

/-!
# Packet piF4, part F: observation time `t_i = 0`, the progressive integrand, `U^{τ,τ} = id`, the window path

* `S7PIF4_sq_null`: an integrand vanishing off `{0}` has `sqIntegralOn = 0`;
* `S7PIF4_prog_zero`: for `τ = 0` the noise integrand of the empirical martingale is progressive and `L²`;
* `S7PIF4_prog_pos`: for `0 < τ ≤ T` the same, from `F1`;
* `S7PIF4_prop_self`: `U^{τ,τ} ψ = ψ` for smooth `ψ`, `τ ∈ [0,T]`;
* `S7PIF4_pathAt_zetaWin`: `pathAt (ζ-window) s = ζ_s` on `[0,T]` when `ζ` is continuous;
* `S7PIF4_key_all`: the key identity for every `τ ∈ [0,T]`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIF4

open HRS HRS.PDE HRS.A33 HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

theorem S7PIF4_sq_null {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Fintype ι] (P : Measure Ω)
    (Φ : ℝ → Ω → ι → ℝ) (hz : ∀ s ω k, s ≠ 0 → Φ s ω k = 0) (T : ℝ) : sqIntegralOn P Φ T = 0 := by
  unfold sqIntegralOn
  have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ∉ ({0} : Set ℝ) := (Set.countable_singleton (0 : ℝ)).ae_notMem _
  have : ∀ ω, ∫⁻ s in Set.Icc 0 T, ∑ k, ‖Φ s ω k‖ₑ ^ 2 = 0 := by
    intro ω
    have : ∀ᵐ s ∂(volume.restrict (Set.Icc 0 T)), ∑ k, ‖Φ s ω k‖ₑ ^ 2 = 0 := by
      refine ae_restrict_of_ae ?_
      filter_upwards [hae] with s hs
      have hs0 : s ≠ 0 := fun h => hs (by simp [h])
      simp [hz s ω _ hs0]
    rw [lintegral_congr_ae this]; simp
  simp [this]

section Prob

variable (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) (N : ℕ) (hN : 1 ≤ N)
  {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
  (hreal : PreparedRealization R.D P
    (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X)

include hm hT hN hreal

/-- `U^{τ,τ} ψ = ψ` for smooth `ψ` and `τ ∈ [0,T]`. -/
theorem S7PIF4_prop_self {ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) T) :
    propagator R.D R.ρ τ τ ψ = ψ := by
  rcases hτ.1.eq_or_lt with h0 | hpos
  · subst h0
    obtain ⟨J, k, hk, hJ, hm0, hm1, H⟩ := HRS.MC.Sec7.S7PIS1.S7PIS1_data R m hm T hT
    exact HRS.MC.Sec7.S7PIS1.S7PIS1_prop_zero H hψ
  · obtain ⟨F, hFcl, hFeq⟩ := HRS.MC.L2C3.l2c3_classical R hpos hψ
    rw [hFeq τ ⟨hτ.1, le_rfl⟩]
    exact hFcl.terminal

/-- the noise integrand at `τ = 0` is progressive and `L²` -/
theorem S7PIF4_prog_zero {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution P ℱ W' W X) {ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) :
    IsProgressiveL2 P ℱ
      (empiricalNoiseIntegrand R.D 0 (fun r => propagator R.D R.ρ r 0 ψ) X) := by
  set f : ℝ → Torus d → ℝ := fun r => propagator R.D R.ρ r 0 ψ with hf
  have hf0 : f 0 = ψ := S7PIF4_prop_self R m hm T hT N hN P X₀ W X hreal hψ ⟨le_rfl, hT.le⟩
  have hgradc : Continuous (Torus.grad ψ) := by
    have h := HRS.KernelD1Aux.isSmooth_grad hψ
    have hF' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift (Torus.grad ψ)) := h
    exact HRS.KernelGrad.isOpenQuotientMap_mk.continuous_comp_iff.mp hF'.continuous
  have hz : ∀ s ω k, s ≠ 0 →
      empiricalNoiseIntegrand R.D 0 f X s ω k = 0 := by
    intro s ω k hs
    unfold empiricalNoiseIntegrand
    have : s ∉ Set.Icc (0 : ℝ) 0 := fun h => hs (le_antisymm h.2 h.1)
    rw [if_neg this]
  refine ⟨?_, fun T' => by rw [S7PIF4_sq_null P _ hz]; exact ENNReal.zero_lt_top⟩
  intro i
  refine (@measurable_pi_iff _ _ _ (Subtype.instMeasurableSpace.prod (ℱ i)) _ _).2 fun k => ?_
  by_cases hi : 0 ≤ i
  · set g : Ω → ℝ := fun ω => (Real.sqrt (2 * R.D.invβ) / N) *
      (Torus.grad ψ (X 0 ω k.1)) k.2 with hg
    have hg0 : Measurable[ℱ 0] g := by
      have h1 : Measurable[ℱ 0] (fun ω => X 0 ω k.1) := (measurable_pi_apply k.1).comp (hF.adapted 0)
      have h2 : Measurable fun x : Torus d => (Torus.grad ψ x) k.2 :=
        ((EuclideanSpace.proj k.2 : Euc d →L[ℝ] ℝ).continuous.comp hgradc).measurable
      exact (h2.comp h1).const_mul _
    have hgi : Measurable[ℱ i] g := hg0.mono (ℱ.mono hi) le_rfl
    have heq : (fun p : Set.Iic i × Ω => empiricalNoiseIntegrand R.D 0 f X p.1 p.2 k) =
        fun p => if ((p.1 : ℝ) = 0) then g p.2 else 0 := by
      funext p
      unfold empiricalNoiseIntegrand
      by_cases h : (p.1 : ℝ) = 0
      · rw [if_pos h, if_pos (by simp [h])]
        rw [h, Real.toNNReal_zero, hf0]
      · rw [if_neg h, if_neg (fun h' => h (le_antisymm h'.2 h'.1))]
    rw [heq]
    have hset : MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ i)]
        {p : Set.Iic i × Ω | (p.1 : ℝ) = 0} := by
      have : {p : Set.Iic i × Ω | (p.1 : ℝ) = 0} = {u : Set.Iic i | (u : ℝ) = 0} ×ˢ Set.univ := by
        ext p; simp
      rw [this]
      exact MeasurableSet.prod (measurable_subtype_coe (measurableSet_singleton 0)) MeasurableSet.univ
    exact Measurable.ite hset (hgi.comp measurable_snd) measurable_const
  · have heq : (fun p : Set.Iic i × Ω => empiricalNoiseIntegrand R.D 0 f X p.1 p.2 k) = fun _ => 0 := by
      funext p
      apply hz
      intro h0
      have : (p.1 : ℝ) ≤ i := p.1.2
      linarith [not_le.1 hi]
    rw [heq]
    exact measurable_const

/-- the noise integrand at `0 < τ ≤ T` is progressive and `L²` -/
theorem S7PIF4_prog_pos {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution P ℱ W' W X) {ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) {τ : ℝ}
    (hτ : τ ∈ Set.Ioc 0 T) :
    IsProgressiveL2 P ℱ
      (empiricalNoiseIntegrand R.D τ (fun r => propagator R.D R.ρ r τ ψ) X) := by
  obtain ⟨F, hFcl, hFeq⟩ := HRS.MC.L2C3.l2c3_classical R hτ.1 hψ
  have hψ2 : Torus.IsCk 2 ψ :=
    ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift ψ) from hψ)
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  obtain ⟨hprogF, -⟩ := HRS.MC.Sec7.S7PIF1.s7_PIF_duality_proof R T hT N hN P X₀ W X hreal hF hτ hψ2 hFcl
  have hΦeq : empiricalNoiseIntegrand R.D τ F X =
      empiricalNoiseIntegrand R.D τ (fun r => propagator R.D R.ρ r τ ψ) X := by
    funext s ω k
    unfold empiricalNoiseIntegrand
    by_cases h : s ∈ Set.Icc 0 τ
    · simp only [h, if_true]
      rw [hFeq s h]
    · simp [h]
  exact hΦeq ▸ hprogF

/-- the key identity for every `τ ∈ [0,T]` -/
theorem S7PIF4_key_all {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution P ℱ W' W X) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) T) :
    ∀ᵐ ω ∂P, ∀ u ∈ Set.Icc (0 : ℝ) τ,
      NegSobolev.eval (zetaAt m P X u ω) (propagator R.D R.ρ u τ φ) =
        NegSobolev.eval (zetaAt m P X 0 ω) (propagator R.D R.ρ 0 τ φ) -
        (Real.sqrt N)⁻¹ * (∫ r in Set.Ioc 0 u,
          NegSobolev.eval (quadFieldAt m R.D.s (fun s => withDensityReal (R.ρ s)) P X r ω)
            (propagator R.D R.ρ r τ φ)) +
        Real.sqrt N * empiricalMartingale P ℱ W' R.D τ (fun r => propagator R.D R.ρ r τ φ) X u ω := by
  rcases hτ.1.eq_or_lt with h0 | hpos
  · subst h0
    have hprog := S7PIF4_prog_zero R m hm T hT N hN P X₀ W X hreal hF hφ
    filter_upwards [] with ω u hu
    have hu0 : u = 0 := le_antisymm hu.2 hu.1
    subst hu0
    have hM0 : empiricalMartingale P ℱ W' R.D 0 (fun r => propagator R.D R.ρ r 0 φ) X 0 ω = 0 :=
      itoIntegral_of_nonpos P ℱ W' _ le_rfl ω
    rw [hM0]
    simp
  · exact S7PIF4_key R m hm T hT N hN P X₀ W X hreal hF hφ ⟨hpos, hτ.2⟩

end Prob

/-- `pathAt` of the `ζ`-window on `[0,T]`. -/
theorem S7PIF4_pathAt_zetaWin {m T : ℝ} {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → Config d N) (ω : Ω)
    (hc : Continuous fun t : Set.Icc (0 : ℝ) T => zetaAt m P X t ω) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) :
    pathAt (zetaWin m T 0 P X ω) s = zetaAt m P X s ω := by
  have hc' : Continuous fun t : Set.Icc (0 : ℝ) T => zetaAt m P X (0 + (t : ℝ)) ω := by
    simpa using hc
  unfold pathAt zetaWin
  rw [dif_pos hs]
  have hw : toPath m T (fun t ω => zetaAt m P X (0 + t) ω) ω =
      (⟨fun t : Set.Icc (0 : ℝ) T => zetaAt m P X (0 + (t : ℝ)) ω, hc'⟩ :
        C(Set.Icc (0 : ℝ) T, NegSobolev d m)) := by
    unfold toPath
    exact dif_pos hc'
  rw [hw]
  simp [PathSpace.at']

end HRS.MC.Sec7.S7PIF4

end
