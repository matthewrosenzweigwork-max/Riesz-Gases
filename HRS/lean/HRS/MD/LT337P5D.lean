import HRS.MD.LT337P5C

/-!
# Packet LT5 (chunk D), file D: `n → ∞` and the localised Coulomb energy identity

`lt5_stopped_identity_proof` is the statement `HRS.MD.LT337.lt5_stopped_identity` (M L3131-3137).  For `ε > 0` and
`t ∈ (0,T]` the fixed-kernel identity (file C) for the truncations `g_{m+n₀} = b15c_gReg d (d-2) (m+n₀)` is passed to the
limit `m → ∞` by dominated convergence, on both sides: the energies `E_{g_n}(X_σ) - E_{g_n}(X_0)` are bounded by `2B` (both
configurations are `ε`-separated on `{τ_ε > 0}`; the difference vanishes on `{τ_ε = 0}`), and the drifts
`1_{r<τ_ε} Jfull_{g_n}` are bounded by `B` (separation `≥ ε`) and converge to `1_{r<τ_ε} ltDrift`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.PDE HRS.Uniform.Q54c HRS.KID HRS.MD.LT337Vocab

namespace HRS.MD.LT337P5

variable {d : ℕ}

theorem lt5_pos_time (hd : 2 ≤ d) {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {D : DynData d} {N : ℕ} (hN : 2 ≤ N) {T Λ ΛV Mb : ℝ} (hT : 0 ≤ T)
    {ρ : ℝ → Torus d → ℝ} {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} (h : LowTempHyp P D N T Λ ΛV Mb ρ X₀ W X)
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hF : IsFilteredSolution P ℱ W' W X)
    {τ : ℝ → Ω → WithTop ℝ} (hτ : StoppingFamily P ℱ X T τ) (C₀ : ℝ)
    (hint0 : Integrable (fun ω => correctedEnergy D C₀ Λ ρ (X 0 ω) 0) P)
    {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht0 : 0 < t) (htT : t ≤ T) :
    Integrable (fun ω => correctedEnergy D C₀ Λ ρ (X (Real.toNNReal (stopTime t (τ ε ω))) ω)
      (stopTime t (τ ε ω))) P ∧
    Integrable (fun p : ℝ × Ω => if ((p.1 : ℝ) : WithTop ℝ) < τ ε p.2
        then ltDrift D ρ p.1 (X (Real.toNNReal p.1) p.2) else 0)
      ((volume.restrict (Set.Icc (0 : ℝ) t)).prod P) ∧
    ∫ ω, correctedEnergy D C₀ Λ ρ (X (Real.toNNReal (stopTime t (τ ε ω))) ω) (stopTime t (τ ε ω)) ∂P -
        ∫ ω, correctedEnergy D C₀ Λ ρ (X 0 ω) 0 ∂P =
      ∫ r in Set.Icc (0 : ℝ) t, ∫ ω, (if ((r : ℝ) : WithTop ℝ) < τ ε ω
        then ltDrift D ρ r (X (Real.toNNReal r) ω) else 0) ∂P := by
  have hd1 : 1 ≤ d := by omega
  have hN0 : 0 < N := by omega
  have c : MFctx D T Λ ρ := ⟨hd1, hT, h.V_reg.1, h.mf, h.mf_reg⟩
  have hsol := h.sol
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) t)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  set μ : Measure (ℝ × Ω) := (volume.restrict (Set.Icc (0 : ℝ) t)).prod P with hμ
  -- constants
  obtain ⟨L, hL0, hL⟩ := HRS.MD.LT337P1.lt1_lipschitz_proof hd Λ ΛV Mb
  have hLip : ∀ r ∈ Set.Icc (0 : ℝ) T, IsLipschitzVF L (meanFieldDrift D (ρ r)) := fun r hr =>
    hL D h.coulomb h.M_bound h.V_reg.1 h.V_reg.2 (ρ r) (c.ck3 hr) (c.cb hr)
  obtain ⟨n₀, B, hB⟩ := lt5_jfull_bound hd c h.coulomb hL0 hLip hε hN
  obtain ⟨BE, hBE⟩ := lt5_energy_bound_sep (d := d) (N := N) hd1 D.hs0 D.hsd Λ hε hN0
  have hsm : ∀ m : ℕ, Torus.IsSmooth (b15c_gReg d D.s (((m + n₀ : ℕ)) : ℝ)) := fun m =>
    b15c_gReg_isSmooth hd1 D.hs0 D.hsd _
  have hev : ∀ (m : ℕ) x, b15c_gReg d D.s (((m + n₀ : ℕ)) : ℝ) (-x) =
      b15c_gReg d D.s (((m + n₀ : ℕ)) : ℝ) x := fun m x => b15c_gReg_neg D.s _ x
  have hσ0 : ∀ ω, 0 ≤ stopTime t (τ ε ω) := fun ω => lt5_stopTime_nonneg ht0.le (hτ.zero_le ε ω)
  have hσT : ∀ ω, stopTime t (τ ε ω) ∈ Set.Icc (0 : ℝ) T :=
    fun ω => ⟨hσ0 ω, (lt5_stopTime_le t _).trans htT⟩
  -- the drift bound on `{r < τ}`
  have hJb : ∀ m : ℕ, ∀ᵐ ω ∂P, ∀ r ∈ Set.Icc (0 : ℝ) t, ((r : ℝ) : WithTop ℝ) < τ ε ω →
      |Jfull D (b15c_gReg d D.s (((m + n₀ : ℕ)) : ℝ)) ρ X r ω| ≤ B := by
    intro m
    filter_upwards [hτ.sep] with ω hω r hr hlt
    have hrT : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans htT⟩
    have hpos : (0 : WithTop ℝ) < τ ε ω := lt_of_le_of_lt (WithTop.coe_le_coe.2 hr.1) hlt
    have hsep := hω ε hε r hrT hlt.le hpos
    exact hB (m + n₀) (Nat.le_add_left n₀ m) r hrT _ hsep
  have hfix := fun m : ℕ => lt5_fixed_kernel c hN ht0 htT hsol hF (hsm m) (hev m) (hτ.stopping ε)
    (hτ.zero_le ε) (hJb m)
  have hE0i : ∀ m : ℕ, Integrable (fun ω => modulatedEnergyKernel (b15c_gReg d D.s (((m + n₀ : ℕ)) : ℝ))
      (X 0 ω) (withDensityReal (ρ 0))) P := fun m => by
    have := c.integrable_energy hN hsol (hsm m) (hev m) (r := 0) ⟨le_rfl, hT⟩
    simpa using this
  -- the limit energy difference
  set Δ : Ω → ℝ := fun ω =>
    rieszEnergy d D.s (X (Real.toNNReal (stopTime t (τ ε ω))) ω) (withDensityReal (ρ (stopTime t (τ ε ω)))) -
      rieszEnergy d D.s (X 0 ω) (withDensityReal (ρ 0)) with hΔ
  have D1 : ∀ᵐ ω ∂P, Tendsto (fun m : ℕ =>
      modulatedEnergyKernel (b15c_gReg d D.s (((m + n₀ : ℕ)) : ℝ))
        (X (Real.toNNReal (stopTime t (τ ε ω))) ω) (withDensityReal (ρ (stopTime t (τ ε ω)))) -
      modulatedEnergyKernel (b15c_gReg d D.s (((m + n₀ : ℕ)) : ℝ)) (X 0 ω) (withDensityReal (ρ 0)))
      atTop (𝓝 (Δ ω)) := by
    filter_upwards [hsol.no_collision] with ω hω
    have hX1 : X (Real.toNNReal (stopTime t (τ ε ω))) ω ∉ collisionSet d N :=
      hω _ (by rw [Real.coe_toNNReal _ (hσ0 ω)]; exact (hσT ω).2)
    have hX0 : X 0 ω ∉ collisionSet d N := hω 0 (by simpa using hT)
    have h0T : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
    have t1 := movc_energy_tendsto hd1 D.hs0 D.hsd (c.dens (hσT ω)) (c.cont (hσT ω))
      (M := fun n : ℕ => (n : ℝ)) tendsto_natCast_atTop_atTop (fun n => Nat.cast_nonneg n) hX1
    have t0 := movc_energy_tendsto hd1 D.hs0 D.hsd (c.dens h0T) (c.cont h0T)
      (M := fun n : ℕ => (n : ℝ)) tendsto_natCast_atTop_atTop (fun n => Nat.cast_nonneg n) hX0
    exact (t1.comp (tendsto_add_atTop_nat n₀)).sub (t0.comp (tendsto_add_atTop_nat n₀))
  have D2 : ∀ᵐ ω ∂P, ∀ m : ℕ,
      ‖modulatedEnergyKernel (b15c_gReg d D.s (((m + n₀ : ℕ)) : ℝ))
        (X (Real.toNNReal (stopTime t (τ ε ω))) ω) (withDensityReal (ρ (stopTime t (τ ε ω)))) -
      modulatedEnergyKernel (b15c_gReg d D.s (((m + n₀ : ℕ)) : ℝ)) (X 0 ω) (withDensityReal (ρ 0))‖
        ≤ 2 * max BE 0 := by
    filter_upwards [hτ.sep] with ω hω m
    have hBE0 : 0 ≤ max BE 0 := le_max_right _ _
    rcases (hτ.zero_le ε ω).eq_or_lt with h0 | hpos
    · have hs0 : stopTime t (τ ε ω) = 0 := by rw [← h0]; exact lt5_stopTime_zero ht0.le
      rw [hs0, Real.toNNReal_zero, sub_self, norm_zero]
      linarith
    · have hs1 := hω ε hε (stopTime t (τ ε ω)) ⟨hσ0 ω, (lt5_stopTime_le t _).trans htT⟩
        (lt5_coe_stopTime_le t _) hpos
      have hs2 := hω ε hε 0 ⟨le_rfl, hT⟩ (by simpa using hpos.le) hpos
      rw [Real.toNNReal_zero] at hs2
      have h1 := hBE (m + n₀) (ρ (stopTime t (τ ε ω))) (c.dens (hσT ω)) (fun y => c.abs_le (hσT ω) y) _ hs1
      have h2 := hBE (m + n₀) (ρ 0) (c.dens ⟨le_rfl, hT⟩) (fun y => c.abs_le ⟨le_rfl, hT⟩ y) _ hs2
      rw [Real.norm_eq_abs]
      refine (abs_sub _ _).trans ?_
      have := le_max_left BE 0
      linarith
  have hΔm : AEStronglyMeasurable Δ P :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun m => ((hfix m).1.sub (hE0i m)).aestronglyMeasurable) D1
  have hΔb : ∀ᵐ ω ∂P, ‖Δ ω‖ ≤ 2 * max BE 0 := by
    filter_upwards [D1, D2] with ω h1 h2
    exact le_of_tendsto h1.norm (Eventually.of_forall h2)
  have hΔi : Integrable Δ P := Integrable.of_bound hΔm _ hΔb
  have Dlim : Tendsto (fun m : ℕ => ∫ ω, (modulatedEnergyKernel (b15c_gReg d D.s (((m + n₀ : ℕ)) : ℝ))
        (X (Real.toNNReal (stopTime t (τ ε ω))) ω) (withDensityReal (ρ (stopTime t (τ ε ω)))) -
      modulatedEnergyKernel (b15c_gReg d D.s (((m + n₀ : ℕ)) : ℝ)) (X 0 ω) (withDensityReal (ρ 0))) ∂P)
      atTop (𝓝 (∫ ω, Δ ω ∂P)) :=
    tendsto_integral_of_dominated_convergence (fun _ => 2 * max BE 0)
      (fun m => ((hfix m).1.sub (hE0i m)).aestronglyMeasurable) (integrable_const _)
      (fun m => by filter_upwards [D2] with ω hω; exact hω m) D1
  -- the drift side
  have hr : ∀ᵐ p ∂μ, p.1 ∈ Set.Icc (0 : ℝ) t :=
    (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Set.Icc (0 : ℝ) t)) (ν := P)).ae
      (ae_restrict_mem measurableSet_Icc)
  have hnc : ∀ᵐ p ∂μ, ∀ s : ℝ≥0, (s : ℝ) ≤ T → X s p.2 ∉ collisionSet d N :=
    (Measure.quasiMeasurePreserving_snd (μ := volume.restrict (Set.Icc (0 : ℝ) t)) (ν := P)).ae
      hsol.no_collision
  have hlimG : ∀ᵐ p ∂μ, Tendsto (fun m : ℕ =>
      if ((p.1 : ℝ) : WithTop ℝ) < τ ε p.2
        then Jfull D (b15c_gReg d D.s (((m + n₀ : ℕ)) : ℝ)) ρ X p.1 p.2 else 0) atTop
      (𝓝 (if ((p.1 : ℝ) : WithTop ℝ) < τ ε p.2
        then ltDrift D ρ p.1 (X (Real.toNNReal p.1) p.2) else 0)) := by
    filter_upwards [hr, hnc] with p hp1 hp2
    by_cases hlt : ((p.1 : ℝ) : WithTop ℝ) < τ ε p.2
    · simp only [hlt, if_true]
      have hrT : p.1 ∈ Set.Icc (0 : ℝ) T := ⟨hp1.1, hp1.2.trans htT⟩
      have hX := hp2 (Real.toNNReal p.1) (by rw [Real.coe_toNNReal _ hp1.1]; exact hrT.2)
      exact (lt5_jfull_tendsto hd c h.coulomb hL0 hLip hN hrT hX).comp (tendsto_add_atTop_nat n₀)
    · simp only [hlt, if_false]
      exact tendsto_const_nhds
  have hGae : AEStronglyMeasurable (fun p : ℝ × Ω => if ((p.1 : ℝ) : WithTop ℝ) < τ ε p.2
      then ltDrift D ρ p.1 (X (Real.toNNReal p.1) p.2) else 0) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun m => (hfix m).2.1.aestronglyMeasurable) hlimG
  have hGb : ∀ᵐ p ∂μ, ‖if ((p.1 : ℝ) : WithTop ℝ) < τ ε p.2
      then ltDrift D ρ p.1 (X (Real.toNNReal p.1) p.2) else 0‖ ≤ max B 0 := by
    have hall : ∀ᵐ p ∂μ, ∀ m : ℕ, ‖if ((p.1 : ℝ) : WithTop ℝ) < τ ε p.2
        then Jfull D (b15c_gReg d D.s (((m + n₀ : ℕ)) : ℝ)) ρ X p.1 p.2 else 0‖ ≤ max B 0 := by
      have := fun m : ℕ => lt5_G_bound (ρ := ρ) (D := D) (X := X) (τ := τ ε) (hJb m)
      exact (ae_all_iff).2 this
    filter_upwards [hall, hlimG] with p h1 h2
    exact le_of_tendsto h2.norm (Eventually.of_forall h1)
  have hGi : Integrable (fun p : ℝ × Ω => if ((p.1 : ℝ) : WithTop ℝ) < τ ε p.2
      then ltDrift D ρ p.1 (X (Real.toNNReal p.1) p.2) else 0) μ := Integrable.of_bound hGae _ hGb
  have Glim : Tendsto (fun m : ℕ => ∫ p, (if ((p.1 : ℝ) : WithTop ℝ) < τ ε p.2
        then Jfull D (b15c_gReg d D.s (((m + n₀ : ℕ)) : ℝ)) ρ X p.1 p.2 else 0) ∂μ) atTop
      (𝓝 (∫ p, (if ((p.1 : ℝ) : WithTop ℝ) < τ ε p.2
        then ltDrift D ρ p.1 (X (Real.toNNReal p.1) p.2) else 0) ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ => max B 0)
      (fun m => (hfix m).2.1.aestronglyMeasurable) (integrable_const _)
      (fun m => lt5_G_bound (ρ := ρ) (D := D) (X := X) (τ := τ ε) (hJb m)) hlimG
  -- the two sequences coincide
  have hseq : ∀ m : ℕ, ∫ ω, (modulatedEnergyKernel (b15c_gReg d D.s (((m + n₀ : ℕ)) : ℝ))
        (X (Real.toNNReal (stopTime t (τ ε ω))) ω) (withDensityReal (ρ (stopTime t (τ ε ω)))) -
      modulatedEnergyKernel (b15c_gReg d D.s (((m + n₀ : ℕ)) : ℝ)) (X 0 ω) (withDensityReal (ρ 0))) ∂P =
      ∫ p, (if ((p.1 : ℝ) : WithTop ℝ) < τ ε p.2
        then Jfull D (b15c_gReg d D.s (((m + n₀ : ℕ)) : ℝ)) ρ X p.1 p.2 else 0) ∂μ := by
    intro m
    rw [integral_sub (hfix m).1 (hE0i m), (hfix m).2.2, hμ, integral_prod _ (hfix m).2.1]
  have hlimeq : ∫ ω, Δ ω ∂P = ∫ p, (if ((p.1 : ℝ) : WithTop ℝ) < τ ε p.2
        then ltDrift D ρ p.1 (X (Real.toNNReal p.1) p.2) else 0) ∂μ :=
    tendsto_nhds_unique Dlim (Glim.congr fun m => (hseq m).symm)
  -- assembly
  have hcorr : (fun ω => correctedEnergy D C₀ Λ ρ (X (Real.toNNReal (stopTime t (τ ε ω))) ω)
      (stopTime t (τ ε ω))) = fun ω => Δ ω + correctedEnergy D C₀ Λ ρ (X 0 ω) 0 := by
    funext ω
    simp only [hΔ, correctedEnergy]
    ring
  have h1 : Integrable (fun ω => correctedEnergy D C₀ Λ ρ (X (Real.toNNReal (stopTime t (τ ε ω))) ω)
      (stopTime t (τ ε ω))) P := by
    rw [hcorr]; exact hΔi.add hint0
  refine ⟨h1, hGi, ?_⟩
  rw [← integral_sub h1 hint0]
  have e : (fun ω => correctedEnergy D C₀ Λ ρ (X (Real.toNNReal (stopTime t (τ ε ω))) ω)
      (stopTime t (τ ε ω)) - correctedEnergy D C₀ Λ ρ (X 0 ω) 0) = Δ := by
    funext ω
    simp only [hΔ, correctedEnergy]
    ring
  rw [e, hlimeq, hμ, integral_prod _ hGi]

theorem lt5_stopped_identity_proof (hd : 2 ≤ d) {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {D : DynData d} {N : ℕ} (hN : 2 ≤ N) {T Λ ΛV Mb : ℝ} (hT : 0 ≤ T)
    {ρ : ℝ → Torus d → ℝ} {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} (h : LowTempHyp P D N T Λ ΛV Mb ρ X₀ W X)
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hF : IsFilteredSolution P ℱ W' W X)
    {τ : ℝ → Ω → WithTop ℝ} (hτ : StoppingFamily P ℱ X T τ) (C₀ : ℝ)
    (hint0 : Integrable (fun ω => correctedEnergy D C₀ Λ ρ (X 0 ω) 0) P) :
    StoppedIdentity P D N T Λ C₀ ρ X τ := by
  intro ε hε t ht
  obtain rfl | hpos := ht.1.eq_or_lt
  · have hσ : ∀ ω, stopTime 0 (τ ε ω) = 0 := fun ω =>
      le_antisymm (lt5_stopTime_le 0 _) (lt5_stopTime_nonneg le_rfl (hτ.zero_le ε ω))
    have hz : (volume.restrict (Set.Icc (0 : ℝ) 0)) = 0 := by
      rw [Set.Icc_self]; exact Measure.restrict_eq_zero.2 (by simp)
    simp only [hσ, Real.toNNReal_zero]
    refine ⟨hint0, ?_, ?_⟩
    · rw [hz, Measure.zero_prod]; exact integrable_zero_measure
    · rw [hz]; simp
  · exact lt5_pos_time hd hN hT h hF hτ C₀ hint0 hε hpos ht.2

end HRS.MD.LT337P5
