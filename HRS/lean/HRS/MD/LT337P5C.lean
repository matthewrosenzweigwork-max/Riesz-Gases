import HRS.MD.LT337P5B

/-!
# Packet LT5 (chunk D), file C: the stopped identity for a fixed smooth kernel

`lt5_fixed_kernel`: for a smooth even kernel `h` and a stopping time `τ ≥ 0` such that `|Jfull_h| ≤ B` on `{r < τ}`,
`E[E_h(X_σ, ρ_σ)] - E[E_h(X_0, ρ_0)] = ∫_0^t E[1_{r<τ} Jfull_h(r)] dr`, `σ = t ∧ τ`
(pathwise identity at the random time `σ` + optional stopping `integral_stoppedProcess_itoIntegral` + Fubini).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.PDE HRS.Uniform.Q54c HRS.KID HRS.MD.LT337Vocab

namespace HRS.MD.LT337P5

variable {d N : ℕ}

theorem lt5_integral_stop (f : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) (τ : WithTop ℝ) :
    ∫ r in Set.Icc (0 : ℝ) (stopTime t τ), f r =
      ∫ r in Set.Icc (0 : ℝ) t, (if ((r : ℝ) : WithTop ℝ) < τ then f r else 0) := by
  induction τ using WithTop.recTopCoe with
  | top => simp [stopTime]
  | coe c =>
    have hstop : stopTime t (c : WithTop ℝ) = min t c := by simp [stopTime]
    rw [hstop]
    simp only [WithTop.coe_lt_coe]
    have e : (fun r : ℝ => if r < c then f r else 0) = (Set.Iio c).indicator f := by
      funext r; simp [Set.indicator]
    rw [e, setIntegral_indicator measurableSet_Iio]
    rcases le_or_gt c t with hc | hc
    · rw [min_eq_right hc]
      have : Set.Icc (0 : ℝ) t ∩ Set.Iio c = Set.Ico 0 c := by
        ext r
        simp only [mem_inter_iff, mem_Icc, mem_Iio, mem_Ico]
        constructor
        · rintro ⟨⟨h0, _⟩, h2⟩; exact ⟨h0, h2⟩
        · rintro ⟨h0, h2⟩; exact ⟨⟨h0, (h2.trans_le hc).le⟩, h2⟩
      rw [this]
      exact (setIntegral_congr_set Ico_ae_eq_Icc).symm
    · rw [min_eq_left hc.le]
      have : Set.Icc (0 : ℝ) t ∩ Set.Iio c = Set.Icc 0 t :=
        inter_eq_left.2 fun r hr => lt_of_le_of_lt hr.2 hc
      rw [this]

section Fixed

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {D : DynData d}
  {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
  {T Λ : ℝ} {ρ : ℝ → Torus d → ℝ}

/-- The a.e. bound for the stopped drift integrand on `[0,t] × Ω`. -/
theorem lt5_G_bound {t : ℝ} {h : Torus d → ℝ} {τ : Ω → WithTop ℝ} {B : ℝ}
    (hJb : ∀ᵐ ω ∂P, ∀ r ∈ Set.Icc (0 : ℝ) t, ((r : ℝ) : WithTop ℝ) < τ ω → |Jfull D h ρ X r ω| ≤ B) :
    ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) t)).prod P),
      ‖if ((p.1 : ℝ) : WithTop ℝ) < τ p.2 then Jfull D h ρ X p.1 p.2 else 0‖ ≤ max B 0 := by
  have hr : ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) t)).prod P), p.1 ∈ Set.Icc (0 : ℝ) t :=
    (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Set.Icc (0 : ℝ) t)) (ν := P)).ae
      (ae_restrict_mem measurableSet_Icc)
  have h2 : ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) t)).prod P), ∀ r ∈ Set.Icc (0 : ℝ) t,
      ((r : ℝ) : WithTop ℝ) < τ p.2 → |Jfull D h ρ X r p.2| ≤ B :=
    (Measure.quasiMeasurePreserving_snd (μ := volume.restrict (Set.Icc (0 : ℝ) t)) (ν := P)).ae hJb
  filter_upwards [hr, h2] with p hp1 hp2
  split_ifs with hlt
  · rw [Real.norm_eq_abs]; exact (hp2 p.1 hp1 hlt).trans (le_max_left _ _)
  · simp

theorem lt5_fixed_kernel (c : MFctx D T Λ ρ) (hN : 2 ≤ N) {t : ℝ} (ht0 : 0 < t) (htT : t ≤ T)
    (hsol : IsStrongSolution P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    {h : Torus d → ℝ} (hsm : Torus.IsSmooth h) (hev : ∀ x, h (-x) = h x)
    {τ : Ω → WithTop ℝ} (hτs : IsStoppingTime ℱ τ) (hτ0 : ∀ ω, 0 ≤ τ ω)
    {B : ℝ} (hJb : ∀ᵐ ω ∂P, ∀ r ∈ Set.Icc (0 : ℝ) t, ((r : ℝ) : WithTop ℝ) < τ ω →
      |Jfull D h ρ X r ω| ≤ B) :
    Integrable (fun ω => modulatedEnergyKernel h (X (Real.toNNReal (stopTime t (τ ω))) ω)
      (withDensityReal (ρ (stopTime t (τ ω))))) P ∧
    Integrable (fun p : ℝ × Ω => if ((p.1 : ℝ) : WithTop ℝ) < τ p.2 then Jfull D h ρ X p.1 p.2 else 0)
      ((volume.restrict (Set.Icc 0 t)).prod P) ∧
    ∫ ω, modulatedEnergyKernel h (X (Real.toNNReal (stopTime t (τ ω))) ω)
        (withDensityReal (ρ (stopTime t (τ ω)))) ∂P -
      ∫ ω, modulatedEnergyKernel h (X 0 ω) (withDensityReal (ρ 0)) ∂P =
    ∫ r in Set.Icc (0 : ℝ) t, ∫ ω, (if ((r : ℝ) : WithTop ℝ) < τ ω then Jfull D h ρ X r ω else 0) ∂P := by
  have hN0 : 0 < N := by omega
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) t)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  set μ : Measure (ℝ × Ω) := (volume.restrict (Set.Icc 0 t)).prod P with hμ
  have hσm : Measurable fun ω => stopTime t (τ ω) := lt5_measurable_stopTime hτs t
  have hσ0 : ∀ ω, 0 ≤ stopTime t (τ ω) := fun ω => lt5_stopTime_nonneg ht0.le (hτ0 ω)
  have hσt : ∀ ω, stopTime t (τ ω) ≤ t := fun ω => lt5_stopTime_le t _
  have hσT : ∀ ω, stopTime t (τ ω) ∈ Set.Icc (0 : ℝ) T := fun ω => ⟨hσ0 ω, (hσt ω).trans htT⟩
  obtain ⟨hΨ1, hΨ2, hpath⟩ := lt5_kid_pathwise_all c hN ht0 htT hsol hF hsm hev
  -- the energy at the random time
  have hE1m : Measurable fun ω => modulatedEnergyKernel h (X (Real.toNNReal (stopTime t (τ ω))) ω)
      (withDensityReal (ρ (stopTime t (τ ω)))) := by
    have hm := lt5_measurable_energy_clamp c hN0 hsm hev
    have hXs : Measurable fun ω => X (Real.toNNReal (stopTime t (τ ω))) ω :=
      (measurable_X_joint hF).comp (hσm.prodMk measurable_id)
    have h2 : Measurable fun ω => ((stopTime t (τ ω), X (Real.toNNReal (stopTime t (τ ω))) ω) :
        ℝ × Config d N) := hσm.prodMk hXs
    have := hm.comp h2
    have e : (fun ω => modulatedEnergyKernel h (X (Real.toNNReal (stopTime t (τ ω))) ω)
        (withDensityReal (ρ (stopTime t (τ ω))))) =
        (fun p : ℝ × Config d N => modulatedEnergyKernel h p.2 (withDensityReal (ρ (clampT T p.1)))) ∘
          (fun ω => ((stopTime t (τ ω), X (Real.toNNReal (stopTime t (τ ω))) ω) : ℝ × Config d N)) := by
      funext ω
      simp only [Function.comp_apply, clampT_of_mem (hσT ω)]
    rw [e]; exact this
  obtain ⟨CE, hCE⟩ := c.energy_bound hsm hev hN0
  have hE1i : Integrable (fun ω => modulatedEnergyKernel h (X (Real.toNNReal (stopTime t (τ ω))) ω)
      (withDensityReal (ρ (stopTime t (τ ω))))) P :=
    Integrable.of_bound hE1m.aestronglyMeasurable CE (ae_of_all _ fun ω => by
      simpa [Real.norm_eq_abs] using hCE _ (hσT ω) _)
  have hE0i : Integrable (fun ω => modulatedEnergyKernel h (X 0 ω) (withDensityReal (ρ 0))) P := by
    have := c.integrable_energy hN hsol hsm hev (r := 0) ⟨le_rfl, c.hT⟩
    simpa using this
  -- the drift integrand on the product
  have hr : ∀ᵐ p ∂μ, p.1 ∈ Set.Icc (0 : ℝ) t :=
    (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Set.Icc (0 : ℝ) t)) (ν := P)).ae
      (ae_restrict_mem measurableSet_Icc)
  have hGm : Measurable fun p : ℝ × Ω =>
      if ((p.1 : ℝ) : WithTop ℝ) < τ p.2 then Jc D h ρ T X p.1 p.2 else 0 :=
    Measurable.ite (lt5_measurableSet_lt hτs) (c.measurable_Jc hF hsm hev) measurable_const
  have hGG : (fun p : ℝ × Ω => if ((p.1 : ℝ) : WithTop ℝ) < τ p.2 then Jfull D h ρ X p.1 p.2 else 0) =ᵐ[μ]
      fun p : ℝ × Ω => if ((p.1 : ℝ) : WithTop ℝ) < τ p.2 then Jc D h ρ T X p.1 p.2 else 0 := by
    filter_upwards [hr] with p hp
    rw [Jc_eq ⟨hp.1, hp.2.trans htT⟩]
  have hGae : AEStronglyMeasurable
      (fun p : ℝ × Ω => if ((p.1 : ℝ) : WithTop ℝ) < τ p.2 then Jfull D h ρ X p.1 p.2 else 0) μ :=
    hGm.aestronglyMeasurable.congr hGG.symm
  have hbd := lt5_G_bound (ρ := ρ) (D := D) (X := X) (h := h) hJb
  have hGint : Integrable
      (fun p : ℝ × Ω => if ((p.1 : ℝ) : WithTop ℝ) < τ p.2 then Jfull D h ρ X p.1 p.2 else 0) μ :=
    Integrable.of_bound hGae (max B 0) hbd
  refine ⟨hE1i, hGint, ?_⟩
  -- the martingale terms
  have hW := hF.brownian
  have hM1 := martingale_stoppedProcess_itoIntegral hW hΨ1 hτs
  have hM2 := martingale_stoppedProcess_itoIntegral hW hΨ2 hτs
  have hI1 := hM1.integrable t
  have hI2 := hM2.integrable t
  have hz1 := integral_stoppedProcess_itoIntegral hW hΨ1 hτs t
  have hz2 := integral_stoppedProcess_itoIntegral hW hΨ2 hτs t
  have hA : Integrable (fun ω => ∫ r in Set.Icc (0 : ℝ) t,
      (if ((r : ℝ) : WithTop ℝ) < τ ω then Jfull D h ρ X r ω else 0)) P := hGint.integral_prod_right
  -- pathwise
  have hpw : ∀ᵐ ω ∂P, modulatedEnergyKernel h (X (Real.toNNReal (stopTime t (τ ω))) ω)
        (withDensityReal (ρ (stopTime t (τ ω)))) - modulatedEnergyKernel h (X 0 ω) (withDensityReal (ρ 0)) =
      (∫ r in Set.Icc (0 : ℝ) t, (if ((r : ℝ) : WithTop ℝ) < τ ω then Jfull D h ρ X r ω else 0)) +
        stoppedProcess (itoIntegral P ℱ W' (fun s ω k => fkeRef D t (Φpp h) X s ω k)) τ t ω -
        stoppedProcess (itoIntegral P ℱ W' (empiricalNoiseIntegrand D t (fK h ρ) X)) τ t ω := by
    filter_upwards [hpath] with ω hω
    have h1 := hω (stopTime t (τ ω)) ⟨hσ0 ω, hσt ω⟩
    rw [h1, lt5_integral_stop (fun r => Jfull D h ρ X r ω) ht0.le (τ ω),
      lt5_stoppedProcess_eq, lt5_stoppedProcess_eq]
  have e1 : ∫ ω, modulatedEnergyKernel h (X (Real.toNNReal (stopTime t (τ ω))) ω)
        (withDensityReal (ρ (stopTime t (τ ω)))) ∂P -
      ∫ ω, modulatedEnergyKernel h (X 0 ω) (withDensityReal (ρ 0)) ∂P =
      ∫ ω, ((∫ r in Set.Icc (0 : ℝ) t, (if ((r : ℝ) : WithTop ℝ) < τ ω then Jfull D h ρ X r ω else 0)) +
        stoppedProcess (itoIntegral P ℱ W' (fun s ω k => fkeRef D t (Φpp h) X s ω k)) τ t ω -
        stoppedProcess (itoIntegral P ℱ W' (empiricalNoiseIntegrand D t (fK h ρ) X)) τ t ω) ∂P := by
    rw [← integral_sub hE1i hE0i]
    exact integral_congr_ae hpw
  have e2 := integral_sub (hA.add hI1) hI2
  have e3 := integral_add hA hI1
  simp only [Pi.add_apply] at e2 e3
  rw [e1, e2, e3, hz1, hz2, add_zero, sub_zero]
  exact (integral_integral_swap (μ := volume.restrict (Set.Icc (0 : ℝ) t)) (ν := P)
    (f := fun r ω => if ((r : ℝ) : WithTop ℝ) < τ ω then Jfull D h ρ X r ω else 0) hGint).symm

end Fixed

end HRS.MD.LT337P5
