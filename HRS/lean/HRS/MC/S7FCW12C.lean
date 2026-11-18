import HRS.MC.S7FCW12B

/-!
# FC-E packet, part C: joint measurability of the particle energies (prefix `s7fcw12_`)

* `s7fcw12_meas_density_integral`: `a ↦ ∫ g a y dμ_a` is measurable for a jointly measurable density `ρt`.
* `s7fcw12_meas_modEnergy`: `(a, x) ↦ modulatedEnergy h x (withDensityReal (ρt a))` is measurable.
* `s7fcw12_rhoPos`: the regime density, extended by `0` to negative times, is jointly measurable.
* `s7fcw12_fcPartTilde_measurable`, `s7fcw12_toL2_congr`: finite-rank field and `toL2` helpers.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Sec7.S7FCW12

open HRS HRS.Sec7 HRS.MC.Sec7.FCPlan

variable {d : ℕ}

instance s7fcw12_borel_torus {d : ℕ} : BorelSpace (Torus d) := Pi.borelSpace

theorem s7fcw12_continuous_of_smooth {f : Torus d → ℝ} (hf : Torus.IsSmooth f) : Continuous f :=
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) := hf
  Torus.continuous_of_continuous_lift hF.continuous

/-- Measurability of a density integral in the parameter `a`, for a jointly measurable density. -/
theorem s7fcw12_meas_density_integral {α : Type*} [MeasurableSpace α] (ρt : α → Torus d → ℝ)
    (hρ : Measurable fun q : α × Torus d => ρt q.1 q.2) (g : α → Torus d → ℝ)
    (hg : Measurable fun q : α × Torus d => g q.1 q.2) :
    Measurable fun a => ∫ y, g a y ∂(withDensityReal (ρt a)) := by
  have hden : (fun a => ∫ y, g a y ∂(withDensityReal (ρt a))) =
      fun a => ∫ y, (ENNReal.ofReal (ρt a y)).toReal • g a y := by
    funext a
    unfold withDensityReal
    refine integral_withDensity_eq_integral_toReal_smul ?_
      (Eventually.of_forall fun y => ENNReal.ofReal_lt_top) (fun y => g a y)
    exact ENNReal.measurable_ofReal.comp (hρ.comp (measurable_const.prodMk measurable_id))
  rw [hden]
  have hF : Measurable fun q : α × Torus d => (ENNReal.ofReal (ρt q.1 q.2)).toReal • g q.1 q.2 :=
    (ENNReal.measurable_toReal.comp (ENNReal.measurable_ofReal.comp hρ)).smul hg
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

/-- The modulated energy `F_N(h; x, μ_a)` is jointly measurable in the parameter `a` and the configuration `x`. -/
theorem s7fcw12_meas_modEnergy {α : Type*} [MeasurableSpace α] {N : ℕ} (h : Torus d → Torus d → ℝ)
    (hh : Measurable fun q : Torus d × Torus d => h q.1 q.2) (ρt : α → Torus d → ℝ)
    (hρ : Measurable fun q : α × Torus d => ρt q.1 q.2) :
    Measurable fun p : α × Config d N => modulatedEnergy h p.2 (withDensityReal (ρt p.1)) := by
  unfold modulatedEnergy
  have hA : Measurable fun p : α × Config d N =>
      ∑ i, ∑ j ∈ Finset.univ.erase i, h (p.2 i) (p.2 j) := by
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    exact hh.comp (f := fun p : α × Config d N => (p.2 i, p.2 j)) (by fun_prop)
  have hB : Measurable fun p : α × Config d N => ∑ i, ∫ y, h (p.2 i) y ∂(withDensityReal (ρt p.1)) := by
    refine Finset.measurable_sum _ fun i _ => ?_
    refine s7fcw12_meas_density_integral (fun p : α × Config d N => ρt p.1)
      (hρ.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)) (fun p y => h (p.2 i) y) ?_
    exact hh.comp (f := fun q : (α × Config d N) × Torus d => (q.1.2 i, q.2)) (by fun_prop)
  have hG : Measurable fun r : (α × Config d N) × Torus d => ∫ y, h r.2 y ∂(withDensityReal (ρt r.1.1)) :=
    s7fcw12_meas_density_integral (fun r : (α × Config d N) × Torus d => ρt r.1.1)
      (hρ.comp ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd))
      (fun r y => h r.2 y)
      (hh.comp (f := fun q : ((α × Config d N) × Torus d) × Torus d => (q.1.2, q.2)) (by fun_prop))
  have hC : Measurable fun p : α × Config d N =>
      ∫ x', (∫ y, h x' y ∂(withDensityReal (ρt p.1))) ∂(withDensityReal (ρt p.1)) :=
    s7fcw12_meas_density_integral (fun p : α × Config d N => ρt p.1)
      (hρ.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
      (fun p x' => ∫ y, h x' y ∂(withDensityReal (ρt p.1))) hG
  exact ((hA.const_mul _).sub (hB.const_mul _)).add (hC.const_mul _)

/-- The regime density, set to `0` at negative times (so that it is jointly measurable on `ℝ × 𝕋^d`). -/
def s7fcw12_rhoPos (R : Regime d) : ℝ × Torus d → ℝ :=
  (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set (Torus d))).piecewise (fun p => R.ρ p.1 p.2) (fun _ => 0)

theorem s7fcw12_rhoPos_eq (R : Regime d) {t : ℝ} (ht : 0 ≤ t) (x : Torus d) :
    s7fcw12_rhoPos R (t, x) = R.ρ t x := by
  simp [s7fcw12_rhoPos, Set.piecewise, ht]

theorem s7fcw12_rho_continuousOn (R : Regime d) :
    ContinuousOn (fun p : ℝ × Torus d => R.ρ p.1 p.2) (Set.Ici 0 ×ˢ Set.univ) := by
  obtain ⟨K, hK⟩ := exists_nat_gt ((d : ℝ) / 2 + 6)
  obtain ⟨ρc, H, hρ⟩ := R.sol K hK
  have hc := HRS.PDE.MFApriori.continuousOn_toFun_prod' (d := d) (K : ℝ) (by linarith) ρc (Set.Ici 0) H.cont
  refine hc.congr ?_
  rintro ⟨t, x⟩ ⟨ht, -⟩
  have ht' : (0 : ℝ) ≤ t := ht
  show R.ρ t x = HRS.PDE.toFun (ρc t) x
  rw [hρ t ht']
  rfl

theorem s7fcw12_rhoPos_measurable (R : Regime d) : Measurable (s7fcw12_rhoPos R) := by
  classical
  refine ContinuousOn.measurable_piecewise (s7fcw12_rho_continuousOn R) continuousOn_const ?_
  exact measurableSet_Ici.prod MeasurableSet.univ

/-- The finite-rank particle field is jointly measurable in the time-parameter and the configuration. -/
theorem s7fcw12_fcPartTilde_measurable (R : Regime d) (r : ℝ) (S : Finset (NonzeroLattice d))
    (K : NonzeroLattice d → FRKernel d) {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (τ : Ω → ℝ)
    (hτ : Measurable τ) (v : Ω → Config d N) (hv : Measurable v) :
    Measurable fun ω => fcPartTilde r S K (withDensityReal fun y => s7fcw12_rhoPos R (τ ω, y)) (v ω) := by
  have hρ : Measurable fun q : ℝ × Torus d => s7fcw12_rhoPos R (q.1, q.2) :=
    (s7fcw12_rhoPos_measurable R).comp measurable_id
  have hmodE : ∀ k : NonzeroLattice d, Measurable fun p : ℝ × Config d N =>
      modulatedEnergy (K k).toFun p.2 (withDensityReal fun y => s7fcw12_rhoPos R (p.1, y)) := by
    intro k
    have hh : Measurable fun q : Torus d × Torus d => (K k).toFun q.1 q.2 := by
      have hf : ∀ i, Continuous ((K k).f i) := fun i => s7fcw12_continuous_of_smooth ((K k).smooth i)
      refine Continuous.measurable ?_
      unfold FRKernel.toFun
      fun_prop
    exact s7fcw12_meas_modEnergy (K k).toFun hh (fun t y => s7fcw12_rhoPos R (t, y)) hρ
  unfold fcPartTilde
  refine s7fcw12_measurable_ofSeq
    (fun ω k => if k ∈ S then (N : ℝ) * modulatedEnergy (K k).toFun (v ω)
      (withDensityReal fun y => s7fcw12_rhoPos R (τ ω, y)) else 0) ?_
  intro k
  by_cases hk : k ∈ S
  · simp only [if_pos hk]
    exact measurable_const.mul ((hmodE k).comp (f := fun ω => (τ ω, v ω)) (hτ.prodMk hv))
  · simp only [if_neg hk]
    exact measurable_const

/-- `toL2` only sees the values on `[0, T]`. -/
theorem s7fcw12_toL2_congr (r T : ℝ) (Y Z : ℝ → NegSobolev d r)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, Y t = Z t) :
    HRS.Sec7.toL2 r T Y = HRS.Sec7.toL2 r T Z := by
  have hae : Y =ᵐ[volume.restrict (Set.Icc 0 T)] Z := by
    rw [EventuallyEq, ae_restrict_iff' measurableSet_Icc]
    exact Eventually.of_forall fun t ht => h t ht
  unfold HRS.Sec7.toL2
  by_cases hY : MemLp Y 2 (volume.restrict (Set.Icc 0 T))
  · have hZ := (memLp_congr_ae hae).1 hY
    rw [dif_pos hY, dif_pos hZ]
    exact MemLp.toLp_congr hY hZ hae
  · have hZ : ¬ MemLp Z 2 (volume.restrict (Set.Icc 0 T)) := fun hZ => hY ((memLp_congr_ae hae).2 hZ)
    rw [dif_neg hY, dif_neg hZ]

end HRS.MC.Sec7.S7FCW12
