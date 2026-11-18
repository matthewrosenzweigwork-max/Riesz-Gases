import HRS.MS.ProClosureS111InitialL3
import HRS.MS.ProClosureS111PhysicalOrbit
import HRS.MS.R2WinOrbAux13

/-!
Physical centered-terminal L³ FTC with no orbit-input hypothesis.
Accepted stationary orbit bounds give a common bounded spatial majorant;
accepted classical families give the actual terminal derivative, including
the right derivative at zero. The conclusion uses the specified L³ classes.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R2WinOrb HRS.MS.R26T6C

local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

theorem physical_centered_terminal_L3_FTC {d : ℕ} (hd : 2 ≤ d)
    (s a beta T u : ℝ) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ))
    (ha : 0 < a) (hbeta : 0 < beta) (hT : 0 < T) (hu : 0 ≤ u)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d s a beta rho)
    (alpha : MultiIndex d) :
    let mu := HRS.Whole.withDensityReal rho
    let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
    let phi := oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha
    let q := fun t => propagatorW C 0 (u + t) phi
    let q' := fun t => propagatorW C 0 (u + t) (generatorW C (u + t) phi)
    let F := fun t => r26t6c_toLp3 mu (fun x => q t x - q t 0)
    let G := fun t => r26t6c_toLp3 mu (fun x => q' t x - q' t 0)
    (∀ t ∈ Icc (0 : ℝ) T, MemLp (fun x => q t x - q t 0) 3 mu ∧
      MemLp (fun x => q' t x - q' t 0) 3 mu) ∧
    StronglyMeasurable (fun t : Icc (0 : ℝ) T => G t) ∧
    IntegrableOn G (Icc (0 : ℝ) T) ∧
    ∀ t ∈ Icc (0 : ℝ) T, F t = F 0 + ∫ v in Icc (0 : ℝ) t, G v := by
  let mu := HRS.Whole.withDensityReal rho
  let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
  let phi := oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha
  let q : ℝ → Euc d → ℝ := fun t => propagatorW C 0 (u + t) phi
  let qp : ℝ → Euc d → ℝ := fun t =>
    propagatorW C 0 (u + t) (generatorW C (u + t) phi)
  let w : ℝ → Euc d → ℝ := fun t x => q t x - q t 0
  let wp : ℝ → Euc d → ℝ := fun t x => qp t x - qp t 0
  letI : IsProbabilityMeasure mu := HRS.Whole.Q34.isProbabilityMeasure_nu hrho.2.1
  obtain ⟨B, c, hB, hc, hbound⟩ := s103_orbit_iter hd hs0 hsd ha hbeta hrho
  let A := B * s103_b d alpha
  have hA : 0 ≤ A := mul_nonneg hB (s103_b_nonneg alpha)
  have hspatial : ∀ z : ℝ, 0 ≤ z →
      Continuous (propagatorW C 0 z phi) ∧
      Continuous (propagatorW C 0 z (generatorW C z phi)) ∧
      ∀ x, |propagatorW C 0 z phi x| ≤ A ∧
        |propagatorW C 0 z (generatorW C z phi) x| ≤ A := by
    intro z hz
    obtain ⟨hex0, hex1⟩ := physical_classical_orbits hd hs0 hsd ha hbeta hrho alpha hz
    have hb0 := hbound alpha z hz 0 (by norm_num) _
      (HRS.MS.Fcau.propagatorW_isClassical hex0) 0 ⟨le_rfl, hz⟩
    have hb1 := hbound alpha z hz 1 (by norm_num) _
      (HRS.MS.Fcau.propagatorW_isClassical hex1) 0 ⟨le_rfl, hz⟩
    have hgen : generatorW C z = generatorW C 0 := by
      change generatorW ((quadraticGradientDyn d s a beta).coeff (fun _ => rho)) z =
        generatorW ((quadraticGradientDyn d s a beta).coeff (fun _ => rho)) 0
      rw [s103_coeff_eq s a beta rho]
      rfl
    refine ⟨hb0.1.continuous, hb1.1.continuous, fun x => ⟨?_, ?_⟩⟩
    · simpa only [C, phi, Function.iterate_zero, id_eq, norm_iteratedFDeriv_zero,
      Real.norm_eq_abs] using
        (s103_cb_of_E hA hb0.2 0 (Nat.zero_le _) x)
    · simpa only [C, phi, Function.iterate_one, hgen, norm_iteratedFDeriv_zero,
      Real.norm_eq_abs] using
        (s103_cb_of_E hA hb1.2 0 (Nat.zero_le _) x)
  have hcenter : ∀ (f : Euc d → ℝ), (∀ x, |f x| ≤ A) →
      ∀ x, |f x - f 0| ≤ 2 * A := by
    intro f hf x
    calc |f x - f 0| ≤ |f x| + |f 0| := by simpa using norm_sub_le (f x) (f 0)
      _ ≤ A + A := add_le_add (hf x) (hf 0)
      _ = 2 * A := by ring
  have hbd : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Euc d,
      |w t x| ≤ 2 * A ∧ |wp t x| ≤ 2 * A := by
    intro t ht x
    have hz := hspatial (u + t) (add_nonneg hu ht.1)
    exact ⟨hcenter _ (fun y => (hz.2.2 y).1) x,
      hcenter _ (fun y => (hz.2.2 y).2) x⟩
  have hL : ∀ t ∈ Icc (0 : ℝ) T, MemLp (w t) 3 mu ∧ MemLp (wp t) 3 mu := by
    intro t ht
    have hz := hspatial (u + t) (add_nonneg hu ht.1)
    constructor
    · exact MemLp.of_bound (hz.1.sub continuous_const).aestronglyMeasurable (2 * A)
        (Filter.Eventually.of_forall fun x => by simpa using (hbd t ht x).1)
    · exact MemLp.of_bound (hz.2.1.sub continuous_const).aestronglyMeasurable (2 * A)
        (Filter.Eventually.of_forall fun x => by simpa using (hbd t ht x).2)
  have hqcont : ∀ x : Euc d,
      ContinuousOn (fun t => q t x) (Icc (0 : ℝ) T) := by
    intro x
    have hz : ContinuousOn (fun z => propagatorW C 0 z phi x) (Ici (0 : ℝ)) := by
      intro z hz
      exact (physical_terminal_derivative_zero hd hs0 hsd ha hbeta hrho alpha hz x).continuousWithinAt
    exact hz.comp (continuous_const.add continuous_id).continuousOn
      (fun t ht => add_nonneg hu ht.1)
  have hqder : ∀ x t, t ∈ Ioo (0 : ℝ) T →
      HasDerivAt (fun v => q v x) (qp t x) t := by
    intro x t ht
    have hut : 0 < u + t := add_pos_of_nonneg_of_pos hu ht.1
    have hz := physical_terminal_derivative_zero hd hs0 hsd ha hbeta hrho alpha hut.le x
    have hd := hz.hasDerivAt (Ici_mem_nhds hut)
    have hd' : HasDerivAt (fun z : ℝ => propagatorW C 0 z phi x)
        (propagatorW C 0 (t + u) (generatorW C (t + u) phi) x) (t + u) := by
      simpa only [add_comm] using hd
    simpa [q, qp, add_comm] using hd'.comp_add_const t u
  exact ⟨hL, L3_FTC_of_pointwise mu w wp (fun _ => 2 * A) T hT.le
    (fun t ht => (hL t ht).1) (fun t ht => (hL t ht).2) (memLp_const _)
    (fun x => (hqcont x).sub (hqcont 0))
    (fun x t ht => (hqder x t ht).sub (hqder 0 t ht)) hbd⟩

#print axioms physical_centered_terminal_L3_FTC

end HRS.MS.ProClosureS111
