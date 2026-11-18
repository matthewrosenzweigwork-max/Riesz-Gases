import HRS.MS.MovAdjAux5
import HRS.MS.S21F_C01
import HRS.Whole.AppendixAAdjoint
import HRS.Whole.Round2

/-!
# S2.1(iii), packet 3: small-form source bounds

This packet uses the real R26-T3 parameter and trajectory records from
`S21F_D00`.  It proves class-uniform relaxation, velocity and local drift
bounds.  The full generator small-form estimate additionally requires a
nonlocal differentiated-force convolution bound.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovAdj

namespace HRS.Fp81.S21

/-- The relaxed relative-density field has a class-uniform `L²(dx)` bound. -/
theorem sol13_class_relaxation_bounds (p : HRS.MS.R26T3.Parameters) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      ∀ R : HRS.MS.R26T3.Trajectory p δ, ∀ t : ℝ, 0 ≤ t →
        let v : Euc p.d → ℝ := fun x => (R.ρ t x - R.ρβ x) / Real.sqrt (R.ρβ x)
        MemOsc (102 * (p.d : ℝ) + 1020) v ∧
        MemLp v 2 (volume : Measure (Euc p.d)) ∧
        (eLpNorm v 2 (volume : Measure (Euc p.d))).toReal ≤
          C₂ * δ * Real.exp (-p.c₁ * t) := by
  let m : ℝ := 102 * (p.d : ℝ) + 1020
  have hdcast : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
  have hm : (p.d : ℝ) / 2 < m := by
    dsimp [m]
    nlinarith
  refine ⟨|p.C₁|, abs_nonneg _, fun δ hδ hδh R t ht => ?_⟩
  dsimp [m]
  let v : Euc p.d → ℝ := fun x => (R.ρ t x - R.ρβ x) / Real.sqrt (R.ρβ x)
  have hrelax := R.resulting.weighted t ht
  have hamp0 : 0 ≤ δ * Real.exp (-p.c₁ * t) :=
    mul_nonneg hδ.le (Real.exp_pos _).le
  have hnorm : oscNorm (102 * (p.d : ℝ) + 1020) v ≤
      |p.C₁| * (δ * Real.exp (-p.c₁ * t)) := by
    calc
      oscNorm (102 * (p.d : ℝ) + 1020) v ≤
          p.C₁ * δ * Real.exp (-p.c₁ * t) := by simpa [v] using hrelax.2
      _ = p.C₁ * (δ * Real.exp (-p.c₁ * t)) := by ring
      _ ≤ |p.C₁| * (δ * Real.exp (-p.c₁ * t)) :=
        mul_le_mul_of_nonneg_right (le_abs_self p.C₁) hamp0
  have hv2 : MemLp v 2 (volume : Measure (Euc p.d)) := by simpa [v] using hrelax.1.1
  have heq : (eLpNorm v 2 (volume : Measure (Euc p.d))).toReal = oscNorm 0 v := by
    rw [HRS.MS.MovOsc.mova2_eLpNorm_two hv2]
    exact ENNReal.toReal_ofReal (Real.sqrt_nonneg _)
  have hmono : oscNorm 0 v ≤ oscNorm (102 * (p.d : ℝ) + 1020) v :=
    (HRS.MS.MovOsc.mo_mono (by positivity) hrelax.1).2
  refine ⟨hrelax.1, hv2, ?_⟩
  · calc
      (eLpNorm v 2 (volume : Measure (Euc p.d))).toReal = oscNorm 0 v := heq
      _ ≤ oscNorm (102 * (p.d : ℝ) + 1020) v := hmono
      _ ≤ |p.C₁| * (δ * Real.exp (-p.c₁ * t)) := hnorm
      _ = |p.C₁| * δ * Real.exp (-p.c₁ * t) := by ring

/-- The weighted relaxation also gives a class-uniform pointwise bound on the
relative-density field.  The constant is the generic oscillator Sobolev
embedding constant and depends only on the fixed dimension and class data. -/
theorem sol13_class_relaxation_linf (p : HRS.MS.R26T3.Parameters) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      ∀ R : HRS.MS.R26T3.Trajectory p δ, ∀ t : ℝ, 0 ≤ t →
        let v : Euc p.d → ℝ := fun x => (R.ρ t x - R.ρβ x) / Real.sqrt (R.ρβ x)
        ∀ x, ‖v x‖ ≤ C * δ * Real.exp (-p.c₁ * t) := by
  let m : ℕ := 102 * p.d + 1020
  have hm : (p.d : ℝ) / 2 < (m : ℝ) := by
    dsimp [m]
    push_cast
    have hdcast : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    nlinarith
  have hm' : ((0 : ℕ) : ℝ) + (p.d : ℝ) / 2 < (m : ℝ) := by simpa using hm
  obtain ⟨Cs, hCs, hSob⟩ := HRS.MS.Mov63.mn_sobolev_emb_gen
    (d := p.d) 0 m hm'
  refine ⟨Cs * |p.C₁|, mul_nonneg hCs (abs_nonneg _),
    fun δ hδ hδh R t ht => ?_⟩
  dsimp
  let v : Euc p.d → ℝ := fun x =>
    (R.ρ t x - R.ρβ x) / Real.sqrt (R.ρβ x)
  have hsd : p.s < (p.d : ℝ) := by
    have hdpos : 0 < (p.d : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ)) p.hd)
    linarith [p.hs]
  let H : HRS.MS.MovLin.Mov2dTh p.d p.s p.β p.a R.ρβ :=
    ⟨p.hd, p.hs0, hsd, p.hβ, p.ha, R.thermal⟩
  obtain ⟨B, -, hGap, -⟩ :=
    HRS.MS.Mov0.mv0_gapref (s := p.s) (q := p.a) (β := p.β)
      p.hd p.hs0 hsd p.ha p.hβ R.thermal
  have hroot := HRS.MS.Mov0.mov0_sqrt_smooth hGap
  have hvcont : Continuous v := by
    dsimp [v]
    exact ((R.resulting.regular t ht).sub hGap.smooth.continuous).div hroot.continuous
      (fun y => (Real.sqrt_pos.2 (hGap.pos y)).ne')
  have hvMem : MemOsc (m : ℝ) v := by
    simpa [m, v] using (R.resulting.weighted t ht).1
  obtain ⟨g, hg, hva, hgb⟩ := hSob v hvMem
  have hveq : v = g := HRS.MS.Mov63.mn_ae_eq_cont hvcont hg.continuous hva
  have hamp0 : 0 ≤ δ * Real.exp (-p.c₁ * t) :=
    mul_nonneg hδ.le (Real.exp_pos _).le
  have hosc : oscNorm (m : ℝ) v ≤ |p.C₁| * δ * Real.exp (-p.c₁ * t) := by
    calc
      oscNorm (m : ℝ) v ≤ p.C₁ * δ * Real.exp (-p.c₁ * t) := by
        simpa [m, v] using (R.resulting.weighted t ht).2
      _ = p.C₁ * (δ * Real.exp (-p.c₁ * t)) := by ring
      _ ≤ |p.C₁| * (δ * Real.exp (-p.c₁ * t)) :=
        mul_le_mul_of_nonneg_right (le_abs_self p.C₁) hamp0
      _ = |p.C₁| * δ * Real.exp (-p.c₁ * t) := by ring
  intro x
  calc
    ‖v x‖ = ‖iteratedFDeriv ℝ 0 g x‖ := by rw [hveq]; simp
    _ ≤ Cs * oscNorm (m : ℝ) v := hgb 0 (by norm_num) x
    _ ≤ Cs * (|p.C₁| * δ * Real.exp (-p.c₁ * t)) :=
      mul_le_mul_of_nonneg_left hosc hCs
    _ = (Cs * |p.C₁|) * δ * Real.exp (-p.c₁ * t) := by ring

/-- Each of the two vector fields explicitly bounded in `IsResultingSolution.velocity`
has the same class-uniform pointwise bound. -/
theorem sol13_class_velocity_components (p : HRS.MS.R26T3.Parameters) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      ∀ R : HRS.MS.R26T3.Trajectory p δ, ∀ t : ℝ, 0 ≤ t →
        let Glog : Euc p.d → Euc p.d := fun x =>
          gradient (fun y => Real.log (R.ρ t y / R.ρβ y)) x
        let V : Euc p.d → Euc p.d := fun x =>
          p.β⁻¹ • gradient (fun y => Real.log (R.ρ t y)) x + p.a • x +
            convGradConvW (rieszKernelGrad p.d p.s) (R.ρ t) x
        ∀ x, ‖Glog x‖ ≤ C * δ * Real.exp (-p.c₁ * t) ∧
          ‖V x‖ ≤ C * δ * Real.exp (-p.c₁ * t) := by
  refine ⟨|p.C₁|, abs_nonneg _, fun δ hδ hδh R t ht => ?_⟩
  dsimp
  let Glog : Euc p.d → Euc p.d := fun x =>
    gradient (fun y => Real.log (R.ρ t y / R.ρβ y)) x
  let V : Euc p.d → Euc p.d := fun x =>
    p.β⁻¹ • gradient (fun y => Real.log (R.ρ t y)) x + p.a • x +
      convGradConvW (rieszKernelGrad p.d p.s) (R.ρ t) x
  have hfields := R.resulting.velocity t ht
  have hG : cbNormVecE (100 * p.d + 1000) Glog ≤
      ENNReal.ofReal (p.C₁ * δ * Real.exp (-p.c₁ * t)) :=
    le_trans le_self_add hfields
  have hV : cbNormVecE (100 * p.d + 1000) V ≤
      ENNReal.ofReal (p.C₁ * δ * Real.exp (-p.c₁ * t)) := by
    rw [add_comm] at hfields
    exact le_trans le_self_add hfields
  have hamp0 : 0 ≤ δ * Real.exp (-p.c₁ * t) :=
    mul_nonneg hδ.le (Real.exp_pos _).le
  have hmax : max (p.C₁ * δ * Real.exp (-p.c₁ * t)) 0 ≤
      |p.C₁| * δ * Real.exp (-p.c₁ * t) := by
    have hfirst : p.C₁ * δ * Real.exp (-p.c₁ * t) ≤
        |p.C₁| * δ * Real.exp (-p.c₁ * t) := by
      calc
        p.C₁ * δ * Real.exp (-p.c₁ * t) = p.C₁ * (δ * Real.exp (-p.c₁ * t)) := by ring
        _ ≤ |p.C₁| * (δ * Real.exp (-p.c₁ * t)) :=
          mul_le_mul_of_nonneg_right (le_abs_self p.C₁) hamp0
        _ = |p.C₁| * δ * Real.exp (-p.c₁ * t) := by ring
    exact max_le hfirst (mul_nonneg (mul_nonneg (abs_nonneg _) hδ.le)
      (Real.exp_pos _).le)
  intro x
  refine ⟨?_, ?_⟩
  · calc
      ‖Glog x‖ ≤ max (p.C₁ * δ * Real.exp (-p.c₁ * t)) 0 := by
        have h := HRS.MS.MovAdj.s67_cbVec_bound hG (Nat.zero_le _) x
        rw [norm_iteratedFDeriv_zero] at h
        exact h
      _ ≤ |p.C₁| * δ * Real.exp (-p.c₁ * t) := hmax
  · calc
      ‖V x‖ ≤ max (p.C₁ * δ * Real.exp (-p.c₁ * t)) 0 := by
        have h := HRS.MS.MovAdj.s67_cbVec_bound hV (Nat.zero_le _) x
        rw [norm_iteratedFDeriv_zero] at h
        exact h
      _ ≤ |p.C₁| * δ * Real.exp (-p.c₁ * t) := hmax

/-- The interaction part of the local drift difference is class-uniformly small.
The identity uses the thermal Euler equation and the two separate velocity-field
bounds stored in `IsResultingSolution`. -/
theorem sol13_local_force_difference_bound (p : HRS.MS.R26T3.Parameters) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      ∀ R : HRS.MS.R26T3.Trajectory p δ, ∀ t : ℝ, 0 ≤ t → ∀ x : Euc p.d,
        ‖convGradConvW (rieszKernelGrad p.d p.s) (R.ρ t) x -
          convGradConvW (rieszKernelGrad p.d p.s) R.ρβ x‖ ≤
            C * δ * Real.exp (-p.c₁ * t) := by
  obtain ⟨C, hC, hvel⟩ := sol13_class_velocity_components p
  refine ⟨C * (1 + p.β⁻¹),
    mul_nonneg hC (add_nonneg (by norm_num) (inv_pos.mpr p.hβ).le),
    fun δ hδ hδh R t ht x => ?_⟩
  have hsd : p.s < (p.d : ℝ) := by
    have hdpos : 0 < (p.d : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ)) p.hd)
    linarith [p.hs]
  let H : HRS.MS.MovLin.Mov2dTh p.d p.s p.β p.a R.ρβ :=
    ⟨p.hd, p.hs0, hsd, p.hβ, p.ha, R.thermal⟩
  obtain ⟨B, -, hGap, -⟩ :=
    HRS.MS.Mov0.mv0_gapref (s := p.s) (q := p.a) (β := p.β)
      p.hd p.hs0 hsd p.ha p.hβ R.thermal
  have hroot := HRS.MS.Mov0.mov0_sqrt_smooth hGap
  let v : Euc p.d → ℝ := fun y => (R.ρ t y - R.ρβ y) / Real.sqrt (R.ρβ y)
  have hvcont : Continuous v := by
    dsimp [v]
    exact ((R.resulting.regular t ht).sub hGap.smooth.continuous).div hroot.continuous
      (fun y => (Real.sqrt_pos.2 (hGap.pos y)).ne')
  have hvMem : MemOsc (102 * (p.d : ℝ) + 1020) v := by
    simpa [v] using (R.resulting.weighted t ht).1
  let m : ℕ := 102 * p.d + 1020
  have hm : (p.d : ℝ) / 2 + (0 : ℝ) + 2 < (m : ℝ) := by
    dsimp [m]
    push_cast
    have hdcast : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    nlinarith
  obtain ⟨Cforce, -, hforce⟩ := HRS.MS.Mov63.mn_force_bound
    (s := p.s) p.hd p.hs0 hsd p.β p.a p.hβ p.ha R.ρβ R.thermal 0 m (by simpa using hm)
  have hvreg := hforce v hvcont (by simpa [m] using hvMem)
  have hvCD : ContDiff ℝ 2 v := by simpa using hvreg.1
  have hρeq : R.ρ t = fun y => R.ρβ y + Real.sqrt (R.ρβ y) * v y := by
    funext y
    have hsne : Real.sqrt (R.ρβ y) ≠ 0 := (Real.sqrt_pos.2 (hGap.pos y)).ne'
    dsimp [v]
    field_simp [hsne]
    ring
  have hρtCD : ContDiff ℝ 2 (R.ρ t) := by
    rw [hρeq]
    exact (hGap.smooth.of_le (by norm_num)).add
      ((hroot.of_le (by norm_num)).mul hvCD)
  have hC1nonneg : 0 ≤ p.C₁ := by
    have hrelax0 := R.resulting.weighted 0 (by norm_num)
    have hosc : 0 ≤ oscNorm (102 * (p.d : ℝ) + 1020)
        (fun y => (R.ρ 0 y - R.ρβ y) / Real.sqrt (R.ρβ y)) := Real.sqrt_nonneg _
    have hamp : 0 < δ * Real.exp (-p.c₁ * (0 : ℝ)) := mul_pos hδ (Real.exp_pos _)
    have hprod : 0 ≤ p.C₁ * δ * Real.exp (-p.c₁ * (0 : ℝ)) := le_trans hosc hrelax0.2
    nlinarith
  have hC1pos : 0 < p.C₁ := by
    by_contra hnot
    have hle : p.C₁ ≤ 0 := le_of_not_gt hnot
    have hzeroC : p.C₁ = 0 := le_antisymm hle hC1nonneg
    have hsol0 := R.resulting.global 0
    have hprob0 : HRS.Whole.IsProbDensity (R.ρ 0) := hsol0.density 0 (by simp)
    have hzero : R.ρ 0 = fun _ => 0 := by
      funext y
      have hupper := (R.resulting.ratio 0 (by norm_num) y).2
      rw [hzeroC] at hupper
      have hupper' : R.ρ 0 y ≤ 0 := by simpa using hupper
      exact le_antisymm hupper' (hprob0.nonneg y)
    have hone := hprob0.integral_one
    rw [hzero] at hone
    simp at hone
  have hρtpos : ∀ y, 0 < R.ρ t y := fun y => by
    have hratio := (R.resulting.ratio t ht y).1
    exact lt_of_lt_of_le (mul_pos (inv_pos.mpr hC1pos) (hGap.pos y)) hratio
  have hlogtCD : ContDiff ℝ 1 (fun y => Real.log (R.ρ t y)) :=
    (hρtCD.log fun y => (hρtpos y).ne').of_le (by norm_num)
  have hlogsCD : ContDiff ℝ 1 (fun y => Real.log (R.ρβ y)) :=
    (hGap.smooth.log fun y => (hGap.pos y).ne').of_le (by norm_num)
  let Glog : Euc p.d → Euc p.d := fun y =>
    gradient (fun z => Real.log (R.ρ t z / R.ρβ z)) y
  let V : Euc p.d → Euc p.d := fun y =>
    p.β⁻¹ • gradient (fun z => Real.log (R.ρ t z)) y + p.a • y +
      convGradConvW (rieszKernelGrad p.d p.s) (R.ρ t) y
  have hlogfun : (fun y => Real.log (R.ρ t y / R.ρβ y)) =
      fun y => Real.log (R.ρ t y) - Real.log (R.ρβ y) := by
    funext y
    exact Real.log_div (hρtpos y).ne' (hGap.pos y).ne'
  have hgrad : Glog x =
      gradient (fun y => Real.log (R.ρ t y)) x -
        gradient (fun y => Real.log (R.ρβ y)) x := by
    have hdt : DifferentiableAt ℝ (fun y => Real.log (R.ρ t y)) x :=
      (hlogtCD.differentiable (by norm_num)) x
    have hds : DifferentiableAt ℝ (fun y => Real.log (R.ρβ y)) x :=
      (hlogsCD.differentiable (by norm_num)) x
    ext i
    rw [PiLp.sub_apply, HRS.Whole.AppendixA.q09_gradient_apply,
      HRS.Whole.AppendixA.q09_gradient_apply,
      HRS.Whole.AppendixA.q09_gradient_apply]
    rw [hlogfun, fderiv_fun_sub hdt hds]
    simp only [ContinuousLinearMap.sub_apply]
  have hEuler := HRS.MS.Mov0.mv0_thermal_force (s := p.s) (q := p.a) (β := p.β)
    p.hd p.hs0 hsd p.ha p.hβ R.thermal x
  have hEuler' : p.β⁻¹ • gradient (fun y => Real.log (R.ρβ y)) x + p.a • x =
      -convGradConvW (rieszKernelGrad p.d p.s) R.ρβ x := by
    calc
      p.β⁻¹ • gradient (fun y => Real.log (R.ρβ y)) x + p.a • x =
          (p.β⁻¹ • gradient (fun y => Real.log (R.ρβ y)) x + p.a • x +
            convGradConvW (rieszKernelGrad p.d p.s) R.ρβ x) -
              convGradConvW (rieszKernelGrad p.d p.s) R.ρβ x := by abel
      _ = 0 - convGradConvW (rieszKernelGrad p.d p.s) R.ρβ x := by rw [hEuler]
      _ = _ := by simp
  have hforceId :
      convGradConvW (rieszKernelGrad p.d p.s) (R.ρ t) x -
        convGradConvW (rieszKernelGrad p.d p.s) R.ρβ x =
      V x - p.β⁻¹ • Glog x := by
    change _ = (p.β⁻¹ • gradient (fun y => Real.log (R.ρ t y)) x +
      p.a • x + convGradConvW (rieszKernelGrad p.d p.s) (R.ρ t) x) -
        p.β⁻¹ • Glog x
    rw [hgrad, smul_sub]
    symm
    calc
      p.β⁻¹ • gradient (fun y => Real.log (R.ρ t y)) x + p.a • x +
          convGradConvW (rieszKernelGrad p.d p.s) (R.ρ t) x -
            (p.β⁻¹ • gradient (fun y => Real.log (R.ρ t y)) x -
              p.β⁻¹ • gradient (fun y => Real.log (R.ρβ y)) x) =
        convGradConvW (rieszKernelGrad p.d p.s) (R.ρ t) x +
          (p.β⁻¹ • gradient (fun y => Real.log (R.ρβ y)) x + p.a • x) := by abel
      _ = convGradConvW (rieszKernelGrad p.d p.s) (R.ρ t) x -
          convGradConvW (rieszKernelGrad p.d p.s) R.ρβ x := by rw [hEuler']; abel
  have hfields := hvel δ hδ hδh R t ht
  have hVbound : ‖V x‖ ≤ C * δ * Real.exp (-p.c₁ * t) := by
    simpa [V] using (hfields x).2
  have hGbound : ‖Glog x‖ ≤ C * δ * Real.exp (-p.c₁ * t) := by
    simpa [Glog] using (hfields x).1
  have hInv : 0 ≤ p.β⁻¹ := (inv_pos.mpr p.hβ).le
  calc
    ‖convGradConvW (rieszKernelGrad p.d p.s) (R.ρ t) x -
        convGradConvW (rieszKernelGrad p.d p.s) R.ρβ x‖ =
      ‖V x - p.β⁻¹ • Glog x‖ := by rw [hforceId]
    _ ≤ ‖V x‖ + ‖p.β⁻¹ • Glog x‖ := norm_sub_le _ _
    _ = ‖V x‖ + p.β⁻¹ * ‖Glog x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr p.hβ)]
    _ ≤ C * δ * Real.exp (-p.c₁ * t) +
        p.β⁻¹ * (C * δ * Real.exp (-p.c₁ * t)) :=
      add_le_add hVbound (mul_le_mul_of_nonneg_left hGbound hInv)
    _ = C * (1 + p.β⁻¹) * δ * Real.exp (-p.c₁ * t) := by ring
end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.sol13_class_relaxation_bounds
#print axioms HRS.Fp81.S21.sol13_class_relaxation_linf
#print axioms HRS.Fp81.S21.sol13_class_velocity_components
#print axioms HRS.Fp81.S21.sol13_local_force_difference_bound
