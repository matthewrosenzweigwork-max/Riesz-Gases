import HRS.MS.UlOrbitAux3
import HRS.MS.FldRemAux1

/-!
Superposition of actual classical adjoint solutions with four bounded spatial
derivatives. Addition of the nonlocal generator is supplied by an integrability
theorem; multiplication by a real scalar commutes with the cancellation integral.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole

variable {d : ℕ}

theorem memCb4_const_mul (a : ℝ) {f : Euc d → ℝ} (hf : MemCb 4 f) :
    MemCb 4 (fun x => a * f x) := by
  refine ⟨contDiff_const.mul hf.1, fun j hj => ?_⟩
  obtain ⟨B, hB⟩ := hf.2 j hj
  refine ⟨|a| * B, ?_⟩
  rintro _ ⟨x, rfl⟩
  change ‖iteratedFDeriv ℝ j (fun y => a * f y) x‖ ≤ |a| * B
  rw [HRS.MS.Ul.ul6_iter_const_mul a
    (hf.1.of_le (by exact_mod_cast hj)).contDiffAt, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hB ⟨x, rfl⟩) (abs_nonneg a)

theorem memCb4_add {f g : Euc d → ℝ} (hf : MemCb 4 f) (hg : MemCb 4 g) :
    MemCb 4 (fun x => f x + g x) := by
  refine ⟨hf.1.add hg.1, fun j hj => ?_⟩
  obtain ⟨Bf, hBf⟩ := hf.2 j hj
  obtain ⟨Bg, hBg⟩ := hg.2 j hj
  refine ⟨Bf + Bg, ?_⟩
  rintro _ ⟨x, rfl⟩
  change ‖iteratedFDeriv ℝ j (f + g) x‖ ≤ Bf + Bg
  rw [iteratedFDeriv_add_apply
    (hf.1.of_le (by exact_mod_cast hj)).contDiffAt
    (hg.1.of_le (by exact_mod_cast hj)).contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add (hBf ⟨x, rfl⟩) (hBg ⟨x, rfl⟩))

theorem convGradConvW_const_mul (G : Euc d → Euc d) (rho : Euc d → ℝ)
    (a : ℝ) (x : Euc d) :
    convGradConvW G (fun y => a * rho y) x = a • convGradConvW G rho x := by
  unfold convGradConvW
  calc
    _ = ∫ y, a • (if ‖x - y‖ ≤ 1 / 4 then
        (rho y - rho x) • G (x - y) else rho y • G (x - y)) := by
      apply integral_congr_ae
      refine ae_of_all _ fun y => ?_
      by_cases h : ‖x - y‖ ≤ 1 / 4 <;> simp [h, smul_smul, mul_sub]
    _ = _ := integral_smul a _

theorem generatorW_const_mul (C : WholeCoeff d) (r a : ℝ)
    {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (x : Euc d) :
    generatorW C r (fun y => a * f y) x = a * generatorW C r f x := by
  have hg : ∀ y, gradient (fun z => a * f z) y = a • gradient f y :=
    HRS.MS.S53.s53_gradient_const_mul a (hf.of_le (by norm_num))
  have hl : Laplacian.laplacian (fun y => a * f y) x =
      a * Laplacian.laplacian f x :=
    InnerProductSpace.laplacian_smul a hf.contDiffAt
  have hn : ∀ j : Fin d,
      (convGradConvW (rieszKernelGrad d C.s)
        (fun y => C.ρ r y * (Torus.matVec C.M.transpose
          (gradient (fun z => a * f z) y)) j) x) j =
        a * (convGradConvW (rieszKernelGrad d C.s)
          (fun y => C.ρ r y * (Torus.matVec C.M.transpose (gradient f y)) j) x) j := by
    intro j
    have heq : (fun y => C.ρ r y * (Torus.matVec C.M.transpose
        (gradient (fun z => a * f z) y)) j) =
        fun y => a * (C.ρ r y * (Torus.matVec C.M.transpose (gradient f y)) j) := by
      funext y
      rw [hg y]
      simp only [Torus.matVec, map_smul, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [heq, convGradConvW_const_mul, PiLp.smul_apply, smul_eq_mul]
  unfold generatorW
  rw [hl, hg x, real_inner_smul_right]
  simp_rw [hn]
  rw [← Finset.mul_sum]
  ring

/-- The additional spatial regularity used to justify the nonlocal superposition. -/
structure ClassicalCb4 (C : WholeCoeff d) (t : ℝ) (phi : Euc d → ℝ)
    (f : ℝ → Euc d → ℝ) : Prop where
  classical : IsClassicalAdjointW C t phi f
  cb4 : ∀ r ∈ Icc (0 : ℝ) t, MemCb 4 (f r)

theorem classicalCb4_const_mul {C : WholeCoeff d} {t : ℝ}
    {phi : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : ClassicalCb4 C t phi f) (a : ℝ) :
    ClassicalCb4 C t (fun x => a * phi x) (fun r x => a * f r x) := by
  have hgen : ∀ r ∈ Icc (0 : ℝ) t, ∀ x,
      generatorW C r (fun y => a * f r y) x = a * generatorW C r (f r) x :=
    fun r hr x => generatorW_const_mul C r a (hf.classical.c2 r hr) x
  refine ⟨?_, fun r hr => memCb4_const_mul a (hf.cb4 r hr)⟩
  refine ⟨fun r hr => contDiff_const.mul (hf.classical.c2 r hr),
    fun j hj => ?_, fun j hj => ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨B, hB⟩ := hf.classical.bdd j hj
    refine ⟨|a| * B, fun r hr x => ?_⟩
    rw [HRS.MS.Ul.ul6_iter_const_mul a
      ((hf.classical.c2 r hr).of_le (by exact_mod_cast hj)).contDiffAt,
      norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hB r hr x) (abs_nonneg a)
  · refine ((hf.classical.cont_c2 j hj).const_smul a).congr fun p => ?_
    exact (HRS.MS.Ul.ul6_iter_const_mul a
      ((hf.classical.c2 p.1 p.1.2).of_le (by exact_mod_cast hj)).contDiffAt).symm
  · funext x
    change a * f t x = a * phi x
    rw [hf.classical.terminal]
  · intro x r hr
    rw [hgen r ⟨hr.1.le, hr.2.le⟩ x]
    convert (hf.classical.time_deriv x r hr).const_mul a using 1 <;> ring
  · have hc : Continuous (fun _ : Icc (0 : ℝ) t × Euc d => a) := continuous_const
    refine (hc.mul hf.classical.cont_time_deriv).congr fun p => ?_
    exact (hgen p.1 p.1.2 p.2).symm
  · obtain ⟨B, hB⟩ := hf.classical.bdd_time_deriv
    refine ⟨|a| * B, fun r hr x => ?_⟩
    rw [hgen r hr x, abs_mul]
    calc
      _ ≤ |a| * (B * (1 + ‖x‖)) :=
        mul_le_mul_of_nonneg_left (hB r hr x) (abs_nonneg a)
      _ = _ := by ring

theorem classicalCb4_add {C : WholeCoeff d} {t : ℝ}
    {phi psi : Euc d → ℝ} {f g : ℝ → Euc d → ℝ}
    (hf : ClassicalCb4 C t phi f) (hg : ClassicalCb4 C t psi g)
    (hgen : ∀ r ∈ Icc (0 : ℝ) t, ∀ x,
      generatorW C r (fun y => f r y + g r y) x =
        generatorW C r (f r) x + generatorW C r (g r) x) :
    ClassicalCb4 C t (fun x => phi x + psi x) (fun r x => f r x + g r x) := by
  refine ⟨?_, fun r hr => memCb4_add (hf.cb4 r hr) (hg.cb4 r hr)⟩
  refine ⟨fun r hr => (hf.classical.c2 r hr).add (hg.classical.c2 r hr),
    fun j hj => ?_, fun j hj => ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨Bf, hBf⟩ := hf.classical.bdd j hj
    obtain ⟨Bg, hBg⟩ := hg.classical.bdd j hj
    refine ⟨Bf + Bg, fun r hr x => ?_⟩
    change ‖iteratedFDeriv ℝ j (f r + g r) x‖ ≤ Bf + Bg
    rw [iteratedFDeriv_add_apply
      ((hf.classical.c2 r hr).of_le (by exact_mod_cast hj)).contDiffAt
      ((hg.classical.c2 r hr).of_le (by exact_mod_cast hj)).contDiffAt]
    exact (norm_add_le _ _).trans (add_le_add (hBf r hr x) (hBg r hr x))
  · refine ((hf.classical.cont_c2 j hj).add (hg.classical.cont_c2 j hj)).congr fun p => ?_
    exact (iteratedFDeriv_add_apply
      ((hf.classical.c2 p.1 p.1.2).of_le (by exact_mod_cast hj)).contDiffAt
      ((hg.classical.c2 p.1 p.1.2).of_le (by exact_mod_cast hj)).contDiffAt).symm
  · funext x
    change f t x + g t x = phi x + psi x
    rw [hf.classical.terminal, hg.classical.terminal]
  · intro x r hr
    rw [hgen r ⟨hr.1.le, hr.2.le⟩ x]
    convert (hf.classical.time_deriv x r hr).add (hg.classical.time_deriv x r hr)
      using 1 <;> ring
  · refine (hf.classical.cont_time_deriv.add hg.classical.cont_time_deriv).congr
      fun p => ?_
    exact (hgen p.1 p.1.2 p.2).symm
  · obtain ⟨Bf, hBf⟩ := hf.classical.bdd_time_deriv
    obtain ⟨Bg, hBg⟩ := hg.classical.bdd_time_deriv
    refine ⟨Bf + Bg, fun r hr x => ?_⟩
    rw [hgen r hr x]
    calc
      _ ≤ |generatorW C r (f r) x| + |generatorW C r (g r) x| := abs_add_le _ _
      _ ≤ Bf * (1 + ‖x‖) + Bg * (1 + ‖x‖) := add_le_add (hBf r hr x) (hBg r hr x)
      _ = _ := by ring

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.generatorW_const_mul
#print axioms HRS.MS.ProClosureS111.classicalCb4_const_mul
#print axioms HRS.MS.ProClosureS111.classicalCb4_add
