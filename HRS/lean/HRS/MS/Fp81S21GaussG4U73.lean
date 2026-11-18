import HRS.MS.Fp81S21GaussG4U72

/-! Joint measurability of the scalar terminal-generator integrand used in U7. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL HRS.MS.S53

/-- The propagated scalar generator of a finite Hermite combination is jointly
measurable in its terminal time and spatial variable on a compact time interval. -/
theorem fp81s21_g4_initial_scalar_joint_meas
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hterm : S104bTermRegGen p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁)
    {f : Euc p.d → ℝ}
    (hf : IsR2DualCombo (wholeSpaceIndex p.d : ℝ) f)
    {T : ℝ} (hT : 0 ≤ T) :
    Measurable (Function.uncurry (fun q : Icc (0 : ℝ) T => fun x : Euc p.d =>
      r26t3_U R 0 q.1 (generatorW (r26t3_coeff R) q.1 f) x)) := by
  classical
  rcases hf with ⟨S, coeff, rfl⟩
  let mode (α : MultiIndex p.d) : Icc (0 : ℝ) T → Euc p.d → ℝ := fun q x =>
    r26t3_U R 0 q.1
      (generatorW (r26t3_coeff R) q.1 (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x
  have hmode : ∀ α : MultiIndex p.d,
      Measurable (Function.uncurry (mode α)) := by
    intro α
    let horb := s104b_orbit_of_termRegGen hterm R.admissible R.resulting α T hT
    let G : ℝ → Euc p.d → ℝ := fun τ =>
      r26t3_U R 0 τ (generatorW (r26t3_coeff R) τ
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α))
    have hG : ∀ τ ∈ Icc (0 : ℝ) T, MemCb 2 (G τ) := by
      intro τ hτ
      simpa [G, r26t3_U, r26t3_coeff] using
        horb.cb1 (r := 0) (by simp [hT]) (by simpa using hτ)
    obtain ⟨G2, hG2, hd12⟩ := horb.diff12 0 ⟨le_rfl, hT⟩
    have hG2' : ∀ τ ∈ Icc (0 : ℝ) T, MemCb 2 (G2 τ) := by
      simpa only [sub_zero] using hG2
    have hd12' : S53Diff T G G2 := by
      simpa [G, r26t3_U, r26t3_coeff] using hd12
    have hGc : S53Cont T G := s53_cont_of_diff hG hG2' hd12'
    have htime : ∀ x : Euc p.d, ContinuousOn (fun τ => G τ x) (Icc (0 : ℝ) T) := by
      intro x τ hτ
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      obtain ⟨η, hη, hclose⟩ := hGc τ hτ (ε / 2) (by positivity)
      refine ⟨η, hη, fun τ' hτ' hdist => ?_⟩
      have hpt := hclose τ' hτ' (by simpa [Real.dist_eq] using hdist) 0 (by norm_num) x
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hpt
      rw [Real.dist_eq]
      exact lt_of_le_of_lt hpt (by linarith)
    let u : Icc (0 : ℝ) T → Euc p.d → ℝ := fun q x => G q.1 x
    have hucont : ∀ q, Continuous (u q) := by
      intro q
      have hq : q.1 ∈ Icc (0 : ℝ) T := q.2
      exact (hG q.1 hq).1.continuous
    have htimeSub : ∀ x, Continuous (fun q : Icc (0 : ℝ) T => u q x) := by
      intro x
      exact (continuousOn_iff_continuous_domRestrict.mp (htime x)).congr
        (fun q => rfl)
    have hujoint : Measurable (Function.uncurry u) :=
      measurable_uncurry_of_continuous_of_measurable htimeSub
        (fun q => (hucont q).measurable)
    have heq : Function.uncurry u = Function.uncurry (mode α) := by
      funext z
      rcases z with ⟨q, x⟩
      simp [u, mode, G]
    rw [← heq]
    exact hujoint
  have hsum : Measurable (Function.uncurry (fun q : Icc (0 : ℝ) T => fun x =>
      ∑ α ∈ S, coeff α * mode α q x)) := by
    have hs : Measurable (fun z : Icc (0 : ℝ) T × Euc p.d =>
        ∑ α ∈ S, coeff α * (Function.uncurry (mode α)) z) :=
      Finset.measurable_sum S (fun α hα => measurable_const.mul (hmode α))
    exact hs
  have hcombo : ∀ q : Icc (0 : ℝ) T,
      (fun x => r26t3_U R 0 q.1
        (generatorW (r26t3_coeff R) q.1
          (fun y => ∑ α ∈ S, coeff α * oscTestFun (wholeSpaceIndex p.d : ℝ) α y)) x) =
      fun x => ∑ α ∈ S, coeff α * mode α q x := by
    intro q
    have h := fp81s21_g4_generator_combo p R hterm (r := 0) (q := q.1)
      le_rfl q.2.1 S coeff
    funext x
    simpa [mode] using congrFun h.2.2 x
  have heq : Function.uncurry (fun q : Icc (0 : ℝ) T => fun x =>
      r26t3_U R 0 q.1 (generatorW (r26t3_coeff R) q.1
        (fun y => ∑ α ∈ S, coeff α * oscTestFun (wholeSpaceIndex p.d : ℝ) α y)) x) =
      Function.uncurry (fun q : Icc (0 : ℝ) T => fun x =>
        ∑ α ∈ S, coeff α * mode α q x) := by
    funext z
    exact congrFun (hcombo z.1) z.2
  rw [heq]
  exact hsum

#print axioms fp81s21_g4_initial_scalar_joint_meas
end HRS.Fp81.S21
end
