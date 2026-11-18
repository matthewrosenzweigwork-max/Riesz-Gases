import HRS.MS.Fp81S21Uniform2
import HRS.MS.Fp81S21MovingM1
import HRS.MS.ProClosureS111WindowOrbit
import HRS.MS.R2WinOrbTRC1
import HRS.MS.WadAux1

/-!
# HRS S2.1(iii), SOL26 packet 14: weighted moving drift

The downstream remote-tail consumer needs the following source-interval
contracts.  Here `H := a + T`, `C := r26t3_coeff R`,
`φ_α := oscTestFun (wholeSpaceIndex p.d : ℝ) α`, and `b` is the moving
quadratic drift field.  The unweighted local source-variation estimate is:

```lean
∀ s ∈ Set.Icc (0 : ℝ) H, ∀ α,
  ∫ v in Set.Ioc 0 b,
    |b v (propagatorW C v s φ_α)| ≤
      K * (∫ v in Set.Ioc 0 b, Mb v) * cα
```

The remote-tail form, with constants chosen before `a`, `T`, and `H`, is:

```lean
∀ a T, 0 ≤ a → 0 < T → ∀ b, 0 ≤ b → b ≤ a → ∀ t ∈ Set.Icc 0 T, ∀ α,
  ∫ v in Set.Ioc 0 b,
    |b v (propagatorW C v (a + t) φ_α)| ≤
      K * cα * Real.exp (-c * (a - b)) *
        (∫ v in Set.Ioc 0 b, Mb v)
```

These are source-time scalar variation bounds.  They imply the interval-local
bound for the drift measure `I ↦ (t ↦ ∫_{I∩[0,a+t]} V^{a+t,v}b(v)dv)`;
the estimate is not a density bound for variation in the terminal-path
parameter.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R2Interp HRS.MS.R2WinOrb HRS.MS.FixEq

/-! A weighted version of `s57p_S_le`: one derivative can grow linearly.
The extra power is absorbed by lowering the Sobolev weight from `P` to `P-1`.
-/
theorem fp81s21_weightedDrift_S_le_growth
    {d r : ℕ} {P B : ℝ} (hP : (d : ℝ) < 2 * (P - 1)) (hB : 0 ≤ B)
    {f : Euc d → ℝ}
    (hderiv : ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x,
      |partialDeriv i f x| ≤ B * jbracket x) :
    s57pS d r P f ≤ ENNReal.ofReal
      ((s57pN d r : ℝ) * (B ^ 2 * ∫ x, s57pW d (P - 1) x)) := by
  have hW := s57pW_integrable (d := d) hP
  have key : ∀ j ≤ r, ∀ i : Fin j → Fin d,
      ∫⁻ x, ENNReal.ofReal
        (jbracket x ^ (-2 * P) * (partialDeriv i f x) ^ 2) ≤
          ENNReal.ofReal (B ^ 2 * ∫ x, s57pW d (P - 1) x) := by
    intro j hj i
    have hpt : ∀ x, ENNReal.ofReal
        (jbracket x ^ (-2 * P) * (partialDeriv i f x) ^ 2) ≤
          ENNReal.ofReal (B ^ 2 * s57pW d (P - 1) x) := by
      intro x
      apply ENNReal.ofReal_le_ofReal
      have hsq : (partialDeriv i f x) ^ 2 ≤ (B * jbracket x) ^ 2 := by
        have h := hderiv j hj i x
        have habs := abs_le.mp h
        exact sq_le_sq' habs.1 habs.2
      have hwt : 0 ≤ jbracket x ^ (-2 * P) :=
        (Real.rpow_pos_of_pos (s57p_jbracket_pos x) _).le
      calc jbracket x ^ (-2 * P) * (partialDeriv i f x) ^ 2
          ≤ jbracket x ^ (-2 * P) * (B * jbracket x) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq hwt
        _ = B ^ 2 * s57pW d (P - 1) x := by
          rw [s57pW]
          have hjb : 0 < jbracket x := s57p_jbracket_pos x
          have hcast : jbracket x ^ (2 : ℝ) = jbracket x ^ (2 : ℕ) := by
            exact Real.rpow_natCast (jbracket x) 2
          calc
            _ = B ^ 2 * (jbracket x ^ (-2 * P) * jbracket x ^ 2) := by
              rw [mul_pow]
              ring
            _ = B ^ 2 * (jbracket x ^ (-2 * P) * jbracket x ^ (2 : ℝ)) := by
              rw [← hcast]
            _ = B ^ 2 * jbracket x ^ ((-2 * P) + 2) := by
              rw [← Real.rpow_add hjb]
            _ = B ^ 2 * jbracket x ^ (-2 * (P - 1)) := by
              congr 2
              ring
    calc ∫⁻ x, ENNReal.ofReal
          (jbracket x ^ (-2 * P) * (partialDeriv i f x) ^ 2)
        ≤ ∫⁻ x, ENNReal.ofReal (B ^ 2 * s57pW d (P - 1) x) := lintegral_mono hpt
      _ = ENNReal.ofReal (∫ x, B ^ 2 * s57pW d (P - 1) x) := by
        rw [ofReal_integral_eq_lintegral_ofReal (hW.const_mul _)
          (Eventually.of_forall fun x =>
            mul_nonneg (sq_nonneg B) (s57pW_nonneg (P - 1) x))]
      _ = ENNReal.ofReal (B ^ 2 * ∫ x, s57pW d (P - 1) x) := by
        rw [integral_const_mul]
  unfold s57pS
  calc
    _ ≤ ∑ j ∈ Finset.range (r + 1), ∑ _i : Fin j → Fin d,
          ENNReal.ofReal (B ^ 2 * ∫ x, s57pW d (P - 1) x) := by
        refine Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun i _ => ?_
        exact key j (by simpa [Nat.lt_succ_iff] using hj) i
    _ = ENNReal.ofReal
          ((s57pN d r : ℝ) * (B ^ 2 * ∫ x, s57pW d (P - 1) x)) := by
        have hnn : 0 ≤ B ^ 2 * ∫ x, s57pW d (P - 1) x :=
          mul_nonneg (sq_nonneg B) (integral_nonneg fun x => s57pW_nonneg (P - 1) x)
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
          Fintype.card_fin, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        unfold s57pN
        push_cast
        rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [ENNReal.ofReal_mul (by positivity)]
        simp

theorem fp81s21_weightedDrift_E_le_growth
    {d r : ℕ} {P B : ℝ} (hP : (d : ℝ) < 2 * (P - 1)) (hB : 0 ≤ B)
    {f : Euc d → ℝ}
    (hderiv : ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x,
      |partialDeriv i f x| ≤ B * jbracket x) :
    weightedSobolevE r P f ≤ ENNReal.ofReal (s57pC d r (P - 1) * B) := by
  rw [s57p_E_eq]
  have hS := fp81s21_weightedDrift_S_le_growth hP hB hderiv
  have hW : 0 ≤ ∫ x, s57pW d (P - 1) x :=
    integral_nonneg fun x => s57pW_nonneg (P - 1) x
  calc (s57pS d r P f) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal ((s57pN d r : ℝ) *
          (B ^ 2 * ∫ x, s57pW d (P - 1) x))) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hS (by norm_num)
    _ = ENNReal.ofReal (((s57pN d r : ℝ) *
          (B ^ 2 * ∫ x, s57pW d (P - 1) x)) ^ (1 / 2 : ℝ)) :=
        ENNReal.ofReal_rpow_of_nonneg
          (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (sq_nonneg B) hW)) (by norm_num)
    _ = ENNReal.ofReal (s57pC d r (P - 1) * B) := by
      congr 1
      unfold s57pC
      rw [← Real.sqrt_eq_rpow,
        show (s57pN d r : ℝ) * (B ^ 2 * ∫ x, s57pW d (P - 1) x) =
          ((s57pN d r : ℝ) * ∫ x, s57pW d (P - 1) x) * B ^ 2 by ring,
        Real.sqrt_mul (mul_nonneg (Nat.cast_nonneg _) hW), Real.sqrt_sq hB]

theorem fp81s21_weightedDrift_centered_test
    {d k r : ℕ} {C : WholeCoeff d} {m T t u A c P : ℝ}
    {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hP : (d : ℝ) < 2 * (P - 1)) (hA : 0 ≤ A)
    (hGrad : R2OrbitGrad C k t φ A c)
    (hf : IsClassicalAdjointW C t φ f)
    (hu : u ∈ Icc (0 : ℝ) t) (hr : r ≤ k + 1) :
    IsR2WeightedTest r P (fun x => f u x - f u 0) ∧
      (weightedSobolevE r P (fun x => f u x - f u 0)).toReal ≤
        s57pC d r (P - 1) * (A * Real.exp (-c * (t - u))) := by
  let B : ℝ := A * Real.exp (-c * (t - u))
  have hB : 0 ≤ B := mul_nonneg hA (Real.exp_pos _).le
  obtain ⟨hGradSmooth, hGradBound⟩ := hGrad f hf u hu
  have hSmooth : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (f u) :=
    HRS.MS.R2WinOrb.s103_fderiv_contDiff
      ((hf.c2 u hu).differentiable (by norm_num)) hGradSmooth
  have hJets := HRS.MS.R2WinOrbNL.s103c_jets_of_cb hB hSmooth hGradBound
  have hFderiv : ∀ x, ‖fderiv ℝ (f u) x‖ ≤ B := by
    intro x
    calc ‖fderiv ℝ (f u) x‖ = ‖iteratedFDeriv ℝ 1 (f u) x‖ := by
          rw [← norm_iteratedFDeriv_one]
      _ ≤ B := hJets 1 (by norm_num) (by omega) x
  have hDiff : Differentiable ℝ (f u) :=
    (hf.c2 u hu).differentiable (by norm_num)
  have hMean : ∀ x, ‖f u x - f u 0‖ ≤ B * ‖x‖ := by
    intro x
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le
      (f := f u) (s := Set.univ) (C := B)
      (fun y _ => hDiff y) (fun y _ => hFderiv y) convex_univ
      (Set.mem_univ (0 : Euc d)) (Set.mem_univ x)
    simpa using h
  let g : Euc d → ℝ := fun x => f u x - f u 0
  have hgSmooth : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) g := by
    dsimp [g]
    exact hSmooth.sub contDiff_const
  have hderiv : ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x,
      |partialDeriv i g x| ≤ B * jbracket x := by
    intro j hj i x
    by_cases hj0 : j = 0
    · subst j
      have hpartial : partialDeriv i g x = g x := by simp [partialDeriv, g]
      rw [hpartial]
      calc |g x| = ‖f u x - f u 0‖ := by simp [g, Real.norm_eq_abs]
        _ ≤ B * ‖x‖ := hMean x
        _ ≤ B * jbracket x := mul_le_mul_of_nonneg_left
          (HRS.MS.Wad.s83_norm_le_jb x) hB
    · have hsub : iteratedFDeriv ℝ j g x = iteratedFDeriv ℝ j (f u) x := by
        dsimp [g]
        rw [show (fun y => f u y - f u 0) = (f u) - fun _ => f u 0 by rfl,
          iteratedFDeriv_sub_apply
            (hSmooth.of_le (by exact_mod_cast (le_trans hj hr))).contDiffAt
            contDiff_const.contDiffAt,
          iteratedFDeriv_const_of_ne hj0, Pi.zero_apply, sub_zero]
      calc |partialDeriv i g x| ≤ ‖iteratedFDeriv ℝ j g x‖ :=
            s57p_abs_partialDeriv_le i g x
        _ = ‖iteratedFDeriv ℝ j (f u) x‖ := by rw [hsub]
        _ ≤ B := hJets j (by omega) (by omega) x
        _ ≤ B * jbracket x := by
          simpa using mul_le_mul_of_nonneg_left
            (HRS.MS.Wad.s83_one_le_jb x) hB
  have hE := fp81s21_weightedDrift_E_le_growth hP hB hderiv
  have hEtop : weightedSobolevE r P g < ⊤ :=
    lt_of_le_of_lt hE ENNReal.ofReal_lt_top
  have hEreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hE
  have hEreal' : (weightedSobolevE r P g).toReal ≤ s57pC d r (P - 1) * B := by
    simpa [ENNReal.toReal_ofReal,
      mul_nonneg (s57pC_nonneg d r (P - 1)) hB] using hEreal
  exact ⟨⟨hgSmooth.of_le (by exact_mod_cast hr), hEtop⟩, by simpa [B] using hEreal'⟩

end HRS.Fp81.S21

end

#print axioms HRS.Fp81.S21.fp81s21_weightedDrift_S_le_growth
#print axioms HRS.Fp81.S21.fp81s21_weightedDrift_E_le_growth
#print axioms HRS.Fp81.S21.fp81s21_weightedDrift_centered_test
