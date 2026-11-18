import HRS.MS.AdjRdWeakTerm
import HRS.MS.UniqN0f
import HRS.MH.AdjointRdDefs

/-!
# S.A.12 L7: continuity and decay of the nonlocal test function `nonlocalTestRd` of a `C_c^∞` test
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd

variable {d : ℕ}

/-- The far-field algebra: `‖x‖ ≥ 2` gives `‖x‖^{-q} ≤ (3/2)^q (1+‖x‖)^{-q}`. -/
theorem sa12l7_far_alg {q : ℝ} (hq : 0 ≤ q) {r : ℝ} (hr : 2 ≤ r) :
    r ^ (-q) ≤ (3 / 2 : ℝ) ^ q * (1 + r) ^ (-q) := by
  have h1 : (2 / 3 : ℝ) * (1 + r) ≤ r := by linarith
  have h2 := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (2 / 3 : ℝ) * (1 + r)) h1
    (by linarith : -q ≤ 0)
  rw [Real.mul_rpow (by norm_num) (by linarith), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2 / 3),
    show (2 / 3 : ℝ) = (3 / 2)⁻¹ by norm_num, Real.inv_rpow (by norm_num), inv_inv] at h2
  exact h2

-- BEGIN SA12.L7
set_option maxHeartbeats 1600000 in
theorem test_nonlocal_decay (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (m : ℕ) (hm : 1 ≤ m) (MB Λ ΛV G₀ νbar T : ℝ) (D : WholeDyn d)
    (μ : ℝ → Euc d → ℝ) (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ)
    (ψ : Euc d → ℝ) (hψ : IsCcInfty ψ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r ∈ Icc (0 : ℝ) T,
      Continuous (nonlocalTestRd (D.coeff μ) r ψ) ∧
      ∀ x, |nonlocalTestRd (D.coeff μ) r ψ x| ≤
        K * jbracket x ^ (-((d : ℝ) + 3 + s + 1)) := by
  obtain ⟨hDs, -, -⟩ := hD.hs
  subst hDs
  have hs0' : 0 ≤ D.s := hs0
  have hsd' : D.s < d := hsd
  have hμ : CoeffHypRd D.s m Λ T μ := hD.hμ
  have hl := rieszKernel_locallyIntegrable (d := d) hs0' hsd'
  have hψ2 : ContDiff ℝ 2 ψ := hψ.1.of_le (by simp)
  have hψ1 : ContDiff ℝ 1 ψ := hψ.1.of_le (by simp)
  -- the support radius
  obtain ⟨R0, hR0⟩ := hψ.2.isCompact.isBounded.subset_closedBall (0 : Euc d)
  set R : ℝ := max R0 1 with hR
  have hR1 : 1 ≤ R := le_max_right _ _
  have hsupp : Function.support ψ ⊆ Metric.closedBall (0 : Euc d) R :=
    (subset_tsupport ψ).trans (hR0.trans (Metric.closedBall_subset_closedBall (le_max_left _ _)))
  -- convolution growth constants
  choose C1 hC1 using fun i : Fin d => HRS.MS.UniqT3.conv_bound hs0' hsd'
    (HRS.MS.UniqT3.D1_contDiff hψ2 i).continuous (HRS.MS.UniqT3.D1_supp hψ.2 i)
  choose C2 hC2 using fun i j : Fin d => HRS.MS.UniqT3.conv_bound hs0' hsd'
    (HRS.MS.UniqN2b.n2b_D1D1_cont hψ2 i j)
    (HRS.MS.UniqT3.D1_supp (HRS.MS.UniqT3.D1_supp hψ.2 i) j)
  set CH : ℝ := ∑ i, |C1 i| with hCH
  set CHH : ℝ := ∑ i, ∑ j, |C2 i j| with hCHH
  have hCH0 : 0 ≤ CH := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hCHH0 : 0 ≤ CHH := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hH : ∀ i x, |kernelConvDeriv d D.s i ψ x| ≤ CH * (1 + ‖x‖) := by
    intro i x
    have h1 : |kernelConvDeriv d D.s i ψ x| ≤ |C1 i| * (1 + ‖x‖) :=
      (hC1 i x).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    exact h1.trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := fun i => |C1 i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i))
      (by positivity))
  have hHH : ∀ i j x, |HRS.MS.UniqT3.D1 j (kernelConvDeriv d D.s i ψ) x| ≤ CHH * (1 + ‖x‖) := by
    intro i j x
    rw [HRS.MS.UniqN1c.n1c_D1_kcd hs0' hsd' hψ2 hψ.2 i j x]
    have h1 : |HRS.Whole.convFun (rieszKernel d D.s) (HRS.MS.UniqT3.D1 j (HRS.MS.UniqT3.D1 i ψ)) x| ≤
        |C2 i j| * (1 + ‖x‖) :=
      (hC2 i j x).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    calc |C2 i j| ≤ ∑ j', |C2 i j'| :=
          Finset.single_le_sum (f := fun j' => |C2 i j'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', |C2 i' j'| :=
          Finset.single_le_sum (f := fun i' => ∑ j', |C2 i' j'|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  set Af : ℝ := (max 1 D.s * 2 ^ (D.s + 1)) * ∫ x, |ψ x| with hAf
  set Ag : ℝ := (max 1 D.s * (D.s + 3) * 2 ^ (D.s + 2)) * ∫ x, |ψ x| with hAg
  have hint0 : 0 ≤ ∫ x, |ψ x| := integral_nonneg fun x => abs_nonneg _
  have hAf0 : 0 ≤ Af := by rw [hAf]; positivity
  have hAg0 : 0 ≤ Ag := by rw [hAg]; positivity
  have hfar1 : ∀ i x, 2 * R ≤ ‖x‖ → |kernelConvDeriv d D.s i ψ x| ≤ Af * ‖x‖ ^ (-D.s - 1) := by
    intro i x hx
    have := HRS.MS.UniqN0.n0_far_bound hs0' i hψ1 hψ.2 (c := 0) hR1 hsupp (y := x)
      (by simpa using hx)
    simp only [sub_zero] at this
    exact this
  have hfar2 : ∀ i j x, 2 * R ≤ ‖x‖ →
      |HRS.MS.UniqT3.D1 j (kernelConvDeriv d D.s i ψ) x| ≤ Ag * ‖x‖ ^ (-D.s - 2) := by
    intro i j x hx
    have := HRS.MS.UniqN0.n0_far_grad_bound hs0' hsd' i j hψ2 hψ.2 (c := 0) hR1 hsupp (y := x)
      (by simpa using hx)
    simp only [sub_zero] at this
    exact this
  set Mabs : ℝ := ∑ i, ∑ j, |D.M j i| with hMabs
  have hMabs0 : 0 ≤ Mabs := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  set p : ℝ := (d : ℝ) + 3 + D.s + 1 with hp
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  set Cρ : ℝ := HRS.MS.UniqC1.c1A d m Λ with hCρ
  have hCρ0 : 0 ≤ Cρ := HRS.MS.UniqE1.e1_A_nonneg m Λ
  set j2 : ℝ := Real.sqrt (1 + (2 * R) ^ 2) with hj2
  have hj20 : 0 < j2 := Real.sqrt_pos.2 (by positivity)
  set Nn : ℝ := Cρ * ((CH + CHH) * (1 + 2 * R)) with hNn
  set Fn : ℝ := Cρ * (Af + Ag) * (3 / 2 : ℝ) ^ (D.s + 1) with hFn
  have hNn0 : 0 ≤ Nn := by rw [hNn]; positivity
  have hFn0 : 0 ≤ Fn := by rw [hFn]; positivity
  set K' : ℝ := max (Nn * j2 ^ p) Fn with hK'
  have hK'0 : 0 ≤ K' := (mul_nonneg hNn0 (Real.rpow_nonneg hj20.le _)).trans (le_max_left _ _)
  refine ⟨Mabs * K', mul_nonneg hMabs0 hK'0, fun r hr => ?_⟩
  obtain ⟨hb1, -, -, hρ1, hρ0, hρ1'⟩ :=
    HRS.MS.UniqE1.e1_coeff hd hs0' hsd' m MB Λ ΛV G₀ hD.hM hD.hV hμ hr
  set ρ : Euc d → ℝ := μ r with hρ
  have hnl : ∀ x, nonlocalTestRd (D.coeff μ) r ψ x = ∑ i : Fin d, ∑ j : Fin d, D.M j i *
      (HRS.MS.UniqT3.D1 j ρ x * kernelConvDeriv d D.s i ψ x + ρ x *
        HRS.Whole.convFun (rieszKernel d D.s) (HRS.MS.UniqT3.D1 j (HRS.MS.UniqT3.D1 i ψ)) x) := by
    intro x
    unfold nonlocalTestRd
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hg : ∀ y, gradient (HRS.Whole.convFun (rieszKernel d D.s) ψ) y i =
        kernelConvDeriv d D.s i ψ y := by
      intro y
      rw [q09_gradient_apply]
      exact HRS.MS.UniqT3.convFun_D1 hl hψ1 hψ.2 i y
    show D.M j i * partialDeriv (fun _ : Fin 1 => j)
      (fun y => μ r y * gradient (HRS.Whole.convFun (rieszKernel d D.s) ψ) y i) x = _
    congr 1
    simp only [hg]
    unfold partialDeriv
    rw [iteratedFDeriv_one_apply]
    exact HRS.MS.UniqN2b.n2b_fderiv_prod hs0' hsd' hρ1 hψ2 hψ.2 i j x
  refine ⟨?_, fun x => ?_⟩
  · have : nonlocalTestRd (D.coeff μ) r ψ = fun x => ∑ i : Fin d, ∑ j : Fin d, D.M j i *
        (HRS.MS.UniqT3.D1 j ρ x * kernelConvDeriv d D.s i ψ x + ρ x *
          HRS.Whole.convFun (rieszKernel d D.s) (HRS.MS.UniqT3.D1 j (HRS.MS.UniqT3.D1 i ψ)) x) :=
      funext hnl
    rw [this]
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => continuous_const.mul ?_
    have c1 : Continuous (HRS.MS.UniqT3.D1 j ρ) :=
      (hρ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have c2 : Continuous (kernelConvDeriv d D.s i ψ) :=
      HRS.MS.UniqT3.K_cont hs0' hsd' (HRS.MS.UniqT3.D1_contDiff hψ2 i).continuous
        (HRS.MS.UniqT3.D1_supp hψ.2 i)
    have c3 : Continuous (HRS.Whole.convFun (rieszKernel d D.s)
        (HRS.MS.UniqT3.D1 j (HRS.MS.UniqT3.D1 i ψ))) :=
      HRS.MS.UniqT3.K_cont hs0' hsd' (HRS.MS.UniqN2b.n2b_D1D1_cont hψ2 i j)
        (HRS.MS.UniqT3.D1_supp (HRS.MS.UniqT3.D1_supp hψ.2 i) j)
    exact (c1.mul c2).add (hρ1.continuous.mul c3)
  · -- the pointwise bound for each summand
    have hjb0 : 0 < jbracket x := by unfold jbracket; positivity
    have hterm : ∀ i j : Fin d,
        |HRS.MS.UniqT3.D1 j ρ x * kernelConvDeriv d D.s i ψ x + ρ x *
          HRS.Whole.convFun (rieszKernel d D.s) (HRS.MS.UniqT3.D1 j (HRS.MS.UniqT3.D1 i ψ)) x| ≤
        K' * jbracket x ^ (-p) := by
      intro i j
      have hkk : HRS.Whole.convFun (rieszKernel d D.s) (HRS.MS.UniqT3.D1 j (HRS.MS.UniqT3.D1 i ψ)) x =
          HRS.MS.UniqT3.D1 j (kernelConvDeriv d D.s i ψ) x :=
        (HRS.MS.UniqN1c.n1c_D1_kcd hs0' hsd' hψ2 hψ.2 i j x).symm
      rw [hkk]
      set u : ℝ := (1 + ‖x‖) ^ (-((d : ℝ) + 3)) with hu
      have hu0 : 0 ≤ u := Real.rpow_nonneg (by positivity) _
      have hd1 : |HRS.MS.UniqT3.D1 j ρ x| ≤ Cρ * u :=
        (HRS.MS.UniqN2b.n2b_D1_le j ρ x).trans (hρ1' x)
      have hd0 : |ρ x| ≤ Cρ * u := hρ0 x
      have hsum : |HRS.MS.UniqT3.D1 j ρ x * kernelConvDeriv d D.s i ψ x + ρ x *
          HRS.MS.UniqT3.D1 j (kernelConvDeriv d D.s i ψ) x| ≤
          Cρ * u * (|kernelConvDeriv d D.s i ψ x| +
            |HRS.MS.UniqT3.D1 j (kernelConvDeriv d D.s i ψ) x|) := by
        calc _ ≤ |HRS.MS.UniqT3.D1 j ρ x * kernelConvDeriv d D.s i ψ x| +
              |ρ x * HRS.MS.UniqT3.D1 j (kernelConvDeriv d D.s i ψ) x| := abs_add_le _ _
          _ = |HRS.MS.UniqT3.D1 j ρ x| * |kernelConvDeriv d D.s i ψ x| +
              |ρ x| * |HRS.MS.UniqT3.D1 j (kernelConvDeriv d D.s i ψ) x| := by
              rw [abs_mul, abs_mul]
          _ ≤ Cρ * u * |kernelConvDeriv d D.s i ψ x| +
              Cρ * u * |HRS.MS.UniqT3.D1 j (kernelConvDeriv d D.s i ψ) x| :=
              add_le_add (mul_le_mul_of_nonneg_right hd1 (abs_nonneg _))
                (mul_le_mul_of_nonneg_right hd0 (abs_nonneg _))
          _ = _ := by ring
      by_cases hx : ‖x‖ ≤ 2 * R
      · -- near region
        have hu1 : u ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg x])
          (by linarith [(by positivity : (0 : ℝ) ≤ d)])
        have hb : |kernelConvDeriv d D.s i ψ x| + |HRS.MS.UniqT3.D1 j (kernelConvDeriv d D.s i ψ) x| ≤
            (CH + CHH) * (1 + 2 * R) := by
          calc _ ≤ CH * (1 + ‖x‖) + CHH * (1 + ‖x‖) := add_le_add (hH i x) (hHH i j x)
            _ = (CH + CHH) * (1 + ‖x‖) := by ring
            _ ≤ (CH + CHH) * (1 + 2 * R) :=
                mul_le_mul_of_nonneg_left (by linarith) (add_nonneg hCH0 hCHH0)
        have hN : |HRS.MS.UniqT3.D1 j ρ x * kernelConvDeriv d D.s i ψ x + ρ x *
            HRS.MS.UniqT3.D1 j (kernelConvDeriv d D.s i ψ) x| ≤ Nn := by
          refine hsum.trans ?_
          rw [hNn]
          have : Cρ * u ≤ Cρ := by nlinarith
          calc Cρ * u * (|kernelConvDeriv d D.s i ψ x| + |HRS.MS.UniqT3.D1 j (kernelConvDeriv d D.s i ψ) x|)
              ≤ Cρ * ((CH + CHH) * (1 + 2 * R)) :=
                mul_le_mul this hb (by positivity) hCρ0
            _ = _ := rfl
        refine hN.trans ?_
        have hjle : jbracket x ≤ j2 := by
          unfold jbracket
          rw [hj2]
          refine Real.sqrt_le_sqrt ?_
          nlinarith [norm_nonneg x]
        have h3 : j2 ^ (-p) ≤ jbracket x ^ (-p) :=
          Real.rpow_le_rpow_of_nonpos hjb0 hjle (by linarith)
        have h4 : j2 ^ p * j2 ^ (-p) = 1 := by
          rw [← Real.rpow_add hj20]; simp
        calc Nn = Nn * (j2 ^ p * j2 ^ (-p)) := by rw [h4, mul_one]
          _ ≤ Nn * (j2 ^ p * jbracket x ^ (-p)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3
                (Real.rpow_nonneg hj20.le _)) hNn0
          _ = (Nn * j2 ^ p) * jbracket x ^ (-p) := by ring
          _ ≤ K' * jbracket x ^ (-p) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hjb0.le _)
      · -- far region
        push Not at hx
        have hr2 : 2 ≤ ‖x‖ := by linarith only [hx, hR1]
        have hr1 : 1 ≤ ‖x‖ := by linarith only [hr2]
        have hF1 := hfar1 i x hx.le
        have hF2 := hfar2 i j x hx.le
        have e1 : (-D.s - 1) = -(D.s + 1) := by ring
        rw [e1] at hF1
        have hexp : ‖x‖ ^ (-D.s - 2) ≤ ‖x‖ ^ (-(D.s + 1)) :=
          Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)
        have hb : |kernelConvDeriv d D.s i ψ x| +
            |HRS.MS.UniqT3.D1 j (kernelConvDeriv d D.s i ψ) x| ≤
            (Af + Ag) * ((3 / 2 : ℝ) ^ (D.s + 1) * (1 + ‖x‖) ^ (-(D.s + 1))) := by
          have hal := sa12l7_far_alg (q := D.s + 1) (by linarith) hr2
          calc _ ≤ Af * ‖x‖ ^ (-(D.s + 1)) + Ag * ‖x‖ ^ (-(D.s + 1)) :=
                add_le_add hF1 (hF2.trans (mul_le_mul_of_nonneg_left hexp hAg0))
            _ = (Af + Ag) * ‖x‖ ^ (-(D.s + 1)) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hal (by positivity)
        have hpow : u * (1 + ‖x‖) ^ (-(D.s + 1)) = (1 + ‖x‖) ^ (-p) := by
          rw [hu, ← Real.rpow_add (by positivity)]
          congr 1
          rw [hp]; ring
        have hFar : |HRS.MS.UniqT3.D1 j ρ x * kernelConvDeriv d D.s i ψ x + ρ x *
            HRS.MS.UniqT3.D1 j (kernelConvDeriv d D.s i ψ) x| ≤ Fn * (1 + ‖x‖) ^ (-p) := by
          refine hsum.trans ?_
          calc Cρ * u * (|kernelConvDeriv d D.s i ψ x| +
                |HRS.MS.UniqT3.D1 j (kernelConvDeriv d D.s i ψ) x|)
              ≤ Cρ * u * ((Af + Ag) * ((3 / 2 : ℝ) ^ (D.s + 1) * (1 + ‖x‖) ^ (-(D.s + 1)))) :=
                mul_le_mul_of_nonneg_left hb (mul_nonneg hCρ0 hu0)
            _ = Fn * (u * (1 + ‖x‖) ^ (-(D.s + 1))) := by rw [hFn]; ring
            _ = Fn * (1 + ‖x‖) ^ (-p) := by rw [hpow]
        refine hFar.trans ?_
        have hjle : 1 + ‖x‖ ≥ jbracket x := by
          unfold jbracket
          rw [ge_iff_le, Real.sqrt_le_left (by positivity)]
          nlinarith [norm_nonneg x]
        have h3 : (1 + ‖x‖) ^ (-p) ≤ jbracket x ^ (-p) :=
          Real.rpow_le_rpow_of_nonpos hjb0 hjle (by linarith)
        calc Fn * (1 + ‖x‖) ^ (-p) ≤ Fn * jbracket x ^ (-p) := mul_le_mul_of_nonneg_left h3 hFn0
          _ ≤ K' * jbracket x ^ (-p) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hjb0.le _)
    rw [hnl x]
    calc |∑ i : Fin d, ∑ j : Fin d, D.M j i * (HRS.MS.UniqT3.D1 j ρ x * kernelConvDeriv d D.s i ψ x + ρ x *
          HRS.Whole.convFun (rieszKernel d D.s) (HRS.MS.UniqT3.D1 j (HRS.MS.UniqT3.D1 i ψ)) x)|
        ≤ ∑ i : Fin d, ∑ j : Fin d, |D.M j i| * (K' * jbracket x ^ (-p)) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hterm i j) (abs_nonneg _)
      _ = Mabs * K' * jbracket x ^ (-p) := by
          rw [hMabs, Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul, Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring
-- END SA12.L7

end HRS.MH.AdjointRd.Phase2SA12Limit
