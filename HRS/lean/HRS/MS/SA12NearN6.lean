import HRS.MS.SA12NearN6C
import HRS.MH.AdjointRdDefs

/-!
# S.A.12 N6: separated supports, all output derivatives of the near operator
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd

-- BEGIN SA12.N6
theorem separated_nonlocal_jets (d m : ℕ) (hd : 1 ≤ d) (s MB ρ h : ℝ)
    (hs0 : 0 ≤ s) (hsd : s < d) (hρ : 1 ≤ ρ) (hh : 0 < h) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Matrix (Fin d) (Fin d) ℝ,
      PDE.MatBound MB M → ∀ (c : Euc d) (K : Set (Euc d)),
      ∀ a : Euc d → ℝ, MemCb 1 a →
      Function.support a ⊆ Metric.closedBall c ρ →
      (∀ x ∈ K, ∀ y ∈ Function.support a, h ≤ ‖x - y‖) →
      ∀ F : Euc d → ℝ, BddJets m F → ∀ j ≤ m, ∀ x ∈ K,
        ENNReal.ofReal ‖iteratedFDeriv ℝ j (eucNonlocal s M a F) x‖ ≤
          ENNReal.ofReal (C * cbNorm 1 a) *
            eLpNorm ((Metric.closedBall c ρ).indicator F) 2 volume := by
  -- kernel derivative bounds away from the origin
  have hker0 : ∀ n : ℕ, ∃ Cn : ℝ, 0 ≤ Cn ∧ (1 ≤ n → ∀ ξ : Euc d, ξ ≠ 0 →
      ‖iteratedFDeriv ℝ n (rieszKernel d s) ξ‖ ≤ Cn * ‖ξ‖ ^ (-s - n)) := by
    intro n
    by_cases hn : 1 ≤ n
    · obtain ⟨C, hC0, hC⟩ := HRS.MS.Ker1.ker1_E_bound (d := d) hs0 n (by
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        linarith)
      exact ⟨C, hC0, fun _ ξ hξ => hC ξ hξ⟩
    · exact ⟨0, le_rfl, fun h1 => absurd h1 hn⟩
  choose Ck hCk0 hCk using hker0
  set BB : ℝ := ∑ n ∈ Finset.range (m + 3), Ck n * h ^ (-s - n) with hBB
  have hBB0 : 0 ≤ BB := Finset.sum_nonneg fun n _ => mul_nonneg (hCk0 n) (Real.rpow_nonneg hh.le _)
  have hker : ∀ n : ℕ, 1 ≤ n → n ≤ m + 2 → ∀ z : Euc d, h ≤ ‖z‖ →
      ‖iteratedFDeriv ℝ n (rieszKernel d s) z‖ ≤ BB := by
    intro n hn1 hn2 z hz
    have hz0 : z ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hz; linarith
    refine (hCk n hn1 z hz0).trans ?_
    have h1 : ‖z‖ ^ (-s - n) ≤ h ^ (-s - n) :=
      Real.rpow_le_rpow_of_nonpos hh hz (by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith)
    calc Ck n * ‖z‖ ^ (-s - n) ≤ Ck n * h ^ (-s - n) := mul_le_mul_of_nonneg_left h1 (hCk0 n)
      _ ≤ BB := Finset.single_le_sum (f := fun n => Ck n * h ^ (-s - n))
          (fun n _ => mul_nonneg (hCk0 n) (Real.rpow_nonneg hh.le _))
          (Finset.mem_range.2 (by omega))
  set V12 : ℝ := (volume (Metric.closedBall (0 : Euc d) ρ)).toReal ^ (1 / 2 : ℝ) with hV12
  have hV0 : 0 ≤ V12 := Real.rpow_nonneg ENNReal.toReal_nonneg _
  set MB' : ℝ := max MB 0 with hMB'
  have hMB0 : 0 ≤ MB' := le_max_right _ _
  set Cmain : ℝ := (d : ℝ) * d * MB' * (d : ℝ) ^ m * (2 * BB) * V12 with hCmain
  have hCmain0 : 0 ≤ Cmain := by rw [hCmain]; positivity
  refine ⟨Cmain + 1, by linarith, ?_⟩
  intro M hM c K a ha hsupp hsep F hF j hj x hx
  have hρ0 : 0 ≤ ρ := by linarith
  have hts : tsupport a ⊆ Metric.closedBall c ρ :=
    closure_minimal hsupp Metric.isClosed_closedBall
  have hsep' : ∀ y ∈ tsupport a, h ≤ ‖x - y‖ := by
    have hcl : IsClosed {y : Euc d | h ≤ ‖x - y‖} :=
      isClosed_le continuous_const (continuous_norm.comp (continuous_const.sub continuous_id))
    exact closure_minimal (fun y hy => hsep x hx y hy) hcl
  have hFs : ContDiff ℝ ∞ F := hF.1
  set I : ℝ := ∫ y in Metric.closedBall c ρ, |F y| with hI
  have hI0 : 0 ≤ I := setIntegral_nonneg Metric.isClosed_closedBall.measurableSet (fun _ _ => abs_nonneg _)
  have hcb := HRS.MH.AdjointRd.Phase2SA12Companions.sa12z_cb_nonneg ha
  -- the pieces
  have hterm := fun (i j' : Fin d) =>
    sa12n_term_bound hd s (m := m) hh hρ0 hBB0 hker ha hFs hts hsep' i j' j hj
  -- the real bound
  have hreal : ‖iteratedFDeriv ℝ j (eucNonlocal s M a F) x‖ ≤
      (d : ℝ) * d * MB' * (d : ℝ) ^ m * (cbNorm 1 a * (2 * BB) * I) := by
    have hfun : eucNonlocal s M a F = fun x' => ∑ i : Fin d, ∑ j' : Fin d, M j' i *
        fderiv ℝ (fun x'' => ∫ y, rieszKernel d s (x'' - y) *
          (a y * fderiv ℝ F y (EuclideanSpace.single j' (1 : ℝ)))) x'
          (EuclideanSpace.single i (1 : ℝ)) := rfl
    have hjle : (j : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
    have hsum : iteratedFDeriv ℝ j (eucNonlocal s M a F) x = ∑ i : Fin d, ∑ j' : Fin d,
        M j' i • iteratedFDeriv ℝ j (fun x' => fderiv ℝ (fun x'' => ∫ y, rieszKernel d s (x'' - y) *
          (a y * fderiv ℝ F y (EuclideanSpace.single j' (1 : ℝ)))) x'
          (EuclideanSpace.single i (1 : ℝ))) x := by
      rw [hfun]
      rw [iteratedFDeriv_fun_sum_apply (fun i _ => ContDiffAt.sum (fun j' _ =>
        contDiffAt_const.mul ((hterm i j').1.of_le hjle)))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [iteratedFDeriv_fun_sum_apply (fun j' _ =>
        contDiffAt_const.mul ((hterm i j').1.of_le hjle))]
      refine Finset.sum_congr rfl fun j' _ => ?_
      have := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := M j' i) (i := j)
        (f := fun x' => fderiv ℝ (fun x'' => ∫ y, rieszKernel d s (x'' - y) *
          (a y * fderiv ℝ F y (EuclideanSpace.single j' (1 : ℝ)))) x'
          (EuclideanSpace.single i (1 : ℝ))) (x := x) ((hterm i j').1.of_le hjle)
      simpa only [smul_eq_mul] using this
    rw [hsum]
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ i : Fin d, ∑ j' : Fin d, (MB' * ((d : ℝ) ^ j * (cbNorm 1 a * (BB + BB) * I))) := by
          refine Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun j' _ => ?_)
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul ((hM j' i).trans (le_max_left _ _)) (hterm i j').2 (norm_nonneg _) hMB0
      _ = (d : ℝ) * d * MB' * (d : ℝ) ^ j * (cbNorm 1 a * (BB + BB) * I) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ (d : ℝ) * d * MB' * (d : ℝ) ^ m * (cbNorm 1 a * (2 * BB) * I) := by
          have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
          have hpow : (d : ℝ) ^ j ≤ (d : ℝ) ^ m := pow_le_pow_right₀ hd1 hj
          have e2 : BB + BB = 2 * BB := by ring
          rw [e2]
          have : 0 ≤ (d : ℝ) * d * MB' := by positivity
          have h3 : 0 ≤ cbNorm 1 a * (2 * BB) * I := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hpow this]
  -- pass to `ℝ≥0∞`
  have hcs := sa12n_cs hF.1.continuous c ρ
  set Q : ℝ := (d : ℝ) * d * MB' * (d : ℝ) ^ m * (cbNorm 1 a * (2 * BB)) with hQ
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  calc ENNReal.ofReal ‖iteratedFDeriv ℝ j (eucNonlocal s M a F) x‖
      ≤ ENNReal.ofReal (Q * I) := ENNReal.ofReal_le_ofReal (by rw [hQ]; nlinarith [hreal])
    _ = ENNReal.ofReal Q * ENNReal.ofReal I := ENNReal.ofReal_mul hQ0
    _ ≤ ENNReal.ofReal Q * (eLpNorm ((Metric.closedBall c ρ).indicator F) 2 volume *
          ENNReal.ofReal V12) := mul_le_mul' le_rfl hcs
    _ = ENNReal.ofReal (Q * V12) * eLpNorm ((Metric.closedBall c ρ).indicator F) 2 volume := by
        rw [ENNReal.ofReal_mul hQ0]; ring
    _ ≤ ENNReal.ofReal ((Cmain + 1) * cbNorm 1 a) *
          eLpNorm ((Metric.closedBall c ρ).indicator F) 2 volume := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        have : Q * V12 = Cmain * cbNorm 1 a := by rw [hQ, hCmain]; ring
        rw [this]; nlinarith [hcb]
-- END SA12.N6

end HRS.MH.AdjointRd.Phase2SA12Near
