import HRS.MS.Fp81S21WeightedGenCoef
import HRS.MS.UlTail
import HRS.Whole.MovtrAux9
import HRS.MS.R2PolyAux1

/-! Finite-order convolution bounds for the physical coefficient. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.R26T3 HRS.MS.Ul

private theorem fp81s21_b3_norm_iter_le_sum {d k : ℕ} {f : Euc d → Euc d}
    (hf : ContDiff ℝ k f) {j : ℕ} (hj : j ≤ k) (x : Euc d) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ ∑ i : Fin d, ‖iteratedFDeriv ℝ j (fun y => f y i) x‖ := by
  have hcomp : ∀ i : Fin d, iteratedFDeriv ℝ j (fun y => f y i) x =
      (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).compContinuousMultilinearMap
        (iteratedFDeriv ℝ j f x) := by
    intro i
    exact (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).iteratedFDeriv_comp_left
      hf.contDiffAt (by exact_mod_cast hj)
  refine ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) ?_
  intro v
  calc ‖iteratedFDeriv ℝ j f x v‖ ≤ ∑ i, |(iteratedFDeriv ℝ j f x v) i| := ult_norm_le_sum_abs _
    _ ≤ ∑ i, ‖iteratedFDeriv ℝ j (fun y => f y i) x‖ * ∏ l, ‖v l‖ := by
      refine Finset.sum_le_sum fun i _ => ?_
      have h := (iteratedFDeriv ℝ j (fun y => f y i) x).le_opNorm v
      rw [hcomp i] at h ⊢
      simpa using h
    _ = (∑ i, ‖iteratedFDeriv ℝ j (fun y => f y i) x‖) * ∏ l, ‖v l‖ := by rw [Finset.sum_mul]

/-- All jets through the required order of the physical convolution are uniformly bounded. -/
theorem fp81s21_b3_convolution_jets (p : Parameters) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 2 : ℝ) →
      ∀ R : Trajectory p δ, ∀ u, 0 ≤ u →
        ContDiff ℝ (fp81s21_b3_q p) (convGradConvW (rieszKernelGrad p.d p.s) (R.ρ u)) ∧
        ∀ j ≤ fp81s21_b3_q p, ∀ x,
          ‖iteratedFDeriv ℝ j (convGradConvW (rieszKernelGrad p.d p.s) (R.ρ u)) x‖ ≤ C := by
  obtain ⟨B, c, hB, hc, hρ⟩ := fp81s21_b3_rho_jets p
  let k := fp81s21_b3_q p
  let N : ℕ := 3 * p.d + k + 10
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hL : (p.d : ℝ) + k + p.s + 3 < (N : ℝ) := by
    dsimp [N]; push_cast
    have : (0 : ℝ) ≤ p.d := Nat.cast_nonneg p.d
    linarith
  have hdL : (p.d : ℝ) < (N : ℝ) := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith [p.hs0]
  obtain ⟨P, hP, hPbound⟩ := HRS.MS.S104e.s104e_u2dec_of_gauss hc (k + 1) N
  have hd : 1 ≤ p.d := by have := p.hd; omega
  choose Ci hCi0 hCi using fun i : Fin p.d => ult_core hd (ult_ker_kap p.hs0 hsd i) k hL
  let C : ℝ := (∑ i, Ci i) * (P * B)
  have hPB : 0 ≤ P * B := mul_nonneg hP hB
  refine ⟨C, mul_nonneg (Finset.sum_nonneg fun i _ => hCi0 i) hPB, ?_⟩
  intro δ hδ hδhalf R u hu
  obtain ⟨hrc, hrb⟩ := hρ δ hδ hδhalf R u hu
  have hr' : ContDiff ℝ (k + 1) (R.ρ u) := hrc.of_le (by dsimp [k]; exact_mod_cast (by omega : fp81s21_b3_q p + 1 ≤ fp81s21_b3_q p + 2))
  have hb' : ∀ j ≤ k + 1, ∀ x, ‖iteratedFDeriv ℝ j (R.ρ u) x‖ ≤ B * Real.exp (-c * ‖x‖ ^ 2) := by
    intro j hj x
    exact hrb j (by dsimp [k] at hj; omega) x
  have hdec := hPbound (R.ρ u) B hB hr' hb'
  have hfun : ∀ i : Fin p.d, (fun x => convGradConvW (rieszKernelGrad p.d p.s) (R.ρ u) x i) = ultK (u2_kap p.d p.s i) (R.ρ u) := by
    intro i
    funext x
    exact (ult_conv_comp hd p.hs0 hsd hdL hPB (ult_U2Dec_mono hdec (by omega : 1 ≤ k + 1)) x).2 i
  have hci : ∀ i : Fin p.d, ContDiff ℝ k (ultK (u2_kap p.d p.s i) (R.ρ u)) ∧
      ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (ultK (u2_kap p.d p.s i) (R.ρ u)) x‖ ≤ Ci i * (P * B) * (1 + ‖x‖) ^ (-(p.s + 1 + j)) :=
    fun i => hCi i (P * B) (R.ρ u) hPB hdec
  have hcd : ContDiff ℝ k (convGradConvW (rieszKernelGrad p.d p.s) (R.ρ u)) := by
    refine contDiff_euclidean.2 fun i => ?_
    rw [hfun i]
    exact (hci i).1
  refine ⟨hcd, ?_⟩
  intro j hj x
  have hexp : (1 + ‖x‖) ^ (-(p.s + 1 + (j : ℝ))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg x])
      (by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith [p.hs0])
  have hbound : ∀ i : Fin p.d, ‖iteratedFDeriv ℝ j (fun y => convGradConvW (rieszKernelGrad p.d p.s) (R.ρ u) y i) x‖ ≤ Ci i * (P * B) := by
    intro i
    rw [hfun i]
    exact ((hci i).2 j hj x).trans (by nlinarith [mul_nonneg (hCi0 i) hPB])
  calc ‖iteratedFDeriv ℝ j (convGradConvW (rieszKernelGrad p.d p.s) (R.ρ u)) x‖
      ≤ ∑ i, ‖iteratedFDeriv ℝ j (fun y => convGradConvW (rieszKernelGrad p.d p.s) (R.ρ u) y i) x‖ :=
        fp81s21_b3_norm_iter_le_sum hcd hj x
    _ ≤ ∑ i, Ci i * (P * B) := Finset.sum_le_sum fun i _ => hbound i
    _ = C := by simp [C, Finset.sum_mul]

private theorem fp81s21_b3_id_jets {d : ℕ} (j : ℕ) (x : Euc d) :
    ‖iteratedFDeriv ℝ j (fun y : Euc d => y) x‖ ≤ jbracket x := by
  have h1 := HRS.MS.R2Poly.s95_one_le_jb x
  have hj : ‖x‖ ≤ jbracket x := by
    have hs := HRS.MS.R2Poly.s95_jb_sq x
    have hp : 0 ≤ jbracket x := by linarith
    nlinarith [norm_nonneg x]
  rcases j with _ | j
  · simpa using hj
  · rcases j with _ | j
    · rw [norm_iteratedFDeriv_one]
      simp only [fderiv_id']
      exact (ContinuousLinearMap.norm_id_le).trans h1
    · rw [← norm_iteratedFDeriv_fderiv]
      have he : fderiv ℝ (fun y : Euc d => y) = fun _ => ContinuousLinearMap.id ℝ (Euc d) := by
        funext y; exact fderiv_fun_id
      rw [he, iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, norm_zero]
      linarith

/-- The coefficient contract with both constants chosen before every trajectory. -/
theorem fp81s21_b3_coefficients (p : Parameters) :
    ∃ B c : ℝ, 0 ≤ B ∧ 0 < c ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 2 : ℝ) → ∀ R : Trajectory p δ,
        fp81s21_b3_Data R B c := by
  obtain ⟨Bρ, c, hBρ, hc, hρ⟩ := fp81s21_b3_rho_jets p
  obtain ⟨C, hC, hconv⟩ := fp81s21_b3_convolution_jets p
  let B := Bρ + C + |p.a|
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B, c, hB, hc, ?_⟩
  intro δ hδ hδhalf R u hu
  obtain ⟨hrc, hrb⟩ := hρ δ hδ hδhalf R u hu
  obtain ⟨hcc, hcb⟩ := hconv δ hδ hδhalf R u hu
  have heq : (r26t3_coeff R).drift u = fun x =>
      -convGradConvW (rieszKernelGrad p.d p.s) (R.ρ u) x - p.a • x := by
    funext x
    simp [r26t3_coeff, WholeDyn.coeff, quadraticGradientDyn, meanFieldDriftW,
      Torus.matVec, HRS.Whole.movtr_gradient_confinement]
  have hid : ContDiff ℝ (fp81s21_b3_q p) (fun x : Euc p.d => p.a • x) :=
    contDiff_id.const_smul p.a
  refine ⟨?_, ?_, hrc, ?_⟩
  · rw [heq]; exact hcc.neg.sub hid
  · intro j hj x
    have hcc' : ContDiffAt ℝ (j : WithTop ℕ∞) (convGradConvW (rieszKernelGrad p.d p.s) (R.ρ u)) x :=
      (hcc.of_le (by exact_mod_cast hj)).contDiffAt
    have hid' : ContDiffAt ℝ (j : WithTop ℕ∞) (fun x : Euc p.d => p.a • x) x :=
      (hid.of_le (by exact_mod_cast hj)).contDiffAt
    rw [heq]
    change ‖iteratedFDeriv ℝ j (-(convGradConvW (rieszKernelGrad p.d p.s) (R.ρ u)) -
      (p.a • (id : Euc p.d → Euc p.d))) x‖ ≤ B * jbracket x
    have hn : ContDiffAt ℝ (j : WithTop ℕ∞) (-(convGradConvW (rieszKernelGrad p.d p.s) (R.ρ u))) x := hcc'.neg
    have hs : ContDiffAt ℝ (j : WithTop ℕ∞) (p.a • (id : Euc p.d → Euc p.d)) x := hid'
    rw [iteratedFDeriv_sub_apply hn hs, iteratedFDeriv_neg_apply]
    rw [show (p.a • (id : Euc p.d → Euc p.d)) = (fun x : Euc p.d => p.a • x) from rfl]
    have hjet : iteratedFDeriv ℝ j (fun y : Euc p.d => p.a • y) x =
        p.a • iteratedFDeriv ℝ j (fun y : Euc p.d => y) x := by
      simpa only [id_eq] using
        (iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := p.a) (f := fun y : Euc p.d => y) (i := j) (x := x) (contDiff_id.contDiffAt))
    rw [hjet]
    have hbr : 1 ≤ jbracket x := HRS.MS.R2Poly.s95_one_le_jb x
    have hjb := fp81s21_b3_id_jets j x
    have hcb' := hcb j hj x
    calc _ ≤ ‖iteratedFDeriv ℝ j (convGradConvW (rieszKernelGrad p.d p.s) (R.ρ u)) x‖ +
        |p.a| * ‖iteratedFDeriv ℝ j (fun y : Euc p.d => y) x‖ := by
          simpa [norm_smul, Real.norm_eq_abs] using (norm_sub_le
            (-iteratedFDeriv ℝ j (convGradConvW (rieszKernelGrad p.d p.s) (R.ρ u)) x)
            (p.a • iteratedFDeriv ℝ j (fun y : Euc p.d => y) x))
      _ ≤ C + |p.a| * jbracket x := add_le_add hcb' (mul_le_mul_of_nonneg_left hjb (abs_nonneg _))
      _ ≤ B * jbracket x := by dsimp [B]; nlinarith [mul_nonneg hBρ (le_trans zero_le_one hbr)]
  · intro j hj x
    exact (hrb j hj x).trans (mul_le_mul_of_nonneg_right (by dsimp [B]; linarith [abs_nonneg p.a]) (Real.exp_pos _).le)

#print axioms HRS.Fp81.S21.fp81s21_b3_convolution_jets
#print axioms HRS.Fp81.S21.fp81s21_b3_coefficients

end HRS.Fp81.S21
