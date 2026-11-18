import HRS.MS.Fp81S21GaussG4U13
import HRS.MS.S111X2Aux8

/-! Bounds on the local generator and the gradient. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.Who HRS.MS.Ul

/-- The gradient has a reference-measure L² bound by the G4 cost. -/
theorem fp81s21_g4_gradient (p : Parameters) {δ : ℝ} (R : Trajectory p δ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ f, IsOscTest (wholeSpaceIndex p.d : ℝ) f →
      MemLp (gradient f) 2 (HRS.Whole.withDensityReal R.ρβ) ∧
      (∫ x, ‖gradient f x‖^2 ∂HRS.Whole.withDensityReal R.ρβ) ≤
        A * fp81s21_g4J p.d f := by
  let P : ℝ := 2 * (p.d : ℝ) + 4
  have hd0 : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
  have hP : 0 ≤ P := by dsimp [P]; linarith
  have hPd : (p.d : ℝ) / 2 < P := by dsimp [P]; linarith
  obtain ⟨C, hC, hc⟩ := fp81s21_g4_weight_to_reference p R hP
  refine ⟨C * (p.d : ℝ)^2, by positivity, ?_⟩
  intro f hf
  have hcb := fp81s21_g4_osc_cb2 p.d hf
  have hgrad : Continuous (gradient f) :=
    HRS.MS.S111X2.s111x2_gradient_continuous (hf.1.of_le (by simp))
  have heq : (fun x => ‖‖gradient f x‖‖) =
      (fun x => ‖iteratedFDeriv ℝ 1 f x‖) := by
    funext x
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_iteratedFDeriv_one]
    unfold gradient
    exact LinearIsometryEquiv.norm_map _ _
  have hcost : wSq P (fun x => ‖‖gradient f x‖‖) ≤
      ENNReal.ofReal ((p.d : ℝ)^2 * fp81s21_g4J p.d f) := by
    rw [heq]
    exact (who_wSq_le_Nsq (r := 1) (i := 1) le_rfl P f).trans (by
      simpa [P, fp81s21_g4J] using
        fp81s21_g4_Nsq_cost (le_trans (by decide) p.hd) hPd hcb)
  have hB : 0 ≤ (p.d : ℝ)^2 * fp81s21_g4J p.d f :=
    mul_nonneg (sq_nonneg _) (fp81s21_g4J_nonneg _ _)
  obtain ⟨hm, hi⟩ := hc (fun x => ‖gradient f x‖) hgrad.norm _ hB hcost
  refine ⟨(memLp_norm_iff hgrad.aestronglyMeasurable).1 hm, ?_⟩
  calc
    _ ≤ C * ((p.d : ℝ)^2 * fp81s21_g4J p.d f) := hi
    _ = _ := by ring

/-- Two derivatives in the operator-norm formulation are bounded by the
original tuple Sobolev cost. -/
theorem fp81s21_g4_Nsq2_cost {d : ℕ} (hd : 1 ≤ d) {P : ℝ}
    (hP : (d : ℝ) / 2 < P) {f : Euc d → ℝ} (hf : CbCls 2 f) :
    Nsq 2 P f ≤ ENNReal.ofReal ((d : ℝ)^2 * (weightedSobolevE 2 P f).toReal^2) := by
  obtain ⟨hfc, B, hB⟩ := hf
  have hN : Nsq 2 P f < ⊤ := who_Nsq_lt_top hP (fun j hj => ⟨B, hB j hj⟩)
  have hE : Esq 2 P f < ⊤ := lt_of_le_of_lt (who_Esq_le hd)
    (ENNReal.mul_lt_top (ENNReal.pow_lt_top (ENNReal.natCast_lt_top d)) hN)
  have hW : weightedSobolevE 2 P f < ⊤ := by
    rw [who_E_eq]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hE.ne
  have heq : Esq 2 P f = ENNReal.ofReal ((weightedSobolevE 2 P f).toReal ^ 2) := by
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hW.ne, who_E_eq,
      ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  calc
    Nsq 2 P f ≤ (d : ℝ≥0∞)^2 * Esq 2 P f := who_Nsq_le hd hfc
    _ = _ := by rw [heq, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- The Laplacian belongs to reference L² and is bounded by the G4 cost. -/
theorem fp81s21_g4_laplacian (p : Parameters) {δ : ℝ} (R : Trajectory p δ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ f, IsOscTest (wholeSpaceIndex p.d : ℝ) f →
      MemLp (Laplacian.laplacian f) 2 (HRS.Whole.withDensityReal R.ρβ) ∧
      (∫ x, (Laplacian.laplacian f x)^2 ∂HRS.Whole.withDensityReal R.ρβ) ≤
        A * fp81s21_g4J p.d f := by
  let P : ℝ := 2 * (p.d : ℝ) + 4
  have hd0 : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
  have hP : 0 ≤ P := by dsimp [P]; linarith
  have hPd : (p.d : ℝ) / 2 < P := by dsimp [P]; linarith
  obtain ⟨C, hC, hc⟩ := fp81s21_g4_weight_to_reference p R hP
  refine ⟨C * ((p.d : ℝ)^2 * (p.d : ℝ)^2), by positivity, ?_⟩
  intro f hf
  have hcb := fp81s21_g4_osc_cb2 p.d hf
  have hlap := who_lap_iter (i := 0) hcb.1
  have hcont : Continuous (Laplacian.laplacian f) := hlap.1.continuous
  have hpoint : ∀ x, ‖Laplacian.laplacian f x‖ ≤
      (p.d : ℝ) * ‖iteratedFDeriv ℝ 2 f x‖ := by
    intro x
    simpa using hlap.2 x
  have hcost : wSq P (fun x => ‖Laplacian.laplacian f x‖) ≤
      ENNReal.ofReal ((p.d : ℝ)^2 * (p.d : ℝ)^2 * fp81s21_g4J p.d f) := by
    calc
      _ ≤ wSq P (fun x => (p.d : ℝ) * ‖iteratedFDeriv ℝ 2 f x‖) :=
        who_wSq_mono fun x => pow_le_pow_left₀ (norm_nonneg _) (hpoint x) 2
      _ = ENNReal.ofReal ((p.d : ℝ)^2) * wSq P (fun x => ‖iteratedFDeriv ℝ 2 f x‖) :=
        who_wSq_smul P _ _
      _ ≤ ENNReal.ofReal ((p.d : ℝ)^2) * Nsq 2 P f :=
        mul_le_mul' le_rfl (who_wSq_le_Nsq le_rfl P f)
      _ ≤ ENNReal.ofReal ((p.d : ℝ)^2) * ENNReal.ofReal ((p.d : ℝ)^2 * fp81s21_g4J p.d f) := by
        apply mul_le_mul' le_rfl
        simpa [P, fp81s21_g4J] using fp81s21_g4_Nsq2_cost (le_trans (by decide) p.hd) hPd hcb
      _ = _ := by rw [← ENNReal.ofReal_mul (sq_nonneg _)]; congr 1; ring
  have hB : 0 ≤ (p.d : ℝ)^2 * (p.d : ℝ)^2 * fp81s21_g4J p.d f :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (fp81s21_g4J_nonneg _ _)
  obtain ⟨hm, hi⟩ := hc _ hcont _ hB hcost
  refine ⟨hm, ?_⟩
  calc _ ≤ C * ((p.d : ℝ)^2 * (p.d : ℝ)^2 * fp81s21_g4J p.d f) := hi
       _ = _ := by ring

/-- The full moving drift is continuous and has time-uniform linear growth. -/
theorem fp81s21_g4_drift_growth (p : Parameters) {δ : ℝ} (R : Trajectory p δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ q : ℝ, 0 ≤ q →
      Continuous ((r26t3_coeff R).drift q) ∧
      ∀ x, ‖(r26t3_coeff R).drift q x‖ ≤ B * jbracket x := by
  have hd : 1 ≤ p.d := le_trans (by decide) p.hd
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  let n : ℕ := 2 * p.d + 5
  have hn : (p.d : ℝ) + 0 + p.s + 3 < (n : ℝ) := by
    dsimp [n]; push_cast
    have hd0 : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
    linarith [p.hs]
  have hnd : (p.d : ℝ) < (n : ℝ) := by linarith [p.hs0]
  obtain ⟨A, hA, hρ⟩ := fp81s21_g4_density_decay p R n
  choose C hC hcore using fun k : Fin p.d => ult_core hd (ult_ker_kap p.hs0 hsd k) 0 (L := (n : ℝ)) (by simpa using hn)
  let B : ℝ := (∑ k, C k) * A + |p.a|
  have hB : 0 ≤ B := by
    dsimp [B]
    exact add_nonneg (mul_nonneg (Finset.sum_nonneg fun k _ => hC k) hA) (abs_nonneg _)
  refine ⟨B, hB, fun q hq => ?_⟩
  have hfun : ∀ k : Fin p.d, (fun x => (convGradConvW (rieszKernelGrad p.d p.s) (R.ρ q) x) k) =
      ultK (u2_kap p.d p.s k) (R.ρ q) := by
    intro k
    funext x
    exact (ult_conv_comp hd p.hs0 hsd hnd hA (hρ q hq) x).2 k
  have hcont : Continuous (convGradConvW (rieszKernelGrad p.d p.s) (R.ρ q)) := by
    have hcd : ContDiff ℝ 0 (convGradConvW (rieszKernelGrad p.d p.s) (R.ρ q)) := by
      refine contDiff_euclidean.2 fun k => ?_
      rw [hfun k]
      exact (hcore k A (R.ρ q) hA (hρ q hq)).1
    exact hcd.continuous
  have hforce : ∀ x, ‖convGradConvW (rieszKernelGrad p.d p.s) (R.ρ q) x‖ ≤ (∑ k, C k) * A := by
    intro x
    calc
      _ ≤ ∑ k : Fin p.d, |(convGradConvW (rieszKernelGrad p.d p.s) (R.ρ q) x) k| := ult_norm_le_sum_abs _
      _ ≤ ∑ k : Fin p.d, C k * A := by
        refine Finset.sum_le_sum fun k _ => ?_
        have h := (hcore k A (R.ρ q) hA (hρ q hq)).2 0 le_rfl x
        have hw : (1 + ‖x‖) ^ (-(p.s + 1 + (0 : ℝ))) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg x]) (by linarith [p.hs0])
        have h' : ‖ultK (u2_kap p.d p.s k) (R.ρ q) x‖ ≤ C k * A := by
          have := mul_le_mul_of_nonneg_left hw (mul_nonneg (hC k) hA)
          calc
            _ ≤ C k * A * (1 + ‖x‖) ^ (-(p.s + 1 + (0 : ℝ))) := by simpa using h
            _ ≤ C k * A := by simpa using this
        rw [show (convGradConvW (rieszKernelGrad p.d p.s) (R.ρ q) x) k =
          ultK (u2_kap p.d p.s k) (R.ρ q) x from congrFun (hfun k) x]
        simpa [Real.norm_eq_abs] using h'
      _ = _ := by rw [Finset.sum_mul]
  have hform : (r26t3_coeff R).drift q = fun x =>
      -convGradConvW (rieszKernelGrad p.d p.s) (R.ρ q) x - p.a • x := by
    funext x
    simp [r26t3_coeff, WholeDyn.coeff, quadraticGradientDyn, meanFieldDriftW,
      Torus.matVec, HRS.Whole.movtr_gradient_confinement]
  rw [hform]
  have hs : Continuous (fun x : Euc p.d => p.a • x) := continuous_id.const_smul p.a
  refine ⟨hcont.neg.sub hs, fun x => ?_⟩
  have hj : 1 ≤ jbracket x := who_one_le_jb x
  have hx : ‖x‖ ≤ jbracket x := by
    have hs := who_jb_sq x
    have hp := norm_nonneg x
    nlinarith
  calc
    ‖-convGradConvW (rieszKernelGrad p.d p.s) (R.ρ q) x - p.a • x‖ ≤
        ‖convGradConvW (rieszKernelGrad p.d p.s) (R.ρ q) x‖ + |p.a| * ‖x‖ := by
          simpa [norm_smul, Real.norm_eq_abs] using norm_sub_le
            (-convGradConvW (rieszKernelGrad p.d p.s) (R.ρ q) x) (p.a • x)
    _ ≤ (∑ k, C k) * A + |p.a| * ‖x‖ := by gcongr; exact hforce x
    _ ≤ B * jbracket x := by
      dsimp [B]
      have hCA : 0 ≤ (∑ k, C k) * A := mul_nonneg (Finset.sum_nonneg fun k _ => hC k) hA
      nlinarith [mul_le_mul_of_nonneg_left hj hCA, mul_le_mul_of_nonneg_left hx (abs_nonneg p.a)]

/-- The local drift pairing is uniformly bounded in reference L². -/
theorem fp81s21_g4_drift (p : Parameters) {δ : ℝ} (R : Trajectory p δ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ q, 0 ≤ q → ∀ f,
      IsOscTest (wholeSpaceIndex p.d : ℝ) f →
      MemLp (fun x => inner ℝ ((r26t3_coeff R).drift q x) (gradient f x))
        2 (HRS.Whole.withDensityReal R.ρβ) ∧
      (∫ x, (inner ℝ ((r26t3_coeff R).drift q x) (gradient f x))^2
        ∂HRS.Whole.withDensityReal R.ρβ) ≤ A * fp81s21_g4J p.d f := by
  let P : ℝ := 2 * (p.d : ℝ) + 4
  have hd0 : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
  have hP : 0 ≤ P := by dsimp [P]; linarith
  have hPd : (p.d : ℝ) / 2 < P := by dsimp [P]; linarith
  obtain ⟨B, hB, hb⟩ := fp81s21_g4_drift_growth p R
  obtain ⟨C, hC, hc⟩ := fp81s21_g4_weight_to_reference p R (P := P + 1) (by linarith)
  refine ⟨C * (B^2 * (p.d : ℝ)^2), by positivity, ?_⟩
  intro q hq f hf
  have hcb := fp81s21_g4_osc_cb2 p.d hf
  have hgrad : Continuous (gradient f) :=
    HRS.MS.S111X2.s111x2_gradient_continuous (hf.1.of_le (by simp))
  have hg : Continuous (fun x => inner ℝ ((r26t3_coeff R).drift q x) (gradient f x)) :=
    (hb q hq).1.inner hgrad
  have hwt : ∀ x : Euc p.d, wt (P + 1) x * jbracket x ^ 2 = wt P x := by
    intro x
    unfold wt
    rw [← Real.rpow_natCast, ← Real.rpow_add (by linarith [who_one_le_jb x] : 0 < jbracket x)]
    congr 1
    ring
  have hpoint : ∀ x, ‖inner ℝ ((r26t3_coeff R).drift q x) (gradient f x)‖ ≤
      B * jbracket x * ‖gradient f x‖ := fun x =>
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ((hb q hq).2 x) (norm_nonneg _))
  have hgradW : wSq P (fun x => ‖gradient f x‖) ≤
      ENNReal.ofReal ((p.d : ℝ)^2 * fp81s21_g4J p.d f) := by
    have heq : (fun x => ‖gradient f x‖) = (fun x => ‖iteratedFDeriv ℝ 1 f x‖) := by
      funext x
      rw [norm_iteratedFDeriv_one]
      unfold gradient
      exact LinearIsometryEquiv.norm_map _ _
    rw [heq]
    exact (who_wSq_le_Nsq (r := 1) (i := 1) le_rfl P f).trans (by
      simpa [P, fp81s21_g4J] using
        fp81s21_g4_Nsq_cost (le_trans (by decide) p.hd) hPd hcb)
  have hw : wSq (P + 1) (fun x => ‖inner ℝ ((r26t3_coeff R).drift q x) (gradient f x)‖) ≤
      ENNReal.ofReal (B^2) * wSq P (fun x => ‖gradient f x‖) := by
    unfold wSq
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro x
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (sq_nonneg B)]
    apply ENNReal.ofReal_le_ofReal
    have hv := pow_le_pow_left₀ (norm_nonneg _) (hpoint x) 2
    have hwp := (who_wt_pos (P + 1) x).le
    have := mul_le_mul_of_nonneg_left hv hwp
    calc
      _ ≤ wt (P + 1) x * (B * jbracket x * ‖gradient f x‖)^2 := this
      _ = B^2 * (wt (P + 1) x * jbracket x ^ 2) * ‖gradient f x‖^2 := by ring
      _ = B^2 * (wt P x * ‖gradient f x‖^2) := by rw [hwt]; ring
  have hcost : wSq (P + 1) (fun x => ‖inner ℝ ((r26t3_coeff R).drift q x) (gradient f x)‖) ≤
      ENNReal.ofReal (B^2 * (p.d : ℝ)^2 * fp81s21_g4J p.d f) := by
    calc
      _ ≤ ENNReal.ofReal (B^2) * wSq P (fun x => ‖gradient f x‖) := hw
      _ ≤ ENNReal.ofReal (B^2) * ENNReal.ofReal ((p.d : ℝ)^2 * fp81s21_g4J p.d f) :=
        mul_le_mul' le_rfl hgradW
      _ = _ := by rw [← ENNReal.ofReal_mul (sq_nonneg _)]; congr 1; ring
  have hcost0 : 0 ≤ B^2 * (p.d : ℝ)^2 * fp81s21_g4J p.d f :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (fp81s21_g4J_nonneg _ _)
  obtain ⟨hm, hi⟩ := hc _ hg _ hcost0 hcost
  refine ⟨hm, ?_⟩
  calc _ ≤ C * (B^2 * (p.d : ℝ)^2 * fp81s21_g4J p.d f) := hi
       _ = _ := by ring

/-- Scalar generator and gradient estimates, uniform over nonnegative times. -/
theorem fp81s21_g4_generator (p : Parameters) :
    fp81s21_g4Phys p (fun _ R =>
      ∃ A : ℝ, 0 ≤ A ∧ ∀ q, 0 ≤ q → ∀ f,
        IsOscTest (wholeSpaceIndex p.d : ℝ) f →
        MemLp (generatorW (r26t3_coeff R) q f) 2 (HRS.Whole.withDensityReal R.ρβ) ∧
        MemLp (gradient f) 2 (HRS.Whole.withDensityReal R.ρβ) ∧
        (∫ x, (generatorW (r26t3_coeff R) q f x)^2 ∂HRS.Whole.withDensityReal R.ρβ) +
        (∫ x, ‖gradient f x‖^2 ∂HRS.Whole.withDensityReal R.ρβ) ≤
          A * fp81s21_g4J p.d f) := by
  obtain ⟨δ0, hδ0, hδhalf, hN⟩ := fp81s21_g4_nonlocal p
  refine ⟨δ0, hδ0, hδhalf, ?_⟩
  intro δ hδ hδle R
  obtain ⟨N, hN0, hNb⟩ := hN δ hδ hδle R
  obtain ⟨L, hL0, hLb⟩ := fp81s21_g4_laplacian p R
  obtain ⟨D, hD0, hDb⟩ := fp81s21_g4_drift p R
  obtain ⟨G, hG0, hGb⟩ := fp81s21_g4_gradient p R
  let ν := (r26t3_coeff R).ν
  refine ⟨3 * (ν^2 * L + D + N) + G, by positivity, ?_⟩
  intro q hq f hf
  obtain ⟨hNm, hNi⟩ := hNb q hq f hf
  obtain ⟨hLm, hLi⟩ := hLb f hf
  obtain ⟨hDm, hDi⟩ := hDb q hq f hf
  obtain ⟨hGm, hGi⟩ := hGb f hf
  let l : Euc p.d → ℝ := Laplacian.laplacian f
  let b : Euc p.d → ℝ := fun x => inner ℝ ((r26t3_coeff R).drift q x) (gradient f x)
  let n : Euc p.d → ℝ := fp81s21_g4N p R q f
  have heq : generatorW (r26t3_coeff R) q f = fun x => ν * l x + b x - n x := by
    funext x
    exact fp81s21_g4_generator_eq p R q f x
  have hgen : MemLp (generatorW (r26t3_coeff R) q f) 2 (HRS.Whole.withDensityReal R.ρβ) := by
    rw [heq]
    exact ((hLm.const_mul ν).add hDm).sub hNm
  have hlsq : Integrable (fun x => (l x)^2) (HRS.Whole.withDensityReal R.ρβ) :=
    (memLp_two_iff_integrable_sq hLm.aestronglyMeasurable).1 hLm
  have hbsq : Integrable (fun x => (b x)^2) (HRS.Whole.withDensityReal R.ρβ) :=
    (memLp_two_iff_integrable_sq hDm.aestronglyMeasurable).1 hDm
  have hnsq : Integrable (fun x => (n x)^2) (HRS.Whole.withDensityReal R.ρβ) :=
    (memLp_two_iff_integrable_sq hNm.aestronglyMeasurable).1 hNm
  have hgsq : Integrable (fun x => (generatorW (r26t3_coeff R) q f x)^2)
      (HRS.Whole.withDensityReal R.ρβ) :=
    (memLp_two_iff_integrable_sq hgen.aestronglyMeasurable).1 hgen
  have hdom : Integrable (fun x => 3 * (ν^2 * (l x)^2 + (b x)^2 + (n x)^2))
      (HRS.Whole.withDensityReal R.ρβ) := ((hlsq.const_mul (ν^2)).add hbsq |>.add hnsq).const_mul 3
  have hmain : (∫ x, (generatorW (r26t3_coeff R) q f x)^2 ∂HRS.Whole.withDensityReal R.ρβ) ≤
      3 * (ν^2 * (∫ x, (l x)^2 ∂HRS.Whole.withDensityReal R.ρβ) +
        (∫ x, (b x)^2 ∂HRS.Whole.withDensityReal R.ρβ) +
        (∫ x, (n x)^2 ∂HRS.Whole.withDensityReal R.ρβ)) := by
    calc
      _ ≤ ∫ x, 3 * (ν^2 * (l x)^2 + (b x)^2 + (n x)^2) ∂HRS.Whole.withDensityReal R.ρβ := by
        apply integral_mono hgsq hdom
        intro x
        rw [heq]
        nlinarith [sq_nonneg (ν * l x - b x), sq_nonneg (ν * l x + n x), sq_nonneg (b x + n x)]
      _ = _ := by
        rw [integral_const_mul]
        have hs1 : (∫ x, ν^2 * (l x)^2 + (b x)^2 + (n x)^2 ∂HRS.Whole.withDensityReal R.ρβ) =
            (∫ x, ν^2 * (l x)^2 + (b x)^2 ∂HRS.Whole.withDensityReal R.ρβ) +
              (∫ x, (n x)^2 ∂HRS.Whole.withDensityReal R.ρβ) := by
          simpa only [Pi.add_apply] using integral_add ((hlsq.const_mul (ν^2)).add hbsq) hnsq
        have hs2 : (∫ x, ν^2 * (l x)^2 + (b x)^2 ∂HRS.Whole.withDensityReal R.ρβ) =
            (∫ x, ν^2 * (l x)^2 ∂HRS.Whole.withDensityReal R.ρβ) +
              (∫ x, (b x)^2 ∂HRS.Whole.withDensityReal R.ρβ) := by
          simpa only [Pi.add_apply] using integral_add (hlsq.const_mul (ν^2)) hbsq
        rw [hs1, hs2, integral_const_mul]
  refine ⟨hgen, hGm, ?_⟩
  have hmul := mul_le_mul_of_nonneg_left hLi (sq_nonneg ν)
  have hJ := fp81s21_g4J_nonneg p.d f
  dsimp [l, b, n] at hmain
  nlinarith

#print axioms HRS.Fp81.S21.fp81s21_g4_generator
#print axioms HRS.Fp81.S21.fp81s21_g4_drift
#print axioms HRS.Fp81.S21.fp81s21_g4_drift_growth
#print axioms HRS.Fp81.S21.fp81s21_g4_laplacian
#print axioms HRS.Fp81.S21.fp81s21_g4_Nsq2_cost
#print axioms HRS.Fp81.S21.fp81s21_g4_gradient
end HRS.Fp81.S21
