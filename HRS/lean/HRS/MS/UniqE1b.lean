import HRS.MS.UniqE1

/-!
# E1 of `UniqPlan.md`, part 2: the bound `|f_ε(σ,x)| ≤ C(ε) B (1+|x|)`

* `e1_fp_eq` : `forwardPairing D ρ t σ u ψ_x` as the three integrals `∫ u R1`, `∫ u R2`, `∫ u R3` of
  packet T3 (`fp_formula` with the profile `θ(v) = η_ε(-v)`, `ψ_x = θ(· - x)`).
* `e1_bound` : for `LocMass B u` and `σ ∈ [0,t]`, `|forwardPairing D ρ t σ u ψ_x| ≤ C B (1+|x|)`,
  `C = C(d, D, ε, MB, Λ, ΛV, G₀, m)` independent of `u, B, σ, x`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqE1

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqM1 HRS.MS.UniqT3

variable {d : ℕ}

/-- The profile `θ(v) = η_ε(-v)`, so that `ψ_x = θ(· - x)`. -/
def th (d : ℕ) (ε : ℝ) : Euc d → ℝ := fun v => eta d ε (-v)

theorem th_cc {ε : ℝ} (hε : 0 < ε) : Cc (th d ε) :=
  ⟨eta_contDiff.comp contDiff_neg, (eta_hasCompactSupport hε).comp_homeomorph (Homeomorph.neg (Euc d))⟩

theorem psi_eq_th (ε : ℝ) (x : Euc d) : (fun y : Euc d => eta d ε (x - y)) = fun y => th d ε (y - x) := by
  funext y; simp [th, neg_sub]

/-- Vanishing off the closed ball `closedBall 0 ε`. -/
def Vn (ε : ℝ) (φ : Euc d → ℝ) : Prop := ∀ v : Euc d, ε < ‖v‖ → φ v = 0

theorem th_vn {ε : ℝ} (hε : 0 < ε) : Vn ε (th d ε) := by
  intro v hv
  by_contra h
  have : -v ∈ ball (0 : Euc d) ε := eta_support hε (Function.mem_support.2 h)
  rw [mem_ball_zero_iff, norm_neg] at this
  linarith

theorem Vn.D1 {ε : ℝ} {φ : Euc d → ℝ} (h : Vn ε φ) (i : Fin d) : Vn ε (HRS.MS.UniqT3.D1 i φ) := by
  intro v hv
  have hev : φ =ᶠ[𝓝 v] fun _ => 0 := by
    have : {w : Euc d | ε < ‖w‖} ∈ 𝓝 v := (isOpen_lt continuous_const continuous_norm).mem_nhds hv
    filter_upwards [this] with w hw using h w hw
  unfold HRS.MS.UniqT3.D1
  rw [hev.fderiv_eq]
  simp

theorem exists_uniform_bound {ι : Type*} [Fintype ι] (φ : ι → Euc d → ℝ)
    (h : ∀ i, ∃ M : ℝ, ∀ v, |φ i v| ≤ M) : ∃ M : ℝ, 0 ≤ M ∧ ∀ i v, |φ i v| ≤ M := by
  choose M hM using h
  refine ⟨∑ i, |M i|, Finset.sum_nonneg fun i _ => abs_nonneg _, fun i v => ?_⟩
  exact (hM i v).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun i => |M i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)))

theorem cc_bdd {φ : Euc d → ℝ} (h : Cc φ) : ∃ M : ℝ, ∀ v, |φ v| ≤ M := by
  obtain ⟨M, hM⟩ := h.cont.bounded_above_of_compact_support h.supp
  exact ⟨M, fun v => by simpa [Real.norm_eq_abs] using hM v⟩

/-- Uniform bounds on `θ`, `D1 i θ`, `D1 j (D1 i θ)` (one constant `Θ`). -/
theorem th_bounds {ε : ℝ} (hε : 0 < ε) : ∃ Θ : ℝ, 0 ≤ Θ ∧ (∀ v, |th d ε v| ≤ Θ) ∧
    (∀ i v, |HRS.MS.UniqT3.D1 i (th d ε) v| ≤ Θ) ∧
    (∀ i j v, |HRS.MS.UniqT3.D1 j (HRS.MS.UniqT3.D1 i (th d ε)) v| ≤ Θ) := by
  have hθ := th_cc (d := d) hε
  obtain ⟨M0, hM0⟩ := cc_bdd hθ
  obtain ⟨M1, hM1, h1⟩ := exists_uniform_bound (ι := Fin d) (fun i => HRS.MS.UniqT3.D1 i (th d ε))
    (fun i => cc_bdd (hθ.D1 i))
  obtain ⟨M2, hM2, h2⟩ := exists_uniform_bound (ι := Fin d × Fin d)
    (fun p => HRS.MS.UniqT3.D1 p.2 (HRS.MS.UniqT3.D1 p.1 (th d ε)))
    (fun p => cc_bdd ((hθ.D1 p.1).D1 p.2))
  have hM0' : 0 ≤ M0 := (abs_nonneg _).trans (hM0 0)
  refine ⟨M0 + M1 + M2, by positivity, fun v => ?_, fun i v => ?_, fun i j v => ?_⟩
  · linarith [hM0 v]
  · linarith [h1 i v]
  · linarith [h2 (i, j) v]

/-- Bounds `|K(D1 i θ)(r)| ≤ CK (1+|r|)` and `|K(D1 j (D1 i θ))(r)| ≤ CK (1+|r|)` for `K = g * ·`. -/
theorem th_conv_bounds {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε) :
    ∃ CK : ℝ, 0 ≤ CK ∧
    (∀ i r, |HRS.Whole.convFun (rieszKernel d s) (HRS.MS.UniqT3.D1 i (th d ε)) r| ≤ CK * (1 + ‖r‖)) ∧
    (∀ i j r, |HRS.Whole.convFun (rieszKernel d s) (HRS.MS.UniqT3.D1 j (HRS.MS.UniqT3.D1 i (th d ε))) r| ≤
      CK * (1 + ‖r‖)) := by
  have hθ := th_cc (d := d) hε
  have key : ∀ {ι : Type} [Fintype ι] (φ : ι → Euc d → ℝ), (∀ i, Cc (φ i)) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i r, |HRS.Whole.convFun (rieszKernel d s) (φ i) r| ≤ C * (1 + ‖r‖) := by
    intro ι _ φ hφ
    choose C hC using fun i => conv_bound hs0 hsd (hφ i).cont (hφ i).supp
    refine ⟨∑ i, |C i|, Finset.sum_nonneg fun i _ => abs_nonneg _, fun i r => ?_⟩
    refine (hC i r).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |C i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)))
      (by positivity))
  obtain ⟨C1, hC1, h1⟩ := key (ι := Fin d) (fun i => HRS.MS.UniqT3.D1 i (th d ε)) (fun i => hθ.D1 i)
  obtain ⟨C2, hC2, h2⟩ := key (ι := Fin d × Fin d)
    (fun p => HRS.MS.UniqT3.D1 p.2 (HRS.MS.UniqT3.D1 p.1 (th d ε))) (fun p => (hθ.D1 p.1).D1 p.2)
  refine ⟨C1 + C2, by positivity, fun i r => ?_, fun i j r => ?_⟩
  · exact (h1 i r).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · exact (h2 (i, j) r).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

/-! ### The decomposition of `forwardPairing` against `ψ_x` -/

theorem e1_fp_eq (D : WholeDyn d) (ρ : ℝ → Euc d → ℝ) (t σ : ℝ) (hs0 : 0 ≤ D.s) (hsd : D.s < d)
    (hb : ∀ i, ContDiff ℝ 1 (fun y => meanFieldDriftW D (ρ (t - σ)) y i))
    (hρ : ContDiff ℝ 1 (ρ (t - σ))) (u : Euc d → ℝ) {ε : ℝ} (hε : 0 < ε) (x : Euc d) :
    forwardPairing D ρ t σ u (fun y => eta d ε (x - y)) =
      D.invβ * (∫ y, u y * R1 (th d ε) x y) -
        (∫ y, u y * R2 (fun i y => meanFieldDriftW D (ρ (t - σ)) y i) (th d ε) x y) -
        ∑ i, ∑ j, D.M j i * (∫ y, u y * R3 D.s (ρ (t - σ)) (th d ε) i j x y) := by
  have hθ := th_cc (d := d) hε
  have hsm : ContDiff ℝ 2 (fun y => th d ε (y - x)) :=
    (hθ.smooth.comp (contDiff_id.sub contDiff_const)).of_le (by simp)
  have hsp : HasCompactSupport (fun y => th d ε (y - x)) :=
    hθ.supp.comp_homeomorph (Homeomorph.subRight x)
  rw [psi_eq_th ε x, fp_formula D ρ t σ hs0 hsd u hsm hsp hb hρ]
  simp only [D1_shift, conv_shift, R1, R2, R3]

/-! ### Coefficient facts at a fixed time -/

theorem e1_drift_coord {m : ℕ} {Cb : ℝ} {f : Euc d → Euc d} (hf : HRS.MS.UniqC1.AdvBounds m Cb f)
    (i : Fin d) :
    ContDiff ℝ 1 (fun y => f y i) ∧ (∀ y, |HRS.MS.UniqT3.D1 i (fun y => f y i) y| ≤ Cb) ∧
      (∀ y, |f y i| ≤ Cb * (1 + ‖y‖)) := by
  have hsm : ContDiff ℝ (m + 1 : ℕ) f := by exact_mod_cast hf.smooth
  have hci : ContDiff ℝ (m + 1 : ℕ) (fun y => f y i) := contDiff_euclidean.1 hsm i
  refine ⟨hci.of_le (by exact_mod_cast (by omega : 1 ≤ m + 1)), fun y => ?_, fun y => ?_⟩
  · have hd : DifferentiableAt ℝ f y := (hsm.differentiable (by simp)) y
    have h1 : fderiv ℝ (fun y => f y i) y =
        (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).comp (fderiv ℝ f y) :=
      ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasFDerivAt.comp y hd.hasFDerivAt).fderiv
    unfold HRS.MS.UniqT3.D1
    rw [h1]
    have h2 := hf.deriv_bdd 1 le_rfl (by omega) y
    rw [norm_iteratedFDeriv_one] at h2
    simp only [ContinuousLinearMap.comp_apply]
    change |(fderiv ℝ f y (EuclideanSpace.single i 1)) i| ≤ Cb
    calc |(fderiv ℝ f y (EuclideanSpace.single i 1)) i| ≤ ‖fderiv ℝ f y (EuclideanSpace.single i 1)‖ := by
          simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (fderiv ℝ f y (EuclideanSpace.single i 1)) i
      _ ≤ ‖fderiv ℝ f y‖ * ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ Cb := by simpa using h2
  · calc |f y i| ≤ ‖f y‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (f y) i
      _ ≤ _ := hf.growth y

theorem wt_mul_aux (y : Euc d) : (1 + ‖y‖) ^ (-((d : ℝ) + 3)) * (1 + ‖y‖) = wt d y := by
  unfold wt
  rw [← Real.rpow_add_one (by positivity)]
  congr 1; ring

theorem e1_rho_smooth {s : ℝ} {m : ℕ} {Λ T : ℝ} {ρ : ℝ → Euc d → ℝ}
    (hcoef : CoeffHypRd s m Λ T ρ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) : ContDiff ℝ 1 (ρ r) :=
  (hcoef.regular.1 r hr).1.1.of_le (by exact_mod_cast (by omega : 1 ≤ m + 3))

/-! ### Pointwise bounds on the three kernels `R1`, `R2`, `R3` -/

theorem e1_R1_vanish {ε : ℝ} (hε : 0 < ε) {x y : Euc d} (h : ε < ‖y - x‖) :
    R1 (th d ε) x y = 0 := by
  simp only [R1]
  exact Finset.sum_eq_zero fun i _ => (((th_vn hε).D1 i).D1 i) _ h

theorem e1_R1_abs {ε Θ : ℝ} (hΘ2 : ∀ i j v, |HRS.MS.UniqT3.D1 j (HRS.MS.UniqT3.D1 i (th d ε)) v| ≤ Θ)
    (x y : Euc d) : |R1 (th d ε) x y| ≤ d * Θ := by
  simp only [R1]
  calc |∑ i, HRS.MS.UniqT3.D1 i (HRS.MS.UniqT3.D1 i (th d ε)) (y - x)|
      ≤ ∑ i, |HRS.MS.UniqT3.D1 i (HRS.MS.UniqT3.D1 i (th d ε)) (y - x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin d, Θ := Finset.sum_le_sum fun i _ => hΘ2 i i _
    _ = d * Θ := by simp

theorem e1_R2_vanish {ε : ℝ} (hε : 0 < ε) (b : Fin d → Euc d → ℝ) {x y : Euc d}
    (h : ε < ‖y - x‖) : R2 b (th d ε) x y = 0 := by
  simp only [R2]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [(th_vn hε) _ h, ((th_vn hε).D1 i) _ h]; ring

theorem e1_R2_abs {ε Θ Cb : ℝ} (hε : 0 < ε) (hΘ0 : 0 ≤ Θ) (hCb0 : 0 ≤ Cb)
    (hΘ0' : ∀ v, |th d ε v| ≤ Θ) (hΘ1 : ∀ i v, |HRS.MS.UniqT3.D1 i (th d ε) v| ≤ Θ)
    (b : Fin d → Euc d → ℝ) (hb1 : ∀ i y, |HRS.MS.UniqT3.D1 i (b i) y| ≤ Cb)
    (hb0 : ∀ i y, |b i y| ≤ Cb * (1 + ‖y‖)) (x y : Euc d) :
    |R2 b (th d ε) x y| ≤ (d * (Cb * Θ * (2 + ε))) * (1 + ‖x‖) := by
  by_cases hy : ‖y - x‖ ≤ ε
  · have hyx : ‖y‖ ≤ ‖x‖ + ε := by
      have := norm_le_norm_add_norm_sub' y x
      linarith
    simp only [R2]
    calc |∑ i, (HRS.MS.UniqT3.D1 i (b i) y * th d ε (y - x) + b i y * HRS.MS.UniqT3.D1 i (th d ε) (y - x))|
        ≤ ∑ i, |HRS.MS.UniqT3.D1 i (b i) y * th d ε (y - x) + b i y * HRS.MS.UniqT3.D1 i (th d ε) (y - x)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin d, (Cb * Θ * (2 + ε)) * (1 + ‖x‖) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have e1 := hb1 i y
          have e2 := hb0 i y
          have e3 := hΘ0' (y - x)
          have e4 := hΘ1 i (y - x)
          calc _ ≤ |HRS.MS.UniqT3.D1 i (b i) y * th d ε (y - x)| + |b i y * HRS.MS.UniqT3.D1 i (th d ε) (y - x)| :=
                abs_add_le _ _
            _ = |HRS.MS.UniqT3.D1 i (b i) y| * |th d ε (y - x)| + |b i y| * |HRS.MS.UniqT3.D1 i (th d ε) (y - x)| := by
                rw [abs_mul, abs_mul]
            _ ≤ Cb * Θ + (Cb * (1 + ‖y‖)) * Θ := by
                gcongr
            _ ≤ (Cb * Θ * (2 + ε)) * (1 + ‖x‖) := by
                have hn := norm_nonneg x
                have : Cb * Θ * (1 + ‖y‖ + 1) ≤ Cb * Θ * ((2 + ε) * (1 + ‖x‖)) := by
                  apply mul_le_mul_of_nonneg_left _ (by positivity)
                  nlinarith [norm_nonneg x]
                nlinarith [this]
      _ = _ := by simp; ring
  · rw [e1_R2_vanish hε b (not_le.1 hy), abs_zero]
    have := norm_nonneg x
    positivity

theorem e1_R3_abs {s ε CK A : ℝ} {ρt : Euc d → ℝ} (hρ0 : ∀ y, |ρt y| ≤ A * (1 + ‖y‖) ^ (-((d : ℝ) + 3)))
    (hρ1 : ∀ y, ‖fderiv ℝ ρt y‖ ≤ A * (1 + ‖y‖) ^ (-((d : ℝ) + 3)))
    (hCK1 : ∀ i r, |HRS.Whole.convFun (rieszKernel d s) (HRS.MS.UniqT3.D1 i (th d ε)) r| ≤ CK * (1 + ‖r‖))
    (hCK2 : ∀ i j r, |HRS.Whole.convFun (rieszKernel d s) (HRS.MS.UniqT3.D1 j (HRS.MS.UniqT3.D1 i (th d ε))) r| ≤
      CK * (1 + ‖r‖))
    (i j : Fin d) (x y : Euc d) :
    |R3 s ρt (th d ε) i j x y| ≤ (A * (CK + CK) * (1 + ‖x‖)) * wt d y := by
  have hDρ : |HRS.MS.UniqT3.D1 j ρt y| ≤ A * (1 + ‖y‖) ^ (-((d : ℝ) + 3)) := by
    refine le_trans ?_ (hρ1 y)
    unfold HRS.MS.UniqT3.D1
    rw [← Real.norm_eq_abs]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    simp
  have hr1 : 1 + ‖y - x‖ ≤ (1 + ‖y‖) * (1 + ‖x‖) := by
    have := norm_sub_le y x
    nlinarith [norm_nonneg y, norm_nonneg x]
  have hX0 : 0 ≤ A * (1 + ‖y‖) ^ (-((d : ℝ) + 3)) := (abs_nonneg _).trans hDρ
  have hKi := hCK1 i (y - x)
  have hKij := hCK2 i j (y - x)
  have hCK0 : 0 ≤ CK := by
    have := (abs_nonneg _).trans (hCK1 i 0)
    simp only [norm_zero, add_zero, mul_one] at this
    exact this
  unfold R3
  calc |HRS.MS.UniqT3.D1 j ρt y * HRS.Whole.convFun (rieszKernel d s) (HRS.MS.UniqT3.D1 i (th d ε)) (y - x) +
        ρt y * HRS.Whole.convFun (rieszKernel d s) (HRS.MS.UniqT3.D1 j (HRS.MS.UniqT3.D1 i (th d ε))) (y - x)|
      ≤ |HRS.MS.UniqT3.D1 j ρt y| * |HRS.Whole.convFun (rieszKernel d s) (HRS.MS.UniqT3.D1 i (th d ε)) (y - x)| +
        |ρt y| * |HRS.Whole.convFun (rieszKernel d s) (HRS.MS.UniqT3.D1 j (HRS.MS.UniqT3.D1 i (th d ε))) (y - x)| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul]
    _ ≤ (A * (1 + ‖y‖) ^ (-((d : ℝ) + 3))) * (CK * (1 + ‖y - x‖)) +
        (A * (1 + ‖y‖) ^ (-((d : ℝ) + 3))) * (CK * (1 + ‖y - x‖)) := by
          exact add_le_add (mul_le_mul hDρ hKi (abs_nonneg _) hX0)
            (mul_le_mul (hρ0 y) hKij (abs_nonneg _) hX0)
    _ ≤ (A * (1 + ‖y‖) ^ (-((d : ℝ) + 3))) * (CK * ((1 + ‖y‖) * (1 + ‖x‖))) +
        (A * (1 + ‖y‖) ^ (-((d : ℝ) + 3))) * (CK * ((1 + ‖y‖) * (1 + ‖x‖))) := by
          gcongr
    _ = A * (CK + CK) * (1 + ‖x‖) * ((1 + ‖y‖) ^ (-((d : ℝ) + 3)) * (1 + ‖y‖)) := by ring
    _ = _ := by rw [wt_mul_aux]

/-! ### Coefficient facts at a fixed time -/

theorem e1_Cb_nonneg (hd : 1 ≤ d) {D : WholeDyn d} (hs0 : 0 ≤ D.s) (hsd : D.s < d) (m : ℕ)
    (MB Λ ΛV G₀ : ℝ) {ρ : ℝ → Euc d → ℝ} {T : ℝ}
    (hMB : HRS.PDE.MatBound MB D.M) (hV : VHypRd (m + 3) ΛV G₀ D.V)
    (hcoef : CoeffHypRd D.s m Λ T ρ) (hT : 0 ≤ T) :
    0 ≤ HRS.MS.UniqC1.c1Cb d D.s m MB Λ ΛV G₀ := by
  have h := (HRS.MS.UniqC1.c1_drift_single hd hs0 hsd m MB Λ ΛV G₀ rfl hMB hV hcoef
    (r := 0) ⟨le_rfl, hT⟩).growth 0
  rw [norm_zero, add_zero, mul_one] at h
  exact (norm_nonneg _).trans h

theorem e1_A_nonneg (m : ℕ) (Λ : ℝ) : 0 ≤ HRS.MS.UniqC1.c1A d m Λ := by
  unfold HRS.MS.UniqC1.c1A; positivity

/-- All the coefficient facts at the time `r = t - σ ∈ [0,T]`, with the constants
`Cb = c1Cb d D.s m MB Λ ΛV G₀`, `A = c1A d m Λ`. -/
theorem e1_coeff (hd : 1 ≤ d) {D : WholeDyn d} (hs0 : 0 ≤ D.s) (hsd : D.s < d) (m : ℕ)
    (MB Λ ΛV G₀ : ℝ) {ρ : ℝ → Euc d → ℝ} {T : ℝ}
    (hMB : HRS.PDE.MatBound MB D.M) (hV : VHypRd (m + 3) ΛV G₀ D.V)
    (hcoef : CoeffHypRd D.s m Λ T ρ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) :
    (∀ i, ContDiff ℝ 1 (fun y => meanFieldDriftW D (ρ r) y i)) ∧
    (∀ i y, |HRS.MS.UniqT3.D1 i (fun y => meanFieldDriftW D (ρ r) y i) y| ≤
        HRS.MS.UniqC1.c1Cb d D.s m MB Λ ΛV G₀) ∧
    (∀ i y, |meanFieldDriftW D (ρ r) y i| ≤ HRS.MS.UniqC1.c1Cb d D.s m MB Λ ΛV G₀ * (1 + ‖y‖)) ∧
    ContDiff ℝ 1 (ρ r) ∧
    (∀ y, |ρ r y| ≤ HRS.MS.UniqC1.c1A d m Λ * (1 + ‖y‖) ^ (-((d : ℝ) + 3))) ∧
    (∀ y, ‖fderiv ℝ (ρ r) y‖ ≤ HRS.MS.UniqC1.c1A d m Λ * (1 + ‖y‖) ^ (-((d : ℝ) + 3))) := by
  have hbd := HRS.MS.UniqC1.c1_drift_single hd hs0 hsd m MB Λ ΛV G₀ rfl hMB hV hcoef hr
  have hcoord := fun i => e1_drift_coord hbd i
  exact ⟨fun i => (hcoord i).1, fun i => (hcoord i).2.1, fun i => (hcoord i).2.2,
    e1_rho_smooth hcoef hr, (e1_rho_decay01 hd hcoef hr).1, (e1_rho_decay01 hd hcoef hr).2⟩

/-! ### The bound -/

/-- **(b)** `|⟨𝓛^σ u, η_ε(x - ·)⟩| ≤ C(ε) B (1+|x|)` for `σ ∈ [0,t]` and `LocMass B u`;
`C` depends only on the data `(d, D, ε, m, MB, Λ, ΛV, G₀)` (not on `u, B, σ, x`). -/
theorem e1_bound (hd : 1 ≤ d) {D : WholeDyn d} (hs0 : 0 ≤ D.s) (hsd : D.s < d) (m : ℕ)
    (MB Λ ΛV G₀ : ℝ) {ρ : ℝ → Euc d → ℝ} {T : ℝ}
    (hMB : HRS.PDE.MatBound MB D.M) (hV : VHypRd (m + 3) ΛV G₀ D.V)
    (hcoef : CoeffHypRd D.s m Λ T ρ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Euc d → ℝ) (B : ℝ), 0 ≤ B → LocMass B u →
      ∀ σ ∈ Set.Icc (0 : ℝ) t, ∀ x : Euc d,
        |forwardPairing D ρ t σ u (fun y => eta d ε (x - y))| ≤ C * B * (1 + ‖x‖) := by
  set Cb : ℝ := HRS.MS.UniqC1.c1Cb d D.s m MB Λ ΛV G₀ with hCb
  set A : ℝ := HRS.MS.UniqC1.c1A d m Λ with hA
  have hA0 : 0 ≤ A := e1_A_nonneg m Λ
  have hCb0 : 0 ≤ Cb := e1_Cb_nonneg hd hs0 hsd m MB Λ ΛV G₀ hMB hV hcoef (ht.1.trans ht.2)
  obtain ⟨Θ, hΘ0, hΘ0', hΘ1, hΘ2⟩ := th_bounds (d := d) hε
  obtain ⟨CK, hCK0, hCK1, hCK2⟩ := th_conv_bounds (d := d) hs0 hsd hε
  obtain ⟨K1, hK10, hK1⟩ := e1_local_bound d ε
  obtain ⟨Kw, hKw0, hKw⟩ := e1_weighted_bound d
  set MB' : ℝ := max MB 0 with hMB'
  set c1 : ℝ := |D.invβ| * (d * Θ) * K1 with hc1
  set c2 : ℝ := (d * (Cb * Θ * (2 + ε))) * K1 with hc2
  set c3 : ℝ := (d : ℝ) ^ 2 * MB' * ((A * (CK + CK)) * Kw) with hc3
  have hc1' : 0 ≤ c1 := by positivity
  have hc2' : 0 ≤ c2 := by positivity
  have hc3' : 0 ≤ c3 := by positivity
  refine ⟨c1 + c2 + c3, by positivity, fun u B hB hu σ hσ x => ?_⟩
  have hr : t - σ ∈ Set.Icc (0 : ℝ) T :=
    ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩
  obtain ⟨hbs, hb1, hb0, hρs, hρ0, hρ1⟩ := e1_coeff hd hs0 hsd m MB Λ ΛV G₀ hMB hV hcoef hr
  rw [e1_fp_eq D ρ t σ hs0 hsd hbs hρs u hε x]
  set ρt : Euc d → ℝ := ρ (t - σ) with hρt
  set b : Fin d → Euc d → ℝ := fun i y => meanFieldDriftW D ρt y i with hbdef
  have hθ := th_cc (d := d) hε
  have hx1 : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have hBx : 0 ≤ B * (1 + ‖x‖) := by positivity
  have T1 : |∫ y, u y * R1 (th d ε) x y| ≤ (d * Θ) * K1 * B := by
    refine hK1 B u x _ (d * Θ) hB hu (fun y hy => ?_) (fun y => e1_R1_abs hΘ2 x y)
    exact e1_R1_vanish hε (by rw [mem_closedBall, dist_eq_norm] at hy; linarith [not_le.1 hy])
  have T2 : |∫ y, u y * R2 b (th d ε) x y| ≤ c2 * B * (1 + ‖x‖) := by
    have := hK1 B u x (R2 b (th d ε) x) ((d * (Cb * Θ * (2 + ε))) * (1 + ‖x‖)) hB hu
      (fun y hy => e1_R2_vanish hε b
        (by rw [mem_closedBall, dist_eq_norm] at hy; linarith [not_le.1 hy]))
      (fun y => e1_R2_abs hε hΘ0 hCb0 hΘ0' hΘ1 b hb1 hb0 x y)
    calc _ ≤ _ := this
      _ = _ := by rw [hc2]; ring
  have T3 : ∀ i j, |∫ y, u y * R3 D.s ρt (th d ε) i j x y| ≤ (A * (CK + CK) * Kw) * B * (1 + ‖x‖) := by
    intro i j
    have hmeas : AEStronglyMeasurable (R3 D.s ρt (th d ε) i j x) volume := by
      have c1 : Continuous (D1 j ρt) := (hρs.continuous_fderiv one_ne_zero).clm_apply continuous_const
      have c2 : Continuous (HRS.Whole.convFun (rieszKernel d D.s) (D1 i (th d ε))) :=
        K_cont hs0 hsd (hθ.D1 i).cont (hθ.D1 i).supp
      have c3 : Continuous (HRS.Whole.convFun (rieszKernel d D.s) (D1 j (D1 i (th d ε)))) :=
        K_cont hs0 hsd ((hθ.D1 i).D1 j).cont ((hθ.D1 i).D1 j).supp
      have : Continuous (R3 D.s ρt (th d ε) i j x) := by
        unfold R3
        exact (c1.mul (c2.comp (continuous_id.sub continuous_const))).add
          (hρs.continuous.mul (c3.comp (continuous_id.sub continuous_const)))
      exact this.aestronglyMeasurable
    have := hKw B u (R3 D.s ρt (th d ε) i j x) (A * (CK + CK) * (1 + ‖x‖)) hB hu hmeas
      (fun y => e1_R3_abs hρ0 hρ1 hCK1 hCK2 i j x y)
    calc _ ≤ _ := this
      _ = _ := by ring
  have hM : ∀ i j, |D.M j i| ≤ MB' := fun i j => (hMB j i).trans (le_max_left _ _)
  have T3s : |∑ i, ∑ j, D.M j i * ∫ y, u y * R3 D.s ρt (th d ε) i j x y| ≤
      (d : ℝ) ^ 2 * MB' * ((A * (CK + CK) * Kw) * B * (1 + ‖x‖)) := by
    calc _ ≤ ∑ i : Fin d, |∑ j, D.M j i * ∫ y, u y * R3 D.s ρt (th d ε) i j x y| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin d, ∑ j : Fin d, |D.M j i * ∫ y, u y * R3 D.s ρt (th d ε) i j x y| :=
          Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin d, ∑ j : Fin d, MB' * ((A * (CK + CK) * Kw) * B * (1 + ‖x‖)) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hM i j) (T3 i j) (abs_nonneg _) ((abs_nonneg _).trans (hM i j))
      _ = _ := by simp; ring
  have T1' : |D.invβ * ∫ y, u y * R1 (th d ε) x y| ≤ c1 * B * (1 + ‖x‖) := by
    rw [abs_mul]
    calc _ ≤ |D.invβ| * ((d * Θ) * K1 * B) := by gcongr
      _ = c1 * B := by rw [hc1]; ring
      _ ≤ c1 * B * (1 + ‖x‖) := le_mul_of_one_le_right (by positivity) hx1
  have T3' : |∑ i, ∑ j, D.M j i * ∫ y, u y * R3 D.s ρt (th d ε) i j x y| ≤ c3 * B * (1 + ‖x‖) :=
    T3s.trans (le_of_eq (by rw [hc3]; ring))
  have h1 := abs_sub ((D.invβ * ∫ y, u y * R1 (th d ε) x y) - (∫ y, u y * R2 b (th d ε) x y))
    (∑ i, ∑ j, D.M j i * ∫ y, u y * R3 D.s ρt (th d ε) i j x y)
  have h2 := abs_sub (D.invβ * ∫ y, u y * R1 (th d ε) x y) (∫ y, u y * R2 b (th d ε) x y)
  linarith [h1, h2, T1', T2, T3']

end HRS.MS.UniqE1
