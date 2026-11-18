import HRS.MS.R2InterpAux2
import HRS.MC.E213O1
import HRS.MS.S21F_D00

/-!
# S21L P12 -- `r26t3_projection_passage` (R26-T3.P12): strong path projections preserve the `C_b^5` ball

Contract of packet R26-T3.P12 (`origin/pro/fine-breakdown`), statement verbatim.  Route: composing with a linear contraction `P`
keeps `Φ` in the `C_b^5` unit ball (`‖D^j(Φ∘P)(w)‖ ≤ ‖D^jΦ(Pw)‖ ‖P‖^j`); for `P_L → id` strongly, `D^j(Φ∘P_L)(w) = D^jΦ(P_L w) ∘ P_L^{⊗j}`
so `v(D^j(Φ∘P_L)(w)) = (P_L^{⊗j} v)(D^jΦ(P_L w)) → v(D^jΦ(w))` by uniform boundedness, strong convergence of `P_L^{⊗j} v` on
`projTensor` and continuity of `D^jΦ`.  The inputs (`s102_projection_strong`) are the merged S10.2 facts.  Helpers `s21l_p12_`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

open HRS HRS.Sec7 HRS.Whole

section Generic

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem s21l_p12_iter {Φ : B → ℝ} (hΦ : ContDiff ℝ 5 Φ) (P : B →L[ℝ] B) {j : ℕ} (hj : j ≤ 5) (w : B) :
    iteratedFDeriv ℝ j (Φ ∘ P) w = (iteratedFDeriv ℝ j Φ (P w)).compContinuousLinearMap fun _ => P :=
  P.iteratedFDeriv_comp_right hΦ w (by exact_mod_cast hj)

theorem s21l_p12_norm {Φ : B → ℝ} (hΦ : ContDiff ℝ 5 Φ) {P : B →L[ℝ] B} (hP : ‖P‖ ≤ 1) {j : ℕ} (hj : j ≤ 5)
    (w : B) : ‖iteratedFDeriv ℝ j (Φ ∘ P) w‖ ≤ ‖iteratedFDeriv ℝ j Φ (P w)‖ := by
  rw [s21l_p12_iter hΦ P hj w]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h1 : ∏ _i : Fin j, ‖P‖ ≤ 1 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) hP
  calc ‖iteratedFDeriv ℝ j Φ (P w)‖ * ∏ _i : Fin j, ‖P‖ ≤ ‖iteratedFDeriv ℝ j Φ (P w)‖ * 1 :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = _ := mul_one _

theorem s21l_p12_ball (P : B →L[ℝ] B) (hP : ‖P‖ ≤ 1) {Φ : B → ℝ} (hΦ : Φ ∈ CbUnitBall B 5) :
    (Φ ∘ P) ∈ CbUnitBall B 5 := by
  obtain ⟨hC, hb, hn⟩ := hΦ
  refine ⟨hC.comp P.contDiff, fun j hj => ?_, ?_⟩
  · obtain ⟨K, hK⟩ := hb j hj
    refine ⟨K, ?_⟩
    rintro _ ⟨w, rfl⟩
    exact (s21l_p12_norm hC hP hj w).trans (hK ⟨P w, rfl⟩)
  · unfold cbNorm at hn ⊢
    refine le_trans (Finset.sum_le_sum fun j hj => ?_) hn
    have hj5 : j ≤ 5 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    refine ciSup_le fun w => ?_
    exact (s21l_p12_norm hC hP hj5 w).trans (le_ciSup (hb j hj5) (P w))

theorem s21l_p12_tensor (P : ℕ → B →L[ℝ] B) (hP1 : ∀ L, ‖P L‖ ≤ 1)
    (hconv : ∀ w, Tendsto (fun L => P L w) atTop (𝓝 w))
    (hT : ∀ (j : ℕ) (v : TensorDual B j), v ∈ projTensor B j →
      Tendsto (fun L => tensorPow j (P L) v) atTop (𝓝 v))
    {Φ : B → ℝ} (hΦ : ContDiff ℝ 5 Φ) {j : ℕ} (hj : j ≤ 5) (w : B) (v : TensorDual B j)
    (hv : v ∈ projTensor B j) :
    Tendsto (fun L => v (iteratedFDeriv ℝ j (Φ ∘ P L) w)) atTop (𝓝 (v (iteratedFDeriv ℝ j Φ w))) := by
  have e : ∀ L, v (iteratedFDeriv ℝ j (Φ ∘ P L) w) =
      (tensorPow j (P L) v) (iteratedFDeriv ℝ j Φ (P L w)) := fun L => by
    rw [s21l_p12_iter hΦ (P L) hj w]
    rfl
  set M := iteratedFDeriv ℝ j Φ w with hM
  have hML : Tendsto (fun L => iteratedFDeriv ℝ j Φ (P L w)) atTop (𝓝 M) :=
    ((hΦ.continuous_iteratedFDeriv (by exact_mod_cast hj)).tendsto w).comp (hconv w)
  have ha : Tendsto (fun L => (tensorPow j (P L) v) M) atTop (𝓝 (v M)) :=
    ((ContinuousLinearMap.apply ℝ ℝ M).continuous.tendsto v).comp (hT j v hv)
  have hn : Tendsto (fun L => ‖iteratedFDeriv ℝ j Φ (P L w) - M‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hML
  have hb : Tendsto (fun L => (tensorPow j (P L) v) (iteratedFDeriv ℝ j Φ (P L w) - M)) atTop (𝓝 0) := by
    have hn' := hn.const_mul ‖v‖
    rw [mul_zero] at hn'
    refine squeeze_zero_norm (fun L => ?_) hn'
    refine ((tensorPow j (P L) v).le_opNorm _).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have := HRS.MC.E213O.tensorPow'_norm_le j (P L) v
    exact this.trans (by
      have h1 : ‖P L‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg _) (hP1 L)
      nlinarith [norm_nonneg v])
  have hsum := hb.add ha
  rw [zero_add] at hsum
  refine hsum.congr fun L => ?_
  rw [e L, map_sub]
  ring

end Generic

theorem r26t3_projection_passage {p : Parameters} (Φ : Window p → ℝ)
    (hΦ : Φ ∈ CbUnitBall (Window p) 5) :
    (∀ L, (Φ ∘ HRS.MS.R2Interp.s102_Pj p.T p.hT L) ∈ CbUnitBall (Window p) 5) ∧
    (∀ w, Tendsto (fun L => Φ (HRS.MS.R2Interp.s102_Pj p.T p.hT L w)) atTop (𝓝 (Φ w))) ∧
    ∀ j ≤ 5, ∀ w (v : projTensor (Window p) j),
      Tendsto (fun L => (v : TensorDual (Window p) j)
        (iteratedFDeriv ℝ j (Φ ∘ HRS.MS.R2Interp.s102_Pj p.T p.hT L) w)) atTop
          (𝓝 ((v : TensorDual (Window p) j) (iteratedFDeriv ℝ j Φ w))) := by
  obtain ⟨hP1, hconv, hT⟩ := HRS.MS.R2Interp.s102_projection_strong (d := p.d) (wholeSpaceIndex p.d) p.T p.hT
  refine ⟨fun L => s21l_p12_ball _ (hP1 L) hΦ, fun w => ?_, fun j hj w v => ?_⟩
  · exact (hΦ.1.continuous.tendsto w).comp (hconv w)
  · exact s21l_p12_tensor (fun L => HRS.MS.R2Interp.s102_Pj p.T p.hT L) hP1 hconv hT hΦ.1 hj w v v.2

end HRS.MS.R26T3
