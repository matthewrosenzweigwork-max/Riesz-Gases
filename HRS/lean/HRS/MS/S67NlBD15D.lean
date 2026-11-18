import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.S67NlBD08
import HRS.MS.S67NlBD15A
import HRS.MS.S67NlBD15E

/-!
# S6.7 nonlinear, packet S6.7nl.15D: coordinate Sobolev profile via the actual K+1 approximation

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4238-4245, row
`S:W:lem:r2mov-global-adjoint` (nonlinear part). Owned definitions: none.
The coordinate-weighted profile `E = Q^K x_i local` equals `(x_i/Q) * P_{K+1}` with `|x_i/Q| <= 1`;
the K+1 hypotheses give `L^2` convergence of the coordinate profiles of the Schwartz approximants
to `E` (bounded multiplier only), the second component of `movc2_force_wt` gives their `H^b`
membership with the bound `C |vn n|_{Sigma^m}`, and `s67bd_sobolev_fatou` (15E) concludes.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

lemma s67bd15d_L2_le {b : ℝ} (hb : 0 ≤ b) {u : Euc d → ℝ}
    (hu : HRS.PDE.ToolboxRd.MemSobolev b u) :
    (eLpNorm u 2 (volume : Measure (Euc d))).toReal ≤ s67bd_Hnorm b u := by
  have hn : 0 ≤ oscNorm 0 u := Real.sqrt_nonneg _
  rw [mn_eLpNorm_eq hu.1, ENNReal.toReal_ofReal hn, oscNorm_zero u hu.1]
  unfold s67bd_Hnorm HRS.PDE.ToolboxRd.sobolevNormSq
  refine Real.sqrt_le_sqrt ?_
  rw [← HRS.PDE.ToolboxRd.FourierAux.integral_norm_sq_fourierL2 hu.1]
  refine integral_mono (HRS.PDE.ToolboxRd.FourierAux.integrable_norm_sq_fourierL2 hu.1) hu.2
    (fun ξ => ?_)
  have h1 : 1 ≤ (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ b :=
    Real.one_le_rpow (by nlinarith [sq_nonneg ‖ξ‖, Real.pi_pos, sq_nonneg Real.pi]) hb
  nlinarith [sq_nonneg ‖HRS.PDE.ToolboxRd.fourierL2 u ξ‖]

lemma s67bd15d_sobolev_sub {b : ℝ} {f g : Euc d → ℝ}
    (hf : HRS.PDE.ToolboxRd.MemSobolev b f) (hg : HRS.PDE.ToolboxRd.MemSobolev b g) :
    HRS.PDE.ToolboxRd.MemSobolev b (fun x => f x - g x) := by
  refine ⟨hf.1.sub hg.1, ?_⟩
  have hw := hf.1.sub hg.1
  have hbound : Integrable (fun ξ => 2 * ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ b *
      ‖HRS.PDE.ToolboxRd.fourierL2 f ξ‖ ^ 2 + (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ b *
      ‖HRS.PDE.ToolboxRd.fourierL2 g ξ‖ ^ 2)) volume := (hf.2.add hg.2).const_mul 2
  refine hbound.mono' ?_ ?_
  · exact (HRS.PDE.ToolboxRd.FourierAux.continuous_wt_rpow b).aestronglyMeasurable.mul
      ((HRS.PDE.ToolboxRd.FourierAux.aestronglyMeasurable_fourierL2 hw).norm.pow 2)
  · filter_upwards [HRS.PDE.ToolboxRd.FourierAux.fourierL2_sub hf.1 hg.1] with ξ hξ
    have hwpos : 0 ≤ (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ b :=
      Real.rpow_nonneg (by positivity) _
    rw [Real.norm_of_nonneg (mul_nonneg hwpos (sq_nonneg _)), hξ]
    have h1 : ‖HRS.PDE.ToolboxRd.fourierL2 f ξ - HRS.PDE.ToolboxRd.fourierL2 g ξ‖ ^ 2 ≤
        2 * (‖HRS.PDE.ToolboxRd.fourierL2 f ξ‖ ^ 2 + ‖HRS.PDE.ToolboxRd.fourierL2 g ξ‖ ^ 2) := by
      have := norm_sub_le (HRS.PDE.ToolboxRd.fourierL2 f ξ) (HRS.PDE.ToolboxRd.fourierL2 g ξ)
      nlinarith [norm_nonneg (HRS.PDE.ToolboxRd.fourierL2 f ξ),
        norm_nonneg (HRS.PDE.ToolboxRd.fourierL2 g ξ), norm_nonneg (HRS.PDE.ToolboxRd.fourierL2 f ξ -
          HRS.PDE.ToolboxRd.fourierL2 g ξ), sq_nonneg (‖HRS.PDE.ToolboxRd.fourierL2 f ξ‖ -
          ‖HRS.PDE.ToolboxRd.fourierL2 g ξ‖)]
    nlinarith [mul_le_mul_of_nonneg_left h1 hwpos]

lemma s67bd15d_uniform (H : Mov2dTh d s β q ρ₀) (m K : ℕ) (hm : (d : ℝ) / 2 + 7 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : SchwartzMap (Euc d) ℝ) (i : Fin d),
      HRS.PDE.ToolboxRd.MemSobolev ((m : ℝ) - movA d s) (fun x => (1 + ‖x‖ ^ 2) ^ K *
        (x i * s67bd_local d s (fun y => Real.sqrt (ρ₀ y) * w y) i x)) ∧
      s67bd_Hnorm ((m : ℝ) - movA d s) (fun x => (1 + ‖x‖ ^ 2) ^ K *
        (x i * s67bd_local d s (fun y => Real.sqrt (ρ₀ y) * w y) i x)) ≤ C * oscNorm (m : ℝ) w := by
  obtain ⟨B, D⟩ := movc2_data H.hd H.hs0 H.hsd H.hq H.hβ H.hρ
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hm2 : (2 : ℝ) ≤ m := by linarith
  have hσ : (m : ℝ) - movA d s ≤ (m : ℝ) - 2 + ((d : ℝ) - s) := by
    have : s + 2 - d ≤ movA d s := le_max_right _ _
    linarith
  obtain ⟨C, hC, hforce⟩ := movc2_force_wt D H.hs0 H.hsd hm2 hσ K
  refine ⟨C, hC, fun w i => ?_⟩
  have h1 := ((hforce w).1 i).2
  exact ⟨h1.1, h1.2⟩

theorem s67bd_coordinate_profile_transfer (H : Mov2dTh d s β q ρ₀)
    (m K : ℕ) (hm : (d : ℝ) / 2 + 7 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Euc d → ℝ, Continuous v → MemOsc (m : ℝ) v →
      ∀ vn : ℕ → SchwartzMap (Euc d) ℝ,
      Tendsto (fun n => oscNorm (m : ℝ) (fun x => vn n x - v x)) atTop (𝓝 0) →
      ∀ i : Fin d,
      HRS.PDE.ToolboxRd.MemSobolev ((m : ℝ) - movA d s) (s67bd_profile d s ρ₀ v (K + 1) i) →
      (∀ n, HRS.PDE.ToolboxRd.MemSobolev ((m : ℝ) - movA d s)
        (s67bd_profile d s ρ₀ (vn n) (K + 1) i)) →
      Tendsto (fun n => s67bd_Hnorm ((m : ℝ) - movA d s)
        (fun x => s67bd_profile d s ρ₀ (vn n) (K + 1) i x - s67bd_profile d s ρ₀ v (K + 1) i x))
        atTop (𝓝 0) →
      HRS.PDE.ToolboxRd.MemSobolev ((m : ℝ) - movA d s) (fun x => (1 + ‖x‖ ^ 2) ^ K *
        (x i * s67bd_local d s (fun y => Real.sqrt (ρ₀ y) * v y) i x)) ∧
      s67bd_Hnorm ((m : ℝ) - movA d s) (fun x => (1 + ‖x‖ ^ 2) ^ K *
        (x i * s67bd_local d s (fun y => Real.sqrt (ρ₀ y) * v y) i x)) ≤
        C * oscNorm (m : ℝ) v := by
  obtain ⟨C, hC0, hunif⟩ := s67bd15d_uniform H m K hm
  refine ⟨C, hC0, fun v _ hv vn hvn i hPv hPn hHconv => ?_⟩
  set b : ℝ := (m : ℝ) - movA d s with hb
  have hb0 : 0 ≤ b := by
    have := (mov2d_a_bounds d H.hd H.hsd).2
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    rw [hb]; linarith
  -- the multiplier `x_i / Q`
  set mu : Euc d → ℝ := fun x => x i / (1 + ‖x‖ ^ 2) with hmu
  have hQ : ∀ x : Euc d, 0 < 1 + ‖x‖ ^ 2 := fun x => by positivity
  have hmuc : Continuous mu := by
    refine (PiLp.continuous_apply 2 _ i).div (by fun_prop) (fun x => (hQ x).ne')
  have hmub : ∀ x, |mu x| ≤ 1 := by
    intro x
    rw [hmu]; simp only
    rw [abs_div, abs_of_pos (hQ x), div_le_one (hQ x)]
    have h1 : |x i| ≤ ‖x‖ := by simpa using PiLp.norm_apply_le x i
    nlinarith [norm_nonneg x, sq_nonneg (‖x‖ - 1)]
  set E : Euc d → ℝ := fun x => (1 + ‖x‖ ^ 2) ^ K *
    (x i * s67bd_local d s (fun y => Real.sqrt (ρ₀ y) * v y) i x) with hE
  set En : ℕ → Euc d → ℝ := fun n x => (1 + ‖x‖ ^ 2) ^ K *
    (x i * s67bd_local d s (fun y => Real.sqrt (ρ₀ y) * vn n y) i x) with hEn
  have hEeq : ∀ x, E x = mu x * s67bd_profile d s ρ₀ v (K + 1) i x := by
    intro x
    have := (hQ x).ne'
    simp only [hE, hmu, s67bd_profile]
    field_simp
    ring
  have hEneq : ∀ n x, En n x = mu x * s67bd_profile d s ρ₀ (vn n) (K + 1) i x := by
    intro n x
    have := (hQ x).ne'
    simp only [hEn, hmu, s67bd_profile]
    field_simp
    ring
  -- `E` is in `L²`
  have hEL2 : MemLp E 2 (volume : Measure (Euc d)) := by
    refine MemLp.of_le_mul (c := 1) (hPv.1) ?_ (Filter.Eventually.of_forall fun x => ?_)
    · have : E = fun x => mu x * s67bd_profile d s ρ₀ v (K + 1) i x := funext hEeq
      rw [this]
      exact hmuc.aestronglyMeasurable.mul hPv.1.aestronglyMeasurable
    · rw [hEeq x, norm_mul, one_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (by simpa using hmub x)
  -- `L²` convergence
  have hL2 : Tendsto (fun n => (eLpNorm (fun x => En n x - E x) 2
      (volume : Measure (Euc d))).toReal) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => ENNReal.toReal_nonneg) (fun n => ?_) hHconv
    have hsub := s67bd15d_sobolev_sub (hPn n) hPv
    have hle : eLpNorm (fun x => En n x - E x) 2 (volume : Measure (Euc d)) ≤
        eLpNorm (fun x => s67bd_profile d s ρ₀ (vn n) (K + 1) i x -
          s67bd_profile d s ρ₀ v (K + 1) i x) 2 (volume : Measure (Euc d)) := by
      have hm : AEStronglyMeasurable (fun x => En n x - E x) (volume : Measure (Euc d)) := by
        have : (fun x => En n x - E x) = fun x => mu x * s67bd_profile d s ρ₀ (vn n) (K + 1) i x -
            mu x * s67bd_profile d s ρ₀ v (K + 1) i x := by
          funext x; rw [hEneq n x, hEeq x]
        rw [this]
        exact (hmuc.aestronglyMeasurable.mul (hPn n).1.aestronglyMeasurable).sub
          (hmuc.aestronglyMeasurable.mul hPv.1.aestronglyMeasurable)
      refine eLpNorm_mono hm fun x => ?_
      rw [hEneq n x, hEeq x, ← mul_sub, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (by simpa using hmub x)
    exact (ENNReal.toReal_mono hsub.1.eLpNorm_ne_top hle).trans (s67bd15d_L2_le hb0 hsub)
  -- osc norms
  have hlin : ∀ (a c : ℝ) (f g : Euc d → ℝ), MemOsc (m : ℝ) f → MemOsc (m : ℝ) g →
      MemOsc (m : ℝ) (fun x => a * f x + c * g x) ∧
      oscNorm (m : ℝ) (fun x => a * f x + c * g x) ≤ |a| * oscNorm (m : ℝ) f + |c| * oscNorm (m : ℝ) g :=
    fun a c f g hf hg => HRS.MS.MovC1.movc1_osc_lin (m : ℝ) a c hf hg
  have hvnm : ∀ n, MemOsc (m : ℝ) (vn n) := fun n => memOsc_schwartz (m : ℝ) (vn n)
  set e : ℕ → Euc d → ℝ := fun n x => vn n x - v x with he
  have hem : ∀ n, MemOsc (m : ℝ) (e n) := fun n => by
    have := (hlin 1 (-1) _ _ (hvnm n) hv).1
    simpa [he, sub_eq_add_neg] using this
  have hosc_vn : Tendsto (fun n => oscNorm (m : ℝ) (vn n)) atTop (𝓝 (oscNorm (m : ℝ) v)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hvn
    rw [Real.norm_eq_abs, abs_le]
    have h1 := (hlin 1 1 _ _ (hem n) hv).2
    have h2 := (hlin 1 (-1) _ _ (hvnm n) (hem n)).2
    have e1 : (fun x => (1 : ℝ) * e n x + 1 * v x) = vn n := by funext x; simp only [he]; ring
    have e2 : (fun x => (1 : ℝ) * vn n x + (-1) * e n x) = v := by funext x; simp only [he]; ring
    rw [e1] at h1
    rw [e2] at h2
    simp only [abs_one, abs_neg, one_mul] at h1 h2
    constructor <;> linarith
  exact s67bd_sobolev_fatou d b hb0 En E (fun n => (hunif (vn n) i).1) hEL2 hL2
    (fun n => C * oscNorm (m : ℝ) (vn n)) (C * oscNorm (m : ℝ) v) (fun n => (hunif (vn n) i).2)
    (hosc_vn.const_mul C)

end HRS.MS.BreakdownS67
