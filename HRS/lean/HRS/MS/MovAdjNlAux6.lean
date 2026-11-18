import HRS.MS.MovAdjNlAux5

/-!
# S6.7 nonlinear row, package A, packet N4 (part 2): `L²` bookkeeping for products `φ · w` (`φ` Schwartz, `w ∈ C_b^k`)

Namespace `HRS.MS.MovAdjNl`, helpers `s67a_`.  Infrastructure for the supplement row `S:W:lem:r2mov-global-adjoint`; not a manuscript row.

* `s67aD j w = ∂_j w`; `s67aA j : 𝓢 →L 𝓢` is `x_j + ∂_j` on Schwartz functions (`s67aA_apply : s67aA j φ x = s67aG j φ x`);
* `s67aG_mul`: `(x_j + ∂_j)(φ w) = (x_j + ∂_j)φ · w + φ · ∂_j w`; `s67aG_add`;
* `S67L h c`: `h ∈ L²` with `‖h‖_{L²} = oscNorm 0 h ≤ c`; `s67a_L2_prod`: `S67L (φ u) (B ‖φ‖)` for `|u| ≤ B`; closure under sums.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdjNl

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovC1 HRS.MS.MovOsc HRS.MS.MovAdj

variable {d : ℕ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

/-- `∂_j w` (coordinate derivative). -/
def s67aD (j : Fin d) (w : Euc d → ℝ) (x : Euc d) : ℝ := fderiv ℝ w x (EuclideanSpace.single j (1 : ℝ))

/-- `x_j + ∂_j` on Schwartz functions. -/
def s67aA (j : Fin d) : 𝓢R →L[ℝ] 𝓢R := mova1_X j + mova1_D j

theorem s67aA_apply (j : Fin d) (φ : 𝓢R) (x : Euc d) : s67aA j φ x = s67aG j φ x := by
  simp [s67aA, s67aG, mova1_X_apply, mova1_D_apply]

theorem s67aG_mul (j : Fin d) (φ : 𝓢R) {w : Euc d → ℝ} (hw : ContDiff ℝ 1 w) (x : Euc d) :
    s67aG j (fun y => φ y * w y) x = s67aA j φ x * w x + φ x * s67aD j w x := by
  have h1 : DifferentiableAt ℝ (fun y => φ y) x := (φ.differentiableAt)
  have h2 : DifferentiableAt ℝ w x := (hw.differentiable (by norm_num)) x
  unfold s67aG s67aD
  rw [s67aA_apply, fderiv_fun_mul h1 h2]
  simp only [s67aG, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem s67aG_add (j : Fin d) {f g : Euc d → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (x : Euc d) :
    s67aG j (fun y => f y + g y) x = s67aG j f x + s67aG j g x := by
  have h1 : DifferentiableAt ℝ f x := (hf.differentiable (by norm_num)) x
  have h2 : DifferentiableAt ℝ g x := (hg.differentiable (by norm_num)) x
  unfold s67aG
  rw [fderiv_fun_add h1 h2]
  simp only [ContinuousLinearMap.add_apply]
  ring

/-- `h ∈ L²` with `‖h‖_{L²} ≤ c`. -/
def S67L (h : Euc d → ℝ) (c : ℝ) : Prop := MemLp h 2 (volume : Measure (Euc d)) ∧ oscNorm 0 h ≤ c

theorem s67a_osc0 {h : Euc d → ℝ} (hh : MemLp h 2 (volume : Measure (Euc d))) :
    MemOsc 0 h ∧ oscNorm 0 h = ‖hh.toLp h‖ := by
  obtain ⟨-, h2, -⟩ := movlin_L2_osc (hh.toLp h)
  have hae : h =ᵐ[volume] ⇑(hh.toLp h) := hh.coeFn_toLp.symm
  exact ⟨⟨hh, by simpa using mov2b_coeff_sq_summable hh⟩, by rw [mov2b_oscNorm_congr hae 0, h2]⟩

theorem S67L.mono {h : Euc d → ℝ} {c c' : ℝ} (hh : S67L h c) (hc : c ≤ c') : S67L h c' := ⟨hh.1, hh.2.trans hc⟩

theorem S67L.add {f g : Euc d → ℝ} {c c' : ℝ} (hf : S67L f c) (hg : S67L g c') :
    S67L (fun x => f x + g x) (c + c') := by
  refine ⟨hf.1.add hg.1, ?_⟩
  have := (movc1_osc_add 0 (s67a_osc0 hf.1).1 (s67a_osc0 hg.1).1).2
  exact this.trans (add_le_add hf.2 hg.2)

theorem s67a_norm_toLp_le_abs {F G : Euc d → ℝ} (hF : MemLp F 2 (volume : Measure (Euc d)))
    (hG : MemLp G 2 (volume : Measure (Euc d))) (h : ∀ x, |F x| ≤ |G x|) :
    ‖hF.toLp F‖ ≤ ‖hG.toLp G‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with x h1 h2
  rw [h1, h2, Real.norm_eq_abs, Real.norm_eq_abs]
  exact h x

theorem s67a_L2_prod (φ : 𝓢R) {u : Euc d → ℝ} (hu : AEStronglyMeasurable u (volume : Measure (Euc d)))
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |u x| ≤ B) : S67L (fun x => φ x * u x) (B * oscNorm 0 φ) := by
  have hφ : MemLp (⇑φ : Euc d → ℝ) 2 (volume : Measure (Euc d)) := φ.memLp 2
  have hL : MemLp (fun x => φ x * u x) 2 (volume : Measure (Euc d)) := by
    have := s67_memLp_mul_bdd hφ hu hb
    simpa [mul_comm] using this
  refine ⟨hL, ?_⟩
  rw [(s67a_osc0 hL).2, (s67a_osc0 hφ).2]
  have hG : MemLp (fun x => B * φ x) 2 (volume : Measure (Euc d)) := hφ.const_mul B
  refine (s67a_norm_toLp_le_abs hL hG fun x => ?_).trans (le_of_eq ?_)
  · rw [abs_mul, abs_mul, abs_of_nonneg hB]
    exact (mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)).trans_eq (mul_comm _ _)
  · have : hG.toLp (fun x => B * φ x) = B • hφ.toLp (⇑φ) := by
      apply Lp.ext
      filter_upwards [hG.coeFn_toLp, Lp.coeFn_smul B (hφ.toLp (⇑φ)), hφ.coeFn_toLp] with x h1 h2 h3
      rw [h1, h2]
      simp [h3]
    rw [this, norm_smul, Real.norm_of_nonneg hB]

theorem s67a_exists_bound {ι : Type*} [Finite ι] (f : ι → ℝ) : ∃ c : ℝ, 0 ≤ c ∧ ∀ i, f i ≤ c := by
  obtain ⟨c, hc⟩ := Finite.exists_le f
  exact ⟨max c 0, le_max_right _ _, fun i => (hc i).trans (le_max_left _ _)⟩

end HRS.MS.MovAdjNl
