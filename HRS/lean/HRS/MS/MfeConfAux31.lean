import HRS.MS.MfeConfAux30
import HRS.Whole.MovtrAux2

/-!
# S.B.1, packet F3 (part 12): the trajectory bundle from `WholeMFEHyp`, and the Plummer-smoothed kernels

* `sb1_tr3_of_hyp`: `WholeMFEHyp` (+ `Sb1Pot`) gives `Sb1Tr3` with the decay `(1+|y|)^{-(d+3)}` of `D^l ρ_t`.
* `sb1gE d s ε = movtr_gEps d s ε` (`-½ log(|z|²+ε²)` resp. `(|z|²+ε²)^{-s/2}`): for `0 < ε ≤ 1` it is an admissible kernel
  (`Sb1KerU`), regular (`Sb1KerR`, `‖∇ k_ε‖ ≤ σ ε^{-s-1}`), with the *uniform* bound `‖∇ k_ε(z)‖ ≤ σ|z|^{-s-1}` and
  pointwise convergence `k_ε → g`, `∇k_ε → ∇g` off the origin.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

open HRS.MP.RdGen

variable {d : ℕ}

theorem sb1_dec3_of_regular (hd : 1 ≤ d) {r : ℕ} {Λ : ℝ} {ρ : Euc d → ℝ} (hcb : MemCb r ρ)
    (hfin : Whole.weightedSupE r ((d : ℝ) + 3) ρ < ⊤) (hΛ : (Whole.weightedSupE r ((d : ℝ) + 3) ρ).toReal ≤ Λ)
    {l : ℕ} (hl : l ≤ r) (y : Euc d) :
    ‖iteratedFDeriv ℝ l ρ y‖ ≤ ((d : ℝ) ^ r * Λ * 2 ^ ((d : ℝ) + 3)) * sb1w ((d : ℝ) + 3) y := by
  have hΛ0 : 0 ≤ Λ := (ENNReal.toReal_nonneg).trans hΛ
  have hjpos : 0 < Whole.jbracket y := by unfold Whole.jbracket; positivity
  have hpt : ∀ i : Fin l → Fin d,
      |iteratedFDeriv ℝ l ρ y (fun p => EuclideanSpace.single (i p) 1)| ≤
        Λ * Whole.jbracket y ^ (-((d : ℝ) + 3)) := by
    intro i
    have h := (rg_partial_weight_bound hfin hl i y).trans hΛ
    have e : |iteratedFDeriv ℝ l ρ y (fun p => EuclideanSpace.single (i p) 1)| =
        (Whole.jbracket y ^ ((d : ℝ) + 3) * |Whole.partialDeriv i ρ y|) * Whole.jbracket y ^ (-((d : ℝ) + 3)) := by
      have : Whole.jbracket y ^ ((d : ℝ) + 3) * Whole.jbracket y ^ (-((d : ℝ) + 3)) = 1 := by
        rw [← Real.rpow_add hjpos]; simp
      unfold Whole.partialDeriv
      calc _ = |iteratedFDeriv ℝ l ρ y (fun p => EuclideanSpace.single (i p) 1)| * 1 := by ring
        _ = _ := by rw [← this]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hjpos.le _)
  have hn := rg_norm_le_of_partial hd (iteratedFDeriv ℝ l ρ y) hpt
  have h1 := rg_jb_rpow_le y (p := (d : ℝ) + 3) (by positivity)
  have hdr : (d : ℝ) ^ l ≤ (d : ℝ) ^ r := pow_le_pow_right₀ (by exact_mod_cast hd) hl
  calc ‖iteratedFDeriv ℝ l ρ y‖ ≤ (d : ℝ) ^ l * (Λ * Whole.jbracket y ^ (-((d : ℝ) + 3))) := hn
    _ ≤ (d : ℝ) ^ r * (Λ * (2 ^ ((d : ℝ) + 3) * (1 + ‖y‖) ^ (-((d : ℝ) + 3)))) := by
        apply mul_le_mul hdr _ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left h1 hΛ0
    _ = _ := by unfold sb1w; ring

/-- the trajectory bundle from the standing hypotheses -/
theorem sb1_tr3_of_hyp {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    {D : Whole.WholeDyn d} {N : ℕ} {T Λ : ℝ} {r : ℕ} {ρ : ℝ → Euc d → ℝ} {X₀ : Ω → Whole.EucConfig d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Whole.EucConfig d N}
    (h : Whole.WholeMFEHyp P D N T Λ r ρ X₀ W X) (hd : 1 ≤ d) (hs0 : 0 ≤ D.s) (hsd : D.s < d)
    {B : ℝ} (hV : Sb1Pot D.V B) :
    Sb1Tr3 D T ((d : ℝ) ^ r * max Λ 0 * 2 ^ ((d : ℝ) + 3)) B ((d : ℝ) ^ r * max Λ 0 * 2 ^ ((d : ℝ) + 3)) ρ where
  tr := sb1_traj_of_hyp h hd hs0 hsd hV
  dec := fun t ht l hl y => by
    have hreg := h.mf_reg t ht
    have hw : Whole.weightedSupE r ((d : ℝ) + 3) (ρ t) ≤ ENNReal.ofReal Λ := le_trans le_add_self hreg.2.2
    have hfin : Whole.weightedSupE r ((d : ℝ) + 3) (ρ t) < ⊤ := lt_of_le_of_lt hw ENNReal.ofReal_lt_top
    have hΛ : (Whole.weightedSupE r ((d : ℝ) + 3) (ρ t)).toReal ≤ max Λ 0 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hw
      rw [ENNReal.toReal_ofReal'] at this
      exact this
    exact sb1_dec3_of_regular hd hreg.2.1 hfin hΛ (hl.trans h.r_ge) y
  pos := fun t ht => h.pos_density t ht
  C3nn := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    positivity

/-! ### Plummer-smoothed kernels -/

section GEps

variable {s : ℝ}

theorem sb1gE_pos {ε : ℝ} (hε : 0 < ε) (z : Euc d) : 0 < ‖z‖ ^ 2 + ε ^ 2 :=
  add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hε 2)

theorem sb1gE_even (ε : ℝ) (z : Euc d) : Whole.movtr_gEps d s ε (-z) = Whole.movtr_gEps d s ε z := by
  simp [Whole.movtr_gEps]

theorem sb1gE_contDiff {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ 2 (Whole.movtr_gEps d s ε) := by
  by_cases hs : s = 0
  · have : Whole.movtr_gEps d s ε = fun z : Euc d => -(1 / 2) * Real.log (‖z‖ ^ 2 + ε ^ 2) := by
      funext z; simp [Whole.movtr_gEps, hs]
    rw [this]
    exact contDiff_const.mul (((contDiff_norm_sq ℝ).add contDiff_const).log fun z => (sb1gE_pos hε z).ne')
  · have : Whole.movtr_gEps d s ε = fun z : Euc d => (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2) := by
      funext z; simp [Whole.movtr_gEps, hs]
    rw [this]
    exact ((contDiff_norm_sq ℝ).add contDiff_const).rpow_const_of_ne fun z => (sb1gE_pos hε z).ne'

theorem sb1gE_fderiv_apply {ε : ℝ} {z : Euc d} (hu : 0 < ‖z‖ ^ 2 + ε ^ 2) (e : Euc d) :
    fderiv ℝ (Whole.movtr_gEps d s ε) z e =
      -(Whole.movtr_sigma s * (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1)) * inner ℝ z e := by
  rw [(Whole.movtr_gEps_hasFDerivAt s ε z hu).fderiv]
  simp [innerSL_apply_apply]

theorem sb1_sigma_nonneg (hs0 : 0 ≤ s) : 0 ≤ Whole.movtr_sigma s := by
  unfold Whole.movtr_sigma; split_ifs <;> linarith

/-- uniform gradient bound `|∇k_ε(z) e| ≤ σ |z|^{-s-1} |e|`, `z ≠ 0`, `ε ≥ 0` -/
theorem sb1gE_grad_le (hs0 : 0 ≤ s) {ε : ℝ} (hε : 0 ≤ ε) {z : Euc d} (hz : z ≠ 0) (e : Euc d) :
    |fderiv ℝ (Whole.movtr_gEps d s ε) z e| ≤ Whole.movtr_sigma s * ‖z‖ ^ (-s - 1) * ‖e‖ := by
  have hzp : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hu : 0 < ‖z‖ ^ 2 + ε ^ 2 := by positivity
  have hσ := sb1_sigma_nonneg hs0
  rw [sb1gE_fderiv_apply hu, abs_mul, abs_neg, abs_of_nonneg (mul_nonneg hσ (Real.rpow_nonneg hu.le _))]
  have h1 : (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1) ≤ (‖z‖ ^ 2) ^ (-s / 2 - 1) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg ε]) (by linarith)
  have h2 : (‖z‖ ^ 2) ^ (-s / 2 - 1) = ‖z‖ ^ (-s - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hzp.le]; congr 1; push_cast; ring
  have h3 : ‖z‖ ^ (-s - 1) = ‖z‖ ^ (-s - 2) * ‖z‖ := by
    rw [show (-s - 1) = (-s - 2) + 1 by ring, Real.rpow_add hzp, Real.rpow_one]
  calc Whole.movtr_sigma s * (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1) * |inner ℝ z e|
      ≤ Whole.movtr_sigma s * ‖z‖ ^ (-s - 2) * (‖z‖ * ‖e‖) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left (h1.trans h2.le) hσ) (abs_real_inner_le_norm _ _)
          (abs_nonneg _) (mul_nonneg hσ (Real.rpow_nonneg hzp.le _))
    _ = Whole.movtr_sigma s * ‖z‖ ^ (-s - 1) * ‖e‖ := by rw [h3]; ring

theorem sb1gE_fderiv_norm_le (hs0 : 0 ≤ s) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (z : Euc d) :
    ‖fderiv ℝ (Whole.movtr_gEps d s ε) z‖ ≤ Whole.movtr_sigma s * ε ^ (-s - 1) := by
  have hσ := sb1_sigma_nonneg hs0
  refine ContinuousLinearMap.opNorm_le_of_unit_norm (mul_nonneg hσ (Real.rpow_nonneg hε.le _)) fun e he => ?_
  rw [Real.norm_eq_abs, sb1gE_fderiv_apply (sb1gE_pos hε z)]
  have := Whole.movtr_dEps_abs_le hs0 hε e z he.le
  unfold Whole.movtr_dEps at this
  exact this

theorem sb1KerU_gE (hs0 : 0 ≤ s) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Sb1KerU d s (Whole.movtr_gEps d s ε) where
  meas := Whole.movtr_gEps_measurable s ε
  lower := fun z => by
    have hu := sb1gE_pos hε z
    by_cases h0 : s = 0
    · subst h0
      simp only [sb1kap, ite_true, one_mul, Whole.movtr_gEps]
      have h1 : ‖z‖ ^ 2 + ε ^ 2 ≤ (1 + ‖z‖) ^ 2 := by nlinarith [norm_nonneg z, sq_nonneg ε]
      have h2 := Real.log_le_log hu h1
      rw [Real.log_pow] at h2
      push_cast at h2
      linarith
    · simp only [sb1kap, h0, ite_false, zero_mul, neg_zero, Whole.movtr_gEps]
      exact Real.rpow_nonneg hu.le _
  upper := fun z hz => by
    have hzp : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hu := sb1gE_pos hε z
    have h1 : ‖z‖ ^ 2 ≤ ‖z‖ ^ 2 + ε ^ 2 := by nlinarith [sq_nonneg ε]
    by_cases h0 : s = 0
    · subst h0
      simp only [Whole.movtr_gEps, Whole.rieszKernel, ite_true]
      have h2 := Real.log_le_log (by positivity) h1
      rw [Real.log_pow] at h2
      push_cast at h2
      linarith
    · simp only [Whole.movtr_gEps, Whole.rieszKernel, h0, ite_false]
      have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h0)
      have : ‖z‖ ^ (-s) = (‖z‖ ^ 2) ^ (-s / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hzp.le]; congr 1; push_cast; ring
      rw [this]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)

theorem sb1KerR_gE (hs0 : 0 ≤ s) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Sb1KerR d (Whole.movtr_gEps d s ε) (Whole.movtr_sigma s * ε ^ (-s - 1)) where
  c2 := sb1gE_contDiff hε
  even := sb1gE_even ε
  gbd := sb1gE_fderiv_norm_le hs0 hε hε1

/-- the smoothing parameters `ε_n = 1/(n+1)` -/
def sb1eps (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/-- the `n`-th smoothed kernel -/
def sb1kn (s : ℝ) (n : ℕ) : Euc d → ℝ := Whole.movtr_gEps d s (sb1eps n)

theorem sb1eps_pos (n : ℕ) : 0 < sb1eps n := by unfold sb1eps; positivity

theorem sb1eps_le_one (n : ℕ) : sb1eps n ≤ 1 := by
  unfold sb1eps
  rw [div_le_one (by positivity)]
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem sb1eps_tendsto : Tendsto sb1eps atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

theorem sb1gE_tendsto {z : Euc d} (hz : z ≠ 0) :
    Tendsto (fun n => Whole.movtr_gEps d s (sb1eps n) z) atTop (𝓝 (Whole.rieszKernel d s z)) := by
  have hzp : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hu : Tendsto (fun n => ‖z‖ ^ 2 + sb1eps n ^ 2) atTop (𝓝 (‖z‖ ^ 2 + 0 ^ 2)) :=
    tendsto_const_nhds.add ((sb1eps_tendsto).pow 2)
  have hne : ‖z‖ ^ 2 + 0 ^ 2 ≠ 0 := by positivity
  rw [← Whole.movtr_gEps_zero]
  by_cases h0 : s = 0
  · simp only [Whole.movtr_gEps, h0, ite_true]
    exact (hu.log hne).const_mul _
  · simp only [Whole.movtr_gEps, h0, ite_false]
    exact hu.rpow_const (Or.inl hne)

theorem sb1gE_fderiv_tendsto {z : Euc d} (hz : z ≠ 0) (e : Euc d) :
    Tendsto (fun n => fderiv ℝ (Whole.movtr_gEps d s (sb1eps n)) z e) atTop
      (𝓝 (fderiv ℝ (Whole.rieszKernel d s) z e)) := by
  have hzp : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hu : Tendsto (fun n => ‖z‖ ^ 2 + sb1eps n ^ 2) atTop (𝓝 (‖z‖ ^ 2 + 0 ^ 2)) :=
    tendsto_const_nhds.add ((sb1eps_tendsto).pow 2)
  have hne : ‖z‖ ^ 2 + 0 ^ 2 ≠ 0 := by positivity
  rw [← Whole.movtr_gEps_zero, sb1gE_fderiv_apply (by positivity : 0 < ‖z‖ ^ 2 + 0 ^ 2)]
  have : ∀ n, fderiv ℝ (Whole.movtr_gEps d s (sb1eps n)) z e =
      -(Whole.movtr_sigma s * (‖z‖ ^ 2 + sb1eps n ^ 2) ^ (-s / 2 - 1)) * inner ℝ z e := fun n =>
    sb1gE_fderiv_apply (sb1gE_pos (sb1eps_pos n) z) e
  simp_rw [this]
  exact ((tendsto_const_nhds.mul (hu.rpow_const (Or.inl hne))).neg).mul_const _

end GEps

end HRS.MS.MfeConf
