import HRS.MS.SuppU2Aux12

/-!
# U2 auxiliary 13: part (b) of `far_derivatives`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.Whole

variable {d : ℕ}

lemma u2_matVec_apply (M : Matrix (Fin d) (Fin d) ℝ) (v : Euc d) (i : Fin d) :
    Torus.matVec M.transpose v i = ∑ l, M l i * v l := by
  simp [Torus.matVec, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, Matrix.transpose_apply]

lemma u2_fderiv_eq_sum (f : Euc d → ℝ) (y w : Euc d) :
    fderiv ℝ f y w = ∑ l, w l * gradient f y l := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := Euc d) (x := w)
    (y := fderiv ℝ f y)
  unfold gradient
  rw [← h, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [mul_comm]

lemma u2_fderiv_apply_bound {k : ℕ} {f : Euc d → ℝ} (hf : ContDiff ℝ (k + 1) f) (w : Euc d)
    (m : ℕ) (hm : m ≤ k) (y : Euc d) :
    ‖iteratedFDeriv ℝ m (fun y => fderiv ℝ f y w) y‖ ≤ ‖w‖ * ‖iteratedFDeriv ℝ (m + 1) f y‖ := by
  have hfd : ContDiff ℝ k (fderiv ℝ f) := hf.fderiv_right (le_refl _)
  let L : (Euc d →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ w
  have h1 := L.norm_iteratedFDeriv_comp_left (f := fderiv ℝ f) (x := y) (N := (k : ℕ∞ω)) (n := m)
    hfd.contDiffAt (by exact_mod_cast hm)
  have hL : ‖L‖ ≤ ‖w‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg w) fun φ => ?_
    simp only [L, ContinuousLinearMap.apply_apply]
    rw [mul_comm]
    exact φ.le_opNorm w
  rw [norm_iteratedFDeriv_fderiv] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))

lemma u2_cb_le {k : ℕ} {f : Euc d → ℝ} (hf : MemCb (k + 1) f) (m : ℕ) (hm : m ≤ k + 1)
    (y : Euc d) : ‖iteratedFDeriv ℝ m f y‖ ≤ cbNorm (k + 1) f := by
  unfold cbNorm
  have h1 : ‖iteratedFDeriv ℝ m f y‖ ≤ ⨆ z, ‖iteratedFDeriv ℝ m f z‖ :=
    le_ciSup (hf.2 m hm) y
  refine h1.trans ?_
  exact Finset.single_le_sum (f := fun j => ⨆ z : Euc d, ‖iteratedFDeriv ℝ j f z‖)
    (fun j _ => Real.iSup_nonneg fun z => norm_nonneg _)
    (Finset.mem_range.mpr (by omega))

lemma u2_cb_nonneg {k : ℕ} {f : Euc d → ℝ} : 0 ≤ cbNorm (k + 1) f := by
  unfold cbNorm
  exact Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun z => norm_nonneg _

lemma u2_prod_dec {k : ℕ} {L Aρ : ℝ} {ρ u : Euc d → ℝ} (hρ : U2Dec k L Aρ ρ) (hAρ : 0 ≤ Aρ)
    (hu : ContDiff ℝ k u) {Bu : ℝ} (hBu : 0 ≤ Bu)
    (hub : ∀ m ≤ k, ∀ y, ‖iteratedFDeriv ℝ m u y‖ ≤ Bu) :
    U2Dec k L (2 ^ k * Aρ * Bu) (fun y => ρ y * u y) := by
  refine ⟨hρ.1.mul hu, fun m hm y => ?_⟩
  have hmul := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := ρ) (g := u) (N := (k : ℕ∞ω)) hρ.1 hu y
    (n := m) (by exact_mod_cast hm)
  refine hmul.trans ?_
  have hw := u2Wt_pos (d := d) L y
  have hterm : ∀ l ∈ Finset.range (m + 1),
      (m.choose l : ℝ) * ‖iteratedFDeriv ℝ l ρ y‖ * ‖iteratedFDeriv ℝ (m - l) u y‖ ≤
        (m.choose l : ℝ) * (Aρ * u2Wt L y * Bu) := by
    intro l hl
    have hl' : l ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have h1 := hρ.2 l (by omega) y
    have h2 := hub (m - l) (by omega) y
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
  calc _ ≤ ∑ l ∈ Finset.range (m + 1), (m.choose l : ℝ) * (Aρ * u2Wt L y * Bu) :=
        Finset.sum_le_sum hterm
    _ = (2 : ℝ) ^ m * (Aρ * u2Wt L y * Bu) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose m
    _ ≤ (2 : ℝ) ^ k * (Aρ * u2Wt L y * Bu) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hm) (by positivity)
    _ = _ := by ring

theorem u2_partB (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s ≤ (d : ℝ) - 2) (k : ℕ) (L : ℝ)
    (hL : (d : ℝ) + k + s + 3 < L) (M : Matrix (Fin d) (Fin d) ℝ) (Λρ : ℝ) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, ContDiff ℝ k ρ → weightedSupE k L ρ ≤ ENNReal.ofReal Λρ →
      ∀ f : Euc d → ℝ, MemCb (k + 1) f →
        ContDiff ℝ k (fun x => divGConvPlain d s
          (fun y => ρ y • Torus.matVec M.transpose (gradient f y)) x) ∧
        decayNormE k (s + 1) (fun x => divGConvPlain d s
          (fun y => ρ y • Torus.matVec M.transpose (gradient f y)) x) ≤
          ENNReal.ofReal (C * cbNorm (k + 1) f) := by
  have hL' : (d : ℝ) + k + (s + 1) + 2 < L := by linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hdL : (d : ℝ) < L := by linarith
  have hL0 : 0 ≤ L := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  choose Ci hCi0 hCi using fun i : Fin d => u2_core (u2_kerFull hd hs0 hsd i) k hL'
  let wv : Fin d → Euc d := fun i => WithLp.toLp 2 (fun l => M l i)
  set Aρ : ℝ := (d : ℝ) ^ k * 2 ^ L * max Λρ 0 with hAρ
  have hAρ0 : 0 ≤ Aρ := by positivity
  refine ⟨∑ i, Ci i * (2 ^ k * Aρ * ‖wv i‖), fun ρ hρ hwse f hf => ?_⟩
  have hΛ : ∀ j ≤ k, ∀ (I : Fin j → Fin d) (x : Euc d),
      jbracket x ^ L * |partialDeriv I ρ x| ≤ max Λρ 0 :=
    fun j hj I x => u2_wse_bound hwse j hj I x
  have hdecρ : U2Dec k L Aρ ρ :=
    ⟨hρ, fun m hm y => u2_norm_le_of_partial (by omega) hL0 (le_max_right _ _) hΛ m hm y⟩
  set cb : ℝ := cbNorm (k + 1) f with hcb
  have hcb0 : 0 ≤ cb := u2_cb_nonneg
  have hf1 : ContDiff ℝ (k + 1) f := by exact_mod_cast hf.1
  have hu : ∀ i, ContDiff ℝ k (fun y => fderiv ℝ f y (wv i)) := fun i =>
    (hf1.fderiv_right (le_refl _)).clm_apply contDiff_const
  have hub : ∀ i, ∀ m ≤ k, ∀ y, ‖iteratedFDeriv ℝ m (fun y => fderiv ℝ f y (wv i)) y‖ ≤
      ‖wv i‖ * cb := fun i m hm y =>
    (u2_fderiv_apply_bound hf1 (wv i) m hm y).trans
      (mul_le_mul_of_nonneg_left (u2_cb_le hf (m + 1) (by omega) y) (norm_nonneg _))
  have hdecG : ∀ i, U2Dec k L (2 ^ k * Aρ * (‖wv i‖ * cb))
      (fun y => ρ y * fderiv ℝ f y (wv i)) := fun i =>
    u2_prod_dec hdecρ hAρ0 (hu i) (mul_nonneg (norm_nonneg _) hcb0) (hub i)
  have hA_i : ∀ i, 0 ≤ 2 ^ k * Aρ * (‖wv i‖ * cb) := fun i => by positivity
  have hdiv : (fun x => divGConvPlain d s
      (fun y => ρ y • Torus.matVec M.transpose (gradient f y)) x) =
      fun x => ∑ i, u2Conv (u2_kap d s i) (fun y => ρ y * fderiv ℝ f y (wv i)) x := by
    funext x
    unfold divGConvPlain
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [u2_conv_eq_y]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have h1 : (ρ y • Torus.matVec M.transpose (gradient f y)) i = ρ y * fderiv ℝ f y (wv i) := by
      rw [PiLp.smul_apply, smul_eq_mul, u2_matVec_apply, u2_fderiv_eq_sum]
    simp only [h1, u2_kap]
    ring
  rw [hdiv]
  refine ⟨?_, ?_⟩
  · exact ContDiff.sum fun i _ => (hCi i _ _ (hA_i i) (hdecG i)).1
  · have hCnn : 0 ≤ (∑ i, Ci i * (2 ^ k * Aρ * ‖wv i‖)) * cb :=
      mul_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (hCi0 i) (by positivity)) hcb0
    have := u2_decayNormE_le (k := k) (b := s + 1) (by linarith)
      (F := fun x => ∑ i, u2Conv (u2_kap d s i) (fun y => ρ y * fderiv ℝ f y (wv i)) x)
      hCnn (fun j hj x => by
        have hcd : ∀ i ∈ (Finset.univ : Finset (Fin d)), ContDiffAt ℝ (j : ℕ∞ω)
            (u2Conv (u2_kap d s i) (fun y => ρ y * fderiv ℝ f y (wv i))) x := fun i _ =>
          (((hCi i _ _ (hA_i i) (hdecG i)).1).of_le (by exact_mod_cast hj)).contDiffAt
        rw [iteratedFDeriv_fun_sum_apply hcd]
        refine (norm_sum_le _ _).trans ?_
        have hsum : ∑ i, ‖iteratedFDeriv ℝ j
            (u2Conv (u2_kap d s i) (fun y => ρ y * fderiv ℝ f y (wv i))) x‖ ≤
            ∑ i, (Ci i * (2 ^ k * Aρ * (‖wv i‖ * cb))) * (1 + ‖x‖) ^ (-((s + 1) + (j : ℝ))) :=
          Finset.sum_le_sum fun i _ => by
            have := (hCi i _ _ (hA_i i) (hdecG i)).2 j hj x
            simpa [mul_assoc] using this
        refine hsum.trans (le_of_eq ?_)
        have hh : ∑ i, (Ci i * (2 ^ k * Aρ * (‖wv i‖ * cb))) =
            (∑ i, Ci i * (2 ^ k * Aρ * ‖wv i‖)) * cb := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [← Finset.sum_mul, hh])
    refine this.trans (le_of_eq ?_)
    rfl

end HRS.Whole
