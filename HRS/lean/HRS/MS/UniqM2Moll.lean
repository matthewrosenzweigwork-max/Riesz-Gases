import HRS.MS.UniqM2Grad

/-!
# M2 of `UniqPlan.md`, part 4: the gradient of the mollification

`IsWeakGrad u v`: `v : ℝ^d → ℝ^d` is measurable and `∫ u ∂_jψ = -∫ v_j ψ` for all `C_c^∞` functions `ψ`.
For `LocMass B u` and a weak gradient `v` with `LocMass B' ‖v‖` the mollification `moll d ε u` has
`fderiv (moll d ε u) x e_j = moll d ε v_j x` and `∫_{ball c 1} ‖∇(moll d ε u)‖² ≤ N(d) B'²`
for `0 < ε ≤ 1`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqM2

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqM1

variable {d : ℕ}

/-- `v` is a weak gradient of `u`, tested against `C_c^∞` functions. -/
def IsWeakGrad (u : Euc d → ℝ) (v : Euc d → Euc d) : Prop :=
  Measurable v ∧ ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∀ j : Fin d,
    ∫ x, u x * fderiv ℝ ψ x (EuclideanSpace.single j 1) = - ∫ x, v x j * ψ x

theorem LocMass.component {B : ℝ} {v : Euc d → Euc d} (hv : Measurable v)
    (h : LocMass B (fun x => ‖v x‖)) (j : Fin d) : LocMass B (fun x => v x j) :=
  LocMass.of_norm_le h ((measurable_pi_apply j |>.comp (WithLp.measurable_ofLp 2 (Fin d → ℝ) |>.comp hv)).aestronglyMeasurable)
    (fun x => by simpa using PiLp.norm_apply_le (v x) j)

/-- The derivative of `y ↦ η_ε(x - y)`. -/
theorem fderiv_eta_comp (ε : ℝ) (x y : Euc d) :
    fderiv ℝ (fun y => eta d ε (x - y)) y = -(fderiv ℝ (eta d ε) (x - y)) := by
  have h : HasFDerivAt (fun y => eta d ε (x - y)) ((fderiv ℝ (eta d ε) (x - y)).comp (-ContinuousLinearMap.id ℝ (Euc d))) y := by
    have h1 : HasFDerivAt (fun y : Euc d => x - y) (-ContinuousLinearMap.id ℝ (Euc d)) y :=
      (hasFDerivAt_id y).const_sub x
    exact (((eta_contDiff (d := d) (ε := ε)).differentiable (by simp)) (x - y)).hasFDerivAt.comp y h1
  rw [h.fderiv]
  ext v
  simp


/-- `∂_j (η_ε * u) = η_ε * v_j` for a weak gradient `v` of `u`. -/
theorem fderiv_moll_apply {ε : ℝ} (hε : 0 < ε) {u : Euc d → ℝ} (hu : LocallyIntegrable u volume)
    {v : Euc d → Euc d} (hv : IsWeakGrad u v) (j : Fin d) (x : Euc d) :
    fderiv ℝ (moll d ε u) x (EuclideanSpace.single j 1) = moll d ε (fun y => v y j) x := by
  set e : Euc d := EuclideanSpace.single j 1 with he
  have hηc := eta_hasCompactSupport (d := d) hε
  have hη1 : ContDiff ℝ 1 (eta d ε) := (eta_contDiff (d := d) (ε := ε)).of_le (by simp)
  rw [moll_eq_cv, fderiv_cv hu hηc hη1, cv_apply]
  have hco : Continuous (fun y => fderiv ℝ (eta d ε) (x - y)) :=
    ((eta_contDiff (d := d) (ε := ε)).continuous_fderiv (by simp)).comp (continuous_const.sub continuous_id)
  have hcs : HasCompactSupport (fun y => fderiv ℝ (eta d ε) (x - y)) :=
    (hηc.fderiv ℝ).comp_homeomorph (Homeomorph.subLeft x)
  have hint : Integrable (fun y => u y • fderiv ℝ (eta d ε) (x - y)) volume :=
    hu.integrable_smul_right_of_hasCompactSupport hco hcs
  rw [ContinuousLinearMap.integral_apply hint e]
  have hψ1 : ContDiff ℝ ∞ (fun y => eta d ε (x - y)) :=
    (eta_contDiff (d := d) (ε := ε)).comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport (fun y => eta d ε (x - y)) :=
    hηc.comp_homeomorph (Homeomorph.subLeft x)
  have h := hv.2 _ hψ1 hψc j
  simp only [fderiv_eta_comp, neg_apply, mul_neg, integral_neg, neg_inj] at h
  unfold moll
  calc ∫ y, (u y • fderiv ℝ (eta d ε) (x - y)) e = ∫ y, u y * fderiv ℝ (eta d ε) (x - y) e := by
        simp
    _ = _ := by rw [h]; exact integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)


/-- The operator norm of a functional on `ℝ^d` is bounded by the `ℓ²` norm of its coordinates. -/
theorem norm_sq_le_sum_apply (L : Euc d →L[ℝ] ℝ) :
    ‖L‖ ^ 2 ≤ ∑ j, (L (EuclideanSpace.single j 1)) ^ 2 := by
  set g := (InnerProductSpace.toDual ℝ (Euc d)).symm L with hg
  have h1 : ‖L‖ = ‖g‖ := ((InnerProductSpace.toDual ℝ (Euc d)).symm.norm_map L).symm
  have h2 : ∀ j, g j = L (EuclideanSpace.single j 1) := fun j => by
    have := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := (EuclideanSpace.single j 1 : Euc d)) (y := L)
    rw [← this, EuclideanSpace.inner_single_right]
    simp [hg]
  rw [h1, EuclideanSpace.norm_sq_eq]
  refine le_of_eq (Finset.sum_congr rfl fun j _ => ?_)
  rw [Real.norm_eq_abs, sq_abs, h2]

theorem moll_grad_mass_le {ε : ℝ} (hε : 0 < ε) {B : ℝ} {u : Euc d → ℝ} (hu : LocMass B u)
    {v : Euc d → Euc d} (hv : IsWeakGrad u v) (hvm : LocMass B (fun x => ‖v x‖)) (c : Euc d) :
    ∫⁻ x in ball c 1, ‖fderiv ℝ (moll d ε u) x‖ₑ ^ 2 ≤ ∫⁻ y in ball c (1 + ε), ‖‖v y‖‖ₑ ^ 2 := by
  have hcomp : ∀ j, LocMass B (fun x => v x j) := fun j => LocMass.component hv.1 hvm j
  have hmeas : ∀ j, Measurable (moll d ε (fun y => v y j)) := fun j =>
    (moll_contDiff hε (hcomp j).locallyIntegrable).continuous.measurable
  have hpt : ∀ x, ‖fderiv ℝ (moll d ε u) x‖ₑ ^ 2 ≤ ∑ j, ‖moll d ε (fun y => v y j) x‖ₑ ^ 2 := by
    intro x
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    calc ENNReal.ofReal (‖fderiv ℝ (moll d ε u) x‖ ^ 2)
        ≤ ENNReal.ofReal (∑ j, (fderiv ℝ (moll d ε u) x (EuclideanSpace.single j 1)) ^ 2) :=
          ENNReal.ofReal_le_ofReal (norm_sq_le_sum_apply _)
      _ = ∑ j, ENNReal.ofReal ((moll d ε (fun y => v y j) x) ^ 2) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun j _ => sq_nonneg _]
          exact Finset.sum_congr rfl fun j _ => by
            rw [fderiv_moll_apply hε hu.locallyIntegrable hv j x]
      _ = _ := Finset.sum_congr rfl fun j _ => by rw [enorm_sq_eq]
  calc ∫⁻ x in ball c 1, ‖fderiv ℝ (moll d ε u) x‖ₑ ^ 2
      ≤ ∫⁻ x in ball c 1, ∑ j, ‖moll d ε (fun y => v y j) x‖ₑ ^ 2 := lintegral_mono hpt
    _ = ∑ j, ∫⁻ x in ball c 1, ‖moll d ε (fun y => v y j) x‖ₑ ^ 2 :=
        lintegral_finsetSum _ fun j _ => (hmeas j).enorm.pow_const 2
    _ ≤ ∑ j, ∫⁻ y in ball c (1 + ε), ‖v y j‖ₑ ^ 2 :=
        Finset.sum_le_sum fun j _ => moll_mass_le hε (hcomp j) c 1
    _ = ∫⁻ y in ball c (1 + ε), ∑ j, ‖v y j‖ₑ ^ 2 :=
        (lintegral_finsetSum' _ fun j _ => ((hcomp j).1.restrict.enorm.pow_const 2)).symm
    _ = _ := by
        refine lintegral_congr fun y => ?_
        rw [enorm_sq_eq, EuclideanSpace.norm_sq_eq,
          ENNReal.ofReal_sum_of_nonneg fun j _ => sq_nonneg _]
        exact Finset.sum_congr rfl fun j _ => by rw [enorm_sq_eq, Real.norm_eq_abs, sq_abs]

/-- Uniform bound for `0 < ε ≤ 1`: `∫_{ball c 1} ‖∇(η_ε * u)‖² ≤ N(d) B²`. -/
theorem moll_grad_mass_le_const (d : ℕ) :
    ∃ N : ℕ, ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ (B : ℝ) (u : Euc d → ℝ) (v : Euc d → Euc d),
      LocMass B u → IsWeakGrad u v → LocMass B (fun x => ‖v x‖) → ∀ c : Euc d,
      ∫⁻ x in ball c 1, ‖fderiv ℝ (moll d ε u) x‖ₑ ^ 2 ≤ (N : ℝ≥0∞) * ENNReal.ofReal (B ^ 2) := by
  obtain ⟨N, hN⟩ := exists_ball_sq_bound d 2
  refine ⟨N, fun ε hε hε1 B u v hu hv hvm c => ?_⟩
  refine (moll_grad_mass_le hε hu hv hvm c).trans ?_
  exact (lintegral_mono_set (ball_subset_ball (by linarith))).trans (hN B _ hvm c)


/-- **(a), (b)**: the weak gradient of `u` with `ulocNormE 1 χ u ≤ B`:  a measurable `v : ℝ^d → ℝ^d`
with `∫ u ∂_jψ = -∫ v_j ψ` for all `C_c^∞` functions `ψ`, `∫_{ball c 1} ‖v‖² ≤ B²` for every `c`
(so also for every component `v_j`). -/
theorem weakGrad_of_ulocNormE {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) {u : Euc d → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hu : ulocNormE 1 χ u ≤ ENNReal.ofReal B) :
    ∃ v : Euc d → Euc d, IsWeakGrad u v ∧ LocMass B (fun x => ‖v x‖) ∧
      ∀ j : Fin d, LocMass B (fun x => v x j) := by
  obtain ⟨v, hm, hid, hLM⟩ := exists_weakGrad hχ hB hu
  exact ⟨v, ⟨hm, hid⟩, hLM, fun j => LocMass.component hm hLM j⟩

/-- **(a), (b), (c) together.**  For every `d` there is `N` (depending only on `d`) such that for every
uloc cutoff `χ`, every `u` with `ulocNormE 1 χ u ≤ ofReal B` there is a weak gradient `v` (as in
`weakGrad_of_ulocNormE`) such that for all `0 < ε ≤ 1`: `∂_j (η_ε * u) = η_ε * v_j` and
`∫_{ball c 1} ‖∇(η_ε * u)‖² ≤ N B²` for every `c`. -/
theorem moll_grad_of_ulocNormE (d : ℕ) :
    ∃ N : ℕ, ∀ {χ : Euc d → ℝ}, IsUlocCutoff χ → ∀ (u : Euc d → ℝ) (B : ℝ), 0 ≤ B →
      ulocNormE 1 χ u ≤ ENNReal.ofReal B →
      ∃ v : Euc d → Euc d, IsWeakGrad u v ∧ LocMass B (fun x => ‖v x‖) ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
          (∀ (j : Fin d) (x : Euc d),
            fderiv ℝ (moll d ε u) x (EuclideanSpace.single j 1) = moll d ε (fun y => v y j) x) ∧
          ∀ c : Euc d, ∫⁻ x in ball c 1, ‖fderiv ℝ (moll d ε u) x‖ₑ ^ 2 ≤
            (N : ℝ≥0∞) * ENNReal.ofReal (B ^ 2) := by
  obtain ⟨N, hN⟩ := moll_grad_mass_le_const d
  refine ⟨N, fun {χ} hχ u B hB hu => ?_⟩
  obtain ⟨v, hv, hLM, -⟩ := weakGrad_of_ulocNormE hχ hB hu
  have hLu : LocMass B u := locMass_of_ulocNormE (m := 1) hχ hB hu
  exact ⟨v, hv, hLM, fun ε hε hε1 =>
    ⟨fun j x => fderiv_moll_apply hε hLu.locallyIntegrable hv j x,
      hN ε hε hε1 B u v hLu hv hLM⟩⟩

end HRS.MS.UniqM2
