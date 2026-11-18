import HRS.ME.NfUPU11

/-!
# Chunk E, packet F5c (namespace `HRS.ME.FamU`): V-uniform Q84 estimates for thermal densities

Originals (`HRS/ME/NfUPU11.lean`), copied with the binders reordered as in `docs/MAIN_E_FAMU_PLAN.md`:
* `q84a_force_bound_unif` (line 51) becomes `q84a_force_bound_unifV`: `∃ M` (V-free: `|βm⁻¹ c₀⁻¹| Λ₀ + Λ₀`),
  then `∀ V, IsSmooth V → ∀ β, ∀ ρ, ParxU … V ρ → …`. `V` enters only through `hV` and the bundle.
* `q84a_estimates_unif` (line 129) becomes `q84a_estimates_unifV`: `∃ C` (from `q84a_gg_bound` and the
  V-free `M`), then `∀ V, IsSmooth V → …`. No `Bf` is needed.
* `q84e_modified_kernels_uniform_unif` (line 280) becomes `q84e_modified_kernels_uniform_unifV`: `∃ Cu`
  (`|C|` with `C` from `q84a_estimates_unifV`), then `∀ V, IsSmooth V → …`. No `Bf` is needed.
The proofs are the originals with the binder order changed.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace HRS.ME.FamU

open HRS HRS.Q84a HRS.Q84d HRS.ME.NfU

variable {d : ℕ}

/-- **F5.4 (V-uniform copy of `q84a_force_bound_unif`).** The constant `M` is chosen before `V`, `β`, `ρ`. -/
theorem q84a_force_bound_unifV (s : ℝ) (βm βp c₀ Λ₀ : ℝ) (hβm : 0 < βm) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (V : Torus d → ℝ), Torus.IsSmooth V → ∀ β ∈ Icc βm βp, ∀ ρ : Torus d → ℝ,
      HRS.ME.ParxU.ParxU d s 1 βp⁻¹ βm⁻¹ c₀ Λ₀ β V ρ → ∀ x, ‖forceField d s ρ x‖ ≤ M := by
  refine ⟨|βm⁻¹ * c₀⁻¹| * |Λ₀| + |Λ₀|, by positivity, fun V hV β hβI ρ U x => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hc0 : 0 < c₀ := U.F.hc₀
  have hρs := U.H.rho_smooth
  have hρ := U.H.thermal
  have hβinv : β⁻¹ ≤ βm⁻¹ := U.beta_bounds.2.1
  have hρ1 := q84a_contDiff_one hρs.smooth
  have hV1 := q84a_contDiff_one hV
  have hρb : ∀ y : Euc d, ‖fderiv ℝ (Torus.lift ρ) y‖ ≤ Λ₀ := fun y =>
    (q84a_fderiv_le_cbNorm_one hρ1 y).trans (U.cbNorm_rho_le (k := 1) le_rfl)
  have hVb : ∀ y : Euc d, ‖fderiv ℝ (Torus.lift V) y‖ ≤ Λ₀ := fun y =>
    (q84a_fderiv_le_cbNorm_one hV1 y).trans (U.cbNorm_V_le (k := 1) le_rfl)
  have hΛ : 0 ≤ Λ₀ := (norm_nonneg _).trans (hρb 0)
  set φ : Torus d → ℝ := convFun (periodicRiesz d s) ρ with hφ
  set Z : ℝ := ∫ y, Real.exp (-β * (V y + φ y)) with hZdef
  have ht : ∀ x, ρ x = Real.exp (-β * (V x + φ x)) / Z := hρ.2
  have hZ : 0 < Z := by
    have h1 := ht 0
    have h2 := hρs.pos 0
    have h3 := Real.exp_pos (-β * (V 0 + φ 0))
    rcases lt_trichotomy Z 0 with h | h | h
    · exfalso
      have : Real.exp (-β * (V 0 + φ 0)) / Z < 0 := div_neg_of_pos_of_neg h3 h
      linarith
    · rw [h, div_zero] at h1; linarith
    · exact h
  have hform : φ = fun x => -β⁻¹ * Real.log (Z * ρ x) - V x := by
    funext x
    have h1 : Z * ρ x = Real.exp (-β * (V x + φ x)) := by
      rw [ht x]; field_simp
    rw [h1, Real.log_exp]
    field_simp
    ring
  have hlift : Torus.lift φ = fun y => -β⁻¹ * Real.log (Z * Torus.lift ρ y) - Torus.lift V y := by
    funext y
    simp only [Torus.lift, Function.comp]
    rw [hform]
  have hne : ∀ y, Z * Torus.lift ρ y ≠ 0 := fun y => (mul_pos hZ (hρs.pos _)).ne'
  have hFx : forceField d s ρ x = (InnerProductSpace.toDual ℝ (Euc d)).symm
      (fderiv ℝ (Torus.lift φ) (Torus.rep x)) := by
    unfold forceField Torus.grad gradient
    rw [q84a_conv_eq hρs]
  rw [hFx, LinearIsometryEquiv.norm_map]
  have hρd : HasFDerivAt (Torus.lift ρ) (fderiv ℝ (Torus.lift ρ) (Torus.rep x)) (Torus.rep x) :=
    ((hρ1.differentiable (by simp)) _).hasFDerivAt
  have hVd : HasFDerivAt (Torus.lift V) (fderiv ℝ (Torus.lift V) (Torus.rep x)) (Torus.rep x) :=
    ((hV1.differentiable (by simp)) _).hasFDerivAt
  have hd := ((((hρd.const_mul Z).log (hne _)).const_mul (-β⁻¹)).sub hVd)
  have h1 : fderiv ℝ (Torus.lift φ) (Torus.rep x) =
      -β⁻¹ • (Z * Torus.lift ρ (Torus.rep x))⁻¹ • Z • fderiv ℝ (Torus.lift ρ) (Torus.rep x)
        - fderiv ℝ (Torus.lift V) (Torus.rep x) := by
    rw [hlift]; exact hd.fderiv
  have hρx : Torus.lift ρ (Torus.rep x) = ρ x := by simp [Torus.lift, Torus.mk_rep]
  rw [h1, hρx]
  refine (norm_sub_le _ _).trans ?_
  have hρx0 : 0 < ρ x := hρs.pos x
  have hc : ‖(-β⁻¹ : ℝ)‖ * (‖(Z * ρ x)⁻¹‖ * ‖Z‖) ≤ βm⁻¹ * c₀⁻¹ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg,
      abs_of_pos (inv_pos.2 hβ), abs_of_pos hZ, abs_of_pos (inv_pos.2 (mul_pos hZ hρx0))]
    have : (Z * ρ x)⁻¹ * Z = (ρ x)⁻¹ := by field_simp
    rw [this]
    exact mul_le_mul hβinv (inv_anti₀ hc0 (U.rho_ge x)) (inv_nonneg.2 hρx0.le) (inv_nonneg.2 hβm.le)
  rw [norm_smul, norm_smul, norm_smul]
  have h2 := mul_le_mul hc (hρb (Torus.rep x)) (norm_nonneg _)
    (mul_nonneg (inv_nonneg.2 hβm.le) (inv_nonneg.2 hc0.le))
  have h3 := hVb (Torus.rep x)
  have hfin : βm⁻¹ * c₀⁻¹ * Λ₀ ≤ |βm⁻¹ * c₀⁻¹| * |Λ₀| :=
    mul_le_mul (le_abs_self _) (le_abs_self _) hΛ (abs_nonneg _)
  calc _ = ‖(-β⁻¹ : ℝ)‖ * (‖(Z * ρ x)⁻¹‖ * ‖Z‖) * ‖fderiv ℝ (Torus.lift ρ) (Torus.rep x)‖ +
        ‖fderiv ℝ (Torus.lift V) (Torus.rep x)‖ := by ring
    _ ≤ |βm⁻¹ * c₀⁻¹| * |Λ₀| + |Λ₀| := add_le_add (h2.trans hfin) (h3.trans (le_abs_self _))

/-- **F5.5 (V-uniform copy of `q84a_estimates_unif`).** One constant `C` for all `V` with `IsSmooth V`,
all `β ∈ [βm, βp]` and all bundle densities `ρ`, all `f, K₁, ψ` as in the original. -/
theorem q84a_estimates_unifV {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp c₀ Λ₀ : ℝ)
    (hβm : 0 < βm) :
    ∃ C : ℝ, ∀ (V : Torus d → ℝ), Torus.IsSmooth V → ∀ β ∈ Icc βm βp, ∀ ρ : Torus d → ℝ,
      HRS.ME.ParxU.ParxU d s 1 βp⁻¹ βm⁻¹ c₀ Λ₀ β V ρ →
      ∀ (f : Torus d → ℝ) (K₁ : ℝ) (ψ : Torus d → Torus d → ℝ), Torus.IsSmooth f →
        IsPairCorrector d s V β ρ f K₁ ψ →
        (∀ x y z, x ≠ y → x ≠ z → y ≠ z → |Gpsi d s ρ ψ x y z| ≤
          C * K₁ * (wEnv s x y * wEnv s x z + wEnv s x y * wEnv s y z + wEnv s x z * wEnv s y z)) ∧
        (∀ x y, x ≠ y → |Bpsi d s ρ ψ x y| ≤ C * K₁ * wEnv s x y ^ 2) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : 1 ≤ s := by rw [hcrit]; linarith
  have hs0 : 0 ≤ s := by linarith
  have hs : 0 < s := by linarith
  have hsd : s < d := by rw [hcrit]; linarith
  obtain ⟨Cg, hCg0, hCg⟩ := q84a_gg_bound hd hs0 hsd
  obtain ⟨M, hM0, hM⟩ := q84a_force_bound_unifV (d := d) s βm βp c₀ Λ₀ hβm
  have h2s : 1 ≤ (2 : ℝ) ^ s := Real.one_le_rpow (by norm_num) hs.le
  refine ⟨8 * Cg * (1 + d) * 2 ^ s + 2 * M + 1 + 8 * Cg + 4 * M,
    fun V hV β hβI ρ hU f K₁ ψ _ hψ => ?_⟩
  have hM := hM V hV β hβI ρ hU
  refine ⟨?_, ?_⟩
  · -- triple bound
    intro x y z hxy hxz hyz
    have hPs : PsiSize s K₁ ψ := hψ.size
    have hsym : IsSymmPair ψ := hψ.symm
    have hK : 0 ≤ K₁ := q84a_K_nonneg hPs hxy
    have hP : 0 ≤ 8 * Cg * (1 + (d : ℝ)) * 2 ^ s * K₁ :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCg0) (by linarith))
        (by positivity)) hK
    have hMK : 0 ≤ M * K₁ := mul_nonneg hM0 hK
    have hwxy := PairCorrAux.one_le_wEnv s x y
    have hwxz := PairCorrAux.one_le_wEnv s x z
    have hwyz := PairCorrAux.one_le_wEnv s y z
    have hwxy0 : 0 < wEnv s x y := by linarith
    have hwxz0 : 0 < wEnv s x z := by linarith
    have hwyz0 : 0 < wEnv s y z := by linarith
    -- the three gradient-difference terms
    have P1 := q84a_Pq_bound hd hs1 hCg0 hCg hPs hxz hxy hyz.symm
    have P2 := q84a_Pq_bound hd hs1 hCg0 hCg hPs hyz hxy.symm hxz.symm
    have P3 := q84a_Pq_bound hd hs1 hCg0 hCg hPs hxy hxz hyz
    rw [PairCorrAux.wEnv_symm s z y] at P1
    rw [PairCorrAux.wEnv_symm s y x, PairCorrAux.wEnv_symm s z x] at P2
    set S := wEnv s x y * wEnv s x z + wEnv s x y * wEnv s y z + wEnv s x z * wEnv s y z with hS
    have hp1 : 0 ≤ wEnv s x y * wEnv s x z := by positivity
    have hp2 : 0 ≤ wEnv s x y * wEnv s y z := by positivity
    have hp3 : 0 ≤ wEnv s x z * wEnv s y z := by positivity
    have hq1 := mul_nonneg (sub_nonneg.2 hwxy) (sub_nonneg.2 hwxz)
    have hq2 := mul_nonneg (sub_nonneg.2 hwxz) (sub_nonneg.2 hwyz)
    have hS1 : wEnv s x y ≤ S := by nlinarith
    have hS2 : wEnv s x z ≤ S := by nlinarith
    have hS3 : wEnv s y z ≤ S := by nlinarith
    have hQ1 : wEnv s x z * wEnv s x y + wEnv s x z * wEnv s y z ≤ S := by nlinarith
    have hQ2 : wEnv s y z * wEnv s x y + wEnv s y z * wEnv s x z ≤ S := by nlinarith
    have hQ3 : wEnv s x y * wEnv s x z + wEnv s x y * wEnv s y z ≤ S := by nlinarith
    have P1' := P1.trans (mul_le_mul_of_nonneg_left hQ1 hP)
    have P2' := P2.trans (mul_le_mul_of_nonneg_left hQ2 hP)
    have P3' := P3.trans (mul_le_mul_of_nonneg_left hQ3 hP)
    -- force terms
    have F1 := q84a_force_term hs1 hPs (hM x) hxy
    have F2 := q84a_force_term hs1 hPs (hM y) hxy.symm
    have F3 := q84a_force_term hs1 hPs (hM x) hxz
    have F4 := q84a_force_term hs1 hPs (hM z) hxz.symm
    have F5 := q84a_force_term hs1 hPs (hM y) hyz
    have F6 := q84a_force_term hs1 hPs (hM z) hyz.symm
    rw [PairCorrAux.wEnv_symm s y x] at F2
    rw [PairCorrAux.wEnv_symm s z x] at F4
    rw [PairCorrAux.wEnv_symm s z y] at F6
    have F1' := F1.trans (mul_le_mul_of_nonneg_left hS1 hMK)
    have F2' := F2.trans (mul_le_mul_of_nonneg_left hS1 hMK)
    have F3' := F3.trans (mul_le_mul_of_nonneg_left hS2 hMK)
    have F4' := F4.trans (mul_le_mul_of_nonneg_left hS2 hMK)
    have F5' := F5.trans (mul_le_mul_of_nonneg_left hS3 hMK)
    have F6' := F6.trans (mul_le_mul_of_nonneg_left hS3 hMK)
    -- the pair projections
    have J1 := hψ.jpair_bound x y hxy
    have J2 := hψ.jpair_bound x z hxz
    have J3 := hψ.jpair_bound y z hyz
    have J1' := J1.trans (mul_le_mul_of_nonneg_left hS1 hK)
    have J2' := J2.trans (mul_le_mul_of_nonneg_left hS2 hK)
    have J3' := J3.trans (mul_le_mul_of_nonneg_left hS3 hK)
    have hS0 : 0 ≤ S := by rw [hS]; positivity
    have hKS : 0 ≤ K₁ * S := mul_nonneg hK hS0
    have hCgS : 0 ≤ (8 * Cg + 4 * M) * (K₁ * S) :=
      mul_nonneg (by positivity) hKS
    unfold Gpsi
    rw [q84a_Tsum_eq hsd hsym x y z]
    rw [abs_le] at P1' P2' P3' F1' F2' F3' F4' F5' F6' J1' J2' J3'
    rw [abs_le]
    constructor <;> linarith [P1'.1, P1'.2, P2'.1, P2'.2, P3'.1, P3'.2, F1'.1, F1'.2, F2'.1, F2'.2,
      F3'.1, F3'.2, F4'.1, F4'.2, F5'.1, F5'.2, F6'.1, F6'.2, J1'.1, J1'.2, J2'.1, J2'.2, J3'.1,
      J3'.2, hCgS]
  · -- pair bound
    intro x y hxy
    have hPs : PsiSize s K₁ ψ := hψ.size
    have hsym : IsSymmPair ψ := hψ.symm
    have hK : 0 ≤ K₁ := q84a_K_nonneg hPs hxy
    have hMK : 0 ≤ M * K₁ := mul_nonneg hM0 hK
    have hr := PairCorrAux.rTrunc_pos hxy
    have hr1 := PairCorrAux.rTrunc_le_one x y
    have hwxy := PairCorrAux.one_le_wEnv s x y
    have hwxy0 : 0 < wEnv s x y := by linarith
    have hrsymm : rTrunc y x = rTrunc x y := PairCorrAux.rTrunc_symm y x
    have hp : 0 ≤ rTrunc x y ^ (-s) := Real.rpow_nonneg hr.le _
    have hGb := q84a_Gb_bound hCg0 hs hCg hxy
    have hA := (q84a_grad_norm hPs hxy).trans
      (mul_le_mul_of_nonneg_left (q84a_one_add_le hr hr1 hs1) hK)
    have hB' := q84a_grad_norm hPs hxy.symm
    rw [hrsymm] at hB'
    have hB := hB'.trans (mul_le_mul_of_nonneg_left (q84a_one_add_le hr hr1 hs1) hK)
    have hΔ : ‖gradFst ψ x y - gradFst ψ y x‖ ≤
        K₁ * (2 * (rTrunc x y * rTrunc x y ^ (-s))) +
        K₁ * (2 * (rTrunc x y * rTrunc x y ^ (-s))) :=
      (norm_sub_le _ _).trans (add_le_add hA hB)
    have hinner := abs_real_inner_le_norm (periodicRieszGrad d s (x - y))
      (gradFst ψ x y - gradFst ψ y x)
    have hprod : ‖periodicRieszGrad d s (x - y)‖ * ‖gradFst ψ x y - gradFst ψ y x‖ ≤
        (2 * Cg * rTrunc x y ^ (-s - 1)) *
          (K₁ * (2 * (rTrunc x y * rTrunc x y ^ (-s))) +
            K₁ * (2 * (rTrunc x y * rTrunc x y ^ (-s)))) :=
      mul_le_mul hGb hΔ (norm_nonneg _) (by positivity)
    have hreq : (2 * Cg * rTrunc x y ^ (-s - 1)) *
        (K₁ * (2 * (rTrunc x y * rTrunc x y ^ (-s))) +
          K₁ * (2 * (rTrunc x y * rTrunc x y ^ (-s)))) =
        8 * Cg * K₁ * (rTrunc x y ^ (-s) * rTrunc x y ^ (-s)) := by
      rw [← q84a_rpow_mul hr s]; ring
    have hpw : rTrunc x y ^ (-s) ≤ wEnv s x y := by unfold wEnv; linarith
    have hsq : rTrunc x y ^ (-s) * rTrunc x y ^ (-s) ≤ wEnv s x y ^ 2 := by nlinarith
    have h8 : 0 ≤ 8 * Cg * K₁ := by positivity
    have hmain : |inner ℝ (periodicRieszGrad d s (x - y)) (gradFst ψ x y - gradFst ψ y x)| ≤
        8 * Cg * K₁ * wEnv s x y ^ 2 := by
      refine hinner.trans (hprod.trans ?_)
      rw [hreq]
      exact mul_le_mul_of_nonneg_left hsq h8
    -- the force terms
    have F1 := q84a_force_term hs1 hPs (hM x) hxy
    have F2 := q84a_force_term hs1 hPs (hM y) hxy.symm
    rw [PairCorrAux.wEnv_symm s y x] at F2
    have hw2 : wEnv s x y ≤ wEnv s x y ^ 2 := by nlinarith
    have F1' := F1.trans (mul_le_mul_of_nonneg_left hw2 hMK)
    have F2' := F2.trans (mul_le_mul_of_nonneg_left hw2 hMK)
    have hKW : 0 ≤ K₁ * wEnv s x y ^ 2 := mul_nonneg hK (by positivity)
    have hCW : 0 ≤ (8 * Cg + 4 * M) * (K₁ * wEnv s x y ^ 2) := mul_nonneg (by positivity) hKW
    have hC0W : 0 ≤ (8 * Cg * (1 + (d : ℝ)) * 2 ^ s + 2 * M + 1) * (K₁ * wEnv s x y ^ 2) :=
      mul_nonneg (by positivity) hKW
    unfold Bpsi Vpsi
    simp only [q84a_gradSnd_eq hsym x y]
    rw [abs_le] at hmain F1' F2'
    rw [abs_le]
    constructor <;> linarith [hmain.1, hmain.2, F1'.1, F1'.2, F2'.1, F2'.2, hCW, hC0W]

/-- **F5.6 (V-uniform copy of `q84e_modified_kernels_uniform_unif`).** `Cu` is chosen after the fixed data
and before `V`, `β`, `ρ`; the conclusion is the original one for every smooth `V`. -/
theorem q84e_modified_kernels_uniform_unifV {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)
    (βm βp c₀ Λ₀ : ℝ) (hβm : 0 < βm) :
    ∃ Cu : ℝ, 0 ≤ Cu ∧ ∀ (V : Torus d → ℝ), Torus.IsSmooth V → ∀ β ∈ Icc βm βp, ∀ ρ : Torus d → ℝ,
      HRS.ME.ParxU.ParxU d s 1 βp⁻¹ βm⁻¹ c₀ Λ₀ β V ρ →
      ∀ (f : Torus d → ℝ) (K₁ : ℝ) (ψ : Torus d → Torus d → ℝ), Torus.IsSmooth f →
      IsPairCorrector d s V β ρ f K₁ ψ →
      IsCanonicalTriple (withDensityReal ρ) (Gpsi d s ρ ψ) →
      ∃ (Jt Bt : Torus d → Torus d → ℝ) (Gt : Torus d → Torus d → Torus d → ℝ),
      (Measurable (fun p : Torus d × Torus d => Jt p.1 p.2) ∧ IsSymmPair Jt ∧
        IsCanonicalPair (withDensityReal ρ) Jt ∧
        ∀ x y, x ≠ y → |Jt x y| ≤ K₁ * wEnv s x y) ∧
      (Measurable (fun p : Torus d × Torus d => Bt p.1 p.2) ∧ IsSymmPair Bt ∧
        ∀ x y, x ≠ y → |Bt x y| ≤ (Cu * K₁) * wEnv s x y ^ 2) ∧
      (Measurable (fun p : Torus d × Torus d × Torus d => Gt p.1 p.2.1 p.2.2) ∧ IsSymmTriple Gt ∧
        IsCanonicalTriple (withDensityReal ρ) Gt ∧
        ∀ x y z, x ≠ y → x ≠ z → y ≠ z → |Gt x y z| ≤
          (Cu * K₁) * (wEnv s x y * wEnv s x z + wEnv s x y * wEnv s y z + wEnv s x z * wEnv s y z)) ∧
      ∀ N : ℕ, 2 ≤ N → ∀ᵐ X ∂(canonicalGibbs (periodicRiesz d s) V N β),
        errStat d s ρ (N := N) ψ X =
          -(2 / (N : ℝ)) * Fstat (N := N) Jt X + (N : ℝ) ^ (-(5 / 2 : ℝ)) * tripleSum Gt X -
            (N : ℝ) ^ (-(5 / 2 : ℝ)) * pairSumOrdered Bt X := by
  obtain ⟨C, hC⟩ := q84a_estimates_unifV (d := d) hd hcrit βm βp c₀ Λ₀ hβm
  refine ⟨|C|, abs_nonneg _, fun V hV β hβI ρ hU f K₁ ψ hf hψ hGcan => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hρs := hU.H.rho_smooth
  have hC := hC V hV β hβI ρ hU
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by rw [hcrit]; linarith
  have hK₁ := q84d_K_nonneg hd hcrit hψ
  have hsm := hψ.size.smooth
  have hsymm := hψ.symm
  obtain ⟨hG, hB⟩ := hC f K₁ ψ hf hψ
  obtain ⟨E, Jh, hE, hE0, hJh, hgood⟩ := q84d_jpair_modification (by omega) hsd hρs hf hψ
  have hJsymm : IsSymmPair (Jpair d s ρ ψ) := fun x y => Q84.q84_Jpair_symm hsymm x y
  obtain ⟨hJm, hJs, hJc, hJb, hJeq⟩ := q84d_Jtil_props (s := s) (by omega) hρs hE hE0 hJsymm hJh hgood
    hψ.jpair_canonical hK₁ hψ.jpair_bound
  have hK : 0 ≤ |C| * K₁ := mul_nonneg (abs_nonneg _) hK₁
  have hB' : ∀ x y : Torus d, x ≠ y → |Bpsi d s ρ ψ x y| ≤ (|C| * K₁) * wEnv s x y ^ 2 := fun x y hxy =>
    (hB x y hxy).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hK₁) (by positivity))
  have hG' : ∀ x y z : Torus d, x ≠ y → x ≠ z → y ≠ z → |Gpsi d s ρ ψ x y z| ≤
      (|C| * K₁) * (wEnv s x y * wEnv s x z + wEnv s x y * wEnv s y z + wEnv s x z * wEnv s y z) := by
    intro x y z hxy hxz hyz
    have w0 : ∀ a b : Torus d, 0 ≤ wEnv s a b := fun a b => zero_le_one.trans (PairCorrAux.one_le_wEnv s a b)
    exact (hG x y z hxy hxz hyz).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hK₁)
      (add_nonneg (add_nonneg (mul_nonneg (w0 _ _) (w0 _ _)) (mul_nonneg (w0 _ _) (w0 _ _)))
        (mul_nonneg (w0 _ _) (w0 _ _))))
  obtain ⟨hBm, hBs, hBb, hBeq⟩ := q84d_Btil_props hsd hsymm hsm hK hB'
  obtain ⟨hGc, hGb⟩ := q84d_Gtil_props (s := s) (by omega) hsd hsymm hsm hE0 hgood hGcan hK hG'
  refine ⟨Jtil E Jh, Btil d s ρ ψ, Gtil d s ρ ψ E Jh, ⟨hJm, hJs, hJc, hJb⟩,
    ⟨hBm, hBs, hBb⟩, ⟨q84d_measurable_Gtil hsd ρ ψ hE hJh, q84d_Gtil_symm ρ ψ E Jh, hGc, hGb⟩, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := by omega
  filter_upwards [q84d_gibbs_ac.ae_le (q84d_ae_not_collision (N := N) (d := d) (by omega)),
    q84d_ae_not_mem_null (V := V) (β := β) (N := N) hE0 (periodicRiesz d s)] with X hX hXE
  have hXne : ∀ a b : Fin N, a ≠ b → X a ≠ X b := fun a b hab hXab => hX ⟨a, b, hab, hXab⟩
  have e1 : pairSumOrdered (Jpair d s ρ ψ) X = pairSumOrdered (Jtil E Jh) X := by
    unfold pairSumOrdered
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
    exact (hJeq _ _ (hXE i) (hXE j) (hXne i j (Finset.ne_of_mem_erase hj).symm)).symm
  have e2 : tripleSum (Gpsi d s ρ ψ) X = tripleSum (Gtil d s ρ ψ E Jh) X := by
    unfold tripleSum
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => ?_
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have hki : k ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
    have hkj : k ≠ j := Finset.ne_of_mem_erase hk
    exact (q84d_Gtil_eq hsymm hsm hsd hgood (hXE i) (hXE j) (hXE k) (hXne i j hji.symm)
      (hXne i k hki.symm) (hXne j k hkj.symm)).symm
  have e3 : pairSumOrdered (Bpsi d s ρ ψ) X = pairSumOrdered (Btil d s ρ ψ) X := by
    unfold pairSumOrdered
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
    exact (hBeq _ _ (hXne i j (Finset.ne_of_mem_erase hj).symm)).symm
  unfold errStat Fstat
  rw [e1, e2, e3]

end HRS.ME.FamU

end
