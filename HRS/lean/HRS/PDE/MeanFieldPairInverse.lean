import HRS.PDE.MeanFieldPairSeries

/-!
# Lemma 4.14, packet P12c: the inverse of the pair generator (package MF-01)

See `HRS/PDE/MeanFieldAdjointPlan.md`, packet P12c.

* `hasDerivAt_pairSemigroup`: `∂_t (U_t^x U_t^y R)(x,y) = (𝒜_x + 𝒜_y)(U_t^x U_t^y R)(x,y)`.
* `pairSemigroup_zero`: `U_0^x U_0^y R = R` for doubly centered `C²` kernels.
* `integral_family_isCk2`: `C^j` regularity of `∫_0^∞ Ψ_t dt` for exponentially decaying families.
* `centeredGen_integral_family`: `-(𝒜_x + 𝒜_y) ∫_0^∞ Ψ_t dt = Ψ_0` when `∂_tΨ = (𝒜_x+𝒜_y)Ψ`.
* `doublyCentered_pairSemigroup`: `U_t^x U_t^y R` is doubly centered.
* `periodic_pair_inverse_aux`: the statement of Lemma 4.14 (`periodic_pair_inverse`), wired in
  `HRS/PDE/MeanField.lean`.

All results use the threshold `3 * mStar d + 2 * d + 8 ≤ J` of `pairSemigroup_eq_tsum`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.MFPair

variable {d : ℕ}

section GeneratorCk

open HRS.PDE HRS.PDE.MFAdjoint

theorem frozen_classical_ck (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ) (hprob : IsProbDensity ρβ)
    (hρC : Torus.IsSmooth ρβ) (hpos : ∀ x, 0 < ρβ x) (ψ : Torus d → ℝ)
    (hψ : Torus.IsCk ((mStar d : ℕ) : WithTop ℕ∞) ψ)
    (T' : ℝ) (hT' : 0 < T') :
    ∃ (R : Regime) (MB Λ VB : ℝ),
      AdjointData s (mStar d) R MB Λ VB (mfData d s hs0 hsd V β hβ) 0 T' (fun _ => ρβ) ∧
      ∃ F : ℝ → Torus d → ℝ,
        IsClassicalAdjointSolution (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) T' ψ F := by
  obtain ⟨R, MB, Λ, VB, hA⟩ := MFSemigroup.adjointData_frozen s hs0 hsd β hβ V hV ρβ hprob hρC hpos (mStar d)
  refine ⟨R, MB, Λ, VB, hA 0 T' hT', ?_⟩
  obtain ⟨C, Cs, -, -, hmain⟩ := adjoint_torus_classical hd s hs0 hsd (mStar d) le_rfl R MB Λ VB
  obtain ⟨hψc, hψm, -, -⟩ := memSob_of_isCk_ps hψ
  obtain ⟨h1, -⟩ := hmain _ 0 T' (fun _ => ρβ) (hA 0 T' hT') T' ⟨hT', le_rfl⟩ ψ hψc hψm
  exact ⟨_, h1⟩

theorem equilibriumSemigroup_generator_ck (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (β : ℝ) (hβ : 0 < β) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρC : Torus.IsSmooth ρβ)
    (hpos : ∀ x, 0 < ρβ x) (ψ : Torus d → ℝ) (hψ : Torus.IsCk ((mStar d : ℕ) : WithTop ℕ∞) ψ) :
    equilibriumSemigroup (mfData d s hs0 hsd V β hβ) ρβ 0 ψ = projMean (withDensityReal ρβ) ψ ∧
    (∀ τ, 0 ≤ τ → pair (withDensityReal ρβ)
      (equilibriumSemigroup (mfData d s hs0 hsd V β hβ) ρβ τ ψ) = 0) ∧
    ∀ x, ∀ τ, 0 ≤ τ →
      HasDerivWithinAt (fun τ' => equilibriumSemigroup (mfData d s hs0 hsd V β hβ) ρβ τ' ψ x)
        (equilibriumGen d s ρβ β⁻¹ (equilibriumSemigroup (mfData d s hs0 hsd V β hβ) ρβ τ ψ) x)
        (Set.Ici 0) τ := by
  set D := mfData d s hs0 hsd V β hβ with hD
  have hprob : IsProbDensity ρβ := hρβ.1
  have := MFSemigroup.isProb_withDensityReal hprob
  have hK : ClassicalAux.ConvKernelFacts d D.s :=
    ClassicalAux.convKernelFacts hd D
  have hV1 : Torus.IsCk 1 D.V := MFSemigroup.isCk_nat_of_isSmooth hV 1
  have hV2 : Torus.IsCk 2 D.V := MFSemigroup.isCk_nat_of_isSmooth hV 2
  have hρ1 : Torus.IsCk 1 ρβ := MFSemigroup.isCk_nat_of_isSmooth hρC 1
  have hρ2 : Torus.IsCk 2 ρβ := MFSemigroup.isCk_nat_of_isSmooth hρC 2
  have hψ2 : Torus.IsCk 2 ψ := hψ.of_le (by have := ClassicalPart.three_le_mStar d; exact_mod_cast (by omega : 2 ≤ mStar d))
  have hρc : Continuous ρβ := ClassicalAux.continuous_of_isCk hρ1
  have h0 : propagator D (fun _ => ρβ) 0 0 ψ = ψ := MFSemigroup.propagator_zero D hK hV1 _ hρ1 hψ2
  refine ⟨?_, fun τ _ => MFSemigroup.pair_projMean _ _, ?_⟩
  · unfold equilibriumSemigroup
    rw [h0]
  intro x τ0 hτ0
  obtain ⟨R, MB, Λ, VB, hA, F, hF⟩ := frozen_classical_ck hd s hs0 hsd β hβ V hV ρβ hprob hρC hpos ψ hψ
    (τ0 + 1) (by linarith)
  set T' := τ0 + 1 with hT'
  have hT0 : 0 < T' := by linarith
  have hlt : τ0 < T' := by linarith
  have hmem : ∀ σ ∈ Set.Icc 0 T', T' - σ ∈ Set.Icc 0 T' := fun σ hσ =>
    ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  have hprop : ∀ σ ∈ Set.Icc 0 T', propagator D (fun _ => ρβ) 0 σ ψ = F (T' - σ) := by
    intro σ hσ
    rcases eq_or_lt_of_le hσ.1 with h | h
    · rw [← h, h0, sub_zero]
      exact hF.terminal.symm
    · exact MFOneLe.propagator_frozen_eq_of_one_le hd s hs0 hsd (mStar d) (by unfold mStar; omega) R MB Λ VB D 0 T'
        ρβ hA ⟨hT0, le_rfl⟩ hF ⟨h, hσ.2⟩
  let G : ℝ → ℝ := fun σ => F (T' - σ) x - pair (withDensityReal ρβ) (F (T' - σ))
  let Gd : ℝ → ℝ := fun σ => backwardGenerator D ρβ (F (T' - σ)) x -
    pair (withDensityReal ρβ) (backwardGenerator D ρβ (F (T' - σ)))
  have hsub : ContinuousOn (fun σ : ℝ => T' - σ) (Set.Icc 0 T') :=
    continuousOn_const.sub continuousOn_id
  have hGcont : ContinuousOn G (Set.Icc 0 T') :=
    ((MFSemigroup.continuousOn_F_apply hF x).comp hsub hmem).sub
      ((MFSemigroup.continuousOn_pair_F hprob hρc hF).comp hsub hmem)
  have hGdcont : ContinuousOn Gd (Set.Icc 0 T') :=
    ((MFSemigroup.continuousOn_bg_apply hF x).comp hsub hmem).sub
      ((MFSemigroup.continuousOn_pair_bg hprob hρc hF).comp hsub hmem)
  have hder : HasDerivWithinAt G (Gd τ0) (Set.Ici 0) τ0 := by
    rcases eq_or_lt_of_le hτ0 with h | h
    · rw [← h]
      exact MFSemigroup.hasDerivWithinAt_Ici_zero hT0
        (fun σ hσ => (MFSemigroup.hasDerivAt_F hF x hσ).sub (MFSemigroup.hasDerivAt_pair_F hprob hρc hF hσ))
        hGcont hGdcont
    · exact ((MFSemigroup.hasDerivAt_F hF x ⟨h, hlt⟩).sub
        (MFSemigroup.hasDerivAt_pair_F hprob hρc hF ⟨h, hlt⟩)).hasDerivWithinAt
  have hS : ∀ σ ∈ Set.Icc 0 T', equilibriumSemigroup D ρβ σ ψ x = G σ := by
    intro σ hσ
    simp only [equilibriumSemigroup, projMean, hprop σ hσ, G]
  have hmem0 : τ0 ∈ Set.Icc 0 T' := ⟨hτ0, hlt.le⟩
  have hval : equilibriumGen d s ρβ β⁻¹ (equilibriumSemigroup D ρβ τ0 ψ) x = Gd τ0 := by
    have hf2 : Torus.IsCk 2 (F (T' - τ0)) := hF.c2 _ (hmem τ0 hmem0)
    have hS0 : equilibriumSemigroup D ρβ τ0 ψ = projMean (withDensityReal ρβ) (F (T' - τ0)) := by
      unfold equilibriumSemigroup
      rw [hprop τ0 hmem0]
    have hord := congrFun (MFOneLe.operator_order_core_of_one_le hd D rfl β hβ rfl hV2 ρβ hρβ hρ2 hpos
      (F (T' - τ0)) hf2) x
    rw [hS0]
    unfold equilibriumGen
    rw [MFSemigroup.lop_projMean]
    exact hord.symm
  have hev : (fun τ' => equilibriumSemigroup D ρβ τ' ψ x) =ᶠ[𝓝[Set.Ici 0] τ0] G := by
    filter_upwards [inter_mem_nhdsWithin (Set.Ici (0 : ℝ)) (Iio_mem_nhds hlt)] with σ hσ
    exact hS σ ⟨hσ.1, hσ.2.le⟩
  exact (hder.congr_of_eventuallyEq hev (hS τ0 hmem0)).congr_deriv hval.symm

end GeneratorCk


/-! ### The pair generator on `C²` functions: linearity, bound, series -/

section OperatorFacts

open HRS.PDE HRS.PDE.MFAdjoint

theorem Lop_eq {ρ : Torus d → ℝ} (hρ : Torus.IsCk 1 ρ) (hpos : ∀ x, 0 < ρ x) {f : Torus d → ℝ}
    (hf : Torus.IsCk 2 f) (x : Torus d) :
    Lop ρ f x = -(Torus.laplacian f x) -
      ∑ j, (Torus.partialDeriv j ρ x / ρ x) * Torus.partialDeriv j f x := by
  unfold Lop
  rw [MFAux.div_smul_grad ρ f hρ hf x]
  have h1 : ∀ j, Torus.partialDeriv j (fun y => ρ y * Torus.partialDeriv j f y) x =
      Torus.partialDeriv j ρ x * Torus.partialDeriv j f x +
        ρ x * Torus.partialDeriv j (Torus.partialDeriv j f) x :=
    fun j => MFAux.partialDeriv_mul j ρ _ hρ (isCk_one_partialDeriv j f hf) x
  simp_rw [h1]
  rw [laplacian_eq_sum f hf x, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hx := (hpos x).ne'
  have e : ∑ j, (Torus.partialDeriv j ρ x / ρ x) * Torus.partialDeriv j f x =
      (ρ x)⁻¹ * ∑ j, Torus.partialDeriv j ρ x * Torus.partialDeriv j f x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by field_simp
  rw [e]
  field_simp
  ring


theorem abs_partialDeriv_le {L : ℕ} (hL : 1 ≤ L) {f : Torus d → ℝ} (hf : Torus.IsCk (L : WithTop ℕ∞) f)
    (j : Fin d) (x : Torus d) : |Torus.partialDeriv j f x| ≤ Torus.cbNorm L f := by
  have h1 : Torus.IsCk 1 f := hf.of_le (by exact_mod_cast hL)
  have e : Torus.partialDeriv j f x = fderiv ℝ (Torus.lift f) (Torus.rep x) (EuclideanSpace.single j 1) := by
    have := partialDeriv_mk j f h1 (Torus.rep x)
    rwa [Torus.mk_rep] at this
  rw [e]
  have h2 := norm_iter_le_cb_ps hf hL (Torus.rep x)
  have h3 : fderiv ℝ (Torus.lift f) (Torus.rep x) (EuclideanSpace.single j 1) =
      iteratedFDeriv ℝ 1 (Torus.lift f) (Torus.rep x) ![EuclideanSpace.single j 1] := by
    rw [iteratedFDeriv_one_apply]; rfl
  rw [h3, ← Real.norm_eq_abs]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  simp only [Finset.univ_unique, Fin.default_eq_zero, Matrix.cons_val_zero, Finset.prod_singleton,
    PiLp.norm_single, norm_one, mul_one]
  exact h2

theorem abs_laplacian_le {L : ℕ} (hL : 2 ≤ L) {f : Torus d → ℝ} (hf : Torus.IsCk (L : WithTop ℕ∞) f)
    (x : Torus d) : |Torus.laplacian f x| ≤ d * Torus.cbNorm L f := by
  have h2 : Torus.IsCk 2 f := hf.of_le (by exact_mod_cast hL)
  have e : Torus.laplacian f x = ∑ j : Fin d, iteratedFDeriv ℝ 2 (Torus.lift f) (Torus.rep x)
      ![EuclideanSpace.single j (1 : ℝ), EuclideanSpace.single j (1 : ℝ)] := by
    have := ClassicalAux.laplacian_mk f h2 (Torus.rep x)
    rwa [Torus.mk_rep] at this
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ j : Fin d, |iteratedFDeriv ℝ 2 (Torus.lift f) (Torus.rep x)
      ![EuclideanSpace.single j (1 : ℝ), EuclideanSpace.single j (1 : ℝ)]| ≤ Torus.cbNorm L f := by
    intro j
    rw [← Real.norm_eq_abs]
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    simp [Fin.prod_univ_two]
    exact norm_iter_le_cb_ps hf hL (Torus.rep x)
  calc _ ≤ ∑ j : Fin d, Torus.cbNorm L f := Finset.sum_le_sum fun j _ => this j
    _ = _ := by simp

theorem abs_Lop_le {ρ : Torus d → ℝ} (hρ : Torus.IsCk 1 ρ) (hpos : ∀ x, 0 < ρ x) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : Torus d → ℝ, Torus.IsCk 2 f → ∀ x, |Lop ρ f x| ≤ K * Torus.cbNorm 2 f := by
  have hρc : Continuous ρ := MFAux.continuous_of_isCk hρ
  have hc : Continuous fun x : Torus d => ∑ j, |Torus.partialDeriv j ρ x / ρ x| :=
    continuous_finsetSum _ fun j _ =>
      ((continuous_partialDeriv j ρ hρ).div hρc fun x => (hpos x).ne').abs
  obtain ⟨C, hC⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hc.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (Set.mem_univ _))
  refine ⟨d + C, by positivity, fun f hf x => ?_⟩
  rw [Lop_eq hρ hpos hf x]
  have h1 := abs_laplacian_le (L := 2) le_rfl hf x
  have hcb := cbNorm_nonneg_ps (d := d) 2 f
  have h2 : |∑ j, (Torus.partialDeriv j ρ x / ρ x) * Torus.partialDeriv j f x| ≤ C * Torus.cbNorm 2 f := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hCx : ∑ j, |Torus.partialDeriv j ρ x / ρ x| ≤ C := by
      have := hC x (Set.mem_univ _)
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)] at this
      exact this
    calc ∑ j, |(Torus.partialDeriv j ρ x / ρ x) * Torus.partialDeriv j f x|
        ≤ ∑ j, |Torus.partialDeriv j ρ x / ρ x| * Torus.cbNorm 2 f := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (abs_partialDeriv_le (L := 2) (by norm_num) hf j x)
            (abs_nonneg _)
      _ = (∑ j, |Torus.partialDeriv j ρ x / ρ x|) * Torus.cbNorm 2 f := by rw [Finset.sum_mul]
      _ ≤ C * Torus.cbNorm 2 f := mul_le_mul_of_nonneg_right hCx hcb
  calc |-(Torus.laplacian f x) - ∑ j, (Torus.partialDeriv j ρ x / ρ x) * Torus.partialDeriv j f x|
      ≤ |-(Torus.laplacian f x)| + |∑ j, (Torus.partialDeriv j ρ x / ρ x) * Torus.partialDeriv j f x| :=
        abs_sub _ _
    _ ≤ d * Torus.cbNorm 2 f + C * Torus.cbNorm 2 f := by rw [abs_neg]; exact add_le_add h1 h2
    _ = _ := by ring

theorem laplacian_sub_fun {f g : Torus d → ℝ} (hf : Torus.IsCk 2 f) (hg : Torus.IsCk 2 g) (x : Torus d) :
    Torus.laplacian (fun y => f y - g y) x = Torus.laplacian f x - Torus.laplacian g x := by
  have hfg : Torus.IsCk 2 (fun y => f y - g y) := isCk_sub_ps hf hg
  rw [laplacian_eq_sum _ hfg, laplacian_eq_sum _ hf, laplacian_eq_sum _ hg, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : Torus.partialDeriv j (fun y => f y - g y) =
      fun y => Torus.partialDeriv j f y - Torus.partialDeriv j g y :=
    funext fun y => MFAdjoint.partialDeriv_sub' j (hf.of_le (by norm_num)) (hg.of_le (by norm_num)) y
  rw [e]
  exact MFAdjoint.partialDeriv_sub' j (isCk_one_partialDeriv j f hf) (isCk_one_partialDeriv j g hg) x

theorem laplacian_smul_fun {f : Torus d → ℝ} (hf : Torus.IsCk 2 f) (a : ℝ) (x : Torus d) :
    Torus.laplacian (fun y => a * f y) x = a * Torus.laplacian f x := by
  have hf' : Torus.IsCk 2 (fun y => a * f y) := by
    unfold Torus.IsCk
    exact contDiff_const.mul hf
  rw [laplacian_eq_sum _ hf', laplacian_eq_sum _ hf, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : Torus.partialDeriv j (fun y => a * f y) =
      fun y => a * Torus.partialDeriv j f y :=
    funext fun y => MFHolder.partialDeriv_const_mul j (hf.of_le (by norm_num)) a y
  rw [e]
  exact MFHolder.partialDeriv_const_mul j (isCk_one_partialDeriv j f hf) a x

theorem Lop_sub_fun {ρ : Torus d → ℝ} (hρ : Torus.IsCk 1 ρ) (hpos : ∀ x, 0 < ρ x) {f g : Torus d → ℝ}
    (hf : Torus.IsCk 2 f) (hg : Torus.IsCk 2 g) (x : Torus d) :
    Lop ρ (fun y => f y - g y) x = Lop ρ f x - Lop ρ g x := by
  have hfg : Torus.IsCk 2 (fun y => f y - g y) := isCk_sub_ps hf hg
  rw [Lop_eq hρ hpos hfg, Lop_eq hρ hpos hf, Lop_eq hρ hpos hg, laplacian_sub_fun hf hg]
  have e : ∀ j, Torus.partialDeriv j (fun y => f y - g y) x =
      Torus.partialDeriv j f x - Torus.partialDeriv j g x := fun j =>
    MFAdjoint.partialDeriv_sub' j (hf.of_le (by norm_num)) (hg.of_le (by norm_num)) x
  simp_rw [e, mul_sub, Finset.sum_sub_distrib]
  ring

theorem Lop_smul_fun {ρ : Torus d → ℝ} (hρ : Torus.IsCk 1 ρ) (hpos : ∀ x, 0 < ρ x) {f : Torus d → ℝ}
    (hf : Torus.IsCk 2 f) (a : ℝ) (x : Torus d) :
    Lop ρ (fun y => a * f y) x = a * Lop ρ f x := by
  have hf' : Torus.IsCk 2 (fun y => a * f y) := by
    unfold Torus.IsCk
    exact contDiff_const.mul hf
  rw [Lop_eq hρ hpos hf', Lop_eq hρ hpos hf, laplacian_smul_fun hf]
  have e : ∀ j, Torus.partialDeriv j (fun y => a * f y) x = a * Torus.partialDeriv j f x := fun j =>
    MFHolder.partialDeriv_const_mul j (hf.of_le (by norm_num)) a x
  simp_rw [e]
  rw [mul_sub, mul_neg, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring


section KopFacts

variable {s : ℝ} {ρ : Torus d → ℝ}

theorem Kop_eq' (hprob : IsProbDensity ρ) (h : Torus d → ℝ) (x : Torus d) :
    Kop (periodicRiesz d s) (withDensityReal ρ) h x =
      convFun (periodicRiesz d s) (fun y => ρ y * h y) x -
        ∫ z, ρ z * convFun (periodicRiesz d s) (fun y => ρ y * h y) z := by
  rw [MFAdjoint.kop_eq s hprob h]
  simp only
  rw [MFAdjoint.pair_mu hprob]

theorem abs_Kop_le (hg : Integrable (periodicRiesz d s)) (hprob : IsProbDensity ρ)
    (hρc : Continuous ρ) {Λ : ℝ} (hΛ : ∀ x, ρ x ≤ Λ) {h : Torus d → ℝ} (hh : Continuous h) {M : ℝ}
    (hM : ∀ y, |h y| ≤ M) (x : Torus d) :
    |Kop (periodicRiesz d s) (withDensityReal ρ) h x| ≤
      2 * ((∫ y, |periodicRiesz d s y|) * (Λ * M)) := by
  rw [Kop_eq' hprob h x]
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hΛ0 : 0 ≤ Λ := (hprob.nonneg 0).trans (hΛ 0)
  have hb : ∀ y, |ρ y * h y| ≤ Λ * M := fun y => by
    rw [abs_mul, abs_of_nonneg (hprob.nonneg y)]
    exact mul_le_mul (hΛ y) (hM y) (abs_nonneg _) hΛ0
  have h1 : ∀ z, |convFun (periodicRiesz d s) (fun y => ρ y * h y) z| ≤
      (∫ y, |periodicRiesz d s y|) * (Λ * M) := fun z =>
    MFThermalExist.convFun_bound_of_le hg hb z
  have hG0 : 0 ≤ (∫ y, |periodicRiesz d s y|) * (Λ * M) :=
    mul_nonneg (integral_nonneg fun _ => abs_nonneg _) (mul_nonneg hΛ0 hM0)
  have hcont : Continuous (convFun (periodicRiesz d s) (fun y => ρ y * h y)) :=
    MFAux.continuous_convFun hg (hρc.mul hh)
  have h2 : |∫ z, ρ z * convFun (periodicRiesz d s) (fun y => ρ y * h y) z| ≤
      (∫ y, |periodicRiesz d s y|) * (Λ * M) := by
    rw [← Real.norm_eq_abs]
    have hi : Integrable (fun z => ρ z * ((∫ y, |periodicRiesz d s y|) * (Λ * M))) :=
      (MFAdjoint.integrable_of_cont hρc).mul_const _
    calc ‖∫ z, ρ z * convFun (periodicRiesz d s) (fun y => ρ y * h y) z‖
        ≤ ∫ z, ρ z * ((∫ y, |periodicRiesz d s y|) * (Λ * M)) := by
          refine norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall fun z => ?_)
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hprob.nonneg z)]
          exact mul_le_mul_of_nonneg_left (h1 z) (hprob.nonneg z)
      _ = (∫ y, |periodicRiesz d s y|) * (Λ * M) := by
          rw [integral_mul_const, hprob.integral_one, one_mul]
  calc _ ≤ |convFun (periodicRiesz d s) (fun y => ρ y * h y) x| +
        |∫ z, ρ z * convFun (periodicRiesz d s) (fun y => ρ y * h y) z| := abs_sub _ _
    _ ≤ _ := by linarith [h1 x]

theorem Kop_sub_fun (hg : Integrable (periodicRiesz d s)) (hprob : IsProbDensity ρ)
    (hρc : Continuous ρ) {h₁ h₂ : Torus d → ℝ} (h1 : Continuous h₁) (h2 : Continuous h₂)
    (x : Torus d) :
    Kop (periodicRiesz d s) (withDensityReal ρ) (fun y => h₁ y - h₂ y) x =
      Kop (periodicRiesz d s) (withDensityReal ρ) h₁ x -
        Kop (periodicRiesz d s) (withDensityReal ρ) h₂ x := by
  rw [Kop_eq' hprob, Kop_eq' hprob h₁, Kop_eq' hprob h₂]
  have e : (fun y => ρ y * (h₁ y - h₂ y)) = fun y => ρ y * h₁ y - ρ y * h₂ y := by
    funext y; ring
  have hc1 : Continuous fun y => ρ y * h₁ y := hρc.mul h1
  have hc2 : Continuous fun y => ρ y * h₂ y := hρc.mul h2
  have hsub : ∀ z, convFun (periodicRiesz d s) (fun y => ρ y * h₁ y - ρ y * h₂ y) z =
      convFun (periodicRiesz d s) (fun y => ρ y * h₁ y) z -
        convFun (periodicRiesz d s) (fun y => ρ y * h₂ y) z := fun z =>
    MFThermal.convFun_sub hg hc1 hc2 z
  rw [e]
  simp_rw [hsub]
  have hcv1 := MFAux.continuous_convFun hg hc1
  have hcv2 := MFAux.continuous_convFun hg hc2
  have : ∫ z, ρ z * (convFun (periodicRiesz d s) (fun y => ρ y * h₁ y) z -
        convFun (periodicRiesz d s) (fun y => ρ y * h₂ y) z) =
      (∫ z, ρ z * convFun (periodicRiesz d s) (fun y => ρ y * h₁ y) z) -
        ∫ z, ρ z * convFun (periodicRiesz d s) (fun y => ρ y * h₂ y) z := by
    simp_rw [mul_sub]
    exact integral_sub (MFAdjoint.integrable_of_cont (hρc.mul hcv1))
      (MFAdjoint.integrable_of_cont (hρc.mul hcv2))
  rw [this]
  ring

theorem Kop_smul_fun (hprob : IsProbDensity ρ) (h : Torus d → ℝ) (a : ℝ) (x : Torus d) :
    Kop (periodicRiesz d s) (withDensityReal ρ) (fun y => a * h y) x =
      a * Kop (periodicRiesz d s) (withDensityReal ρ) h x := by
  rw [Kop_eq' hprob, Kop_eq' hprob h]
  have e : ∀ z, convFun (periodicRiesz d s) (fun y => ρ y * (a * h y)) z =
      a * convFun (periodicRiesz d s) (fun y => ρ y * h y) z := by
    intro z
    unfold convFun
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    ring
  simp_rw [e]
  have : ∫ z, ρ z * (a * convFun (periodicRiesz d s) (fun y => ρ y * h y) z) =
      a * ∫ z, ρ z * convFun (periodicRiesz d s) (fun y => ρ y * h y) z := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    ring
  rw [this]
  ring

end KopFacts


section GenFacts

variable (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
  (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
  (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρC : Torus.IsSmooth ρβ)
  (hpos : ∀ x, 0 < ρβ x)

include hd hV hρβ hρC hpos

theorem centeredGen_eq {f : Torus d → ℝ} (hf : Torus.IsCk 2 f) :
    centeredGen (mfData d s hs0 hsd V β hβ) ρβ f = fun x =>
      -(β⁻¹ * Lop ρβ f x + Kop (periodicRiesz d s) (withDensityReal ρβ) (Lop ρβ f) x) := by
  have hV2 : Torus.IsCk 2 V := isCk_of_smooth_ps hV 2
  have hρ2 : Torus.IsCk 2 ρβ := isCk_of_smooth_ps hρC 2
  exact MFOneLe.operator_order_core_of_one_le hd (mfData d s hs0 hsd V β hβ) rfl β hβ rfl hV2 ρβ
    hρβ hρ2 hpos f hf

theorem centeredGen_sub_fun {f g : Torus d → ℝ} (hf : Torus.IsCk 2 f) (hg : Torus.IsCk 2 g) (x : Torus d) :
    centeredGen (mfData d s hs0 hsd V β hβ) ρβ (fun y => f y - g y) x =
      centeredGen (mfData d s hs0 hsd V β hβ) ρβ f x -
        centeredGen (mfData d s hs0 hsd V β hβ) ρβ g x := by
  have hρ1 : Torus.IsCk 1 ρβ := isCk_of_smooth_ps hρC 1
  have hρc : Continuous ρβ := MFAux.continuous_of_isCk hρ1
  have hprob : IsProbDensity ρβ := hρβ.1
  have hfg : Torus.IsCk 2 (fun y => f y - g y) := isCk_sub_ps hf hg
  rw [centeredGen_eq hd s hs0 hsd β hβ V hV ρβ hρβ hρC hpos hfg,
    centeredGen_eq hd s hs0 hsd β hβ V hV ρβ hρβ hρC hpos hf,
    centeredGen_eq hd s hs0 hsd β hβ V hV ρβ hρβ hρC hpos hg]
  have e : Lop ρβ (fun y => f y - g y) = fun y => Lop ρβ f y - Lop ρβ g y :=
    funext fun y => Lop_sub_fun hρ1 hpos hf hg y
  simp only
  rw [e, Kop_sub_fun (MFOneLe.integrable_periodicRiesz hd s hs0 hsd) hprob hρc
    (MFAdjoint.continuous_lop hprob hρ1 hpos hf) (MFAdjoint.continuous_lop hprob hρ1 hpos hg) x]
  simp only [mul_sub]
  ring

theorem centeredGen_smul_fun {f : Torus d → ℝ} (hf : Torus.IsCk 2 f) (a : ℝ) (x : Torus d) :
    centeredGen (mfData d s hs0 hsd V β hβ) ρβ (fun y => a * f y) x =
      a * centeredGen (mfData d s hs0 hsd V β hβ) ρβ f x := by
  have hρ1 : Torus.IsCk 1 ρβ := isCk_of_smooth_ps hρC 1
  have hprob : IsProbDensity ρβ := hρβ.1
  have hf' : Torus.IsCk 2 (fun y => a * f y) := by
    unfold Torus.IsCk
    exact contDiff_const.mul hf
  rw [centeredGen_eq hd s hs0 hsd β hβ V hV ρβ hρβ hρC hpos hf',
    centeredGen_eq hd s hs0 hsd β hβ V hV ρβ hρβ hρC hpos hf]
  have e : Lop ρβ (fun y => a * f y) = fun y => a * Lop ρβ f y :=
    funext fun y => Lop_smul_fun hρ1 hpos hf a y
  simp only
  rw [e, Kop_smul_fun hprob (Lop ρβ f) a x]
  ring

theorem abs_centeredGen_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : Torus d → ℝ, Torus.IsCk 2 f → ∀ x,
      |centeredGen (mfData d s hs0 hsd V β hβ) ρβ f x| ≤ K * Torus.cbNorm 2 f := by
  have hρ1 : Torus.IsCk 1 ρβ := isCk_of_smooth_ps hρC 1
  have hρc : Continuous ρβ := MFAux.continuous_of_isCk hρ1
  have hprob : IsProbDensity ρβ := hρβ.1
  have hg := MFOneLe.integrable_periodicRiesz hd s hs0 hsd
  obtain ⟨K1, hK1, hL⟩ := abs_Lop_le hρ1 hpos
  obtain ⟨Λ, hΛ⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hρc.continuousOn
  have hΛ' : ∀ x, ρβ x ≤ |Λ| := fun x => by
    have := hΛ x (Set.mem_univ _)
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_abs_self _))
  set G1 := ∫ y, |periodicRiesz d s y| with hG1
  have hG10 : 0 ≤ G1 := integral_nonneg fun _ => abs_nonneg _
  refine ⟨β⁻¹ * K1 + 2 * (G1 * (|Λ| * K1)), by positivity, fun f hf x => ?_⟩
  rw [centeredGen_eq hd s hs0 hsd β hβ V hV ρβ hρβ hρC hpos hf]
  simp only
  have hcb := cbNorm_nonneg_ps (d := d) 2 f
  have h1 := hL f hf x
  have h2 := abs_Kop_le hg hprob hρc hΛ' (MFAdjoint.continuous_lop hprob hρ1 hpos hf)
    (M := K1 * Torus.cbNorm 2 f) (fun y => hL f hf y) x
  rw [abs_neg]
  calc |β⁻¹ * Lop ρβ f x + Kop (periodicRiesz d s) (withDensityReal ρβ) (Lop ρβ f) x|
      ≤ |β⁻¹ * Lop ρβ f x| + |Kop (periodicRiesz d s) (withDensityReal ρβ) (Lop ρβ f) x| :=
        abs_add_le _ _
    _ ≤ β⁻¹ * (K1 * Torus.cbNorm 2 f) + 2 * (G1 * (|Λ| * (K1 * Torus.cbNorm 2 f))) := by
        refine add_le_add ?_ h2
        rw [abs_mul, abs_of_pos (inv_pos.2 hβ)]
        exact mul_le_mul_of_nonneg_left h1 (inv_pos.2 hβ).le
    _ = _ := by ring


theorem centeredGen_add_fun {f g : Torus d → ℝ} (hf : Torus.IsCk 2 f) (hg : Torus.IsCk 2 g) (x : Torus d) :
    centeredGen (mfData d s hs0 hsd V β hβ) ρβ (fun y => f y + g y) x =
      centeredGen (mfData d s hs0 hsd V β hβ) ρβ f x +
        centeredGen (mfData d s hs0 hsd V β hβ) ρβ g x := by
  have hg' : Torus.IsCk 2 (fun y => (-1 : ℝ) * g y) := by
    unfold Torus.IsCk
    exact contDiff_const.mul hg
  have e : (fun y => f y + g y) = fun y => f y - (-1 : ℝ) * g y := by
    funext y; ring
  rw [e, centeredGen_sub_fun hd s hs0 hsd β hβ V hV ρβ hρβ hρC hpos hf hg',
    centeredGen_smul_fun hd s hs0 hsd β hβ V hV ρβ hρβ hρC hpos hg]
  ring

theorem centeredGen_zero_fun (x : Torus d) :
    centeredGen (mfData d s hs0 hsd V β hβ) ρβ (fun _ => (0 : ℝ)) x = 0 := by
  have h0 : Torus.IsCk 2 (fun _ : Torus d => (1 : ℝ)) := contDiff_const
  have := centeredGen_smul_fun hd s hs0 hsd β hβ V hV ρβ hρβ hρC hpos h0 0 x
  simpa using this

theorem centeredGen_finset_sum {ι : Type*} (g : ι → Torus d → ℝ) (hg : ∀ i, Torus.IsCk 2 (g i))
    (t : Finset ι) [DecidableEq ι] (x : Torus d) :
    centeredGen (mfData d s hs0 hsd V β hβ) ρβ (fun y => ∑ i ∈ t, g i y) x =
      ∑ i ∈ t, centeredGen (mfData d s hs0 hsd V β hβ) ρβ (g i) x := by
  induction t using Finset.induction_on with
  | empty => simpa using centeredGen_zero_fun hd s hs0 hsd β hβ V hV ρβ hρβ hρC hpos x
  | insert a t ha ih =>
    have hck : Torus.IsCk 2 (fun y => ∑ i ∈ t, g i y) := by
      unfold Torus.IsCk
      exact ContDiff.sum fun i _ => hg i
    simp only [Finset.sum_insert ha]
    rw [centeredGen_add_fun hd s hs0 hsd β hβ V hV ρβ hρβ hρC hpos (hg a) hck, ih]

theorem centeredGen_tsum (g : Lattice d → Torus d → ℝ) (hg : ∀ k, Torus.IsCk 2 (g k))
    (hs : Summable fun k => Torus.cbNorm 2 (g k)) (x : Torus d) :
    Torus.IsCk 2 (fun y => ∑' k, g k y) ∧
      HasSum (fun k => centeredGen (mfData d s hs0 hsd V β hβ) ρβ (g k) x)
        (centeredGen (mfData d s hs0 hsd V β hβ) ρβ (fun y => ∑' k, g k y) x) := by
  classical
  obtain ⟨K, hK0, hK⟩ := abs_centeredGen_le hd s hs0 hsd β hβ V hV ρβ hρβ hρC hpos
  obtain ⟨hCk, -⟩ := isCk_tsum_cbNorm_ps 2 g hg hs
  refine ⟨hCk, ?_⟩
  have hsum : ∀ y, Summable fun k => g k y := fun y =>
    Summable.of_norm_bounded hs (fun k => by
      rw [Real.norm_eq_abs]; exact abs_le_cb_ps (hg k) y)
  have htail := tendsto_tsum_compl_atTop_zero (fun k => Torus.cbNorm 2 (g k))
  unfold HasSum
  rw [tendsto_iff_dist_tendsto_zero]
  have hbound : ∀ F : Finset (Lattice d),
      dist (∑ k ∈ F, centeredGen (mfData d s hs0 hsd V β hβ) ρβ (g k) x)
        (centeredGen (mfData d s hs0 hsd V β hβ) ρβ (fun y => ∑' k, g k y) x) ≤
      K * (3 * ∑' k : {k // k ∉ F}, Torus.cbNorm 2 (g k)) := by
    intro F
    have hF : Torus.IsCk 2 (fun y => ∑ k ∈ F, g k y) := by
      unfold Torus.IsCk
      exact ContDiff.sum fun i _ => hg i
    have hres : (fun y => (∑' k, g k y) - ∑ k ∈ F, g k y) = fun y => ∑' k : {k // k ∉ F}, g k y := by
      funext y
      have : ∑ x ∈ F, g x y + ∑' k : {k // k ∉ F}, g k y = ∑' k, g k y :=
        (hsum y).sum_add_tsum_compl (s := F)
      linarith
    have hsub := hs.subtype {k | k ∉ F}
    obtain ⟨hCk', hnorm⟩ := isCk_tsum_cbNorm_ps 2 (fun k : {k // k ∉ F} => g k) (fun k => hg k)
      (hs.subtype _)
    have h1 := centeredGen_sub_fun hd s hs0 hsd β hβ V hV ρβ hρβ hρC hpos hCk hF x
    rw [hres] at h1
    rw [centeredGen_finset_sum hd s hs0 hsd β hβ V hV ρβ hρβ hρC hpos g hg F x] at h1
    have h2 := hK _ hCk' x
    have hn : (((2 : ℕ) : ℝ) + 1) = 3 := by norm_num
    rw [hn] at hnorm
    rw [Real.dist_eq]
    have e : ∑ k ∈ F, centeredGen (mfData d s hs0 hsd V β hβ) ρβ (g k) x -
        centeredGen (mfData d s hs0 hsd V β hβ) ρβ (fun y => ∑' k, g k y) x =
        -centeredGen (mfData d s hs0 hsd V β hβ) ρβ (fun y => ∑' k : {k // k ∉ F}, g k y) x := by
      rw [h1]; ring
    rw [e, abs_neg]
    exact h2.trans (mul_le_mul_of_nonneg_left hnorm hK0)
  refine squeeze_zero (fun F => dist_nonneg) hbound ?_
  simpa using (htail.const_mul 3).const_mul K

end GenFacts

end OperatorFacts


/-! ### Term data for the Fourier series of `pairSemigroup` -/

section TermData

open HRS.PDE HRS.PDE.MFAdjoint

theorem term_data (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρC : Torus.IsSmooth ρβ)
    (hpos : ∀ x, 0 < ρβ x) (J : ℕ) (hJ : 3 * mStar d + 2 * d + 8 ≤ J) (R : Torus d → Torus d → ℝ)
    (hR : IsCk2 J R) :
    ∃ Bc Ba : Lattice d → ℝ, (∀ k, 0 ≤ Bc k) ∧ (∀ k, 0 ≤ Ba k) ∧ (Summable fun k => Bc k * Ba k) ∧
      (∀ k, Torus.IsCk ((mStar d : ℕ) : WithTop ℕ∞) (Torus.cosMode k) ∧
        Torus.IsCk ((mStar d : ℕ) : WithTop ℕ∞) (Torus.sinMode k) ∧
        Torus.IsCk ((mStar d : ℕ) : WithTop ℕ∞) (fun y' => (sliceCoeff R k y').re) ∧
        Torus.IsCk ((mStar d : ℕ) : WithTop ℕ∞) (fun y' => (sliceCoeff R k y').im)) ∧
      ∀ k t, 0 ≤ t →
        (Torus.IsCk 2 (equilibriumSemigroup (mfData d s hs0 hsd V β hβ) ρβ t (Torus.cosMode k)) ∧
          Torus.cbNorm 2 (equilibriumSemigroup (mfData d s hs0 hsd V β hβ) ρβ t (Torus.cosMode k)) ≤ Bc k) ∧
        (Torus.IsCk 2 (equilibriumSemigroup (mfData d s hs0 hsd V β hβ) ρβ t (Torus.sinMode k)) ∧
          Torus.cbNorm 2 (equilibriumSemigroup (mfData d s hs0 hsd V β hβ) ρβ t (Torus.sinMode k)) ≤ Bc k) ∧
        (Torus.IsCk 2 (equilibriumSemigroup (mfData d s hs0 hsd V β hβ) ρβ t (fun y' => (sliceCoeff R k y').re)) ∧
          Torus.cbNorm 2 (equilibriumSemigroup (mfData d s hs0 hsd V β hβ) ρβ t
            (fun y' => (sliceCoeff R k y').re)) ≤ Ba k) ∧
        (Torus.IsCk 2 (equilibriumSemigroup (mfData d s hs0 hsd V β hβ) ρβ t (fun y' => (sliceCoeff R k y').im)) ∧
          Torus.cbNorm 2 (equilibriumSemigroup (mfData d s hs0 hsd V β hβ) ρβ t
            (fun y' => (sliceCoeff R k y').im)) ≤ Ba k) := by
  have hd1 : 1 ≤ d := by omega
  have h3 := ClassicalPart.three_le_mStar d
  have hmst := MFAdjoint.mStar_gt d
  set L : ℕ := mStar d + 4 with hL
  have hJL : 2 * L + d + 1 ≤ J := by omega
  obtain ⟨c₀, Λ₀, H⟩ := frozenHyp_of_smooth s hs0 hsd β hβ V hV ρβ hρβ hρC hpos (L + mStar d)
  have hjL : (d : ℝ) / 2 + ((2 : ℕ) : ℝ) < (L : ℝ) := by
    rw [hL]; push_cast; linarith
  obtain ⟨M, c, hM, hc, hbd⟩ := S_cb_bound hd1 s 2 L (by omega) hjL β⁻¹ β⁻¹ c₀ Λ₀
  obtain ⟨C0, hC0, hsl0⟩ := exists_sliceCoeff_bound (d := d) 0 J
  obtain ⟨C1, hC1, hsl1⟩ := exists_sliceCoeff_bound (d := d) L (J - L)
  have hG0 : 0 ≤ cbNorm2 J R :=
    Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
  set G := cbNorm2 J R with hG
  have hSbd : ∀ (h : Torus d → ℝ) (B : ℝ), Torus.IsCk (L : WithTop ℕ∞) h → Torus.cbNorm L h ≤ B →
      ∀ t, 0 ≤ t →
        Torus.IsCk 2 (equilibriumSemigroup (mfData d s hs0 hsd V β hβ) ρβ t h) ∧
        Torus.cbNorm 2 (equilibriumSemigroup (mfData d s hs0 hsd V β hβ) ρβ t h) ≤ M * B := by
    intro h B hh hB t ht
    obtain ⟨h1, h2⟩ := hbd β V ρβ H h hh t ht
    refine ⟨by exact_mod_cast h1, ?_⟩
    have hexp : Real.exp (-c * t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have hcb := cbNorm_nonneg_ps L h
    calc _ ≤ M * Real.exp (-c * t) * Torus.cbNorm L h := h2
      _ ≤ M * 1 * Torus.cbNorm L h := by gcongr
      _ ≤ M * B := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hB hM.le
  have hcos : ∀ k : Lattice d, Torus.cbNorm L (Torus.cosMode k) ≤ (L + 1) * Lattice.jp k ^ L := by
    intro k
    have := cbNorm_trigTerm_le 1 0 k L
    rw [← cosMode_eq_trig] at this
    simpa using this
  have hsin : ∀ k : Lattice d, Torus.cbNorm L (Torus.sinMode k) ≤ (L + 1) * Lattice.jp k ^ L := by
    intro k
    have := cbNorm_trigTerm_le 0 1 k L
    rw [← sinMode_eq_trig] at this
    simpa using this
  have hjpsum2 : Summable fun k : Lattice d =>
      Lattice.jp k ^ ((L : ℝ) + -((J - L : ℕ) : ℝ)) :=
    summable_jp_rpow_ps _ (by
      have : (2 * L + d + 1 : ℝ) ≤ J := by exact_mod_cast hJL
      rw [Nat.cast_sub (by omega : L ≤ J)]
      have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
      linarith)
  refine ⟨fun k => M * ((L + 1) * Lattice.jp k ^ L),
    fun k => M * (C1 * G * Lattice.jp k ^ (-((J - L : ℕ) : ℝ))), ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    have := Torus.jp_pos (d := d) k
    positivity
  · intro k
    have := Torus.jp_pos (d := d) k
    positivity
  · refine (hjpsum2.mul_left (M * ((L + 1) * (M * (C1 * G))))).congr fun k => ?_
    rw [← jp_pow_mul_rpow_ps k L]
    ring
  · intro k
    obtain ⟨h1, h2, -, -⟩ := hsl1 J (by omega) R hR k
    exact ⟨isCk_cos_ps k _, isCk_sin_ps k _, h1.of_le (by exact_mod_cast (by omega : mStar d ≤ L)),
      h2.of_le (by exact_mod_cast (by omega : mStar d ≤ L))⟩
  · intro k t ht
    obtain ⟨h1, h2, h3', h4⟩ := hsl1 J (by omega) R hR k
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hcb := hSbd _ _ (isCk_cos_ps k L) (hcos k) t ht
      exact ⟨hcb.1, hcb.2⟩
    · have hcb := hSbd _ _ (isCk_sin_ps k L) (hsin k) t ht
      exact ⟨hcb.1, hcb.2⟩
    · have hcb := hSbd _ _ h1 h3' t ht
      exact ⟨hcb.1, hcb.2⟩
    · have hcb := hSbd _ _ h2 h4 t ht
      exact ⟨hcb.1, hcb.2⟩

end TermData

theorem hasDerivWithinAt_tsum_Ici {ι : Type*} (f f' : ι → ℝ → ℝ) (u : ι → ℝ) (hu : Summable u)
    (hf : ∀ k t, 0 ≤ t → HasDerivWithinAt (f k) (f' k t) (Set.Ici 0) t)
    (hbd : ∀ k t, 0 ≤ t → |f' k t| ≤ u k)
    (hsum : ∀ t, 0 ≤ t → Summable fun k => f k t) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun t' => ∑' k, f k t') (∑' k, f' k t) (Set.Ici 0) t := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hpt : ∀ k, Tendsto (fun y => slope (f k) t y) (𝓝[Set.Ici 0 \ {t}] t) (𝓝 (f' k t)) := fun k =>
    hasDerivWithinAt_iff_tendsto_slope.1 (hf k t ht)
  have hmem : Set.Ici (0 : ℝ) \ {t} ∈ 𝓝[Set.Ici 0 \ {t}] t := self_mem_nhdsWithin
  have hb : ∀ᶠ y in 𝓝[Set.Ici 0 \ {t}] t, ∀ k, ‖slope (f k) t y‖ ≤ u k := by
    filter_upwards [hmem] with y hy
    intro k
    have hy0 : 0 ≤ y := hy.1
    have hyt : y ≠ t := hy.2
    have hmvt := (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := f k) (f' := f' k) (C := u k) (fun z hz => hf k z hz)
      (fun z hz => by rw [Real.norm_eq_abs]; exact hbd k z hz) (Set.mem_Ici.2 ht) (Set.mem_Ici.2 hy0)
    rw [slope_def_field, norm_div, Real.norm_eq_abs, Real.norm_eq_abs]
    have hne : 0 < |y - t| := abs_pos.2 (sub_ne_zero.2 hyt)
    rw [div_le_iff₀ hne]
    simpa [Real.norm_eq_abs, mul_comm] using hmvt
  have hT := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[Set.Ici 0 \ {t}] t)
    (f := fun y k => slope (f k) t y) (g := fun k => f' k t) hu hpt hb
  refine hT.congr' ?_
  filter_upwards [hmem] with y hy
  have hy0 : 0 ≤ y := hy.1
  simp only [slope_def_field]
  rw [← (hsum y hy0).tsum_sub (hsum t ht), ← tsum_div_const]


section PairDeriv

open HRS.PDE HRS.PDE.MFAdjoint

theorem hasDerivAt_pairSemigroup (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρC : Torus.IsSmooth ρβ)
    (hpos : ∀ x, 0 < ρβ x) (J : ℕ) (hJ : 3 * mStar d + 2 * d + 8 ≤ J) (R : Torus d → Torus d → ℝ)
    (hR : IsCk2 J R) (x y : Torus d) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun t' => pairSemigroup (mfData d s hs0 hsd V β hβ) ρβ t' R x y)
      (centeredGen (mfData d s hs0 hsd V β hβ) ρβ
          (fun x' => pairSemigroup (mfData d s hs0 hsd V β hβ) ρβ t R x' y) x +
        centeredGen (mfData d s hs0 hsd V β hβ) ρβ
          (fun y' => pairSemigroup (mfData d s hs0 hsd V β hβ) ρβ t R x y') y) (Set.Ici 0) t := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Bc, Ba, hBc, hBa, hsum, hCk, hbd⟩ :=
    term_data hd s hs0 hsd β hβ V hV ρβ hρβ hρC hpos J hJ R hR
  obtain ⟨K, hK0, hK⟩ := abs_centeredGen_le hd1 s hs0 hsd β hβ V hV ρβ hρβ hρC hpos
  set D := mfData d s hs0 hsd V β hβ with hD
  set S : ℝ → (Torus d → ℝ) → Torus d → ℝ := fun τ => equilibriumSemigroup D ρβ τ with hS
  set a : Lattice d → Torus d → ℝ := fun k y' => (sliceCoeff R k y').re with ha
  set b : Lattice d → Torus d → ℝ := fun k y' => (sliceCoeff R k y').im with hb
  have hprob : IsProbDensity ρβ := hρβ.1
  have hgen : ∀ f : Torus d → ℝ, Torus.IsCk ((mStar d : ℕ) : WithTop ℕ∞) f → ∀ (z : Torus d) (τ : ℝ),
      0 ≤ τ → Torus.IsCk 2 (S τ f) →
      HasDerivWithinAt (fun τ' => S τ' f z) (centeredGen D ρβ (S τ f) z) (Set.Ici 0) τ := by
    intro f hf z τ hτ h2
    have := (equilibriumSemigroup_generator_ck hd1 s hs0 hsd β hβ V hV ρβ hρβ hρC hpos f hf).2.2 z τ hτ
    have e := congrFun (centeredGen_eq hd1 s hs0 hsd β hβ V hV ρβ hρβ hρC hpos h2) z
    rw [e]
    exact this
  have hgc : ∀ {f g : Torus d → ℝ}, Torus.IsCk 2 f → Torus.IsCk 2 g → ∀ z : Torus d,
      centeredGen D ρβ (fun y => f y + g y) z = centeredGen D ρβ f z + centeredGen D ρβ g z :=
    fun hf hg z => centeredGen_add_fun hd1 s hs0 hsd β hβ V hV ρβ hρβ hρC hpos hf hg z
  have hsm : ∀ {f : Torus d → ℝ}, Torus.IsCk 2 f → ∀ (c : ℝ) (z : Torus d),
      centeredGen D ρβ (fun y => c * f y) z = c * centeredGen D ρβ f z :=
    fun hf c z => centeredGen_smul_fun hd1 s hs0 hsd β hβ V hV ρβ hρβ hρC hpos hf c z
  have hts : ∀ g : Lattice d → Torus d → ℝ, (∀ k, Torus.IsCk 2 (g k)) →
      (Summable fun k => Torus.cbNorm 2 (g k)) → ∀ z : Torus d,
      Torus.IsCk 2 (fun y => ∑' k, g k y) ∧
        HasSum (fun k => centeredGen D ρβ (g k) z) (centeredGen D ρβ (fun y => ∑' k, g k y) z) :=
    fun g hg hs z => centeredGen_tsum hd1 s hs0 hsd β hβ V hV ρβ hρβ hρC hpos g hg hs z
  -- the terms
  set F : Lattice d → ℝ → ℝ := fun k τ => S τ (Torus.cosMode k) x * S τ (a k) y -
    S τ (Torus.sinMode k) x * S τ (b k) y with hF
  set F' : Lattice d → ℝ → ℝ := fun k τ =>
    (centeredGen D ρβ (S τ (Torus.cosMode k)) x * S τ (a k) y +
        S τ (Torus.cosMode k) x * centeredGen D ρβ (S τ (a k)) y) -
      (centeredGen D ρβ (S τ (Torus.sinMode k)) x * S τ (b k) y +
        S τ (Torus.sinMode k) x * centeredGen D ρβ (S τ (b k)) y) with hF'
  have hderiv : ∀ k τ, 0 ≤ τ → HasDerivWithinAt (F k) (F' k τ) (Set.Ici 0) τ := by
    intro k τ hτ
    obtain ⟨hck1, hck2, hck3, hck4⟩ := hCk k
    obtain ⟨⟨c1, -⟩, ⟨c2, -⟩, ⟨c3, -⟩, ⟨c4, -⟩⟩ := hbd k τ hτ
    exact ((hgen _ hck1 x τ hτ c1).mul (hgen _ hck3 y τ hτ c3)).sub
      ((hgen _ hck2 x τ hτ c2).mul (hgen _ hck4 y τ hτ c4))
  -- bounds
  have hsb : ∀ k τ, 0 ≤ τ → |S τ (Torus.cosMode k) x| ≤ Bc k ∧ |S τ (Torus.sinMode k) x| ≤ Bc k ∧
      |S τ (a k) y| ≤ Ba k ∧ |S τ (b k) y| ≤ Ba k := by
    intro k τ hτ
    obtain ⟨⟨c1, d1⟩, ⟨c2, d2⟩, ⟨c3, d3⟩, ⟨c4, d4⟩⟩ := hbd k τ hτ
    exact ⟨(abs_le_cb_ps (L := 2) c1 x).trans d1, (abs_le_cb_ps (L := 2) c2 x).trans d2,
      (abs_le_cb_ps (L := 2) c3 y).trans d3, (abs_le_cb_ps (L := 2) c4 y).trans d4⟩
  have hgb : ∀ k τ, 0 ≤ τ → |centeredGen D ρβ (S τ (Torus.cosMode k)) x| ≤ K * Bc k ∧
      |centeredGen D ρβ (S τ (Torus.sinMode k)) x| ≤ K * Bc k ∧
      |centeredGen D ρβ (S τ (a k)) y| ≤ K * Ba k ∧ |centeredGen D ρβ (S τ (b k)) y| ≤ K * Ba k := by
    intro k τ hτ
    obtain ⟨⟨c1, d1⟩, ⟨c2, d2⟩, ⟨c3, d3⟩, ⟨c4, d4⟩⟩ := hbd k τ hτ
    exact ⟨(hK _ c1 x).trans (mul_le_mul_of_nonneg_left d1 hK0),
      (hK _ c2 x).trans (mul_le_mul_of_nonneg_left d2 hK0),
      (hK _ c3 y).trans (mul_le_mul_of_nonneg_left d3 hK0),
      (hK _ c4 y).trans (mul_le_mul_of_nonneg_left d4 hK0)⟩
  have hF'b : ∀ k τ, 0 ≤ τ → |F' k τ| ≤ 4 * (K * (Bc k * Ba k)) := by
    intro k τ hτ
    obtain ⟨e1, e2, e3, e4⟩ := hsb k τ hτ
    obtain ⟨f1, f2, f3, f4⟩ := hgb k τ hτ
    have hb0 := hBc k
    have ha0 := hBa k
    have t1 : |centeredGen D ρβ (S τ (Torus.cosMode k)) x * S τ (a k) y| ≤ K * Bc k * Ba k := by
      rw [abs_mul]; exact mul_le_mul f1 e3 (abs_nonneg _) (by positivity)
    have t2 : |S τ (Torus.cosMode k) x * centeredGen D ρβ (S τ (a k)) y| ≤ Bc k * (K * Ba k) := by
      rw [abs_mul]; exact mul_le_mul e1 f3 (abs_nonneg _) hb0
    have t3 : |centeredGen D ρβ (S τ (Torus.sinMode k)) x * S τ (b k) y| ≤ K * Bc k * Ba k := by
      rw [abs_mul]; exact mul_le_mul f2 e4 (abs_nonneg _) (by positivity)
    have t4 : |S τ (Torus.sinMode k) x * centeredGen D ρβ (S τ (b k)) y| ≤ Bc k * (K * Ba k) := by
      rw [abs_mul]; exact mul_le_mul e2 f4 (abs_nonneg _) hb0
    simp only [hF']
    calc _ ≤ |centeredGen D ρβ (S τ (Torus.cosMode k)) x * S τ (a k) y +
          S τ (Torus.cosMode k) x * centeredGen D ρβ (S τ (a k)) y| +
        |centeredGen D ρβ (S τ (Torus.sinMode k)) x * S τ (b k) y +
          S τ (Torus.sinMode k) x * centeredGen D ρβ (S τ (b k)) y| := abs_sub _ _
      _ ≤ (K * Bc k * Ba k + Bc k * (K * Ba k)) + (K * Bc k * Ba k + Bc k * (K * Ba k)) :=
          add_le_add ((abs_add_le _ _).trans (add_le_add t1 t2)) ((abs_add_le _ _).trans (add_le_add t3 t4))
      _ = _ := by ring
  have hFb : ∀ k τ, 0 ≤ τ → |F k τ| ≤ 2 * (Bc k * Ba k) := by
    intro k τ hτ
    obtain ⟨e1, e2, e3, e4⟩ := hsb k τ hτ
    have hb0 := hBc k
    have ha0 := hBa k
    simp only [hF]
    calc _ ≤ |S τ (Torus.cosMode k) x * S τ (a k) y| + |S τ (Torus.sinMode k) x * S τ (b k) y| :=
          abs_sub _ _
      _ ≤ Bc k * Ba k + Bc k * Ba k := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul e1 e3 (abs_nonneg _) hb0) (mul_le_mul e2 e4 (abs_nonneg _) hb0)
      _ = _ := by ring
  have hsumF : ∀ τ, 0 ≤ τ → Summable fun k => F k τ := fun τ hτ =>
    Summable.of_norm_bounded (hsum.mul_left 2) (fun k => by
      rw [Real.norm_eq_abs]; exact hFb k τ hτ)
  have key := hasDerivWithinAt_tsum_Ici F F' (fun k => 4 * (K * (Bc k * Ba k)))
    ((hsum.mul_left K).mul_left 4) hderiv hF'b hsumF t ht
  have hP : ∀ x' y', pairSemigroup D ρβ t R x' y' = ∑' k, (S t (Torus.cosMode k) x' * S t (a k) y' -
      S t (Torus.sinMode k) x' * S t (b k) y') := fun x' y' =>
    pairSemigroup_eq_tsum hd s hs0 hsd β hβ V hV ρβ hρβ hρC hpos J hJ R hR t ht x' y'
  -- the `x`-slice series
  set g : Lattice d → Torus d → ℝ := fun k x' => S t (a k) y * S t (Torus.cosMode k) x' +
    (-(S t (b k) y)) * S t (Torus.sinMode k) x' with hg
  have hg2 : ∀ k, Torus.IsCk 2 (g k) := fun k =>
    (isCk_const_mul_ps (hbd k t ht).1.1 _).add (isCk_const_mul_ps (hbd k t ht).2.1.1 _)
  have hgs : Summable fun k => Torus.cbNorm 2 (g k) := by
    refine Summable.of_nonneg_of_le (fun k => cbNorm_nonneg_ps _ _) (fun k => ?_) (hsum.mul_left 2)
    obtain ⟨e1, e2, e3, e4⟩ := hsb k t ht
    obtain ⟨⟨c1, d1⟩, ⟨c2, d2⟩, ⟨c3, d3⟩, ⟨c4, d4⟩⟩ := hbd k t ht
    have hadd := Torus.cbNorm_add_le 2 (fun x' => S t (a k) y * S t (Torus.cosMode k) x')
      (fun x' => (-(S t (b k) y)) * S t (Torus.sinMode k) x') (isCk_const_mul_ps c1 _)
      (isCk_const_mul_ps c2 _)
    have hs1 := cbNorm_smul_le_ps c1 (S t (a k) y)
    have hs2 := cbNorm_smul_le_ps c2 (-(S t (b k) y))
    rw [abs_neg] at hs2
    have e : g k = (fun x' => S t (a k) y * S t (Torus.cosMode k) x') +
        (fun x' => (-(S t (b k) y)) * S t (Torus.sinMode k) x') := rfl
    rw [e]
    calc _ ≤ _ := hadd.trans (add_le_add hs1 hs2)
      _ ≤ Ba k * Bc k + Ba k * Bc k := add_le_add
          (mul_le_mul e3 d1 (cbNorm_nonneg_ps _ _) (hBa k))
          (mul_le_mul e4 d2 (cbNorm_nonneg_ps _ _) (hBa k))
      _ = _ := by ring
  obtain ⟨-, hxg⟩ := hts g hg2 hgs x
  have hxe : (fun x' => pairSemigroup D ρβ t R x' y) = fun x' => ∑' k, g k x' := by
    funext x'
    rw [hP x' y]
    exact tsum_congr fun k => by simp only [hg]; ring
  have hgk : ∀ k, centeredGen D ρβ (g k) x = S t (a k) y * centeredGen D ρβ (S t (Torus.cosMode k)) x +
      (-(S t (b k) y)) * centeredGen D ρβ (S t (Torus.sinMode k)) x := by
    intro k
    have h1 := hgc (isCk_const_mul_ps (hbd k t ht).1.1 (S t (a k) y))
      (isCk_const_mul_ps (hbd k t ht).2.1.1 (-(S t (b k) y))) x
    rw [hsm (hbd k t ht).1.1, hsm (hbd k t ht).2.1.1] at h1
    exact h1
  have hxs : HasSum (fun k => S t (a k) y * centeredGen D ρβ (S t (Torus.cosMode k)) x +
      (-(S t (b k) y)) * centeredGen D ρβ (S t (Torus.sinMode k)) x)
      (centeredGen D ρβ (fun x' => pairSemigroup D ρβ t R x' y) x) := by
    rw [hxe]
    convert hxg using 1
    funext k
    exact (hgk k).symm
  -- the `y`-slice series
  set h : Lattice d → Torus d → ℝ := fun k y' => S t (Torus.cosMode k) x * S t (a k) y' +
    (-(S t (Torus.sinMode k) x)) * S t (b k) y' with hh
  have hh2 : ∀ k, Torus.IsCk 2 (h k) := fun k =>
    (isCk_const_mul_ps (hbd k t ht).2.2.1.1 _).add (isCk_const_mul_ps (hbd k t ht).2.2.2.1 _)
  have hhs : Summable fun k => Torus.cbNorm 2 (h k) := by
    refine Summable.of_nonneg_of_le (fun k => cbNorm_nonneg_ps _ _) (fun k => ?_) (hsum.mul_left 2)
    obtain ⟨e1, e2, e3, e4⟩ := hsb k t ht
    obtain ⟨⟨c1, d1⟩, ⟨c2, d2⟩, ⟨c3, d3⟩, ⟨c4, d4⟩⟩ := hbd k t ht
    have hadd := Torus.cbNorm_add_le 2 (fun y' => S t (Torus.cosMode k) x * S t (a k) y')
      (fun y' => (-(S t (Torus.sinMode k) x)) * S t (b k) y') (isCk_const_mul_ps c3 _)
      (isCk_const_mul_ps c4 _)
    have hs1 := cbNorm_smul_le_ps c3 (S t (Torus.cosMode k) x)
    have hs2 := cbNorm_smul_le_ps c4 (-(S t (Torus.sinMode k) x))
    rw [abs_neg] at hs2
    have e : h k = (fun y' => S t (Torus.cosMode k) x * S t (a k) y') +
        (fun y' => (-(S t (Torus.sinMode k) x)) * S t (b k) y') := rfl
    rw [e]
    calc _ ≤ _ := hadd.trans (add_le_add hs1 hs2)
      _ ≤ Bc k * Ba k + Bc k * Ba k := add_le_add
          (mul_le_mul e1 d3 (cbNorm_nonneg_ps _ _) (hBc k))
          (mul_le_mul e2 d4 (cbNorm_nonneg_ps _ _) (hBc k))
      _ = _ := by ring
  obtain ⟨-, hyg⟩ := hts h hh2 hhs y
  have hye : (fun y' => pairSemigroup D ρβ t R x y') = fun y' => ∑' k, h k y' := by
    funext y'
    rw [hP x y']
    exact tsum_congr fun k => by simp only [hh]; ring
  have hhk : ∀ k, centeredGen D ρβ (h k) y = S t (Torus.cosMode k) x * centeredGen D ρβ (S t (a k)) y +
      (-(S t (Torus.sinMode k) x)) * centeredGen D ρβ (S t (b k)) y := by
    intro k
    have h1 := hgc (isCk_const_mul_ps (hbd k t ht).2.2.1.1 (S t (Torus.cosMode k) x))
      (isCk_const_mul_ps (hbd k t ht).2.2.2.1 (-(S t (Torus.sinMode k) x))) y
    rw [hsm (hbd k t ht).2.2.1.1, hsm (hbd k t ht).2.2.2.1] at h1
    exact h1
  have hys : HasSum (fun k => S t (Torus.cosMode k) x * centeredGen D ρβ (S t (a k)) y +
      (-(S t (Torus.sinMode k) x)) * centeredGen D ρβ (S t (b k)) y)
      (centeredGen D ρβ (fun y' => pairSemigroup D ρβ t R x y') y) := by
    rw [hye]
    convert hyg using 1
    funext k
    exact (hhk k).symm
  refine (key.congr (fun τ hτ => ?_) ?_).congr_deriv ?_
  · exact pairSemigroup_eq_tsum hd s hs0 hsd β hβ V hV ρβ hρβ hρC hpos J hJ R hR τ hτ x y
  · exact pairSemigroup_eq_tsum hd s hs0 hsd β hβ V hV ρβ hρβ hρC hpos J hJ R hR t ht x y
  · rw [← (hxs.add hys).tsum_eq]
    refine tsum_congr fun k => ?_
    simp only [hF']
    ring

end PairDeriv


section PairZero

open HRS.PDE HRS.PDE.MFAdjoint

theorem isCk_slice2 (J : ℕ) (R : Torus d → Torus d → ℝ) (hR : IsCk2 J R) (x : Torus d) :
    Torus.IsCk (J : WithTop ℕ∞) (fun y => R x y) := by
  have e : Torus.lift (fun y => R x y) = fun u => lift2 R (Torus.rep x, u) := by
    funext u
    simp [Torus.lift, lift2, Torus.mk_rep]
  unfold Torus.IsCk
  rw [e]
  exact hR.comp (contDiff_const.prodMk contDiff_id)

theorem equilibriumSemigroup_zero_ck (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ)
    (hβ : 0 < β) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρC : Torus.IsSmooth ρβ) {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) :
    equilibriumSemigroup (mfData d s hs0 hsd V β hβ) ρβ 0 ψ = projMean (withDensityReal ρβ) ψ := by
  set D := mfData d s hs0 hsd V β hβ with hD
  have hK : ClassicalAux.ConvKernelFacts d D.s := ClassicalAux.convKernelFacts hd D
  have hV1 : Torus.IsCk 1 D.V := MFSemigroup.isCk_nat_of_isSmooth hV 1
  have hρ1 : Torus.IsCk 1 ρβ := MFSemigroup.isCk_nat_of_isSmooth hρC 1
  have h0 : propagator D (fun _ => ρβ) 0 0 ψ = ψ := MFSemigroup.propagator_zero D hK hV1 _ hρ1 hψ
  unfold equilibriumSemigroup
  rw [h0]

theorem pairSemigroup_zero (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρC : Torus.IsSmooth ρβ)
    (hpos : ∀ x, 0 < ρβ x) (R : Torus d → Torus d → ℝ) (hR : IsCk2 2 R)
    (hcen : DoublyCentered (withDensityReal ρβ) R) :
    pairSemigroup (mfData d s hs0 hsd V β hβ) ρβ 0 R = R := by
  have hd1 : 1 ≤ d := by omega
  funext x y
  have hin : (fun y' => equilibriumSemigroup (mfData d s hs0 hsd V β hβ) ρβ 0 (fun x' => R x' y') x) =
      fun y' => R x y' := by
    funext y'
    rw [equilibriumSemigroup_zero_ck hd1 s hs0 hsd β hβ V hV ρβ hρC (isCk_slice 2 R hR y')]
    simp only [projMean]
    rw [hcen.1 y', sub_zero]
  show equilibriumSemigroup (mfData d s hs0 hsd V β hβ) ρβ 0
    (fun y' => equilibriumSemigroup (mfData d s hs0 hsd V β hβ) ρβ 0 (fun x' => R x' y') x) y = R x y
  rw [hin, equilibriumSemigroup_zero_ck hd1 s hs0 hsd β hβ V hV ρβ hρC (isCk_slice2 2 R hR x)]
  simp only [projMean]
  rw [hcen.2 x, sub_zero]

end PairZero


section IntegralFamily

open HRS.PDE HRS.PDE.MFAdjoint

theorem norm_iteratedFDeriv_le_cbNorm2 {j : ℕ} {R : Torus d → Torus d → ℝ} (hR : IsCk2 j R) {i : ℕ}
    (hi : i ≤ j) (p : Euc d × Euc d) : ‖iteratedFDeriv ℝ i (lift2 R) p‖ ≤ cbNorm2 j R := by
  unfold cbNorm2
  have hb : ∀ i' ∈ Finset.range (j + 1), 0 ≤ ⨆ p : Euc d × Euc d, ‖iteratedFDeriv ℝ i' (lift2 R) p‖ :=
    fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
  refine le_trans (le_ciSup (bddAbove_norm_iteratedFDeriv hR (perX_lift2 R) (perY_lift2 R) hi) p) ?_
  exact Finset.single_le_sum hb (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))

theorem cbNorm2_nonneg (j : ℕ) (R : Torus d → Torus d → ℝ) : 0 ≤ cbNorm2 j R :=
  Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _

theorem integral_exp_bound {C c : ℝ} (hc : 0 < c) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun t : ℝ => C * Real.exp (-c * max t 0)) (volume.restrict (Set.Ici T)) ∧
      ∫ t in Set.Ici T, C * Real.exp (-c * max t 0) = C * Real.exp (-c * T) / c := by
  have e : ∀ t ∈ Set.Ici T, C * Real.exp (-c * max t 0) = C * Real.exp (-c * t) := fun t ht =>
    by rw [max_eq_left (hT.trans ht)]
  have hi : IntegrableOn (fun t : ℝ => C * Real.exp (-c * t)) (Set.Ici T) :=
    ((integrableOn_Ici_iff_integrableOn_Ioi (by simp)).2 (exp_neg_integrableOn_Ioi T hc)).const_mul C
  refine ⟨(hi.congr_fun (fun t ht => (e t ht).symm) measurableSet_Ici), ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ici e, integral_const_mul,
    integral_Ici_eq_integral_Ioi]
  have := integral_exp_mul_Ioi (a := -c) (by linarith) T
  rw [this]
  field_simp


theorem family_tail (j : ℕ) (Ψ : ℝ → Torus d → Torus d → ℝ) (C c : ℝ) (hc : 0 < c)
    (hreg : ∀ t, 0 ≤ t → IsCk2 j (Ψ t)) (hbd : ∀ t, 0 ≤ t → cbNorm2 j (Ψ t) ≤ C * Real.exp (-c * t))
    (hcont : ∀ i : ℕ, i ≤ j → ∀ p : Euc d × Euc d,
      ContinuousOn (fun t => iteratedFDeriv ℝ i (lift2 (Ψ t)) p) (Set.Ici 0))
    (T : ℝ) (hT : 0 ≤ T) :
    ContDiff ℝ j (fun p : Euc d × Euc d => ∫ t in Set.Ici T, lift2 (Ψ t) p) ∧
      ∀ i ≤ j, ∀ p, ‖iteratedFDeriv ℝ i (fun p : Euc d × Euc d => ∫ t in Set.Ici T, lift2 (Ψ t) p) p‖ ≤
        C * Real.exp (-c * T) / c := by
  set g : ℝ → Euc d × Euc d → ℝ := fun t => lift2 (Ψ (max t 0)) with hg
  obtain ⟨hbi, hbv⟩ := integral_exp_bound (C := C) hc hT
  have hmax : ∀ t : ℝ, 0 ≤ max t 0 := fun t => le_max_right _ _
  have hcdg : ∀ t, ContDiff ℝ j (g t) := fun t => hreg _ (hmax t)
  have hbd' : ∀ t i p, i ≤ j → ‖iteratedFDeriv ℝ i (g t) p‖ ≤ C * Real.exp (-c * max t 0) :=
    fun t i p hi => (norm_iteratedFDeriv_le_cbNorm2 (hreg _ (hmax t)) hi p).trans (hbd _ (hmax t))
  have hcg : ∀ i, i ≤ j → ∀ p, Continuous fun t : ℝ => iteratedFDeriv ℝ i (g t) p := fun i hi p =>
    (hcont i hi p).comp_continuous (continuous_id.max continuous_const) (fun t => hmax t)
  have hF : (fun p : Euc d × Euc d => ∫ t in Set.Ici T, lift2 (Ψ t) p) =
      fun p => ∫ t, g t p ∂(volume.restrict (Set.Ici T)) := by
    funext p
    refine setIntegral_congr_fun measurableSet_Ici (fun t ht => ?_)
    simp only [hg, max_eq_left (hT.trans ht)]
  rw [hF]
  have hc0 : ∀ p, Continuous fun t : ℝ => g t p := by
    intro p
    have := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => Euc d × Euc d) ℝ
      (0 : Fin 0 → Euc d × Euc d)).continuous.comp (hcg 0 (Nat.zero_le _) p)
    refine this.congr (fun t => ?_)
    simp [iteratedFDeriv_zero_apply]
  have hint : ∀ p, Integrable (fun t => g t p) (volume.restrict (Set.Ici T)) := fun p =>
    hbi.mono' (hc0 p).aestronglyMeasurable (Filter.Eventually.of_forall fun t => by
      have := hbd' t 0 p (Nat.zero_le _)
      simpa using this)
  have hmeas : ∀ i ≤ j, ∀ p, AEStronglyMeasurable (fun t => iteratedFDeriv ℝ i (g t) p)
      (volume.restrict (Set.Ici T)) := fun i hi p => (hcg i hi p).aestronglyMeasurable
  rcases Nat.eq_zero_or_pos j with h0 | hjpos
  · subst h0
    have hcontF : Continuous fun p : Euc d × Euc d => ∫ t, g t p ∂(volume.restrict (Set.Ici T)) :=
      continuous_of_dominated (fun p => (hc0 p).aestronglyMeasurable)
        (fun p => Filter.Eventually.of_forall fun t => by
          have := hbd' t 0 p le_rfl
          simpa using this) hbi (Filter.Eventually.of_forall fun t => (hcdg t).continuous)
    refine ⟨contDiff_zero.2 hcontF, fun i hi p => ?_⟩
    obtain rfl : i = 0 := by omega
    rw [norm_iteratedFDeriv_zero, ← hbv]
    exact norm_integral_le_of_norm_le hbi (Filter.Eventually.of_forall fun t => by
      have := hbd' t 0 p le_rfl
      simpa using this)
  · have key := contDiff_integral_dominated (B := Euc d × Euc d) (volume.restrict (Set.Ici T)) g j hjpos
      hcdg hint hmeas (fun _ t => C * Real.exp (-c * max t 0)) (fun _ _ _ => hbi)
      (fun i _ hi p x => hbd' p i x hi)
    refine ⟨key.1, fun i hi p => ?_⟩
    rw [key.2 i hi p, ← hbv]
    exact norm_integral_le_of_norm_le hbi (Filter.Eventually.of_forall fun t => hbd' t i p hi)


theorem integral_family_isCk2 (j : ℕ) (Ψ : ℝ → Torus d → Torus d → ℝ) (C c : ℝ) (hc : 0 < c)
    (hreg : ∀ t, 0 ≤ t → IsCk2 j (Ψ t)) (hbd : ∀ t, 0 ≤ t → cbNorm2 j (Ψ t) ≤ C * Real.exp (-c * t))
    (hcont : ∀ i : ℕ, i ≤ j → ∀ p : Euc d × Euc d,
      ContinuousOn (fun t => iteratedFDeriv ℝ i (lift2 (Ψ t)) p) (Set.Ici 0)) :
    IntegrableOn (fun t => cbNorm2 j (Ψ t)) (Set.Ici 0) ∧
      (∀ x y, IntegrableOn (fun t => Ψ t x y) (Set.Ici 0)) ∧
      IsCk2 j (fun x y => ∫ t in Set.Ici (0 : ℝ), Ψ t x y) ∧
      Tendsto (fun T : ℝ => cbNorm2 j (fun x y =>
        (∫ t in Set.Ici (0 : ℝ), Ψ t x y) - ∫ t in (0 : ℝ)..T, Ψ t x y)) atTop (𝓝 0) := by
  have hmax : ∀ t : ℝ, 0 ≤ max t 0 := fun t => le_max_right _ _
  obtain ⟨hbi, hbv⟩ := integral_exp_bound (C := C) hc (le_refl (0 : ℝ))
  have hcg : ∀ i, i ≤ j → ∀ p, Continuous fun t : ℝ => iteratedFDeriv ℝ i (lift2 (Ψ (max t 0))) p :=
    fun i hi p => (hcont i hi p).comp_continuous (continuous_id.max continuous_const) (fun t => hmax t)
  -- (1) integrability of the norm
  have hmeasN : Measurable fun t : ℝ => cbNorm2 j (Ψ (max t 0)) := by
    unfold cbNorm2
    refine Finset.measurable_sum _ (fun i hi => ?_)
    have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    refine LowerSemicontinuous.measurable ?_
    refine lowerSemicontinuous_ciSup (fun t => ?_) (fun p => ?_)
    · exact bddAbove_norm_iteratedFDeriv (hreg _ (hmax t)) (perX_lift2 _) (perY_lift2 _) hi'
    · exact ((hcg i hi' p).norm).lowerSemicontinuous
  have h1 : IntegrableOn (fun t => cbNorm2 j (Ψ t)) (Set.Ici 0) := by
    refine hbi.mono' ?_ ?_
    · refine hmeasN.aestronglyMeasurable.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      simp only [max_eq_left (Set.mem_Ici.1 ht)]
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      have ht' : 0 ≤ t := Set.mem_Ici.1 ht
      rw [Real.norm_eq_abs, abs_of_nonneg (cbNorm2_nonneg _ _), max_eq_left ht']
      exact hbd t ht'
  -- (2) pointwise integrability
  have hpt : ∀ x y, IntegrableOn (fun t => Ψ t x y) (Set.Ici 0) := by
    intro x y
    have hc0 : ∀ p : Euc d × Euc d, ContinuousOn (fun t => lift2 (Ψ t) p) (Set.Ici 0) := by
      intro p
      have := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => Euc d × Euc d) ℝ
        (0 : Fin 0 → Euc d × Euc d)).continuous.comp_continuousOn (hcont 0 (Nat.zero_le _) p)
      refine this.congr (fun t _ => ?_)
      simp [iteratedFDeriv_zero_apply]
    refine hbi.mono' ?_ ?_
    · have := (hc0 (Torus.rep x, Torus.rep y)).aestronglyMeasurable (μ := volume) measurableSet_Ici
      refine this.congr ?_
      filter_upwards with t
      simp [lift2, Torus.mk_rep]
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      have ht' : 0 ≤ t := Set.mem_Ici.1 ht
      have := (norm_iteratedFDeriv_le_cbNorm2 (hreg t ht') (Nat.zero_le _)
        (Torus.rep x, Torus.rep y)).trans (hbd t ht')
      rw [norm_iteratedFDeriv_zero] at this
      rw [max_eq_left ht']
      simpa [lift2, Torus.mk_rep] using this
  -- (3) regularity
  have h3 : IsCk2 j (fun x y => ∫ t in Set.Ici (0 : ℝ), Ψ t x y) :=
    (family_tail j Ψ C c hc hreg hbd hcont 0 le_rfl).1
  -- (4) tail
  have htail : ∀ T, 0 ≤ T → cbNorm2 j (fun x y =>
        (∫ t in Set.Ici (0 : ℝ), Ψ t x y) - ∫ t in (0 : ℝ)..T, Ψ t x y) ≤
      (j + 1) * (C * Real.exp (-c * T) / c) := by
    intro T hT
    have hfun : (fun x y => (∫ t in Set.Ici (0 : ℝ), Ψ t x y) - ∫ t in (0 : ℝ)..T, Ψ t x y) =
        fun x y => ∫ t in Set.Ici T, Ψ t x y := by
      funext x y
      have hint := hpt x y
      rw [intervalIntegral.integral_of_le hT]
      have h1 : ∫ t in Set.Ici (0 : ℝ), Ψ t x y =
          (∫ t in Set.Ioc 0 T, Ψ t x y) + ∫ t in Set.Ioi T, Ψ t x y := by
        rw [integral_Ici_eq_integral_Ioi, ← Set.Ioc_union_Ioi_eq_Ioi hT,
          setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
            (hint.mono_set (fun t ht => Set.mem_Ici.2 ht.1.le))
            (hint.mono_set (fun t ht => Set.mem_Ici.2 (hT.trans ht.le)))]
      rw [h1, integral_Ici_eq_integral_Ioi]
      ring
    rw [hfun]
    obtain ⟨-, hb⟩ := family_tail j Ψ C c hc hreg hbd hcont T hT
    unfold cbNorm2
    calc ∑ i ∈ Finset.range (j + 1), ⨆ p : Euc d × Euc d, ‖iteratedFDeriv ℝ i
          (lift2 (fun x y => ∫ t in Set.Ici T, Ψ t x y)) p‖
        ≤ ∑ i ∈ Finset.range (j + 1), C * Real.exp (-c * T) / c := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          refine ciSup_le fun p => ?_
          exact hb i hi' p
      _ = _ := by simp
  have hexp : Tendsto (fun T : ℝ => Real.exp (-c * T)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
  have hup : Tendsto (fun T : ℝ => ((j : ℝ) + 1) * (C * Real.exp (-c * T) / c)) atTop (𝓝 0) := by
    have := ((hexp.const_mul C).div_const c).const_mul ((j : ℝ) + 1)
    simpa using this
  refine ⟨h1, hpt, h3, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Filter.Eventually.of_forall fun T => cbNorm2_nonneg _ _) ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact htail T hT

end IntegralFamily


section JetsAndWeights

open HRS.PDE HRS.PDE.MFAdjoint

/-- `∂_j f (z) = D (lift f) (rep z) e_j`. -/
theorem partialDeriv_eq_jet {f : Torus d → ℝ} (hf : Torus.IsCk 1 f) (j : Fin d) (z : Torus d) :
    Torus.partialDeriv j f z =
      iteratedFDeriv ℝ 1 (Torus.lift f) (Torus.rep z) ![EuclideanSpace.single j (1 : ℝ)] := by
  have e := partialDeriv_mk j f hf (Torus.rep z)
  rw [Torus.mk_rep] at e
  rw [e, iteratedFDeriv_one_apply]
  rfl

theorem laplacian_eq_jet {f : Torus d → ℝ} (hf : Torus.IsCk 2 f) (z : Torus d) :
    Torus.laplacian f z = ∑ j : Fin d, iteratedFDeriv ℝ 2 (Torus.lift f) (Torus.rep z)
      ![EuclideanSpace.single j (1 : ℝ), EuclideanSpace.single j (1 : ℝ)] := by
  have := ClassicalAux.laplacian_mk f hf (Torus.rep z)
  rwa [Torus.mk_rep] at this

theorem Lop_jets {ρ : Torus d → ℝ} (hρ : Torus.IsCk 1 ρ) (hpos : ∀ x, 0 < ρ x) {f : Torus d → ℝ}
    (hf : Torus.IsCk 2 f) (z : Torus d) :
    Lop ρ f z = -(∑ j : Fin d, iteratedFDeriv ℝ 2 (Torus.lift f) (Torus.rep z)
        ![EuclideanSpace.single j (1 : ℝ), EuclideanSpace.single j (1 : ℝ)]) -
      ∑ j : Fin d, (Torus.partialDeriv j ρ z / ρ z) *
        iteratedFDeriv ℝ 1 (Torus.lift f) (Torus.rep z) ![EuclideanSpace.single j (1 : ℝ)] := by
  rw [Lop_eq hρ hpos hf z, laplacian_eq_jet hf z]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [partialDeriv_eq_jet (hf.of_le (by norm_num)) j z]

theorem iteratedFDeriv_partial_left (G : Euc d × Euc d → ℝ) {n : ℕ} (hG : ContDiff ℝ n G) {i : ℕ}
    (hi : i ≤ n) (u v : Euc d) :
    iteratedFDeriv ℝ i (fun u' => G (u', v)) u =
      (iteratedFDeriv ℝ i G (u, v)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) := by
  have h1 : (fun u' => G (u', v)) =
      (fun p => G (p + (0, v))) ∘ (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) := by
    funext u'; simp
  have hf : ContDiff ℝ n (fun p => G (p + (0, v))) := hG.comp (contDiff_id.add contDiff_const)
  rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_right _ hf u (by exact_mod_cast hi),
    iteratedFDeriv_comp_add_right]
  simp

theorem norm_iteratedFDeriv_partial_left_le (G : Euc d × Euc d → ℝ) {n : ℕ} (hG : ContDiff ℝ n G)
    {i : ℕ} (hi : i ≤ n) (u v : Euc d) :
    ‖iteratedFDeriv ℝ i (fun u' => G (u', v)) u‖ ≤ ‖iteratedFDeriv ℝ i G (u, v)‖ := by
  rw [iteratedFDeriv_partial_left G hG hi]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h1 : ‖ContinuousLinearMap.inl ℝ (Euc d) (Euc d)‖ ≤ 1 := ContinuousLinearMap.norm_inl_le_one _ _ _
  have : ∏ _i : Fin i, ‖ContinuousLinearMap.inl ℝ (Euc d) (Euc d)‖ ≤ 1 := by
    rw [Finset.prod_const]
    exact pow_le_one₀ (norm_nonneg _) h1
  calc _ ≤ ‖iteratedFDeriv ℝ i G (u, v)‖ * 1 :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = _ := mul_one _


section KopWeight

variable {s : ℝ} {ρ : Torus d → ℝ}

theorem integrable_kernel_mul {g : Torus d → ℝ} (hg : Integrable g) (x : Torus d) {c : Torus d → ℝ}
    (hc : Continuous c) : Integrable (fun y => g (x - y) * c y) := by
  have hgx : Integrable (fun y => g (x - y)) := hg.comp_sub_left x
  obtain ⟨B, hB⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hc.continuousOn
  exact hgx.mul_bdd hc.aestronglyMeasurable (c := B)
    (Filter.Eventually.of_forall fun y => hB y (Set.mem_univ _))

theorem Kop_weight (hg : Integrable (periodicRiesz d s)) (hprob : IsProbDensity ρ)
    (hρc : Continuous ρ) {h : Torus d → ℝ} (hh : Continuous h) (x : Torus d) :
    Kop (periodicRiesz d s) (withDensityReal ρ) h x =
      ∫ y, ((periodicRiesz d s (x - y) - convFun (periodicRiesz d s) ρ y) * ρ y) * h y := by
  rw [Kop_eq' hprob h x]
  have hswap := MFAdjoint.integral_convFun_mul_swap hg (fun z => periodicRiesz_neg z)
    (a := fun y => ρ y * h y) (b := ρ) (hρc.mul hh) hρc
  have e1 : ∫ z, ρ z * convFun (periodicRiesz d s) (fun y => ρ y * h y) z =
      ∫ z, ρ z * h z * convFun (periodicRiesz d s) ρ z := by
    rw [← hswap]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by simp only; ring)
  rw [e1]
  have hi1 : Integrable (fun y => periodicRiesz d s (x - y) * (ρ y * h y)) :=
    integrable_kernel_mul hg x (hρc.mul hh)
  have hcv : Continuous (convFun (periodicRiesz d s) ρ) := MFAux.continuous_convFun hg hρc
  have hi2 : Integrable (fun z => ρ z * h z * convFun (periodicRiesz d s) ρ z) :=
    MFAdjoint.integrable_of_cont ((hρc.mul hh).mul hcv)
  rw [convFun, ← integral_sub hi1 hi2]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only; ring)

theorem integral_weight_family (w : Torus d → ℝ) (hw : Integrable w) (ν : Measure ℝ) [SFinite ν]
    (H : ℝ → Torus d → ℝ) (hHt : ∀ y, Continuous fun t => H t y) (hHy : ∀ t, Measurable (H t))
    (b : ℝ → ℝ) (hb : Integrable b ν) (hHb : ∀ t y, |H t y| ≤ b t) :
    Integrable (fun t => ∫ y, w y * H t y) ν ∧
      ∫ y, w y * (∫ t, H t y ∂ν) = ∫ t, (∫ y, w y * H t y) ∂ν := by
  have hmeas : Measurable (Function.uncurry H) :=
    measurable_uncurry_of_continuous_of_measurable hHt hHy
  have hint : Integrable (fun p : ℝ × Torus d => w p.2 * H p.1 p.2) (ν.prod volume) := by
    have hbw : Integrable (fun p : ℝ × Torus d => b p.1 * ‖w p.2‖) (ν.prod volume) :=
      hb.mul_prod hw.norm
    refine hbw.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (AEStronglyMeasurable.comp_snd (μ := ν) hw.aestronglyMeasurable :
        AEStronglyMeasurable (fun p : ℝ × Torus d => w p.2) (ν.prod volume)).mul
        hmeas.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, mul_comm]
      exact mul_le_mul (hHb p.1 p.2) (by rw [Real.norm_eq_abs]) (abs_nonneg _)
        ((abs_nonneg _).trans (hHb p.1 p.2))
  refine ⟨hint.integral_prod_left, ?_⟩
  have e : ∀ y, w y * (∫ t, H t y ∂ν) = ∫ t, w y * H t y ∂ν := fun y =>
    (integral_const_mul _ _).symm
  simp_rw [e]
  exact integral_integral_swap (f := fun y t => w y * H t y) hint.swap

end KopWeight

end JetsAndWeights


section SliceFamily

open HRS.PDE HRS.PDE.MFAdjoint

theorem continuous_of_iteratedFDeriv_zero {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : X → E → ℝ} {p : E} (h : Continuous fun x => iteratedFDeriv ℝ 0 (g x) p) :
    Continuous fun x => g x p := by
  have := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => E) ℝ (0 : Fin 0 → E)).continuous.comp h
  refine this.congr (fun t => ?_)
  simp [iteratedFDeriv_zero_apply]

/-- A family of `C²` functions on the torus, with jets bounded by an integrable function of `t ≥ 0`
and continuous in `t`. -/
structure SliceFam (G : ℝ → Torus d → ℝ) (b : ℝ → ℝ) : Prop where
  hb : Integrable b (volume.restrict (Set.Ici (0 : ℝ)))
  reg : ∀ t, 0 ≤ t → Torus.IsCk 2 (G t)
  bd : ∀ t, 0 ≤ t → ∀ i ≤ 2, ∀ u, ‖iteratedFDeriv ℝ i (Torus.lift (G t)) u‖ ≤ b t
  cont : ∀ i ≤ 2, ∀ u, ContinuousOn (fun t => iteratedFDeriv ℝ i (Torus.lift (G t)) u) (Set.Ici 0)

section SliceFamLemmas

variable {G : ℝ → Torus d → ℝ} {b : ℝ → ℝ}

theorem SliceFam.reg' (h : SliceFam G b) (t : ℝ) : Torus.IsCk 2 (G (max t 0)) :=
  h.reg _ (le_max_right _ _)

theorem SliceFam.bd' (h : SliceFam G b) (t : ℝ) {i : ℕ} (hi : i ≤ 2) (u : Euc d) :
    ‖iteratedFDeriv ℝ i (Torus.lift (G (max t 0))) u‖ ≤ b (max t 0) :=
  h.bd _ (le_max_right _ _) i hi u

theorem SliceFam.cont' (h : SliceFam G b) {i : ℕ} (hi : i ≤ 2) (u : Euc d) :
    Continuous fun t : ℝ => iteratedFDeriv ℝ i (Torus.lift (G (max t 0))) u :=
  (h.cont i hi u).comp_continuous (continuous_id.max continuous_const)
    (fun t => Set.mem_Ici.2 (le_max_right _ _))

theorem SliceFam.hb' (h : SliceFam G b) :
    Integrable (fun t => b (max t 0)) (volume.restrict (Set.Ici (0 : ℝ))) :=
  h.hb.congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    simp [max_eq_left (Set.mem_Ici.1 ht)])

theorem SliceFam.cont0 (h : SliceFam G b) (u : Euc d) :
    Continuous fun t : ℝ => Torus.lift (G (max t 0)) u :=
  continuous_of_iteratedFDeriv_zero (g := fun t => Torus.lift (G (max t 0))) (h.cont' (Nat.zero_le 2) u)

theorem SliceFam.int0 (h : SliceFam G b) (u : Euc d) :
    Integrable (fun t => Torus.lift (G (max t 0)) u) (volume.restrict (Set.Ici (0 : ℝ))) :=
  h.hb'.mono' (h.cont0 u).aestronglyMeasurable (Filter.Eventually.of_forall fun t => by
    have := h.bd' t (Nat.zero_le 2) u
    simpa using this)

theorem SliceFam.jets (h : SliceFam G b) :
    Torus.IsCk 2 (fun x' => ∫ t in Set.Ici (0 : ℝ), G t x') ∧
      ∀ i ≤ 2, ∀ u, iteratedFDeriv ℝ i (Torus.lift (fun x' => ∫ t in Set.Ici (0 : ℝ), G t x')) u =
        ∫ t in Set.Ici (0 : ℝ), iteratedFDeriv ℝ i (Torus.lift (G t)) u := by
  have hF : Torus.lift (fun x' => ∫ t in Set.Ici (0 : ℝ), G t x') =
      fun u => ∫ t, Torus.lift (G (max t 0)) u ∂(volume.restrict (Set.Ici (0 : ℝ))) := by
    funext u
    refine setIntegral_congr_fun measurableSet_Ici (fun t ht => ?_)
    simp only [Torus.lift, Function.comp, max_eq_left (Set.mem_Ici.1 ht)]
  have key := contDiff_integral_dominated (B := Euc d) (volume.restrict (Set.Ici (0 : ℝ)))
    (fun t u => Torus.lift (G (max t 0)) u) 2 (by norm_num) (fun t => h.reg' t) h.int0
    (fun i hi u => (h.cont' hi u).aestronglyMeasurable) (fun _ t => b (max t 0)) (fun _ _ _ => h.hb')
    (fun i _ hi t u => h.bd' t hi u)
  refine ⟨?_, fun i hi u => ?_⟩
  · unfold Torus.IsCk
    rw [hF]
    exact key.1
  · rw [hF, key.2 i hi u]
    refine setIntegral_congr_fun measurableSet_Ici (fun t ht => ?_)
    simp only [max_eq_left (Set.mem_Ici.1 ht)]


theorem SliceFam.int_jet (h : SliceFam G b) {i : ℕ} (hi : i ≤ 2) (u : Euc d) :
    Integrable (fun t => iteratedFDeriv ℝ i (Torus.lift (G (max t 0))) u)
      (volume.restrict (Set.Ici (0 : ℝ))) :=
  h.hb'.mono' (h.cont' hi u).aestronglyMeasurable (Filter.Eventually.of_forall fun t => h.bd' t hi u)

theorem SliceFam.lop (h : SliceFam G b) {ρ : Torus d → ℝ} (hρ : Torus.IsCk 1 ρ)
    (hpos : ∀ x, 0 < ρ x) (z : Torus d) :
    Lop ρ (fun x' => ∫ t in Set.Ici (0 : ℝ), G t x') z =
        ∫ t in Set.Ici (0 : ℝ), Lop ρ (G t) z ∧
      Integrable (fun t => Lop ρ (G (max t 0)) z) (volume.restrict (Set.Ici (0 : ℝ))) ∧
      Continuous fun t => Lop ρ (G (max t 0)) z := by
  set Λ2 : (Euc d [×2]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    -(∑ j : Fin d, ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euc d) ℝ
      ![EuclideanSpace.single j (1 : ℝ), EuclideanSpace.single j (1 : ℝ)]) with hΛ2
  set Λ1 : (Euc d [×1]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    -(∑ j : Fin d, (Torus.partialDeriv j ρ z / ρ z) • ContinuousMultilinearMap.apply ℝ
      (fun _ : Fin 1 => Euc d) ℝ ![EuclideanSpace.single j (1 : ℝ)]) with hΛ1
  have hform : ∀ f : Torus d → ℝ, Torus.IsCk 2 f → Lop ρ f z =
      Λ2 (iteratedFDeriv ℝ 2 (Torus.lift f) (Torus.rep z)) +
        Λ1 (iteratedFDeriv ℝ 1 (Torus.lift f) (Torus.rep z)) := by
    intro f hf
    rw [Lop_jets hρ hpos hf z]
    simp only [hΛ2, hΛ1, ContinuousLinearMap.neg_apply, ContinuousLinearMap.coe_sum',
      Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      ContinuousMultilinearMap.apply_apply, smul_eq_mul]
    ring
  obtain ⟨hF2, hJ⟩ := h.jets
  have hint2 := h.int_jet (i := 2) le_rfl (Torus.rep z)
  have hint1 := h.int_jet (i := 1) (by norm_num) (Torus.rep z)
  have hGt : ∀ t : ℝ, Lop ρ (G (max t 0)) z =
      Λ2 (iteratedFDeriv ℝ 2 (Torus.lift (G (max t 0))) (Torus.rep z)) +
        Λ1 (iteratedFDeriv ℝ 1 (Torus.lift (G (max t 0))) (Torus.rep z)) := fun t =>
    hform _ (h.reg' t)
  have hI : Integrable (fun t => Lop ρ (G (max t 0)) z) (volume.restrict (Set.Ici (0 : ℝ))) := by
    simp_rw [hGt]
    exact (Λ2.integrable_comp hint2).add (Λ1.integrable_comp hint1)
  have hC : Continuous fun t => Lop ρ (G (max t 0)) z := by
    simp_rw [hGt]
    exact (Λ2.continuous.comp (h.cont' (i := 2) le_rfl (Torus.rep z))).add
      (Λ1.continuous.comp (h.cont' (i := 1) (by norm_num) (Torus.rep z)))
  refine ⟨?_, hI, hC⟩
  rw [hform _ hF2, hJ 2 le_rfl, hJ 1 (by norm_num)]
  have e2 : ∫ t in Set.Ici (0 : ℝ), iteratedFDeriv ℝ 2 (Torus.lift (G t)) (Torus.rep z) =
      ∫ t, iteratedFDeriv ℝ 2 (Torus.lift (G (max t 0))) (Torus.rep z)
        ∂(volume.restrict (Set.Ici (0 : ℝ))) :=
    setIntegral_congr_fun measurableSet_Ici (fun t ht => by simp [max_eq_left (Set.mem_Ici.1 ht)])
  have e1 : ∫ t in Set.Ici (0 : ℝ), iteratedFDeriv ℝ 1 (Torus.lift (G t)) (Torus.rep z) =
      ∫ t, iteratedFDeriv ℝ 1 (Torus.lift (G (max t 0))) (Torus.rep z)
        ∂(volume.restrict (Set.Ici (0 : ℝ))) :=
    setIntegral_congr_fun measurableSet_Ici (fun t ht => by simp [max_eq_left (Set.mem_Ici.1 ht)])
  rw [e2, e1, ← Λ2.integral_comp_comm hint2, ← Λ1.integral_comp_comm hint1,
    ← integral_add (Λ2.integrable_comp hint2) (Λ1.integrable_comp hint1)]
  refine setIntegral_congr_fun measurableSet_Ici (fun t ht => ?_)
  have := hGt t
  simp only [max_eq_left (Set.mem_Ici.1 ht)] at this ⊢
  exact this.symm


theorem cbNorm_le_of_jets {L : ℕ} {f : Torus d → ℝ} {B : ℝ}
    (hB : ∀ i ≤ L, ∀ u, ‖iteratedFDeriv ℝ i (Torus.lift f) u‖ ≤ B) :
    Torus.cbNorm L f ≤ (L + 1) * B := by
  unfold Torus.cbNorm
  calc ∑ i ∈ Finset.range (L + 1), ⨆ u : Euc d, ‖iteratedFDeriv ℝ i (Torus.lift f) u‖
      ≤ ∑ i ∈ Finset.range (L + 1), B := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        exact ciSup_le fun u => hB i hi' u
    _ = _ := by simp

end SliceFamLemmas

section SliceGen

variable (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
  (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
  (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρC : Torus.IsSmooth ρβ)
  (hpos : ∀ x, 0 < ρβ x)

include hd hV hρβ hρC hpos

theorem centeredGen_integral_slice {G : ℝ → Torus d → ℝ} {b : ℝ → ℝ} (h : SliceFam G b) (x : Torus d) :
    Torus.IsCk 2 (fun x' => ∫ t in Set.Ici (0 : ℝ), G t x') ∧
      IntegrableOn (fun t => centeredGen (mfData d s hs0 hsd V β hβ) ρβ (G t) x) (Set.Ici 0) ∧
      centeredGen (mfData d s hs0 hsd V β hβ) ρβ (fun x' => ∫ t in Set.Ici (0 : ℝ), G t x') x =
        ∫ t in Set.Ici (0 : ℝ), centeredGen (mfData d s hs0 hsd V β hβ) ρβ (G t) x := by
  have hρ1 : Torus.IsCk 1 ρβ := isCk_of_smooth_ps hρC 1
  have hρc : Continuous ρβ := MFAux.continuous_of_isCk hρ1
  have hprob : IsProbDensity ρβ := hρβ.1
  have hg := MFOneLe.integrable_periodicRiesz hd s hs0 hsd
  obtain ⟨hF2, -⟩ := h.jets
  set ν : Measure ℝ := volume.restrict (Set.Ici (0 : ℝ)) with hν
  set H : ℝ → Torus d → ℝ := fun t y => Lop ρβ (G (max t 0)) y with hH
  have hcl : ∀ t, Continuous (H t) := fun t =>
    MFAdjoint.continuous_lop hprob hρ1 hpos (h.reg' t)
  obtain ⟨K1, hK1, hL⟩ := abs_Lop_le hρ1 hpos
  have hHb : ∀ t y, |H t y| ≤ K1 * (3 * b (max t 0)) := by
    intro t y
    have h3 := cbNorm_le_of_jets (L := 2) (f := G (max t 0)) (B := b (max t 0))
      (fun i hi u => h.bd' t hi u)
    have := hL _ (h.reg' t) y
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hK1)
    simpa using h3.trans (by norm_num)
  have hbB : Integrable (fun t => K1 * (3 * b (max t 0))) ν :=
    (h.hb'.const_mul 3).const_mul K1
  have hW : ∀ x : Torus d, Integrable (fun y => ((periodicRiesz d s (x - y) -
      convFun (periodicRiesz d s) ρβ y) * ρβ y)) := by
    intro x
    have e : (fun y => ((periodicRiesz d s (x - y) - convFun (periodicRiesz d s) ρβ y) * ρβ y)) =
        fun y => periodicRiesz d s (x - y) * ρβ y - convFun (periodicRiesz d s) ρβ y * ρβ y := by
      funext y; ring
    rw [e]
    exact (integrable_kernel_mul hg x hρc).sub (MFAdjoint.integrable_of_cont
      ((MFAux.continuous_convFun hg hρc).mul hρc))
  have hLF : ∀ y, Lop ρβ (fun x' => ∫ t, G t x' ∂ν) y = ∫ t, H t y ∂ν := by
    intro y
    refine (h.lop hρ1 hpos y).1.trans ?_
    exact setIntegral_congr_fun measurableSet_Ici (fun t ht => by simp [hH, max_eq_left (Set.mem_Ici.1 ht)])
  have hKop : ∀ x : Torus d,
      Integrable (fun t => Kop (periodicRiesz d s) (withDensityReal ρβ) (H t) x) ν ∧
      Kop (periodicRiesz d s) (withDensityReal ρβ)
        (Lop ρβ (fun x' => ∫ t in Set.Ici (0 : ℝ), G t x')) x =
        ∫ t, Kop (periodicRiesz d s) (withDensityReal ρβ) (H t) x ∂ν := by
    intro x
    obtain ⟨hI, hE⟩ := integral_weight_family _ (hW x) ν H
      (fun y => (h.lop hρ1 hpos y).2.2) (fun t => (hcl t).measurable) _ hbB hHb
    have e1 : ∀ t, Kop (periodicRiesz d s) (withDensityReal ρβ) (H t) x =
        ∫ y, ((periodicRiesz d s (x - y) - convFun (periodicRiesz d s) ρβ y) * ρβ y) * H t y :=
      fun t => Kop_weight hg hprob hρc (hcl t) x
    refine ⟨hI.congr (Filter.Eventually.of_forall fun t => (e1 t).symm), ?_⟩
    simp_rw [e1]
    rw [Kop_weight hg hprob hρc (MFAdjoint.continuous_lop hprob hρ1 hpos hF2) x]
    simp_rw [hLF]
    exact hE
  refine ⟨hF2, ?_⟩
  have hI1 : Integrable (fun t => H t x) ν := (h.lop hρ1 hpos x).2.1
  have hint : Integrable (fun t => centeredGen (mfData d s hs0 hsd V β hβ) ρβ (G (max t 0)) x) ν := by
    have e : ∀ t, centeredGen (mfData d s hs0 hsd V β hβ) ρβ (G (max t 0)) x =
        -(β⁻¹ * H t x + Kop (periodicRiesz d s) (withDensityReal ρβ) (H t) x) := fun t =>
      congrFun (centeredGen_eq hd s hs0 hsd β hβ V hV ρβ hρβ hρC hpos (h.reg' t)) x
    simp_rw [e]
    exact ((hI1.const_mul β⁻¹).add (hKop x).1).neg
  have hcongr : ∀ t ∈ Set.Ici (0 : ℝ), centeredGen (mfData d s hs0 hsd V β hβ) ρβ (G (max t 0)) x =
      centeredGen (mfData d s hs0 hsd V β hβ) ρβ (G t) x := fun t ht => by
    simp [max_eq_left (Set.mem_Ici.1 ht)]
  refine ⟨hint.congr (ae_restrict_of_forall_mem measurableSet_Ici hcongr), ?_⟩
  rw [centeredGen_eq hd s hs0 hsd β hβ V hV ρβ hρβ hρC hpos hF2]
  simp only
  rw [(hKop x).2, (h.lop hρ1 hpos x).1]
  have e : ∀ t, centeredGen (mfData d s hs0 hsd V β hβ) ρβ (G (max t 0)) x =
      -(β⁻¹ * H t x + Kop (periodicRiesz d s) (withDensityReal ρβ) (H t) x) := fun t =>
    congrFun (centeredGen_eq hd s hs0 hsd β hβ V hV ρβ hρβ hρC hpos (h.reg' t)) x
  have hL1 : ∫ t in Set.Ici (0 : ℝ), Lop ρβ (G t) x = ∫ t, H t x ∂ν :=
    setIntegral_congr_fun measurableSet_Ici (fun t ht => by simp [hH, max_eq_left (Set.mem_Ici.1 ht)])
  rw [hL1, ← integral_const_mul, ← integral_add (hI1.const_mul β⁻¹) (hKop x).1, ← integral_neg]
  have : ∫ t in Set.Ici (0 : ℝ), centeredGen (mfData d s hs0 hsd V β hβ) ρβ (G t) x =
      ∫ t, centeredGen (mfData d s hs0 hsd V β hβ) ρβ (G (max t 0)) x ∂ν :=
    (setIntegral_congr_fun measurableSet_Ici (fun t ht => hcongr t ht)).symm
  rw [this]
  exact integral_congr_ae (Filter.Eventually.of_forall fun t => (e t).symm)

end SliceGen

end SliceFamily


section CenteredGenIntegral

open HRS.PDE HRS.PDE.MFAdjoint

theorem sliceFam_x (j : ℕ) (hj : 2 ≤ j) (Ψ : ℝ → Torus d → Torus d → ℝ) (C c : ℝ) (hc : 0 < c)
    (hreg : ∀ t, 0 ≤ t → IsCk2 j (Ψ t)) (hbd : ∀ t, 0 ≤ t → cbNorm2 j (Ψ t) ≤ C * Real.exp (-c * t))
    (hcont : ∀ i : ℕ, i ≤ j → ∀ p : Euc d × Euc d,
      ContinuousOn (fun t => iteratedFDeriv ℝ i (lift2 (Ψ t)) p) (Set.Ici 0)) (y : Torus d) :
    SliceFam (fun t x' => Ψ t x' y) (fun t => C * Real.exp (-c * t)) := by
  have hlift : ∀ t, Torus.lift (fun x' => Ψ t x' y) = fun u => lift2 (Ψ t) (u, Torus.rep y) := by
    intro t; funext u
    simp [Torus.lift, lift2, Torus.mk_rep]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((integrableOn_Ici_iff_integrableOn_Ioi (by simp)).2
      (exp_neg_integrableOn_Ioi 0 hc)).const_mul C
  · intro t ht
    exact (isCk_slice j (Ψ t) (hreg t ht) y).of_le (by exact_mod_cast hj)
  · intro t ht i hi u
    rw [hlift t]
    exact (norm_iteratedFDeriv_partial_left_le (lift2 (Ψ t)) (hreg t ht) (by omega) u
      (Torus.rep y)).trans ((norm_iteratedFDeriv_le_cbNorm2 (hreg t ht) (by omega) _).trans (hbd t ht))
  · intro i hi u
    have h1 := (ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin i => ContinuousLinearMap.inl ℝ (Euc d) (Euc d))).continuous.comp_continuousOn
      (hcont i (by omega) (u, Torus.rep y))
    refine h1.congr (fun t ht => ?_)
    simp only [Function.comp]
    rw [hlift t, iteratedFDeriv_partial_left (lift2 (Ψ t)) (hreg t ht) (by omega) u (Torus.rep y)]
    rfl


theorem sliceFam_y (j : ℕ) (hj : 2 ≤ j) (Ψ : ℝ → Torus d → Torus d → ℝ) (C c : ℝ) (hc : 0 < c)
    (hreg : ∀ t, 0 ≤ t → IsCk2 j (Ψ t)) (hbd : ∀ t, 0 ≤ t → cbNorm2 j (Ψ t) ≤ C * Real.exp (-c * t))
    (hcont : ∀ i : ℕ, i ≤ j → ∀ p : Euc d × Euc d,
      ContinuousOn (fun t => iteratedFDeriv ℝ i (lift2 (Ψ t)) p) (Set.Ici 0)) (x : Torus d) :
    SliceFam (fun t y' => Ψ t x y') (fun t => C * Real.exp (-c * t)) := by
  have hlift : ∀ t, Torus.lift (fun y' => Ψ t x y') = fun v => lift2 (Ψ t) (Torus.rep x, v) := by
    intro t; funext v
    simp [Torus.lift, lift2, Torus.mk_rep]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((integrableOn_Ici_iff_integrableOn_Ioi (by simp)).2
      (exp_neg_integrableOn_Ioi 0 hc)).const_mul C
  · intro t ht
    exact (isCk_slice2 j (Ψ t) (hreg t ht) x).of_le (by exact_mod_cast hj)
  · intro t ht i hi u
    rw [hlift t]
    exact (norm_iteratedFDeriv_partial_le (lift2 (Ψ t)) (hreg t ht) (by omega) (Torus.rep x) u).trans
      ((norm_iteratedFDeriv_le_cbNorm2 (hreg t ht) (by omega) _).trans (hbd t ht))
  · intro i hi u
    have h1 := (ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin i => ContinuousLinearMap.inr ℝ (Euc d) (Euc d))).continuous.comp_continuousOn
      (hcont i (by omega) (Torus.rep x, u))
    refine h1.congr (fun t ht => ?_)
    simp only [Function.comp]
    rw [hlift t, iteratedFDeriv_partial (lift2 (Ψ t)) (hreg t ht) (by omega) (Torus.rep x) u]
    rfl


theorem centeredGen_integral_family (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ)
    (hβ : 0 < β) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρC : Torus.IsSmooth ρβ)
    (hpos : ∀ x, 0 < ρβ x) (Ψ : ℝ → Torus d → Torus d → ℝ) (C c : ℝ) (hc : 0 < c)
    (hreg : ∀ t, 0 ≤ t → IsCk2 2 (Ψ t)) (hbd : ∀ t, 0 ≤ t → cbNorm2 2 (Ψ t) ≤ C * Real.exp (-c * t))
    (hcont : ∀ i : ℕ, i ≤ 2 → ∀ p : Euc d × Euc d,
      ContinuousOn (fun t => iteratedFDeriv ℝ i (lift2 (Ψ t)) p) (Set.Ici 0))
    (hderiv : ∀ x y, ∀ t, 0 ≤ t → HasDerivWithinAt (fun t' => Ψ t' x y)
      (centeredGen (mfData d s hs0 hsd V β hβ) ρβ (fun x' => Ψ t x' y) x +
        centeredGen (mfData d s hs0 hsd V β hβ) ρβ (fun y' => Ψ t x y') y) (Set.Ici 0) t)
    (x y : Torus d) :
    -(centeredGen (mfData d s hs0 hsd V β hβ) ρβ (fun x' => ∫ t in Set.Ici (0 : ℝ), Ψ t x' y) x +
        centeredGen (mfData d s hs0 hsd V β hβ) ρβ (fun y' => ∫ t in Set.Ici (0 : ℝ), Ψ t x y') y) =
      Ψ 0 x y := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨-, hAx, hEx⟩ := centeredGen_integral_slice hd1 s hs0 hsd β hβ V hV ρβ hρβ hρC hpos
    (sliceFam_x 2 le_rfl Ψ C c hc hreg hbd hcont y) x
  obtain ⟨-, hAy, hEy⟩ := centeredGen_integral_slice hd1 s hs0 hsd β hβ V hV ρβ hρβ hρC hpos
    (sliceFam_y 2 le_rfl Ψ C c hc hreg hbd hcont x) y
  rw [hEx, hEy, ← integral_add hAx hAy]
  set w : ℝ → ℝ := fun t => centeredGen (mfData d s hs0 hsd V β hβ) ρβ (fun x' => Ψ t x' y) x +
    centeredGen (mfData d s hs0 hsd V β hβ) ρβ (fun y' => Ψ t x y') y with hw
  have hwi : IntegrableOn w (Set.Ici 0) := hAx.add hAy
  set u : ℝ → ℝ := fun t => Ψ t x y with hu
  have hderiv' : ∀ t, 0 ≤ t → HasDerivWithinAt u (w t) (Set.Ici 0) t := fun t ht => hderiv x y t ht
  have hucont : ContinuousOn u (Set.Ici 0) := fun t ht => (hderiv' t ht).continuousWithinAt
  have hftc : ∀ T, 0 ≤ T → ∫ t in (0 : ℝ)..T, w t = u T - u 0 := by
    intro T hT
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
      (hucont.mono Set.Icc_subset_Ici_self)
      (fun t ht => (hderiv' t ht.1.le).hasDerivAt (Ici_mem_nhds ht.1)) ?_
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 (hwi.mono_set (fun t ht => Set.mem_Ici.2 ht.1.le))
  have hT1 : Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, w t) atTop (𝓝 (∫ t in Set.Ioi (0 : ℝ), w t)) :=
    intervalIntegral_tendsto_integral_Ioi 0 (hwi.mono_set Set.Ioi_subset_Ici_self) tendsto_id
  have hexp : Tendsto (fun T : ℝ => C * Real.exp (-c * T)) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (show -c < 0 by linarith))).const_mul C
    simpa using this
  have huT : Tendsto u atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hexp
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    have := (norm_iteratedFDeriv_le_cbNorm2 (hreg T hT) (Nat.zero_le _)
      (Torus.rep x, Torus.rep y)).trans (hbd T hT)
    rw [norm_iteratedFDeriv_zero] at this
    simpa [hu, lift2, Torus.mk_rep] using this
  have hT2 : Tendsto (fun T : ℝ => u T - u 0) atTop (𝓝 (0 - u 0)) := huT.sub tendsto_const_nhds
  have hT1' : Tendsto (fun T : ℝ => u T - u 0) atTop (𝓝 (∫ t in Set.Ioi (0 : ℝ), w t)) := by
    refine hT1.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact hftc T hT
  have := tendsto_nhds_unique hT1' hT2
  rw [integral_Ici_eq_integral_Ioi, this]
  simp [hu]

end CenteredGenIntegral


section PairCentered

open HRS.PDE HRS.PDE.MFAdjoint

theorem doublyCentered_pairSemigroup (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ)
    (hβ : 0 < β) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρC : Torus.IsSmooth ρβ)
    (hpos : ∀ x, 0 < ρβ x) (J : ℕ) (hJ : 3 * mStar d + 2 * d + 8 ≤ J) (R : Torus d → Torus d → ℝ)
    (hR : IsCk2 J R) (t : ℝ) (ht : 0 ≤ t) :
    DoublyCentered (withDensityReal ρβ) (pairSemigroup (mfData d s hs0 hsd V β hβ) ρβ t R) := by
  have hd1 : 1 ≤ d := by omega
  have hprob : IsProbDensity ρβ := hρβ.1
  have hρ1 : Torus.IsCk 1 ρβ := isCk_of_smooth_ps hρC 1
  have hρc : Continuous ρβ := MFAux.continuous_of_isCk hρ1
  haveI := MFSemigroup.isProb_withDensityReal hprob
  set D := mfData d s hs0 hsd V β hβ with hD
  set S : ℝ → (Torus d → ℝ) → Torus d → ℝ := fun τ => equilibriumSemigroup D ρβ τ with hS
  have hSc : ∀ τ (f : Torus d → ℝ), pair (withDensityReal ρβ) (S τ f) = 0 := fun τ f => by
    simp only [hS, equilibriumSemigroup]
    exact MFSemigroup.pair_projMean _ _
  refine ⟨fun y => ?_, fun x => ?_⟩
  · obtain ⟨Bc, Ba, hBc, hBa, hsum, hCk, hbd⟩ :=
      term_data hd s hs0 hsd β hβ V hV ρβ hρβ hρC hpos J hJ R hR
    set a : Lattice d → Torus d → ℝ := fun k y' => (sliceCoeff R k y').re with ha
    set b : Lattice d → Torus d → ℝ := fun k y' => (sliceCoeff R k y').im with hb
    set T : Lattice d → Torus d → ℝ := fun k x' => S t (a k) y * S t (Torus.cosMode k) x' +
      (-(S t (b k) y)) * S t (Torus.sinMode k) x' with hT
    have hcts : ∀ f : Torus d → ℝ, Torus.IsCk 2 f → Continuous f := fun f hf =>
      MFAux.continuous_of_isCk (hf.of_le (by norm_num))
    have hTc : ∀ k, Continuous (T k) := fun k =>
      (continuous_const.mul (hcts _ (hbd k t ht).1.1)).add (continuous_const.mul (hcts _ (hbd k t ht).2.1.1))
    have hTb : ∀ k x', |T k x'| ≤ 2 * (Bc k * Ba k) := by
      intro k x'
      obtain ⟨⟨c1, d1⟩, ⟨c2, d2⟩, ⟨c3, d3⟩, ⟨c4, d4⟩⟩ := hbd k t ht
      have e1 : |S t (Torus.cosMode k) x'| ≤ Bc k := (abs_le_cb_ps (L := 2) c1 x').trans d1
      have e2 : |S t (Torus.sinMode k) x'| ≤ Bc k := (abs_le_cb_ps (L := 2) c2 x').trans d2
      have e3 : |S t (a k) y| ≤ Ba k := (abs_le_cb_ps (L := 2) c3 y).trans d3
      have e4 : |S t (b k) y| ≤ Ba k := (abs_le_cb_ps (L := 2) c4 y).trans d4
      have hb0 := hBc k
      have ha0 := hBa k
      calc |T k x'| ≤ |S t (a k) y * S t (Torus.cosMode k) x'| +
            |(-(S t (b k) y)) * S t (Torus.sinMode k) x'| := abs_add_le _ _
        _ ≤ Ba k * Bc k + Ba k * Bc k := by
            rw [abs_mul, abs_mul, abs_neg]
            exact add_le_add (mul_le_mul e3 e1 (abs_nonneg _) ha0) (mul_le_mul e4 e2 (abs_nonneg _) ha0)
        _ = _ := by ring
    have hPT : ∀ x', pairSemigroup D ρβ t R x' y = ∑' k, T k x' := fun x' => by
      rw [pairSemigroup_eq_tsum hd s hs0 hsd β hβ V hV ρβ hρβ hρC hpos J hJ R hR t ht x' y]
      exact tsum_congr fun k => by simp only [hT]; ring
    have hT0 : ∀ k, ∫ x', ρβ x' * T k x' = 0 := by
      intro k
      have hA := hSc t (Torus.cosMode k)
      have hB := hSc t (Torus.sinMode k)
      rw [MFAdjoint.pair_mu hprob] at hA hB
      have hAi : Integrable (fun x' => ρβ x' * S t (Torus.cosMode k) x') :=
        MFAdjoint.integrable_of_cont (hρc.mul (hcts _ (hbd k t ht).1.1))
      have hBi : Integrable (fun x' => ρβ x' * S t (Torus.sinMode k) x') :=
        MFAdjoint.integrable_of_cont (hρc.mul (hcts _ (hbd k t ht).2.1.1))
      have e : ∀ x', ρβ x' * T k x' = S t (a k) y * (ρβ x' * S t (Torus.cosMode k) x') +
          (-(S t (b k) y)) * (ρβ x' * S t (Torus.sinMode k) x') := fun x' => by simp only [hT]; ring
      simp_rw [e]
      rw [integral_add (hAi.const_mul _) (hBi.const_mul _), integral_const_mul, integral_const_mul,
        hA, hB]
      ring
    have hint : ∀ k, Integrable (fun x' => ρβ x' * T k x') := fun k =>
      MFAdjoint.integrable_of_cont (hρc.mul (hTc k))
    have hnorm : ∀ k, ∫ x', ‖ρβ x' * T k x'‖ ≤ 2 * (Bc k * Ba k) := by
      intro k
      calc ∫ x', ‖ρβ x' * T k x'‖ ≤ ∫ x', ρβ x' * (2 * (Bc k * Ba k)) := by
            refine integral_mono (hint k).norm
              ((MFAdjoint.integrable_of_cont hρc).mul_const _) (fun x' => ?_)
            simp only
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hprob.nonneg x')]
            exact mul_le_mul_of_nonneg_left (hTb k x') (hprob.nonneg x')
        _ = 2 * (Bc k * Ba k) := by rw [integral_mul_const, hprob.integral_one, one_mul]
    have hsm : Summable fun k => ∫ x', ‖ρβ x' * T k x'‖ :=
      Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _) hnorm
        (hsum.mul_left 2)
    have hHS := hasSum_integral_of_summable_integral_norm hint hsm
    have h0 : (fun k => ∫ x', ρβ x' * T k x') = fun _ => (0 : ℝ) := funext hT0
    rw [h0] at hHS
    have hz := hHS.unique hasSum_zero
    rw [MFAdjoint.pair_mu hprob]
    have e2 : ∀ x', ρβ x' * pairSemigroup D ρβ t R x' y = ∑' k, ρβ x' * T k x' := fun x' => by
      rw [hPT x', tsum_mul_left]
    simp_rw [e2]
    exact hz
  · exact hSc t _


theorem integral_family_doublyCentered (j : ℕ) (Ψ : ℝ → Torus d → Torus d → ℝ) (C c : ℝ) (hc : 0 < c)
    (hreg : ∀ t, 0 ≤ t → IsCk2 j (Ψ t)) (hbd : ∀ t, 0 ≤ t → cbNorm2 j (Ψ t) ≤ C * Real.exp (-c * t))
    (hcont : ∀ p : Euc d × Euc d,
      ContinuousOn (fun t => iteratedFDeriv ℝ 0 (lift2 (Ψ t)) p) (Set.Ici 0))
    {ρ : Torus d → ℝ} (hprob : IsProbDensity ρ) (hρc : Continuous ρ)
    (hcen : ∀ t, 0 ≤ t → DoublyCentered (withDensityReal ρ) (Ψ t)) :
    DoublyCentered (withDensityReal ρ) (fun x y => ∫ t in Set.Ici (0 : ℝ), Ψ t x y) := by
  have hmax : ∀ t : ℝ, 0 ≤ max t 0 := fun t => le_max_right _ _
  obtain ⟨hbi, -⟩ := integral_exp_bound (C := C) hc (le_refl (0 : ℝ))
  have hc0 : ∀ p : Euc d × Euc d, Continuous fun t : ℝ => lift2 (Ψ (max t 0)) p := fun p =>
    continuous_of_iteratedFDeriv_zero (g := fun t => lift2 (Ψ (max t 0)))
      ((hcont p).comp_continuous (continuous_id.max continuous_const)
        (fun t => Set.mem_Ici.2 (hmax t)))
  have hbd0 : ∀ t (p : Euc d × Euc d), |lift2 (Ψ (max t 0)) p| ≤ C * Real.exp (-c * max t 0) := by
    intro t p
    have := (norm_iteratedFDeriv_le_cbNorm2 (hreg _ (hmax t)) (Nat.zero_le j) p).trans
      (hbd _ (hmax t))
    rw [norm_iteratedFDeriv_zero] at this
    simpa using this
  have hρi : Integrable ρ := MFAdjoint.integrable_of_cont hρc
  have hpair : ∀ f : Torus d → ℝ, pair (withDensityReal ρ) f = ∫ z, ρ z * f z := fun f =>
    MFAdjoint.pair_mu hprob f
  have hslx : ∀ τ, 0 ≤ τ → ∀ y : Torus d, Continuous fun x => Ψ τ x y := fun τ hτ y =>
    Torus.continuous_of_continuous_lift (isCk_slice j (Ψ τ) (hreg τ hτ) y).continuous
  have hsly : ∀ τ, 0 ≤ τ → ∀ x : Torus d, Continuous fun y => Ψ τ x y := fun τ hτ x =>
    Torus.continuous_of_continuous_lift (isCk_slice2 j (Ψ τ) (hreg τ hτ) x).continuous
  have hid : ∀ (τ : ℝ) (x y : Torus d), lift2 (Ψ τ) (Torus.rep x, Torus.rep y) = Ψ τ x y := by
    intro τ x y; simp [lift2, Torus.mk_rep]
  constructor
  · intro y
    set H : ℝ → Torus d → ℝ := fun t x => Ψ (max t 0) x y with hH
    obtain ⟨-, hE⟩ := integral_weight_family ρ hρi (volume.restrict (Set.Ici (0 : ℝ))) H
      (fun x => by simpa [hH, hid] using hc0 (Torus.rep x, Torus.rep y))
      (fun t => (hslx _ (hmax t) y).measurable) _ hbi
      (fun t x => by simpa [hH, hid] using hbd0 t (Torus.rep x, Torus.rep y))
    rw [hpair]
    have e1 : ∀ x, ∫ t in Set.Ici (0 : ℝ), Ψ t x y = ∫ t, H t x ∂(volume.restrict (Set.Ici (0 : ℝ))) :=
      fun x => setIntegral_congr_fun measurableSet_Ici (fun t ht => by simp [hH, max_eq_left (Set.mem_Ici.1 ht)])
    simp only [e1]
    rw [hE]
    have : ∀ t : ℝ, ∫ x, ρ x * H t x = 0 := fun t => by
      rw [← hpair]; exact (hcen _ (hmax t)).1 y
    simp [this]
  · intro x
    set H : ℝ → Torus d → ℝ := fun t y => Ψ (max t 0) x y with hH
    obtain ⟨-, hE⟩ := integral_weight_family ρ hρi (volume.restrict (Set.Ici (0 : ℝ))) H
      (fun y => by simpa [hH, hid] using hc0 (Torus.rep x, Torus.rep y))
      (fun t => (hsly _ (hmax t) x).measurable) _ hbi
      (fun t y => by simpa [hH, hid] using hbd0 t (Torus.rep x, Torus.rep y))
    rw [hpair]
    have e1 : ∀ y, ∫ t in Set.Ici (0 : ℝ), Ψ t x y = ∫ t, H t y ∂(volume.restrict (Set.Ici (0 : ℝ))) :=
      fun y => setIntegral_congr_fun measurableSet_Ici (fun t ht => by simp [hH, max_eq_left (Set.mem_Ici.1 ht)])
    simp only [e1]
    rw [hE]
    have : ∀ t : ℝ, ∫ y, ρ y * H t y = 0 := fun t => by
      rw [← hpair]; exact (hcen _ (hmax t)).2 x
    simp [this]



theorem periodic_pair_inverse_aux (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ)
    (hβ : 0 < β) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρC : Torus.IsSmooth ρβ)
    (hpos : ∀ x, 0 < ρβ x) :
    ∀ j : ℕ, 2 ≤ j → ∃ J : ℕ, ∀ R : Torus d → Torus d → ℝ, IsCk2 J R →
      DoublyCentered (withDensityReal ρβ) R →
      (∀ t, 0 ≤ t → IsCk2 j (pairSemigroup (mfData d s hs0 hsd V β hβ) ρβ t R)) ∧
      IntegrableOn (fun t => cbNorm2 j (pairSemigroup (mfData d s hs0 hsd V β hβ) ρβ t R))
        (Set.Ici 0) ∧
      (∀ x y, IntegrableOn (fun t => pairSemigroup (mfData d s hs0 hsd V β hβ) ρβ t R x y)
        (Set.Ici 0)) ∧
      Tendsto (fun T : ℝ => cbNorm2 j (fun x y =>
          pairInverse (mfData d s hs0 hsd V β hβ) ρβ R x y -
            ∫ t in (0 : ℝ)..T, pairSemigroup (mfData d s hs0 hsd V β hβ) ρβ t R x y))
        atTop (𝓝 0) ∧
      IsCk2 j (pairInverse (mfData d s hs0 hsd V β hβ) ρβ R) ∧
      DoublyCentered (withDensityReal ρβ) (pairInverse (mfData d s hs0 hsd V β hβ) ρβ R) ∧
      ∀ x y, -(centeredGen (mfData d s hs0 hsd V β hβ) ρβ
            (fun x' => pairInverse (mfData d s hs0 hsd V β hβ) ρβ R x' y) x +
          centeredGen (mfData d s hs0 hsd V β hβ) ρβ
            (fun y' => pairInverse (mfData d s hs0 hsd V β hβ) ρβ R x y') y) = R x y := by
  intro j hj2
  have hρ1 : Torus.IsCk 1 ρβ := isCk_of_smooth_ps hρC 1
  have hρc : Continuous ρβ := MFAux.continuous_of_isCk hρ1
  have hprob : IsProbDensity ρβ := hρβ.1
  obtain ⟨J₀, C, c, hC, hc, hdec⟩ :=
    exists_pairSemigroup_decay hd s hs0 hsd β hβ V hV ρβ hρβ hρC hpos j
  obtain ⟨J₂, C₂, c₂, hC₂, hc₂, hdec₂⟩ :=
    exists_pairSemigroup_decay hd s hs0 hsd β hβ V hV ρβ hρβ hρC hpos 2
  have h3 := ClassicalPart.three_le_mStar d
  refine ⟨max (max J₀ J₂) (3 * mStar d + 2 * d + 8), fun R hR hcen => ?_⟩
  have hle : ∀ m, m ≤ max (max J₀ J₂) (3 * mStar d + 2 * d + 8) → IsCk2 m R := fun m hm =>
    hR.of_le (by exact_mod_cast hm)
  have hRJ₀ : IsCk2 J₀ R := hle _ (by omega)
  have hRJ₂ : IsCk2 J₂ R := hle _ (by omega)
  have hR2 : IsCk2 2 R := hle _ (by omega)
  set D := mfData d s hs0 hsd V β hβ with hD
  have hreg : ∀ t, 0 ≤ t → IsCk2 j (pairSemigroup D ρβ t R) := fun t ht =>
    (hdec R hRJ₀ t ht).1
  have hbd : ∀ t, 0 ≤ t → cbNorm2 j (pairSemigroup D ρβ t R) ≤
      (C * cbNorm2 J₀ R) * Real.exp (-c * t) := fun t ht => by
    have := (hdec R hRJ₀ t ht).2.1
    calc _ ≤ C * Real.exp (-c * t) * cbNorm2 J₀ R := this
      _ = _ := by ring
  have hcont : ∀ i : ℕ, i ≤ j → ∀ p : Euc d × Euc d, ContinuousOn (fun t' =>
      iteratedFDeriv ℝ i (lift2 (pairSemigroup D ρβ t' R)) p) (Set.Ici 0) :=
    (hdec R hRJ₀ 0 le_rfl).2.2
  obtain ⟨hint, hptw, hCk, htend⟩ := integral_family_isCk2 j (fun t => pairSemigroup D ρβ t R)
    (C * cbNorm2 J₀ R) c hc hreg hbd hcont
  refine ⟨hreg, hint, hptw, htend, hCk, ?_, ?_⟩
  · refine integral_family_doublyCentered j (fun t => pairSemigroup D ρβ t R) (C * cbNorm2 J₀ R) c hc
      hreg hbd (fun p => hcont 0 (Nat.zero_le _) p) hprob hρc (fun t ht => ?_)
    exact doublyCentered_pairSemigroup hd s hs0 hsd β hβ V hV ρβ hρβ hρC hpos _ (le_max_right _ _) R hR t ht
  · intro x y
    have hreg₂ : ∀ t, 0 ≤ t → IsCk2 2 (pairSemigroup D ρβ t R) := fun t ht => (hdec₂ R hRJ₂ t ht).1
    have hbd₂ : ∀ t, 0 ≤ t → cbNorm2 2 (pairSemigroup D ρβ t R) ≤
        (C₂ * cbNorm2 J₂ R) * Real.exp (-c₂ * t) := fun t ht => by
      have := (hdec₂ R hRJ₂ t ht).2.1
      calc _ ≤ C₂ * Real.exp (-c₂ * t) * cbNorm2 J₂ R := this
        _ = _ := by ring
    have key := centeredGen_integral_family hd s hs0 hsd β hβ V hV ρβ hρβ hρC hpos
      (fun t => pairSemigroup D ρβ t R) (C₂ * cbNorm2 J₂ R) c₂ hc₂ hreg₂ hbd₂
      (fun i hi p => (hdec₂ R hRJ₂ 0 le_rfl).2.2 i hi p)
      (fun x y t ht => hasDerivAt_pairSemigroup hd s hs0 hsd β hβ V hV ρβ hρβ hρC hpos _
        (le_max_right _ _) R hR x y t ht) x y
    have h0 := congrFun (congrFun (pairSemigroup_zero hd s hs0 hsd β hβ V hV ρβ hρβ hρC hpos R hR2 hcen) x) y
    rw [h0] at key
    exact key

end PairCentered

end HRS.PDE.MFPair
