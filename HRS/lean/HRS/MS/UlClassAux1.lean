import HRS.MS.UlMildAux5

/-!
# UL-5 (S5.1 infrastructure, supplement foundation packet), part 1: the generator of `ouSg` at `0+`

Not a manuscript row.  Files: `UlClassAux1` (this file: right derivative of `h ↦ P_h φ (x)` at `h = 0`
for `φ ∈ C_b^2`, joint continuity and uniform bounds for strongly continuous families),
`UlClassAux2` (the Duhamel integral is a classical solution of the inhomogeneous OU equation),
`UlClass` (existence and uniqueness of the classical evolution `IsUlBackwardEvolution`), `UlTie1`
(the frozen statement `ul_adjoint_fixed_viscosity`).  Helper lemmas carry the prefix `ul5_`.

* `ul5_avg_tendsto`: `∫ ψ (e^{-sQ} x + y) dN(0,Σ_s)(y) → ψ x` as `s → 0+` for bounded continuous `ψ`
  (Markov inequality with the first moment bound `ul3C_m1`).
* `ul5_iter_tendsto`: `D^i (P_s φ)(x) → D^i φ (x)` as `s → 0+` (`i ≤ 2`).
* `ul5_gen_right`: `HasDerivWithinAt (fun s => P_s φ x) (L_0 φ x) (Ici 0) 0` for `φ ∈ C_b^2`,
  `L_0 φ = νΔφ + ⟨-Qx, ∇φ⟩` (`ul5A`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff ComplexConjugate FourierTransform RealInnerProductSpace Matrix MatrixOrder

namespace HRS.MS.Ul
open HRS HRS.Whole HRS.Whole.AppendixA HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.UlocMW
open HRS.MS.Lc HRS.MD.EQLawPath

variable {d : ℕ}

section Gen
variable (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ}

/-- the base generator `L_0 f = νΔf + ⟨-Qx, ∇f⟩` -/
def ul5A (Q : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (f : Euc d → ℝ) (x : Euc d) : ℝ :=
  ν * Laplacian.laplacian f x + inner ℝ (-(Torus.matVec Q x)) (gradient f x)

/-- `ψ(e^{-sQ}x + y)` averaged against `N(0,Σ_s)` converges to `ψ(x)` as `s → 0+` -/
theorem ul5_avg_tendsto (hν : 0 < ν) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {ψ : Euc d → F} (hψ : Continuous ψ) {B : ℝ} (hB : ∀ y, ‖ψ y‖ ≤ B) (x : Euc d) :
    Tendsto (fun s : ℝ => ∫ y, ψ (ouExp Q s x + y) ∂(ouLaw Q ν s)) (𝓝[≥] 0) (𝓝 (ψ x)) := by
  obtain ⟨c, hc0, hc⟩ := ul3C_m1 Q hν 1
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hψδ⟩ := Metric.continuous_iff.1 hψ x (ε / 4) (by positivity)
  have hpt : ∀ z, ‖ψ z - ψ x‖ ≤ ε / 4 + (2 * B / δ) * ‖z - x‖ := by
    intro z
    by_cases hz : ‖z - x‖ < δ
    · have h1 := hψδ z (by rwa [dist_eq_norm])
      rw [dist_eq_norm] at h1
      have h2 : 0 ≤ (2 * B / δ) * ‖z - x‖ := by positivity
      linarith
    · push_neg at hz
      have h1 : ‖ψ z - ψ x‖ ≤ 2 * B := (norm_sub_le _ _).trans (by linarith [hB z, hB x])
      have h2 : 2 * B ≤ (2 * B / δ) * ‖z - x‖ := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
        nlinarith [mul_le_mul_of_nonneg_left hz (by positivity : (0 : ℝ) ≤ 2 * B)]
      linarith [show 0 ≤ ε / 4 from by positivity]
  set K : ℝ := 2 * B / δ with hK
  have hK0 : 0 ≤ K := by positivity
  have h1 : Continuous fun s' : ℝ => ouExp Q s' x - x :=
    ((ul2_exp_cont Q).clm_apply continuous_const).sub continuous_const
  have h1' : Tendsto (fun s' : ℝ => ‖ouExp Q s' x - x‖) (𝓝[≥] 0) (𝓝 0) := by
    have := (h1.norm.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ici (0 : ℝ)))
    simpa [ouExp_zero] using this
  have h2 : Tendsto (fun s' : ℝ => c * Real.sqrt s') (𝓝[≥] 0) (𝓝 0) := by
    have hc' : Continuous fun s' : ℝ => c * Real.sqrt s' := continuous_const.mul Real.continuous_sqrt
    have := (hc'.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ici (0 : ℝ)))
    simpa using this
  have hg : Tendsto (fun s' : ℝ => K * (‖ouExp Q s' x - x‖ + c * Real.sqrt s')) (𝓝[≥] 0) (𝓝 0) := by
    simpa using (h1'.add h2).const_mul K
  filter_upwards [hg.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 2)),
    Icc_mem_nhdsGE (zero_lt_one' ℝ)] with s hs hs1
  rw [dist_eq_norm]
  have hi : Integrable (fun y => ψ (ouExp Q s x + y)) (ouLaw Q ν s) :=
    Integrable.of_bound (hψ.comp (continuous_const.add continuous_id)).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun y => hB _)
  have hnorm : Integrable (fun y : Euc d => ‖y‖) (ouLaw Q ν s) :=
    (IsGaussian.integrable_id (μ := ouLaw Q ν s)).norm
  have e : (∫ y, ψ (ouExp Q s x + y) ∂(ouLaw Q ν s)) - ψ x =
      ∫ y, (ψ (ouExp Q s x + y) - ψ x) ∂(ouLaw Q ν s) := by
    rw [integral_sub hi (integrable_const _)]; simp
  rw [e]
  have hint : Integrable (fun y : Euc d => ε / 4 + K * ‖ouExp Q s x - x‖ + K * ‖y‖) (ouLaw Q ν s) :=
    (integrable_const _).add (hnorm.const_mul K)
  calc ‖∫ y, (ψ (ouExp Q s x + y) - ψ x) ∂(ouLaw Q ν s)‖
      ≤ ∫ y, (ε / 4 + K * ‖ouExp Q s x - x‖ + K * ‖y‖) ∂(ouLaw Q ν s) := by
        refine norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun y => ?_)
        refine (hpt _).trans ?_
        have : ‖ouExp Q s x + y - x‖ ≤ ‖ouExp Q s x - x‖ + ‖y‖ := by
          calc ‖ouExp Q s x + y - x‖ = ‖(ouExp Q s x - x) + y‖ := by congr 1; abel
            _ ≤ _ := norm_add_le _ _
        nlinarith [mul_le_mul_of_nonneg_left this hK0]
    _ = ε / 4 + K * ‖ouExp Q s x - x‖ + K * ∫ y, ‖y‖ ∂(ouLaw Q ν s) := by
        rw [integral_add (integrable_const _) (hnorm.const_mul K), integral_const_mul]
        simp
    _ ≤ ε / 4 + K * ‖ouExp Q s x - x‖ + K * (c * Real.sqrt s) := by
        gcongr
        exact hc s hs1
    _ < ε := by nlinarith [hs]

/-- derivatives of `P_s φ` at a point converge to those of `φ` as `s → 0+` -/
theorem ul5_iter_tendsto (hν : 0 < ν) {φ : Euc d → ℝ} (hφ : ContDiff ℝ 2 φ) {M : ℝ}
    (hM : ∀ i ≤ 2, ∀ y, ‖iteratedFDeriv ℝ i φ y‖ ≤ M) {i : ℕ} (hi : i ≤ 2) (x : Euc d) :
    Tendsto (fun s : ℝ => iteratedFDeriv ℝ i (ouSg Q ν s φ) x) (𝓝[≥] 0)
      (𝓝 (iteratedFDeriv ℝ i φ x)) := by
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin i => Euc d) ℝ,
      ψ = iteratedFDeriv ℝ i φ := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : (Euc d →L[ℝ] Euc d) → (ContinuousMultilinearMap ℝ (fun _ : Fin i => Euc d) ℝ
      →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin i => Euc d) ℝ),
      T = fun E => ContinuousMultilinearMap.compContinuousLinearMapL (F := ℝ) (fun _ : Fin i => E) :=
    ⟨_, rfl⟩
  have hψc : Continuous ψ := by rw [hψdef]; exact hφ.continuous_iteratedFDeriv (by exact_mod_cast hi)
  have hψM : ∀ y, ‖ψ y‖ ≤ M := by rw [hψdef]; exact fun y => hM i hi y
  have hΨ := ul5_avg_tendsto Q hν hψc hψM x
  have hT1 : T 1 = ContinuousLinearMap.id ℝ _ := by
    rw [hT]
    ext f x
    simp
  have hTc : Continuous T := by rw [hT]; exact ul3C_T_cont (d := d) i
  have hE0 : Tendsto (fun s : ℝ => ouExp Q s) (𝓝[≥] 0) (𝓝 (1 : Euc d →L[ℝ] Euc d)) := by
    have := (ul2_exp_cont Q).continuousAt (x := 0)
    have h0 := this.tendsto
    rw [ouExp_zero Q] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hg : Continuous (fun p : (Euc d →L[ℝ] Euc d) ×
      ContinuousMultilinearMap ℝ (fun _ : Fin i => Euc d) ℝ => T p.1 p.2) :=
    (hTc.comp continuous_fst).clm_apply continuous_snd
  have hprod : Tendsto (fun s : ℝ => T (ouExp Q s) (∫ y, ψ (ouExp Q s x + y) ∂(ouLaw Q ν s)))
      (𝓝[≥] 0) (𝓝 (T 1 (ψ x))) :=
    (hg.tendsto (1, ψ x)).comp (hE0.prodMk_nhds hΨ)
  rw [hT1] at hprod
  simp only [ContinuousLinearMap.id_apply] at hprod
  rw [hψdef] at hprod
  refine hprod.congr fun s => ?_
  have hder := (ul3C_smooth Q ν s 2 (by exact_mod_cast hφ) (M := M) (fun j hj y => hM j hj y)).2 i hi x
  have hint : Integrable (fun y => iteratedFDeriv ℝ i φ (ouExp Q s x + y)) (ouLaw Q ν s) := by
    rw [← hψdef]
    exact Integrable.of_bound (hψc.comp (continuous_const.add continuous_id)).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun y => hψM _)
  have e : iteratedFDeriv ℝ i (ouSg Q ν s φ) x =
      T (ouExp Q s) (∫ y, iteratedFDeriv ℝ i φ (ouExp Q s x + y) ∂(ouLaw Q ν s)) := by
    rw [hder, hT]
    simp only
    rw [← ContinuousLinearMap.integral_comp_comm _ hint]
    rfl
  exact e.symm

/-- the generator as a continuous functional of the derivatives of orders 1 and 2 -/
def ul5G (Q : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (x : Euc d)
    (p : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => Euc d) ℝ ×
      ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Euc d) ℝ) : ℝ :=
  ν * ∑ i : Fin d, p.2 ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] -
    p.1 (fun _ => Torus.matVec Q x)

theorem ul5G_cont2 (Q : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) :
    Continuous (fun q : Euc d × (ContinuousMultilinearMap ℝ (fun _ : Fin 1 => Euc d) ℝ ×
      ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Euc d) ℝ) => ul5G Q ν q.1 q.2) := by
  unfold ul5G
  have hmv : Continuous fun x : Euc d => Torus.matVec Q x :=
    LinearMap.continuous_of_finiteDimensional (Matrix.toEuclideanLin Q)
  have h1 : Continuous fun q : Euc d × (ContinuousMultilinearMap ℝ (fun _ : Fin 1 => Euc d) ℝ ×
      ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Euc d) ℝ) =>
      q.2.1 (fun _ => Torus.matVec Q q.1) :=
    (continuous_fst.comp continuous_snd).eval (continuous_pi fun _ => hmv.comp continuous_fst)
  have h2 : ∀ v : Fin 2 → Euc d, Continuous fun q : Euc d × (ContinuousMultilinearMap ℝ
      (fun _ : Fin 1 => Euc d) ℝ × ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Euc d) ℝ) =>
      q.2.2 v :=
    fun v => (continuous_snd.comp continuous_snd).eval continuous_const
  exact (continuous_const.mul (continuous_finsetSum _ fun i _ => h2 _)).sub h1

theorem ul5G_cont (Q : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (x : Euc d) : Continuous (ul5G Q ν x) :=
  (ul5G_cont2 Q ν).comp (continuous_const.prodMk continuous_id)

theorem ul5G_sub (Q : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (x : Euc d) (p q : ContinuousMultilinearMap ℝ
    (fun _ : Fin 1 => Euc d) ℝ × ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Euc d) ℝ) :
    ul5G Q ν x (p - q) = ul5G Q ν x p - ul5G Q ν x q := by
  simp only [ul5G, Prod.fst_sub, Prod.snd_sub, sub_apply,
    Finset.sum_sub_distrib]
  ring

theorem ul5G_add (Q : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (x : Euc d) (p q : ContinuousMultilinearMap ℝ
    (fun _ : Fin 1 => Euc d) ℝ × ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Euc d) ℝ) :
    ul5G Q ν x (p + q) = ul5G Q ν x p + ul5G Q ν x q := by
  simp only [ul5G, Prod.fst_add, Prod.snd_add, add_apply,
    Finset.sum_add_distrib]
  ring

theorem ul5_A_eq (Q : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (f : Euc d → ℝ) (x : Euc d) :
    ul5A Q ν f x = ul5G Q ν x (iteratedFDeriv ℝ 1 f x, iteratedFDeriv ℝ 2 f x) := by
  unfold ul5A ul5G
  dsimp only
  have hL : Laplacian.laplacian f x = ∑ i : Fin d,
      iteratedFDeriv ℝ 2 f x ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] := by
    have := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (f := f)
      (EuclideanSpace.basisFun (Fin d) ℝ)) x
    rw [this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [EuclideanSpace.basisFun_apply]
  have hI : inner ℝ (-(Torus.matVec Q x)) (gradient f x) =
      - iteratedFDeriv ℝ 1 f x (fun _ => Torus.matVec Q x) := by
    have := ul4_inner_eq (fun x => -(Torus.matVec Q x)) f x
    rw [this, map_neg, iteratedFDeriv_one_apply]
  rw [hL, hI]
  ring

theorem ul5_A_sub (Q : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) {f g : Euc d → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (x : Euc d) :
    ul5A Q ν (fun y => f y - g y) x = ul5A Q ν f x - ul5A Q ν g x := by
  rw [ul5_A_eq, ul5_A_eq, ul5_A_eq, ← ul5G_sub]
  congr 1
  have h1 := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := 1) (x := x) (hf.of_le (by norm_num)).contDiffAt
    (hg.of_le (by norm_num)).contDiffAt
  have h2 := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := 2) (x := x) hf.contDiffAt hg.contDiffAt
  exact Prod.ext h1 h2

theorem ul5_A_add (Q : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) {f g : Euc d → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (x : Euc d) :
    ul5A Q ν (fun y => f y + g y) x = ul5A Q ν f x + ul5A Q ν g x := by
  rw [ul5_A_eq, ul5_A_eq, ul5_A_eq, ← ul5G_add]
  congr 1
  have h1 := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := 1) (x := x) (hf.of_le (by norm_num)).contDiffAt
    (hg.of_le (by norm_num)).contDiffAt
  have h2 := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := 2) (x := x) hf.contDiffAt hg.contDiffAt
  exact Prod.ext h1 h2

/-- **The right derivative of `s ↦ P_s φ (x)` at `s = 0`** for `φ ∈ C_b^2`: `L_0 φ (x)`. -/
theorem ul5_gen_right (hν : 0 < ν) {φ : Euc d → ℝ} (hφ : ContDiff ℝ 2 φ) {M : ℝ}
    (hM : ∀ i ≤ 2, ∀ y, ‖iteratedFDeriv ℝ i φ y‖ ≤ M) (x : Euc d) :
    HasDerivWithinAt (fun s => ouSg Q ν s φ x) (ul5A Q ν φ x) (Ici 0) 0 := by
  have hcont := ul4_ouSg_cont_time Q hν hφ hM x
  refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi 0) ?_ ?_ self_mem_nhdsWithin ?_
  · intro s hs
    exact (ou_forward_hasDerivAt Q hν.le hφ hM hs x).differentiableAt.differentiableWithinAt
  · exact (hcont 0 (mem_Ici.2 le_rfl)).mono Ioi_subset_Ici_self
  · have h1 := ul5_iter_tendsto Q hν hφ hM (i := 1) (by norm_num) x
    have h2 := ul5_iter_tendsto Q hν hφ hM (i := 2) le_rfl x
    have hG : Tendsto (fun s : ℝ => ul5A Q ν (ouSg Q ν s φ) x) (𝓝[≥] 0) (𝓝 (ul5A Q ν φ x)) := by
      simp only [ul5_A_eq]
      exact ((ul5G_cont Q ν x).tendsto _).comp (h1.prodMk_nhds h2)
    refine (hG.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (ou_forward_hasDerivAt Q hν.le hφ hM hs x).deriv.symm

theorem ul5_matVec_le (Q : Matrix (Fin d) (Fin d) ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : Euc d, ‖Torus.matVec Q y‖ ≤ K * ‖y‖ :=
  ⟨‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Q)‖, norm_nonneg _, fun y =>
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Q)).le_opNorm y⟩

/-- a pointwise bound for the base generator in terms of the first and second derivatives -/
theorem ul5_A_bound (Q : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) {f : Euc d → ℝ} {b1 b2 : ℝ} (x : Euc d)
    (h1 : ‖iteratedFDeriv ℝ 1 f x‖ ≤ b1) (h2 : ‖iteratedFDeriv ℝ 2 f x‖ ≤ b2) :
    |ul5A Q ν f x| ≤ |ν| * (d * b2) + b1 * ‖Torus.matVec Q x‖ := by
  rw [ul5_A_eq]
  unfold ul5G
  dsimp only
  have hb2 : 0 ≤ b2 := (norm_nonneg _).trans h2
  have hb1 : 0 ≤ b1 := (norm_nonneg _).trans h1
  have hterm : ∀ i : Fin d, |iteratedFDeriv ℝ 2 f x
      ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)]| ≤ b2 := by
    intro i
    have := (iteratedFDeriv ℝ 2 f x).le_opNorm
      ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)]
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    simp [Fin.prod_univ_two, PiLp.norm_single]
    exact h2
  have hsum : |∑ i : Fin d, iteratedFDeriv ℝ 2 f x
      ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)]| ≤ d * b2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
    simp
  have hv : |iteratedFDeriv ℝ 1 f x (fun _ => Torus.matVec Q x)| ≤ b1 * ‖Torus.matVec Q x‖ := by
    have := (iteratedFDeriv ℝ 1 f x).le_opNorm (fun _ => Torus.matVec Q x)
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton]
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  calc |ν * ∑ i : Fin d, iteratedFDeriv ℝ 2 f x
        ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] -
        iteratedFDeriv ℝ 1 f x (fun _ => Torus.matVec Q x)|
      ≤ |ν * ∑ i : Fin d, iteratedFDeriv ℝ 2 f x
        ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)]| +
        |iteratedFDeriv ℝ 1 f x (fun _ => Torus.matVec Q x)| := abs_sub _ _
    _ ≤ |ν| * (d * b2) + b1 * ‖Torus.matVec Q x‖ := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hsum (abs_nonneg _)) hv

end Gen

section Unif
variable {k : ℕ} {θ : Euc d → ℝ}

/-- joint continuity from continuity in `x` and uniform continuity in `σ` -/
theorem ul5_joint_cont {E : Type*} [NormedAddCommGroup E] {I : Set ℝ} {U : ℝ → Euc d → E}
    (hU : ∀ σ ∈ I, Continuous (U σ))
    (hunif : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ σ ∈ I, ∀ σ' ∈ I, |σ - σ'| < δ → ∀ x,
      ‖U σ x - U σ' x‖ ≤ ε) :
    Continuous (fun p : I × Euc d => U p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨⟨σ₀, h0⟩, x₀⟩
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hu⟩ := hunif (ε / 2) (by positivity)
  obtain ⟨η, hη, hx⟩ := Metric.continuous_iff.1 (hU σ₀ h0) x₀ (ε / 2) (by positivity)
  refine ⟨min δ η, lt_min hδ hη, ?_⟩
  rintro ⟨⟨σ, hσ⟩, x⟩ hd
  rw [Prod.dist_eq, max_lt_iff] at hd
  obtain ⟨hd1, hd2⟩ := hd
  have hd1' : |σ - σ₀| < δ := by
    have := lt_of_lt_of_le hd1 (min_le_left δ η)
    simpa [Subtype.dist_eq, Real.dist_eq] using this
  have hd2' : dist x x₀ < η := lt_of_lt_of_le hd2 (min_le_right δ η)
  have h1 := hu σ hσ σ₀ h0 hd1' x
  have h2 := hx x hd2'
  rw [dist_eq_norm] at h2 ⊢
  calc ‖U σ x - U σ₀ x₀‖ = ‖(U σ x - U σ₀ x) + (U σ₀ x - U σ₀ x₀)‖ := by congr 1; abel
    _ ≤ ‖U σ x - U σ₀ x‖ + ‖U σ₀ x - U σ₀ x₀‖ := norm_add_le _ _
    _ < ε := by linarith

/-- uniform continuity of the derivatives of a uniformly strongly continuous family -/
theorem ul5_ureg_cb (hθ : IsUlCutoff θ) {T : ℝ} {a : ℝ → Euc d → ℝ} (ha : UlUReg k θ T a) {j : ℕ}
    (hk : (j : ℝ) + (d : ℝ) / 2 < k) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ σ ∈ Icc (0 : ℝ) T, ∀ σ' ∈ Icc (0 : ℝ) T, |σ - σ'| < δ → ∀ i ≤ j, ∀ x,
      ‖iteratedFDeriv ℝ i (a σ) x - iteratedFDeriv ℝ i (a σ') x‖ ≤ ε := by
  obtain ⟨C, hC, hcb⟩ := ulClosure_cb k j hk θ hθ
  obtain ⟨δ, hδ, hu⟩ := ha.unif (ε / C) (by positivity)
  refine ⟨δ, hδ, fun σ hσ σ' hσ' hd i hi x => ?_⟩
  have hcl := ul4_closure_sub hθ (ha.mem σ hσ) (ha.mem σ' hσ')
  obtain ⟨hmem, hnorm⟩ := hcb _ hcl
  have h1 : ContDiff ℝ (i : WithTop ℕ∞) (a σ) :=
    (hcb _ (ha.mem σ hσ)).1.1.of_le (by exact_mod_cast hi)
  have h2 : ContDiff ℝ (i : WithTop ℕ∞) (a σ') :=
    (hcb _ (ha.mem σ' hσ')).1.1.of_le (by exact_mod_cast hi)
  have e := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := i) (x := x) h1.contDiffAt h2.contDiffAt
  have e' : iteratedFDeriv ℝ i (fun y => a σ y - a σ' y) x =
      iteratedFDeriv ℝ i (a σ) x - iteratedFDeriv ℝ i (a σ') x := e
  rw [← e']
  refine (ul3_cb_apply hmem hi x).trans (hnorm.trans ?_)
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hu σ hσ σ' hσ' hd)
  rw [ENNReal.toReal_ofReal (by positivity)] at this
  calc C * (ulNormE k θ (fun y => a σ y - a σ' y)).toReal ≤ C * (ε / C) :=
        mul_le_mul_of_nonneg_left this hC.le
    _ = ε := by field_simp

/-- joint continuity of the derivatives of a uniformly strongly continuous family -/
theorem ul5_ureg_joint (hθ : IsUlCutoff θ) {T : ℝ} {a : ℝ → Euc d → ℝ} (ha : UlUReg k θ T a) {j : ℕ}
    (hk : (j : ℝ) + (d : ℝ) / 2 < k) {i : ℕ} (hi : i ≤ j) :
    Continuous (fun p : Icc (0 : ℝ) T × Euc d => iteratedFDeriv ℝ i (a p.1) p.2) := by
  obtain ⟨C, hC, hcb⟩ := ulClosure_cb k j hk θ hθ
  refine ul5_joint_cont (E := ContinuousMultilinearMap ℝ (fun _ : Fin i => Euc d) ℝ)
    (U := fun σ x => iteratedFDeriv ℝ i (a σ) x)
    (fun σ hσ => ?_) (fun ε hε => ?_)
  · exact ((hcb _ (ha.mem σ hσ)).1.1.continuous_iteratedFDeriv (by exact_mod_cast hi))
  · obtain ⟨δ, hδ, h⟩ := ul5_ureg_cb hθ ha hk hε
    exact ⟨δ, hδ, fun σ hσ σ' hσ' hd x => h σ hσ σ' hσ' hd i hi x⟩

/-- uniform bounds for a strongly continuous family -/
theorem ul5_ureg_bdd (hθ : IsUlCutoff θ) {T : ℝ} {a : ℝ → Euc d → ℝ} (ha : UlReg k θ T a) {j : ℕ}
    (hk : (j : ℝ) + (d : ℝ) / 2 < k) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ σ ∈ Icc (0 : ℝ) T, MemCb j (a σ) ∧ cbNorm j (a σ) ≤ B := by
  obtain ⟨C, hC, hcb⟩ := ulClosure_cb k j hk θ hθ
  obtain ⟨W, hW⟩ := ul4_bdd hθ ha
  refine ⟨C * max W 0, by positivity, fun σ hσ => ?_⟩
  obtain ⟨h1, h2⟩ := hcb _ (ha.mem σ hσ)
  refine ⟨h1, h2.trans ?_⟩
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    ((hW σ hσ).trans (ENNReal.ofReal_le_ofReal (le_max_left W 0)))
  rw [ENNReal.toReal_ofReal (le_max_right _ _)] at this
  exact mul_le_mul_of_nonneg_left this hC.le

/-- uniform continuity of `ulPert` along a uniformly strongly continuous family -/
theorem ul5_pert_unif {s : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {ρ : Euc d → ℝ} {c : Euc d → Euc d}
    {ν : ℝ} (H : UlHyp s M ρ c ν k θ) {T : ℝ} {w : ℝ → Euc d → ℝ} (hw : UlUReg k θ T w)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ σ ∈ Icc (0 : ℝ) T, ∀ σ' ∈ Icc (0 : ℝ) T, |σ - σ'| < δ → ∀ x,
      |ulPert s M ρ c (w σ) x - ulPert s M ρ c (w σ') x| ≤ ε := by
  obtain ⟨Ccb, hCcb, hcb⟩ := ulClosure_cb k 4 H.hk θ H.hθ
  obtain ⟨Cp, hCp0, hpcb⟩ := ul4_pert_cb H.hs0 H.hsd M ρ H.hρ H.hc
  obtain ⟨δ, hδ, hw'⟩ := hw.unif (ε / (Cp * Ccb + 1)) (by positivity)
  refine ⟨δ, hδ, fun σ hσ σ' hσ' hσδ x => ?_⟩
  have hd := hcb _ (ul4_closure_sub H.hθ (hw.mem σ hσ) (hw.mem σ' hσ'))
  rw [← ul4_pert_sub H.hs0 H.hsd M ρ H.hρ c (hcb _ (hw.mem σ hσ)).1 (hcb _ (hw.mem σ' hσ')).1 x]
  refine ((hpcb _ hd.1).2 x).trans ?_
  have h1 : (ulNormE k θ (fun x => w σ x - w σ' x)).toReal ≤ ε / (Cp * Ccb + 1) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hw' σ hσ σ' hσ' hσδ)
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  calc Cp * cbNorm 4 (fun x => w σ x - w σ' x) ≤ Cp * (Ccb * (ε / (Cp * Ccb + 1))) :=
        mul_le_mul_of_nonneg_left (hd.2.trans (mul_le_mul_of_nonneg_left h1 hCcb.le)) hCp0
    _ ≤ ε := by
        rw [← mul_assoc, ← mul_div_assoc, div_le_iff₀ (by positivity)]
        nlinarith [mul_nonneg hCp0 hCcb.le]

end Unif

end HRS.MS.Ul
