import HRS.MH.DualityRdDefs
import HRS.MP.RdGenCalc
import HRS.MP.RdGenAux
import HRS.Whole.MovtrAux4
import HRS.Whole.Q09BAux2

/-!
# DualityRd packet C1a: the pairing expansion (Lemma 3.1 (1)-(4)) on `ℝ^d`

Port of `HRS.pairing_expansion_pointwise` (`HRS/Stochastic/Duality.lean:86`) to the whole space.  With
`w = Mᵀ∇ψ(x)`, `v_j(y) = (Mᵀ∇ψ(y))_j`, `h_j = ρ v_j`, the algebraic core is the pointwise identity
`ρ(x-z) K(x,x-z) = ∑_j (w_j κ_j(z) R(z) - κ_j(z) R_j(z))` (`R`, `R_j` the cancellation-convention
differences of `ρ`, `h_j`), where `κ_j = (∇g)_j`.  Integrability and bounds come from the whole-space
kernel estimates `HRS.MP.RdGen.rg_integrable`, `rg_norm_T_le`, `rg_force_comp`, `rg_rho_decay`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.DualityRd

open HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

/-! ### Linear algebra -/

theorem dc1a_inner_matVec (M : Matrix (Fin d) (Fin d) ℝ) (u v : Euc d) :
    inner ℝ u (Torus.matVec M v) = inner ℝ (Torus.matVec M.transpose u) v := by
  rw [HRS.Whole.Q09B.q09b_inner_euc, HRS.Whole.Q09B.q09b_inner_euc]
  simp only [HRS.Whole.Q09B.q09b_matVec_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dc1a_inner_matVec_sum (M : Matrix (Fin d) (Fin d) ℝ) (a v : Euc d) :
    inner ℝ a (Torus.matVec M v) = ∑ j, (Torus.matVec M.transpose a) j * v j := by
  rw [dc1a_inner_matVec, HRS.Whole.Q09B.q09b_inner_euc]

theorem dc1a_matVec_sub (M : Matrix (Fin d) (Fin d) ℝ) (a b : Euc d) :
    Torus.matVec M (a - b) = Torus.matVec M a - Torus.matVec M b := by
  unfold Torus.matVec
  exact map_sub _ _ _

/-! ### Weighted derivative classes of the data -/

theorem dc1a_bdd_two {ψ : Euc d → ℝ} (hψ : MemCb 2 ψ) :
    ∃ B : ℝ, ∀ n, n ≤ 2 → ∀ x, ‖iteratedFDeriv ℝ n ψ x‖ ≤ B := by
  have h : ∀ n, n ≤ 2 → ∃ B : ℝ, ∀ x, ‖iteratedFDeriv ℝ n ψ x‖ ≤ B := fun n hn => by
    obtain ⟨B, hB⟩ := hψ.2 n hn
    exact ⟨B, fun x => hB (Set.mem_range_self x)⟩
  obtain ⟨B0, h0⟩ := h 0 (by norm_num)
  obtain ⟨B1, h1⟩ := h 1 (by norm_num)
  obtain ⟨B2, h2⟩ := h 2 le_rfl
  have p1 : 0 ≤ B1 := (norm_nonneg _).trans (h1 0)
  have p0 : 0 ≤ B0 := (norm_nonneg _).trans (h0 0)
  have p2 : 0 ≤ B2 := (norm_nonneg _).trans (h2 0)
  refine ⟨B0 + B1 + B2, fun n hn x => ?_⟩
  interval_cases n
  · linarith [h0 x]
  · linarith [h1 x]
  · linarith [h2 x]

theorem dc1a_grad_comp_rgW {ψ : Euc d → ℝ} (hψ : MemCb 2 ψ) (i : Fin d) :
    ∃ B : ℝ, 0 ≤ B ∧ HRS.MP.RdGen.RgW (fun _ => (1 : ℝ)) 1 B (fun y => gradient ψ y i) := by
  obtain ⟨B, hB⟩ := dc1a_bdd_two hψ
  refine ⟨max 0 B, le_max_left _ _, ?_⟩
  have h := HRS.MP.RdGen.rg_grad_comp (k := 1) (φ := ψ) hψ.1
    (fun n hn x => hB n (by omega) x) i
  exact HRS.MP.RdGen.RgW.mono (fun _ => zero_le_one) h (le_max_right _ _)

/-- `v_j(y) = (Mᵀ∇ψ(y))_j` is a bounded `C^1` function with bounded derivative. -/
theorem dc1a_v_rgW {ψ : Euc d → ℝ} (hψ : MemCb 2 ψ) (M : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) :
    ∃ c : ℝ, 0 ≤ c ∧ HRS.MP.RdGen.RgW (fun _ => (1 : ℝ)) 1 c
      (fun y => (Torus.matVec M.transpose (gradient ψ y)) j) := by
  have hc : ∀ i : Fin d, ∃ B : ℝ, 0 ≤ B ∧
      HRS.MP.RdGen.RgW (fun _ => (1 : ℝ)) 1 B (fun y => gradient ψ y i) :=
    fun i => dc1a_grad_comp_rgW hψ i
  choose B hB0 hB using hc
  have hsum := HRS.MP.RdGen.RgW.sum (w := fun _ : Euc d => (1 : ℝ)) (k := 1) Finset.univ
    (c := fun i => |M i j| * B i) (u := fun i y => M i j * gradient ψ y i)
    (fun i _ => HRS.MP.RdGen.RgW.const_mul (M i j) (hB i))
  refine ⟨max 0 (∑ i, |M i j| * B i), le_max_left _ _, ?_⟩
  refine HRS.MP.RdGen.RgW.mono (fun _ => zero_le_one) ?_ (le_max_right _ _)
  have e : (fun y => (Torus.matVec M.transpose (gradient ψ y)) j) =
      fun y => ∑ i ∈ Finset.univ, M i j * gradient ψ y i := by
    funext y
    rw [HRS.Whole.Q09B.q09b_matVec_apply]
    simp [Matrix.transpose_apply]
  rw [e]
  exact hsum

/-- Facts extracted from a weighted class `RgW` with the decay weight. -/
theorem dc1a_rgW_facts {u : Euc d → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hu : HRS.MP.RdGen.RgW (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) 1 c u) :
    Differentiable ℝ u ∧ Continuous u ∧ (∀ y, ‖u y‖ ≤ c * (1 + ‖y‖) ^ (-((d : ℝ) + 1))) ∧
      (∀ y, ‖fderiv ℝ u y‖ ≤ c) ∧ (∀ y, ‖u y‖ ≤ c) := by
  have hw1 : ∀ y : Euc d, (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ 1 := fun y =>
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y])
      (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
  have h0 : ∀ y, ‖u y‖ ≤ c * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := fun y => by
    have := hu.2 0 (Nat.zero_le _) y
    rwa [norm_iteratedFDeriv_zero] at this
  have h1 : ∀ y, ‖fderiv ℝ u y‖ ≤ c := fun y => by
    have := hu.2 1 le_rfl y
    rw [norm_iteratedFDeriv_one] at this
    exact this.trans (mul_le_of_le_one_right hc (hw1 y))
  have hdiff : Differentiable ℝ u := hu.1.differentiable (by norm_num)
  exact ⟨hdiff, hdiff.continuous, h0, h1,
    fun y => (h0 y).trans (mul_le_of_le_one_right hc (hw1 y))⟩

/-- The density `ρ` is a weighted class with the decay weight. -/
theorem dc1a_rho_rgW {ρ : Euc d → ℝ} (hd : 1 ≤ d) (hρ : RegSliceRd ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ HRS.MP.RdGen.RgW (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) 1 C ρ := by
  unfold RegSliceRd at hρ
  obtain ⟨_, hcb, hfin⟩ := hρ
  have hdec := HRS.MP.RdGen.rg_rho_decay hd hcb hfin (le_refl _)
  refine ⟨(d : ℝ) ^ 3 * (weightedSupE 3 ((d : ℝ) + 3) ρ).toReal * 2 ^ ((d : ℝ) + 3), ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (by positivity) ENNReal.toReal_nonneg) (by positivity)
  · exact ⟨ContDiff.of_le hdec.1 (by exact_mod_cast (show 1 ≤ 3 by norm_num)),
      fun n hn y => hdec.2 n (by omega) y⟩

theorem dc1a_mul_rgW {u v : Euc d → ℝ} {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hu : HRS.MP.RdGen.RgW (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) 1 C u)
    (hv : HRS.MP.RdGen.RgW (fun _ => (1 : ℝ)) 1 c v) :
    HRS.MP.RdGen.RgW (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) 1 (2 ^ 1 * C * c)
      (fun y => u y * v y) :=
  HRS.MP.RdGen.RgW.mul (fun y => by positivity) hC hc hu hv

/-! ### The pointwise identity and the integrals -/

/-- Pointwise algebra: `ρ(x-z) K(x,x-z)` in terms of the cancellation-convention differences. -/
theorem dc1a_pointwise (D : WholeDyn d) (ψ ρ : Euc d → ℝ) (x z : Euc d) :
    ρ (x - z) * pairKernelRd D ψ x (x - z) =
      ∑ j : Fin d, ((Torus.matVec D.M.transpose (gradient ψ x)) j *
          (rieszKernelGrad d D.s z j * movtr_R ρ x z)
        - rieszKernelGrad d D.s z j *
          movtr_R (fun y => ρ y * (Torus.matVec D.M.transpose (gradient ψ y)) j) x z) := by
  by_cases hz : z = 0
  · subst hz
    simp [pairKernelRd, movtr_R]
  · have hne : x ≠ x - z := fun h => hz (sub_eq_self.mp h.symm)
    have hK : pairKernelRd D ψ x (x - z) = ∑ j : Fin d,
        ((Torus.matVec D.M.transpose (gradient ψ x)) j -
          (Torus.matVec D.M.transpose (gradient ψ (x - z))) j) * rieszKernelGrad d D.s z j := by
      unfold pairKernelRd
      rw [if_neg hne, sub_sub_cancel, dc1a_inner_matVec_sum, dc1a_matVec_sub]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [PiLp.sub_apply]
    rw [hK, Finset.mul_sum]
    by_cases hnear : ‖z‖ ≤ 1 / 4
    · simp only [movtr_R, if_pos hnear]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · simp only [movtr_R, if_neg hnear]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

/-- An integrable kernel-weighted difference: `z ↦ κ(z) · R(z)` for a weighted-class `u`. -/
theorem dc1a_kernel_int {u : Euc d → ℝ} {c : ℝ} (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (hc : 0 ≤ c)
    (hu : HRS.MP.RdGen.RgW (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) 1 c u)
    {κ : Euc d → ℝ} (hκ : HRS.MP.RdGen.RgKer d s (movtr_sigma s) κ) (x : Euc d) :
    Integrable (fun z => κ z * movtr_R u x z) := by
  obtain ⟨h1, -, h0, h1', -⟩ := dc1a_rgW_facts hc hu
  have := HRS.MP.RdGen.rg_integrable hd hs0 hsd hκ h1 hc hc h0 h1' x
  refine this.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [smul_eq_mul, HRS.MP.RdGen.rg_movtr_R_eq]

/-- The cancellation-convention integral `∫ κ(z) R(z) dz` is the component of the convolution. -/
theorem dc1a_force_eq {u : Euc d → ℝ} {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    {c : ℝ} (hc : 0 ≤ c)
    (hu : HRS.MP.RdGen.RgW (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) 1 c u) (x : Euc d) (j : Fin d) :
    (convGradConvW (rieszKernelGrad d s) u x) j = ∫ z, rieszKernelGrad d s z j * movtr_R u x z := by
  obtain ⟨h1, -, h0, h1', -⟩ := dc1a_rgW_facts hc hu
  rw [HRS.MP.RdGen.rg_force_comp hd hs0 hsd h1 hc hc h0 h1' x j]
  unfold HRS.MP.RdGen.rgT
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [smul_eq_mul, HRS.MP.RdGen.rg_movtr_R_eq]

/-- The norm bound of the cancellation-convention convolution (uniform in `x`). -/
theorem dc1a_force_bound {u : Euc d → ℝ} {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    {c : ℝ} (hc : 0 ≤ c)
    (hu : HRS.MP.RdGen.RgW (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) 1 c u) (x : Euc d) (j : Fin d) :
    ‖(convGradConvW (rieszKernelGrad d s) u x) j‖ ≤
      movtr_sigma s * (c * HRS.MP.RdGen.rgNear d s + 4 ^ (s + 1) * c * HRS.MP.RdGen.rgW d) := by
  obtain ⟨h1, -, h0, h1', -⟩ := dc1a_rgW_facts hc hu
  rw [HRS.MP.RdGen.rg_force_comp hd hs0 hsd h1 hc hc h0 h1' x j]
  have hK := HRS.MP.RdGen.rgKerComp_ok hs0 j
  exact HRS.MP.RdGen.rg_norm_T_le hd hs0 hsd hK h1 hc hc h0 h1' x

/-- Measurability of a parametric cancellation-convention integral. -/
theorem dc1a_meas_int {κ : Euc d → ℝ} (hκ : Measurable κ) {u : Euc d → ℝ} (hu : Continuous u) :
    StronglyMeasurable (fun x => ∫ z, κ z * movtr_R u x z) := by
  have h1 : Measurable (fun p : Euc d × Euc d => κ p.2) := hκ.comp measurable_snd
  have h2 : Measurable (fun p : Euc d × Euc d => u (p.1 - p.2)) :=
    hu.measurable.comp (measurable_fst.sub measurable_snd)
  have h3 : Measurable (fun p : Euc d × Euc d => u p.1) := hu.measurable.comp measurable_fst
  have h4 : Measurable (fun p : Euc d × Euc d => movtr_R u p.1 p.2) := by
    unfold movtr_R
    exact Measurable.ite (measurableSet_le (measurable_norm.comp measurable_snd) measurable_const)
      (h2.sub h3) h2
  exact (Measurable.mul h1 h4).stronglyMeasurable.integral_prod_right

theorem dc1a_integral_withDensity {ρ : Euc d → ℝ} (hm : Measurable ρ) (hnn : ∀ y, 0 ≤ ρ y)
    (f : Euc d → ℝ) :
    ∫ y, f y ∂(Whole.withDensityReal ρ) = ∫ y, ρ y * f y := by
  unfold Whole.withDensityReal
  have hmeas : Measurable (fun x => ENNReal.ofReal (ρ x)) := ENNReal.measurable_ofReal.comp hm
  rw [integral_withDensity_eq_integral_toReal_smul hmeas
    (Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Function.comp_apply, ENNReal.toReal_ofReal (hnn y), smul_eq_mul]

theorem dc1a_abs_sum_le {ι : Type*} (s : Finset ι) (a b α β : ι → ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ α i) (hb : ∀ i ∈ s, |b i| ≤ β i) (hα : ∀ i ∈ s, 0 ≤ α i)
    (hβ : ∀ i ∈ s, 0 ≤ β i) :
    |∑ i ∈ s, a i * b i| ≤ ∑ i ∈ s, α i * β i := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [abs_mul]
  exact mul_le_mul (ha i hi) (hb i hi) (abs_nonneg _) (hα i hi)

theorem dc1a_force_bound' {u : Euc d → ℝ} {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    {c : ℝ} (hc : 0 ≤ c)
    (hu : HRS.MP.RdGen.RgW (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) 1 c u) (j : Fin d) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖(convGradConvW (rieszKernelGrad d s) u x) j‖ ≤ B :=
  ⟨max 0 (movtr_sigma s * (c * HRS.MP.RdGen.rgNear d s + 4 ^ (s + 1) * c * HRS.MP.RdGen.rgW d)),
    le_max_left _ _, fun x => (dc1a_force_bound hd hs0 hsd hc hu x j).trans (le_max_right _ _)⟩

theorem dc1a_abs_sum_le' {ι : Type*} (s : Finset ι) (a α : ι → ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ α i) : |∑ i ∈ s, a i| ≤ ∑ i ∈ s, α i :=
  (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ha)

theorem pairing_expansion_rd_proof (D : WholeDyn d) (hd : 1 ≤ d) (hs0 : 0 ≤ D.s) (hsd : D.s < d) {ρ : Euc d → ℝ}
    (hρ : RegSliceRd ρ) {ψ : Euc d → ℝ} (hψ : MemCb 2 ψ) :
    (∀ x, Integrable (fun y => ρ y * pairKernelRd D ψ x y)) ∧
    (∀ x, ∫ y, pairKernelRd D ψ x y ∂(Whole.withDensityReal ρ)
        = inner ℝ (gradient ψ x) (Torus.matVec D.M (convGradConvW (rieszKernelGrad d D.s) ρ x))
          - nlTermRd D ρ ψ x) ∧
    Integrable (fun x => ρ x * inner ℝ (gradient ψ x)
      (Torus.matVec D.M (convGradConvW (rieszKernelGrad d D.s) ρ x))) ∧
    Integrable (fun x => ρ x * nlTermRd D ρ ψ x) := by
  obtain ⟨Cρ, hCρ0, hρW⟩ := dc1a_rho_rgW hd hρ
  have hP : Whole.IsProbDensity ρ := by unfold RegSliceRd at hρ; exact hρ.1
  have hρm : Measurable ρ := hP.measurable
  have hρnn : ∀ y, 0 ≤ ρ y := hP.nonneg
  obtain ⟨hρdiff, hρcont, hρ0, hρ1, -⟩ := dc1a_rgW_facts hCρ0 hρW
  have hρint : Integrable ρ :=
    Integrable.mono' ((HRS.MP.RdGen.rg_W_integrable hd).const_mul Cρ) hρm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => hρ0 y)
  choose cv hcv0 hvW using fun j : Fin d => dc1a_v_rgW hψ D.M j
  have hcvb : ∀ j x, |(Torus.matVec D.M.transpose (gradient ψ x)) j| ≤ cv j := fun j x => by
    have := (hvW j).2 0 (Nat.zero_le _) x
    rw [norm_iteratedFDeriv_zero] at this
    simpa [Real.norm_eq_abs] using this
  have hvc : ∀ j : Fin d, Continuous fun x => (Torus.matVec D.M.transpose (gradient ψ x)) j :=
    fun j => (hvW j).1.continuous
  have hc2 : ∀ j : Fin d, 0 ≤ 2 ^ 1 * Cρ * cv j :=
    fun j => mul_nonneg (mul_nonneg (by norm_num) hCρ0) (hcv0 j)
  have hhW : ∀ j : Fin d, HRS.MP.RdGen.RgW (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) 1
      (2 ^ 1 * Cρ * cv j) (fun y => ρ y * (Torus.matVec D.M.transpose (gradient ψ y)) j) :=
    fun j => dc1a_mul_rgW hCρ0 (hcv0 j) hρW (hvW j)
  have hhF : ∀ j : Fin d, Differentiable ℝ (fun y => ρ y * (Torus.matVec D.M.transpose (gradient ψ y)) j) ∧
      Continuous (fun y => ρ y * (Torus.matVec D.M.transpose (gradient ψ y)) j) := fun j =>
    ⟨(dc1a_rgW_facts (hc2 j) (hhW j)).1, (dc1a_rgW_facts (hc2 j) (hhW j)).2.1⟩
  have hκm : ∀ j : Fin d, Measurable (fun z => rieszKernelGrad d D.s z j) :=
    fun j => (HRS.MP.RdGen.rgKerComp_ok hs0 j).meas
  have hκ : ∀ j : Fin d, HRS.MP.RdGen.RgKer d D.s (movtr_sigma D.s) (fun z => rieszKernelGrad d D.s z j) :=
    fun j => HRS.MP.RdGen.rgKerComp_ok hs0 j
  -- the integrand in `z` is integrable and equals the sum of the component kernels
  have hIint : ∀ x, Integrable (fun z => ∑ j : Fin d,
      ((Torus.matVec D.M.transpose (gradient ψ x)) j * (rieszKernelGrad d D.s z j * movtr_R ρ x z)
        - rieszKernelGrad d D.s z j *
          movtr_R (fun y => ρ y * (Torus.matVec D.M.transpose (gradient ψ y)) j) x z)) := fun x =>
    integrable_finsetSum _ fun j _ =>
      ((dc1a_kernel_int hd hs0 hsd hCρ0 hρW (hκ j) x).const_mul _).sub
        (dc1a_kernel_int hd hs0 hsd (hc2 j) (hhW j) (hκ j) x)
  have hZint : ∀ x, Integrable (fun z => ρ (x - z) * pairKernelRd D ψ x (x - z)) := fun x =>
    (hIint x).congr (Filter.Eventually.of_forall fun z => (dc1a_pointwise D ψ ρ x z).symm)
  have hIj : ∀ x (j : Fin d), Integrable (fun z => (Torus.matVec D.M.transpose (gradient ψ x)) j *
      (rieszKernelGrad d D.s z j * movtr_R ρ x z)
        - rieszKernelGrad d D.s z j * movtr_R (fun y => ρ y * (Torus.matVec D.M.transpose (gradient ψ y)) j) x z) :=
    fun x j => ((dc1a_kernel_int hd hs0 hsd hCρ0 hρW (hκ j) x).const_mul _).sub
        (dc1a_kernel_int hd hs0 hsd (hc2 j) (hhW j) (hκ j) x)
  have hIeq : ∀ x, ∫ z, ρ (x - z) * pairKernelRd D ψ x (x - z) =
      ∑ j : Fin d, ((Torus.matVec D.M.transpose (gradient ψ x)) j * convGradConvW (rieszKernelGrad d D.s) ρ x j
        - convGradConvW (rieszKernelGrad d D.s)
            (fun y => ρ y * (Torus.matVec D.M.transpose (gradient ψ y)) j) x j) := fun x => by
    rw [funext (dc1a_pointwise D ψ ρ x)]
    rw [integral_finsetSum _ fun j _ => hIj x j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_sub ((dc1a_kernel_int hd hs0 hsd hCρ0 hρW (hκ j) x).const_mul _)
        (dc1a_kernel_int hd hs0 hsd (hc2 j) (hhW j) (hκ j) x), integral_const_mul,
      dc1a_force_eq hd hs0 hsd hCρ0 hρW x j, dc1a_force_eq hd hs0 hsd (hc2 j) (hhW j) x j]
  -- measurability and bounds of the components
  have hconv_meas : ∀ j : Fin d, Measurable (fun x => (convGradConvW (rieszKernelGrad d D.s) ρ x) j) := by
    intro j
    have e : (fun x => (convGradConvW (rieszKernelGrad d D.s) ρ x) j) =
        fun x => ∫ z, rieszKernelGrad d D.s z j * movtr_R ρ x z :=
      funext fun x => dc1a_force_eq hd hs0 hsd hCρ0 hρW x j
    rw [e]
    exact (dc1a_meas_int (hκm j) hρcont).measurable
  have hnl_meas : ∀ j : Fin d, Measurable (fun x => (convGradConvW (rieszKernelGrad d D.s)
      (fun y => ρ y * (Torus.matVec D.M.transpose (gradient ψ y)) j) x) j) := by
    intro j
    have e : (fun x => (convGradConvW (rieszKernelGrad d D.s)
        (fun y => ρ y * (Torus.matVec D.M.transpose (gradient ψ y)) j) x) j) =
        fun x => ∫ z, rieszKernelGrad d D.s z j *
          movtr_R (fun y => ρ y * (Torus.matVec D.M.transpose (gradient ψ y)) j) x z :=
      funext fun x => dc1a_force_eq hd hs0 hsd (hc2 j) (hhW j) x j
    rw [e]
    exact (dc1a_meas_int (hκm j) (hhF j).2).measurable
  choose Bc hBc0 hBc using fun j : Fin d => dc1a_force_bound' hd hs0 hsd hCρ0 hρW j
  choose Bh hBh0 hBh using fun j : Fin d => dc1a_force_bound' hd hs0 hsd (hc2 j) (hhW j) j
  -- (1) the integrability in `y`
  have part1 : ∀ x, Integrable (fun y => ρ y * pairKernelRd D ψ x y) := fun x => by
    have h := (hZint x).comp_sub_left x
    simpa only [sub_sub_cancel] using h
  -- (2) the pairing with the density `ρ`
  have part2 : ∀ x, ∫ y, pairKernelRd D ψ x y ∂(Whole.withDensityReal ρ)
      = inner ℝ (gradient ψ x) (Torus.matVec D.M (convGradConvW (rieszKernelGrad d D.s) ρ x))
          - nlTermRd D ρ ψ x := fun x => by
    rw [dc1a_integral_withDensity hρm hρnn (fun y => pairKernelRd D ψ x y)]
    have hsub := integral_sub_left_eq_self (fun y => ρ y * pairKernelRd D ψ x y) volume x
    rw [← hsub, hIeq x, dc1a_inner_matVec_sum]
    unfold nlTermRd
    rw [Finset.sum_sub_distrib]
  -- (3) the interaction term of the drift
  have hmeasS : Measurable (fun x => ∑ j : Fin d, (Torus.matVec D.M.transpose (gradient ψ x)) j *
      convGradConvW (rieszKernelGrad d D.s) ρ x j) :=
    Finset.measurable_sum _ fun j _ => (hvc j).measurable.mul (hconv_meas j)
  have part3 : Integrable (fun x => ρ x * inner ℝ (gradient ψ x)
      (Torus.matVec D.M (convGradConvW (rieszKernelGrad d D.s) ρ x))) := by
    have e3 : (fun x => ρ x * inner ℝ (gradient ψ x)
        (Torus.matVec D.M (convGradConvW (rieszKernelGrad d D.s) ρ x))) =
        fun x => ρ x * ∑ j : Fin d, (Torus.matVec D.M.transpose (gradient ψ x)) j *
          convGradConvW (rieszKernelGrad d D.s) ρ x j := by
      funext x; rw [dc1a_inner_matVec_sum]
    rw [e3]
    refine Integrable.mono' (hρint.const_mul (∑ j : Fin d, cv j * Bc j))
      (hρm.mul hmeasS).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    have hS : |∑ j : Fin d, (Torus.matVec D.M.transpose (gradient ψ x)) j *
        convGradConvW (rieszKernelGrad d D.s) ρ x j| ≤ ∑ j : Fin d, cv j * Bc j :=
      dc1a_abs_sum_le _ _ _ _ _ (fun j _ => hcvb j x) (fun j _ => hBc j x)
        (fun j _ => hcv0 j) (fun j _ => hBc0 j)
    show ‖ρ x * ∑ j : Fin d, (Torus.matVec D.M.transpose (gradient ψ x)) j *
        convGradConvW (rieszKernelGrad d D.s) ρ x j‖ ≤ (∑ j : Fin d, cv j * Bc j) * ρ x
    calc ‖ρ x * ∑ j : Fin d, (Torus.matVec D.M.transpose (gradient ψ x)) j *
          convGradConvW (rieszKernelGrad d D.s) ρ x j‖
        = ρ x * |∑ j : Fin d, (Torus.matVec D.M.transpose (gradient ψ x)) j *
          convGradConvW (rieszKernelGrad d D.s) ρ x j| := by
          rw [norm_mul, Real.norm_of_nonneg (hρnn x), Real.norm_eq_abs]
      _ ≤ ρ x * ∑ j : Fin d, cv j * Bc j := mul_le_mul_of_nonneg_left hS (hρnn x)
      _ = (∑ j : Fin d, cv j * Bc j) * ρ x := mul_comm _ _
  -- (4) the nonlocal term
  have part4 : Integrable (fun x => ρ x * nlTermRd D ρ ψ x) := by
    show Integrable (fun x => ρ x * ∑ j : Fin d, (convGradConvW (rieszKernelGrad d D.s)
      (fun y => ρ y * (Torus.matVec D.M.transpose (gradient ψ y)) j) x) j)
    have hmeas4 : Measurable (fun x => ∑ j : Fin d, (convGradConvW (rieszKernelGrad d D.s)
        (fun y => ρ y * (Torus.matVec D.M.transpose (gradient ψ y)) j) x) j) :=
      Finset.measurable_sum _ fun j _ => hnl_meas j
    refine Integrable.mono' (hρint.const_mul (∑ j : Fin d, Bh j))
      (hρm.mul hmeas4).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    have hS : ‖∑ j : Fin d, (convGradConvW (rieszKernelGrad d D.s)
        (fun y => ρ y * (Torus.matVec D.M.transpose (gradient ψ y)) j) x) j‖ ≤ ∑ j : Fin d, Bh j := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hBh j x)
    show ‖ρ x * ∑ j : Fin d, (convGradConvW (rieszKernelGrad d D.s)
        (fun y => ρ y * (Torus.matVec D.M.transpose (gradient ψ y)) j) x) j‖ ≤ (∑ j : Fin d, Bh j) * ρ x
    calc ‖ρ x * ∑ j : Fin d, (convGradConvW (rieszKernelGrad d D.s)
          (fun y => ρ y * (Torus.matVec D.M.transpose (gradient ψ y)) j) x) j‖
        = ρ x * ‖∑ j : Fin d, (convGradConvW (rieszKernelGrad d D.s)
          (fun y => ρ y * (Torus.matVec D.M.transpose (gradient ψ y)) j) x) j‖ := by
          rw [norm_mul, Real.norm_of_nonneg (hρnn x)]
      _ ≤ ρ x * ∑ j : Fin d, Bh j := mul_le_mul_of_nonneg_left hS (hρnn x)
      _ = (∑ j : Fin d, Bh j) * ρ x := mul_comm _ _
  exact ⟨part1, part2, part3, part4⟩

end HRS.MH.DualityRd
