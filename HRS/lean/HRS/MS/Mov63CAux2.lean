import HRS.MS.Mov63CAux1

/-!
# S6.3, uniqueness chain (N3a, part 1): calculus lemmas and the pointwise-in-`r` identity

Namespace `HRS.MS.Mov63`, helper prefix `mnc_`.  Infrastructure for S6.3 (`mov_nonlinear`); not manuscript rows.
See `Mov63CAux1` for the plan.

* `mnc_ibp_div`: `∫ div Y · ψ = -∫ ⟨Y, ∇ψ⟩` when one of `Y, ψ` has compact support.
* `mnc_div_rho_grad`, `mnc_div_flux`: `div(ρ ∇ψ) = ρ(Δψ + ⟨∇log ρ, ∇ψ⟩) = √ρ (Δφ - Vφ)` for `ψ = φ/√ρ`.
* linearity / measurability / sup-bound of the cancellation force on `RgW` functions.
* `mnc_decomp`: for `ρ_t = ρ₀ + h` with `RegSliceRd ρ_t`, `ψ = φ/√ρ₀`, `φ ∈ C_c^∞`:
  `pair(ρ_t)(νΔψ - ⟨qx,∇ψ⟩) + I(ρ_t) = ∫ v D_φ + A_ψ(h) + Q_ψ(h,h)`, `v = h/√ρ₀`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ}

/-! ### Integration by parts for the divergence -/

lemma mnc_comp_fderiv_apply (Y : Euc d → Euc d) (hY : Differentiable ℝ Y) (x : Euc d) (e : Euc d) (i : Fin d) :
    (fderiv ℝ Y x e) i = fderiv ℝ (fun y => Y y i) x e := by
  have h : HasFDerivAt (fun y => Y y i) ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).comp (fderiv ℝ Y x)) x :=
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasFDerivAt.comp x (hY x).hasFDerivAt
  rw [h.fderiv]
  simp

lemma mnc_inner_single (a : Euc d) (i : Fin d) : inner ℝ (EuclideanSpace.single i (1 : ℝ)) a = a i := by
  simp [EuclideanSpace.inner_single_left]

lemma mnc_gradient_apply (ψ : Euc d → ℝ) (x : Euc d) (i : Fin d) :
    (gradient ψ x) i = fderiv ℝ ψ x (EuclideanSpace.single i 1) := by
  rw [← HRS.MS.PoisKolm.kl_inner_gradient, mnc_inner_single]

lemma mnc_inner_eq_sum (a b : Euc d) : inner ℝ a b = ∑ i, a i * b i := by
  rw [← HRS.MS.Gap.gap1_sum_inner a b]
  simp_rw [mnc_inner_single]

lemma mnc_ibp_div {Y : Euc d → Euc d} {ψ : Euc d → ℝ} (hY : ContDiff ℝ 1 Y) (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ ∨ HasCompactSupport Y) :
    ∫ x, movDiv Y x * ψ x = -∫ x, inner ℝ (Y x) (gradient ψ x) := by
  have hYd : Differentiable ℝ Y := hY.differentiable (by norm_num)
  have hYi : ∀ i : Fin d, ContDiff ℝ 1 (fun y => Y y i) := fun i => contDiff_euclidean.1 hY i
  have hψc : Continuous ψ := hψ.continuous
  -- integrability facts, componentwise
  have hI : ∀ i : Fin d,
      Integrable (fun x => fderiv ℝ (fun y => Y y i) x (EuclideanSpace.single i 1) * ψ x) ∧
      Integrable (fun x => fderiv ℝ ψ x (EuclideanSpace.single i 1) * Y x i) ∧
      Integrable (fun x => ψ x * Y x i) := by
    intro i
    set e : Euc d := EuclideanSpace.single i 1 with he
    have hdY : Continuous fun x => fderiv ℝ (fun y => Y y i) x e :=
      ((hYi i).continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hdψ : Continuous fun x => fderiv ℝ ψ x e :=
      (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hYc : Continuous fun x => Y x i := (hYi i).continuous
    rcases hc with h | h
    · have h2 : HasCompactSupport fun x => fderiv ℝ ψ x e := h.fderiv_apply (𝕜 := ℝ) e
      refine ⟨(hdY.mul hψc).integrable_of_hasCompactSupport (h.mul_left (f := fun x => fderiv ℝ (fun y => Y y i) x e)),
        (hdψ.mul hYc).integrable_of_hasCompactSupport (h2.mul_right (f' := fun x => Y x i)),
        (hψc.mul hYc).integrable_of_hasCompactSupport (h.mul_right (f' := fun x => Y x i))⟩
    · have h1 : HasCompactSupport fun x => Y x i := h.comp_left (g := fun v : Euc d => v i) (by simp)
      have h2 : HasCompactSupport fun x => fderiv ℝ (fun y => Y y i) x e := h1.fderiv_apply (𝕜 := ℝ) e
      refine ⟨(hdY.mul hψc).integrable_of_hasCompactSupport (h2.mul_right (f' := ψ)),
        (hdψ.mul hYc).integrable_of_hasCompactSupport (h1.mul_left (f := fun x => fderiv ℝ ψ x e)),
        (hψc.mul hYc).integrable_of_hasCompactSupport (h1.mul_left (f := ψ))⟩
  have hterm : ∀ i : Fin d, ∫ x, (fderiv ℝ Y x (EuclideanSpace.single i 1)) i * ψ x =
      -∫ x, (Y x i) * (gradient ψ x) i := by
    intro i
    set e : Euc d := EuclideanSpace.single i 1 with he
    have h1 : ∀ x, (fderiv ℝ Y x e) i = fderiv ℝ (fun y => Y y i) x e := fun x => mnc_comp_fderiv_apply Y hYd x e i
    obtain ⟨hA, hB, hC⟩ := hI i
    have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Euc d)))
      (f := ψ) (g := fun y => Y y i) (v := e)
      (by simpa using hB) (by simpa [mul_comm] using hA) hC
      (fun x _ => hψ.differentiable (by norm_num) x) (fun x _ => (hYi i).differentiable (by norm_num) x)
    simp_rw [h1, mnc_gradient_apply]
    calc ∫ x, fderiv ℝ (fun y => Y y i) x e * ψ x = ∫ x, ψ x * fderiv ℝ (fun y => Y y i) x e :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
      _ = -∫ x, fderiv ℝ ψ x e * Y x i := key
      _ = -∫ x, Y x i * fderiv ℝ ψ x e := by
          congr 1
          exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  have hlhs : ∀ x, movDiv Y x * ψ x =
      ∑ i, fderiv ℝ (fun y => Y y i) x (EuclideanSpace.single i 1) * ψ x := by
    intro x
    unfold movDiv
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mnc_comp_fderiv_apply Y hYd x _ i]
  have hrhs : ∀ x, inner ℝ (Y x) (gradient ψ x) =
      ∑ i, fderiv ℝ ψ x (EuclideanSpace.single i 1) * Y x i := by
    intro x
    rw [mnc_inner_eq_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mnc_gradient_apply, mul_comm]
  simp_rw [hlhs, hrhs]
  rw [integral_finsetSum _ (fun i _ => (hI i).1), integral_finsetSum _ (fun i _ => (hI i).2.1),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := hterm i
  have h1 : ∀ x, fderiv ℝ (fun y => Y y i) x (EuclideanSpace.single i 1) = (fderiv ℝ Y x (EuclideanSpace.single i 1)) i :=
    fun x => (mnc_comp_fderiv_apply Y hYd x _ i).symm
  simp_rw [h1]
  rw [this]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show (Y x) i * (gradient ψ x) i = _
  rw [mnc_gradient_apply, mul_comm]


/-! ### Divergence of `ρ ∇ψ`, ground-state form -/

section Ground

variable {ρ : Euc d → ℝ}

lemma mnc_div_rho_grad (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ x, 0 < ρ x) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (x : Euc d) :
    movDiv (fun y => ρ y • gradient ψ y) x =
      ρ x * (Laplacian.laplacian ψ x + inner ℝ (gradient (fun y => Real.log (ρ y)) x) (gradient ψ x)) := by
  have hρd : DifferentiableAt ℝ ρ x := (hρ.differentiable (by simp)) x
  rw [mv1_movDiv_smul hρd (mov2a_gradient_diff hψ x), mov2a_movDiv_gradient hψ]
  have hs : ∑ i, fderiv ℝ ρ x (EuclideanSpace.single i 1) * (gradient ψ x) i =
      ρ x * inner ℝ (gradient (fun y => Real.log (ρ y)) x) (gradient ψ x) := by
    rw [← mov2a_sum_fderiv_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mv1_fderiv_rho hρd (hpos x)]
    ring
  rw [hs]
  ring

lemma mnc_div_flux (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ x, 0 < ρ x) {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (x : Euc d) :
    movDiv (fun y => ρ y • gradient (fun z => φ z / Real.sqrt (ρ z)) y) x =
      Real.sqrt (ρ x) * (Laplacian.laplacian φ x - mov2a_V ρ x * φ x) := by
  have h := mov2a_diffusion_gen (β := 1) hρ hpos hφ x
  simp only [inv_one, one_mul] at h
  have hs : 0 < Real.sqrt (ρ x) := Real.sqrt_pos.2 (hpos x)
  have e : movDiv (fun y => ρ y • gradient (fun z => φ z / Real.sqrt (ρ z)) y) x =
      Real.sqrt (ρ x) * (-(-(Real.sqrt (ρ x))⁻¹ * movDiv (fun y => ρ y • gradient (fun z => φ z / Real.sqrt (ρ z)) y) x)) := by
    field_simp
  rw [e, h]
  ring

/-- `ψ = φ/√ρ` is smooth with compact support when `φ` is. -/
lemma mnc_psi_smooth (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ x, 0 < ρ x) {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (fun x => φ x / Real.sqrt (ρ x)) :=
  hφ.div (hρ.sqrt fun x => (hpos x).ne') fun x => (Real.sqrt_pos.2 (hpos x)).ne'

lemma mnc_psi_cs {φ : Euc d → ℝ} (hc : HasCompactSupport φ) :
    HasCompactSupport (fun x => φ x / Real.sqrt (ρ x)) := by
  have e : (fun x => φ x / Real.sqrt (ρ x)) = φ * (fun x => (Real.sqrt (ρ x))⁻¹) := by
    funext x; simp [div_eq_mul_inv]
  rw [e]
  exact hc.mul_right

lemma mnc_memCb_of_cs {g : Euc d → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (k : ℕ) : MemCb k g := by
  refine ⟨hg.of_le (by exact_mod_cast le_top), fun j hj => ?_⟩
  have h1 : Continuous (iteratedFDeriv ℝ j g) := hg.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)
  have h2 : HasCompactSupport (iteratedFDeriv ℝ j g) := hc.iteratedFDeriv j
  have := (h1.norm).bddAbove_range_of_hasCompactSupport (h2.norm)
  exact this

end Ground


/-! ### The cancellation force on `RgW` functions -/

section Force

variable {s : ℝ}

/-- The decay weight of the `RgW` class used by `DualityRd`. -/
abbrev mnc_W (d : ℕ) : Euc d → ℝ := fun y => (1 + ‖y‖) ^ (-((d : ℝ) + 1))

lemma mnc_force_coord (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {f : Euc d → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hf : HRS.MP.RdGen.RgW (mnc_W d) 1 c f) (x : Euc d) (j : Fin d) :
    (movForce d s f x) j = ∫ z, rieszKernelGrad d s z j * movtr_R f x z :=
  dc1a_force_eq hd hs0 hsd hc hf x j

lemma mnc_movtr_R_add (f g : Euc d → ℝ) (x z : Euc d) :
    movtr_R (fun y => f y + g y) x z = movtr_R f x z + movtr_R g x z := by
  unfold movtr_R
  split_ifs <;> ring

lemma mnc_movtr_R_smul (a : ℝ) (f : Euc d → ℝ) (x z : Euc d) :
    movtr_R (fun y => a * f y) x z = a * movtr_R f x z := by
  unfold movtr_R
  split_ifs <;> ring

lemma mnc_force_add (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {f g : Euc d → ℝ} {cf cg : ℝ}
    (hcf : 0 ≤ cf) (hcg : 0 ≤ cg) (hf : HRS.MP.RdGen.RgW (mnc_W d) 1 cf f)
    (hg : HRS.MP.RdGen.RgW (mnc_W d) 1 cg g) (x : Euc d) :
    movForce d s (fun y => f y + g y) x = movForce d s f x + movForce d s g x := by
  ext j
  have hfg := hf.add hg
  rw [mnc_force_coord hd hs0 hsd (add_nonneg hcf hcg) hfg x j]
  simp only [PiLp.add_apply]
  rw [mnc_force_coord hd hs0 hsd hcf hf x j, mnc_force_coord hd hs0 hsd hcg hg x j,
    ← integral_add (dc1a_kernel_int hd hs0 hsd hcf hf (HRS.MP.RdGen.rgKerComp_ok hs0 j) x)
      (dc1a_kernel_int hd hs0 hsd hcg hg (HRS.MP.RdGen.rgKerComp_ok hs0 j) x)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [mnc_movtr_R_add]
  ring

lemma mnc_force_smul (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {f : Euc d → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hf : HRS.MP.RdGen.RgW (mnc_W d) 1 c f) (a : ℝ) (x : Euc d) :
    movForce d s (fun y => a * f y) x = a • movForce d s f x := by
  ext j
  have hf' := hf.const_mul a
  rw [mnc_force_coord hd hs0 hsd (mul_nonneg (abs_nonneg a) hc) hf' x j]
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [mnc_force_coord hd hs0 hsd hc hf x j, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [mnc_movtr_R_smul]
  ring

/-- The sup-bound constant of the force (linear in the `RgW` constant). -/
def mnc_Bf (d : ℕ) (s : ℝ) : ℝ :=
  movtr_sigma s * (HRS.MP.RdGen.rgNear d s + 4 ^ (s + 1) * HRS.MP.RdGen.rgW d)

lemma mnc_force_bound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {f : Euc d → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hf : HRS.MP.RdGen.RgW (mnc_W d) 1 c f) (x : Euc d) (j : Fin d) :
    |(movForce d s f x) j| ≤ mnc_Bf d s * c := by
  have h := dc1a_force_bound hd hs0 hsd hc hf x j
  rw [Real.norm_eq_abs] at h
  refine h.trans (le_of_eq ?_)
  unfold mnc_Bf
  ring

lemma mnc_force_meas (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {f : Euc d → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hf : HRS.MP.RdGen.RgW (mnc_W d) 1 c f) (j : Fin d) :
    Measurable (fun x => (movForce d s f x) j) :=
  dc1b_conv_meas hd hs0 hsd hc hf j

lemma mnc_rgW_integrable (hd : 1 ≤ d) {f : Euc d → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hf : HRS.MP.RdGen.RgW (mnc_W d) 1 c f) : Integrable f :=
  dc1b_rgW_int hd hc hf


lemma mnc_norm_le_coord (v : Euc d) (B : ℝ) (hB : 0 ≤ B) (h : ∀ j, |v j| ≤ B) : ‖v‖ ≤ d * B := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  calc ∑ j, ‖v j‖ ^ 2 ≤ ∑ j : Fin d, B ^ 2 := Finset.sum_le_sum fun j _ => by
        rw [Real.norm_eq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h j) 2
    _ = d * B ^ 2 := by simp
    _ ≤ (d * B) ^ 2 := by
        rcases Nat.eq_zero_or_pos d with h0 | h0
        · simp [h0]
        · have : (1 : ℝ) ≤ d := by exact_mod_cast h0
          nlinarith [sq_nonneg B]

lemma mnc_force_norm_bound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {f : Euc d → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hf : HRS.MP.RdGen.RgW (mnc_W d) 1 c f) (x : Euc d) :
    ‖movForce d s f x‖ ≤ d * (mnc_Bf d s * c) := by
  have hB : 0 ≤ mnc_Bf d s * c := by
    have := (abs_nonneg _).trans (mnc_force_bound hd hs0 hsd hc hf x ⟨0, by omega⟩)
    exact this
  exact mnc_norm_le_coord _ _ hB fun j => mnc_force_bound hd hs0 hsd hc hf x j

lemma mnc_grad_contDiff {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) : Continuous (gradient ψ) :=
  (HRS.MS.Gap.gap1_contDiff_gradient hψ 1).continuous

lemma mnc_grad_cs {ψ : Euc d → ℝ} (hc : HasCompactSupport ψ) : HasCompactSupport (gradient ψ) := by
  have h1 : HasCompactSupport (fderiv ℝ ψ) := hc.fderiv (𝕜 := ℝ)
  have : gradient ψ = (InnerProductSpace.toDual ℝ (Euc d)).symm ∘ fderiv ℝ ψ := by
    funext x; rfl
  rw [this]
  exact h1.comp_left (by simp)

lemma mnc_int_mul_gradforce (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) {h : Euc d → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hh : HRS.MP.RdGen.RgW (mnc_W d) 1 c h) {g : Euc d → ℝ} (hg : Continuous g) :
    Integrable (fun x => g x * inner ℝ (gradient ψ x) (movForce d s h x)) := by
  have hgr := mnc_grad_contDiff hψ
  have hgcs := mnc_grad_cs hψc
  have hmaj : Integrable (fun x => |g x| * ‖gradient ψ x‖ * (d * (mnc_Bf d s * c))) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((hg.abs).mul hgr.norm).mul continuous_const
    · exact HasCompactSupport.mul_right (f := fun x => |g x| * ‖gradient ψ x‖) (f' := fun _ => (d : ℝ) * (mnc_Bf d s * c))
        (HasCompactSupport.mul_left (f := fun x => |g x|) hgcs.norm)
  have hmeas : AEStronglyMeasurable (fun x => g x * inner ℝ (gradient ψ x) (movForce d s h x)) := by
    have e : (fun x => g x * inner ℝ (gradient ψ x) (movForce d s h x)) =
        fun x => g x * ∑ j, (gradient ψ x) j * (movForce d s h x) j := by
      funext x; rw [mnc_inner_eq_sum]
    rw [e]
    refine Measurable.aestronglyMeasurable (hg.measurable.mul (Finset.measurable_sum _ fun j _ => ?_))
    exact ((EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous.comp hgr).measurable.mul
      (mnc_force_meas hd hs0 hsd hc hh j)
  refine Integrable.mono' hmaj hmeas (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, Real.norm_eq_abs]
  have h1 : |inner ℝ (gradient ψ x) (movForce d s h x)| ≤ ‖gradient ψ x‖ * (d * (mnc_Bf d s * c)) :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (mnc_force_norm_bound hd hs0 hsd hc hh x) (norm_nonneg _))
  calc |g x| * |inner ℝ (gradient ψ x) (movForce d s h x)| ≤ |g x| * (‖gradient ψ x‖ * (d * (mnc_Bf d s * c))) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = _ := by ring

end Force


/-! ### The pointwise-in-`r` decomposition -/

section Decomp

variable {s β q : ℝ} {ρ : Euc d → ℝ}

lemma mnc_lap_cont {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) : Continuous (Laplacian.laplacian ψ) := by
  have h2 : Continuous (iteratedFDeriv ℝ 2 ψ) := hψ.continuous_iteratedFDeriv (m := 2) (by norm_num)
  have e : Laplacian.laplacian ψ = fun y => ∑ i : Fin d, iteratedFDeriv ℝ 2 ψ y
      ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] := funext fun y => mnb_lap_formula ψ y
  rw [e]
  refine continuous_finsetSum _ fun i _ => ?_
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euc d) ℝ
    ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)]).continuous.comp h2

lemma mnc_lap_cs {ψ : Euc d → ℝ} (hc : HasCompactSupport ψ) : HasCompactSupport (Laplacian.laplacian ψ) := by
  have e : Laplacian.laplacian ψ = fun y => ∑ i : Fin d, iteratedFDeriv ℝ 2 ψ y
      ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] := funext fun y => mnb_lap_formula ψ y
  rw [e]
  have h2 := hc.iteratedFDeriv (𝕜 := ℝ) 2
  have : ∀ i : Fin d, HasCompactSupport fun y => iteratedFDeriv ℝ 2 ψ y
      ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] := fun i =>
    h2.comp_left (g := fun L : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Euc d) ℝ =>
      L ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)]) (by simp)
  have hs : ∀ (t : Finset (Fin d)), HasCompactSupport fun y => ∑ i ∈ t, iteratedFDeriv ℝ 2 ψ y
      ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact (HasCompactSupport.zero : HasCompactSupport (0 : Euc d → ℝ))
    | insert a t ha ih =>
      simp only [Finset.sum_insert ha]
      exact (this a).add ih
  exact hs Finset.univ

lemma mnc_loggrad_cont (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ x, 0 < ρ x) :
    Continuous (fun x => gradient (fun y => Real.log (ρ y)) x) :=
  mnc_grad_contDiff (hρ.log fun x => (hpos x).ne')

/-- `A_ψ(h) = -∫ ρ ⟨∇ψ, ∇g*h⟩`. -/
def mnc_A (d : ℕ) (s : ℝ) (ρ ψ h : Euc d → ℝ) : ℝ :=
  -∫ x, ρ x * inner ℝ (gradient ψ x) (movForce d s h x)

/-- `Q_ψ(h,h') = -∫ h ⟨∇ψ, ∇g*h'⟩`. -/
def mnc_Q (d : ℕ) (s : ℝ) (ψ h h' : Euc d → ℝ) : ℝ :=
  -∫ x, h x * inner ℝ (gradient ψ x) (movForce d s h' x)


theorem mnc_decomp (H : Mov2dTh d s β q ρ) {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    {h : Euc d → ℝ} {ch : ℝ} (hch : 0 ≤ ch) (hhW : HRS.MP.RdGen.RgW (mnc_W d) 1 ch h)
    (hreg : RegSliceRd (fun y => ρ y + h y)) :
    Whole.pair (Whole.withDensityReal (fun y => ρ y + h y))
        (fun x => (quadraticGradientDyn d s q β).invβ * Laplacian.laplacian (fun z => φ z / Real.sqrt (ρ z)) x -
          inner ℝ (gradient (quadraticGradientDyn d s q β).V x) (gradient (fun z => φ z / Real.sqrt (ρ z)) x)) +
      interactionPairingW (quadraticGradientDyn d s q β) (fun z => φ z / Real.sqrt (ρ z))
        (Whole.withDensityReal (fun y => ρ y + h y)) (Whole.withDensityReal (fun y => ρ y + h y)) =
    (∫ x, (h x / Real.sqrt (ρ x)) * (β⁻¹ * (Laplacian.laplacian φ x - mov2a_V ρ x * φ x))) +
      mnc_A d s ρ (fun z => φ z / Real.sqrt (ρ z)) h + mnc_Q d s (fun z => φ z / Real.sqrt (ρ z)) h h := by
  have hd1 : 1 ≤ d := by have := H.hd; omega
  have hρsm := mnc_rho_smooth H
  have hpos := (mnb_rhoData H).pos
  set ψ : Euc d → ℝ := fun z => φ z / Real.sqrt (ρ z) with hψdef
  have hψs : ContDiff ℝ ∞ ψ := mnc_psi_smooth hρsm hpos hφ
  have hψc : HasCompactSupport ψ := mnc_psi_cs hφc
  have hψM : MemCb 2 ψ := mnc_memCb_of_cs hψs hψc 2
  obtain ⟨Kρ, hKρ, hρW⟩ := mnc_rgW_rho H
  have hρtW : HRS.MP.RdGen.RgW (mnc_W d) 1 (Kρ + ch) (fun y => ρ y + h y) := hρW.add hhW
  set ρt : Euc d → ℝ := fun y => ρ y + h y with hρt
  have hP : Whole.IsProbDensity ρt := hreg.1
  have hρtc : Continuous ρt := (dc1a_rgW_facts (add_nonneg hKρ hch) hρtW).2.1
  have hρc : Continuous ρ := hρsm.continuous
  have hhc : Continuous h := (dc1a_rgW_facts hch hhW).2.1
  set D := quadraticGradientDyn d s q β with hD
  have hM : ∀ y : Euc d, Torus.matVec D.M y = -y := fun y => by simp [hD, quadraticGradientDyn, Torus.matVec]
  have hI := (self_pairing_rd_proof D hd1 H.hs0 H.hsd hreg hψM).1
  have hpair : ∀ f : Euc d → ℝ, Whole.pair (Whole.withDensityReal ρt) f = ∫ x, ρt x * f x := fun f =>
    dc1a_integral_withDensity hP.measurable hP.nonneg f
  have hforce : ∀ x, movForce d s ρt x = movForce d s ρ x + movForce d s h x :=
    fun x => mnc_force_add hd1 H.hs0 H.hsd hKρ hch hρW hhW x
  have hEuler : ∀ x, β⁻¹ • gradient (fun y => Real.log (ρ y)) x + q • x + movForce d s ρ x = 0 :=
    fun x => HRS.MS.Mov0.mv0_thermal_force H.hd H.hs0 H.hsd H.hq H.hβ H.hρ x
  -- the continuous compactly supported factor E
  set E : Euc d → ℝ := fun x => Laplacian.laplacian ψ x +
    inner ℝ (gradient (fun y => Real.log (ρ y)) x) (gradient ψ x) with hEdef
  have hgr := mnc_grad_contDiff hψs
  have hgcs := mnc_grad_cs hψc
  have hEc : Continuous E := (mnc_lap_cont hψs).add ((mnc_loggrad_cont hρsm hpos).inner hgr)
  have hEcs : HasCompactSupport E := by
    refine HasCompactSupport.add (mnc_lap_cs hψc) ?_
    refine hgcs.mono' ?_
    intro x hx
    refine subset_tsupport _ ?_
    intro h0
    apply hx
    simp [h0]
  -- pointwise algebra
  have hrhoE : ∀ x, ρ x * E x = Real.sqrt (ρ x) * (Laplacian.laplacian φ x - mov2a_V ρ x * φ x) := by
    intro x
    rw [← mnc_div_rho_grad hρsm hpos hψs x, mnc_div_flux hρsm hpos hφ x]
  have hEW : ∀ x, E x = (Laplacian.laplacian φ x - mov2a_V ρ x * φ x) / Real.sqrt (ρ x) := by
    intro x
    have hs : 0 < Real.sqrt (ρ x) := Real.sqrt_pos.2 (hpos x)
    have hss : Real.sqrt (ρ x) * Real.sqrt (ρ x) = ρ x := Real.mul_self_sqrt (hpos x).le
    have h1 := hrhoE x
    have h2 : Real.sqrt (ρ x) * Real.sqrt (ρ x) * E x = Real.sqrt (ρ x) * (Laplacian.laplacian φ x - mov2a_V ρ x * φ x) := by
      rw [hss]; exact h1
    rw [eq_div_iff hs.ne']
    refine mul_left_cancel₀ hs.ne' ?_
    linear_combination h2
  have hfx : ∀ x, gradient D.V x = q • x := fun x => movtr_gradient_confinement q x
  have hpt : ∀ x, ρt x * (D.invβ * Laplacian.laplacian ψ x - inner ℝ (gradient D.V x) (gradient ψ x)) +
      -(ρt x * inner ℝ (gradient ψ x) (movForce d s ρt x)) =
      β⁻¹ * (ρ x * E x) + β⁻¹ * (h x * E x) +
        (-(ρ x * inner ℝ (gradient ψ x) (movForce d s h x))) + (-(h x * inner ℝ (gradient ψ x) (movForce d s h x))) := by
    intro x
    have he := congrArg (fun v => inner ℝ (gradient ψ x) v) (hEuler x)
    simp only [inner_add_right, inner_smul_right, inner_zero_right] at he
    rw [hforce x, inner_add_right, hfx x, inner_smul_left, real_inner_comm (gradient ψ x) x]
    simp only [hD, quadraticGradientDyn, hEdef, hρt]
    have hc : inner ℝ (gradient (fun y => Real.log (ρ y)) x) (gradient ψ x) =
        inner ℝ (gradient ψ x) (gradient (fun y => Real.log (ρ y)) x) := real_inner_comm _ _
    simp only [hc, conj_trivial] at *
    linear_combination (-(ρ x + h x)) * he
  -- the drift factor f
  set f : Euc d → ℝ := fun x => D.invβ * Laplacian.laplacian ψ x - inner ℝ (gradient D.V x) (gradient ψ x) with hf
  have hfc : Continuous f := by
    refine ((continuous_const.mul (mnc_lap_cont hψs))).sub ?_
    have : (fun x => inner ℝ (gradient D.V x) (gradient ψ x)) = fun x => inner ℝ (q • x) (gradient ψ x) :=
      funext fun x => by rw [hfx x]
    rw [this]
    exact (continuous_id.const_smul q).inner hgr
  have hfcs : HasCompactSupport f := by
    refine HasCompactSupport.sub ((mnc_lap_cs hψc).mul_left (f := fun _ => D.invβ)) ?_
    refine hgcs.mono' ?_
    intro x hx
    refine subset_tsupport _ ?_
    intro h0
    apply hx
    simp [h0]
  have hI1 : Integrable (fun x => ρt x * f x) :=
    (hρtc.mul hfc).integrable_of_hasCompactSupport (hfcs.mul_left (f := ρt))
  have hI2 : Integrable (fun x => -(ρt x * inner ℝ (gradient ψ x) (movForce d s ρt x))) :=
    (mnc_int_mul_gradforce hd1 H.hs0 H.hsd hψs hψc (add_nonneg hKρ hch) hρtW hρtc).neg
  have hI' : interactionPairingW D ψ (Whole.withDensityReal ρt) (Whole.withDensityReal ρt) =
      ∫ x, -(ρt x * inner ℝ (gradient ψ x) (movForce d s ρt x)) := by
    rw [hI]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have : convGradConvW (rieszKernelGrad d D.s) ρt x = movForce d s ρt x := rfl
    simp only [this, hM, inner_neg_right, mul_neg]
  -- integrability of the four pieces
  have hG1 : Integrable (fun x => ρ x * E x) :=
    (hρc.mul hEc).integrable_of_hasCompactSupport (hEcs.mul_left (f := ρ))
  have hG2 : Integrable (fun x => h x * E x) :=
    (hhc.mul hEc).integrable_of_hasCompactSupport (hEcs.mul_left (f := h))
  have hG3 : Integrable (fun x => -(ρ x * inner ℝ (gradient ψ x) (movForce d s h x))) :=
    (mnc_int_mul_gradforce hd1 H.hs0 H.hsd hψs hψc hch hhW hρc).neg
  have hG4 : Integrable (fun x => -(h x * inner ℝ (gradient ψ x) (movForce d s h x))) :=
    (mnc_int_mul_gradforce hd1 H.hs0 H.hsd hψs hψc hch hhW hhc).neg
  -- the divergence integral vanishes
  have hdiv0 : ∫ x, ρ x * E x = 0 := by
    have hY : ContDiff ℝ 1 (fun y => ρ y • gradient ψ y) :=
      (hρsm.of_le (by exact_mod_cast le_top)).smul (HRS.MS.Gap.gap1_contDiff_gradient hψs 1)
    have hYc : HasCompactSupport (fun y => ρ y • gradient ψ y) := hgcs.smul_left (f := ρ)
    have := mnc_ibp_div hY (contDiff_const (c := (1 : ℝ))) (Or.inr hYc)
    simp only [mul_one] at this
    have e : ∀ x, movDiv (fun y => ρ y • gradient ψ y) x = ρ x * E x := fun x =>
      mnc_div_rho_grad hρsm hpos hψs x
    simp_rw [e] at this
    rw [this]
    simp
  calc _ = (∫ x, ρt x * f x) + ∫ x, -(ρt x * inner ℝ (gradient ψ x) (movForce d s ρt x)) := by
        rw [hpair, hI']
    _ = ∫ x, (ρt x * f x + -(ρt x * inner ℝ (gradient ψ x) (movForce d s ρt x))) :=
        (integral_add hI1 hI2).symm
    _ = ∫ x, (β⁻¹ * (ρ x * E x) + β⁻¹ * (h x * E x) +
        (-(ρ x * inner ℝ (gradient ψ x) (movForce d s h x))) +
          (-(h x * inner ℝ (gradient ψ x) (movForce d s h x)))) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => hpt x)
    _ = β⁻¹ * (∫ x, ρ x * E x) + β⁻¹ * (∫ x, h x * E x) +
        (∫ x, -(ρ x * inner ℝ (gradient ψ x) (movForce d s h x))) +
          (∫ x, -(h x * inner ℝ (gradient ψ x) (movForce d s h x))) := by
        have i12 : Integrable (fun x => β⁻¹ * (ρ x * E x) + β⁻¹ * (h x * E x)) :=
          (hG1.const_mul _).add (hG2.const_mul _)
        have i123 : Integrable (fun x => β⁻¹ * (ρ x * E x) + β⁻¹ * (h x * E x) +
            (-(ρ x * inner ℝ (gradient ψ x) (movForce d s h x)))) := i12.add hG3
        have e1 : ∫ x, (β⁻¹ * (ρ x * E x) + β⁻¹ * (h x * E x) +
            (-(ρ x * inner ℝ (gradient ψ x) (movForce d s h x))) +
            (-(h x * inner ℝ (gradient ψ x) (movForce d s h x)))) =
            (∫ x, (β⁻¹ * (ρ x * E x) + β⁻¹ * (h x * E x) +
            (-(ρ x * inner ℝ (gradient ψ x) (movForce d s h x))))) +
            ∫ x, -(h x * inner ℝ (gradient ψ x) (movForce d s h x)) := integral_add i123 hG4
        have e2 : ∫ x, (β⁻¹ * (ρ x * E x) + β⁻¹ * (h x * E x) +
            (-(ρ x * inner ℝ (gradient ψ x) (movForce d s h x)))) =
            (∫ x, (β⁻¹ * (ρ x * E x) + β⁻¹ * (h x * E x))) +
            ∫ x, -(ρ x * inner ℝ (gradient ψ x) (movForce d s h x)) := integral_add i12 hG3
        have e3 : ∫ x, (β⁻¹ * (ρ x * E x) + β⁻¹ * (h x * E x)) =
            (∫ x, β⁻¹ * (ρ x * E x)) + ∫ x, β⁻¹ * (h x * E x) := integral_add (hG1.const_mul _) (hG2.const_mul _)
        rw [e1, e2, e3, integral_const_mul, integral_const_mul]
    _ = _ := by
        rw [hdiv0, integral_neg, integral_neg]
        unfold mnc_A mnc_Q
        have e2 : β⁻¹ * ∫ x, h x * E x =
            ∫ x, (h x / Real.sqrt (ρ x)) * (β⁻¹ * (Laplacian.laplacian φ x - mov2a_V ρ x * φ x)) := by
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          dsimp only
          rw [hEW x]; ring
        rw [e2]
        ring

end Decomp

end HRS.MS.Mov63
