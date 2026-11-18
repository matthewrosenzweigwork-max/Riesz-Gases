import HRS.Energy.StaticLimitAux

/-!
# The response equation for spectral kernels (work package STAT-4.21)

For a probability measure `μ` on the torus and the spectral kernel `g = specKernel a`
(`a ≥ 0` summable), the response equation `h + β K_μ h = P_μ ψ`, `μ(h) = 0`
(`HRS.IsResponse`) has an a.e.-unique solution for every `β ≥ 0` and `ψ ∈ L²(μ)`; the solution
is obtained from the Lax-Milgram theorem for the coercive form
`B(f,k) = ⟨f,k⟩ + β ∑_i ⟨Z_i,f⟩⟨Z_i,k⟩` with the centred features `Z_i = Ψ_i - μ(Ψ_i)`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace HRS.StaticLimitAux

open HRS Torus

variable {d : ℕ} {a : Lattice d → ℝ}

section Resp

variable (μ : Measure (Torus d)) [IsProbabilityMeasure μ]

/-- Class in `L²(μ)` of a continuous function on the (compact) torus. -/
def cl (f : Torus d → ℝ) (hf : Continuous f) : Lp ℝ 2 μ :=
  (hf.memLp_of_hasCompactSupport (μ := μ) (p := 2) (HasCompactSupport.of_compactSpace _)).toLp f

theorem cl_ae {f : Torus d → ℝ} (hf : Continuous f) : cl μ f hf =ᵐ[μ] f :=
  MemLp.coeFn_toLp _

theorem norm_cl_le {f : Torus d → ℝ} (hf : Continuous f) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x, |f x| ≤ C) : ‖cl μ f hf‖ ≤ C := by
  have h := Lp.norm_le_of_ae_bound (f := cl μ f hf) hC (by
    filter_upwards [cl_ae μ hf] with x hx
    rw [hx, Real.norm_eq_abs]; exact hb x)
  have h1 : measureUnivNNReal μ = 1 := by simp [measureUnivNNReal]
  rw [h1] at h
  simpa using h

theorem inner_cl_left {f : Torus d → ℝ} (hf : Continuous f) (k : Lp ℝ 2 μ) :
    ⟪cl μ f hf, k⟫ = ∫ x, f x * k x ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [cl_ae μ hf] with x hx
  rw [hx]; simp [mul_comm]

theorem inner_cl_cl {f g : Torus d → ℝ} (hf : Continuous f) (hg : Continuous g) :
    ⟪cl μ f hf, cl μ g hg⟫ = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [cl_ae μ hf, cl_ae μ hg] with x hx hy
  rw [hx, hy]; simp [mul_comm]

theorem inner_cl_right {f : Torus d → ℝ} (hf : Continuous f) (k : Lp ℝ 2 μ) :
    ⟪k, cl μ f hf⟫ = ∫ x, f x * k x ∂μ := by
  rw [real_inner_comm, inner_cl_left]

/-- The mean of a feature. -/
def mfeat (a : Lattice d → ℝ) (i : Idx d) : ℝ := ∫ x, feat a i x ∂μ

/-- The centred features `Z_i = Ψ_i - μ(Ψ_i)`. -/
def Zfeat (a : Lattice d → ℝ) (i : Idx d) (x : Torus d) : ℝ := feat a i x - mfeat μ a i

theorem continuous_Zfeat (i : Idx d) : Continuous (Zfeat μ a i) :=
  (continuous_feat i).sub continuous_const

theorem abs_mfeat_le (i : Idx d) : |mfeat μ a i| ≤ fbound a i := by
  unfold mfeat
  refine abs_integral_le_integral_abs.trans ?_
  calc ∫ x, |feat a i x| ∂μ ≤ ∫ _x, fbound a i ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
          (integrable_const _) (Filter.Eventually.of_forall fun x => abs_feat_le i x)
    _ = fbound a i := by simp

theorem abs_Zfeat_le (i : Idx d) (x : Torus d) : |Zfeat μ a i x| ≤ 2 * fbound a i := by
  unfold Zfeat
  calc |feat a i x - mfeat μ a i| ≤ |feat a i x| + |mfeat μ a i| := abs_sub _ _
    _ ≤ 2 * fbound a i := by linarith [abs_feat_le (a := a) i x, abs_mfeat_le μ (a := a) i]

/-- The class of the centred feature `Z_i` in `L²(μ)`. -/
def ZL (a : Lattice d → ℝ) (i : Idx d) : Lp ℝ 2 μ := cl μ (Zfeat μ a i) (continuous_Zfeat μ i)

theorem norm_ZL_le (i : Idx d) : ‖ZL μ a i‖ ≤ 2 * fbound a i :=
  norm_cl_le μ _ (mul_nonneg zero_le_two (fbound_nonneg i)) (abs_Zfeat_le μ i)

section Resp2

variable (ha0 : ∀ k, 0 ≤ a k) (has : Summable a)

include ha0 has in
theorem memℓp_Tco (f : Lp ℝ 2 μ) : Memℓp (fun i : Idx d => ⟪ZL μ a i, f⟫) 2 := by
  rw [Torus.memℓp_two_iff]
  refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_)
    ((summable_fbound_sq ha0 has).mul_left (4 * ‖f‖ ^ 2))
  have h1 : |⟪ZL μ a i, f⟫| ≤ ‖ZL μ a i‖ * ‖f‖ := abs_real_inner_le_norm _ _
  have h2 : ‖ZL μ a i‖ * ‖f‖ ≤ (2 * fbound a i) * ‖f‖ :=
    mul_le_mul_of_nonneg_right (norm_ZL_le μ i) (norm_nonneg _)
  have h3 : |⟪ZL μ a i, f⟫| ≤ (2 * fbound a i) * ‖f‖ := h1.trans h2
  calc ⟪ZL μ a i, f⟫ ^ 2 = |⟪ZL μ a i, f⟫| ^ 2 := (sq_abs _).symm
    _ ≤ ((2 * fbound a i) * ‖f‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
    _ = 4 * ‖f‖ ^ 2 * (fbound a i * fbound a i) := by ring

include ha0 has in
/-- The moment map `f ↦ (⟨Z_i, f⟩)_i ∈ ℓ²`. -/
def Tco : Lp ℝ 2 μ →L[ℝ] lp (fun _ : Idx d => ℝ) 2 :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun i => ⟪ZL μ a i, f⟫, memℓp_Tco μ ha0 has f⟩
      map_add' := fun f g => by
        apply Subtype.ext; funext i; simp [inner_add_right]; rfl
      map_smul' := fun c f => by
        apply Subtype.ext; funext i; simp [inner_smul_right] }
    (2 * Real.sqrt (∑' i : Idx d, fbound a i * fbound a i))
    (fun f => by
      show ‖(⟨fun i => ⟪ZL μ a i, f⟫, memℓp_Tco μ ha0 has f⟩ : lp (fun _ : Idx d => ℝ) 2)‖ ≤ _
      set S : ℝ := ∑' i : Idx d, fbound a i * fbound a i with hS
      have hS0 : 0 ≤ S := tsum_nonneg fun i => mul_self_nonneg _
      obtain ⟨hsum, hnorm⟩ := Torus.lp_two_sq
        (⟨fun i => ⟪ZL μ a i, f⟫, memℓp_Tco μ ha0 has f⟩ : lp (fun _ : Idx d => ℝ) 2)
      have hsq : ‖(⟨fun i => ⟪ZL μ a i, f⟫, memℓp_Tco μ ha0 has f⟩ : lp (fun _ : Idx d => ℝ) 2)‖ ^ 2 ≤
          (2 * Real.sqrt S * ‖f‖) ^ 2 := by
        rw [hnorm]
        have : (2 * Real.sqrt S * ‖f‖) ^ 2 = ∑' i : Idx d, 4 * ‖f‖ ^ 2 * (fbound a i * fbound a i) := by
          rw [tsum_mul_left, ← hS]
          have := Real.sq_sqrt hS0
          calc (2 * Real.sqrt S * ‖f‖) ^ 2 = 4 * ‖f‖ ^ 2 * (Real.sqrt S) ^ 2 := by ring
            _ = _ := by rw [this]
        rw [this]
        refine Summable.tsum_le_tsum (fun i => ?_) hsum ((summable_fbound_sq ha0 has).mul_left _)
        have h1 : |⟪ZL μ a i, f⟫| ≤ ‖ZL μ a i‖ * ‖f‖ := abs_real_inner_le_norm _ _
        have h2 : ‖ZL μ a i‖ * ‖f‖ ≤ (2 * fbound a i) * ‖f‖ :=
          mul_le_mul_of_nonneg_right (norm_ZL_le μ i) (norm_nonneg _)
        have h3 : |⟪ZL μ a i, f⟫| ≤ (2 * fbound a i) * ‖f‖ := h1.trans h2
        show ⟪ZL μ a i, f⟫ ^ 2 ≤ _
        calc ⟪ZL μ a i, f⟫ ^ 2 = |⟪ZL μ a i, f⟫| ^ 2 := (sq_abs _).symm
          _ ≤ ((2 * fbound a i) * ‖f‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
          _ = 4 * ‖f‖ ^ 2 * (fbound a i * fbound a i) := by ring
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq)

include ha0 has in
/-- The coercive bilinear form `B(f,k) = ⟨f,k⟩ + β ∑_i ⟨Z_i,f⟩⟨Z_i,k⟩`. -/
def Bform (β : ℝ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ →L[ℝ] ℝ :=
  innerSL ℝ + β • (innerSL ℝ : lp (fun _ : Idx d => ℝ) 2 →L[ℝ] lp (fun _ : Idx d => ℝ) 2 →L[ℝ] ℝ).bilinearComp
    (Tco μ ha0 has) (Tco μ ha0 has)

include ha0 has in
theorem Bform_apply (β : ℝ) (f k : Lp ℝ 2 μ) :
    Bform μ ha0 has β f k = ⟪f, k⟫ + β * ⟪Tco μ ha0 has f, Tco μ ha0 has k⟫ := by
  simp [Bform]
  rfl

include ha0 has in
theorem Bform_coercive {β : ℝ} (hβ : 0 ≤ β) : IsCoercive (Bform μ ha0 has β) := by
  refine ⟨1, one_pos, fun u => ?_⟩
  rw [Bform_apply μ ha0 has, one_mul, ← real_inner_self_eq_norm_mul_norm]
  have : 0 ≤ β * ⟪Tco μ ha0 has u, Tco μ ha0 has u⟫ :=
    mul_nonneg hβ (real_inner_self_nonneg)
  linarith

include ha0 has in
theorem exists_B_solution {β : ℝ} (hβ : 0 ≤ β) (z : Lp ℝ 2 μ) :
    ∃ h : Lp ℝ 2 μ, ∀ k, ⟪z, k⟫ = Bform μ ha0 has β h k := by
  refine ⟨(Bform_coercive μ ha0 has hβ).continuousLinearEquivOfBilin.symm z, fun k => ?_⟩
  have := (Bform_coercive μ ha0 has hβ).continuousLinearEquivOfBilin_apply
    ((Bform_coercive μ ha0 has hβ).continuousLinearEquivOfBilin.symm z) k
  simpa using this

theorem Tco_apply (f : Lp ℝ 2 μ) (i : Idx d) : (Tco μ ha0 has f) i = ⟪ZL μ a i, f⟫ := rfl

include ha0 has in
theorem inner_Tco (f k : Lp ℝ 2 μ) :
    ⟪Tco μ ha0 has f, Tco μ ha0 has k⟫ = ∑' i : Idx d, ⟪ZL μ a i, f⟫ * ⟪ZL μ a i, k⟫ := by
  rw [lp.inner_eq_tsum]
  refine tsum_congr fun i => ?_
  rw [Tco_apply, Tco_apply]
  simp [mul_comm]

include ha0 has in
/-- Function-level form of the Lax-Milgram solution: existence of the response. -/
theorem isResponse_of_solution {β : ℝ} (hβ : 0 ≤ β) {ψ : Torus d → ℝ} (hψ : Continuous ψ)
    (h : Lp ℝ 2 μ) (hh : ∀ k, ⟪cl μ (fun x => ψ x - pair μ ψ) (hψ.sub continuous_const), k⟫ =
      Bform μ ha0 has β h k) :
    IsResponse (specKernel a) μ β ψ ⇑h := by
  set z : Lp ℝ 2 μ := cl μ (fun x => ψ x - pair μ ψ) (hψ.sub continuous_const) with hz
  have hhint : Integrable (⇑h) μ := (Lp.memLp h).integrable one_le_two
  set one : Lp ℝ 2 μ := cl μ (fun _ => (1 : ℝ)) continuous_const with hone
  have hT1 : Tco μ ha0 has one = 0 := by
    apply Subtype.ext; funext i
    show ⟪ZL μ a i, one⟫ = 0
    rw [hone, ZL, inner_cl_cl]
    simp only [Zfeat, mul_one]
    rw [integral_sub (integrable_const _ |>.mono' (continuous_feat i).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_feat_le i x)) (integrable_const _)]
    simp [mfeat]
  have hψint : Integrable ψ μ :=
    hψ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hz1 : ⟪z, one⟫ = 0 := by
    rw [hz, hone, inner_cl_cl]
    simp only [mul_one]
    rw [integral_sub hψint (integrable_const _)]
    simp [pair]
  have hmean : ∫ x, h x ∂μ = 0 := by
    have h1 := hh one
    rw [Bform_apply μ ha0 has, hT1, inner_zero_right, mul_zero, add_zero, hz1] at h1
    rw [hone, inner_cl_right] at h1
    simpa using h1.symm
  set c : Idx d → ℝ := fun i => ∫ y, feat a i y * h y ∂μ with hc
  have hc_bd : ∀ i, |c i| ≤ (∫ x, ‖h x‖ ∂μ) * fbound a i := fun i => by
    have := abs_integral_le_integral_abs.trans (norm_integral_feat_le (a := a) μ hhint i)
    rw [mul_comm]; exact this
  set G : Torus d → ℝ := fun x => ∫ y, specKernel a (x - y) * h y ∂μ with hG
  have hGsum : ∀ x, HasSum (fun i => feat a i x * c i) (G x) :=
    fun x => hasSum_kernel_integral ha0 has μ hhint x
  have hGc : Continuous G := continuous_kernel_integral ha0 has μ hhint
  have hmsum : HasSum (fun i => c i * mfeat μ a i) (pair μ G) := by
    have := hasSum_integral_tsum_mul ha0 has μ (e := feat a) (fun i => continuous_feat i)
      (B := 1) (fun i y => by simpa using abs_feat_le i y) (c := c) (C := ∫ x, ‖h x‖ ∂μ) hc_bd
      (k := fun _ => (1 : ℝ)) (integrable_const 1)
    simp only [mul_one] at this
    have e : ∀ x, ∑' i : Idx d, c i * feat a i x = G x := fun x => by
      rw [← (hGsum x).tsum_eq]; exact tsum_congr fun i => mul_comm _ _
    simp_rw [e] at this
    exact this
  have hw : ∀ x, HasSum (fun i => c i * Zfeat μ a i x) (G x - pair μ G) := by
    intro x
    have := (hGsum x).sub hmsum
    convert this using 1
    funext i; simp only [Zfeat]; ring
  have hZc : ∀ i, ⟪ZL μ a i, h⟫ = c i := by
    intro i
    rw [ZL, inner_cl_left]
    simp only [Zfeat, sub_mul]
    rw [integral_sub (integrable_feat_mul μ hhint i) ((hhint.const_mul _))]
    rw [integral_const_mul, hmean]; simp [hc]
  have hwk : ∀ k : Lp ℝ 2 μ, ∫ x, (G x - pair μ G) * k x ∂μ = ⟪Tco μ ha0 has h, Tco μ ha0 has k⟫ := by
    intro k
    have hk : Integrable (⇑k) μ := (Lp.memLp k).integrable one_le_two
    have := hasSum_integral_tsum_mul ha0 has μ (e := Zfeat μ a) (continuous_Zfeat μ)
      (B := 2) (fun i x => abs_Zfeat_le μ i x) hc_bd hk
    simp_rw [fun x => (hw x).tsum_eq] at this
    rw [inner_Tco μ ha0 has, ← this.tsum_eq]
    refine tsum_congr fun i => ?_
    rw [hZc, ZL, inner_cl_left]
  set wL : Lp ℝ 2 μ := cl μ (fun x => G x - pair μ G) (hGc.sub continuous_const) with hwL
  set kk : Lp ℝ 2 μ := h + β • wL - z with hkk
  have hkk0 : ∀ k, ⟪kk, k⟫ = 0 := by
    intro k
    rw [hkk, inner_sub_left, inner_add_left, real_inner_smul_left, hwL, inner_cl_left, hwk k, hh k,
      Bform_apply μ ha0 has]
    ring
  have hk0 : kk = 0 := inner_self_eq_zero.mp (hkk0 kk)
  refine ⟨Lp.memLp h, hmean, ?_⟩
  have hz_ae : (⇑z : Torus d → ℝ) =ᵐ[μ] fun x => ψ x - pair μ ψ := cl_ae μ _
  have hw_ae : (⇑wL : Torus d → ℝ) =ᵐ[μ] fun x => G x - pair μ G := cl_ae μ _
  have hkk_ae : (⇑kk : Torus d → ℝ) =ᵐ[μ] fun x => h x + β * wL x - z x := by
    rw [hkk]
    filter_upwards [Lp.coeFn_sub (h + β • wL) z, Lp.coeFn_add h (β • wL), Lp.coeFn_smul β wL]
      with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, Pi.add_apply, h3, Pi.smul_apply, smul_eq_mul]
  have hzero : (⇑kk : Torus d → ℝ) =ᵐ[μ] 0 := by rw [hk0]; exact Lp.coeFn_zero _ _ _
  filter_upwards [hkk_ae, hzero, hz_ae, hw_ae] with x h1 h2 h3 h4
  have h5 : h x + β * wL x - z x = 0 := by rw [← h1]; simpa using h2
  rw [h3, h4] at h5
  have : Kop (specKernel a) μ (⇑h) x = G x - pair μ G := rfl
  rw [this]
  simp only [projMean]
  linarith

include ha0 has in
theorem exists_isResponse {β : ℝ} (hβ : 0 ≤ β) {ψ : Torus d → ℝ} (hψ : Continuous ψ) :
    ∃ h : Torus d → ℝ, IsResponse (specKernel a) μ β ψ h := by
  obtain ⟨h, hh⟩ := exists_B_solution μ ha0 has hβ
    (cl μ (fun x => ψ x - pair μ ψ) (hψ.sub continuous_const))
  exact ⟨⇑h, isResponse_of_solution μ ha0 has hβ hψ h hh⟩

end Resp2

/-- The convolution `x ↦ ∫ g(x-y) f(y) dμ(y)`. -/
def Gfun (a : Lattice d → ℝ) (f : Torus d → ℝ) (x : Torus d) : ℝ :=
  ∫ y, specKernel a (x - y) * f y ∂μ

theorem Gfun_sub (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) {f₁ f₂ : Torus d → ℝ}
    (h₁ : Integrable f₁ μ) (h₂ : Integrable f₂ μ) (x : Torus d) :
    Gfun μ a (f₁ - f₂) x = Gfun μ a f₁ x - Gfun μ a f₂ x := by
  unfold Gfun
  have i1 : Integrable (fun y => specKernel a (x - y) * f₁ y) μ :=
    h₁.bdd_mul (f := fun y => specKernel a (x - y)) (c := ∑' k, a k)
      ((continuous_specKernel ha0 has).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact abs_specKernel_le ha0 has _)
  have i2 : Integrable (fun y => specKernel a (x - y) * f₂ y) μ :=
    h₂.bdd_mul (f := fun y => specKernel a (x - y)) (c := ∑' k, a k)
      ((continuous_specKernel ha0 has).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact abs_specKernel_le ha0 has _)
  rw [← integral_sub i1 i2]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp [mul_sub])

theorem Kop_eq (g : Torus d → ℝ) (f : Torus d → ℝ) (x : Torus d) :
    Kop g μ f x = (∫ y, g (x - y) * f y ∂μ) - pair μ (fun x => ∫ y, g (x - y) * f y ∂μ) := rfl

/-- Uniqueness of the response (nonnegativity of `K_μ`). -/
theorem isResponse_unique (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) {β : ℝ} (hβ : 0 ≤ β)
    {ψ h₁ h₂ : Torus d → ℝ} (r₁ : IsResponse (specKernel a) μ β ψ h₁)
    (r₂ : IsResponse (specKernel a) μ β ψ h₂) : h₁ =ᵐ[μ] h₂ := by
  obtain ⟨m₁, p₁, e₁⟩ := r₁
  obtain ⟨m₂, p₂, e₂⟩ := r₂
  have i₁ : Integrable h₁ μ := m₁.integrable one_le_two
  have i₂ : Integrable h₂ μ := m₂.integrable one_le_two
  set δ : Torus d → ℝ := h₁ - h₂ with hδ
  have mδ : MemLp δ 2 μ := m₁.sub m₂
  have iδ : Integrable δ μ := i₁.sub i₂
  have pδ : ∫ x, δ x ∂μ = 0 := by
    have : ∫ x, δ x ∂μ = pair μ h₁ - pair μ h₂ := integral_sub i₁ i₂
    rw [this, p₁, p₂]; ring
  set Gδ : Torus d → ℝ := Gfun μ a δ with hGδ
  have cGδ : Continuous Gδ := continuous_kernel_integral ha0 has μ iδ
  have cG₁ : Continuous (Gfun μ a h₁) := continuous_kernel_integral ha0 has μ i₁
  have cG₂ : Continuous (Gfun μ a h₂) := continuous_kernel_integral ha0 has μ i₂
  have iG₁ : Integrable (Gfun μ a h₁) μ := cG₁.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have iG₂ : Integrable (Gfun μ a h₂) μ := cG₂.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have pG : pair μ Gδ = pair μ (Gfun μ a h₁) - pair μ (Gfun μ a h₂) := by
    have : Gδ = fun x => Gfun μ a h₁ x - Gfun μ a h₂ x := by
      funext x; exact Gfun_sub μ ha0 has i₁ i₂ x
    rw [this]; exact integral_sub iG₁ iG₂
  -- the equation for δ
  have eδ : ∀ᵐ x ∂μ, δ x + β * (Gδ x - pair μ Gδ) = 0 := by
    filter_upwards [e₁, e₂] with x x₁ x₂
    have k₁ : Kop (specKernel a) μ h₁ x = Gfun μ a h₁ x - pair μ (Gfun μ a h₁) := rfl
    have k₂ : Kop (specKernel a) μ h₂ x = Gfun μ a h₂ x - pair μ (Gfun μ a h₂) := rfl
    rw [k₁] at x₁; rw [k₂] at x₂
    have := Gfun_sub μ ha0 has i₁ i₂ x
    rw [pG]
    simp only [hδ, Pi.sub_apply] at *
    rw [hGδ, this]
    linarith
  -- integrate against δ
  have hint1 : Integrable (fun x => δ x * δ x) μ := by
    simpa [sq] using mδ.integrable_sq
  have hint2 : Integrable (fun x => δ x * Gδ x) μ :=
    iδ.mul_bdd (c := (isCompact_univ.exists_bound_of_continuousOn cGδ.continuousOn).choose)
      cGδ.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
        have := (isCompact_univ.exists_bound_of_continuousOn cGδ.continuousOn).choose_spec x (Set.mem_univ x)
        simpa using this)
  have hpos := posdef_nonneg ha0 has μ iδ
  have hsplit : ∫ x, δ x * δ x ∂μ + β * ∫ x, δ x * Gδ x ∂μ = 0 := by
    have h0 : ∫ x, δ x * (δ x + β * (Gδ x - pair μ Gδ)) ∂μ = 0 := by
      rw [integral_eq_zero_of_ae]
      filter_upwards [eδ] with x hx
      simp [hx]
    have : ∫ x, δ x * (δ x + β * (Gδ x - pair μ Gδ)) ∂μ =
        ∫ x, δ x * δ x ∂μ + β * ∫ x, δ x * Gδ x ∂μ - β * pair μ Gδ * ∫ x, δ x ∂μ := by
      have e : ∀ x, δ x * (δ x + β * (Gδ x - pair μ Gδ)) =
          δ x * δ x + β * (δ x * Gδ x) - β * pair μ Gδ * δ x := fun x => by ring
      simp_rw [e]
      have A1 : Integrable (fun x => δ x * δ x + β * (δ x * Gδ x)) μ := hint1.add (hint2.const_mul β)
      have A2 : Integrable (fun x => β * pair μ Gδ * δ x) μ := iδ.const_mul _
      have A3 : Integrable (fun x => β * (δ x * Gδ x)) μ := hint2.const_mul β
      rw [integral_sub A1 A2, integral_add hint1 A3, integral_const_mul, integral_const_mul]
    rw [this, pδ] at h0
    linarith
  have hGδeq : ∫ x, δ x * Gδ x ∂μ = ∫ x, δ x * ∫ y, specKernel a (x - y) * δ y ∂μ ∂μ := rfl
  have hsq0 : ∫ x, δ x * δ x ∂μ = 0 := by
    have h3 : 0 ≤ ∫ x, δ x * δ x ∂μ := integral_nonneg fun x => mul_self_nonneg _
    have h4 : 0 ≤ β * ∫ x, δ x * Gδ x ∂μ := mul_nonneg hβ (by rw [hGδeq]; exact hpos)
    linarith
  have := (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg (δ x)) hint1).mp hsq0
  filter_upwards [this] with x hx
  have : δ x * δ x = 0 := hx
  have : δ x = 0 := mul_self_eq_zero.mp this
  simpa [hδ, sub_eq_zero] using this


end Resp

end HRS.StaticLimitAux
