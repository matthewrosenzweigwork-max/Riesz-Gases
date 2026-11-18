import HRS.MS.SobMulAux1

/-!
# MS-SOBMUL, part 2: Fourier transform of `T · f` for a Schwartz function `T` and `f ∈ L²`
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform Convolution

namespace HRS.MS.SobMul
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

/-! ### Schwartz–Schwartz product formula -/

theorem sobmul_fourier_fourier (g : SchwartzMap (Euc d) ℂ) (x : Euc d) :
    (𝓕 (𝓕 g : SchwartzMap (Euc d) ℂ) : SchwartzMap (Euc d) ℂ) (-x) = g x := by
  have h0 : 𝓕⁻ (𝓕 g : SchwartzMap (Euc d) ℂ) = g := by simp
  have h := congrArg (fun F : SchwartzMap (Euc d) ℂ => F x) h0
  try simp only at h
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg] at h
  rw [← h]; rfl

theorem sobmul_fourier_mul (T φ : SchwartzMap (Euc d) ℂ) (ξ : Euc d) :
    𝓕 (fun x => T x * φ x) ξ =
      ∫ η, (𝓕 T : SchwartzMap (Euc d) ℂ) (ξ - η) * (𝓕 φ : SchwartzMap (Euc d) ℂ) η := by
  set a : SchwartzMap (Euc d) ℂ := 𝓕 T
  set b : SchwartzMap (Euc d) ℂ := 𝓕 φ
  have hC := SchwartzMap.convolution_apply (ContinuousLinearMap.mul ℂ ℂ) a b ξ
  have hP : SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) a b =
      𝓕⁻ (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕 a) (𝓕 b)) := by
    simp [SchwartzMap.convolution]
  rw [hP, SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_comp_neg] at hC
  have e1 : (fun x : Euc d => ((SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕 a) (𝓕 b) :
      SchwartzMap (Euc d) ℂ) (-x))) = fun x => T x * φ x := by
    ext x
    rw [SchwartzMap.pairing_apply_apply]
    simp only [ContinuousLinearMap.mul_apply']
    rw [sobmul_fourier_fourier T x, sobmul_fourier_fourier φ x]
  have e2 : ∀ x, (⇑(SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕 a) (𝓕 b))) (-x) =
      T x * φ x := fun x => congrFun e1 x
  simp only [e2] at hC
  rw [hC]
  simp only [convolution, ContinuousLinearMap.mul_apply']
  rw [← integral_sub_left_eq_self (fun t => a t * b (ξ - t)) volume ξ]
  simp

/-! ### Multiplication by a Schwartz function on `L²` -/

/-- the Schwartz function `T` as an element of `L^∞` -/
def sobmul_TLp (T : SchwartzMap (Euc d) ℂ) : Lp (α := Euc d) ℂ ⊤ :=
  (T.memLp ⊤ volume).toLp T

theorem sobmul_TLp_coe (T : SchwartzMap (Euc d) ℂ) :
    (sobmul_TLp T : Euc d → ℂ) =ᵐ[volume] ⇑T := MemLp.coeFn_toLp _

/-- multiplication by `T` on `L²` -/
def sobmul_mulLp (T : SchwartzMap (Euc d) ℂ) : Lp (α := Euc d) ℂ 2 →+ Lp (α := Euc d) ℂ 2 where
  toFun F := (sobmul_TLp T : Lp (α := Euc d) ℂ ⊤) • F
  map_zero' := Lp.smul_zero _ _ _
  map_add' F G := Lp.add_smul _ F G

theorem sobmul_mulLp_coe (T : SchwartzMap (Euc d) ℂ) (F : Lp (α := Euc d) ℂ 2) :
    (sobmul_mulLp T F : Euc d → ℂ) =ᵐ[volume] fun x => T x * F x := by
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (sobmul_TLp T) F, sobmul_TLp_coe T] with x h1 h2
  simp only [sobmul_mulLp, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [h1]; simp [h2]

theorem continuous_sobmul_mulLp (T : SchwartzMap (Euc d) ℂ) : Continuous (sobmul_mulLp T) := by
  apply AddMonoidHomClass.continuous_of_bound (sobmul_mulLp T)
    ‖(sobmul_TLp T : Lp (α := Euc d) ℂ ⊤)‖
  intro F
  exact Lp.norm_smul_le (r := 2) (sobmul_TLp T) F

/-! ### The convolution functional -/

/-- `h ↦ ∫ a(ξ - η) h(η) dη` on `L²` -/
def sobmul_conv (a : Euc d → ℂ) (ξ : Euc d) (h : Lp (α := Euc d) ℂ 2) : ℂ :=
  ∫ η, a (ξ - η) * h η

theorem sobmul_continuous_conv (a : SchwartzMap (Euc d) ℂ) (ξ : Euc d) :
    Continuous (sobmul_conv a ξ) := by
  have hk : MemLp (fun η : Euc d => starRingEnd ℂ (a (ξ - η))) 2 volume := by
    have h1 : MemLp (fun η : Euc d => a (ξ - η)) 2 volume :=
      (a.memLp 2 volume).comp_measurePreserving (Measure.measurePreserving_sub_left volume ξ)
    exact h1.star
  set kL : Lp (α := Euc d) ℂ 2 := hk.toLp _ with hkL
  have key : sobmul_conv a ξ = fun h => inner ℂ kL h := by
    ext h
    rw [MeasureTheory.L2.inner_def]
    unfold sobmul_conv
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hk] with η hη
    rw [hη]
    simp [mul_comm]
  rw [key]
  exact continuous_const.inner continuous_id

/-! ### The main identity on `L²` -/

theorem sobmul_FT_toLp (φ : SchwartzMap (Euc d) ℂ) :
    FT d (φ.toLp 2) = (𝓕 φ : SchwartzMap (Euc d) ℂ).toLp 2 :=
  SchwartzMap.toLp_fourier_eq _

theorem sobmul_fourier_mulLp (T : SchwartzMap (Euc d) ℂ) (f : Lp (α := Euc d) ℂ 2) :
    (FT d (sobmul_mulLp T f) : Euc d → ℂ) =ᵐ[volume]
      fun ξ => sobmul_conv (𝓕 T : SchwartzMap (Euc d) ℂ) ξ (FT d f) := by
  -- Schwartz case
  have hS : ∀ φ : SchwartzMap (Euc d) ℂ, (FT d (sobmul_mulLp T (φ.toLp 2)) : Euc d → ℂ) =ᵐ[volume]
      fun ξ => sobmul_conv (𝓕 T : SchwartzMap (Euc d) ℂ) ξ (FT d (φ.toLp 2)) := by
    intro φ
    set Q : SchwartzMap (Euc d) ℂ := SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) T φ with hQ
    have h1 : sobmul_mulLp T (φ.toLp 2) = Q.toLp 2 := by
      apply Lp.ext
      filter_upwards [sobmul_mulLp_coe T (φ.toLp 2), SchwartzMap.coeFn_toLp φ 2 volume,
        SchwartzMap.coeFn_toLp Q 2 volume] with x a b c
      rw [a, c, b, hQ, SchwartzMap.pairing_apply_apply]; simp
    have e1 := sobmul_FT_toLp Q
    have e2 := sobmul_FT_toLp φ
    rw [h1, e1]
    filter_upwards [SchwartzMap.coeFn_toLp (𝓕 Q : SchwartzMap (Euc d) ℂ) 2 volume] with ξ a
    rw [a]
    have b1 : (𝓕 Q : SchwartzMap (Euc d) ℂ) ξ = 𝓕 (fun x => T x * φ x) ξ := by
      rw [SchwartzMap.fourier_coe]
      rfl
    rw [b1, sobmul_fourier_mul]
    unfold sobmul_conv
    apply integral_congr_ae
    filter_upwards [SchwartzMap.coeFn_toLp (𝓕 φ : SchwartzMap (Euc d) ℂ) 2 volume] with η c
    rw [e2, c]
  -- density
  have hd := SchwartzMap.denseRange_toLpCLM (E := Euc d) (F := ℂ) (p := 2)
    ENNReal.ofNat_ne_top (μ := volume)
  have hf : f ∈ closure (Set.range (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure (Euc d)))) := by
    rw [hd.closure_range]; trivial
  obtain ⟨x, hx, hxl⟩ := mem_closure_iff_seq_limit.1 hf
  choose φ hφ using hx
  have hxφ : ∀ n, x n = (φ n).toLp 2 := fun n => by rw [← hφ n]; simp
  have hF : Tendsto (fun n => FT d (sobmul_mulLp T (x n))) atTop
      (𝓝 (FT d (sobmul_mulLp T f))) :=
    ((FT d).continuous.comp (continuous_sobmul_mulLp T)).tendsto f |>.comp hxl
  obtain ⟨ns, hmono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hF).exists_seq_tendsto_ae
  have hall : ∀ᵐ ξ ∂(volume : Measure (Euc d)), ∀ n,
      (FT d (sobmul_mulLp T (x n)) : Euc d → ℂ) ξ =
        sobmul_conv (𝓕 T : SchwartzMap (Euc d) ℂ) ξ (FT d (x n)) := by
    rw [ae_all_iff]
    intro n
    rw [hxφ n]
    exact hS (φ n)
  filter_upwards [hns, hall] with ξ h1 h2
  have h3 : Tendsto (fun i => sobmul_conv (𝓕 T : SchwartzMap (Euc d) ℂ) ξ (FT d (x (ns i))))
      atTop (𝓝 (sobmul_conv (𝓕 T : SchwartzMap (Euc d) ℂ) ξ (FT d f))) := by
    have hc := (sobmul_continuous_conv (𝓕 T : SchwartzMap (Euc d) ℂ) ξ).comp (FT d).continuous
    exact (hc.tendsto f).comp (hxl.comp hmono.tendsto_atTop)
  exact tendsto_nhds_unique h1 (h3.congr fun i => (h2 _).symm)

end HRS.MS.SobMul
