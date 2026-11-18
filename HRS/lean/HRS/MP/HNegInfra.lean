import HRS.Whole.SobolevDual
import HRS.PDE.ToolboxRd.Fourier

/-!
# Infrastructure for `HNeg d Γ = H^{-Γ}(ℝ^d)`: Hilbert structure, duality, norming family, Parseval

Packet MPHNEG.  Helper names carry the prefix `mhn_`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff ComplexConjugate FourierTransform

namespace HRS.MP.HNegInfra
open HRS.Whole

variable {d : ℕ}

/-! ### Stage 1: instances -/

/-- The real inner product on `HNeg d Γ`, restricted from `Lp ℂ 2 (sobolevMeasure d Γ)`; its
normed-space structure is the existing one (definitionally) and its norm is the existing norm. -/
instance mhn_innerProductSpace (Γ : ℝ) : InnerProductSpace ℝ (HNeg d Γ) :=
  inferInstanceAs (InnerProductSpace ℝ (HNegSubmodule d Γ))

theorem mhn_toNormedSpace (Γ : ℝ) : (mhn_innerProductSpace (d := d) Γ).toNormedSpace =
    (inferInstance : NormedSpace ℝ (HNeg d Γ)) := rfl

theorem mhn_sfinite (Γ : ℝ) : SFinite (sobolevMeasure d Γ) := by
  unfold sobolevMeasure; infer_instance

instance mhn_secondCountable (Γ : ℝ) : SecondCountableTopology (HNeg d Γ) := by
  haveI : SFinite (sobolevMeasure d Γ) := mhn_sfinite Γ
  haveI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have : SecondCountableTopology (Lp ℂ 2 (sobolevMeasure d Γ)) := inferInstance
  have : SecondCountableTopology (HNegSubmodule d Γ) := inferInstance
  exact inferInstanceAs (SecondCountableTopology (HNegSubmodule d Γ))

instance mhn_separable (Γ : ℝ) : TopologicalSpace.SeparableSpace (HNeg d Γ) :=
  inferInstance

theorem mhn_lp_inner_re {α : Type*} [MeasurableSpace α] (μ : Measure α) (f g : Lp ℂ 2 μ) :
    inner ℝ f g = (inner ℂ f g).re := by
  rw [L2.inner_def, L2.inner_def]
  have h := integral_re (𝕜 := ℂ) (L2.integrable_inner (𝕜 := ℂ) f g)
  simp only [RCLike.re_to_complex] at h
  rw [← h]
  rfl

/-- The real inner product of `HNeg` is the real part of the complex `L²(μ)` inner product. -/
theorem mhn_inner_eq {Γ : ℝ} (F G : HNeg d Γ) :
    inner ℝ F G = (inner ℂ ((F : HNegSubmodule d Γ).1 : Lp ℂ 2 (sobolevMeasure d Γ))
      ((G : HNegSubmodule d Γ).1 : Lp ℂ 2 (sobolevMeasure d Γ))).re := by
  show inner ℝ ((F : HNegSubmodule d Γ).1 : Lp ℂ 2 (sobolevMeasure d Γ))
      ((G : HNegSubmodule d Γ).1 : Lp ℂ 2 (sobolevMeasure d Γ)) = _
  exact mhn_lp_inner_re _ _ _

theorem mhn_norm_eq {Γ : ℝ} (F : HNeg d Γ) :
    ‖F‖ = ‖((F : HNegSubmodule d Γ).1 : Lp ℂ 2 (sobolevMeasure d Γ))‖ := rfl

/-! ### Weights and the Fourier-side measure -/

section Weights

variable {Γ : ℝ}

theorem mhn_base_pos (ξ : Euc d) : 0 < 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by positivity

/-- `ρ(ξ) = (1+4π²|ξ|²)^{-Γ}`, the density of `sobolevMeasure` with respect to Lebesgue measure. -/
def mhn_rho (Γ : ℝ) (ξ : Euc d) : ℝ := (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-Γ)

theorem mhn_rho_pos (ξ : Euc d) : 0 < mhn_rho Γ ξ :=
  Real.rpow_pos_of_pos (mhn_base_pos ξ) _

theorem mhn_rho_mul (ξ : Euc d) :
    mhn_rho Γ ξ * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ Γ = 1 := by
  unfold mhn_rho
  rw [← Real.rpow_add (mhn_base_pos ξ)]
  simp

theorem mhn_continuous_rho : Continuous (mhn_rho Γ : Euc d → ℝ) := by
  unfold mhn_rho
  exact Continuous.rpow_const (by fun_prop) (fun x => Or.inl (mhn_base_pos x).ne')

theorem mhn_continuous_rho_inv : Continuous (fun ξ : Euc d => (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ Γ) :=
  Continuous.rpow_const (by fun_prop) (fun x => Or.inl (mhn_base_pos x).ne')

theorem mhn_measurable_weight : Measurable (sobolevWeight d Γ) := by
  unfold sobolevWeight
  fun_prop

theorem mhn_toReal_weight (ξ : Euc d) : (sobolevWeight d Γ ξ).toReal = mhn_rho Γ ξ :=
  ENNReal.toReal_ofReal (mhn_rho_pos ξ).le

theorem mhn_ac : sobolevMeasure d Γ ≪ (volume : Measure (Euc d)) :=
  withDensity_absolutelyContinuous _ _

theorem mhn_ae_mu_iff (p : Euc d → Prop) :
    (∀ᵐ ξ ∂(sobolevMeasure d Γ), p ξ) ↔ ∀ᵐ ξ : Euc d, p ξ := by
  unfold sobolevMeasure
  rw [ae_withDensity_iff mhn_measurable_weight]
  constructor
  · intro h
    filter_upwards [h] with ξ hξ
    exact hξ (by simp [sobolevWeight, mhn_rho_pos (Γ := Γ) ξ |>.ne'] ; exact mhn_rho_pos ξ)
  · intro h
    filter_upwards [h] with ξ hξ _ using hξ

theorem mhn_integral_mu {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Euc d → E) :
    ∫ ξ, g ξ ∂(sobolevMeasure d Γ) = ∫ ξ, mhn_rho Γ ξ • g ξ := by
  unfold sobolevMeasure
  rw [integral_withDensity_eq_integral_toReal_smul mhn_measurable_weight
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)) g]
  congr 1; ext ξ
  rw [mhn_toReal_weight]

theorem mhn_integrable_mu {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Euc d → E) :
    Integrable g (sobolevMeasure d Γ) ↔ Integrable (fun ξ => mhn_rho Γ ξ • g ξ) volume := by
  unfold sobolevMeasure
  rw [integrable_withDensity_iff_integrable_smul' mhn_measurable_weight
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  refine integrable_congr (ae_of_all _ (fun ξ => ?_))
  show (sobolevWeight d Γ ξ).toReal • g ξ = _
  rw [mhn_toReal_weight]

end Weights

/-! ### Stage 2(a): the Riesz representative of `pairing φ` and the bound -/

section Psi

variable {Γ : ℝ}
open HRS.PDE.ToolboxRd

/-- The weighted Fourier transform `(1+4π²|ξ|²)^Γ φ̂` of a function `φ`. -/
def mhn_psi (Γ : ℝ) (φ : Euc d → ℝ) (ξ : Euc d) : ℂ :=
  (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ Γ : ℝ) : ℂ) * fourierL2 φ ξ

theorem mhn_memLp_psi {φ : Euc d → ℝ} (h : HRS.PDE.ToolboxRd.MemSobolev Γ φ) :
    MemLp (mhn_psi Γ φ) 2 (sobolevMeasure d Γ) := by
  have hm : AEStronglyMeasurable (mhn_psi Γ φ) (sobolevMeasure d Γ) := by
    refine AEStronglyMeasurable.mono_ac mhn_ac ?_
    exact (Complex.continuous_ofReal.comp mhn_continuous_rho_inv).aestronglyMeasurable.mul
      (HRS.PDE.ToolboxRd.FourierAux.aestronglyMeasurable_fourierL2 h.1)
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  rw [mhn_integrable_mu]
  refine h.2.congr (ae_of_all _ (fun ξ => ?_))
  have hρ := mhn_rho_mul (Γ := Γ) ξ
  simp only [mhn_psi, norm_mul, Complex.norm_real, Real.norm_eq_abs, smul_eq_mul]
  have hpos : 0 < (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ Γ := Real.rpow_pos_of_pos (mhn_base_pos ξ) _
  rw [abs_of_pos hpos]
  calc (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ Γ * ‖fourierL2 φ ξ‖ ^ 2
      = (mhn_rho Γ ξ * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ Γ) *
        ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ Γ * ‖fourierL2 φ ξ‖ ^ 2) := by rw [hρ, one_mul]
    _ = _ := by ring

/-- The element `(1+4π²|ξ|²)^Γ φ̂` of `L²(ℂ; sobolevMeasure)`. -/
def mhn_psiLp {φ : Euc d → ℝ} (h : HRS.PDE.ToolboxRd.MemSobolev Γ φ) : Lp ℂ 2 (sobolevMeasure d Γ) :=
  (mhn_memLp_psi h).toLp _

theorem mhn_psiLp_ae {φ : Euc d → ℝ} (h : HRS.PDE.ToolboxRd.MemSobolev Γ φ) :
    ∀ᵐ ξ : Euc d, (mhn_psiLp h : Euc d → ℂ) ξ = mhn_psi Γ φ ξ :=
  (mhn_ae_mu_iff _).1 (MemLp.coeFn_toLp _)

theorem mhn_inner_psiLp {φ : Euc d → ℝ} (h : HRS.PDE.ToolboxRd.MemSobolev Γ φ) (G : Lp ℂ 2 (sobolevMeasure d Γ)) :
    inner ℂ (mhn_psiLp h) G = ∫ ξ, conj (fourierL2 φ ξ) * (G : Euc d → ℂ) ξ := by
  rw [L2.inner_def, mhn_integral_mu]
  refine integral_congr_ae ?_
  filter_upwards [mhn_psiLp_ae h] with ξ hξ
  rw [hξ]
  have hρ := mhn_rho_mul (Γ := Γ) ξ
  simp only [mhn_psi, Complex.real_smul, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  have : ((mhn_rho Γ ξ : ℝ) : ℂ) * (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ Γ : ℝ) : ℂ) = 1 := by
    exact_mod_cast hρ
  linear_combination (conj (fourierL2 φ ξ) * (G : Euc d → ℂ) ξ) * this

theorem mhn_norm_psiLp {φ : Euc d → ℝ} (h : HRS.PDE.ToolboxRd.MemSobolev Γ φ) :
    ‖mhn_psiLp h‖ = HRS.Whole.sobolevNorm Γ φ := by
  have h1 : ‖mhn_psiLp h‖ ^ 2 = (inner ℂ (mhn_psiLp h) (mhn_psiLp h)).re :=
    norm_sq_eq_re_inner (𝕜 := ℂ) _
  rw [mhn_inner_psiLp] at h1
  have h2 : (∫ ξ, conj (fourierL2 φ ξ) * (mhn_psiLp h : Euc d → ℂ) ξ).re =
      HRS.PDE.ToolboxRd.sobolevNormSq Γ φ := by
    unfold HRS.PDE.ToolboxRd.sobolevNormSq
    have : (∫ ξ, conj (fourierL2 φ ξ) * (mhn_psiLp h : Euc d → ℂ) ξ) =
        ∫ ξ, (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ Γ * ‖fourierL2 φ ξ‖ ^ 2 : ℝ) : ℂ) := by
      refine integral_congr_ae ?_
      filter_upwards [mhn_psiLp_ae h] with ξ hξ
      rw [hξ]
      simp only [mhn_psi]
      have := Complex.mul_conj (fourierL2 φ ξ)
      rw [Complex.normSq_eq_norm_sq] at this
      push_cast at this ⊢
      linear_combination (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ Γ : ℝ) : ℂ) * this
    rw [this, integral_complex_ofReal, Complex.ofReal_re]
  show ‖mhn_psiLp h‖ = Real.sqrt _
  rw [← h2, ← h1, Real.sqrt_sq (norm_nonneg _)]

theorem mhn_pairing_eq {φ : Euc d → ℝ} (h : HRS.PDE.ToolboxRd.MemSobolev Γ φ) (F : HNeg d Γ) :
    HNeg.pairing φ F =
      (inner ℂ (mhn_psiLp h) ((F : HNegSubmodule d Γ).1 : Lp ℂ 2 (sobolevMeasure d Γ))).re := by
  rw [mhn_inner_psiLp]; rfl

/-- Stage 2(a): the duality bound `|⟨φ,F⟩| ≤ ‖F‖_{H^{-Γ}} ‖φ‖_{H^Γ}`. -/
theorem hneg_pairing_le {φ : Euc d → ℝ} (hφ : IsSobolevTest Γ φ) (F : HNeg d Γ) :
    |HNeg.pairing φ F| ≤ ‖F‖ * HRS.Whole.sobolevNorm Γ φ := by
  rw [mhn_pairing_eq hφ.2 F, ← mhn_norm_psiLp hφ.2, mul_comm, mhn_norm_eq]
  exact (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)

end Psi

/-! ### Membership of an `Lp` element in the real subspace -/

theorem mhn_mem_of_conj {Γ : ℝ} (G : Lp ℂ 2 (sobolevMeasure d Γ))
    (hG : ∀ᵐ ξ ∂(sobolevMeasure d Γ), (G : Euc d → ℂ) (-ξ) = conj ((G : Euc d → ℂ) ξ)) :
    G ∈ HNegSubmodule d Γ := by
  have h1 := Lp.coeFn_compMeasurePreserving G (sobolevMeasure_neg Γ)
  have h2 := ContinuousLinearMap.coeFn_compLpL
    ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap)
    (Lp.compMeasurePreserving (fun ξ : Euc d => -ξ) (sobolevMeasure_neg Γ) G)
  have h3 : (realStructure d Γ) G =
      ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.compLpL 2 (sobolevMeasure d Γ))
        (Lp.compMeasurePreserving (fun ξ : Euc d => -ξ) (sobolevMeasure_neg Γ) G) := rfl
  have h4 : realStructure d Γ G = G := by
    apply Lp.ext
    rw [h3]
    filter_upwards [h1, h2, hG] with ξ a b c
    simp only [Function.comp_apply] at a b
    rw [b, a, c]
    simp
  simp only [HNegSubmodule, LinearMap.mem_ker]
  simp [h4]

/-! ### Real test functions with compactly supported Fourier transform -/

section Tests

/-- Fourier-side data: smooth, compactly supported, with the reality condition `h(-ξ) = conj h(ξ)`.
They are exactly the Fourier transforms of real functions in this class. -/
def mhn_Hc (d : ℕ) : Submodule ℝ (Euc d → ℂ) where
  carrier := {h | ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧ ∀ ξ, h (-ξ) = conj (h ξ)}
  add_mem' := by
    rintro a b ⟨ha1, ha2, ha3⟩ ⟨hb1, hb2, hb3⟩
    exact ⟨ha1.add hb1, ha2.add hb2, fun ξ => by simp [ha3, hb3]⟩
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero, fun ξ => by simp⟩
  smul_mem' := by
    rintro c a ⟨ha1, ha2, ha3⟩
    refine ⟨contDiff_const.smul ha1, ha2.smul_left, fun ξ => ?_⟩
    simp [Complex.real_smul, ha3]

/-- `h ∈ mhn_Hc` as a Schwartz function. -/
def mhn_S (h : mhn_Hc d) : SchwartzMap (Euc d) ℂ := h.2.2.1.toSchwartzMap h.2.1

/-- The inverse Fourier transform of `h`, a Schwartz function. -/
def mhn_U (h : mhn_Hc d) : SchwartzMap (Euc d) ℂ := 𝓕⁻ (mhn_S h)

/-- The real test function with Fourier transform `h`. -/
def mhn_phi (h : mhn_Hc d) : Euc d → ℝ := fun x => (mhn_U h x).re

theorem mhn_U_apply (h : mhn_Hc d) (x : Euc d) :
    mhn_U h x = ∫ v : Euc d, Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I) • h.1 v := by
  have : (⇑(mhn_U h) : Euc d → ℂ) = 𝓕⁻ (⇑(mhn_S h) : Euc d → ℂ) :=
    SchwartzMap.fourierInv_coe (mhn_S h)
  rw [this, Real.fourierInv_eq']
  rfl

theorem mhn_U_conj (h : mhn_Hc d) (x : Euc d) : conj (mhn_U h x) = mhn_U h x := by
  rw [mhn_U_apply, ← integral_conj]
  rw [← integral_neg_eq_self]
  congr 1; ext v
  have hr := h.2.2.2 v
  simp only [smul_eq_mul, map_mul, inner_neg_left]
  rw [hr, Complex.conj_conj, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem mhn_phi_coe (h : mhn_Hc d) (x : Euc d) : ((mhn_phi h x : ℝ) : ℂ) = mhn_U h x :=
  Complex.conj_eq_iff_re.1 (mhn_U_conj h x)

theorem mhn_contDiff_phi (h : mhn_Hc d) : ContDiff ℝ ∞ (mhn_phi h) :=
  Complex.reCLM.contDiff.comp ((mhn_U h).smooth (⊤ : ℕ∞))

theorem mhn_memLp_phi (h : mhn_Hc d) : MemLp (mhn_phi h) 2 volume :=
  ((mhn_U h).memLp 2 volume).re

theorem mhn_fourierL2_phi (h : mhn_Hc d) :
    HRS.PDE.ToolboxRd.fourierL2 (mhn_phi h) =ᵐ[volume] (h : Euc d → ℂ) := by
  have hφ := mhn_memLp_phi h
  rw [HRS.PDE.ToolboxRd.FourierAux.fourierL2_eq hφ]
  have e1 : HRS.PDE.ToolboxRd.FourierAux.ofRealLp hφ = (mhn_U h).toLp 2 := by
    apply Lp.ext
    filter_upwards [HRS.PDE.ToolboxRd.FourierAux.ofRealLp_coe hφ, SchwartzMap.coeFn_toLp (mhn_U h) 2 volume]
      with x a b
    rw [a, b, mhn_phi_coe]
  rw [e1]
  have e2 : HRS.PDE.ToolboxRd.FourierAux.FT d ((mhn_U h).toLp 2) = (mhn_S h).toLp 2 := by
    have h1 := SchwartzMap.toLp_fourier_eq (mhn_U h)
    have h2 : (𝓕 (mhn_U h) : SchwartzMap (Euc d) ℂ) = mhn_S h := by
      unfold mhn_U
      exact FourierInvPair.fourier_fourierInv_eq _
    rw [h2] at h1
    exact h1
  rw [e2]
  filter_upwards [SchwartzMap.coeFn_toLp (mhn_S h) 2 volume] with x hx
  rw [hx]; rfl

theorem mhn_memSobolev_phi (Γ : ℝ) (h : mhn_Hc d) :
    HRS.PDE.ToolboxRd.MemSobolev Γ (mhn_phi h) := by
  refine ⟨mhn_memLp_phi h, ?_⟩
  have hcont : Continuous (h : Euc d → ℂ) := h.2.1.continuous
  have hc : HasCompactSupport
      (fun ξ : Euc d => (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ Γ * ‖(h : Euc d → ℂ) ξ‖ ^ 2) := by
    refine h.2.2.1.mono ?_
    intro ξ hξ
    simp only [Function.mem_support, ne_eq] at hξ ⊢
    intro h0
    apply hξ
    simp [h0]
  have hint : Integrable
      (fun ξ : Euc d => (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ Γ * ‖(h : Euc d → ℂ) ξ‖ ^ 2) volume :=
    Continuous.integrable_of_hasCompactSupport
      (mhn_continuous_rho_inv.mul (hcont.norm.pow 2)) hc
  refine hint.congr ?_
  filter_upwards [mhn_fourierL2_phi h] with ξ hξ
  rw [hξ]

theorem mhn_isSobolevTest_phi (Γ : ℝ) (h : mhn_Hc d) : IsSobolevTest Γ (mhn_phi h) :=
  ⟨mhn_contDiff_phi h, mhn_memSobolev_phi Γ h⟩

/-- The Riesz representative `(1+4π²|ξ|²)^Γ h` of the test `φ_h`, as an element of `L²(μ)`. -/
def mhn_repLp (Γ : ℝ) (h : mhn_Hc d) : Lp ℂ 2 (sobolevMeasure d Γ) :=
  mhn_psiLp (mhn_memSobolev_phi Γ h)

theorem mhn_repLp_ae (Γ : ℝ) (h : mhn_Hc d) :
    ∀ᵐ ξ : Euc d, (mhn_repLp Γ h : Euc d → ℂ) ξ =
      (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ Γ : ℝ) : ℂ) * (h : Euc d → ℂ) ξ := by
  filter_upwards [mhn_psiLp_ae (mhn_memSobolev_phi Γ h), mhn_fourierL2_phi h] with ξ a b
  unfold mhn_repLp
  rw [a]
  simp only [mhn_psi]
  rw [b]

theorem mhn_repLp_mem (Γ : ℝ) (h : mhn_Hc d) : mhn_repLp Γ h ∈ HNegSubmodule d Γ := by
  apply mhn_mem_of_conj
  rw [mhn_ae_mu_iff]
  have h1 := (Measure.measurePreserving_neg (volume : Measure (Euc d))).quasiMeasurePreserving.ae
    (mhn_repLp_ae Γ h)
  filter_upwards [mhn_repLp_ae Γ h, h1] with ξ a b
  rw [b, a]
  simp only [norm_neg, h.2.2.2 ξ, map_mul, Complex.conj_ofReal]

/-- The Riesz-representative map `h ↦ (1+4π²|ξ|²)^Γ h`, real-linear into `HNeg d Γ`. -/
def mhn_rep (Γ : ℝ) : mhn_Hc d →ₗ[ℝ] HNeg d Γ where
  toFun h := (⟨mhn_repLp Γ h, mhn_repLp_mem Γ h⟩ : HNegSubmodule d Γ)
  map_add' a b := by
    apply Subtype.ext
    apply Lp.ext
    show (mhn_repLp Γ (a + b) : Euc d → ℂ) =ᵐ[sobolevMeasure d Γ]
      ((mhn_repLp Γ a + mhn_repLp Γ b : Lp ℂ 2 (sobolevMeasure d Γ)) : Euc d → ℂ)
    rw [Filter.EventuallyEq, mhn_ae_mu_iff]
    filter_upwards [mhn_repLp_ae Γ (a + b), mhn_repLp_ae Γ a, mhn_repLp_ae Γ b,
      (mhn_ae_mu_iff _).1 (Lp.coeFn_add (mhn_repLp Γ a) (mhn_repLp Γ b))] with ξ h1 h2 h3 h4
    rw [h4, Pi.add_apply, h1, h2, h3]
    simp [mul_add]
  map_smul' c a := by
    apply Subtype.ext
    apply Lp.ext
    show (mhn_repLp Γ (c • a) : Euc d → ℂ) =ᵐ[sobolevMeasure d Γ]
      ((c • mhn_repLp Γ a : Lp ℂ 2 (sobolevMeasure d Γ)) : Euc d → ℂ)
    rw [Filter.EventuallyEq, mhn_ae_mu_iff]
    filter_upwards [mhn_repLp_ae Γ (c • a), mhn_repLp_ae Γ a,
      (mhn_ae_mu_iff _).1 (Lp.coeFn_smul c (mhn_repLp Γ a))] with ξ h1 h2 h4
    rw [h4, Pi.smul_apply, h1, h2]
    simp [Complex.real_smul]
    ring

theorem mhn_rep_val (Γ : ℝ) (h : mhn_Hc d) :
    (((mhn_rep Γ h : HNeg d Γ) : HNegSubmodule d Γ).1 : Lp ℂ 2 (sobolevMeasure d Γ)) =
      mhn_repLp Γ h := rfl

theorem mhn_pairing_phi (Γ : ℝ) (h : mhn_Hc d) (F : HNeg d Γ) :
    HNeg.pairing (mhn_phi h) F = inner ℝ (mhn_rep Γ h) F := by
  rw [mhn_pairing_eq (mhn_memSobolev_phi Γ h) F, mhn_inner_eq]
  rfl

theorem mhn_norm_rep (Γ : ℝ) (h : mhn_Hc d) :
    ‖mhn_rep Γ h‖ = HRS.Whole.sobolevNorm Γ (mhn_phi h) := by
  rw [mhn_norm_eq]
  exact mhn_norm_psiLp (mhn_memSobolev_phi Γ h)

end Tests

/-! ### Density of the representatives -/

section Density

variable {Γ : ℝ}

theorem mhn_ac' : (volume : Measure (Euc d)) ≪ sobolevMeasure d Γ :=
  Measure.ae_le_iff_absolutelyContinuous.1 (fun s hs => (mhn_ae_mu_iff (Γ := Γ) (· ∈ s)).1 hs)

theorem mhn_locInt (F : HNeg d Γ) : LocallyIntegrable F.fourier (volume : Measure (Euc d)) := by
  have hmeas : AEStronglyMeasurable F.fourier (volume : Measure (Euc d)) :=
    (Lp.aestronglyMeasurable _).mono_ac mhn_ac'
  have hint0 : Integrable (fun ξ => ‖F.fourier ξ‖ ^ 2) (sobolevMeasure d Γ) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).1 (Lp.memLp _)
  have hint : Integrable (fun ξ => mhn_rho Γ ξ * ‖F.fourier ξ‖ ^ 2) (volume : Measure (Euc d)) :=
    (mhn_integrable_mu _).1 hint0
  rw [locallyIntegrable_iff]
  intro K hK
  refine Integrable.mono' (g := fun ξ => (1 / 2) *
    (mhn_rho Γ ξ * ‖F.fourier ξ‖ ^ 2 + (mhn_rho Γ ξ)⁻¹)) ?_ hmeas.restrict ?_
  · refine Integrable.const_mul (Integrable.add hint.integrableOn ?_) _
    have : Continuous fun ξ : Euc d => (mhn_rho Γ ξ)⁻¹ :=
      mhn_continuous_rho.inv₀ (fun x => (mhn_rho_pos x).ne')
    exact this.continuousOn.integrableOn_compact hK
  · refine ae_of_all _ (fun ξ => ?_)
    have hr := mhn_rho_pos (Γ := Γ) ξ
    set x := ‖F.fourier ξ‖
    set r := mhn_rho Γ ξ
    have h1 : (1 / 2) * (r * x ^ 2 + r⁻¹) - x = (r * x - 1) ^ 2 / (2 * r) := by
      field_simp
      ring
    have h2 : 0 ≤ (r * x - 1) ^ 2 / (2 * r) := by positivity
    linarith

theorem mhn_inner_rep_eq (h : mhn_Hc d) (F : HNeg d Γ) :
    inner ℝ (mhn_rep Γ h) F = (∫ ξ, conj ((h : Euc d → ℂ) ξ) * F.fourier ξ).re := by
  rw [← mhn_pairing_phi]
  unfold HNeg.pairing
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [mhn_fourierL2_phi h] with ξ hξ
  rw [hξ]

theorem mhn_conj_integral (f : Euc d → ℂ) (hf : ∀ᵐ ξ : Euc d, f (-ξ) = conj (f ξ))
    (k : Euc d → ℂ) :
    conj (∫ ξ, k ξ * f ξ) = ∫ ξ, conj (k (-ξ)) * f ξ := by
  rw [← integral_conj, ← integral_neg_eq_self (fun ξ => conj (k ξ * f ξ)) volume]
  refine integral_congr_ae ?_
  filter_upwards [hf] with ξ hξ
  simp [hξ]

theorem mhn_real_cd (g : Euc d → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (σ : ℝ) :
    ContDiff ℝ ∞ (fun ξ : Euc d => 1 / 2 * (g ξ + σ * g (-ξ))) ∧
      HasCompactSupport (fun ξ : Euc d => 1 / 2 * (g ξ + σ * g (-ξ))) := by
  have hneg : HasCompactSupport (fun ξ : Euc d => g (-ξ)) :=
    hgc.comp_homeomorph (Homeomorph.neg (Euc d))
  refine ⟨contDiff_const.mul (hg.add (contDiff_const.mul (hg.comp contDiff_neg))), ?_⟩
  have h1 : HasCompactSupport (fun ξ : Euc d => g ξ + σ * g (-ξ)) :=
    hgc.add (hneg.mul_left)
  exact h1.mul_left

theorem mhn_integral_test_zero (F : HNeg d Γ)
    (hF : ∀ h : mhn_Hc d, inner ℝ (mhn_rep Γ h) F = 0)
    (g : Euc d → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∫ ξ, g ξ • F.fourier ξ = 0 := by
  set f : Euc d → ℂ := F.fourier with hf
  have hreal : ∀ᵐ ξ : Euc d, f (-ξ) = conj (f ξ) :=
    (mhn_ae_mu_iff _).1 (HNeg.fourier_conj F)
  have hloc : LocallyIntegrable f (volume : Measure (Euc d)) := mhn_locInt F
  obtain ⟨ge1, ge2⟩ := mhn_real_cd g hg hgc 1
  obtain ⟨go1, go2⟩ := mhn_real_cd g hg hgc (-1)
  set ge : Euc d → ℝ := fun ξ => 1 / 2 * (g ξ + 1 * g (-ξ)) with hge
  set go : Euc d → ℝ := fun ξ => 1 / 2 * (g ξ + (-1) * g (-ξ)) with hgo
  have hge_even : ∀ ξ, ge (-ξ) = ge ξ := by
    intro ξ; simp only [hge, neg_neg]; ring
  have hgo_odd : ∀ ξ, go (-ξ) = - go ξ := by
    intro ξ; simp only [hgo, neg_neg]; ring
  have hsum : ∀ ξ, g ξ = ge ξ + go ξ := by
    intro ξ; simp only [hge, hgo]; ring
  -- the two admissible test data
  let h1 : mhn_Hc d := ⟨fun ξ => ((ge ξ : ℝ) : ℂ), by
    refine ⟨Complex.ofRealCLM.contDiff.comp ge1, ?_, fun ξ => ?_⟩
    · exact ge2.comp_left Complex.ofReal_zero
    · simp [hge_even]⟩
  let h2 : mhn_Hc d := ⟨fun ξ => Complex.I * ((go ξ : ℝ) : ℂ), by
    refine ⟨contDiff_const.mul (Complex.ofRealCLM.contDiff.comp go1), ?_, fun ξ => ?_⟩
    · exact (go2.comp_left Complex.ofReal_zero).mul_left
    · simp [hgo_odd]⟩
  have e1 := hF h1
  have e2 := hF h2
  rw [mhn_inner_rep_eq] at e1 e2
  set A : ℂ := ∫ ξ, ((ge ξ : ℝ) : ℂ) * f ξ with hA
  set B : ℂ := ∫ ξ, ((go ξ : ℝ) : ℂ) * f ξ with hB
  have hA1 : A.re = 0 := by
    rw [← e1]
    congr 1
    refine integral_congr_ae (ae_of_all _ (fun ξ => ?_))
    simp [h1, hf]
  have hB1 : B.im = 0 := by
    have : (∫ ξ, conj ((h2 : Euc d → ℂ) ξ) * f ξ) = -Complex.I * B := by
      rw [hB, ← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ (fun ξ => ?_))
      simp [h2]
      ring
    rw [this] at e2
    simpa using e2
  have hA2 : conj A = A := by
    rw [hA, mhn_conj_integral f hreal]
    refine integral_congr_ae (ae_of_all _ (fun ξ => ?_))
    simp [hge_even]
  have hB2 : conj B = -B := by
    rw [hB, mhn_conj_integral f hreal, ← integral_neg]
    refine integral_congr_ae (ae_of_all _ (fun ξ => ?_))
    simp [hgo_odd]
  have hA3 : A = 0 := by
    apply Complex.ext
    · simpa using hA1
    · have := congrArg Complex.im hA2
      simp at this
      change A.im = 0
      linarith
  have hB3 : B = 0 := by
    apply Complex.ext
    · have := congrArg Complex.re hB2
      simp at this
      change B.re = 0
      linarith
    · simpa using hB1
  have hint1 : Integrable (fun ξ => ((ge ξ : ℝ) : ℂ) * f ξ) volume := by
    have := hloc.integrable_smul_left_of_hasCompactSupport
      (Complex.ofRealCLM.contDiff.comp ge1).continuous (ge2.comp_left Complex.ofReal_zero)
    simpa using this
  have hint2 : Integrable (fun ξ => ((go ξ : ℝ) : ℂ) * f ξ) volume := by
    have := hloc.integrable_smul_left_of_hasCompactSupport
      (Complex.ofRealCLM.contDiff.comp go1).continuous (go2.comp_left Complex.ofReal_zero)
    simpa using this
  have : (∫ ξ, g ξ • f ξ) = A + B := by
    rw [hA, hB, ← integral_add hint1 hint2]
    refine integral_congr_ae (ae_of_all _ (fun ξ => ?_))
    show g ξ • f ξ = ((ge ξ : ℝ) : ℂ) * f ξ + ((go ξ : ℝ) : ℂ) * f ξ
    rw [hsum ξ, Complex.real_smul]
    push_cast
    ring
  rw [this, hA3, hB3, add_zero]

theorem mhn_eq_zero_of_orth (F : HNeg d Γ)
    (hF : ∀ h : mhn_Hc d, inner ℝ (mhn_rep Γ h) F = 0) : F = 0 := by
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := (volume : Measure (Euc d)))
    (mhn_locInt F) (fun g hg hgc => mhn_integral_test_zero F hF g hg hgc)
  apply Subtype.ext
  apply Lp.ext
  show ((F : HNegSubmodule d Γ).1 : Lp ℂ 2 (sobolevMeasure d Γ)) =ᵐ[sobolevMeasure d Γ]
    ((0 : Lp ℂ 2 (sobolevMeasure d Γ)) : Euc d → ℂ)
  filter_upwards [(mhn_ae_mu_iff (Γ := Γ) _).2 hae, Lp.coeFn_zero ℂ 2 (sobolevMeasure d Γ)]
    with ξ h1 h2
  rw [h2]
  exact h1

/-- Stage 2(b): smooth tests separate points of `HNeg d Γ` (hence are dense in `H^Γ`). -/
theorem hneg_eq_zero_of_pairing_zero (F : HNeg d Γ)
    (hF : ∀ φ : Euc d → ℝ, IsSobolevTest Γ φ → HNeg.pairing φ F = 0) : F = 0 :=
  mhn_eq_zero_of_orth F (fun h => by
    rw [← mhn_pairing_phi]; exact hF _ (mhn_isSobolevTest_phi Γ h))

end Density

/-! ### Abstract Hilbert-space lemmas -/

section Abstract

open InnerProductSpace (gramSchmidt gramSchmidtNormed span_gramSchmidt span_gramSchmidtNormed_range
  gramSchmidtNormed_orthonormal')

theorem mhn_seq_dense {H : Type*} [PseudoMetricSpace H] [TopologicalSpace.SeparableSpace H]
    (S : Set H) (hS : S.Nonempty) :
    ∃ u : ℕ → H, (∀ n, u n ∈ S) ∧ S ⊆ closure (Set.range u) := by
  haveI : SecondCountableTopology H := UniformSpace.secondCountable_of_separable H
  haveI : Nonempty S := hS.to_subtype
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq S
  refine ⟨fun n => (u n : H), fun n => (u n).2, fun y hy => ?_⟩
  exact hu.induction_on (p := fun z : S => (z : H) ∈ closure (Set.range fun n => (u n : H)))
    ⟨y, hy⟩ (isClosed_closure.preimage continuous_subtype_val) (fun n => subset_closure ⟨n, rfl⟩)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem mhn_norming_abstract (R : Submodule ℝ H) (hR : Rᗮ = ⊥) :
    ∃ s : ℕ → H, (∀ n, s n ∈ R) ∧ (∀ n, ‖s n‖ ≤ 1) ∧
      ∀ x : H, ‖x‖ = ⨆ n, |inner ℝ (s n) x| := by
  obtain ⟨s, hsS, hsd⟩ := mhn_seq_dense {y : H | y ∈ R ∧ ‖y‖ ≤ 1} ⟨0, R.zero_mem, by simp⟩
  refine ⟨s, fun n => (hsS n).1, fun n => (hsS n).2, fun x => ?_⟩
  have hbdd : BddAbove (Set.range fun n => |inner ℝ (s n) x|) := by
    refine ⟨‖x‖, ?_⟩
    rintro _ ⟨n, rfl⟩
    calc |inner ℝ (s n) x| ≤ ‖s n‖ * ‖x‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right (hsS n).2 (norm_nonneg _)
      _ = ‖x‖ := one_mul _
  set K := ⨆ n, |inner ℝ (s n) x| with hK
  have hK0 : 0 ≤ K := Real.iSup_nonneg (fun n => abs_nonneg _)
  apply le_antisymm
  · have h1 : ∀ y ∈ R, |inner ℝ y x| ≤ K * ‖y‖ := by
      intro y hy
      by_cases hy0 : y = 0
      · simp [hy0]
      have hn : 0 < ‖y‖ := norm_pos_iff.2 hy0
      have hmem : (‖y‖⁻¹ • y) ∈ {y : H | y ∈ R ∧ ‖y‖ ≤ 1} :=
        ⟨R.smul_mem _ hy, by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']⟩
      have hcl : |inner ℝ (‖y‖⁻¹ • y) x| ≤ K := by
        have hclosed : IsClosed {z : H | |inner ℝ z x| ≤ K} :=
          isClosed_le (by fun_prop) continuous_const
        have hsub : Set.range s ⊆ {z : H | |inner ℝ z x| ≤ K} := by
          rintro _ ⟨n, rfl⟩
          exact le_ciSup hbdd n
        exact (closure_minimal hsub hclosed) (hsd hmem)
      rw [real_inner_smul_left, abs_mul, abs_of_pos (inv_pos.2 hn)] at hcl
      have := mul_le_mul_of_nonneg_left hcl hn.le
      rw [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul] at this
      linarith
    have hdense : Dense (R : Set H) := by
      rw [dense_iff_closure_eq]
      have h2 : R.topologicalClosure = ⊤ := by
        rw [Submodule.topologicalClosure_eq_top_iff]; exact hR
      have := congrArg (fun T : Submodule ℝ H => (T : Set H)) h2
      simpa [Submodule.topologicalClosure_coe] using this
    have hclosed2 : IsClosed {z : H | |inner ℝ z x| ≤ K * ‖z‖} :=
      isClosed_le (by fun_prop) (by fun_prop)
    have hx := (closure_minimal h1 hclosed2) (by rw [hdense.closure_eq]; exact Set.mem_univ x)
    change |inner ℝ x x| ≤ K * ‖x‖ at hx
    rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg ‖x‖)] at hx
    by_cases hx0 : x = 0
    · simp [hx0, hK0]
    have hn : 0 < ‖x‖ := norm_pos_iff.2 hx0
    nlinarith
  · refine ciSup_le (fun n => ?_)
    calc |inner ℝ (s n) x| ≤ ‖s n‖ * ‖x‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right (hsS n).2 (norm_nonneg _)
      _ = ‖x‖ := one_mul _

theorem mhn_parseval_abstract (R : Submodule ℝ H) (hR : Rᗮ = ⊥) :
    ∃ e : ℕ → H, (∀ n, e n ∈ R) ∧ ∀ x : H, HasSum (fun n => (inner ℝ (e n) x) ^ 2) (‖x‖ ^ 2) := by
  obtain ⟨u, huR, hud⟩ := mhn_seq_dense (R : Set H) ⟨0, R.zero_mem⟩
  have hgR : ∀ n, gramSchmidtNormed ℝ u n ∈ R := by
    intro n
    have h1 : gramSchmidt ℝ u n ∈ R := by
      have : gramSchmidt ℝ u n ∈ Submodule.span ℝ (Set.range u) := by
        rw [← span_gramSchmidt]; exact Submodule.subset_span ⟨n, rfl⟩
      exact (Submodule.span_le.2 (by rintro _ ⟨m, rfl⟩; exact huR m)) this
    exact R.smul_mem _ h1
  refine ⟨gramSchmidtNormed ℝ u, hgR, fun x => ?_⟩
  set v : {i | gramSchmidtNormed ℝ u i ≠ 0} → H := fun i => gramSchmidtNormed ℝ u i with hv
  have hsp : (Submodule.span ℝ (Set.range v))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have hle : Submodule.span ℝ (Set.range (gramSchmidtNormed ℝ u)) ≤
        Submodule.span ℝ (Set.range v) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨n, rfl⟩
      by_cases hn : gramSchmidtNormed ℝ u n = 0
      · rw [hn]; exact Submodule.zero_mem _
      · exact Submodule.subset_span ⟨⟨n, hn⟩, rfl⟩
    have hy' := Submodule.orthogonal_le hle hy
    have hu : ∀ n, inner ℝ (u n) y = 0 := by
      intro n
      have : u n ∈ Submodule.span ℝ (Set.range (gramSchmidtNormed ℝ u)) := by
        rw [span_gramSchmidtNormed_range, span_gramSchmidt]; exact Submodule.subset_span ⟨n, rfl⟩
      exact (Submodule.mem_orthogonal _ _).1 hy' _ this
    have hclosed : IsClosed {z : H | inner ℝ z y = 0} := isClosed_eq (by fun_prop) continuous_const
    have hsub : Set.range u ⊆ {z : H | inner ℝ z y = 0} := by
      rintro _ ⟨n, rfl⟩; exact hu n
    have hRy : y ∈ Rᗮ := by
      rw [Submodule.mem_orthogonal]
      intro r hr
      exact (closure_minimal hsub hclosed) (hud hr)
    rw [hR] at hRy
    exact hRy
  let b : HilbertBasis {i | gramSchmidtNormed ℝ u i ≠ 0} ℝ H :=
    HilbertBasis.mkOfOrthogonalEqBot (gramSchmidtNormed_orthonormal' u) hsp
  have hb : ∀ i, b i = gramSchmidtNormed ℝ u i := fun i =>
    congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot (gramSchmidtNormed_orthonormal' u) hsp) i
  have h1 := b.hasSum_inner_mul_inner x x
  rw [real_inner_self_eq_norm_sq] at h1
  have h2 : HasSum (fun i : {i | gramSchmidtNormed ℝ u i ≠ 0} =>
      (inner ℝ (gramSchmidtNormed ℝ u i) x) ^ 2) (‖x‖ ^ 2) := by
    convert h1 using 2 with i
    rw [hb i, real_inner_comm, sq]
  have hsupp : Function.support (fun n => (inner ℝ (gramSchmidtNormed ℝ u n) x) ^ 2) ⊆
      {i | gramSchmidtNormed ℝ u i ≠ 0} := by
    intro n hn
    by_contra hc
    apply hn
    have : gramSchmidtNormed ℝ u n = 0 := by simpa using hc
    simp [this]
  exact (hasSum_subtype_iff_of_support_subset hsupp).1 h2

end Abstract

/-! ### Stage 2(c),(d) and stage 3: the final statements -/

theorem mhn_range_orth_bot (Γ : ℝ) : (LinearMap.range (mhn_rep (d := d) Γ))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro F hF
  refine mhn_eq_zero_of_orth F (fun h => ?_)
  rw [Submodule.mem_orthogonal] at hF
  exact hF _ ⟨h, rfl⟩

/-- Stage 2(d): a countable norming family of smooth tests. -/
theorem hneg_norming (d : ℕ) (Γ : ℝ) :
    ∃ φ : ℕ → (Euc d → ℝ), (∀ n, IsSobolevTest Γ (φ n)) ∧
      (∀ n, HRS.Whole.sobolevNorm Γ (φ n) ≤ 1) ∧
      ∀ F : HNeg d Γ, ‖F‖ = ⨆ n, |HNeg.pairing (φ n) F| := by
  obtain ⟨s, hsR, hs1, hnorm⟩ := mhn_norming_abstract (LinearMap.range (mhn_rep (d := d) Γ))
    (mhn_range_orth_bot Γ)
  choose h hh using fun n => hsR n
  refine ⟨fun n => mhn_phi (h n), fun n => mhn_isSobolevTest_phi Γ (h n), fun n => ?_, fun F => ?_⟩
  · rw [← mhn_norm_rep, hh]; exact hs1 n
  · rw [hnorm F]
    congr 1; ext n
    rw [mhn_pairing_phi, hh]

/-- Stage 2(c): the `H^{-Γ}` norm is determined by pairings against smooth tests. -/
theorem hneg_norm_le_of_pairing {d : ℕ} {Γ : ℝ} (F : HNeg d Γ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ φ : Euc d → ℝ, IsSobolevTest Γ φ →
      |HNeg.pairing φ F| ≤ c * HRS.Whole.sobolevNorm Γ φ) : ‖F‖ ≤ c := by
  obtain ⟨φ, hφ, hφ1, hnorm⟩ := hneg_norming d Γ
  rw [hnorm F]
  refine ciSup_le (fun n => ?_)
  calc |HNeg.pairing (φ n) F| ≤ c * HRS.Whole.sobolevNorm Γ (φ n) := h _ (hφ n)
    _ ≤ c * 1 := mul_le_mul_of_nonneg_left (hφ1 n) hc
    _ = c := mul_one c

/-- Stage 3: Parseval over a smooth orthonormal system. -/
theorem hneg_parseval (d : ℕ) (Γ : ℝ) :
    ∃ e : ℕ → (Euc d → ℝ), (∀ ℓ, IsSobolevTest Γ (e ℓ)) ∧
      ∀ F : HNeg d Γ, HasSum (fun ℓ => (HNeg.pairing (e ℓ) F) ^ 2) (‖F‖ ^ 2) := by
  obtain ⟨s, hsR, hs⟩ := mhn_parseval_abstract (LinearMap.range (mhn_rep (d := d) Γ))
    (mhn_range_orth_bot Γ)
  choose h hh using fun n => hsR n
  refine ⟨fun n => mhn_phi (h n), fun n => mhn_isSobolevTest_phi Γ (h n), fun F => ?_⟩
  have := hs F
  convert this using 2 with n
  rw [mhn_pairing_phi, hh]

/-! ### Stage 4: measurability of `HNeg`-valued maps via a norming family -/

section Measurability

variable {Γ : ℝ}

theorem mhn_pairing_sub {φ : Euc d → ℝ} (hφ : IsSobolevTest Γ φ) (F G : HNeg d Γ) :
    HNeg.pairing φ (F - G) = HNeg.pairing φ F - HNeg.pairing φ G := by
  rw [mhn_pairing_eq hφ.2, mhn_pairing_eq hφ.2, mhn_pairing_eq hφ.2]
  show (inner ℂ (mhn_psiLp hφ.2) ((F : HNegSubmodule d Γ).1 - (G : HNegSubmodule d Γ).1 :
      Lp ℂ 2 (sobolevMeasure d Γ))).re = _
  rw [inner_sub_right, Complex.sub_re]

theorem mhn_continuous_pairing {φ : Euc d → ℝ} (hφ : IsSobolevTest Γ φ) :
    Continuous (fun F : HNeg d Γ => HNeg.pairing φ F) := by
  have : (fun F : HNeg d Γ => HNeg.pairing φ F) = fun F : HNeg d Γ =>
      (inner ℂ (mhn_psiLp hφ.2) ((F : HNegSubmodule d Γ).1 : Lp ℂ 2 (sobolevMeasure d Γ))).re := by
    ext F; exact mhn_pairing_eq hφ.2 F
  rw [this]
  exact Complex.continuous_re.comp
    ((continuous_const.inner continuous_subtype_val))

/-- Stage 4: a map into `HNeg d Γ` is measurable iff its pairings with the members of a countable
norming family of smooth tests are measurable. -/
theorem hneg_measurable_iff {Ω : Type*} [MeasurableSpace Ω] {φ : ℕ → Euc d → ℝ}
    (hφ : ∀ n, IsSobolevTest Γ (φ n))
    (hnorm : ∀ F : HNeg d Γ, ‖F‖ = ⨆ n, |HNeg.pairing (φ n) F|) (F : Ω → HNeg d Γ) :
    Measurable F ↔ ∀ n, Measurable (fun x => HNeg.pairing (φ n) (F x)) := by
  let T : HNeg d Γ → (ℕ → ℝ) := fun G n => HNeg.pairing (φ n) G
  have hTc : Continuous T := continuous_pi (fun n => mhn_continuous_pairing (hφ n))
  have hTi : Function.Injective T := by
    intro G H hGH
    have h0 : ‖G - H‖ = 0 := by
      rw [hnorm]
      have : ∀ n, |HNeg.pairing (φ n) (G - H)| = 0 := by
        intro n
        rw [mhn_pairing_sub (hφ n), sub_eq_zero.2 (congrFun hGH n)]
        simp
      simp [this]
    exact sub_eq_zero.1 (norm_eq_zero.1 h0)
  have : SecondCountableTopology (HNeg d Γ) := inferInstance
  have hemb : MeasurableEmbedding T := hTc.measurableEmbedding hTi
  constructor
  · intro hF n
    exact (measurable_pi_apply n).comp (hTc.measurable.comp hF)
  · intro h
    rw [← hemb.measurable_comp_iff]
    exact measurable_pi_iff.2 h

end Measurability

end HRS.MP.HNegInfra
