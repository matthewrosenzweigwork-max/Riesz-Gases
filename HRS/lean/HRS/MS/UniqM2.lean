import HRS.MS.UniqM1Fin

/-!
# M2 of `UniqPlan.md`, part 1: weak derivatives of a Fourier-`H¹` function
-/

noncomputable section

open MeasureTheory Filter Topology Metric LineDeriv
open scoped ENNReal ContDiff FourierTransform ComplexConjugate

namespace HRS.MS.UniqM2

open HRS HRS.Whole HRS.Whole.AppendixA HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.UniqM1

variable {d : ℕ}

/-- The symbol `2πi ξ_j` of `∂_j`. -/
def mult (j : Fin d) (ξ : Euc d) : ℂ := 2 * Real.pi * Complex.I * ((ξ j : ℝ) : ℂ)

theorem continuous_mult (j : Fin d) : Continuous (mult j) := by
  unfold mult
  have : Continuous fun ξ : Euc d => ξ j := by fun_prop
  fun_prop

theorem norm_mult_sq (j : Fin d) (ξ : Euc d) : ‖mult j ξ‖ ^ 2 = 4 * Real.pi ^ 2 * (ξ j) ^ 2 := by
  unfold mult
  simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
    mul_one]
  rw [abs_of_pos Real.pi_pos, mul_pow, mul_pow, sq_abs]; ring

theorem sum_norm_mult_sq (ξ : Euc d) :
    ∑ j, ‖mult j ξ‖ ^ 2 = 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by
  simp_rw [norm_mult_sq]
  rw [← Finset.mul_sum, EuclideanSpace.norm_sq_eq]
  simp

theorem norm_mult_sq_le (j : Fin d) (ξ : Euc d) : ‖mult j ξ‖ ^ 2 ≤ wt ξ := by
  have h : ‖mult j ξ‖ ^ 2 ≤ ∑ i, ‖mult i ξ‖ ^ 2 :=
    Finset.single_le_sum (f := fun i => ‖mult i ξ‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  rw [sum_norm_mult_sq] at h
  unfold wt; linarith

theorem conj_mult (j : Fin d) (ξ : Euc d) : conj (mult j ξ) = - mult j ξ := by
  unfold mult
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

/-- The Fourier transform of `∂_j w`: `2πi ξ_j ŵ(ξ)`. -/
def gfun (w : Euc d → ℝ) (j : Fin d) (ξ : Euc d) : ℂ := mult j ξ * fourierL2 w ξ

theorem memLp_gfun {w : Euc d → ℝ} (hw : HRS.PDE.ToolboxRd.MemSobolev 1 w) (j : Fin d) : MemLp (gfun w j) 2 volume := by
  have hm : AEStronglyMeasurable (gfun w j) volume :=
    (continuous_mult j).aestronglyMeasurable.mul (aestronglyMeasurable_fourierL2 hw.1)
  rw [memLp_two_iff_integrable_sq_norm hm]
  refine Integrable.mono' hw.2 (hm.norm.pow 2) (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_of_nonneg (by positivity), Real.rpow_one]
  show ‖gfun w j ξ‖ ^ 2 ≤ wt ξ * _
  unfold gfun
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (norm_mult_sq_le j ξ) (by positivity)

/-! ### Test functions as Schwartz maps -/

/-- A smooth compactly supported real function as a complex Schwartz function. -/
def testS {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    SchwartzMap (Euc d) ℂ :=
  (hc.comp_left (g := ((↑) : ℝ → ℂ)) (by simp)).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hψ)

theorem testS_apply {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (x : Euc d) :
    testS hψ hc x = ((ψ x : ℝ) : ℂ) := rfl

theorem lineDeriv_testS {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (m x : Euc d) :
    (∂_{m} (testS hψ hc)) x = ((fderiv ℝ ψ x m : ℝ) : ℂ) := by
  rw [SchwartzMap.lineDerivOp_apply]
  show lineDeriv ℝ (fun x => ((ψ x : ℝ) : ℂ)) x m = _
  have h : HasFDerivAt (fun x => ((ψ x : ℝ) : ℂ)) ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).comp (fderiv ℝ ψ x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x ((hψ.differentiable (by simp)).differentiableAt.hasFDerivAt)
  exact (h.hasLineDerivAt m).lineDeriv


/-! ### The weak derivative via Plancherel -/

theorem inner_cc (a b : ℂ) : inner ℂ a b = conj a * b := RCLike.inner_apply' a b

/-- Pairing identity (complex form): if `V̂ = 2πiξ_j ŵ`, then `∫ w ∂_jψ = -∫ conj(V) ψ`. -/
theorem pairing_identity {w : Euc d → ℝ} (hw : HRS.PDE.ToolboxRd.MemSobolev 1 w) (j : Fin d)
    (V : Lp (α := Euc d) ℂ 2) (hV : FT d V = (memLp_gfun hw j).toLp (gfun w j))
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    ∫ x, w x * fderiv ℝ ψ x (EuclideanSpace.single j 1) = - ∫ x, (V x).re * ψ x := by
  set e : Euc d := EuclideanSpace.single j 1 with he
  have hw2 : MemLp w 2 volume := hw.1
  set f := testS hψ hc with hf
  set W := ofRealLp hw2 with hW
  set G := (memLp_gfun hw j).toLp (gfun w j) with hG
  set Φ : Lp (α := Euc d) ℂ 2 := (∂_{e} f).toLp 2 with hΦ
  set Ψ : Lp (α := Euc d) ℂ 2 := f.toLp 2 with hΨ
  -- Plancherel on both sides
  have h1 : inner ℂ W Φ = inner ℂ (FT d W) (FT d Φ) := (inner_FT W Φ).symm
  have h2 : inner ℂ V Ψ = inner ℂ G (FT d Ψ) := by rw [← hV]; exact (inner_FT V Ψ).symm
  have hFΦ : FT d Φ = (𝓕 (∂_{e} f)).toLp 2 := SchwartzMap.toLp_fourier_eq _
  have hFΨ : FT d Ψ = (𝓕 f).toLp 2 := SchwartzMap.toLp_fourier_eq _
  -- the Fourier side
  have h3 : inner ℂ (FT d W) (FT d Φ) = - inner ℂ G (FT d Ψ) := by
    rw [L2.inner_def, L2.inner_def]
    rw [← integral_neg]
    refine integral_congr_ae ?_
    have a1 : (FT d W : Euc d → ℂ) =ᵐ[volume] fourierL2 w := by rw [fourierL2_eq hw2]
    filter_upwards [a1, SchwartzMap.coeFn_toLp (𝓕 (∂_{e} f)) 2 volume,
      SchwartzMap.coeFn_toLp (𝓕 f) 2 volume, MemLp.coeFn_toLp (memLp_gfun hw j)] with ξ b1 b2 b3 b4
    rw [hFΦ, hFΨ]
    have c2 : ((𝓕 (∂_{e} f)).toLp 2 : Euc d → ℂ) ξ = (𝓕 (∂_{e} f)) ξ := b2
    have c3 : ((𝓕 f).toLp 2 : Euc d → ℂ) ξ = (𝓕 f) ξ := b3
    have c4 : (G : Euc d → ℂ) ξ = gfun w j ξ := b4
    rw [c2, c3, c4, b1, SchwartzMap.fourier_lineDerivOp_eq]
    simp only [smul_apply, inner_cc]
    have ht : (fun x : Euc d => inner ℝ x e).HasTemperateGrowth := ((innerSL ℝ).flip e).hasTemperateGrowth
    rw [SchwartzMap.smulLeftCLM_apply_apply ht]
    have hie : inner ℝ ξ e = ξ j := by
      rw [he, EuclideanSpace.inner_single_right]; simp
    rw [hie]
    unfold gfun mult
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, smul_eq_mul, Complex.real_smul]
    ring
  have h4 : inner ℂ W Φ = - inner ℂ V Ψ := by rw [h1, h3, h2]
  have eW : inner ℂ W Φ = (((∫ x, w x * fderiv ℝ ψ x e : ℝ)) : ℂ) := by
    rw [L2.inner_def, ← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [ofRealLp_coe hw2, SchwartzMap.coeFn_toLp (∂_{e} f) 2 volume] with x b1 b2
    have c1 : (W : Euc d → ℂ) x = ((w x : ℝ) : ℂ) := b1
    have c2 : (Φ : Euc d → ℂ) x = (∂_{e} f) x := b2
    rw [c1, c2, lineDeriv_testS hψ hc, inner_cc]
    simp
  have eV : (inner ℂ V Ψ).re = ∫ x, (V x).re * ψ x := by
    rw [L2.inner_def]
    refine (integral_re (𝕜 := ℂ) (L2.integrable_inner V Ψ)).symm.trans (integral_congr_ae ?_)
    filter_upwards [SchwartzMap.coeFn_toLp f 2 volume] with x b2
    have c2 : (Ψ : Euc d → ℂ) x = f x := b2
    rw [c2, testS_apply, inner_cc]
    simp
  have := congrArg Complex.re h4
  rw [eW, Complex.neg_re, eV, Complex.ofReal_re] at this
  exact this


theorem Lp_norm_sq (F : Lp (α := Euc d) ℂ 2) : ‖F‖ ^ 2 = ∫ x, ‖F x‖ ^ 2 := by
  have h := L2.inner_def (𝕜 := ℂ) F F
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)] at h
  have h2 : ((‖F‖ ^ 2 : ℝ) : ℂ) = ((∫ x, ‖F x‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine (by exact_mod_cast h : ((‖F‖ ^ 2 : ℝ) : ℂ) = _).trans (integral_congr_ae (Eventually.of_forall fun x => ?_))
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]; push_cast; rfl
  exact_mod_cast h2

/-- Existence of one weak derivative `∂_j w ∈ L²` (real-valued), with the Plancherel bound. -/
theorem weakDeriv_exists {w : Euc d → ℝ} (hw : HRS.PDE.ToolboxRd.MemSobolev 1 w) (j : Fin d) :
    ∃ v : Euc d → ℝ, Measurable v ∧ MemLp v 2 volume ∧
      ∫ x, v x ^ 2 ≤ ∫ ξ, ‖gfun w j ξ‖ ^ 2 ∧
      ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        ∫ x, w x * fderiv ℝ ψ x (EuclideanSpace.single j 1) = - ∫ x, v x * ψ x := by
  set G := (memLp_gfun hw j).toLp (gfun w j) with hG
  set V : Lp (α := Euc d) ℂ 2 := (FT d).symm G with hV
  have hFV : FT d V = G := (FT d).apply_symm_apply G
  have hre : AEStronglyMeasurable (fun x => (V x).re) volume :=
    Complex.continuous_re.comp_aestronglyMeasurable (Lp.aestronglyMeasurable V)
  have hae : (fun x => (V x).re) =ᵐ[volume] hre.mk _ := hre.ae_eq_mk
  have hmem : MemLp (fun x => (V x).re) 2 volume := by
    have := (Lp.memLp V).re
    exact this
  refine ⟨hre.mk _, hre.stronglyMeasurable_mk.measurable, hmem.ae_eq hae, ?_, ?_⟩
  · have h1 : ∫ x, (hre.mk _ x) ^ 2 = ∫ x, (V x).re ^ 2 :=
      integral_congr_ae (hae.mono fun x (hx : (V x).re = hre.mk _ x) => by
        show (hre.mk _ x) ^ 2 = (V x).re ^ 2
        rw [← hx])
    rw [h1]
    have h2 : ‖V‖ ^ 2 = ∫ ξ, ‖gfun w j ξ‖ ^ 2 := by
      rw [← (FT d).norm_map V, hFV, Lp_norm_sq]
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp (memLp_gfun hw j)] with ξ b
      rw [b]
    rw [← h2, Lp_norm_sq]
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) ?_ (Eventually.of_forall fun x => ?_)
    · exact (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable V)).1 (Lp.memLp V)
    · show (V x).re ^ 2 ≤ ‖V x‖ ^ 2
      calc (V x).re ^ 2 = |(V x).re| ^ 2 := (sq_abs _).symm
        _ ≤ ‖V x‖ ^ 2 := by gcongr; exact Complex.abs_re_le_norm _
  · intro ψ hψ hc
    rw [pairing_identity hw j V hFV hψ hc]
    congr 1
    exact integral_congr_ae (hae.mono fun x (hx : (V x).re = hre.mk _ x) => by
      show (V x).re * ψ x = hre.mk _ x * ψ x
      rw [hx])


theorem sum_integral_gfun_le {w : Euc d → ℝ} (hw : HRS.PDE.ToolboxRd.MemSobolev 1 w) :
    ∑ j, ∫ ξ, ‖gfun w j ξ‖ ^ 2 ≤ sobolevNormSq 1 w := by
  have hint : ∀ j, Integrable (fun ξ => ‖gfun w j ξ‖ ^ 2) volume := fun j =>
    (memLp_two_iff_integrable_sq_norm (memLp_gfun hw j).aestronglyMeasurable).1 (memLp_gfun hw j)
  rw [← integral_finsetSum _ fun j _ => hint j, sobolevNormSq_eq]
  refine integral_mono (integrable_finsetSum _ fun j _ => hint j) hw.2 fun ξ => ?_
  rw [Real.rpow_one]
  show ∑ j, ‖gfun w j ξ‖ ^ 2 ≤ wt ξ * _
  simp only [gfun, norm_mul, mul_pow]
  rw [← Finset.sum_mul, sum_norm_mult_sq]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  unfold wt; linarith [sq_nonneg ‖ξ‖]

/-- **Weak gradient of a Fourier-`H¹` function.**  There are measurable `L²` functions `v_j` with
`∫ w ∂_jψ = -∫ v_j ψ` for every `C_c^∞` function `ψ`, and `∑_j ‖v_j‖₂² ≤ ‖w‖²_{H¹}`. -/
theorem weakGrad_of_memSobolev {w : Euc d → ℝ} (hw : HRS.PDE.ToolboxRd.MemSobolev 1 w) :
    ∃ v : Fin d → Euc d → ℝ, (∀ j, Measurable (v j)) ∧ (∀ j, MemLp (v j) 2 volume) ∧
      ∑ j, ∫ x, v j x ^ 2 ≤ sobolevNormSq 1 w ∧
      ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∀ j : Fin d,
        ∫ x, w x * fderiv ℝ ψ x (EuclideanSpace.single j 1) = - ∫ x, v j x * ψ x := by
  choose v hm hl hb hid using fun j => weakDeriv_exists hw j
  refine ⟨v, hm, hl, le_trans (Finset.sum_le_sum fun j _ => hb j) (sum_integral_gfun_le hw), ?_⟩
  intro ψ hψ hc j
  exact hid j ψ hψ hc

/-- A bound `sobolevNormE r w ≤ ofReal B` gives membership in `H^r` and `‖w‖²_{H^r} ≤ B²`. -/
theorem memSobolev_of_sobolevNormE_le {r : ℝ} {w : Euc d → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (h : sobolevNormE r w ≤ ENNReal.ofReal B) :
    HRS.PDE.ToolboxRd.MemSobolev r w ∧ sobolevNormSq r w ≤ B ^ 2 := by
  by_cases hm : HRS.PDE.ToolboxRd.MemSobolev r w
  · refine ⟨hm, ?_⟩
    unfold sobolevNormE at h
    rw [if_pos hm, ENNReal.ofReal_le_ofReal_iff hB] at h
    have h0 : 0 ≤ sobolevNormSq r w := integral_nonneg fun ξ => by
      have := wt_pos (d := d) ξ
      positivity
    calc sobolevNormSq r w = (Real.sqrt (sobolevNormSq r w)) ^ 2 := (Real.sq_sqrt h0).symm
      _ ≤ B ^ 2 := by gcongr
  · exfalso
    unfold sobolevNormE at h
    rw [if_neg hm] at h
    exact absurd h (by simp)

end HRS.MS.UniqM2
