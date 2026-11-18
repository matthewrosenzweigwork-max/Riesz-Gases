import HRS.MS.UniqN3aG

/-!
# N3a, part H: from Schwartz `u` to `u ∈ L²`, and the final bridge
-/

noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate SchwartzMap LineDeriv

namespace HRS.MS.UniqN3a
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.UniqT2

variable {d : ℕ}

/-- Real Cauchy–Schwarz on `L²`. -/
theorem cs_real {f g : Euc d → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    |∫ x, f x * g x| ≤ Real.sqrt (∫ x, f x ^ 2) * Real.sqrt (∫ x, g x ^ 2) := by
  have hP : Integrable (fun x => f x ^ 2) := hf.integrable_sq
  have hQ : Integrable (fun x => g x ^ 2) := hg.integrable_sq
  have hR : Integrable (fun x => f x * g x) := by
    refine Integrable.mono' ((hP.add hQ).div_const 2)
      (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (|f x| - |g x|), sq_abs (f x), sq_abs (g x)]
  have h2 : (∫ x, f x * g x) ^ 2 ≤ (∫ x, f x ^ 2) * (∫ x, g x ^ 2) :=
    cs_aux hP hQ hR fun t x => by nlinarith [sq_nonneg (t * f x - g x)]
  rw [← Real.sqrt_mul (integral_nonneg fun x => sq_nonneg _)]
  exact Real.abs_le_sqrt h2

/-- Density of Schwartz functions in `L²`, in the form used here. -/
theorem exists_schwartz_approx {u : Euc d → ℝ} (hu : MemLp u 2 volume) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : SchwartzMap (Euc d) ℝ, ∫ x, (u x - φ x) ^ 2 ≤ ε := by
  have hdense := SchwartzMap.denseRange_toLpCLM (E := Euc d) (F := ℝ) (p := 2)
    (μ := volume) (by norm_num)
  obtain ⟨φ, hφ⟩ := hdense.exists_dist_lt (hu.toLp u) (Real.sqrt_pos.2 hε)
  refine ⟨φ, ?_⟩
  have hφm : MemLp (⇑φ) 2 volume := φ.memLp 2 volume
  have hh : MemLp (fun x => u x - φ x) 2 volume := hu.sub hφm
  have hcoe : ⇑(hu.toLp u - (SchwartzMap.toLpCLM ℝ ℝ 2 volume) φ) =ᵐ[volume] fun x => u x - φ x := by
    filter_upwards [Lp.coeFn_sub (hu.toLp u) ((SchwartzMap.toLpCLM ℝ ℝ 2 volume) φ),
      hu.coeFn_toLp, SchwartzMap.coeFn_toLp φ 2 volume] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2]
    simp [h3]
  rw [dist_eq_norm, Lp.norm_def, eLpNorm_congr_ae hcoe,
    hh.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)] at hφ
  have hnn : 0 ≤ ∫ x, ‖u x - φ x‖ ^ ((2 : ℝ≥0∞).toReal) := integral_nonneg fun x => by positivity
  rw [ENNReal.toReal_ofReal (by positivity)] at hφ
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hφ hnn
  have hX : (∫ x, ‖u x - φ x‖ ^ 2) ^ (2 : ℝ)⁻¹ < Real.sqrt ε := hφ
  rw [← one_div, ← Real.sqrt_eq_rpow, Real.sqrt_lt_sqrt_iff hnn] at hX
  refine le_of_lt (lt_of_eq_of_lt ?_ hX)
  congr 1; funext x; rw [Real.norm_eq_abs, sq_abs]

/-- Dependence of the Fourier form on `u` (for `v` with `m v̂ ∈ L²`). -/
theorem lhs_diff_le {c s : ℝ} (q : Euc d) {u φ v : Euc d → ℝ} (hu : MemLp u 2 volume)
    (hφ : MemLp φ 2 volume) (hG : MemLp (fun ξ => ((mq c s q ξ : ℝ) : ℂ) * fourierL2 v ξ) 2 volume) :
    |symbolForm (mq c s q) u v - symbolForm (mq c s q) φ v| ≤
      Real.sqrt (∫ x, (u x - φ x) ^ 2) *
        Real.sqrt (∫ ξ, ‖((mq c s q ξ : ℝ) : ℂ) * fourierL2 v ξ‖ ^ 2) := by
  set G : Euc d → ℂ := fun ξ => ((mq c s q ξ : ℝ) : ℂ) * fourierL2 v ξ with hGdef
  have e : ∀ w : Euc d → ℝ, symbolForm (mq c s q) w v = (∫ ξ, fourierL2 w ξ * conj (G ξ)).re := by
    intro w
    unfold symbolForm
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [hGdef, map_mul, Complex.conj_ofReal]; ring
  rw [e u, e φ]
  have i1 := integrable_mul_conj (memLp_fourierL2 hu) hG
  have i2 := integrable_mul_conj (memLp_fourierL2 hφ) hG
  rw [← Complex.sub_re, ← integral_sub i1 i2]
  have hsub := fourierL2_sub hu hφ
  have e2 : ∫ ξ, (fourierL2 u ξ * conj (G ξ) - fourierL2 φ ξ * conj (G ξ)) =
      ∫ ξ, fourierL2 (fun x => u x - φ x) ξ * conj (G ξ) := by
    refine integral_congr_ae ?_
    filter_upwards [hsub] with ξ hξ
    rw [hξ]; ring
  rw [e2]
  refine (Complex.abs_re_le_norm _).trans ?_
  refine (cs_L2 (memLp_fourierL2 (hu.sub hφ)) hG).trans ?_
  rw [integral_norm_sq_fourierL2 (hu.sub hφ)]
  exact le_rfl

/-- Dependence of the physical form on `u`. -/
theorem rhs_diff_le {u φ w : Euc d → ℝ} (hu : MemLp u 2 volume) (hφ : MemLp φ 2 volume)
    (hw : MemLp w 2 volume) :
    |(∫ x, u x * w x) - ∫ x, φ x * w x| ≤
      Real.sqrt (∫ x, (u x - φ x) ^ 2) * Real.sqrt (∫ x, w x ^ 2) := by
  have i1 : Integrable (fun x => u x * w x) := hu.integrable_mul hw
  have i2 : Integrable (fun x => φ x * w x) := hφ.integrable_mul hw
  rw [← integral_sub i1 i2]
  have : ∫ x, (u x * w x - φ x * w x) = ∫ x, (u x - φ x) * w x :=
    integral_congr_ae (Eventually.of_forall fun x => by ring)
  rw [this]
  exact cs_real (hu.sub hφ) hw

end HRS.MS.UniqN3a
