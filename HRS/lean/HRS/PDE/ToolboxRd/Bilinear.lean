import HRS.PDE.ToolboxRd.Defs
import HRS.PDE.ToolboxRd.Fourier
import HRS.PDE.ToolboxRd.Levy
import HRS.PDE.ToolboxRd.Weighted

/-!
# The bilinear identity of Lemma C.3(ii) on `ℝ^d`

`bilinear_core`: for an even measurable kernel `𝔨` with `|𝔨(z)| ≤ C|z|^{-d-θ}` and
`∫ 𝔨(z)(1 - cos 2π⟨ξ,z⟩) dz = m(ξ)`, and Lipschitz `u, v ∈ H¹`,
`∬ |𝔨(z) δ_z u(x) δ_z v(x)| < ∞` and `B(u,v) = ½ ∬ 𝔨(z) δ_z u(x) δ_z v(x) dz dx`.

Proof route: absolute convergence from `∫|δ_z u||δ_z v| ≤ K min(|z|²,1)`; for each `z`,
Plancherel and the translation formula give `∫ δ_z u δ_z v dx = ∫ |1-e^{-2πi⟨z,ξ⟩}|² û \bar{v̂} dξ`;
Fubini in `(z, ξ)` and `∫𝔨(z)|1-e^{-2πi⟨z,ξ⟩}|² dz = 2 m(ξ)`.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform

namespace HRS.PDE.ToolboxRd.BilinAux
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux
variable {d : ℕ}

/-! ### Slice bounds -/

theorem sobolevNormSq_nonneg (u : Euc d → ℝ) : 0 ≤ sobolevNormSq 1 u :=
  integral_nonneg fun ξ => mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _)

theorem integral_diff_sq_le_four {u : Euc d → ℝ} (hu : MemLp u 2 volume) (z : Euc d) :
    ∫ x, (u x - u (x - z)) ^ 2 ≤ 4 * ∫ x, u x ^ 2 := by
  have hs := memLp_translate hu z
  have i1 : Integrable (fun x => u x ^ 2) volume := hu.integrable_sq
  have i2 : Integrable (fun x => u (x - z) ^ 2) volume := hs.integrable_sq
  have key : ∫ x, u (x - z) ^ 2 = ∫ x : Euc d, u x ^ 2 :=
    integral_sub_right_eq_self (μ := volume) (fun x => u x ^ 2) z
  calc ∫ x, (u x - u (x - z)) ^ 2 ≤ ∫ x, (2 * u x ^ 2 + 2 * u (x - z) ^ 2) :=
        integral_mono (hu.sub hs).integrable_sq ((i1.const_mul 2).add (i2.const_mul 2))
          fun x => by simp only; nlinarith [sq_nonneg (u x + u (x - z))]
    _ = 4 * ∫ x, u x ^ 2 := by
        rw [integral_add (i1.const_mul 2) (i2.const_mul 2), integral_const_mul,
          integral_const_mul, key]; ring

/-- `∫ |δ_z u||δ_z v| ≤ K min(|z|², 1)` -/
theorem slice_bound {u v : Euc d → ℝ} (hu : MemSobolev 1 u) (hv : MemSobolev 1 v) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : Euc d,
      ∫ x, |(u x - u (x - z)) * (v x - v (x - z))| ≤ K * min (‖z‖ ^ 2) 1 := by
  set a := sobolevNormSq 1 u
  set b := sobolevNormSq 1 v
  set N := ∫ x, u x ^ 2
  set M := ∫ x, v x ^ 2
  have ha : 0 ≤ a := sobolevNormSq_nonneg u
  have hb : 0 ≤ b := sobolevNormSq_nonneg v
  have hN : 0 ≤ N := integral_nonneg fun x => sq_nonneg _
  have hM : 0 ≤ M := integral_nonneg fun x => sq_nonneg _
  refine ⟨(a + b + 4 * (N + M)) / 2, by positivity, fun z => ?_⟩
  have hdu : Integrable (fun x => (u x - u (x - z)) ^ 2) volume :=
    (hu.1.sub (memLp_translate hu.1 z)).integrable_sq
  have hdv : Integrable (fun x => (v x - v (x - z)) ^ 2) volume :=
    (hv.1.sub (memLp_translate hv.1 z)).integrable_sq
  have h1 : ∫ x, |(u x - u (x - z)) * (v x - v (x - z))| ≤
      ∫ x, (1 / 2 * (u x - u (x - z)) ^ 2 + 1 / 2 * (v x - v (x - z)) ^ 2) := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
      ((hdu.const_mul _).add (hdv.const_mul _)) (Eventually.of_forall fun x => ?_)
    simp only
    rw [abs_mul]
    nlinarith [sq_nonneg (|u x - u (x - z)| - |v x - v (x - z)|), sq_abs (u x - u (x - z)),
      sq_abs (v x - v (x - z))]
  rw [integral_add (hdu.const_mul _) (hdv.const_mul _), integral_const_mul, integral_const_mul]
    at h1
  have e1 := diff_sq_le hu z
  have e2 := diff_sq_le hv z
  have f1 := integral_diff_sq_le_four hu.1 z
  have f2 := integral_diff_sq_le_four hv.1 z
  refine h1.trans ?_
  have hz : 0 ≤ ‖z‖ ^ 2 := sq_nonneg _
  rcases le_total (‖z‖ ^ 2) 1 with h | h
  · rw [min_eq_left h]
    nlinarith [mul_nonneg hz hN, mul_nonneg hz hM]
  · rw [min_eq_right h]
    nlinarith [mul_nonneg hz ha, mul_nonneg hz hb]

/-! ### Absolute integrability -/

theorem measurable_integrand {u v : Euc d → ℝ} (hu : Continuous u) (hv : Continuous v)
    {𝔨 : Euc d → ℝ} (hmeas : Measurable 𝔨) :
    Measurable (fun p : Euc d × Euc d =>
      𝔨 p.2 * (u p.1 - u (p.1 - p.2)) * (v p.1 - v (p.1 - p.2))) := by
  have := hu.measurable
  have := hv.measurable
  fun_prop

theorem integrable_core (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) {𝔨 : Euc d → ℝ}
    (hmeas : Measurable 𝔨)
    (hb : ∃ C : ℝ, ∀ z : Euc d, z ≠ 0 → |𝔨 z| ≤ C * ‖z‖ ^ (-(d : ℝ) - θ))
    {Lu Lv : ℝ} {u v : Euc d → ℝ} (hLu : IsLipschitz Lu u) (hLv : IsLipschitz Lv v)
    (hu : MemSobolev 1 u) (hv : MemSobolev 1 v) :
    Integrable (fun p : Euc d × Euc d =>
      𝔨 p.2 * (u p.1 - u (p.1 - p.2)) * (v p.1 - v (p.1 - p.2))) := by
  have huc := continuous_of_isLipschitz hLu
  have hvc := continuous_of_isLipschitz hLv
  have hF := measurable_integrand huc hvc hmeas
  obtain ⟨K, hK0, hK⟩ := slice_bound hu hv
  rw [Measure.volume_eq_prod, integrable_prod_iff' hF.aestronglyMeasurable]
  have hslice : ∀ z : Euc d, ∫ x, ‖𝔨 z * (u x - u (x - z)) * (v x - v (x - z))‖ =
      |𝔨 z| * ∫ x, |(u x - u (x - z)) * (v x - v (x - z))| := by
    intro z
    rw [← integral_const_mul]
    congr 1; ext x
    rw [Real.norm_eq_abs, mul_assoc, abs_mul]
  refine ⟨Eventually.of_forall fun z => ?_, ?_⟩
  · have hi := ((hu.1.sub (memLp_translate hu.1 z)).integrable_mul
      (hv.1.sub (memLp_translate hv.1 z)))
    have := hi.const_mul (𝔨 z)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply, Pi.sub_apply]; ring
  · have hmin := LevyAux.kernel_min_integrable hd hθ0 hθ2 hb hmeas
    refine Integrable.mono' (hmin.const_mul K) ?_ (Eventually.of_forall fun z => ?_)
    · exact (hF.stronglyMeasurable.norm.integral_prod_left').aestronglyMeasurable
    · simp only
      rw [hslice, Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (integral_nonneg fun x => abs_nonneg _))]
      calc |𝔨 z| * ∫ x, |(u x - u (x - z)) * (v x - v (x - z))| ≤ |𝔨 z| * (K * min (‖z‖ ^ 2) 1) :=
            mul_le_mul_of_nonneg_left (hK z) (abs_nonneg _)
        _ = _ := by ring

/-! ### Fourier side -/

theorem continuous_phase_uncurry : Continuous (fun p : Euc d × Euc d => phase p.1 p.2) := by
  unfold phase; fun_prop

theorem phase_zero (h : Euc d) : phase h 0 = 1 := by simp [phase]

theorem slice_fourier {u v : Euc d → ℝ} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (h : Euc d) :
    (((∫ x, (u x - u (x - h)) * (v x - v (x - h)) : ℝ)) : ℂ) =
      ∫ ξ, ((‖1 - phase h ξ‖ ^ 2 : ℝ) : ℂ) * (fourierL2 u ξ * conj (fourierL2 v ξ)) := by
  have hwu : MemLp (fun x => u x - u (x - h)) 2 volume := hu.sub (memLp_translate hu h)
  have hwv : MemLp (fun x => v x - v (x - h)) 2 volume := hv.sub (memLp_translate hv h)
  rw [← integral_fourierL2_mul_conj hwu hwv]
  apply integral_congr_ae
  filter_upwards [fourierL2_sub_translate hu h, fourierL2_sub_translate hv h] with ξ a b
  rw [a, b, map_mul]
  have : (1 - phase h ξ) * conj (1 - phase h ξ) = ((‖1 - phase h ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  calc (1 - phase h ξ) * fourierL2 u ξ * (conj (1 - phase h ξ) * conj (fourierL2 v ξ))
      = ((1 - phase h ξ) * conj (1 - phase h ξ)) * (fourierL2 u ξ * conj (fourierL2 v ξ)) := by
        ring
    _ = _ := by rw [this]

theorem norm_sq_eq_cos (z ξ : Euc d) :
    ‖1 - phase z ξ‖ ^ 2 = 2 * (1 - Real.cos (2 * Real.pi * inner ℝ ξ z)) := by
  rw [norm_one_sub_phase_sq, real_inner_comm,
    show 2 * Real.pi * inner ℝ ξ z = 2 * (Real.pi * inner ℝ ξ z) by ring, Real.cos_two_mul]
  have := Real.sin_sq_add_cos_sq (Real.pi * inner ℝ ξ z)
  nlinarith

theorem norm_sq_le_min (z ξ : Euc d) :
    ‖1 - phase z ξ‖ ^ 2 ≤ 4 * Real.pi ^ 2 * min 1 (‖ξ‖ ^ 2 * ‖z‖ ^ 2) := by
  have h1 := norm_one_sub_phase_le z ξ
  have h2 : ‖1 - phase z ξ‖ ≤ 2 := by
    calc ‖1 - phase z ξ‖ ≤ ‖(1 : ℂ)‖ + ‖phase z ξ‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_phase]; simp; norm_num
  have h0 := norm_nonneg (1 - phase z ξ)
  have hpi : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have e1 : ‖1 - phase z ξ‖ ^ 2 ≤ 4 := by nlinarith
  have e2 : ‖1 - phase z ξ‖ ^ 2 ≤ 4 * Real.pi ^ 2 * (‖ξ‖ ^ 2 * ‖z‖ ^ 2) := by
    calc ‖1 - phase z ξ‖ ^ 2 ≤ (2 * Real.pi * (‖z‖ * ‖ξ‖)) ^ 2 := by gcongr
      _ = _ := by ring
  rcases le_total 1 (‖ξ‖ ^ 2 * ‖z‖ ^ 2) with h | h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h]; exact e2

theorem rpow_le_wt {θ : ℝ} (hθ : 0 < θ) (ξ : Euc d) : ‖ξ‖ ^ θ ≤ wt ξ ^ (θ / 2) := by
  have hc : 0 ≤ ‖ξ‖ := norm_nonneg _
  have e : ‖ξ‖ ^ θ = (‖ξ‖ ^ 2) ^ (θ / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc]; congr 1; push_cast; ring
  rw [e]
  apply Real.rpow_le_rpow (by positivity) _ (by linarith)
  unfold wt
  have hp : 1 ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  nlinarith [mul_le_mul_of_nonneg_right hp (sq_nonneg ‖ξ‖)]

theorem scaling_bound (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) {𝔨 : Euc d → ℝ}
    (hmeas : Measurable 𝔨)
    (hb : ∃ C : ℝ, ∀ z : Euc d, z ≠ 0 → |𝔨 z| ≤ C * ‖z‖ ^ (-(d : ℝ) - θ)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ξ : Euc d,
      Integrable (fun z => |𝔨 z| * ‖1 - phase z ξ‖ ^ 2) ∧
      ∫ z, |𝔨 z| * ‖1 - phase z ξ‖ ^ 2 ≤ A * wt ξ ^ (θ / 2) := by
  obtain ⟨C, hC⟩ := hb
  set f : Euc d → ℝ := fun w => ‖w‖ ^ (-(d : ℝ) - θ) * min (‖w‖ ^ 2) 1 with hfdef
  have hf : Integrable f := by
    have := LevyAux.kernel_min_integrable hd hθ0 hθ2 (𝔨 := fun z : Euc d => ‖z‖ ^ (-(d : ℝ) - θ))
      ⟨1, fun z hz => by
        rw [abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]; simp⟩
      (by fun_prop)
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only [hfdef]
    rw [abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  set J := ∫ w, f w with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun w =>
    mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (le_min (by positivity) zero_le_one)
  refine ⟨4 * Real.pi ^ 2 * |C| * J, mul_nonneg (mul_nonneg (by positivity) (abs_nonneg _)) hJ0, fun ξ => ?_⟩
  have hmeasI : Measurable (fun z : Euc d => |𝔨 z| * ‖1 - phase z ξ‖ ^ 2) := by
    have : Continuous (fun z : Euc d => phase z ξ) :=
      continuous_phase_uncurry.comp (continuous_id.prodMk continuous_const)
    exact hmeas.abs.mul (by fun_prop)
  by_cases hξ : ξ = 0
  · subst hξ
    have : (fun z : Euc d => |𝔨 z| * ‖1 - phase z 0‖ ^ 2) = fun _ => 0 := by
      funext z; simp [phase_zero]
    rw [this]
    refine ⟨integrable_zero _ _ _, ?_⟩
    simp only [integral_zero]
    have := wt_pos (d := d) 0
    positivity
  · have hr : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    set r := ‖ξ‖ with hrdef
    set dom : Euc d → ℝ := fun z => 4 * Real.pi ^ 2 * |C| * r ^ ((d : ℝ) + θ) * f (r • z) with hdom
    have hdomI : Integrable dom := by
      have := (integrable_comp_smul_iff volume f hr.ne').2 hf
      exact this.const_mul _
    have hdomint : ∫ z, dom z = 4 * Real.pi ^ 2 * |C| * J * r ^ θ := by
      simp only [hdom]
      rw [integral_const_mul, Measure.integral_comp_smul volume f r, finrank_euclideanSpace_fin]
      have h1 : |(r ^ d)⁻¹| = (r ^ d)⁻¹ := abs_of_nonneg (by positivity)
      rw [smul_eq_mul, h1, Real.rpow_add hr, Real.rpow_natCast, ← hJ]
      field_simp
    have hpt : ∀ z : Euc d, |𝔨 z| * ‖1 - phase z ξ‖ ^ 2 ≤ dom z := by
      intro z
      have hdom0 : 0 ≤ dom z := by
        simp only [hdom, hfdef]
        have : 0 ≤ f (r • z) := mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
          (le_min (by positivity) zero_le_one)
        positivity
      by_cases hz : z = 0
      · subst hz
        have : phase (0 : Euc d) ξ = 1 := by simp [phase]
        rw [this]; simpa using hdom0
      · have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
        have h1 : |𝔨 z| ≤ |C| * ‖z‖ ^ (-(d : ℝ) - θ) :=
          (hC z hz).trans (mul_le_mul_of_nonneg_right (le_abs_self C)
            (Real.rpow_nonneg (norm_nonneg _) _))
        have h2 := norm_sq_le_min z ξ
        have h3 : dom z = |C| * ‖z‖ ^ (-(d : ℝ) - θ) *
            (4 * Real.pi ^ 2 * min 1 (r ^ 2 * ‖z‖ ^ 2)) := by
          simp only [hdom, hfdef]
          rw [norm_smul, Real.norm_of_nonneg hr.le, Real.mul_rpow hr.le hzn.le, mul_pow,
            min_comm]
          have : r ^ ((d : ℝ) + θ) * r ^ (-(d : ℝ) - θ) = 1 := by
            rw [← Real.rpow_add hr]; simp
          calc _ = (r ^ ((d : ℝ) + θ) * r ^ (-(d : ℝ) - θ)) * (4 * Real.pi ^ 2 * |C| *
                (‖z‖ ^ (-(d : ℝ) - θ) * min 1 (r ^ 2 * ‖z‖ ^ 2))) := by ring
            _ = _ := by rw [this]; ring
        rw [h3]
        calc |𝔨 z| * ‖1 - phase z ξ‖ ^ 2
            ≤ (|C| * ‖z‖ ^ (-(d : ℝ) - θ)) * (4 * Real.pi ^ 2 * min 1 (r ^ 2 * ‖z‖ ^ 2)) :=
              mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
          _ = _ := by ring
    have hbd : ∀ᵐ z : Euc d, ‖|𝔨 z| * ‖1 - phase z ξ‖ ^ 2‖ ≤ dom z :=
      Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (by positivity)]; exact hpt z
    have hI : Integrable (fun z : Euc d => |𝔨 z| * ‖1 - phase z ξ‖ ^ 2) :=
      hdomI.mono' hmeasI.aestronglyMeasurable hbd
    refine ⟨hI, ?_⟩
    refine (integral_mono hI hdomI hpt).trans ?_
    rw [hdomint]
    have := rpow_le_wt hθ0 ξ
    have h0 : 0 ≤ 4 * Real.pi ^ 2 * |C| * J :=
      mul_nonneg (mul_nonneg (by positivity) (abs_nonneg _)) hJ0
    exact mul_le_mul_of_nonneg_left this h0

/-! ### Assembly -/

theorem integrable_wt_Q {θ : ℝ} (_hθ : 0 < θ) {u v : Euc d → ℝ}
    (hu : MemSobolev (θ / 2) u) (hv : MemSobolev (θ / 2) v) :
    Integrable (fun ξ => wt ξ ^ (θ / 2) * ‖fourierL2 u ξ * conj (fourierL2 v ξ)‖) volume := by
  have hau := aestronglyMeasurable_fourierL2 hu.1
  have hav := aestronglyMeasurable_fourierL2 hv.1
  have hU : Integrable (fun ξ => wt ξ ^ (θ / 2) * ‖fourierL2 u ξ‖ ^ 2) volume := hu.2
  have hV : Integrable (fun ξ => wt ξ ^ (θ / 2) * ‖fourierL2 v ξ‖ ^ 2) volume := hv.2
  refine Integrable.mono' ((hU.add hV).div_const 2)
    ((continuous_wt_rpow _).aestronglyMeasurable.mul
      (hau.mul (Complex.continuous_conj.comp_aestronglyMeasurable hav)).norm)
    (Eventually.of_forall fun ξ => ?_)
  have h0 : 0 ≤ wt ξ ^ (θ / 2) := Real.rpow_nonneg (wt_pos ξ).le _
  rw [Real.norm_of_nonneg (mul_nonneg h0 (norm_nonneg _))]
  simp only [norm_mul, Complex.norm_conj, Pi.add_apply]
  nlinarith [mul_nonneg h0 (sq_nonneg (‖fourierL2 u ξ‖ - ‖fourierL2 v ξ‖))]

theorem bilinear_core (hd : 1 ≤ d) {θ : ℝ} {m : Euc d → ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2)
    (_hm : IsHomogSymbol θ m) (𝔨 : Euc d → ℝ) (_hev : ∀ z, 𝔨 (-z) = 𝔨 z)
    (hmeas : Measurable 𝔨)
    (hb : ∃ C : ℝ, ∀ z : Euc d, z ≠ 0 → |𝔨 z| ≤ C * ‖z‖ ^ (-(d : ℝ) - θ))
    (hs : ∀ ξ : Euc d, Integrable (fun z => 𝔨 z * (1 - Real.cos (2 * Real.pi * inner ℝ ξ z))) ∧
      ∫ z, 𝔨 z * (1 - Real.cos (2 * Real.pi * inner ℝ ξ z)) = m ξ) :
    ∀ (Lu Lv : ℝ) (u v : Euc d → ℝ), IsLipschitz Lu u → IsLipschitz Lv v →
      MemSobolev 1 u → MemSobolev 1 v →
      Integrable (fun p : Euc d × Euc d =>
        𝔨 p.2 * (u p.1 - u (p.1 - p.2)) * (v p.1 - v (p.1 - p.2))) ∧
      symbolForm m u v =
        (1 / 2) * ∫ p : Euc d × Euc d,
          𝔨 p.2 * (u p.1 - u (p.1 - p.2)) * (v p.1 - v (p.1 - p.2)) := by
  intro Lu Lv u v hLu hLv hu hv
  have hint := integrable_core hd hθ0 hθ2 hmeas hb hLu hLv hu hv
  refine ⟨hint, ?_⟩
  have huc := continuous_of_isLipschitz hLu
  have hvc := continuous_of_isLipschitz hLv
  set Q : Euc d → ℂ := fun ξ => fourierL2 u ξ * conj (fourierL2 v ξ) with hQdef
  have hQ : Integrable Q volume := integrable_fourierL2_mul_conj hu.1 hv.1
  set G : Euc d × Euc d → ℂ := fun q => ((𝔨 q.1 * ‖1 - phase q.1 q.2‖ ^ 2 : ℝ) : ℂ) * Q q.2
    with hGdef
  -- the real kernel in `(z, ξ)`
  have hKmeas : Measurable (fun q : Euc d × Euc d => 𝔨 q.1 * ‖1 - phase q.1 q.2‖ ^ 2) := by
    have := continuous_phase_uncurry (d := d)
    exact (hmeas.comp measurable_fst).mul (by fun_prop)
  have hKabs : Measurable (fun q : Euc d × Euc d => |𝔨 q.1| * ‖1 - phase q.1 q.2‖ ^ 2) := by
    have := continuous_phase_uncurry (d := d)
    exact (hmeas.comp measurable_fst).abs.mul (by fun_prop)
  -- the symbol identity
  have hsym : ∀ ξ : Euc d, Integrable (fun z => 𝔨 z * ‖1 - phase z ξ‖ ^ 2) ∧
      ∫ z, 𝔨 z * ‖1 - phase z ξ‖ ^ 2 = 2 * m ξ := by
    intro ξ
    have e : (fun z => 𝔨 z * ‖1 - phase z ξ‖ ^ 2) =
        fun z => 2 * (𝔨 z * (1 - Real.cos (2 * Real.pi * inner ℝ ξ z))) := by
      funext z; rw [norm_sq_eq_cos]; ring
    rw [e]
    exact ⟨(hs ξ).1.const_mul 2, by rw [integral_const_mul, (hs ξ).2]⟩
  obtain ⟨A, hA0, hA⟩ := scaling_bound hd hθ0 hθ2 hmeas hb
  -- integrability of `G`
  have hGint : Integrable G (volume : Measure (Euc d × Euc d)) := by
    have hGm : AEStronglyMeasurable G (volume : Measure (Euc d × Euc d)) := by
      refine (Complex.measurable_ofReal.comp hKmeas).aestronglyMeasurable.mul ?_
      exact hQ.aestronglyMeasurable.comp_snd
    rw [Measure.volume_eq_prod, integrable_prod_iff' (by rw [← Measure.volume_eq_prod]; exact hGm)]
    refine ⟨Eventually.of_forall fun ξ => ?_, ?_⟩
    · exact ((hsym ξ).1.ofReal).mul_const (Q ξ)
    · have hu2 : MemSobolev (θ / 2) u := memSobolev_mono (by linarith) hu
      have hv2 : MemSobolev (θ / 2) v := memSobolev_mono (by linarith) hv
      have hdom := (integrable_wt_Q hθ0 hu2 hv2).const_mul A
      have hnorm : ∀ z ξ : Euc d, ‖G (z, ξ)‖ = |𝔨 z| * ‖1 - phase z ξ‖ ^ 2 * ‖Q ξ‖ := by
        intro z ξ
        simp only [hGdef]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (sq_nonneg ‖1 - phase z ξ‖)]
      have hSn : ∀ ξ : Euc d, ∫ z, ‖G (z, ξ)‖ =
          (∫ z, |𝔨 z| * ‖1 - phase z ξ‖ ^ 2) * ‖Q ξ‖ := by
        intro ξ
        simp_rw [hnorm]
        exact integral_mul_const _ _
      refine Integrable.mono' hdom ?_ (Eventually.of_forall fun ξ => ?_)
      · have hS : StronglyMeasurable (fun ξ : Euc d => ∫ z, |𝔨 z| * ‖1 - phase z ξ‖ ^ 2) :=
          hKabs.stronglyMeasurable.integral_prod_left'
        have hQn : AEStronglyMeasurable (fun ξ : Euc d => ‖Q ξ‖) volume :=
          hQ.aestronglyMeasurable.norm
        have := hS.aestronglyMeasurable.mul hQn
        refine this.congr (Eventually.of_forall fun ξ => ?_)
        exact (hSn ξ).symm
      · have hS0 : 0 ≤ ∫ z, |𝔨 z| * ‖1 - phase z ξ‖ ^ 2 :=
          integral_nonneg fun z => mul_nonneg (abs_nonneg _) (sq_nonneg _)
        rw [hSn ξ, Real.norm_of_nonneg (mul_nonneg hS0 (norm_nonneg _))]
        have := (hA ξ).2
        change _ ≤ A * (wt ξ ^ (θ / 2) * ‖Q ξ‖)
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  have hGint' : Integrable G (volume.prod volume : Measure (Euc d × Euc d)) := by
    rwa [Measure.volume_eq_prod] at hGint
  have hint' : Integrable (fun p : Euc d × Euc d =>
      𝔨 p.2 * (u p.1 - u (p.1 - p.2)) * (v p.1 - v (p.1 - p.2))) (volume.prod volume) := by
    rwa [Measure.volume_eq_prod] at hint
  have hslice : ∀ z : Euc d,
      (((∫ x, 𝔨 z * (u x - u (x - z)) * (v x - v (x - z)) : ℝ)) : ℂ) = ∫ ξ, G (z, ξ) := by
    intro z
    have e : ∫ x, 𝔨 z * (u x - u (x - z)) * (v x - v (x - z)) =
        𝔨 z * ∫ x, (u x - u (x - z)) * (v x - v (x - z)) := by
      rw [← integral_const_mul]; congr 1; ext x; ring
    rw [e, Complex.ofReal_mul, slice_fourier hu.1 hv.1 z, ← integral_const_mul]
    congr 1; ext ξ
    simp only [hGdef, hQdef]; push_cast; ring
  have hI : (((∫ p : Euc d × Euc d,
      𝔨 p.2 * (u p.1 - u (p.1 - p.2)) * (v p.1 - v (p.1 - p.2)) : ℝ)) : ℂ) =
      ∫ ξ, ((2 * m ξ : ℝ) : ℂ) * Q ξ := by
    rw [Measure.volume_eq_prod, integral_prod_symm _ hint']
    calc (((∫ z, ∫ x, 𝔨 (x, z).2 * (u (x, z).1 - u ((x, z).1 - (x, z).2)) *
            (v (x, z).1 - v ((x, z).1 - (x, z).2)) : ℝ)) : ℂ)
        = ∫ z, (((∫ x, 𝔨 z * (u x - u (x - z)) * (v x - v (x - z)) : ℝ)) : ℂ) :=
          integral_complex_ofReal.symm
      _ = ∫ z, ∫ ξ, G (z, ξ) := integral_congr_ae (Eventually.of_forall hslice)
      _ = ∫ ξ, ∫ z, G (z, ξ) :=
          integral_integral_swap (f := fun z ξ => G (z, ξ)) hGint'
      _ = ∫ ξ, ((2 * m ξ : ℝ) : ℂ) * Q ξ := by
          refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
          simp only [hGdef]
          rw [integral_mul_const, integral_complex_ofReal, (hsym ξ).2]
  have hI2 : (∫ ξ, ((2 * m ξ : ℝ) : ℂ) * Q ξ) =
      2 * ∫ ξ, ((m ξ : ℝ) : ℂ) * Q ξ := by
    rw [← integral_const_mul]
    congr 1; ext ξ; push_cast; ring
  rw [hI2] at hI
  have hre := congrArg Complex.re hI
  rw [Complex.ofReal_re] at hre
  rw [symbolForm_eq_re]
  have : (2 * ∫ ξ, ((m ξ : ℝ) : ℂ) * Q ξ).re = 2 * (∫ ξ, ((m ξ : ℝ) : ℂ) * Q ξ).re := by simp
  rw [this] at hre
  rw [hre]; ring

end HRS.PDE.ToolboxRd.BilinAux
