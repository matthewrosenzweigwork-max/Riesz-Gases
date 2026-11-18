import HRS.MS.Mov63EAux6

/-!
# S6.3, packet N6 (part 7): global integration by parts and the weak-form integrand for `C_b²` tests

Namespace `HRS.MS.Mov63`, prefix `mne_`.  See `Mov63EAux1`.

* `mne_ibp_glob`: `∫ div Y · f = -∫ ⟨Y,∇f⟩` for `C¹` data with `div Y · f`, `⟨Y,∇f⟩`, `|f|‖Y‖` integrable (cutoffs `mnc_cut`).
* `mne_cb2_bounds`, `mne_J`: for `ψ ∈ C_b²`: `∫ div Y_u ψ = ∫ ρ_u (νΔψ - ⟨qx,∇ψ⟩) - ∫ ρ_u ⟨∇ψ,∇g*ρ_u⟩` (two global integrations by parts).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

section GlobIBP

lemma mne_cut_tendsto {F : Euc d → ℝ} (hF : Integrable F) :
    Tendsto (fun n : ℕ => ∫ x, mnc_cut d n x * F x) atTop (𝓝 (∫ x, F x)) := by
  refine tendsto_integral_of_dominated_convergence (fun x => |F x|) ?_ hF.abs ?_ ?_
  · intro n
    exact (((mnc_cut_smooth n).continuous.aestronglyMeasurable).mul hF.aestronglyMeasurable)
  · intro n
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mnc_cut_nonneg n x)]
    exact mul_le_of_le_one_left (abs_nonneg _) (mnc_cut_le_one n x)
  · refine Eventually.of_forall fun x => ?_
    refine tendsto_const_nhds.congr' ?_
    rw [EventuallyEq, eventually_atTop]
    refine ⟨⌈‖x‖⌉₊, fun n hn => ?_⟩
    have : ‖x‖ ≤ (n : ℝ) + 1 := by
      have h1 := Nat.le_ceil ‖x‖
      have h2 : ((⌈‖x‖⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    simp [mnc_cut_one n this]

/-- **Global integration by parts** for `C¹` data with the three integrability hypotheses. -/
theorem mne_ibp_glob {Y : Euc d → Euc d} {f : Euc d → ℝ} (hY : ContDiff ℝ 1 Y) (hf : ContDiff ℝ 1 f)
    (i1 : Integrable (fun x => movDiv Y x * f x)) (i2 : Integrable (fun x => inner ℝ (Y x) (gradient f x)))
    (i3 : Integrable (fun x => |f x| * ‖Y x‖)) :
    ∫ x, movDiv Y x * f x = -∫ x, inner ℝ (Y x) (gradient f x) := by
  obtain ⟨Cg, hCg0, hCg⟩ := mnc_cut_grad_bound (d := d)
  have hYc : Continuous Y := hY.continuous
  have hfc : Continuous f := hf.continuous
  -- the identity for each cutoff
  have key : ∀ n : ℕ, ∫ x, movDiv Y x * (mnc_cut d n x * f x) =
      -((∫ x, mnc_cut d n x * inner ℝ (Y x) (gradient f x)) +
        ∫ x, f x * inner ℝ (Y x) (gradient (mnc_cut d n) x)) := by
    intro n
    have hχ := mnc_cut_smooth (d := d) n
    have hχc := mnc_cut_cs (d := d) n
    have hg1 : ContDiff ℝ 1 (fun x => mnc_cut d n x * f x) := (hχ.of_le (by simp)).mul hf
    have hcs : HasCompactSupport (fun x => mnc_cut d n x * f x) := hχc.mul_right
    have h := mnc_ibp_div hY hg1 (Or.inl hcs)
    rw [h]
    congr 1
    have hdiff : ∀ x, inner ℝ (Y x) (gradient (fun y => mnc_cut d n y * f y) x) =
        mnc_cut d n x * inner ℝ (Y x) (gradient f x) + f x * inner ℝ (Y x) (gradient (mnc_cut d n) x) := by
      intro x
      rw [HRS.MS.PoisKolm.kl_inner_gradient, HRS.MS.PoisKolm.kl_inner_gradient, HRS.MS.PoisKolm.kl_inner_gradient]
      have hd1 : DifferentiableAt ℝ (mnc_cut d n) x := (hχ.differentiable (by simp)) x
      have hd2 : DifferentiableAt ℝ f x := (hf.differentiable (by norm_num)) x
      have h : fderiv ℝ (fun y => mnc_cut d n y * f y) x =
          mnc_cut d n x • fderiv ℝ f x + f x • fderiv ℝ (mnc_cut d n) x :=
        (hd1.hasFDerivAt.mul hd2.hasFDerivAt).fderiv
      rw [h]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    simp_rw [hdiff]
    have j1 : Integrable (fun x => mnc_cut d n x * inner ℝ (Y x) (gradient f x)) := by
      refine i2.norm.mono' ?_ (Eventually.of_forall fun x => ?_)
      · exact ((mnc_cut_smooth n).continuous.aestronglyMeasurable).mul i2.aestronglyMeasurable
      · rw [norm_mul, Real.norm_of_nonneg (mnc_cut_nonneg n x)]
        exact mul_le_of_le_one_left (norm_nonneg _) (mnc_cut_le_one n x)
    have gcs : HasCompactSupport (gradient (mnc_cut d n)) := mnc_grad_cs hχc
    have hgc : Continuous (gradient (mnc_cut d n)) := (HRS.MS.Gap.gap1_contDiff_gradient hχ 1).continuous
    have j2 : Integrable (fun x => f x * inner ℝ (Y x) (gradient (mnc_cut d n) x)) := by
      refine (hfc.mul (hYc.inner hgc)).integrable_of_hasCompactSupport ?_
      exact gcs.mono' (fun x hx => subset_tsupport _ (fun h0 => hx (by
        show f x * inner ℝ (Y x) (gradient (mnc_cut d n) x) = 0
        rw [h0, inner_zero_right, mul_zero])))
    exact integral_add j1 j2
  -- limits
  have L1 : Tendsto (fun n : ℕ => ∫ x, movDiv Y x * (mnc_cut d n x * f x)) atTop (𝓝 (∫ x, movDiv Y x * f x)) := by
    have := mne_cut_tendsto i1
    refine this.congr (fun n => ?_)
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  have L2 : Tendsto (fun n : ℕ => ∫ x, mnc_cut d n x * inner ℝ (Y x) (gradient f x)) atTop
      (𝓝 (∫ x, inner ℝ (Y x) (gradient f x))) := mne_cut_tendsto i2
  have L3 : Tendsto (fun n : ℕ => ∫ x, f x * inner ℝ (Y x) (gradient (mnc_cut d n) x)) atTop (𝓝 0) := by
    have hb : ∀ n : ℕ, |∫ x, f x * inner ℝ (Y x) (gradient (mnc_cut d n) x)| ≤
        (Cg / ((n : ℝ) + 1)) * ∫ x, |f x| * ‖Y x‖ := by
      intro n
      rw [← Real.norm_eq_abs]
      refine (norm_integral_le_integral_norm _).trans ?_
      rw [← integral_const_mul]
      refine integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _) (i3.const_mul _)
        (Eventually.of_forall fun x => ?_)
      show ‖f x * inner ℝ (Y x) (gradient (mnc_cut d n) x)‖ ≤ Cg / ((n : ℝ) + 1) * (|f x| * ‖Y x‖)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 : |inner ℝ (Y x) (gradient (mnc_cut d n) x)| ≤ ‖Y x‖ * (Cg / ((n : ℝ) + 1)) :=
        (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hCg n x) (norm_nonneg _))
      calc |f x| * |inner ℝ (Y x) (gradient (mnc_cut d n) x)| ≤ |f x| * (‖Y x‖ * (Cg / ((n : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = Cg / ((n : ℝ) + 1) * (|f x| * ‖Y x‖) := by ring
    have hlim : Tendsto (fun n : ℕ => (Cg / ((n : ℝ) + 1)) * ∫ x, |f x| * ‖Y x‖) atTop (𝓝 0) := by
      have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul Cg
      have h2 := h1.mul_const (∫ x, |f x| * ‖Y x‖)
      rw [mul_zero, zero_mul] at h2
      exact h2.congr (fun n => by ring)
    exact squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact hb n) hlim
  have hlim := L2.add L3
  have hlim2 := (hlim.neg)
  have := tendsto_nhds_unique L1 (hlim2.congr (fun n => (key n).symm))
  rw [this, add_zero]

end GlobIBP

section WeakJ

variable {m : ℕ} (hm : (d : ℝ) / 2 + 3 < m) (H : Mov2dTh d s β q ρ)

lemma mne_int_of_bound {F : Euc d → ℝ} {K : ℝ} (hF : Continuous F)
    (hb : ∀ x, |F x| ≤ K * (1 + ‖x‖) ^ (-((d : ℝ) + 1))) : Integrable F :=
  ((mne_integrableG (d := d)).const_mul K).mono' hF.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)

/-- Bounds of a `C_b²` test function. -/
lemma mne_cb2_bounds {ψ : Euc d → ℝ} (hψ : MemCb 2 ψ) :
    ∃ B0 B1 B2 : ℝ, 0 ≤ B0 ∧ 0 ≤ B1 ∧ 0 ≤ B2 ∧ (∀ x, |ψ x| ≤ B0) ∧ (∀ x, ‖gradient ψ x‖ ≤ B1) ∧
      (∀ x, |Laplacian.laplacian ψ x| ≤ B2) := by
  obtain ⟨⟨b0, hb0⟩, ⟨b1, hb1⟩, ⟨b2, hb2⟩⟩ : (BddAbove (Set.range fun x => ‖iteratedFDeriv ℝ 0 ψ x‖)) ∧
      (BddAbove (Set.range fun x => ‖iteratedFDeriv ℝ 1 ψ x‖)) ∧ (BddAbove (Set.range fun x => ‖iteratedFDeriv ℝ 2 ψ x‖)) :=
    ⟨hψ.2 0 (by norm_num), hψ.2 1 (by norm_num), hψ.2 2 (le_refl _)⟩
  have u0 : ∀ x, |ψ x| ≤ max b0 0 := fun x => by
    have : ‖iteratedFDeriv ℝ 0 ψ x‖ ≤ b0 := hb0 ⟨x, rfl⟩
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have u1 : ∀ x, ‖gradient ψ x‖ ≤ max b1 0 := fun x => by
    have : ‖iteratedFDeriv ℝ 1 ψ x‖ ≤ b1 := hb1 ⟨x, rfl⟩
    rw [norm_iteratedFDeriv_one, ← mnc_norm_gradient] at this
    exact this.trans (le_max_left _ _)
  have u2 : ∀ x, |Laplacian.laplacian ψ x| ≤ d * max b2 0 := fun x => by
    refine (mne_lap_bound _ x).trans ?_
    have h2 : ‖iteratedFDeriv ℝ 2 ψ x‖ ≤ b2 := hb2 ⟨x, rfl⟩
    exact mul_le_mul_of_nonneg_left (h2.trans (le_max_left _ _)) (Nat.cast_nonneg d)
  exact ⟨max b0 0, max b1 0, d * max b2 0, le_max_right _ _, le_max_right _ _,
    mul_nonneg (Nat.cast_nonneg d) (le_max_right _ _), u0, u1, u2⟩


lemma mne_abs_mul_le {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hA : 0 ≤ A) : |a * b| ≤ A * B := by
  rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) hA

include H in
/-- **The weak-form integrand as the integral of the flux divergence**, for `C_b²` test functions. -/
theorem mne_J {ψ : Euc d → ℝ} (hψ : MemCb 2 ψ) (u : OscSpace d (m : ℝ)) :
    ∫ x, movDiv (mneY d s q β ρ hm u) x * ψ x =
      (∫ x, mneRho ρ hm u x * (β⁻¹ * Laplacian.laplacian ψ x - inner ℝ (q • x : Euc d) (gradient ψ x))) +
        ∫ x, -(mneRho ρ hm u x * inner ℝ (gradient ψ x) (movForce d s (mneRho ρ hm u) x)) := by
  obtain ⟨KG, hKG0, hKG⟩ := mne_flux_bound hm H ‖u‖
  obtain ⟨B0, B1, B2, hB0, hB1, hB2, b0, b1, b2⟩ := mne_cb2_bounds hψ
  have hb := fun x => hKG u le_rfl x
  have hRcd := mne_rho_cd hm H u
  have hRc : Continuous (mneRho ρ hm u) := hRcd.continuous
  have hgR : Continuous (gradient (mneRho ρ hm u)) :=
    (mne_grad_cd (n := 2) (f := mneRho ρ hm u) (by exact_mod_cast hRcd)).continuous
  have hFc : Continuous (movForce d s (mneRho ρ hm u)) := (mne_Fr_cd hm H u).continuous
  have hYcd := mne_Y_cd hm H u
  have hYc : Continuous (mneY d s q β ρ hm u) := hYcd.continuous
  have hdivc : Continuous (movDiv (mneY d s q β ρ hm u)) := mne_movDiv_cont hYcd
  have hψ2 : ContDiff ℝ 2 ψ := hψ.1
  have hψ1 : ContDiff ℝ 1 ψ := hψ2.of_le (by norm_num)
  have hψc : Continuous ψ := hψ2.continuous
  have hgψcd : ContDiff ℝ 1 (gradient ψ) := mne_grad_cd (n := 1) (f := ψ) (by exact_mod_cast hψ2)
  have hgψ : Continuous (gradient ψ) := hgψcd.continuous
  have hlapψ : Continuous (Laplacian.laplacian ψ) := mne_lap_cont hψ2
  have hG0 : ∀ x : Euc d, 0 ≤ (1 + ‖x‖) ^ (-((d : ℝ) + 1)) := fun x => by positivity
  -- integrability for the first integration by parts (flux against ψ)
  have iA1 : Integrable (fun x => movDiv (mneY d s q β ρ hm u) x * ψ x) :=
    mne_int_of_bound (K := KG * B0) (hdivc.mul hψc) (fun x => by
      calc _ ≤ (KG * (1 + ‖x‖) ^ (-((d : ℝ) + 1))) * B0 :=
            mne_abs_mul_le (hb x).2.2.2.2.2.2 (b0 x) (mul_nonneg hKG0 (hG0 x))
        _ = _ := by ring)
  have iA2 : Integrable (fun x => inner ℝ (mneY d s q β ρ hm u x) (gradient ψ x)) :=
    mne_int_of_bound (K := KG * B1) (hYc.inner hgψ) (fun x => by
      refine (abs_real_inner_le_norm _ _).trans ?_
      calc _ ≤ (KG * (1 + ‖x‖) ^ (-((d : ℝ) + 1))) * B1 :=
            mul_le_mul (hb x).2.2.2.2.2.1 (b1 x) (norm_nonneg _) (mul_nonneg hKG0 (hG0 x))
        _ = _ := by ring)
  have iA3 : Integrable (fun x => |ψ x| * ‖mneY d s q β ρ hm u x‖) :=
    mne_int_of_bound (K := B0 * KG) (hψc.abs.mul hYc.norm) (fun x => by
      rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _))]
      calc _ ≤ B0 * (KG * (1 + ‖x‖) ^ (-((d : ℝ) + 1))) :=
            mul_le_mul (b0 x) (hb x).2.2.2.2.2.1 (norm_nonneg _) hB0
        _ = _ := by ring)
  have hA := mne_ibp_glob hYcd hψ1 iA1 iA2 iA3
  -- integrability for the second integration by parts (∇ψ against ρ_u)
  have hdivg : movDiv (gradient ψ) = Laplacian.laplacian ψ := funext fun x =>
    HRS.MS.S98.s98_movDiv_gradient hψ2 x
  have iB1 : Integrable (fun x => movDiv (gradient ψ) x * mneRho ρ hm u x) := by
    rw [hdivg]
    exact mne_int_of_bound (K := B2 * KG) (hlapψ.mul hRc) (fun x => by
      calc _ ≤ B2 * (KG * (1 + ‖x‖) ^ (-((d : ℝ) + 1))) :=
            mne_abs_mul_le (b2 x) (hb x).1 hB2
        _ = _ := by ring)
  have iB2 : Integrable (fun x => inner ℝ (gradient ψ x) (gradient (mneRho ρ hm u) x)) :=
    mne_int_of_bound (K := B1 * KG) (hgψ.inner hgR) (fun x => by
      refine (abs_real_inner_le_norm _ _).trans ?_
      calc _ ≤ B1 * (KG * (1 + ‖x‖) ^ (-((d : ℝ) + 1))) :=
            mul_le_mul (b1 x) (hb x).2.1 (norm_nonneg _) hB1
        _ = _ := by ring)
  have iB3 : Integrable (fun x => |mneRho ρ hm u x| * ‖gradient ψ x‖) :=
    mne_int_of_bound (K := KG * B1) (hRc.abs.mul hgψ.norm) (fun x => by
      rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _))]
      calc _ ≤ (KG * (1 + ‖x‖) ^ (-((d : ℝ) + 1))) * B1 :=
            mul_le_mul (hb x).1 (b1 x) (norm_nonneg _) (mul_nonneg hKG0 (hG0 x))
        _ = _ := by ring)
  have hB := mne_ibp_glob hgψcd (hRcd.of_le (by norm_num)) iB1 iB2 iB3
  rw [hdivg] at hB iB1
  -- the splitting of the flux pairing
  have j1 : Integrable (fun x => inner ℝ (gradient (mneRho ρ hm u) x) (gradient ψ x)) :=
    iB2.congr (Eventually.of_forall fun x => real_inner_comm _ _)
  have j2 : Integrable (fun x => mneRho ρ hm u x * inner ℝ (q • x : Euc d) (gradient ψ x)) :=
    mne_int_of_bound (K := |q| * B1 * KG) (hRc.mul ((continuous_id.const_smul q).inner hgψ)) (fun x => by
      rw [abs_mul]
      have h1 : |inner ℝ (q • x : Euc d) (gradient ψ x)| ≤ |q| * ‖x‖ * B1 := by
        refine (abs_real_inner_le_norm _ _).trans ?_
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (b1 x) (by positivity)
      calc |mneRho ρ hm u x| * |inner ℝ (q • x : Euc d) (gradient ψ x)| ≤
            |mneRho ρ hm u x| * (|q| * ‖x‖ * B1) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = (|q| * B1) * (|mneRho ρ hm u x| * ‖x‖) := by ring
        _ ≤ (|q| * B1) * (KG * (1 + ‖x‖) ^ (-((d : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left (hb x).2.2.2.1 (by positivity)
        _ = _ := by ring)
  have j3 : Integrable (fun x => mneRho ρ hm u x * inner ℝ (movForce d s (mneRho ρ hm u) x) (gradient ψ x)) :=
    mne_int_of_bound (K := B1 * KG) (hRc.mul (hFc.inner hgψ)) (fun x => by
      rw [abs_mul]
      have h1 : |inner ℝ (movForce d s (mneRho ρ hm u) x) (gradient ψ x)| ≤
          ‖movForce d s (mneRho ρ hm u) x‖ * B1 :=
        (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (b1 x) (norm_nonneg _))
      calc |mneRho ρ hm u x| * |inner ℝ (movForce d s (mneRho ρ hm u) x) (gradient ψ x)| ≤
            |mneRho ρ hm u x| * (‖movForce d s (mneRho ρ hm u) x‖ * B1) :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = B1 * (|mneRho ρ hm u x| * ‖movForce d s (mneRho ρ hm u) x‖) := by ring
        _ ≤ B1 * (KG * (1 + ‖x‖) ^ (-((d : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left (hb x).2.2.2.2.1 hB1
        _ = _ := by ring)
  have hpt : ∀ x, inner ℝ (mneY d s q β ρ hm u x) (gradient ψ x) =
      β⁻¹ * inner ℝ (gradient (mneRho ρ hm u) x) (gradient ψ x) +
        (mneRho ρ hm u x * inner ℝ (q • x : Euc d) (gradient ψ x) +
          mneRho ρ hm u x * inner ℝ (movForce d s (mneRho ρ hm u) x) (gradient ψ x)) := by
    intro x
    simp only [mneY, inner_add_left, inner_smul_left, conj_trivial]
    ring
  have hI : ∫ x, inner ℝ (mneY d s q β ρ hm u x) (gradient ψ x) =
      β⁻¹ * (∫ x, inner ℝ (gradient (mneRho ρ hm u) x) (gradient ψ x)) +
        ((∫ x, mneRho ρ hm u x * inner ℝ (q • x : Euc d) (gradient ψ x)) +
          ∫ x, mneRho ρ hm u x * inner ℝ (movForce d s (mneRho ρ hm u) x) (gradient ψ x)) := by
    simp_rw [hpt]
    have j23 : Integrable (fun x => mneRho ρ hm u x * inner ℝ (q • x : Euc d) (gradient ψ x) +
        mneRho ρ hm u x * inner ℝ (movForce d s (mneRho ρ hm u) x) (gradient ψ x)) := j2.add j3
    rw [integral_add (j1.const_mul _) j23, integral_add j2 j3, integral_const_mul]
  have hJ : ∫ x, Laplacian.laplacian ψ x * mneRho ρ hm u x =
      -∫ x, inner ℝ (gradient (mneRho ρ hm u) x) (gradient ψ x) := by
    rw [hB]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun x => real_inner_comm _ _)
  have hT1 : ∫ x, mneRho ρ hm u x * (β⁻¹ * Laplacian.laplacian ψ x - inner ℝ (q • x : Euc d) (gradient ψ x)) =
      β⁻¹ * (∫ x, Laplacian.laplacian ψ x * mneRho ρ hm u x) -
        ∫ x, mneRho ρ hm u x * inner ℝ (q • x : Euc d) (gradient ψ x) := by
    have e : ∀ x, mneRho ρ hm u x * (β⁻¹ * Laplacian.laplacian ψ x - inner ℝ (q • x : Euc d) (gradient ψ x)) =
        β⁻¹ * (Laplacian.laplacian ψ x * mneRho ρ hm u x) -
          mneRho ρ hm u x * inner ℝ (q • x : Euc d) (gradient ψ x) := fun x => by ring
    simp_rw [e]
    rw [integral_sub (iB1.const_mul _) j2, integral_const_mul]
  have hT2 : ∫ x, -(mneRho ρ hm u x * inner ℝ (gradient ψ x) (movForce d s (mneRho ρ hm u) x)) =
      -∫ x, mneRho ρ hm u x * inner ℝ (movForce d s (mneRho ρ hm u) x) (gradient ψ x) := by
    rw [← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun x => by dsimp only; rw [real_inner_comm])
  rw [hA, hI, hT1, hT2, hJ]
  ring

end WeakJ

end HRS.MS.Mov63

end
