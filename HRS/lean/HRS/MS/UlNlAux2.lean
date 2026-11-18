import HRS.MS.UlNlAux1

/-!
# UL-1 (S5.1 nonlocal term), part 2: the cancellation integration by parts

For `0 ≤ s < d`, `H = θ' g` (`g = rieszKernel d s`), `dH_i = θ' ∂_i g + ∂_iθ' g` and `ψ ∈ C¹_c`, `ψ(0) = 0`:
`∫ dH_i ψ = - ∫ H ∂_iψ` (`ul1_ibp`), by excising `B(0,ε)` with the cutoff `n1aΦ ε` (as `n1a_ibp_eps`);
the boundary term is `O(ε^{d-s'})`, `s' = (s+d)/2 < d`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.Ul

open HRS HRS.Whole HRS.MS.UniqN2a HRS.MS.UniqN0 HRS.MS.UniqN1a

variable {d : ℕ}

/-- `H = θ' g` -/
def ul1H (d : ℕ) (s : ℝ) (z : Euc d) : ℝ := ul1Th d z * rieszKernel d s z

/-- `∂_i H = θ' ∂_i g + ∂_iθ' g` (off the origin) -/
def ul1dH (d : ℕ) (s : ℝ) (i : Fin d) (z : Euc d) : ℝ :=
  ul1Th d z * kap d s i z + fderiv ℝ (ul1Th d) z (EuclideanSpace.single i 1) * rieszKernel d s z

theorem ul1_kap_eq (s : ℝ) (i : Fin d) (z : Euc d) :
    kap d s i z = fderiv ℝ (rieszKernel d s) z (EuclideanSpace.single i 1) := by
  simp only [kap, rieszKernelGrad]
  exact HRS.Whole.AppendixA.q09_gradient_apply _ _ _

theorem ul1_fderiv_th_zero' {z : Euc d} (hz : 1 / 4 ≤ ‖z‖) (v : Euc d) :
    fderiv ℝ (ul1Th d) z v = 0 := by
  have hmin : IsLocalMin (ul1Th d) z :=
    Filter.Eventually.of_forall fun w => by rw [ul1_th_zero hz]; exact ul1_th_nonneg w
  rw [hmin.fderiv_eq_zero]; rfl

theorem ul1_dH_zero {s : ℝ} (i : Fin d) {z : Euc d} (hz : 1 / 4 ≤ ‖z‖) : ul1dH d s i z = 0 := by
  simp [ul1dH, ul1_th_zero hz, ul1_fderiv_th_zero' hz]

theorem ul1_H_contDiffAt {s : ℝ} {z : Euc d} (hz : z ≠ 0) : ContDiffAt ℝ 1 (ul1H d s) z := by
  have h2 : ContDiffAt ℝ 1 (rieszKernel d s) z :=
    ((rieszKernel_contDiffOn (d := d) (s := s)).contDiffAt
      (isOpen_ne.mem_nhds (show z ∈ {x : Euc d | x ≠ 0} from hz))).of_le (by exact_mod_cast le_top)
  exact (ul1_th_contDiff.contDiffAt.of_le (by exact_mod_cast le_top)).mul h2

theorem ul1_fderiv_H {s : ℝ} (i : Fin d) {z : Euc d} (hz : z ≠ 0) :
    fderiv ℝ (ul1H d s) z (EuclideanSpace.single i 1) = ul1dH d s i z := by
  have h2 : ContDiffAt ℝ 1 (rieszKernel d s) z :=
    ((rieszKernel_contDiffOn (d := d) (s := s)).contDiffAt
      (isOpen_ne.mem_nhds (show z ∈ {x : Euc d | x ≠ 0} from hz))).of_le (by exact_mod_cast le_top)
  have h1 : DifferentiableAt ℝ (ul1Th d) z :=
    (ul1_th_contDiff.differentiable (by simp)) z
  have h3 := h1.hasFDerivAt.mul (h2.differentiableAt one_ne_zero).hasFDerivAt
  have : HasFDerivAt (ul1H d s) _ z := h3
  rw [this.fderiv]
  simp [ul1dH, ul1_kap_eq]
  ring

/-! ### Integrability -/

theorem ul1_H_integrable {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) : Integrable (ul1H d s) := by
  have := HRS.MS.Tc3.tc3_Gloc_integrable (d := d) ul1_th_contDiff.continuous ul1_th_compact hs0 hsd
  exact this

theorem ul1_ball_majorant {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    Integrable (ballF (d := d) s) := by
  rcases hs0.eq_or_lt with h | h
  · subst h
    have : ballF (d := d) 0 = (ball (0 : Euc d) 1).indicator (fun _ => (1 : ℝ)) := by
      funext z
      by_cases hz : ‖z‖ < 1
      · have : z ∈ ball (0 : Euc d) 1 := by simpa using hz
        simp [ballF, hz, this]
      · have : z ∉ ball (0 : Euc d) 1 := by simpa using hz
        simp [ballF, hz, this]
    rw [this]
    exact ind_ball_integrable
  · exact ballF_integrable h hsd

/-- a `C¹_c` function is globally Lipschitz -/
theorem ul1_lip_of_C1c {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    ∃ L : ℝ, 0 ≤ L ∧ (∀ z, ‖fderiv ℝ ψ z‖ ≤ L) ∧ ∀ z w, |ψ z - ψ w| ≤ L * ‖z - w‖ := by
  have hc : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv one_ne_zero
  have hs : HasCompactSupport (fderiv ℝ ψ) := hψc.fderiv (𝕜 := ℝ)
  obtain ⟨L0, hL0⟩ := hc.bounded_above_of_compact_support hs
  set L := max L0 0 with hL
  have hb : ∀ z, ‖fderiv ℝ ψ z‖ ≤ L := fun z => (hL0 z).trans (le_max_left _ _)
  refine ⟨L, le_max_right _ _, hb, fun z w => ?_⟩
  have hd : Differentiable ℝ ψ := hψ.differentiable one_ne_zero
  have hL' : LipschitzWith (Real.toNNReal L) ψ := by
    refine lipschitzWith_of_nnnorm_fderiv_le hd fun x => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (le_max_right _ _)]
    exact hb x
  have := hL'.dist_le_mul z w
  rwa [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (le_max_right _ _)] at this

/-- `|dH_i ψ|` is integrable for `ψ` Lipschitz, compactly supported, `ψ 0 = 0` -/
theorem ul1_dH_psi_integrable {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i : Fin d) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (h0 : ψ 0 = 0) :
    Integrable (fun z => ul1dH d s i z * ψ z) := by
  obtain ⟨L, hL0, -, hL⟩ := ul1_lip_of_C1c hψ hψc
  have hψz : ∀ z, |ψ z| ≤ L * ‖z‖ := fun z => by simpa [h0] using hL z 0
  -- the part `θ' ∂_i g ψ`
  have hA : Integrable (fun z => ul1Th d z * kap d s i z * ψ z) := by
    have hm := (ul1_ball_majorant (d := d) hs0 hsd).const_mul (max 1 s * L)
    refine hm.mono' ?_ ?_
    · exact ((ul1_th_contDiff.continuous.measurable.mul (kap_measurable s i)).mul
        hψ.continuous.measurable).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun z => ?_
      by_cases hz1 : 1 / 4 ≤ ‖z‖
      · simp [ul1_th_zero hz1, ballF]
        positivity
      · have hz1' : ‖z‖ < 1 / 4 := not_le.1 hz1
        by_cases hz0 : z = 0
        · subst hz0
          simp [h0, ballF]
          positivity
        · have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
          have hb := kap_bound hs0 i hz0
          have h1 : ‖z‖ ^ (-s - 1) * ‖z‖ = ‖z‖ ^ (-s) := by
            rw [← Real.rpow_add_one hn.ne']; congr 1; ring
          have hball : ballF (d := d) s z = ‖z‖ ^ (-s) := by simp [ballF, show ‖z‖ < 1 by linarith]
          rw [hball, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (ul1_th_nonneg z)]
          calc ul1Th d z * |kap d s i z| * |ψ z|
              ≤ 1 * (max 1 s * ‖z‖ ^ (-s - 1)) * (L * ‖z‖) := by
                gcongr
                · exact ul1_th_le_one z
                · exact hψz z
            _ = max 1 s * L * ‖z‖ ^ (-s) := by rw [← h1]; ring
  -- the part `∂_iθ' g ψ`
  have hB : Integrable (fun z => (fderiv ℝ (ul1Th d) z (EuclideanSpace.single i 1) * ψ z) *
      rieszKernel d s z) := by
    have hc : Continuous (fun z => fderiv ℝ (ul1Th d) z (EuclideanSpace.single i 1) * ψ z) :=
      ((ul1_th_contDiff.continuous_fderiv (by simp)).clm_apply continuous_const).mul hψ.continuous
    have hcs : HasCompactSupport (fun z => fderiv ℝ (ul1Th d) z (EuclideanSpace.single i 1) * ψ z) :=
      hψc.mul_left
    exact (rieszKernel_locallyIntegrable hs0 hsd).integrable_smul_left_of_hasCompactSupport hc hcs
  refine (hA.add hB).congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [ul1dH, Pi.add_apply]
  ring

theorem ul1_ae_ne_zero (hd : 0 < d) : ∀ᵐ z : Euc d ∂(volume : Measure (Euc d)), z ≠ 0 := by
  haveI : NeZero d := ⟨hd.ne'⟩
  haveI : Nontrivial (Euc d) := inferInstance
  have : (volume : Measure (Euc d)) {(0 : Euc d)} = 0 := measure_singleton 0
  simpa [ae_iff] using this

theorem ul1_H_measurable (s : ℝ) : Measurable (ul1H d s) :=
  ul1_th_contDiff.continuous.measurable.mul (HRS.MS.Tc3.tc3_measurable_riesz s)

theorem ul1_dH_measurable (s : ℝ) (i : Fin d) : Measurable (ul1dH d s i) := by
  unfold ul1dH
  have h1 : Continuous (fun z : Euc d => fderiv ℝ (ul1Th d) z (EuclideanSpace.single i 1)) :=
    (ul1_th_contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
  exact (ul1_th_contDiff.continuous.measurable.mul (kap_measurable s i)).add
    (h1.measurable.mul (HRS.MS.Tc3.tc3_measurable_riesz s))

/-- `|g z| ≤ A ‖z‖^{-s'}` for `0 < ‖z‖ ≤ 1`, `s' = (s+d)/2 < d` -/
theorem ul1_g_bound {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ z : Euc d, z ≠ 0 → ‖z‖ ≤ 1 →
      |rieszKernel d s z| ≤ A * ‖z‖ ^ (-((s + d) / 2)) := by
  have hs' : 0 < (s + d) / 2 := by
    have : (0 : ℝ) < d := lt_of_le_of_lt hs0 hsd
    linarith
  rcases hs0.eq_or_lt with h | h
  · subst h
    refine ⟨1 / ((0 + d) / 2), by positivity, fun z hz hz1 => ?_⟩
    have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hlog : Real.log ‖z‖ ≤ 0 := Real.log_nonpos hn.le hz1
    simp only [rieszKernel, ite_true]
    rw [abs_neg, abs_of_nonpos hlog, ← Real.log_inv]
    have := Real.log_le_rpow_div (inv_nonneg.2 hn.le) hs'
    rw [Real.inv_rpow hn.le, ← Real.rpow_neg hn.le] at this
    calc _ ≤ _ := this
      _ = _ := by ring
  · refine ⟨1, zero_le_one, fun z hz hz1 => ?_⟩
    have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hs0' : s ≠ 0 := h.ne'
    simp only [rieszKernel, hs0', ite_false, one_mul]
    rw [abs_of_nonneg (by positivity)]
    have hss : s ≤ (s + d) / 2 := by linarith
    exact Real.rpow_le_rpow_of_exponent_ge hn hz1 (by linarith)

/-- the exact identity at positive `ε` -/
theorem ul1_ibp_eps {s : ℝ} (i : Fin d) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) (h0 : ψ 0 = 0) {ε : ℝ} (hε : 0 < ε) :
    ∫ z, ul1H d s z * (fderiv ℝ (n1aΦ ε) z (EuclideanSpace.single i 1) * ψ z +
        n1aΦ ε z * fderiv ℝ ψ z (EuclideanSpace.single i 1)) =
      -∫ z, ul1dH d s i z * (n1aΦ ε z * ψ z) := by
  set F : Euc d → ℝ := fun z => n1aΦ ε z * ψ z with hFdef
  have hη : ContDiff ℝ 1 (n1aΦ (d := d) ε) := (n1aΦ_contDiff ε).of_le (by exact_mod_cast le_top)
  have hF : ContDiff ℝ 1 F := hη.mul hψ
  have hFc : HasCompactSupport F := hψc.mul_left
  have hsupp : tsupport F ⊆ {t | ε ≤ ‖t‖} := by
    refine closure_minimal (fun t ht => ?_) (isClosed_le continuous_const continuous_norm)
    by_contra h
    have h' : ‖t‖ < ε := not_le.1 h
    apply ht
    simp only [hFdef]
    rw [n1aΦ_zero hε h'.le, zero_mul]
  have hk : ∀ t ∈ tsupport F, ContDiffAt ℝ 1 (ul1H d s) t := by
    intro t ht
    refine ul1_H_contDiffAt (fun h => ?_)
    have := hsupp ht
    simp only [Set.mem_setOf_eq, h, norm_zero] at this
    linarith
  have key := n0_ibp hF hFc hk (EuclideanSpace.single i (1 : ℝ))
  have e1 : ∀ t, fderiv ℝ F t (EuclideanSpace.single i 1) =
      fderiv ℝ (n1aΦ ε) t (EuclideanSpace.single i 1) * ψ t +
        n1aΦ ε t * fderiv ℝ ψ t (EuclideanSpace.single i 1) := by
    intro t
    rw [hFdef, fderiv_fun_mul (hη.differentiable one_ne_zero t) (hψ.differentiable one_ne_zero t)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have e2 : ∀ t, fderiv ℝ (ul1H d s) t (EuclideanSpace.single i 1) * F t = ul1dH d s i t * F t := by
    intro t
    by_cases ht : t = 0
    · subst ht; simp [hFdef, h0]
    · rw [ul1_fderiv_H i ht]
  simp_rw [e1] at key
  simp_rw [e2] at key
  exact key

/-- `ψ`-quantities used below -/
theorem ul1_ibp {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i : Fin d) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (h0 : ψ 0 = 0) :
    ∫ z, ul1dH d s i z * ψ z =
      -∫ z, ul1H d s z * fderiv ℝ ψ z (EuclideanSpace.single i 1) := by
  have hd : 0 < d := by
    have : (0 : ℝ) < d := lt_of_le_of_lt hs0 hsd
    exact_mod_cast this
  obtain ⟨L, hL0, hLd, hLl⟩ := ul1_lip_of_C1c hψ hψc
  obtain ⟨A, hA0, hA⟩ := ul1_g_bound hs0 hsd
  obtain ⟨Lη, hLη0, hLη⟩ := n1a_bump_fderiv_bound (d := d)
  set e : Euc d := EuclideanSpace.single i 1 with he
  have hψz : ∀ z, |ψ z| ≤ L * ‖z‖ := fun z => by simpa [h0] using hLl z 0
  have hψ' : ∀ z, |fderiv ℝ ψ z e| ≤ L := fun z => by
    have := (fderiv ℝ ψ z).le_opNorm e
    have h1 : ‖e‖ = 1 := by simp [he]
    rw [h1, mul_one] at this
    exact (Real.norm_eq_abs _ ▸ this).trans (hLd z)
  have hψb : ∃ Bψ, ∀ z, |ψ z| ≤ Bψ := by
    obtain ⟨B, hB⟩ := hψ.continuous.bounded_above_of_compact_support hψc
    exact ⟨B, fun z => by simpa using hB z⟩
  obtain ⟨Bψ, hBψ⟩ := hψb
  set Hf := ul1H d s with hHf
  have hHint : Integrable Hf := ul1_H_integrable hs0 hsd
  have hHm := ul1_H_measurable (d := d) s
  have hdHψ := ul1_dH_psi_integrable hs0 hsd i hψ hψc h0
  have hψ'c : Continuous (fun z => fderiv ℝ ψ z e) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hηc : ∀ ε : ℝ, Continuous (n1aΦ (d := d) ε) := fun ε => (n1aΦ_contDiff ε).continuous
  have hηd : ∀ ε : ℝ, Continuous (fun z : Euc d => fderiv ℝ (n1aΦ ε) z e) := fun ε =>
    ((n1aΦ_contDiff (d := d) ε).continuous_fderiv (by simp)).clm_apply continuous_const
  have hηb : ∀ ε : ℝ, 0 < ε → ∀ z : Euc d, |fderiv ℝ (n1aΦ ε) z e| ≤ Lη * ε⁻¹ := by
    intro ε hε z
    have h1 := n1aΦ_fderiv_bound hLη hε z
    have h2 := (fderiv ℝ (n1aΦ (d := d) ε) z).le_opNorm e
    have h3 : ‖e‖ = 1 := by simp [he]
    rw [h3, mul_one] at h2
    exact (Real.norm_eq_abs _ ▸ h2).trans h1
  set l : Filter ℝ := 𝓝[>] 0 with hl
  have hlev : ∀ᶠ ε in l, 0 < ε := self_mem_nhdsWithin
  -- pointwise convergence of the cutoff
  have hηlim : ∀ z : Euc d, z ≠ 0 → Tendsto (fun ε => n1aΦ (d := d) ε z) l (𝓝 1) := by
    intro z hz
    have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ‖z‖ / 2 by positivity)] with ε hε'
    exact (n1aΦ_one hε'.1 (by linarith [hε'.2])).symm
  have hae := ul1_ae_ne_zero hd
  -- the three limits
  have hA_lim : Tendsto (fun ε => ∫ z, Hf z * (n1aΦ ε z * fderiv ℝ ψ z e)) l
      (𝓝 (∫ z, Hf z * fderiv ℝ ψ z e)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun z => |Hf z| * L) ?_ ?_ ?_ ?_
    · filter_upwards with ε
      exact (hHm.mul ((hηc ε).measurable.mul hψ'c.measurable)).aestronglyMeasurable
    · filter_upwards [hlev] with ε hε
      refine Filter.Eventually.of_forall fun z => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have h1 : |n1aΦ ε z| ≤ 1 := by
        rw [abs_of_nonneg (n1aΦ_nonneg ε z)]; exact n1aΦ_le_one ε z
      calc |Hf z| * (|n1aΦ ε z| * |fderiv ℝ ψ z e|) ≤ |Hf z| * (1 * L) := by
            gcongr; exact hψ' z
        _ = _ := by ring
    · exact hHint.abs.mul_const L
    · filter_upwards [hae] with z hz
      have := ((hηlim z hz).mul_const (fderiv ℝ ψ z e)).const_mul (Hf z)
      simpa using this
  have hC_lim : Tendsto (fun ε => ∫ z, ul1dH d s i z * (n1aΦ ε z * ψ z)) l
      (𝓝 (∫ z, ul1dH d s i z * ψ z)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun z => |ul1dH d s i z * ψ z|) ?_ ?_ ?_ ?_
    · filter_upwards with ε
      exact ((ul1_dH_measurable s i).mul ((hηc ε).measurable.mul hψ.continuous.measurable)).aestronglyMeasurable
    · filter_upwards [hlev] with ε hε
      refine Filter.Eventually.of_forall fun z => ?_
      have h1 : |n1aΦ ε z| ≤ 1 := by
        rw [abs_of_nonneg (n1aΦ_nonneg ε z)]; exact n1aΦ_le_one ε z
      have : ul1dH d s i z * (n1aΦ ε z * ψ z) = (ul1dH d s i z * ψ z) * n1aΦ ε z := by ring
      rw [Real.norm_eq_abs, this, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) h1
    · exact hdHψ.abs
    · filter_upwards [hae] with z hz
      have := ((hηlim z hz).mul_const (ψ z)).const_mul (ul1dH d s i z)
      simpa [mul_assoc] using this
  have hB_lim : Tendsto (fun ε => ∫ z, Hf z * (fderiv ℝ (n1aΦ ε) z e * ψ z)) l (𝓝 0) := by
    have hp : (0 : ℝ) < (d : ℝ) - (s + d) / 2 := by linarith
    set V : ℝ := volume.real (closedBall (0 : Euc d) 1) with hV
    set C0 : ℝ := (2 * A * Lη * L) * (2 ^ d * V) with hC0
    have hbound : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        ‖∫ z, Hf z * (fderiv ℝ (n1aΦ ε) z e * ψ z)‖ ≤ C0 * ε ^ ((d : ℝ) - (s + d) / 2) := by
      intro ε hε hε2
      set S : Set (Euc d) := closedBall 0 (2 * ε) with hS
      have hsupp : ∀ z, z ∉ S → Hf z * (fderiv ℝ (n1aΦ ε) z e * ψ z) = 0 := by
        intro z hz
        have : 2 * ε < ‖z‖ := by simpa [hS, mem_closedBall_zero_iff] using hz
        rw [n1aΦ_fderiv_zero_out hε this]; simp
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
      have hCnn : 0 ≤ 2 * A * Lη * L * ε ^ (-((s + d) / 2)) := by positivity
      have hpt : ∀ z ∈ S, ‖Hf z * (fderiv ℝ (n1aΦ ε) z e * ψ z)‖ ≤
          2 * A * Lη * L * ε ^ (-((s + d) / 2)) := by
        intro z hz
        have hzS : ‖z‖ ≤ 2 * ε := by simpa [hS, mem_closedBall_zero_iff] using hz
        by_cases hzε : ‖z‖ < ε
        · rw [n1aΦ_fderiv_zero_in hε hzε]; simpa using hCnn
        · have hzε' : ε ≤ ‖z‖ := not_lt.1 hzε
          have hz0 : z ≠ 0 := by
            intro h; rw [h, norm_zero] at hzε'; linarith
          have hg := hA z hz0 (by linarith)
          have hHle : |Hf z| ≤ A * ε ^ (-((s + d) / 2)) := by
            have h1 : |Hf z| ≤ |rieszKernel d s z| := by
              simp only [hHf, ul1H, abs_mul]
              exact mul_le_of_le_one_left (abs_nonneg _) (by
                rw [abs_of_nonneg (ul1_th_nonneg z)]; exact ul1_th_le_one z)
            have h2 : ‖z‖ ^ (-((s + d) / 2)) ≤ ε ^ (-((s + d) / 2)) :=
              Real.rpow_le_rpow_of_nonpos hε hzε' (by linarith)
            exact h1.trans (hg.trans (mul_le_mul_of_nonneg_left h2 hA0))
          have hη1 := hηb ε hε z
          have hψ1 : |ψ z| ≤ L * (2 * ε) := (hψz z).trans (mul_le_mul_of_nonneg_left hzS hL0)
          rw [Real.norm_eq_abs, abs_mul, abs_mul]
          have hεp : 0 ≤ ε ^ (-((s + d) / 2)) := by positivity
          calc |Hf z| * (|fderiv ℝ (n1aΦ ε) z e| * |ψ z|)
              ≤ (A * ε ^ (-((s + d) / 2))) * ((Lη * ε⁻¹) * (L * (2 * ε))) := by
                gcongr
            _ = 2 * A * Lη * L * ε ^ (-((s + d) / 2)) := by field_simp
      have hSfin : volume S < ⊤ := measure_closedBall_lt_top
      refine (norm_setIntegral_le_of_norm_le_const hSfin hpt).trans ?_
      rw [hS, Measure.real, Measure.addHaar_closedBall' _ _ (by positivity)]
      simp only [finrank_euclideanSpace, Fintype.card_fin]
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
      have hVV : (volume (closedBall (0 : Euc d) 1)).toReal = V := rfl
      rw [hVV, show ε ^ ((d : ℝ) - (s + d) / 2) = ε ^ (-((s + d) / 2)) * ε ^ d by
        rw [← Real.rpow_natCast, ← Real.rpow_add hε]; congr 1; ring, hC0, mul_pow]
      ring_nf
      exact le_rfl
    refine squeeze_zero_norm' (a := fun ε => C0 * ε ^ ((d : ℝ) - (s + d) / 2)) ?_ ?_
    · filter_upwards [hlev, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε hε2
      exact hbound ε hε hε2.2.le
    · have h1 : Tendsto (fun ε : ℝ => ε ^ ((d : ℝ) - (s + d) / 2)) (𝓝 0) (𝓝 0) := by
        have := (Real.continuous_rpow_const hp.le).tendsto 0
        rwa [Real.zero_rpow hp.ne'] at this
      simpa using (tendsto_nhdsWithin_of_tendsto_nhds h1).const_mul C0
  -- combine
  have hid : ∀ᶠ ε in l, (∫ z, Hf z * (n1aΦ ε z * fderiv ℝ ψ z e)) +
      (∫ z, Hf z * (fderiv ℝ (n1aΦ ε) z e * ψ z)) = -∫ z, ul1dH d s i z * (n1aΦ ε z * ψ z) := by
    filter_upwards [hlev] with ε hε
    have h := ul1_ibp_eps (s := s) i hψ hψc h0 hε
    have hAi : Integrable (fun z => Hf z * (n1aΦ ε z * fderiv ℝ ψ z e)) :=
      hHint.mul_bdd (c := 1 * L) ((hηc ε).mul hψ'c).aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs, abs_mul]
          have h1 : |n1aΦ ε z| ≤ 1 := by
            rw [abs_of_nonneg (n1aΦ_nonneg ε z)]; exact n1aΦ_le_one ε z
          exact mul_le_mul h1 (hψ' z) (abs_nonneg _) zero_le_one)
    have hBi : Integrable (fun z => Hf z * (fderiv ℝ (n1aΦ ε) z e * ψ z)) :=
      hHint.mul_bdd (c := (Lη * ε⁻¹) * Bψ) ((hηd ε).mul hψ.continuous).aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hηb ε hε z) (hBψ z) (abs_nonneg _) (by positivity))
    rw [← h]
    simp_rw [mul_add]
    rw [integral_add hBi hAi, add_comm]
  have hlim2 := (hA_lim.add hB_lim)
  have hlim3 := hC_lim.neg
  have := tendsto_nhds_unique (hlim2.congr' hid) hlim3
  simp only [add_zero] at this
  linarith

/-! ### The decomposition of the cancellation convolution -/

theorem ul1_K_formula (s : ℝ) (i : Fin d) (z : Euc d) :
    ul1K d s i z = (1 - ul1Th d z) * kap d s i z -
      fderiv ℝ (ul1Th d) z (EuclideanSpace.single i 1) * rieszKernel d s z := by
  by_cases hz : z = 0
  · subst hz
    have hev : ul1Gh d s =ᶠ[𝓝 (0 : Euc d)] fun _ => 0 := by
      filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds
        (show ‖(0 : Euc d)‖ < 1 / 8 by simp)] with w hw
      simp [ul1Gh, ul1_th_one hw.le]
    have h1 : fderiv ℝ (ul1Gh d s) 0 = 0 := by rw [hev.fderiv_eq]; simp
    simp [ul1K, h1, ul1_th_one (show ‖(0 : Euc d)‖ ≤ 1 / 8 by simp),
      ul1_fderiv_th_zero (show ‖(0 : Euc d)‖ < 1 / 8 by simp)]
  · have h2 : ContDiffAt ℝ 1 (rieszKernel d s) z :=
      ((rieszKernel_contDiffOn (d := d) (s := s)).contDiffAt
        (isOpen_ne.mem_nhds (show z ∈ {x : Euc d | x ≠ 0} from hz))).of_le (by exact_mod_cast le_top)
    have h1 : DifferentiableAt ℝ (ul1Th d) z := (ul1_th_contDiff.differentiable (by simp)) z
    have h3 := (h1.hasFDerivAt.const_sub 1).mul (h2.differentiableAt one_ne_zero).hasFDerivAt
    have h4 : HasFDerivAt (ul1Gh d s) _ z := h3
    simp only [ul1K]
    rw [h4.fderiv]
    simp [ul1_kap_eq]
    ring

theorem ul1_K_bdd {s : ℝ} (hs0 : 0 ≤ s) (i : Fin d) : ∃ B : ℝ, ∀ z, |ul1K d s i z| ≤ B := by
  obtain ⟨B, hB⟩ := ul1_K_deriv_bdd hs0 i 0
  exact ⟨B, fun z => by simpa using hB z⟩

/-- the cutoff `≡ 1` on `B̄(0,1/2)` -/
def ul1B2 (d : ℕ) : ContDiffBump (0 : Euc d) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

theorem ul1_odd_integral {f : Euc d → ℝ} (hf : ∀ z, f (-z) = - f z) : ∫ z, f z = 0 := by
  have h := integral_neg_eq_self f (volume : Measure (Euc d))
  simp only [hf, integral_neg] at h
  linarith

/-- the indicator of `‖z‖ ≤ 1/4` -/
def ul1Ind (d : ℕ) (z : Euc d) : ℝ := if ‖z‖ ≤ 1 / 4 then 1 else 0

theorem ul1_kap_far_bound {s : ℝ} (hs0 : 0 ≤ s) (i : Fin d) {z : Euc d} (hz : 1 / 8 ≤ ‖z‖) :
    |kap d s i z| ≤ max 1 s * 8 ^ (s + 1) := by
  have hn : 0 < ‖z‖ := by linarith
  have h := kap_bound hs0 i (norm_pos_iff.1 hn)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (le_trans zero_le_one (le_max_left _ _)))
  have h3 : ‖z‖ ^ (-s - 1) ≤ (1 / 8) ^ (-s - 1) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hz (by linarith)
  have h4 : ((1 : ℝ) / 8) ^ (-s - 1) = 8 ^ (s + 1) := by
    rw [Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow,
      show -s - 1 = -(s + 1) by ring, Real.rpow_neg (by norm_num)]
    simp
  rwa [h4] at h3

theorem ul1_P4_integrable {s : ℝ} (hs0 : 0 ≤ s) (i : Fin d) :
    Integrable (fun z => (ul1Ind d z - ul1Th d z) * kap d s i z) := by
  have hm : Measurable (fun z : Euc d => (ul1Ind d z - ul1Th d z) * kap d s i z) := by
    have : Measurable (ul1Ind d) := by
      unfold ul1Ind
      exact Measurable.ite (measurableSet_le measurable_norm measurable_const) measurable_const
        measurable_const
    exact (this.sub ul1_th_contDiff.continuous.measurable).mul (kap_measurable s i)
  have hi : Integrable ((ball (0 : Euc d) 1).indicator (fun _ => max 1 s * 8 ^ (s + 1))) :=
    (integrable_indicator_iff measurableSet_ball).2 (integrableOn_const measure_ball_lt_top.ne)
  refine hi.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  by_cases h1 : 1 / 8 ≤ ‖z‖
  · by_cases h2 : ‖z‖ ≤ 1 / 4
    · have hz : z ∈ ball (0 : Euc d) 1 := by simp; linarith
      rw [Set.indicator_of_mem hz, Real.norm_eq_abs, abs_mul]
      have h3 : |ul1Ind d z - ul1Th d z| ≤ 1 := by
        have := ul1_th_nonneg z; have := ul1_th_le_one z
        simp only [ul1Ind, h2, if_true]
        rw [abs_le]; constructor <;> linarith
      calc _ ≤ 1 * (max 1 s * 8 ^ (s + 1)) :=
            mul_le_mul h3 (ul1_kap_far_bound hs0 i h1) (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    · have h2' : 1 / 4 ≤ ‖z‖ := (not_le.1 h2).le
      have h0 : (ul1Ind d z - ul1Th d z) * kap d s i z = 0 := by
        have hI : ul1Ind d z = 0 := by simp only [ul1Ind]; rw [if_neg h2]
        rw [hI, ul1_th_zero h2']; ring
      rw [h0, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => by positivity) z
  · have h1' : ‖z‖ < 1 / 8 := not_le.1 h1
    have hz : ‖z‖ ≤ 1 / 4 := by linarith
    have h0 : (ul1Ind d z - ul1Th d z) * kap d s i z = 0 := by
      have hI : ul1Ind d z = 1 := by simp only [ul1Ind]; rw [if_pos hz]
      rw [hI, ul1_th_one h1'.le]; ring
    rw [h0, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => by positivity) z

theorem ul1_P3_integrable {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i : Fin d) :
    Integrable (fun z => fderiv ℝ (ul1Th d) z (EuclideanSpace.single i 1) * rieszKernel d s z) := by
  have hc : Continuous (fun z : Euc d => fderiv ℝ (ul1Th d) z (EuclideanSpace.single i 1)) :=
    (ul1_th_contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcs : HasCompactSupport (fun z : Euc d => fderiv ℝ (ul1Th d) z (EuclideanSpace.single i 1)) :=
    (ul1_th_compact.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Euc d →L[ℝ] ℝ => L (EuclideanSpace.single i 1))
      (by simp)
  exact (rieszKernel_locallyIntegrable hs0 hsd).integrable_smul_left_of_hasCompactSupport hc hcs

theorem ul1_decomp {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i : Fin d) {F : Euc d → ℝ}
    (hF : ContDiff ℝ 1 F) (hFi : Integrable F) (x : Euc d) :
    ∫ y, (if ‖x - y‖ ≤ 1 / 4 then (F y - F x) * kap d s i (x - y) else F y * kap d s i (x - y)) =
      (∫ z, ul1H d s z * fderiv ℝ F (x - z) (EuclideanSpace.single i 1)) +
        ∫ z, ul1K d s i z * F (x - z) := by
  set e : Euc d := EuclideanSpace.single i 1 with he
  set φ : Euc d → ℝ := fun z => F (x - z) - F x with hφ
  set ψ : Euc d → ℝ := fun z => ul1B2 d z * φ z with hψ
  have hφd : ContDiff ℝ 1 φ := (hF.comp (contDiff_const.sub contDiff_id)).sub contDiff_const
  have hψd : ContDiff ℝ 1 ψ := ((ul1B2 d).contDiff (n := 1)).mul hφd
  have hψc : HasCompactSupport ψ := (ul1B2 d).hasCompactSupport.mul_right
  have hψ0 : ψ 0 = 0 := by simp [hψ, hφ]
  have hψφ : ∀ z : Euc d, ‖z‖ < 1 / 2 → ψ =ᶠ[𝓝 z] φ := by
    intro z hz
    filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds hz] with w hw
    simp only [hψ, (ul1B2 d).one_of_mem_closedBall (by simpa [ul1B2] using hw.le), one_mul]
  -- the integral over `y`
  set Φ : Euc d → ℝ := fun z => if ‖z‖ ≤ 1 / 4 then φ z * kap d s i z else F (x - z) * kap d s i z
    with hΦ
  have e1 : ∫ y, (if ‖x - y‖ ≤ 1 / 4 then (F y - F x) * kap d s i (x - y) else
      F y * kap d s i (x - y)) = ∫ z, Φ z := by
    rw [← integral_sub_left_eq_self Φ volume x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hΦ, hφ, sub_sub_cancel]
  rw [e1]
  -- pieces
  have hFx : Integrable (fun z => F (x - z)) := hFi.comp_sub_left x
  have hP1 : Integrable (fun z => ul1dH d s i z * φ z) := by
    have := ul1_dH_psi_integrable hs0 hsd i hψd hψc hψ0
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    by_cases hz : 1 / 4 ≤ ‖z‖
    · simp [ul1_dH_zero i hz]
    · have hz' : ‖z‖ < 1 / 2 := by linarith [not_le.1 hz]
      simp only [hψ, (ul1B2 d).one_of_mem_closedBall (by simpa [ul1B2] using hz'.le), one_mul]
  have hP2 : Integrable (fun z => ul1K d s i z * F (x - z)) := by
    obtain ⟨B, hB⟩ := ul1_K_bdd hs0 i
    exact hFx.bdd_mul (ul1_K_contDiff s i).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by simpa using hB z)
  have hP3 := ul1_P3_integrable hs0 hsd i
  have hP4 := ul1_P4_integrable hs0 i
  have hpt : ∀ z, Φ z = ul1dH d s i z * φ z + ul1K d s i z * F (x - z) +
      (F x * (fderiv ℝ (ul1Th d) z e * rieszKernel d s z) -
        F x * ((ul1Ind d z - ul1Th d z) * kap d s i z)) := by
    intro z
    rw [ul1_K_formula]
    simp only [hΦ, ul1dH, ul1Ind, hφ]
    split_ifs <;> ring
  have hsum : ∫ z, Φ z = (∫ z, ul1dH d s i z * φ z) + (∫ z, ul1K d s i z * F (x - z)) +
      (F x * (∫ z, fderiv ℝ (ul1Th d) z e * rieszKernel d s z) -
        F x * (∫ z, (ul1Ind d z - ul1Th d z) * kap d s i z)) := by
    have hP12 : Integrable (fun z => ul1dH d s i z * φ z + ul1K d s i z * F (x - z)) := hP1.add hP2
    have hP34 : Integrable (fun z => F x * (fderiv ℝ (ul1Th d) z e * rieszKernel d s z) -
        F x * ((ul1Ind d z - ul1Th d z) * kap d s i z)) :=
      (hP3.const_mul (F x)).sub (hP4.const_mul (F x))
    simp_rw [hpt]
    rw [integral_add hP12 hP34, integral_add hP1 hP2,
      integral_sub (hP3.const_mul (F x)) (hP4.const_mul (F x)), integral_const_mul,
      integral_const_mul]
  have hz3 : ∫ z, fderiv ℝ (ul1Th d) z e * rieszKernel d s z = 0 :=
    ul1_odd_integral fun z => by
      rw [ul1_fderiv_th_neg, rieszKernel_neg]; ring
  have hz4 : ∫ z, (ul1Ind d z - ul1Th d z) * kap d s i z = 0 :=
    ul1_odd_integral fun z => by
      have : ul1Ind d (-z) = ul1Ind d z := by simp [ul1Ind]
      rw [this, ul1_th_neg, kap_neg]; ring
  rw [hsum, hz3, hz4]
  -- integration by parts
  have hibp := ul1_ibp hs0 hsd i hψd hψc hψ0
  have hl : ∫ z, ul1dH d s i z * φ z = ∫ z, ul1H d s z * fderiv ℝ F (x - z) e := by
    have h1 : ∫ z, ul1dH d s i z * φ z = ∫ z, ul1dH d s i z * ψ z := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      by_cases hz : 1 / 4 ≤ ‖z‖
      · simp [ul1_dH_zero i hz]
      · have hz' : ‖z‖ < 1 / 2 := by linarith [not_le.1 hz]
        simp only [hψ, (ul1B2 d).one_of_mem_closedBall (by simpa [ul1B2] using hz'.le), one_mul]
    rw [h1, hibp, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    beta_reduce
    by_cases hz : 1 / 4 ≤ ‖z‖
    · simp [ul1H, ul1_th_zero hz]
    · have hz' : ‖z‖ < 1 / 2 := by linarith [not_le.1 hz]
      rw [(hψφ z hz').fderiv_eq]
      have hd : HasFDerivAt φ ((fderiv ℝ F (x - z)).comp (0 - ContinuousLinearMap.id ℝ (Euc d))) z :=
        ((hF.differentiable one_ne_zero) (x - z)).hasFDerivAt.comp z
          ((hasFDerivAt_const x z).sub (hasFDerivAt_id z)) |>.sub_const (F x)
      rw [hd.fderiv]
      simp [he]
  rw [hl]
  ring

/-! ### Integrability of the cancellation integrand and the vector decomposition -/

theorem ul1_lip_near {F : Euc d → ℝ} (hF : ContDiff ℝ 1 F) (x : Euc d) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ y, ‖x - y‖ ≤ 1 / 4 → |F y - F x| ≤ L * ‖x - y‖ := by
  have hc : Continuous (fderiv ℝ F) := hF.continuous_fderiv one_ne_zero
  obtain ⟨L0, hL0⟩ := (isCompact_closedBall x (1 / 4)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max L0 0, le_max_right _ _, fun y hy => ?_⟩
  have hyB : y ∈ closedBall x (1 / 4) := by rw [mem_closedBall, dist_comm, dist_eq_norm]; exact hy
  have := (convex_closedBall x (1 / 4)).norm_image_sub_le_of_norm_fderiv_le (C := max L0 0)
    (fun w _ => hF.differentiable one_ne_zero w) (fun w hw => (hL0 w hw).trans (le_max_left _ _))
    (mem_closedBall_self (by norm_num)) hyB
  rw [Real.norm_eq_abs] at this
  rw [norm_sub_rev] at this
  exact this

theorem ul1_comp_integrable {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (k : Fin d) {F : Euc d → ℝ}
    (hF : ContDiff ℝ 1 F) (hFi : Integrable F) (x : Euc d) :
    Integrable (fun y => if ‖x - y‖ ≤ 1 / 4 then (F y - F x) * kap d s k (x - y)
      else F y * kap d s k (x - y)) := by
  obtain ⟨L, hL0, hL⟩ := ul1_lip_near hF x
  have hmeasI : MeasurableSet {y : Euc d | ‖x - y‖ ≤ 1 / 4} :=
    measurableSet_le (measurable_const.sub measurable_id).norm measurable_const
  have hk : Measurable (fun y : Euc d => kap d s k (x - y)) :=
    (kap_measurable s k).comp (measurable_const.sub measurable_id)
  have hFm : Measurable F := hF.continuous.measurable
  have hball_nn : ∀ w : Euc d, 0 ≤ ballF (d := d) s w := fun w => by
    unfold ballF; split_ifs <;> positivity
  -- near part
  have hnear : Integrable (fun y => if ‖x - y‖ ≤ 1 / 4 then (F y - F x) * kap d s k (x - y) else 0) := by
    have hm := ((ul1_ball_majorant (d := d) hs0 hsd).comp_sub_left x).const_mul (max 1 s * L)
    refine hm.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact (Measurable.ite hmeasI ((hFm.sub measurable_const).mul hk) measurable_const).aestronglyMeasurable
    · by_cases hy : ‖x - y‖ ≤ 1 / 4
      · simp only [hy, if_true]
        by_cases hy0 : x - y = 0
        · have : y = x := by rw [sub_eq_zero] at hy0; exact hy0.symm
          subst this
          simp only [sub_self]
          rw [zero_mul, norm_zero]
          exact mul_nonneg (mul_nonneg (le_trans zero_le_one (le_max_left _ _)) hL0) (hball_nn _)
        · have hn : 0 < ‖x - y‖ := norm_pos_iff.2 hy0
          have hb := kap_bound hs0 k hy0
          have h1 : ‖x - y‖ ^ (-s - 1) * ‖x - y‖ = ‖x - y‖ ^ (-s) := by
            rw [← Real.rpow_add_one hn.ne']; congr 1; ring
          have hball : ballF (d := d) s (x - y) = ‖x - y‖ ^ (-s) := by
            simp [ballF, show ‖x - y‖ < 1 by linarith]
          rw [hball, Real.norm_eq_abs, abs_mul]
          calc |F y - F x| * |kap d s k (x - y)|
              ≤ (L * ‖x - y‖) * (max 1 s * ‖x - y‖ ^ (-s - 1)) :=
                mul_le_mul (hL y hy) hb (abs_nonneg _) (by positivity)
            _ = max 1 s * L * ‖x - y‖ ^ (-s) := by rw [← h1]; ring
      · simp only [hy, if_false, norm_zero]
        exact mul_nonneg (by positivity) (hball_nn _)
  -- far part
  have hfar : Integrable (fun y => if ‖x - y‖ ≤ 1 / 4 then 0 else F y * kap d s k (x - y)) := by
    have hm := hFi.abs.const_mul (max 1 s * 8 ^ (s + 1))
    refine hm.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact (Measurable.ite hmeasI measurable_const (hFm.mul hk)).aestronglyMeasurable
    · by_cases hy : ‖x - y‖ ≤ 1 / 4
      · simp only [hy, if_true, norm_zero]; positivity
      · have hy' : 1 / 8 ≤ ‖x - y‖ := by linarith [not_le.1 hy]
        simp only [hy, if_false]
        rw [Real.norm_eq_abs, abs_mul]
        calc |F y| * |kap d s k (x - y)| ≤ |F y| * (max 1 s * 8 ^ (s + 1)) :=
              mul_le_mul_of_nonneg_left (ul1_kap_far_bound hs0 k hy') (abs_nonneg _)
          _ = _ := by ring
  refine (hnear.add hfar).congr (Filter.Eventually.of_forall fun y => ?_)
  by_cases hy : ‖x - y‖ ≤ 1 / 4
  · simp only [Pi.add_apply, hy, ↓reduceIte, add_zero]
  · simp only [Pi.add_apply, hy, ↓reduceIte, zero_add]

/-- the `i`-th component of the cancellation convolution -/
theorem ul1_conv_comp {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i : Fin d) {F : Euc d → ℝ}
    (hF : ContDiff ℝ 1 F) (hFi : Integrable F) (x : Euc d) :
    (convGradConvW (rieszKernelGrad d s) F x) i =
      ∫ y, (if ‖x - y‖ ≤ 1 / 4 then (F y - F x) * kap d s i (x - y)
        else F y * kap d s i (x - y)) := by
  set v : Euc d → Euc d := fun y =>
    if ‖x - y‖ ≤ 1 / 4 then (F y - F x) • rieszKernelGrad d s (x - y)
      else F y • rieszKernelGrad d s (x - y) with hv
  have hvk : ∀ y k, v y k = if ‖x - y‖ ≤ 1 / 4 then (F y - F x) * kap d s k (x - y)
      else F y * kap d s k (x - y) := by
    intro y k
    simp only [hv]
    split_ifs <;> simp [kap]
  have hvi : Integrable v := by
    have hrepr : v = fun y => ∑ k, (v y k) • (EuclideanSpace.single k (1 : ℝ) : Euc d) := by
      funext y; ext l; simp [Finset.sum_apply, Pi.single_apply]
    rw [hrepr]
    refine integrable_finset_sum _ fun k _ => Integrable.smul_const ?_ _
    simp_rw [hvk]
    exact ul1_comp_integrable hs0 hsd k hF hFi x
  have := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).integral_comp_comm hvi
  show (∫ y, v y) i = _
  have hpr : ∀ w : Euc d, (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) w = w i := fun w => rfl
  simp only [hpr] at this
  rw [← this]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => hvk y i)

theorem ul1_H_mul_cont_integrable {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {c : Euc d → ℝ}
    (hc : Continuous c) : Integrable (fun z => ul1H d s z * c z) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Euc d) (1 / 4)).exists_bound_of_continuousOn
    hc.continuousOn
  have hm := (ul1_H_integrable hs0 hsd).abs.mul_const (max M 0)
  refine hm.mono' ((ul1_H_measurable s).mul hc.measurable).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : 1 / 4 ≤ ‖z‖
  · simp [ul1H, ul1_th_zero hz]
  · rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul_of_nonneg_left ((hM z (by rw [mem_closedBall_zero_iff]; linarith [not_le.1 hz])).trans
      (le_max_left _ _)) (abs_nonneg _)

theorem ul1_nl_decomp {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (Fs : Fin d → Euc d → ℝ)
    (hF : ∀ j, ContDiff ℝ 1 (Fs j)) (hFi : ∀ j, Integrable (Fs j)) (x : Euc d) :
    ∑ j, (convGradConvW (rieszKernelGrad d s) (Fs j) x) j =
      HRS.Whole.convFun (ul1H d s) (fun y => ∑ j, fderiv ℝ (Fs j) y (EuclideanSpace.single j 1)) x +
        ∑ j, ∫ z, ul1K d s j z * Fs j (x - z) := by
  have h1 : ∀ j, (convGradConvW (rieszKernelGrad d s) (Fs j) x) j =
      (∫ z, ul1H d s z * fderiv ℝ (Fs j) (x - z) (EuclideanSpace.single j 1)) +
        ∫ z, ul1K d s j z * Fs j (x - z) := fun j => by
    rw [ul1_conv_comp hs0 hsd j (hF j) (hFi j) x, ul1_decomp hs0 hsd j (hF j) (hFi j) x]
  simp_rw [h1]
  rw [Finset.sum_add_distrib]
  congr 1
  unfold HRS.Whole.convFun
  rw [← integral_sub_left_eq_self (fun y => ul1H d s (x - y) * ∑ j, fderiv ℝ (Fs j) y
    (EuclideanSpace.single j 1)) volume x]
  simp only [sub_sub_cancel, Finset.mul_sum]
  rw [integral_finset_sum]
  intro j _
  exact ul1_H_mul_cont_integrable hs0 hsd
    (((hF j).continuous_fderiv one_ne_zero).clm_apply continuous_const |>.comp
      (continuous_const.sub continuous_id))

end HRS.MS.Ul
