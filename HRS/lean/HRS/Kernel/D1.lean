import HRS.PDE.Convention
import HRS.Kernel.Riesz

/-!
# One-dimensional periodic Riesz / logarithmic kernel facts

The `d ≥ 2` results of `HRS/Kernel/Riesz.lean` (Fourier coefficients, local singularity,
gradient bound) only use `2 ≤ d` to feed `rieszConst_pos` / `periodicRiesz_tendsto`, which in
fact hold for `1 ≤ d`.  Section `HRS.KernelD1Aux` re-proves these chains for `1 ≤ d`; then the
`d = 1` statements are assembled, including the smoothness of `∇g` off the origin and its
local form `∇g = ∇g_E + r`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace KernelD1

variable {d : ℕ}

open Classical in
/-- The radial coefficient `a_s(z) > 0` of the Euclidean singular force (M L11815):
`∇|z|^{-s} = -s|z|^{-s-2} z` for `s > 0`, `∇(-log|z|) = -|z|^{-2} z` for `s = 0`. -/
def rieszRadial (s : ℝ) (z : Euc d) : ℝ :=
  if s = 0 then ‖z‖ ^ (-2 : ℝ) else s * ‖z‖ ^ (-s - 2)

/-- The Euclidean singular force `∇g_E(z) = -a_s(z) z` (M L11815). -/
def eucRieszGrad (s : ℝ) (z : Euc d) : Euc d := -(rieszRadial s z) • z

end KernelD1

section KernelD1Aux

open Complex Set
open scoped Real

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

namespace KernelD1Aux

open HRS.KernelAux

theorem tendsto_d1 {d : ℕ} {s : ℝ} (hsd : s < d) (x : Torus d) (hx : x ≠ 0) :
    Tendsto (fun ε => heatRiesz d s ε x) (𝓝[>] 0) (𝓝 (periodicRiesz d s x)) := by
  obtain ⟨L, hL⟩ := heat_limit_exists hsd x hx
  have : periodicRiesz d s x = L := hL.limUnder_eq
  rw [this]; exact hL

theorem rieszConst_pos_d1 {d : ℕ} {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    0 < rieszConst d s := by
  have hd' : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  unfold rieszConst
  split_ifs with h
  · exact mul_pos (mul_pos (by positivity) (by positivity)) (Real.Gamma_pos_of_pos (by positivity))
  · have hs : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h)
    exact div_pos (mul_pos (mul_pos (by positivity) (by positivity))
      (Real.Gamma_pos_of_pos (by linarith))) (Real.Gamma_pos_of_pos (by linarith))

theorem subA_nonneg_d1 {d : ℕ} {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) : 0 ≤ subA d s := by
  unfold subA
  have := rieszConst_pos_d1 hd hs0 hsd
  have := Real.Gamma_pos_of_pos (show 0 < ((d:ℝ) - s) / 2 by linarith)
  have : 0 < (2 * π) ^ (s - d) := Real.rpow_pos_of_pos (by positivity) _
  positivity


theorem integral_mode_d1 {d : ℕ} {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (k : Lattice d) :
    ∫ x : Torus d, Torus.mode (-k) x * ((periodicRiesz d s x : ℝ) : ℂ) = ((rieszCoeff d s k : ℝ) : ℂ) := by
  have hd0 : 0 < d := by omega
  have : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
  obtain ⟨C1, C2, hC1, hC2, hbd⟩ := heat_eps_bound hs0 hsd
  set μ : Measure (Fin d → ℝ) := volume.restrict (Box d) with hμ
  set G : (Fin d → ℝ) → ℝ := fun y => C1 * ‖y‖ ^ (-((s + d)/2)) + C2 with hG
  set Fε : ℝ → (Fin d → ℝ) → ℂ := fun ε y =>
    Torus.mode (-k) (boxPt y) * ((heatRiesz d s ε (boxPt y) : ℝ) : ℂ) with hFε
  set F0 : (Fin d → ℝ) → ℂ := fun y =>
    Torus.mode (-k) (boxPt y) * ((periodicRiesz d s (boxPt y) : ℝ) : ℂ) with hF0
  have hne : ∀ᵐ y ∂μ, y ≠ 0 := by
    have h1 : ∀ᵐ y ∂(volume : Measure (Fin d → ℝ)), y ≠ 0 := by
      rw [ae_iff]; simp
    exact ae_restrict_of_ae h1
  have hmem : ∀ᵐ y ∂μ, y ∈ Box d := ae_restrict_mem (measurableSet_Box d)
  have hdom := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝[>] (0:ℝ))
    (F := Fε) (f := F0) G ?_ ?_ ?_ ?_
  · -- identify the limit
    have h1 : ∀ ε : ℝ, 0 < ε → ∫ y, Fε ε y ∂μ =
        ((rieszCoeff d s k * Real.exp (-ε * Lattice.enorm k ^ 2) : ℝ) : ℂ) := by
      intro ε hε
      rw [← integral_heat_mode hsd hε k]
      exact (integral_torus_box (fun x : Torus d => Torus.mode (-k) x * ((heatRiesz d s ε x : ℝ) : ℂ))).symm
    have h2 : Tendsto (fun ε : ℝ => ((rieszCoeff d s k * Real.exp (-ε * Lattice.enorm k ^ 2) : ℝ) : ℂ))
        (𝓝[>] 0) (𝓝 ((rieszCoeff d s k : ℝ) : ℂ)) := by
      have : Continuous fun ε : ℝ => ((rieszCoeff d s k * Real.exp (-ε * Lattice.enorm k ^ 2) : ℝ) : ℂ) := by
        fun_prop
      have := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
      simpa using this
    have h3 : Tendsto (fun ε : ℝ => ∫ y, Fε ε y ∂μ) (𝓝[>] 0) (𝓝 ((rieszCoeff d s k : ℝ) : ℂ)) :=
      h2.congr' (by filter_upwards [self_mem_nhdsWithin] with ε hε using (h1 ε hε).symm)
    have h4 := tendsto_nhds_unique hdom h3
    rw [← h4]
    exact integral_torus_box (fun x : Torus d => Torus.mode (-k) x * ((periodicRiesz d s x : ℝ) : ℂ))
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    refine Continuous.aestronglyMeasurable ?_
    exact ((Torus.continuous_mode _).comp (continuous_boxPt d)).mul
      (Complex.continuous_ofReal.comp ((KernelAux.continuous_heatRiesz hsd hε').comp (continuous_boxPt d)))
  · filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
    filter_upwards [hne, hmem] with y hy hyB
    have hy0 : boxPt y ≠ 0 := fun h => hy (boxPt_eq_zero hyB h)
    obtain ⟨j, hj⟩ := exists_argmax hd0 y
    have hyj : y j ≠ 0 := by
      intro h0
      apply hy
      have : ‖y‖ = 0 := by rw [hj, h0, abs_zero]
      exact norm_eq_zero.mp this
    have := hbd y (Box_abs_le hyB) j hyj ε hε.1 hε.2.le
    simp only [hFε, norm_mul, norm_mode, one_mul, Complex.norm_real, Real.norm_eq_abs, hG, hj]
    exact this
  · have hI : IntegrableOn (fun y : Fin d → ℝ => ‖y‖ ^ (-((s + d)/2))) (Box d) :=
      integrableOn_Box_rpow hd0 (by linarith)
    exact (hI.const_mul C1).add (integrableOn_const (measure_Box_ne_top d))
  · filter_upwards [hne, hmem] with y hy hyB
    have hy0 : boxPt y ≠ 0 := fun h => hy (boxPt_eq_zero hyB h)
    have := tendsto_d1 hsd (boxPt y) hy0
    exact (Complex.continuous_ofReal.tendsto _ |>.comp this).const_mul _


theorem box_bound_d1 {d : ℕ} {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C1 C2 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧ ∀ y : Fin d → ℝ, y ∈ Box d → y ≠ 0 →
      |periodicRiesz d s (boxPt y)| ≤ C1 * ‖y‖ ^ (-((s + d)/2)) + C2 := by
  have hd0 : 0 < d := by omega
  obtain ⟨C1, C2, hC1, hC2, hbd⟩ := heat_eps_bound hs0 hsd
  refine ⟨C1, C2, hC1, hC2, fun y hyB hy => ?_⟩
  have hy0 : boxPt y ≠ 0 := fun h => hy (boxPt_eq_zero hyB h)
  obtain ⟨j, hj⟩ := exists_argmax hd0 y
  have hyj : y j ≠ 0 := by
    intro h0
    apply hy
    have : ‖y‖ = 0 := by rw [hj, h0, abs_zero]
    exact norm_eq_zero.mp this
  have hlim := (tendsto_d1 hsd (boxPt y) hy0).abs
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
  have := hbd y (Box_abs_le hyB) j hyj ε hε.1 hε.2.le
  rwa [← hj] at this

theorem aesm_d1 {d : ℕ} {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    AEStronglyMeasurable (periodicRiesz d s) (volume : Measure (Torus d)) := by
  have hd0 : 0 < d := by omega
  refine aestronglyMeasurable_of_tendsto_ae (u := atTop) (f := fun n : ℕ => heatRiesz d s (1 / ((n:ℝ) + 1)))
    (fun n => (KernelAux.continuous_heatRiesz hsd (by positivity)).aestronglyMeasurable) ?_
  filter_upwards [torus_ae_ne hd0] with x hx
  have h := tendsto_d1 hsd x hx
  refine h.comp ?_
  refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Filter.Eventually.of_forall fun n => ?_⟩
  simp only [mem_Ioi]; positivity

theorem integrable_d1 {d : ℕ} {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    Integrable (periodicRiesz d s) := by
  have hd0 : 0 < d := by omega
  obtain ⟨C1, C2, hC1, hC2, hbd⟩ := box_bound_d1 hd hs0 hsd
  refine ⟨aesm_d1 hd hs0 hsd, ?_⟩
  unfold HasFiniteIntegral
  rw [lintegral_torus_box (fun x => ‖periodicRiesz d s x‖ₑ)]
  have hI : IntegrableOn (fun y : Fin d → ℝ => C1 * ‖y‖ ^ (-((s + d)/2)) + C2) (Box d) :=
    ((integrableOn_Box_rpow hd0 (by linarith)).const_mul C1).add
      (integrableOn_const (measure_Box_ne_top d))
  have hne : ∀ᵐ y ∂(volume.restrict (Box d)), y ≠ 0 := by
    exact ae_restrict_of_ae (ae_ne_pi hd0)
  calc ∫⁻ y in Box d, ‖periodicRiesz d s (boxPt y)‖ₑ
      ≤ ∫⁻ y in Box d, ENNReal.ofReal (C1 * ‖y‖ ^ (-((s + d)/2)) + C2) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hne, ae_restrict_mem (measurableSet_Box d)] with y hy hyB
        rw [← ofReal_norm, Real.norm_eq_abs]
        exact ENNReal.ofReal_le_ofReal (hbd y hyB hy)
    _ = ∫⁻ y in Box d, ‖C1 * ‖y‖ ^ (-((s + d)/2)) + C2‖ₑ := by
        refine lintegral_congr fun y => ?_
        rw [Real.enorm_of_nonneg (by positivity)]
    _ < ∞ := hI.2


theorem eq_integral_d1 {d : ℕ} {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (x : Torus d) (hx : x ≠ 0) :
    periodicRiesz d s x = subA d s * ∫ t in Ioi (0:ℝ), t ^ (((d:ℝ) - s) / 2 - 1) * psiFn x t := by
  set a : ℝ := ((d:ℝ) - s) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  obtain ⟨M, hM0, hM⟩ := psi_bound x hx
  have hcont := psi_continuousOn x
  have hmeas : ∀ ε : ℝ, 0 ≤ ε → AEStronglyMeasurable (fun t : ℝ => t ^ (a - 1) * psiFn x (t + ε))
      (volume.restrict (Ioi 0)) := by
    intro ε hε
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht)) ?_
    refine hcont.comp (continuousOn_id.add continuousOn_const) fun t ht => ?_
    simp only [mem_Ioi] at ht ⊢
    linarith
  have hlim : Tendsto (fun ε => ∫ t in Ioi (0:ℝ), t ^ (a - 1) * psiFn x (t + ε)) (𝓝[>] 0)
      (𝓝 (∫ t in Ioi (0:ℝ), t ^ (a - 1) * psiFn x t)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t => M * (Real.exp (-t) * t ^ (a - 1))) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε using hmeas ε (le_of_lt hε)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
      have hε' : 0 < ε := hε
      have ht' : 0 < t := ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht' _)]
      have h1 := hM (t + ε) (by linarith)
      have h2 : Real.exp (-(t + ε)) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith)
      have h3 := Real.rpow_pos_of_pos ht' (a - 1)
      calc t ^ (a - 1) * |psiFn x (t + ε)| ≤ t ^ (a - 1) * (M * Real.exp (-t)) := by
            gcongr
            exact h1.trans (by gcongr)
        _ = _ := by ring
    · exact (Real.GammaIntegral_convergent ha).const_mul M
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
      have ht' : 0 < t := ht
      refine Tendsto.const_mul _ ?_
      have h1 : Tendsto (fun ε : ℝ => t + ε) (𝓝[>] 0) (𝓝 t) := by
        have : Tendsto (fun ε : ℝ => t + ε) (𝓝 0) (𝓝 (t + 0)) :=
          (continuous_const.add continuous_id).tendsto 0
        rw [add_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      have h2 : ContinuousAt (psiFn x) t :=
        (hcont t ht').continuousAt (Ioi_mem_nhds ht')
      exact h2.tendsto.comp h1
  have h2 : Tendsto (fun ε => heatRiesz d s ε x) (𝓝[>] 0)
      (𝓝 (subA d s * ∫ t in Ioi (0:ℝ), t ^ (a - 1) * psiFn x t)) := by
    refine (hlim.const_mul _).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (heatRiesz_eq_integral hsd hε x).symm
  exact tendsto_nhds_unique (tendsto_d1 hsd x hx) h2

theorem decomp1_d1 {d : ℕ} {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (y : Euc d)
    (hy : ∀ m : Lattice d, 0 < wsq (fun i => y i) m) :
    periodicRiesz d s (Torus.mk y) =
      subA d s * (π ^ ((d:ℝ)/2) * ∑' m : Lattice d, Wfun s (π^2 * wsq (fun i => y i) m)
        - 1 / (((d:ℝ) - s)/2)) +
      ∑' k : Lattice d, coefF2 d s k * Torus.cosMode k (Torus.mk y) := by
  have hmk : Torus.mk y = boxPt (fun i => y i) := rfl
  have hx0 : Torus.mk y ≠ 0 := by rw [hmk]; exact boxPt_ne_zero_of_wsq hy
  rw [eq_integral_d1 hd hs0 hsd _ hx0]
  have hint := integrableOn_psi hsd (Torus.mk y) hx0
  have hsplit : ∫ t in Ioi (0:ℝ), t ^ (((d:ℝ) - s) / 2 - 1) * psiFn (Torus.mk y) t =
      (∫ t in Ioc (0:ℝ) 1, t ^ (((d:ℝ) - s) / 2 - 1) * psiFn (Torus.mk y) t) +
      ∫ t in Ioi (1:ℝ), t ^ (((d:ℝ) - s) / 2 - 1) * psiFn (Torus.mk y) t := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi zero_le_one))
  rw [hsplit, mul_add, F2_eq hsd, hmk, int_Ioc_psi hs0 hsd _ hy]

theorem local_decomp_d1 {d : ℕ} {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (S : ℝ → ℝ) (hS : ContDiff ℝ ∞' S) (c : ℝ) (sing : ℝ → ℝ)
    (hsing : ∀ y : Euc d, y ≠ 0 → ‖y‖ ≤ 1/16 →
      subA d s * π ^ ((d:ℝ)/2) * Wfun s (π ^ 2 * ‖y‖ ^ 2) = sing ‖y‖ + S (π ^ 2 * ‖y‖ ^ 2) + c) :
    ∃ (r : Torus d → ℝ) (δ : ℝ), 0 < δ ∧ Torus.IsSmooth r ∧
      ∀ x : Euc d, ‖x‖ < δ → x ≠ 0 → periodicRiesz d s (Torus.mk x) = sing ‖x‖ + r (Torus.mk x) := by
  set K0 := subA d s * π ^ ((d:ℝ)/2) with hK0
  set F2e : Euc d → ℝ := fun y => ∑' k : Lattice d, coefF2 d s k * Torus.cosMode k (Torus.mk y)
    with hF2e
  set f : Euc d → ℝ := fun y =>
    chi d y * (S (π ^ 2 * ‖y‖ ^ 2) + c - subA d s * (1 / (((d:ℝ) - s)/2)) + F2e y) +
      K0 * ∑' m : Lattice d, Tm d s m y with hf
  have hfC : ContDiff ℝ ∞' f := by
    have h1 : ContDiff ℝ ∞' (fun y : Euc d => S (π ^ 2 * ‖y‖ ^ 2)) :=
      hS.comp (contDiff_const.mul (contDiff_norm_sq ℝ))
    have h2 : ContDiff ℝ ∞' F2e := contDiff_F2 hsd
    exact (contDiff_chi.mul (((h1.add contDiff_const).sub contDiff_const).add h2)).add
      (contDiff_const.mul (contDiff_images hs0))
  have hfs : ∀ y, 1/8 ≤ ‖y‖ → f y = 0 := by
    intro y hy
    have hc := chi_zero (d := d) hy
    have hT : ∀ m, Tm d s m y = 0 := fun m => by simp [Tm, hc]
    simp only [hf, hc, hT, tsum_zero, zero_mul, mul_zero, add_zero]
  obtain ⟨r, hr, hrf⟩ := periodize hfC hfs
  refine ⟨r, 1/16, by norm_num, hr, fun x hx hx0 => ?_⟩
  have hx' : ‖x‖ ≤ 1/16 := hx.le
  rw [hrf x (by linarith), decomp1_d1 hd hs0 hsd x (wsq_pos_small hx0 hx'), decomp2 hs0 hx']
  have hsx := hsing x hx0 hx'
  simp only [hf, hF2e, chi_one hx', one_mul]
  rw [hK0] at hsx ⊢
  linear_combination hsx


theorem local_sing_d1 {d : ℕ} {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) :
    ∃ (r : Torus d → ℝ) (δ : ℝ), 0 < δ ∧ Torus.IsSmooth r ∧
      ∀ x : Euc d, ‖x‖ < δ → x ≠ 0 →
        periodicRiesz d s (Torus.mk x) = ‖x‖ ^ (-s) + r (Torus.mk x) := by
  set K0 := subA d s * π ^ ((d:ℝ)/2) with hK0
  refine local_decomp_d1 hd hs0.le hsd (fun w => -(K0 * Hp (s/2 - 1) w))
    (contDiff_const.mul (contDiff_Hp (by linarith))).neg 0 (fun r => r ^ (-s)) ?_
  intro y hy0 _
  have hy : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hw : 0 < π ^ 2 * ‖y‖ ^ 2 := by positivity
  rw [Wfun_pos_eq hs0 hw]
  have hpow : (π ^ 2 * ‖y‖ ^ 2) ^ (-(s/2)) = π ^ (-s) * ‖y‖ ^ (-s) := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul Real.pi_pos.le, ← Real.rpow_mul hy.le]
    congr 2 <;> push_cast <;> ring
  rw [hpow]
  have hc := subA_const_pos hs0 hsd
  rw [← hK0] at hc
  linear_combination ‖y‖ ^ (-s) * hc

theorem log_sing_d1 {d : ℕ} (hd : 1 ≤ d) :
    ∃ (r : Torus d → ℝ) (δ : ℝ), 0 < δ ∧ Torus.IsSmooth r ∧
      ∀ x : Euc d, ‖x‖ < δ → x ≠ 0 →
        periodicRiesz d 0 (Torus.mk x) = -Real.log ‖x‖ + r (Torus.mk x) := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  obtain ⟨S0, hS0, hW⟩ := Wfun_zero_eq
  refine local_decomp_d1 hd le_rfl hd0 (fun w => (1/2) * S0 w) (contDiff_const.mul hS0)
    (-Real.log π) (fun r => -Real.log r) ?_
  intro y hy0 _
  have hy : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hw : 0 < π ^ 2 * ‖y‖ ^ 2 := by positivity
  rw [hW _ hw, subA_const_zero (by omega),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  push_cast
  ring



theorem gradComp_bound_d1 {d : ℕ} {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (j : Fin d) :
    ∃ C1 C2 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧ ∀ x : Euc d, (∀ i, |x i| ≤ 1/2) → x ≠ 0 →
      |gradComp s j (Torus.mk x)| ≤ C1 * ‖x‖ ^ (-s - 1) + C2 := by
  obtain ⟨K, hK0, hK⟩ := psiG_small_bound (d := d) j
  obtain ⟨M1, hM10, hM1⟩ := psiG_large_bound (d := d) j
  set a : ℝ := ((d:ℝ) - s) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  set N : ℝ := s / 2 + 2 with hN
  have hN1 : 1 < N := by rw [hN]; linarith
  set P : ℝ := 2 * π ^ 2 * Real.sqrt π ^ d with hP
  have hP0 : 0 ≤ P := by positivity
  set A := subA d s with hA
  have hA0 : 0 ≤ A := subA_nonneg_d1 hd hs0 hsd
  set θ2 : ℝ := π ^ 2 / 8 with hθ2
  have hθ2p : 0 < θ2 := by positivity
  have hG1 : 0 ≤ Real.Gamma (N - 1) := (Real.Gamma_pos_of_pos (by linarith)).le
  refine ⟨A * (P * Real.Gamma (N - 1) * π ^ (-(s + 2))),
    A * (P * K * (Real.Gamma (N - 1) * θ2 ^ (-(N - 1))) + M1 * Real.Gamma a),
    by positivity, by positivity, fun x hx hx0 => ?_⟩
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  set θ1 : ℝ := π ^ 2 * ‖x‖ ^ 2 with hθ1
  have hθ1p : 0 < θ1 := by positivity
  set b1 : ℝ → ℝ := fun t => P * ‖x‖ * (t ^ (-N) * Real.exp (-θ1 / t)) +
    P * K * (t ^ (-N) * Real.exp (-θ2 / t)) with hb1
  have hb1i : IntegrableOn b1 (Ioc 0 1) :=
    ((integrableOn_pow_exp_Ioc (by linarith) hθ1p).const_mul _).add
      ((integrableOn_pow_exp_Ioc (by linarith) hθ2p).const_mul _)
  set B : ℝ → ℝ := fun t => (Ioc (0:ℝ) 1).indicator b1 t + M1 * (Real.exp (-t) * t ^ (a - 1)) with hB
  have hBi : IntegrableOn B (Ioi 0) :=
    (hb1i.integrable_indicator measurableSet_Ioc).integrableOn.add
      ((Real.GammaIntegral_convergent ha).const_mul M1)
  have hpt : ∀ t ∈ Ioi (0:ℝ), ‖t ^ (a - 1) * psiG j (Torus.mk x) t‖ ≤ B t := by
    intro t ht
    have ht0 : 0 < t := ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
    rcases le_or_gt t 1 with h1 | h1
    · have hmem : t ∈ Ioc (0:ℝ) 1 := ⟨ht0, h1⟩
      simp only [hB, Set.indicator_of_mem hmem]
      have h2 := hK x hx t ht0 h1
      have hpow : t ^ (a - 1) * (Real.sqrt (π / t) ^ d * (2 * π ^ 2 / t)) = P * t ^ (-N) := by
        rw [sqrt_div_pow_eq d ht0, hP, div_eq_mul_inv (2 * π ^ 2), ← Real.rpow_neg_one t]
        have : t ^ (a - 1) * (Real.sqrt π ^ d * t ^ (-(d:ℝ)/2) * (2 * π ^ 2 * t ^ (-1:ℝ))) =
            2 * π ^ 2 * Real.sqrt π ^ d * (t ^ (a - 1) * t ^ (-(d:ℝ)/2) * t ^ (-1:ℝ)) := by ring
        rw [this, ← Real.rpow_add ht0, ← Real.rpow_add ht0]
        congr 2
        rw [hN, ha_def]; ring
      have e1 : Real.exp (-(π ^ 2 * ‖x‖ ^ 2 / t)) = Real.exp (-θ1 / t) := by rw [hθ1, neg_div]
      have e2 : Real.exp (-(π ^ 2 / (8 * t))) = Real.exp (-θ2 / t) := by
        rw [hθ2]; congr 1; field_simp
      rw [e1, e2] at h2
      have hp := Real.rpow_pos_of_pos ht0 (a - 1)
      calc t ^ (a - 1) * |psiG j (Torus.mk x) t|
          ≤ t ^ (a - 1) * (Real.sqrt (π / t) ^ d * (2 * π ^ 2 / t) *
              (‖x‖ * Real.exp (-θ1 / t) + K * Real.exp (-θ2 / t))) := by gcongr
        _ = (t ^ (a - 1) * (Real.sqrt (π / t) ^ d * (2 * π ^ 2 / t))) *
              (‖x‖ * Real.exp (-θ1 / t) + K * Real.exp (-θ2 / t)) := by ring
        _ = b1 t := by rw [hpow, hb1]; ring
        _ ≤ b1 t + M1 * (Real.exp (-t) * t ^ (a - 1)) := by
            have : 0 ≤ M1 * (Real.exp (-t) * t ^ (a - 1)) := by positivity
            linarith
    · have hnmem : t ∉ Ioc (0:ℝ) 1 := fun h => by linarith [h.2]
      simp only [hB, Set.indicator_of_notMem hnmem, zero_add]
      have h2 := hM1 (Torus.mk x) t h1.le
      have hp := Real.rpow_pos_of_pos ht0 (a - 1)
      calc t ^ (a - 1) * |psiG j (Torus.mk x) t| ≤ t ^ (a - 1) * (M1 * Real.exp (-t)) := by gcongr
        _ = _ := by ring
  have hint : |∫ t in Ioi (0:ℝ), t ^ (a - 1) * psiG j (Torus.mk x) t| ≤ ∫ t in Ioi (0:ℝ), B t := by
    rw [← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le hBi
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall hpt))
  have hBint : ∫ t in Ioi (0:ℝ), B t = (∫ t in Ioc (0:ℝ) 1, b1 t) + M1 * Real.Gamma a := by
    simp only [hB]
    rw [integral_add (hb1i.integrable_indicator measurableSet_Ioc).integrableOn
      ((Real.GammaIntegral_convergent ha).const_mul M1), integral_const_mul,
      ← Real.Gamma_eq_integral ha, setIntegral_indicator measurableSet_Ioc,
      Set.inter_eq_right.mpr Ioc_subset_Ioi_self]
  have hb1int : ∫ t in Ioc (0:ℝ) 1, b1 t ≤
      P * ‖x‖ * (Real.Gamma (N - 1) * θ1 ^ (-(N - 1))) + P * K * (Real.Gamma (N - 1) * θ2 ^ (-(N - 1))) := by
    simp only [hb1]
    rw [integral_add ((integrableOn_pow_exp_Ioc (by linarith) hθ1p).const_mul _)
      ((integrableOn_pow_exp_Ioc (by linarith) hθ2p).const_mul _), integral_const_mul, integral_const_mul]
    gcongr
    · exact int_Ioc_pow_exp_le hN1 hθ1p
    · exact int_Ioc_pow_exp_le hN1 hθ2p
  have hθ1pow : ‖x‖ * θ1 ^ (-(N - 1)) = π ^ (-(s + 2)) * ‖x‖ ^ (-s - 1) := by
    rw [hθ1, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul Real.pi_pos.le, ← Real.rpow_mul hxn.le]
    have e3 : ‖x‖ * (π ^ ((2:ℕ) * -(N - 1) : ℝ) * ‖x‖ ^ ((2:ℕ) * -(N - 1) : ℝ)) =
        π ^ ((2:ℕ) * -(N - 1) : ℝ) * (‖x‖ ^ (1:ℝ) * ‖x‖ ^ ((2:ℕ) * -(N - 1) : ℝ)) := by
      rw [Real.rpow_one]; ring
    rw [e3, ← Real.rpow_add hxn]
    congr 2 <;> push_cast <;> rw [hN] <;> ring
  unfold gradComp
  rw [← hA, abs_mul, abs_of_nonneg hA0]
  calc A * |∫ t in Ioi (0:ℝ), t ^ (((d:ℝ) - s) / 2 - 1) * psiG j (Torus.mk x) t|
      ≤ A * ((P * ‖x‖ * (Real.Gamma (N - 1) * θ1 ^ (-(N - 1))) +
          P * K * (Real.Gamma (N - 1) * θ2 ^ (-(N - 1)))) + M1 * Real.Gamma a) := by
        gcongr
        exact hint.trans (hBint ▸ by linarith)
    _ = A * (P * Real.Gamma (N - 1) * (‖x‖ * θ1 ^ (-(N - 1)))) +
          A * (P * K * (Real.Gamma (N - 1) * θ2 ^ (-(N - 1))) + M1 * Real.Gamma a) := by ring
    _ = _ := by rw [hθ1pow]; ring


theorem grad_bound_d1 {d : ℕ} {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, ∀ x : Euc d, x ≠ 0 → (∀ i, |x i| ≤ 1 / 2) →
      ‖periodicRieszGrad d s (Torus.mk x)‖ ≤ C * (‖x‖ ^ (-s - 1) + 1) := by
  choose C1 C2 hC1 hC2 hC using fun j => gradComp_bound_d1 hd hs0 hsd j
  refine ⟨∑ j, (C1 j + C2 j), fun x hx0 hx => ?_⟩
  rw [periodicRieszGrad_eq hsd x hx hx0]
  refine (norm_toLp_le_sum _).trans ?_
  have hr : 0 ≤ ‖x‖ ^ (-s - 1) := Real.rpow_nonneg (norm_nonneg _) _
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => (hC j x hx hx0).trans ?_
  have := hC1 j
  have := hC2 j
  nlinarith


/-! ### Smoothness of the image sum off the lattice -/

/-- the quadratic `q_p(x) = π² |x - p|²` centred at an arbitrary point `p` -/
def qp {d : ℕ} (p : Euc d) (x : Euc d) : ℝ := π ^ 2 * ‖x - p‖ ^ 2

theorem norm_iteratedFDeriv_qp_le {d : ℕ} (m : Euc d) (n : ℕ) (x : Euc d) :
    ‖iteratedFDeriv ℝ n (qp m) x‖ ≤ π ^ 2 * 2 ^ n * (1 + ‖x - m‖) ^ 2 := by
  set B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ := (π ^ 2) • (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) with hB
  have hq : qp m = fun y => B (y - m) (y - m) := by
    funext y
    simp only [qp, B, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
  have hf : ContDiff ℝ ∞' (fun y : Euc d => y - m) := contDiff_id.sub contDiff_const
  rw [hq]
  have h1 := B.norm_iteratedFDeriv_le_of_bilinear hf hf x (n := n) (by exact_mod_cast le_top)
  have hBn : ‖B‖ ≤ π ^ 2 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [hB]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs]
    rw [innerSL_apply_apply, abs_of_nonneg (by positivity : (0:ℝ) ≤ π^2), mul_assoc]
    gcongr
    exact abs_real_inner_le_norm u v
  set R := 1 + ‖x - m‖ with hR
  have hR0 : 0 ≤ R := by positivity
  have hsum : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun y : Euc d => y - m) x‖ *
        ‖iteratedFDeriv ℝ (n - i) (fun y : Euc d => y - m) x‖ ≤ 2 ^ n * R ^ 2 := by
    calc _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (R * R) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [mul_assoc]
          gcongr
          · exact norm_iteratedFDeriv_sub_const_le _ _ _
          · exact norm_iteratedFDeriv_sub_const_le _ _ _
      _ = 2 ^ n * R ^ 2 := by
          rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
          push_cast; ring
  calc _ ≤ ‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun y : Euc d => y - m) x‖ *
        ‖iteratedFDeriv ℝ (n - i) (fun y : Euc d => y - m) x‖ := h1
    _ ≤ π ^ 2 * (2 ^ n * R ^ 2) := by gcongr
    _ = _ := by ring

theorem image_comp_bound_p {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : Euc d, 1 ≤ ‖m‖ → ∀ x : Euc d, ‖x‖ ≤ 1/4 → ∀ j ≤ n,
      ‖iteratedFDeriv ℝ j (fun y => Wt s (qp m y)) x‖ ≤
        K * (‖m‖ ^ (2 * n) * Real.exp (-2 * ‖m‖ ^ 2)) := by
  choose B hB0 hB using Wt_deriv_bound s hs
  set BS := ∑ i ∈ Finset.range (n + 1), B i with hBS
  have hBS0 : 0 ≤ BS := Finset.sum_nonneg fun i _ => hB0 i
  have hπ : (9:ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
  refine ⟨(n.factorial : ℝ) * BS * (18 * π ^ 2) ^ n, by positivity, fun m hm x hx j hj => ?_⟩
  set e := ‖m‖ with he
  have he1 : 1 ≤ e := hm
  set w := qp m x with hw
  set R := 1 + ‖x - m‖ with hR
  have hdist1 : e - 1/4 ≤ ‖x - m‖ := by
    have := norm_sub_norm_le (m) x
    rw [norm_sub_rev] at this
    have : e = ‖m‖ := rfl
    linarith
  have hdist2 : ‖x - m‖ ≤ e + 1/4 := by
    have := norm_sub_le x (m)
    have : e = ‖m‖ := rfl
    linarith
  have hw4 : 4 * e ^ 2 ≤ w := by
    have h1 : 3/4 * e ≤ ‖x - m‖ := by linarith
    have h2 : (3/4 * e) ^ 2 ≤ ‖x - m‖ ^ 2 := by gcongr
    simp only [hw, qp]
    nlinarith
  have hw1 : 1 ≤ w := by nlinarith
  have hR1 : 1 ≤ R := by simp only [hR]; linarith [norm_nonneg (x - m)]
  have hR3 : R ≤ 3 * e := by simp only [hR]; linarith
  -- Faa di Bruno
  have hC : ∀ i, i ≤ j → ‖iteratedFDeriv ℝ i (Wt s) (qp m x)‖ ≤ BS * Real.exp (-w / 2) := by
    intro i hi
    refine (hB i w hw1).trans ?_
    gcongr
    exact Finset.single_le_sum (f := B) (fun k _ => hB0 k) (Finset.mem_range.mpr (by omega))
  have hD : ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i (qp m) x‖ ≤ (2 * π ^ 2 * R ^ 2) ^ i := by
    intro i hi _
    have h1 : 1 ≤ π ^ 2 * R ^ 2 := by nlinarith
    have h2 : π ^ 2 * 2 ^ i * R ^ 2 ≤ (2 * π ^ 2 * R ^ 2) ^ i := by
      rw [show 2 * π ^ 2 * R ^ 2 = 2 * (π ^ 2 * R ^ 2) by ring, mul_pow]
      calc π ^ 2 * 2 ^ i * R ^ 2 = 2 ^ i * (π ^ 2 * R ^ 2) := by ring
        _ ≤ 2 ^ i * (π ^ 2 * R ^ 2) ^ i := by gcongr; exact le_self_pow₀ h1 (by omega)
    exact (norm_iteratedFDeriv_qp_le m i x).trans h2
  have hqm : ContDiff ℝ ∞' (qp m) := by
    unfold qp
    exact contDiff_const.mul ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))
  have hFB := norm_iteratedFDeriv_comp_le (contDiff_Wt s hs) hqm (n := j) (by exact_mod_cast le_top) x hC hD
  refine (le_of_eq_of_le rfl hFB).trans ?_
  have hexp : Real.exp (-w / 2) ≤ Real.exp (-2 * e ^ 2) := by
    rw [Real.exp_le_exp]; linarith
  have hpow : (2 * π ^ 2 * R ^ 2) ^ j ≤ (18 * π ^ 2) ^ n * e ^ (2 * n) := by
    have hb : 1 ≤ 18 * π ^ 2 * e ^ 2 := by nlinarith
    have hR9 : R ^ 2 ≤ 9 * e ^ 2 := by nlinarith
    have hbase : 2 * π ^ 2 * R ^ 2 ≤ 18 * π ^ 2 * e ^ 2 := by
      calc 2 * π ^ 2 * R ^ 2 ≤ 2 * π ^ 2 * (9 * e ^ 2) := by gcongr
        _ = 18 * π ^ 2 * e ^ 2 := by ring
    calc (2 * π ^ 2 * R ^ 2) ^ j ≤ (18 * π ^ 2 * e ^ 2) ^ j :=
          pow_le_pow_left₀ (by positivity) hbase j
      _ ≤ (18 * π ^ 2 * e ^ 2) ^ n := pow_le_pow_right₀ hb hj
      _ = (18 * π ^ 2) ^ n * e ^ (2 * n) := by rw [mul_pow, pow_mul]
  have hfact : (j.factorial : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_le hj
  calc (j.factorial : ℝ) * (BS * Real.exp (-w / 2)) * (2 * π ^ 2 * R ^ 2) ^ j
      ≤ (n.factorial : ℝ) * (BS * Real.exp (-2 * e ^ 2)) * ((18 * π ^ 2) ^ n * e ^ (2 * n)) := by
        gcongr
    _ = _ := by ring


theorem image_term_bound_p {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : Euc d, 1 ≤ ‖m‖ → ∀ x : Euc d,
      ‖iteratedFDeriv ℝ n (fun y => chi d y * Wt s (qp m y)) x‖ ≤
        K * (‖m‖ ^ (2 * n) * Real.exp (-2 * ‖m‖ ^ 2)) := by
  obtain ⟨K, hK0, hK⟩ := image_comp_bound_p (d := d) hs n
  choose M hM0 hM using fun i => chi_deriv_bound (d := d) i
  set MS := ∑ i ∈ Finset.range (n + 1), M i with hMS
  have hMS0 : 0 ≤ MS := Finset.sum_nonneg fun i _ => hM0 i
  refine ⟨2 ^ n * MS * K, by positivity, fun m hm x => ?_⟩
  set E := ‖m‖ ^ (2 * n) * Real.exp (-2 * ‖m‖ ^ 2) with hE
  have hE0 : 0 ≤ E := by
    have : 0 ≤ ‖m‖ := norm_nonneg _
    positivity
  by_cases hx : 1/8 < ‖x‖
  · rw [iteratedFDeriv_chi_mul_eq_zero _ hx, norm_zero]
    positivity
  · push Not at hx
    have hx4 : ‖x‖ ≤ 1/4 := by linarith
    have hqm : ContDiff ℝ ∞' (qp m) := by
      unfold qp
      exact contDiff_const.mul ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))
    have hG : ContDiff ℝ ∞' (fun y => Wt s (qp m y)) := (contDiff_Wt s hs).comp hqm
    refine (norm_iteratedFDeriv_mul_le contDiff_chi hG x (n := n) (by exact_mod_cast le_top)).trans ?_
    calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (chi d) x‖ *
          ‖iteratedFDeriv ℝ (n - i) (fun y => Wt s (qp m y)) x‖
        ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * MS * (K * E) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          gcongr
          · exact (hM i x).trans (Finset.single_le_sum (f := M) (fun k _ => hM0 k) hi)
          · exact hK m hm x hx4 (n - i) (Nat.sub_le n i)
      _ = 2 ^ n * MS * K * E := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
          push_cast; ring

theorem wsq_eq_norm_sq {d : ℕ} (y : Euc d) (m : Lattice d) :
    wsq (fun i => y i) m = ‖y - Lattice.toEuc m‖ ^ 2 := by
  have h := wsq_eq_qm y m
  unfold qm at h
  have hπ : 0 < π ^ 2 := by positivity
  exact mul_left_cancel₀ hπ.ne' h

theorem eventually_wsq_pos {d : ℕ} (y0 : Euc d) (hy0 : ∀ m : Lattice d, 0 < wsq (fun i => y0 i) m) :
    ∀ᶠ y in 𝓝 y0, ∀ m : Lattice d, 0 < wsq (fun i => y i) m := by
  set F : Set (Lattice d) := {m | π ^ 2 * wsq (fun i => y0 i) m < 1} with hF
  have hFfin : F.Finite := by
    have := Filter.eventually_cofinite.mp (eventually_one_le_wsq (d := d) (fun i => y0 i))
    exact this.subset fun m hm => not_le.mpr hm
  have hnear : ∀ᶠ y in 𝓝 y0, ∀ m ∈ F, 0 < wsq (fun i => y i) m := by
    rw [Filter.eventually_all_finite hFfin]
    intro m _
    have hc : Continuous fun y : Euc d => wsq (fun i => y i) m := by unfold wsq; fun_prop
    exact hc.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (hy0 m))
  have hball : ∀ᶠ y in 𝓝 y0, ‖y - y0‖ < 1/16 := by
    filter_upwards [Metric.ball_mem_nhds y0 (by norm_num : (0:ℝ) < 1/16)] with y hy
    simpa [dist_eq_norm] using hy
  filter_upwards [hnear, hball] with y h1 h2 m
  by_cases hm : m ∈ F
  · exact h1 m hm
  · have h3 : 1 ≤ π ^ 2 * wsq (fun i => y0 i) m := not_lt.mp hm
    rw [wsq_eq_norm_sq] at h3 ⊢
    have hv : 1/4 ≤ ‖y0 - Lattice.toEuc m‖ := by
      by_contra h
      push Not at h
      have h0 := norm_nonneg (y0 - Lattice.toEuc m)
      have hp : π ^ 2 < 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
      have hv2 : ‖y0 - Lattice.toEuc m‖ ^ 2 < 1/16 := by nlinarith
      have := mul_lt_mul'' hp hv2 (by positivity) (by positivity)
      linarith
    have h4 : ‖y0 - Lattice.toEuc m‖ ≤ ‖y0 - y‖ + ‖y - Lattice.toEuc m‖ := by
      have := norm_add_le (y0 - y) (y - Lattice.toEuc m)
      simpa using this
    rw [norm_sub_rev] at h2
    have : 0 < ‖y - Lattice.toEuc m‖ := by linarith
    positivity

theorem finite_ball_lattice {d : ℕ} (c : Euc d) (R : ℝ) :
    {m : Lattice d | ‖Lattice.toEuc m - c‖ < R}.Finite := by
  refine (Set.finite_Icc (fun i => ⌊c i⌋ - ⌈R⌉) (fun i => ⌈c i⌉ + ⌈R⌉)).subset ?_
  intro m hm
  simp only [mem_setOf_eq] at hm
  have hi : ∀ i, |((m i : ℤ) : ℝ) - c i| < R := fun i => by
    have := (PiLp.norm_apply_le (Lattice.toEuc m - c) i).trans_lt hm
    simpa [Lattice.toEuc, Real.norm_eq_abs] using this
  constructor
  · intro i
    have h1 := (abs_lt.mp (hi i)).1
    have h2 := Int.floor_le (c i)
    have h3 := Int.le_ceil R
    have : ((⌊c i⌋ - ⌈R⌉ : ℤ) : ℝ) ≤ ((m i : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · intro i
    have h1 := (abs_lt.mp (hi i)).2
    have h2 := Int.le_ceil (c i)
    have h3 := Int.le_ceil R
    have : ((m i : ℤ) : ℝ) ≤ ((⌈c i⌉ + ⌈R⌉ : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this

theorem contDiff_qp {d : ℕ} (p : Euc d) : ContDiff ℝ ∞' (qp p) := by
  unfold qp; exact contDiff_const.mul ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))

theorem contDiff_shift_images {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (c : Euc d) :
    ContDiff ℝ ∞' (fun z : Euc d => ∑' m : Lattice d, chi d z * Wt s (qp (Lattice.toEuc m - c) z)) := by
  choose K hK0 hK using fun n => image_term_bound_p (d := d) hs n
  choose M hM0 hM using fun n => enorm_pow_gauss_bound (2 * n)
  set v : ℕ → Lattice d → ℝ := fun n m =>
    K n * (‖Lattice.toEuc m - c‖ ^ (2 * n) * Real.exp (-2 * ‖Lattice.toEuc m - c‖ ^ 2)) with hv
  refine contDiff_tsum_of_eventually (v := v) (fun m => ?_) (fun n _ => ?_) (fun n _ => ?_)
  · exact contDiff_chi.mul ((contDiff_Wt s hs).comp (contDiff_qp _))
  · refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
      ((summable_gauss_wsq (fun i => c i) (c := 1/4) (by norm_num)).mul_left (K n * M n))
    · have := hK0 n
      simp only [hv]
      positivity
    · have he : 0 ≤ ‖Lattice.toEuc m - c‖ := norm_nonneg _
      have h1 := hM n _ he
      have h2 : Real.exp (-2 * ‖Lattice.toEuc m - c‖ ^ 2) ≤ Real.exp (-‖Lattice.toEuc m - c‖ ^ 2 / 2) := by
        rw [Real.exp_le_exp]; nlinarith [sq_nonneg ‖Lattice.toEuc m - c‖]
      have hw : wsq (fun i => c i) m = ‖Lattice.toEuc m - c‖ ^ 2 := by
        rw [wsq_eq_norm_sq, norm_sub_rev]
      simp only [hv]
      rw [hw]
      calc K n * (‖Lattice.toEuc m - c‖ ^ (2 * n) * Real.exp (-2 * ‖Lattice.toEuc m - c‖ ^ 2))
          ≤ K n * (‖Lattice.toEuc m - c‖ ^ (2 * n) * Real.exp (-‖Lattice.toEuc m - c‖ ^ 2 / 2)) := by
            have := hK0 n
            gcongr
        _ ≤ K n * (M n * Real.exp (-(1/4) * ‖Lattice.toEuc m - c‖ ^ 2)) := by
            have := hK0 n
            gcongr
        _ = _ := by ring_nf
  · refine Filter.eventually_cofinite.mpr ((finite_ball_lattice c 1).subset fun m hm => ?_)
    by_contra hlt
    apply hm
    have h1 : 1 ≤ ‖Lattice.toEuc m - c‖ := not_lt.mp hlt
    exact fun x => hK n _ h1 x

theorem contDiffAt_Wsum {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (y0 : Euc d)
    (hy0 : ∀ m : Lattice d, 0 < wsq (fun i => y0 i) m) :
    ContDiffAt ℝ ∞' (fun y : Euc d => ∑' m : Lattice d, Wfun s (π ^ 2 * wsq (fun i => y i) m)) y0 := by
  set p : Lattice d → Euc d := fun m => Lattice.toEuc m - y0 with hp
  have hq : ∀ m z, π ^ 2 * wsq (fun i => (y0 + z) i) m = qp (p m) z := by
    intro m z
    rw [wsq_eq_norm_sq]
    unfold qp
    rw [show y0 + z - Lattice.toEuc m = z - p m by simp only [hp]; abel]
  set F : Set (Lattice d) := {m | ‖p m‖ < 1/2} with hF
  have hFfin : F.Finite := finite_ball_lattice y0 (1/2)
  set B : Lattice d → Euc d → ℝ := fun m z => Wfun s (qp (p m) z) - Wt s (qp (p m) z) with hB
  have hB0 : ∀ m ∉ hFfin.toFinset, ∀ z : Euc d, ‖z‖ ≤ 1/16 → B m z = 0 := by
    intro m hm z hz
    simp only [Set.Finite.mem_toFinset, hF, mem_setOf_eq, not_lt] at hm
    have h1 : 1/2 - 1/16 ≤ ‖z - p m‖ := by
      have := norm_sub_norm_le (p m) z
      have e : ‖p m - z‖ = ‖z - p m‖ := norm_sub_rev _ _
      linarith
    have h2 : 1/2 ≤ qp (p m) z := by
      unfold qp
      have hπ : (9:ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
      nlinarith [mul_self_nonneg (‖z - p m‖ - 7/16)]
    simp only [hB, Wt, thetaCut_eq_one h2, one_mul, sub_self]
  have hsum : ∀ z : Euc d, ‖z‖ ≤ 1/16 →
      ∑' m : Lattice d, Wfun s (qp (p m) z) =
        ∑' m : Lattice d, chi d z * Wt s (qp (p m) z) + ∑ m ∈ hFfin.toFinset, B m z := by
    intro z hz
    have hW : Summable fun m : Lattice d => Wfun s (qp (p m) z) := by
      have := summable_Wfun_wsq hs (fun i => (y0 + z) i)
      simpa only [hq] using this
    have hBs : Summable fun m : Lattice d => B m z :=
      summable_of_ne_finset_zero (s := hFfin.toFinset) fun m hm => hB0 m hm z hz
    have hA : ∀ m, chi d z * Wt s (qp (p m) z) = Wfun s (qp (p m) z) - B m z := by
      intro m; rw [chi_one hz]; simp only [hB]; ring
    simp_rw [hA]
    rw [hW.tsum_sub hBs, tsum_eq_sum (s := hFfin.toFinset) (fun m hm => hB0 m hm z hz)]
    ring
  have hBsm : ∀ m : Lattice d, ContDiffAt ℝ ∞' (B m) 0 := by
    intro m
    have hpm : 0 < qp (p m) 0 := by
      have h := hy0 m
      rw [wsq_eq_norm_sq] at h
      unfold qp
      have : ‖(0 : Euc d) - p m‖ = ‖y0 - Lattice.toEuc m‖ := by
        rw [hp]; simp only [zero_sub, norm_neg]; rw [norm_sub_rev]
      rw [this]
      have : 0 < ‖y0 - Lattice.toEuc m‖ := by
        by_contra hle
        push Not at hle
        nlinarith [norm_nonneg (y0 - Lattice.toEuc m)]
      positivity
    have h1 : ContDiffAt ℝ ∞' (Wfun s) (qp (p m) 0) :=
      (contDiffOn_Wfun s hs).contDiffAt (Ioi_mem_nhds hpm)
    exact (h1.comp 0 (contDiff_qp _).contDiffAt).sub (((contDiff_Wt s hs).comp (contDiff_qp _)).contDiffAt)
  have h0 : ContDiffAt ℝ ∞' (fun z : Euc d => ∑' m : Lattice d, Wfun s (qp (p m) z)) 0 := by
    have hsm : ContDiffAt ℝ ∞' (fun z : Euc d => ∑' m : Lattice d, chi d z * Wt s (qp (p m) z) +
        ∑ m ∈ hFfin.toFinset, B m z) 0 :=
      (contDiff_shift_images hs y0).contDiffAt.add (ContDiffAt.sum fun m _ => hBsm m)
    refine hsm.congr_of_eventuallyEq ?_
    filter_upwards [Metric.closedBall_mem_nhds (0 : Euc d) (by norm_num : (0:ℝ) < 1/16)] with z hz
    rw [hsum z (by simpa using hz)]
  have h1 : ContDiffAt ℝ ∞' (fun z : Euc d => ∑' m : Lattice d,
      Wfun s (π ^ 2 * wsq (fun i => (y0 + z) i) m)) 0 := by
    simpa only [hq] using h0
  have h2 := ContDiffAt.comp y0 (g := fun z : Euc d => ∑' m : Lattice d,
      Wfun s (π ^ 2 * wsq (fun i => (y0 + z) i) m)) (f := fun y : Euc d => y - y0)
    (by simpa using h1) (contDiffAt_id.sub contDiffAt_const)
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  simp [Function.comp]


theorem contDiffAt_lift_g {d : ℕ} {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (y0 : Euc d)
    (hy0 : ∀ m : Lattice d, 0 < wsq (fun i => y0 i) m) :
    ContDiffAt ℝ ∞' (Torus.lift (periodicRiesz d s)) y0 := by
  have hW := contDiffAt_Wsum (s := s) hs0 y0 hy0
  have hF2 := (contDiff_F2 hsd).contDiffAt (x := y0)
  have hform : ContDiffAt ℝ ∞' (fun y : Euc d => subA d s * (π ^ ((d:ℝ)/2) *
      ∑' m : Lattice d, Wfun s (π ^ 2 * wsq (fun i => y i) m) - 1 / (((d:ℝ) - s)/2)) +
      ∑' k : Lattice d, coefF2 d s k * Torus.cosMode k (Torus.mk y)) y0 :=
    (contDiffAt_const.mul ((contDiffAt_const.mul hW).sub contDiffAt_const)).add hF2
  refine hform.congr_of_eventuallyEq ?_
  filter_upwards [eventually_wsq_pos y0 hy0] with y hy
  exact decomp1_d1 hd hs0 hsd y hy

/-! ### The one-dimensional embedding -/

/-- the point `y ∈ ℝ` as a vector of `ℝ¹ = Euc 1` -/
def ev (y : ℝ) : Euc 1 := WithLp.toLp 2 (fun _ => y)

@[simp] theorem ev_apply (y : ℝ) (i : Fin 1) : (ev y) i = y := rfl

theorem norm_ev (y : ℝ) : ‖ev y‖ = |y| := by
  rw [EuclideanSpace.norm_eq]
  simp [ev, Real.sqrt_sq_eq_abs]

theorem ev_eq (x : Euc 1) : x = ev (x 0) := by
  ext i
  fin_cases i
  rfl

theorem wsq_ev (y : ℝ) (m : Lattice 1) : wsq (fun i => (ev y) i) m = ((m 0 : ℤ) - y) ^ 2 := by
  simp [wsq]

theorem wsq_ev_pos {y : ℝ} (hy : ∀ n : ℤ, y ≠ n) (m : Lattice 1) : 0 < wsq (fun i => (ev y) i) m := by
  rw [wsq_ev]
  have : ((m 0 : ℤ) : ℝ) - y ≠ 0 := fun h => hy (m 0) (by linarith)
  positivity

theorem mk_ev_sub_int (y : ℝ) (n : ℤ) : Torus.mk (ev (y - n)) = Torus.mk (ev y) := by
  funext i
  simp only [Torus.mk, ev_apply]
  have : ((n : ℝ) : UnitAddCircle) = 0 := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨n, by simp⟩
  rw [AddCircle.coe_sub, this, sub_zero]

theorem mk_ev_ne_zero {y : ℝ} (hy : ∀ n : ℤ, y ≠ n) : Torus.mk (ev y) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp only [Torus.mk, ev_apply, Pi.zero_apply] at this
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp this
  exact hy n (by simpa using hn.symm)

theorem exists_gap {y0 : ℝ} (hy0 : ∀ n : ℤ, y0 ≠ n) : ∃ r : ℝ, 0 < r ∧ ∀ n : ℤ, 2 * r ≤ |y0 - n| := by
  have h1 : 0 < y0 - ⌊y0⌋ := by
    have := Int.floor_le y0
    have := hy0 ⌊y0⌋
    exact sub_pos.mpr (lt_of_le_of_ne (Int.floor_le y0) (Ne.symm this))
  have h2 : 0 < (⌊y0⌋ : ℝ) + 1 - y0 := by linarith [Int.lt_floor_add_one y0]
  refine ⟨min (y0 - ⌊y0⌋) ((⌊y0⌋ : ℝ) + 1 - y0) / 2, by positivity, fun n => ?_⟩
  rcases le_or_gt n ⌊y0⌋ with h | h
  · have : (n : ℝ) ≤ ⌊y0⌋ := by exact_mod_cast h
    have := min_le_left (y0 - ⌊y0⌋) ((⌊y0⌋ : ℝ) + 1 - y0)
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have : (⌊y0⌋ : ℝ) + 1 ≤ n := by exact_mod_cast h
    have := min_le_right (y0 - ⌊y0⌋) ((⌊y0⌋ : ℝ) + 1 - y0)
    rw [abs_of_nonpos (by linarith)]
    linarith


theorem psiG_bound_unif {d : ℕ} (j : Fin d) {c D : ℝ} (hc : 0 < c) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Euc d, (∀ i, |x i| ≤ 1/2) → c ≤ ‖x‖ → ‖x‖ ≤ D →
      ∀ u : ℝ, 0 < u → |psiG j (Torus.mk x) u| ≤ M * Real.exp (-u) := by
  obtain ⟨K, hK0, hK⟩ := psiG_small_bound (d := d) j
  obtain ⟨M1, hM10, hM1⟩ := psiG_large_bound (d := d) j
  set c0 := min (π ^ 2 * c ^ 2) (π ^ 2 / 8) with hc0
  have hc0p : 0 < c0 := lt_min (by positivity) (by positivity)
  set M0 := π ^ d * (2 * π ^ 2) * (|D| + K) * (((d + 1).factorial : ℝ) / c0 ^ (d + 1)) with hM0
  have hM00 : 0 ≤ M0 := by positivity
  refine ⟨M0 * Real.exp 1 + M1, by positivity, fun x hx hcx hxD u hu => ?_⟩
  have hxn : 0 < ‖x‖ := lt_of_lt_of_le hc hcx
  rcases le_total u 1 with h1 | h1
  · refine (hK x hx u hu h1).trans ?_
    set w := 1 / u with hw
    have hw0 : 0 < w := by positivity
    have hsq : Real.sqrt (π / u) ≤ π * w := by
      have h2 : 1 ≤ π / u := by rw [le_div_iff₀ hu]; linarith [Real.pi_gt_three]
      have h3 : Real.sqrt (π / u) ≤ π / u := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
      calc Real.sqrt (π / u) ≤ π / u := h3
        _ = π * w := by rw [hw]; ring
    have hc0x : c0 ≤ π ^ 2 * ‖x‖ ^ 2 := by
      refine (min_le_left _ _).trans ?_
      have : c ^ 2 ≤ ‖x‖ ^ 2 := by gcongr
      nlinarith [Real.pi_pos]
    have he1 : Real.exp (-(π ^ 2 * ‖x‖ ^ 2 / u)) ≤ Real.exp (-(c0 * w)) := by
      rw [Real.exp_le_exp, hw]
      have : c0 * (1 / u) ≤ π ^ 2 * ‖x‖ ^ 2 * (1 / u) := by gcongr
      have e : π ^ 2 * ‖x‖ ^ 2 / u = π ^ 2 * ‖x‖ ^ 2 * (1 / u) := by ring
      linarith
    have he2 : Real.exp (-(π ^ 2 / (8 * u))) ≤ Real.exp (-(c0 * w)) := by
      rw [Real.exp_le_exp, hw]
      have : c0 ≤ π ^ 2 / 8 := min_le_right _ _
      have : c0 * (1 / u) ≤ π ^ 2 / 8 * (1 / u) := by gcongr
      have e : π ^ 2 / (8 * u) = π ^ 2 / 8 * (1 / u) := by field_simp
      linarith
    have hpe := pow_exp_bound c0 hc0p (d + 1) w hw0.le
    have hxD' : ‖x‖ ≤ |D| := hxD.trans (le_abs_self D)
    have hfin : Real.sqrt (π / u) ^ d * (2 * π ^ 2 / u) *
        (‖x‖ * Real.exp (-(π ^ 2 * ‖x‖ ^ 2 / u)) + K * Real.exp (-(π ^ 2 / (8 * u)))) ≤ M0 := by
      calc Real.sqrt (π / u) ^ d * (2 * π ^ 2 / u) *
            (‖x‖ * Real.exp (-(π ^ 2 * ‖x‖ ^ 2 / u)) + K * Real.exp (-(π ^ 2 / (8 * u))))
          ≤ (π * w) ^ d * (2 * π ^ 2 * w) * (|D| * Real.exp (-(c0 * w)) + K * Real.exp (-(c0 * w))) := by
            have e : 2 * π ^ 2 / u = 2 * π ^ 2 * w := by rw [hw]; ring
            rw [e]
            gcongr
        _ = π ^ d * (2 * π ^ 2) * (|D| + K) * (w ^ (d + 1) * Real.exp (-(c0 * w))) := by ring
        _ ≤ M0 := by rw [hM0]; gcongr
    have : 1 ≤ Real.exp 1 * Real.exp (-u) := by
      rw [← Real.exp_add]; apply Real.one_le_exp; linarith
    nlinarith [Real.exp_pos (-u), Real.exp_pos 1]
  · refine (hM1 _ u h1).trans ?_
    have : 0 ≤ M0 * Real.exp 1 * Real.exp (-u) := by positivity
    nlinarith [Real.exp_pos (-u)]

theorem psiG_ev_unif {r : ℝ} (hr : 0 < r) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ, (∀ n : ℤ, r ≤ |y - n|) →
      ∀ u : ℝ, 0 < u → |psiG (0 : Fin 1) (Torus.mk (ev y)) u| ≤ M * Real.exp (-u) := by
  obtain ⟨M, hM0, hM⟩ := psiG_bound_unif (d := 1) (0 : Fin 1) (c := r) (D := 1/2) hr
  refine ⟨M, hM0, fun y hy u hu => ?_⟩
  have hn : |y - (round y : ℤ)| ≤ 1/2 := abs_sub_round y
  rw [← mk_ev_sub_int y (round y)]
  refine hM (ev (y - (round y : ℤ))) (fun i => by simpa using hn) ?_ ?_ u hu
  · rw [norm_ev]; exact hy _
  · rw [norm_ev]; exact hn

theorem hasDerivAt_psiFn_ev {t : ℝ} (ht : 0 < t) (y : ℝ) :
    HasDerivAt (fun y : ℝ => psiFn (Torus.mk (ev y)) t) (psiG (0 : Fin 1) (Torus.mk (ev y)) t) y := by
  have hdot : ∀ (k : Lattice 1) (z : ℝ), Lattice.dot k (ev z) = ((k 0 : ℤ) : ℝ) * z := by
    intro k z; simp [Lattice.dot]
  set g : Lattice 1 → ℝ → ℝ := fun k z =>
    if k = 0 then 0 else Real.exp (-t * Lattice.enorm k ^ 2) * Real.cos (2 * π * (((k 0 : ℤ) : ℝ) * z)) with hg
  set g' : Lattice 1 → ℝ → ℝ := fun k z =>
    -(Real.exp (-t * Lattice.enorm k ^ 2) * (2 * π * ((k 0 : ℤ) : ℝ)) * Real.sin (2 * π * (((k 0 : ℤ) : ℝ) * z)))
    with hg'
  have e1 : (fun z : ℝ => psiFn (Torus.mk (ev z)) t) = fun z => ∑' k, g k z := by
    funext z
    unfold psiFn
    refine tsum_congr fun k => ?_
    by_cases hk : k = 0
    · simp [hg, hk]
    · simp only [hg, hk, if_false, Torus.cosMode_mk, hdot]
  have e2 : psiG (0 : Fin 1) (Torus.mk (ev y)) t = ∑' k, g' k y := by
    unfold psiG
    refine tsum_congr fun k => ?_
    simp only [hg', Torus.sinMode_mk, hdot]
  rw [e1, e2]
  have hu : Summable fun k : Lattice 1 => 2 * π * (Lattice.enorm k ^ 1 * Real.exp (-t * Lattice.enorm k ^ 2)) :=
    (summable_pow_gauss_lattice 1 ht 1).mul_left _
  refine hasDerivAt_tsum (y₀ := y) (u := fun k : Lattice 1 => 2 * π * (Lattice.enorm k ^ 1 * Real.exp (-t * Lattice.enorm k ^ 2)))
    hu (fun k z => ?_) (fun k z => ?_) ?_ y
  · by_cases hk : k = 0
    · have h0 : ((k 0 : ℤ) : ℝ) = 0 := by simp [hk]
      simp only [hg, hg', hk, if_true, h0]
      simpa using hasDerivAt_const z (0 : ℝ)
    · simp only [hg, hg', hk, if_false]
      have h1 : HasDerivAt (fun z : ℝ => 2 * π * (((k 0 : ℤ) : ℝ) * z)) (2 * π * ((k 0 : ℤ) : ℝ)) z := by
        simpa using ((hasDerivAt_id z).const_mul ((k 0 : ℤ) : ℝ)).const_mul (2 * π)
      have h2 := (h1.cos).const_mul (Real.exp (-t * Lattice.enorm k ^ 2))
      convert h2 using 1
      ring
  · simp only [hg']
    have h1 := abs_coord_le_enorm k 0
    have he : 0 ≤ Lattice.enorm k := norm_nonneg _
    rw [norm_neg, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_mul,
      abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
    calc Real.exp (-t * Lattice.enorm k ^ 2) * (2 * π * |((k 0 : ℤ) : ℝ)|) *
          |Real.sin (2 * π * (((k 0 : ℤ) : ℝ) * z))|
        ≤ Real.exp (-t * Lattice.enorm k ^ 2) * (2 * π * Lattice.enorm k) * 1 := by
          gcongr
          exact Real.abs_sin_le_one _
      _ = _ := by rw [pow_one]; ring
  · refine Summable.of_norm_bounded (summable_gauss_lattice 1 t ht) fun k => ?_
    by_cases hk : k = 0
    · simp [hg, hk, (Real.exp_pos _).le]
    · simp only [hg, hk, if_false, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc _ ≤ Real.exp (-t * Lattice.enorm k ^ 2) * 1 := by gcongr; exact Real.abs_cos_le_one _
        _ = _ := mul_one _

theorem grad_apply_ev {s : ℝ} (hs1 : s < 1) {y : ℝ} (hy : ∀ n : ℤ, y ≠ n) :
    (periodicRieszGrad 1 s (Torus.mk (ev y))) 0 = subA 1 s *
      ∫ t in Ioi (0:ℝ), t ^ ((((1:ℕ):ℝ) - s) / 2 - 1) * psiG (0 : Fin 1) (Torus.mk (ev y)) t := by
  have hsd : s < ((1:ℕ):ℝ) := by simpa using hs1
  have hn : |y - (round y : ℤ)| ≤ 1/2 := abs_sub_round y
  have hne : ev (y - (round y : ℤ)) ≠ 0 := by
    intro h
    have : ‖ev (y - (round y : ℤ))‖ = 0 := by rw [h]; simp
    rw [norm_ev, abs_eq_zero] at this
    exact hy (round y) (by linarith)
  have h := periodicRieszGrad_eq hsd (ev (y - (round y : ℤ))) (fun i => by simpa using hn) hne
  rw [mk_ev_sub_int] at h
  rw [h]
  simp only [gradComp]

theorem hasDerivAt_g_ev {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) {y0 : ℝ} (hy0 : ∀ n : ℤ, y0 ≠ n) :
    HasDerivAt (fun y : ℝ => periodicRiesz 1 s (Torus.mk (ev y)))
      ((periodicRieszGrad 1 s (Torus.mk (ev y0))) 0) y0 := by
  have hsd : s < ((1:ℕ):ℝ) := by simpa using hs1
  obtain ⟨r, hr, hgap⟩ := exists_gap hy0
  obtain ⟨M, hM0, hM⟩ := psiG_ev_unif hr
  set a : ℝ := (((1:ℕ):ℝ) - s) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; push_cast; linarith
  have hball : ∀ y ∈ Metric.ball y0 r, ∀ n : ℤ, r ≤ |y - n| := by
    intro y hy n
    rw [Metric.mem_ball, Real.dist_eq] at hy
    have h1 := hgap n
    have h2 : |y0 - n| ≤ |y0 - y| + |y - n| := by
      have := abs_add_le (y0 - y) (y - n)
      simpa using this
    rw [abs_sub_comm y0 y] at h2
    linarith
  have hnz : ∀ y ∈ Metric.ball y0 r, ∀ n : ℤ, y ≠ n := by
    intro y hy n h
    have := hball y hy n
    rw [h, sub_self, abs_zero] at this
    linarith
  set F : ℝ → ℝ → ℝ := fun y t => t ^ (a - 1) * psiFn (Torus.mk (ev y)) t with hF
  set F' : ℝ → ℝ → ℝ := fun y t => t ^ (a - 1) * psiG (0 : Fin 1) (Torus.mk (ev y)) t with hF'
  have hcpow : ContinuousOn (fun t : ℝ => t ^ (a - 1)) (Ioi 0) :=
    continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht)
  have hFm : ∀ y, AEStronglyMeasurable (F y) (volume.restrict (Ioi 0)) := fun y =>
    (hcpow.mul (psi_continuousOn _)).aestronglyMeasurable measurableSet_Ioi
  have hF'm : ∀ y, AEStronglyMeasurable (F' y) (volume.restrict (Ioi 0)) := fun y =>
    (hcpow.mul (psiG_continuousOn _ _)).aestronglyMeasurable measurableSet_Ioi
  obtain ⟨M2, hM20, hM2⟩ := psi_bound (Torus.mk (ev y0)) (mk_ev_ne_zero hy0)
  have hint : Integrable (F y0) (volume.restrict (Ioi 0)) := by
    refine Integrable.mono' ((Real.GammaIntegral_convergent ha).const_mul M2) (hFm y0) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    have ht' : 0 < t := ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht' _)]
    have h1 := hM2 t ht'
    have h3 := Real.rpow_pos_of_pos ht' (a - 1)
    calc t ^ (a - 1) * |psiFn (Torus.mk (ev y0)) t| ≤ t ^ (a - 1) * (M2 * Real.exp (-t)) := by gcongr
      _ = _ := by ring
  have hdiff := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0:ℝ)))
    (F := F) (F' := F') (x₀ := y0) (s := Metric.ball y0 r) (bound := fun t => M * (Real.exp (-t) * t ^ (a - 1))) (Metric.ball_mem_nhds y0 hr)
    (Filter.Eventually.of_forall hFm) hint (hF'm y0) ?_ ((Real.GammaIntegral_convergent ha).const_mul M) ?_
  · have hderiv := hdiff.2
    have hg : (fun y : ℝ => periodicRiesz 1 s (Torus.mk (ev y))) =ᶠ[𝓝 y0]
        fun y => subA 1 s * ∫ t in Ioi (0:ℝ), F y t := by
      filter_upwards [Metric.ball_mem_nhds y0 hr] with y hy
      exact eq_integral_d1 le_rfl hs0 hsd _ (mk_ev_ne_zero (hnz y hy))
    rw [grad_apply_ev hs1 hy0]
    exact (hderiv.const_mul (subA 1 s)).congr_of_eventuallyEq hg
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    intro y hy
    have ht' : 0 < t := ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht' _)]
    have h1 := hM y (hball y hy) t ht'
    have h3 := Real.rpow_pos_of_pos ht' (a - 1)
    calc t ^ (a - 1) * |psiG (0 : Fin 1) (Torus.mk (ev y)) t| ≤ t ^ (a - 1) * (M * Real.exp (-t)) := by
          gcongr
      _ = _ := by ring
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    intro y _
    exact (hasDerivAt_psiFn_ev ht y).const_mul (t ^ (a - 1))


/-! ### Gradient on the torus -/

theorem gradient_periodic {d : ℕ} (f : Euc d → ℝ) (a : Euc d) (hf : ∀ z, f (z + a) = f z) (x : Euc d) :
    gradient f (x + a) = gradient f x := by
  have h : fderiv ℝ f (x + a) = fderiv ℝ f x := by
    rw [← fderiv_comp_add_right]
    congr 1
    funext z
    exact hf z
  simp [gradient, h]

theorem lift_grad {d : ℕ} (φ : Torus d → ℝ) (x : Euc d) :
    Torus.lift (Torus.grad φ) x = gradient (Torus.lift φ) x := by
  obtain ⟨m0, hm0⟩ := rep_mk_eq x
  simp only [Torus.lift, Function.comp, Torus.grad]
  rw [hm0]
  exact gradient_periodic (Torus.lift φ) (Lattice.toEuc m0) (fun z => Torus.lift_periodic φ z m0) x

theorem isSmooth_grad {d : ℕ} {φ : Torus d → ℝ} (h : Torus.IsSmooth φ) :
    Torus.IsSmooth (Torus.grad φ) := by
  unfold Torus.IsSmooth Torus.IsCk at h ⊢
  have : Torus.lift (Torus.grad φ) = gradient (Torus.lift φ) := funext (lift_grad φ)
  rw [this]
  have h1 : ContDiff ℝ ∞' (fderiv ℝ (Torus.lift φ)) := h.fderiv_right (by simp)
  exact ((InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff).comp h1

theorem gradient_zero_of_even {d : ℕ} (f : Euc d → ℝ) (hf : DifferentiableAt ℝ f 0)
    (heven : ∀ᶠ z in 𝓝 (0 : Euc d), f (-z) = f z) : gradient f 0 = 0 := by
  have h1 : HasFDerivAt (fun z => f (-z)) (-(fderiv ℝ f 0)) 0 := by
    have h := hf.hasFDerivAt
    have hn : HasFDerivAt (fun z : Euc d => -z) (-(ContinuousLinearMap.id ℝ (Euc d))) 0 :=
      (hasFDerivAt_id (0 : Euc d)).neg
    have := HasFDerivAt.comp (0 : Euc d) (g := f) (f := fun z : Euc d => -z) (by simpa using h) hn
    convert this using 1 <;> first | rfl | (ext v; simp)
  have h2 : HasFDerivAt f (-(fderiv ℝ f 0)) 0 :=
    h1.congr_of_eventuallyEq (heven.mono fun z hz => hz.symm)
  have h3 : fderiv ℝ f 0 = -(fderiv ℝ f 0) := h2.fderiv
  have h4 : fderiv ℝ f 0 = 0 := by
    ext v
    have := congrArg (fun L => L v) h3
    simp only [ContinuousLinearMap.neg_apply] at this
    simp only [ContinuousLinearMap.zero_apply]
    linarith
  simp [gradient, h4]

theorem contDiff_ev : ContDiff ℝ ∞' ev := by
  have : ev = fun y : ℝ => y • ev 1 := by
    funext y; ext i; simp [ev]
  rw [this]
  exact contDiff_id.smul contDiff_const

theorem hasDerivAt_ev (y : ℝ) : HasDerivAt ev (ev 1) y := by
  have : ev = fun y : ℝ => y • ev 1 := by
    funext y; ext i; simp [ev]
  rw [this]
  simpa using (hasDerivAt_id y).smul_const (ev 1)


theorem mk_ev_int (n : ℤ) : Torus.mk (ev (n : ℝ)) = 0 := by
  funext i
  simp only [Torus.mk, ev_apply, Pi.zero_apply]
  exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨n, by simp⟩

theorem mk_zero_euc : Torus.mk (0 : Euc 1) = 0 := by
  funext i
  simp [Torus.mk]

theorem mk_neg_euc (x : Euc 1) : Torus.mk (-x) = -Torus.mk x := by
  funext i
  simp [Torus.mk]

theorem off_int_of_mk_ne {x : Euc 1} (hx : Torus.mk x ≠ 0) : ∀ n : ℤ, x 0 ≠ n := by
  intro n hn
  apply hx
  have : x = ev n := calc x = ev (x 0) := ev_eq x
    _ = ev n := by rw [hn]
  rw [this]
  exact mk_ev_int n

theorem contDiffAt_H {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) {y0 : ℝ} (hy0 : ∀ n : ℤ, y0 ≠ n) :
    ContDiffAt ℝ ∞' (fun y : ℝ => periodicRiesz 1 s (Torus.mk (ev y))) y0 := by
  have hsd : s < ((1:ℕ):ℝ) := by simpa using hs1
  have h := contDiffAt_lift_g le_rfl hs0 hsd (ev y0) (fun m => wsq_ev_pos hy0 m)
  exact h.comp y0 contDiff_ev.contDiffAt

theorem periodicRieszGrad_ev_eq {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) {y : ℝ} (hy : ∀ n : ℤ, y ≠ n) :
    periodicRieszGrad 1 s (Torus.mk (ev y)) =
      ev (deriv (fun y : ℝ => periodicRiesz 1 s (Torus.mk (ev y))) y) := by
  rw [(hasDerivAt_g_ev hs0 hs1 hy).deriv]
  exact ev_eq _

theorem smoothOffZero_aux {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Torus.IsSmoothOffZero (periodicRieszGrad 1 s) := by
  intro x hx
  refine ContDiffAt.contDiffWithinAt ?_
  have hx' := off_int_of_mk_ne hx
  obtain ⟨r, hr, hgap⟩ := exists_gap hx'
  set H : ℝ → ℝ := fun y => periodicRiesz 1 s (Torus.mk (ev y)) with hH
  have hH0 : ContDiffAt ℝ ∞' H (x 0) := contDiffAt_H hs0 hs1 hx'
  have hdH : ContDiffAt ℝ ∞' (deriv H) (x 0) := by
    have h1 : ContDiffAt ℝ ∞' (fderiv ℝ H) (x 0) := hH0.fderiv_right (by simp)
    have h2 : ContDiffAt ℝ ∞' (fun y => fderiv ℝ H y 1) (x 0) := h1.clm_apply contDiffAt_const
    exact h2
  have hproj : ContDiff ℝ ∞' (fun z : Euc 1 => z 0) := (EuclideanSpace.proj (0 : Fin 1) : Euc 1 →L[ℝ] ℝ).contDiff
  have hF : ContDiffAt ℝ ∞' (fun z : Euc 1 => ev (deriv H (z 0))) x :=
    (contDiff_ev.contDiffAt).comp x (hdH.comp x hproj.contDiffAt :
      ContDiffAt ℝ ∞' (deriv H ∘ fun z : Euc 1 => z 0) x)
  refine hF.congr_of_eventuallyEq ?_
  have hnb : {z : Euc 1 | |z 0 - x 0| < r} ∈ 𝓝 x := by
    have hc : Continuous fun z : Euc 1 => |z 0 - x 0| := by fun_prop
    exact hc.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by simpa using hr))
  filter_upwards [hnb] with z hz
  have hz' : ∀ n : ℤ, z 0 ≠ n := by
    intro n hn
    have h1 := hgap n
    have h2 : |x 0 - n| ≤ |x 0 - z 0| + |z 0 - n| := by
      have := abs_add_le (x 0 - z 0) (z 0 - n)
      simpa using this
    have hz2 : |z 0 - x 0| < r := hz
    rw [hn] at h2 hz2
    rw [sub_self, abs_zero, abs_sub_comm (x 0) (n:ℝ)] at h2
    rw [abs_sub_comm] at hz2 h2
    linarith
  show periodicRieszGrad 1 s (Torus.mk z) = ev (deriv H (z 0))
  have : z = ev (z 0) := ev_eq z
  conv_lhs => rw [this]
  exact periodicRieszGrad_ev_eq hs0 hs1 hz'


theorem hasDerivAt_abs_rpow {s : ℝ} (hs : 0 < s) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun y : ℝ => |y| ^ (-s)) (-(s * |y| ^ (-s - 2)) * y) y := by
  rcases lt_or_gt_of_ne hy with h | h
  · -- y < 0
    have h1 : HasDerivAt (fun y : ℝ => (-y) ^ (-s)) ((-s) * (-y) ^ (-s - 1) * (-1)) y := by
      have := (Real.hasDerivAt_rpow_const (x := -y) (p := -s) (Or.inl (by linarith))).comp y (hasDerivAt_neg y)
      convert this using 1 <;> first | rfl | ring
    have h2 : (fun y : ℝ => |y| ^ (-s)) =ᶠ[𝓝 y] fun y => (-y) ^ (-s) := by
      filter_upwards [Iio_mem_nhds h] with z hz
      rw [abs_of_neg hz]
    refine (h1.congr_of_eventuallyEq h2).congr_deriv ?_
    rw [abs_of_neg h]
    have : (-y) ^ (-s - 1) = (-y) ^ (-s - 2) * (-y) := by
      rw [← Real.rpow_add_one (by linarith)]; congr 1; ring
    rw [this]; ring
  · have h1 : HasDerivAt (fun y : ℝ => y ^ (-s)) ((-s) * y ^ (-s - 1)) y :=
      Real.hasDerivAt_rpow_const (Or.inl h.ne')
    have h2 : (fun y : ℝ => |y| ^ (-s)) =ᶠ[𝓝 y] fun y => y ^ (-s) := by
      filter_upwards [Ioi_mem_nhds h] with z hz
      rw [abs_of_pos hz]
    refine (h1.congr_of_eventuallyEq h2).congr_deriv ?_
    rw [abs_of_pos h]
    have : y ^ (-s - 1) = y ^ (-s - 2) * y := by
      rw [← Real.rpow_add_one h.ne']; congr 1; ring
    rw [this]; ring

theorem hasDerivAt_neg_log_abs {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun y : ℝ => -Real.log |y|) (-(|y| ^ (-2 : ℝ)) * y) y := by
  have h1 : HasDerivAt (fun y : ℝ => -Real.log y) (-(y⁻¹)) y := (Real.hasDerivAt_log hy).neg
  have h2 : (fun y : ℝ => -Real.log |y|) = fun y => -Real.log y := by
    funext z; rw [Real.log_abs]
  rw [h2]
  refine h1.congr_deriv ?_
  rw [Real.rpow_neg (abs_nonneg y), Real.rpow_two, sq_abs]
  field_simp

theorem hasDerivAt_lift_ev {y : ℝ} {f : Euc 1 → ℝ} (hf : DifferentiableAt ℝ f (ev y)) :
    HasDerivAt (fun y : ℝ => f (ev y)) (gradient f (ev y) 0) y := by
  have h : HasFDerivAt f (InnerProductSpace.toDual ℝ (Euc 1) (gradient f (ev y))) (ev y) :=
    hf.hasGradientAt
  have := HasFDerivAt.comp_hasDerivAt y h (hasDerivAt_ev y)
  have hval : ((InnerProductSpace.toDual ℝ (Euc 1)) (gradient f (ev y))) (ev 1) = gradient f (ev y) 0 := by
    rw [InnerProductSpace.toDual_apply_apply, PiLp.inner_apply, Fin.sum_univ_one]
    simp only [ev]
    simp
  rw [hval] at this
  exact this


theorem local_grad_aux {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (sing : ℝ → ℝ) (r0 : Torus 1 → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hr0 : Torus.IsSmooth r0)
    (hloc : ∀ x : Euc 1, ‖x‖ < δ → x ≠ 0 →
      periodicRiesz 1 s (Torus.mk x) = sing ‖x‖ + r0 (Torus.mk x))
    (hsing : ∀ y : ℝ, y ≠ 0 → HasDerivAt (fun y => sing |y|)
      (-(KernelD1.rieszRadial s (ev y)) * y) y) :
    ∃ (r : Torus 1 → Euc 1) (δ : ℝ), 0 < δ ∧ Torus.IsSmooth r ∧ r 0 = 0 ∧
      ∀ x : Euc 1, ‖x‖ < δ → x ≠ 0 →
        periodicRieszGrad 1 s (Torus.mk x) = KernelD1.eucRieszGrad s x + r (Torus.mk x) := by
  have hc : ContDiff ℝ ∞' (Torus.lift r0) := hr0
  have hdiff : Differentiable ℝ (Torus.lift r0) := hc.differentiable (by simp)
  refine ⟨Torus.grad r0, min δ 1, lt_min hδ one_pos, isSmooth_grad hr0, ?_, ?_⟩
  · have h1 : Torus.grad r0 0 = gradient (Torus.lift r0) 0 := by
      have := lift_grad r0 0
      simpa [Torus.lift, mk_zero_euc] using this
    rw [h1]
    apply gradient_zero_of_even _ (hdiff 0)
    filter_upwards [Metric.ball_mem_nhds (0 : Euc 1) hδ] with z hz
    have hz' : ‖z‖ < δ := by simpa using hz
    show r0 (Torus.mk (-z)) = r0 (Torus.mk z)
    by_cases hz0 : z = 0
    · simp [hz0]
    · have h2 := hloc z hz' hz0
      have h3 := hloc (-z) (by simpa using hz') (neg_ne_zero.mpr hz0)
      have hg : periodicRiesz 1 s (Torus.mk (-z)) = periodicRiesz 1 s (Torus.mk z) := by
        rw [mk_neg_euc, periodicRiesz_neg]
      rw [norm_neg] at h3
      linarith
  · intro x hx hx0
    obtain ⟨y, rfl⟩ : ∃ y, x = ev y := ⟨x 0, ev_eq x⟩
    rw [norm_ev] at hx
    have hxδ : |y| < δ := lt_of_lt_of_le hx (min_le_left _ _)
    have hx1 : |y| < 1 := lt_of_lt_of_le hx (min_le_right _ _)
    have hy0 : y ≠ 0 := by
      intro h
      apply hx0
      ext i
      simp [h, ev]
    have hnz : ∀ n : ℤ, y ≠ n := by
      intro n h
      have h1 : |(n : ℝ)| < 1 := by rw [← h]; exact hx1
      have h2 : |n| < 1 := by exact_mod_cast h1
      have h3 : n = 0 := by
        rw [abs_lt] at h2
        omega
      apply hy0
      rw [h, h3]
      simp
    rw [periodicRieszGrad_ev_eq hs0 hs1 hnz]
    set H : ℝ → ℝ := fun y => periodicRiesz 1 s (Torus.mk (ev y)) with hH
    have hnb : ∀ᶠ z in 𝓝 y, |z| < δ ∧ z ≠ 0 := by
      refine Filter.Eventually.and ?_ (isOpen_ne.mem_nhds hy0)
      exact continuous_abs.continuousAt.preimage_mem_nhds (Iio_mem_nhds hxδ)
    have hHd : HasDerivAt H (-(KernelD1.rieszRadial s (ev y)) * y + gradient (Torus.lift r0) (ev y) 0) y := by
      have h1 := (hsing y hy0).add (hasDerivAt_lift_ev (f := Torus.lift r0) (y := y) (hdiff _))
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [hnb] with z hz
      have hzn : ev z ≠ 0 := by
        intro h
        apply hz.2
        have := congrArg (fun w : Euc 1 => w 0) h
        simpa [ev] using this
      have := hloc (ev z) (by rw [norm_ev]; exact hz.1) hzn
      rw [norm_ev] at this
      simpa [hH, Torus.lift] using this
    rw [hHd.deriv]
    have hg := lift_grad r0 (ev y)
    have hg0 : (Torus.grad r0 (Torus.mk (ev y))) 0 = gradient (Torus.lift r0) (ev y) 0 := by
      rw [← hg]; rfl
    ext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    simp only [KernelD1.eucRieszGrad, ev_apply, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul]
    rw [hg0]


end KernelD1Aux

end KernelD1Aux


section KernelD1Facts

variable {s : ℝ}

/-- `d = 1` version of `integral_periodicRiesz`: `g` is integrable with mean zero. -/
theorem integral_periodicRiesz_d1 (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Integrable (periodicRiesz 1 s) ∧ ∫ x, periodicRiesz 1 s x = 0 := by
  have hsd : s < ((1 : ℕ) : ℝ) := by simpa using hs1
  refine ⟨KernelD1Aux.integrable_d1 le_rfl hs0 hsd, ?_⟩
  have h := KernelD1Aux.integral_mode_d1 le_rfl hs0 hsd (0 : Lattice 1)
  simp only [neg_zero, Torus.mode_zero, one_mul] at h
  rw [integral_complex_ofReal] at h
  have h0 : rieszCoeff 1 s 0 = 0 := by simp [rieszCoeff]
  rw [h0] at h
  exact_mod_cast h

/-- `d = 1` version of `periodicRiesz_fourierCoeff`. -/
theorem periodicRiesz_fourierCoeff_d1 (hs0 : 0 ≤ s) (hs1 : s < 1) (k : Lattice 1) :
    Torus.funFourierCoeff (fun x => (periodicRiesz 1 s x : ℂ)) k = rieszCoeff 1 s k := by
  have hsd : s < ((1 : ℕ) : ℝ) := by simpa using hs1
  have h := KernelD1Aux.integral_mode_d1 le_rfl hs0 hsd k
  unfold Torus.funFourierCoeff UnitAddTorus.mFourierCoeff
  rw [Torus.volume_eq_pi_haar] at h
  simp only [smul_eq_mul]
  exact h

/-- **`d = 1` kernel input.** Local singularity of the periodic Riesz kernel on
`𝕋¹` for `0 < s < 1`: `g(x) = |x|^{-s} + r(x)` near `0`, `r` smooth (`H:eq:intro-kernel`,
M L181-186, in dimension one). -/
theorem periodicRiesz_local_singularity_d1 (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ (r : Torus 1 → ℝ) (δ : ℝ), 0 < δ ∧ Torus.IsSmooth r ∧
      ∀ x : Euc 1, ‖x‖ < δ → x ≠ 0 →
        periodicRiesz 1 s (Torus.mk x) = ‖x‖ ^ (-s) + r (Torus.mk x) := by
  have hsd : s < ((1 : ℕ) : ℝ) := by simpa using hs1
  exact KernelD1Aux.local_sing_d1 le_rfl hs0 hsd

/-- **`d = 1` kernel input.** Local singularity of the periodic logarithmic kernel
on `𝕋¹`: `g(x) = -log|x| + r(x)` near `0`, `r` smooth. -/
theorem periodicLog_local_singularity_d1 :
    ∃ (r : Torus 1 → ℝ) (δ : ℝ), 0 < δ ∧ Torus.IsSmooth r ∧
      ∀ x : Euc 1, ‖x‖ < δ → x ≠ 0 →
        periodicRiesz 1 0 (Torus.mk x) = -Real.log ‖x‖ + r (Torus.mk x) :=
  KernelD1Aux.log_sing_d1 le_rfl


/-- **`d = 1` kernel input.** The force `∇g` is smooth away from the origin on
`𝕋¹` for `0 ≤ s < 1` (the `d = 1` analogue of `periodicRieszGrad_smoothOffZero`). -/
theorem periodicRieszGrad_smoothOffZero_d1 (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Torus.IsSmoothOffZero (periodicRieszGrad 1 s) :=
  KernelD1Aux.smoothOffZero_aux hs0 hs1

/-- **`d = 1` kernel input.** Gradient bound `|∇g(x)| ≤ C(|x|^{-s-1} + 1)` on
`𝕋¹` for `0 ≤ s < 1` (the `d = 1` analogue of `periodicRiesz_grad_bound`). -/
theorem periodicRieszGrad_bound_d1 (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ∃ C : ℝ, ∀ x : Euc 1, x ≠ 0 → (∀ i, |x i| ≤ 1 / 2) →
      ‖periodicRieszGrad 1 s (Torus.mk x)‖ ≤ C * (‖x‖ ^ (-s - 1) + 1) := by
  have hsd : s < ((1 : ℕ) : ℝ) := by simpa using hs1
  exact KernelD1Aux.grad_bound_d1 le_rfl hs0 hsd

open KernelD1 in
/-- **`d = 1` kernel input.** Local form of the force on `𝕋¹`:
`∇g(mk x) = ∇g_E(x) + r(mk x)` near `0`, `r` smooth with `r(0) = 0`. -/
theorem periodicRieszGrad_local_singularity_d1 (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ∃ (r : Torus 1 → Euc 1) (δ : ℝ), 0 < δ ∧ Torus.IsSmooth r ∧ r 0 = 0 ∧
      ∀ x : Euc 1, ‖x‖ < δ → x ≠ 0 →
        periodicRieszGrad 1 s (Torus.mk x) = eucRieszGrad s x + r (Torus.mk x) := by
  by_cases hs : s = 0
  · subst hs
    obtain ⟨r0, δ, hδ, hr0, hloc⟩ := periodicLog_local_singularity_d1
    refine KernelD1Aux.local_grad_aux hs0 hs1 (fun r => -Real.log r) r0 δ hδ hr0 hloc ?_
    intro y hy
    have h := KernelD1Aux.hasDerivAt_neg_log_abs hy
    simpa [KernelD1.rieszRadial, KernelD1Aux.norm_ev] using h
  · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    obtain ⟨r0, δ, hδ, hr0, hloc⟩ := periodicRiesz_local_singularity_d1 hspos hs1
    refine KernelD1Aux.local_grad_aux hs0 hs1 (fun r => r ^ (-s)) r0 δ hδ hr0 hloc ?_
    intro y hy
    have h := KernelD1Aux.hasDerivAt_abs_rpow hspos hy
    simpa [KernelD1.rieszRadial, KernelD1Aux.norm_ev, hs] using h

end KernelD1Facts

end HRS
