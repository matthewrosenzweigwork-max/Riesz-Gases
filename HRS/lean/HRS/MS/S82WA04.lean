import HRS.MS.S82WK6
import HRS.MS.S82WM1
import HRS.MS.S82WN2

/-!
# S8.2 A04 (S82W), part 11: `gibbs_graph_closure` (frozen statement)
The cut-off approximants `Θ_n F` (S82WK6) are mollified in `C²` (S82WM1); the generator has mean zero on
smooth compactly supported functions (S82WN2), and the mean passes to the `L²` limit.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82W
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82U

lemma w_eLp_bound {α V : Type*} [MeasurableSpace α] [NormedAddCommGroup V] {P : Measure α}
    [IsProbabilityMeasure P] {g : α → V} {ε : ℝ} (hg : AEStronglyMeasurable g P)
    (h : ∀ᵐ x ∂P, ‖g x‖ ≤ ε) :
    eLpNorm g 2 P ≤ ENNReal.ofReal ε := by
  refine (eLpNorm_le_of_ae_bound hg h).trans ?_
  simp [measure_univ]

section approx
variable {d N : ℕ}

lemma wGb_contOn (hd : 2 ≤ d) (a : ℝ) : ContinuousOn (wGb d N a) (eucCollisionSet d N)ᶜ := by
  refine continuousOn_finsetSum _ fun i _ => ContinuousOn.add (continuousOn_finsetSum _ fun j hj => ?_)
    (continuous_const.mul continuous_norm).continuousOn
  refine continuousOn_const.mul (ContinuousOn.rpow_const ?_ fun X hX => Or.inl ?_)
  · exact (continuous_norm.comp ((continuous_apply i).sub (continuous_apply j))).continuousOn
  · exact norm_ne_zero_iff.2 (sub_ne_zero.2 fun h => hX ⟨i, j, (Finset.ne_of_mem_erase hj).symm, h⟩)

/-- the three `L²(canonicalP)` distances of a smooth approximant of a `C²` compactly supported function
are small -/
lemma w_smooth_approx (hd : 2 ≤ d) (hN : 0 < N) {a beta : ℝ} (ha : 0 < a) (hbeta : 0 < beta)
    {f : EucConfig d N → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hfD : tsupport f ⊆ (eucCollisionSet d N)ᶜ) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : EucConfig d N → ℝ, ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧
      tsupport h ⊆ (eucCollisionSet d N)ᶜ ∧
      eLpNorm (fun X => h X - f X) 2 (canonicalP d N a beta) ≤ ENNReal.ofReal ε ∧
      (∀ i, eLpNorm (fun X => Phase2S82.configGrad h X i - Phase2S82.configGrad f X i) 2
        (canonicalP d N a beta) ≤ ENNReal.ofReal ε) ∧
      eLpNorm (fun X => particleGenerator (quadraticGradientDyn d (criticalS d) a beta) h X -
        particleGenerator (quadraticGradientDyn d (criticalS d) a beta) f X) 2 (canonicalP d N a beta) ≤
        ENNReal.ofReal ε := by
  haveI := u4_prob (N := N) hd ha hbeta
  obtain ⟨K, hKc, hKD, hfK, hK⟩ := w_density (volume : Measure (EucConfig d N)) u4_D_open hf hc hfD
  obtain ⟨C0, hC0⟩ := hKc.exists_bound_of_continuousOn ((wGb_contOn (N := N) hd a).mono hKD)
  set Cb : ℝ := max C0 0 with hCb
  have hCb0 : 0 ≤ Cb := le_max_right _ _
  have hCbK : ∀ x ∈ K, wGb d N a x ≤ Cb := fun x hx =>
    (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC0 x hx) |>.trans (le_max_left _ _)
  set Cδ : ℝ := 1 + beta⁻¹ * N * d + Cb with hCδ
  have hν : 0 ≤ beta⁻¹ * N * d := by positivity
  have hCδ1 : 1 ≤ Cδ := by linarith
  have hδ : 0 < ε / Cδ := div_pos hε (by linarith)
  obtain ⟨h, hsm, hhK, hjet⟩ := hK (ε / Cδ) hδ
  have hh2 : ContDiff ℝ 2 h := hsm.of_le (by norm_num)
  have hcd : ContDiffOn ℝ 2 h (eucCollisionSet d N)ᶜ := hh2.contDiffOn
  have hfcd : ContDiffOn ℝ 2 f (eucCollisionSet d N)ᶜ := hf.contDiffOn
  have hKc' : IsCompact K := hKc
  have hhc : HasCompactSupport h := hKc'.of_isClosed_subset (isClosed_tsupport h) hhK
  have hae : ∀ᵐ X ∂(canonicalP d N a beta), X ∉ eucCollisionSet d N := by
    rw [ae_iff]; simpa using u4_P_coll hd N a beta
  have hδε : ε / Cδ ≤ ε := div_le_self hε.le hCδ1
  have hCδδ : Cδ * (ε / Cδ) = ε := by field_simp
  refine ⟨h, hsm, hhc, hhK.trans hKD, ?_, fun i => ?_, ?_⟩
  · refine w_eLp_bound (ε := ε) (u4_aesm_of_contOn (d := d) (N := N) (a := a) (beta := beta) hd
      (hcd.continuousOn.sub hfcd.continuousOn)) ?_
    filter_upwards [hae] with X hX
    rw [Real.norm_eq_abs]; exact (hjet X).1.trans hδε
  · refine w_eLp_bound (ε := ε) (u4_aesm_of_contOn (d := d) (N := N) (a := a) (beta := beta) hd
      ((w_grad_cont hcd i).sub (w_grad_cont hfcd i))) ?_
    filter_upwards [hae] with X hX
    rw [← w_configGrad_sub hcd hfcd hX i]
    refine (u4_configGrad_norm_le (hcd.sub hfcd) hX i).trans ?_
    rw [w_fderiv_sub hcd hfcd hX]
    exact (hjet X).2.1.trans hδε
  · refine w_eLp_bound (ε := ε) (u4_aesm_of_contOn (d := d) (N := N) (a := a) (beta := beta) hd
      ((w_gen_cont hd a beta hcd).sub (w_gen_cont hd a beta hfcd))) ?_
    filter_upwards [hae] with X hX
    rw [← w_gen_sub hcd hfcd hX, Real.norm_eq_abs]
    have hgb := w_gen_bound hd hN ha.le beta hbeta (hcd.sub hfcd) hX
    rw [w_j2, w_fderiv2_sub hcd hfcd hX, w_fderiv_sub hcd hfcd hX] at hgb
    have hj1 := (hjet X).2.1
    have hj2 := (hjet X).2.2
    refine hgb.trans ?_
    have hG0 := wGb_nonneg hd ha.le (N := N) X
    have hterm : wGb d N a X * ‖fderiv ℝ h X - fderiv ℝ f X‖ ≤ Cb * (ε / Cδ) := by
      by_cases hXK : X ∈ K
      · exact mul_le_mul (hCbK X hXK) hj1 (norm_nonneg _) hCb0
      · have hz : fderiv ℝ h X - fderiv ℝ f X = 0 := by
          have e1 : fderiv ℝ h X = 0 := by
            have : h =ᶠ[𝓝 X] fun _ => (0 : ℝ) := by
              filter_upwards [(isClosed_tsupport h).isOpen_compl.mem_nhds (fun hx => hXK (hhK hx))] with y hy
              exact image_eq_zero_of_notMem_tsupport hy
            rw [this.fderiv_eq]; simp
          have e2 : fderiv ℝ f X = 0 := by
            have : f =ᶠ[𝓝 X] fun _ => (0 : ℝ) := by
              filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds (fun hx => hXK (hfK hx))] with y hy
              exact image_eq_zero_of_notMem_tsupport hy
            rw [this.fderiv_eq]; simp
          rw [e1, e2, sub_zero]
        rw [hz]; simp only [norm_zero, mul_zero]; positivity
    have hterm2 : beta⁻¹ * N * d * ‖fderiv ℝ (fderiv ℝ h) X - fderiv ℝ (fderiv ℝ f) X‖ ≤
        beta⁻¹ * N * d * (ε / Cδ) := mul_le_mul_of_nonneg_left hj2 hν
    calc _ ≤ beta⁻¹ * N * d * (ε / Cδ) + Cb * (ε / Cδ) := add_le_add hterm2 hterm
      _ ≤ Cδ * (ε / Cδ) := by nlinarith [div_pos hε (by linarith : 0 < Cδ)]
      _ = ε := hCδδ

section assembly
variable {d N : ℕ}

lemma w_tendstoL2_of_eLp {P : Measure (EucConfig d N)} {Fn : ℕ → EucConfig d N → ℝ} {F : EucConfig d N → ℝ}
    (hF : AEStronglyMeasurable F P) (hm : ∀ n, AEStronglyMeasurable (fun X => Fn n X - F X) P)
    (h : Tendsto (fun n => eLpNorm (fun X => Fn n X - F X) 2 P) atTop (𝓝 0)) : HRS.TendstoL2 P Fn F := by
  refine ⟨hF, ?_⟩
  have e : ∀ n, ∫⁻ Y, ‖Fn n Y - F Y‖ₑ ^ 2 ∂P = eLpNorm (fun X => Fn n X - F X) 2 P ^ (2 : ℝ) := by
    intro n
    rw [w_eLp_two (hm n), ← ENNReal.rpow_mul]
    norm_num
  simp_rw [e]
  have := (ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0 |>.comp h
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at this
  exact this

lemma w_tri {α V : Type*} [MeasurableSpace α] [NormedAddCommGroup V] {P : Measure α} {u v w : α → V} :
    eLpNorm (fun x => u x - w x) 2 P ≤
      eLpNorm (fun x => u x - v x) 2 P + eLpNorm (fun x => v x - w x) 2 P := by
  have := eLpNorm_add_le (f := fun x => u x - v x) (g := fun x => v x - w x) (μ := P) (p := 2) (by norm_num)
  have e : ((fun x => u x - v x) + fun x => v x - w x) = fun x => u x - w x := by
    funext x; simp
  rwa [e] at this

lemma w_squeeze {a b c : ℕ → ℝ≥0∞} (hb : Tendsto b atTop (𝓝 0)) (hc : Tendsto c atTop (𝓝 0))
    (h : ∀ n, a n ≤ b n + c n) : Tendsto a atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using hb.add hc)
    (fun n => bot_le) h

lemma w_inv_tendsto : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
  have := (ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  simpa using this

end assembly

end approx

end HRS.MS.S82W

namespace HRS.MS.Phase2S82
open HRS HRS.Whole

/-- the pole envelope used in the statement of `gibbs_graph_closure` (verbatim from the skeleton) -/
def configPoleEnvelope {d N : ℕ} (M : ℝ) (X : EucConfig d N) : ℝ :=
  (1 + ‖X‖) ^ M * ∏ i, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-M))

theorem gibbs_graph_closure (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N)
    (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (F : EucConfig d N → ℝ)
    (hF : ContDiffOn ℝ 2 F (eucCollisionSet d N)ᶜ)
    (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hb : ∀ X, X ∉ eucCollisionSet d N →
      |F X| + ‖fderiv ℝ F X‖ + ‖iteratedFDeriv ℝ 2 F X‖ ≤
        A * configPoleEnvelope M X) :
    GeneratorClosure a beta F
      (particleGenerator (quadraticGradientDyn d (criticalS d) a beta) F) ∧
      ∫ X, particleGenerator (quadraticGradientDyn d (criticalS d) a beta) F X
        ∂canonicalP d N a beta = 0 := by
  have hN0 : 0 < N := by omega
  haveI := HRS.MS.S82U.u4_prob (N := N) hd ha hbeta
  have hb' : ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
      |F X| + ‖fderiv ℝ F X‖ + ‖iteratedFDeriv ℝ 2 F X‖ ≤ A * HRS.MS.S82U.u4Env M M X := hb
  obtain ⟨h1, h2, h3⟩ := HRS.MS.S82U.u4_L2 hd hN0 ha hbeta hF hM hA hb'
  obtain ⟨f, hfprop, hf0, hf1, hf2⟩ := HRS.MS.S82W.w_cutoff_seq hd hN0 ha hbeta hF hM hA hb'
  set P := canonicalP d N a beta with hP
  have hex : ∀ n : ℕ, ∃ h : EucConfig d N → ℝ, ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧
      tsupport h ⊆ (eucCollisionSet d N)ᶜ ∧
      eLpNorm (fun X => h X - f n X) 2 P ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) ∧
      (∀ i, eLpNorm (fun X => Phase2S82.configGrad h X i - Phase2S82.configGrad (f n) X i) 2 P ≤
        ENNReal.ofReal (1 / ((n : ℝ) + 1))) ∧
      eLpNorm (fun X => particleGenerator (quadraticGradientDyn d (criticalS d) a beta) h X -
        particleGenerator (quadraticGradientDyn d (criticalS d) a beta) (f n) X) 2 P ≤
        ENNReal.ofReal (1 / ((n : ℝ) + 1)) := fun n =>
    HRS.MS.S82W.w_smooth_approx hd hN0 ha hbeta (hfprop n).1 (hfprop n).2.1 (hfprop n).2.2
      (by positivity)
  choose Fn hFn using hex
  have hFcd : ContDiffOn ℝ 2 F (eucCollisionSet d N)ᶜ := hF
  have hfcd : ∀ n, ContDiffOn ℝ 2 (f n) (eucCollisionSet d N)ᶜ := fun n => (hfprop n).1.contDiffOn
  have hFncd : ∀ n, ContDiffOn ℝ 2 (Fn n) (eucCollisionSet d N)ᶜ := fun n =>
    ((hFn n).1.of_le (by norm_num)).contDiffOn
  have aesm0 : ∀ φ ψ : EucConfig d N → ℝ, ContDiffOn ℝ 2 φ (eucCollisionSet d N)ᶜ →
      ContDiffOn ℝ 2 ψ (eucCollisionSet d N)ᶜ → AEStronglyMeasurable (fun X => φ X - ψ X) P :=
    fun φ ψ hφ hψ => HRS.MS.S82U.u4_aesm_of_contOn (d := d) (N := N) (a := a) (beta := beta) hd
      (hφ.continuousOn.sub hψ.continuousOn)
  have aesm1 : ∀ (φ ψ : EucConfig d N → ℝ), ContDiffOn ℝ 2 φ (eucCollisionSet d N)ᶜ →
      ContDiffOn ℝ 2 ψ (eucCollisionSet d N)ᶜ → ∀ i, AEStronglyMeasurable
      (fun X => Phase2S82.configGrad φ X i - Phase2S82.configGrad ψ X i) P :=
    fun φ ψ hφ hψ i => HRS.MS.S82U.u4_aesm_of_contOn (d := d) (N := N) (a := a) (beta := beta) hd
      ((HRS.MS.S82W.w_grad_cont hφ i).sub (HRS.MS.S82W.w_grad_cont hψ i))
  have aesm2 : ∀ φ ψ : EucConfig d N → ℝ, ContDiffOn ℝ 2 φ (eucCollisionSet d N)ᶜ →
      ContDiffOn ℝ 2 ψ (eucCollisionSet d N)ᶜ → AEStronglyMeasurable (fun X =>
        particleGenerator (quadraticGradientDyn d (criticalS d) a beta) φ X -
          particleGenerator (quadraticGradientDyn d (criticalS d) a beta) ψ X) P :=
    fun φ ψ hφ hψ => HRS.MS.S82U.u4_aesm_of_contOn (d := d) (N := N) (a := a) (beta := beta) hd
      ((HRS.MS.S82W.w_gen_cont hd a beta hφ).sub (HRS.MS.S82W.w_gen_cont hd a beta hψ))
  -- the three convergences
  have T0 : Tendsto (fun n => eLpNorm (fun X => Fn n X - F X) 2 P) atTop (𝓝 0) :=
    HRS.MS.S82W.w_squeeze HRS.MS.S82W.w_inv_tendsto hf0 fun n =>
      HRS.MS.S82W.w_tri.trans (add_le_add (hFn n).2.2.2.1 le_rfl)
  have T1 : ∀ i, Tendsto (fun n => eLpNorm (fun X => Phase2S82.configGrad (Fn n) X i -
      Phase2S82.configGrad F X i) 2 P) atTop (𝓝 0) := fun i =>
    HRS.MS.S82W.w_squeeze HRS.MS.S82W.w_inv_tendsto (hf1 i) fun n =>
      HRS.MS.S82W.w_tri.trans (add_le_add ((hFn n).2.2.2.2.1 i) le_rfl)
  have T2 : Tendsto (fun n => eLpNorm (fun X => particleGenerator (quadraticGradientDyn d (criticalS d) a beta)
      (Fn n) X - particleGenerator (quadraticGradientDyn d (criticalS d) a beta) F X) 2 P) atTop (𝓝 0) :=
    HRS.MS.S82W.w_squeeze HRS.MS.S82W.w_inv_tendsto hf2 fun n =>
      HRS.MS.S82W.w_tri.trans (add_le_add (hFn n).2.2.2.2.2 le_rfl)
  have hFsm : AEStronglyMeasurable F P := h1.aestronglyMeasurable
  have hLFsm := h2.aestronglyMeasurable
  have TL0 : HRS.TendstoL2 P Fn F := HRS.MS.S82W.w_tendstoL2_of_eLp hFsm
    (fun n => aesm0 (Fn n) F (hFncd n) hFcd) T0
  have TL2 : HRS.TendstoL2 P (fun n => particleGenerator (quadraticGradientDyn d (criticalS d) a beta) (Fn n))
      (particleGenerator (quadraticGradientDyn d (criticalS d) a beta) F) :=
    HRS.MS.S82W.w_tendstoL2_of_eLp hLFsm (fun n => aesm2 (Fn n) F (hFncd n) hFcd) T2
  refine ⟨⟨h1, h2, h3, Fn, fun n => ⟨(hFn n).1, (hFn n).2.1, (hFn n).2.2.1⟩, TL0, TL2, T1⟩, ?_⟩
  -- mean zero
  have hmean : ∀ n, ∫ X, particleGenerator (quadraticGradientDyn d (criticalS d) a beta) (Fn n) X ∂P = 0 :=
    fun n => HRS.MS.S82W.w_mean_zero_smooth hd hbeta ((hFn n).1.of_le (by norm_num)) (hFn n).2.1
      (hFn n).2.2.1
  have hL1 : Tendsto (fun n => ∫⁻ X, ‖particleGenerator (quadraticGradientDyn d (criticalS d) a beta) (Fn n) X -
      particleGenerator (quadraticGradientDyn d (criticalS d) a beta) F X‖ₑ ∂P) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds T2 (fun n => bot_le) (fun n => ?_)
    have := eLpNorm_le_eLpNorm_of_exponent_le (μ := P) (p := 1) (q := 2)
      (f := fun X => particleGenerator (quadraticGradientDyn d (criticalS d) a beta) (Fn n) X -
        particleGenerator (quadraticGradientDyn d (criticalS d) a beta) F X) (by norm_num)
    rwa [eLpNorm_one_eq_lintegral_enorm (aesm2 (Fn n) F (hFncd n) hFcd)] at this
  have hint : ∀ᶠ n in atTop, Integrable (fun X => particleGenerator (quadraticGradientDyn d (criticalS d) a beta)
      (Fn n) X) P := by
    filter_upwards [T2.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < 1 from one_pos))] with n hn
    have hmem : MemLp (fun X => particleGenerator (quadraticGradientDyn d (criticalS d) a beta) (Fn n) X -
        particleGenerator (quadraticGradientDyn d (criticalS d) a beta) F X) 2 P :=
      hn.trans ENNReal.one_lt_top
    have := (hmem.add h2).integrable (by norm_num)
    convert this using 1
    funext X; simp
  have hT := tendsto_integral_of_L1 (fun X => particleGenerator (quadraticGradientDyn d (criticalS d) a beta) F X)
    hLFsm hint hL1
  exact tendsto_nhds_unique hT (tendsto_const_nhds.congr fun n => (hmean n).symm)

end HRS.MS.Phase2S82
