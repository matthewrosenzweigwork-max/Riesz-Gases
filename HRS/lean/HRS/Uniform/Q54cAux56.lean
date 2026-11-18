import HRS.Uniform.Q54cAux55

/-!
# Q54c, part 56: weak time-continuity of a mean-field solution
-/

noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS.Uniform.Q54c

open HRS HRS.PDE

variable {d : ℕ}

theorem isCk2_const (c : ℝ) : Torus.IsCk 2 (fun _ : Torus d => c) := by
  unfold Torus.IsCk Torus.lift; exact contDiff_const

theorem isCk2_add {f g : Torus d → ℝ} (hf : Torus.IsCk 2 f) (hg : Torus.IsCk 2 g) :
    Torus.IsCk 2 (fun x => f x + g x) := by
  unfold Torus.IsCk Torus.lift at *; exact hf.add hg

theorem isCk2_sub {f g : Torus d → ℝ} (hf : Torus.IsCk 2 f) (hg : Torus.IsCk 2 g) :
    Torus.IsCk 2 (fun x => f x - g x) := by
  unfold Torus.IsCk Torus.lift at *; exact hf.sub hg

theorem isCk2_const_mul {f : Torus d → ℝ} (a : ℝ) (hf : Torus.IsCk 2 f) :
    Torus.IsCk 2 (fun x => a * f x) := by
  unfold Torus.IsCk Torus.lift at *; exact contDiff_const.mul hf

theorem exists_isCk_approx (ψ : Torus d → ℝ) (hψ : Continuous ψ) (ε : ℝ) (hε : 0 < ε) :
    ∃ χ : Torus d → ℝ, Torus.IsCk 2 χ ∧ ∀ x, |ψ x - χ x| ≤ ε := by
  let F : C(Torus d, ℂ) := ⟨fun x => (ψ x : ℂ), Complex.continuous_ofReal.comp hψ⟩
  have hF : F ∈ (Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := Fin d)))).topologicalClosure := by
    rw [UnitAddTorus.span_mFourier_closure_eq_top]; trivial
  have hF' : F ∈ closure ((Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := Fin d))) :
      Submodule ℂ C(Torus d, ℂ)) : Set C(Torus d, ℂ)) := by
    rw [← Submodule.topologicalClosure_coe]; exact hF
  obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.1 hF' ε hε
  have key : ∀ b ∈ Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := Fin d))),
      Torus.IsCk 2 (fun x => (b x).re) ∧ Torus.IsCk 2 (fun x => (b x).im) := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact ⟨by exact_mod_cast HRS.PDE.MFPair.isCk_cos_ps (d := d) k 2,
        by exact_mod_cast HRS.PDE.MFPair.isCk_sin_ps (d := d) k 2⟩
    | zero =>
      exact ⟨isCk2_const 0, isCk2_const 0⟩
    | add x y _ _ hx hy =>
      exact ⟨by simpa [Complex.add_re] using isCk2_add hx.1 hy.1,
        by simpa [Complex.add_im] using isCk2_add hx.2 hy.2⟩
    | smul a x _ hx =>
      exact ⟨by simpa [Complex.mul_re] using isCk2_sub (isCk2_const_mul a.re hx.1) (isCk2_const_mul a.im hx.2),
        by simpa [Complex.mul_im] using isCk2_add (isCk2_const_mul a.re hx.2) (isCk2_const_mul a.im hx.1)⟩
  refine ⟨fun x => (b x).re, (key b hb).1, fun x => ?_⟩
  have h1 : dist (F x) (b x) ≤ dist F b := ContinuousMap.dist_apply_le_dist x
  have h2 : |ψ x - (b x).re| ≤ dist (F x) (b x) := by
    rw [Complex.dist_eq]
    have : ψ x - (b x).re = ((F x) - b x).re := by simp [F]
    rw [this]
    exact Complex.abs_re_le_norm _
  linarith

theorem isCk_continuous {k : WithTop ℕ∞} {f : Torus d → ℝ} (hf : Torus.IsCk k f) : Continuous f :=
  Torus.continuous_of_continuous_lift hf.continuous

/-- A weak solution of the mean-field equation with `C^{d+1}` regular densities is weakly continuous in time. -/
theorem weak_continuity (D : DynData d) (hd : 1 ≤ d) (T Λ : ℝ) (hT : 0 ≤ T) (K : ℕ) (hK : d + 1 ≤ K)
    (ρ : ℝ → Torus d → ℝ) (hmf : IsMeanFieldSolution D T ρ) (hreg : IsRegularMF K Λ T ρ)
    (hV : Torus.IsCk 1 D.V) :
    ∀ ψ : Torus d → ℝ, Continuous ψ → ContinuousOn (fun t => ∫ x, ψ x * ρ t x) (Icc 0 T) := by
  have hK1 : 1 ≤ K := by omega
  have hρ : ∀ r ∈ Icc 0 T, IsProbDensity (ρ r) ∧ Torus.IsCk K (ρ r) ∧ Torus.cbNorm K (ρ r) ≤ Λ :=
    fun r hr => ⟨hmf.density r hr, (hreg r hr).1, (hreg r hr).2⟩
  have hρc : ∀ r ∈ Icc 0 T, Continuous (ρ r) := fun r hr => isCk_continuous (hρ r hr).2.1
  have hrel : ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ → ∀ t ∈ Icc 0 T,
      (∫ x, ψ x * ρ t x) - (∫ x, ψ x * ρ 0 x) = ∫ r in Icc 0 t, wkG D ρ ψ r := by
    intro ψ hψ t ht
    have := weak_eq_wkG hmf hψ ht
    rwa [pair_wDR (hmf.density t ht), pair_wDR (hmf.density 0 ⟨le_rfl, hT⟩)] at this
  have hbd : ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ → ∃ C : ℝ, ∀ r ∈ Icc 0 T, |wkG D ρ ψ r| ≤ C :=
    fun ψ hψ => wkG_bound hd D T Λ K hK1 hV ρ hρ ψ hψ
  have hmeas : ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ → Measurable (fun r => ∫ x, ψ x * ρ (clampT T r) x) := by
    intro ψ hψ
    obtain ⟨C, hC⟩ := hbd ψ hψ
    obtain ⟨f', hf', hff'⟩ := junk_interval_measurable hT (wkG D ρ ψ) (fun t => ∫ x, ψ x * ρ t x) hC
      (hrel ψ hψ)
    have : (fun r => ∫ x, ψ x * ρ (clampT T r) x) = fun r => f' (clampT T r) := by
      funext r; exact (hff' _ (clampT_mem hT r)).symm
    rw [this]; exact hf'.comp (continuous_clampT T).measurable
  set ρt : ℝ → Torus d → ℝ := fun r => ρ (clampT T r) with hρt
  have hpt : ∀ x, Measurable fun r => ρt r x :=
    measurable_pt_of_modes ρt (fun r => hρc _ (clampT_mem hT r))
      (fun r => summable_fcoef_of_ck (ContDiff.of_le (hρ _ (clampT_mem hT r)).2.1 (by exact_mod_cast hK)))
      (fun r => (hmf.density _ (clampT_mem hT r)).integral_one)
      (fun k => hmeas _ (by exact_mod_cast isCk_realMode k 2))
  have hcont2 : ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ → ContinuousOn (fun t => ∫ x, ψ x * ρ t x) (Icc 0 T) := by
    intro ψ hψ
    obtain ⟨C, hC⟩ := hbd ψ hψ
    have hmG : Measurable (wkG D ρt ψ) := measurable_wkG D ψ hψ hV ρt
      (fun r => hmf.density _ (clampT_mem hT r)) (fun r => hρc _ (clampT_mem hT r)) hpt
    have hae : AEStronglyMeasurable (wkG D ρ ψ) (volume.restrict (Icc 0 T)) := by
      refine hmG.aestronglyMeasurable.congr ?_
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc]
      exact Eventually.of_forall fun r hr => by simp only [wkG, ρt, clampT_of_mem hr]
    exact junk_interval_continuousOn hT (wkG D ρ ψ) _ hC (hrel ψ hψ) hae
  intro ψ hψ
  have hdiff : ∀ (ε : ℝ) (χ : Torus d → ℝ), Torus.IsCk 2 χ → (∀ x, |ψ x - χ x| ≤ ε) →
      ∀ t ∈ Icc 0 T, |(∫ x, ψ x * ρ t x) - ∫ x, χ x * ρ t x| ≤ ε := by
    intro ε χ hχ hχψ t ht
    have hp := hmf.density t ht
    have hρi : Continuous (ρ t) := hρc t ht
    have hχc : Continuous χ := isCk_continuous hχ
    have i1 : Integrable (fun x => ψ x * ρ t x) :=
      (hψ.mul hρi).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have i2 : Integrable (fun x => χ x * ρ t x) :=
      (hχc.mul hρi).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have i3 : Integrable (ρ t) := hρi.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [← integral_sub i1 i2]
    have h1 : |∫ x, (ψ x * ρ t x - χ x * ρ t x)| ≤ ∫ x, |ψ x * ρ t x - χ x * ρ t x| := by
      simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => ψ x * ρ t x - χ x * ρ t x)
    refine h1.trans ?_
    calc ∫ x, |ψ x * ρ t x - χ x * ρ t x| ≤ ∫ x, ε * ρ t x := by
          refine integral_mono ((i1.sub i2).abs) (i3.const_mul ε) fun x => ?_
          simp only
          rw [← sub_mul, abs_mul, abs_of_nonneg (hp.nonneg x)]
          exact mul_le_mul_of_nonneg_right (hχψ x) (hp.nonneg x)
      _ = ε := by rw [integral_const_mul, hp.integral_one, mul_one]
  choose χ hχ hχψ using fun n : ℕ => exists_isCk_approx ψ hψ (1 / ((n : ℝ) + 1)) (by positivity)
  have hunif : TendstoUniformlyOn (fun (n : ℕ) (t : ℝ) => ∫ x, χ n x * ρ t x)
      (fun t => ∫ x, ψ x * ρ t x) atTop (Icc 0 T) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    filter_upwards [eventually_ge_atTop N] with n hn t ht
    rw [Real.dist_eq]
    refine lt_of_le_of_lt (hdiff _ (χ n) (hχ n) (hχψ n) t ht) (lt_of_le_of_lt ?_ hN)
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  exact hunif.continuousOn (Eventually.of_forall fun n => hcont2 _ (hχ n)).frequently

end HRS.Uniform.Q54c
