import HRS.MS.Fp81S21WickApprox10

/-! Gaussian finite-rank coefficient fields and time sections. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- The reference product-L² class of a finite-rank kernel. -/
def fp81s21_rankKernelLp {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (D : fp81s21_RankKernel p.d) :
    Lp ℝ 2 ((HRS.Whole.withDensityReal R.ρβ).prod (HRS.Whole.withDensityReal R.ρβ)) := by
  let μ := HRS.Whole.withDensityReal R.ρβ
  letI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  have hdata : ∀ i, IsR2Test (D.u i) :=
    fun i => ⟨D.valid.smooth i, D.valid.compactSupport i⟩
  have hk : MemLp (fun xy : Euc p.d × Euc p.d => D.kernel xy.1 xy.2) 2
      (μ.prod μ) := HRS.MS.R2Chaos.s94_finiteRank_memLp hdata
  exact hk.toLp (fun xy => D.kernel xy.1 xy.2)

/-- The supplied Gaussian finite-rank outputs form jointly measurable finite
coordinate fields and measurable random time-L² sections. The same operator and
coherent field retain the uniform singular-kernel replacement profile. -/
theorem fp81s21_wick_rankKernel_time_fields (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4),
      ∀ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
      ∀ Λ : ℝ, 0 ≤ Λ →
      ∀ D : HRS.MS.R2S11.s11V p.d Λ → ℕ → fp81s21_RankKernel p.d,
      ∀ B C : ℝ, 0 ≤ B → 0 ≤ C →
      IsR2UniformApprox p.s C B (HRS.Whole.withDensityReal R.ρβ)
        (fun θ => commutatorKernel p.d p.s θ.1) (fun θ k => (D θ k).kernel) →
      ∃ τ : ℕ → ℝ, (∀ k, 0 ≤ τ k) ∧ Tendsto τ atTop (𝓝 0) ∧
      ∀ G : GaussianRealization R,
      ∃ W : ℝ → Lp ℝ 2 ((HRS.Whole.withDensityReal R.ρβ).prod
        (HRS.Whole.withDensityReal R.ρβ)) →L[ℝ] Lp ℝ 2 G.P,
      ∃ qs : ℝ → G.Ω → r26t6_Coeff, ∃ M : ℝ,
        fp81s21_MomentRep Es G.P (fp81s21_wickChartField Es qs) qs M ∧
        (∀ u : ℝ, 0 ≤ u → ∀ f : Euc p.d → ℝ, IsR2Test f →
          ∀ θ : HRS.MS.R2S11.s11V p.d Λ, θ.1 = gradient f → ∀ k : ℕ,
            fp81s21_SqErr G.P
              (fun ω => W u (fp81s21_rankKernelLp R (D θ k)) ω)
              (fun ω => fp81s21_wickChartField Es qs u ω f) (τ k)) ∧
        ∀ (m k : ℕ) (θ : Fin m → HRS.MS.R2S11.s11V p.d Λ),
          ∃ Mq : ℝ, ∃ q : ℝ → G.Ω → r26t6_Coeff,
          Measurable (Function.uncurry q) ∧
          (∀ u, 0 ≤ u → MemLp (q u) 2 G.P ∧
            (∫ ω, ‖q u ω‖ ^ 2 ∂G.P) ≤ Mq ∧
            ∀ᵐ ω ∂G.P, ∀ j : ℕ,
              q u ω j = if hj : j < m then
                (W u (fp81s21_rankKernelLp R (D (θ ⟨j, hj⟩) k)) : G.Ω → ℝ) ω
              else 0) ∧
          ∀ a : ℝ, 0 ≤ a → ∀ H : ℝ, 0 ≤ H →
            ∃ U : G.Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)),
              fp81s21_TimeL2Rep G.P q Mq a H U := by
  obtain ⟨δa, hδa, hδah, ha⟩ := fp81s21_wick_rankKernel_supplied_profile p
  obtain ⟨δb, hδb, hδbh, hb⟩ := fp81s21_wickFam_linear_family_continuous p
  refine ⟨min δa δb, lt_min hδa hδb, (min_le_left _ _).trans hδah, ?_⟩
  intro δ hδ hδle R Es E Λ hΛ D B C hB hC happrox
  obtain ⟨K, hK, τ, hτ, hτlim, hG⟩ :=
    ha δ hδ (hδle.trans (min_le_left _ _)) R Es E Λ hΛ D B C hB hC happrox
  refine ⟨τ, hτ, hτlim, ?_⟩
  intro G
  letI : IsProbabilityMeasure (HRS.Whole.withDensityReal R.ρβ) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  obtain ⟨T, W, qs, M, hW, hag, hrep, herr⟩ := hG G
  have hc := hb δ hδ (hδle.trans (min_le_right _ _)) R G T K
    (fun u hu => (hW u hu).choose)
    (fun u hu α hα => hag u hu _ (HRS.MS.GenPath.s56_isOscTest _ α) hα)
  have hwcont := fp81s21_wickFam_supplied_wick_continuous_joint p R K G T W hW hag hc
  have hwbound : ∀ u, 0 ≤ u → ‖W u‖ ≤ K ^ 2 / Real.sqrt 2 := by
    intro u hu
    obtain ⟨hL, hJ, hWu⟩ := hW u hu
    rw [hWu]
    exact fp81s21_wickB311_operator_norm (T u) K hL hJ
  have hK' : 0 ≤ K ^ 2 / Real.sqrt 2 := div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  refine ⟨W, qs, M, hrep, ?_, ?_⟩
  · intro u hu f hf θ hθ k
    obtain ⟨hk, he⟩ := herr u hu f hf θ hθ k
    simpa [fp81s21_rankKernelLp] using he
  · intro m k θ
    let μ := HRS.Whole.withDensityReal R.ρβ
    let v : ℕ → Lp ℝ 2 (μ.prod μ) := fun j =>
      if hj : j < m then fp81s21_rankKernelLp R (D (θ ⟨j, hj⟩) k) else 0
    have hv : Summable (fun j => ‖v j‖ ^ 2) := by
      apply summable_of_ne_finset_zero (s := Finset.range m)
      intro j hj
      have hn : ¬ j < m := by simpa using hj
      simp [v, hn]
    obtain ⟨q, hqm, hq⟩ := fp81s21_operator_coeff_field (μ.prod μ) G.P W
      (K ^ 2 / Real.sqrt 2) hK' hwbound (fun x => (hwcont x).1) v hv
    let Mq : ℝ := (K ^ 2 / Real.sqrt 2) ^ 2 * ∑' j, ‖v j‖ ^ 2
    refine ⟨Mq, q, hqm, ?_, ?_⟩
    · intro u hu
      obtain ⟨hmem, hbound, hcoord⟩ := hq u hu
      refine ⟨hmem, hbound, ?_⟩
      filter_upwards [hcoord, Lp.coeFn_zero ℝ 2 G.P] with ω hω hzero j
      by_cases hj : j < m
      · simpa [v, hj] using hω j
      · simpa [v, hj, hzero] using hω j
    · intro a ha H hH
      let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
      let g : ℝ × G.Ω → r26t6_Coeff := fun z => q (a + z.1) z.2
      have hgm : Measurable g :=
        hqm.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
      have hsec : ∀ᵐ t ∂dt, MemLp (fun ω => g (t, ω)) 2 G.P ∧
          (∫ ω, ‖g (t, ω)‖ ^ 2 ∂G.P) ≤ Mq := by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        exact ⟨(hq (a + t) (add_nonneg ha ht.1)).1,
          (hq (a + t) (add_nonneg ha ht.1)).2.1⟩
      obtain ⟨hg, hbnd⟩ := fp81s21_memLp_prod_of_section_bound dt G.P g hgm Mq hsec
      have hi : Integrable (fun z => ‖g z‖ ^ 2) (dt.prod G.P) :=
        (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg
      have hs : ∀ᵐ ω ∂G.P, MemLp (fun t => g (t, ω)) 2 dt := by
        filter_upwards [hi.prod_left_ae] with ω hω
        exact (memLp_two_iff_integrable_sq_norm
          (hgm.comp (measurable_prodMk_right (y := ω))).aestronglyMeasurable).2 hω
      obtain ⟨U, hUm, hUL, hUeq, hUin⟩ := fp81s21_time_section_exists G.P H g hgm hg
      refine ⟨U, hUm, hUL, ?_, ?_⟩
      · rw [hUin]
        simpa [dt, Measure.restrict_apply_univ, Real.volume_Icc,
          ENNReal.toReal_ofReal hH] using hbnd
      · filter_upwards [hs, hUeq] with ω hω heq
        exact ⟨hω, heq⟩

#print axioms fp81s21_rankKernelLp
#print axioms fp81s21_wick_rankKernel_time_fields
end HRS.Fp81.S21
end
