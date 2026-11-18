import HRS.MS.Fp81S21WickApprox35
import HRS.MS.Fp81S21WickApprox29
import HRS.MS.Fp81S21WickFam6
import HRS.MS.Fp81S21WickFam16

/-! Time sections for an already selected physical Wick family. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- Lift a fixed-time profile for the supplied physical family to every time
representative of its fixed weak coefficients. -/
theorem fp81s21_quadraticPhysical31_time_lift (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
    ∀ Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4),
    ∀ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
    ∀ ε : ℕ → ℝ, ∀ S : fp81s21_QuadraticPhysical31 p R Es E ε,
    ∀ (m : ℕ) (Λ : ℝ) (θ : Fin m → HRS.MS.R2S11.s11V p.d Λ),
    (∀ j, (θ j).1 = gradient (E.test j)) →
    ∀ D : HRS.MS.R2S11.s11V p.d Λ → ℕ → fp81s21_RankKernel p.d,
    ∀ τ : ℕ → ℝ,
    (∀ G : GaussianRealization R, ∀ u : ℝ, 0 ≤ u →
      ∀ f : Euc p.d → ℝ, IsR2Test f →
      ∀ θ' : HRS.MS.R2S11.s11V p.d Λ, θ'.1 = gradient f → ∀ k : ℕ,
      ∃ hf : MemLp (fun xy : Euc p.d × Euc p.d => (D θ' k).kernel xy.1 xy.2)
        2 ((HRS.Whole.withDensityReal R.ρβ).prod (HRS.Whole.withDensityReal R.ρβ)),
      fp81s21_SqErr G.P
        (fun ω => S.W G u (hf.toLp (fun xy => (D θ' k).kernel xy.1 xy.2)) ω)
        (fun ω => fp81s21_wickChartField Es (S.qs G) u ω f) (τ k)) →
    ∀ G : GaussianRealization R, ∀ (a H : ℝ), 0 ≤ a → 0 ≤ H →
    ∀ V : G.Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)),
    fp81s21_TimeL2Rep G.P (S.qe G) (S.Kstar ^ 4 * S.B / 2) a H V →
    ∀ k : ℕ, ∃ Mq : ℝ, ∃ q : ℝ → G.Ω → r26t6_Coeff,
      Measurable (Function.uncurry q) ∧
      (∀ u, 0 ≤ u → ∀ᵐ ω ∂G.P, ∀ j : ℕ,
        q u ω j = if hj : j < m then
          (S.W G u (fp81s21_rankKernelLp R (D (θ ⟨j, hj⟩) k)) : G.Ω → ℝ) ω
        else 0) ∧
      ∃ U : G.Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)),
        fp81s21_TimeL2Rep G.P q Mq a H U ∧
        fp81s21_SqErr G.P U (fun ω => fp81s21_timeProject H m (V ω))
          (Real.sqrt (H * (m : ℝ)) * τ k) := by
  obtain ⟨δ0, hδ0, hδhalf, hb⟩ := fp81s21_wickFam_linear_family_continuous p
  refine ⟨δ0, hδ0, hδhalf, ?_⟩
  intro δ hδ hδle R Es E ε S m Λ θ hθ D τ hprofile G a H ha hH V hV k
  let T := S.T G
  let W := S.W G
  let qs := S.qs G
  let qe := S.qe G
  let Kstar := S.Kstar
  let Bstar := S.B
  obtain ⟨hW, hT, hqe, hstrong, hrepE', hag, hrest⟩ := S.payload G
  have herr := hprofile G
  letI : IsProbabilityMeasure (HRS.Whole.withDensityReal R.ρβ) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  have hc := hb δ hδ hδle R G T Kstar
    (fun u hu => (hW u hu).choose)
    (fun u hu α hα => hT u hu _ (HRS.MS.GenPath.s56_isOscTest _ α) hα)
  have hwcont := fp81s21_wickFam_supplied_wick_continuous_joint
    p R Kstar G T W hW hT hc
  have hwbound : ∀ u, 0 ≤ u → ‖W u‖ ≤ Kstar ^ 2 / Real.sqrt 2 := by
    intro u hu
    obtain ⟨hL, hJ, hWu⟩ := hW u hu
    change ‖S.W G u‖ ≤ Kstar ^ 2 / Real.sqrt 2
    rw [hWu]
    exact fp81s21_wickB311_operator_norm (T u) Kstar hL hJ
  have hK' : 0 ≤ Kstar ^ 2 / Real.sqrt 2 := by positivity
  let μ := HRS.Whole.withDensityReal R.ρβ
  let v : ℕ → Lp ℝ 2 (μ.prod μ) := fun j =>
    if hj : j < m then fp81s21_rankKernelLp R (D (θ ⟨j, hj⟩) k) else 0
  have hv : Summable (fun j => ‖v j‖ ^ 2) := by
    apply summable_of_ne_finset_zero (s := Finset.range m)
    intro j hj
    have hn : ¬ j < m := by simpa using hj
    simp [v, hn]
  obtain ⟨q, hqm, hq⟩ := fp81s21_operator_coeff_field (μ.prod μ) G.P W
    (Kstar ^ 2 / Real.sqrt 2) hK' hwbound (fun x => (hwcont x).1) v hv
  let Mq : ℝ := (Kstar ^ 2 / Real.sqrt 2) ^ 2 * ∑' j, ‖v j‖ ^ 2
  refine ⟨Mq, q, hqm, ?_⟩
  refine ⟨?_, ?_⟩
  · intro u hu
    obtain ⟨_, _, hcoord⟩ := hq u hu
    filter_upwards [hcoord, Lp.coeFn_zero ℝ 2 G.P] with ω hω hzero j
    by_cases hj : j < m
    · simpa [v, hj] using hω j
    · simpa [v, hj, hzero] using hω j
  ·
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
    have hU : fp81s21_TimeL2Rep G.P q Mq a H U := by
      refine ⟨hUm, hUL, ?_, ?_⟩
      · rw [hUin]
        simpa [dt, Measure.restrict_apply_univ, Real.volume_Icc,
          ENNReal.toReal_ofReal hH] using hbnd
      · filter_upwards [hs, hUeq] with ω hω heq
        exact ⟨hω, heq⟩
    have hqcoord : ∀ u, 0 ≤ u → ∀ᵐ ω ∂G.P, ∀ j : ℕ,
        q u ω j = if hj : j < m then
          (W u (fp81s21_rankKernelLp R (D (θ ⟨j, hj⟩) k)) : G.Ω → ℝ) ω else 0 := by
      intro u hu
      obtain ⟨_, _, hcoord⟩ := hq u hu
      filter_upwards [hcoord, Lp.coeFn_zero ℝ 2 G.P] with ω hω hzero j
      by_cases hj : j < m
      · simpa [v, hj] using hω j
      · simpa [v, hj, hzero] using hω j
    have hfixed : ∀ u, 0 ≤ u → ∀ j : Fin m,
        fp81s21_SqErr G.P
          (fun ω => W u (fp81s21_rankKernelLp R (D (θ j) k)) ω)
          (fun ω => fp81s21_wickChartField Es qs u ω (E.test j)) (τ k) := by
      intro u hu j
      obtain ⟨hf, hfixed⟩ :=
        herr u hu (E.test j) (E.test_smooth j) (θ j) (hθ j) k
      simpa [fp81s21_rankKernelLp] using hfixed
    have herror := fp81s21_wick_rankKernel_time_sqerr2 R G E m
      (fun j => fp81s21_rankKernelLp R (D (θ j) k)) W
      (fp81s21_wickChartField Es qs) q qe Mq (Kstar ^ 4 * Bstar / 2)
      a H (τ k) ha hH hqm hqcoord hrepE' U V hU hV hfixed
    exact ⟨U, hU, herror⟩

#print axioms fp81s21_quadraticPhysical31_time_lift
end HRS.Fp81.S21
end
