import HRS.MS.Fp81S21GaussianPropagated
import HRS.MS.Fp81S21GaussianSourceDensity
import HRS.MS.Fp81S21ChaosLimit
import HRS.MS.Fp81S21GaussTimeRep
import HRS.MS.Fp81S21EmbedIdent

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111
open HRS.MC.E213U13

/-- A continuous Gaussian-source operator has first-chaos values everywhere
when its oscillator-test image is dense and its values on that image are in
first chaos. -/
theorem fp81s21_firstChaos_of_dense_operator
    {X Ω ι : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    {μ : Measure X} {P : Measure Ω} [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → ℝ) (hξ : HRS.IsStdGaussianSeq P ξ)
    (hξmeas : ∀ i, Measurable (ξ i))
    (testLp : ι → Lp ℝ 2 μ)
    (hdense : Dense (Set.range testLp))
    (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P)
    (htest : ∀ i, HRS.InFirstChaos P ξ 2
      (fun ω => (L (testLp i)) ω)) :
    ∀ f : Lp ℝ 2 μ, HRS.InFirstChaos P ξ 2
      (fun ω => (L f) ω) := by
  intro f
  have hnear : ∀ n : ℕ, ∃ i : ι,
      dist (testLp i) f < 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨y, hdist, hy⟩ := (Metric.dense_iff.1 hdense) f
      (1 / ((n : ℝ) + 1)) hpos
    obtain ⟨i, rfl⟩ := hy
    exact ⟨i, hdist⟩
  choose i hi using hnear
  have hdist : Tendsto (fun n : ℕ => dist (testLp (i n)) f)
      atTop (𝓝 0) := by
    refine squeeze_zero (fun _ => dist_nonneg) (fun n => (hi n).le) ?_
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have htestSeq : Tendsto (fun n : ℕ => testLp (i n)) atTop (𝓝 f) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hdist.eventually (Iio_mem_nhds hε)] with n hn
    exact hn
  have hLconv : Tendsto (fun n : ℕ => L (testLp (i n))) atTop (𝓝 (L f)) :=
    (L.continuous.tendsto f).comp htestSeq
  let W : Ω → ℝ := fun ω => (L f) ω
  have htarget : (Lp.memLp (L f)).toLp W = L f :=
    Lp.toLp_coeFn (L f) (Lp.memLp (L f))
  have hLconv' : Tendsto (fun n : ℕ => L (testLp (i n))) atTop
      (𝓝 ((Lp.memLp (L f)).toLp W)) := by
    rw [htarget]
    exact hLconv
  have hLlim0 : Tendsto (fun n : ℕ => eLpNorm
      (((L (testLp (i n)) : Lp ℝ 2 P) : Ω → ℝ) - W) 2 P)
      atTop (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm
      (fun n => L (testLp (i n))) W (Lp.memLp (L f))).1 hLconv'
  have hLexp (n : ℕ) : eLpNorm
      (((L (testLp (i n)) : Lp ℝ 2 P) : Ω → ℝ) - W) 2 P =
      eLpNorm (fun ω => (L (testLp (i n))) ω - W ω)
        (ENNReal.ofReal (2 : ℝ)) P := by
    rw [ENNReal.ofReal_ofNat]
    congr 1
  have hLlim : Tendsto (fun n : ℕ => eLpNorm
      (fun ω => (L (testLp (i n))) ω - W ω)
      (ENNReal.ofReal (2 : ℝ)) P) atTop (𝓝 0) := by
    simpa only [hLexp] using hLlim0
  exact fp81s21_firstChaos_closed P ξ hξ hξmeas 2 (by norm_num)
    (fun n ω => (L (testLp (i n))) ω) W
    (Lp.memLp (L f)).aestronglyMeasurable hLlim (fun n => htest (i n))

/-- For a coefficient field with compact-test agreement to a continuous
linear source operator, each coordinate is first chaos on that same source.
The proof first extends the operator's oscillator-test chaos certificate by
density, then uses compact chart sections and coefficient convergence. -/
theorem fp81s21_gaussian_coord_firstChaos_time
    {Ω : Type*} [MeasurableSpace Ω]
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → ℝ) (hξ : HRS.IsStdGaussianSeq P ξ)
    (hξmeas : ∀ i, Measurable (ξ i))
    (L : ℝ → Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ) →L[ℝ]
      Lp ℝ 2 P)
    (q : ℝ → Ω → r26t6_Coeff)
    (hq : ∀ u : ℝ, 0 ≤ u → MemLp (q u) 2 P)
    (hcompact : ∀ u : ℝ, 0 ≤ u → ∀ g : Euc p.d → ℝ,
      IsR2Test g → ∀ hg : MemLp g 2 (HRS.Whole.withDensityReal R.ρβ),
        (fun ω => fp81s21_chartAction E (q u ω) g) =ᵐ[P]
          (L u (hg.toLp g) : Ω → ℝ))
    (hosc : ∀ u : ℝ, 0 ≤ u → ∀ φ : fp81s21_oscTest p.d,
      HRS.InFirstChaos P ξ 2
        (fun ω => (L u (fp81s21_gaussianSourceSpace_oscTestLp p R φ)) ω)) :
    ∀ u : ℝ, 0 ≤ u → ∀ j : ℕ,
      HRS.InFirstChaos P ξ 2 (fun ω => q u ω j) := by
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    have hd : (0 : ℝ) ≤ (p.d : ℝ) := Nat.cast_nonneg _
    nlinarith
  intro u hu j
  have hLfirst : ∀ f : Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ),
      HRS.InFirstChaos P ξ 2 (fun ω => (L u f) ω) :=
    fp81s21_firstChaos_of_dense_operator ξ hξ hξmeas
      (fp81s21_gaussianSourceSpace_oscTestLp p R)
      (fp81s21_gaussianSourceSpace_oscTest_dense p R) (L u) (hosc u hu)
  have hagree := fp81s21_linear_weighted_agreement p R E P
    (L u) (q u) (hq u hu) (hcompact u hu)
  let c : r26t6_Coeff := lp.single 2 j (1 : ℝ)
  let V : ℕ → Ω → ℝ := fun n ω =>
    inner ℝ (q u ω) (coeffSection c n)
  let Y : Ω → ℝ := fun ω => inner ℝ (q u ω) c
  have hVmem : ∀ n : ℕ, MemLp (V n) 2 P := by
    intro n
    simpa [V] using (hq u hu).inner_const (coeffSection c n)
  have hYmem : MemLp Y 2 P := by
    simpa [Y] using (hq u hu).inner_const c
  have hVfirst : ∀ n : ℕ, HRS.InFirstChaos P ξ 2 (V n) := by
    intro n
    let g : compactSmoothSubmodule p.d := chartSection E c n
    have hgW : IsR2WeightedTest (2 * p.d + 8) ((p.d : ℝ) + 2)
        (g : Euc p.d → ℝ) :=
      weightedTestSubmodule_iff.1 (weighted_test_of_compact_smooth hP
        (show IsR2Test (g : Euc p.d → ℝ) from g.property))
    obtain ⟨hf, heq⟩ := hagree (g : Euc p.d → ℝ) hgW
    have hActionFirst : HRS.InFirstChaos P ξ 2
        (fun ω => fp81s21_chartAction E (q u ω) (g : Euc p.d → ℝ)) :=
      InFirstChaos.congr_ae heq.symm
        (hLfirst (hf.toLp (g : Euc p.d → ℝ)))
    have hActionEq :
        (fun ω => fp81s21_chartAction E (q u ω) (g : Euc p.d → ℝ)) =ᵐ[P] V n := by
      filter_upwards [] with ω
      simp [V, g, fp81s21_chartAction, encode_chartSection E hP c n]
    exact InFirstChaos.congr_ae hActionEq hActionFirst
  let Yp : Lp ℝ 2 P := hYmem.toLp Y
  let Ynp : ℕ → Lp ℝ 2 P := fun n => (hVmem n).toLp (V n)
  have heq : ∀ n : ℕ, ‖Ynp n - Yp‖ ^ 2 =
      ∫ ω, (V n ω - Y ω) ^ 2 ∂P := by
    intro n
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (Ynp n) Yp,
      (hVmem n).coeFn_toLp, hYmem.coeFn_toLp] with ω h1 h2 h3
    change (Ynp n - Yp) ω * (Ynp n - Yp) ω = _
    rw [h1]
    simp only [Pi.sub_apply]
    change Ynp n ω = V n ω at h2
    change Yp ω = Y ω at h3
    rw [h2, h3]
    ring
  have hsquare := inner_pairing_square_tendsto P (q u) (hq u hu) c
    (coeffSection c) (coeffSection_tendsto c)
  have hsq : Tendsto (fun n : ℕ => ‖Ynp n - Yp‖ ^ 2) atTop (𝓝 0) := by
    simpa only [heq, V, Y] using hsquare
  have hYconv : Tendsto Ynp atTop (𝓝 Yp) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa only [Function.comp_def, Real.sqrt_zero,
      Real.sqrt_sq (norm_nonneg _)] using hsqrt
  have hLpconv : Tendsto (fun n => (hVmem n).toLp (V n)) atTop
      (𝓝 (hYmem.toLp Y)) := by
    simpa only [Ynp, Yp] using hYconv
  have hlim0 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    V hVmem Y hYmem).1 hLpconv
  have hlim : Tendsto (fun n => eLpNorm (V n - Y)
      (ENNReal.ofReal (2 : ℝ)) P) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_ofNat] using hlim0
  have hYfirst : HRS.InFirstChaos P ξ 2 Y :=
    fp81s21_firstChaos_closed P ξ hξ hξmeas 2 (by norm_num)
      V Y hYmem.aestronglyMeasurable hlim hVfirst
  have hsingle : ∀ ω, Y ω = q u ω j := by
    intro ω
    simp [Y, c, lp.inner_single_right]
  have hcoordAE : Y =ᵐ[P] (fun ω => q u ω j) :=
    Filter.Eventually.of_forall hsingle
  exact InFirstChaos.congr_ae hcoordAE hYfirst

/-- The actual 35d-J history field is the canonical V2-G embedded field
`fp81s21_gaussian_embedFamily p Es E (qsUG)`. Its chaos certificate follows
from the same retained source operator and the V2-G weak-chart representative:
the two coefficient representatives agree almost everywhere by MomentRep
uniqueness. -/
theorem fp81s21_gaussian_V2_G_canonical_hcoord
    (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    {δ : ℝ} (R : Trajectory p δ)
    (hμ₀ : IsProbabilityMeasure (r26t3_mu R 0))
    (D : fp81s21_gaussian_source_retained_data p R hμ₀)
    (T : ℝ → Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ) →L[ℝ]
      Lp ℝ 2 D.G0.P)
    (hTosc : ∀ u : ℝ, 0 ≤ u → ∀ φ : fp81s21_oscTest p.d,
      (T u (fp81s21_gaussianSourceSpace_oscTestLp p R φ) : D.G0.Ω → ℝ) =ᵐ[D.G0.P]
        (fun ω => OscDual.eval (D.G0.Z u ω) φ.1))
    (qsUG : ℝ → D.G0.Ω → r26t6_Coeff) (MUG : ℝ)
    (hcanonical : fp81s21_MomentRep E D.G0.P
      (fun u ω f => OscDual.eval (D.G0.Z u ω) f)
      (fp81s21_gaussian_embedFamily p Es E qsUG) MUG)
    (M2 : ℝ) (qsG : ℝ → D.G0.Ω → r26t6_Coeff)
    (hweak : fp81s21_MomentRep E D.G0.P
      (fun u ω f => OscDual.eval (D.G0.Z u ω) f)
      (fun u ω => fp81s21_gaussian_chartEmbed p Es E (qsG u ω)) M2) :
    ∀ u : ℝ, 0 ≤ u → ∀ j : ℕ,
      HRS.InFirstChaos D.G0.P (fp81s21_gaussian_source_measurableXi D) 2
        (fun ω => (fp81s21_gaussian_embedFamily p Es E qsUG u ω) j) := by
  let ξ' := fp81s21_gaussian_source_measurableXi D
  obtain ⟨hmeas, hstd, _, heval⟩ :=
    fp81s21_gaussian_source_measurable_eval_firstChaos D
  have hosc : ∀ u : ℝ, 0 ≤ u → ∀ φ : fp81s21_oscTest p.d,
      HRS.InFirstChaos D.G0.P ξ' 2
        (fun ω => (T u (fp81s21_gaussianSourceSpace_oscTestLp p R φ)) ω) := by
    intro u hu φ
    exact InFirstChaos.congr_ae (hTosc u hu φ).symm (heval u hu φ)
  have hcompact : ∀ u : ℝ, 0 ≤ u → ∀ g : Euc p.d → ℝ,
      IsR2Test g → ∀ hg : MemLp g 2 (HRS.Whole.withDensityReal R.ρβ),
        (fun ω => fp81s21_chartAction E
          (fp81s21_gaussian_chartEmbed p Es E (qsG u ω)) g) =ᵐ[D.G0.P]
          (T u (hg.toLp g) : D.G0.Ω → ℝ) := by
    intro u hu g hg hgμ
    let φ : fp81s21_oscTest p.d :=
      ⟨g, r2Test_isOscTest (wholeSpaceIndex p.d : ℝ) hg⟩
    have hfield := (hweak.2 u hu).2.2
    have hT := hTosc u hu φ
    filter_upwards [hfield, hT] with ω hω hTω
    calc
      fp81s21_chartAction E (fp81s21_gaussian_chartEmbed p Es E (qsG u ω)) g =
          OscDual.eval (D.G0.Z u ω) g := hω.1 g hg
      _ = (T u (hgμ.toLp g)) ω := (hTω).symm
  have hweakCoord := fp81s21_gaussian_coord_firstChaos_time
    p R E D.G0.P ξ' hstd hmeas T
    (fun u ω => fp81s21_gaussian_chartEmbed p Es E (qsG u ω))
    (fun u hu => (hweak.2 u hu).1) hcompact hosc
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    nlinarith [p.hd]
  have huniq : ∀ u : ℝ, 0 ≤ u →
      (fun ω => fp81s21_gaussian_embedFamily p Es E qsUG u ω) =ᵐ[D.G0.P]
        (fun ω => fp81s21_gaussian_chartEmbed p Es E (qsG u ω)) :=
    fp81s21_MomentRep_eq_ae hP E D.G0.P
      (fun u ω f => OscDual.eval (D.G0.Z u ω) f)
      (fp81s21_gaussian_embedFamily p Es E qsUG)
      (fun u ω => fp81s21_gaussian_chartEmbed p Es E (qsG u ω))
      MUG M2 hcanonical hweak
  intro u hu j
  have hcoordEq :
      (fun ω => (fp81s21_gaussian_embedFamily p Es E qsUG u ω) j) =ᵐ[D.G0.P]
        (fun ω => fp81s21_gaussian_chartEmbed p Es E (qsG u ω) j) := by
    filter_upwards [huniq u hu] with ω hω
    exact congrArg (fun z : r26t6_Coeff => z j) hω
  exact InFirstChaos.congr_ae hcoordEq.symm (hweakCoord u hu j)

#print axioms fp81s21_firstChaos_of_dense_operator
#print axioms fp81s21_gaussian_coord_firstChaos_time
#print axioms fp81s21_gaussian_V2_G_canonical_hcoord

end HRS.Fp81.S21
end
