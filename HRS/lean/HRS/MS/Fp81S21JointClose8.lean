import HRS.MS.Fp81S21JointClose7
import HRS.MS.Fp81S21JointClose5
import HRS.MS.Fp81S21JointClose6

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal NNReal
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111
namespace HRS.Fp81.S21

local instance fp81s21_jointClose8_U_measSpace (H : ℝ) :
    MeasurableSpace (fp81s21_jointP_U H) := borel _
local instance fp81s21_jointClose8_U_borelSpace (H : ℝ) :
    BorelSpace (fp81s21_jointP_U H) := ⟨rfl⟩
local instance fp81s21_jointClose8_pair_measSpace (H : ℝ) :
    MeasurableSpace (fp81s21_jointP_U H × fp81s21_jointP_U H) := borel _
local instance fp81s21_jointClose8_pair_borelSpace (H : ℝ) :
    BorelSpace (fp81s21_jointP_U H × fp81s21_jointP_U H) := ⟨rfl⟩

/-- Joint physical time-L² comparison, conditional on a chart-uniform
positive lower bound for the two available physical radii. -/
theorem fp81s21_joint_timeL2_comparison (p : Parameters)
    (hRad : ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
        (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)),
        δ0 ≤ fp81s21_jointClose_bundleRadius p Es E ∧
        δ0 ≤ fp81s21_jointClose_errorRadius p Es E) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
    ∀ (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
      (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)),
    ∃ εN εG εB : ℕ → ℝ, ∃ S : fp81s21_Physical31 p R Es E εN εG εB,
    ∀ H : ℝ, 0 < H → ∃ q : ℕ → ℝ,
    (∀ N, 0 ≤ q N) ∧ Tendsto q atTop (𝓝 0) ∧
    ∀ N : ℕ, ∀ hN : 2 ≤ N, ∀ A : Particle R N,
    ∀ G : GaussianRealization R, ∀ a : ℝ, 0 ≤ a →
    ∀ Uη UB : A.Ω → fp81s21_jointP_U H,
    ∀ Vη VB : G.Ω → fp81s21_jointP_U H,
    fp81s21_TimeL2Rep A.P
      (fun u ω => fp81s21_particle_embedField p Es E (S.qsηN N hN A u ω)) S.MN a H Uη →
    fp81s21_TimeL2Rep A.P
      (fun u ω => fp81s21_particle_embedField p Es E (S.qsBN N hN A u ω)) S.MN a H UB →
    fp81s21_TimeL2Rep G.P
      (fp81s21_gaussian_embedFamily p Es E (S.gaussian.qsηG G)) S.gaussian.MηG a H Vη →
    fp81s21_TimeL2Rep G.P (S.gaussian.quadratic.qe G)
      (S.gaussian.quadratic.Kstar ^ 4 * S.gaussian.quadratic.B / 2) a H VB →
    wassersteinE 2 (law A.P (fun ω => (Uη ω, UB ω)))
      (law G.P (fun ω => (Vη ω, VB ω))) ≤ ENNReal.ofReal (q N) := by
  obtain ⟨δc, hδc, hδch, hc⟩ := fp81s21_jointClose_chart_uniform p hRad
  obtain ⟨δl, hδl, hδlh, hl⟩ := fp81s21_jointL_arbitrary_horizon_raw_profile_unconditional p
  refine ⟨min δc δl, lt_min hδc hδl, (min_le_left _ _).trans hδch, ?_⟩
  intro δ hδ hδle R Es E
  obtain ⟨he, εN, εG, εB, hn, hnl, hg, hgl, hb, hbl, hs⟩ := hc Es E
  let S := Classical.choice (hs δ hδ (hδle.trans (min_le_left _ _)) R)
  refine ⟨εN, εG, εB, S, ?_⟩
  have hshared := (Classical.choose_spec (fp81s21_jointN_sqerr_physical p Es E)).2.2
    δ hδ ((hδle.trans (min_le_left _ _)).trans he) R εN εG εB hn hg hb S
  have hdata : ∀ m : ℕ, ∃ Λ : ℝ,
      ∃ θ : Fin m → HRS.MS.R2S11.s11V p.d Λ,
      ∃ D : HRS.MS.R2S11.s11V p.d Λ → ℕ → fp81s21_RankKernel p.d,
      ∃ τN τG : ℕ → ℝ,
      0 ≤ Λ ∧ (∀ j, (θ j).1 = gradient (E.test j)) ∧
      (∀ k, 0 ≤ τN k) ∧ (∀ k, 0 ≤ τG k) ∧
      Tendsto τN atTop (𝓝 0) ∧ Tendsto τG atTop (𝓝 0) ∧
      (∀ H : ℝ, ∀ hH : 0 < H, ∀ k : ℕ, ∃ Ddiag : ℝ, 0 ≤ Ddiag ∧
        ∀ N : ℕ, ∀ hN : 2 ≤ N, ∀ A : Particle R N, ∀ a : ℝ, 0 ≤ a →
        ∀ Uη UB : A.Ω → fp81s21_jointP_U H,
        fp81s21_TimeL2Rep A.P
          (fun u ω => fp81s21_particle_embedField p Es E (S.qsηN N hN A u ω)) S.MN a H Uη →
        fp81s21_TimeL2Rep A.P
          (fun u ω => fp81s21_particle_embedField p Es E (S.qsBN N hN A u ω)) S.MN a H UB →
        fp81s21_SqErr A.P (fun ω => (Uη ω, UB ω))
          (fun ω => fp81s21_jointP_map H hH E m (fun j => D (θ j) k)
            (flucPathW (wholeSpaceIndex p.d : ℝ) H a (Real.sqrt (N : ℝ)) A.X R.ρ ω) -
            fp81s21_jointC_partialCenter H (∫ ω', fp81s21_jointP_map H hH E m
              (fun j => D (θ j) k) (flucPathW (wholeSpaceIndex p.d : ℝ) H a
                (Real.sqrt (N : ℝ)) A.X R.ρ ω') ∂A.P))
          (Real.sqrt (H * S.MN) * εN m + Real.sqrt (H * S.MN) * εN m +
            Real.sqrt (H * (m : ℝ)) * τN k + Ddiag / Real.sqrt (N : ℝ))) ∧
      (∀ H : ℝ, ∀ hH : 0 < H, ∀ G : GaussianRealization R, ∀ a : ℝ, 0 ≤ a →
        ∀ Vη VB : G.Ω → fp81s21_jointP_U H,
        fp81s21_TimeL2Rep G.P (fp81s21_gaussian_embedFamily p Es E (S.gaussian.qsηG G))
          S.gaussian.MηG a H Vη →
        fp81s21_TimeL2Rep G.P (S.gaussian.quadratic.qe G)
          (S.gaussian.quadratic.Kstar ^ 4 * S.gaussian.quadratic.B / 2) a H VB →
        ∀ k : ℕ, fp81s21_SqErr G.P (fun ω => (Vη ω, VB ω))
          (fun ω => fp81s21_jointP_map H hH E m (fun j => D (θ j) k)
            (processWindow (wholeSpaceIndex p.d : ℝ) H a G.Z ω) -
            fp81s21_jointG_partialCenter H (∫ ω', fp81s21_jointP_map H hH E m
              (fun j => D (θ j) k) (processWindow (wholeSpaceIndex p.d : ℝ) H a G.Z ω') ∂G.P))
          (Real.sqrt (H * S.gaussian.MηG) * εG m +
            Real.sqrt (H * (S.gaussian.quadratic.Kstar ^ 4 * S.gaussian.quadratic.B / 2)) * εB m +
            Real.sqrt (H * (m : ℝ)) * τG k + 0)) := by
    intro m
    obtain ⟨Λ, θ, D, hΛ, hθ, τN, τG, hτN, hτG, hnlim, hglim, hp, hgg⟩ := hshared m
    exact ⟨Λ, θ, D, τN, τG, hΛ, hθ, hτN, hτG, hnlim, hglim, hp, hgg⟩
  choose Λ θ D τN τG hsel using hdata
  intro H hH
  obtain ⟨d, hd, M, hM, hL⟩ := hl δ hδ (hδle.trans (min_le_right _ _)) R H hH
  have hdiag := fun (m k : ℕ) => (hsel m).2.2.2.2.2.2.1 H hH k
  choose c hc hpart using hdiag
  let s : ℕ → ℝ := fun m =>
    Real.sqrt (H * S.MN) * εN m + Real.sqrt (H * S.MN) * εN m +
    (Real.sqrt (H * S.gaussian.MηG) * εG m +
      Real.sqrt (H * (S.gaussian.quadratic.Kstar ^ 4 * S.gaussian.quadratic.B / 2)) * εB m)
  let t : ℕ → ℕ → ℝ := fun m k =>
    Real.sqrt (H * (m : ℝ)) * τN m k + Real.sqrt (H * (m : ℝ)) * τG m k
  let K : ℕ → ℕ → ℝ := fun m k =>
    fp81s21_jointC2_mapConstant H hH E m (fun j => D m (θ m j) k)
  have hs0 : Tendsto s atTop (𝓝 0) := by
    dsimp [s]
    simpa using (((hnl.const_mul (Real.sqrt (H * S.MN))).add
      (hnl.const_mul (Real.sqrt (H * S.MN)))).add
      ((hgl.const_mul (Real.sqrt (H * S.gaussian.MηG))).add
        (hbl.const_mul (Real.sqrt (H * (S.gaussian.quadratic.Kstar ^ 4 * S.gaussian.quadratic.B / 2))))))
  have ht0 : ∀ m, Tendsto (t m) atTop (𝓝 0) := by
    intro m
    dsimp [t]
    simpa using (((hsel m).2.2.2.2.1.const_mul (Real.sqrt (H * (m : ℝ)))).add
      ((hsel m).2.2.2.2.2.1.const_mul (Real.sqrt (H * (m : ℝ)))))
  have hspos : ∀ m, 0 ≤ s m := by
    intro m
    dsimp [s]
    have := hn m
    have := hg m
    have := hb m
    positivity
  have htpos : ∀ m k, 0 ≤ t m k := by
    intro m k
    dsimp [t]
    exact add_nonneg (mul_nonneg (Real.sqrt_nonneg _) ((hsel m).2.2.1 k))
      (mul_nonneg (Real.sqrt_nonneg _) ((hsel m).2.2.2.1 k))
  let b := fp81s21_jointClose_cutoffBound s t c K M d
  obtain ⟨hq, hq0⟩ := fp81s21_jointClose_cutoff_profile s t c K M d
    hspos htpos hc hM hd.1 hs0 ht0 hd.2
  refine ⟨fp81s21_jointClose_profile b, hq, hq0, ?_⟩
  intro N hN A G a ha Uη UB Vη VB hUη hUB hVη hVB
  apply fp81s21_jointClose_inf_bound _ b N
  · refine ⟨0, ?_⟩
    rintro y ⟨⟨m, k, r⟩, rfl⟩
    dsimp [b, fp81s21_jointClose_cutoffBound]
    exact add_nonneg (add_nonneg (add_nonneg (hspos m) (htpos m k))
      (div_nonneg (hc m k) (Real.sqrt_nonneg _)))
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  · intro m k r
    have hNerr := hpart m k N hN A a ha Uη UB hUη hUB
    have hGerr := (hsel m).2.2.2.2.2.2.2 H hH G a ha Vη VB hVη hVB k
    rw [fp81s21_jointN_partialCenter_eq] at hGerr
    have hrawN : AEMeasurable (fp81s21_jointC_particleWindow p R A H a) A.P := by
      simpa [fp81s21_jointC_particleWindow] using
        (fp81s21_particle_window_centered p R hN A hH ha).1.aemeasurable
    have hrawG : AEMeasurable (fp81s21_jointC_gaussianWindow p R G H a) G.P := by
      simpa [fp81s21_jointC_gaussianWindow] using
        (HRS.MS.S111BD.s111_shifted_window_aemeas p.d G.P (r26t3_coeff R)
          (wholeSpaceIndex p.d : ℝ) p.β⁻¹ H a (a + H)
          (HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ)
          G.Z (G.evolution (a + H)) hH.le ha le_rfl).1
    have hNnonneg : 0 ≤ Real.sqrt (H * S.MN) * εN m +
        Real.sqrt (H * S.MN) * εN m + Real.sqrt (H * (m : ℝ)) * τN m k +
        c m k / Real.sqrt (N : ℝ) := by
      have := hn m
      have := (hsel m).2.2.1 k
      have := hc m k
      positivity
    have hGnonneg : 0 ≤ Real.sqrt (H * S.gaussian.MηG) * εG m +
        Real.sqrt (H * (S.gaussian.quadratic.Kstar ^ 4 * S.gaussian.quadratic.B / 2)) * εB m +
        Real.sqrt (H * (m : ℝ)) * τG m k + 0 := by
      have := hg m
      have := hb m
      have := (hsel m).2.2.2.1 k
      positivity
    have hprod : (Prod.instMeasurableSpace : MeasurableSpace
        (fp81s21_jointP_U H × fp81s21_jointP_U H)) = borel _ :=
      @BorelSpace.measurable_eq _ _ Prod.instMeasurableSpace Prod.borelSpace
    have hcut := fp81s21_jointClose_physical_ae_cutoff R hN A G H hH E m
      (fun j => D m (θ m j) k) a ha (fun ω => (Uη ω, UB ω))
      (fun ω => (Vη ω, VB ω)) hrawN hrawG
      (by
        have hm := hUη.1.prodMk hUB.1
        rw [hprod] at hm
        exact hm)
      (by
        have hm := hVη.1.prodMk hVB.1
        rw [hprod] at hm
        exact hm) _ _ hNnonneg hGnonneg d hd M hM ((r : ℝ) + 1)
      (by exact le_add_of_nonneg_left (Nat.cast_nonneg r)) (by simpa [fp81s21_jointC_particleWindow] using hNerr)
      (by simpa [fp81s21_jointC_gaussianWindow] using hGerr)
      (by simpa [fp81s21_jointC_particleWindow, fp81s21_jointC_gaussianWindow] using
        hL N hN A G a ha)
    convert hcut using 1 <;> simp only [b, fp81s21_jointClose_cutoffBound, s, t, K] <;> ring

#print axioms fp81s21_joint_timeL2_comparison
end HRS.Fp81.S21
end
