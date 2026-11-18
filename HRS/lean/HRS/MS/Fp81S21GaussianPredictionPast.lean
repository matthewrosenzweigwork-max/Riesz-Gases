import HRS.MS.Fp81S21GaussianPropagatedSourceBridge3
import HRS.MS.Fp81S21GaussianPredictionDecomposition2

/-! Packet 36: the continuous physical prediction is the supplied retained
cutoff past. Only dense window times and oscillator basis indices are intersected;
the cutoff remains outside the a.e. quantifier. The supplied future is unchanged.
Interface adjustments: expand `Rad` into its radius telescope; use an interval
subtype for the cutoff, as in 36A; quantify over the already compatible record
`RetainedCutoffPaths`, so neither a new law nor a new selection is assumed.
The conclusion retains 36A's physical/adapted clauses alongside the identification. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6
open HRS.MS.ProClosureS111 HRS.MS.R2Interp HRS.MS.GenPath

/-- Strictly before the cutoff the future kernel has empty time support.
The equality case is handled by the propagated identity, including time zero. -/
private theorem fp81s21_prediction_past_noise_zero
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {r t : ℝ} (htr : t < r) (φ : Euc p.d → ℝ) :
    movingNoiseFeature R r t φ = 0 := by
  have hk : movingNoiseKernel R r t φ = 0 := by
    funext q
    have hn : q.1 ∉ Icc r t := fun h => (not_le_of_gt htr) (h.1.trans h.2)
    simp only [movingNoiseKernel, if_neg hn, Pi.zero_apply]
  simp only [movingNoiseFeature, hk, dif_pos MemLp.zero, MemLp.toLp_zero]

/-- One cutoff-continuous physical prediction, with exact past-measurable
representatives, agrees at every fixed cutoff with every supplied compatible
retained past. Its sum with that same supplied future is the actual physical
window. No source, chart, thermal operator, history, or future is reselected. -/
theorem fp81s21_gaussian_prediction_eq_retained_past (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
      ∀ Q : fp81s21_Physical35 p R, ∀ a : ℝ, ∀ ha : 0 ≤ a,
      ∃ Y : Q.src.G0.Ω → C(Icc (0 : ℝ) (a + p.T), Window p),
        Measurable Y ∧
        (∀ r : Icc (0 : ℝ) (a + p.T), ∃ Yr : Q.src.G0.Ω → Window p,
          Measurable Yr ∧
          Measurable[MeasurableSpace.comap
            (fp81s21_predictionPast Q.tofp81s21_Gaussian35Selection (r : ℝ)) inferInstance] Yr ∧
          (fun ω => Y ω r) =ᵐ[Q.src.G0.P] Yr) ∧
        (∀ r : Icc (0 : ℝ) (a + p.T), ∀ τ : Icc (0 : ℝ) p.T,
          ∀ᵐ ω ∂Q.src.G0.P,
            OscPath.at' (Y ω r) τ =
              r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
                (a + τ) (min (r : ℝ) (a + τ))
                (fp81s21_chartAction Q.E (fp81s21_gaussian35_qG
                  Q.tofp81s21_Gaussian35Selection (min (r : ℝ) (a + τ)) ω))) ∧
        ∀ r : Icc (0 : ℝ) (a + p.T),
        ∀ γ : Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)),
        ∀ D : fp81s21_RetainedCutoffPaths Q a r γ,
          ((fun ω => Y ω r) =ᵐ[Q.src.G0.P]
            fun ω => physicalWindowRestriction ha (le_refl (a + p.T)) (D.Xpast ω)) ∧
          (r26t3_Zpath Q.src.G0 a =ᵐ[Q.src.G0.P]
            fun ω => Y ω r +
              physicalWindowRestriction ha (le_refl (a + p.T)) (D.Xfuture ω)) := by
  obtain ⟨δv, hv, hvh, hversion⟩ := fp81s21_gaussian_prediction_continuous_ae_adapted p
  obtain ⟨δb, hb, _, hbridge⟩ := fp81s21_gaussian_propagated_source_bridge p
  obtain ⟨δo, ho, _, horbit⟩ := fp81s21_uniform_orbit_amplitudes p
  refine ⟨min δv (min δb δo), lt_min hv (lt_min hb ho),
    (min_le_left _ _).trans hvh, ?_⟩
  intro δ hδ hδle R
  letI := fp81s21_initialMeasure_isProbability p R
  have hδv : δ ≤ δv := hδle.trans (min_le_left _ _)
  have hδb : δ ≤ δb := hδle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδo : δ ≤ δo := hδle.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨Co, co, _, _, hD⟩ := horbit δ hδ hδo R
  intro Q a ha
  obtain ⟨Y, hYm, hYpast, hphys⟩ := hversion δ hδ hδv R Q a ha
  have hH : 0 < a + p.T := add_pos_of_nonneg_of_pos ha p.hT
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) p.d]
  refine ⟨Y, hYm, hYpast, hphys, ?_⟩
  intro r γ D
  let res := physicalWindowRestriction (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
    ha (le_refl (a + p.T))
  have hcoord (τ : Icc (0 : ℝ) p.T) (α : MultiIndex p.d) :
      ∀ᵐ ω ∂Q.src.G0.P,
        OscDual.coord (OscPath.at' (Y ω r) τ) α =
          OscDual.coord (OscPath.at' (res (D.Xpast ω)) τ) α := by
    let t := physicalWindowTime ha (le_refl (a + p.T)) τ
    let φ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
    have hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ := s56_isOscTest _ _
    have ht : (t : ℝ) = a + τ := rfl
    by_cases hrt : (r : ℝ) ≤ t
    · have hmin : min (r : ℝ) (a + τ) = r := min_eq_left hrt
      have hb := hbridge δ hδ hδb R Q a ha r r.property t ⟨hrt, t.property.2⟩ α
      filter_upwards [hphys r τ, hb, D.propagated t hrt φ hφ] with ω hy hb hp
      rw [hmin] at hy
      rw [hy, ← ht, s102_Vprop_coord hP (hD (a + p.T) hH)
        (fp81s21_chartAction_S102Z Q.E _) (fp81s21_S102Lin p R (a + p.T))
        r.property ⟨hrt, t.property.2⟩ α]
      change fp81s21_chartAction Q.E
        (fp81s21_gaussian35_qG Q.tofp81s21_Gaussian35Selection r ω)
        (propagatorW (r26t3_coeff R) r t φ) =
          OscDual.coord (OscPath.at' (D.Xpast ω) t) α
      rw [hb]
      simpa only [φ, OscDual.eval_oscTestFun] using hp.symm
    · have htr : (t : ℝ) < r := lt_of_not_ge hrt
      have hmin : min (r : ℝ) (a + τ) = t := min_eq_right htr.le
      have hdiag : propagatorW (r26t3_coeff R) t t φ = φ :=
        (fp81s21_U_osc_test_classical p R hφ t.property.1).terminal
      have hb := hbridge δ hδ hδb R Q a ha t t.property t ⟨le_rfl, t.property.2⟩ α
      have hn := fp81s21_prediction_past_noise_zero p R htr φ
      filter_upwards [hphys r τ, hb, D.evaluations.past t φ hφ] with ω hy hb hp
      rw [hmin] at hy
      rw [hy, ← ht, s102_Vprop_coord hP (hD (a + p.T) hH)
        (fp81s21_chartAction_S102Z Q.E _) (fp81s21_S102Lin p R (a + p.T))
        t.property ⟨le_rfl, t.property.2⟩ α]
      change fp81s21_chartAction Q.E
        (fp81s21_gaussian35_qG Q.tofp81s21_Gaussian35Selection t ω)
        (propagatorW (r26t3_coeff R) t t φ) =
          OscDual.coord (OscPath.at' (D.Xpast ω) t) α
      rw [hb]
      rw [hdiag, fp81s21_combinedFeature]
      rw [hn, sub_zero] at hp
      simpa only [φ, OscDual.eval_oscTestFun] using hp.symm
  letI : Nonempty (Icc (0 : ℝ) p.T) := ⟨⟨0, le_rfl, p.hT.le⟩⟩
  let s : ℕ → Icc (0 : ℝ) p.T := TopologicalSpace.denseSeq _
  have hs : DenseRange s := TopologicalSpace.denseRange_denseSeq _
  have heq : (fun ω => Y ω r) =ᵐ[Q.src.G0.P] fun ω => res (D.Xpast ω) := by
    have hc : ∀ i : ℕ × MultiIndex p.d, ∀ᵐ ω ∂Q.src.G0.P,
        OscDual.coord (OscPath.at' (Y ω r) (s i.1)) i.2 =
          OscDual.coord (OscPath.at' (res (D.Xpast ω)) (s i.1)) i.2 :=
      fun i => hcoord (s i.1) i.2
    filter_upwards [ae_all_iff.2 hc] with ω hω
    exact s56_pathCoords_injective (wholeSpaceIndex p.d : ℝ) p.T s hs (funext hω)
  refine ⟨heq, ?_⟩
  have hsum := fp81s21_source_cutoff_window_sum Q a ha r
    D.Xpast D.Xfuture D.evaluations
  filter_upwards [heq, hsum] with ω hy hz
  change res (D.Xpast ω + D.Xfuture ω) = r26t3_Zpath Q.src.G0 a ω at hz
  rw [hy, ← map_add]
  exact hz.symm

#print axioms fp81s21_prediction_past_noise_zero
#print axioms fp81s21_gaussian_prediction_eq_retained_past
end HRS.Fp81.S21
end
