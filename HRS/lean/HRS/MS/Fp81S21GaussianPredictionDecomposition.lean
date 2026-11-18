import HRS.MS.Fp81S21GaussianPredictionAdapted3
import HRS.MS.ProClosureS111WindowRestriction

/-! Packet 36B, part (ii): identification of the supplied cutoff paths with
 the retained physical window. This does not identify the 36A prediction with
 the past path. All evaluation hypotheses are literal FutureIndep39 outputs;
 no law of X0 is used. Only countably many fixed-time null sets are intersected. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111 HRS.MS.GenPath

variable {p : Parameters} {δ : ℝ} {R : Trajectory p δ}

local instance fp81s21_decomposition_initial_probability :
    IsProbabilityMeasure (r26t3_mu R 0) := fp81s21_initialMeasure_isProbability p R

/-- The two displayed source-evaluation certificates of FutureIndep39,
for supplied paths on the unchanged source of the physical package. -/
structure fp81s21_CutoffSourceEvaluations (Q : fp81s21_Physical35 p R)
    (H r : ℝ)
    (Xpast Xfuture : Q.src.G0.Ω → OscPath p.d (wholeSpaceIndex p.d : ℝ) H) : Prop where
  past : ∀ (t : Icc (0 : ℝ) H) (φ : Euc p.d → ℝ),
    IsOscTest (wholeSpaceIndex p.d : ℝ) φ → ∀ᵐ ω ∂Q.src.G0.P,
      OscDual.eval (OscPath.at' (Xpast ω) t) φ =
        Q.src.W (Q.src.J (WithLp.toLp 2
          (fp81s21_initialGaussianFeature p R Q.src.hK t φ,
            movingNoiseFeature R 0 t φ - movingNoiseFeature R r t φ))) ω
  future : ∀ (t : Icc (0 : ℝ) H) (φ : Euc p.d → ℝ),
    IsOscTest (wholeSpaceIndex p.d : ℝ) φ → ∀ᵐ ω ∂Q.src.G0.P,
      OscDual.eval (OscPath.at' (Xfuture ω) t) φ =
        Q.src.W (Q.src.J (fp81s21_futureNoiseSourceFeature p R r t φ)) ω

/-- Replayed locally: the actual retained window evaluates to the actual
retained process at each fixed window time. -/
private theorem fp81s21_decomposition_window_at
    (G : GaussianRealization R) (a : ℝ) (ha : 0 ≤ a)
    (τ : Icc (0 : ℝ) p.T) :
    (fun ω => OscPath.at' (r26t3_Zpath G a ω) τ) =ᵐ[G.P]
      fun ω => G.Z (a + τ) ω := by
  have hc := (G.evolution (a + p.T)).cont
  have hm : MapsTo (fun u : ℝ => a + u) (Icc (0 : ℝ) p.T)
      (Icc (0 : ℝ) (a + p.T)) := by
    intro u hu
    exact ⟨add_nonneg ha hu.1, by linarith [hu.2]⟩
  have hshift : ContinuousOn (fun u : ℝ => a + u) (Icc (0 : ℝ) p.T) :=
    (continuous_const.add continuous_id).continuousOn
  filter_upwards [hc] with ω hω
  have hw : Continuous (fun u : Icc (0 : ℝ) p.T => G.Z (a + u) ω) :=
    continuousOn_iff_continuous_restrict.mp (hω.comp hshift hm)
  simp [r26t3_Zpath, processWindow, windowPathOf, OscPath.at', hw]

/-- Part (ii) for any supplied FutureIndep39 cutoff paths, not merely some
paths with the same laws. No smallness radius is needed for this identification. -/
theorem fp81s21_source_cutoff_window_sum
    (Q : fp81s21_Physical35 p R) (a : ℝ) (ha : 0 ≤ a) (r : ℝ)
    (Xpast Xfuture : Q.src.G0.Ω → OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T))
    (hsource : fp81s21_CutoffSourceEvaluations Q (a + p.T) r Xpast Xfuture) :
    (fun ω => physicalWindowRestriction ha (le_refl (a + p.T))
      (Xpast ω + Xfuture ω)) =ᵐ[Q.src.G0.P] r26t3_Zpath Q.src.G0 a := by
  letI : IsProbabilityMeasure (r26t3_mu R 0) := fp81s21_initialMeasure_isProbability p R
  letI : Nonempty (Icc (0 : ℝ) p.T) := ⟨⟨0, le_rfl, p.hT.le⟩⟩
  let s : ℕ → Icc (0 : ℝ) p.T := TopologicalSpace.denseSeq _
  have hs : DenseRange s := TopologicalSpace.denseRange_denseSeq _
  let res := physicalWindowRestriction (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
    ha (le_refl (a + p.T))
  have hcoord : ∀ i : ℕ × MultiIndex p.d, ∀ᵐ ω ∂Q.src.G0.P,
      OscDual.coord (OscPath.at' (res (Xpast ω + Xfuture ω)) (s i.1)) i.2 =
        OscDual.coord (OscPath.at' (r26t3_Zpath Q.src.G0 a ω) (s i.1)) i.2 := by
    intro i
    let t := physicalWindowTime ha (le_refl (a + p.T)) (s i.1)
    let φ := oscTestFun (wholeSpaceIndex p.d : ℝ) i.2
    have hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ := s56_isOscTest _ _
    have hlinear := fp81s21_combined_source_decomposition p R Q.src.hK
      Q.src.G0.P Q.src.J Q.src.W Q.src.rawBundle.2.2.2.1
      Q.src.rawBundle.2.2.2.2.1 Q.src.allFeatureGaussianLaw r t φ
    have hret := Q.src.sourceEvaluation t t.property.1 φ hφ
    have hat := fp81s21_decomposition_window_at Q.src.G0 a ha (s i.1)
    filter_upwards [hsource.past t φ hφ, hsource.future t φ hφ,
      hlinear, hret, hat] with ω hp hf hl hz hw
    have hsum : OscDual.eval (OscPath.at' (Xpast ω) t) φ +
        OscDual.eval (OscPath.at' (Xfuture ω) t) φ =
          OscDual.eval (Q.src.G0.Z t ω) φ := by rw [hp, hf, hz, hl]
    rw [hw]
    change OscDual.coord (OscPath.at' (Xpast ω) t + OscPath.at' (Xfuture ω) t) i.2 =
      OscDual.coord (Q.src.G0.Z t ω) i.2
    rw [OscDual.coord_add]
    simpa only [φ, OscDual.eval_oscTestFun] using hsum
  filter_upwards [ae_all_iff.2 hcoord] with ω hω
  exact s56_pathCoords_injective (wholeSpaceIndex p.d : ℝ) p.T s hs (funext hω)

#print axioms fp81s21_decomposition_window_at
#print axioms fp81s21_source_cutoff_window_sum
end HRS.Fp81.S21
end
