import HRS.MS.Fp81S21PredictionPhysical
import HRS.MS.Fp81S21GaussianWindowRS2

/-! Simultaneous compatibility with the supplied continuous Gaussian prediction.
Countable reconstruction is applied to two continuous predictions, never to an
uncountable family of raw almost-everywhere coefficient identities. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp HRS.MS.CovMeas

private theorem fp81s21_recentRS_coeff_ext
    {d k : ℕ} {w : ℝ} (E : r26t6_WeightedChart d k w) (x y : r26t6_Coeff)
    (h : ∀ f, IsR2Test f → fp81s21_chartAction E x f = fp81s21_chartAction E y f) :
    x = y := by
  ext i
  have he : E.encode (E.test i) = (lp.single 2 i (1 : ℝ) : r26t6_Coeff) := by
    ext j
    rw [E.test_coord]
    simp [lp.single_apply, Pi.single_apply, eq_comm]
  have hi := h (E.test i) (E.test_smooth i)
  simpa [fp81s21_chartAction, he, lp.inner_single_right] using hi

/-- The retained Gaussian prediction agrees at every recent cutoff, including
the clipped tail, with the supplied `GRS` prediction. `CD`, zero mean and `PSpec`
are exactly packet 33's certificates, using the same retained chart. -/
theorem fp81s21_recentRS_gaussian_prediction_restrict
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) (Q : fp81s21_Physical35 p R)
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (L : ℝ) (hL : 0 < L) (a : ℝ) (ha : 0 ≤ a) (Φ : Window p → ℝ)
    (W : fp81s21_GRS Q future a ha Φ)
    (X : Q.src.G0.Ω → CH (L + p.T))
    (hX : CD Q.E Q.src.G0.P (fun u ω f => OscDual.eval (Q.src.G0.Z u ω) f)
      (max (a - L) 0) (L + p.T) X)
    (hmean : (∫ ω, X ω ∂Q.src.G0.P) = 0)
    (P : CH (L + p.T) →L[ℝ] YH p (L + p.T)) (hP : PSpec p R Q.E L a P) :
    ∀ᵐ ω ∂Q.src.G0.P, ∀ v : I (L + p.T),
      P (cen Q.src.G0.P X ω) v = fp81s21_remote_G_extend Q.src.G0 a ha W.Y ω
        (max (a - L) 0 + min (v : ℝ) (a - max (a - L) 0 + p.T)) := by
  let b := max (a - L) 0
  let h := a - b + p.T
  have hg := recent_geometry L a hL ha
  have hb : 0 ≤ b := hg.1
  have hθ : 0 ≤ a - b := hg.2.1
  have hh : 0 ≤ h := add_nonneg hθ p.hT.le
  let cut : I (L + p.T) → I (a + p.T) := fun v =>
    ⟨b + min (v : ℝ) h, add_nonneg hb (le_min v.property.1 hh), by
      have := min_le_right (v : ℝ) h
      dsimp [h] at *
      linarith⟩
  have hcut : Continuous cut :=
    (continuous_const.add (continuous_subtype_val.min continuous_const)).subtype_mk _
  have hsec (s : I (L + p.T)) :
      (fun ω => X ω s) =ᵐ[Q.src.G0.P]
        fp81s21_gaussian35_qG Q.tofp81s21_Gaussian35Selection (b + (s : ℝ)) := by
    have hc := ((Q.canon.payload Q.src.G0).coefficients.weak_momentRep.2
      (b + (s : ℝ)) (add_nonneg hb s.property.1)).2.2
    filter_upwards [hX.2.2, hc] with ω hx hq
    apply fp81s21_recentRS_coeff_ext Q.E
    intro f hf
    exact (hx s f hf).trans (hq.1 f hf).symm
  have hfixed (v : I (L + p.T)) (τ : I p.T) :
      ∀ᵐ ω ∂Q.src.G0.P, OscPath.at' (P (cen Q.src.G0.P X ω) v) τ =
        OscPath.at' (W.Y ω (cut v)) τ := by
    let s : I (L + p.T) := ⟨min (v : ℝ) (a - b + (τ : ℝ)),
      le_min v.property.1 (add_nonneg hθ τ.property.1),
      (min_le_left _ _).trans v.property.2⟩
    have htime : b + (s : ℝ) = min (cut v : ℝ) (a + (τ : ℝ)) := by
      change b + min (v : ℝ) (a - b + (τ : ℝ)) =
        min (b + min (v : ℝ) h) (a + (τ : ℝ))
      dsimp [h]
      simp only [min_def]
      split_ifs <;> linarith [τ.property.2]
    filter_upwards [hsec s, W.physical (cut v) τ] with ω hx hw
    have hp := hP (X ω) v τ s.property
    simp only [cen, hmean, sub_zero]
    rw [hw]
    change OscPath.at' (P (X ω) v) τ = _
    change OscPath.at' (P (X ω) v) τ =
      r2Vprop (r26t3_coeff R) (m p) (a + (τ : ℝ)) (b + (s : ℝ))
        (fp81s21_chartAction Q.E (X ω s)) at hp
    rw [hp, hx, htime]
  letI : Nonempty (I (L + p.T)) := ⟨⟨0, le_rfl, (add_pos hL p.hT).le⟩⟩
  letI : Nonempty (I p.T) := ⟨⟨0, le_rfl, p.hT.le⟩⟩
  let vs : ℕ → I (L + p.T) := TopologicalSpace.denseSeq _
  let ts : ℕ → I p.T := TopologicalSpace.denseSeq _
  have hv : DenseRange vs := TopologicalSpace.denseRange_denseSeq _
  have ht : DenseRange ts := TopologicalSpace.denseRange_denseSeq _
  have hcount : ∀ᵐ ω ∂Q.src.G0.P, ∀ n : ℕ, ∀ k : ℕ,
      OscPath.at' (P (cen Q.src.G0.P X ω) (vs n)) (ts k) =
        OscPath.at' (W.Y ω (cut (vs n))) (ts k) :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun k => hfixed (vs n) (ts k)
  filter_upwards [hcount] with ω hω
  have hpaths (n : ℕ) : P (cen Q.src.G0.P X ω) (vs n) = W.Y ω (cut (vs n)) := by
    apply ContinuousMap.ext
    exact congrFun (DenseRange.equalizer ht
      (P (cen Q.src.G0.P X ω) (vs n)).continuous
      (W.Y ω (cut (vs n))).continuous (funext (hω n)))
  have hall := DenseRange.equalizer hv (P (cen Q.src.G0.P X ω)).continuous
    ((W.Y ω).continuous.comp hcut) (funext hpaths)
  intro v
  have he := congrFun hall v
  change P (cen Q.src.G0.P X ω) v = W.Y ω (cut v) at he
  rw [he]
  change W.Y ω (cut v) = W.Y ω (projIcc 0 (a + p.T) _ (cut v : ℝ))
  rw [projIcc_val]

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_recentRS_gaussian_prediction_restrict
end
