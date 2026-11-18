import HRS.MS.Fp81S21PredictionPhysicalDefs
import HRS.MS.Fp81S21GaussianPropagated
import HRS.MS.Fp81S21GaussModification
import HRS.MS.Fp81S21AdjointAll
import HRS.MS.GenPathAux47

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp
  HRS.MS.CovMeas HRS.MS.ProClosureS111

local instance fp81s21_predictionGaussian_CH_measSpace (H : ℝ) :
    MeasurableSpace (CH H) := borel _
local instance fp81s21_predictionGaussian_CH_borelSpace (H : ℝ) :
    BorelSpace (CH H) := ⟨rfl⟩

/-- The retained linear Gaussian operator agrees with every fixed weighted test
at every fixed time of the continuous physical representative. -/
theorem fp81s21_gaussian_prediction_weighted_agreement
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (r p) (Pw p))
    (εN εG εB : ℕ → ℝ) (S31 : fp81s21_Physical31 p R Es E εN εG εB)
    (G : GaussianRealization R) (L : ℝ) (hL : 0 < L) (a : ℝ) (ha : 0 ≤ a)
    (X : G.Ω → CH (L + p.T))
    (hX : CD E G.P (fun u ω f => OscDual.eval (G.Z u ω) f)
      (max (a - L) 0) (L + p.T) X) :
    GA p R E G (S31.gaussian.quadratic.T G) (max (a - L) 0) (L + p.T) X := by
  intro s f hf
  have hb : 0 ≤ max (a - L) 0 := (recent_geometry L a hL ha).1
  have hu : 0 ≤ max (a - L) 0 + (s : ℝ) := add_nonneg hb s.property.1
  have hq : MemLp (fun ω => X ω s) 2 G.P := by
    exact (ContinuousMap.evalCLM ℝ s).comp_memLp' hX.2.1
  apply fp81s21_linear_weighted_agreement p R E G.P
    (S31.gaussian.quadratic.T G (max (a - L) 0 + (s : ℝ)))
    (fun ω => X ω s) hq
  · intro g hg hgμ
    filter_upwards [hX.2.2,
      (S31.gaussian.quadratic.payload G).2.1
        (max (a - L) 0 + (s : ℝ)) hu g
        (r2Test_isOscTest _ hg) hgμ] with ω hXω hTω
    exact (hXω s g hg).trans hTω.symm
  · exact hf

private theorem fp81s21_prediction_chart_test_coordinate
    {d k : ℕ} {w : ℝ} (E : r26t6_WeightedChart d k w)
    (z : r26t6_Coeff) (j : ℕ) :
    fp81s21_chartAction E z (E.test j) = z j := by
  have he : E.encode (E.test j) =
      (lp.single 2 j (1 : ℝ) : r26t6_Coeff) := by
    ext i
    change E.encode (E.test j) i = _
    rw [E.test_coord]
    simp [lp.single_apply, Pi.single_apply, eq_comm]
  rw [fp81s21_chartAction, he]
  simpa [lp.inner_single_right]

/-- The continuous Gaussian chart path has zero Bochner mean. -/
theorem fp81s21_gaussian_prediction_mean_zero
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (r p) (Pw p))
    (εN εG εB : ℕ → ℝ) (S31 : fp81s21_Physical31 p R Es E εN εG εB)
    (G : GaussianRealization R) (L : ℝ) (hL : 0 < L) (a : ℝ) (ha : 0 ≤ a)
    (X : G.Ω → CH (L + p.T))
    (hX : CD E G.P (fun u ω f => OscDual.eval (G.Z u ω) f)
      (max (a - L) 0) (L + p.T) X) :
    (∫ ω, X ω ∂G.P) = 0 := by
  have hga := fp81s21_gaussian_prediction_weighted_agreement p R Es E
    εN εG εB S31 G L hL a ha X hX
  have hP : (p.d : ℝ) < 2 * Pw p := by dsimp [Pw]; nlinarith [p.hd]
  have hb : 0 ≤ max (a - L) 0 := (recent_geometry L a hL ha).1
  have hmean : ∀ s : I (L + p.T), ∀ j : ℕ,
      (∫ ω, X ω s j ∂G.P) = 0 := by
    intro s j
    have htest : IsR2WeightedTest (r p) (Pw p) (E.test j) :=
      weightedTestSubmodule_iff.1 (weighted_test_of_compact_smooth hP (E.test_smooth j))
    obtain ⟨hf, hagree⟩ := hga s (E.test j) htest
    let u : ℝ := max (a - L) 0 + (s : ℝ)
    let v : Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ) := hf.toLp (E.test j)
    let Y : G.Ω → Fin 1 → ℝ := fun ω _ => (S31.gaussian.quadratic.T G u v) ω
    have hYm : AEMeasurable Y G.P := aemeasurable_pi_iff.2 fun _ =>
      (Lp.stronglyMeasurable (S31.gaussian.quadratic.T G u v)).aestronglyMeasurable.aemeasurable
    obtain ⟨_, hjoint, _⟩ := (S31.gaussian.quadratic.payload G).1 u
      (add_nonneg hb s.property.1)
    have hYmean := (hjoint 1 (fun _ => v)).2
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)
    rw [integral_map hYm (by fun_prop)] at hYmean
    have hscalar : (∫ ω, (S31.gaussian.quadratic.T G u v) ω ∂G.P) = 0 := by
      simpa [Y, ContinuousLinearMap.proj_apply] using hYmean
    calc
      _ = ∫ ω, fp81s21_chartAction E (X ω s) (E.test j) ∂G.P := by
        apply integral_congr_ae
        filter_upwards [] with ω
        exact (fp81s21_prediction_chart_test_coordinate E (X ω s) j).symm
      _ = ∫ ω, (S31.gaussian.quadratic.T G u v) ω ∂G.P := integral_congr_ae hagree
      _ = 0 := hscalar
  have hInt : Integrable X G.P := hX.2.1.integrable one_le_two
  ext s j
  have hc := (ContinuousMap.evalCLM ℝ s).integral_comp_comm hInt
  change (∫ ω, X ω s ∂G.P) = (∫ ω, X ω ∂G.P) s at hc
  have hq : Integrable (fun ω => X ω s) G.P :=
    (ContinuousMap.evalCLM ℝ s).integrable_comp hInt
  have hj := (lp.evalCLM ℝ (fun _ : ℕ => ℝ) (2 : ℝ≥0∞) j).integral_comp_comm hq
  change (∫ ω, X ω s j ∂G.P) = (∫ ω, X ω s ∂G.P) j at hj
  rw [← hc, ← hj, hmean s j]
  rfl

/-- Simultaneous time and Hermite-coordinate agreement with the oscillator path. -/
theorem fp81s21_gaussian_prediction_hermite_agreement
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (r p) (Pw p))
    (εN εG εB : ℕ → ℝ) (S31 : fp81s21_Physical31 p R Es E εN εG εB)
    (G : GaussianRealization R) (L : ℝ) (hL : 0 < L) (a : ℝ) (ha : 0 ≤ a)
    (c : MultiIndex p.d → ℝ)
    (hD : S101Data (r26t3_coeff R) (m p)
      (max (a - L) 0 + (L + p.T)) (r p) c)
    (X : G.Ω → CH (L + p.T))
    (hX : CD E G.P (fun u ω f => OscDual.eval (G.Z u ω) f)
      (max (a - L) 0) (L + p.T) X) :
    ∀ᵐ ω ∂G.P, ∀ s : I (L + p.T), ∀ α : MultiIndex p.d,
      fp81s21_chartAction E (X ω s) (oscTestFun (m p) α) =
        OscDual.coord (G.Z (max (a - L) 0 + (s : ℝ)) ω) α := by
  let H : ℝ := L + p.T
  let b : ℝ := max (a - L) 0
  have hH : 0 < H := by dsimp [H]; linarith [p.hT]
  have hb : 0 ≤ b := (recent_geometry L a hL ha).1
  have hP : (p.d : ℝ) < 2 * Pw p := by dsimp [Pw]; nlinarith [p.hd]
  have hterm : ∀ u : ℝ, 0 ≤ u → ∀ α : MultiIndex p.d,
      propagatorW (r26t3_coeff R) u u (oscTestFun (m p) α) = oscTestFun (m p) α := by
    intro u hu α
    obtain ⟨f, hf⟩ := fp81s21_adjoint_of_hermite_combo p R
      (s101_isCombo_single (m p) α) hu
    exact (s102_propagator_classical ⟨f, hf⟩).terminal
  have htest : ∀ α : MultiIndex p.d, IsR2WeightedTest (r p) (Pw p)
      (oscTestFun (m p) α) := by
    intro α
    have h := (s102_orbit_test hP hD (u := b)
      ⟨hb, by linarith [hH.le]⟩ (t := b) ⟨le_rfl, by linarith [hH.le]⟩ α).1
    rwa [hterm b hb α] at h
  have hga := fp81s21_gaussian_prediction_weighted_agreement p R Es E
    εN εG εB S31 G L hL a ha X hX
  obtain ⟨Zbar, _, hZcont, hZeq⟩ := fp81s21_gauss_modification p R G
  letI : Nonempty (I H) := ⟨⟨0, le_rfl, hH.le⟩⟩
  let seq : ℕ → I H := TopologicalSpace.denseSeq _
  have hseq : DenseRange seq := TopologicalSpace.denseRange_denseSeq _
  have hdense : ∀ᵐ ω ∂G.P, ∀ n : ℕ, ∀ α : MultiIndex p.d,
      fp81s21_chartAction E (X ω (seq n)) (oscTestFun (m p) α) =
        OscDual.eval (Zbar (b + (seq n : ℝ)) ω) (oscTestFun (m p) α) := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro α
    obtain ⟨hf, hga'⟩ := hga (seq n) (oscTestFun (m p) α) (htest α)
    have hu : 0 ≤ b + (seq n : ℝ) := add_nonneg hb (seq n).property.1
    have hT := (S31.gaussian.quadratic.payload G).2.1 (b + (seq n : ℝ)) hu
      (oscTestFun (m p) α) (HRS.MS.GenPath.s56_isOscTest (m p) α) hf
    filter_upwards [hga', hT, hZeq] with ω h1 h2 h3
    exact h1.trans (h2.trans (by rw [h3 _ hu]))
  filter_upwards [hdense, hZeq] with ω hd hz
  intro s α
  have hc : Continuous (fun t : I H =>
      fp81s21_chartAction E (X ω t) (oscTestFun (m p) α)) := by
    change Continuous (fun t => inner ℝ (X ω t) (E.encode (oscTestFun (m p) α)))
    exact (continuous_id.inner continuous_const).comp (X ω).continuous
  let φ : HRS.MS.S111X1.oscSub p.d (m p) :=
    ⟨oscTestFun (m p) α, HRS.MS.GenPath.s56_isOscTest (m p) α⟩
  have he : Continuous (fun z : OscDual p.d (m p) =>
      OscDual.eval z (oscTestFun (m p) α)) := by
    have heq : (fun z : OscDual p.d (m p) => OscDual.eval z (oscTestFun (m p) α)) =
        fun z => gaussianOscEval φ z := by
      funext z
      exact (gaussianOscEval_apply φ z).symm
    rw [heq]
    exact (gaussianOscEval φ).continuous
  have hp : Continuous (fun t : I H =>
      OscDual.eval (Zbar (b + (t : ℝ)) ω) (oscTestFun (m p) α)) :=
    he.comp ((hZcont ω).comp (continuous_const.add continuous_subtype_val))
  have heq : (fun t : I H => fp81s21_chartAction E (X ω t) (oscTestFun (m p) α)) ∘ seq =
      (fun t : I H => OscDual.eval (Zbar (b + (t : ℝ)) ω) (oscTestFun (m p) α)) ∘ seq := by
    funext n
    exact hd n α
  have heq' := congrFun (DenseRange.equalizer hseq hc hp heq) s
  rw [hz (b + (s : ℝ)) (add_nonneg hb s.property.1), OscDual.eval_oscTestFun] at heq'
  exact heq'

/-- The supplied continuous chart path gives the canonical Gaussian prediction. -/
theorem fp81s21_gaussian_prediction_id
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (r p) (Pw p))
    (εN εG εB : ℕ → ℝ) (S31 : fp81s21_Physical31 p R Es E εN εG εB)
    (G : GaussianRealization R) (L : ℝ) (hL : 0 < L) (a : ℝ) (ha : 0 ≤ a)
    (c : MultiIndex p.d → ℝ)
    (hD : S101Data (r26t3_coeff R) (m p)
      (max (a - L) 0 + (L + p.T)) (r p) c)
    (P : CH (L + p.T) →L[ℝ] YH p (L + p.T))
    (hP : PSpec p R E L a P) (X : G.Ω → CH (L + p.T))
    (hX : CD E G.P (fun u ω f => OscDual.eval (G.Z u ω) f)
      (max (a - L) 0) (L + p.T) X) :
    (∫ ω, X ω ∂G.P) = 0 ∧
    GA p R E G (S31.gaussian.quadratic.T G) (max (a - L) 0) (L + p.T) X ∧
    GId p R E G L a X (fun ω => P (cen G.P X ω)) := by
  let H : ℝ := L + p.T
  let b : ℝ := max (a - L) 0
  let θ : ℝ := a - b
  let h : ℝ := θ + p.T
  have hH : 0 < H := by dsimp [H]; linarith [p.hT]
  have hg := recent_geometry L a hL ha
  have hb : 0 ≤ b := hg.1
  have hθ : 0 ≤ θ := hg.2.1
  have hθL : θ ≤ L := hg.2.2.1
  have hsum : b + θ = a := hg.2.2.2
  have hh : h ≤ H := by dsimp [h, H]; linarith
  have hh0 : 0 ≤ h := by dsimp [h]; linarith [p.hT]
  have hpdim : (p.d : ℝ) < 2 * Pw p := by dsimp [Pw]; nlinarith [p.hd]
  have hlin : S102Lin (r26t3_coeff R) (m p) (b + H) :=
    fp81s21_S102Lin p R (b + H)
  have hterm : ∀ u : ℝ, 0 ≤ u → ∀ α : MultiIndex p.d,
      propagatorW (r26t3_coeff R) u u (oscTestFun (m p) α) = oscTestFun (m p) α := by
    intro u hu α
    obtain ⟨f, hf⟩ := fp81s21_adjoint_of_hermite_combo p R
      (s101_isCombo_single (m p) α) hu
    exact (s102_propagator_classical ⟨f, hf⟩).terminal
  have hmean := fp81s21_gaussian_prediction_mean_zero p R Es E εN εG εB S31
    G L hL a ha X hX
  refine ⟨hmean, fp81s21_gaussian_prediction_weighted_agreement p R Es E εN εG εB
    S31 G L hL a ha X hX, ?_⟩
  have hcoord := fp81s21_gaussian_prediction_hermite_agreement p R Es E
    εN εG εB S31 G L hL a ha c hD X hX
  filter_upwards [hcoord, (G.evolution (b + H)).cont] with ω hcoordω hcont
  have hdiag : ∀ s : I H,
      r2Vprop (r26t3_coeff R) (m p) (b + (s : ℝ)) (b + (s : ℝ))
        (fp81s21_chartAction E (X ω s)) = G.Z (b + (s : ℝ)) ω := by
    intro s
    have hu : b + (s : ℝ) ∈ I (b + H) :=
      ⟨add_nonneg hb s.property.1, by linarith [s.property.2]⟩
    apply s102_ext
    intro α
    rw [s102_Vprop_coord hpdim hD (fp81s21_chartAction_S102Z E (X ω s)) hlin
      hu ⟨le_rfl, hu.2⟩ α, hterm _ hu.1 α]
    exact hcoordω s α
  change ∀ v : I H, ∀ τ : I p.T, _
  intro v τ
  let q : ℝ := min (v : ℝ) h
  let s : ℝ := min (v : ℝ) (θ + (τ : ℝ))
  have hq : q ∈ I H := ⟨le_min v.property.1 hh0, (min_le_left _ _).trans v.property.2⟩
  have hs : s ∈ I H := ⟨le_min v.property.1 (add_nonneg hθ τ.property.1),
    (min_le_left _ _).trans v.property.2⟩
  have hu : b + q ∈ I (b + H) := ⟨add_nonneg hb hq.1, by linarith [hq.2]⟩
  have ht : a + (τ : ℝ) ∈ I (b + H) :=
    ⟨add_nonneg ha τ.property.1, by dsimp [H]; linarith [τ.property.2]⟩
  let w : OscPath p.d (m p) (b + H) :=
    windowPathOf (m p) (b + H) 0 (fun u => G.Z u ω)
  have hwat : ∀ t ∈ I (b + H), r2PathAt w t = G.Z t ω := by
    intro t ht'
    exact s102_windowPathOf_at hcont ht'
  have hQ : Qext E b H X ω (b + q) = fp81s21_chartAction E (X ω ⟨q, hq⟩) := by
    unfold Qext
    have hmem : b + q - b ∈ I H := by simpa using hq
    rw [dif_pos hmem]
    congr 2
    apply Subtype.ext
    simp
  have hmatch : r2Vprop (r26t3_coeff R) (m p) (b + q) (b + q)
      (Qext E b H X ω (b + q)) = r2PathAt w (b + q) := by
    rw [hQ, hwat _ hu]
    exact hdiag ⟨q, hq⟩
  have hp := fp81s21_predicted_chart_at hpdim hD hlin E (X ω ⟨q, hq⟩) w
    (Qext E b H X ω) hu ht (by rw [hQ]; exact fp81s21_chartAction_S102Z E _)
    (by intro f hf; rw [hQ]) hmatch
  have heval := hP (X ω) v τ hs
  have hleft : OscPath.at' (P (cen G.P X ω) v) τ =
      r2Vprop (r26t3_coeff R) (m p) (a + (τ : ℝ)) (b + s)
        (fp81s21_chartAction E (X ω ⟨s, hs⟩)) := by
    simpa [cen, hmean, s] using heval
  rw [hleft]
  change _ = r2PathAt (r2Predicted (r26t3_coeff R) w (Qext E b H X ω) (b + q)) (a + (τ : ℝ))
  rw [hp]
  split_ifs with htu
  · have hsval : s = θ + (τ : ℝ) := by
      dsimp [s, q, h] at *
      apply min_eq_right
      linarith [min_le_left (v : ℝ) (θ + p.T)]
    have hst : b + s = a + (τ : ℝ) := by rw [hsval]; linarith
    rw [← hst, hwat _ (by rw [hst]; exact ht)]
    exact hdiag ⟨s, hs⟩
  · have hqv : q = (v : ℝ) := by
      dsimp [q, h] at *
      apply min_eq_left
      have := min_le_right (v : ℝ) (θ + p.T)
      by_contra hv
      have heq := min_eq_right (le_of_not_ge hv)
      rw [heq] at htu
      linarith [τ.property.2]
    have hsv : s = (v : ℝ) := by
      dsimp [s]
      apply min_eq_left
      rw [hqv] at htu
      linarith
    have hsq : s = q := hsv.trans hqv.symm
    change r2Vprop (r26t3_coeff R) (m p) (a + (τ : ℝ)) (b + s)
      (fp81s21_chartAction E (X ω ⟨s, hs⟩)) =
      r2Vprop (r26t3_coeff R) (m p) (a + (τ : ℝ)) (b + q)
      (fp81s21_chartAction E (X ω ⟨q, hq⟩))
    have he : (⟨s, hs⟩ : I H) = ⟨q, hq⟩ := Subtype.ext hsq
    have hc := congrArg (fun t : I H => fp81s21_chartAction E (X ω t)) he
    rw [hc, congrArg (fun t : ℝ => b + t) hsq]

#print axioms HRS.Fp81.S21.fp81s21_gaussian_prediction_weighted_agreement
#print axioms HRS.Fp81.S21.fp81s21_gaussian_prediction_mean_zero
#print axioms HRS.Fp81.S21.fp81s21_gaussian_prediction_hermite_agreement
#print axioms HRS.Fp81.S21.fp81s21_gaussian_prediction_id
end HRS.Fp81.S21
