import HRS.MS.SA16E1E2b

/-!
# S.A.16 E2: `charFlow_pullback_bound`
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Evolution
open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.Whole.AppendixALemmas
  HRS.Whole.AppendixA.Phase2SA16

theorem e2_movDiv_bound {d k : ℕ} (hk : 1 ≤ k) {B : ℝ} {b : ℝ → Euc d → Euc d}
    (hb : DriftBounds d k B b) {r : ℝ} (hr : 0 ≤ r) (z : Euc d) : |movDiv (b r) z| ≤ d * B := by
  have hd : ‖fderiv ℝ (b r) z‖ ≤ B := by
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]
    exact (hb.2 r hr).2.2 1 le_rfl hk z
  unfold movDiv
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i : Fin d, |fderiv ℝ (b r) z (EuclideanSpace.single i 1) i|
      ≤ ∑ _i : Fin d, B := Finset.sum_le_sum fun i _ => by
        refine (PiLp.norm_apply_le _ i |>.trans' (le_of_eq (Real.norm_eq_abs _).symm)).trans ?_
        refine ((fderiv ℝ (b r) z).le_opNorm _).trans ?_
        simpa using mul_le_mul_of_nonneg_right hd (norm_nonneg (EuclideanSpace.single i (1:ℝ)))
    _ = d * B := by simp

theorem e2_det_bound {d k : ℕ} (hk : 1 ≤ k) {B : ℝ} {b : ℝ → Euc d → Euc d}
    (hb : DriftBounds d k B b) {t : ℝ} (ht : 0 ≤ t) {f : ℝ → Euc d} (r : ℝ → ℝ)
    (hr : r = fun s => movDiv (b s) (f s)) :
    Real.exp (-(∫ s in Icc (0:ℝ) t, r s)) ≤ Real.exp (d * B * t) := by
  refine Real.exp_le_exp.2 ?_
  have h := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ)) (s := Icc (0:ℝ) t)
    (f := r) (C := d * B) (by simp) (fun s hs => by
      rw [hr, Real.norm_eq_abs]
      exact e2_movDiv_bound hk hb hs.1 _)
  have h2 : (volume : Measure ℝ).real (Icc (0:ℝ) t) = t := by simp [Measure.real, ht]
  rw [h2, Real.norm_eq_abs] at h
  have := neg_abs_le (∫ s in Icc (0:ℝ) t, r s)
  linarith [le_abs_self (-(∫ s in Icc (0:ℝ) t, r s)), abs_neg (∫ s in Icc (0:ℝ) t, r s)]

/-- E2: pathwise Lp change of variables plus finite chain rule.
No random-flow generator-domain assumption appears here. -/
theorem charFlow_pullback_bound (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k)
    (p B T : ℝ) [Fact (2 ≤ p)] (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ b, DriftBounds d k B b →
      ∀ ν : ℝ, 0 ≤ ν → ∀ w : ℝ≥0 → Fin d → ℝ, Continuous w → w 0=0 →
      ∀ t ∈ Icc (0 : ℝ) T, ∀ φ : Euc d → ℝ, IsCcInfty φ →
      wNormE k p (fun x => φ (Function.invFun (charFlow d b ν w t) x)) ≤
        ENNReal.ofReal (C*Real.exp (C*t))*wNormE k p φ := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hp0 : 0 < p := by linarith
  obtain ⟨C0, hC0pos, hgeo⟩ := charFlow_geometry d k hd hk B T hT
  set K1 : ℝ := ((k + 1 : ℝ) * (k.factorial : ℝ) * (max C0 1) ^ k * ((d : ℝ) + 1) ^ k) with hK1
  have hK10 : 0 < K1 := by positivity
  refine ⟨K1 + d * |B| / p + 1, by positivity, fun b hb ν hν w hw hw0 t ht φ hφ => ?_⟩
  obtain ⟨hbij, hXcd, hΦcd, hder, hdet⟩ := hgeo b hb ν hν w hw hw0 t ht
  set X := charFlow d b ν w t with hX
  set Φ := Function.invFun X with hΦ
  have hφk : ContDiff ℝ k φ := hφ.1.of_le (by exact_mod_cast le_top)
  have hXc : Continuous X := hXcd.continuous
  have hΦc : Continuous Φ := hΦcd.continuous
  have hg : ContDiff ℝ k (fun x => φ (Φ x)) := hφk.comp hΦcd
  have hgc : HasCompactSupport (fun x => φ (Φ x)) := by
    refine HasCompactSupport.intro (hφ.2.isCompact.image hXc) (fun x hx => ?_)
    have hx' : Φ x ∉ tsupport φ := fun h => hx ⟨Φ x, h, Function.invFun_eq (hbij.2 x)⟩
    exact image_eq_zero_of_notMem_tsupport hx'
  have hφc : HasCompactSupport φ := hφ.2
  -- the norm of the pullback is the L^p norm of its jet
  rw [show (fun x => φ (Function.invFun (charFlow d b ν w t) x)) = fun x => φ (Φ x) from rfl,
    e2_wNormE_eq d k p hg hgc, e2_wNormE_eq d k p hφk hφc]
  -- pointwise chain rule bound
  have hpt : ∀ x, ‖wJet k (fun x => φ (Φ x)) x‖ ≤ ‖K1 • wJet k φ (Φ x)‖ := by
    intro x
    have := e2_pointwise d k (C0 := C0) (φ := φ) (Φ := Φ) hφk hΦcd
      (fun j h1 h2 y => (hder j h1 h2 y).2) x
    rw [norm_smul, Real.norm_of_nonneg hK10.le]
    exact this
  have h1 : eLpNorm (wJet k (fun x => φ (Φ x))) (ENNReal.ofReal p) volume ≤
      eLpNorm (K1 • fun x => wJet k φ (Φ x)) (ENNReal.ofReal p) volume :=
    eLpNorm_mono_ae (e2_jet_cont hg).aestronglyMeasurable (Eventually.of_forall hpt)
  rw [eLpNorm_const_smul] at h1
  -- change of variables
  have hJac : ∀ y, |(fderiv ℝ X y).det| ≤ Real.exp (d * B * t) := by
    intro y
    have := hdet y
    have e2 : |LinearMap.det (fderiv ℝ X y).toLinearMap| = |(fderiv ℝ X y).det| := rfl
    rw [e2] at this
    rw [this]
    exact e2_det_bound hk hb ht.1 (f := fun s => charFlow d b ν w s y) _ rfl
  have hcov := e2_cov (V := WIndex d k → ℝ) (q := p) (by linarith) hbij
    (X' := fun y => fderiv ℝ X y)
    (fun y => (hXcd.differentiable (Nat.one_le_iff_ne_zero.1 hk |> fun h => by exact_mod_cast h) y).hasFDerivAt) hJac
    (F := wJet k φ) (sa16j_jet_cont hφ.1 k) hΦc
  refine h1.trans ?_
  have hK1e : ‖K1‖ₑ = ENNReal.ofReal K1 := by
    rw [← ofReal_norm, Real.norm_of_nonneg hK10.le]
  rw [hK1e]
  refine (mul_le_mul_right (hcov) _).trans ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul hK10.le]
  refine mul_le_mul_left ?_ _
  refine ENNReal.ofReal_le_ofReal ?_
  have hexp : Real.exp (d * B * t) ^ (1 / p) = Real.exp (d * B * t / p) := by
    rw [← Real.exp_mul]; congr 1; ring
  rw [hexp]
  set C : ℝ := K1 + d * |B| / p + 1 with hC
  have hdB : (d : ℝ) * B * t / p ≤ C * t := by
    have h1 : (d : ℝ) * B * t / p ≤ (d * |B| / p) * t := by
      rw [div_mul_eq_mul_div]
      refine div_le_div_of_nonneg_right ?_ hp0.le
      have : (d : ℝ) * B ≤ d * |B| := mul_le_mul_of_nonneg_left (le_abs_self B) (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_right this ht.1
    have h2 : (d * |B| / p) * t ≤ C * t := by
      refine mul_le_mul_of_nonneg_right ?_ ht.1
      have : 0 < K1 := hK10
      rw [hC]; linarith
    exact h1.trans h2
  have hKC : K1 ≤ C := by
    have : 0 ≤ (d:ℝ) * |B| / p := by positivity
    rw [hC]; linarith
  exact mul_le_mul hKC (Real.exp_le_exp.2 hdB) (Real.exp_pos _).le (by rw [hC]; positivity)

end HRS.Whole.AppendixA.Phase2SA16Evolution
