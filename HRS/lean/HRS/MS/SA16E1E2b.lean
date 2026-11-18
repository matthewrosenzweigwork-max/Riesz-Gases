import HRS.MS.SA16E1E2a

/-!
# S.A.16 E2 (part b): `wNormE` of a compactly supported `C^k` function, chain rule bound, change of variables
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Evolution
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16

/-- For a compactly supported `C^k` function `wNormE` is the `L^p` norm of the jet. -/
theorem e2_wNormE_eq (d k : ℕ) (p : ℝ) [Fact (2 ≤ p)] {g : Euc d → ℝ} (hg : ContDiff ℝ k g)
    (hc : HasCompactSupport g) :
    wNormE k p g = eLpNorm (wJet k g) (ENNReal.ofReal p) volume := by
  obtain ⟨G, hG⟩ := e2_jet_mem d k p hg hc
  have hz : ∀ᵐ x ∂(volume : Measure (Euc d)),
      ((G : WLp d k p) : Euc d → (WIndex d k → ℝ)) x (wZero d k) = g x := by
    filter_upwards [hG] with x hx
    rw [hx]
    simp only [wJet, wZero, partialDeriv]
    exact iteratedFDeriv_zero_apply _
  rw [wNormE_eq_lift_norm d k p G g hz]
  have hnorm : ‖G‖ = ‖(G : WLp d k p)‖ := rfl
  rw [hnorm, Lp.norm_def, eLpNorm_congr_ae hG]
  exact ENNReal.ofReal_toReal (by
    have := Lp.eLpNorm_lt_top (G : WLp d k p)
    rw [eLpNorm_congr_ae hG] at this
    exact this.ne)

/-- The finite chain rule bound for jets. -/
theorem e2_pointwise (d k : ℕ) {C0 : ℝ} {φ : Euc d → ℝ} {Φ : Euc d → Euc d}
    (hφ : ContDiff ℝ k φ) (hΦ : ContDiff ℝ k Φ)
    (hC0 : ∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ x, ‖iteratedFDeriv ℝ j Φ x‖ ≤ C0) (x : Euc d) :
    ‖wJet k (φ ∘ Φ) x‖ ≤ ((k + 1 : ℝ) * (k.factorial : ℝ) * (max C0 1) ^ k * ((d : ℝ) + 1) ^ k) *
      ‖wJet k φ (Φ x)‖ := by
  set D : ℝ := max C0 1 with hD
  have hD1 : 1 ≤ D := le_max_right _ _
  set Cx : ℝ := ((d : ℝ) + 1) ^ k * ‖wJet k φ (Φ x)‖ with hCx
  have hCx0 : 0 ≤ Cx := by positivity
  have hC : ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i φ (Φ x)‖ ≤ Cx := by
    intro i hi
    refine (sa16j_norm_iter_le φ (Φ x) i).trans ?_
    calc ∑ r : Fin i → Fin d, |partialDeriv r φ (Φ x)|
        ≤ ∑ _r : Fin i → Fin d, ‖wJet k φ (Φ x)‖ :=
          Finset.sum_le_sum fun r _ => sa16j_pd_le_jet k φ (Φ x) hi r
      _ = (d : ℝ) ^ i * ‖wJet k φ (Φ x)‖ := by simp [Finset.sum_const]
      _ ≤ Cx := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          calc (d : ℝ) ^ i ≤ ((d : ℝ) + 1) ^ i :=
                pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) _
            _ ≤ ((d : ℝ) + 1) ^ k :=
                pow_le_pow_right₀ (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg _; linarith) hi
  have hDd : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i Φ x‖ ≤ D ^ i := fun i h1 h2 =>
    (hC0 i h1 h2 x).trans ((le_max_left _ _).trans (le_self_pow₀ hD1 (by omega)))
  refine (sa16j_jet_norm_le k (φ ∘ Φ) x).trans ?_
  have hj : ∀ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ j (φ ∘ Φ) x‖ ≤
      (k.factorial : ℝ) * Cx * D ^ k := by
    intro j hj'
    have hjk : j ≤ k := by have := Finset.mem_range.1 hj'; omega
    have h1 := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (g := φ) (f := Φ) (n := j) (N := (k : ℕ∞ω))
      hφ hΦ (by exact_mod_cast hjk) x (C := Cx) (D := D) (fun i hi => hC i (hi.trans hjk))
      (fun i h1 h2 => hDd i h1 (h2.trans hjk))
    have hf : (j.factorial : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_le hjk
    have hmono : (j.factorial : ℝ) * Cx * D ^ j ≤ (k.factorial : ℝ) * Cx * D ^ k :=
      mul_le_mul (mul_le_mul_of_nonneg_right hf hCx0) (pow_le_pow_right₀ hD1 hjk)
        (by positivity) (by positivity)
    exact h1.trans hmono
  have hsum := Finset.sum_le_sum hj
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  refine hsum.trans (le_of_eq ?_)
  simp only [hCx]
  push_cast
  ring

/-- Change of variables for the `L^q` norm under the inverse of a diffeomorphism with bounded Jacobian. -/
theorem e2_cov {d : ℕ} {V : Type*} [NormedAddCommGroup V] {q : ℝ} (hq : 1 ≤ q)
    {X : Euc d → Euc d} (hX : Function.Bijective X) {X' : Euc d → (Euc d →L[ℝ] Euc d)}
    (hX' : ∀ y, HasFDerivAt X (X' y) y) {J : ℝ} (hJ : ∀ y, |(X' y).det| ≤ J)
    {F : Euc d → V} (hF : Continuous F) (hΦ : Continuous (Function.invFun X)) :
    eLpNorm (fun x => F (Function.invFun X x)) (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (J ^ (1 / q)) * eLpNorm F (ENNReal.ofReal q) volume := by
  have hq0 : 0 < q := by linarith
  have hqe0 : ENNReal.ofReal q ≠ 0 := by simpa using hq0
  have hqetop : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  have hqr : (ENNReal.ofReal q).toReal = q := ENNReal.toReal_ofReal hq0.le
  have hJ0 : 0 ≤ J := (abs_nonneg _).trans (hJ 0)
  have hinj : Function.Injective X := hX.1
  have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul (μ := (volume : Measure (Euc d)))
    (f := X) (f' := X') (s := univ) MeasurableSet.univ (fun y _ => (hX' y).hasFDerivWithinAt)
    hinj.injOn (fun y => ‖F (Function.invFun X y)‖ₑ ^ q)
  have himg : X '' univ = univ := by
    rw [Set.image_univ]; exact Set.range_eq_univ.2 hX.2
  rw [himg] at hcov
  simp only [Measure.restrict_univ] at hcov
  have hmain : ∫⁻ x, ‖F (Function.invFun X x)‖ₑ ^ q ≤ ENNReal.ofReal J * ∫⁻ y, ‖F y‖ₑ ^ q := by
    rw [hcov]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun y => ?_
    simp only [Function.leftInverse_invFun hinj y]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hJ y)) le_rfl
  have hm1 : AEStronglyMeasurable (fun x => F (Function.invFun X x)) volume :=
    (hF.comp hΦ).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hqe0 hqetop hm1,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hqe0 hqetop hF.aestronglyMeasurable, hqr]
  have h1 := ENNReal.rpow_le_rpow hmain (show 0 ≤ 1 / q by positivity)
  refine h1.trans (le_of_eq ?_)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (show 0 ≤ 1 / q by positivity),
    ENNReal.ofReal_rpow_of_nonneg hJ0 (by positivity)]

end HRS.Whole.AppendixA.Phase2SA16Evolution
