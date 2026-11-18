import HRS.MC.SEdgeB10b
import HRS.MC.SEdgeB7
import HRS.MC.SEdgeB11a
import HRS.Main.HaarAux1
import HRS.MC.SEdgeS16aAux1

/-!
# S16a, Aux2: the Haar-background Gibbs law, coordinates of `eta_N`, uniform coordinate tails

Gibbs-side facts for `sed_S16a_field_clt`: `volume = withDensityReal 1`; `Q_N = modulatedGibbs g N beta volume`
is a probability measure, invariant under diagonal translations, so each one-particle marginal is Haar;
the coordinates of `eta_N = sqrt N (mu_N - dx)` in `E_m` are `jp^{-m} sqrt N mu_N(e_k)`; and by `sed_B7_lln_proof`
(with `m = 1`, `|e_k| <= sqrt 2`) their second moments are bounded by `C jp^{-2m}` uniformly in `N` and `k`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.S16a

open HRS HRS.Sec7 HRS.MC.SEdge

variable {d : ℕ}

theorem s16a_smoothPos : SmoothPosDensity (fun _ : Torus d => (1 : ℝ)) := by
  refine ⟨⟨fun _ => zero_le_one, measurable_const, ?_⟩, ?_, fun _ => one_pos⟩
  · simp
  · unfold Torus.IsSmooth Torus.IsCk Torus.lift
    exact contDiff_const

theorem s16a_wdr_one : withDensityReal (fun _ : Torus d => (1 : ℝ)) = volume := by
  unfold withDensityReal
  simp

/-- The Gibbs law at the Haar background. -/
abbrev s16aQ (d : ℕ) (s : ℝ) (N : ℕ) (β : ℝ) : Measure (Config d N) :=
  modulatedGibbs (periodicRiesz d s) N β (volume : Measure (Torus d))

theorem s16a_sedQ (s β : ℝ) (N : ℕ) :
    sed_Q d s N β (fun _ : Torus d => (1 : ℝ)) = s16aQ d s N β := by
  unfold sed_Q s16aQ
  rw [s16a_wdr_one]

variable {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 ≤ β)
include hd hs0 hs hβ

theorem s16a_prob {N : ℕ} (hN : 1 ≤ N) : IsProbabilityMeasure (s16aQ d s N β) := by
  have := HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hβ (s16a_smoothPos (d := d)) N hN
  rwa [s16a_sedQ] at this

omit hβ in
theorem s16a_invariant {N : ℕ} (hN : 1 ≤ N) (a : Torus d) :
    (s16aQ d s N β).map (fun X : Config d N => fun i => X i + a) = s16aQ d s N β := by
  have hsd : s < d := by
    have : (d : ℝ) / 2 ≤ d := by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    linarith
  exact haar_gibbs_shift_invariant (PoleCavityAux.measurable_periodicRiesz hd hs0 hsd) hN β a

omit hd hs0 hs hβ in
/-- Every one-particle marginal of a translation invariant law is Haar. -/
theorem s16a_marginal_volume {N : ℕ} {Q : Measure (Config d N)} [IsProbabilityMeasure Q]
    (hQ : ∀ a : Torus d, Q.map (fun X : Config d N => fun i => X i + a) = Q) (i : Fin N) :
    Q.map (fun X : Config d N => X i) = (volume : Measure (Torus d)) := by
  have he : Measurable (fun X : Config d N => X i) := measurable_pi_apply _
  have hinv : ∀ a : Torus d,
      (Q.map (fun X : Config d N => X i)).map (fun x : Torus d => x + a) =
        Q.map (fun X : Config d N => X i) := by
    intro a
    have hcomp : ((fun x : Torus d => x + a) ∘ (fun X : Config d N => X i)) =
        (fun X : Config d N => X i) ∘ (fun X : Config d N => fun i => X i + a) := rfl
    rw [Measure.map_map (measurable_add_const a) he, hcomp,
      ← Measure.map_map he (haar_shift_measurable (N := N) (d := d) a), hQ a]
  have hprob : IsProbabilityMeasure (Q.map (fun X : Config d N => X i)) :=
    (Measure.isProbabilityMeasure_map_iff he.aemeasurable).2 inferInstance
  have : Measure.IsAddLeftInvariant (Q.map (fun X : Config d N => X i)) := ⟨fun a => by
    have e : (fun x : Torus d => a + x) = fun x => x + a := funext fun x => add_comm a x
    rw [e]
    exact hinv a⟩
  have hc := Measure.isAddInvariant_eq_smul_of_compactSpace (Q.map (fun X : Config d N => X i))
    (volume : Measure (Torus d))
  have hmass := congrArg (fun ν : Measure (Torus d) => ν Set.univ) hc
  have hc1 : (Q.map (fun X : Config d N => X i)).addHaarScalarFactor
      (volume : Measure (Torus d)) = 1 := by
    simpa using hmass.symm
  rw [hc, hc1, one_smul]

omit hd hs0 hs hβ in
theorem s16a_realMode_meas (k : NonzeroLattice d) : Measurable (Torus.realMode k : Torus d → ℝ) :=
  (continuous_realMode' k).measurable

/-- `E_Q mu_N(e_k) = 0`. -/
theorem s16a_centering {N : ℕ} (hN : 1 ≤ N) (k : NonzeroLattice d) :
    ∫ X, pair (empirical X) (Torus.realMode k) ∂(s16aQ d s N β) = 0 := by
  have := s16a_prob hd hs0 hs hβ hN
  have hinv := s16a_invariant (β := β) hd hs0 hs hN
  have hm := fun i : Fin N => s16a_marginal_volume (Q := s16aQ d s N β) hinv i
  have hi : ∀ i : Fin N, ∫ X, Torus.realMode k (X i) ∂(s16aQ d s N β) = 0 := by
    intro i
    have := integral_map (μ := s16aQ d s N β) (φ := fun X : Config d N => X i)
      (f := (Torus.realMode k : Torus d → ℝ)) (measurable_pi_apply i).aemeasurable
      (s16a_realMode_meas k).aestronglyMeasurable
    rw [← this, hm i]
    exact Torus.integral_realMode k
  have hbd : ∀ (i : Fin N) (X : Config d N), |Torus.realMode k (X i)| ≤ Real.sqrt 2 :=
    fun i X => Torus.abs_realMode_le k _
  have hint : ∀ i : Fin N, Integrable (fun X : Config d N => Torus.realMode k (X i))
      (s16aQ d s N β) := fun i =>
    Integrable.of_bound ((s16a_realMode_meas k).comp (measurable_pi_apply i)).aestronglyMeasurable
      (Real.sqrt 2) (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]; exact hbd i X)
  have : ∀ X : Config d N, pair (empirical X) (Torus.realMode k) =
      (∑ i, Torus.realMode k (X i)) / N := fun X =>
    HRS.MC.SEdge.B4c.b4c_pair_empirical X (s16a_realMode_meas k)
  simp_rw [this]
  rw [integral_div, integral_finsetSum _ fun i _ => hint i]
  simp [hi]

omit hd hs0 hs hβ in
theorem s16a_coord_eta {m : ℝ} (hm : (d : ℝ) < 2 * m) {N : ℕ} (hN : 1 ≤ N) (X : Config d N)
    (k : NonzeroLattice d) :
    NegSobolev.coord (etaE m X (volume : Measure (Torus d))) k =
      Lattice.jp k.1 ^ (-m) * (Real.sqrt N * pair (empirical X) (Torus.realMode k)) := by
  have h := coord_ofMeasureDiff_empirical (m := m) hm (volume : Measure (Torus d)) hN X k
  have h2 : NegSobolev.coord (etaE m X (volume : Measure (Torus d))) k =
      Real.sqrt N * NegSobolev.coord (NegSobolev.ofMeasureDiff m (empirical X)
        (volume : Measure (Torus d))) k := rfl
  rw [h2, h]
  have h3 : Torus.measureRealCoeff (volume : Measure (Torus d)) k = 0 := Torus.integral_realMode k
  rw [h3, HRS.MC.SEdge.B4c.b4c_pair_empirical X (s16a_realMode_meas k)]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  field_simp
  ring

/-- Uniform second-moment bound for the coordinates of `eta_N`. -/
theorem s16a_pair_sq_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ k : NonzeroLattice d,
      ∫ X, pair (empirical X) (Torus.realMode k) ^ 2 ∂(s16aQ d s N β) ≤ C / N := by
  obtain ⟨C0, hC0⟩ := HRS.MC.SEdge.B7.sed_B7_lln_proof hd hs0 hs hβ (s16a_smoothPos (d := d))
    (Real.sqrt 2) 1
  refine ⟨max C0 0, le_max_right _ _, fun N hN k => ?_⟩
  have h := hC0 (Torus.realMode k) (s16a_realMode_meas k) (fun x => Torus.abs_realMode_le k x) N hN
  rw [s16a_sedQ, s16a_wdr_one] at h
  have h0 : pair (volume : Measure (Torus d)) (Torus.realMode k) = 0 := Torus.integral_realMode k
  rw [h0] at h
  simp only [sub_zero, mul_one, pow_one] at h
  refine h.trans ?_
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  exact div_le_div_of_nonneg_right (le_max_left _ _) hNpos.le

theorem s16a_coord_tail {m : ℝ} (hm : (d : ℝ) < 2 * m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ k : NonzeroLattice d,
      ∫⁻ X, ENNReal.ofReal (NegSobolev.coord (etaE m X (volume : Measure (Torus d))) k ^ 2)
        ∂(s16aQ d s N β) ≤ ENNReal.ofReal (C * Lattice.jp k.1 ^ (-(2 * m))) := by
  obtain ⟨C, hC0, hC⟩ := s16a_pair_sq_bound hd hs0 hs hβ
  refine ⟨C, hC0, fun N hN k => ?_⟩
  haveI := s16a_prob hd hs0 hs hβ hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set u := (Torus.realMode k : Torus d → ℝ) with hu
  have hcoord : ∀ X : Config d N, NegSobolev.coord (etaE m X (volume : Measure (Torus d))) k ^ 2 =
      Lattice.jp k.1 ^ (-(2 * m)) * N * pair (empirical X) u ^ 2 := by
    intro X
    rw [s16a_coord_eta hm hN, mul_pow, mul_pow, Real.sq_sqrt hNpos.le,
      show -(2 * m) = 2 * (-m) by ring, ← Torus.jp_rpow_sq]
    ring
  have hmeas : Measurable (fun X : Config d N => pair (empirical X) u) := by
    have : (fun X : Config d N => pair (empirical X) u) = fun X => (∑ i, u (X i)) / N :=
      funext fun X => HRS.MC.SEdge.B4c.b4c_pair_empirical X (s16a_realMode_meas k)
    rw [this]
    exact (Finset.measurable_sum _ fun i _ => (s16a_realMode_meas k).comp (measurable_pi_apply i)).div_const _
  have hbd : ∀ X : Config d N, |pair (empirical X) u| ≤ Real.sqrt 2 := by
    intro X
    haveI := empirical_isProbabilityMeasure hN X
    unfold pair
    calc |∫ x, u x ∂(empirical X)| ≤ ∫ x, |u x| ∂(empirical X) := by
          simpa using abs_integral_le_integral_abs (μ := empirical X) (f := u)
      _ ≤ ∫ x, Real.sqrt 2 ∂(empirical X) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _)
            (integrable_const _) (Filter.Eventually.of_forall fun x => Torus.abs_realMode_le k x)
      _ = Real.sqrt 2 := by simp
  have hint : Integrable (fun X : Config d N => pair (empirical X) u ^ 2) (s16aQ d s N β) :=
    Integrable.of_bound (hmeas.pow_const 2).aestronglyMeasurable (Real.sqrt 2 ^ 2)
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hbd X) 2)
  have hj : 0 < Lattice.jp k.1 ^ (-(2 * m)) := Real.rpow_pos_of_pos (Torus.jp_pos _) _
  have hint2 : Integrable (fun X : Config d N =>
      Lattice.jp k.1 ^ (-(2 * m)) * N * pair (empirical X) u ^ 2) (s16aQ d s N β) :=
    hint.const_mul _
  simp_rw [hcoord]
  rw [← ofReal_integral_eq_lintegral_ofReal hint2
    (Filter.Eventually.of_forall fun X => mul_nonneg (mul_nonneg hj.le hNpos.le) (sq_nonneg _))]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ∫ X, Lattice.jp k.1 ^ (-(2 * m)) * N * pair (empirical X) u ^ 2 ∂(s16aQ d s N β)
      = Lattice.jp k.1 ^ (-(2 * m)) * N * ∫ X, pair (empirical X) u ^ 2 ∂(s16aQ d s N β) := by
        rw [integral_const_mul]
    _ ≤ Lattice.jp k.1 ^ (-(2 * m)) * N * (C / N) :=
        mul_le_mul_of_nonneg_left (hC N hN k) (by positivity)
    _ = C * Lattice.jp k.1 ^ (-(2 * m)) := by field_simp

end HRS.MC.SEdge.S16a

end
