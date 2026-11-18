import HRS.MC.Sec7Vocab
import HRS.MC.S7S7a
import HRS.MC.SEdgeB7
import HRS.MC.SEdgeB4b
import HRS.MC.SEdgeB5b
import HRS.Energy.StaticLimitJoint
import HRS.Energy.StaticLimitEnergy

/-!
# Packet `s7_S7c_hilbert_stein`, helper 1: the coordinates of `zeta_N`

`coord (zetaE r Q X) k = sed_Y Q (phi_k) X`, measurability of `zetaE`, and the `L^1` bound
`E |W_{N,k}| <= c0 <k>^{-r}` (from the law of large numbers `sed_B7_lln`), hence integrability of `||W_N||`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7c

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux

variable {d : ℕ}

theorem s7c_meanEmp_integral {N : ℕ} (hN : 1 ≤ N) (P : Measure (Config d N)) [IsProbabilityMeasure P]
    {f : Torus d → ℝ} (hf : Continuous f) :
    ∫ x, f x ∂(meanEmpirical P) = ∫ Y, pair (empirical Y) f ∂P := by
  rw [integral_meanEmpirical P hf]
  have : ∀ Y : Config d N, pair (empirical Y) f = (N : ℝ)⁻¹ * ∑ i, f (Y i) :=
    fun Y => pair_empirical (by omega) Y f
  simp_rw [this]
  rw [integral_const_mul, integral_finsetSum]
  intro i _
  exact (hf.comp (continuous_apply i)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem s7c_coord_zeta {N : ℕ} (hN : 1 ≤ N) {r : ℝ} (hr : (d : ℝ) < 2 * r)
    (P : Measure (Config d N)) [IsProbabilityMeasure P] (X : Config d N) (k : NonzeroLattice d) :
    NegSobolev.coord (zetaE r P X) k = sed_Y P (s7_phi r k) X := by
  haveI := empirical_isProbabilityMeasure (by omega : 0 < N) X
  haveI := isProbabilityMeasure_meanEmpirical P hN
  unfold zetaE
  rw [NegSobolev.coord_smul', coord_ofMeasureDiff hr]
  have hphi : s7_phi r k = fun x => Lattice.jp k.1 ^ (-r) * Torus.realMode k x := rfl
  unfold sed_Y
  rw [hphi]
  have h1 : ∀ Z : Config d N, pair (empirical Z) (fun x => Lattice.jp k.1 ^ (-r) * Torus.realMode k x) =
      Lattice.jp k.1 ^ (-r) * pair (empirical Z) (Torus.realMode k) := by
    intro Z; unfold pair; rw [integral_const_mul]
  have h2 : ∫ Y, pair (empirical Y) (fun x => Lattice.jp k.1 ^ (-r) * Torus.realMode k x) ∂P =
      Lattice.jp k.1 ^ (-r) * ∫ Y, pair (empirical Y) (Torus.realMode k) ∂P := by
    simp_rw [h1]; rw [integral_const_mul]
  rw [h1, h2]
  unfold Torus.measureRealCoeff
  rw [s7c_meanEmp_integral hN P (continuous_realMode' k)]
  unfold pair
  ring

theorem s7c_zeta_meas {N : ℕ} (hN : 1 ≤ N) {r : ℝ} (hr : (d : ℝ) < 2 * r)
    (P : Measure (Config d N)) [IsProbabilityMeasure P] : Measurable (zetaE r P) := by
  haveI := isProbabilityMeasure_meanEmpirical P hN
  have := (measurable_ofMeasureDiff_empirical (m := r) hr (meanEmpirical P) hN).const_smul
    (Real.sqrt N)
  exact this


theorem s7c_abs_int_sq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : Ω → ℝ} (hm : Measurable Y) {M : ℝ} (hb : ∀ x, |Y x| ≤ M) :
    (∫ x, |Y x| ∂P) ^ 2 ≤ ∫ x, Y x ^ 2 ∂P := by
  have hL : MemLp (fun x => |Y x|) 2 P :=
    MemLp.of_bound hm.abs.aestronglyMeasurable M (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs, abs_abs] using hb x)
  have h := variance_eq_sub hL
  have h0 := variance_nonneg (fun x => |Y x|) P
  have : (fun x => |Y x|) ^ 2 = fun x => Y x ^ 2 := by funext x; simp [sq_abs]
  rw [this] at h
  simp only [Pi.pow_apply] at h
  have h2 : ∫ x, |Y x| ∂P = P[fun x => |Y x|] := rfl
  rw [h2]
  linarith

theorem s7c_Wk_L1 {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {r : ℝ} :
    ∃ c0 : ℝ, 0 ≤ c0 ∧ ∀ N : ℕ, 1 ≤ N → ∀ k : NonzeroLattice d,
      Integrable (fun X => sed_Y (sed_Q d s N γ ρ) (s7_phi r k) X) (sed_Q d s N γ ρ) ∧
      ∫ X, |sed_Y (sed_Q d s N γ ρ) (s7_phi r k) X| ∂(sed_Q d s N γ ρ) ≤
        c0 * Lattice.jp k.1 ^ (-r) := by
  obtain ⟨C, hC⟩ := HRS.MC.SEdge.B7.sed_B7_lln_proof hd hs0 hs hγ hρ (Real.sqrt 2) 1
  refine ⟨2 * Real.sqrt (max C 0), by positivity, fun N hN k => ?_⟩
  haveI hP : IsProbabilityMeasure (withDensityReal ρ) := HRS.MC.SEdge.B3.b3_prob hρ
  haveI hQ : IsProbabilityMeasure (sed_Q d s N γ ρ) :=
    HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hγ hρ N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  set u : Torus d → ℝ := Torus.realMode k with hu
  have hum : Measurable u := (continuous_realMode' k).measurable
  have hub : ∀ x, |u x| ≤ Real.sqrt 2 := fun x => Torus.abs_realMode_le k x
  set c : ℝ := Lattice.jp k.1 ^ (-r) with hc
  have hc0 : 0 ≤ c := by have := Torus.jp_pos k.1; positivity
  set Y : Config d N → ℝ := fun X => pair (empirical X) u - pair (withDensityReal ρ) u with hY
  have hpm : Measurable (fun X : Config d N => pair (empirical X) u) :=
    HRS.MC.SEdge.B5b.b5b_pair_meas hN hum
  have hYm : Measurable Y := hpm.sub_const _
  have hYb : ∀ X, |Y X| ≤ 2 * Real.sqrt 2 := fun X =>
    HRS.MC.SEdge.B7.b7_bound hN (withDensityReal ρ) hum hub X
  have hYi : Integrable Y (sed_Q d s N γ ρ) :=
    Integrable.of_bound hYm.aestronglyMeasurable _ (Filter.Eventually.of_forall fun X => by
      simpa [Real.norm_eq_abs] using hYb X)
  set m : ℝ := ∫ X, Y X ∂(sed_Q d s N γ ρ) with hm
  have hphi : ∀ X : Config d N, pair (empirical X) (s7_phi r k) = c * pair (empirical X) u := by
    intro X; unfold pair; show ∫ x, c * u x ∂(empirical X) = _; rw [integral_const_mul]
  have hpi : Integrable (fun X : Config d N => pair (empirical X) u) (sed_Q d s N γ ρ) := by
    refine Integrable.of_bound hpm.aestronglyMeasurable (Real.sqrt 2) (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs]
    exact HRS.MC.SEdge.B5b.b5b_pair_bdd hN hub X
  have hYX : ∀ X, sed_Y (sed_Q d s N γ ρ) (s7_phi r k) X = c * Real.sqrt N * (Y X - m) := by
    intro X
    unfold sed_Y
    have h1 : ∫ Z, pair (empirical Z) (s7_phi r k) ∂(sed_Q d s N γ ρ) =
        c * ∫ Z, pair (empirical Z) u ∂(sed_Q d s N γ ρ) := by
      simp_rw [hphi]; rw [integral_const_mul]
    have h2 : m = ∫ Z, pair (empirical Z) u ∂(sed_Q d s N γ ρ) - pair (withDensityReal ρ) u := by
      rw [hm]; simp only [hY]; rw [integral_sub hpi (integrable_const _)]; simp
    rw [hphi, h1, h2]
    simp only [hY]
    ring
  have hint : Integrable (fun X => sed_Y (sed_Q d s N γ ρ) (s7_phi r k) X) (sed_Q d s N γ ρ) := by
    simp_rw [hYX]
    exact (hYi.sub (integrable_const _)).const_mul _
  refine ⟨hint, ?_⟩
  have hmY : |m| ≤ ∫ X, |Y X| ∂(sed_Q d s N γ ρ) := abs_integral_le_integral_abs
  have hE : ∫ X, |sed_Y (sed_Q d s N γ ρ) (s7_phi r k) X| ∂(sed_Q d s N γ ρ) ≤
      c * Real.sqrt N * (2 * ∫ X, |Y X| ∂(sed_Q d s N γ ρ)) := by
    simp_rw [hYX, abs_mul]
    rw [integral_const_mul]
    rw [abs_of_nonneg hc0, abs_of_nonneg (Real.sqrt_nonneg _)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ∫ X, |Y X - m| ∂(sed_Q d s N γ ρ) ≤ ∫ X, (|Y X| + |m|) ∂(sed_Q d s N γ ρ) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
            (hYi.abs.add (integrable_const _)) (Filter.Eventually.of_forall fun X => abs_sub _ _)
      _ = ∫ X, |Y X| ∂(sed_Q d s N γ ρ) + |m| := by
          rw [integral_add hYi.abs (integrable_const _)]; simp
      _ ≤ 2 * ∫ X, |Y X| ∂(sed_Q d s N γ ρ) := by linarith
  have hsq := s7c_abs_int_sq (sed_Q d s N γ ρ) hYm hYb
  have hmom : ∫ X, Y X ^ 2 ∂(sed_Q d s N γ ρ) ≤ max C 0 / N := by
    have := hC u hum hub N hN
    simp only [pow_one, mul_one] at this
    exact this.trans (div_le_div_of_nonneg_right (le_max_left _ _) hNp.le)
  have hE1 : ∫ X, |Y X| ∂(sed_Q d s N γ ρ) ≤ Real.sqrt (max C 0 / N) :=
    Real.le_sqrt_of_sq_le (hsq.trans hmom)
  have hsN : Real.sqrt N * Real.sqrt (max C 0 / N) = Real.sqrt (max C 0) := by
    rw [← Real.sqrt_mul hNp.le]; congr 1; field_simp
  calc _ ≤ c * Real.sqrt N * (2 * ∫ X, |Y X| ∂(sed_Q d s N γ ρ)) := hE
    _ ≤ c * Real.sqrt N * (2 * Real.sqrt (max C 0 / N)) := by gcongr
    _ = (2 * Real.sqrt (max C 0)) * c := by rw [← hsN]; ring

end HRS.MC.Sec7.S7c

end
