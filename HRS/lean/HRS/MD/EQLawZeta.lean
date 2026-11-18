import HRS.Energy.StaticLimitBasic
import HRS.Energy.Modulated
import HRS.Torus.Sobolev

/-!
# EQ-LAW (packet `eq_path_stationary`), part 3: continuity of `ζ_N` in the configuration, measurability of path functionals

* `eqlaw_continuous_of_coord`: a map into `E_m` with continuous coordinates and square-summable uniform bound is continuous.
* `eqlaw_continuous_zetaE`: for `m > d/2` and a probability law `P` on configurations the map `x ↦ zetaE m P x` is continuous.
* `eqlaw_pathOf`, `eqlaw_aemeasurable_pathOf`: the "continuous path or `0`" construction of `windowZeta`, and a.e.
  measurability of `σ ↦ pathOf (f σ)` when the evaluations are measurable and the paths a.s. continuous.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQLawPath

variable {d : ℕ} {m : ℝ}

theorem eqlaw_coord_sub (F G : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (F - G) k = NegSobolev.coord F k - NegSobolev.coord G k := by
  have := congrFun (lp.coeFn_sub (show lp (fun _ : NonzeroLattice d => ℝ) 2 from F)
    (show lp (fun _ : NonzeroLattice d => ℝ) 2 from G)) k
  exact this

theorem eqlaw_continuous_of_coord {α : Type*} [TopologicalSpace α] (F : α → NegSobolev d m)
    (b : NonzeroLattice d → ℝ) (hb : Summable b)
    (hc : ∀ k, Continuous fun x => NegSobolev.coord (F x) k)
    (hbd : ∀ x k, NegSobolev.coord (F x) k ^ 2 ≤ b k) : Continuous F := by
  rw [continuous_iff_continuousAt]
  intro y
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hε2 : (0 : ℝ) < ε ^ 2 / 8 := by positivity
  obtain ⟨s, hs⟩ := ((tendsto_order.1 (tendsto_tsum_compl_atTop_zero b)).2 _ hε2).exists
  have h2 : Continuous fun x => ∑ k ∈ s, (NegSobolev.coord (F x) k - NegSobolev.coord (F y) k) ^ 2 :=
    continuous_finsetSum _ fun k _ => ((hc k).sub continuous_const).pow 2
  have hy0 : (∑ k ∈ s, (NegSobolev.coord (F y) k - NegSobolev.coord (F y) k) ^ 2) < ε ^ 2 / 2 := by
    simp only [sub_self]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    positivity
  filter_upwards [h2.continuousAt.eventually (Iio_mem_nhds hy0)] with x hx
  have hx' : (∑ k ∈ s, (NegSobolev.coord (F x) k - NegSobolev.coord (F y) k) ^ 2) < ε ^ 2 / 2 := hx
  obtain ⟨hsum, hnorm⟩ := NegSobolev.coord_sq (F x - F y)
  simp_rw [eqlaw_coord_sub] at hsum hnorm
  have hbs : Summable fun k => 4 * b k := hb.mul_left 4
  have hle : ∀ k, (NegSobolev.coord (F x) k - NegSobolev.coord (F y) k) ^ 2 ≤ 4 * b k := by
    intro k
    have h1 := hbd x k
    have h2 := hbd y k
    nlinarith [sq_nonneg (NegSobolev.coord (F x) k + NegSobolev.coord (F y) k)]
  have htail : ∑' k : {k // k ∉ s}, (NegSobolev.coord (F x) k - NegSobolev.coord (F y) k) ^ 2 ≤
      4 * ∑' k : {k // k ∉ s}, b k := by
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun k => hle k) (hsum.subtype _) (hbs.subtype _)
  have hsplit := hsum.sum_add_tsum_subtype_compl s
  have hn2 : ‖F x - F y‖ ^ 2 < ε ^ 2 := by
    rw [hnorm, ← hsplit]
    linarith
  rw [dist_eq_norm]
  by_contra hge
  push Not at hge
  have := pow_le_pow_left₀ hε.le hge 2
  linarith

theorem eqlaw_continuous_ofMeasureDiff_empirical {N : ℕ} (hm : (d : ℝ) < 2 * m) (ν : Measure (Torus d))
    [IsProbabilityMeasure ν] (hN : 1 ≤ N) :
    Continuous fun X : Config d N => NegSobolev.ofMeasureDiff m (empirical X) ν := by
  refine eqlaw_continuous_of_coord _ (fun k => 8 * Lattice.jp k.1 ^ (-(2 * m)))
    ((summable_jp_rpow (d := d) m hm).mul_left 8) (fun k => ?_) (fun X k => ?_)
  · simp_rw [coord_ofMeasureDiff_empirical hm ν hN]
    refine continuous_const.mul (Continuous.sub (continuous_const.mul ?_) continuous_const)
    exact continuous_finsetSum _ fun i _ => (continuous_realMode' k).comp (continuous_apply i)
  · have := empirical_isProbabilityMeasure (by omega : 0 < N) X
    rw [coord_ofMeasureDiff hm (empirical X) ν, mul_pow, Torus.jp_rpow_sq,
      show 2 * -m = -(2 * m) by ring]
    have h1 := Torus.abs_measureRealCoeff_le (empirical X) k
    have h2 := Torus.abs_measureRealCoeff_le ν k
    simp only [measure_univ, ENNReal.toReal_one, mul_one] at h1 h2
    have h3 : |Torus.measureRealCoeff (empirical X) k - Torus.measureRealCoeff ν k| ≤
        2 * Real.sqrt 2 := by
      calc _ ≤ _ := abs_sub _ _
        _ ≤ Real.sqrt 2 + Real.sqrt 2 := add_le_add h1 h2
        _ = _ := by ring
    have h4 : (Torus.measureRealCoeff (empirical X) k - Torus.measureRealCoeff ν k) ^ 2 ≤ 8 := by
      have := pow_le_pow_left₀ (abs_nonneg _) h3 2
      rw [sq_abs] at this
      calc _ ≤ _ := this
        _ = 8 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
    have hj : 0 ≤ Lattice.jp k.1 ^ (-(2 * m)) := Real.rpow_nonneg (Torus.jp_pos _).le _
    nlinarith

theorem eqlaw_continuous_zetaE {N : ℕ} (hm : (d : ℝ) < 2 * m) (hN : 1 ≤ N) (P : Measure (Config d N))
    [IsProbabilityMeasure P] : Continuous fun X : Config d N => zetaE m P X := by
  have := isProbabilityMeasure_meanEmpirical P hN
  exact (eqlaw_continuous_ofMeasureDiff_empirical hm (meanEmpirical P) hN).const_smul (Real.sqrt N)


open Classical in
/-- The continuous path, or the zero path if `f` is not continuous (the construction of `Main.windowZeta`). -/
def eqlaw_pathOf (d : ℕ) (m T : ℝ) (f : Set.Icc (0 : ℝ) T → NegSobolev d m) : PathSpace d m T :=
  if h : Continuous f then ⟨f, h⟩ else 0

theorem eqlaw_aemeasurable_pathOf {S : Type*} [MeasurableSpace S] (Q : Measure S) (T : ℝ)
    (f : S → Set.Icc (0 : ℝ) T → NegSobolev d m) (hmeas : ∀ t, Measurable fun σ => f σ t)
    (hcont : ∀ᵐ σ ∂Q, Continuous (f σ)) :
    AEMeasurable (fun σ => eqlaw_pathOf d m T (f σ)) Q := by
  classical
  set A : Set S := {σ | ¬ Continuous (f σ)} with hAdef
  have hA : Q A = 0 := ae_iff.1 hcont
  set N : Set S := toMeasurable Q A with hNdef
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : Q N = 0 := by rw [hNdef, measure_toMeasurable]; exact hA
  have hAN : A ⊆ N := subset_toMeasurable _ _
  have hcN : ∀ σ : ↥Nᶜ, Continuous (f σ.1) := fun σ => by
    by_contra h
    exact σ.2 (hAN h)
  let F : ↥Nᶜ → PathSpace d m T := fun σ => ⟨f σ.1, hcN σ⟩
  have hF : Measurable F := by
    have : Measurable fun σ : ↥Nᶜ => (⟨f σ.1, hcN σ⟩ : C(Set.Icc (0 : ℝ) T, NegSobolev d m)) :=
      (ContinuousMap.measurable_iff_eval).2 fun t => (hmeas t).comp measurable_subtype_coe
    exact this
  have hg : Measurable fun σ : S => if hx : σ ∈ Nᶜ then F ⟨σ, hx⟩ else
      (0 : PathSpace d m T) :=
    Measurable.dite (g := fun _ => (0 : PathSpace d m T)) hF measurable_const hNm.compl
  refine hg.aemeasurable.congr ?_
  have hae : ∀ᵐ σ ∂Q, σ ∉ N := by
    rw [ae_iff]; simpa using hN0
  filter_upwards [hae] with σ hσ
  have hσ' : σ ∈ Nᶜ := hσ
  simp only [hσ', dif_pos]
  have hc : Continuous (f σ) := hcN ⟨σ, hσ'⟩
  unfold eqlaw_pathOf
  exact (dif_pos hc).symm

end HRS.MD.EQLawPath
