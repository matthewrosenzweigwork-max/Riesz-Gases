import HRS.MS.QsfIbp5

/-!
# S4.5 packet B2, part 6: the limit `ε → 0` and the Gibbs integration by parts identity

`s45_gibbs_ibp`: for `0 ≤ s`, `a, β > 0`, `N ≥ 1`, `d ≥ 1`, a `C¹` vector field `v` on `ℝ^d` with bounded `v`, `Dv` and
a `C¹` functional `F` on `(ℝ^d)^N` with bounded `F`, `dF`,
`∫ [ (∑_k div v(x_k)) F + dF(v(X)) - β F (∑_i a⟨x_i,v(x_i)⟩ + N⁻¹ ∑_{i<j} ⟨∇g(x_i-x_j), v(x_i)-v(x_j)⟩) ]
   e^{-β H_N(X)} dX = 0`,
with `∇g = rieszKernelGrad d s` and `H_N = canonicalHamiltonian`.  No cutoff at collisions is needed: the
identity is proved for the smoothed kernel and passed to the limit by dominated convergence with the
bounded symmetrised pair term.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc)

variable {d N : ℕ}

theorem s45_continuous_F {s : ℝ} {ε : ℝ} (hε : ε ≠ 0) : Continuous (s45_F (d := d) s ε) := by
  unfold s45_F
  refine Continuous.smul (f := fun z : Euc d => -(movtr_sigma s * (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1)))
    (g := fun z => z) ?_ continuous_id
  refine (continuous_const.mul ?_).neg
  have hb : Continuous fun z : Euc d => ‖z‖ ^ 2 + ε ^ 2 := by fun_prop
  refine hb.rpow_const fun z => Or.inl ?_
  positivity

theorem s45_continuous_div {v : Euc d → Euc d} (hv : ContDiff ℝ 1 v) : Continuous (s45_div v) := by
  unfold s45_div
  refine continuous_finsetSum _ fun a _ => ?_
  exact (EuclideanSpace.proj a : Euc d →L[ℝ] ℝ).continuous.comp
    ((hv.continuous_fderiv one_ne_zero).clm_apply continuous_const)

theorem s45_continuous_I {s a β ε : ℝ} (hε : ε ≠ 0) {v : Euc d → Euc d} (hv : ContDiff ℝ 1 v)
    {F : EucConfig d N → ℝ} (hF : ContDiff ℝ 1 F) : Continuous (s45_I s a β ε v F) := by
  have hw : Continuous (s45_w s a β ε : EucConfig d N → ℝ) :=
    (s45_differentiable_w s a β hε).continuous
  have hFc := hF.continuous
  have hvc := hv.continuous
  have hdiv := s45_continuous_div hv
  have hdF : Continuous fun X : EucConfig d N => fderiv ℝ F X (fun k => v (X k)) :=
    (hF.continuous_fderiv one_ne_zero).clm_apply (continuous_pi fun k => hvc.comp (continuous_apply k))
  have hFe := s45_continuous_F (d := d) (s := s) hε
  unfold s45_I
  refine hw.mul (Continuous.sub ?_ ?_)
  · exact (continuous_finsetSum _ fun k _ => hdiv.comp (continuous_apply k)).mul hFc |>.add hdF
  · refine continuous_const.mul (hFc.mul (Continuous.add ?_ ?_))
    · exact continuous_finsetSum _ fun i _ => continuous_const.mul
        ((continuous_apply i).inner (hvc.comp (continuous_apply i)))
    · refine continuous_const.mul (continuous_finsetSum _ fun i _ =>
        continuous_finsetSum _ fun j _ => ?_)
      exact (hFe.comp ((continuous_apply i).sub (continuous_apply j))).inner
        ((hvc.comp (continuous_apply i)).sub (hvc.comp (continuous_apply j)))

/-- Off the collision set the integrand is continuous in `ε` (for all `ε`). -/
theorem s45_continuous_in_eps {s a β : ℝ} {v : Euc d → Euc d} (hv : ContDiff ℝ 1 v)
    {F : EucConfig d N → ℝ} (X : EucConfig d N) (hX : ∀ i j, i ≠ j → X i ≠ X j) :
    Continuous fun ε : ℝ => s45_I s a β ε v F X := by
  have hg : ∀ i j : Fin N, i ≠ j → Continuous fun ε : ℝ => movtr_gEps d s ε (X i - X j) := by
    intro i j hij
    have hz : X i - X j ≠ 0 := sub_ne_zero.2 (hX i j hij)
    have hz0 : 0 < ‖X i - X j‖ := norm_pos_iff.2 hz
    unfold movtr_gEps
    by_cases hs : s = 0
    · simp only [hs, ite_true]
      have hb : Continuous fun ε : ℝ => ‖X i - X j‖ ^ 2 + ε ^ 2 := by fun_prop
      refine continuous_const.mul (hb.log fun ε => ?_)
      positivity
    · simp only [hs, ite_false]
      have hb : Continuous fun ε : ℝ => ‖X i - X j‖ ^ 2 + ε ^ 2 := by fun_prop
      exact hb.rpow_const fun ε => Or.inl (by positivity)
  have hF' : ∀ i j : Fin N, i ≠ j → Continuous fun ε : ℝ => s45_F s ε (X i - X j) := by
    intro i j hij
    have hz : X i - X j ≠ 0 := sub_ne_zero.2 (hX i j hij)
    have hz0 : 0 < ‖X i - X j‖ := norm_pos_iff.2 hz
    unfold s45_F
    refine Continuous.smul (f := fun ε : ℝ => -(movtr_sigma s * (‖X i - X j‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1)))
      (g := fun _ => X i - X j) ?_ continuous_const
    refine (continuous_const.mul ?_).neg
    have hb : Continuous fun ε : ℝ => ‖X i - X j‖ ^ 2 + ε ^ 2 := by fun_prop
    exact hb.rpow_const fun ε => Or.inl (by positivity)
  unfold s45_I s45_w s45_H
  refine Continuous.mul (Real.continuous_exp.comp (continuous_const.mul
    (continuous_const.add (continuous_const.mul ?_)))) (continuous_const.sub (continuous_const.mul
      (continuous_const.mul (continuous_const.add (continuous_const.mul ?_)))))
  · refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j hj => hg i j ?_
    have : i < j := by simpa using hj
    exact this.ne
  · refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j hj => ?_
    have hij : i < j := by simpa using hj
    exact (hF' i j hij.ne).inner continuous_const

theorem s45_F_zero {s : ℝ} {z : Euc d} (hz : z ≠ 0) : s45_F s 0 z = rieszKernelGrad d s z := by
  rw [movtr_rieszKernelGrad_eq s hz]
  unfold s45_F
  rw [movtr_u0 (s := s) z hz]
  congr 3
  ring_nf

/-- **Gibbs integration by parts.** -/
theorem s45_gibbs_ibp {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (hN : 1 ≤ N) {v : Euc d → Euc d} (hv : ContDiff ℝ 1 v) {Bv Dv : ℝ} (hBv : ∀ x, ‖v x‖ ≤ Bv)
    (hDv : ∀ x, ‖fderiv ℝ v x‖ ≤ Dv) {F : EucConfig d N → ℝ} (hF : ContDiff ℝ 1 F) {BF DF : ℝ}
    (hBF : ∀ X, |F X| ≤ BF) (hDF : ∀ X, ‖fderiv ℝ F X‖ ≤ DF) :
    ∫ X, (((∑ k, s45_div v (X k)) * F X + fderiv ℝ F X (fun k => v (X k))) -
      β * (F X * (∑ i, a * ⟪X i, v (X i)⟫ + (1 / (N : ℝ)) *
        ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
          ⟪rieszKernelGrad d s (X i - X j), v (X i) - v (X j)⟫))) *
      Real.exp (-β * canonicalHamiltonian (rieszKernel d s) (confinement a) X) = 0 := by
  have hvd : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hFd : Differentiable ℝ F := hF.differentiable (by norm_num)
  obtain ⟨K, hK0, hK⟩ := s45_I_le hs0 ha hβ hN hvd hBv hDv hBF hDF
  have hint : Integrable (fun X : EucConfig d N =>
      K * (1 + ‖X‖) * Real.exp (-((β * a / 4) * ‖X‖ ^ 2))) := by
    refine s45_integrable_of_dom (c := β * a / 4) (by positivity) ?_ hK0 fun X => ?_
    · have hm : Continuous fun X : EucConfig d N =>
          K * (1 + ‖X‖) * Real.exp (-((β * a / 4) * ‖X‖ ^ 2)) := by fun_prop
      exact hm.aestronglyMeasurable
    · rw [abs_of_nonneg (by positivity)]
  have hcol : ∀ᵐ X : EucConfig d N ∂volume, ∀ i j, i ≠ j → X i ≠ X j := by
    have h0 := HRS.MP.SelfSimP4Impl.p4g_collision_null hd N
    have := (measure_eq_zero_iff_ae_notMem.1 h0)
    filter_upwards [this] with X hX i j hij hXij
    exact hX ⟨i, j, hij, hXij⟩
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := (volume : Measure (EucConfig d N)))
    (l := 𝓝[>] (0 : ℝ)) (F := fun ε X => s45_I s a β ε v F X) (f := fun X => s45_I s a β 0 v F X)
    (fun X => K * (1 + ‖X‖) * Real.exp (-((β * a / 4) * ‖X‖ ^ 2)))
    (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (s45_continuous_I (ne_of_gt hε) hv hF).aestronglyMeasurable)
    (by
      filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
      exact Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]; exact hK ε hε.1 hε.2 X)
    hint
    (by
      filter_upwards [hcol] with X hX
      exact (s45_continuous_in_eps (s := s) (a := a) (β := β) hv (F := F) X hX).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds)
  have hzero : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∫ X, s45_I s a β ε v F X = 0 := by
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
    exact s45_sum_eps hs0 ha hβ hN hε.1 hε.2 hvd hBv hDv hFd hBF hDF
  have h0 : ∫ X, s45_I s a β 0 v F X = 0 :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hzero.mono fun ε h => h.symm))
  rw [← h0]
  refine integral_congr_ae ?_
  filter_upwards [hcol] with X hX
  have hpair : ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      ⟪s45_F s 0 (X i - X j), v (X i) - v (X j)⟫ =
      ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      ⟪rieszKernelGrad d s (X i - X j), v (X i) - v (X j)⟫ := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
    have hij : i < j := by simpa using hj
    rw [s45_F_zero (sub_ne_zero.2 (hX i j hij.ne))]
  unfold s45_I
  rw [s45_w_zero, hpair, mul_comm]

end S45

end
