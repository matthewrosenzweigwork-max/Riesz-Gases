import Mathlib
import HRS.Main.A33Aux16

/-!
# Packet A33, helper 17: the Gaussian law of the noise field `G_t` in `E_J`
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A33

open HRS HRS.PDE HRS.PDE.ET

variable {d : ℕ}

theorem a33_continuous_coord {m : ℝ} (k : NonzeroLattice d) :
    Continuous (fun F : NegSobolev d m => NegSobolev.coord F k) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun F G => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm]
  let F' : lp (fun _ : NonzeroLattice d => ℝ) 2 := F
  let G' : lp (fun _ : NonzeroLattice d => ℝ) 2 := G
  have h := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (F' - G') k
  have h2 : (F' - G' : lp (fun _ : NonzeroLattice d => ℝ) 2) k = F' k - G' k := by
    rw [lp.coeFn_sub]; rfl
  rw [h2, Real.norm_eq_abs] at h
  rw [Real.norm_eq_abs, NNReal.coe_one, one_mul]
  exact h

theorem a33_inner_tendsto {m : ℝ} (e : ℕ ≃ NonzeroLattice d) (a F : NegSobolev d m) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n,
      NegSobolev.coord F (e i) * NegSobolev.coord a (e i)) atTop (𝓝 (inner ℝ a F)) := by
  have h := lp.hasSum_inner (𝕜 := ℝ) (G := fun _ : NonzeroLattice d => ℝ)
    (show lp (fun _ : NonzeroLattice d => ℝ) 2 from a) (show lp (fun _ : NonzeroLattice d => ℝ) 2 from F)
  have h' := (e.hasSum_iff (f := fun k : NonzeroLattice d =>
    inner ℝ ((show lp (fun _ : NonzeroLattice d => ℝ) 2 from a) k)
      ((show lp (fun _ : NonzeroLattice d => ℝ) 2 from F) k))).2 h
  have := h'.tendsto_sum_nat
  refine this.congr fun n => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [RCLike.inner_apply, conj_trivial]
  rfl

section Noise

variable (S : A33Setup d) (q : ℝ) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] (W : Lp (Euc d) 2 (a33_nu d S.T S.ρ) → Ω → ℝ) (hI : A33Iso P W)
  (e : ℕ ≃ NonzeroLattice d)

include hI e in
theorem a33_noise_map_gaussian {t : ℝ} (ht : t ∈ Set.Icc 0 S.T)
    (L : StrongDual ℝ (NegSobolev d (S.J : ℝ))) :
    ∃ v : ℝ≥0, (P.map (a33_Gfield S q W t)).map L = gaussianReal 0 v := by
  classical
  set a : NegSobolev d (S.J : ℝ) := (InnerProductSpace.toDual ℝ (NegSobolev d (S.J : ℝ))).symm L
    with ha
  have hL : ∀ F : NegSobolev d (S.J : ℝ), L F = inner ℝ a F := fun F =>
    (InnerProductSpace.toDual_symm_apply (x := F) (y := L)).symm
  set c : ℕ → ℝ := fun i => NegSobolev.coord a (e i) * Lattice.jp (e i).1 ^ (-(S.J : ℝ)) with hc
  set u : ℕ → Lp (Euc d) 2 (a33_nu d S.T S.ρ) := fun i => a33_vec S q t (Torus.realMode (e i)) with hu
  set w : ℕ → Lp (Euc d) 2 (a33_nu d S.T S.ρ) := fun n => ∑ i ∈ Finset.range n, c i • u i with hw
  have hsum : Summable (fun i => c i • u i) := by
    have h1 : Summable fun i : ℕ => NegSobolev.coord a (e i) ^ 2 :=
      (e.summable_iff (f := fun k : NonzeroLattice d => NegSobolev.coord a k ^ 2)).2
        (NegSobolev.coord_sq a).1
    have h2 : Summable fun i : ℕ => (Lattice.jp (e i).1 ^ (-(S.J : ℝ)) *
        ‖a33_vec S q t (Torus.realMode (e i))‖) ^ 2 :=
      (e.summable_iff (f := fun k : NonzeroLattice d => (Lattice.jp k.1 ^ (-(S.J : ℝ)) *
        ‖a33_vec S q t (Torus.realMode k)‖) ^ 2)).2 (S.trace_summable q ht)
    refine Summable.of_norm_bounded (h1.add h2) fun i => ?_
    have hj : 0 < Lattice.jp (e i).1 ^ (-(S.J : ℝ)) := Real.rpow_pos_of_pos (Torus.jp_pos _) _
    simp only [hc, hu, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hj]
    set x := NegSobolev.coord a (e i)
    set y := Lattice.jp (e i).1 ^ (-(S.J : ℝ)) * ‖a33_vec S q t (Torus.realMode (e i))‖
    have hy : 0 ≤ y := mul_nonneg hj.le (norm_nonneg _)
    have : |x| * Lattice.jp (e i).1 ^ (-(S.J : ℝ)) * ‖a33_vec S q t (Torus.realMode (e i))‖ = |x| * y := by
      simp only [y]; ring
    rw [this]
    nlinarith [sq_nonneg (|x| - y), sq_abs x]
  set w' : Lp (Euc d) 2 (a33_nu d S.T S.ρ) := ∑' i, c i • u i with hw'
  have hwlim : Tendsto w atTop (𝓝 w') := hsum.hasSum.tendsto_sum_nat
  set G := a33_Gfield S q W t with hG
  have hGm : Measurable G := a33_Gfield_meas S q W e hI t
  set V : ℕ → Ω → ℝ := fun n ω => ∑ i ∈ Finset.range n,
    NegSobolev.coord (G ω) (e i) * NegSobolev.coord a (e i) with hV
  have hVm : ∀ n, Measurable (V n) := fun n =>
    Finset.measurable_sum _ fun i _ => ((a33_continuous_coord (e i)).measurable.comp hGm).mul_const _
  have hVlim : ∀ ω, Tendsto (fun n => V n ω) atTop (𝓝 (L (G ω))) := fun ω => by
    rw [hL]; exact a33_inner_tendsto e a (G ω)
  have hgood := a33_ae_summable S q W hI ht
  have hVW : ∀ n, V n =ᵐ[P] W (w n) := by
    intro n
    filter_upwards [hI.fin u c (Finset.range n), hgood] with ω h1 h2
    have hmem : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-(S.J : ℝ)) *
        a33_X S q W t k ω) 2 := (Torus.memℓp_two_iff _).2 h2
    rw [hw]
    simp only
    rw [h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcoord : NegSobolev.coord (G ω) (e i) = Lattice.jp (e i).1 ^ (-(S.J : ℝ)) *
        a33_X S q W t (e i) ω := HRS.Q41.q41_coord_ofSeq (m := (S.J : ℝ)) hmem (e i)
    rw [hcoord, hc]
    simp only [hu, a33_X]
    ring
  have hlawn : ∀ n, P.map (V n) = gaussianReal 0 (Real.toNNReal (‖w n‖ ^ 2)) := fun n => by
    rw [Measure.map_congr (hVW n), hI.single]
  refine ⟨Real.toNNReal (‖w'‖ ^ 2), ?_⟩
  have hLm : Measurable fun ω => L (G ω) := L.continuous.measurable.comp hGm
  rw [Measure.map_map L.continuous.measurable hGm]
  refine Measure.ext_of_charFun ?_
  funext s
  have hfun : (L ∘ G) = fun ω => L (G ω) := rfl
  rw [hfun, a33_charFun_eq _ hLm]
  have h1 : Tendsto (fun n => ∫ ω, Complex.exp (((s * V n ω : ℝ) : ℂ) * Complex.I) ∂P) atTop
      (𝓝 (∫ ω, Complex.exp (((s * L (G ω) : ℝ) : ℂ) * Complex.I) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => 1) (fun n => ?_) (integrable_const _)
      (fun n => ?_) ?_
    · exact (a33_meas_exp _ (hVm n) s).aestronglyMeasurable
    · exact Eventually.of_forall fun ω => (Complex.norm_exp_ofReal_mul_I _).le
    · refine Eventually.of_forall fun ω => ?_
      have hc : Continuous fun x : ℝ => Complex.exp (((s * x : ℝ) : ℂ) * Complex.I) := by fun_prop
      exact (hc.tendsto _).comp (hVlim ω)
  have h2 : ∀ n, ∫ ω, Complex.exp (((s * V n ω : ℝ) : ℂ) * Complex.I) ∂P =
      Complex.exp (-(((‖w n‖ ^ 2 : ℝ) : ℂ) * (s : ℂ) ^ 2 / 2)) := by
    intro n
    rw [← a33_charFun_eq (V n) (hVm n) s, hlawn n, charFun_gaussianReal]
    rw [Real.coe_toNNReal _ (sq_nonneg _)]
    simp
  simp_rw [h2] at h1
  have h3 : Tendsto (fun n => Complex.exp (-(((‖w n‖ ^ 2 : ℝ) : ℂ) * (s : ℂ) ^ 2 / 2))) atTop
      (𝓝 (Complex.exp (-(((‖w'‖ ^ 2 : ℝ) : ℂ) * (s : ℂ) ^ 2 / 2)))) := by
    refine (Complex.continuous_exp.tendsto _).comp ?_
    have := ((Complex.continuous_ofReal.tendsto _).comp ((hwlim.norm).pow 2)).mul_const ((s : ℂ) ^ 2)
    exact (this.div_const 2).neg
  have := tendsto_nhds_unique h1 h3
  rw [this, charFun_gaussianReal, Real.coe_toNNReal _ (sq_nonneg _)]
  simp

end Noise

end HRS.A33
