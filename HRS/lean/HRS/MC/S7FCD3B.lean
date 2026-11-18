import HRS.MC.SEdgeS16aAux1
import HRS.MC.SEdgeB10b
import HRS.MC.SEdgeB3
import HRS.MC.S7S7a
import HRS.MC.S7S7bAux13
import HRS.MC.S7S7cAux1
import HRS.MC.S7S7cAux7
import HRS.MC.S7S7dAux3
import HRS.MC.S7FCD3BLaw

/-!
# FC-D3 (L5): finite-dimensional convergence and weak convergence of `ζ_N` (centred at the actual mean)

Generalisation of packet S16a (`sed_S16a_field_clt_proof`, Haar background) to a general smooth positive
background `ρ`, temperature `γ ≥ 0`, `s < d/2`, `r = 2d+6`:

* `d3_proj_zeta`: the coordinate projection of `zetaE r P X` on a finite frequency set `S` is the
  reconstruction `s16a_Phi r S` of the exactly centred statistic `centeredStat P (s16a_phi S) X`;
* `d3_law_G`: the finite-dimensional marginals of `G` are `multivariateGaussian 0 (sed_Cmat ...)`
  (`FCD3BLaw.lean`);
* `d3_zeta_weak`: weak convergence of `law ζ_N` (`N ↦ Q_{N+1}`) to `G` via the abstract criterion
  `s16a_weak_conv`, with tails from `s7b_Y_moment` (`q = 1`) and finite-dimensional convergence from
  `sed_B10b_clt_proof`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.FCD3B

open HRS HRS.Sec7 HRS.MC.SEdge HRS.MC.SEdge.S16a

variable {d : ℕ} {s : ℝ}

/-- The coordinates of `ζ` on the frequencies of `S`, against the centred statistic. -/
theorem d3b_coord_zeta_phi {N : ℕ} (hN : 1 ≤ N) {r : ℝ} (hr : (d : ℝ) < 2 * r)
    (P : Measure (Config d N)) [IsProbabilityMeasure P] (X : Config d N)
    (S : Finset (NonzeroLattice d)) (a : Fin S.card) :
    NegSobolev.coord (zetaE r P X) (s16a_e S a) =
      Lattice.jp (s16a_e S a).1 ^ (-r) * centeredStat P (s16a_phi S) X a := by
  rw [HRS.MC.Sec7.S7c.s7c_coord_zeta hN hr P X (s16a_e S a)]
  unfold sed_Y centeredStat
  simp only [PiLp.toLp_apply]
  have h1 : ∀ Z : Config d N, pair (empirical Z) (s7_phi r (s16a_e S a)) =
      Lattice.jp (s16a_e S a).1 ^ (-r) * pair (empirical Z) (s16a_phi S a) := by
    intro Z
    simp only [pair, s7_phi, s16a_phi, integral_const_mul]
  simp only [h1, integral_const_mul]
  ring

/-- **Projection of `ζ`**: the finite-dimensional coordinates are the reconstruction of the centred statistic. -/
theorem d3_proj_zeta {N : ℕ} (hN : 1 ≤ N) {r : ℝ} (hr : (d : ℝ) < 2 * r)
    (P : Measure (Config d N)) [IsProbabilityMeasure P] (S : Finset (NonzeroLattice d))
    (X : Config d N) :
    s16a_proj S (zetaE r P X) = s16a_Phi r S (centeredStat P (s16a_phi S) X) := by
  classical
  unfold s16a_proj s16a_Phi
  rw [s16a_sum_eq]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [d3b_coord_zeta_phi hN hr P X S a]

/-- Pointwise tail bound for one coordinate of `ζ_N`, uniform in `N ≥ 1`. -/
theorem d3b_coord_tail {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ}
    (hγ : 0 ≤ γ) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {r : ℝ} (hr : (d : ℝ) < 2 * r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ k : NonzeroLattice d,
      ∫⁻ X, ENNReal.ofReal (NegSobolev.coord (zetaE r (sed_Q d s N γ ρ) X) k ^ 2)
        ∂(sed_Q d s N γ ρ) ≤ ENNReal.ofReal (2 * C * Lattice.jp k.1 ^ (-(2 * r))) := by
  obtain ⟨C, hC0, hC⟩ := HRS.MC.Sec7.S7b.s7b_Y_moment hd hs0 hs hγ hρ 1
  refine ⟨C, hC0, fun N hN k => ?_⟩
  haveI hQ : IsProbabilityMeasure (sed_Q d s N γ ρ) :=
    HRS.MC.SEdge.B5a.b5a_Q_prob hd hs0 hs hγ hρ hN
  set w : Torus d → ℝ := s7_phi r k with hw
  have hwc : Continuous w := HRS.Q66.q66_cont_of_smooth (HRS.MC.Sec7.S7a.s7a_phi_smooth r k)
  have hjp : 0 ≤ Lattice.jp k.1 ^ (-r) := Real.rpow_nonneg (Torus.jp_pos _).le _
  have hT : ∀ x, |w x| ≤ Lattice.jp k.1 ^ (-r) * Real.sqrt 2 := by
    intro x
    show |Lattice.jp k.1 ^ (-r) * Torus.realMode k x| ≤ _
    rw [abs_mul, abs_of_nonneg hjp]
    exact mul_le_mul_of_nonneg_left (Torus.abs_realMode_le k x) hjp
  have hmoment := hC w _ (HRS.MC.Sec7.S7a.s7a_phi_smooth r k) hT N hN
  have hpow : (Lattice.jp k.1 ^ (-r)) ^ 2 = Lattice.jp k.1 ^ (-(2 * r)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Torus.jp_pos _).le]
    congr 1
    push_cast
    ring
  have hint : Integrable (fun X => sed_Y (sed_Q d s N γ ρ) w X ^ 2) (sed_Q d s N γ ρ) := by
    have hm : Measurable (sed_Y (sed_Q d s N γ ρ) w) :=
      HRS.MC.Sec7.S7c.s7c_sedY_meas hN (sed_Q d s N γ ρ) hwc
    refine Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable
      ((Real.sqrt N * (2 * (Lattice.jp k.1 ^ (-r) * Real.sqrt 2))) ^ 2)
      (Filter.Eventually.of_forall fun X => ?_)
    have hb := HRS.MC.Sec7.S7d.s7d_sedY_bdd hN (sed_Q d s N γ ρ) hT X
    have h0 := abs_nonneg (sed_Y (sed_Q d s N γ ρ) w X)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc sed_Y (sed_Q d s N γ ρ) w X ^ 2 = |sed_Y (sed_Q d s N γ ρ) w X| ^ 2 := (sq_abs _).symm
      _ ≤ _ := pow_le_pow_left₀ h0 hb 2
  have hsq : ∫ X, sed_Y (sed_Q d s N γ ρ) w X ^ 2 ∂(sed_Q d s N γ ρ) ≤
      C * (Lattice.jp k.1 ^ (-r) * Real.sqrt 2) ^ (2 * 1) := by
    have := hmoment
    simpa [sq_abs] using this
  have hfin : C * (Lattice.jp k.1 ^ (-r) * Real.sqrt 2) ^ (2 * 1) =
      2 * C * Lattice.jp k.1 ^ (-(2 * r)) := by
    rw [show (2 * 1 : ℕ) = 2 from rfl, mul_pow, Real.sq_sqrt (by norm_num), hpow]
    ring
  have hcoord : ∀ X : Config d N,
      ENNReal.ofReal (NegSobolev.coord (zetaE r (sed_Q d s N γ ρ) X) k ^ 2) =
        ENNReal.ofReal (sed_Y (sed_Q d s N γ ρ) w X ^ 2) := by
    intro X
    rw [HRS.MC.Sec7.S7c.s7c_coord_zeta hN hr (sed_Q d s N γ ρ) X k]
  simp_rw [hcoord]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun X => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (hsq.trans_eq hfin)

/-- Uniform summable tail weights for the coordinates of `ζ_N`. -/
theorem d3b_weight_summable {d : ℕ} {r : ℝ} (hr : (d : ℝ) < 2 * r) (C : ℝ) :
    Summable (fun k : NonzeroLattice d => 2 * C * Lattice.jp k.1 ^ (-(2 * r))) :=
  (HRS.MC.Sec7.S7c.s7c_summable_jp (d := d) (r := 2 * r) hr).mul_left (2 * C)

/-- **Weak convergence of `law ζ_N` to `G`** (general smooth positive background, `ζ` centred at the actual
mean). -/
theorem d3_zeta_weak {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ}
    (hγ : 0 ≤ γ) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {r : ℝ} (hr : r = 2 * (d : ℝ) + 6)
    (G : Measure (NegSobolev d r)) [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianWithCov r G fun φ ψ =>
      ∫ x, φ x * responseRep (periodicRiesz d s) (withDensityReal ρ) γ ψ x ∂(withDensityReal ρ)) :
    ∀ F : NegSobolev d r → ℝ, Continuous F → (∃ M, ∀ x, |F x| ≤ M) →
      Tendsto (fun N : ℕ => ∫ X, F (zetaE r (sed_Q d s (N + 1) γ ρ) X)
        ∂(sed_Q d s (N + 1) γ ρ)) atTop (𝓝 (∫ y, F y ∂G)) := by
  have hrd : (d : ℝ) < 2 * r := by
    rw [hr]
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hQp : ∀ n : ℕ, IsProbabilityMeasure (sed_Q d s (n + 1) γ ρ) := fun n =>
    HRS.MC.SEdge.B5a.b5a_Q_prob hd hs0 hs hγ hρ (by omega)
  have hzm : ∀ n : ℕ, Measurable (zetaE r (sed_Q d s (n + 1) γ ρ)) := fun n =>
    HRS.MC.Sec7.S7c.s7c_zeta_meas (by omega) hrd (sed_Q d s (n + 1) γ ρ)
  let ν : ℕ → Measure (NegSobolev d r) := fun n =>
    (sed_Q d s (n + 1) γ ρ).map (zetaE r (sed_Q d s (n + 1) γ ρ))
  have hνp : ∀ n, IsProbabilityMeasure (ν n) := fun n =>
    (Measure.isProbabilityMeasure_map_iff (hzm n).aemeasurable).2 (hQp n)
  haveI := hνp
  obtain ⟨C, hC0, hC⟩ := d3b_coord_tail hd hs0 hs hγ hρ hrd
  have hws := d3b_weight_summable (d := d) hrd C
  have hw0 : ∀ k : NonzeroLattice d, 0 ≤ 2 * C * Lattice.jp k.1 ^ (-(2 * r)) := fun k =>
    mul_nonneg (mul_nonneg (by norm_num) hC0) (Real.rpow_nonneg (Torus.jp_pos _).le _)
  have hcont_coord : ∀ k : NonzeroLattice d,
      Measurable (fun y : NegSobolev d r => ENNReal.ofReal (NegSobolev.coord y k ^ 2)) := fun k =>
    Measurable.ennreal_ofReal ((s16a_continuous_coord k).pow 2).measurable
  have hν_tail : ∀ n k, ∫⁻ y, ENNReal.ofReal (NegSobolev.coord y k ^ 2) ∂(ν n) ≤
      ENNReal.ofReal (2 * C * Lattice.jp k.1 ^ (-(2 * r))) := by
    intro n k
    show ∫⁻ y, ENNReal.ofReal (NegSobolev.coord y k ^ 2)
      ∂((sed_Q d s (n + 1) γ ρ).map _) ≤ _
    rw [lintegral_map (hcont_coord k) (hzm n)]
    exact hC (n + 1) (by omega) k
  have hfdd : S16aFdd ν G := by
    intro S F' hF'c hF'b
    set Ψ : EuclideanSpace ℝ (Fin S.card) → ℝ := fun z => F' (s16a_Phi r S z) with hΨ
    have hΨc : Continuous Ψ := hF'c.comp (s16a_continuous_Phi r S)
    have hΨb : ∃ M, ∀ z, |Ψ z| ≤ M := by
      obtain ⟨M, hM⟩ := hF'b
      exact ⟨M, fun z => hM _⟩
    have hB := HRS.MC.SEdge.B10b.sed_B10b_clt_proof hd hs0 hs hγ hρ
      (φ := s16a_phi S) (fun a => s16a_phi_smooth S a) hΨc hΨb
    have hB' : Tendsto (fun n : ℕ => ∫ X, Ψ (centeredStat (sed_Q d s (n + 1) γ ρ) (s16a_phi S) X)
        ∂(sed_Q d s (n + 1) γ ρ)) atTop
        (𝓝 (∫ z, Ψ z ∂multivariateGaussian 0 (sed_Cmat d s γ ρ (s16a_phi S)))) :=
      hB.comp (tendsto_add_atTop_nat 1)
    have hlimeq : ∫ y, F' (s16a_proj S y) ∂G =
        ∫ z, Ψ z ∂multivariateGaussian 0 (sed_Cmat d s γ ρ (s16a_phi S)) := by
      rw [← d3b_law_G hd hs0 hs hγ hρ G hG S,
        integral_map (s16a_Wmap r S).continuous.measurable.aemeasurable hΨc.aestronglyMeasurable]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [hΨ, s16a_proj_eq_Phi]
    rw [hlimeq]
    refine hB'.congr fun n => ?_
    show _ = ∫ y, F' (s16a_proj S y) ∂((sed_Q d s (n + 1) γ ρ).map (zetaE r (sed_Q d s (n + 1) γ ρ)))
    rw [integral_map (f := fun y => F' (s16a_proj S y)) (hzm n).aemeasurable
      (hF'c.comp (s16a_continuous_proj S)).aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp only [hΨ]
    rw [d3_proj_zeta (by omega) hrd (sed_Q d s (n + 1) γ ρ) S X]
  intro F hFc hFb
  have hmain := s16a_weak_conv ν G hws hw0 hν_tail hfdd F hFc hFb
  refine hmain.congr fun n => ?_
  show ∫ y, F y ∂((sed_Q d s (n + 1) γ ρ).map (zetaE r (sed_Q d s (n + 1) γ ρ))) = _
  exact integral_map (hzm n).aemeasurable hFc.aestronglyMeasurable

end HRS.MC.Sec7.FCD3B

end
