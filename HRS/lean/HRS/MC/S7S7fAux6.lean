import HRS.MC.S7S7fAux5
import HRS.Equilibrium.Parametrix.PX1AuxDeriv

/-!
# Packet S7f, helper 6: the limit side of the assembly

With `f = steinSolG G Φ`, `D_{klj} = E D³f(G)[ε_k,ε_l,ε_j]`, `T_{klj} = μ(a_j v_k·∇φ_l)`, `Q_{k;lj} = sed_Qt`,
`κ_{klj} = μ(a_k a_l a_j)`:
`-∑ T D + γ (1/2) ∑ Q D = (1/6) ∫∫ D³Φ(F)[ℓ_x,ℓ_x,ℓ_x] dμ dG`
(`sed_B9cancel`, symmetry of `D³f`, `stein_third_derivative`, `S7e`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7f

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux HRS.MC.Sec7.S7d HRS.MC.Sec7.S7c HRS.MC.Sec7.S7e

variable {d : ℕ} {s : ℝ} {r : ℝ}

theorem s7f_D3_swap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf : ContDiff ℝ 3 f) (z x y w : E) :
    iteratedFDeriv ℝ 3 f z ![x, w, y] = iteratedFDeriv ℝ 3 f z ![x, y, w] := by
  have h := HRS.Parx.iteratedFDeriv_perm (n := 3) (x := z) hf.contDiffAt (Equiv.swap 1 2) ![x, y, w]
  have e : (![x, y, w] ∘ (Equiv.swap (1 : Fin 3) 2)) = ![x, w, y] := by
    funext i; fin_cases i <;> rfl
  rw [e] at h
  exact h

theorem s7f_limit_identity (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hr : r = 2 * (d : ℝ) + 6)
    {γ : ℝ} (hγ : 0 ≤ γ) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
    {a : NonzeroLattice d → Torus d → ℝ} {v : NonzeroLattice d → Fin d → Torus d → ℝ} {C₀ : ℝ}
    (hmode : s7_ModeData d s γ ρ r a v C₀)
    (G : Measure (NegSobolev d r)) [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianWithCov r G fun φ ψ =>
      ∫ x, φ x * responseRep (periodicRiesz d s) (withDensityReal ρ) γ ψ x ∂(withDensityReal ρ))
    {Φ : NegSobolev d r → ℝ} (hΦ : Φ ∈ CbUnitBall (NegSobolev d r) 5) :
    -(∑' k : NonzeroLattice d, ∑' l : NonzeroLattice d, ∑' j : NonzeroLattice d,
          (∫ x, a j x * sed_drift (v k) (s7_phi r l) x ∂(withDensityReal ρ)) *
            ∫ F, iteratedFDeriv ℝ 3 (steinSolG G Φ) F ![s7_eps r k, s7_eps r l, s7_eps r j] ∂G) +
      γ * ((1 / 2) * ∑' k : NonzeroLattice d, ∑' l : NonzeroLattice d, ∑' j : NonzeroLattice d,
          sed_Qt d s ρ (v k) (a l) (a j) *
            ∫ F, iteratedFDeriv ℝ 3 (steinSolG G Φ) F ![s7_eps r l, s7_eps r j, s7_eps r k] ∂G) =
      (1 / 6) * ∫ F, ∫ x, iteratedFDeriv ℝ 3 Φ F
            ![ellPt (periodicRiesz d s) (withDensityReal ρ) γ r x,
              ellPt (periodicRiesz d s) (withDensityReal ρ) γ r x,
              ellPt (periodicRiesz d s) (withDensityReal ρ) γ r x] ∂(withDensityReal ρ) ∂G := by
  classical
  haveI hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  have hmem : MemCb 5 Φ := ⟨hΦ.1, hΦ.2.1⟩
  have hcl : s7d_Cl (steinSolG G Φ) := s7d_stein_cl G hG.1 hΦ
  have hb := s7d_b_summable (d := d)
  have hb0 := s7f_b_nonneg (d := d)
  haveI : IsGaussian G := hG.1.1
  have hγ1 : Integrable (fun y : NegSobolev d r => ‖y‖) G := (IsGaussian.integrable_id (μ := G)).norm
  obtain ⟨C₀', Cd, hC0, hCd, ha, hdr, hlip⟩ := s7d_mode_bounds hr hmode
  obtain ⟨Gq, hGq0, hGq⟩ := s7d_Qt_bound hd hs0 hs hρ
  have hcont_a : ∀ k, Continuous (a k) := fun k => HRS.Q66.q66_cont_of_smooth (hmode.smooth_a k)
  have hmeas_a : ∀ k, Measurable (a k) := fun k => (hcont_a k).measurable
  have hbpos := s7d_b_pos (d := d)
  -- the abstract families
  set T : NonzeroLattice d → NonzeroLattice d → NonzeroLattice d → ℝ := fun k l j =>
    ∫ x, a j x * sed_drift (v k) (s7_phi r l) x ∂(withDensityReal ρ) with hTdef
  set Q : NonzeroLattice d → NonzeroLattice d → NonzeroLattice d → ℝ := fun k l j =>
    sed_Qt d s ρ (v k) (a l) (a j) with hQdef
  set κ : NonzeroLattice d → NonzeroLattice d → NonzeroLattice d → ℝ := fun k l j =>
    ∫ x, a k x * a l x * a j x ∂(withDensityReal ρ) with hκdef
  set D : NonzeroLattice d → NonzeroLattice d → NonzeroLattice d → ℝ := fun k l j =>
    ∫ F, iteratedFDeriv ℝ 3 (steinSolG G Φ) F ![s7_eps r k, s7_eps r l, s7_eps r j] ∂G with hDdef
  have hD3b : ∀ (k l j : NonzeroLattice d) F,
      |iteratedFDeriv ℝ 3 (steinSolG G Φ) F ![s7_eps r k, s7_eps r l, s7_eps r j]| ≤ 1 := by
    intro k l j F
    have := s7d_D3_bound (hcl.2 3 (by norm_num) (by norm_num) F) (s7_eps r k) (s7_eps r l) (s7_eps r j)
    rwa [s7e_eps_norm, s7e_eps_norm, s7e_eps_norm, mul_one, mul_one] at this
  have hT : ∀ k l j, |T k l j| ≤ (C₀' * Cd) * s7_b k * s7_b l * s7_b j := by
    intro k l j
    refine (s7f_abs_integral_le _ (C := (C₀' * s7_b j) * (Cd * (s7_b k * s7_b l))) (fun x => ?_)).trans
      (le_of_eq (by ring))
    rw [abs_mul]
    exact mul_le_mul (ha j x) (hdr k l x) (abs_nonneg _) (mul_nonneg hC0.le (hb0 j))
  have hQ : ∀ k l j, |Q k l j| ≤ (C₀' ^ 3 * (1 + Gq) * d / 2) * s7_b k * s7_b l * s7_b j := by
    intro k l j
    have hLpos : 0 < C₀' * s7_b k := mul_pos hC0 (hbpos k)
    have := hGq (v k) hLpos (hlip k) (fun i => hmode.smooth_v k i) (f := a l) (g := a j)
      (hcont_a l) (hcont_a j) (ha l) (ha j)
    refine this.trans (le_of_eq ?_)
    ring
  have hκ : ∀ k l j, |κ k l j| ≤ (C₀' ^ 3) * s7_b k * s7_b l * s7_b j := by
    intro k l j
    refine (s7f_abs_integral_le _ (C := (C₀' * s7_b k) * (C₀' * s7_b l) * (C₀' * s7_b j))
      (fun x => ?_)).trans (le_of_eq (by ring))
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (ha k x) (ha l x) (abs_nonneg _) (mul_nonneg hC0.le (hb0 k))) (ha j x)
      (abs_nonneg _) (mul_nonneg (mul_nonneg hC0.le (hb0 k)) (mul_nonneg hC0.le (hb0 l)))
  have hD : ∀ k l j, |D k l j| ≤ 1 := fun k l j => s7f_abs_integral_le _ (hD3b k l j)
  have hf3 : ContDiff ℝ 3 (steinSolG G Φ) := hcl.1.of_le (by norm_num)
  have hsw : ∀ k l j, D k j l = D k l j := fun k l j =>
    integral_congr_ae (Eventually.of_forall fun F => s7f_D3_swap hf3 F _ _ _)
  have hcyc : ∀ k l j, D l j k = D k l j := fun k l j =>
    integral_congr_ae (Eventually.of_forall fun F => (s7d_D3_cyc hf3 F _ _ _).symm)
  have hB9 : ∀ k l j, T k l j + T k j l - γ * Q k l j = κ k l j := by
    intro k l j
    have h := HRS.MC.SEdge.B9cancel.sed_B9cancel_proof hd hs0 hs hγ hρ (hmode.smooth_a k)
      (hmode.smooth_a l) (hmode.smooth_a j) (HRS.MC.Sec7.S7a.s7a_phi_smooth r l)
      (HRS.MC.Sec7.S7a.s7a_phi_smooth r j) (hmode.smooth_v k) (hmode.div k) (hmode.resp l)
      (hmode.resp j)
    have e1 : T k l j = ∫ x, sed_drift (v k) (s7_phi r l) x * a j x ∂(withDensityReal ρ) :=
      integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
    have e2 : T k j l = ∫ x, sed_drift (v k) (s7_phi r j) x * a l x ∂(withDensityReal ρ) :=
      integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
    rw [e1, e2]
    exact h
  have key := s7f_cancel_alg hb hb0 γ hT hQ hκ hD hB9 hsw hcyc
  -- the third-derivative identity and `S7e`
  have hthird : ∀ k l j, D k l j = -(1 / 3) * ∫ F, iteratedFDeriv ℝ 3 Φ F
      ![s7_eps r k, s7_eps r l, s7_eps r j] ∂G := fun k l j =>
    HRS.third_core hG.1 hmem hγ1 _
  have h1 : ∑' k, ∑' l, ∑' j, κ k l j * D k l j =
      -(1 / 3) * ∑' k, ∑' l, ∑' j, κ k l j * ∫ F, iteratedFDeriv ℝ 3 Φ F
        ![s7_eps r k, s7_eps r l, s7_eps r j] ∂G := by
    simp_rw [hthird, ← tsum_mul_left]
    refine tsum_congr fun k => tsum_congr fun l => tsum_congr fun j => ?_
    ring
  have hD3Φ : ∀ (k l j : NonzeroLattice d) F,
      |iteratedFDeriv ℝ 3 Φ F ![s7_eps r k, s7_eps r l, s7_eps r j]| ≤ 1 := by
    intro k l j F
    have h4 : ‖iteratedFDeriv ℝ 3 Φ F‖ ≤ 1 := by
      have := Tilt715Aux.norm_iter_le_cbNorm hmem (j := 3) (by norm_num) F
      exact this.trans (by simpa using hΦ.2.2)
    have := s7d_D3_bound h4 (s7_eps r k) (s7_eps r l) (s7_eps r j)
    rwa [s7e_eps_norm, s7e_eps_norm, s7e_eps_norm, mul_one, mul_one] at this
  have h2 : ∑' k, ∑' l, ∑' j, κ k l j * ∫ F, iteratedFDeriv ℝ 3 Φ F
        ![s7_eps r k, s7_eps r l, s7_eps r j] ∂G =
      ∫ F, ∫ x, iteratedFDeriv ℝ 3 Φ F
            ![ellPt (periodicRiesz d s) (withDensityReal ρ) γ r x,
              ellPt (periodicRiesz d s) (withDensityReal ρ) γ r x,
              ellPt (periodicRiesz d s) (withDensityReal ρ) γ r x] ∂(withDensityReal ρ) ∂G := by
    have hint3 : ∀ k l j, Integrable (fun F => κ k l j * iteratedFDeriv ℝ 3 Φ F
        ![s7_eps r k, s7_eps r l, s7_eps r j]) G := by
      intro k l j
      refine Integrable.of_bound ?_ (|κ k l j|) (Eventually.of_forall fun F => ?_)
      · exact (continuous_const.mul ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 3 =>
          NegSobolev d r) ℝ ![s7_eps r k, s7_eps r l, s7_eps r j]).continuous.comp
          (hmem.1.continuous_iteratedFDeriv (m := 3) (by norm_num)))).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul]
        calc |κ k l j| * |iteratedFDeriv ℝ 3 Φ F ![s7_eps r k, s7_eps r l, s7_eps r j]| ≤
              |κ k l j| * 1 := mul_le_mul_of_nonneg_left (hD3Φ k l j F) (abs_nonneg _)
          _ = _ := mul_one _
    have := s7e_integral_triple G hb hb0 (C₀' ^ 3) (fun k l j F => κ k l j *
        iteratedFDeriv ℝ 3 Φ F ![s7_eps r k, s7_eps r l, s7_eps r j]) hint3
      (fun k l j F => by
        rw [abs_mul]
        calc |κ k l j| * |iteratedFDeriv ℝ 3 Φ F ![s7_eps r k, s7_eps r l, s7_eps r j]| ≤
              ((C₀' ^ 3) * s7_b k * s7_b l * s7_b j) * 1 :=
              mul_le_mul (hκ k l j) (hD3Φ k l j F) (abs_nonneg _)
                (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hC0.le 3) (hb0 k)) (hb0 l)) (hb0 j))
          _ = _ := mul_one _)
    simp_rw [integral_const_mul] at this
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun F => ?_)
    exact s7_S7e_pairing_identification_proof hd hs0 hs r hr hγ hρ hmode (iteratedFDeriv ℝ 3 Φ F)
  rw [h1, h2] at key
  calc _ = _ := key
    _ = _ := by ring

end HRS.MC.Sec7.S7f

end
