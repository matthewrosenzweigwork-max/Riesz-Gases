import HRS.MC.S7FCH3E
import HRS.MC.S7FCW2

/-!
# S7FCH3F: the coordinate moments of `B - G` and the choice of `(S₀, L₀)` (H3, part F)

* `S7FCH3_coord_moment`: for `t ≥ 0` at which `B t` is the Wick quadratic field, the `L^p(Ω)` moment of the `k`-th Fourier
  coordinate of `B t - fcGaussAt t` (with the continuous version `η'`);
* `S7FCH3_choose`: the real-variable choice of `S₀` and `L₀`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCH3

open HRS HRS.Sec7 HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.S7FCW9 HRS.MC.SEdge

variable {d : ℕ}

theorem S7FCH3_memℓp_fin (r : ℝ) (S : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ)
    (hc : ∀ k, k ∉ S → c k = 0) : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-r) * c k) 2 := by
  rw [Torus.memℓp_two_iff]
  exact summable_of_ne_finset_zero (s := S) fun k hk => by simp [hc k hk]

theorem S7FCH3_fc_sub {r : ℝ} (F G : NegSobolev d r) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (F - G) k = NegSobolev.fourierCoeff F k - NegSobolev.fourierCoeff G k := by
  unfold NegSobolev.fourierCoeff NegSobolev.coord
  rw [← mul_sub]
  congr 1

theorem S7FCH3_fc_gauss {r : ℝ} (S : Finset (NonzeroLattice d)) (Kf : NonzeroLattice d → FRKernel d)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (η : ℝ → Ω → NegSobolev d r) (t : ℝ) (ω : Ω)
    (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (fcGaussAt r S Kf P η t ω) k =
      if k ∈ S then (Kf k).quad (η t ω) - ∫ ω', (Kf k).quad (η t ω') ∂P else 0 := by
  classical
  unfold fcGaussAt
  rw [S7FCW9_fourierCoeff_ofSeq _ (S7FCH3_memℓp_fin r S _ (fun k hk => by simp [hk]))]

/-- The `L^p` moment of the `k`-th coordinate of `B t - G t` at a good time `t`. -/
theorem S7FCH3_coord_moment (R : Regime d) (r : ℝ) {Ω' : Type} [MeasurableSpace Ω']
    (P' : Measure Ω') [IsProbabilityMeasure P'] (η η' : ℝ → Ω' → NegSobolev d r)
    (hηm : ∀ t, Measurable (η t)) (K0 : ℝ) (hK0 : 0 ≤ K0)
    (hC1 : ∀ t : ℝ, 0 ≤ t → HasFiniteGaussianCoeffs P' (η t) ∧ ModeCovBound P' (η t) K0)
    (hη'ae : ∀ t : ℝ, 0 ≤ t → η' t =ᵐ[P'] η t)
    (B : ℝ → Ω' → NegSobolev d r) (hBm : Measurable (Function.uncurry B))
    (p Cp Cq M₀ : ℝ) (hp : 2 ≤ p) (hCp : 0 ≤ Cp)
    (hchaos : ∀ t : ℝ, 0 ≤ t → ∀ (μ : Measure (Torus d)) (h : Torus d → Torus d → ℝ) (Q : Ω' → ℝ),
      IsHalfWick P' (η t) μ h Q → AEStronglyMeasurable Q P' →
      (Summable fun q : NonzeroLattice d × NonzeroLattice d => wickCoeff μ h q.1 q.2 ^ 2) →
      eLpNorm (fun ω => Q ω - wickSection P' (η t) μ h ∅ ω) (ENNReal.ofReal p) P' ≤
        ENNReal.ofReal (Cp * K0 * Real.sqrt (tailHS (wickCoeff μ h) ∅)))
    (hCq : ∀ t : ℝ, 0 ≤ t → ∀ k : NonzeroLattice d,
      (Summable fun q : NonzeroLattice d × NonzeroLattice d =>
        wickCoeff (withDensityReal (R.ρ t)) (hTransport d R.D.s (Torus.realMode k)) q.1 q.2 ^ 2) ∧
      tailHS (wickCoeff (withDensityReal (R.ρ t)) (hTransport d R.D.s (Torus.realMode k))) ∅ ≤
        Cq * Lattice.jp k.1 ^ ((d : ℝ) + 3))
    (hdens : ∀ t : ℝ, 0 ≤ t → IsProbDensity (R.ρ t)) (hM : ∀ t : ℝ, 0 ≤ t → ∀ x, R.ρ t x ≤ M₀)
    (S : Finset (NonzeroLattice d)) (Kf : NonzeroLattice d → FRKernel d) (t : ℝ) (ht : 0 ≤ t)
    (hW : IsWickQuadraticField R.D.s P' (fun ω => η t ω) (withDensityReal (R.ρ t)) (B t))
    (k : NonzeroLattice d) :
    ∫⁻ ω, ENNReal.ofReal (|NegSobolev.fourierCoeff (B t ω - fcGaussAt r S Kf P' η' t ω) k| ^ p) ∂P' ≤
      ENNReal.ofReal ((Cp * K0) ^ p *
        (if k ∈ S then (∫ z : Torus d × Torus d,
            (hTransport d R.D.s (Torus.realMode k) z.1 z.2 - (Kf k).toFun z.1 z.2) ^ 2
              ∂((volume : Measure (Torus d)).prod volume)) ^ (p / 2)
         else (Cq * Lattice.jp k.1 ^ ((d : ℝ) + 3)) ^ (p / 2))) := by
  classical
  have hs0 := R.D.hs0
  have hs := R.hs
  have hd2 := R.hd
  haveI : IsProbabilityMeasure (withDensityReal (R.ρ t)) := isProb_withDensityReal (hdens t ht)
  obtain ⟨hG, hMC⟩ := hC1 t ht
  have hQ : IsHalfWick P' (η t) (withDensityReal (R.ρ t)) (hTransport d R.D.s (Torus.realMode k))
      (fun ω => NegSobolev.eval (B t ω) (Torus.realMode k)) := hW k
  have hQe : (fun ω => NegSobolev.eval (B t ω) (Torus.realMode k)) =
      fun ω => NegSobolev.fourierCoeff (B t ω) k := funext fun ω => S7FCW9_eval_realMode _ k
  have hQe' : ∀ ω, NegSobolev.eval (B t ω) (Torus.realMode k) = NegSobolev.fourierCoeff (B t ω) k :=
    fun ω => S7FCW9_eval_realMode _ k
  have hQm : Measurable (fun ω => NegSobolev.eval (B t ω) (Torus.realMode k)) := by
    rw [hQe]
    exact (HRS.FieldSingAux.measurable_fourierCoeff k).comp (hBm.comp (measurable_const.prodMk measurable_id))
  -- replace `η'` by `η` at the fixed time `t`
  have hint : ∀ k, ∫ ω', (Kf k).quad (η' t ω') ∂P' = ∫ ω', (Kf k).quad (η t ω') ∂P' := by
    intro k
    refine integral_congr_ae ?_
    filter_upwards [hη'ae t ht] with ω hω
    rw [hω]
  have hcoord : ∀ᵐ ω ∂P', NegSobolev.fourierCoeff (B t ω - fcGaussAt r S Kf P' η' t ω) k =
      NegSobolev.fourierCoeff (B t ω) k -
        (if k ∈ S then (Kf k).quad (η t ω) - ∫ ω', (Kf k).quad (η t ω') ∂P' else 0) := by
    filter_upwards [hη'ae t ht] with ω hω
    rw [S7FCH3_fc_sub, S7FCH3_fc_gauss, hω, hint]
  by_cases hk : k ∈ S
  · rw [if_pos hk]
    have hΦm : Measurable (fun ω => (Kf k).quad (η t ω) - ∫ ω', (Kf k).quad (η t ω') ∂P') :=
      ((S7FCH3_quad_cont (Kf k)).measurable.comp (hηm t)).sub measurable_const
    have H1 := HRS.MC.Sec7.S7FCH1.s7_FC_H1b_gauss_proof P' r (η t) K0 hG hMC (withDensityReal (R.ρ t)) (Kf k)
    have Hsub := S7FCH3_isHalfWick_sub (hηm t) hQm hΦm hQ H1
      (h'' := fun x y => hTransport d R.D.s (Torus.realMode k) x y - (Kf k).toFun x y)
      (fun a b => S7FCH3_diff_wick hs0 hs hd2 (hM t ht) k (Kf k) a b)
    obtain ⟨hsum, htail⟩ := S7FCH3_diff_hs hs0 hs hd2 (hM t ht) k (Kf k)
    have hmeas : AEStronglyMeasurable (fun ω => (fun ω => NegSobolev.eval (B t ω) (Torus.realMode k)) ω -
        (fun ω => (Kf k).quad (η t ω) - ∫ ω', (Kf k).quad (η t ω') ∂P') ω) P' :=
      (hQm.sub hΦm).aestronglyMeasurable
    have hm := S7FCH3_moment_gen P' (η t) K0 hK0 p Cp hp hCp (hchaos t ht) Hsub hmeas hsum htail
    refine le_trans (le_of_eq ?_) hm
    refine lintegral_congr_ae ?_
    filter_upwards [hcoord] with ω hω
    rw [hω, if_pos hk, hQe' ω]
  · rw [if_neg hk]
    obtain ⟨hsum, htail⟩ := hCq t ht k
    have hTb0 : 0 ≤ Cq * Lattice.jp k.1 ^ ((d : ℝ) + 3) := by
      have := S7FCW9_tailHS_nonneg (wickCoeff (withDensityReal (R.ρ t)) (hTransport d R.D.s (Torus.realMode k))) ∅
      linarith
    have hm := S7FCH3_moment_gen P' (η t) K0 hK0 p Cp hp hCp (hchaos t ht) hQ hQm.aestronglyMeasurable hsum htail
    refine le_trans (le_of_eq ?_) hm
    refine lintegral_congr_ae ?_
    filter_upwards [hcoord] with ω hω
    rw [hω, if_neg hk, sub_zero, hQe' ω]

/-- The real-variable choice of `S₀` and `L₀`. -/
theorem S7FCH3_choose (a : NonzeroLattice d → ℝ) (ha : ∀ k, 0 ≤ a k) (hsum : Summable a)
    (ε : NonzeroLattice d → ℕ → ℝ) (hε0 : ∀ k L, 0 ≤ ε k L) (hεt : ∀ k, Tendsto (ε k) atTop (𝓝 0))
    (c1 c2 m θ : ℝ) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hm : 0 < m) (hθ : 0 < θ) :
    ∃ S₀ : Finset (NonzeroLattice d), ∀ S : Finset (NonzeroLattice d), S₀ ⊆ S → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      c1 * ∑ k ∈ S, a k * ε k L ^ m + c2 * ∑' k, (if k ∈ S then 0 else a k) ≤ θ := by
  classical
  have ht := (HRS.MC.Sec7.S7FCH1.S7FCH1_tail_tendsto a hsum).const_mul c2
  rw [mul_zero] at ht
  obtain ⟨S₀, hS₀⟩ := Filter.eventually_atTop.1 (ht.eventually (gt_mem_nhds (show (0 : ℝ) < θ / 2 by linarith)))
  refine ⟨S₀, fun S hS => ?_⟩
  have h2 : Tendsto (fun L : ℕ => c1 * ∑ k ∈ S, a k * ε k L ^ m) atTop (𝓝 0) := by
    have : Tendsto (fun L : ℕ => ∑ k ∈ S, a k * ε k L ^ m) atTop (𝓝 (∑ k ∈ S, a k * 0 ^ m)) := by
      refine tendsto_finset_sum _ fun k _ => ?_
      exact (((Real.continuousAt_rpow_const 0 m (Or.inr hm.le)).tendsto.comp (hεt k)).const_mul (a k))
    rw [Real.zero_rpow hm.ne'] at this
    simpa using this.const_mul c1
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.1 (h2.eventually (gt_mem_nhds (show (0 : ℝ) < θ / 2 by linarith)))
  refine ⟨L₀, fun L hL => ?_⟩
  have h3 := hL₀ L hL
  have h4 := hS₀ S hS
  linarith

end HRS.MC.Sec7.S7FCH3

end
