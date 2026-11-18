import HRS.Main.A9Aux25

/-!
# Packet A9, part 26: pointwise convergence of the transported fields and the qualitative convergence of
the linear field laws at the adjoint level `γ` (copies of `a34_field_pointwise`, `a34_qual_one/two`)
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.Main.A9

open HRS HRS.PDE HRS.PDE.ET HRS.A33 HRS.Main HRS.A34

variable {d : ℕ}

theorem a9_field_pointwise (s : ℝ) (Rg : Regime) (ν₀ MB Λ T VB : ℝ) (S : MainData d)
    (hs : S.s = s) (hT : S.T = T) (L : LimitCoeffs d)
    (hcoef : CoeffConvergence S L Rg ν₀ MB Λ VB (gammaIdx d) (gammaIdx d))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (F : NegSobolev d (gammaIdx d : ℝ)) {γ' : ℝ}
    (hγ : (gammaIdx d : ℝ) < γ') :
    Tendsto (fun N => ‖NegSobolev.embed γ'
        (S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) F) -
        NegSobolev.embed γ' (L.A • transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) F)‖)
      atTop (𝓝 0) := by
  subst hs hT
  have hd := S.hd
  have hs0 := S.hs0
  have hsd := S.hsd
  obtain ⟨K', hK'0, hK'⟩ := a34_transport_unif hd S.s hs0 hsd Rg MB Λ VB ν₀ S.T
  have hmono : ∀ N, 1 ≤ N → AdjointData S.s (gammaIdx d) Rg MB Λ VB (S.dyn N) ν₀ S.T (S.ρ N) :=
    fun N hN => hcoef.seq_adjoint N hN
  have hmonoL : AdjointData S.s (gammaIdx d) Rg MB Λ VB (L.dyn S) ν₀ S.T L.ρ :=
    hcoef.limit_adjoint
  have hfacts := fun (N : ℕ) (hN : 1 ≤ N) =>
    a9_delta_facts S L (gammaIdx d) N Rg ν₀ MB Λ VB (hcoef.seq_adjoint N hN) hcoef.limit_adjoint
  set Δ : ℕ → ℝ := fun N => S.coeffDiscrepancy L (gammaIdx d) N with hΔ
  have hΔt : Tendsto Δ atTop (𝓝 0) := hcoef.tendsto
  have hev1 : ∀ᶠ N in atTop, Δ N ≤ 1 := (tendsto_order.1 hΔt).2 1 one_pos |>.mono fun N h => h.le
  have hAN : Tendsto (fun N => S.AN N) atTop (𝓝 L.A) := by
    refine tendsto_sub_nhds_zero_iff.1 (squeeze_zero_norm' ?_ hΔt)
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [Real.norm_eq_abs]
    exact (hfacts N hN).2.2.2.2
  -- the mode-wise convergence
  have hmode : ∀ k : NonzeroLattice d, Tendsto (fun N => NegSobolev.eval F
      (propagator (S.dyn N) (S.ρ N) 0 t (Torus.realMode k))) atTop
      (𝓝 (NegSobolev.eval F (propagator (L.dyn S) L.ρ 0 t (Torus.realMode k)))) :=
    fun k => a9_mode_conv S L Rg ν₀ MB Λ VB hcoef ht F k
  -- bounds
  have hbd : ∀ᶠ N in atTop, ‖S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) F -
      L.A • transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) F‖ ^ 2 ≤
      ((2 * |L.A| + 1) * (‖F‖ * K')) ^ 2 := by
    filter_upwards [eventually_ge_atTop 1, hev1] with N hN hN1
    have h1 := hK' (S.dyn N) (S.ρ N) (hmono N hN) t ht F
    have h2 := hK' (L.dyn S) L.ρ hmonoL t ht F
    have hAb : |S.AN N| ≤ |L.A| + 1 := by
      have := (hfacts N hN).2.2.2.2
      have h3 : |S.AN N| ≤ |L.A| + |S.AN N - L.A| := by
        have := abs_add_le L.A (S.AN N - L.A)
        simpa using this
      linarith
    have hFK : 0 ≤ ‖F‖ * K' := mul_nonneg (norm_nonneg _) hK'0
    have hn1 : ‖S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) F‖ ≤
        (|L.A| + 1) * (‖F‖ * K') := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul hAb h1 (norm_nonneg _) (by positivity)
    have hn2 : ‖L.A • transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) F‖ ≤
        |L.A| * (‖F‖ * K') := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    have h4 := (norm_sub_le _ _).trans (add_le_add hn1 hn2)
    refine pow_le_pow_left₀ (norm_nonneg _) (h4.trans (le_of_eq ?_)) 2
    ring
  refine a34_embed_tendsto hγ
    (fun N => S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) F)
    (L.A • transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) F) _ hbd ?_
  intro k
  have hcN : ∀ᶠ N in atTop, NegSobolev.coord
      (S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) F) k =
      S.AN N * (Lattice.jp k.1 ^ (-(gammaIdx d : ℝ)) *
        NegSobolev.eval F (propagator (S.dyn N) (S.ρ N) 0 t (Torus.realMode k))) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [a34_coord_smul, a34_coord_tf hd Rg MB Λ VB ν₀ S.T (S.dyn N) (S.ρ N) (hmono N hN) ht F k]
  have hL : NegSobolev.coord (L.A • transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) F) k =
      L.A * (Lattice.jp k.1 ^ (-(gammaIdx d : ℝ)) *
        NegSobolev.eval F (propagator (L.dyn S) L.ρ 0 t (Torus.realMode k))) := by
    rw [a34_coord_smul, a34_coord_tf hd Rg MB Λ VB ν₀ S.T (L.dyn S) L.ρ hmonoL ht F k]
  rw [hL]
  exact Tendsto.congr' (hcN.mono fun N h => h.symm)
    (hAN.mul (tendsto_const_nhds.mul (hmode k)))

end HRS.Main.A9
