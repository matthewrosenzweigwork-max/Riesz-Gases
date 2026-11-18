import HRS.Main.A34Aux27

/-!
# Packet A34, helper 28: pointwise convergence of the transported fields in the weaker topology
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace BoundedContinuousFunction

namespace HRS.A34

open HRS HRS.PDE HRS.PDE.ET HRS.A33 HRS.Main

variable {d : ℕ}

theorem a34_converges_congr {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    {μ μ' : ℕ → Measure E} {ν : Measure E} (h : ∀ᶠ N in atTop, μ N = μ' N)
    (hc : ConvergesInLaw μ ν) : ConvergesInLaw μ' ν := by
  intro f
  refine (hc f).congr' ?_
  filter_upwards [h] with N hN
  rw [hN]

theorem a34_conv_of_pointwise {E E' : Type*} [MeasurableSpace E] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [MeasurableSpace E'] [BorelSpace E'] {ν : Measure E}
    [IsProbabilityMeasure ν] (g : ℕ → E → E') (g₀ : E → E')
    (hg : ∀ᶠ N in atTop, Measurable (g N)) (hg₀ : Measurable g₀)
    (hpt : ∀ x, Tendsto (fun N => g N x) atTop (𝓝 (g₀ x))) :
    ConvergesInLaw (fun N => ν.map (g N)) (ν.map g₀) := by
  intro f
  have h0 : ∫ x, f x ∂(ν.map g₀) = ∫ y, f (g₀ y) ∂ν :=
    integral_map hg₀.aemeasurable f.continuous.aestronglyMeasurable
  rw [h0]
  have hlim : Tendsto (fun N => ∫ y, f (g N y) ∂ν) atTop (𝓝 (∫ y, f (g₀ y) ∂ν)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => ‖f‖) ?_ ?_ ?_ ?_
    · filter_upwards [hg] with N hN
      exact (f.continuous.measurable.comp hN).aestronglyMeasurable
    · exact Eventually.of_forall fun N => Eventually.of_forall fun y => by
        simpa [Real.norm_eq_abs] using f.norm_coe_le_norm (g N y)
    · exact integrable_const _
    · exact Eventually.of_forall fun y => (f.continuous.tendsto _).comp (hpt y)
  refine hlim.congr' ?_
  filter_upwards [hg] with N hN
  exact (integral_map hN.aemeasurable f.continuous.aestronglyMeasurable).symm

/-- the embedding as an additive homomorphism -/
def a34_embedHom {m m' : ℝ} (hmm' : m ≤ m') : NegSobolev d m →+ NegSobolev d m' where
  toFun := NegSobolev.embed m'
  map_zero' := by
    have := a34_embed_sub hmm' (0 : NegSobolev d m) 0
    simpa using this
  map_add' := a34_embed_add hmm'

theorem a34_map_conv_embed {m m' : ℝ} (hmm' : m ≤ m') (μ ν : Measure (NegSobolev d m))
    [SFinite μ] [SFinite ν] :
    (μ ∗ ν).map (NegSobolev.embed m') =
      (μ.map (NegSobolev.embed m')) ∗ (ν.map (NegSobolev.embed m')) := by
  haveI := InitialDataAux.negSobolev_secondCountable d m
  haveI := InitialDataAux.negSobolev_secondCountable d m'
  exact Measure.map_conv_addMonoidHom (μ := μ) (ν := ν) (a34_embedHom hmm') (a34_embed_meas hmm')

theorem a34_coord_smul {m : ℝ} (c : ℝ) (v : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (c • v) k = c * NegSobolev.coord v k := by
  unfold NegSobolev.coord
  exact lp.coeFn_smul c (v : lp (fun _ : NonzeroLattice d => ℝ) 2) ▸ rfl

theorem a34_coord_tf (hd : 1 ≤ d) {s : ℝ} (Rg : Regime) (MB Λ VB ν₀ T : ℝ) (D : DynData d)
    (ρ : ℝ → Torus d → ℝ) (hA : AdjointData s (gammaIdx d) Rg MB Λ VB D ν₀ T ρ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) (F : NegSobolev d (gammaIdx d : ℝ)) (k : NonzeroLattice d) :
    NegSobolev.coord (transportField D ρ t (gammaIdx d : ℝ) F) k =
      Lattice.jp k.1 ^ (-(gammaIdx d : ℝ)) *
        NegSobolev.eval F (propagator D ρ 0 t (Torus.realMode k)) := by
  have hm3 := ClassicalPart.three_le_mStar d
  have hγ : gammaIdx d = mStar d + d + 3 := rfl
  have hJ : mStar d ≤ gammaIdx d := by omega
  have hJ2 : mStar d + d ≤ gammaIdx d := by omega
  have hA' : AdjointData D.s (gammaIdx d) Rg MB Λ VB D ν₀ T ρ := by rw [hA.hs]; exact hA
  let S : A33Setup d := ⟨gammaIdx d, hJ, hJ2, hd, Rg, MB, Λ, VB, ν₀, D, T, ρ, hA'⟩
  exact NegSobolev.coord_ofSeq_of_mem _ (S.transport_memℓp ht F) k

theorem a34_field_pointwise (s : ℝ) (Rg : Regime) (ν₀ MB Λ T VB : ℝ) (S : MainData d)
    (hs : S.s = s) (hT : S.T = T) (L : LimitCoeffs d)
    (hcoef : CoeffConvergence S L Rg ν₀ MB Λ VB (gammaIdx d + 2) (gammaIdx d))
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
  obtain ⟨C, hC0, hC⟩ := a34_aco_diff hd S.s hs0 hsd Rg MB Λ VB ν₀ S.T
  have hmono : ∀ N, 1 ≤ N → AdjointData S.s (gammaIdx d) Rg MB Λ VB (S.dyn N) ν₀ S.T (S.ρ N) :=
    fun N hN => HRS.PDE.StabAux.adjointData_mono (by omega) (hcoef.seq_adjoint N hN)
  have hmonoL : AdjointData S.s (gammaIdx d) Rg MB Λ VB (L.dyn S) ν₀ S.T L.ρ :=
    HRS.PDE.StabAux.adjointData_mono (by omega) hcoef.limit_adjoint
  have hfacts := fun (N : ℕ) (hN : 1 ≤ N) =>
    a34_delta_facts S L (gammaIdx d) N Rg ν₀ MB Λ VB
      (HRS.PDE.StabAux.adjointData_mono (by omega) (hcoef.seq_adjoint N hN))
      (HRS.PDE.StabAux.adjointData_mono (by omega) hcoef.limit_adjoint)
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
      (𝓝 (NegSobolev.eval F (propagator (L.dyn S) L.ρ 0 t (Torus.realMode k)))) := by
    intro k
    refine tendsto_sub_nhds_zero_iff.1 (squeeze_zero_norm'
      (a := fun N => ‖F‖ * (C * Δ N * sobolevNorm ((gammaIdx d + 2 : ℕ) : ℝ)
        (Torus.realMode k : Torus d → ℝ))) ?_ ?_)
    · filter_upwards [eventually_ge_atTop 1] with N hN
      rw [Real.norm_eq_abs]
      obtain ⟨h0, hρ, hβ, -, -⟩ := hfacts N hN
      exact hC (S.dyn N) (L.dyn S) (S.ρ N) L.ρ (hcoef.seq_adjoint N hN) hcoef.limit_adjoint rfl rfl
        (Δ N) h0 hρ hβ t ht F k
    · have := ((hΔt.const_mul C).mul_const (sobolevNorm ((gammaIdx d + 2 : ℕ) : ℝ)
        (Torus.realMode k : Torus d → ℝ))).const_mul ‖F‖
      simpa using this
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

end HRS.A34
