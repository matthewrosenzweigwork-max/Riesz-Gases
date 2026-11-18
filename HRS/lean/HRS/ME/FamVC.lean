import HRS.MD.EQInterpWin
import HRS.Main.HeadlineEquilibrium
import HRS.PDE.TorusFPSpec
import HRS.PDE.MeanFieldSemigroup
import HRS.Energy.Modulated

/-!
# Packet V3a (namespace `HRS.ME.FamV`): the time-zero rate observable of the window `ζ^{0+·}`

* `rateEval d m T hT k : PathSpace d m T →L[ℝ] ℝ`, `w ↦ NegSobolev.eval (w.at' 0) (Torus.cosMode k)`,
  realised as the inner product with the fixed `ℓ²` vector `cosVec d m k` (so it is continuous
  without a separate bound); `rateEval_apply` is the defining identity.
* `canonicalGibbs_isExchangeable`: the canonical Gibbs law `canonicalGibbs (periodicRiesz d s) V N β`
  is exchangeable for every potential `V` (permutation invariance of the Hamiltonian; no density hypothesis).
* `rate_zeta_law`: for a stationary Gibbs flow of the rate family `V = rateV k β θ` on the horizon `0 + T`,
  the image under `rateEval` of the law of the window `windowZeta m T 0 P X` is `HRS.Main.rateLaw d s k β N θ`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.FamV

/-! ### Exchangeability of the canonical Gibbs law -/

theorem sum_pair_identity {N : ℕ} (H : Fin N → Fin N → ℝ) (hH : ∀ i j, H i j = H j i) :
    ∑ i, ∑ j, H i j =
      2 * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), H i j + ∑ i, H i i := by
  simp only [Finset.sum_filter]
  have hpt : ∀ i j, H i j = (if i < j then H i j else 0) + (if j < i then H i j else 0) +
      (if i = j then H i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [if_pos h, if_neg (not_lt.2 h.le), if_neg h.ne]; ring
    · simp
    · rw [if_neg (not_lt.2 h.le), if_pos h, if_neg h.ne']; ring
  have hB : ∑ i, ∑ j, (if j < i then H i j else 0) = ∑ i, ∑ j, (if i < j then H i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [hH]
  have hD : ∑ i, ∑ j, (if i = j then H i j else 0) = ∑ i, H i i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  have hsplit : ∑ i, ∑ j, H i j = (∑ i, ∑ j, (if i < j then H i j else 0)) +
      (∑ i, ∑ j, (if j < i then H i j else 0)) + ∑ i, ∑ j, (if i = j then H i j else 0) := by
    have hrow : ∀ i, ∑ j, H i j = (∑ j, (if i < j then H i j else 0)) +
        (∑ j, (if j < i then H i j else 0)) + ∑ j, (if i = j then H i j else 0) := fun i => by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => hpt i j
    simp only [hrow, Finset.sum_add_distrib]
  rw [hsplit, hB, hD]
  ring

theorem pairSum_perm {N : ℕ} (H : Fin N → Fin N → ℝ) (hH : ∀ i j, H i j = H j i)
    (σ : Equiv.Perm (Fin N)) :
    ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), H (σ i) (σ j) =
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), H i j := by
  have h1 := sum_pair_identity (fun i j => H (σ i) (σ j)) (fun i j => hH _ _)
  have h2 := sum_pair_identity H hH
  have hF : ∑ i, ∑ j, H (σ i) (σ j) = ∑ i, ∑ j, H i j := by
    calc ∑ i, ∑ j, H (σ i) (σ j) = ∑ i, ∑ j, H (σ i) j :=
          Finset.sum_congr rfl fun i _ => Equiv.sum_comp σ (H (σ i))
      _ = ∑ i, ∑ j, H i j := Equiv.sum_comp σ (fun i => ∑ j, H i j)
  have hD : ∑ i, H (σ i) (σ i) = ∑ i, H i i := Equiv.sum_comp σ (fun i => H i i)
  linarith

theorem canonicalHamiltonian_comp_perm {d N : ℕ} (g V : Torus d → ℝ) (hg : ∀ x, g (-x) = g x)
    (X : Config d N) (σ : Equiv.Perm (Fin N)) :
    HRS.canonicalHamiltonian g V (X ∘ σ) = HRS.canonicalHamiltonian g V X := by
  unfold HRS.canonicalHamiltonian
  have hH : ∀ i j : Fin N, g (X i - X j) = g (X j - X i) := fun i j => by
    rw [← hg (X i - X j), neg_sub]
  have hp := pairSum_perm (fun i j => g (X i - X j)) hH σ
  have hv : ∑ i, V ((X ∘ σ) i) = ∑ i, V (X i) := Equiv.sum_comp σ (fun i => V (X i))
  have hp' : ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), g ((X ∘ σ) i - (X ∘ σ) j) =
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), g (X i - X j) := hp
  rw [hv, hp']

theorem canonicalGibbs_isExchangeable {d N : ℕ} (g V : Torus d → ℝ) (hg : ∀ x, g (-x) = g x)
    (β : ℝ) : HRS.IsExchangeable (HRS.canonicalGibbs g V N β) := by
  intro σ
  have hmeas : AEMeasurable (fun X : Config d N => X ∘ σ)
      ((volume : Measure (Config d N)).withDensity fun X =>
        ENNReal.ofReal (Real.exp (-β * HRS.canonicalHamiltonian g V X))) :=
    (HRS.permMeasEquiv σ).measurable.aemeasurable
  have hvol : (volume : Measure (Config d N)) =
      Measure.pi fun _ : Fin N => (volume : Measure (Torus d)) := rfl
  unfold HRS.canonicalGibbs
  rw [Measure.map_smul _ hmeas]
  congr 1
  rw [hvol]
  refine HRS.map_withDensity_perm _ σ _ fun X => ?_
  simp only [canonicalHamiltonian_comp_perm g V hg X σ]

/-! ### The vector representing `F ↦ F(cos_k)` -/

theorem memℓp_fourierVec (d : ℕ) (m : ℝ) (φ : Torus d → ℝ)
    (hs : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2) :
    Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ m * Torus.funRealCoeff φ k) 2 := by
  rw [Torus.memℓp_two_iff]
  refine hs.congr fun k => ?_
  rw [mul_pow, Torus.jp_rpow_sq]

/-- The `ℓ²` vector `k ↦ ⟨k⟩^{m} φ̂(k)`, representing `F ↦ F(φ)` as an inner product in `E_m`. -/
def fourierVec (d : ℕ) (m : ℝ) (φ : Torus d → ℝ)
    (hs : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2) :
    NegSobolev d m :=
  (⟨fun k : NonzeroLattice d => Lattice.jp k.1 ^ m * Torus.funRealCoeff φ k,
    memℓp_fourierVec d m φ hs⟩ : lp (fun _ : NonzeroLattice d => ℝ) 2)

theorem summable_cosMode (d : ℕ) (m : ℝ) (k : Lattice d) :
    Summable fun l : NonzeroLattice d =>
      Lattice.jp l.1 ^ (2 * m) * Torus.funRealCoeff (Torus.cosMode k) l ^ 2 := by
  obtain ⟨-, hs⟩ := HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (HRS.d1_isSmooth_cosMode k) m
  exact hs

/-- The vector representing `F ↦ F(cos_k)` in `E_m`. -/
def cosVec (d : ℕ) (m : ℝ) (k : Lattice d) : NegSobolev d m :=
  fourierVec d m (Torus.cosMode k) (summable_cosMode d m k)

theorem eval_eq_inner_cos {d : ℕ} {m : ℝ} (F : NegSobolev d m) (k : Lattice d) :
    NegSobolev.eval F (Torus.cosMode k) = @inner ℝ (NegSobolev d m) _ F (cosVec d m k) := by
  have h := lp.inner_eq_tsum (𝕜 := ℝ) (G := fun _ : NonzeroLattice d => ℝ)
    (F : lp (fun _ : NonzeroLattice d => ℝ) 2) (cosVec d m k : lp (fun _ : NonzeroLattice d => ℝ) 2)
  refine Eq.trans ?_ h.symm
  unfold NegSobolev.eval
  refine tsum_congr fun l => ?_
  simp only [NegSobolev.fourierCoeff, RCLike.inner_apply, conj_trivial]
  show Lattice.jp l.1 ^ m * NegSobolev.coord F l * Torus.funRealCoeff (Torus.cosMode k) l =
    (Lattice.jp l.1 ^ m * Torus.funRealCoeff (Torus.cosMode k) l) * NegSobolev.coord F l
  ring

/-! ### The rate observable `rateEval` -/

/-- The time-`0` point of the window, as an element of `[0,T]`. -/
def t0 {T : ℝ} (hT : 0 ≤ T) : Set.Icc (0 : ℝ) T := ⟨0, Set.left_mem_Icc.2 hT⟩

/-- The continuous linear map `w ↦ NegSobolev.eval (w.at' 0) (Torus.cosMode k)` on `𝒳_{m,T}`. -/
def rateEval (d : ℕ) (m T : ℝ) (hT : 0 ≤ T) (k : Lattice d) : PathSpace d m T →L[ℝ] ℝ :=
  (innerSL ℝ (cosVec d m k)).comp (ContinuousMap.evalCLM ℝ (t0 hT))

theorem rateEval_apply {d : ℕ} {m T : ℝ} (hT : 0 ≤ T) (k : Lattice d) (w : PathSpace d m T) :
    rateEval d m T hT k w = NegSobolev.eval (w.at' (t0 hT)) (Torus.cosMode k) := by
  show innerSL ℝ (cosVec d m k) (w.at' (t0 hT)) = _
  rw [innerSL_apply_apply, eval_eq_inner_cos, real_inner_comm]

/-! ### The rate potential and the law of `rateY` -/

theorem rateV_isSmooth_C {d : ℕ} (k : Lattice d) (β θ : ℝ) :
    Torus.IsSmooth (HRS.rateV k β θ) := by
  unfold Torus.IsSmooth Torus.IsCk
  have hdot : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : HRS.Euc d => Lattice.dot k y) := by
    unfold Lattice.dot
    exact ContDiff.sum fun i _ => contDiff_const.mul
      (EuclideanSpace.proj i : HRS.Euc d →L[ℝ] ℝ).contDiff
  have : Torus.lift (HRS.rateV k β θ) =
      fun y => -θ * Real.cos (2 * Real.pi * Lattice.dot k y) / β := by
    funext y
    simp only [Torus.lift, Function.comp, HRS.rateV, Torus.cosMode_mk]
  rw [this]
  exact (contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul hdot))).div_const β

theorem measurable_rateY {d : ℕ} (s : ℝ) (k : Lattice d) (β θ : ℝ) (N : ℕ) :
    Measurable (HRS.rateY d s k β N θ) := by
  have hc : Continuous (HRS.rateY d s k β N θ) := by
    unfold HRS.rateY
    exact continuous_const.mul ((continuous_const.mul (continuous_finsetSum _ fun i _ =>
      (Torus.continuous_cosMode k).comp (continuous_apply i))).sub continuous_const)
  exact hc.measurable

/-- The `E_m`-pairing of the centred empirical field `ζ_N = √N(μ_N - m_N)` with `cos_k`. -/
theorem eval_zetaE_cos {d : ℕ} {m : ℝ} (hm : (d : ℝ) < 2 * m) (k : Lattice d) {N : ℕ} (hN : 1 ≤ N)
    (μ : Measure (Config d N)) [IsProbabilityMeasure μ] (x : Config d N) :
    NegSobolev.eval (HRS.zetaE m μ x) (Torus.cosMode k) =
      Real.sqrt N * (HRS.pair (HRS.empirical x) (Torus.cosMode k) -
        HRS.pair (HRS.meanEmpirical μ) (Torus.cosMode k)) := by
  have := HRS.empirical_isProbabilityMeasure (by omega : 0 < N) x
  have := HRS.isProbabilityMeasure_meanEmpirical μ hN
  unfold HRS.zetaE
  rw [eval_eq_inner_cos, real_inner_smul_left, ← eval_eq_inner_cos,
    NegSobolev.eval_ofMeasureDiff hm (HRS.empirical x) (HRS.meanEmpirical μ) (Torus.cosMode k)
      (HRS.d1_isSmooth_cosMode k)]

/-- Main statement (packet V3a). For a stationary Gibbs flow of the rate family on the horizon `0 + T`,
the law of `rateEval` applied to the window `ζ^{0+·}` is the rate law `HRS.Main.rateLaw`. -/
theorem rate_zeta_law {d : ℕ} (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ}
    (hβ : 0 < β) (k : Lattice d) (θ : ℝ) {N : ℕ} (hN : 2 ≤ N) {m T : ℝ} (hm : (d : ℝ) < 2 * m)
    (hT : 0 ≤ T) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → HRS.Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : HRS.LZ.IsStationaryGibbsFlow P s hs0 hsd (HRS.rateV k β θ) β hβ (0 + T) X₀ W X) :
    (HRS.law P (HRS.Main.windowZeta m T 0 P X)).map (rateEval d m T hT k) =
      HRS.Main.rateLaw d s k β N θ := by
  have hV : Torus.IsSmooth (HRS.rateV k β θ) := rateV_isSmooth_C k β θ
  obtain ⟨hstat, hmeas, -⟩ := HRS.MD.EQInterp.flow_facts hd hs0 hsd _ hV hβ hN P hX
  have hex : HRS.IsExchangeable
      (HRS.canonicalGibbs (HRS.periodicRiesz d s) (HRS.rateV k β θ) N β) :=
    canonicalGibbs_isExchangeable _ _ (fun x => HRS.periodicRiesz_neg x) β
  have hGp : IsProbabilityMeasure
      (HRS.canonicalGibbs (HRS.periodicRiesz d s) (HRS.rateV k β θ) N β) := by
    rw [← hstat 0 (by simp [hT])]
    exact (Measure.isProbabilityMeasure_map_iff (hmeas 0).aemeasurable).2 inferInstance
  have hcont := HRS.MD.EQInterp.windowZeta_cont_ae hd hs0 hsd _ hV hβ hN (le_refl (0 : ℝ)) hT P hX hm
  have hae : (rateEval d m T hT k ∘ HRS.Main.windowZeta m T 0 P X) =ᵐ[P]
      (fun ω => HRS.rateY d s k β N θ (X 0 ω)) := by
    filter_upwards [hcont] with ω hω
    show rateEval d m T hT k (HRS.Main.windowZeta m T 0 P X ω) = _
    rw [rateEval_apply, HRS.MD.EQInterp.windowZeta_at' P X ω hω (t0 hT)]
    have h0 : Real.toNNReal (0 + ((t0 hT : Set.Icc (0 : ℝ) T) : ℝ)) = 0 := by simp [t0]
    rw [h0, hstat 0 (by simp [hT]), eval_zetaE_cos hm k (by omega)
      (HRS.canonicalGibbs (HRS.periodicRiesz d s) (HRS.rateV k β θ) N β) (X 0 ω)]
    rw [HRS.meanEmpirical_eq_firstMarginal _ hex (by omega),
      HRS.pair_empirical (by omega : 0 < N) (X 0 ω) (Torus.cosMode k)]
    simp only [HRS.rateY, HRS.rateMeanN, HRS.rateGibbs, one_div]
  have hW : AEMeasurable (HRS.Main.windowZeta m T 0 P X) P :=
    HRS.MD.EQInterp.windowZeta_aemeasurable hd hs0 hsd _ hV hβ hN (le_refl (0 : ℝ)) hT P hX hm
  have hR : Measurable (rateEval d m T hT k) := (rateEval d m T hT k).continuous.measurable
  calc (HRS.law P (HRS.Main.windowZeta m T 0 P X)).map (rateEval d m T hT k)
      = P.map (rateEval d m T hT k ∘ HRS.Main.windowZeta m T 0 P X) :=
        AEMeasurable.map_map_of_aemeasurable hR.aemeasurable hW
    _ = P.map (fun ω => HRS.rateY d s k β N θ (X 0 ω)) := Measure.map_congr hae
    _ = (P.map (X 0)).map (HRS.rateY d s k β N θ) :=
        (Measure.map_map (measurable_rateY s k β θ N) (hmeas 0)).symm
    _ = (HRS.canonicalGibbs (HRS.periodicRiesz d s) (HRS.rateV k β θ) N β).map
          (HRS.rateY d s k β N θ) := by
        rw [hstat 0 (by simp [hT])]
    _ = HRS.Main.rateLaw d s k β N θ := rfl

end HRS.ME.FamV
