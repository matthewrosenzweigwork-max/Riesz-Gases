import HRS.MC.S7UCDefs
import HRS.MC.S7FCH3G

/-!
# S7UCQA: proof of `s7_UC_H3_gauss_approx_unif` (UC-H3)

The statement is copied verbatim from `HRS/MC/S7UCPlan.lean` (namespace `HRS.MC.Sec7.UCPlan`); it is proved here in
namespace `HRS.MC.Sec7.S7UCQ` and tied to the plan statement in `HRS/MC/S7UCQTie.lean`.

Route: the proof of `HRS.MC.Sec7.S7FCH3.s7_FC_H3_gauss_approx_proof` (`S7FCH3G.lean`) with the time variable `t` replaced by
`a + t`.  All constants (`K0`, `Cp`, `Cq`, `M₀`, the choice of `S₀`, `L₀`) are produced before `a` is introduced, because
`S7FCH3_coord_moment`, `hchaos`, `hCq` are stated for every `t ≥ 0`; only the Wick hypothesis (translate of `UCField.2.1`), the
`L²` hypothesis (the `a`-th window of `UCField`) and the pathwise identification `η = η'` on `[0, a+T]` depend on `a`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7UCQ

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.S7FCH4
open HRS.MC.Sec7.UCPlan HRS.MC.Sec7.S7FCH3 HRS.MC.Sec7.S7FCW9

variable {d : ℕ}

/-- Translation of an a.e. statement on `Ici 0` to the window `[0,T]` shifted by `a ≥ 0`. -/
theorem S7UCQ_ae_shift {P : ℝ → Prop} (hP : ∀ᵐ t ∂(volume.restrict (Set.Ici (0 : ℝ))), P t)
    (a T : ℝ) (ha : 0 ≤ a) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), P (a + t) := by
  have h0 : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ici (0 : ℝ) → P t :=
    (ae_restrict_iff' measurableSet_Ici).1 hP
  have h1 : ∀ᵐ t ∂(volume : Measure ℝ), a + t ∈ Set.Ici (0 : ℝ) → P (a + t) :=
    (measurePreserving_add_left volume a).quasiMeasurePreserving.ae h0
  refine (ae_restrict_iff' measurableSet_Icc).2 (h1.mono fun t ht htI => ht ?_)
  exact add_nonneg ha htI.1

/-- Joint measurability is preserved by the time shift `t ↦ a + t`. -/
theorem S7UCQ_meas_shift {E Ω' : Type*} [MeasurableSpace E] [MeasurableSpace Ω'] (Y : ℝ → Ω' → E)
    (hY : Measurable (Function.uncurry Y)) (a : ℝ) :
    Measurable (Function.uncurry (fun (t : ℝ) (ω : Ω') => Y (a + t) ω)) :=
  hY.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)

/-- A.s. the continuous version `η'` agrees with `η` on `[0,T']`. -/
theorem S7UCQ_path_eq {r : ℝ} {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    (η η' : ℝ → Ω' → NegSobolev d r) (T' : ℝ) (hT' : 0 < T')
    (hη'ae : ∀ t : ℝ, 0 ≤ t → η' t =ᵐ[P'] η t)
    (hη'cont : ∀ (ω : Ω') (T : ℝ), ContinuousOn (fun t => η' t ω) (Set.Icc 0 T))
    (hcont : ∀ᵐ ω ∂P', ContinuousOn (fun t => η t ω) (Set.Icc 0 T')) :
    ∀ᵐ ω ∂P', ∀ t ∈ Set.Icc (0 : ℝ) T', η t ω = η' t ω := by
  set D : Set ℝ := Set.range ((↑) : ℚ → ℝ) ∩ Set.Ioo 0 T' with hD
  have hDc : D.Countable := (Set.countable_range _).mono Set.inter_subset_left
  have hq' : ∀ s ∈ D, ∀ᵐ ω ∂P', η s ω = η' s ω := fun s hs => by
    filter_upwards [hη'ae s (le_of_lt hs.2.1)] with ω hω
    exact hω.symm
  have hall := (MeasureTheory.ae_ball_iff hDc).2 hq'
  filter_upwards [hall, hcont] with ω hω hc
  have hEq : Set.EqOn (fun t => η t ω) (fun t => η' t ω) D := fun s hs => hω s hs
  have hcl : Set.Icc (0 : ℝ) T' ⊆ closure D := by
    have hdense : Dense (Set.range ((↑) : ℚ → ℝ)) := Rat.denseRange_cast
    have h1 : Set.Ioo (0 : ℝ) T' ⊆ closure (Set.Ioo 0 T' ∩ Set.range ((↑) : ℚ → ℝ)) :=
      hdense.open_subset_closure_inter isOpen_Ioo
    have h2 : closure (Set.Ioo (0 : ℝ) T') ⊆ closure D := by
      refine closure_minimal (h1.trans ?_) isClosed_closure
      refine closure_mono ?_
      rw [Set.inter_comm]
    rw [← closure_Ioo hT'.ne] at *
    exact h2
  exact fun t ht => (hEq.of_subset_closure hc ((hη'cont ω T')) (fun s hs => ⟨hs.2.1.le, hs.2.2.le⟩) hcl) ht

/-- **UC-H3** (verbatim statement of `HRS.MC.Sec7.UCPlan.s7_UC_H3_gauss_approx_unif`). -/
theorem s7_UC_H3_gauss_approx_unif_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η : ℝ → Ω' → NegSobolev d r)
    (hη : IsGaussianLimitField R.D R.ρ (withDensityReal R.ρ₀) R.β₀ r P' η)
    (B : ℝ → Ω' → NegSobolev d r) (hB : UCField R r P' η B)
    (ε₂ c : ℝ) (K : NonzeroLattice d → ℕ → FRKernel d) (hK : FCKernelData R ε₂ c K) (q : ℝ) (hq : 1 ≤ q)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ S₀ : Finset (NonzeroLattice d), ∀ S : Finset (NonzeroLattice d), S₀ ⊆ S →
      ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∀ a : ℝ, 0 ≤ a →
        Integrable (fun ω => ‖(pairLim r T a η B ω).2 -
          toL2 r T (fun t => fcGaussAt r S (fun k => K k L) P' η (a + t) ω)‖ ^ q) P' ∧
        ∫ ω, ‖(pairLim r T a η B ω).2 -
          toL2 r T (fun t => fcGaussAt r S (fun k => K k L) P' η (a + t) ω)‖ ^ q ∂P' ≤ δ := by
  classical
  obtain ⟨hBm, hBW, hBL2⟩ := hB
  -- Step 0: constants and the continuous version of `η`
  have hηm : ∀ t, Measurable (η t) := by
    obtain ⟨Y₀, -, hLin⟩ := hη
    exact (hLin 0).meas
  obtain ⟨K0, hK0, hC1'⟩ := HRS.MC.Sec7.S7FCW2.s7_FC_C1_coeffs_proof R r hr
  have hC1 : ∀ t : ℝ, 0 ≤ t → HasFiniteGaussianCoeffs P' (η t) ∧ ModeCovBound P' (η t) K0 :=
    fun t ht => hC1' P' η hη t ht
  obtain ⟨η', hη'm, hη'ae, hη'cont⟩ := HRS.MC.Sec7.S7FCW2.s7_FC_C3_version_proof R r P' η hη
  obtain ⟨m₀, M₀, hm₀, hbd⟩ := R.bounds
  have hdens : ∀ t : ℝ, 0 ≤ t → IsProbDensity (R.ρ t) := fun t ht =>
    (R.mf (t + 1) (by linarith)).density t ⟨ht, by linarith⟩
  have hM : ∀ t : ℝ, 0 ≤ t → ∀ x, R.ρ t x ≤ M₀ := fun t ht x => (hbd t ht x).2
  obtain ⟨Cq, hCq0, hhd⟩ := HRS.MC.QRSpec.Hd.qrs_hd_commutator_tail_proof R.D.s R.D.hs0 R.hs R.hd
  set p : ℝ := max q 2 with hp
  have hp2 : 2 ≤ p := le_max_right _ _
  have hqp : q ≤ p := le_max_left _ _
  set m : ℝ := p / 2 with hm
  have hm1 : 1 ≤ m := by rw [hm]; linarith
  have hm0 : 0 < m := by linarith
  have h2m : 2 * m = p := by rw [hm]; ring
  obtain ⟨Cp, hCp0, hCp⟩ := HRS.MC.QRSpec.Chaos.qrs_chaos_lp_lim_proof p hp2
  have hchaos : ∀ t : ℝ, 0 ≤ t → ∀ (μ : Measure (Torus d)) (h : Torus d → Torus d → ℝ) (Q : Ω' → ℝ),
      IsHalfWick P' (η t) μ h Q → AEStronglyMeasurable Q P' →
      (Summable fun q : NonzeroLattice d × NonzeroLattice d => wickCoeff μ h q.1 q.2 ^ 2) →
      eLpNorm (fun ω => Q ω - wickSection P' (η t) μ h ∅ ω) (ENNReal.ofReal p) P' ≤
        ENNReal.ofReal (Cp * K0 * Real.sqrt (tailHS (wickCoeff μ h) ∅)) :=
    fun t ht μ h Q hQ hQm hs => hCp d r P' (η t) (hC1 t ht).1 K0 hK0 (hC1 t ht).2 μ h Q hQ hQm hs ∅
  have hCq : ∀ t : ℝ, 0 ≤ t → ∀ k : NonzeroLattice d,
      (Summable fun q : NonzeroLattice d × NonzeroLattice d =>
        wickCoeff (withDensityReal (R.ρ t)) (hTransport d R.D.s (Torus.realMode k)) q.1 q.2 ^ 2) ∧
      tailHS (wickCoeff (withDensityReal (R.ρ t)) (hTransport d R.D.s (Torus.realMode k))) ∅ ≤
        Cq * Lattice.jp k.1 ^ ((d : ℝ) + 3) := fun t ht k => by
    have h1 := hhd (R.ρ t) (hdens t ht) M₀ (hM t ht) k 1 le_rfl
    exact ⟨h1.1, h1.2.1⟩
  -- Step 1: the weights and the choice of `S₀`, `L₀`
  have hasum : Summable (S7FCH3_wt d r : NonzeroLattice d → ℝ) := by
    have := S7FCW9_summable_jp (d := d) (2 * r - ((d : ℝ) + 3))
      (by rw [hr]; push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
    exact this.congr fun k => rfl
  set A : ℝ := ∑' k, S7FCH3_wt d r k + 1 with hA
  have hA0 : 0 < A := by
    have : 0 ≤ ∑' k, S7FCH3_wt d r k := tsum_nonneg fun k => (S7FCH3_wt_pos r k).le
    linarith
  set εf : NonzeroLattice d → ℕ → ℝ := fun k L => ∫ z : Torus d × Torus d,
    (hTransport d R.D.s (Torus.realMode k) z.1 z.2 - (K k L).toFun z.1 z.2) ^ 2
      ∂((volume : Measure (Torus d)).prod volume) with hεf
  have hεt : ∀ k, Tendsto (εf k) atTop (𝓝 0) := fun k => S7FCH3_eps_tendsto R hK k
  have hε0 : ∀ k L, 0 ≤ εf k L := fun k L => integral_nonneg fun z => sq_nonneg _
  set c1 : ℝ := (Cp * K0) ^ p with hc1
  set c2 : ℝ := (Cp * K0) ^ p * Cq ^ m with hc2
  have hc10 : 0 ≤ c1 := Real.rpow_nonneg (mul_nonneg hCp0.le hK0) _
  have hc20 : 0 ≤ c2 := mul_nonneg hc10 (Real.rpow_nonneg hCq0.le _)
  have hTpos : 0 < T ^ m * A ^ (m - 1) :=
    mul_pos (Real.rpow_pos_of_pos hT _) (Real.rpow_pos_of_pos hA0 _)
  have hθ : 0 < δ ^ (2 * m / q) / (T ^ m * A ^ (m - 1)) :=
    div_pos (Real.rpow_pos_of_pos hδ _) hTpos
  obtain ⟨S₀, hS₀⟩ := S7FCH3_choose (S7FCH3_wt d r) (fun k => (S7FCH3_wt_pos r k).le) hasum εf hε0 hεt
    c1 c2 m _ hc10 hc20 hm0 hθ
  refine ⟨S₀, fun S hS => ?_⟩
  obtain ⟨L₀, hL₀⟩ := hS₀ S hS
  refine ⟨L₀, fun L hL a ha => ?_⟩
  have hSum := hL₀ L hL
  -- Step 2: the finite-rank field on the continuous version and its coordinates (window `a`)
  set Kf : NonzeroLattice d → FRKernel d := fun k => K k L with hKf
  set G' : ℝ → Ω' → NegSobolev d r := fun t ω => fcGaussAt r S Kf P' η' t ω with hG'
  have hG'm : Measurable (Function.uncurry G') := S7FCH3_G_meas S Kf P' η' hη'm
  have hBam := S7UCQ_meas_shift B hBm a
  have hGam := S7UCQ_meas_shift G' hG'm a
  set Dm : NonzeroLattice d → ℝ := fun k => c1 * (if k ∈ S then εf k L ^ m else Cq ^ m) with hDm
  have hDm0 : ∀ k, 0 ≤ Dm k := fun k => by
    refine mul_nonneg hc10 ?_
    split_ifs
    · exact Real.rpow_nonneg (hε0 k L) _
    · exact Real.rpow_nonneg hCq0.le _
  -- the split of the weighted sum
  have hsplit : ∀ k, S7FCH3_wt d r k * Dm k =
      (if k ∈ S then S7FCH3_wt d r k * (c1 * εf k L ^ m) else 0) +
        c2 * (if k ∈ S then 0 else S7FCH3_wt d r k) := by
    intro k
    by_cases hk : k ∈ S <;> simp [hDm, hk, hc2] <;> ring
  have hu : Summable fun k => (if k ∈ S then S7FCH3_wt d r k * (c1 * εf k L ^ m) else 0) :=
    summable_of_ne_finset_zero (s := S) fun k hk => by simp [hk]
  have hv : Summable fun k : NonzeroLattice d => (if k ∈ S then 0 else S7FCH3_wt d r k) := by
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hasum
    · split_ifs
      · exact le_rfl
      · exact (S7FCH3_wt_pos r k).le
    · split_ifs
      · exact (S7FCH3_wt_pos r k).le
      · exact le_rfl
  have hDs : Summable fun k => S7FCH3_wt d r k * Dm k := by
    simp_rw [hsplit]
    exact hu.add (hv.mul_left c2)
  have hsumDm : ∑' k, S7FCH3_wt d r k * Dm k =
      c1 * ∑ k ∈ S, S7FCH3_wt d r k * εf k L ^ m + c2 * ∑' k, (if k ∈ S then 0 else S7FCH3_wt d r k) := by
    simp_rw [hsplit]
    rw [hu.tsum_add (hv.mul_left c2), tsum_mul_left]
    congr 1
    rw [tsum_eq_sum (s := S) (fun k hk => by simp [hk])]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp [hk]
    ring
  -- Step 3: the moment hypothesis of the core lemma (times `a + t`)
  have hBWa := S7UCQ_ae_shift hBW a T ha
  have hmom : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ k : NonzeroLattice d,
      ∫⁻ ω, ENNReal.ofReal (|NegSobolev.fourierCoeff ((fun (t : ℝ) (ω : Ω') => B (a + t) ω - G' (a + t) ω) t ω) k| ^ (2 * m)) ∂P' ≤
        ENNReal.ofReal (S7FCH3_sg d k ^ m * Dm k) := by
    filter_upwards [hBWa, ae_restrict_mem measurableSet_Icc] with t hWt ht k
    have h0 := S7FCH3_coord_moment R r P' η η' hηm K0 hK0 hC1 hη'ae B hBm p Cp Cq M₀ hp2 hCp0.le hchaos hCq
      hdens hM S Kf (a + t) (add_nonneg ha ht.1) hWt k
    rw [h2m]
    refine h0.trans (ENNReal.ofReal_le_ofReal ?_)
    have hσ : 1 ≤ S7FCH3_sg d k ^ m := by
      refine Real.one_le_rpow ?_ hm0.le
      exact Real.one_le_rpow (Torus.jp_ge_one k.1) (by positivity)
    have hσ0 : 0 ≤ S7FCH3_sg d k := (S7FCH3_sg_pos k).le
    by_cases hk : k ∈ S
    · simp only [hk, if_true, hDm]
      rw [show p / 2 = m from hm.symm]
      have : 0 ≤ c1 * εf k L ^ m := mul_nonneg hc10 (Real.rpow_nonneg (hε0 k L) _)
      nlinarith
    · simp only [hk, if_false, hDm]
      rw [show p / 2 = m from hm.symm, Real.mul_rpow hCq0.le (Real.rpow_nonneg (Torus.jp_pos k.1).le _)]
      unfold S7FCH3_sg
      rw [hc1]
      nlinarith [Real.rpow_nonneg (Real.rpow_nonneg (Torus.jp_pos k.1).le ((d : ℝ) + 3)) m]
  have hW := S7FCH3_core_moment r hr P' T hT (fun (t : ℝ) (ω : Ω') => B (a + t) ω - G' (a + t) ω) (hBam.sub hGam) m hm1 Dm hDm0 hDs hmom
  -- Step 4: the norm bound
  have hbound : T ^ m * (A ^ (m - 1) * ∑' k, S7FCH3_wt d r k * Dm k) ≤ δ ^ (2 * m / q) := by
    rw [hsumDm]
    have h2 : (T ^ m * A ^ (m - 1)) * (δ ^ (2 * m / q) / (T ^ m * A ^ (m - 1))) = δ ^ (2 * m / q) :=
      mul_div_cancel₀ _ hTpos.ne'
    calc T ^ m * (A ^ (m - 1) * (c1 * ∑ k ∈ S, S7FCH3_wt d r k * εf k L ^ m +
          c2 * ∑' k, (if k ∈ S then 0 else S7FCH3_wt d r k)))
        = (T ^ m * A ^ (m - 1)) * (c1 * ∑ k ∈ S, S7FCH3_wt d r k * εf k L ^ m +
          c2 * ∑' k, (if k ∈ S then 0 else S7FCH3_wt d r k)) := by ring
      _ ≤ (T ^ m * A ^ (m - 1)) * (δ ^ (2 * m / q) / (T ^ m * A ^ (m - 1))) :=
          mul_le_mul_of_nonneg_left hSum hTpos.le
      _ = δ ^ (2 * m / q) := h2
  have hqm : q ≤ 2 * m := by rw [h2m]; exact hqp
  obtain ⟨-, hint, hle⟩ := S7FCH3_norm_moment P' r T (fun (t : ℝ) (ω : Ω') => B (a + t) ω) (fun (t : ℝ) (ω : Ω') => G' (a + t) ω) hBam hGam (hBL2 T hT a ha) m _ hm1 hW q hq hqm δ hδ hbound
  -- Step 5: transfer from `η'` back to `η` pathwise on `[a, a+T]`
  have hcont : ∀ᵐ ω ∂P', ContinuousOn (fun t => η t ω) (Set.Icc 0 (a + T)) := by
    obtain ⟨Y₀, -, hLin⟩ := hη
    exact (hLin (a + T)).cont
  have hpath := S7UCQ_path_eq P' η η' (a + T) (by linarith) hη'ae hη'cont hcont
  have hGeq : ∀ᵐ ω ∂P', toL2 r T (fun t => fcGaussAt r S (fun k => K k L) P' η (a + t) ω) =
      toL2 r T (fun t => G' (a + t) ω) := by
    filter_upwards [hpath] with ω hω
    refine S7FCH3_toL2_congr r T (fun t ht => ?_)
    exact S7FCH3_fcGauss_congr S Kf P' η η' (a + t) (hη'ae (a + t) (add_nonneg ha ht.1)) ω
      (hω (a + t) ⟨add_nonneg ha ht.1, by linarith [ht.2]⟩)
  have hnorm : ∀ᵐ ω ∂P', ‖(pairLim r T a η B ω).2 -
      toL2 r T (fun t => fcGaussAt r S (fun k => K k L) P' η (a + t) ω)‖ ^ q =
      ‖toL2 r T (fun t => B (a + t) ω) - toL2 r T (fun t => G' (a + t) ω)‖ ^ q := by
    filter_upwards [hGeq] with ω hω
    rw [hω]
    simp only [pairLim]
  refine ⟨hint.congr (hnorm.mono fun ω h => h.symm), ?_⟩
  calc ∫ ω, ‖(pairLim r T a η B ω).2 -
        toL2 r T (fun t => fcGaussAt r S (fun k => K k L) P' η (a + t) ω)‖ ^ q ∂P'
      = ∫ ω, ‖toL2 r T (fun t => B (a + t) ω) - toL2 r T (fun t => G' (a + t) ω)‖ ^ q ∂P' :=
        integral_congr_ae hnorm
    _ ≤ δ := hle

end HRS.MC.Sec7.S7UCQ

end
