import HRS.MS.MfeConfAux171
import HRS.MS.MfeConfAux17

/-!
# S.B.1 (SB5), R3d (part 3): `SbMovEnt` from the standing hypotheses, modulo `Sb1HBAll`

`sb1_movEnt_core`: for the data of `WholeMFEHyp` (any `d ≥ 1`, `0 ≤ s < d`, potential with `Sb1Pot` and confinement) and an
integrable Lipschitz majorant `K` of the transport, `SbMovEnt D N T ρ P X₀ X` holds, assuming the vanishing remainder `Sb1HBAll d`.
The initial law is truncated to the events `{dμ₀/d(sb1Dm sb1Gw) ≤ j + j₀}` (`sb1_bdd_movEnt_cond`), the truncation is removed by
`sb1_uncondition`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open HRS HRS.Whole
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

theorem sb1_movEnt_core (hHB : Sb1HBAll d) (hd : 1 ≤ d) {D : Whole.WholeDyn d} (hs0 : 0 ≤ D.s) (hsd : D.s < d)
    {B : ℝ} (hV : Sb1Pot D.V B) {cV CV : ℝ} (hcV : 0 < cV) (hconf : ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x)
    (hN : 2 ≤ N) {T Λ : ℝ} {r : ℕ} (hT : 0 ≤ T) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ρ : ℝ → Euc d → ℝ} {X₀ : Ω → Whole.EucConfig d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Whole.EucConfig d N}
    (h : Whole.WholeMFEHyp P D N T Λ r ρ X₀ W X) (K : ℝ → ℝ) (hKi : IntegrableOn K (Set.Icc 0 T))
    (hK : ∀ t ∈ Set.Icc (0 : ℝ) T, Whole.HasLipBoundW (Whole.mfeTransportW D (ρ t)) (K t)) :
    SbMovEnt D N T ρ P X₀ X := by
  have hN1 : 1 ≤ N := by omega
  have hN0 : 0 < N := by omega
  have hβ := h.pos_temp
  have H := sb1_tr3_of_hyp h hd hs0 hsd hV
  have hXm : ∀ t, Measurable (X t) := h.sol.adapted
  have hX0m : Measurable (X 0) := hXm 0
  have hmap : P.map (X 0) = P.map X₀ := Measure.map_congr h.sol.init
  suffices hmain : SbMovEnt D N T ρ P (X 0) X by
    unfold SbMovEnt at hmain ⊢
    rw [hmap] at hmain
    exact hmain
  obtain ⟨a, b, ha, hb, -, hcoarse⟩ := sb1_coarse_comm H hN1
  have hco : Sb1Coarse D N T ρ a b := ⟨ha, hb, hcoarse⟩
  have hnc := h.sol.no_collision
  rcases hT.eq_or_lt with hT0 | hTp
  · subst hT0
    exact sb1_movEnt_T0 H hN1 hβ hco (hK 0 ⟨le_rfl, le_rfl⟩) hXm hnc
  -- T > 0
  obtain ⟨ℱ, W', hF⟩ := h.filtered
  have hX' : Whole.IsWholeStrongSolution P D T (X 0) W X :=
    ⟨Eventually.of_forall fun _ => rfl, h.sol.eqn, h.sol.cont, h.sol.adapted, h.sol.no_collision⟩
  obtain ⟨η, A3, A4, hη, hη0, hA3, hA4, hB⟩ := hHB D H hTp N hN1 hβ K hK
  set μ₀ : Measure (Whole.EucConfig d N) := P.map (X 0) with hμ₀
  haveI : IsProbabilityMeasure μ₀ := (Measure.isProbabilityMeasure_map_iff hX0m.aemeasurable).2 inferInstance
  set R : Measure (Whole.EucConfig d N) := sb1Dm (fun Z => sb1Gw D (Whole.rieszKernel d D.s) N Z) with hR
  haveI : SigmaFinite R := by rw [hR, sb1Dm]; infer_instance
  have hent : relEntropy μ₀ (Whole.canonicalGibbs (Whole.rieszKernel d D.s) D.V N (1 / D.invβ)) ≠ ⊤ := by
    have := h.gibbs_entropy
    rw [← hmap] at this
    exact this
  have hmom0 : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂μ₀ < ⊤ :=
    sb1_init_moment hs0 hβ hV.c3.continuous.measurable ⟨cV, CV, hcV, hconf⟩ hent
  have hac : μ₀ ≪ R := by
    obtain ⟨c, hc0, hcan⟩ := sb1_canon_eq D hN0
    have h1 : μ₀ ≪ c • R := by
      have := (klDiv_ne_top_iff.1 hent).1
      rwa [hcan] at this
    intro A hA
    exact h1 (by simp [hA])
  have hrn : ∀ᵐ Z ∂μ₀, μ₀.rnDeriv R Z < ⊤ := hac.ae_le (Measure.rnDeriv_lt_top μ₀ R)
  have hex : ∀ᵐ Z ∂μ₀, ∃ k : ℕ, μ₀.rnDeriv R Z ≤ k := by
    filter_upwards [hrn] with Z hZ
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hZ.ne
    exact ⟨n, hn.le⟩
  set E : ℕ → Set (Whole.EucConfig d N) := fun k => {Z | μ₀.rnDeriv R Z ≤ k} with hE
  have hEb : ∀ k, MeasurableSet (E k) ∧ μ₀.restrict (E k) ≤ (k : ℝ≥0∞) • R := fun k => sb1_event_bdd μ₀ R hac k
  have hEmono : Monotone E := fun i j hij Z (hZ : μ₀.rnDeriv R Z ≤ i) =>
    show μ₀.rnDeriv R Z ≤ j from hZ.trans (Nat.cast_le.2 hij)
  obtain ⟨j0, hj0⟩ : ∃ j0, μ₀ (E j0) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have h1 : μ₀ (⋃ k, E k) = 0 := measure_iUnion_null hcon
    have h2 : ∀ᵐ Z ∂μ₀, Z ∈ ⋃ k, E k := by
      filter_upwards [hex] with Z ⟨k, hk⟩ using Set.mem_iUnion.2 ⟨k, hk⟩
    have h3 : μ₀ (⋃ k, E k)ᶜ = 0 := ae_iff.1 h2
    have := measure_union_le (μ := μ₀) (⋃ k, E k) (⋃ k, E k)ᶜ
    rw [Set.union_compl_self, h1, h3] at this
    simp at this
  set E' : ℕ → Set (Whole.EucConfig d N) := fun j => E (j + j0) with hE'
  have hE'm : ∀ j, MeasurableSet (E' j) := fun j => (hEb _).1
  have hE'mono : Monotone E' := fun i j hij => hEmono (Nat.add_le_add_right hij j0)
  have hPE : ∀ S, MeasurableSet S → P (X 0 ⁻¹' S) = μ₀ S := fun S hS => (Measure.map_apply hX0m hS).symm
  have hpos : ∀ j, P (X 0 ⁻¹' E' j) ≠ 0 := fun j => by
    rw [hPE _ (hE'm j)]
    exact fun h0 => hj0 (measure_mono_null (hEmono (Nat.le_add_left j0 j)) h0)
  have hcov : ∀ᵐ ζ ∂P, ∃ j, X 0 ζ ∈ E' j := by
    refine ae_of_ae_map hX0m.aemeasurable (p := fun Z => ∃ j, Z ∈ E' j) ?_
    filter_upwards [hex] with Z ⟨k, hk⟩
    exact ⟨k, show μ₀.rnDeriv R Z ≤ ((k + j0 : ℕ) : ℝ≥0∞) from hk.trans (Nat.cast_le.2 (Nat.le_add_right k j0))⟩
  have hcond : ∀ j, SbMovEnt D N T ρ (cond P (X 0 ⁻¹' E' j)) (X 0) X := by
    intro j
    have hp := hpos j
    set p : ℝ≥0∞ := P (X 0 ⁻¹' E' j) with hpdef
    have hmapc := sb1_cond_map_eq P hX0m (hE'm j)
    have hmom : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂((cond P (X 0 ⁻¹' E' j)).map (X 0)) < ⊤ := by
      rw [hmapc, lintegral_smul_measure]
      exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hp))
        (lt_of_le_of_lt (lintegral_mono' Measure.restrict_le_self le_rfl) hmom0)
    refine sb1_bdd_movEnt_cond H h.gradient hTp hN1 hβ hcV hconf K hKi hK hX' hF hX0m (hE'm j) hp hmom
      ((p⁻¹ * ((j + j0 : ℕ) : ℝ≥0∞)).toReal) ENNReal.toReal_nonneg ?_ η A3 A4 hη hη0 hA3 hA4 hB
    have hfin : p⁻¹ * ((j + j0 : ℕ) : ℝ≥0∞) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hp) (ENNReal.natCast_ne_top _)
    rw [hmapc, ENNReal.ofReal_toReal hfin, mul_smul]
    refine Measure.le_iff.2 fun t ht => ?_
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul' le_rfl (Measure.le_iff'.1 (hEb (j + j0)).2 t)
  exact sb1_uncondition H hT hN1 hβ K hKi hK hco hXm hX0m (Eventually.of_forall fun _ => rfl) hnc hE'm hE'mono hpos hcov
    hcond

end HRS.MS.MfeConf
