import HRS.Whole.Round2
import HRS.Whole.Orbits
import HRS.Energy.StaticLimitJoint
import HRS.Prob.Edgeworth
import HRS.MC.E213TElem

/-!
# S11IID, helper file 1: the iid Edgeworth core on the product space `(ℕ → ℝ^d) × H`

Generic Hilbert-space part (`s11iid_core`): for `Y : ℝ^d → H` continuous, bounded, `μ`-centered, with uniformly
summable coordinate squares along a Hilbert basis, and a centered Gaussian `G` on `H` with the covariance of `Y#μ`,
the Hilbert-space Edgeworth expansion `HRS.hilbert_edgeworth_C4` (on `((ℕ → ℝ^d) × H, μ^{⊗ℕ} ⊗ G)`, `C_b^5 ⊆ C_b^4`)
gives the normalised statement for `Ssum Y N` under `μ^{⊗N}`.  The proof follows the periodic case
`HRS/MC/S7S7z.lean` (`gamma = 0` of `static_field`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace HRS.Whole

open HRS.StaticLimitAux

section Generic

variable {d : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- The product probability space `((ℕ → ℝ^d) × H, μ^{⊗ℕ} ⊗ G)`. -/
abbrev s11iid_P (μ : Measure (Euc d)) (G : Measure H) : Measure ((ℕ → Euc d) × H) :=
  (Pinf μ).prod G

section Space

variable (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (G : Measure H)
  [IsProbabilityMeasure G] {Y : Euc d → H} (hY : Measurable Y)

theorem s11iid_map_fst : (s11iid_P μ G).map Prod.fst = Pinf μ := by
  simp [s11iid_P]

theorem s11iid_map_snd : (s11iid_P μ G).map Prod.snd = G := by
  simp [s11iid_P]

include hY in
theorem s11iid_law_X (i : ℕ) :
    HRS.law (s11iid_P μ G) (fun ω => Y (ω.1 i)) = μ.map Y := by
  have h : (fun ω : (ℕ → Euc d) × H => Y (ω.1 i)) = Xi Y i ∘ Prod.fst := rfl
  unfold HRS.law
  rw [h, ← Measure.map_map (measurable_Xi hY i) measurable_fst, s11iid_map_fst]
  exact law_Xi μ hY i

include hY in
theorem s11iid_iid :
    HRS.IsIIDCopies (s11iid_P μ G) (fun (i : ℕ) (ω : (ℕ → Euc d) × H) => Y (ω.1 i)) := by
  refine ⟨?_, fun i j => by rw [s11iid_law_X μ G hY i, s11iid_law_X μ G hY j]⟩
  have h := (iid_Xi μ hY (H := H)).1
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro S sets hsets
  have e1 : (⋂ i ∈ S, (fun ω : (ℕ → Euc d) × H => Y (ω.1 i)) ⁻¹' sets i) =
      Prod.fst ⁻¹' (⋂ i ∈ S, Xi Y i ⁻¹' sets i) := by
    ext ω; simp [Xi]
  have e2 : ∀ i, (fun ω : (ℕ → Euc d) × H => Y (ω.1 i)) ⁻¹' sets i =
      Prod.fst ⁻¹' (Xi Y i ⁻¹' sets i) := fun i => rfl
  have hm1 : MeasurableSet (⋂ i ∈ S, Xi Y i ⁻¹' sets i) :=
    MeasurableSet.biInter S.countable_toSet fun i hi => measurable_Xi hY i (hsets i hi)
  rw [e1, ← Measure.map_apply measurable_fst hm1, s11iid_map_fst]
  simp_rw [e2]
  rw [Finset.prod_congr rfl fun i hi => by
    rw [← Measure.map_apply measurable_fst (measurable_Xi hY i (hsets i hi)), s11iid_map_fst]]
  exact h S hsets

include hY in
theorem s11iid_integral_sum (Φ : H → ℝ) (hΦ : Continuous Φ) (N : ℕ) :
    ∫ ω, Φ ((Real.sqrt N)⁻¹ • ∑ i : Fin N, Y (ω.1 i)) ∂(s11iid_P μ G) =
      ∫ z, Φ (Ssum Y N z) ∂(Measure.pi fun _ : Fin N => μ) := by
  have hr : Measurable (fun (ω : ℕ → Euc d) (j : Fin N) => ω j) :=
    Measurable.of_eval fun j => measurable_pi_apply _
  have hT : Measurable (fun (ω : (ℕ → Euc d) × H) (j : Fin N) => ω.1 j) :=
    hr.comp measurable_fst
  have hmap : (s11iid_P μ G).map (fun (ω : (ℕ → Euc d) × H) (j : Fin N) => ω.1 j) =
      Measure.pi fun _ : Fin N => μ := by
    rw [show (fun (ω : (ℕ → Euc d) × H) (j : Fin N) => ω.1 j) =
      (fun (ω : ℕ → Euc d) (j : Fin N) => ω j) ∘ Prod.fst from rfl,
      ← Measure.map_map hr measurable_fst, s11iid_map_fst]
    exact map_restrict_eq μ N
  rw [← hmap]
  exact (integral_map hT.aemeasurable
    ((hΦ.measurable.comp (measurable_Ssum' hY N)).aestronglyMeasurable)).symm

theorem s11iid_integral_snd (Φ : H → ℝ) (hΦ : Continuous Φ) :
    ∫ ω, Φ ω.2 ∂(s11iid_P μ G) = ∫ F, Φ F ∂G := by
  rw [← s11iid_map_snd μ G, integral_map measurable_snd.aemeasurable hΦ.aestronglyMeasurable]
  rw [s11iid_map_snd]

theorem s11iid_third (hYc : Continuous Y) {C : ℝ} (hC : ∀ x, ‖Y x‖ ≤ C) {Φ : H → ℝ}
    (hΦ : Φ ∈ CbUnitBall H 3) :
    thirdMomentPairing (s11iid_P μ G) Φ (fun ω => ω.2) (fun ω => Y (ω.1 0)) =
      ∫ F, ∫ x, iteratedFDeriv ℝ 3 Φ F ![Y x, Y x, Y x] ∂μ ∂G := by
  set f : H × Euc d → ℝ := fun q => iteratedFDeriv ℝ 3 Φ q.1 ![Y q.2, Y q.2, Y q.2]
    with hf
  have hcont : Continuous f := by
    have h1 : Continuous fun q : H × Euc d => iteratedFDeriv ℝ 3 Φ q.1 :=
      (hΦ.1.continuous_iteratedFDeriv (by norm_num)).comp continuous_fst
    have hv : Continuous fun q : H × Euc d => (![Y q.2, Y q.2, Y q.2] : Fin 3 → H) := by
      refine continuous_pi fun i => ?_
      fin_cases i <;> exact hYc.comp continuous_snd
    exact h1.eval hv
  have hb : ∀ q, ‖f q‖ ≤ C ^ 3 := fun q => by
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    have h1 := iteratedFDeriv_norm_le_of_mem hΦ (le_refl 3) q.1
    have h2 : ∏ i, ‖(![Y q.2, Y q.2, Y q.2] : Fin 3 → H) i‖ ≤ C ^ 3 := by
      simp only [Fin.prod_univ_three]
      have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC q.2)
      have := hC q.2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      calc ‖Y q.2‖ * ‖Y q.2‖ * ‖Y q.2‖ ≤ C * C * C := by gcongr
        _ = C ^ 3 := by ring
    calc _ ≤ 1 * C ^ 3 := mul_le_mul h1 h2 (Finset.prod_nonneg fun i _ => norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hint : Integrable f (G.prod μ) :=
    Integrable.of_bound hcont.aestronglyMeasurable (C ^ 3) (Filter.Eventually.of_forall hb)
  have hev : Measurable (fun ω : (ℕ → Euc d) × H => ω.1 0) :=
    (measurable_pi_apply 0).comp measurable_fst
  have hT : Measurable (Prod.map (Prod.snd : (ℕ → Euc d) × H → H)
      (fun ω : (ℕ → Euc d) × H => ω.1 0)) := measurable_snd.prodMap hev
  have hmap : ((s11iid_P μ G).prod (s11iid_P μ G)).map
      (Prod.map (Prod.snd : (ℕ → Euc d) × H → H)
        (fun ω : (ℕ → Euc d) × H => ω.1 0)) = G.prod μ := by
    rw [← Measure.map_prod_map _ _ measurable_snd hev, s11iid_map_snd]
    congr 1
    rw [show (fun ω : (ℕ → Euc d) × H => ω.1 0) = (fun ω : ℕ → Euc d => ω 0) ∘ Prod.fst
      from rfl, ← Measure.map_map (measurable_pi_apply 0) measurable_fst, s11iid_map_fst]
    exact Measure.infinitePi_map_eval (μ := fun _ : ℕ => μ) 0
  unfold thirdMomentPairing
  change ∫ p, f (Prod.map Prod.snd (fun ω : (ℕ → Euc d) × H => ω.1 0) p) ∂_ = _
  rw [← integral_map hT.aemeasurable hcont.aestronglyMeasurable, hmap, integral_prod _ hint]

end Space

theorem s11iid_alg (a b t ε s : ℝ) (hs : 0 < s) (h : |a - b - 1 / (6 * s) * t| ≤ ε / s) :
    |s * (a - b) - 1 / 6 * t| ≤ ε := by
  have e : s * (a - b) - 1 / 6 * t = s * (a - b - 1 / (6 * s) * t) := by
    field_simp
  rw [e, abs_mul, abs_of_pos hs]
  calc s * |a - b - 1 / (6 * s) * t| ≤ s * (ε / s) := mul_le_mul_of_nonneg_left h hs.le
    _ = ε := by field_simp

/-- Uniform tails of the coordinate squares along a Hilbert basis, from a summable envelope. -/
theorem s11iid_tail (e : HilbertBasis ℕ ℝ H) (Y : Euc d → H) (w : ℕ → ℝ) (hw : Summable w)
    (hYw : ∀ n x, (inner ℝ (e n) (Y x)) ^ 2 ≤ w n) {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ x : Euc d, ∑' n : {n : ℕ // n₀ ≤ n}, (inner ℝ (e n) (Y x)) ^ 2 ≤ ε := by
  have ht := (tendsto_tsum_compl_atTop_zero w).comp tendsto_finset_range
  obtain ⟨n₀, hn₀⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  refine ⟨n₀, fun x => ?_⟩
  have e' : ∀ f : ℕ → ℝ, ∑' n : {n : ℕ // n₀ ≤ n}, f n.1 =
      ∑' k : {x : ℕ // x ∉ Finset.range n₀}, f k.1 :=
    fun f => (Equiv.tsum_eq (Equiv.subtypeEquivRight (fun x => by simp)) (fun b => f b.1)).symm
  rw [e' (fun n => (inner ℝ (e n) (Y x)) ^ 2)]
  refine le_trans ?_ hn₀.le
  refine Summable.tsum_le_tsum (fun k => hYw k.1 x) ?_ ?_
  · refine Summable.subtype (Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => hYw n x) hw) _
  · exact hw.subtype _

/-- **The iid Edgeworth core.** -/
theorem s11iid_core (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (e : HilbertBasis ℕ ℝ H)
    (Y : Euc d → H) (hYc : Continuous Y) (C : ℝ) (hC : ∀ x, ‖Y x‖ ≤ C)
    (hcent : ∫ x, Y x ∂μ = 0) (w : ℕ → ℝ) (hw : Summable w)
    (hYw : ∀ n x, (inner ℝ (e n) (Y x)) ^ 2 ≤ w n)
    (G : Measure H) [IsProbabilityMeasure G] (hGg : IsCenteredGaussian G)
    (hcov : ∀ x y, covarianceBilin G x y = covarianceBilin (μ.map Y) x y) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N → ∀ Φ ∈ CbUnitBall H 5,
      |Real.sqrt N * (∫ z, Φ (Ssum Y N z) ∂(Measure.pi fun _ : Fin N => μ) - ∫ F, Φ F ∂G) -
        (1 / 6) * ∫ F, ∫ x, iteratedFDeriv ℝ 3 Φ F ![Y x, Y x, Y x] ∂μ ∂G| ≤ ε := by
  intro ε hε
  have hYm : Measurable Y := hYc.measurable
  have hC0 : 0 ≤ C := by
    have := hC 0
    exact (norm_nonneg _).trans this
  have hX0m : Measurable (fun ω : (ℕ → Euc d) × H => Y (ω.1 0)) :=
    hYm.comp ((measurable_pi_apply 0).comp measurable_fst)
  have hcent' : ∫ ω, Y ((ω : (ℕ → Euc d) × H).1 0) ∂(s11iid_P μ G) = 0 := by
    have hh := integral_map (μ := s11iid_P μ G) measurable_fst.aemeasurable
      (measurable_Xi hYm 0).aestronglyMeasurable
    rw [s11iid_map_fst] at hh
    show ∫ ω, Xi Y 0 ω.1 ∂(s11iid_P μ G) = 0
    rw [← hh]
    have := integral_map (μ := Pinf μ) (measurable_pi_apply (0 : ℕ)).aemeasurable
      hYm.aestronglyMeasurable
    rw [Measure.infinitePi_map_eval (μ := fun _ : ℕ => μ) 0] at this
    show ∫ ω, Y (ω 0) ∂(Pinf μ) = 0
    rw [← this]
    exact hcent
  have hint4 : Integrable (fun ω : (ℕ → Euc d) × H => ‖Y (ω.1 0)‖ ^ 4) (s11iid_P μ G) :=
    Integrable.of_bound (hX0m.norm.pow_const 4).aestronglyMeasurable (C ^ 4)
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hC _) 4)
  have h4 : ∫ ω, ‖Y ((ω : (ℕ → Euc d) × H).1 0)‖ ^ 4 ∂(s11iid_P μ G) ≤ C ^ 4 := by
    calc _ ≤ ∫ _ω, C ^ 4 ∂(s11iid_P μ G) := integral_mono hint4 (integrable_const _)
          fun ω => pow_le_pow_left₀ (norm_nonneg _) (hC _) 4
      _ = C ^ 4 := by simp
  have htail : ∀ ε > 0, ∃ n₀ : ℕ, ∀ _a : Unit,
      ∫ ω, ∑' n : {n : ℕ // n₀ ≤ n}, (inner ℝ (e n) (Y ((ω : (ℕ → Euc d) × H).1 0))) ^ 2
        ∂(s11iid_P μ G) ≤ ε := by
    intro ε' hε'
    obtain ⟨n₀, hn₀⟩ := s11iid_tail e Y w hw hYw hε'
    refine ⟨n₀, fun _ => ?_⟩
    calc _ ≤ ∫ _ω, ε' ∂(s11iid_P μ G) := integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun ω => tsum_nonneg fun n => sq_nonneg _)
          (integrable_const _) (Filter.Eventually.of_forall fun ω => hn₀ _)
      _ = ε' := by simp
  have hGrv : IsCenteredGaussianRV (s11iid_P μ G) (fun ω : (ℕ → Euc d) × H => ω.2)
      fun x y => ProbabilityTheory.covarianceBilin
        (HRS.law (s11iid_P μ G) (fun ω : (ℕ → Euc d) × H => Y (ω.1 0))) x y := by
    have hlaw : HRS.law (s11iid_P μ G) (fun ω : (ℕ → Euc d) × H => ω.2) = G := by
      unfold HRS.law; exact s11iid_map_snd μ G
    refine ⟨measurable_snd.aemeasurable, ?_, fun x y => ?_⟩
    · rw [hlaw]; exact hGg
    · rw [hlaw, s11iid_law_X μ G hYm 0]
      exact hcov x y
  obtain ⟨N₀, hN₀⟩ := hilbert_edgeworth_C4 e (ι := Unit)
    (Ω := fun _ => (ℕ → Euc d) × H) (fun _ => s11iid_P μ G)
    (fun _ ω => Y (ω.1 0)) (fun _ => hX0m.aemeasurable) (fun _ => hcent') (C ^ 4)
    (fun _ => hint4) (fun _ => h4) htail (fun _ ω => ω.2) (fun _ => hGrv) ε hε
  refine ⟨N₀, fun N hN hN1 Φ hΦ => ?_⟩
  have hΦ4 : Φ ∈ CbUnitBall H 4 := cbUnitBall_anti (by norm_num) hΦ
  have hΦ3 : Φ ∈ CbUnitBall H 3 := cbUnitBall_anti (by norm_num) hΦ
  have hΦc : Continuous Φ := hΦ4.1.continuous
  have hiid : IsIIDCopies (s11iid_P μ G) (fun (i : Fin N) (ω : (ℕ → Euc d) × H) => Y (ω.1 i)) := by
    obtain ⟨h1, -⟩ := s11iid_iid μ G hYm
    exact ⟨h1.precomp Fin.val_injective, fun i j => by
      rw [s11iid_law_X μ G hYm, s11iid_law_X μ G hYm]⟩
  have h := hN₀ N hN () (fun i ω => Y (ω.1 i))
    (fun i => (hYm.comp ((measurable_pi_apply (i : ℕ)).comp measurable_fst)).aemeasurable) hiid
    (fun i => by rw [s11iid_law_X μ G hYm, s11iid_law_X μ G hYm]) Φ hΦ4
  rw [s11iid_integral_sum μ G hYm Φ hΦc N, s11iid_integral_snd μ G Φ hΦc,
    s11iid_third μ G hYc hC hΦ3] at h
  have hNpos : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN1)
  exact s11iid_alg _ _ _ _ _ hNpos h

end Generic


section Static

variable {d : ℕ}

theorem s11iid_prob {ρ : Euc d → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x = 1) :
    IsProbabilityMeasure (withDensityReal ρ) := by
  have hint : Integrable ρ volume := by
    by_contra h
    rw [integral_undef h] at hρ1
    exact zero_ne_one hρ1
  constructor
  unfold withDensityReal
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hρ0), hρ1]
  simp

/-- `ℓ_x = δ_x - μ ∈ B_M` (the iid summand at `γ = 0`). -/
def s11iid_Y (M : ℝ) (μ : Measure (Euc d)) (x : Euc d) : OscDual d M :=
  OscDual.ofMeasureDiff M (Measure.dirac x) μ

theorem s11iid_ell_eq (g : Euc d → ℝ) (μ : Measure (Euc d)) (m : ℕ) (x : Euc d) :
    r2EllPt g μ 0 m x = s11iid_Y (m : ℝ) μ x := by
  unfold r2EllPt s11iid_Y OscDual.ofMeasureDiff
  congr 1
  funext α
  simp [responseRepW, projMean, pair, measureHermiteCoeff]

variable {M : ℝ} (hM : (d : ℝ) < M) (μ : Measure (Euc d)) [IsProbabilityMeasure μ]

include hM in
theorem s11iid_hermiteCoeff_Y (x : Euc d) (α : MultiIndex d) :
    OscDual.hermiteCoeff (s11iid_Y M μ x) α = hermiteFunD α x - ∫ y, hermiteFunD α y ∂μ := by
  unfold s11iid_Y
  rw [OscDual.hermiteCoeff_ofMeasureDiff hM]
  simp [measureHermiteCoeff]

include hM in
theorem s11iid_coord_Y (x : Euc d) (α : MultiIndex d) :
    OscDual.coord (s11iid_Y M μ x) α =
      oscEigenvalue d α ^ (-(M / 2)) * (hermiteFunD α x - ∫ y, hermiteFunD α y ∂μ) := by
  rw [OscDual.coord_eq_mul, s11iid_hermiteCoeff_Y hM μ]

theorem s11iid_continuous_hermiteFunD (α : MultiIndex d) : Continuous (hermiteFunD α) := by
  unfold hermiteFunD
  refine continuous_finset_prod _ fun i _ => ?_
  exact (contDiff_hermiteFun (α i)).continuous.comp (by fun_prop)

include hM in
theorem s11iid_coord_sq_le : ∃ K : ℝ, ∀ (x : Euc d) (α : MultiIndex d),
    (OscDual.coord (s11iid_Y M μ x) α) ^ 2 ≤ K * oscEigenvalue d α ^ (-M) := by
  obtain ⟨C0, hC0⟩ := hermiteFunD_uniform_bound (d := d)
  refine ⟨(2 * C0) ^ 2, fun x α => ?_⟩
  have hmu : |∫ y, hermiteFunD α y ∂μ| ≤ C0 := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := hermiteFunD α) (C := C0)
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hC0 α y)
    simpa [Real.norm_eq_abs, Measure.real] using this
  have hc : |hermiteFunD α x - ∫ y, hermiteFunD α y ∂μ| ≤ 2 * C0 := by
    refine (abs_sub _ _).trans ?_
    linarith [hC0 α x]
  have h1 := OscDual.hermiteCoeff_sq (m := M) (s11iid_Y M μ x) α
  rw [s11iid_hermiteCoeff_Y hM μ] at h1
  rw [← h1]
  have h2 : (hermiteFunD α x - ∫ y, hermiteFunD α y ∂μ) ^ 2 ≤ (2 * C0) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hc 2
  have h3 := oscEv_pos (d := d) α
  have h4 : 0 < oscEigenvalue d α ^ (-M) := Real.rpow_pos_of_pos h3 _
  nlinarith

include hM in
theorem s11iid_norm_le : ∃ C : ℝ, ∀ x, ‖s11iid_Y M μ x‖ ≤ C := by
  obtain ⟨K, hK⟩ := s11iid_coord_sq_le hM μ
  have hs := (OscDual.summable_oscEv_neg_rpow (d := d) hM).mul_left K
  refine ⟨Real.sqrt (∑' α : MultiIndex d, K * oscEigenvalue d α ^ (-M)), fun x => ?_⟩
  rw [OscDual.norm_eq_coord]
  exact Real.sqrt_le_sqrt (Summable.tsum_le_tsum (fun α => hK x α)
    (OscDual.coord_sq_summable' _) hs)

include hM in
theorem s11iid_continuous : Continuous (s11iid_Y M μ) := by
  obtain ⟨K, hK⟩ := s11iid_coord_sq_le hM μ
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hb : Summable fun α : MultiIndex d => 4 * K * oscEigenvalue d α ^ (-M) := by
    have := (OscDual.summable_oscEv_neg_rpow (d := d) hM).mul_left (4 * K)
    exact this
  have key : Tendsto (fun x => ∑' α : MultiIndex d,
      (OscDual.coord (s11iid_Y M μ x) α - OscDual.coord (s11iid_Y M μ x₀) α) ^ 2)
      (𝓝 x₀) (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝 x₀)
      (f := fun (x : Euc d) (α : MultiIndex d) =>
        (OscDual.coord (s11iid_Y M μ x) α - OscDual.coord (s11iid_Y M μ x₀) α) ^ 2)
      (g := fun _ => (0 : ℝ)) (bound := fun α => 4 * K * oscEigenvalue d α ^ (-M)) hb
      (fun α => by
        have hc : Continuous fun x : Euc d => OscDual.coord (s11iid_Y M μ x) α := by
          simp_rw [s11iid_coord_Y hM μ]
          exact continuous_const.mul ((s11iid_continuous_hermiteFunD α).sub continuous_const)
        have h2 : Continuous fun x : Euc d =>
            (OscDual.coord (s11iid_Y M μ x) α - OscDual.coord (s11iid_Y M μ x₀) α) ^ 2 :=
          (hc.sub continuous_const).pow 2
        simpa using h2.tendsto x₀)
      (Filter.Eventually.of_forall fun x α => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have h1 := hK x α
        have h2 := hK x₀ α
        nlinarith [sq_nonneg (OscDual.coord (s11iid_Y M μ x) α + OscDual.coord (s11iid_Y M μ x₀) α)])
    simpa using this
  have e : (fun x => ‖s11iid_Y M μ x - s11iid_Y M μ x₀‖) = fun x => Real.sqrt (∑' α : MultiIndex d,
      (OscDual.coord (s11iid_Y M μ x) α - OscDual.coord (s11iid_Y M μ x₀) α) ^ 2) := by
    funext x
    rw [OscDual.norm_eq_coord]
    rfl
  rw [e]
  simpa using key.sqrt


/-! #### Hilbert basis of `B_M` indexed by `ℕ` -/

/-- The identity isometry `B_M ≃ ℓ²`. -/
def s11iid_repr (d : ℕ) (M : ℝ) : OscDual d M ≃ₗᵢ[ℝ] lp (fun _ : MultiIndex d => ℝ) 2 where
  toFun := id
  invFun := id
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  norm_map' := fun _ => rfl

/-- The standard Hilbert basis of `B_M` indexed by multi-indices. -/
def s11iid_basis0 (d : ℕ) (M : ℝ) : HilbertBasis (MultiIndex d) ℝ (OscDual d M) :=
  HilbertBasis.ofRepr (s11iid_repr d M)

theorem s11iid_basis0_apply (M : ℝ) (α : MultiIndex d) :
    (s11iid_basis0 d M α : OscDual d M) =
      (show OscDual d M from lp.single (E := fun _ : MultiIndex d => ℝ) 2 α (1 : ℝ)) := by
  classical
  rw [← HilbertBasis.repr_symm_single]; rfl

/-- A Hilbert basis indexed by `ℕ` (reindexing by `σ`). -/
def s11iid_basis (M : ℝ) (σ : ℕ ≃ MultiIndex d) : HilbertBasis ℕ ℝ (OscDual d M) :=
  HilbertBasis.mk (v := fun n => (s11iid_basis0 d M (σ n) : OscDual d M))
    ((s11iid_basis0 d M).orthonormal.comp σ σ.injective) (by
      have h := (s11iid_basis0 d M).dense_span
      have e : Set.range (fun n => (s11iid_basis0 d M (σ n) : OscDual d M)) =
          Set.range (s11iid_basis0 d M) := σ.surjective.range_comp (s11iid_basis0 d M)
      rw [e, h])

theorem s11iid_inner_basis (M : ℝ) (σ : ℕ ≃ MultiIndex d) (n : ℕ) (u : OscDual d M) :
    inner ℝ (s11iid_basis M σ n) u = OscDual.coord u (σ n) := by
  rw [s11iid_basis, HilbertBasis.coe_mk, s11iid_basis0_apply]
  show inner ℝ (lp.single (E := fun _ : MultiIndex d => ℝ) 2 (σ n) (1 : ℝ))
    (show lp (fun _ : MultiIndex d => ℝ) 2 from u) = _
  rw [lp.inner_single_left]
  simp [OscDual.coord]

theorem s11iid_coord_eq_inner (M : ℝ) (α : MultiIndex d) (u : OscDual d M) :
    OscDual.coord u α = inner ℝ (show OscDual d M from lp.single (E := fun _ : MultiIndex d => ℝ) 2 α (1 : ℝ)) u := by
  show _ = inner ℝ (lp.single (E := fun _ : MultiIndex d => ℝ) 2 α (1 : ℝ))
    (show lp (fun _ : MultiIndex d => ℝ) 2 from u)
  rw [lp.inner_single_left]
  simp [OscDual.coord]

theorem s11iid_exists_equiv (hd : 1 ≤ d) : Nonempty (ℕ ≃ MultiIndex d) := by
  haveI : Infinite (MultiIndex d) := by
    refine Infinite.of_injective (fun n : ℕ => (Pi.single (⟨0, by omega⟩ : Fin d) n : MultiIndex d)) ?_
    intro a b hab
    have := congrFun hab ⟨0, by omega⟩
    simpa using this
  exact nonempty_equiv_of_countable

include hM in
theorem s11iid_integral_Y : ∫ x, s11iid_Y M μ x ∂μ = 0 := by
  have hcont := s11iid_continuous hM μ
  obtain ⟨C, hC⟩ := s11iid_norm_le hM μ
  have hint : Integrable (s11iid_Y M μ) μ :=
    Integrable.of_bound hcont.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  obtain ⟨C0, hC0⟩ := hermiteFunD_uniform_bound (d := d)
  have hco : ∀ α, OscDual.coord (∫ x, s11iid_Y M μ x ∂μ) α = 0 := by
    intro α
    rw [s11iid_coord_eq_inner, ← integral_inner hint]
    simp_rw [← s11iid_coord_eq_inner, s11iid_coord_Y hM μ]
    have hi : Integrable (hermiteFunD α) μ :=
      Integrable.of_bound (s11iid_continuous_hermiteFunD α).aestronglyMeasurable C0
        (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hC0 α y)
    rw [integral_const_mul, integral_sub hi (integrable_const _)]
    simp
  have : (∫ x, s11iid_Y M μ x ∂μ) = 0 := by
    refine lp.ext (funext fun α => ?_)
    exact hco α
  exact this


/-! #### The Gaussian, the susceptibility covariance at `γ = 0` -/

include hM in
theorem s11iid_exists_gaussian : ∃ G : Measure (OscDual d M), IsProbabilityMeasure G ∧
    IsCenteredGaussian G ∧
    ∀ x y, covarianceBilin G x y = covarianceBilin (μ.map (s11iid_Y M μ)) x y := by
  have hcont := s11iid_continuous hM μ
  obtain ⟨C, hC⟩ := s11iid_norm_le hM μ
  have hYL : MemLp (s11iid_Y M μ) 2 μ :=
    MemLp.of_bound hcont.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  obtain ⟨htc, -⟩ := HRS.isTraceClassCov_covarianceBilin μ (s11iid_Y M μ) hYL
    (s11iid_integral_Y hM μ)
  obtain ⟨γ, hp, hg, hcov⟩ := HRS.exists_centeredGaussian_of_traceClass _ htc
  exact ⟨γ, hp, hg, hcov⟩

theorem s11iid_resp_ae (g : Euc d → ℝ) {ψ : Euc d → ℝ} (hψc : Continuous ψ) {C : ℝ}
    (hC : ∀ x, |ψ x| ≤ C) : responseInverse g μ 0 ψ =ᵐ[μ] projMean μ ψ := by
  have hint : Integrable ψ μ :=
    Integrable.of_bound hψc.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)
  have hpair : |pair μ ψ| ≤ C := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := ψ) (C := C)
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hC y)
    simpa [pair, Real.norm_eq_abs, Measure.real] using this
  have hres : IsResponse g μ 0 ψ (projMean μ ψ) := by
    refine ⟨⟨?_, ?_⟩, Filter.Eventually.of_forall fun x => by simp⟩
    · refine MemLp.of_bound (hψc.sub continuous_const).aestronglyMeasurable (C + C)
        (Filter.Eventually.of_forall fun x => ?_)
      show ‖ψ x - pair μ ψ‖ ≤ C + C
      rw [Real.norm_eq_abs]
      exact (abs_sub _ _).trans (add_le_add (hC x) hpair)
    · show ∫ x, (ψ x - pair μ ψ) ∂μ = 0
      rw [integral_sub hint (integrable_const _)]
      simp [pair]
  have hex : ∃ h, IsResponse g μ 0 ψ h := ⟨_, hres⟩
  unfold responseInverse
  rw [dif_pos hex]
  filter_upwards [hex.choose_spec.2] with x hx
  simpa using hx

theorem s11iid_susc (g : Euc d → ℝ) (α β : MultiIndex d) :
    susceptibilityCov g μ 0 (hermiteFunD α) (hermiteFunD β) =
      ∫ x, (hermiteFunD α x - ∫ y, hermiteFunD α y ∂μ) *
        (hermiteFunD β x - ∫ y, hermiteFunD β y ∂μ) ∂μ := by
  obtain ⟨C0, hC0⟩ := hermiteFunD_uniform_bound (d := d)
  have h := s11iid_resp_ae μ g (s11iid_continuous_hermiteFunD β) (C := C0) (fun x => hC0 β x)
  unfold susceptibilityCov l2Inner
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]
  simp [projMean, pair]

include hM in
theorem s11iid_osc (g : Euc d → ℝ) (G : Measure (OscDual d M)) [IsProbabilityMeasure G]
    (hg : IsCenteredGaussian G)
    (hcov : ∀ x y, covarianceBilin G x y = covarianceBilin (μ.map (s11iid_Y M μ)) x y) :
    IsCenteredGaussianOsc M G (susceptibilityCov g μ 0) := by
  refine ⟨hg, fun α β => ?_⟩
  haveI := hg.1
  have hcont := s11iid_continuous hM μ
  obtain ⟨C, hC⟩ := s11iid_norm_le hM μ
  have hYae : AEMeasurable (s11iid_Y M μ) μ := hcont.aemeasurable
  have hYL : MemLp (s11iid_Y M μ) 2 μ :=
    MemLp.of_bound hcont.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  have hmem : MemLp id 2 G := ProbabilityTheory.IsGaussian.memLp_two_id
  have hn : Integrable (fun z : OscDual d M => ‖z‖ ^ 2) G := by
    have := hmem.integrable_norm_pow (p := 2) (by norm_num)
    simpa using this
  set a : OscDual d M := (oscEigenvalue d α ^ (M / 2)) •
    (show OscDual d M from lp.single (E := fun _ : MultiIndex d => ℝ) 2 α (1 : ℝ)) with ha
  set b : OscDual d M := (oscEigenvalue d β ^ (M / 2)) •
    (show OscDual d M from lp.single (E := fun _ : MultiIndex d => ℝ) 2 β (1 : ℝ)) with hb
  have hca : ∀ F : OscDual d M, OscDual.hermiteCoeff F α = inner ℝ a F := by
    intro F
    rw [ha, real_inner_smul_left, ← s11iid_coord_eq_inner]
    rfl
  have hcb : ∀ F : OscDual d M, OscDual.hermiteCoeff F β = inner ℝ b F := by
    intro F
    rw [hb, real_inner_smul_left, ← s11iid_coord_eq_inner]
    rfl
  simp_rw [hca, hcb]
  have hint : Integrable (fun F : OscDual d M => inner ℝ a F * inner ℝ b F) G := by
    refine (hn.const_mul (‖a‖ * ‖b‖)).mono' ?_ (Filter.Eventually.of_forall fun F => ?_)
    · exact ((continuous_const.inner continuous_id).mul
        (continuous_const.inner continuous_id)).aestronglyMeasurable
    · rw [norm_mul]
      calc ‖inner ℝ a F‖ * ‖inner ℝ b F‖ ≤ (‖a‖ * ‖F‖) * (‖b‖ * ‖F‖) :=
            mul_le_mul (norm_inner_le_norm _ _) (norm_inner_le_norm _ _) (norm_nonneg _)
              (by positivity)
        _ = ‖a‖ * ‖b‖ * ‖F‖ ^ 2 := by ring
  refine ⟨hint, ?_⟩
  have h1 : ∫ F, inner ℝ a F * inner ℝ b F ∂G = covarianceBilin G a b := by
    rw [covarianceBilin_apply hmem, HRS.HilbertCLTAux.gaussian_mean_zero hg]
    simp
  have hmemY : MemLp id 2 (μ.map (s11iid_Y M μ)) :=
    (memLp_map_measure_iff aestronglyMeasurable_id hYae).mpr hYL
  have hmean : (μ.map (s11iid_Y M μ))[id] = 0 := by
    show ∫ z, id z ∂(μ.map (s11iid_Y M μ)) = 0
    rw [integral_map hYae aestronglyMeasurable_id]
    exact s11iid_integral_Y hM μ
  have h2 : covarianceBilin (μ.map (s11iid_Y M μ)) a b =
      ∫ x, inner ℝ a (s11iid_Y M μ x) * inner ℝ b (s11iid_Y M μ x) ∂μ := by
    rw [covarianceBilin_apply hmemY, hmean]
    simp only [sub_zero]
    rw [integral_map hYae (by fun_prop)]
  rw [h1, hcov, h2, s11iid_susc μ g α β]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [← hca, ← hcb, s11iid_hermiteCoeff_Y hM μ, s11iid_hermiteCoeff_Y hM μ]


include hM in
theorem s11iid_tensor : ∃ K : projTensor (OscDual d M) 3, ∀ T : (OscDual d M) [×3]→L[ℝ] ℝ,
    (K : TensorDual (OscDual d M) 3) T =
      ∫ x, T ![s11iid_Y M μ x, s11iid_Y M μ x, s11iid_Y M μ x] ∂μ := by
  have hcont := s11iid_continuous hM μ
  obtain ⟨C, hC⟩ := s11iid_norm_le hM μ
  have hasm : AEStronglyMeasurable (s11iid_Y M μ) μ := hcont.aestronglyMeasurable
  have hint : Integrable (fun x => ‖s11iid_Y M μ x‖ * ‖s11iid_Y M μ x‖ * ‖s11iid_Y M μ x‖) μ := by
    refine Integrable.of_bound (C := C * C * C) ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact ((hcont.norm.mul hcont.norm).mul hcont.norm).aestronglyMeasurable
    · have h0 : 0 ≤ ‖s11iid_Y M μ x‖ := norm_nonneg _
      have h1 := hC x
      have hC0 : 0 ≤ C := h0.trans h1
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      gcongr
  refine ⟨⟨HRS.MC.E213T.bochTensor3 μ (s11iid_Y M μ) (s11iid_Y M μ) (s11iid_Y M μ),
    HRS.MC.E213T.bochTensor3_mem hasm hasm hasm hint⟩, fun T => ?_⟩
  exact HRS.MC.E213T.bochTensor3_apply hasm hasm hasm hint T

end Static

section Zeta

variable {d : ℕ}

theorem s11iid_gibbs_zero (g : Euc d → ℝ) (N : ℕ) (μ : Measure (Euc d)) [IsProbabilityMeasure μ] :
    modulatedGibbs g N 0 μ = Measure.pi fun _ : Fin N => μ := by
  have h1 : gibbsNormalizer g N 0 μ = 1 := by
    unfold gibbsNormalizer
    simp
  unfold modulatedGibbs
  rw [h1]
  simp

theorem s11iid_meanEmpirical_pi (N : ℕ) (hN : 1 ≤ N) (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] : meanEmpirical (Measure.pi fun _ : Fin N => μ) = μ := by
  ext A hA
  rw [meanEmpirical_apply _ hA]
  have h : ∀ i : Fin N, (Measure.pi fun _ : Fin N => μ) {X | X i ∈ A} = μ A := fun i => by
    have h := Measure.pi_map_eval (μ := fun _ : Fin N => μ) i
    simp only [measure_univ, Finset.prod_const_one, one_smul] at h
    have h2 := congrArg (fun ν : Measure (Euc d) => ν A) h
    rw [Measure.map_apply (measurable_pi_apply i) hA] at h2
    exact h2
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact ENNReal.inv_mul_cancel_left (by exact_mod_cast (show N ≠ 0 by omega))
    (ENNReal.natCast_ne_top N)

theorem s11iid_hermiteCoeff_sum {M : ℝ} {ι : Type*} (s : Finset ι) (u : ι → OscDual d M)
    (α : MultiIndex d) :
    OscDual.hermiteCoeff (∑ i ∈ s, u i) α = ∑ i ∈ s, OscDual.hermiteCoeff (u i) α := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := OscDual.hermiteCoeff_smul (0 : ℝ) (0 : OscDual d M) α
    simp only [smul_zero, zero_mul] at h
    simp [h]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, OscDual.hermiteCoeff_add, ih, Finset.sum_insert ha]

theorem s11iid_zeta_eq {M : ℝ} (hM : (d : ℝ) < M) (N : ℕ) (hN : 1 ≤ N) (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] (z : EucConfig d N) :
    zetaB M (Measure.pi fun _ : Fin N => μ) z = Ssum (s11iid_Y M μ) N z := by
  unfold zetaB Ssum
  rw [s11iid_meanEmpirical_pi N hN μ]
  have := empirical_isProbabilityMeasure (Nat.pos_of_ne_zero (by omega : N ≠ 0)) z
  refine OscDual.ext_hermiteCoeff fun α => ?_
  rw [OscDual.hermiteCoeff_smul, OscDual.hermiteCoeff_ofMeasureDiff hM,
    OscDual.hermiteCoeff_smul, s11iid_hermiteCoeff_sum]
  simp_rw [s11iid_hermiteCoeff_Y hM μ]
  have hp := pair_empirical (Nat.pos_of_ne_zero (by omega : N ≠ 0)) z (hermiteFunD α)
  have hp' : measureHermiteCoeff (empirical z) α = (N : ℝ)⁻¹ * ∑ i, hermiteFunD α (z i) := hp
  rw [hp', Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hr : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
  have hr0 : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  unfold measureHermiteCoeff
  generalize Real.sqrt (N : ℝ) = r at hr hr0 ⊢
  rw [← hr]
  field_simp

end Zeta

section Assembly

variable {d : ℕ}

/-- **The static iid row at `γ = 0`.** -/
theorem s11iid_static (hd : 2 ≤ d) (m : ℕ) (hm : ((4 * d + 40 : ℕ) : ℝ) + 2 * d + 4 < m)
    (ρ : Euc d → ℝ) (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x = 1) :
    R2StaticEdgeworth d 0 0 m ρ := by
  have hM : (d : ℝ) < (m : ℝ) := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    push_cast at hm
    linarith
  have hμ := s11iid_prob hρ0 hρ1
  unfold R2StaticEdgeworth
  set μ := withDensityReal ρ with hμdef
  obtain ⟨G, hGp, hGg, hGcov⟩ := s11iid_exists_gaussian hM μ
  have := hGp
  have hcont := s11iid_continuous hM μ
  obtain ⟨C, hC⟩ := s11iid_norm_le hM μ
  obtain ⟨K, hK⟩ := s11iid_coord_sq_le hM μ
  obtain ⟨σ⟩ := s11iid_exists_equiv (by omega : 1 ≤ d)
  have hw : Summable fun n => K * oscEigenvalue d (σ n) ^ (-(m : ℝ)) :=
    ((OscDual.summable_oscEv_neg_rpow hM).mul_left K).comp_injective σ.injective
  have hcore := s11iid_core μ (s11iid_basis (m : ℝ) σ) (s11iid_Y (m : ℝ) μ) hcont C hC
    (s11iid_integral_Y hM μ) _ hw
    (fun n x => by rw [s11iid_inner_basis]; exact hK x (σ n)) G hGg hGcov
  refine ⟨G, hGp, s11iid_osc hM μ _ G hGg hGcov, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨C, fun x => by rw [s11iid_ell_eq]; exact hC x⟩
  · intro α
    simp only [s11iid_ell_eq]
    simp_rw [s11iid_coord_Y hM μ]
    exact continuous_const.mul ((s11iid_continuous_hermiteFunD α).sub continuous_const)
  · simp only [s11iid_ell_eq]
    exact s11iid_tensor hM μ
  · intro N hN2
    rw [s11iid_gibbs_zero]
    have : zetaB (m : ℝ) (Measure.pi fun _ : Fin N => μ) = Ssum (s11iid_Y (m : ℝ) μ) N :=
      funext (s11iid_zeta_eq hM N (by omega) μ)
    rw [this]
    exact measurable_Ssum' hcont.measurable N
  · intro ε hε
    obtain ⟨N₀, hN₀⟩ := hcore ε hε
    refine ⟨max N₀ 2, fun N hN hN2 Φ hΦ => ?_⟩
    have h := hN₀ N (le_trans (le_max_left _ _) hN) (by omega) Φ hΦ
    have e1 : ∫ X, Φ (zetaB (m : ℝ) (modulatedGibbs (rieszKernel d 0) N 0 μ) X)
        ∂(modulatedGibbs (rieszKernel d 0) N 0 μ) =
        ∫ z, Φ (Ssum (s11iid_Y (m : ℝ) μ) N z) ∂(Measure.pi fun _ : Fin N => μ) := by
      rw [s11iid_gibbs_zero]
      congr 1
      funext X
      rw [s11iid_zeta_eq hM N (by omega) μ X]
    simp only [s11iid_ell_eq]
    rw [e1]
    exact h

end Assembly

end HRS.Whole
