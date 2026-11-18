import HRS.MC.S7S7zAux3
import HRS.Prob.Edgeworth

/-!
# Packet `s7_S7z_product_case`: the case `gamma = 0` of `static_field` is `hilbert_edgeworth_C4`

`modulatedGibbs .. 0 .. = mu^{(x)N}`, `zeta_N = N^{-1/2} sum_i (delta_{x_i} - mu)` in `E_r`, `ellPt .. 0 r x = delta_x - mu`;
apply Lemma 7.1 (`hilbert_edgeworth_C4`) on `((N -> T^d) x E_r, Pinf mu (x) G)`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.Sec7.S7z

open HRS HRS.Sec7 HRS.StaticLimitAux

variable {d : ℕ} {r : ℝ}

/-- A Hilbert basis of `E_r` indexed by `ℕ`. -/
def s7z_basis (σ : ℕ ≃ NonzeroLattice d) (r : ℝ) : HilbertBasis ℕ ℝ (NegSobolev d r) :=
  HilbertBasis.mk (v := fun n => (negBasis d r (σ n) : NegSobolev d r))
    ((negBasis d r).orthonormal.comp σ σ.injective) (by
      have h := (negBasis d r).dense_span
      have e : Set.range (fun n => (negBasis d r (σ n) : NegSobolev d r)) =
          Set.range (negBasis d r) := σ.surjective.range_comp (negBasis d r)
      rw [e, h])

theorem s7z_inner_basis (σ : ℕ ≃ NonzeroLattice d) (n : ℕ) (F : NegSobolev d r) :
    ⟪(s7z_basis σ r) n, F⟫ = NegSobolev.coord F (σ n) := by
  rw [s7z_basis, HilbertBasis.coe_mk, negBasis_apply]
  show ⟪lp.single 2 (σ n) (1 : ℝ), (show lp (fun _ : NonzeroLattice d => ℝ) 2 from F)⟫ = _
  rw [lp.inner_single_left]
  simp [NegSobolev.coord]

theorem s7z_exists_equiv (hd : 1 ≤ d) : Nonempty (ℕ ≃ NonzeroLattice d) := by
  haveI : Infinite (NonzeroLattice d) := by
    refine Infinite.of_injective (fun n : ℕ => (⟨Pi.single ⟨0, by omega⟩ ((n : ℤ) + 1), by
      intro h
      have := congrFun h ⟨0, by omega⟩
      simp at this
      omega⟩ : NonzeroLattice d)) ?_
    intro a b hab
    have := congrFun (congrArg Subtype.val hab) ⟨0, by omega⟩
    simp at this
    exact_mod_cast this
  exact nonempty_equiv_of_countable

theorem s7z_tail (hm : (d : ℝ) < 2 * r) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (σ : ℕ ≃ NonzeroLattice d) {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ x : Torus d,
      ∑' n : {n : ℕ // n₀ ≤ n}, ⟪(s7z_basis σ r) n.1, Ye r μ x⟫ ^ 2 ≤ ε := by
  set w : ℕ → ℝ := fun n => 8 * Lattice.jp (σ n).1 ^ (-(2 * r)) with hw
  have hws : Summable w :=
    ((summable_jp_rpow (d := d) r hm).comp_injective σ.injective).mul_left 8
  have ht := (tendsto_tsum_compl_atTop_zero w).comp tendsto_finset_range
  obtain ⟨n₀, hn₀⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  refine ⟨n₀, fun x => ?_⟩
  have e : ∀ f : ℕ → ℝ, ∑' n : {n : ℕ // n₀ ≤ n}, f n.1 = ∑' k : {x : ℕ // x ∉ Finset.range n₀}, f k.1 :=
    fun f => (Equiv.tsum_eq (Equiv.subtypeEquivRight (fun x => by simp)) (fun b => f b.1)).symm
  rw [e (fun n => ⟪(s7z_basis σ r) n, Ye r μ x⟫ ^ 2)]
  refine le_trans ?_ hn₀.le
  have hle : ∀ n, ⟪(s7z_basis σ r) n, Ye r μ x⟫ ^ 2 ≤ w n := fun n => by
    rw [s7z_inner_basis]
    exact coord_sq_le_ofMeasureDiff hm (Measure.dirac x) μ (σ n)
  refine Summable.tsum_le_tsum (fun k => hle k.1) ?_ ?_
  · refine Summable.subtype (Summable.of_nonneg_of_le (fun n => sq_nonneg _) hle hws) _
  · exact hws.subtype _

theorem s7z_alg (a b t ε s : ℝ) (hs : 0 < s) (h : |a - b - 1 / (6 * s) * t| ≤ ε / s) :
    |s * (a - b) - 1 / 6 * t| ≤ ε := by
  have e : s * (a - b) - 1 / 6 * t = s * (a - b - 1 / (6 * s) * t) := by
    field_simp
  rw [e, abs_mul, abs_of_pos hs]
  calc s * |a - b - 1 / (6 * s) * t| ≤ s * (ε / s) := mul_le_mul_of_nonneg_left h hs.le
    _ = ε := by field_simp

theorem s7_S7z_product_case_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (r : ℝ)
    (hr : r = 2 * (d : ℝ) + 6) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ)
    (G : Measure (NegSobolev d r)) [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianWithCov r G fun φ ψ =>
      ∫ x, φ x * responseRep (periodicRiesz d s) (withDensityReal ρ) 0 ψ x ∂(withDensityReal ρ)) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N → ∀ Φ ∈ CbUnitBall (NegSobolev d r) 5,
      |Real.sqrt N *
          (∫ X, Φ (zetaE r (modulatedGibbs (periodicRiesz d s) N 0 (withDensityReal ρ)) X)
              ∂(modulatedGibbs (periodicRiesz d s) N 0 (withDensityReal ρ)) - ∫ F, Φ F ∂G) -
        (1 / 6) * ∫ F, ∫ x, iteratedFDeriv ℝ 3 Φ F
            ![ellPt (periodicRiesz d s) (withDensityReal ρ) 0 r x,
              ellPt (periodicRiesz d s) (withDensityReal ρ) 0 r x,
              ellPt (periodicRiesz d s) (withDensityReal ρ) 0 r x] ∂(withDensityReal ρ) ∂G| ≤ ε := by
  intro ε hε
  have hm : (d : ℝ) < 2 * r := by
    rw [hr]; have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  haveI hμ : IsProbabilityMeasure (withDensityReal ρ) := HRS.isProb_withDensityReal hρ.density
  obtain ⟨σ⟩ := s7z_exists_equiv (by omega : 1 ≤ d)
  set μ := withDensityReal ρ with hμdef
  set Y : Torus d → NegSobolev d r := Ye r μ with hY
  have hYc : Continuous Y := continuous_Ye hm μ
  have hYm : Measurable Y := hYc.measurable
  set C : ℝ := Real.sqrt (8 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * r))) with hCdef
  have hC : ∀ x, ‖Y x‖ ≤ C := fun x => norm_ofMeasureDiff_le hm (Measure.dirac x) μ
  have hC0 : 0 ≤ C := Real.sqrt_nonneg _
  have hX0m : Measurable (fun ω : (ℕ → Torus d) × NegSobolev d r => Y (ω.1 0)) :=
    hYm.comp ((measurable_pi_apply 0).comp measurable_fst)
  -- hypotheses of Lemma 7.1
  have hcent : ∫ ω, Y ((ω : (ℕ → Torus d) × NegSobolev d r).1 0) ∂(s7zP μ G) = 0 := by
    have hh := integral_map (μ := s7zP μ G) measurable_fst.aemeasurable
      (measurable_Xi hYm 0).aestronglyMeasurable
    rw [s7z_map_fst] at hh
    show ∫ ω, Xi Y 0 ω.1 ∂(s7zP μ G) = 0
    rw [← hh]
    have := integral_map (μ := Pinf μ) (measurable_pi_apply (0 : ℕ)).aemeasurable
      hYm.aestronglyMeasurable
    rw [Measure.infinitePi_map_eval (μ := fun _ : ℕ => μ) 0] at this
    show ∫ ω, Y (ω 0) ∂(Pinf μ) = 0
    rw [← this]
    exact integral_Ye_eq_zero hm μ
  have hint4 : Integrable (fun ω : (ℕ → Torus d) × NegSobolev d r => ‖Y (ω.1 0)‖ ^ 4) (s7zP μ G) :=
    Integrable.of_bound (hX0m.norm.pow_const 4).aestronglyMeasurable (C ^ 4)
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hC _) 4)
  have h4 : ∫ ω, ‖Y ((ω : (ℕ → Torus d) × NegSobolev d r).1 0)‖ ^ 4 ∂(s7zP μ G) ≤ C ^ 4 := by
    calc _ ≤ ∫ _ω, C ^ 4 ∂(s7zP μ G) := integral_mono hint4 (integrable_const _)
          fun ω => pow_le_pow_left₀ (norm_nonneg _) (hC _) 4
      _ = C ^ 4 := by simp
  have htail : ∀ ε > 0, ∃ n₀ : ℕ, ∀ _a : Unit,
      ∫ ω, ∑' n : {n : ℕ // n₀ ≤ n}, (inner ℝ ((s7z_basis σ r) n) (Y ((ω : (ℕ → Torus d) × NegSobolev d r).1 0))) ^ 2
        ∂(s7zP μ G) ≤ ε := by
    intro ε' hε'
    obtain ⟨n₀, hn₀⟩ := s7z_tail hm μ σ hε'
    refine ⟨n₀, fun _ => ?_⟩
    calc _ ≤ ∫ _ω, ε' ∂(s7zP μ G) := integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun ω => tsum_nonneg fun n => sq_nonneg _)
          (integrable_const _) (Filter.Eventually.of_forall fun ω => hn₀ _)
      _ = ε' := by simp
  have hGrv : IsCenteredGaussianRV (s7zP μ G) (fun ω : (ℕ → Torus d) × NegSobolev d r => ω.2)
      fun x y => ProbabilityTheory.covarianceBilin
        (HRS.law (s7zP μ G) (fun ω : (ℕ → Torus d) × NegSobolev d r => Y (ω.1 0))) x y := by
    have hlaw : HRS.law (s7zP μ G) (fun ω : (ℕ → Torus d) × NegSobolev d r => ω.2) = G := by
      unfold HRS.law; exact s7z_map_snd μ G
    refine ⟨measurable_snd.aemeasurable, ?_, fun x y => ?_⟩
    · rw [hlaw]; exact hG.1
    · rw [hlaw, s7z_law_X μ G hYm 0]
      have := s7z_cov_eq hm μ (periodicRiesz d s) G hG.1 hG.2
      exact congrArg (fun A => A x y) this
  obtain ⟨N₀, hN₀⟩ := hilbert_edgeworth_C4 (s7z_basis σ r) (ι := Unit)
    (Ω := fun _ => (ℕ → Torus d) × NegSobolev d r) (fun _ => s7zP μ G)
    (fun _ ω => Y (ω.1 0)) (fun _ => hX0m.aemeasurable) (fun _ => hcent) (C ^ 4)
    (fun _ => hint4) (fun _ => h4) htail (fun _ ω => ω.2) (fun _ => hGrv) ε hε
  refine ⟨N₀, fun N hN hN1 Φ hΦ => ?_⟩
  have hΦ4 : Φ ∈ CbUnitBall (NegSobolev d r) 4 := cbUnitBall_anti (by norm_num) hΦ
  have hΦ3 : Φ ∈ CbUnitBall (NegSobolev d r) 3 := cbUnitBall_anti (by norm_num) hΦ
  have hΦc : Continuous Φ := hΦ4.1.continuous
  have hiid : IsIIDCopies (s7zP μ G) (fun (i : Fin N) (ω : (ℕ → Torus d) × NegSobolev d r) => Y (ω.1 i)) := by
    obtain ⟨h1, -⟩ := s7z_iid μ G hYm
    exact ⟨h1.precomp Fin.val_injective, fun i j => by
      rw [s7z_law_X μ G hYm, s7z_law_X μ G hYm]⟩
  have h := hN₀ N hN () (fun i ω => Y (ω.1 i))
    (fun i => (hYm.comp ((measurable_pi_apply (i : ℕ)).comp measurable_fst)).aemeasurable) hiid
    (fun i => by rw [s7z_law_X μ G hYm, s7z_law_X μ G hYm]) Φ hΦ4
  rw [s7z_integral_sum μ G hYm Φ hΦc N, s7z_integral_snd μ G Φ hΦc,
    s7z_third μ G hYc hC hΦ3] at h
  have hz : ∫ z, Φ (Ssum Y N z) ∂(Measure.pi fun _ : Fin N => μ) =
      ∫ X, Φ (zetaE r (modulatedGibbs (periodicRiesz d s) N 0 μ) X)
        ∂(modulatedGibbs (periodicRiesz d s) N 0 μ) := by
    rw [s7z_gibbs_zero]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z =>
      congrArg Φ (s7z_zeta_eq hm N hN1 μ z).symm)
  rw [hz] at h
  simp only [s7z_ell_eq]
  have hNpos : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN1)
  exact s7z_alg _ _ _ _ _ hNpos h

end HRS.MC.Sec7.S7z
