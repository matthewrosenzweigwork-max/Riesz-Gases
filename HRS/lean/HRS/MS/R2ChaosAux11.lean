import HRS.MS.R2ChaosAux10
import HRS.MS.SuppU1
import HRS.MS.WrQuadAux3

/-!
# HRS.MS.R2ChaosAux11 -- the centering operator on `L²(μ ⊗ μ)`

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

`‖cen g‖_{L²(μ⊗μ)} ≤ 4 ‖g‖_{L²(μ⊗μ)}` (each of the four terms of `r2CenterKernel` is bounded by `‖g‖`), measurability and
symmetry of `r2CenterKernel`, `L²` membership of envelope-bounded kernels (through S9.1).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

variable {d : ℕ}

theorem s94_lintegral_sq_eq {α : Type*} [MeasurableSpace α] {ν : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f ν) : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν = eLpNorm f 2 ν ^ 2 := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hf]
  simp only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

section Center

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s94_eLpNorm_G1_le {g : Euc d → Euc d → ℝ} (hg : Measurable fun q : Euc d × Euc d => g q.1 q.2) :
    eLpNorm (fun x => ∫ y', g x y' ∂μ) 2 μ ≤ eLpNorm (fun q : Euc d × Euc d => g q.1 q.2) 2 (μ.prod μ) := by
  have hG1m : Measurable fun x => ∫ y', g x y' ∂μ :=
    (hg.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  have hsec : ∀ x, Measurable fun y' => g x y' := fun x => hg.comp measurable_prodMk_left
  have h1 : ∀ x, ‖∫ y', g x y' ∂μ‖ₑ ≤ eLpNorm (fun y' => g x y') 2 μ := by
    intro x
    calc ‖∫ y', g x y' ∂μ‖ₑ ≤ ∫⁻ y', ‖g x y'‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
      _ = eLpNorm (fun y' => g x y') 1 μ := (eLpNorm_one_eq_lintegral_enorm (hsec x).aestronglyMeasurable).symm
      _ ≤ eLpNorm (fun y' => g x y') 2 μ := eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  have h2 : ∫⁻ x, ‖∫ y', g x y' ∂μ‖ₑ ^ 2 ∂μ ≤ ∫⁻ x, eLpNorm (fun y' => g x y') 2 μ ^ 2 ∂μ :=
    lintegral_mono fun x => by gcongr; exact h1 x
  have h3 : ∫⁻ x, eLpNorm (fun y' => g x y') 2 μ ^ 2 ∂μ =
      eLpNorm (fun q : Euc d × Euc d => g q.1 q.2) 2 (μ.prod μ) ^ 2 := by
    rw [← s94_lintegral_sq_eq hg.aestronglyMeasurable, lintegral_prod _ (hg.enorm.pow_const 2).aemeasurable]
    refine lintegral_congr fun x => ?_
    rw [← s94_lintegral_sq_eq (hsec x).aestronglyMeasurable]
  rw [s94_lintegral_sq_eq hG1m.aestronglyMeasurable] at h2
  rw [h3] at h2
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 h2

theorem s94_eLpNorm_G2_le {g : Euc d → Euc d → ℝ} (hg : Measurable fun q : Euc d × Euc d => g q.1 q.2) :
    eLpNorm (fun y => ∫ x', g x' y ∂μ) 2 μ ≤ eLpNorm (fun q : Euc d × Euc d => g q.1 q.2) 2 (μ.prod μ) := by
  have h := s94_eLpNorm_G1_le (μ := μ) (g := fun x y => g y x) (hg.comp measurable_swap)
  refine h.trans (le_of_eq ?_)
  have := eLpNorm_comp_measurePreserving (p := 2) (g := fun q : Euc d × Euc d => g q.1 q.2)
    hg.aestronglyMeasurable (Measure.measurePreserving_swap (μ := μ) (ν := μ))
  exact this

theorem s94_eLpNorm_center_le {g : Euc d → Euc d → ℝ} (hg : Measurable fun q : Euc d × Euc d => g q.1 q.2) :
    eLpNorm (fun q : Euc d × Euc d => r2CenterKernel μ g q.1 q.2) 2 (μ.prod μ) ≤
      4 * eLpNorm (fun q : Euc d × Euc d => g q.1 q.2) 2 (μ.prod μ) := by
  set E := eLpNorm (fun q : Euc d × Euc d => g q.1 q.2) 2 (μ.prod μ) with hE
  have hG1m : Measurable fun x => ∫ y', g x y' ∂μ :=
    (hg.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  have hG2m : Measurable fun y => ∫ x', g x' y ∂μ :=
    ((hg.comp measurable_swap).stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  have hG1 := s94_eLpNorm_G1_le (μ := μ) hg
  have hG2 := s94_eLpNorm_G2_le (μ := μ) hg
  have hf1 : eLpNorm (fun q : Euc d × Euc d => ∫ y', g q.1 y' ∂μ) 2 (μ.prod μ) =
      eLpNorm (fun x => ∫ y', g x y' ∂μ) 2 μ :=
    eLpNorm_comp_measurePreserving (p := 2) (g := fun x => ∫ y', g x y' ∂μ) hG1m.aestronglyMeasurable
      (measurePreserving_fst (μ := μ) (ν := μ))
  have hf2 : eLpNorm (fun q : Euc d × Euc d => ∫ x', g x' q.2 ∂μ) 2 (μ.prod μ) =
      eLpNorm (fun y => ∫ x', g x' y ∂μ) 2 μ :=
    eLpNorm_comp_measurePreserving (p := 2) (g := fun y => ∫ x', g x' y ∂μ) hG2m.aestronglyMeasurable
      (measurePreserving_snd (μ := μ) (ν := μ))
  have hc : eLpNorm (fun _ : Euc d × Euc d => ∫ x', ∫ y', g x' y' ∂μ ∂μ) 2 (μ.prod μ) ≤ E := by
    rw [eLpNorm_const _ two_ne_zero (IsProbabilityMeasure.ne_zero _)]
    simp only [measure_univ, ENNReal.one_rpow, mul_one]
    calc ‖∫ x', ∫ y', g x' y' ∂μ ∂μ‖ₑ ≤ ∫⁻ x', ‖∫ y', g x' y' ∂μ‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
      _ = eLpNorm (fun x => ∫ y', g x y' ∂μ) 1 μ := (eLpNorm_one_eq_lintegral_enorm hG1m.aestronglyMeasurable).symm
      _ ≤ eLpNorm (fun x => ∫ y', g x y' ∂μ) 2 μ := eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
      _ ≤ E := hG1
  have hgm : AEStronglyMeasurable (fun q : Euc d × Euc d => g q.1 q.2) (μ.prod μ) := hg.aestronglyMeasurable
  have hm1 : AEStronglyMeasurable (fun q : Euc d × Euc d => ∫ y', g q.1 y' ∂μ) (μ.prod μ) :=
    (hG1m.comp measurable_fst).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (fun q : Euc d × Euc d => ∫ x', g x' q.2 ∂μ) (μ.prod μ) :=
    (hG2m.comp measurable_snd).aestronglyMeasurable
  have e : (fun q : Euc d × Euc d => r2CenterKernel μ g q.1 q.2) = fun q =>
      g q.1 q.2 - (∫ y', g q.1 y' ∂μ) - (∫ x', g x' q.2 ∂μ) + ∫ x', ∫ y', g x' y' ∂μ ∂μ := rfl
  rw [e]
  have t1 : eLpNorm (fun q : Euc d × Euc d => g q.1 q.2 - (∫ y', g q.1 y' ∂μ)) 2 (μ.prod μ) ≤ E + E := by
    refine (eLpNorm_sub_le (by norm_num)).trans ?_
    rw [hf1]; exact add_le_add le_rfl hG1
  have t2 : eLpNorm (fun q : Euc d × Euc d => g q.1 q.2 - (∫ y', g q.1 y' ∂μ) - (∫ x', g x' q.2 ∂μ)) 2 (μ.prod μ)
      ≤ E + E + E := by
    refine (eLpNorm_sub_le (by norm_num)).trans ?_
    rw [hf2]; exact add_le_add t1 hG2
  refine (eLpNorm_add_le (by norm_num)).trans ?_
  calc _ ≤ (E + E + E) + E := add_le_add t2 hc
    _ = 4 * E := by ring

theorem s94_center_measurable {g : Euc d → Euc d → ℝ} (hg : Measurable fun q : Euc d × Euc d => g q.1 q.2) :
    Measurable fun q : Euc d × Euc d => r2CenterKernel μ g q.1 q.2 := by
  have hG1m : Measurable fun x => ∫ y', g x y' ∂μ :=
    (hg.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  have hG2m : Measurable fun y => ∫ x', g x' y ∂μ :=
    ((hg.comp measurable_swap).stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  have e : (fun q : Euc d × Euc d => r2CenterKernel μ g q.1 q.2) = fun q =>
      g q.1 q.2 - (∫ y', g q.1 y' ∂μ) - (∫ x', g x' q.2 ∂μ) + ∫ x', ∫ y', g x' y' ∂μ ∂μ := rfl
  rw [e]
  exact ((hg.sub (hG1m.comp measurable_fst)).sub (hG2m.comp measurable_snd)).add measurable_const

theorem s94_center_symm {g : Euc d → Euc d → ℝ} (hsym : ∀ x y, g x y = g y x) (x y : Euc d) :
    r2CenterKernel μ g x y = r2CenterKernel μ g y x := by
  unfold r2CenterKernel
  have h1 : ∫ y', g y y' ∂μ = ∫ x', g x' y ∂μ := integral_congr_ae (ae_of_all _ fun z => hsym y z)
  have h2 : ∫ x', g x' x ∂μ = ∫ y', g x y' ∂μ := integral_congr_ae (ae_of_all _ fun z => hsym z x)
  rw [h1, h2, hsym x y]
  ring

theorem s94_center_sub {g g' : Euc d → Euc d → ℝ}
    (h1 : ∀ x, Integrable (fun y => g x y) μ) (h1' : ∀ x, Integrable (fun y => g' x y) μ)
    (h2 : ∀ y, Integrable (fun x => g x y) μ) (h2' : ∀ y, Integrable (fun x => g' x y) μ)
    (h3 : Integrable (fun x => ∫ y', g x y' ∂μ) μ) (h3' : Integrable (fun x => ∫ y', g' x y' ∂μ) μ) (x y : Euc d) :
    r2CenterKernel μ (fun x y => g x y - g' x y) x y = r2CenterKernel μ g x y - r2CenterKernel μ g' x y := by
  unfold r2CenterKernel
  have e1 : ∫ y', (g x y' - g' x y') ∂μ = (∫ y', g x y' ∂μ) - ∫ y', g' x y' ∂μ := integral_sub (h1 x) (h1' x)
  have e2 : ∫ x', (g x' y - g' x' y) ∂μ = (∫ x', g x' y ∂μ) - ∫ x', g' x' y ∂μ := integral_sub (h2 y) (h2' y)
  have e3 : ∫ x', ∫ y', (g x' y' - g' x' y') ∂μ ∂μ =
      (∫ x', ∫ y', g x' y' ∂μ ∂μ) - ∫ x', ∫ y', g' x' y' ∂μ ∂μ := by
    have : ∀ x', ∫ y', (g x' y' - g' x' y') ∂μ = (∫ y', g x' y' ∂μ) - ∫ y', g' x' y' ∂μ :=
      fun x' => integral_sub (h1 x') (h1' x')
    simp_rw [this]
    exact integral_sub h3 h3'
  rw [e1, e2, e3]
  ring

end Center

section Env

variable {s T : ℝ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s94_finiteRank_bounded {m : ℕ} {c : Fin m → Fin m → ℝ} {u : Fin m → Euc d → ℝ}
    (hu : ∀ a, IsR2Test (u a)) : ∃ C : ℝ, ∀ x y, |r2FiniteRankKernel c u x y| ≤ C := by
  have hb : ∀ a, ∃ C : ℝ, ∀ x, |u a x| ≤ C := fun a => s94_test_bounded (hu a)
  choose C hC using hb
  refine ⟨∑ a, ∑ b, |c a b| * C a * C b, fun x y => ?_⟩
  unfold r2FiniteRankKernel
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [abs_mul, abs_mul]
  have h1 := hC a x
  have h2 := hC b y
  have h3 : 0 ≤ |u a x| := abs_nonneg _
  have h5 : 0 ≤ C a := h3.trans h1
  calc |c a b| * |u a x| * |u b y| ≤ |c a b| * C a * C b := by gcongr
    _ = _ := by ring

theorem s94_finiteRank_measurable {m : ℕ} {c : Fin m → Fin m → ℝ} {u : Fin m → Euc d → ℝ}
    (hu : ∀ a, IsR2Test (u a)) : Measurable fun q : Euc d × Euc d => r2FiniteRankKernel c u q.1 q.2 := by
  unfold r2FiniteRankKernel
  refine Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_
  exact (((s94_test_continuous (hu a)).measurable.comp measurable_fst).const_mul (c a b)).mul
    ((s94_test_continuous (hu b)).measurable.comp measurable_snd)

theorem s94_finiteRank_memLp {m : ℕ} {c : Fin m → Fin m → ℝ} {u : Fin m → Euc d → ℝ}
    (hu : ∀ a, IsR2Test (u a)) :
    MemLp (fun q : Euc d × Euc d => r2FiniteRankKernel c u q.1 q.2) 2 (μ.prod μ) := by
  obtain ⟨C, hC⟩ := s94_finiteRank_bounded (c := c) hu
  exact MemLp.of_bound (s94_finiteRank_measurable hu).aestronglyMeasurable C
    (ae_of_all _ fun q => by simpa using hC q.1 q.2)

theorem s94_B_nonneg (hd : 2 ≤ d) {s B : ℝ} {h : Euc d → Euc d → ℝ} (hh : IsBoundedPairKernel s B h) :
    0 ≤ B := by
  have hfr : Module.finrank ℝ (Euc d) = d := finrank_euclideanSpace_fin
  haveI : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hfr]; omega)
  obtain ⟨x0, y0, hxy0⟩ := exists_pair_ne (Euc d)
  have h1 := hh.bound x0 y0 hxy0
  have h2 : 0 < 1 + rieszWeight s (x0 - y0) := by
    have : 0 ≤ rieszWeight s (x0 - y0) := HRS.MS.Wr.wr3_rieszWeight_nonneg s _
    linarith
  have := (abs_nonneg (h x0 y0)).trans h1
  exact (mul_nonneg_iff_of_pos_right h2).mp this

end Env

section Env2

variable {s : ℝ}

/-- Integrability facts for an envelope-bounded kernel against `μ = ρ dx`. -/
theorem s94_env_facts (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {M L B : ℝ} {ρ : Euc d → ℝ}
    (hρ : IsRound2Density d s M L ρ) {h : Euc d → Euc d → ℝ} (hh : IsBoundedPairKernel s B h) :
    (∀ x, Integrable (fun y => h x y) (Whole.withDensityReal ρ)) ∧
      (∀ y, Integrable (fun x => h x y) (Whole.withDensityReal ρ)) ∧
      Integrable (fun x => ∫ y', h x y' ∂(Whole.withDensityReal ρ)) (Whole.withDensityReal ρ) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < (d : ℝ) := by linarith
  have hB := s94_B_nonneg hd hh
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  have hle : Whole.withDensityReal ρ ≤ ENNReal.ofReal 1 • Whole.withDensityReal ρ := by simp
  have hint : ∀ x, Integrable (fun y => h x y) (Whole.withDensityReal ρ) := fun x =>
    HRS.MS.Wr.wr14a_integrable_of_env_bound (by omega) hs0 hsd M hρ.prob hρ.bdd hle zero_le_one hB
      (x := x) (f := fun y => h x y) (hh.measurable.comp measurable_prodMk_left)
      (fun y hy => hh.bound x y (Ne.symm hy))
  refine ⟨hint, fun y => ?_, ?_⟩
  · have := hint y
    refine this.congr (ae_of_all _ fun x => hh.symm y x)
  · obtain ⟨c, hc0, hc⟩ := HRS.MS.Wr.wr14a_Hc_bound (d := d) (by omega) hs0 hsd M
    refine Integrable.of_bound ?_ (c * 1 * B) (ae_of_all _ fun x => ?_)
    · exact (hh.measurable.stronglyMeasurable.integral_prod_right' (ν := Whole.withDensityReal ρ)).aestronglyMeasurable
    · have := hc hρ.prob hρ.bdd hle zero_le_one hB (h := h) (fun x y hxy => hh.bound x y hxy) x
      simpa [HRS.MS.Wr.wr14a_Hc, Real.norm_eq_abs] using this

/-- An envelope-bounded kernel lies in `L²(μ ⊗ μ)` (through the finite-rank approximation S9.1). -/
theorem s94_env_memLp (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {M L B : ℝ} {ρ : Euc d → ℝ}
    (hρ : IsRound2Density d s M L ρ) {h : Euc d → Euc d → ℝ} (hh : IsBoundedPairKernel s B h) :
    MemLp (fun q : Euc d × Euc d => h q.1 q.2) 2 ((Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ)) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  obtain ⟨C, hC⟩ := HRS.Whole.U1.round2_approximation_proof hd s hs0 hs
  obtain ⟨hj, hA⟩ := hC M L ρ hρ B h hh
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hconv := hA.converges 2 (by norm_num) (by linarith)
  obtain ⟨j, hj'⟩ := (hconv.eventually (gt_mem_nhds ENNReal.zero_lt_top)).exists
  obtain ⟨m, c, u, ⟨_, hsm, hcp⟩, hjeq⟩ := hA.finiteRank j
  have hut : ∀ a, IsR2Test (u a) := fun a => ⟨hsm a, hcp a⟩
  have hfr : MemLp (fun q : Euc d × Euc d => hj j q.1 q.2) 2 ((Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ)) := by
    rw [hjeq]; exact s94_finiteRank_memLp hut
  have hdiff : MemLp (fun q : Euc d × Euc d => hj j q.1 q.2 - h q.1 q.2) 2
      ((Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ)) := by
    have : ENNReal.ofReal 2 = 2 := by norm_num
    rw [this] at hj'
    exact hj'
  have e : (fun q : Euc d × Euc d => h q.1 q.2) =
      fun q => hj j q.1 q.2 - (hj j q.1 q.2 - h q.1 q.2) := funext fun q => by ring
  rw [e]
  exact hfr.sub hdiff

end Env2

end HRS.MS.R2Chaos
