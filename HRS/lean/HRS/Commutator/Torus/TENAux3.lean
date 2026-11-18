import HRS.Commutator.Torus.Defs

/-!
# Torus energy layer (packet T-EN), helper part 3: periodisation, evenness, charge integrals

Prefix `ten_`.  Used by `energy_identity_T`: evenness of `f_η^𝕋` (reindexing of the periodisation), the
charge `ν = μ_N - μ` integrated against continuous/bounded functions, and integrability on `𝕋^d`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

theorem ten_toEuc_add (k m : Lattice d) :
    Lattice.toEuc (k + m) = Lattice.toEuc k + Lattice.toEuc m := by
  ext i
  simp [Lattice.toEuc]

theorem ten_toEuc_neg (k : Lattice d) : Lattice.toEuc (-k) = -Lattice.toEuc k := by
  ext i
  simp [Lattice.toEuc]

/-- The covering map is additive. -/
theorem ten_mk_neg (y : Euc d) : Torus.mk (-y) = -Torus.mk y := by
  funext i
  simp [Torus.mk]

/-- Two lifts of the same point of the torus differ by a lattice vector. -/
theorem ten_mk_sub_lattice {x y : Euc d} (h : Torus.mk x = Torus.mk y) :
    ∃ k : Lattice d, x = y + Lattice.toEuc k := by
  have hn : ∀ i : Fin d, ∃ n : ℤ, x i = y i + n := by
    intro i
    have hi : ((x i : ℝ) : UnitAddCircle) = ((y i : ℝ) : UnitAddCircle) := congrFun h i
    have h0 : (((x i - y i : ℝ)) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub, hi, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).1 h0
    exact ⟨n, by rw [zsmul_eq_mul, mul_one] at hn; linarith⟩
  choose n hn using hn
  refine ⟨n, ?_⟩
  ext i
  simp [Lattice.toEuc, hn i]

/-- The periodisation is computed from any lift. -/
theorem ten_perio_mk (F : Euc d → ℝ) (y : Euc d) :
    perio F (Torus.mk y) = ∑' m : Lattice d, F (y + Lattice.toEuc m) := by
  obtain ⟨k, hk⟩ := ten_mk_sub_lattice (show Torus.mk (Torus.rep (Torus.mk y)) = Torus.mk y from
    Torus.mk_rep _)
  unfold perio
  rw [hk]
  calc ∑' m : Lattice d, F (y + Lattice.toEuc k + Lattice.toEuc m)
      = ∑' m : Lattice d, F (y + Lattice.toEuc (k + m)) :=
        tsum_congr fun m => by rw [ten_toEuc_add, add_assoc]
    _ = ∑' m : Lattice d, F (y + Lattice.toEuc m) :=
        (Equiv.addLeft k).tsum_eq (fun m => F (y + Lattice.toEuc m))

/-- The periodisation of an even function is even. -/
theorem ten_perio_neg {F : Euc d → ℝ} (hF : ∀ z, F (-z) = F z) (x : Torus d) :
    perio F (-x) = perio F x := by
  have hx : -x = Torus.mk (-Torus.rep x) := by
    rw [ten_mk_neg, Torus.mk_rep]
  have h1 : perio F (-x) = ∑' m : Lattice d, F (-Torus.rep x + Lattice.toEuc m) := by
    rw [hx, ten_perio_mk]
  rw [h1]
  show _ = ∑' m : Lattice d, F (Torus.rep x + Lattice.toEuc m)
  calc ∑' m : Lattice d, F (-Torus.rep x + Lattice.toEuc m)
      = ∑' m : Lattice d, F (Torus.rep x + Lattice.toEuc (-m)) := by
        refine tsum_congr fun m => ?_
        rw [← hF (Torus.rep x + Lattice.toEuc (-m))]
        congr 1
        rw [ten_toEuc_neg]
        abel
    _ = ∑' m : Lattice d, F (Torus.rep x + Lattice.toEuc m) :=
        (Equiv.neg (Lattice d)).tsum_eq (fun m => F (Torus.rep x + Lattice.toEuc m))

/-- `f_η` is even. -/
theorem ten_fTrunc_neg (s η : ℝ) (x : Euc d) : Whole.fTrunc s η (-x) = Whole.fTrunc s η x := by
  unfold Whole.fTrunc Whole.phiT Whole.phi
  simp [smul_neg, norm_neg]

/-- The mean-free periodised truncation `f_η^𝕋` is even. -/
theorem ten_fTorus_neg (s η : ℝ) (x : Torus d) : fTorus s η (-x) = fTorus s η x := by
  unfold fTorus
  rw [ten_perio_neg (fun z => ten_fTrunc_neg s η z) x]

/-- The kernel `g_η^𝕋` is even. -/
theorem ten_gTorus_neg (s η : ℝ) (x : Torus d) : gTorus s η (-x) = gTorus s η x := by
  by_cases hx : x = 0
  · subst hx
    simp
  · have hnx : -x ≠ 0 := neg_ne_zero.2 hx
    simp only [gTorus, hx, hnx, ite_false]
    rw [periodicRiesz_neg, ten_fTorus_neg]

/-! ### Integrability and bounds on `𝕋^d` (finite measure, continuous or bounded functions) -/

/-- A bounded measurable function on `𝕋^d` is integrable. -/
theorem ten_integrable_of_bdd {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {F : α → ℝ} (hF : Measurable F) (C : ℝ) (hC : ∀ x, ‖F x‖ ≤ C) : Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable C (ae_of_all _ hC)

/-- A continuous function on `𝕋^d` is bounded. -/
theorem ten_bound_of_continuous {G : Torus d → ℝ} (hG : Continuous G) : ∃ C, ∀ x, ‖G x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hG.continuousOn
  exact ⟨C, fun x => hC x (Set.mem_univ x)⟩


/-- For a measurable density `a`, the signed measure `a dx` integrates `g` as `∫ a g`. -/
theorem ten_int_ofDensity (a g : Torus d → ℝ) (ha : Measurable a)
    (hag : Integrable (fun x => a x * g x)) :
    (SMT.ofDensity a).int g = ∫ x, a x * g x := by
  have hm1 : Measurable fun x => ENNReal.ofReal (a x) := ha.ennreal_ofReal
  have hm2 : Measurable fun x => ENNReal.ofReal (-a x) := ha.neg.ennreal_ofReal
  have ht1 : ∀ᵐ x ∂(volume : Measure (Torus d)), ENNReal.ofReal (a x) < ⊤ :=
    ae_of_all _ fun x => ENNReal.ofReal_lt_top
  have ht2 : ∀ᵐ x ∂(volume : Measure (Torus d)), ENNReal.ofReal (-a x) < ⊤ :=
    ae_of_all _ fun x => ENNReal.ofReal_lt_top
  have hI1 : Integrable (fun x => (ENNReal.ofReal (a x)).toReal • g x) := by
    have : (fun x => (ENNReal.ofReal (a x)).toReal • g x) =
        {x | 0 < a x}.indicator (fun x => a x * g x) := by
      funext x
      by_cases h : 0 < a x
      · rw [Set.indicator_of_mem (show x ∈ {x | 0 < a x} from h), ENNReal.toReal_ofReal', smul_eq_mul,
          max_eq_left h.le]
      · rw [Set.indicator_of_notMem (show x ∉ {x | 0 < a x} from h), ENNReal.toReal_ofReal', smul_eq_mul,
          max_eq_right (not_lt.1 h), zero_mul]
    rw [this]
    exact hag.indicator (measurableSet_lt measurable_const ha)
  have hI2 : Integrable (fun x => (ENNReal.ofReal (-a x)).toReal • g x) := by
    have : (fun x => (ENNReal.ofReal (-a x)).toReal • g x) =
        {x | a x < 0}.indicator (fun x => -(a x * g x)) := by
      funext x
      by_cases h : a x < 0
      · rw [Set.indicator_of_mem (show x ∈ {x | a x < 0} from h), ENNReal.toReal_ofReal', smul_eq_mul,
          max_eq_left (by linarith), neg_mul]
      · rw [Set.indicator_of_notMem (show x ∉ {x | a x < 0} from h), ENNReal.toReal_ofReal', smul_eq_mul,
          max_eq_right (by linarith [not_lt.1 h]), zero_mul]
    rw [this]
    exact (hag.neg).indicator (measurableSet_lt ha measurable_const)
  unfold SMT.int SMT.ofDensity
  rw [integral_withDensity_eq_integral_toReal_smul hm1 ht1 g,
    integral_withDensity_eq_integral_toReal_smul hm2 ht2 g, ← integral_sub hI1 hI2]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [ENNReal.toReal_ofReal', smul_eq_mul]
  rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self]

/-- The charge `ν = μ_N - μ` integrates a bounded measurable `f` as `N⁻¹ ∑ f(X_i) - ∫ ρ f`. -/
theorem ten_charge_int {N : ℕ} (ρ : Torus d → ℝ) (hρ : BddDensityT ρ) (hN : 1 ≤ N) (X : Config d N)
    (f : Torus d → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    (chargeT X ρ).int f = (1 / (N : ℝ)) * ∑ i, f (X i) - ∫ x, ρ x * f x := by
  have hρm := hρ.measurable
  obtain ⟨B, hB⟩ := hρ.bdd
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hN0 : 0 < N := by omega
  haveI := HRS.empirical_isProbabilityMeasure hN0 X
  have hfρ : Integrable (fun x => ρ x * f x) := by
    refine ten_integrable_of_bdd (μ := volume) (hρm.mul hf) (B * C) (fun x => ?_)
    rw [norm_mul]
    exact mul_le_mul (by rw [Real.norm_eq_abs]; exact hB x) (hC x) (norm_nonneg _) hB0
  have hIE : Integrable f (HRS.empirical X) :=
    ten_integrable_of_bdd (μ := HRS.empirical X) hf C hC
  have hW1 : Integrable f (volume.withDensity fun x => ENNReal.ofReal (-ρ x)) := by
    refine (integrable_withDensity_iff_integrable_smul' hρm.neg.ennreal_ofReal
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)).2 ?_
    refine ten_integrable_of_bdd (μ := volume)
      ((ENNReal.measurable_toReal.comp hρm.neg.ennreal_ofReal).smul hf) (B * C) (fun x => ?_)
    rw [smul_eq_mul, ENNReal.toReal_ofReal', norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (le_max_right _ _)]
    exact mul_le_mul (max_le ((neg_le_abs _).trans (hB x)) hB0) (hC x) (norm_nonneg _) hB0
  have hW2 : Integrable f (volume.withDensity fun x => ENNReal.ofReal (ρ x)) := by
    refine (integrable_withDensity_iff_integrable_smul' hρm.ennreal_ofReal
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)).2 ?_
    refine ten_integrable_of_bdd (μ := volume)
      ((ENNReal.measurable_toReal.comp hρm.ennreal_ofReal).smul hf) (B * C) (fun x => ?_)
    rw [smul_eq_mul, ENNReal.toReal_ofReal', norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (le_max_right _ _)]
    exact mul_le_mul (max_le ((le_abs_self _).trans (hB x)) hB0) (hC x) (norm_nonneg _) hB0
  have hD := ten_int_ofDensity (fun x => -ρ x) f hρm.neg (by simpa using hfρ.neg)
  have hD' : ∫ x, f x ∂(volume.withDensity fun x => ENNReal.ofReal (-ρ x)) -
      ∫ x, f x ∂(volume.withDensity fun x => ENNReal.ofReal (ρ x)) = -∫ x, ρ x * f x := by
    have h2 := hD
    unfold SMT.int SMT.ofDensity at h2
    simp only [neg_neg] at h2
    rw [h2, ← integral_neg]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  have hE : ∫ x, f x ∂(HRS.empirical X) = (N : ℝ)⁻¹ * ∑ i, f (X i) :=
    HRS.pair_empirical hN0 X f
  unfold SMT.int chargeT
  rw [integral_add_measure hIE hW1, hE, one_div]
  linarith [hD']


/-- The modulated-energy expansion of `‖ν‖²_G` for a continuous even kernel `G` and `ν = μ_N - μ`
(diagonal included, `G(0)` the value at the origin). -/
theorem ten_kerEnergy_charge {N : ℕ} (G : Torus d → ℝ) (hG : Continuous G)
    (hGe : ∀ z, G (-z) = G z) (ρ : Torus d → ℝ) (hρ : BddDensityT ρ) (hN : 1 ≤ N) (X : Config d N) :
    kerEnergyT G (chargeT X ρ) =
      (1 / (N : ℝ) ^ 2) * (∑ i, ∑ j, G (X i - X j))
        - (2 / (N : ℝ)) * (∑ i, (∫ y, G (X i - y) * ρ y))
        + (∫ x, ∫ y, G (x - y) * ρ x * ρ y) := by
  have hρm := hρ.measurable
  have hGm : Measurable G := hG.measurable
  obtain ⟨B, hB⟩ := hρ.bdd
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  obtain ⟨C, hC⟩ := ten_bound_of_continuous hG
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hρB : ∀ y : Torus d, ‖ρ y‖ ≤ B := fun y => by rw [Real.norm_eq_abs]; exact hB y
  have hGz : ∀ z : Torus d, Measurable (fun y : Torus d => G (z - y)) :=
    fun z => hGm.comp (measurable_const.sub measurable_id)
  -- the density-weighted kernel is bounded
  have hbdd : ∀ x y : Torus d, ‖ρ y * G (x - y)‖ ≤ B * C := fun x y => by
    rw [norm_mul]; exact mul_le_mul (hρB y) (hC _) (norm_nonneg _) hB0
  have hint_bound : ∀ x : Torus d, ‖∫ y, ρ y * G (x - y)‖ ≤ B * C := fun x => by
    have h := norm_integral_le_of_norm_le_const (μ := volume) (f := fun y => ρ y * G (x - y))
      (C := B * C) (ae_of_all _ fun y => hbdd x y)
    simpa using h
  -- the function `Φ(x) = N⁻¹∑_j G(x - X_j) - ∫ ρ(y) G(x - y) dy`
  set Φ : Torus d → ℝ := fun x => (1 / (N : ℝ)) * ∑ j, G (x - X j) - ∫ y, ρ y * G (x - y) with hΦ
  have hΦbd : ∀ x, ‖Φ x‖ ≤ C + B * C := fun x => by
    have hS : ‖∑ j, G (x - X j)‖ ≤ (N : ℝ) * C := by
      calc ‖∑ j, G (x - X j)‖ ≤ ∑ j, ‖G (x - X j)‖ := norm_sum_le _ _
        _ ≤ ∑ _j : Fin N, C := Finset.sum_le_sum fun j _ => hC _
        _ = (N : ℝ) * C := by simp
    have hfirst : ‖(1 / (N : ℝ)) * ∑ j, G (x - X j)‖ ≤ C := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / N)]
      calc 1 / (N : ℝ) * ‖∑ j, G (x - X j)‖ ≤ 1 / (N : ℝ) * ((N : ℝ) * C) :=
            mul_le_mul_of_nonneg_left hS (by positivity)
        _ = C := by field_simp
    exact (norm_sub_le _ _).trans (add_le_add hfirst (hint_bound x))
  have hΦm : Measurable Φ := by
    have h1 : Continuous fun x : Torus d => (1 / (N : ℝ)) * ∑ j, G (x - X j) := by fun_prop
    have hF : StronglyMeasurable (fun p : Torus d × Torus d => ρ p.2 * G (p.1 - p.2)) :=
      ((hρm.comp measurable_snd).mul (hGm.comp (measurable_fst.sub measurable_snd))).stronglyMeasurable
    have h2 : Measurable fun x : Torus d => ∫ y, ρ y * G (x - y) := hF.integral_prod_right'.measurable
    exact h1.measurable.sub h2
  -- the inner integrals are the charge integrals against `G(x - ·)`
  have hinner : ∀ x : Torus d, (chargeT X ρ).int (fun y => G (x - y)) = Φ x := by
    intro x
    rw [ten_charge_int ρ hρ hN X (fun y => G (x - y)) (hGz x) C (fun y => hC _)]
  have hmain : kerEnergyT G (chargeT X ρ) = (chargeT X ρ).int Φ := by
    unfold kerEnergyT SMT.pair2
    simp only [hinner]
  rw [hmain, ten_charge_int ρ hρ hN X Φ hΦm (C + B * C) hΦbd]
  -- joint integrability on `𝕋^d × 𝕋^d`
  have hJ : Integrable (fun p : Torus d × Torus d => G (p.1 - p.2) * ρ p.1 * ρ p.2) := by
    refine ten_integrable_of_bdd (μ := volume)
      (((hGm.comp (measurable_fst.sub measurable_snd)).mul (hρm.comp measurable_fst)).mul
        (hρm.comp measurable_snd)) (C * B * B) (fun p => ?_)
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul (hC _) (hρB p.1) (norm_nonneg _) hC0) (hρB p.2) (norm_nonneg _)
      (mul_nonneg hC0 hB0)
  have hI_ρG : ∀ j : Fin N, Integrable (fun x => ρ x * G (x - X j)) := fun j =>
    ten_integrable_of_bdd (μ := volume) (hρm.mul (hGm.comp (measurable_id.sub measurable_const)))
      (B * C) (fun x => by rw [norm_mul]; exact mul_le_mul (hρB x) (hC _) (norm_nonneg _) hB0)
  have hI2 : Integrable (fun x => ∫ y, G (x - y) * ρ x * ρ y) := hJ.integral_prod_left
  -- `ρ Φ` integrated
  have hρΦ : ∀ x, ρ x * Φ x = (1 / (N : ℝ)) * ∑ j, ρ x * G (x - X j)
      - ∫ y, G (x - y) * ρ x * ρ y := by
    intro x
    have hint : ∫ y, G (x - y) * ρ x * ρ y = ρ x * ∫ y, ρ y * G (x - y) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun y => by ring)
    have hsumr : ∑ j, ρ x * G (x - X j) = ρ x * ∑ j, G (x - X j) := (Finset.mul_sum _ _ _).symm
    rw [hint, hsumr]
    simp only [hΦ]
    ring
  have hint2 : ∫ x, ρ x * Φ x = (1 / (N : ℝ)) * ∑ j, (∫ x, ρ x * G (x - X j))
      - (∫ x, ∫ y, G (x - y) * ρ x * ρ y) := by
    have hA : Integrable (fun x => (1 / (N : ℝ)) * ∑ j, ρ x * G (x - X j)) :=
      (integrable_finsetSum _ fun j _ => hI_ρG j).const_mul _
    have e1 : ∫ x, ρ x * Φ x = ∫ x, ((1 / (N : ℝ)) * ∑ j, ρ x * G (x - X j)
        - ∫ y, G (x - y) * ρ x * ρ y) :=
      integral_congr_ae (ae_of_all _ hρΦ)
    have e2 : ∫ x, ((1 / (N : ℝ)) * ∑ j, ρ x * G (x - X j)
        - ∫ y, G (x - y) * ρ x * ρ y) = (∫ x, (1 / (N : ℝ)) * ∑ j, ρ x * G (x - X j))
        - (∫ x, ∫ y, G (x - y) * ρ x * ρ y) := integral_sub hA hI2
    have e3 : ∫ x, (1 / (N : ℝ)) * ∑ j, ρ x * G (x - X j) =
        (1 / (N : ℝ)) * ∑ j, (∫ x, ρ x * G (x - X j)) := by
      rw [integral_const_mul, integral_finsetSum _ (fun j _ => hI_ρG j)]
    rw [e1, e2, e3]
  have hsymm : ∀ j : Fin N, ∫ x, ρ x * G (x - X j) = ∫ y, G (X j - y) * ρ y := by
    intro j
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    have : G (x - X j) = G (X j - x) := by rw [← neg_sub x (X j), hGe]
    show ρ x * G (x - X j) = G (X j - x) * ρ x
    rw [this]; ring
  have hcomm : ∀ i : Fin N, ∫ y, G (X i - y) * ρ y = ∫ y, ρ y * G (X i - y) :=
    fun i => integral_congr_ae (ae_of_all _ fun y => mul_comm _ _)
  have hPhi : ∀ i, Φ (X i) = (1 / (N : ℝ)) * ∑ j, G (X i - X j) - ∫ y, ρ y * G (X i - y) :=
    fun i => rfl
  have hS1 : ∑ i, Φ (X i) = (1 / (N : ℝ)) * ∑ i, ∑ j, G (X i - X j)
      - ∑ i, ∫ y, ρ y * G (X i - y) := by
    rw [Finset.sum_congr rfl (fun i _ => hPhi i), Finset.sum_sub_distrib, Finset.mul_sum]
  have hS2 : ∫ x, ρ x * Φ x = (1 / (N : ℝ)) * ∑ j, (∫ y, G (X j - y) * ρ y)
      - (∫ x, ∫ y, G (x - y) * ρ x * ρ y) := by
    rw [hint2]
    simp only [hsymm]
  rw [hS1, hS2]
  simp only [hcomm]
  ring

end HRS.Commutator.TorusNote
