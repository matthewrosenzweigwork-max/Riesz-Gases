import HRS.MS.UlocCutAux2
import HRS.Whole.AppendixALemmas

/-!
# MS-ULOC-CUT: Lemma S.A.31(i), repaired (equivalence of uniformly local norms for different cutoffs)

The frozen statement `HRS.Whole.AppendixALemmas.uloc_embedding_cutoffs` has a false third conjunct
for `d ≥ 5`: balls of radius `1` around `ℤ^d` do not cover `ℝ^d`.  Here:

* `uloc_embedding_cutoffs_fine_proof`: the repaired statement with the lattice `(⌈√d⌉)⁻¹ ℤ^d`;
* `uloc_embedding_cutoffs_12_proof`: the first two conjuncts for the original lattice `ℤ^d`.

Route (S L11009-11011): a finite-net partition-of-unity argument, `uc_key` in `UlocCutAux2.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.UlocCut
open HRS.Whole.AppendixA

variable {d : ℕ}

/-- lattice variant on the lattice (⌈√d⌉)⁻¹ ℤ^d. -/
def ulNormLatFine (m : ℕ) (χ : Euc d → ℝ) (u : Euc d → ℝ) : ℝ≥0∞ :=
  ⨆ z : Fin d → ℤ, HRS.Whole.sobolevNormE (m : ℝ) fun x =>
    χ (x - ((⌈Real.sqrt d⌉₊ : ℝ)⁻¹) • HRS.Whole.latticePt z) * u x

/-- the point `(⌈√d⌉)⁻¹ z` of the fine lattice -/
def uc_fp (z : Fin d → ℤ) : Euc d := ((⌈Real.sqrt d⌉₊ : ℝ)⁻¹) • HRS.Whole.latticePt z

theorem uc_fp_add (a b : Fin d → ℤ) : uc_fp a + uc_fp b = uc_fp (a + b) := by
  unfold uc_fp HRS.Whole.latticePt
  ext i
  simp [mul_add]

theorem uc_round (c x : ℝ) (hc : 0 < c) : |x - c * round (x / c)| ≤ c / 2 := by
  have h := abs_sub_round (x / c)
  have e : x - c * round (x / c) = c * (x / c - round (x / c)) := by
    rw [mul_sub, mul_div_cancel₀ _ hc.ne']
  rw [e, abs_mul, abs_of_pos hc]
  nlinarith

theorem uc_fine_approx (p : Euc d) : ∃ k : Fin d → ℤ, ‖p - uc_fp k‖ ≤ 1 / 2 := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    exact ⟨0, by simp [EuclideanSpace.norm_eq]⟩
  set N : ℕ := ⌈Real.sqrt d⌉₊ with hN
  have hsq : Real.sqrt d ≤ (N : ℝ) := Nat.le_ceil _
  have hNpos : (0 : ℝ) < N := by
    have : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
    linarith
  have hdN : (d : ℝ) ≤ (N : ℝ) ^ 2 := (Real.sqrt_le_iff.1 hsq).2
  set c : ℝ := (N : ℝ)⁻¹ with hc
  have hcpos : 0 < c := inv_pos.2 hNpos
  refine ⟨fun i => round (p i / c), ?_⟩
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨by norm_num, ?_⟩
  have hi : ∀ i, ‖(p - uc_fp fun i => round (p i / c)) i‖ ^ 2 ≤ (c / 2) ^ 2 := by
    intro i
    have h1 : (p - uc_fp fun i => round (p i / c)) i = p i - c * round (p i / c) := by
      simp [uc_fp, HRS.Whole.latticePt, hc, hN]
    rw [h1, Real.norm_eq_abs]
    have h2 := uc_round c (p i) hcpos
    exact pow_le_pow_left₀ (by positivity) h2 2
  calc ∑ i, ‖(p - uc_fp fun i => round (p i / c)) i‖ ^ 2 ≤ ∑ _i : Fin d, (c / 2) ^ 2 :=
        Finset.sum_le_sum fun i _ => hi i
    _ = d * (c / 2) ^ 2 := by simp
    _ ≤ (1 / 2) ^ 2 := by
        have : (d : ℝ) * c ^ 2 ≤ 1 := by
          rw [hc, inv_pow]
          rw [← div_eq_mul_inv, div_le_one (by positivity)]
          exact hdN
        nlinarith

/-- a finite subfamily of balls of radius `1` about the centres `c i` covering `closedBall 0 R` -/
theorem uc_cover {ι : Type*} (c : ι → Euc d) (hc : ∀ p : Euc d, ∃ i, ‖p - c i‖ < 1) (R : ℝ) :
    ∃ J : Finset ι, ∀ p : Euc d, ‖p‖ ≤ R → ∃ i ∈ J, ‖p - c i‖ < 1 := by
  have h := (isCompact_closedBall (0 : Euc d) R).elim_finite_subcover
    (fun i => Metric.ball (c i) 1) (fun i => Metric.isOpen_ball) (fun p _ => by
      obtain ⟨i, hi⟩ := hc p
      exact Set.mem_iUnion.2 ⟨i, by simpa [dist_eq_norm] using hi⟩)
  obtain ⟨J, hJ⟩ := h
  refine ⟨J, fun p hp => ?_⟩
  have := hJ (by simpa using hp)
  simp only [Set.mem_iUnion] at this
  obtain ⟨i, hi, hpi⟩ := this
  exact ⟨i, hi, by simpa [dist_eq_norm] using hpi⟩

theorem uc_conj1 (m : ℕ) (χ χ' : Euc d → ℝ) (hχ : IsUlocCutoff χ) (hχ' : IsUlocCutoff χ') :
    ∃ C : ℝ, ∀ u : Euc d → ℝ, ulocNormE m χ u ≤ ENNReal.ofReal C * ulocNormE m χ' u := by
  obtain ⟨Y, hY⟩ := uc_cover (fun y : Euc d => y) (fun p => ⟨p, by simpa using one_pos⟩) (2 + 0)
  obtain ⟨C, hC, h⟩ := uc_key m χ χ' hχ hχ' Y 0 le_rfl
    (fun p hp => by
      obtain ⟨y, hy, hpy⟩ := hY p hp
      exact ⟨y, hy, hpy.le⟩)
  refine ⟨C * Y.card, fun u => ?_⟩
  refine iSup_le fun z => ?_
  refine (h z z (by simp) u).trans ?_
  have : ∑ y ∈ Y, HRS.Whole.sobolevNormE (m : ℝ) (fun x => χ' (x - (z + y)) * u x) ≤
      Y.card • ulocNormE m χ' u :=
    Finset.sum_le_card_nsmul _ _ _ fun y _ => le_iSup (fun z : Euc d =>
      HRS.Whole.sobolevNormE (m : ℝ) fun x => χ' (x - z) * u x) (z + y)
  calc _ ≤ ENNReal.ofReal C * (Y.card • ulocNormE m χ' u) := by gcongr
    _ = ENNReal.ofReal (C * Y.card) * ulocNormE m χ' u := by
        rw [nsmul_eq_mul, ← mul_assoc, ENNReal.ofReal_mul hC.le]
        simp

theorem uc_conj3 (m : ℕ) (χ χ' : Euc d → ℝ) (hχ : IsUlocCutoff χ) (hχ' : IsUlocCutoff χ') :
    ∃ C : ℝ, ∀ u : Euc d → ℝ, ulocNormE m χ u ≤ ENNReal.ofReal C * ulNormLatFine m χ' u := by
  obtain ⟨J, hJ⟩ := uc_cover (uc_fp (d := d)) (fun p => by
    obtain ⟨k, hk⟩ := uc_fine_approx p
    exact ⟨k, by linarith⟩) (2 + 1 / 2)
  obtain ⟨C, hC, h⟩ := uc_key m χ χ' hχ hχ' (J.image uc_fp) (1 / 2) (by norm_num)
    (fun p hp => by
      obtain ⟨j, hj, hpj⟩ := hJ p hp
      exact ⟨uc_fp j, Finset.mem_image_of_mem _ hj, hpj.le⟩)
  refine ⟨C * (J.image uc_fp).card, fun u => ?_⟩
  refine iSup_le fun z => ?_
  obtain ⟨k0, hk0⟩ := uc_fine_approx z
  refine (h z (uc_fp k0) hk0 u).trans ?_
  have : ∑ y ∈ J.image uc_fp, HRS.Whole.sobolevNormE (m : ℝ)
      (fun x => χ' (x - (uc_fp k0 + y)) * u x) ≤ (J.image uc_fp).card • ulNormLatFine m χ' u := by
    refine Finset.sum_le_card_nsmul _ _ _ fun y hy => ?_
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
    rw [uc_fp_add]
    exact le_iSup (fun k : Fin d → ℤ => HRS.Whole.sobolevNormE (m : ℝ) fun x =>
      χ' (x - ((⌈Real.sqrt d⌉₊ : ℝ)⁻¹) • HRS.Whole.latticePt k) * u x) (k0 + j)
  calc _ ≤ ENNReal.ofReal C * ((J.image uc_fp).card • ulNormLatFine m χ' u) := by gcongr
    _ = ENNReal.ofReal (C * (J.image uc_fp).card) * ulNormLatFine m χ' u := by
        rw [nsmul_eq_mul, ← mul_assoc, ENNReal.ofReal_mul hC.le]
        simp

theorem uc_fine_le (m : ℕ) (χ u : Euc d → ℝ) : ulNormLatFine m χ u ≤ ulocNormE m χ u :=
  iSup_le fun k => le_iSup (fun z : Euc d =>
    HRS.Whole.sobolevNormE (m : ℝ) fun x => χ (x - z) * u x) (uc_fp k)

theorem uc_lat_le (m : ℕ) (χ u : Euc d → ℝ) :
    HRS.Whole.AppendixALemmas.ulNormLat m χ u ≤ ulocNormE m χ u :=
  iSup_le fun k => le_iSup (fun z : Euc d =>
    HRS.Whole.sobolevNormE (m : ℝ) fun x => χ (x - z) * u x) (HRS.Whole.cellPt d k)

/-- Lemma S.A.31(i), repaired: the third conjunct uses the lattice `(⌈√d⌉)⁻¹ ℤ^d`. -/
theorem uloc_embedding_cutoffs_fine_proof (m : ℕ) (χ χ' : Euc d → ℝ) (hχ : IsUlocCutoff χ)
    (hχ' : IsUlocCutoff χ') :
    ∃ C : ℝ, ∀ u : Euc d → ℝ,
      ulocNormE m χ u ≤ ENNReal.ofReal C * ulocNormE m χ' u ∧
      ulNormLatFine m χ u ≤ ENNReal.ofReal C * ulocNormE m χ' u ∧
      ulocNormE m χ u ≤ ENNReal.ofReal C * ulNormLatFine m χ' u := by
  obtain ⟨C1, h1⟩ := uc_conj1 m χ χ' hχ hχ'
  obtain ⟨C3, h3⟩ := uc_conj3 m χ χ' hχ hχ'
  refine ⟨max C1 C3, fun u => ?_⟩
  have e1 : ENNReal.ofReal C1 ≤ ENNReal.ofReal (max C1 C3) := ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have e3 : ENNReal.ofReal C3 ≤ ENNReal.ofReal (max C1 C3) := ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have h1' : ulocNormE m χ u ≤ ENNReal.ofReal (max C1 C3) * ulocNormE m χ' u :=
    (h1 u).trans (by gcongr)
  have h3' : ulocNormE m χ u ≤ ENNReal.ofReal (max C1 C3) * ulNormLatFine m χ' u :=
    (h3 u).trans (by gcongr)
  exact ⟨h1', (uc_fine_le m χ u).trans h1', h3'⟩

/-- Lemma S.A.31(i), first two conjuncts for the original lattice `ℤ^d` (true for all `d`). -/
theorem uloc_embedding_cutoffs_12_proof (m : ℕ) (χ χ' : Euc d → ℝ) (hχ : IsUlocCutoff χ)
    (hχ' : IsUlocCutoff χ') :
    ∃ C : ℝ, ∀ u : Euc d → ℝ,
      ulocNormE m χ u ≤ ENNReal.ofReal C * ulocNormE m χ' u ∧
      HRS.Whole.AppendixALemmas.ulNormLat m χ u ≤ ENNReal.ofReal C * ulocNormE m χ' u := by
  obtain ⟨C1, h1⟩ := uc_conj1 m χ χ' hχ hχ'
  exact ⟨C1, fun u => ⟨h1 u, (uc_lat_le m χ u).trans (h1 u)⟩⟩

/-- The repaired frozen lattice norm `ulNormLat` (lattice `cellPt`) equals `ulNormLatFine`. -/
theorem uc_ulNormLat_eq_fine (m : ℕ) (χ u : Euc d → ℝ) :
    HRS.Whole.AppendixALemmas.ulNormLat m χ u = ulNormLatFine m χ u := by
  have h : ((⌈Real.sqrt d⌉ : ℤ) : ℝ) = ((⌈Real.sqrt d⌉₊ : ℕ) : ℝ) := by
    rw [← natCast_ceil_eq_intCast_ceil (Real.sqrt_nonneg _)]
  unfold HRS.Whole.AppendixALemmas.ulNormLat ulNormLatFine HRS.Whole.cellPt
  rw [h]

/-- Lemma S.A.31(i), statement verbatim from the repaired frozen theorem
`HRS.Whole.AppendixALemmas.uloc_embedding_cutoffs` (lattice `cellPt`, repair MS-ULOC-LAT applied). -/
theorem uloc_embedding_cutoffs_proof (m : ℕ) (χ χ' : Euc d → ℝ) (hχ : IsUlocCutoff χ)
    (hχ' : IsUlocCutoff χ') :
    ∃ C : ℝ, ∀ u : Euc d → ℝ,
      ulocNormE m χ u ≤ ENNReal.ofReal C * ulocNormE m χ' u ∧
      HRS.Whole.AppendixALemmas.ulNormLat m χ u ≤ ENNReal.ofReal C * ulocNormE m χ' u ∧
      ulocNormE m χ u ≤ ENNReal.ofReal C * HRS.Whole.AppendixALemmas.ulNormLat m χ' u := by
  obtain ⟨C, h⟩ := uloc_embedding_cutoffs_fine_proof m χ χ' hχ hχ'
  refine ⟨C, fun u => ?_⟩
  obtain ⟨a, b, c⟩ := h u
  refine ⟨a, ?_, ?_⟩
  · rw [uc_ulNormLat_eq_fine]; exact b
  · rw [uc_ulNormLat_eq_fine]; exact c

example := (@uloc_embedding_cutoffs_proof : type_of% @HRS.Whole.AppendixALemmas.uloc_embedding_cutoffs)

end HRS.MS.UlocCut
