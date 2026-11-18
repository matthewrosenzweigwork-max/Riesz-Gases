import Mathlib
import HRS.MS.UniqG1Gronwall
import HRS.MS.UniqG1Meas

/-!
# G2b: abstract closing lemma (real analysis only)

Setting: centres `c : ι` with local energies `F c τ`, dissipation densities `D c τ`, supremum energy
`X τ = ⨆ c, F c τ` on `Icc 0 t`, neighbour sets `S c` of cardinality `≤ N`.

Route.  Fix `τ ∈ Icc 0 t`, put `R := C * ∫_0^τ X + η τ`, `A c := ∫_0^τ D c`, `a := ⨆ c, A c`.
From the hypothesis `h1` (dropping `F c τ ≥ 0`) we get `ν A c ≤ R + δ' N a` for every `c`; taking the
supremum gives `ν a ≤ R + δ' N a`, hence `δ' N a ≤ (ν/2) a ≤ R`.  Therefore `F c τ ≤ 2R` for all `c`,
so `X τ ≤ 2 R ≤ 2 (C ∫_0^τ X + η t)`.  The corollary feeds this into the Gronwall lemma
`g1_gronwall_source_paren` with `a := 2C`, `δ := 2 η t`.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace HRS.MS.UniqG2b

/-- `∫_0^τ D ≤ ∫_0^t D` for a nonnegative integrable `D` on `[0,t]`. -/
theorem g2b_int_le_total (D : ℝ → ℝ) (t τ : ℝ) (hτ : τ ∈ Set.Icc 0 t)
    (hD0 : ∀ σ ∈ Set.Icc 0 t, 0 ≤ D σ) (hDi : IntervalIntegrable D volume 0 t) :
    ∫ σ in (0:ℝ)..τ, D σ ≤ ∫ σ in (0:ℝ)..t, D σ := by
  have hsub1 : Set.uIcc 0 τ ⊆ Set.uIcc 0 t :=
    Set.uIcc_subset_uIcc Set.left_mem_uIcc (Set.mem_uIcc_of_le hτ.1 hτ.2)
  have hsub2 : Set.uIcc τ t ⊆ Set.uIcc 0 t :=
    Set.uIcc_subset_uIcc (Set.mem_uIcc_of_le hτ.1 hτ.2) Set.right_mem_uIcc
  have h1 : IntervalIntegrable D volume 0 τ := hDi.mono_set hsub1
  have h2 : IntervalIntegrable D volume τ t := hDi.mono_set hsub2
  have hnn : 0 ≤ ∫ σ in τ..t, D σ :=
    intervalIntegral.integral_nonneg hτ.2 fun σ hσ => hD0 σ ⟨hτ.1.trans hσ.1, hσ.2⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  linarith

/-- Closing estimate: `X τ ≤ 2 (C ∫_0^τ X + η t)` on `Icc 0 t`. -/
theorem g2b_closing {ι : Type*} [Nonempty ι] (t ν C η δ' : ℝ) (N : ℕ) (S : ι → Finset ι)
    (F D : ι → ℝ → ℝ) (X : ℝ → ℝ) (ht : 0 ≤ t) (hν : 0 < ν) (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hδ' : 0 ≤ δ') (hN : ∀ c, (S c).card ≤ N) (hsmall : δ' * N ≤ ν / 2)
    (hF0 : ∀ c, ∀ τ ∈ Set.Icc 0 t, 0 ≤ F c τ)
    (hFB : ∃ B0, ∀ c, ∀ τ ∈ Set.Icc 0 t, F c τ ≤ B0)
    (hFc : ∀ c, ContinuousOn (F c) (Set.Icc 0 t))
    (hX : ∀ τ ∈ Set.Icc 0 t, X τ = ⨆ c, F c τ)
    (hD0 : ∀ c, ∀ τ ∈ Set.Icc 0 t, 0 ≤ D c τ)
    (hDint : ∀ c, IntervalIntegrable (D c) MeasureTheory.volume 0 t)
    (hDB : ∃ B1, ∀ c, ∫ σ in (0:ℝ)..t, D c σ ≤ B1)
    (hXint : IntervalIntegrable X MeasureTheory.volume 0 t)
    (h1 : ∀ c, ∀ τ ∈ Set.Icc 0 t, F c τ + ν * ∫ σ in (0:ℝ)..τ, D c σ ≤
      C * (∫ σ in (0:ℝ)..τ, X σ) + η * τ + δ' * ∑ c' ∈ S c, ∫ σ in (0:ℝ)..τ, D c' σ) :
    ∀ τ ∈ Set.Icc 0 t, X τ ≤ 2 * (C * (∫ σ in (0:ℝ)..τ, X σ) + η * t) := by
  obtain ⟨B1, hB1⟩ := hDB
  intro τ hτ
  have hAnn : ∀ c, 0 ≤ ∫ σ in (0:ℝ)..τ, D c σ := fun c =>
    intervalIntegral.integral_nonneg hτ.1 fun σ hσ => hD0 c σ ⟨hσ.1, hσ.2.trans hτ.2⟩
  have hAB : ∀ c, ∫ σ in (0:ℝ)..τ, D c σ ≤ B1 := fun c =>
    (g2b_int_le_total (D c) t τ hτ (hD0 c) (hDint c)).trans (hB1 c)
  have hAbdd : BddAbove (Set.range fun c => ∫ σ in (0:ℝ)..τ, D c σ) :=
    ⟨B1, by rintro _ ⟨c, rfl⟩; exact hAB c⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = ⨆ c, ∫ σ in (0:ℝ)..τ, D c σ := ⟨_, rfl⟩
  have hAc : ∀ c, ∫ σ in (0:ℝ)..τ, D c σ ≤ a := fun c => by
    rw [ha]; exact le_ciSup hAbdd c
  have ha0 : 0 ≤ a := by
    rw [ha]; exact Real.iSup_nonneg hAnn
  -- sum over neighbours
  have hsumle : ∀ c, δ' * ∑ c' ∈ S c, ∫ σ in (0:ℝ)..τ, D c' σ ≤ δ' * (N * a) := fun c => by
    apply mul_le_mul_of_nonneg_left _ hδ'
    calc ∑ c' ∈ S c, ∫ σ in (0:ℝ)..τ, D c' σ ≤ ∑ c' ∈ S c, a :=
          Finset.sum_le_sum fun c' _ => hAc c'
      _ = ((S c).card : ℝ) * a := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * a := mul_le_mul_of_nonneg_right (by exact_mod_cast hN c) ha0
  -- supremum over centres: `ν a ≤ R + δ' N a`
  have hsup : a ≤ (C * (∫ σ in (0:ℝ)..τ, X σ) + η * τ + δ' * (N * a)) / ν := by
    refine ha.le.trans (ciSup_le fun c => ?_)
    rw [le_div_iff₀ hν]
    have hc := h1 c τ hτ
    have hF := hF0 c τ hτ
    have hs := hsumle c
    linarith [hAnn c]
  have hsup' : a * ν ≤ C * (∫ σ in (0:ℝ)..τ, X σ) + η * τ + δ' * (N * a) :=
    (le_div_iff₀ hν).1 hsup
  have hhalf : δ' * (N * a) ≤ ν / 2 * a := by
    calc δ' * (N * a) = (δ' * N) * a := by ring
      _ ≤ ν / 2 * a := mul_le_mul_of_nonneg_right hsmall ha0
  have hRb : δ' * (N * a) ≤ C * (∫ σ in (0:ℝ)..τ, X σ) + η * τ := by
    linarith
  have hFb : ∀ c, F c τ ≤ 2 * (C * (∫ σ in (0:ℝ)..τ, X σ) + η * τ) := by
    intro c
    have hc := h1 c τ hτ
    have hs := hsumle c
    have hnu : 0 ≤ ν * ∫ σ in (0:ℝ)..τ, D c σ := mul_nonneg hν.le (hAnn c)
    linarith
  have hηt : η * τ ≤ η * t := mul_le_mul_of_nonneg_left hτ.2 hη
  rw [hX τ hτ]
  refine ciSup_le fun c => ?_
  linarith [hFb c]

/-- Gronwall form of the closing estimate: `X τ ≤ 2 η t exp(2 C τ)` on `Icc 0 t`. -/
theorem g2b_closing_gronwall {ι : Type*} [Nonempty ι] (t ν C η δ' : ℝ) (N : ℕ) (S : ι → Finset ι)
    (F D : ι → ℝ → ℝ) (X : ℝ → ℝ) (ht : 0 ≤ t) (hν : 0 < ν) (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hδ' : 0 ≤ δ') (hN : ∀ c, (S c).card ≤ N) (hsmall : δ' * N ≤ ν / 2)
    (hF0 : ∀ c, ∀ τ ∈ Set.Icc 0 t, 0 ≤ F c τ)
    (hFB : ∃ B0, ∀ c, ∀ τ ∈ Set.Icc 0 t, F c τ ≤ B0)
    (hFc : ∀ c, ContinuousOn (F c) (Set.Icc 0 t))
    (hX : ∀ τ ∈ Set.Icc 0 t, X τ = ⨆ c, F c τ)
    (hD0 : ∀ c, ∀ τ ∈ Set.Icc 0 t, 0 ≤ D c τ)
    (hDint : ∀ c, IntervalIntegrable (D c) MeasureTheory.volume 0 t)
    (hDB : ∃ B1, ∀ c, ∫ σ in (0:ℝ)..t, D c σ ≤ B1)
    (hXint : IntervalIntegrable X MeasureTheory.volume 0 t)
    (h1 : ∀ c, ∀ τ ∈ Set.Icc 0 t, F c τ + ν * ∫ σ in (0:ℝ)..τ, D c σ ≤
      C * (∫ σ in (0:ℝ)..τ, X σ) + η * τ + δ' * ∑ c' ∈ S c, ∫ σ in (0:ℝ)..τ, D c' σ) :
    ∀ τ ∈ Set.Icc 0 t, X τ ≤ 2 * η * t * Real.exp (2 * C * τ) := by
  have hclose := g2b_closing t ν C η δ' N S F D X ht hν hC hη hδ' hN hsmall hF0 hFB hFc hX hD0
    hDint hDB hXint h1
  have hXnn : ∀ τ ∈ Set.Icc 0 t, 0 ≤ X τ := fun τ hτ => by
    rw [hX τ hτ]; exact Real.iSup_nonneg fun c => hF0 c τ hτ
  obtain ⟨B0, hB0⟩ := hFB
  obtain ⟨B', hB'⟩ := HRS.MS.UniqG1.g1_iSup_bdd F t ⟨B0, hB0⟩ ‹Nonempty ι›
  have hmeas0 := HRS.MS.UniqG1.g1_iSup_measurable F t hFc ⟨B0, hB0⟩ ‹Nonempty ι›
  have hmeas : AEStronglyMeasurable X (volume.restrict (Set.Icc 0 t)) :=
    hmeas0.congr (ae_restrict_of_forall_mem measurableSet_Icc fun τ hτ => (hX τ hτ).symm)
  refine HRS.MS.UniqG1.g1_gronwall_source_paren X t (2 * C) (2 * η * t)
    (mul_nonneg zero_le_two hC) (mul_nonneg (mul_nonneg zero_le_two hη) ht) hXnn
    ⟨B', fun τ hτ => by rw [hX τ hτ]; exact hB' τ hτ⟩ hmeas (fun τ hτ => ?_)
  have := hclose τ hτ
  linarith

end HRS.MS.UniqG2b
