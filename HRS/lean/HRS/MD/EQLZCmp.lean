import HRS.MD.EQLZVocab
import HRS.MD.EQLZDet

/-!
# EQ-LZ packet CMP: comparison through the initial density (`eqlz_cmp`), proof

Both measures are finite and are tested against `g₀(z_0) ∏ g_i(z_i)` with smooth factors
(`lzdet_ext_cons`).  The left side is, by `HasFDD` (gap list `t_0, t_1 - t_0, ...`), `∫ g₀ K d(ρπ) = ∫ ρ g₀ K dπ`
(`K` the iterated kernel); the right side is `E' (ρ g₀)(Z'_0) ∏ g_i(Z'_{t_i})`, which `HasFDD` for `Z'` with the
bounded measurable first factor `ρ g₀` also evaluates to `∫ ρ g₀ K dπ`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal
open HRS HRS.MD.EQLZ HRS.MD.EQLZDet

namespace HRS.MD.EQLZCmp

variable {n : ℕ}

/-- The list of (gap, function) pairs of the times `t_0 ≤ ... ≤ t_{k-1}` started at `t0`. -/
def lzcGaps : (k : ℕ) → (Fin k → ℝ) → ℝ → (Fin k → Torus n → ℝ) → List (ℝ × (Torus n → ℝ))
  | 0, _, _, _ => []
  | k + 1, t, t0, g => (t 0 - t0, g 0) :: lzcGaps k (fun i => t i.succ) (t 0) (fun i => g i.succ)

theorem lzcGaps_prod {Ω : Type*} (Z : ℝ → Ω → Torus n) :
    ∀ (k : ℕ) (t : Fin k → ℝ) (t0 : ℝ) (g : Fin k → Torus n → ℝ) (ω : Ω),
      fddProd Z t0 (lzcGaps k t t0 g) ω = ∏ i, g i (Z (t i) ω) := by
  intro k
  induction k with
  | zero => intro t t0 g ω; simp [lzcGaps, fddProd]
  | succ k ih =>
    intro t t0 g ω
    simp only [lzcGaps, fddProd]
    rw [add_sub_cancel, ih (fun i => t i.succ) (t 0) (fun i => g i.succ) ω, Fin.prod_univ_succ]

theorem lzcGaps_adm :
    ∀ (k : ℕ) (t : Fin k → ℝ) (t0 : ℝ) (g : Fin k → Torus n → ℝ), Monotone t → (∀ i, t0 ≤ t i) →
      (∀ i, Torus.IsSmooth (g i)) → ∀ p ∈ lzcGaps k t t0 g, 0 ≤ p.1 ∧ Torus.IsSmooth p.2 := by
  intro k
  induction k with
  | zero => intro t t0 g _ _ _ p hp; simp [lzcGaps] at hp
  | succ k ih =>
    intro t t0 g ht h0 hg p hp
    simp only [lzcGaps, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨sub_nonneg.mpr (h0 0), hg 0⟩
    · exact ih (fun i => t i.succ) (t 0) (fun i => g i.succ)
        (fun i j hij => ht (Fin.succ_le_succ_iff.mpr hij)) (fun i => ht (Fin.zero_le _))
        (fun i => hg i.succ) p hp

theorem eqlz_cmp_proof (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P'] (Z : ℝ → Ω → Torus n) (Z' : ℝ → Ω' → Torus n)
    (hZ : ∀ t : ℝ, 0 ≤ t → Measurable (Z t)) (hZ' : ∀ t : ℝ, 0 ≤ t → Measurable (Z' t))
    (c : ℝ) (ρ : Torus n → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρc : ∀ x, ρ x ≤ c)
    (hfdd : HasFDD hn hκ hU P Z ((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (ρ x)))
    (hfdd' : HasFDD hn hκ hU P' Z' (d1_gibbsMeasure κ U))
    (k : ℕ) (t : Fin k → ℝ) (ht : Monotone t) (ht0 : ∀ i, 0 ≤ t i) :
    P.map (fun ω => (Z 0 ω, fun i => Z (t i) ω)) =
      (P'.map (fun ω => (Z' 0 ω, fun i => Z' (t i) ω))).withDensity (fun p => ENNReal.ofReal (ρ p.1)) := by
  set π := d1_gibbsMeasure κ U with hπ
  have hmeas : ∀ {Ω₁ : Type} [MeasurableSpace Ω₁] (Y : ℝ → Ω₁ → Torus n),
      (∀ t : ℝ, 0 ≤ t → Measurable (Y t)) →
      Measurable (fun ω => (Y 0 ω, fun i => Y (t i) ω)) := by
    intro Ω₁ _ Y hY
    exact (hY 0 le_rfl).prodMk (measurable_pi_iff.mpr fun i => hY _ (ht0 i))
  have hm := hmeas Z hZ
  have hm' := hmeas Z' hZ'
  set m' := P'.map (fun ω => (Z' 0 ω, fun i => Z' (t i) ω)) with hm'def
  have hfin : IsFiniteMeasure (m'.withDensity (fun p => ENNReal.ofReal (ρ p.1))) := by
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    calc ∫⁻ p, ENNReal.ofReal (ρ p.1) ∂m' ≤ ∫⁻ p, ENNReal.ofReal c ∂m' :=
          lintegral_mono fun p => ENNReal.ofReal_le_ofReal (hρc p.1)
      _ < ⊤ := by simp
  apply lzdet_ext_cons
  intro g₀ g hg₀ hg
  have hg₀c := lzdet_continuous hg₀
  have hcont : Continuous (fun p : Torus n × (Fin k → Torus n) => g₀ p.1 * ∏ i, g i (p.2 i)) :=
    (hg₀c.comp continuous_fst).mul
      (continuous_finsetProd _ fun i _ => (lzdet_continuous (hg i)).comp ((continuous_apply i).comp continuous_snd))
  -- the common kernel
  set l := lzcGaps k t 0 g with hl
  have hadm := lzcGaps_adm k t 0 g ht ht0 hg
  obtain ⟨C₀, hC₀⟩ := lzdet_bdd hg₀c
  -- left side
  have hL : ∫ p, g₀ p.1 * ∏ i, g i (p.2 i) ∂(P.map (fun ω => (Z 0 ω, fun i => Z (t i) ω))) =
      ∫ x, ρ x * (g₀ x * fddKer hn hκ hU l x) ∂π := by
    rw [integral_map hm.aemeasurable hcont.aestronglyMeasurable]
    have h := hfdd l hadm g₀ hg₀c.measurable ⟨C₀, hC₀⟩
    have hprodZ : ∀ ω, ∏ i, g i (Z (t i) ω) = fddProd Z 0 l ω := fun ω => (lzcGaps_prod Z k t 0 g ω).symm
    simp only [hprodZ]
    rw [h, integral_withDensity_eq_integral_toReal_smul (hρ.ennreal_ofReal)
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    congr 1; funext x
    rw [ENNReal.toReal_ofReal (hρ0 x), smul_eq_mul]
  -- right side
  have hρg : Measurable (fun x => ρ x * g₀ x) := hρ.mul hg₀c.measurable
  have hbd : ∃ C : ℝ, ∀ x, |ρ x * g₀ x| ≤ C := by
    refine ⟨c * C₀, fun x => ?_⟩
    rw [abs_mul, abs_of_nonneg (hρ0 x)]
    exact mul_le_mul (hρc x) (hC₀ x) (abs_nonneg _) ((hρ0 x).trans (hρc x))
  have hR : ∫ p, g₀ p.1 * ∏ i, g i (p.2 i) ∂(m'.withDensity (fun p => ENNReal.ofReal (ρ p.1))) =
      ∫ x, ρ x * (g₀ x * fddKer hn hκ hU l x) ∂π := by
    rw [integral_withDensity_eq_integral_toReal_smul
      (f := fun p : Torus n × (Fin k → Torus n) => ENNReal.ofReal (ρ p.1))
      (hρ.comp measurable_fst).ennreal_ofReal
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    have e1 : ∀ p : Torus n × (Fin k → Torus n), (ENNReal.ofReal (ρ p.1)).toReal •
        (g₀ p.1 * ∏ i, g i (p.2 i)) = (ρ p.1 * g₀ p.1) * ∏ i, g i (p.2 i) := by
      intro p
      rw [ENNReal.toReal_ofReal (hρ0 p.1), smul_eq_mul, mul_assoc]
    simp only [e1]
    have hc2 : Measurable (fun p : Torus n × (Fin k → Torus n) => (ρ p.1 * g₀ p.1) * ∏ i, g i (p.2 i)) :=
      (hρg.comp measurable_fst).mul
        (Finset.measurable_prod _ fun i _ => (lzdet_continuous (hg i)).measurable.comp
          ((measurable_pi_apply i).comp measurable_snd))
    rw [hm'def, integral_map hm'.aemeasurable hc2.aestronglyMeasurable]
    have h := hfdd' l hadm (fun x => ρ x * g₀ x) hρg hbd
    have hprodZ' : ∀ ω, ∏ i, g i (Z' (t i) ω) = fddProd Z' 0 l ω := fun ω => (lzcGaps_prod Z' k t 0 g ω).symm
    simp only [hprodZ']
    rw [h]
    congr 1; funext x; ring
  rw [hL, hR]

end HRS.MD.EQLZCmp

end
