import HRS.MS.SuppU1Aux3
import HRS.MS.SuppU1Aux8

/-!
# U1 aux 9: the finite-rank approximation of a kernel with a Riesz envelope (generic version).
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.Whole.U1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

lemma u1_tri {α : Type*} [MeasurableSpace α] (P : Measure α) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (f g l : α → ℝ) :
    eLpNorm (fun x => f x - l x) p P
      ≤ eLpNorm (fun x => f x - g x) p P + eLpNorm (fun x => g x - l x) p P := by
  have : (fun x => f x - l x) = (fun x => f x - g x) + (fun x => g x - l x) := by
    funext x; simp
  rw [this]
  exact eLpNorm_add_le hp

lemma u1_symm_Lr (P : Measure (E × E)) (hP : MeasurePreserving Prod.swap P P) {r : ℝ} (hr : 1 ≤ r)
    (G hh : E × E → ℝ) (hG : AEStronglyMeasurable G P) (hhm : AEStronglyMeasurable hh P)
    (hsym : ∀ p : E × E, hh p.swap = hh p) :
    eLpNorm (fun p => (G p + G p.swap) / 2 - hh p) (ENNReal.ofReal r) P
      ≤ eLpNorm (fun p => G p - hh p) (ENNReal.ofReal r) P := by
  have hp1 : 1 ≤ ENNReal.ofReal r := by simpa using ENNReal.ofReal_le_ofReal hr
  set a : E × E → ℝ := fun p => G p - hh p with ha
  have ham : AEStronglyMeasurable a P := hG.sub hhm
  have ha' : AEStronglyMeasurable (a ∘ Prod.swap) P := ham.comp_measurePreserving hP
  have hnorm : eLpNorm (a ∘ Prod.swap) (ENNReal.ofReal r) P = eLpNorm a (ENNReal.ofReal r) P :=
    eLpNorm_comp_measurePreserving ham hP
  have heq : (fun p => (G p + G p.swap) / 2 - hh p) = (1 / 2 : ℝ) • (a + a ∘ Prod.swap) := by
    funext p
    simp only [ha, Pi.smul_apply, Pi.add_apply, Function.comp_apply, smul_eq_mul]
    rw [hsym p]; ring
  rw [heq, eLpNorm_const_smul]
  calc ‖(1 / 2 : ℝ)‖ₑ * eLpNorm (a + a ∘ Prod.swap) (ENNReal.ofReal r) P
      ≤ ‖(1 / 2 : ℝ)‖ₑ * (eLpNorm a (ENNReal.ofReal r) P + eLpNorm (a ∘ Prod.swap) (ENNReal.ofReal r) P) := by
        gcongr
        exact eLpNorm_add_le hp1
    _ = eLpNorm a (ENNReal.ofReal r) P := by
        rw [hnorm, ← two_mul, ← mul_assoc]
        have : ‖(1 / 2 : ℝ)‖ₑ * 2 = 1 := by
          rw [Real.enorm_eq_ofReal (by norm_num)]
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
          norm_num
        rw [this, one_mul]


lemma u1_cut_bound {s B : ℝ} (hB : 0 ≤ B) (h : E → E → ℝ)
    (hbd : ∀ x y, x ≠ y → |h x y| ≤ B * u1Vs s ‖x - y‖) (R : ℕ) (q : E × E) (hq : q.1 ≠ q.2) :
    |u1Cut R h q| ≤ B * u1Vs s ‖q.1 - q.2‖ := by
  by_cases hqS : q ∈ closedBall (0:E) R ×ˢ closedBall (0:E) R
  · simp only [u1Cut, indicator_of_mem hqS]; exact hbd q.1 q.2 hq
  · simp only [u1Cut, indicator_of_notMem hqS, abs_zero]
    exact mul_nonneg hB (by linarith [u1Vs_ge_one (s := s) (norm_nonneg (q.1 - q.2))])

lemma u1_cut_loc {s B : ℝ} (hs : 0 ≤ s) (hsd : s < (Module.finrank ℝ E : ℝ)) (hB : 0 ≤ B)
    (h : E → E → ℝ) (hm : Measurable fun p : E × E => h p.1 p.2)
    (hbd : ∀ x y, x ≠ y → |h x y| ≤ B * u1Vs s ‖x - y‖) (R : ℕ) :
    LocallyIntegrable (u1Cut R h) (μ.prod μ) := by
  have hd0 : (0:ℝ) < Module.finrank ℝ E := lt_of_le_of_lt hs hsd
  have hd : 1 ≤ Module.finrank ℝ E := by exact_mod_cast hd0
  have hbdν : ∀ᵐ q ∂(μ.prod μ), |h q.1 q.2| ≤ B * u1Vs s ‖q.1 - q.2‖ :=
    (u1_ae_offdiag μ hd).mono fun q hq => hbd q.1 q.2 hq
  exact (u1_integrable_cut μ hs hsd (fun p => h p.1 p.2) hm.aestronglyMeasurable B R hB
      (Nat.cast_nonneg R) hbdν).locallyIntegrable

lemma u1_approx {s : ℝ} (hs : 0 ≤ s) (hsd : s < (Module.finrank ℝ E : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℝ) (μ' : Measure E) [IsProbabilityMeasure μ'],
      μ' ≤ ENNReal.ofReal M • μ → ∀ (B : ℝ), 0 < B → ∀ (h : E → E → ℝ),
      Measurable (fun p : E × E => h p.1 p.2) → (∀ x y, h x y = h y x) →
      (∀ x y, x ≠ y → |h x y| ≤ B * u1Vs s ‖x - y‖) →
      ∀ r : ℝ, 1 ≤ r → r * s < (Module.finrank ℝ E : ℝ) → ∀ ε' : ℝ, 0 < ε' →
      ∃ (m : ℕ) (c : Fin m → Fin m → ℝ) (u : Fin m → E → ℝ),
        (∀ a b, c a b = c b a) ∧ (∀ a, ContDiff ℝ ∞ (u a)) ∧ (∀ a, HasCompactSupport (u a)) ∧
        (∀ x y, x ≠ y → |∑ a, ∑ b, c a b * u a x * u b y| ≤ C * B * u1Vs s ‖x - y‖) ∧
        eLpNorm (fun p : E × E => (∑ a, ∑ b, c a b * u a p.1 * u b p.2) - h p.1 p.2)
          (ENNReal.ofReal r) (μ'.prod μ') ≤ ENNReal.ofReal ε' := by
  obtain ⟨C₀, hC₀, henv⟩ := u1_mol_envelope μ hs hsd
  refine ⟨C₀ + 1, by positivity, ?_⟩
  intro M μ' _ hle B hB h hm hsymm hbd r hr hrs ε' hε'
  have hr0 : 0 < r := by linarith
  have hε3 : (0:ℝ) < ε' / 3 := by positivity
  have hε3' : (0 : ℝ≥0∞) < ENNReal.ofReal (ε' / 3) := ENNReal.ofReal_pos.mpr hε3
  have hd0 : (0:ℝ) < Module.finrank ℝ E := lt_of_le_of_lt hs hsd
  have hd : 1 ≤ Module.finrank ℝ E := by exact_mod_cast hd0
  have hp1 : 1 ≤ ENNReal.ofReal r := by simpa using ENNReal.ofReal_le_ofReal hr
  have hmpP : MeasurePreserving Prod.swap (μ'.prod μ') (μ'.prod μ') :=
    Measure.measurePreserving_swap (μ := μ') (ν := μ')
  obtain ⟨R, hR⟩ := ((u1_cut_tendsto μ hs hr0 hrs hB.le μ' hle h hm hbd).eventually
    (gt_mem_nhds hε3')).exists
  obtain ⟨n, hn⟩ := ((u1_mol_tendsto μ hs hsd hr0 hrs hB.le hC₀ μ' hle h hm hbd henv R).eventually
    (gt_mem_nhds hε3')).exists
  set G : E × E → ℝ := u1Mol μ n (u1Cut R h) with hGdef
  have hloc := u1_cut_loc μ hs hsd hB.le h hm hbd R
  have hGc : Continuous G := u1Mol_continuous μ n _ hloc
  have hGenv : ∀ p : E × E, p.1 ≠ p.2 → |G p| ≤ C₀ * B * u1Vs s ‖p.1 - p.2‖ := by
    intro p hp
    have hcutν : ∀ᵐ q ∂(μ.prod μ), |u1Cut R h q| ≤ B * u1Vs s ‖q.1 - q.2‖ :=
      (u1_ae_offdiag μ hd).mono fun q hq => u1_cut_bound hB.le h hbd R q hq
    exact henv (u1Cut R h) B hB.le hcutν n p hp
  set Gs : E × E → ℝ := fun p => (G p + G p.swap) / 2 with hGs
  have hGsc : Continuous Gs := (hGc.add (hGc.comp continuous_swap)).div_const 2
  have hGss : ∀ x y, Gs (x, y) = Gs (y, x) := by
    intro x y; simp only [hGs, Prod.swap_prod_mk]; rw [add_comm]
  have hsupp : ∀ x y, Gs (x, y) ≠ 0 → ‖x‖ ≤ (R : ℝ) + 1 ∧ ‖y‖ ≤ (R : ℝ) + 1 := by
    intro x y hxy
    by_cases h1 : G (x, y) = 0
    · by_cases h2 : G (y, x) = 0
      · exfalso; apply hxy; simp [hGs, h1, h2]
      · have := u1Mol_support μ n R h (y, x) h2; exact ⟨this.2, this.1⟩
    · exact u1Mol_support μ n R h (x, y) h1
  set η : ℝ := min B (ε' / 3) with hη
  obtain ⟨m, c, u, hcs, hsm, hcp, hk⟩ :=
    u1_finiteRank_of_continuous Gs hGsc hGss ((R : ℝ) + 1) η (lt_min hB hε3) hsupp
  have hkc : Continuous (fun p : E × E => ∑ a, ∑ b, c a b * u a p.1 * u b p.2) := by
    refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => ?_
    exact (continuous_const.mul ((hsm a).continuous.comp continuous_fst)).mul
      ((hsm b).continuous.comp continuous_snd)
  refine ⟨m, c, u, hcs, hsm, hcp, ?_, ?_⟩
  · intro x y hxy
    have h1 := hk x y
    have hG1 := hGenv (x, y) hxy
    have hG2 := hGenv (y, x) (Ne.symm hxy)
    simp only [norm_sub_rev y x] at hG2
    simp only at hG1
    have hV := u1Vs_ge_one (s := s) (norm_nonneg (x - y))
    have hηB : η ≤ B := min_le_left _ _
    have hGsb : |Gs (x, y)| ≤ C₀ * B * u1Vs s ‖x - y‖ := by
      simp only [hGs, Prod.swap_prod_mk]
      rw [abs_div, abs_two]
      have := abs_add_le (G (x, y)) (G (y, x))
      linarith
    calc |∑ a, ∑ b, c a b * u a x * u b y|
        = |Gs (x, y) - (Gs (x, y) - ∑ a, ∑ b, c a b * u a x * u b y)| := by ring_nf
      _ ≤ |Gs (x, y)| + |Gs (x, y) - ∑ a, ∑ b, c a b * u a x * u b y| := abs_sub _ _
      _ ≤ (C₀ + 1) * B * u1Vs s ‖x - y‖ := by nlinarith
  · have hhm : AEStronglyMeasurable (fun p : E × E => h p.1 p.2) (μ'.prod μ') := hm.aestronglyMeasurable
    have hcutm : Measurable (u1Cut R h) :=
      hm.indicator (measurableSet_closedBall.prod measurableSet_closedBall)
    calc eLpNorm (fun p : E × E => (∑ a, ∑ b, c a b * u a p.1 * u b p.2) - h p.1 p.2)
          (ENNReal.ofReal r) (μ'.prod μ')
        ≤ eLpNorm (fun p : E × E => (∑ a, ∑ b, c a b * u a p.1 * u b p.2) - Gs p)
            (ENNReal.ofReal r) (μ'.prod μ')
          + eLpNorm (fun p : E × E => Gs p - h p.1 p.2) (ENNReal.ofReal r) (μ'.prod μ') :=
          u1_tri _ hp1 _ _ _
      _ ≤ ENNReal.ofReal η + eLpNorm (fun p : E × E => G p - h p.1 p.2) (ENNReal.ofReal r)
            (μ'.prod μ') := by
          gcongr
          · have := eLpNorm_le_of_ae_bound (μ := μ'.prod μ') (p := ENNReal.ofReal r)
              (f := fun p : E × E => (∑ a, ∑ b, c a b * u a p.1 * u b p.2) - Gs p)
              (hkc.sub hGsc).aestronglyMeasurable (C := η)
              (ae_of_all _ fun p => by
                rw [Real.norm_eq_abs, abs_sub_comm]; exact hk p.1 p.2)
            simpa using this
          · exact u1_symm_Lr (μ'.prod μ') hmpP hr G (fun p => h p.1 p.2) hGc.aestronglyMeasurable
              hhm (fun p => by simp [hsymm p.1 p.2])
      _ ≤ ENNReal.ofReal η + (eLpNorm (fun p : E × E => G p - u1Cut R h p) (ENNReal.ofReal r)
            (μ'.prod μ') + eLpNorm (fun p : E × E => u1Cut R h p - h p.1 p.2) (ENNReal.ofReal r)
            (μ'.prod μ')) := by
          gcongr
          exact u1_tri _ hp1 _ _ _
      _ ≤ ENNReal.ofReal (ε' / 3) + (ENNReal.ofReal (ε' / 3) + ENNReal.ofReal (ε' / 3)) := by
          gcongr
          exact min_le_right _ _
      _ = ENNReal.ofReal ε' := by
          rw [← ENNReal.ofReal_add hε3.le hε3.le, ← ENNReal.ofReal_add hε3.le (by positivity)]
          congr 1; ring

end HRS.Whole.U1
