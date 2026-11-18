import HRS.Energy.Commutator.RenormStj0Point

/-!
# Route S, packet STJ: the integrated master inequality for `d = 1`, `s = 0`
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS.Commutator.Renorm

namespace HRS.Commutator.Stj

theorem split_bound2 {ι : Type*} [Fintype ι] (w a1 a2 c : ℝ) (mm tt : ι → ℝ) (hw : 0 ≤ w) (hc : 0 ≤ c)
    (hmm : ∀ i, 0 ≤ mm i) (htt : ∀ i, 0 ≤ tt i) :
    ENNReal.ofReal w * ENNReal.ofReal (a1 + a2 + c * ∑ i, mm i + c * ∑ i, tt i) ≤
      ENNReal.ofReal (w * a1) + ENNReal.ofReal (w * a2) +
        ∑ i, ENNReal.ofReal c * (ENNReal.ofReal w * ENNReal.ofReal (mm i)) +
        ∑ i, ENNReal.ofReal c * (ENNReal.ofReal w * ENNReal.ofReal (tt i)) := by
  have h := split_bound w a1 a2 0 c mm tt hw hc hmm htt
  simpa using h

/-- the `l`-integral of a sum of masses -/
theorem piece_massSum {Cm : ℝ}
    (hmass : ∀ η : ℝ, 0 < η → η < 1 / 2 →
      IntegrableOn (fun l : ℝ => l ^ (-bexp 1 0) * mass 1 l η) (Ioi 0) ∧
      ∫ l in Ioi (0 : ℝ), l ^ (-bexp 1 0) * mass 1 l η ≤ Cm * η⁻¹)
    {N : ℕ} (c ρ : Fin N → ℝ) (hc : ∀ i, 0 ≤ c i) (hρ : ∀ i, 0 < ρ i ∧ ρ i < 1 / 2) :
    IntegrableOn (fun l : ℝ => l ^ (-bexp 1 0) * ∑ i, c i * mass 1 l (ρ i)) (Ioi 0) ∧
    ∫ l in Ioi (0 : ℝ), l ^ (-bexp 1 0) * ∑ i, c i * mass 1 l (ρ i) ≤ ∑ i, c i * (Cm * (ρ i)⁻¹) := by
  have hrw : ∀ l : ℝ, l ^ (-bexp 1 0) * ∑ i, c i * mass 1 l (ρ i) =
      ∑ i, c i * (l ^ (-bexp 1 0) * mass 1 l (ρ i)) := fun l => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [hrw]
  have hI : ∀ i, IntegrableOn (fun l : ℝ => c i * (l ^ (-bexp 1 0) * mass 1 l (ρ i))) (Ioi 0) :=
    fun i => ((hmass (ρ i) (hρ i).1 (hρ i).2).1).const_mul _
  refine ⟨integrable_finset_sum _ fun i _ => hI i, ?_⟩
  rw [integral_finset_sum _ fun i _ => hI i]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hmass (ρ i) (hρ i).1 (hρ i).2).2 (hc i)

/-- the shape of the lower-order terms of the integrated energy majorants -/
def Q1 {N : ℕ} (Λ : ℝ) (η : Fin N → ℝ) : ℝ := (1 / (N : ℝ)) + (1 + Λ) * (1 / (N : ℝ)) * ∑ i, η i

set_option maxHeartbeats 8000000 in
theorem stj_raw0 {c : ℝ} (hc : 0 < c)
    (hker : ∀ x : Torus 1, x ≠ 0 →
      periodicRiesz 1 0 x = c * ∫ l in Ioi (0 : ℝ), l ^ (-bexp 1 0) * sliceG 1 l x) :
    ∃ CQ Ksg KE KM KT1 KT2 Cm Kb : ℝ, 0 ≤ CQ ∧ 0 ≤ Ksg ∧ 0 ≤ KE ∧ 0 ≤ KM ∧ 0 ≤ KT1 ∧ 0 ≤ KT2 ∧ 0 ≤ Cm ∧
      0 ≤ Kb ∧
    ∀ {N : ℕ}, 2 ≤ N → ∀ {Λ : ℝ}, 1 ≤ Λ → ∀ {ρ : Torus 1 → ℝ}, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ {X : Config 1 N}, X ∉ collisionSet 1 N → ∀ {L : ℝ}, 0 ≤ L → ∀ {v : Torus 1 → Euc 1},
      IsLipschitzVF L v →
      ∃ η : Fin N → ℝ, (∀ i, smearRadius Λ X i / 2 < η i ∧ η i < smearRadius Λ X i) ∧
        ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp 1 0)) *
            ENNReal.ofReal |offDiagPairing (commKernel (SliceAux.sgv l) v) X (withDensityReal ρ)| ≤
          ENNReal.ofReal (
            CQ * L * ((2 / c) * rieszEnergy 1 0 X (withDensityReal ρ) + c⁻¹ * Sig0 η + KE * Q1 Λ η) +
            4 * L * Ksg * Cm * (1 / (N : ℝ)) +
            (2 / (N : ℝ)) * ∑ i, Λ * L * (KM * η i) +
            ((2 / (N : ℝ)) * ∑ _i : Fin N, L * (KT1 / N) +
            (2 / (N : ℝ)) * (L * KT2 * N) * (2 * ((2 / c) * rieszEnergy 1 0 X (withDensityReal ρ) +
              c⁻¹ * Sig0 (fun i => smearRadius Λ X i / 4) + KE * Q1 Λ (fun i => smearRadius Λ X i / 4)) +
              Kb * (1 / (N : ℝ))))) := by
  obtain ⟨CQ, Ksg, hCQ, hKsg, hPP⟩ := P_pointwise0
  obtain ⟨KE, hKE0, hEint⟩ := Ebar0_integral hc hker
  obtain ⟨KM, hKM0, hKM⟩ := muMaj_lintegral (d := 1) le_rfl (s := 0) le_rfl (by norm_num) (by norm_num)
  obtain ⟨KT1, KT2, hKT10, hKT20, hT⟩ := T_i_total (d := 1) le_rfl (s := 0) le_rfl (by norm_num) (by norm_num)
  obtain ⟨Cm, hCm0, hCm⟩ := mass_integral (d := 1) le_rfl (s := 0) le_rfl (by norm_num) (by norm_num)
  obtain ⟨Kc, hKc0, hKc⟩ := Qi_int_le_d1
  set ω : ℝ := (volume : Measure (Euc 1)).real (Metric.ball 0 1) with hω
  have hω0 : 0 ≤ ω := measureReal_nonneg
  refine ⟨CQ, Ksg, KE, KM, KT1, KT2, Cm, 32 * Kc ^ 2 * ω * Cm, hCQ, hKsg, hKE0, hKM0, hKT10, hKT20, hCm0,
    by positivity, ?_⟩
  have hmassI : ∀ η : ℝ, 0 < η → η < 1 / 2 →
      IntegrableOn (fun l : ℝ => l ^ (-bexp 1 0) * mass 1 l η) (Ioi 0) ∧
      ∫ l in Ioi (0 : ℝ), l ^ (-bexp 1 0) * mass 1 l η ≤ Cm * η⁻¹ := by
    intro η hη hη2
    obtain ⟨h1, h2⟩ := hCm η hη hη2
    refine ⟨h1, h2.trans (le_of_eq ?_)⟩
    have : ((1 : ℕ) : ℝ) - 2 - 0 = -1 := by norm_num
    rw [this, Real.rpow_neg_one]
  intro N hN Λ hΛ ρ hρ hρΛ X hX L hL v hv
  have hN0 : N ≠ 0 := by omega
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  set μ := withDensityReal ρ with hμdef
  haveI : IsProbabilityMeasure μ := isProb_withDensityReal hρ
  have hΛ0 : 0 ≤ Λ := by linarith
  have hμ : μ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus 1)) := withDensityReal_le_smul' hρΛ
  have hμ1 : μ Set.univ = 1 := measure_univ
  have hX' : ∀ i j, i ≠ j → X i ≠ X j := fun i j hij h => hX ⟨i, j, hij, h⟩
  obtain ⟨hr0, hrl, hr8, hsep⟩ := radii_facts (d := 1) le_rfl hN hΛ X hX'
  set r : Fin N → ℝ := fun i => smearRadius Λ X i with hr
  have hpick : ∀ i, ∃ t ∈ Ioo (r i / 2) (r i),
      (∫⁻ x, Phi 1 0 (r i) (fun l => fieldF l X μ i) x ∂(chC 1 t (X i))) *
        ((volume : Measure (Euc 1)).toSphere univ * ENNReal.ofReal ((r i / 2) ^ 1)) ≤
      ∫⁻ x : Torus 1, (if r i / 2 < KernelGrad.tdist x (X i) ∧ KernelGrad.tdist x (X i) < r i then
        Phi 1 0 (r i) (fun l => fieldF l X μ i) x else 0) := fun i =>
    sphere_pick (d := 1) le_rfl (hr0 i) (by linarith [hr8 i]) (X i) _
      (measurable_Phi 1 0 (r i) (measurable_fieldF_uncurry X μ i))
  choose η hηmem hηpick using hpick
  refine ⟨η, fun i => ⟨(hηmem i).1, (hηmem i).2⟩, ?_⟩
  have hη : ∀ i, 0 < η i ∧ η i ≤ 1 / 8 := fun i =>
    ⟨by linarith [(hηmem i).1, hr0 i], by linarith [(hηmem i).2, hr8 i]⟩
  have hη2 : ∀ i, 0 < η i ∧ η i < 1 / 2 := fun i => ⟨(hη i).1, by linarith [(hη i).2]⟩
  have hdisj : ∀ i j, i ≠ j → η i + η j < KernelGrad.tdist (X i) (X j) := fun i j hij => by
    have := hsep i j hij; have := (hηmem i).2; have := (hηmem j).2; linarith
  set η0 : Fin N → ℝ := fun i => r i / 4 with hη0def
  have hη0 : ∀ i, 0 < η0 i ∧ η0 i ≤ 1 / 8 := fun i => ⟨by have := hr0 i; simp only [hη0def]; positivity,
    by have := hr8 i; simp only [hη0def]; linarith⟩
  have hη02 : ∀ i, 0 < η0 i ∧ η0 i < 1 / 2 := fun i => ⟨(hη0 i).1, by linarith [(hη0 i).2]⟩
  have hdisj0 : ∀ i j, i ≠ j → η0 i + η0 j < KernelGrad.tdist (X i) (X j) := fun i j hij => by
    have := hsep i j hij; have := hr0 i; have := hr0 j; simp only [hη0def]; linarith
  -- the integrals of the real majorants
  have hE : ∀ η : Fin N → ℝ, (∀ i, 0 < η i ∧ η i ≤ 1 / 8) →
      IntegrableOn (fun l : ℝ => l ^ (-bexp 1 0) * Ebar0 X η μ Λ l) (Ioi 0) ∧
      ∫ l in Ioi (0 : ℝ), l ^ (-bexp 1 0) * Ebar0 X η μ Λ l ≤
        (2 / c) * rieszEnergy 1 0 X μ + c⁻¹ * Sig0 η + KE * Q1 Λ η :=
    fun η hη => hEint hN0 X hX' η hη hΛ0 hρΛ
  obtain ⟨hEi, hEb'⟩ := hE η hη
  obtain ⟨hEi0, hEb0'⟩ := hE η0 hη0
  have hCQL : 0 ≤ CQ * L := mul_nonneg hCQ hL
  have hΛL : 0 ≤ Λ * L := mul_nonneg hΛ0 hL
  obtain ⟨hf1, hB1, hm1⟩ := piece_scaled hEi
    (fun l hl => Ebar0_nonneg hN0 hl hη hdisj hμ hμ1 hΛ0) hCQL hEb'
  -- the self blocks
  have hSBform : ∀ l : ℝ, SBmaj Ksg L η l =
      ∑ i, ((1 / (N : ℝ)) ^ 2 * (L * (4 * Ksg * η i))) * mass 1 l (η i) := fun l => by
    unfold SBmaj; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have hcSB : ∀ i, 0 ≤ (1 / (N : ℝ)) ^ 2 * (L * (4 * Ksg * η i)) := fun i => by
    have := (hη i).1; positivity
  obtain ⟨hSBi, hSBb⟩ := piece_massSum hmassI (fun i => (1 / (N : ℝ)) ^ 2 * (L * (4 * Ksg * η i))) η hcSB hη2
  have hSBint : IntegrableOn (fun l : ℝ => l ^ (-bexp 1 0) * SBmaj Ksg L η l) (Ioi 0) :=
    hSBi.congr_fun (fun l _ => by rw [hSBform]) measurableSet_Ioi
  have hSBnn : ∀ l ∈ Ioi (0 : ℝ), 0 ≤ l ^ (-bexp 1 0) * SBmaj Ksg L η l := fun l hl => by
    refine mul_nonneg (Real.rpow_nonneg (le_of_lt hl) _) ?_
    unfold SBmaj
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => ?_)
    have := (hη i).1
    have hm : 0 ≤ mass 1 l (η i) := mass_nonneg 1 l (η i)
    positivity
  have hSBle : ∫ l in Ioi (0 : ℝ), l ^ (-bexp 1 0) * SBmaj Ksg L η l ≤ 4 * L * Ksg * Cm * (1 / (N : ℝ)) := by
    have e1 : ∫ l in Ioi (0 : ℝ), l ^ (-bexp 1 0) * SBmaj Ksg L η l =
        ∫ l in Ioi (0 : ℝ), l ^ (-bexp 1 0) * ∑ i, ((1 / (N : ℝ)) ^ 2 * (L * (4 * Ksg * η i))) * mass 1 l (η i) :=
      integral_congr_ae (Filter.Eventually.of_forall fun l => by simp only [hSBform])
    rw [e1]
    refine hSBb.trans (le_of_eq ?_)
    have e2 : ∀ i, (1 / (N : ℝ)) ^ 2 * (L * (4 * Ksg * η i)) * (Cm * (η i)⁻¹) =
        (1 / (N : ℝ)) ^ 2 * (4 * L * Ksg * Cm) := fun i => by
      have := (hη i).1.ne'
      field_simp
    simp only [e2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  obtain ⟨hf2, hB2, hm2⟩ := lint_bound hSBint hSBnn hSBle
  -- the `μ` blocks
  have hKM' : ∀ η : ℝ, 0 < η → η ≤ 1 / 8 → ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp 1 0)) *
      ENNReal.ofReal (muMaj 1 l η) ≤ ENNReal.ofReal (KM * η ^ (((1 : ℕ) : ℝ) - 0)) := hKM
  have hf4 := piece_muMaj (d := 1) le_rfl (s := 0) hKM' hη (c := 2 / (N : ℝ)) (Λ := Λ) (L := L)
    (by positivity) hΛL hKM0
  have hexp : ∀ x : ℝ, x ^ (((1 : ℕ) : ℝ) - 0) = x := fun x => by simp
  simp only [hexp] at hf4
  have hm4 := aemeas_muMaj_sum (d := 1) (s := 0) le_rfl hη (2 / (N : ℝ)) Λ L
  -- the auxiliary energy
  have hcBm : ∀ i, 0 ≤ 2 * (1 / (N : ℝ)) ^ 2 * (4 * Kc ^ 2 * (r i * ω)) := fun i => by
    have := hr0 i; positivity
  have hBform : ∀ l : ℝ, 2 * (1 / (N : ℝ)) ^ 2 * ∑ i, 4 * Kc ^ 2 * mass 1 l (r i / 4) * (r i * ω) =
      ∑ i, (2 * (1 / (N : ℝ)) ^ 2 * (4 * Kc ^ 2 * (r i * ω))) * mass 1 l (η0 i) := fun l => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by simp only [hη0def]; ring
  obtain ⟨hBi, hBb⟩ := piece_massSum hmassI (fun i => 2 * (1 / (N : ℝ)) ^ 2 * (4 * Kc ^ 2 * (r i * ω))) η0
    hcBm hη02
  have hBsum : ∑ i, 2 * (1 / (N : ℝ)) ^ 2 * (4 * Kc ^ 2 * (r i * ω)) * (Cm * (η0 i)⁻¹) =
      32 * Kc ^ 2 * ω * Cm * (1 / (N : ℝ)) := by
    have e : ∀ i, 2 * (1 / (N : ℝ)) ^ 2 * (4 * Kc ^ 2 * (r i * ω)) * (Cm * (η0 i)⁻¹) =
        (1 / (N : ℝ)) ^ 2 * (32 * Kc ^ 2 * ω * Cm) := fun i => by
      have hri : r i ≠ 0 := (hr0 i).ne'
      simp only [hη0def]
      field_simp
      ring
    simp only [e, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hBnn : ∀ l ∈ Ioi (0 : ℝ), 0 ≤ l ^ (-bexp 1 0) *
      (2 * (1 / (N : ℝ)) ^ 2 * ∑ i, 4 * Kc ^ 2 * mass 1 l (r i / 4) * (r i * ω)) := fun l hl => by
    refine mul_nonneg (Real.rpow_nonneg (le_of_lt hl) _) (mul_nonneg (by positivity)
      (Finset.sum_nonneg fun i _ => ?_))
    have := hr0 i
    have hm : 0 ≤ mass 1 l (r i / 4) := mass_nonneg 1 l _
    positivity
  obtain ⟨hZ, hZnn, -⟩ : (∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp 1 0)) *
        ENNReal.ofReal (2 * Ebar0 X (fun i => r i / 4) μ Λ l + 2 * (1 / (N : ℝ)) ^ 2 *
          ∑ i, 4 * Kc ^ 2 * mass 1 l (r i / 4) * (r i * ω))) ≤
      ENNReal.ofReal (2 * ((2 / c) * rieszEnergy 1 0 X μ + c⁻¹ * Sig0 η0 + KE * Q1 Λ η0) +
        32 * Kc ^ 2 * ω * Cm * (1 / (N : ℝ))) ∧
      0 ≤ 2 * ((2 / c) * rieszEnergy 1 0 X μ + c⁻¹ * Sig0 η0 + KE * Q1 Λ η0) +
        32 * Kc ^ 2 * ω * Cm * (1 / (N : ℝ)) ∧ True := by
    have hfi : IntegrableOn (fun l : ℝ => 2 * (l ^ (-bexp 1 0) * Ebar0 X η0 μ Λ l) +
        l ^ (-bexp 1 0) * (2 * (1 / (N : ℝ)) ^ 2 * ∑ i, 4 * Kc ^ 2 * mass 1 l (r i / 4) * (r i * ω))) (Ioi 0) := by
      have hB' : IntegrableOn (fun l : ℝ => l ^ (-bexp 1 0) *
          (2 * (1 / (N : ℝ)) ^ 2 * ∑ i, 4 * Kc ^ 2 * mass 1 l (r i / 4) * (r i * ω))) (Ioi 0) :=
        hBi.congr_fun (fun l _ => by rw [hBform]) measurableSet_Ioi
      exact (hEi0.const_mul 2).add hB'
    have h0 : ∀ l ∈ Ioi (0 : ℝ), 0 ≤ 2 * (l ^ (-bexp 1 0) * Ebar0 X η0 μ Λ l) +
        l ^ (-bexp 1 0) * (2 * (1 / (N : ℝ)) ^ 2 * ∑ i, 4 * Kc ^ 2 * mass 1 l (r i / 4) * (r i * ω)) :=
      fun l hl => by
        have h1 := Ebar0_nonneg hN0 hl hη0 hdisj0 hμ hμ1 hΛ0
        have h3 : 0 ≤ l ^ (-bexp 1 0) := Real.rpow_nonneg (le_of_lt hl) _
        have h4 := hBnn l hl
        positivity
    have hint : ∫ l in Ioi (0 : ℝ), (2 * (l ^ (-bexp 1 0) * Ebar0 X η0 μ Λ l) +
        l ^ (-bexp 1 0) * (2 * (1 / (N : ℝ)) ^ 2 * ∑ i, 4 * Kc ^ 2 * mass 1 l (r i / 4) * (r i * ω))) ≤
        2 * ((2 / c) * rieszEnergy 1 0 X μ + c⁻¹ * Sig0 η0 + KE * Q1 Λ η0) +
        32 * Kc ^ 2 * ω * Cm * (1 / (N : ℝ)) := by
      have hB' : IntegrableOn (fun l : ℝ => l ^ (-bexp 1 0) *
          (2 * (1 / (N : ℝ)) ^ 2 * ∑ i, 4 * Kc ^ 2 * mass 1 l (r i / 4) * (r i * ω))) (Ioi 0) :=
        hBi.congr_fun (fun l _ => by rw [hBform]) measurableSet_Ioi
      rw [integral_add (hEi0.const_mul 2) hB', integral_const_mul]
      have e : ∫ l in Ioi (0 : ℝ), l ^ (-bexp 1 0) *
          (2 * (1 / (N : ℝ)) ^ 2 * ∑ i, 4 * Kc ^ 2 * mass 1 l (r i / 4) * (r i * ω)) =
          ∫ l in Ioi (0 : ℝ), l ^ (-bexp 1 0) * ∑ i, (2 * (1 / (N : ℝ)) ^ 2 * (4 * Kc ^ 2 * (r i * ω))) *
            mass 1 l (η0 i) :=
        integral_congr_ae (Filter.Eventually.of_forall fun l => by simp only [hBform])
      rw [e]
      have := hBb.trans (le_of_eq hBsum)
      linarith [hEb0']
    obtain ⟨h1, h2, h3⟩ := lint_bound hfi h0 hint
    refine ⟨?_, h2, trivial⟩
    refine le_trans (le_of_eq ?_) h1
    refine setLIntegral_congr_fun measurableSet_Ioi fun l hl => ?_
    have hl' : (0 : ℝ) < l := hl
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hl'.le _)]
    congr 1
    unfold Ebar0 at *
    ring
  -- the field term
  have hFm : ∀ i, Measurable fun p : ℝ × Torus 1 => (fun l : ℝ => fieldF l X μ i) p.1 p.2 := fun i =>
    measurable_fieldF_uncurry X μ i
  have hTi : ∀ i, ∫⁻ l in Ioi (0 : ℝ), Tmaj 1 0 (r i) (η i) L (X i) (fun l => fieldF l X μ i) l ≤
      ENNReal.ofReal (L * (KT1 / N)) + ENNReal.ofReal (L * KT2 * N) *
        Yloc 1 0 (r i) (X i) (fun l => fieldF l X μ i) := fun i => by
    have h := hT hNpos (hr0 i) (hr8 i) (hηmem i).1.le (hηmem i).2 hL (hFm i) (hηpick i)
    simpa using h
  have hA5 : ∀ i : Fin N, 0 ≤ L * (KT1 / N) := fun i => by positivity
  have hY := sumY0_le 0 hN0 (r := r) hr0 hr8 hsep hΛ0 hμ hμ1 hKc0 (fun {l} hl σ _ a {r'} hr' hr2 => hKc hl σ a hr' hr2)
  have hF5 := piece_field (fun i l => Tmaj 1 0 (r i) (η i) L (X i) (fun l => fieldF l X μ i) l)
    (fun i => measurable_Tmaj 1 0 (r i) (η i) L (X i) (hFm i)) (2 / (N : ℝ)) (L * KT2 * N)
    (2 * ((2 / c) * rieszEnergy 1 0 X μ + c⁻¹ * Sig0 η0 + KE * Q1 Λ η0) + 32 * Kc ^ 2 * ω * Cm * (1 / (N : ℝ)))
    (fun _ => L * (KT1 / N)) (fun i => Yloc 1 0 (r i) (X i) (fun l => fieldF l X μ i))
    (by positivity) (by positivity) hA5 hTi (hY.trans hZ)
  -- the pointwise bound
  have hpt : ∀ l ∈ Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp 1 0)) *
      ENNReal.ofReal |offDiagPairing (commKernel (SliceAux.sgv l) v) X μ| ≤
      ENNReal.ofReal (l ^ (-bexp 1 0) * (CQ * L * Ebar0 X η μ Λ l)) +
      ENNReal.ofReal (l ^ (-bexp 1 0) * SBmaj Ksg L η l) +
      ∑ i, ENNReal.ofReal (2 / (N : ℝ)) * (ENNReal.ofReal (l ^ (-bexp 1 0)) *
        ENNReal.ofReal (Λ * L * muMaj 1 l (η i))) +
      ∑ i, ENNReal.ofReal (2 / (N : ℝ)) *
        Tmaj 1 0 (r i) (η i) L (X i) (fun l => fieldF l X μ i) l := by
    intro l hl
    have hl' : (0 : ℝ) < l := hl
    have h := hPP hN0 hl' hη hdisj hΛ0 hμ hμ1 hL hv
    have hsp := split_bound2 (ι := Fin N) (l ^ (-bexp 1 0)) (CQ * L * Ebar0 X η μ Λ l)
      (SBmaj Ksg L η l) (2 / (N : ℝ))
      (fun i => Λ * L * muMaj 1 l (η i)) (fun i => |fieldT l v X (chS 1 l (η i) (X i)) μ i|)
      (Real.rpow_nonneg hl'.le _) (by positivity)
      (fun i => mul_nonneg hΛL (muMaj_nonneg (d := 1) le_rfl hl' (hη i).1 (hη2 i).2)) (fun i => abs_nonneg _)
    refine le_trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal h)) (hsp.trans ?_)
    refine add_le_add le_rfl (Finset.sum_le_sum fun i _ => mul_le_mul' le_rfl ?_)
    exact T_pointwise (d := 1) le_rfl 0 (hr0 i) (hηmem i).1.le (hηmem i).2 (hη2 i).2 hL hv (X i)
      (fun l => measurable_fieldF l X μ i) hl'
  -- integrate
  have hnn5 : 0 ≤ (2 / (N : ℝ)) * ∑ _i : Fin N, L * (KT1 / N) :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => hA5 i)
  have hnn6 : 0 ≤ (2 / (N : ℝ)) * (L * KT2 * N) * (2 * ((2 / c) * rieszEnergy 1 0 X μ + c⁻¹ * Sig0 η0 +
      KE * Q1 Λ η0) + 32 * Kc ^ 2 * ω * Cm * (1 / (N : ℝ))) :=
    mul_nonneg (by positivity) hZnn
  have hnn4 : 0 ≤ (2 / (N : ℝ)) * ∑ i, Λ * L * (KM * η i) :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ =>
      mul_nonneg hΛL (mul_nonneg hKM0 (hη i).1.le))
  have hm12 : AEMeasurable (fun l : ℝ => ENNReal.ofReal (l ^ (-bexp 1 0) * (CQ * L * Ebar0 X η μ Λ l)) +
      ENNReal.ofReal (l ^ (-bexp 1 0) * SBmaj Ksg L η l)) (volume.restrict (Ioi (0 : ℝ))) := hm1.add hm2
  have hm124 : AEMeasurable (fun l : ℝ => ENNReal.ofReal (l ^ (-bexp 1 0) * (CQ * L * Ebar0 X η μ Λ l)) +
      ENNReal.ofReal (l ^ (-bexp 1 0) * SBmaj Ksg L η l) +
      ∑ i, ENNReal.ofReal (2 / (N : ℝ)) * (ENNReal.ofReal (l ^ (-bexp 1 0)) *
        ENNReal.ofReal (Λ * L * muMaj 1 l (η i)))) (volume.restrict (Ioi (0 : ℝ))) := hm12.add hm4
  have hE12 : 0 ≤ CQ * L * ((2 / c) * rieszEnergy 1 0 X μ + c⁻¹ * Sig0 η + KE * Q1 Λ η) +
      4 * L * Ksg * Cm * (1 / (N : ℝ)) := add_nonneg hB1 hB2
  have hsum_nn : 0 ≤ CQ * L * ((2 / c) * rieszEnergy 1 0 X μ + c⁻¹ * Sig0 η + KE * Q1 Λ η) +
      4 * L * Ksg * Cm * (1 / (N : ℝ)) + (2 / (N : ℝ)) * ∑ i, Λ * L * (KM * η i) := add_nonneg hE12 hnn4
  have hetot : ENNReal.ofReal (CQ * L * ((2 / c) * rieszEnergy 1 0 X μ + c⁻¹ * Sig0 η + KE * Q1 Λ η) +
      4 * L * Ksg * Cm * (1 / (N : ℝ)) + (2 / (N : ℝ)) * ∑ i, Λ * L * (KM * η i) +
      ((2 / (N : ℝ)) * ∑ _i : Fin N, L * (KT1 / N) +
      (2 / (N : ℝ)) * (L * KT2 * N) * (2 * ((2 / c) * rieszEnergy 1 0 X μ + c⁻¹ * Sig0 η0 +
        KE * Q1 Λ η0) + 32 * Kc ^ 2 * ω * Cm * (1 / (N : ℝ))))) =
      ENNReal.ofReal (CQ * L * ((2 / c) * rieszEnergy 1 0 X μ + c⁻¹ * Sig0 η + KE * Q1 Λ η)) +
        ENNReal.ofReal (4 * L * Ksg * Cm * (1 / (N : ℝ))) +
        ENNReal.ofReal ((2 / (N : ℝ)) * ∑ i, Λ * L * (KM * η i)) +
        (ENNReal.ofReal ((2 / (N : ℝ)) * ∑ _i : Fin N, L * (KT1 / N)) +
          ENNReal.ofReal ((2 / (N : ℝ)) * (L * KT2 * N) * (2 * ((2 / c) * rieszEnergy 1 0 X μ +
            c⁻¹ * Sig0 η0 + KE * Q1 Λ η0) + 32 * Kc ^ 2 * ω * Cm * (1 / (N : ℝ))))) := by
    rw [ENNReal.ofReal_add hsum_nn (add_nonneg hnn5 hnn6), ENNReal.ofReal_add hE12 hnn4,
      ENNReal.ofReal_add hB1 hB2, ENNReal.ofReal_add hnn5 hnn6]
  calc ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp 1 0)) *
        ENNReal.ofReal |offDiagPairing (commKernel (SliceAux.sgv l) v) X μ|
      ≤ ∫⁻ l in Ioi (0 : ℝ), (ENNReal.ofReal (l ^ (-bexp 1 0) * (CQ * L * Ebar0 X η μ Λ l)) +
      ENNReal.ofReal (l ^ (-bexp 1 0) * SBmaj Ksg L η l) +
      ∑ i, ENNReal.ofReal (2 / (N : ℝ)) * (ENNReal.ofReal (l ^ (-bexp 1 0)) *
        ENNReal.ofReal (Λ * L * muMaj 1 l (η i))) +
      ∑ i, ENNReal.ofReal (2 / (N : ℝ)) *
        Tmaj 1 0 (r i) (η i) L (X i) (fun l => fieldF l X μ i) l) :=
        setLIntegral_mono' measurableSet_Ioi hpt
    _ = (∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp 1 0) * (CQ * L * Ebar0 X η μ Λ l))) +
        (∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp 1 0) * SBmaj Ksg L η l)) +
        (∫⁻ l in Ioi (0 : ℝ), ∑ i, ENNReal.ofReal (2 / (N : ℝ)) * (ENNReal.ofReal (l ^ (-bexp 1 0)) *
          ENNReal.ofReal (Λ * L * muMaj 1 l (η i)))) +
        (∫⁻ l in Ioi (0 : ℝ), ∑ i, ENNReal.ofReal (2 / (N : ℝ)) *
          Tmaj 1 0 (r i) (η i) L (X i) (fun l => fieldF l X μ i) l) := by
        rw [lintegral_add_left' hm124, lintegral_add_left' hm12, lintegral_add_left' hm1]
    _ ≤ ENNReal.ofReal (CQ * L * ((2 / c) * rieszEnergy 1 0 X μ + c⁻¹ * Sig0 η + KE * Q1 Λ η)) +
        ENNReal.ofReal (4 * L * Ksg * Cm * (1 / (N : ℝ))) +
        ENNReal.ofReal ((2 / (N : ℝ)) * ∑ i, Λ * L * (KM * η i)) +
        (ENNReal.ofReal ((2 / (N : ℝ)) * ∑ _i : Fin N, L * (KT1 / N)) +
          ENNReal.ofReal ((2 / (N : ℝ)) * (L * KT2 * N) * (2 * ((2 / c) * rieszEnergy 1 0 X μ +
            c⁻¹ * Sig0 η0 + KE * Q1 Λ η0) + 32 * Kc ^ 2 * ω * Cm * (1 / (N : ℝ))))) :=
        add_le_add (add_le_add (add_le_add hf1 hf2) hf4) hF5
    _ = _ := hetot.symm

end HRS.Commutator.Stj
