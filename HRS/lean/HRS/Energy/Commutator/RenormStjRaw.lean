import HRS.Energy.Commutator.RenormStjMaster

/-!
# Route S, packet STJ: the integrated master inequality (`s > 0`)
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS.Commutator.Renorm

namespace HRS.Commutator.Stj

variable {d : ℕ}

/-- the radius-dependent shape of the integrated energy majorants -/
def Sig1 (d : ℕ) (s : ℝ) {N : ℕ} (Λ : ℝ) (η : Fin N → ℝ) : ℝ :=
  (1 / (N : ℝ)) ^ 2 * ∑ i, (η i ^ (-s) + 1) + (1 + Λ) * (1 / (N : ℝ)) * ∑ i, η i ^ ((d : ℝ) - s)

theorem Ebar_nonneg (hd : 1 ≤ d) {N : ℕ} (hN : N ≠ 0) {l : ℝ} (hl : 0 < l) {X : Config d N}
    {η : Fin N → ℝ} (hη : ∀ i, 0 < η i ∧ η i ≤ 1 / 8)
    (hdisj : ∀ i j, i ≠ j → η i + η j < KernelGrad.tdist (X i) (X j))
    {μ : Measure (Torus d)} [IsFiniteMeasure μ] {Λ : ℝ}
    (hμ : μ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d))) (hμ1 : μ Set.univ = 1) (hΛ0 : 0 ≤ Λ) :
    0 ≤ Ebar d X η μ Λ l := by
  have hη2 : ∀ i, 0 < η i ∧ η i < 1 / 2 := fun i => ⟨(hη i).1, by linarith [(hη i).2]⟩
  exact (energy_nonneg hd hN hl (sliceCharges_stj hd hl hη2 hdisj) ENNReal.ofReal_ne_top hμ hμ1).trans
    (energy_le_Ebar hd hN hl hη hdisj hΛ0 hμ hμ1)

theorem Ubar_nonneg {N : ℕ} {l : ℝ} (η : Fin N → ℝ) {Λ : ℝ} (hΛ0 : 0 ≤ Λ) : 0 ≤ Ubar d η Λ l := by
  unfold Ubar
  refine add_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ =>
    add_nonneg ENNReal.toReal_nonneg (Fint_nonneg d l (η i)))) (mul_nonneg (by positivity)
    (Finset.sum_nonneg fun i _ => Fint_nonneg d l (η i)))

theorem piece_scaled {e : ℝ} {g : ℝ → ℝ} (hg : IntegrableOn (fun l : ℝ => l ^ e * g l) (Ioi 0))
    (h0 : ∀ l ∈ Ioi (0 : ℝ), 0 ≤ g l) {B k : ℝ} (hk : 0 ≤ k)
    (hB : ∫ l in Ioi (0 : ℝ), l ^ e * g l ≤ B) :
    ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ e * (k * g l)) ≤ ENNReal.ofReal (k * B) ∧ 0 ≤ k * B ∧
      AEMeasurable (fun l : ℝ => ENNReal.ofReal (l ^ e * (k * g l))) (volume.restrict (Ioi (0 : ℝ))) := by
  have hf : IntegrableOn (fun l : ℝ => l ^ e * (k * g l)) (Ioi 0) := by
    exact IntegrableOn.congr_fun (hg.const_mul k) (fun l _ => by ring) measurableSet_Ioi
  refine lint_bound hf (fun l hl => mul_nonneg (Real.rpow_nonneg (le_of_lt hl) _) (mul_nonneg hk (h0 l hl))) ?_
  have : ∫ l in Ioi (0 : ℝ), l ^ e * (k * g l) = k * ∫ l in Ioi (0 : ℝ), l ^ e * g l := by
    rw [← integral_const_mul]; exact integral_congr_ae (Filter.Eventually.of_forall fun l => by ring)
  rw [this]
  exact mul_le_mul_of_nonneg_left hB hk

theorem piece_Jl (hd : 1 ≤ d) {s : ℝ} {KJ : ℝ} (hKJ : ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) *
      ENNReal.ofReal (Jl d l) ≤ ENNReal.ofReal KJ) {k : ℝ} (hk : 0 ≤ k) :
    ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (k * Jl d l) ≤
      ENNReal.ofReal (k * KJ) := by
  have e1 : ∀ l : ℝ, ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (k * Jl d l) =
      ENNReal.ofReal k * (ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (Jl d l)) := fun l => by
    rw [ENNReal.ofReal_mul hk]; ring
  simp_rw [e1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul hk]
  exact mul_le_mul' le_rfl hKJ

theorem piece_muMaj (hd : 1 ≤ d) {s : ℝ} {KM : ℝ} (hKM : ∀ η : ℝ, 0 < η → η ≤ 1 / 8 →
      ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (muMaj d l η) ≤
        ENNReal.ofReal (KM * η ^ ((d : ℝ) - s)))
    {N : ℕ} {η : Fin N → ℝ} (hη : ∀ i, 0 < η i ∧ η i ≤ 1 / 8) {c Λ L : ℝ} (hc : 0 ≤ c) (hΛL : 0 ≤ Λ * L)
    (hKM0 : 0 ≤ KM) :
    (∫⁻ l in Ioi (0 : ℝ), ∑ i, ENNReal.ofReal c * (ENNReal.ofReal (l ^ (-bexp d s)) *
        ENNReal.ofReal (Λ * L * muMaj d l (η i)))) ≤
      ENNReal.ofReal (c * ∑ i, Λ * L * (KM * η i ^ ((d : ℝ) - s))) := by
  have hi : ∀ i, ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal c * (ENNReal.ofReal (l ^ (-bexp d s)) *
      ENNReal.ofReal (Λ * L * muMaj d l (η i))) ≤ ENNReal.ofReal (c * (Λ * L * (KM * η i ^ ((d : ℝ) - s)))) := by
    intro i
    have e1 : ∀ l : ℝ, ENNReal.ofReal c * (ENNReal.ofReal (l ^ (-bexp d s)) *
        ENNReal.ofReal (Λ * L * muMaj d l (η i))) =
        ENNReal.ofReal (c * (Λ * L)) * (ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (muMaj d l (η i))) :=
      fun l => by
        rw [ENNReal.ofReal_mul hΛL, ENNReal.ofReal_mul hc]; ring
    simp_rw [e1]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (c * (Λ * L)) * ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) *
          ENNReal.ofReal (muMaj d l (η i))
        ≤ ENNReal.ofReal (c * (Λ * L)) * ENNReal.ofReal (KM * η i ^ ((d : ℝ) - s)) :=
          mul_le_mul' le_rfl (hKM (η i) (hη i).1 (hη i).2)
      _ = ENNReal.ofReal (c * (Λ * L) * (KM * η i ^ ((d : ℝ) - s))) := by
          rw [ENNReal.ofReal_mul (mul_nonneg hc hΛL)]
      _ = _ := by congr 1; ring
  have hnn : ∀ i, 0 ≤ c * (Λ * L * (KM * η i ^ ((d : ℝ) - s))) := fun i =>
    mul_nonneg hc (mul_nonneg hΛL (mul_nonneg hKM0 (Real.rpow_nonneg (hη i).1.le _)))
  rw [lintegral_finset_sum' _ (fun i _ => ?_)]
  · refine (Finset.sum_le_sum fun i _ => hi i).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hnn i), Finset.mul_sum]
  · have h1 : AEMeasurable (fun l : ℝ => muMaj d l (η i)) (volume.restrict (Ioi (0 : ℝ))) :=
      aemeasurable_muMaj hd (hη i).1
    exact ((ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).aemeasurable.mul
      (h1.const_mul (Λ * L)).ennreal_ofReal).const_mul _

theorem aemeas_muMaj_sum (hd : 1 ≤ d) {s : ℝ} {N : ℕ} {η : Fin N → ℝ} (hη : ∀ i, 0 < η i ∧ η i ≤ 1 / 8)
    (c Λ L : ℝ) :
    AEMeasurable (fun l : ℝ => ∑ i, ENNReal.ofReal c * (ENNReal.ofReal (l ^ (-bexp d s)) *
        ENNReal.ofReal (Λ * L * muMaj d l (η i)))) (volume.restrict (Ioi (0 : ℝ))) := by
  have h2 : AEMeasurable (fun l : ℝ => ENNReal.ofReal (l ^ (-bexp d s))) (volume.restrict (Ioi (0 : ℝ))) :=
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).aemeasurable
  have hi : ∀ i ∈ (Finset.univ : Finset (Fin N)), AEMeasurable (fun l : ℝ => ENNReal.ofReal c *
      (ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (Λ * L * muMaj d l (η i))))
      (volume.restrict (Ioi (0 : ℝ))) := by
    intro i _
    have h1 : AEMeasurable (fun l : ℝ => ENNReal.ofReal (Λ * L * muMaj d l (η i)))
        (volume.restrict (Ioi (0 : ℝ))) :=
      ((aemeasurable_muMaj hd (hη i).1).const_mul (Λ * L)).ennreal_ofReal
    exact (h2.mul h1).const_mul _
  exact Finset.aemeasurable_fun_sum _ hi

theorem piece_field {N : ℕ} (T : Fin N → ℝ → ℝ≥0∞) (hTm : ∀ i, Measurable (T i)) (c b Z : ℝ)
    (A : Fin N → ℝ) (Y : Fin N → ℝ≥0∞) (hc : 0 ≤ c) (hb : 0 ≤ b) (hA : ∀ i, 0 ≤ A i)
    (hT : ∀ i, ∫⁻ l in Ioi (0 : ℝ), T i l ≤ ENNReal.ofReal (A i) + ENNReal.ofReal b * Y i)
    (hY : ∑ i, Y i ≤ ENNReal.ofReal Z) :
    ∫⁻ l in Ioi (0 : ℝ), ∑ i, ENNReal.ofReal c * T i l ≤
      ENNReal.ofReal (c * ∑ i, A i) + ENNReal.ofReal (c * b * Z) := by
  rw [lintegral_finset_sum _ (fun i _ => (hTm i).const_mul _)]
  have h1 : ∀ i, ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal c * T i l ≤
      ENNReal.ofReal c * (ENNReal.ofReal (A i) + ENNReal.ofReal b * Y i) := fun i => by
    rw [lintegral_const_mul _ (hTm i)]
    exact mul_le_mul' le_rfl (hT i)
  calc ∑ i, ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal c * T i l
      ≤ ∑ i, ENNReal.ofReal c * (ENNReal.ofReal (A i) + ENNReal.ofReal b * Y i) :=
        Finset.sum_le_sum fun i _ => h1 i
    _ = ENNReal.ofReal c * ∑ i, ENNReal.ofReal (A i) + ENNReal.ofReal c * ENNReal.ofReal b * ∑ i, Y i := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]; ring
    _ ≤ ENNReal.ofReal c * ∑ i, ENNReal.ofReal (A i) + ENNReal.ofReal c * ENNReal.ofReal b * ENNReal.ofReal Z :=
        add_le_add le_rfl (mul_le_mul' le_rfl hY)
    _ = ENNReal.ofReal (c * ∑ i, A i) + ENNReal.ofReal (c * b * Z) := by
        rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_sum_of_nonneg (fun i _ => hA i),
          ENNReal.ofReal_mul (mul_nonneg hc hb), ENNReal.ofReal_mul hc]

set_option maxHeartbeats 4000000 in
theorem stj_raw (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hs : (d : ℝ) - 2 < s) (hsd : s < d) {c : ℝ} (hc : 0 < c)
    (hker : ∀ x : Torus d, x ≠ 0 →
      periodicRiesz d s x = c * ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * sliceG d l x) :
    ∃ CQ Cs KE KU KJ KM KT1 KT2 : ℝ, 0 ≤ CQ ∧ 0 ≤ Cs ∧ 0 ≤ KE ∧ 0 ≤ KU ∧ 0 ≤ KJ ∧ 0 ≤ KM ∧ 0 ≤ KT1 ∧
      0 ≤ KT2 ∧
    ∀ {N : ℕ}, 2 ≤ N → ∀ {Λ : ℝ}, 1 ≤ Λ → ∀ {ρ : Torus d → ℝ}, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ {X : Config d N}, X ∉ collisionSet d N → ∀ {L : ℝ}, 0 ≤ L → ∀ {v : Torus d → Euc d},
      IsLipschitzVF L v →
      ∃ η : Fin N → ℝ, (∀ i, smearRadius Λ X i / 2 < η i ∧ η i < smearRadius Λ X i) ∧
        ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) *
            ENNReal.ofReal |offDiagPairing (commKernel (SliceAux.sgv l) v) X (withDensityReal ρ)| ≤
          ENNReal.ofReal (
            CQ * L * ((2 / c) * rieszEnergy d s X (withDensityReal ρ) + KE * Sig1 d s Λ η) +
            Cs * L * (KU * Sig1 d s Λ η) + 2 * L * (1 / (N : ℝ)) * KJ +
            (2 / (N : ℝ)) * ∑ i, Λ * L * (KM * η i ^ ((d : ℝ) - s)) +
            ((2 / (N : ℝ)) * ∑ i, L * (KT1 * smearRadius Λ X i ^ (-s) / N) +
            (2 / (N : ℝ)) * (L * KT2 * N) * (2 * ((2 / c) * rieszEnergy d s X (withDensityReal ρ) +
              KE * Sig1 d s Λ (fun i => smearRadius Λ X i / 4)) +
              2 * (KU * Sig1 d s Λ (fun i => smearRadius Λ X i / 4))))) := by
  obtain ⟨CQ, Cs, hCQ, hCs, hPP⟩ := P_pointwise hd
  obtain ⟨KE, hKE0, hEint⟩ := Ebar_integral hd hs0 hs hsd hc hker
  obtain ⟨KU, hKU0, hUint⟩ := Ubar_integral hd hs0 hs hsd hc hker
  obtain ⟨KJ, hKJ0, hKJ⟩ := Jl_lintegral hd hs0.le hs hsd
  obtain ⟨KM, hKM0, hKM⟩ := muMaj_lintegral hd hs0.le hs hsd
  obtain ⟨KT1, KT2, hKT10, hKT20, hT⟩ := T_i_total hd hs0.le hs hsd
  refine ⟨CQ, Cs, KE, KU, KJ, KM, KT1, KT2, hCQ, hCs, hKE0, hKU0, hKJ0, hKM0, hKT10, hKT20, ?_⟩
  intro N hN Λ hΛ ρ hρ hρΛ X hX L hL v hv
  have hN0 : N ≠ 0 := by omega
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  set μ := withDensityReal ρ with hμdef
  haveI : IsProbabilityMeasure μ := isProb_withDensityReal hρ
  have hΛ0 : 0 ≤ Λ := by linarith
  have hμ : μ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d)) := withDensityReal_le_smul' hρΛ
  have hμ1 : μ Set.univ = 1 := measure_univ
  have hX' : ∀ i j, i ≠ j → X i ≠ X j := fun i j hij h => hX ⟨i, j, hij, h⟩
  obtain ⟨hr0, hrl, hr8, hsep⟩ := radii_facts hd hN hΛ X hX'
  set r : Fin N → ℝ := fun i => smearRadius Λ X i with hr
  have hpick : ∀ i, ∃ t ∈ Ioo (r i / 2) (r i),
      (∫⁻ x, Phi d s (r i) (fun l => fieldF l X μ i) x ∂(chC d t (X i))) *
        ((volume : Measure (Euc d)).toSphere univ * ENNReal.ofReal ((r i / 2) ^ d)) ≤
      ∫⁻ x : Torus d, (if r i / 2 < KernelGrad.tdist x (X i) ∧ KernelGrad.tdist x (X i) < r i then
        Phi d s (r i) (fun l => fieldF l X μ i) x else 0) := fun i =>
    sphere_pick hd (hr0 i) (by linarith [hr8 i]) (X i) _
      (measurable_Phi d s (r i) (measurable_fieldF_uncurry X μ i))
  choose η hηmem hηpick using hpick
  refine ⟨η, fun i => ⟨(hηmem i).1, (hηmem i).2⟩, ?_⟩
  have hη : ∀ i, 0 < η i ∧ η i ≤ 1 / 8 := fun i =>
    ⟨by linarith [(hηmem i).1, hr0 i], by linarith [(hηmem i).2, hr8 i]⟩
  have hdisj : ∀ i j, i ≠ j → η i + η j < KernelGrad.tdist (X i) (X j) := fun i j hij => by
    have := hsep i j hij; have := (hηmem i).2; have := (hηmem j).2; linarith
  set η0 : Fin N → ℝ := fun i => r i / 4 with hη0def
  have hη0 : ∀ i, 0 < η0 i ∧ η0 i ≤ 1 / 8 := fun i => ⟨by have := hr0 i; simp only [hη0def]; positivity,
    by have := hr8 i; simp only [hη0def]; linarith⟩
  have hdisj0 : ∀ i j, i ≠ j → η0 i + η0 j < KernelGrad.tdist (X i) (X j) := fun i j hij => by
    have := hsep i j hij; have := hr0 i; have := hr0 j; simp only [hη0def]; linarith
  -- the integrals of the real majorants
  have hE : ∀ η : Fin N → ℝ, (∀ i, 0 < η i ∧ η i ≤ 1 / 8) →
      IntegrableOn (fun l : ℝ => l ^ (-bexp d s) * Ebar d X η μ Λ l) (Ioi 0) ∧
      ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * Ebar d X η μ Λ l ≤
        (2 / c) * rieszEnergy d s X μ + KE * Sig1 d s Λ η := fun η hη => hEint hN0 X hX' η hη hΛ0 hρΛ
  have hU : ∀ η : Fin N → ℝ, (∀ i, 0 < η i ∧ η i ≤ 1 / 8) →
      IntegrableOn (fun l : ℝ => l ^ (-bexp d s) * Ubar d η Λ l) (Ioi 0) ∧
      ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * Ubar d η Λ l ≤ KU * Sig1 d s Λ η :=
    fun η hη => hUint hN0 η hη hΛ0
  obtain ⟨hEi, hEb'⟩ := hE η hη
  obtain ⟨hEi0, hEb0'⟩ := hE η0 hη0
  obtain ⟨hUi, hUb'⟩ := hU η hη
  obtain ⟨hUi0, hUb0'⟩ := hU η0 hη0
  have hCQL : 0 ≤ CQ * L := mul_nonneg hCQ hL
  have hCsL : 0 ≤ Cs * L := mul_nonneg hCs hL
  have hΛL : 0 ≤ Λ * L := mul_nonneg hΛ0 hL
  obtain ⟨hf1, hB1, hm1⟩ := piece_scaled hEi
    (fun l hl => Ebar_nonneg hd hN0 hl hη hdisj hμ hμ1 hΛ0) hCQL hEb'
  obtain ⟨hf2, hB2, hm2⟩ := piece_scaled hUi (fun l hl => Ubar_nonneg η hΛ0) hCsL hUb'
  have hk3 : 0 ≤ 2 * L * (1 / (N : ℝ)) := by positivity
  have hf3 := piece_Jl hd hKJ hk3
  have hm3 : AEMeasurable (fun l : ℝ => ENNReal.ofReal (l ^ (-bexp d s)) *
      ENNReal.ofReal (2 * L * (1 / (N : ℝ)) * Jl d l)) (volume.restrict (Ioi (0 : ℝ))) :=
    ((ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).mul
      (ENNReal.measurable_ofReal.comp ((measurable_Jl_l d).const_mul _))).aemeasurable
  have hKM' : ∀ η : ℝ, 0 < η → η ≤ 1 / 8 → ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) *
      ENNReal.ofReal (muMaj d l η) ≤ ENNReal.ofReal (KM * η ^ ((d : ℝ) - s)) := hKM
  have hf4 := piece_muMaj hd hKM' hη (c := 2 / (N : ℝ)) (Λ := Λ) (L := L) (by positivity) hΛL hKM0
  have hm4 := aemeas_muMaj_sum (s := s) hd hη (2 / (N : ℝ)) Λ L
  -- the auxiliary energy
  have hY := sumY_le hd s hN0 hr0 hr8 hsep hΛ0 hμ hμ1
  obtain ⟨hZ, hZnn, -⟩ : (∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) *
        ENNReal.ofReal (2 * Ebar d X η0 μ Λ l + 2 * Ubar d η0 Λ l)) ≤
      ENNReal.ofReal (2 * ((2 / c) * rieszEnergy d s X μ + KE * Sig1 d s Λ η0) + 2 * (KU * Sig1 d s Λ η0)) ∧
      0 ≤ 2 * ((2 / c) * rieszEnergy d s X μ + KE * Sig1 d s Λ η0) + 2 * (KU * Sig1 d s Λ η0) ∧ True := by
    have hfi : IntegrableOn (fun l : ℝ => 2 * (l ^ (-bexp d s) * Ebar d X η0 μ Λ l) +
        2 * (l ^ (-bexp d s) * Ubar d η0 Λ l)) (Ioi 0) := (hEi0.const_mul 2).add (hUi0.const_mul 2)
    have h0 : ∀ l ∈ Ioi (0 : ℝ), 0 ≤ 2 * (l ^ (-bexp d s) * Ebar d X η0 μ Λ l) +
        2 * (l ^ (-bexp d s) * Ubar d η0 Λ l) := fun l hl => by
      have h1 := Ebar_nonneg hd hN0 hl hη0 hdisj0 hμ hμ1 hΛ0
      have h2 := Ubar_nonneg (d := d) (l := l) η0 hΛ0
      have h3 : 0 ≤ l ^ (-bexp d s) := Real.rpow_nonneg (le_of_lt hl) _
      positivity
    have hint : ∫ l in Ioi (0 : ℝ), (2 * (l ^ (-bexp d s) * Ebar d X η0 μ Λ l) +
        2 * (l ^ (-bexp d s) * Ubar d η0 Λ l)) =
        2 * (∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * Ebar d X η0 μ Λ l) +
          2 * (∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * Ubar d η0 Λ l) := by
      rw [integral_add (hEi0.const_mul 2) (hUi0.const_mul 2), integral_const_mul, integral_const_mul]
    obtain ⟨h1, h2, h3⟩ := lint_bound hfi h0 (B := 2 * ((2 / c) * rieszEnergy d s X μ + KE * Sig1 d s Λ η0) +
      2 * (KU * Sig1 d s Λ η0)) (by rw [hint]; linarith [hEb0', hUb0'])
    refine ⟨?_, h2, trivial⟩
    refine le_trans (le_of_eq ?_) h1
    refine setLIntegral_congr_fun measurableSet_Ioi fun l hl => ?_
    have hl' : (0 : ℝ) < l := hl
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hl'.le _)]
    congr 1; ring
  -- the field term
  have hFm : ∀ i, Measurable fun p : ℝ × Torus d => (fun l : ℝ => fieldF l X μ i) p.1 p.2 := fun i =>
    measurable_fieldF_uncurry X μ i
  have hTi : ∀ i, ∫⁻ l in Ioi (0 : ℝ), Tmaj d s (r i) (η i) L (X i) (fun l => fieldF l X μ i) l ≤
      ENNReal.ofReal (L * (KT1 * r i ^ (-s) / N)) + ENNReal.ofReal (L * KT2 * N) *
        Yloc d s (r i) (X i) (fun l => fieldF l X μ i) := fun i =>
    hT hNpos (hr0 i) (hr8 i) (hηmem i).1.le (hηmem i).2 hL (hFm i) (hηpick i)
  have hA5 : ∀ i, 0 ≤ L * (KT1 * r i ^ (-s) / N) := fun i =>
    mul_nonneg hL (div_nonneg (mul_nonneg hKT10 (Real.rpow_nonneg (hr0 i).le _)) hNr.le)
  have hF5 := piece_field (fun i l => Tmaj d s (r i) (η i) L (X i) (fun l => fieldF l X μ i) l)
    (fun i => measurable_Tmaj d s (r i) (η i) L (X i) (hFm i)) (2 / (N : ℝ)) (L * KT2 * N)
    (2 * ((2 / c) * rieszEnergy d s X μ + KE * Sig1 d s Λ η0) + 2 * (KU * Sig1 d s Λ η0))
    (fun i => L * (KT1 * r i ^ (-s) / N)) (fun i => Yloc d s (r i) (X i) (fun l => fieldF l X μ i))
    (by positivity) (by positivity) hA5 hTi (hY.trans hZ)
  -- the pointwise bound
  have hpt : ∀ l ∈ Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) *
      ENNReal.ofReal |offDiagPairing (commKernel (SliceAux.sgv l) v) X μ| ≤
      ENNReal.ofReal (l ^ (-bexp d s) * (CQ * L * Ebar d X η μ Λ l)) +
      ENNReal.ofReal (l ^ (-bexp d s) * (Cs * L * Ubar d η Λ l)) +
      ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (2 * L * (1 / (N : ℝ)) * Jl d l) +
      ∑ i, ENNReal.ofReal (2 / (N : ℝ)) * (ENNReal.ofReal (l ^ (-bexp d s)) *
        ENNReal.ofReal (Λ * L * muMaj d l (η i))) +
      ∑ i, ENNReal.ofReal (2 / (N : ℝ)) *
        Tmaj d s (r i) (η i) L (X i) (fun l => fieldF l X μ i) l := by
    intro l hl
    have hl' : (0 : ℝ) < l := hl
    have h := hPP hN0 hl' hη hdisj hΛ0 hμ hμ1 hL hv
    have hη2 : ∀ i, η i < 1 / 2 := fun i => by linarith [(hη i).2]
    have hsp := split_bound (ι := Fin N) (l ^ (-bexp d s)) (CQ * L * Ebar d X η μ Λ l)
      (Cs * L * Ubar d η Λ l) (2 * L * (1 / (N : ℝ)) * Jl d l) (2 / (N : ℝ))
      (fun i => Λ * L * muMaj d l (η i)) (fun i => |fieldT l v X (chS d l (η i) (X i)) μ i|)
      (Real.rpow_nonneg hl'.le _) (by positivity)
      (fun i => mul_nonneg hΛL (muMaj_nonneg hd hl' (hη i).1 (by linarith [(hη i).2]))) (fun i => abs_nonneg _)
    refine le_trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal h)) (hsp.trans ?_)
    refine add_le_add le_rfl (Finset.sum_le_sum fun i _ => mul_le_mul' le_rfl ?_)
    exact T_pointwise hd s (hr0 i) (hηmem i).1.le (hηmem i).2 (by linarith [(hη i).2]) hL hv (X i)
      (fun l => measurable_fieldF l X μ i) hl'
  -- integrate
  have hnn5 : 0 ≤ (2 / (N : ℝ)) * ∑ i, L * (KT1 * r i ^ (-s) / N) :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => hA5 i)
  have hnn6 : 0 ≤ (2 / (N : ℝ)) * (L * KT2 * N) * (2 * ((2 / c) * rieszEnergy d s X μ +
      KE * Sig1 d s Λ η0) + 2 * (KU * Sig1 d s Λ η0)) :=
    mul_nonneg (by positivity) hZnn
  have hnn3 : 0 ≤ 2 * L * (1 / (N : ℝ)) * KJ := by positivity
  have hnn4 : 0 ≤ (2 / (N : ℝ)) * ∑ i, Λ * L * (KM * η i ^ ((d : ℝ) - s)) :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ =>
      mul_nonneg hΛL (mul_nonneg hKM0 (Real.rpow_nonneg (hη i).1.le _)))
  have hsum_nn : 0 ≤ CQ * L * ((2 / c) * rieszEnergy d s X μ + KE * Sig1 d s Λ η) +
      Cs * L * (KU * Sig1 d s Λ η) + 2 * L * (1 / (N : ℝ)) * KJ +
      (2 / (N : ℝ)) * ∑ i, Λ * L * (KM * η i ^ ((d : ℝ) - s)) := by
    have := hB1; have := hB2; positivity
  have hm12 : AEMeasurable (fun l : ℝ => ENNReal.ofReal (l ^ (-bexp d s) * (CQ * L * Ebar d X η μ Λ l)) +
      ENNReal.ofReal (l ^ (-bexp d s) * (Cs * L * Ubar d η Λ l))) (volume.restrict (Ioi (0 : ℝ))) := hm1.add hm2
  have hm123 : AEMeasurable (fun l : ℝ => ENNReal.ofReal (l ^ (-bexp d s) * (CQ * L * Ebar d X η μ Λ l)) +
      ENNReal.ofReal (l ^ (-bexp d s) * (Cs * L * Ubar d η Λ l)) +
      ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (2 * L * (1 / (N : ℝ)) * Jl d l))
      (volume.restrict (Ioi (0 : ℝ))) := hm12.add hm3
  have hm1234 : AEMeasurable (fun l : ℝ => ENNReal.ofReal (l ^ (-bexp d s) * (CQ * L * Ebar d X η μ Λ l)) +
      ENNReal.ofReal (l ^ (-bexp d s) * (Cs * L * Ubar d η Λ l)) +
      ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (2 * L * (1 / (N : ℝ)) * Jl d l) +
      ∑ i, ENNReal.ofReal (2 / (N : ℝ)) * (ENNReal.ofReal (l ^ (-bexp d s)) *
        ENNReal.ofReal (Λ * L * muMaj d l (η i)))) (volume.restrict (Ioi (0 : ℝ))) := hm123.add hm4
  have hE12 : 0 ≤ CQ * L * ((2 / c) * rieszEnergy d s X μ + KE * Sig1 d s Λ η) +
      Cs * L * (KU * Sig1 d s Λ η) := add_nonneg hB1 hB2
  have hE123 : 0 ≤ CQ * L * ((2 / c) * rieszEnergy d s X μ + KE * Sig1 d s Λ η) +
      Cs * L * (KU * Sig1 d s Λ η) + 2 * L * (1 / (N : ℝ)) * KJ := add_nonneg hE12 hnn3
  have hetot : ENNReal.ofReal (CQ * L * ((2 / c) * rieszEnergy d s X μ + KE * Sig1 d s Λ η) +
      Cs * L * (KU * Sig1 d s Λ η) + 2 * L * (1 / (N : ℝ)) * KJ +
      (2 / (N : ℝ)) * ∑ i, Λ * L * (KM * η i ^ ((d : ℝ) - s)) +
      ((2 / (N : ℝ)) * ∑ i, L * (KT1 * r i ^ (-s) / N) +
      (2 / (N : ℝ)) * (L * KT2 * N) * (2 * ((2 / c) * rieszEnergy d s X μ +
        KE * Sig1 d s Λ η0) + 2 * (KU * Sig1 d s Λ η0)))) =
      ENNReal.ofReal (CQ * L * ((2 / c) * rieszEnergy d s X μ + KE * Sig1 d s Λ η)) +
        ENNReal.ofReal (Cs * L * (KU * Sig1 d s Λ η)) + ENNReal.ofReal (2 * L * (1 / (N : ℝ)) * KJ) +
        ENNReal.ofReal ((2 / (N : ℝ)) * ∑ i, Λ * L * (KM * η i ^ ((d : ℝ) - s))) +
        (ENNReal.ofReal ((2 / (N : ℝ)) * ∑ i, L * (KT1 * r i ^ (-s) / N)) +
          ENNReal.ofReal ((2 / (N : ℝ)) * (L * KT2 * N) * (2 * ((2 / c) * rieszEnergy d s X μ +
            KE * Sig1 d s Λ η0) + 2 * (KU * Sig1 d s Λ η0)))) := by
    rw [ENNReal.ofReal_add hsum_nn (add_nonneg hnn5 hnn6), ENNReal.ofReal_add hE123 hnn4,
      ENNReal.ofReal_add hE12 hnn3, ENNReal.ofReal_add hB1 hB2, ENNReal.ofReal_add hnn5 hnn6]
  calc ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) *
        ENNReal.ofReal |offDiagPairing (commKernel (SliceAux.sgv l) v) X μ|
      ≤ ∫⁻ l in Ioi (0 : ℝ), (ENNReal.ofReal (l ^ (-bexp d s) * (CQ * L * Ebar d X η μ Λ l)) +
      ENNReal.ofReal (l ^ (-bexp d s) * (Cs * L * Ubar d η Λ l)) +
      ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (2 * L * (1 / (N : ℝ)) * Jl d l) +
      ∑ i, ENNReal.ofReal (2 / (N : ℝ)) * (ENNReal.ofReal (l ^ (-bexp d s)) *
        ENNReal.ofReal (Λ * L * muMaj d l (η i))) +
      ∑ i, ENNReal.ofReal (2 / (N : ℝ)) *
        Tmaj d s (r i) (η i) L (X i) (fun l => fieldF l X μ i) l) :=
        setLIntegral_mono' measurableSet_Ioi hpt
    _ = (∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s) * (CQ * L * Ebar d X η μ Λ l))) +
        (∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s) * (Cs * L * Ubar d η Λ l))) +
        (∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (2 * L * (1 / (N : ℝ)) * Jl d l)) +
        (∫⁻ l in Ioi (0 : ℝ), ∑ i, ENNReal.ofReal (2 / (N : ℝ)) * (ENNReal.ofReal (l ^ (-bexp d s)) *
          ENNReal.ofReal (Λ * L * muMaj d l (η i)))) +
        (∫⁻ l in Ioi (0 : ℝ), ∑ i, ENNReal.ofReal (2 / (N : ℝ)) *
          Tmaj d s (r i) (η i) L (X i) (fun l => fieldF l X μ i) l) := by
        rw [lintegral_add_left' hm1234, lintegral_add_left' hm123, lintegral_add_left' hm12,
          lintegral_add_left' hm1]
    _ ≤ ENNReal.ofReal (CQ * L * ((2 / c) * rieszEnergy d s X μ + KE * Sig1 d s Λ η)) +
        ENNReal.ofReal (Cs * L * (KU * Sig1 d s Λ η)) + ENNReal.ofReal (2 * L * (1 / (N : ℝ)) * KJ) +
        ENNReal.ofReal ((2 / (N : ℝ)) * ∑ i, Λ * L * (KM * η i ^ ((d : ℝ) - s))) +
        (ENNReal.ofReal ((2 / (N : ℝ)) * ∑ i, L * (KT1 * r i ^ (-s) / N)) +
          ENNReal.ofReal ((2 / (N : ℝ)) * (L * KT2 * N) * (2 * ((2 / c) * rieszEnergy d s X μ +
            KE * Sig1 d s Λ η0) + 2 * (KU * Sig1 d s Λ η0)))) :=
        add_le_add (add_le_add (add_le_add (add_le_add hf1 hf2) hf3) hf4) hF5
    _ = _ := hetot.symm

end HRS.Commutator.Stj
