/-
# HRS.Equilibrium.PairMomentsTT -- the triple-sum variance under the reference (EQ-01b)
-/
import HRS.Equilibrium.PairMomentsCrude

open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.PairMom

open HRS HRS.External HRS.Quad HRS.External.PoleVar

variable {d : ℕ} {s : ℝ}

section Level1Gen

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ]

/-- Reduction of the first level to the second: the `i`-th triple row under the reference is the
pair sum under the one-pin ensemble. -/
theorem level1_of_level2 (V : WeakPotential μ) {lam : ℝ} (hlam0 : 0 ≤ lam) {m : ℕ}
    {g3 : Torus d → Torus d → Torus d → ℝ}
    (hgm : Measurable (fun p : Torus d × Torus d × Torus d => g3 p.1 p.2.1 p.2.2)) {𝒳 : ℝ≥0∞}
    (h2 : ∀ x : Torus d, ∫⁻ Y, ‖pairSumOrdered (g3 x) Y‖ₑ ^ 2
      ∂(pinnedLaw V lam (m + 1) (pinsWith (fun e : Empty => e.elim) x)) ≤ 𝒳) (i : Fin (m + 2)) :
    ∫⁻ Y, ‖tripleB g3 i (Y i) Y‖ₑ ^ 2 ∂(pinnedLaw V lam (m + 2) (fun e : Empty => e.elim)) ≤ 𝒳 := by
  by_cases htop : 𝒳 = ⊤
  · rw [htop]; exact le_top
  have hΦ : Measurable fun Y : Fin (m + 1 + 1) → Torus d => ‖tripleB g3 i (Y i) Y‖ₑ ^ 2 :=
    (measurable_tripleB hgm i).enorm.pow_const 2
  rw [lintegral_pinned_succ V hlam0 (fun e : Empty => e.elim) i hΦ]
  calc _ ≤ ∫⁻ x, pinWeight V lam (fun e : Empty => e.elim) (m + 1) x * 𝒳 ∂μ := by
        refine lintegral_mono fun x => mul_le_mul' le_rfl ?_
        simp only [insertAt_same, tripleB_insertAt]
        exact h2 x
    _ = _ := by
        rw [lintegral_mul_const' _ _ htop,
          lintegral_pinWeight V hlam0 (fun e : Empty => e.elim) i (0 : Fin (m + 1)), one_mul]

end Level1Gen

section TripleRef

theorem partt_ref_large (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)
    (Mmax M'max γmax Cq : ℝ) (hCq : 0 ≤ Cq) (Cu : ℝ) (hCu : 0 ≤ Cu) (δC : ℝ) (hδC : 0 ≤ δC)
    (C2 : ℝ) (hC2 : 0 ≤ C2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : WeakPotential (withDensityReal ρ)),
      PotBound (d := d) s c Mmax M'max γmax Cq V →
      (∀ x y : Torus d, x ≠ y → V.q x y ≤ Cu * wEnv s x y) → ∀ m : ℕ, 1 ≤ m → weakKappa V β ≤ 1 / 2 →
      ∀ C1 : ℝ, RefDens V β (m + 1) (δC * deltaN d s (m + 2)) C1 → RefDens2 V β m C2 →
      ∀ (K : ℝ) (g3 : Torus d → Torus d → Torus d → ℝ),
      Measurable (fun p : Torus d × Torus d × Torus d => g3 p.1 p.2.1 p.2.2) →
      IsSymmTriple g3 → IsCanonicalTriple (withDensityReal ρ) g3 →
      (∀ x y z, x ≠ y → x ≠ z → y ≠ z → |g3 x y z| ≤ K * tEnv s x y z) →
        evariance (fun X : Config d (m + 2) => ((m + 2 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) * tripleSum g3 X)
          (pinnedLaw V (β / ((m + 2 : ℕ) : ℝ)) (m + 2) (fun e : Empty => e.elim)) ≤
        ENNReal.ofReal (C * K ^ 2 * logEN (m + 2) ^ 2 / ((m + 2 : ℕ) : ℝ) ^ 2) := by
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  obtain ⟨Cμ, hCμ0, hCμ⟩ := mean2_large hd hcrit β hβ ρ hρ c hc Mmax M'max γmax Cq hCq Cu hCu δC hδC C2 hC2
  obtain ⟨Cl, hCl0, hCl⟩ := level1_bound hd hcrit β hβ ρ hρ c hc Mmax M'max γmax Cq hCq
  refine ⟨18 * Cl * (1 + Cμ ^ 2), by positivity, fun V hV hVu m hm1 hκ C1 RD1 RD2 K g3 hgm hsym hcan hg3 => ?_⟩
  have hMean := hCμ V hV hVu m hm1 C1 RD1 RD2 K g3 hgm hcan hg3
  have hl1 := fun i : Fin (m + 2) =>
    hCl V hV m hm1 hκ K (|K| * Cμ) (by positivity) g3 hgm hsym hg3 hMean i
  have hNp : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
  have hvar := evariance_tripleSum_le V hβ.le (N := m + 2) (by omega) hκ hgm hsym
    (((m + 2 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)))
  refine hvar.trans ?_
  have hsum : ∑ i : Fin (m + 2), ∫⁻ Y, ‖tripleB g3 i (Y i) Y‖ₑ ^ 2
      ∂(pinnedLaw V (β / ((m + 2 : ℕ) : ℝ)) (m + 2) (fun e : Empty => e.elim)) ≤
      ENNReal.ofReal ((m + 2 : ℕ) : ℝ) * ENNReal.ofReal (Cl * (K ^ 2 + (|K| * Cμ) ^ 2) *
        ((m + 2 : ℕ) : ℝ) ^ 2 * logEN (m + 2) ^ 2) := by
    calc _ ≤ ∑ _i : Fin (m + 2), ENNReal.ofReal (Cl * (K ^ 2 + (|K| * Cμ) ^ 2) *
          ((m + 2 : ℕ) : ℝ) ^ 2 * logEN (m + 2) ^ 2) := Finset.sum_le_sum fun i _ => hl1 i
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ENNReal.ofReal_natCast]
  refine (mul_le_mul' le_rfl hsum).trans ?_
  have hc2 : (((m + 2 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ))) ^ 2 = 1 / ((m + 2 : ℕ) : ℝ) ^ 5 := by
    rw [rpow_sq_neg (m + 2) (by omega)]
    have : (2 * (5 / 2 : ℝ)) = ((5 : ℕ) : ℝ) := by norm_num
    rw [this, Real.rpow_natCast]
  have hL1 := logEN_pos' (N := m + 2) (by omega)
  rw [hc2, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [mul_pow, sq_abs]
  field_simp

end TripleRef

section TripleCrude

theorem enorm_sq_sum_le {ι : Type*} (t : Finset ι) (b : ι → ℝ) :
    ‖∑ i ∈ t, b i‖ₑ ^ 2 ≤ ENNReal.ofReal (t.card : ℝ) * ∑ i ∈ t, ‖b i‖ₑ ^ 2 := by
  have e1 : ‖∑ i ∈ t, b i‖ₑ ^ 2 = ENNReal.ofReal ((∑ i ∈ t, b i) ^ 2) := by
    rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
  have e2 : ∀ i, ‖b i‖ₑ ^ 2 = ENNReal.ofReal (b i ^ 2) := fun i => by
    rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
  simp_rw [e1, e2]
  have h1 := sq_sum_le_card_mul_sum_sq (s := t) (f := b)
  refine (ENNReal.ofReal_le_ofReal h1).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ]

/-- Crude variance bound for the scaled ordered triple sum under a measure dominated by the reference. -/
theorem crude_tripleSum (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {m : ℕ}
    {g3 : Torus d → Torus d → Torus d → ℝ}
    (hgm : Measurable (fun p : Torus d × Torus d × Torus d => g3 p.1 p.2.1 p.2.2)) (c : ℝ) {𝒳 : ℝ≥0∞}
    (h2 : ∀ x : Torus d, ∫⁻ Y, ‖pairSumOrdered (g3 x) Y‖ₑ ^ 2
      ∂(pinnedLaw V (β / ((m + 2 : ℕ) : ℝ)) (m + 1) (pinsWith (fun e : Empty => e.elim) x)) ≤ 𝒳)
    {Q : Measure (Config d (m + 2))} [IsProbabilityMeasure Q] {K' : ℝ}
    (hle : Q ≤ ENNReal.ofReal K' • pinnedLaw V (β / ((m + 2 : ℕ) : ℝ)) (m + 2) (fun e : Empty => e.elim)) :
    evariance (fun X : Config d (m + 2) => c * tripleSum g3 X) Q ≤
      ENNReal.ofReal K' * (ENNReal.ofReal (c ^ 2) * (ENNReal.ofReal (((m + 2 : ℕ) : ℝ) ^ 2) * 𝒳)) := by
  have hlam0 : 0 ≤ β / ((m + 2 : ℕ) : ℝ) := by positivity
  have hF : Measurable (fun X : Config d (m + 2) => c * tripleSum g3 X) :=
    measurable_const.mul (measurable_tripleSum hgm)
  refine (evar_transfer_crude hle hF).trans (mul_le_mul' le_rfl ?_)
  have hB : ∀ i : Fin (m + 2), Measurable fun Y : Config d (m + 2) => ‖tripleB g3 i (Y i) Y‖ₑ ^ 2 :=
    fun i => (measurable_tripleB hgm i).enorm.pow_const 2
  have hS : Measurable fun X : Config d (m + 2) => ‖tripleSum g3 X‖ₑ ^ 2 :=
    (measurable_tripleSum hgm).enorm.pow_const 2
  calc ∫⁻ X, ‖c * tripleSum g3 X‖ₑ ^ 2
        ∂(pinnedLaw V (β / ((m + 2 : ℕ) : ℝ)) (m + 2) (fun e : Empty => e.elim))
      = ENNReal.ofReal (c ^ 2) * ∫⁻ X, ‖tripleSum g3 X‖ₑ ^ 2
        ∂(pinnedLaw V (β / ((m + 2 : ℕ) : ℝ)) (m + 2) (fun e : Empty => e.elim)) := by
        simp_rw [enorm_sq_mul_real]
        exact lintegral_const_mul _ hS
    _ ≤ _ := by
        refine mul_le_mul' le_rfl ?_
        have hts : ∀ X : Config d (m + 2), tripleSum g3 X = ∑ i : Fin (m + 2), tripleB g3 i (X i) X :=
          fun X => rfl
        calc ∫⁻ X, ‖tripleSum g3 X‖ₑ ^ 2
              ∂(pinnedLaw V (β / ((m + 2 : ℕ) : ℝ)) (m + 2) (fun e : Empty => e.elim))
            ≤ ∫⁻ X, ENNReal.ofReal ((Finset.univ : Finset (Fin (m + 2))).card : ℝ) *
                ∑ i : Fin (m + 2), ‖tripleB g3 i (X i) X‖ₑ ^ 2
                ∂(pinnedLaw V (β / ((m + 2 : ℕ) : ℝ)) (m + 2) (fun e : Empty => e.elim)) := by
              refine lintegral_mono fun X => ?_
              rw [hts X]
              exact enorm_sq_sum_le _ _
          _ = ENNReal.ofReal ((Finset.univ : Finset (Fin (m + 2))).card : ℝ) *
                ∑ i : Fin (m + 2), ∫⁻ X, ‖tripleB g3 i (X i) X‖ₑ ^ 2
                ∂(pinnedLaw V (β / ((m + 2 : ℕ) : ℝ)) (m + 2) (fun e : Empty => e.elim)) := by
              rw [lintegral_const_mul _ (Finset.measurable_sum _ fun i _ => hB i),
                lintegral_finsetSum _ (fun i _ => hB i)]
          _ ≤ ENNReal.ofReal ((Finset.univ : Finset (Fin (m + 2))).card : ℝ) *
                ∑ _i : Fin (m + 2), 𝒳 := by
              gcongr with i _
              exact level1_of_level2 V hlam0 hgm h2 i
          _ = ENNReal.ofReal (((m + 2 : ℕ) : ℝ) ^ 2) * 𝒳 := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
                ENNReal.ofReal_natCast, ← mul_assoc, sq, ENNReal.ofReal_mul (by positivity),
                ENNReal.ofReal_natCast]

end TripleCrude

section TripleAll

theorem tripleSum_two (g3 : Torus d → Torus d → Torus d → ℝ) (X : Config d 2) : tripleSum g3 X = 0 := by
  unfold tripleSum
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj => Finset.sum_eq_zero fun k hk => ?_
  exfalso
  have h1 : j ≠ i := Finset.ne_of_mem_erase hj
  have h2 : k ≠ j := Finset.ne_of_mem_erase hk
  have h3 : k ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
  have h1' : j.val ≠ i.val := fun h => h1 (Fin.ext h)
  have h2' : k.val ≠ j.val := fun h => h2 (Fin.ext h)
  have h3' : k.val ≠ i.val := fun h => h3 (Fin.ext h)
  have := i.2; have := j.2; have := k.2
  omega

/-- Part (t) of Proposition 4.12 for `Q_{N,β}(μ)`, all `N ≥ 2`. -/
theorem partt_all (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β) (ρ : Torus d → ℝ)
    (hρs : SmoothPosDensity ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : ℝ) (g3 : Torus d → Torus d → Torus d → ℝ),
      Measurable (fun p : Torus d × Torus d × Torus d => g3 p.1 p.2.1 p.2.2) →
      IsSymmTriple g3 → IsCanonicalTriple (withDensityReal ρ) g3 →
      (∀ x y z, x ≠ y → x ≠ z → y ≠ z → |g3 x y z| ≤ K * tEnv s x y z) → ∀ N : ℕ, 2 ≤ N →
        evariance (fun X : Config d N => (N : ℝ) ^ (-(5 / 2 : ℝ)) * tripleSum g3 X)
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
          ENNReal.ofReal (C * K ^ 2 * logEN N ^ 2 / (N : ℝ) ^ 2) := by
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρs.density
  obtain ⟨c, Cq, Mmax, M'max, γmax, N₁, KQ, δC, C1, Cu, C2, Vf, hc, hCq, hN₁, hKQ, hδC, hC1, hCu, hC2, hVu, hbd,
    hprob, hcrude, hlarge, hlarge2⟩ := exists_setting hd hcrit β hβ ρ hρs
  obtain ⟨Cl, hCl0, hCl⟩ := partt_ref_large hd hcrit β hβ ρ hρs c hc Mmax M'max γmax Cq hCq Cu hCu δC hδC C2 hC2
  obtain ⟨Cc, hCc0, hCc⟩ := level2_crude hd hcrit β hβ ρ hρs c hc Mmax M'max γmax Cq hCq
  choose K' hK'pos hK'le using hcrude
  set Csum : ℝ := ∑ n ∈ Finset.range N₁, K' n * Cc * (N₁ : ℝ) ^ 3 with hCsum
  have hCsum0 : 0 ≤ Csum := Finset.sum_nonneg fun n _ => by have := hK'pos n; positivity
  refine ⟨max (KQ * Cl) Csum, le_trans (by positivity) (le_max_left _ _),
    fun K g3 hgm hsym hcan hg3 N hN => ?_⟩
  by_cases hN2 : N = 2
  · subst hN2
    have : (fun X : Config d 2 => ((2 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) * tripleSum g3 X) = 0 := by
      funext X
      simp [tripleSum_two]
    rw [this, evariance_zero]
    exact bot_le
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  have hm1 : 1 ≤ m := by omega
  have hF : Measurable (fun X : Config d (m + 2) => ((m + 2 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) * tripleSum g3 X) :=
    measurable_const.mul (measurable_tripleSum hgm)
  have hP : IsProbabilityMeasure (modulatedGibbs (periodicRiesz d s) (m + 2) β (withDensityReal ρ)) :=
    hprob (m + 1)
  have hNp : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
  have hL1 := logEN_pos' (N := m + 2) (by omega)
  by_cases hbig : N₁ ≤ m + 2
  · obtain ⟨hle, hκ, hRD⟩ := hlarge (m + 1) hbig
    have hRD2 := hlarge2 m hbig
    refine (evar_transfer_large hle hF).trans ?_
    have h1 := hCl (Vf (m + 1)) (hbd (m + 1)) (hVu (m + 1)) m hm1 hκ C1 hRD hRD2 K g3 hgm hsym hcan hg3
    refine (mul_le_mul' le_rfl h1).trans ?_
    rw [← ENNReal.ofReal_mul hKQ.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have : KQ * (Cl * K ^ 2 * logEN (m + 2) ^ 2 / ((m + 2 : ℕ) : ℝ) ^ 2) ≤
        max (KQ * Cl) Csum * K ^ 2 * logEN (m + 2) ^ 2 / ((m + 2 : ℕ) : ℝ) ^ 2 := by
      rw [← mul_div_assoc, ← mul_assoc, ← mul_assoc]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      have : 0 ≤ K ^ 2 * logEN (m + 2) ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right (le_max_left (KQ * Cl) Csum) this]
    exact this
  · push Not at hbig
    have hNlt : m + 2 < N₁ := hbig
    obtain ⟨hle⟩ : Nonempty (modulatedGibbs (periodicRiesz d s) (m + 2) β (withDensityReal ρ) ≤
        ENNReal.ofReal (K' (m + 1)) • pinnedLaw (Vf (m + 1)) (β / ((m + 2 : ℕ) : ℝ)) (m + 2)
          (fun e : Empty => e.elim)) := ⟨hK'le (m + 1)⟩
    have h2 := hCc (Vf (m + 1)) (hbd (m + 1)) m hm1 K g3 hgm hg3
    have hcr := crude_tripleSum (Vf (m + 1)) hβ.le (m := m) hgm
      (((m + 2 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ))) h2 hle
    refine hcr.trans ?_
    have hc2 : (((m + 2 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ))) ^ 2 = 1 / ((m + 2 : ℕ) : ℝ) ^ 5 := by
      rw [rpow_sq_neg (m + 2) (by omega)]
      have : (2 * (5 / 2 : ℝ)) = ((5 : ℕ) : ℝ) := by norm_num
      rw [this, Real.rpow_natCast]
    have hKn := hK'pos (m + 1)
    rw [hc2, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul hKn.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hterm : K' (m + 1) * Cc * (N₁ : ℝ) ^ 3 ≤ Csum := by
      rw [hCsum]
      exact Finset.single_le_sum (f := fun n => K' n * Cc * (N₁ : ℝ) ^ 3)
        (fun n _ => by have := hK'pos n; positivity) (Finset.mem_range.2 (by omega))
    have hNN1 : ((m + 2 : ℕ) : ℝ) ≤ (N₁ : ℝ) := by exact_mod_cast hNlt.le
    set Nr : ℝ := ((m + 2 : ℕ) : ℝ) with hNr
    have e : K' (m + 1) * (1 / Nr ^ 5 * (Nr ^ 2 * (Cc * K ^ 2 * Nr ^ 4 * logEN (m + 2) ^ 2)))
        = (K' (m + 1) * Cc * K ^ 2 * logEN (m + 2) ^ 2) * Nr := by
      field_simp
    rw [e]
    have h3 : (K' (m + 1) * Cc * K ^ 2 * logEN (m + 2) ^ 2) * Nr ≤
        (K' (m + 1) * Cc * (N₁ : ℝ) ^ 3) * K ^ 2 * logEN (m + 2) ^ 2 / Nr ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have h4 : Nr * Nr ^ 2 ≤ (N₁ : ℝ) ^ 3 := by
        have : Nr ^ 3 ≤ (N₁ : ℝ) ^ 3 := pow_le_pow_left₀ hNp.le hNN1 3
        nlinarith [this]
      have h5 : 0 ≤ K' (m + 1) * Cc * K ^ 2 * logEN (m + 2) ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h4 h5]
    refine h3.trans ?_
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have : 0 ≤ K ^ 2 * logEN (m + 2) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right (hterm.trans (le_max_right (KQ * Cl) Csum)) this]

end TripleAll

end HRS.PairMom

end
