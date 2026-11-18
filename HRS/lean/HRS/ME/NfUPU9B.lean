import HRS.Equilibrium.PairMomentsTT
import HRS.Equilibrium.PairMomentsL1
import HRS.ME.NfUPU9
import HRS.ME.NfUPU1bB

/-!
# Packet PU9, part B (uniform first-level and triple-sum bounds `level1_bound`, `partt_ref_large`)

Uniform copies (namespace `HRS.ME.NfU`) of the following lemmas (rule for uniform statements in
`docs/MAIN_E_NF_PLAN.md`, conventions as in `NfUPU9.lean`):

* `level1_bound_unif` of `HRS.PairMom.level1_bound` (PairMomentsL1 l.43).  Uses `level2_bound_unif`.
* `partt_ref_large_unif` of `HRS.PairMom.partt_ref_large` (PairMomentsTT l.49).  Uses `mean2_large_unif`
  (PairMomentsM2 with the fixed density bound `Λ₀`) and `level1_bound_unif`.  The hypotheses `weakKappa V β ≤ 1/2`,
  `RefDens V β …`, `RefDens2 V β …` mention `β` and stay after `V`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Function
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace HRS.ME.NfU

open HRS HRS.External HRS.Quad HRS.External.PoleVar HRS.PairMom HRS.PairCorrAux HRS.PoleCavityAux
  HRS.ME.PmU

variable {d : ℕ}

/-- Uniform `level1_bound`: the constant of `level2_bound_unif` is reused; uniform in `β ∈ Icc βm βp`, `ρ`. -/
theorem level1_bound_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp c₀ Λ₀ : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (hΛ : 1 ≤ Λ₀) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)
    (Mmax M'max γmax Cq : ℝ) (hCq : 0 ≤ Cq) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, RhoU d βm βp c₀ Λ₀ β ρ →
      ∀ (V : WeakPotential (withDensityReal ρ)),
      PotBound (d := d) s c Mmax M'max γmax Cq V → ∀ m : ℕ, 1 ≤ m → weakKappa V β ≤ 1 / 2 →
      ∀ (K A : ℝ), 0 ≤ A → ∀ (g3 : Torus d → Torus d → Torus d → ℝ),
      Measurable (fun p : Torus d × Torus d × Torus d => g3 p.1 p.2.1 p.2.2) →
      IsSymmTriple g3 →
      (∀ x y z, x ≠ y → x ≠ z → y ≠ z → |g3 x y z| ≤ K * tEnv s x y z) →
      (∀ x u : Torus d, x ≠ u →
        |∑ k : Fin m, ∫ z, g3 x u z ∂((pinnedLaw V (β / ((m + 2 : ℕ) : ℝ)) m
          (pinsWith (pinsWith (fun e : Empty => e.elim) x) u)).map (fun Y => Y k))| ≤
          A * (wEnv s x u * (logEN (m + 2) + ellEnv x u))) →
      ∀ i : Fin (m + 2),
        ∫⁻ Y, ‖tripleB g3 i (Y i) Y‖ₑ ^ 2
            ∂(pinnedLaw V (β / ((m + 2 : ℕ) : ℝ)) (m + 2) (fun e : Empty => e.elim)) ≤
          ENNReal.ofReal (C * (K ^ 2 + A ^ 2) * ((m + 2 : ℕ) : ℝ) ^ 2 * logEN (m + 2) ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := level2_bound_unif hd hcrit βm βp c₀ Λ₀ hβm hββ hΛ c hc Mmax M'max γmax Cq hCq
  refine ⟨C, hC0, fun β hβI ρ hU V hV m hm1 hκ K A hA g3 hgm hsym hg3 hMean i => ?_⟩
  have hβ : 0 < β := hU.hβpos
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hU.rho.density
  have hlam0 : 0 ≤ β / ((m + 2 : ℕ) : ℝ) := by positivity
  have hΦ : Measurable fun Y : Fin (m + 1 + 1) → Torus d => ‖tripleB g3 i (Y i) Y‖ₑ ^ 2 :=
    (measurable_tripleB hgm i).enorm.pow_const 2
  rw [lintegral_pinned_succ V hlam0 (fun e : Empty => e.elim) i hΦ]
  calc _ ≤ ∫⁻ x, pinWeight V (β / ((m + 2 : ℕ) : ℝ)) (fun e : Empty => e.elim) (m + 1) x *
        ENNReal.ofReal (C * (K ^ 2 + A ^ 2) * ((m + 2 : ℕ) : ℝ) ^ 2 * logEN (m + 2) ^ 2) ∂(withDensityReal ρ) := by
        refine lintegral_mono fun x => mul_le_mul' le_rfl ?_
        simp only [insertAt_same, tripleB_insertAt]
        exact hC β hβI ρ hU V hV m hm1 hκ K A hA g3 hgm hsym hg3 hMean x
    _ = _ := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
          lintegral_pinWeight V hlam0 (fun e : Empty => e.elim) i (0 : Fin (m + 1)), one_mul]

/-- Uniform `partt_ref_large`: the constant `18 Cl (1 + Cμ²)` (`Cμ` from `mean2_large_unif`, `Cl` from
`level1_bound_unif`) is chosen after the fixed data; uniform in `β ∈ Icc βm βp` and `ρ`. -/
theorem partt_ref_large_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp c₀ Λ₀ : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (hΛ : 1 ≤ Λ₀) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)
    (Mmax M'max γmax Cq : ℝ) (hCq : 0 ≤ Cq) (Cu : ℝ) (hCu : 0 ≤ Cu) (δC : ℝ) (hδC : 0 ≤ δC)
    (C2 : ℝ) (hC2 : 0 ≤ C2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, RhoU d βm βp c₀ Λ₀ β ρ →
      ∀ (V : WeakPotential (withDensityReal ρ)),
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
  obtain ⟨Cμ, hCμ0, hCμ⟩ := mean2_large_unif hd hcrit βm βp c₀ Λ₀ hβm hββ hΛ c hc Mmax M'max γmax Cq hCq
    Cu hCu δC hδC C2 hC2
  obtain ⟨Cl, hCl0, hCl⟩ := level1_bound_unif hd hcrit βm βp c₀ Λ₀ hβm hββ hΛ c hc Mmax M'max γmax Cq hCq
  refine ⟨18 * Cl * (1 + Cμ ^ 2), by positivity,
    fun β hβI ρ hU V hV hVu m hm1 hκ C1 RD1 RD2 K g3 hgm hsym hcan hg3 => ?_⟩
  have hβ : 0 < β := hU.hβpos
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hU.rho.density
  have hMean := hCμ β hβI ρ hU V hV hVu m hm1 C1 RD1 RD2 K g3 hgm hcan hg3
  have hl1 := fun i : Fin (m + 2) =>
    hCl β hβI ρ hU V hV m hm1 hκ K (|K| * Cμ) (by positivity) g3 hgm hsym hg3 hMean i
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

end HRS.ME.NfU

end
