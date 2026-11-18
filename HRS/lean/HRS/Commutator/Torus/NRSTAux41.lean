import HRS.Commutator.Torus.NRSTAux40

/-!
# NRS-T, part 41: the multiplier bound `hmul` of `nrst_main`
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS HRS.Commutator.TorusNote.NRST

variable {d : ℕ} {s : ℝ}

lemma nrstr_hom_le_of_N2 {β C : ℝ} (hC : 0 ≤ C) {f Γ : NRST.TPA d}
    (h : eLpNorm (NRST.ev (NRST.lam β f)) 2 volume ≤
      ENNReal.ofReal C * eLpNorm (NRST.ev (NRST.lam β Γ)) 2 volume) :
    NRST.hom β f ≤ C ^ 2 * NRST.hom β Γ := by
  rw [nrstr_N2_lam, nrstr_N2_lam, ← ENNReal.ofReal_mul hC] at h
  have hs := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (Real.sqrt_nonneg _))).1 h
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
  rw [Real.sq_sqrt (NRST.hom_nonneg _ _), mul_pow, Real.sq_sqrt (NRST.hom_nonneg _ _)] at hsq
  exact hsq

lemma nrstr_mul_zero (V : Fin d → NRST.TPA d) (hVr : ∀ j x, (NRST.ev (V j) x).im = 0) {L : ℝ} (hL0 : 0 ≤ L)
    (hLip : IsLipschitzVF L (NRST.vOf V)) (a c : Fin d) (Γ : NRST.TPA d) (hΓ0 : Γ.coeff 0 = 0) :
    NRST.hom 0 (NRST.dd a (V c) * Γ) ≤ L ^ 2 * NRST.hom 0 Γ := by
  refine nrstr_hom_le_of_N2 hL0 ?_
  set m : NRST.TPA d := NRST.dd a (V c) with hm
  have h1 : eLpNorm (NRST.ev (NRST.lam 0 (m * Γ))) 2 volume ≤ eLpNorm (NRST.ev (m * Γ)) 2 volume := by
    have := nrstr_N2_le (g := NRST.lam 0 (m * Γ)) (f := m * Γ) (c := 1) zero_le_one (fun k => by
      unfold NRST.lam
      rw [NRST.coeff_mulSeq, norm_mul, Complex.norm_real, Real.norm_eq_abs, one_mul]
      by_cases hk : k = 0
      · simp [hk, NRST.lw_zero]
      · have : NRST.lw 0 k = 1 := by simp [NRST.lw, hk]
        simp [this])
    simpa using this
  have h2 : eLpNorm (NRST.ev (m * Γ)) 2 volume ≤ ENNReal.ofReal L * eLpNorm (NRST.ev Γ) 2 volume := by
    have hmeas : AEStronglyMeasurable (NRST.ev (m * Γ)) volume := (NRST.continuous_ev _).aestronglyMeasurable
    have : eLpNorm (NRST.ev (m * Γ)) 2 volume ≤ eLpNorm (L • NRST.ev Γ) 2 volume := by
      refine eLpNorm_mono hmeas fun x => ?_
      rw [NRST.ev_mul, Pi.mul_apply, norm_mul]
      rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hL0]
      exact mul_le_mul_of_nonneg_right (norm_ev_dd_le_of_lip V hVr hL0 hLip a c x) (norm_nonneg _)
    refine this.trans (le_of_eq ?_)
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hL0]
  have h3 : eLpNorm (NRST.ev Γ) 2 volume ≤ eLpNorm (NRST.ev (NRST.lam 0 Γ)) 2 volume := by
    have := nrstr_N2_le (g := Γ) (f := NRST.lam 0 Γ) (c := 1) zero_le_one (fun k => by
      unfold NRST.lam
      rw [NRST.coeff_mulSeq, norm_mul, Complex.norm_real, Real.norm_eq_abs, one_mul]
      by_cases hk : k = 0
      · simp [hk, hΓ0]
      · have : NRST.lw 0 k = 1 := by simp [NRST.lw, hk]
        simp [this])
    simpa using this
  exact h1.trans (h2.trans (mul_le_mul' le_rfl h3))

theorem nrstr_hmul (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ CB : ℝ, 0 ≤ CB ∧ ∀ (V : Fin d → NRST.TPA d), (∀ j x, (NRST.ev (V j) x).im = 0) → ∀ K : ℝ,
      TorusSubTransport d s (NRST.vOf V) K → ∀ m : ℕ, 1 ≤ m → m ≤ ⌊((d : ℝ) - s) / 2⌋₊ →
        ∀ (a c : Fin d) (Γ : NRST.TPA d), NRST.IsRealT Γ → Γ.coeff 0 = 0 →
          NRST.hom (((d : ℝ) - s) / 2 - ⌊((d : ℝ) - s) / 2⌋₊ + m - 1) (NRST.dd a (V c) * Γ) ≤
            (CB * K) ^ 2 * NRST.hom (((d : ℝ) - s) / 2 - ⌊((d : ℝ) - s) / 2⌋₊ + m - 1) Γ := by
  classical
  set α : ℝ := ((d : ℝ) - s) / 2 with hα
  set k0 : ℕ := ⌊α⌋₊ with hk0
  have hα0 : 0 ≤ α := by rw [hα]; linarith
  have hk0α : (k0 : ℝ) ≤ α := Nat.floor_le hα0
  have hex : ∀ m : ℕ, 1 ≤ m → m ≤ k0 → ∃ CB : ℝ, 0 ≤ CB ∧
      ∀ (V : Fin d → NRST.TPA d), (∀ j x, (NRST.ev (V j) x).im = 0) → ∀ K : ℝ,
        TorusSubTransport d s (NRST.vOf V) K → ∀ (a c : Fin d) (Γ : NRST.TPA d), NRST.IsRealT Γ →
          Γ.coeff 0 = 0 → NRST.hom (α - k0 + m - 1) (NRST.dd a (V c) * Γ) ≤
            (CB * K) ^ 2 * NRST.hom (α - k0 + m - 1) Γ := by
    intro m hm1 hmk
    have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have hmk' : (m : ℝ) ≤ k0 := by exact_mod_cast hmk
    have hτ0 : 0 ≤ α - k0 + m - 1 := by linarith
    have hτα : α - k0 + m - 1 ≤ α - 1 := by linarith
    rcases hτ0.lt_or_eq with hτ | hτ
    · exact nrstr_mul_tau hd hs0 hsd hτ hτα
    · refine ⟨1, zero_le_one, fun V hVr K hv a c Γ hΓ hΓ0 => ?_⟩
      obtain ⟨L, F, hL0, hF0, hLip, -, hLF⟩ := hv
      rw [← hτ]
      refine (nrstr_mul_zero V hVr hL0 hLip a c Γ hΓ0).trans ?_
      rw [one_mul]
      refine mul_le_mul_of_nonneg_right ?_ (NRST.hom_nonneg _ _)
      nlinarith
  choose! CBf hCBf using hex
  refine ⟨∑ m ∈ Finset.Icc 1 k0, CBf m, Finset.sum_nonneg fun m hm => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hm
    exact (hCBf m h1 h2).1
  intro V hVr K hv m hm1 hmk a c Γ hΓ hΓ0
  have hK0 : 0 ≤ K := by
    obtain ⟨L, F, hL0, hF0, -, -, hLF⟩ := hv
    linarith
  have hle : CBf m ≤ ∑ m ∈ Finset.Icc 1 k0, CBf m :=
    Finset.single_le_sum (f := CBf) (fun m hm => by
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hm
      exact (hCBf m h1 h2).1) (Finset.mem_Icc.2 ⟨hm1, hmk⟩)
  refine ((hCBf m hm1 hmk).2 V hVr K hv a c Γ hΓ hΓ0).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (NRST.hom_nonneg _ _)
  exact pow_le_pow_left₀ (mul_nonneg (hCBf m hm1 hmk).1 hK0) (mul_le_mul_of_nonneg_right hle hK0) 2

end HRS.Commutator.TorusNote
