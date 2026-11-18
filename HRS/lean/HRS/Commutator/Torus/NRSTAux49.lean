import HRS.Commutator.Torus.NRSTAux48

/-!
# NRS-T, part 49: the base case `α' ∈ (0,1)` on the torus, by transference of `xsc`
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS HRS.Commutator.TorusNote.NRST

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

theorem nrstr_hbase (hd : 1 ≤ d) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (V : Fin d → NRST.TPA d)
    (hVr : ∀ j x, (NRST.ev (V j) x).im = 0) {L : ℝ} (hL0 : 0 ≤ L)
    (hLip : IsLipschitzVF L (NRST.vOf V)) (h : NRST.TPA d) :
    ‖NRST.Jf V (2 * σ) h‖ ≤ (((d : ℝ) + ((d : ℝ) + 2 * σ + 2) / 2) * L) * NRST.hom σ h := by
  set C : ℝ := (d : ℝ) + ((d : ℝ) + 2 * σ + 2) / 2 with hC
  have hC0 : 0 ≤ C := by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; rw [hC]; positivity
  have hN1 : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 := fun n => by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hNpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by linarith [hN1 n]
  obtain ⟨m0, hm0def⟩ : ∃ m0 : ℝ, m0 = nrstr_m0 d := ⟨_, rfl⟩
  have hm0 : 0 < m0 := by rw [hm0def]; exact nrstr_m0_pos
  -- the sequences
  have ha := (nrstr_pair_tendsto hσ0 V hVr h).norm
  rw [← hm0def] at ha
  have hlim : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hR1 : Tendsto (fun n : ℕ => (1 + 1 / (8 * ((n : ℝ) + 1))) ^ (2 * σ)) atTop (𝓝 1) := by
    have e1 : Tendsto (fun n : ℕ => 1 + 1 / (8 * ((n : ℝ) + 1))) atTop (𝓝 1) := by
      have := (hlim.const_mul (1 / 8)).const_add 1
      simp only [mul_zero, add_zero] at this
      refine this.congr fun n => ?_
      field_simp
    have := (Real.continuousAt_rpow_const 1 (2 * σ) (Or.inl one_ne_zero)).tendsto.comp e1
    rw [Real.one_rpow] at this
    exact this
  have hE : Tendsto (fun n : ℕ => (2 * Real.pi / (8 * ((n : ℝ) + 1))) ^ (2 * σ)) atTop (𝓝 0) := by
    have e1 : Tendsto (fun n : ℕ => 2 * Real.pi / (8 * ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have := hlim.const_mul (2 * Real.pi / 8)
      simp only [mul_zero] at this
      refine this.congr fun n => ?_
      field_simp
    have := (Real.continuousAt_rpow_const 0 (2 * σ) (Or.inr (by linarith))).tendsto.comp e1
    rw [Real.zero_rpow (by linarith : (2 * σ) ≠ 0)] at this
    exact this
  have hb : Tendsto (fun n : ℕ => C * L * m0 * ((1 + 1 / (8 * ((n : ℝ) + 1))) ^ (2 * σ) * NRST.hom σ h +
      (2 * Real.pi / (8 * ((n : ℝ) + 1))) ^ (2 * σ) * ‖h.coeff 0‖ ^ 2)) atTop
      (𝓝 (C * L * m0 * (1 * NRST.hom σ h + 0 * ‖h.coeff 0‖ ^ 2))) :=
    ((hR1.mul_const _).add (hE.mul_const _)).const_mul _
  have hle : ∀ n : ℕ, ‖HRS.Commutator.Whole.XNRS.xpair (2 * σ)
        (nrstr_W h ((n : ℝ) + 1) (by positivity))
        (HRS.Commutator.Whole.XNRS.xadv (nrstr_v V) (nrstr_W h ((n : ℝ) + 1) (by positivity))) /
        ((((n : ℝ) + 1) ^ d : ℝ) : ℂ)‖ ≤
      C * L * m0 * ((1 + 1 / (8 * ((n : ℝ) + 1))) ^ (2 * σ) * NRST.hom σ h +
        (2 * Real.pi / (8 * ((n : ℝ) + 1))) ^ (2 * σ) * ‖h.coeff 0‖ ^ 2) := by
    intro n
    have hNd : (0 : ℝ) < ((n : ℝ) + 1) ^ d := by have := hNpos n; positivity
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hNd.le, div_le_iff₀ hNd]
    have h1 := HRS.Commutator.Whole.XNRS.xsc hd hσ0 hσ1 (nrstr_v_xtvf V) hL0 (nrstr_v_xlip V hL0 hLip)
      (nrstr_W h ((n : ℝ) + 1) (by positivity))
    have h2 := nrstr_xhom_le hσ0 h (hN1 n)
    rw [← hm0def] at h2
    refine h1.trans ?_
    rw [← hC]
    calc C * L * HRS.Commutator.Whole.XNRS.xhom σ (nrstr_W h ((n : ℝ) + 1) (by positivity))
        ≤ C * L * (((n : ℝ) + 1) ^ d * m0 * ((1 + 1 / (8 * ((n : ℝ) + 1))) ^ (2 * σ) * NRST.hom σ h +
            (2 * Real.pi / (8 * ((n : ℝ) + 1))) ^ (2 * σ) * ‖h.coeff 0‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hC0 hL0)
      _ = _ := by ring
  have hfin := le_of_tendsto_of_tendsto' ha hb hle
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hm0.le, one_mul, zero_mul, add_zero] at hfin
  have : m0 * ‖NRST.Jf V (2 * σ) h‖ ≤ m0 * (C * L * NRST.hom σ h) := by nlinarith [hfin]
  exact le_of_mul_le_mul_left this hm0

end HRS.Commutator.TorusNote
