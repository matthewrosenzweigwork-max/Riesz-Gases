import HRS.Commutator.Torus.NRSTAux35

/-!
# NRS-T, part 36: identification of Fourier coefficients, and HLS/Sobolev for trigonometric polynomials
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS HRS.Commutator.TorusNote.NRST

variable {d : ℕ}

lemma nrstr_ae_eq_of_fcoef {u : Torus d → ℝ} {U : NRST.TPA d} (hU : NRST.IsRealT U) (hu : Integrable u)
    (h : ∀ k, Torus.fcoef u k = U.coeff k) :
    u =ᵐ[volume] fun x => (NRST.ev U x).re := by
  have ht : Integrable (fun x => (NRST.ev U x).re) :=
    (Complex.continuous_re.comp (NRST.continuous_ev U)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have := text_ae_eq_zero_of_fcoef (g := fun x => u x - (NRST.ev U x).re) (hu.sub ht) fun k => by
    rw [text_fcoef_sub hu ht, h k, nrstr_fcoef_re hU k, sub_self]
  filter_upwards [this] with x hx
  simpa [sub_eq_zero] using hx

lemma nrstr_eLpNorm_of_fcoef {u : Torus d → ℝ} {U : NRST.TPA d} (hU : NRST.IsRealT U) (hu : Integrable u)
    (h : ∀ k, Torus.fcoef u k = U.coeff k) (p : ℝ≥0∞) :
    eLpNorm u p volume = eLpNorm (NRST.ev U) p volume := by
  rw [eLpNorm_congr_ae (nrstr_ae_eq_of_fcoef hU hu h), nrstr_eLpNorm_re hU]

/-- HLS/Sobolev for trigonometric polynomials. -/
lemma nrstr_hls_trig (hd : 1 ≤ d) {σ : ℝ} (hσ : 0 < σ) {p q : ℝ≥0∞} (hp : 1 < p) (hpq : p < q) (hq : q < ⊤)
    (hrel : q⁻¹ = p⁻¹ - ENNReal.ofReal (σ / d)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : NRST.TPA d), NRST.IsRealT U → U.coeff 0 = 0 →
      ∀ w : Torus d → ℝ, MemLp w p volume →
        (∀ k, Torus.fcoef w k = ((NRST.lw σ k : ℝ) : ℂ) * U.coeff k) →
        eLpNorm (NRST.ev U) q volume ≤ ENNReal.ofReal C * eLpNorm w p volume := by
  obtain ⟨C, hC, h⟩ := text_hls_main hd σ p q hp hpq hq hσ hrel
  refine ⟨C, hC, fun U hU hU0 w hw hwk => ?_⟩
  have hw0 : Torus.fcoef w 0 = 0 := by rw [hwk 0, NRST.lw_zero]; simp
  obtain ⟨h', hh'm, hh'0, hh'k, hh'n⟩ := h w hw hw0
  have hq1 : (1 : ℝ≥0∞) ≤ q := hp.le.trans hpq.le
  have hh'i : Integrable h' := hh'm.integrable hq1
  have hcf : ∀ k, Torus.fcoef h' k = U.coeff k := by
    intro k
    by_cases hk : k = 0
    · subst hk; rw [hh'0, hU0]
    · rw [hh'k k hk, hwk k, ← mul_assoc, ← Complex.ofReal_mul]
      have : (2 * Real.pi * Lattice.enorm k) ^ (-σ) * NRST.lw σ k = 1 := by
        unfold NRST.lw
        rw [if_neg hk, ← Real.rpow_add (by have := NRST.enorm_pos hk; positivity)]
        simp
      rw [this]; simp
  rw [← nrstr_eLpNorm_of_fcoef hU hh'i hcf]
  exact hh'n

end HRS.Commutator.TorusNote
