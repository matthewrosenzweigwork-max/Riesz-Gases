import HRS.Commutator.Torus.NRSTAux32

/-!
# NRS-T, part 33: low modes, and the ratio multiplier on `L^p(𝕋^d)`
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS HRS.Commutator.TorusNote.NRST

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma nrstr_coeff_le {P : ℝ≥0∞} (hP : 1 ≤ P) (f : NRST.TPA d) (k : Lattice d) :
    ‖f.coeff k‖ₑ ≤ eLpNorm (NRST.ev f) P volume := by
  have hcont := NRST.continuous_ev f
  refine le_trans ?_ (eLpNorm_le_eLpNorm_of_exponent_le hP (f := NRST.ev f))
  have h1 : ‖f.coeff k‖ₑ ≤ eLpNorm (NRST.ev f) 1 volume := by
    rw [← NRST.ev_coeff f k, eLpNorm_one_eq_lintegral_enorm]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    refine lintegral_mono fun x => ?_
    rw [enorm_mul]
    have : ‖Torus.mode (-k) x‖ₑ = 1 := by
      rw [← ofReal_norm, Torus.norm_mode]; simp
    rw [this, one_mul]
    all_goals try exact hcont.aestronglyMeasurable
  exact h1

lemma nrstr_eLpNorm_le_sum {P : ℝ≥0∞} (hP : 1 ≤ P) (h : NRST.TPA d) :
    eLpNorm (NRST.ev h) P volume ≤ ∑ k ∈ h.coeff.support, ‖h.coeff k‖ₑ := by
  have hb : ∀ᵐ x : Torus d ∂volume, ‖NRST.ev h x‖ ≤ ∑ k ∈ h.coeff.support, ‖h.coeff k‖ := by
    refine Filter.Eventually.of_forall fun x => ?_
    rw [NRST.ev_apply_sum]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
    rw [norm_mul, Torus.norm_mode, mul_one]
  have := eLpNorm_le_of_ae_bound (p := P) (NRST.continuous_ev h).aestronglyMeasurable hb
  rw [measure_univ, ENNReal.one_rpow, one_mul] at this
  refine this.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => norm_nonneg _)]
  exact Finset.sum_congr rfl fun k _ => ofReal_norm _

lemma nrstr_lowmodes {P : ℝ≥0∞} (hP : 1 ≤ P) (Slo : Finset (Lattice d)) (mm : Lattice d → ℂ)
    {C1 : ℝ≥0∞} (hC1 : C1 ≠ ⊤)
    (hhi : ∀ g : NRST.TPA d, (∀ k ∈ g.coeff.support, k ∉ Slo) →
      eLpNorm (NRST.ev (NRST.mulSeq mm g)) P volume ≤ C1 * eLpNorm (NRST.ev g) P volume) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ g : NRST.TPA d,
      eLpNorm (NRST.ev (NRST.mulSeq mm g)) P volume ≤ C * eLpNorm (NRST.ev g) P volume := by
  classical
  have hPt : ∀ x : ℝ≥0∞, x ≠ ⊤ → x ≠ ⊤ := fun _ h => h
  refine ⟨C1 * (1 + Slo.card) + ∑ k ∈ Slo, ‖mm k‖ₑ, ?_, fun g => ?_⟩
  · refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hC1 (by simp), ?_⟩
    exact ENNReal.sum_ne_top.2 fun k _ => enorm_ne_top
  set glo : NRST.TPA d := NRST.mulSeq (fun k => if k ∈ Slo then 1 else 0) g with hglo
  set ghi : NRST.TPA d := NRST.mulSeq (fun k => if k ∈ Slo then 0 else 1) g with hghi
  have hsplit : g = ghi + glo := by
    rw [← AddMonoidAlgebra.coeff_inj]
    ext k
    simp only [hglo, hghi, AddMonoidAlgebra.coeff_add, NRST.coeff_mulSeq, Finsupp.add_apply]
    split_ifs <;> simp
  have hlosupp : glo.coeff.support ⊆ Slo := by
    intro k hk
    by_contra hkS
    rw [Finsupp.mem_support_iff] at hk
    apply hk
    simp [hglo, hkS]
  have hhisupp : ∀ k ∈ ghi.coeff.support, k ∉ Slo := by
    intro k hk hkS
    rw [Finsupp.mem_support_iff] at hk
    apply hk
    simp [hghi, hkS]
  have hloc : ∀ k ∈ Slo, glo.coeff k = g.coeff k := by
    intro k hk; simp [hglo, hk]
  have hcg : ∀ k, ‖g.coeff k‖ₑ ≤ eLpNorm (NRST.ev g) P volume := fun k => nrstr_coeff_le hP g k
  -- low part of `ev g`
  have hlo1 : eLpNorm (NRST.ev glo) P volume ≤ Slo.card * eLpNorm (NRST.ev g) P volume := by
    refine (nrstr_eLpNorm_le_sum hP glo).trans ?_
    calc ∑ k ∈ glo.coeff.support, ‖glo.coeff k‖ₑ ≤ ∑ k ∈ Slo, ‖glo.coeff k‖ₑ :=
          Finset.sum_le_sum_of_subset hlosupp
      _ ≤ ∑ k ∈ Slo, eLpNorm (NRST.ev g) P volume :=
          Finset.sum_le_sum fun k hk => by rw [hloc k hk]; exact hcg k
      _ = _ := by simp
  have hlo2 : eLpNorm (NRST.ev (NRST.mulSeq mm glo)) P volume ≤
      (∑ k ∈ Slo, ‖mm k‖ₑ) * eLpNorm (NRST.ev g) P volume := by
    refine (nrstr_eLpNorm_le_sum hP _).trans ?_
    calc ∑ k ∈ (NRST.mulSeq mm glo).coeff.support, ‖(NRST.mulSeq mm glo).coeff k‖ₑ
        ≤ ∑ k ∈ Slo, ‖(NRST.mulSeq mm glo).coeff k‖ₑ :=
          Finset.sum_le_sum_of_subset ((NRST.supp_mulSeq_subset _ _).trans hlosupp)
      _ ≤ ∑ k ∈ Slo, ‖mm k‖ₑ * eLpNorm (NRST.ev g) P volume := by
          refine Finset.sum_le_sum fun k hk => ?_
          rw [NRST.coeff_mulSeq, enorm_mul, hloc k hk]
          gcongr
          exact hcg k
      _ = _ := by rw [Finset.sum_mul]
  -- high part
  have hhi1 : eLpNorm (NRST.ev ghi) P volume ≤ (1 + Slo.card) * eLpNorm (NRST.ev g) P volume := by
    have e : NRST.ev ghi = NRST.ev g - NRST.ev glo := by
      rw [hsplit, NRST.ev_add]
      · funext x; simp
    have hg' : g = ghi + glo := hsplit
    have e2 : NRST.ev ghi = NRST.ev g - NRST.ev glo := by
      have : NRST.ev g = NRST.ev ghi + NRST.ev glo := by
        conv_lhs => rw [hg']
        exact NRST.ev_add _ _
      funext x
      have := congrFun this x
      simp only [Pi.add_apply] at this
      simp only [Pi.sub_apply]
      rw [this]; ring
    rw [e2]
    refine (eLpNorm_sub_le hP).trans ?_
    calc eLpNorm (NRST.ev g) P volume + eLpNorm (NRST.ev glo) P volume
        ≤ eLpNorm (NRST.ev g) P volume + Slo.card * eLpNorm (NRST.ev g) P volume := by gcongr
      _ = _ := by ring
  have hdec : NRST.mulSeq mm g = NRST.mulSeq mm ghi + NRST.mulSeq mm glo := by
    conv_lhs => rw [hsplit]
    exact NRST.mulSeq_add _ _ _
  rw [hdec, NRST.ev_add]
  refine (eLpNorm_add_le hP).trans ?_
  calc eLpNorm (NRST.ev (NRST.mulSeq mm ghi)) P volume + eLpNorm (NRST.ev (NRST.mulSeq mm glo)) P volume
      ≤ C1 * eLpNorm (NRST.ev ghi) P volume + (∑ k ∈ Slo, ‖mm k‖ₑ) * eLpNorm (NRST.ev g) P volume :=
        add_le_add (hhi ghi hhisupp) hlo2
    _ ≤ C1 * ((1 + Slo.card) * eLpNorm (NRST.ev g) P volume) +
          (∑ k ∈ Slo, ‖mm k‖ₑ) * eLpNorm (NRST.ev g) P volume := by gcongr
    _ = _ := by ring

/-- The ratio multiplier `(1+4π²|k|²)^{β/2}(2π|k|)^{-β}` is bounded on `L^p(𝕋^d)` for trigonometric polynomials. -/
theorem nrstr_ratio_T (hd : 3 ≤ d) {β : ℝ} (hβ : 0 < β) (hβd : β < d) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ g : NRST.TPA d,
      eLpNorm (NRST.ev (NRST.mulSeq (fun k => nrstr_mmB β (Lattice.toEuc k)) g)) (ENNReal.ofReal p) volume ≤
        C * eLpNorm (NRST.ev g) (ENNReal.ofReal p) volume := by
  classical
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Cx, hCx, hRd⟩ := nrstr_Rd_bessel hd hβ hβd hp
  obtain ⟨C1, hC1, hT⟩ := nrstr_transfer hd1 hp (nrstr_mmB β) {k : Lattice d | 3 ≤ ‖Lattice.toEuc k‖} hCx hRd
  have hP : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le
  refine nrstr_lowmodes hP (Fintype.piFinset (fun _ : Fin d => Finset.Icc (-3 : ℤ) 3))
    (fun k => nrstr_mmB β (Lattice.toEuc k)) hC1 fun g hg => hT g fun k hk => ?_
  have hkS := hg k hk
  simp only [Fintype.mem_piFinset, Finset.mem_Icc, not_forall, not_and_or, not_le] at hkS
  obtain ⟨i, hi⟩ := hkS
  have h1 : |((k i : ℤ) : ℝ)| ≤ ‖Lattice.toEuc k‖ := by
    have := PiLp.norm_apply_le (Lattice.toEuc k) i
    simpa [Lattice.toEuc, Real.norm_eq_abs] using this
  have h2 : (4 : ℝ) ≤ |((k i : ℤ) : ℝ)| := by
    rcases hi with h | h
    · have : (k i : ℤ) ≤ -4 := by omega
      have : ((k i : ℤ) : ℝ) ≤ -4 := by exact_mod_cast this
      rw [abs_of_nonpos (by linarith)]; linarith
    · have : (4 : ℤ) ≤ k i := by omega
      have : (4 : ℝ) ≤ ((k i : ℤ) : ℝ) := by exact_mod_cast this
      rw [abs_of_nonneg (by linarith)]; exact this
  show 3 ≤ ‖Lattice.toEuc k‖
  linarith

end HRS.Commutator.TorusNote
