import HRS.Commutator.Torus.NRSTAux30

/-!
# NRS-T, part 31: the Riesz transform bound on the torus (transference, conclusion)
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS HRS.Commutator.TorusNote.NRST

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- Transference: an `ℝ^d` `L^p` multiplier bound for the cut-off lifts gives the torus bound. -/
theorem nrstr_transfer (hd : 1 ≤ d) {p : ℝ} (hp : 1 < p) (mm : 𝔼 → ℂ) (S : Set (Lattice d))
    {Cx : ℝ≥0∞} (hCx : Cx ≠ ⊤)
    (hRd : ∀ f : NRST.TPA d, (∀ k ∈ f.coeff.support, k ∈ S) → ∃ θ : 𝔼 → ℂ, θ.HasTemperateGrowth ∧
        (∀ k ∈ f.coeff.support, θ (Lattice.toEuc k) = mm (Lattice.toEuc k)) ∧
        ∀ (N : ℝ) (hN : 1 ≤ N), ∃ Rs : SchwartzMap 𝔼 ℂ,
          (∀ x, Rs x = nrstg_T θ (nrstr_W f N (by linarith)) x) ∧
          eLpNorm (⇑Rs) (ENNReal.ofReal p) volume ≤
            Cx * eLpNorm (⇑(nrstr_W f N (by linarith))) (ENNReal.ofReal p) volume) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : NRST.TPA d, (∀ k ∈ f.coeff.support, k ∈ S) →
      eLpNorm (NRST.ev (NRST.mulSeq (fun k => mm (Lattice.toEuc k)) f)) (ENNReal.ofReal p) volume ≤
        C * eLpNorm (NRST.ev f) (ENNReal.ofReal p) volume := by
  classical
  have hp0 : 0 < p := by linarith
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨r, c, hr, hr1, hc, hφ⟩ := nrstr_phi_lower (d := d)
  obtain ⟨CU, hCU, hUp⟩ := nrstr_upper hd hr hr1 hp.le
  set c' : ℝ≥0∞ := ENNReal.ofReal c * ENNReal.ofReal ((r / d) ^ d) ^ (1 / p) with hc'
  have hc'0 : c' ≠ 0 := by
    rw [hc']
    refine mul_ne_zero (by simp [hc]) ?_
    exact (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 (by positivity)) ENNReal.ofReal_ne_top).ne'
  have hc't : c' ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
  refine ⟨c'⁻¹ * (Cx * ENNReal.ofReal CU), ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hc'0)
    (ENNReal.mul_ne_top hCx ENNReal.ofReal_ne_top), fun f hfS => ?_⟩
  obtain ⟨θ, hθ, hθf, hRs⟩ := hRd f hfS
  obtain ⟨CE, B, hB, hstep⟩ := nrstr_riesz_step hd hp mm hr hr1 hc hφ hUp f θ hθ hθf hRs
  have hlim : Tendsto (fun M : ℕ => Cx * ENNReal.ofReal CU * eLpNorm (NRST.ev f) (ENNReal.ofReal p) volume +
      ENNReal.ofReal (CE / ((d : ℝ) * ((M : ℝ) + 1) / r)) * B) atTop
      (𝓝 (Cx * ENNReal.ofReal CU * eLpNorm (NRST.ev f) (ENNReal.ofReal p) volume + 0 * B)) := by
    refine tendsto_const_nhds.add (ENNReal.Tendsto.mul_const ?_ (Or.inr hB))
    have h1 : Tendsto (fun M : ℕ => (d : ℝ) / r * ((M : ℝ) + 1)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity)
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    have h2 : Tendsto (fun M : ℕ => CE / ((d : ℝ) * ((M : ℝ) + 1) / r)) atTop (𝓝 0) := by
      have := h1.const_div_atTop CE
      refine this.congr fun M => ?_
      congr 1; ring
    simpa using ENNReal.tendsto_ofReal h2
  have hle := ge_of_tendsto' hlim hstep
  rw [zero_mul, add_zero] at hle
  calc eLpNorm (NRST.ev (NRST.mulSeq (fun k => mm (Lattice.toEuc k)) f))
        (ENNReal.ofReal p) volume
      = c'⁻¹ * (c' * eLpNorm (NRST.ev (NRST.mulSeq
        (fun k => mm (Lattice.toEuc k)) f)) (ENNReal.ofReal p) volume) := by
        rw [ENNReal.inv_mul_cancel_left hc'0 hc't]
    _ ≤ c'⁻¹ * (Cx * ENNReal.ofReal CU * eLpNorm (NRST.ev f) (ENNReal.ofReal p) volume) := by
        gcongr
    _ = _ := by ring

/-- The Riesz transform `R_a` on mean-free trigonometric polynomials is bounded on `L^p(𝕋^d)`. -/
theorem nrstr_riesz_T (hd : 1 ≤ d) {p : ℝ} (hp : 1 < p) (a : Fin d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : NRST.TPA d, f.coeff 0 = 0 →
      eLpNorm (NRST.ev (NRST.mulSeq
        (fun k => HRS.Commutator.Whole.XBB.xbbRm a (Lattice.toEuc k)) f)) (ENNReal.ofReal p) volume ≤
        C * eLpNorm (NRST.ev f) (ENNReal.ofReal p) volume := by
  classical
  obtain ⟨Cx, hCx, hRd⟩ := nrstr_Rd_bound hd hp a
  obtain ⟨C, hC, hT⟩ := nrstr_transfer hd hp (HRS.Commutator.Whole.XBB.xbbRm a) {k : Lattice d | k ≠ 0} hCx
    (fun f hfS => by
      set R : ℝ := 1 + ∑ k ∈ f.coeff.support, ‖Lattice.toEuc k‖ + 1 / 8 with hR
      have hR1 : 1 ≤ R := by
        have : 0 ≤ ∑ k ∈ f.coeff.support, ‖Lattice.toEuc k‖ := Finset.sum_nonneg fun k _ => norm_nonneg _
        rw [hR]; linarith
      refine hRd f R hR1 (fun k hk => ⟨hfS k hk, ?_⟩)
      have := Finset.single_le_sum (f := fun k => ‖Lattice.toEuc k‖) (fun k _ => norm_nonneg _) hk
      rw [hR]; linarith)
  refine ⟨C, hC, fun f hf0 => hT f fun k hk h => ?_⟩
  rw [h] at hk; exact (Finsupp.mem_support_iff.1 hk) hf0

end HRS.Commutator.TorusNote
