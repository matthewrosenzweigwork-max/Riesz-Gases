import HRS.Commutator.Torus.NRSTAux36

/-!
# NRS-T, part 37: the `L^p` bound for `J^τ ∂_a W` via the Riesz transform and the ratio multiplier
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS HRS.Commutator.TorusNote.NRST

variable {d : ℕ}

lemma nrstr_Jb_dd_eq (τ : ℝ) (a : Fin d) (W : NRST.TPA d) :
    nrstr_Jb τ (NRST.dd a W) = NRST.mulSeq (fun k => nrstr_mmB τ (Lattice.toEuc k))
      (NRST.mulSeq (fun k => HRS.Commutator.Whole.XBB.xbbRm a (Lattice.toEuc k)) (NRST.lam (τ + 1) W)) := by
  rw [← AddMonoidAlgebra.coeff_inj]
  ext k
  simp only [nrstr_Jb, NRST.dd, NRST.lam, NRST.coeff_mulSeq]
  by_cases hk : k = 0
  · subst hk; simp [NRST.lw_zero]
  · have he := NRST.enorm_pos hk
    have hn : ‖Lattice.toEuc k‖ = Lattice.enorm k := rfl
    have hka : (Lattice.toEuc k) a = ((k a : ℤ) : ℝ) := by simp [Lattice.toEuc]
    unfold nrstr_mmB HRS.Commutator.Whole.XBB.xbbRm HRS.Commutator.Whole.XLI.bsymX NRST.lw nrstr_jb
    rw [if_neg hk, hn, hka]
    set t : ℝ := 2 * Real.pi * Lattice.enorm k with ht
    have htpos : 0 < t := by rw [ht]; positivity
    have key : t ^ (-τ) * t ^ (τ + 1) = t := by
      rw [← Real.rpow_add htpos]; simp
    have key' : (((t ^ (-τ) : ℝ)) : ℂ) * ((t ^ (τ + 1) : ℝ) : ℂ) = (t : ℂ) := by
      rw [← Complex.ofReal_mul, key]
    have hc : (Lattice.enorm k : ℂ) ≠ 0 := by exact_mod_cast he.ne'
    have ht' : (t : ℂ) = 2 * (Real.pi : ℂ) * (Lattice.enorm k : ℂ) := by
      rw [ht]; push_cast; ring
    have hq : ((((k a : ℤ) : ℝ) / Lattice.enorm k : ℝ) : ℂ) = ((k a : ℤ) : ℂ) / (Lattice.enorm k : ℂ) := by
      push_cast; ring
    rw [hq]
    set A : ℂ := (((1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ (τ / 2) : ℝ) : ℂ) with hA
    set T1 : ℂ := (((t ^ (-τ) : ℝ)) : ℂ) with hT1
    set T2 : ℂ := (((t ^ (τ + 1) : ℝ)) : ℂ) with hT2
    calc A * (2 * ↑Real.pi * Complex.I * ((k a : ℤ) : ℂ) * W.coeff k)
        = A * (2 * (Real.pi : ℂ) * (Lattice.enorm k : ℂ)) * Complex.I * ((k a : ℤ) : ℂ) /
            (Lattice.enorm k : ℂ) * W.coeff k := by field_simp
      _ = A * (T1 * T2) * Complex.I * ((k a : ℤ) : ℂ) / (Lattice.enorm k : ℂ) * W.coeff k := by
          rw [key', ht']
      _ = _ := by ring

lemma nrstr_Jb_dd_bound (hd : 3 ≤ d) {τ : ℝ} (hτ : 0 < τ) (hτd : τ < d) {p : ℝ} (hp : 1 < p) (a : Fin d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ W : NRST.TPA d,
      eLpNorm (NRST.ev (nrstr_Jb τ (NRST.dd a W))) (ENNReal.ofReal p) volume ≤
        C * eLpNorm (NRST.ev (NRST.lam (τ + 1) W)) (ENNReal.ofReal p) volume := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Cr, hCr, hR⟩ := nrstr_riesz_T hd1 hp a
  obtain ⟨Cb, hCb, hB⟩ := nrstr_ratio_T hd hτ hτd hp
  refine ⟨Cb * Cr, ENNReal.mul_ne_top hCb hCr, fun W => ?_⟩
  rw [nrstr_Jb_dd_eq]
  refine (hB _).trans ?_
  rw [mul_assoc]
  gcongr
  refine hR _ ?_
  simp [NRST.lam, NRST.lw_zero]

end HRS.Commutator.TorusNote
