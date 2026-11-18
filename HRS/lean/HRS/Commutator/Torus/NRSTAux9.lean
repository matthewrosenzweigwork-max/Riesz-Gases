import HRS.Commutator.Torus.NRSTAux8

/-!
# NRS-T, part 9: the commutator bound for real trigonometric polynomials (conditional on base and multiplier bounds)
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal

namespace HRS.Commutator.TorusNote.NRST

open HRS HRS.Commutator

variable {d : ℕ} {s : ℝ}

theorem trig_bound (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {k : ℕ}
    (hk1 : (k : ℝ) ≤ ((d : ℝ) - s) / 2) (V : Fin d → TPA d) (A : TPA d)
    {L K C0 CB : ℝ} (hL0 : 0 ≤ L) (hLK : L ≤ K) (hC0 : 0 ≤ C0) (hCB : 0 ≤ CB)
    (hVr : ∀ j x, (ev (V j) x).im = 0) (hAr : ∀ x, (ev A x).im = 0) (hA0 : A.coeff 0 = 0)
    (hLip : IsLipschitzVF L (vOf V))
    (hbase : ∀ h : TPA d, IsRealT h → ‖Jf V (2 * (((d : ℝ) - s) / 2 - k)) h‖ ≤
      C0 * K * hom (((d : ℝ) - s) / 2 - k) h)
    (hmul : ∀ m : ℕ, 1 ≤ m → m ≤ k → ∀ (a c : Fin d) (Γ : TPA d), IsRealT Γ → Γ.coeff 0 = 0 →
      hom (((d : ℝ) - s) / 2 - k + m - 1) (dd a (V c) * Γ) ≤
        (CB * K) ^ 2 * hom (((d : ℝ) - s) / 2 - k + m - 1) Γ) :
    |CcommFunT (periodicRieszGrad d s) (vOf V) (aOf A)| ≤
      2 * rieszConst d s * Cm d C0 CB k * K * hom (-(((d : ℝ) - s) / 2)) A := by
  have hK : 0 ≤ K := hL0.trans hLK
  have hc0 : 0 < rieszConst d s := rieszConst_pos (by omega) hs0 (by linarith)
  have hα' : 0 ≤ ((d : ℝ) - s) / 2 - k := by linarith
  rw [comm_eq hd hs0 hsd V A hL0 hVr hAr hLip]
  set H := Rg d s A with hH
  set X := adv V H with hX
  have hAreal : IsRealT A := fun k => (conj_coeff_of_real A hAr k).symm
  have hind := ind V hK hC0 hCB hα' hbase hmul k le_rfl H (isRealT_Rg s hAreal)
  have e1 : 2 * (((d : ℝ) - s) / 2 - k) + 2 * (k : ℝ) = (d : ℝ) - s := by ring
  have e2 : ((d : ℝ) - s) / 2 - k + (k : ℝ) = ((d : ℝ) - s) / 2 := by ring
  rw [e1, e2, hom_Rg] at hind
  have hJ : Jf V ((d : ℝ) - s) H = (rieszConst d s : ℂ) * pr A X := by
    unfold Jf
    rw [hH, lam_Rg s A hA0]
    unfold pr
    rw [smul_mul_assoc, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]
  have hre : |(pr A X).re| ≤ ‖pr A X‖ := Complex.abs_re_le_norm _
  have hn : ‖Jf V ((d : ℝ) - s) H‖ = rieszConst d s * ‖pr A X‖ := by
    rw [hJ, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0.le]
  rw [hn] at hind
  have hh : 0 ≤ hom (-(((d : ℝ) - s) / 2)) A := hom_nonneg _ _
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have : rieszConst d s * ‖pr A X‖ ≤ Cm d C0 CB k * K * (rieszConst d s ^ 2 * hom (-(((d : ℝ) - s) / 2)) A) := hind
  have h3 : ‖pr A X‖ ≤ Cm d C0 CB k * K * (rieszConst d s * hom (-(((d : ℝ) - s) / 2)) A) := by
    have := (mul_le_mul_iff_of_pos_left hc0).1 (by nlinarith [this] : rieszConst d s * ‖pr A X‖ ≤
      rieszConst d s * (Cm d C0 CB k * K * (rieszConst d s * hom (-(((d : ℝ) - s) / 2)) A)))
    exact this
  nlinarith [hre, h3]

end HRS.Commutator.TorusNote.NRST
