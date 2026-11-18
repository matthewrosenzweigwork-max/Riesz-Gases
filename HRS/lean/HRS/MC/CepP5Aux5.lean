import HRS.MC.CepP5Aux4

/-!
# Packet P5, Aux5: the adjoint identity `∫ g · L F = ∫ (Fwd g - ∂_t g) · F`
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MC.CepP5

open HRS HRS.MC.CepP3 HRS.MC.CepP4

variable {d N : ℕ}

/-- The `k`-th coordinate of the drift. -/
def bk (b : ℝ × (Fin N → Euc d) → Fin N → Euc d) (k : Fin N × Fin d) (p : ℝ × (Fin N → Euc d)) : ℝ :=
  b p k.1 k.2

/-- The `k`-th spatial coordinate direction. -/
abbrev eV (d N : ℕ) (k : Fin N × Fin d) : ℝ × (Fin N → Euc d) := (0, configBasis d N k)

/-- The forward operator `c Δ g - div (b g)` in covering coordinates. -/
def Fwd (c : ℝ) (b : ℝ × (Fin N → Euc d) → Fin N → Euc d) (g : ℝ × (Fin N → Euc d) → ℝ)
    (p : ℝ × (Fin N → Euc d)) : ℝ :=
  c * ∑ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ g) p (eV d N k) (eV d N k)
    - ∑ k : Fin N × Fin d, fderiv ℝ (fun q => bk b k q * g q) p (eV d N k)

theorem vec_decomp (v : Fin N → Euc d) :
    ((0 : ℝ), v) = ∑ k : Fin N × Fin d, v k.1 k.2 • ((0 : ℝ), configBasis d N k) := by
  refine Prod.ext ?_ ?_
  · simp [Prod.fst_sum]
  · rw [Prod.snd_sum]
    funext i
    ext j
    simp [configBasis, Fintype.sum_prod_type, Pi.single_apply, Finset.sum_apply]

theorem fderiv_drift (b : ℝ × (Fin N → Euc d) → Fin N → Euc d) (F : ℝ × (Fin N → Euc d) → ℝ)
    (p : ℝ × (Fin N → Euc d)) :
    fderiv ℝ F p (0, b p) = ∑ k : Fin N × Fin d, bk b k p * fderiv ℝ F p (0, configBasis d N k) := by
  rw [vec_decomp (b p), map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_smul]
  rfl

theorem contDiffOn_fderiv2_apply {O : Set (ℝ × (Fin N → Euc d))} (hO : IsOpen O)
    {u : ℝ × (Fin N → Euc d) → ℝ} (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u O)
    (v w : ℝ × (Fin N → Euc d)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p => fderiv ℝ (fderiv ℝ u) p v w) O := by
  have h1 := hu.fderiv_of_isOpen (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) hO (by simp)
  have h2 := h1.fderiv_of_isOpen (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) hO (by simp)
  exact ((h2.clm_apply contDiffOn_const).clm_apply contDiffOn_const)

theorem contDiffOn_bk {O : Set (ℝ × (Fin N → Euc d))}
    {b : ℝ × (Fin N → Euc d) → Fin N → Euc d} (hb : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b O)
    (k : Fin N × Fin d) : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bk b k) O := by
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p => b p k.1) O :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) k.1).contDiff.comp_contDiffOn hb
  exact (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) k.2).contDiff.comp_contDiffOn h1

theorem fderiv_eval {F : ℝ × (Fin N → Euc d) → ℝ} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (p v w : ℝ × (Fin N → Euc d)) :
    fderiv ℝ (fun q => fderiv ℝ F q v) p w = fderiv ℝ (fderiv ℝ F) p w v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    (hF.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).differentiable (by simp) p
  rw [fderiv_clm_apply hd (differentiableAt_const v)]
  simp

theorem CK.fderiv2_self {O : Set (ℝ × (Fin N → Euc d))} {F : ℝ × (Fin N → Euc d) → ℝ} (h : CK O F)
    (v : ℝ × (Fin N → Euc d)) : CK O (fun p => fderiv ℝ (fderiv ℝ F) p v v) := by
  have := (h.fderiv_apply v).fderiv_apply v
  have e : (fun p => fderiv ℝ (fderiv ℝ F) p v v) = fun p => fderiv ℝ (fun q => fderiv ℝ F q v) p v := by
    funext p; exact (fderiv_eval h.smooth p v v).symm
  rw [e]; exact this

theorem ibp_Lop {O : Set (ℝ × (Fin N → Euc d))} (hO : IsOpen O) {g : ℝ × (Fin N → Euc d) → ℝ}
    (hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g O)
    {b : ℝ × (Fin N → Euc d) → Fin N → Euc d} (hb : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b O)
    (c : ℝ) {F : ℝ × (Fin N → Euc d) → ℝ} (hF : CK O F) :
    ∫ p, g p * HRS.MC.CepP3.Lop c b F p = ∫ p, (Fwd c b g p - fderiv ℝ g p (1, 0)) * F p := by
  haveI := isAddHaar_volume_cov (d := d) (N := N)
  have hA : CK O (fun p => fderiv ℝ F p (1, 0)) := hF.fderiv_apply _
  have hC : ∀ k, CK O (fun p => fderiv ℝ F p (eV d N k)) := fun k => hF.fderiv_apply _
  have hB : ∀ k, CK O (fun p => fderiv ℝ (fderiv ℝ F) p (eV d N k) (eV d N k)) := fun k => hF.fderiv2_self _
  have hbg : ∀ k, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p => bk b k p * g p) O :=
    fun k => (contDiffOn_bk hb k).mul hg
  have hdg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p => fderiv ℝ g p (1, 0)) O :=
    contDiffOn_fderiv_apply hO hg _
  -- pointwise expansion of the left side
  have hpt : ∀ p, g p * HRS.MC.CepP3.Lop c b F p = g p * fderiv ℝ F p (1, 0)
      + c * ∑ k, g p * fderiv ℝ (fderiv ℝ F) p (eV d N k) (eV d N k)
      + ∑ k, (bk b k p * g p) * fderiv ℝ F p (eV d N k) := by
    intro p
    unfold HRS.MC.CepP3.Lop
    rw [fderiv_drift b F p]
    have h1 : g p * (c * ∑ k, fderiv ℝ (fderiv ℝ F) p (eV d N k) (eV d N k)) =
        c * ∑ k, g p * fderiv ℝ (fderiv ℝ F) p (eV d N k) (eV d N k) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    have h2 : g p * ∑ k, bk b k p * fderiv ℝ F p (eV d N k) = ∑ k, (bk b k p * g p) * fderiv ℝ F p (eV d N k) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [mul_add, mul_add, h1, h2]
  -- integrability
  have iA := integrable_mul_O hg.continuousOn hA.smooth.continuous hA.compact hA.sub
  have iB : ∀ k, Integrable (fun p => g p * fderiv ℝ (fderiv ℝ F) p (eV d N k) (eV d N k)) := fun k =>
    integrable_mul_O hg.continuousOn (hB k).smooth.continuous (hB k).compact (hB k).sub
  have iC : ∀ k, Integrable (fun p => (bk b k p * g p) * fderiv ℝ F p (eV d N k)) := fun k =>
    integrable_mul_O (hbg k).continuousOn (hC k).smooth.continuous (hC k).compact (hC k).sub
  have lhs : ∫ p, g p * HRS.MC.CepP3.Lop c b F p =
      (- ∫ p, fderiv ℝ g p (1, 0) * F p) + c * (∑ k, ∫ p, fderiv ℝ (fderiv ℝ g) p (eV d N k) (eV d N k) * F p)
        + (∑ k, (- ∫ p, fderiv ℝ (fun q => bk b k q * g q) p (eV d N k) * F p)) := by
    simp only [hpt]
    have iB' : Integrable (fun p => c * ∑ k, g p * fderiv ℝ (fderiv ℝ F) p (eV d N k) (eV d N k)) :=
      (integrable_finsetSum _ fun k _ => iB k).const_mul c
    have iC' : Integrable (fun p => ∑ k, (bk b k p * g p) * fderiv ℝ F p (eV d N k)) :=
      integrable_finsetSum _ fun k _ => iC k
    have iAB : Integrable (fun p => g p * fderiv ℝ F p (1, 0)
        + c * ∑ k, g p * fderiv ℝ (fderiv ℝ F) p (eV d N k) (eV d N k)) := iA.add iB'
    rw [integral_add iAB iC', integral_add iA iB',
      integral_const_mul, integral_finsetSum _ (fun k _ => iB k),
      integral_finsetSum _ (fun k _ => iC k)]
    congr 1
    · congr 1
      · exact ibp_O hO hg hF.smooth hF.compact hF.sub (1, 0)
      · congr 1
        exact Finset.sum_congr rfl (fun k _ => ibp2_O hO hg hF (eV d N k))
    · exact Finset.sum_congr rfl (fun k _ => ibp_O hO (hbg k) hF.smooth hF.compact hF.sub (eV d N k))
  -- the right side
  have jB : ∀ k, Integrable (fun p => fderiv ℝ (fderiv ℝ g) p (eV d N k) (eV d N k) * F p) := fun k =>
    integrable_mul_O (contDiffOn_fderiv2_apply hO hg _ _).continuousOn hF.smooth.continuous hF.compact hF.sub
  have jC : ∀ k, Integrable (fun p => fderiv ℝ (fun q => bk b k q * g q) p (eV d N k) * F p) := fun k =>
    integrable_mul_O (contDiffOn_fderiv_apply hO (hbg k) _).continuousOn hF.smooth.continuous hF.compact hF.sub
  have jA := integrable_mul_O hdg.continuousOn hF.smooth.continuous hF.compact hF.sub
  have rhs : ∫ p, (Fwd c b g p - fderiv ℝ g p (1, 0)) * F p =
      c * (∑ k, ∫ p, fderiv ℝ (fderiv ℝ g) p (eV d N k) (eV d N k) * F p)
        - (∑ k, ∫ p, fderiv ℝ (fun q => bk b k q * g q) p (eV d N k) * F p)
        - ∫ p, fderiv ℝ g p (1, 0) * F p := by
    have hpt2 : ∀ p, (Fwd c b g p - fderiv ℝ g p (1, 0)) * F p =
        c * ∑ k, fderiv ℝ (fderiv ℝ g) p (eV d N k) (eV d N k) * F p
          - ∑ k, fderiv ℝ (fun q => bk b k q * g q) p (eV d N k) * F p
          - fderiv ℝ g p (1, 0) * F p := by
      intro p
      unfold Fwd
      simp only [sub_mul, Finset.sum_mul, mul_assoc, Finset.mul_sum]
    simp only [hpt2]
    have jB' : Integrable (fun p => c * ∑ k, fderiv ℝ (fderiv ℝ g) p (eV d N k) (eV d N k) * F p) :=
      (integrable_finsetSum _ fun k _ => jB k).const_mul c
    have jC' : Integrable (fun p => ∑ k, fderiv ℝ (fun q => bk b k q * g q) p (eV d N k) * F p) :=
      integrable_finsetSum _ fun k _ => jC k
    have jBC : Integrable (fun p => c * ∑ k, fderiv ℝ (fderiv ℝ g) p (eV d N k) (eV d N k) * F p
        - ∑ k, fderiv ℝ (fun q => bk b k q * g q) p (eV d N k) * F p) := jB'.sub jC'
    rw [integral_sub jBC jA, integral_sub jB' jC',
      integral_const_mul, integral_finsetSum _ (fun k _ => jB k), integral_finsetSum _ (fun k _ => jC k)]
  rw [lhs, rhs, Finset.sum_neg_distrib]
  ring

end HRS.MC.CepP5
