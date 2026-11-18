import HRS.MS.R26T8AP16f1

/-!
# S8.2 T8A P16f: the canonical half of the half-order defect
`r26t8a_defect_canonical_full`: for `CanonicalPair F` and `Conormal (rawGainReg (gainReg k σ + 2) σ) 0 M σ A F` (`σ < d`),
`newtonDefect` is canonical.  `newtonDefect = F + pairJ Q + Z`, `Z = Lop Q(.,y)(x) + Lop Q(x,.)(y)`, where the centring terms of `Lop`
vanish (`r26t8a_local_ibp_gen`), `pairJ Q` is canonical (`r26t8a_nonlocal_canonical_gen`) and `Z` is canonical (integrability by the row
lemma, zero rows by `r26t8a_local_ibp_gen` and `r26t8a_local_row_comm`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_canonical_add {d : ℕ} {mu : Measure (Euc d)} {f g : Euc d → Euc d → ℝ}
    (hf : CanonicalPair mu f) (hg : CanonicalPair mu g) : CanonicalPair mu (fun x y => f x y + g x y) := by
  refine ⟨fun y => (hf.1 y).add (hg.1 y), fun x => (hf.2.1 x).add (hg.2.1 x), fun y => ?_, fun x => ?_⟩
  · rw [integral_add (hf.1 y) (hg.1 y), hf.2.2.1 y, hg.2.2.1 y, add_zero]
  · rw [integral_add (hf.2.1 x) (hg.2.1 x), hf.2.2.2 x, hg.2.2.2 x, add_zero]

set_option maxHeartbeats 6400000 in
theorem r26t8a_defect_canonical_full (d : ℕ) (hd : 2 ≤ d) (k : ℕ)
    (a beta M sigma : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hsigma : sigma < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) (rho : Euc d → ℝ)
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) (F : Euc d → Euc d → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hFcan : CanonicalPair (HRS.Whole.withDensityReal rho) F)
    (hF : Conormal (r26t8a_rawGainReg (r26t8a_gainReg k sigma + 2) sigma) 0 M sigma A F) :
    CanonicalPair (HRS.Whole.withDensityReal rho)
      (newtonDefect (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi F) := by
  obtain ⟨C2, hC20, hC2⟩ := r26t8a_local_newton_bound_full d hd 2 0 a beta M sigma ha hbeta hM hsigma chi hchi
  have hF2 : Conormal (r26t8a_rawGainReg 2 sigma) 0 M sigma A F :=
    r26t8a_conormal_mono (r26t8a_rawGainReg_mono (Nat.le_add_left 2 _) sigma) hF
  obtain ⟨-, hQcan, hQ'⟩ := hC2 rho hrho F A hA hF2
  have hprob : HRS.Whole.IsProbDensity rho := hrho.1.1
  set mu := HRS.Whole.withDensityReal rho with hmu
  set C0 := critCoeff d a beta rho with hC0
  set Q : Euc d → Euc d → ℝ := localNewton mu beta⁻¹ chi F with hQdef
  have hCnu : C0.ν = beta⁻¹ := r26t8a_critCoeff_nu a beta rho
  have hQ1 : Conormal (0 + 2) 1 M (sigma - 2) (C2 * A) Q := hQ'
  have hQs : Conormal (0 + 2) 1 M (sigma - 2) (C2 * A) (fun x y => Q y x) :=
    r26t8a_f24_conormal_swap hchi hQ1
  have hC2A : 0 ≤ C2 * A := mul_nonneg hC20 hA
  have hcan1 : ∀ u, ∫ y, rho y * Q u y = 0 := fun u => by
    rw [← r26t8a_f25_wd_integral hprob (Q u)]; exact hQcan.2.2.2 u
  have hcan2 : ∀ u, ∫ y, rho y * (fun x y => Q y x) u y = 0 := fun u => by
    show ∫ y, rho y * Q y u = 0
    rw [← r26t8a_f25_wd_integral hprob (fun y => Q y u)]; exact hQcan.2.2.1 u
  have hLop : ∀ (G : Euc d → Euc d → ℝ) (y : Euc d), (fun x => r26t8a_Lop C0 (fun w => G w y) x) =
      fun x => beta⁻¹ * Laplacian.laplacian (fun z => G z y) x + inner ℝ (C0.drift 0 x) (pairGradX G x y) := by
    intro G y; funext x
    unfold r26t8a_Lop; rw [hCnu]; rfl
  have hibp1 : ∀ y, Integrable (fun x => r26t8a_Lop C0 (fun w => Q w y) x) mu ∧
      ∫ x, r26t8a_Lop C0 (fun w => Q w y) x ∂mu = 0 := by
    intro y
    have := r26t8a_local_ibp_gen d hd 0 1 a beta M sigma (C2 * A) ha hbeta hM hsigma hC2A rho hrho Q hQ1 y
    rw [hLop Q y]; exact this
  have hibp2 : ∀ x, Integrable (fun y => r26t8a_Lop C0 (Q x) y) mu ∧ ∫ y, r26t8a_Lop C0 (Q x) y ∂mu = 0 := by
    intro x
    have := r26t8a_local_ibp_gen d hd 0 1 a beta M sigma (C2 * A) ha hbeta hM hsigma hC2A rho hrho
      (fun x y => Q y x) hQs x
    have e := hLop (fun x y => Q y x) x
    exact (by rw [show (fun y => r26t8a_Lop C0 (Q x) y) = fun y => r26t8a_Lop C0 (fun w => (fun x y => Q y x) w x) y
      from rfl, e]; exact this)
  have hrow1 : ∀ x, Integrable (fun y => r26t8a_Lop C0 (fun w => Q w y) x) mu :=
    r26t8a_local_row_int d hd 1 a beta M sigma (C2 * A) ha hbeta hM hsigma hC2A hrho hQ1
  have hrow2 : ∀ y, Integrable (fun x => r26t8a_Lop C0 (Q x) y) mu := fun y =>
    r26t8a_local_row_int d hd 1 a beta M sigma (C2 * A) ha hbeta hM hsigma hC2A hrho hQs y
  have hcomm1 : ∀ x, ∫ y, r26t8a_Lop C0 (fun w => Q w y) x ∂mu = 0 := fun x => by
    rw [r26t8a_f25_wd_integral hprob]
    exact r26t8a_local_row_comm d hd 0 1 a beta M sigma (C2 * A) ha hbeta hM hsigma hC2A hrho hQ1 hcan1 x
  have hcomm2 : ∀ y, ∫ x, r26t8a_Lop C0 (Q x) y ∂mu = 0 := fun y => by
    rw [r26t8a_f25_wd_integral hprob]
    exact r26t8a_local_row_comm d hd 0 1 a beta M sigma (C2 * A) ha hbeta hM hsigma hC2A hrho hQs hcan2 y
  have hint2 : ∀ y, Integrable (oneJ C0 (fun u => Q u y)) mu := fun y =>
    (r26t8a_g5_row d hd 0 1 a beta M sigma ha hbeta hM hsigma rho hrho Q (C2 * A) hC2A hQ1 y).1
  have hint4 : ∀ x, Integrable (oneJ C0 (Q x)) mu := fun x =>
    (r26t8a_g5_row d hd 0 1 a beta M sigma ha hbeta hM hsigma rho hrho (fun x y => Q y x) (C2 * A) hC2A hQs x).1
  have hZ : CanonicalPair mu (fun x y => r26t8a_Lop C0 (fun w => Q w y) x + r26t8a_Lop C0 (Q x) y) := by
    refine ⟨fun y => (hibp1 y).1.add (hrow2 y), fun x => (hrow1 x).add (hibp2 x).1, fun y => ?_, fun x => ?_⟩
    · rw [integral_add (hibp1 y).1 (hrow2 y), (hibp1 y).2, hcomm2 y, add_zero]
    · rw [integral_add (hrow1 x) (hibp2 x).1, hcomm1 x, (hibp2 x).2, add_zero]
  have hJ : CanonicalPair mu (pairJ C0 mu Q) :=
    r26t8a_nonlocal_canonical_gen hd 0 1 a beta M sigma (C2 * A) ha hbeta hM hsigma hC2A rho hrho Q hQcan hQ1
  have hN : newtonDefect C0 mu chi F = fun x y => F x y +
      (pairJ C0 mu Q x y + (r26t8a_Lop C0 (fun w => Q w y) x + r26t8a_Lop C0 (Q x) y)) := by
    funext x y
    have e1 : newtonDefect C0 mu chi F x y = F x y + pairA C0 mu Q x y := by
      show F x y + pairA C0 mu (localNewton mu C0.ν chi F) x y = _
      rw [hCnu]
    have e2 := r26t8a_p15_defect_alg C0 mu Q x y (hibp1 y).1 (hint2 y) (hibp2 x).1 (hint4 x)
    rw [(hibp1 y).2, (hibp2 x).2] at e2
    linarith
  rw [hN]
  exact r26t8a_canonical_add hFcan (r26t8a_canonical_add hJ hZ)

end HRS.MS.R26T8A
