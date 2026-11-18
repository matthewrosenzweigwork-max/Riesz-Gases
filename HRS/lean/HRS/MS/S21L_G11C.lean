import HRS.MS.S21L_G11A

/-!
# S21L G11C -- the Wick chaos of a finite-rank kernel in any orthonormal basis (R26-T3.G11, third step)

Port of the S9.4 finite-rank argument (`s94_wick_finiteRank`, `HRS/MS/R2ChaosAux10.lean`) to the abstract linear field
`η` of G11 (`S21LEta`): the Wick sections, in any orthonormal basis `a` of `L²_0(μ)`, of the centred finite-rank kernel
`∑ c_αβ P u_α ⊗ P u_β` converge in `L²(P)` to `∑ c_αβ (η(u_α)η(u_β) - E η(u_α)η(u_β))`.  Prefix `s21l_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.deprecated false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

open HRS.MS.R2Chaos HRS.Whole

variable {d : ℕ} {Ω' : Type} [MeasurableSpace Ω'] {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
  {P' : Measure Ω'} [IsProbabilityMeasure P'] {η : (Euc d → ℝ) → Ω' → ℝ} {Λ : ℝ}

theorem s21l_cov_proj (h : S21LEta μ P' η Λ) {f : Euc d → ℝ} (hf : MemLp f 2 μ) :
    ∫ ζ, η f ζ ^ 2 ∂P' ≤ Λ * ∫ x, (Whole.projMean μ f x) ^ 2 ∂μ := by
  have h1 := s21l_eta_center h hf
  have h2 : ∫ ζ, η f ζ ^ 2 ∂P' = ∫ ζ, η (fun x => f x - ∫ y, f y ∂μ) ζ ^ 2 ∂P' :=
    integral_congr_ae (by filter_upwards [h1] with ζ hζ; rw [hζ])
  rw [h2]
  have hc : MemLp (fun x => f x - ∫ y, f y ∂μ) 2 μ := hf.sub (memLp_const _)
  exact (h.cov _ hc).trans le_rfl

theorem s21l_remainder_le (h : S21LEta μ P' η Λ) {a : ℕ → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i))
    (hon : ∀ i j, ∫ x, Whole.projMean μ (a i) x * Whole.projMean μ (a j) x ∂μ = if i = j then 1 else 0)
    {u : Euc d → ℝ} (hu : IsR2Test u) (n : ℕ) :
    ∫ ζ, (η u ζ - ∑ i : Fin n, s94gam μ u a i * η (a i) ζ) ^ 2 ∂P' ≤
      Λ * (∫ x, (Whole.projMean μ u x) ^ 2 ∂μ - ∑ i : Fin n, s94gam μ u a i ^ 2) := by
  set γ : Fin n → ℝ := fun i => s94gam μ u a i with hγ
  have hu2 : MemLp u 2 μ := s21l_test_memLp hu
  have ha2 : ∀ i : Fin n, MemLp (a i) 2 μ := fun i => s21l_test_memLp (ha i)
  have hg : MemLp (fun x => ∑ i : Fin n, γ i * a i x) 2 μ :=
    memLp_finsetSum _ fun i _ => (ha2 i).const_mul _
  have hlin := h.lin u (fun x => ∑ i : Fin n, γ i * a i x) (-1) hu2 hg
  have hsum := s21l_eta_sum h Finset.univ γ (fun i : Fin n => a i) (fun i _ => ha2 i)
  set w : Euc d → ℝ := fun x => u x - ∑ i : Fin n, γ i * a i x with hw
  have hwe : u + (-1 : ℝ) • (fun x => ∑ i : Fin n, γ i * a i x) = w := by
    funext x; simp [hw, sub_eq_add_neg]
  rw [hwe] at hlin
  have hwL : MemLp w 2 μ := hu2.sub hg
  have h1 : ∫ ζ, (η u ζ - ∑ i : Fin n, γ i * η (a i) ζ) ^ 2 ∂P' = ∫ ζ, η w ζ ^ 2 ∂P' := by
    refine integral_congr_ae ?_
    filter_upwards [hlin, hsum] with ζ h1 h2
    rw [h1]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [h2]
    ring
  have hP : ∀ x, Whole.projMean μ w x = Whole.projMean μ u x - ∑ i : Fin n, γ i * Whole.projMean μ (a i) x := by
    intro x
    have hui : Integrable u μ := s94_test_integrable hu μ
    have hai : ∀ i : Fin n, Integrable (a i) μ := fun i => s94_test_integrable (ha i) μ
    have hsI : Integrable (fun x => ∑ i : Fin n, γ i * a i x) μ :=
      integrable_finset_sum _ fun i _ => (hai i).const_mul _
    have e1 : ∫ y, w y ∂μ = ∫ y, u y ∂μ - ∑ i : Fin n, γ i * ∫ y, a i y ∂μ := by
      simp only [hw]
      rw [integral_sub hui hsI, integral_finset_sum _ fun i _ => (hai i).const_mul _]
      simp only [integral_const_mul]
    show w x - ∫ y, w y ∂μ = (u x - ∫ y, u y ∂μ) - ∑ i : Fin n, γ i * (a i x - ∫ y, a i y ∂μ)
    rw [e1]
    simp only [hw, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [h1]
  refine (s21l_cov_proj h hwL).trans ?_
  have e2 : ∫ x, (Whole.projMean μ w x) ^ 2 ∂μ = ∫ x, (Whole.projMean μ u x - ∑ i : Fin n, γ i * Whole.projMean μ (a i) x) ^ 2 ∂μ :=
    integral_congr_ae (ae_of_all _ fun x => by beta_reduce; rw [hP x])
  rw [e2]
  exact le_of_eq (by rw [s94_remainder_sq ha hon hu n])

theorem s21l_gfam_joint (h : S21LEta μ P' η Λ) {m n : ℕ} {u : Fin m → Euc d → ℝ}
    (hu : ∀ α, IsR2Test (u α)) {a : ℕ → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i)) :
    S94GFam P' (fun (j : Fin (m + n)) ζ => η (Fin.append u (fun i : Fin n => a i) j) ζ) := by
  refine s21l_gfam h (f := Fin.append u (fun i : Fin n => a i)) fun j => ?_
  refine Fin.addCases (fun α => ?_) (fun i => ?_) j
  · simpa using s21l_test_memLp (μ := μ) (hu α)
  · simpa using s21l_test_memLp (μ := μ) (ha i)

theorem s21l_lin_joint_X {m n : ℕ} (u : Fin m → Euc d → ℝ) (a : ℕ → Euc d → ℝ) (α : Fin m) (ζ : Ω') :
    s94lin (fun (j : Fin (m + n)) ζ => η (Fin.append u (fun i : Fin n => a i) j) ζ)
      (Fin.append (Pi.single α 1) (fun _ : Fin n => (0 : ℝ))) ζ = η (u α) ζ := by
  unfold s94lin
  rw [Fin.sum_univ_add]
  simp [Pi.single_apply]

theorem s21l_lin_joint_Z {m n : ℕ} (u : Fin m → Euc d → ℝ) (a : ℕ → Euc d → ℝ) (γ : Fin n → ℝ) (ζ : Ω') :
    s94lin (fun (j : Fin (m + n)) ζ => η (Fin.append u (fun i : Fin n => a i) j) ζ)
      (Fin.append (fun _ : Fin m => (0 : ℝ)) γ) ζ = ∑ i : Fin n, γ i * η (a i) ζ := by
  unfold s94lin
  rw [Fin.sum_univ_add]
  simp

/-- Pointwise-in-`n` bound for the error of one product `Z_α Z_β - X_α X_β`. -/
theorem s21l_fr_D_bound (h : S21LEta μ P' η Λ) (hΛ0 : 0 ≤ Λ) {a : ℕ → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i))
    (hon : ∀ i j, ∫ x, Whole.projMean μ (a i) x * Whole.projMean μ (a j) x ∂μ = if i = j then 1 else 0)
    {m : ℕ} {u : Fin m → Euc d → ℝ} (hu : ∀ α, IsR2Test (u α))
    (α β : Fin m) (n : ℕ) :
    ∫ ζ, ((∑ i : Fin n, s94gam μ (u α) a i * η (a i) ζ) *
        (∑ i : Fin n, s94gam μ (u β) a i * η (a i) ζ) -
        η (u α) ζ * η (u β) ζ) ^ 2 ∂P' ≤
      6 * ((Λ * (∫ x, (Whole.projMean μ (u α) x) ^ 2 ∂μ - s94gsum μ (u α) a n)) *
          (Λ * ∫ x, (Whole.projMean μ (u β) x) ^ 2 ∂μ) +
        (∫ ζ, (η (u α) ζ) ^ 2 ∂P') *
          (Λ * (∫ x, (Whole.projMean μ (u β) x) ^ 2 ∂μ - s94gsum μ (u β) a n))) := by
  set G : Fin (m + n) → Ω' → ℝ := fun (j : Fin (m + n)) ζ =>
    η (Fin.append u (fun i : Fin n => a i) j) ζ with hG
  have hGf : S94GFam P' G := s21l_gfam_joint h hu ha
  set γ : Fin m → Fin n → ℝ := fun α i => s94gam μ (u α) a i with hγ
  set vX : Fin m → Fin (m + n) → ℝ := fun α => Fin.append (Pi.single α 1) (fun _ : Fin n => (0 : ℝ)) with hvX
  set vZ : Fin m → Fin (m + n) → ℝ := fun α => Fin.append (fun _ : Fin m => (0 : ℝ)) (γ α) with hvZ
  have hX : ∀ α ζ, s94lin G (vX α) ζ = η (u α) ζ := fun α ζ =>
    s21l_lin_joint_X (n := n) u a α ζ
  have hZ : ∀ α ζ, s94lin G (vZ α) ζ = ∑ i : Fin n, s94gam μ (u α) a i * η (a i) ζ :=
    fun α ζ => s21l_lin_joint_Z (m := m) u a (γ α) ζ
  have hU : ∀ α ζ, s94lin G (vX α - vZ α) ζ =
      η (u α) ζ - ∑ i : Fin n, s94gam μ (u α) a i * η (a i) ζ := fun α ζ => by
    rw [s94lin_sub, hX, hZ]
  have hS := s21l_gseq h ha hon
  -- second moments
  have qU : ∀ α, s94q P' G (vX α - vZ α) ≤ Λ * (∫ x, (Whole.projMean μ (u α) x) ^ 2 ∂μ - s94gsum μ (u α) a n) := by
    intro α
    unfold s94q
    simp_rw [hU]
    exact s21l_remainder_le h ha hon (hu α) n
  have qZ : ∀ α, s94q P' G (vZ α) ≤ Λ * ∫ x, (Whole.projMean μ (u α) x) ^ 2 ∂μ := by
    intro α
    have h1 := (hS n).2 (γ α)
    have h2 : s94q P' G (vZ α) = s94q P' (fun (i : Fin n) ζ => η (a i) ζ) (γ α) := by
      unfold s94q
      refine integral_congr_ae (ae_of_all _ fun ζ => ?_)
      simp only [hZ]
      rfl
    rw [h2]
    refine h1.trans ?_
    have := s94_gsum_le ha hon (hu α) n
    unfold s94gsum at this
    exact mul_le_mul_of_nonneg_left this hΛ0
  have qX : s94q P' G (vX α) = ∫ ζ, (η (u α) ζ) ^ 2 ∂P' := by
    unfold s94q; simp_rw [hX]
  have qX' : s94q P' G (vX β) = ∫ ζ, (η (u β) ζ) ^ 2 ∂P' := by
    unfold s94q; simp_rw [hX]
  -- pointwise bound
  have hpt : ∀ ζ, ((∑ i : Fin n, s94gam μ (u α) a i * η (a i) ζ) *
        (∑ i : Fin n, s94gam μ (u β) a i * η (a i) ζ) -
        η (u α) ζ * η (u β) ζ) ^ 2 ≤
      2 * (s94lin G (vX α - vZ α) ζ ^ 2 * s94lin G (vZ β) ζ ^ 2) +
        2 * (s94lin G (vX α) ζ ^ 2 * s94lin G (vX β - vZ β) ζ ^ 2) := by
    intro ζ
    simp only [hU, hZ, hX]
    set Za := ∑ i : Fin n, s94gam μ (u α) a i * η (a i) ζ
    set Zb := ∑ i : Fin n, s94gam μ (u β) a i * η (a i) ζ
    set Xa := η (u α) ζ
    set Xb := η (u β) ζ
    have : Za * Zb - Xa * Xb = -((Xa - Za) * Zb) - Xa * (Xb - Zb) := by ring
    rw [this]
    nlinarith [sq_nonneg ((Xa - Za) * Zb - Xa * (Xb - Zb))]
  have hi1 := hGf.integrable_sq_mul_sq (vX α - vZ α) (vZ β)
  have hi2 := hGf.integrable_sq_mul_sq (vX α) (vX β - vZ β)
  have hmain : ∫ ζ, ((∑ i : Fin n, s94gam μ (u α) a i * η (a i) ζ) *
        (∑ i : Fin n, s94gam μ (u β) a i * η (a i) ζ) -
        η (u α) ζ * η (u β) ζ) ^ 2 ∂P' ≤
      ∫ ζ, (2 * (s94lin G (vX α - vZ α) ζ ^ 2 * s94lin G (vZ β) ζ ^ 2) +
        2 * (s94lin G (vX α) ζ ^ 2 * s94lin G (vX β - vZ β) ζ ^ 2)) ∂P' := by
    have hR : Integrable (fun ζ => 2 * (s94lin G (vX α - vZ α) ζ ^ 2 * s94lin G (vZ β) ζ ^ 2) +
        2 * (s94lin G (vX α) ζ ^ 2 * s94lin G (vX β - vZ β) ζ ^ 2)) P' :=
      (hi1.const_mul 2).add (hi2.const_mul 2)
    have hmeasD : AEMeasurable (fun ζ => ((∑ i : Fin n, s94gam μ (u α) a i * η (a i) ζ) *
        (∑ i : Fin n, s94gam μ (u β) a i * η (a i) ζ) -
        η (u α) ζ * η (u β) ζ) ^ 2) P' := by
      have : (fun ζ => ((∑ i : Fin n, s94gam μ (u α) a i * η (a i) ζ) *
        (∑ i : Fin n, s94gam μ (u β) a i * η (a i) ζ) -
        η (u α) ζ * η (u β) ζ) ^ 2) =
          fun ζ => (s94lin G (vZ α) ζ * s94lin G (vZ β) ζ - s94lin G (vX α) ζ * s94lin G (vX β) ζ) ^ 2 := by
        funext ζ; simp only [hZ, hX]
      rw [this]
      exact (((hGf.meas_lin _).mul (hGf.meas_lin _)).sub ((hGf.meas_lin _).mul (hGf.meas_lin _))).pow_const 2
    have hL : Integrable (fun ζ => ((∑ i : Fin n, s94gam μ (u α) a i * η (a i) ζ) *
        (∑ i : Fin n, s94gam μ (u β) a i * η (a i) ζ) -
        η (u α) ζ * η (u β) ζ) ^ 2) P' := by
      refine Integrable.mono' hR hmeasD.aestronglyMeasurable (ae_of_all _ fun ζ => ?_)
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hpt ζ
    exact integral_mono hL hR hpt
  refine hmain.trans ?_
  rw [integral_add (hi1.const_mul 2) (hi2.const_mul 2), integral_const_mul, integral_const_mul]
  have b1 := hGf.bivariate_le (vX α - vZ α) (vZ β)
  have b2 := hGf.bivariate_le (vX α) (vX β - vZ β)
  have q1 := S94GFam.q_nonneg (P := P') (z := G) (vX α - vZ α)
  have q2 := S94GFam.q_nonneg (P := P') (z := G) (vZ β)
  have q3 := S94GFam.q_nonneg (P := P') (z := G) (vX α)
  have q4 := S94GFam.q_nonneg (P := P') (z := G) (vX β - vZ β)
  rw [qX] at b2
  have c1 : s94q P' G (vX α - vZ α) * s94q P' G (vZ β) ≤
      (Λ * (∫ x, (Whole.projMean μ (u α) x) ^ 2 ∂μ - s94gsum μ (u α) a n)) *
        (Λ * ∫ x, (Whole.projMean μ (u β) x) ^ 2 ∂μ) := mul_le_mul (qU α) (qZ β) q2 ((q1.trans (qU α)))
  have c2 : (∫ ζ, (η (u α) ζ) ^ 2 ∂P') * s94q P' G (vX β - vZ β) ≤
      (∫ ζ, (η (u α) ζ) ^ 2 ∂P') *
        (Λ * (∫ x, (Whole.projMean μ (u β) x) ^ 2 ∂μ - s94gsum μ (u β) a n)) :=
    mul_le_mul_of_nonneg_left (qU β) (by rw [← qX]; exact q3)
  nlinarith [b1, b2, c1, c2]


theorem s21l_fr_memLp (h : S21LEta μ P' η Λ) {a : ℕ → Euc d → ℝ}
    (ha : ∀ i, IsR2Test (a i)) {m : ℕ} {u : Fin m → Euc d → ℝ} (hu : ∀ α, IsR2Test (u α))
    (α β : Fin m) (n : ℕ) :
    MemLp (fun ζ => (∑ i : Fin n, s94gam μ (u α) a i * η (a i) ζ) *
        (∑ i : Fin n, s94gam μ (u β) a i * η (a i) ζ)) 2 P' ∧
      MemLp (fun ζ => η (u α) ζ * η (u β) ζ) 2 P' := by
  set G : Fin (m + n) → Ω' → ℝ := fun (j : Fin (m + n)) ζ =>
    η (Fin.append u (fun i : Fin n => a i) j) ζ with hG
  have hGf : S94GFam P' G := s21l_gfam_joint h hu ha
  constructor
  · have e : (fun ζ => (∑ i : Fin n, s94gam μ (u α) a i * η (a i) ζ) *
        (∑ i : Fin n, s94gam μ (u β) a i * η (a i) ζ)) =
        fun ζ => s94lin G (Fin.append (fun _ : Fin m => (0 : ℝ)) (fun i : Fin n => s94gam μ (u α) a i)) ζ *
          s94lin G (Fin.append (fun _ : Fin m => (0 : ℝ)) (fun i : Fin n => s94gam μ (u β) a i)) ζ := by
      funext ζ
      rw [hG, s21l_lin_joint_Z (m := m) u a, s21l_lin_joint_Z (m := m) u a]
    rw [e]
    exact hGf.memLp_lin_mul _ _
  · have e : (fun ζ => η (u α) ζ * η (u β) ζ) =
        fun ζ => s94lin G (Fin.append (Pi.single α 1) (fun _ : Fin n => (0 : ℝ))) ζ *
          s94lin G (Fin.append (Pi.single β 1) (fun _ : Fin n => (0 : ℝ))) ζ := by
      funext ζ
      rw [hG, s21l_lin_joint_X (n := n) u a, s21l_lin_joint_X (n := n) u a]
    rw [e]
    exact hGf.memLp_lin_mul _ _

/-- The Wick chaos of the centered finite-rank kernel `∑ c_αβ P u_α ⊗ P u_β` is `∑ c_αβ (η(u_α)η(u_β) - E)`,
whatever the orthonormal basis. -/
theorem s21l_wick_finiteRank (h : S21LEta μ P' η Λ)
    (hΛ0 : 0 ≤ Λ) {a : ℕ → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i))
    (hon : ∀ i j, ∫ x, Whole.projMean μ (a i) x * Whole.projMean μ (a j) x ∂μ = if i = j then 1 else 0)
    (hcomplete : ∀ f : Euc d → ℝ, MemLp f 2 μ → ∫ x, f x ∂μ = 0 → (∀ i, ∫ x, f x * a i x ∂μ = 0) → f =ᵐ[μ] 0)
    {m : ℕ} (c : Fin m → Fin m → ℝ) {u : Fin m → Euc d → ℝ} (hu : ∀ α, IsR2Test (u α))
    :
    s94WickL2 P' μ a (fun i ζ => η (a i) ζ) (r2CenterKernel μ (r2FiniteRankKernel c u))
      (fun ζ => ∑ α, ∑ β, c α β * (η (u α) ζ * η (u β) ζ -
        ∫ ζ', η (u α) ζ' * η (u β) ζ' ∂P')) := by
  set z : ℕ → Ω' → ℝ := fun i ζ => η (a i) ζ with hz
  have hS := s21l_gseq h ha hon
  have hXG : S94GFam P' (fun (α : Fin m) ζ => η (u α) ζ) := s21l_gfam h (fun α => s21l_test_memLp (hu α))
  set Q : Ω' → ℝ := fun ζ => ∑ α, ∑ β, c α β * (η (u α) ζ * η (u β) ζ -
        ∫ ζ', η (u α) ζ' * η (u β) ζ' ∂P') with hQ
  have hQL : MemLp Q 2 P' := by
    refine memLp_finsetSum _ fun α _ => memLp_finsetSum _ fun β _ => ?_
    exact ((hXG.memLp_zz α β).sub (memLp_const _)).const_mul (c α β)
  refine ⟨hQL, ?_⟩
  have hcoef : (fun i j => r2WickCoeff μ a (r2CenterKernel μ (r2FiniteRankKernel c u)) i j) =
      fun i j => ∑ α, ∑ β, c α β * s94gam μ (u α) a i * s94gam μ (u β) a j := by
    funext i j; exact s94_coeff_finiteRank ha hu i j
  rw [hcoef]
  set Zn : Fin m → ℕ → Ω' → ℝ := fun α n ζ => ∑ i : Fin n, s94gam μ (u α) a i * z i ζ with hZn
  have hsec : ∀ n ζ, s94Sec P' z (fun i j => ∑ α, ∑ β, c α β * s94gam μ (u α) a i * s94gam μ (u β) a j) n ζ =
      ∑ α, ∑ β, c α β * (Zn α n ζ * Zn β n ζ - ∫ ζ', Zn α n ζ' * Zn β n ζ' ∂P') := fun n ζ =>
    s94_sec_eq_of_coeff (s94_gseq_integrable_zz hS) c (fun α i => s94gam μ (u α) a i) n ζ
  set Xv : Fin m → Ω' → ℝ := fun α ζ => η (u α) ζ with hXv
  set D : ℕ → Fin m → Fin m → Ω' → ℝ := fun n α β ζ => Zn α n ζ * Zn β n ζ - Xv α ζ * Xv β ζ with hD
  have hDmem : ∀ n α β, MemLp (D n α β) 2 P' := fun n α β =>
    ((s21l_fr_memLp h ha hu α β n).1).sub ((s21l_fr_memLp h ha hu α β n).2)
  have hZZ : ∀ n α β, Integrable (fun ζ => Zn α n ζ * Zn β n ζ) P' := fun n α β =>
    ((s21l_fr_memLp h ha hu α β n).1).integrable (by norm_num)
  have hXX : ∀ α β, Integrable (fun ζ => Xv α ζ * Xv β ζ) P' := fun α β =>
    ((s21l_fr_memLp h ha hu α β 0).2).integrable (by norm_num)
  have hdiff : ∀ n ζ, s94Sec P' z (fun i j => ∑ α, ∑ β, c α β * s94gam μ (u α) a i * s94gam μ (u β) a j) n ζ - Q ζ =
      ∑ α, ∑ β, c α β * (D n α β ζ - ∫ ζ', D n α β ζ' ∂P') := by
    intro n ζ
    rw [hsec, hQ, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    have : ∫ ζ', D n α β ζ' ∂P' = ∫ ζ', Zn α n ζ' * Zn β n ζ' ∂P' - ∫ ζ', Xv α ζ' * Xv β ζ' ∂P' := by
      simp only [hD]
      exact integral_sub (hZZ n α β) (hXX α β)
    rw [this]
    simp only [hD, hXv]
    ring
  -- the bound
  set B : ℕ → ℝ := fun n => (m : ℝ) * m * ∑ α, ∑ β, c α β ^ 2 *
    (6 * ((Λ * (∫ x, (Whole.projMean μ (u α) x) ^ 2 ∂μ - s94gsum μ (u α) a n)) *
          (Λ * ∫ x, (Whole.projMean μ (u β) x) ^ 2 ∂μ) +
        (∫ ζ, (η (u α) ζ) ^ 2 ∂P') *
          (Λ * (∫ x, (Whole.projMean μ (u β) x) ^ 2 ∂μ - s94gsum μ (u β) a n)))) with hB
  have hbound : ∀ n, ∫ ζ, (s94Sec P' z (fun i j => ∑ α, ∑ β, c α β * s94gam μ (u α) a i * s94gam μ (u β) a j) n ζ -
      Q ζ) ^ 2 ∂P' ≤ B n := by
    intro n
    simp_rw [hdiff]
    have hy : ∀ α β, MemLp (fun ζ => c α β * (D n α β ζ - ∫ ζ', D n α β ζ' ∂P')) 2 P' := fun α β =>
      ((hDmem n α β).sub (memLp_const _)).const_mul (c α β)
    refine (s94_sq_sum_two hy).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun β _ => ?_
    have e : ∀ ζ, (c α β * (D n α β ζ - ∫ ζ', D n α β ζ' ∂P')) ^ 2 =
        c α β ^ 2 * (D n α β ζ - ∫ ζ', D n α β ζ' ∂P') ^ 2 := fun ζ => by ring
    simp_rw [e]
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ((s94_var_le (hDmem n α β)).trans ?_) (sq_nonneg _)
    exact s21l_fr_D_bound h hΛ0 ha hon hu α β n
  have hBt : Tendsto B atTop (𝓝 0) := by
    have hT : ∀ α, Tendsto (fun n => s94gsum μ (u α) a n) atTop (𝓝 (∫ x, (Whole.projMean μ (u α) x) ^ 2 ∂μ)) :=
      fun α => s94_gsum_tendsto ha hon hcomplete (hu α)
    have hr : ∀ α, Tendsto (fun n => Λ * (∫ x, (Whole.projMean μ (u α) x) ^ 2 ∂μ - s94gsum μ (u α) a n)) atTop (𝓝 0) := by
      intro α
      have := ((hT α).const_sub (∫ x, (Whole.projMean μ (u α) x) ^ 2 ∂μ)).const_mul Λ
      simpa using this
    have hterm : ∀ α β, Tendsto (fun n => c α β ^ 2 *
        (6 * ((Λ * (∫ x, (Whole.projMean μ (u α) x) ^ 2 ∂μ - s94gsum μ (u α) a n)) *
          (Λ * ∫ x, (Whole.projMean μ (u β) x) ^ 2 ∂μ) +
        (∫ ζ, (η (u α) ζ) ^ 2 ∂P') *
          (Λ * (∫ x, (Whole.projMean μ (u β) x) ^ 2 ∂μ - s94gsum μ (u β) a n))))) atTop (𝓝 0) := by
      intro α β
      have h1 := (((hr α).mul_const (Λ * ∫ x, (Whole.projMean μ (u β) x) ^ 2 ∂μ)).add
        ((hr β).const_mul (∫ ζ, (η (u α) ζ) ^ 2 ∂P'))).const_mul 6
      have h2 := h1.const_mul (c α β ^ 2)
      simpa using h2
    have hs : Tendsto (fun n => ∑ α, ∑ β, c α β ^ 2 *
        (6 * ((Λ * (∫ x, (Whole.projMean μ (u α) x) ^ 2 ∂μ - s94gsum μ (u α) a n)) *
          (Λ * ∫ x, (Whole.projMean μ (u β) x) ^ 2 ∂μ) +
        (∫ ζ, (η (u α) ζ) ^ 2 ∂P') *
          (Λ * (∫ x, (Whole.projMean μ (u β) x) ^ 2 ∂μ - s94gsum μ (u β) a n))))) atTop (𝓝 0) := by
      have := tendsto_finset_sum (Finset.univ : Finset (Fin m)) fun α _ =>
        tendsto_finset_sum (Finset.univ : Finset (Fin m)) fun β _ => hterm α β
      simpa using this
    have := hs.const_mul ((m : ℝ) * m)
    simpa [hB] using this
  exact squeeze_zero (fun n => integral_nonneg fun ζ => sq_nonneg _) hbound hBt

end HRS.MS.R26T3
