import HRS.MS.R2ChaosAux9

/-!
# HRS.MS.R2ChaosAux10 -- the Wick chaos of a finite-rank kernel (convergence)

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

variable {d : ℕ}

section Generic

variable {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

theorem s94_var_le {D : Ω' → ℝ} (hD : MemLp D 2 P') : ∫ ζ, (D ζ - ∫ ζ', D ζ' ∂P') ^ 2 ∂P' ≤ ∫ ζ, D ζ ^ 2 ∂P' := by
  have h1 : Integrable D P' := hD.integrable (by norm_num)
  have h2 : Integrable (fun ζ => D ζ ^ 2) P' := hD.integrable_sq
  have e : ∀ ζ, (D ζ - ∫ ζ', D ζ' ∂P') ^ 2 = D ζ ^ 2 - 2 * (∫ ζ', D ζ' ∂P') * D ζ + (∫ ζ', D ζ' ∂P') ^ 2 :=
    fun ζ => by ring
  simp_rw [e]
  have i3 : Integrable (fun ζ => 2 * (∫ ζ', D ζ' ∂P') * D ζ) P' := h1.const_mul _
  have i23 : Integrable (fun ζ => D ζ ^ 2 - 2 * (∫ ζ', D ζ' ∂P') * D ζ) P' := h2.sub i3
  rw [integral_add i23 (integrable_const _), integral_sub h2 i3, integral_const_mul]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  nlinarith [sq_nonneg (∫ ζ', D ζ' ∂P')]

theorem s94_sq_sum_two {m : ℕ} {y : Fin m → Fin m → Ω' → ℝ} (hy : ∀ α β, MemLp (y α β) 2 P') :
    ∫ ζ, (∑ α, ∑ β, y α β ζ) ^ 2 ∂P' ≤ (m : ℝ) * m * ∑ α, ∑ β, ∫ ζ, y α β ζ ^ 2 ∂P' := by
  have hint : ∀ α β, Integrable (fun ζ => y α β ζ ^ 2) P' := fun α β => (hy α β).integrable_sq
  have hpt : ∀ ζ, (∑ α, ∑ β, y α β ζ) ^ 2 ≤ (m : ℝ) * m * ∑ α, ∑ β, y α β ζ ^ 2 := fun ζ => by
    calc (∑ α, ∑ β, y α β ζ) ^ 2 ≤ (Finset.univ : Finset (Fin m)).card * ∑ α, (∑ β, y α β ζ) ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ ≤ (Finset.univ : Finset (Fin m)).card * ∑ α, ((Finset.univ : Finset (Fin m)).card * ∑ β, y α β ζ ^ 2) := by
          gcongr with α _
          exact sq_sum_le_card_mul_sum_sq
      _ = (m : ℝ) * m * ∑ α, ∑ β, y α β ζ ^ 2 := by
          simp only [Finset.card_univ, Fintype.card_fin, ← Finset.mul_sum]
          ring
  calc ∫ ζ, (∑ α, ∑ β, y α β ζ) ^ 2 ∂P' ≤ ∫ ζ, (m : ℝ) * m * ∑ α, ∑ β, y α β ζ ^ 2 ∂P' := by
        refine integral_mono ?_ ?_ hpt
        · exact (memLp_finset_sum _ fun α _ => memLp_finset_sum _ fun β _ => hy α β).integrable_sq
        · exact (integrable_finset_sum _ fun α _ => integrable_finset_sum _ fun β _ => hint α β).const_mul _
    _ = _ := by
        rw [integral_const_mul, integral_finset_sum _ fun α _ => integrable_finset_sum _ fun β _ => hint α β]
        congr 1
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [integral_finset_sum _ fun β _ => hint α β]

end Generic

section FR

variable {s T b p K : ℝ} {μ : Measure (Euc d)} {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
  {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {X : ∀ N, ℝ≥0 → Ω N → EucConfig d N}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)}

/-- Squared norm sums. -/
def s94gsum (μ : Measure (Euc d)) (u : Euc d → ℝ) (a : ℕ → Euc d → ℝ) (n : ℕ) : ℝ :=
  ∑ i : Fin n, s94gam μ u a i ^ 2

theorem s94_gsum_le [IsProbabilityMeasure μ] {a : ℕ → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i))
    (hon : ∀ i j, ∫ x, Whole.projMean μ (a i) x * Whole.projMean μ (a j) x ∂μ = if i = j then 1 else 0)
    {u : Euc d → ℝ} (hu : IsR2Test u) (n : ℕ) :
    s94gsum μ u a n ≤ ∫ x, (Whole.projMean μ u x) ^ 2 ∂μ := by
  have h := s94_remainder_sq ha hon hu n
  have h0 : 0 ≤ ∫ x, (Whole.projMean μ u x - ∑ i : Fin n, s94gam μ u a i * Whole.projMean μ (a i) x) ^ 2 ∂μ :=
    integral_nonneg fun x => sq_nonneg _
  unfold s94gsum
  linarith

/-- Pointwise-in-`n` bound for the error of one product `Z_α Z_β - X_α X_β`. -/
theorem s94_fr_D_bound (hset : IsRound2PathSetting d s T b p K μ P X P' ξ) [IsProbabilityMeasure μ] {Λ : ℝ}
    (hcov : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ a, IsR2Test a →
      ∫ ζ, (r2PathEval T (ξ a ζ) t) ^ 2 ∂P' ≤ Λ * ∫ x, (Whole.projMean μ a x) ^ 2 ∂μ)
    (hΛ0 : 0 ≤ Λ) {a : ℕ → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i))
    (hon : ∀ i j, ∫ x, Whole.projMean μ (a i) x * Whole.projMean μ (a j) x ∂μ = if i = j then 1 else 0)
    {m : ℕ} {u : Fin m → Euc d → ℝ} (hu : ∀ α, IsR2Test (u α)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    (α β : Fin m) (n : ℕ) :
    ∫ ζ, ((∑ i : Fin n, s94gam μ (u α) a i * r2PathEval T (ξ (a i) ζ) t) *
        (∑ i : Fin n, s94gam μ (u β) a i * r2PathEval T (ξ (a i) ζ) t) -
        r2PathEval T (ξ (u α) ζ) t * r2PathEval T (ξ (u β) ζ) t) ^ 2 ∂P' ≤
      6 * ((Λ * (∫ x, (Whole.projMean μ (u α) x) ^ 2 ∂μ - s94gsum μ (u α) a n)) *
          (Λ * ∫ x, (Whole.projMean μ (u β) x) ^ 2 ∂μ) +
        (∫ ζ, (r2PathEval T (ξ (u α) ζ) t) ^ 2 ∂P') *
          (Λ * (∫ x, (Whole.projMean μ (u β) x) ^ 2 ∂μ - s94gsum μ (u β) a n))) := by
  set G : Fin (m + n) → Ω' → ℝ := fun (j : Fin (m + n)) ζ =>
    r2PathEval T (ξ (Fin.append u (fun i : Fin n => a i) j) ζ) t with hG
  have hGf : S94GFam P' G := s94_gfam_joint hset hu ha ht
  set γ : Fin m → Fin n → ℝ := fun α i => s94gam μ (u α) a i with hγ
  set vX : Fin m → Fin (m + n) → ℝ := fun α => Fin.append (Pi.single α 1) (fun _ : Fin n => (0 : ℝ)) with hvX
  set vZ : Fin m → Fin (m + n) → ℝ := fun α => Fin.append (fun _ : Fin m => (0 : ℝ)) (γ α) with hvZ
  have hX : ∀ α ζ, s94lin G (vX α) ζ = r2PathEval T (ξ (u α) ζ) t := fun α ζ =>
    s94_lin_joint_X (n := n) u a t α ζ
  have hZ : ∀ α ζ, s94lin G (vZ α) ζ = ∑ i : Fin n, s94gam μ (u α) a i * r2PathEval T (ξ (a i) ζ) t :=
    fun α ζ => s94_lin_joint_Z (m := m) u a t (γ α) ζ
  have hU : ∀ α ζ, s94lin G (vX α - vZ α) ζ =
      r2PathEval T (ξ (u α) ζ) t - ∑ i : Fin n, s94gam μ (u α) a i * r2PathEval T (ξ (a i) ζ) t := fun α ζ => by
    rw [s94lin_sub, hX, hZ]
  have hS := s94_gseq_of_setting hset hcov hΛ0 ha hon ht
  -- second moments
  have qU : ∀ α, s94q P' G (vX α - vZ α) ≤ Λ * (∫ x, (Whole.projMean μ (u α) x) ^ 2 ∂μ - s94gsum μ (u α) a n) := by
    intro α
    unfold s94q
    simp_rw [hU]
    exact s94_remainder_le hset hcov ha hon (hu α) ht n
  have qZ : ∀ α, s94q P' G (vZ α) ≤ Λ * ∫ x, (Whole.projMean μ (u α) x) ^ 2 ∂μ := by
    intro α
    have h1 := (hS n).2 (γ α)
    have h2 : s94q P' G (vZ α) = s94q P' (fun (i : Fin n) ζ => r2PathEval T (ξ (a i) ζ) t) (γ α) := by
      unfold s94q
      refine integral_congr_ae (ae_of_all _ fun ζ => ?_)
      simp only [hZ]
      rfl
    rw [h2]
    refine h1.trans ?_
    have := s94_gsum_le ha hon (hu α) n
    unfold s94gsum at this
    exact mul_le_mul_of_nonneg_left this hΛ0
  have qX : s94q P' G (vX α) = ∫ ζ, (r2PathEval T (ξ (u α) ζ) t) ^ 2 ∂P' := by
    unfold s94q; simp_rw [hX]
  have qX' : s94q P' G (vX β) = ∫ ζ, (r2PathEval T (ξ (u β) ζ) t) ^ 2 ∂P' := by
    unfold s94q; simp_rw [hX]
  -- pointwise bound
  have hpt : ∀ ζ, ((∑ i : Fin n, s94gam μ (u α) a i * r2PathEval T (ξ (a i) ζ) t) *
        (∑ i : Fin n, s94gam μ (u β) a i * r2PathEval T (ξ (a i) ζ) t) -
        r2PathEval T (ξ (u α) ζ) t * r2PathEval T (ξ (u β) ζ) t) ^ 2 ≤
      2 * (s94lin G (vX α - vZ α) ζ ^ 2 * s94lin G (vZ β) ζ ^ 2) +
        2 * (s94lin G (vX α) ζ ^ 2 * s94lin G (vX β - vZ β) ζ ^ 2) := by
    intro ζ
    simp only [hU, hZ, hX]
    set Za := ∑ i : Fin n, s94gam μ (u α) a i * r2PathEval T (ξ (a i) ζ) t
    set Zb := ∑ i : Fin n, s94gam μ (u β) a i * r2PathEval T (ξ (a i) ζ) t
    set Xa := r2PathEval T (ξ (u α) ζ) t
    set Xb := r2PathEval T (ξ (u β) ζ) t
    have : Za * Zb - Xa * Xb = -((Xa - Za) * Zb) - Xa * (Xb - Zb) := by ring
    rw [this]
    nlinarith [sq_nonneg ((Xa - Za) * Zb - Xa * (Xb - Zb))]
  have hi1 := hGf.integrable_sq_mul_sq (vX α - vZ α) (vZ β)
  have hi2 := hGf.integrable_sq_mul_sq (vX α) (vX β - vZ β)
  have hmain : ∫ ζ, ((∑ i : Fin n, s94gam μ (u α) a i * r2PathEval T (ξ (a i) ζ) t) *
        (∑ i : Fin n, s94gam μ (u β) a i * r2PathEval T (ξ (a i) ζ) t) -
        r2PathEval T (ξ (u α) ζ) t * r2PathEval T (ξ (u β) ζ) t) ^ 2 ∂P' ≤
      ∫ ζ, (2 * (s94lin G (vX α - vZ α) ζ ^ 2 * s94lin G (vZ β) ζ ^ 2) +
        2 * (s94lin G (vX α) ζ ^ 2 * s94lin G (vX β - vZ β) ζ ^ 2)) ∂P' := by
    have hR : Integrable (fun ζ => 2 * (s94lin G (vX α - vZ α) ζ ^ 2 * s94lin G (vZ β) ζ ^ 2) +
        2 * (s94lin G (vX α) ζ ^ 2 * s94lin G (vX β - vZ β) ζ ^ 2)) P' :=
      (hi1.const_mul 2).add (hi2.const_mul 2)
    have hmeasD : AEMeasurable (fun ζ => ((∑ i : Fin n, s94gam μ (u α) a i * r2PathEval T (ξ (a i) ζ) t) *
        (∑ i : Fin n, s94gam μ (u β) a i * r2PathEval T (ξ (a i) ζ) t) -
        r2PathEval T (ξ (u α) ζ) t * r2PathEval T (ξ (u β) ζ) t) ^ 2) P' := by
      have : (fun ζ => ((∑ i : Fin n, s94gam μ (u α) a i * r2PathEval T (ξ (a i) ζ) t) *
        (∑ i : Fin n, s94gam μ (u β) a i * r2PathEval T (ξ (a i) ζ) t) -
        r2PathEval T (ξ (u α) ζ) t * r2PathEval T (ξ (u β) ζ) t) ^ 2) =
          fun ζ => (s94lin G (vZ α) ζ * s94lin G (vZ β) ζ - s94lin G (vX α) ζ * s94lin G (vX β) ζ) ^ 2 := by
        funext ζ; simp only [hZ, hX]
      rw [this]
      exact (((hGf.meas_lin _).mul (hGf.meas_lin _)).sub ((hGf.meas_lin _).mul (hGf.meas_lin _))).pow_const 2
    have hL : Integrable (fun ζ => ((∑ i : Fin n, s94gam μ (u α) a i * r2PathEval T (ξ (a i) ζ) t) *
        (∑ i : Fin n, s94gam μ (u β) a i * r2PathEval T (ξ (a i) ζ) t) -
        r2PathEval T (ξ (u α) ζ) t * r2PathEval T (ξ (u β) ζ) t) ^ 2) P' := by
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
  have c2 : (∫ ζ, (r2PathEval T (ξ (u α) ζ) t) ^ 2 ∂P') * s94q P' G (vX β - vZ β) ≤
      (∫ ζ, (r2PathEval T (ξ (u α) ζ) t) ^ 2 ∂P') *
        (Λ * (∫ x, (Whole.projMean μ (u β) x) ^ 2 ∂μ - s94gsum μ (u β) a n)) :=
    mul_le_mul_of_nonneg_left (qU β) (by rw [← qX]; exact q3)
  nlinarith [b1, b2, c1, c2]

theorem s94_gsum_tendsto [IsProbabilityMeasure μ] {a : ℕ → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i))
    (hon : ∀ i j, ∫ x, Whole.projMean μ (a i) x * Whole.projMean μ (a j) x ∂μ = if i = j then 1 else 0)
    (hcomplete : ∀ f : Euc d → ℝ, MemLp f 2 μ → ∫ x, f x ∂μ = 0 → (∀ i, ∫ x, f x * a i x ∂μ = 0) → f =ᵐ[μ] 0)
    {u : Euc d → ℝ} (hu : IsR2Test u) :
    Tendsto (fun n => s94gsum μ u a n) atTop (𝓝 (∫ x, (Whole.projMean μ u x) ^ 2 ∂μ)) := by
  have := s94_parseval ha hon hcomplete (s94_memLp_projMean (μ := μ) hu) (s94_integral_projMean hu)
  refine this.congr fun n => ?_
  unfold s94gsum s94gam
  rw [s94_sum_fin_range (n := n) (fun i => (∫ x, Whole.projMean μ u x * Whole.projMean μ (a i) x ∂μ) ^ 2)]

theorem S94GFam.memLp_lin_mul {Ω'' : Type*} [MeasurableSpace Ω''] {P'' : Measure Ω''} [IsProbabilityMeasure P'']
    {N : ℕ} {G : Fin N → Ω'' → ℝ} (hG : S94GFam P'' G) (v w : Fin N → ℝ) :
    MemLp (fun ζ => s94lin G v ζ * s94lin G w ζ) 2 P'' := by
  refine (memLp_two_iff_integrable_sq ((hG.meas_lin v).mul (hG.meas_lin w)).aestronglyMeasurable).2 ?_
  refine (hG.integrable_sq_mul_sq v w).congr (ae_of_all _ fun ζ => ?_)
  simp [mul_pow]

theorem s94_gseq_integrable_zz {z : ℕ → Ω' → ℝ} {Λ : ℝ} (hz : S94GSeq P' z Λ) (i j : ℕ) :
    Integrable (fun ζ => z i ζ * z j ζ) P' := by
  have hi' : i < max (i + 1) (j + 1) := lt_max_of_lt_left (Nat.lt_succ_self i)
  have hj' : j < max (i + 1) (j + 1) := lt_max_of_lt_right (Nat.lt_succ_self j)
  exact (hz (max (i + 1) (j + 1))).1.integrable_zz ⟨i, hi'⟩ ⟨j, hj'⟩

theorem s94_fr_memLp (hset : IsRound2PathSetting d s T b p K μ P X P' ξ) {a : ℕ → Euc d → ℝ}
    (ha : ∀ i, IsR2Test (a i)) {m : ℕ} {u : Fin m → Euc d → ℝ} (hu : ∀ α, IsR2Test (u α))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (α β : Fin m) (n : ℕ) :
    MemLp (fun ζ => (∑ i : Fin n, s94gam μ (u α) a i * r2PathEval T (ξ (a i) ζ) t) *
        (∑ i : Fin n, s94gam μ (u β) a i * r2PathEval T (ξ (a i) ζ) t)) 2 P' ∧
      MemLp (fun ζ => r2PathEval T (ξ (u α) ζ) t * r2PathEval T (ξ (u β) ζ) t) 2 P' := by
  set G : Fin (m + n) → Ω' → ℝ := fun (j : Fin (m + n)) ζ =>
    r2PathEval T (ξ (Fin.append u (fun i : Fin n => a i) j) ζ) t with hG
  have hGf : S94GFam P' G := s94_gfam_joint hset hu ha ht
  constructor
  · have e : (fun ζ => (∑ i : Fin n, s94gam μ (u α) a i * r2PathEval T (ξ (a i) ζ) t) *
        (∑ i : Fin n, s94gam μ (u β) a i * r2PathEval T (ξ (a i) ζ) t)) =
        fun ζ => s94lin G (Fin.append (fun _ : Fin m => (0 : ℝ)) (fun i : Fin n => s94gam μ (u α) a i)) ζ *
          s94lin G (Fin.append (fun _ : Fin m => (0 : ℝ)) (fun i : Fin n => s94gam μ (u β) a i)) ζ := by
      funext ζ
      rw [hG, s94_lin_joint_Z (m := m) u a t, s94_lin_joint_Z (m := m) u a t]
    rw [e]
    exact hGf.memLp_lin_mul _ _
  · have e : (fun ζ => r2PathEval T (ξ (u α) ζ) t * r2PathEval T (ξ (u β) ζ) t) =
        fun ζ => s94lin G (Fin.append (Pi.single α 1) (fun _ : Fin n => (0 : ℝ))) ζ *
          s94lin G (Fin.append (Pi.single β 1) (fun _ : Fin n => (0 : ℝ))) ζ := by
      funext ζ
      rw [hG, s94_lin_joint_X (n := n) u a t, s94_lin_joint_X (n := n) u a t]
    rw [e]
    exact hGf.memLp_lin_mul _ _

/-- The Wick chaos of the centered finite-rank kernel `∑ c_αβ P u_α ⊗ P u_β` is `∑ c_αβ (ξ(u_α)ξ(u_β) - E)`,
whatever the orthonormal basis. -/
theorem s94_wick_finiteRank (hset : IsRound2PathSetting d s T b p K μ P X P' ξ) [IsProbabilityMeasure μ]
    {Λ : ℝ}
    (hcov : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ a, IsR2Test a →
      ∫ ζ, (r2PathEval T (ξ a ζ) t) ^ 2 ∂P' ≤ Λ * ∫ x, (Whole.projMean μ a x) ^ 2 ∂μ)
    (hΛ0 : 0 ≤ Λ) {a : ℕ → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i))
    (hon : ∀ i j, ∫ x, Whole.projMean μ (a i) x * Whole.projMean μ (a j) x ∂μ = if i = j then 1 else 0)
    (hcomplete : ∀ f : Euc d → ℝ, MemLp f 2 μ → ∫ x, f x ∂μ = 0 → (∀ i, ∫ x, f x * a i x ∂μ = 0) → f =ᵐ[μ] 0)
    {m : ℕ} (c : Fin m → Fin m → ℝ) {u : Fin m → Euc d → ℝ} (hu : ∀ α, IsR2Test (u α))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    s94WickL2 P' μ a (fun i ζ => r2PathEval T (ξ (a i) ζ) t) (r2CenterKernel μ (r2FiniteRankKernel c u))
      (fun ζ => ∑ α, ∑ β, c α β * (r2PathEval T (ξ (u α) ζ) t * r2PathEval T (ξ (u β) ζ) t -
        ∫ ζ', r2PathEval T (ξ (u α) ζ') t * r2PathEval T (ξ (u β) ζ') t ∂P')) := by
  set z : ℕ → Ω' → ℝ := fun i ζ => r2PathEval T (ξ (a i) ζ) t with hz
  have hS := s94_gseq_of_setting hset hcov hΛ0 ha hon ht
  have hXG : S94GFam P' (fun (α : Fin m) ζ => r2PathEval T (ξ (u α) ζ) t) := s94_gfam_of_setting hset hu ht
  set Q : Ω' → ℝ := fun ζ => ∑ α, ∑ β, c α β * (r2PathEval T (ξ (u α) ζ) t * r2PathEval T (ξ (u β) ζ) t -
        ∫ ζ', r2PathEval T (ξ (u α) ζ') t * r2PathEval T (ξ (u β) ζ') t ∂P') with hQ
  have hQL : MemLp Q 2 P' := by
    refine memLp_finset_sum _ fun α _ => memLp_finset_sum _ fun β _ => ?_
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
  set Xv : Fin m → Ω' → ℝ := fun α ζ => r2PathEval T (ξ (u α) ζ) t with hXv
  set D : ℕ → Fin m → Fin m → Ω' → ℝ := fun n α β ζ => Zn α n ζ * Zn β n ζ - Xv α ζ * Xv β ζ with hD
  have hDmem : ∀ n α β, MemLp (D n α β) 2 P' := fun n α β =>
    ((s94_fr_memLp hset ha hu ht α β n).1).sub ((s94_fr_memLp hset ha hu ht α β n).2)
  have hZZ : ∀ n α β, Integrable (fun ζ => Zn α n ζ * Zn β n ζ) P' := fun n α β =>
    ((s94_fr_memLp hset ha hu ht α β n).1).integrable (by norm_num)
  have hXX : ∀ α β, Integrable (fun ζ => Xv α ζ * Xv β ζ) P' := fun α β =>
    ((s94_fr_memLp hset ha hu ht α β 0).2).integrable (by norm_num)
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
        (∫ ζ, (r2PathEval T (ξ (u α) ζ) t) ^ 2 ∂P') *
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
    exact s94_fr_D_bound hset hcov hΛ0 ha hon hu ht α β n
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
        (∫ ζ, (r2PathEval T (ξ (u α) ζ) t) ^ 2 ∂P') *
          (Λ * (∫ x, (Whole.projMean μ (u β) x) ^ 2 ∂μ - s94gsum μ (u β) a n))))) atTop (𝓝 0) := by
      intro α β
      have h1 := (((hr α).mul_const (Λ * ∫ x, (Whole.projMean μ (u β) x) ^ 2 ∂μ)).add
        ((hr β).const_mul (∫ ζ, (r2PathEval T (ξ (u α) ζ) t) ^ 2 ∂P'))).const_mul 6
      have h2 := h1.const_mul (c α β ^ 2)
      simpa using h2
    have hs : Tendsto (fun n => ∑ α, ∑ β, c α β ^ 2 *
        (6 * ((Λ * (∫ x, (Whole.projMean μ (u α) x) ^ 2 ∂μ - s94gsum μ (u α) a n)) *
          (Λ * ∫ x, (Whole.projMean μ (u β) x) ^ 2 ∂μ) +
        (∫ ζ, (r2PathEval T (ξ (u α) ζ) t) ^ 2 ∂P') *
          (Λ * (∫ x, (Whole.projMean μ (u β) x) ^ 2 ∂μ - s94gsum μ (u β) a n))))) atTop (𝓝 0) := by
      have := tendsto_finset_sum (Finset.univ : Finset (Fin m)) fun α _ =>
        tendsto_finset_sum (Finset.univ : Finset (Fin m)) fun β _ => hterm α β
      simpa using this
    have := hs.const_mul ((m : ℝ) * m)
    simpa [hB] using this
  exact squeeze_zero (fun n => integral_nonneg fun ζ => sq_nonneg _) hbound hBt

end FR

end HRS.MS.R2Chaos
