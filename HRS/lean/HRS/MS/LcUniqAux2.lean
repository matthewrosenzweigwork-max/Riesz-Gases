import HRS.MS.LcUniqAux1
import HRS.Whole.Adjoint

/-!
# LC-U (part 2): uniqueness of bounded classical backward solutions (S4.11, uniqueness)

`lc_unique`: two `IsLocalBackwardSolution ν b t f u₁/u₂` with the same data, `b r x = -(Qx) - c r + B r x`,
agree on `[0,t] × ℝ^d`.  Hypotheses (all for `r ∈ [0,t]` only): `0 ≤ ν r ≤ ν*`, `‖c r‖ ≤ Λc`,
`‖B r x‖ ≤ ΛB`.  No continuity of `ν`, `c`, `B` and no symmetry of `Q` is needed (the structure
`IsLocalBackwardSolution` carries the regularity of the solutions; the brief's continuity hypotheses
are therefore dropped, which only strengthens the statement).  `IsLocalBackwardSolution` is unchanged.

Route.  `w = u₁ - u₂` is bounded, jointly continuous, `C²` in `x`, `w(t) = 0`, `∂_r w + νΔw + b·∇w = 0`
for `r ∈ (0,t)`.  For `δ = r₀ ∈ (0,t]` the function `G(τ,z) = w(t-τ,z)` on `[0,t-δ]` has
`∂_τ G = νΔw + b·∇w` (only for `τ ∈ (0,t-δ]`), and the penalised maximum principle with the time derivative
on `(0,T]` only (`lu_penalized_max_Ioc`) applies: at a spatial maximum of `G - ε(1+‖z‖²)e^{λτ}` one has
`∇w = 2εe^{λτ} z`, `Δw ≤ 2dεe^{λτ}` (`lu_max_point`), hence
`∂_τ G ≤ εe^{λτ}(2dν* + 2‖Q‖‖z‖² + 2(Λc+ΛB)‖z‖) < ελ(1+‖z‖²)e^{λτ}` for `λ = 2dν* + 2‖Q‖ + Λc + ΛB + 1`.
Thus `w ≤ 0` on `[r₀,t]`; by symmetry `w = 0`; then `r = 0` by continuity.
-/

open Filter Topology Set
open scoped RealInnerProductSpace

namespace HRS.MS.Lc

open HRS HRS.Whole HRS.MS.PoisMax

variable {d : ℕ}

lemma lu_contOn {t : ℝ} {u : ℝ → Euc d → ℝ}
    (hc : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => u p.1 p.2) :
    ContinuousOn (fun p : ℝ × Euc d => u p.1 p.2) (Icc 0 t ×ˢ univ) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hψ : Continuous fun p : (Icc 0 t ×ˢ (univ : Set (Euc d)) : Set (ℝ × Euc d)) =>
      ((⟨p.1.1, p.2.1⟩ : Set.Icc (0 : ℝ) t), p.1.2) :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val)
  exact hc.comp hψ

lemma lu_contOn_rev {t T : ℝ} (hT : T ≤ t) {u : ℝ → Euc d → ℝ}
    (hc : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => u p.1 p.2) :
    ContinuousOn (fun p : ℝ × Euc d => u (t - p.1) p.2) (Icc 0 T ×ˢ univ) := by
  have hφ : Continuous fun p : ℝ × Euc d => ((t - p.1, p.2) : ℝ × Euc d) :=
    (continuous_const.sub continuous_fst).prodMk continuous_snd
  refine (lu_contOn hc).comp hφ.continuousOn ?_
  intro p hp
  refine ⟨⟨?_, ?_⟩, mem_univ _⟩
  · linarith [hp.1.2]
  · linarith [hp.1.1]

lemma lu_grad_sub {u v : Euc d → ℝ} (hu : Differentiable ℝ u) (hv : Differentiable ℝ v) (z : Euc d) :
    gradient (fun y => u y - v y) z = gradient u z - gradient v z := by
  have h : HasGradientAt (fun y => u y - v y) (gradient u z - gradient v z) z := by
    rw [hasGradientAt_iff_hasFDerivAt, map_sub]
    exact (hasGradientAt_iff_hasFDerivAt.mp (hu z).hasGradientAt).sub
      (hasGradientAt_iff_hasFDerivAt.mp (hv z).hasGradientAt)
  exact h.gradient

lemma lu_lap_sub {u v : Euc d → ℝ} (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (z : Euc d) :
    Laplacian.laplacian (fun y => u y - v y) z =
      Laplacian.laplacian u z - Laplacian.laplacian v z := by
  have := (hu.contDiffAt (x := z)).laplacian_sub (hv.contDiffAt (x := z))
  exact this

/-- One-sided comparison: `u₁ ≤ u₂` on `(0,t] × ℝ^d`. -/
theorem lu_one_sided {Q : Matrix (Fin d) (Fin d) ℝ} {c : ℝ → Euc d} {B : ℝ → Euc d → Euc d}
    {ν : ℝ → ℝ} {νstar Λc ΛB t : ℝ} {f : Euc d → ℝ} {u₁ u₂ : ℝ → Euc d → ℝ}
    (ht : 0 < t) (hν : ∀ r ∈ Icc 0 t, 0 ≤ ν r ∧ ν r ≤ νstar)
    (hc : ∀ r ∈ Icc 0 t, ‖c r‖ ≤ Λc) (hB : ∀ r ∈ Icc 0 t, ∀ x, ‖B r x‖ ≤ ΛB)
    (h₁ : IsLocalBackwardSolution ν (fun r x => -(Torus.matVec Q x) - c r + B r x) t f u₁)
    (h₂ : IsLocalBackwardSolution ν (fun r x => -(Torus.matVec Q x) - c r + B r x) t f u₂) :
    ∀ r ∈ Ioc 0 t, ∀ x, u₁ r x ≤ u₂ r x := by
  intro r hr x
  set T : ℝ := t - r with hT
  have hT0 : 0 ≤ T := by rw [hT]; linarith [hr.2]
  set K : ℝ := ‖(Matrix.toEuclideanLin Q).toContinuousLinearMap‖ with hK
  have hKb : ∀ z : Euc d, ‖Torus.matVec Q z‖ ≤ K * ‖z‖ := fun z =>
    ((Matrix.toEuclideanLin Q).toContinuousLinearMap).le_opNorm z
  have hνs : 0 ≤ νstar := (hν 0 ⟨le_rfl, ht.le⟩).1.trans (hν 0 ⟨le_rfl, ht.le⟩).2
  have hΛc : 0 ≤ Λc := (norm_nonneg _).trans (hc 0 ⟨le_rfl, ht.le⟩)
  have hΛB : 0 ≤ ΛB := (norm_nonneg _).trans (hB 0 ⟨le_rfl, ht.le⟩ 0)
  set lam : ℝ := 2 * d * νstar + 2 * K + Λc + ΛB + 1 with hlam
  -- the functions
  set G : ℝ → Euc d → ℝ := fun τ z => u₁ (t - τ) z - u₂ (t - τ) z with hG
  set Gt : ℝ → Euc d → ℝ := fun τ z =>
    ν (t - τ) * Laplacian.laplacian (fun y => u₁ (t - τ) y - u₂ (t - τ) y) z +
      inner ℝ (-(Torus.matVec Q z) - c (t - τ) + B (t - τ) z)
        (gradient (fun y => u₁ (t - τ) y - u₂ (t - τ) y) z) with hGt
  have hmemI : ∀ τ ∈ Icc 0 T, t - τ ∈ Icc 0 t := fun τ hτ =>
    ⟨by linarith [hτ.2, hr.1], by linarith [hτ.1]⟩
  have hcont : ContinuousOn (fun p : ℝ × Euc d => G p.1 p.2) (Icc 0 T ×ˢ univ) :=
    (lu_contOn_rev (by rw [hT]; linarith [hr.1]) h₁.cont).sub
      (lu_contOn_rev (by rw [hT]; linarith [hr.1]) h₂.cont)
  have hder : ∀ τ ∈ Ioc 0 T, ∀ z, HasDerivWithinAt (fun s => G s z) (Gt τ z) (Icc 0 T) τ := by
    intro τ hτ z
    have hr' : t - τ ∈ Ioo 0 t := ⟨by linarith [hτ.2, hr.1], by linarith [hτ.1]⟩
    have hneg : HasDerivAt (fun x : ℝ => t - x) (-1) τ := by
      simpa using (hasDerivAt_id τ).const_sub t
    have d1 := (h₁.time_deriv z (t - τ) hr').comp τ hneg
    have d2 := (h₂.time_deriv z (t - τ) hr').comp τ hneg
    have hd := d1.sub d2
    have e : Gt τ z = (-(ν (t - τ) * Laplacian.laplacian (u₁ (t - τ)) z +
          inner ℝ (-(Torus.matVec Q z) - c (t - τ) + B (t - τ) z) (gradient (u₁ (t - τ)) z))) * -1 -
        (-(ν (t - τ) * Laplacian.laplacian (u₂ (t - τ)) z +
          inner ℝ (-(Torus.matVec Q z) - c (t - τ) + B (t - τ) z) (gradient (u₂ (t - τ)) z))) * -1 := by
      simp only [hGt]
      rw [lu_lap_sub (h₁.c2 _ (hmemI τ ⟨hτ.1.le, hτ.2⟩)) (h₂.c2 _ (hmemI τ ⟨hτ.1.le, hτ.2⟩)),
        lu_grad_sub ((h₁.c2 _ (hmemI τ ⟨hτ.1.le, hτ.2⟩)).differentiable (by norm_num))
          ((h₂.c2 _ (hmemI τ ⟨hτ.1.le, hτ.2⟩)).differentiable (by norm_num)), inner_sub_right]
      ring
    rw [e]
    exact hd.hasDerivWithinAt
  have h0 : ∀ z, G 0 z ≤ 0 := by
    intro z
    simp [hG, h₁.terminal, h₂.terminal]
  have hgrow : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ t' ∈ Icc 0 T, ∀ z, G t' z ≤ C + δ * ‖z‖ ^ 2 := by
    obtain ⟨B₁, hB₁⟩ := h₁.bdd
    obtain ⟨B₂, hB₂⟩ := h₂.bdd
    intro δ hδ
    refine ⟨B₁ + B₂, fun t' ht' z => ?_⟩
    have h1 := hB₁ _ (hmemI t' ht') z
    have h2 := hB₂ _ (hmemI t' ht') z
    have h3 := le_abs_self (u₁ (t - t') z)
    have h4 := neg_abs_le (u₂ (t - t') z)
    have h5 : 0 ≤ δ * ‖z‖ ^ 2 := by positivity
    simp only [hG]
    linarith
  have hfail : ∃ lam : ℝ, ∀ ε : ℝ, 0 < ε → ∀ τ ∈ Ioc 0 T, ∀ z,
      0 < G τ z - ε * (1 + ‖z‖ ^ 2) * Real.exp (lam * τ) →
      (∀ z', G τ z' - ε * (1 + ‖z'‖ ^ 2) * Real.exp (lam * τ) ≤
        G τ z - ε * (1 + ‖z‖ ^ 2) * Real.exp (lam * τ)) →
      Gt τ z < ε * lam * (1 + ‖z‖ ^ 2) * Real.exp (lam * τ) := by
    refine ⟨lam, fun ε hε τ hτ z _ hmax => ?_⟩
    have hτI : τ ∈ Icc 0 T := ⟨hτ.1.le, hτ.2⟩
    have hrI : t - τ ∈ Icc 0 t := hmemI τ hτI
    set κ : ℝ := ε * Real.exp (lam * τ) with hκ
    have hκpos : 0 < κ := by positivity
    have hC1 := h₁.c2 _ hrI
    have hC2 := h₂.c2 _ hrI
    have ha : ContDiff ℝ 2 (fun y => u₁ (t - τ) y - u₂ (t - τ) y) := hC1.sub hC2
    have hmax' : ∀ z', (fun y => u₁ (t - τ) y - u₂ (t - τ) y) z' - κ * (1 + ‖z'‖ ^ 2) ≤
        (fun y => u₁ (t - τ) y - u₂ (t - τ) y) z - κ * (1 + ‖z‖ ^ 2) := by
      intro z'
      have h := hmax z'
      simp only [hG] at h
      have e1 : ε * (1 + ‖z'‖ ^ 2) * Real.exp (lam * τ) = κ * (1 + ‖z'‖ ^ 2) := by rw [hκ]; ring
      have e2 : ε * (1 + ‖z‖ ^ 2) * Real.exp (lam * τ) = κ * (1 + ‖z‖ ^ 2) := by rw [hκ]; ring
      simp only
      linarith
    obtain ⟨hgrad, hlap⟩ := lu_max_point ha hmax'
    have hνr := hν _ hrI
    have hbnorm : ‖-(Torus.matVec Q z) - c (t - τ) + B (t - τ) z‖ ≤ K * ‖z‖ + Λc + ΛB := by
      calc ‖-(Torus.matVec Q z) - c (t - τ) + B (t - τ) z‖
          ≤ ‖-(Torus.matVec Q z) - c (t - τ)‖ + ‖B (t - τ) z‖ := norm_add_le _ _
        _ ≤ (‖-(Torus.matVec Q z)‖ + ‖c (t - τ)‖) + ‖B (t - τ) z‖ := by
            gcongr; exact norm_sub_le _ _
        _ ≤ (K * ‖z‖ + Λc) + ΛB := by
            rw [norm_neg]
            gcongr
            · exact hKb z
            · exact hc _ hrI
            · exact hB _ hrI z
        _ = _ := by ring
    have hin : inner ℝ (-(Torus.matVec Q z) - c (t - τ) + B (t - τ) z) ((2 * κ) • z) ≤
        2 * κ * ((K * ‖z‖ + Λc + ΛB) * ‖z‖) := by
      rw [real_inner_smul_right]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hbnorm (norm_nonneg _))
    have hdd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have h1 : ν (t - τ) * Laplacian.laplacian (fun y => u₁ (t - τ) y - u₂ (t - τ) y) z ≤
        νstar * (2 * κ * d) := by
      calc _ ≤ ν (t - τ) * (2 * κ * d) := mul_le_mul_of_nonneg_left hlap hνr.1
        _ ≤ _ := mul_le_mul_of_nonneg_right hνr.2 (by positivity)
    have hGt_le : Gt τ z ≤ νstar * (2 * κ * d) + 2 * κ * ((K * ‖z‖ + Λc + ΛB) * ‖z‖) := by
      simp only [hGt]
      rw [hgrad]
      linarith
    have hK0 : 0 ≤ K := norm_nonneg _
    have hkey : νstar * (2 * d) + 2 * ((K * ‖z‖ + Λc + ΛB) * ‖z‖) < lam * (1 + ‖z‖ ^ 2) := by
      have hn := norm_nonneg z
      have hdν : 0 ≤ (d : ℝ) * νstar := mul_nonneg hdd hνs
      have hsq : 0 ≤ ‖z‖ ^ 2 := sq_nonneg _
      have hΛ : 2 * (Λc + ΛB) * ‖z‖ ≤ (Λc + ΛB) * (1 + ‖z‖ ^ 2) := by
        nlinarith [sq_nonneg (‖z‖ - 1), add_nonneg hΛc hΛB]
      rw [hlam]
      nlinarith [mul_nonneg hdν hsq, mul_nonneg hK0 hsq]
    have := mul_lt_mul_of_pos_left hkey hκpos
    calc Gt τ z ≤ _ := hGt_le
      _ = κ * (νstar * (2 * d) + 2 * ((K * ‖z‖ + Λc + ΛB) * ‖z‖)) := by ring
      _ < κ * (lam * (1 + ‖z‖ ^ 2)) := this
      _ = _ := by rw [hκ]; ring
  have key := lu_penalized_max_Ioc (E := Euc d) G Gt T hcont hder h0 hgrow hfail T
    ⟨hT0, le_rfl⟩ x
  have e : t - T = r := by rw [hT]; ring
  simp only [hG, e] at key
  linarith

/-- **LC-U.**  Two bounded classical backward solutions with the same terminal datum and the same
drift `b r x = -(Qx) - c r + B r x` coincide on `[0,t] × ℝ^d`. -/
theorem lc_unique {Q : Matrix (Fin d) (Fin d) ℝ} {c : ℝ → Euc d} {B : ℝ → Euc d → Euc d}
    {ν : ℝ → ℝ} {νstar Λc ΛB t : ℝ} {f : Euc d → ℝ} {u₁ u₂ : ℝ → Euc d → ℝ}
    (ht : 0 ≤ t) (hν : ∀ r ∈ Icc 0 t, 0 ≤ ν r ∧ ν r ≤ νstar)
    (hc : ∀ r ∈ Icc 0 t, ‖c r‖ ≤ Λc) (hB : ∀ r ∈ Icc 0 t, ∀ x, ‖B r x‖ ≤ ΛB)
    (h₁ : IsLocalBackwardSolution ν (fun r x => -(Torus.matVec Q x) - c r + B r x) t f u₁)
    (h₂ : IsLocalBackwardSolution ν (fun r x => -(Torus.matVec Q x) - c r + B r x) t f u₂) :
    ∀ r ∈ Icc 0 t, ∀ x, u₁ r x = u₂ r x := by
  intro r hr x
  rcases hr.2.eq_or_lt with hrt | hrt
  · rw [hrt, h₁.terminal, h₂.terminal]
  have ht' : 0 < t := lt_of_le_of_lt hr.1 hrt
  have hpos : ∀ r ∈ Ioc 0 t, u₁ r x = u₂ r x := fun r hr =>
    le_antisymm (lu_one_sided ht' hν hc hB h₁ h₂ r hr x) (lu_one_sided ht' hν hc hB h₂ h₁ r hr x)
  rcases hr.1.eq_or_lt with h0 | h0
  · subst h0
    set g : ℝ → ℝ := fun r => u₁ r x - u₂ r x with hg
    have hcol : ∀ u : ℝ → Euc d → ℝ, (Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => u p.1 p.2) →
        ContinuousOn (fun r => u r x) (Icc 0 t) := fun u hu =>
      (lu_contOn hu).comp (continuous_id.prodMk continuous_const).continuousOn
        (fun r hr => ⟨hr, mem_univ _⟩)
    have hgc : ContinuousOn g (Icc 0 t) := (hcol _ h₁.cont).sub (hcol _ h₂.cont)
    have hcw : ContinuousWithinAt g (Ioc 0 t) 0 :=
      (hgc 0 ⟨le_rfl, ht⟩).mono Ioc_subset_Icc_self
    have hne : (𝓝[Ioc 0 t] (0 : ℝ)).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioc ht'.ne]
      exact ⟨le_rfl, ht⟩
    have hlim : Tendsto g (𝓝[Ioc 0 t] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun r hr => by
        simp only [hg, hpos r hr, sub_self])
    have := tendsto_nhds_unique hcw.tendsto hlim
    simpa [hg, sub_eq_zero] using this
  · exact hpos r ⟨h0, hr.2⟩

/-- Corollary: if a solution exists, every solution equals the chosen one. -/
theorem lc_unique_of_exists {Q : Matrix (Fin d) (Fin d) ℝ} {c : ℝ → Euc d} {B : ℝ → Euc d → Euc d}
    {ν : ℝ → ℝ} {νstar Λc ΛB t : ℝ} {f : Euc d → ℝ}
    (ht : 0 ≤ t) (hν : ∀ r ∈ Icc 0 t, 0 ≤ ν r ∧ ν r ≤ νstar)
    (hc : ∀ r ∈ Icc 0 t, ‖c r‖ ≤ Λc) (hB : ∀ r ∈ Icc 0 t, ∀ x, ‖B r x‖ ≤ ΛB)
    (hex : ∃ u, IsLocalBackwardSolution ν (fun r x => -(Torus.matVec Q x) - c r + B r x) t f u)
    {u' : ℝ → Euc d → ℝ}
    (hu' : IsLocalBackwardSolution ν (fun r x => -(Torus.matVec Q x) - c r + B r x) t f u') :
    ∀ r ∈ Icc 0 t, ∀ x, u' r x = hex.choose r x :=
  lc_unique ht hν hc hB hu' hex.choose_spec

end HRS.MS.Lc
