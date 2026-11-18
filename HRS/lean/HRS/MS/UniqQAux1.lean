import HRS.MS.LcUniqAux2
import HRS.MS.UlOu

/-!
# UNIQ-Q (supporting packet of the frozen row S5.2 `orbit_feature_bounded`), part 1: PLAN and the maximum principle with a source

**Goal.**  `S52bUniq (fixedViscosityCoeff s (-1) Q ν c ρ) T` (`OrbFeatAux2`): two classical adjoint solutions
(`IsClassicalAdjointW`, i.e. `C_b²` in `x`, `∂_r f` of linear growth) with the same terminal datum agree, for
`d ≥ 2`, `0 ≤ s < d`, `ν > 0`, `ρ` Schwartz, `c` bounded, `Q` an arbitrary matrix (the drift `-Qx + c` is not of
gradient form, so `Fcau.propagatorW_eq` / `uloc_uniqueness` (S.A.33) cannot be instantiated: their engine is
written for `meanFieldDriftW D`).  Then `orbit_feature_bounded_proof` (`UniqQTie`) via `orbit_feature_bounded_of_uniq`.

**Route (checked against the library; cheaper than the classical-to-mild Duhamel identity).**  The difference
`u = f₁ - f₂` is a bounded `C_b²` classical solution with `u(t) = 0` of
`-∂_r u = L₀ u + S`, `L₀ = νΔ - ⟨Qx, ∇·⟩` (the OU generator, semigroup `ouSg`), `S = ⟨c,∇u⟩ - N(∇u)`
(`N` = the nonlocal term `ulNL`), `S` bounded.
1. (`UniqQAux1`) *Maximum principle with a source* (a port of `lu_one_sided`, `HRS/MS/LcUniqAux2`, with the
   penalised maximum `lu_penalized_max_Ioc`): `|u(a) - P_{b-a} u(b)| ≤ (b-a) sup|S|` on any `[a,b] ⊆ [0,t]`.
   No mild formula, no Kolmogorov equation for the pair `(τ,σ)`, no generator limit is needed.
2. (`UniqQAux2..3`) *Gaussian smoothing with sup-norm data*: for `g ∈ C¹` with bounded gradient and `|g| ≤ B`
   (the gradient bound does not enter the constants) `|P_τ g(x) - P_τ g(x')| ≤ C τ^{-1/2} B |x-x'|` (Stein, via
   `ul3_avg_deriv`/`ul3_S_preimage`), `P_τ` preserves the class, translation identity, second differences
   `|Δ_aΔ_e P_τ g| ≤ C B τ^{-(1+β)/2}|a|^β|e|`.
3. (`UniqQAux4`) *Discrete Duhamel*: on a window `[r,t₁]`, `u(t₁) = 0`, `|S| ≤ m`, partition `t_i = r + ih`,
   `E_i = u(t_i) - P_h u(t_{i+1})`, `|E_i| ≤ hm` (step 1), exactly `u(r) = ∑_i P_{ih} E_i` (semigroup law),
   so `|∇u(r)| ≤ C m ℓ^{1/2}` and `[∇u(r)]_β ≤ C m ℓ^{(1-β)/2}`, `ℓ = t₁ - r` (`∑_{i<n} i^{-γ} ≤ n^{1-γ}/(1-γ)`,
   `n → ∞`).
4. (`UniqQAux5`) *The nonlocal term*: `|N(∇u)(x)| ≤ K (‖∇u‖_∞ + [∇u]_β)` for `β > s + 1 - d`, `β < 1`
   (cancellation integral, `kap_bound`, `ballF_integrable`, far part against `‖ρ‖_{L¹}`); linearity of `ulNL`.
5. (`UniqQAux6`) *Closing*: `|S| ≤ m` on a window of length `δ` ⇒ `|S| ≤ m/2` ⇒ `S = 0` ⇒ `u = 0` on the window
   (step 1 with `M = 0`); propagate window by window from `t` down to `0`.
6. (`UniqQTie`) `S52bUniq` for the frozen coefficient and `orbit_feature_bounded_proof`.

Size estimate 2.5k-3.5k lines (stop rule 4.5k).  Helper names carry the prefix `uniqq_`; namespace `HRS.MS.UniqQ`.

**This file**: `uniqq_mp_pos`/`uniqq_mp`, the maximum principle for a sub-solution of
`-∂_r w ≤ ν Δw + ⟨-Qx,∇w⟩ + M`, `w(b) ≤ 0`: `w(r) ≤ (b-r) M`.
-/

noncomputable section

open Filter Topology Set
open scoped RealInnerProductSpace

namespace HRS.MS.UniqQ

open HRS HRS.Whole HRS.MS.Lc HRS.MS.Ul

variable {d : ℕ}

/-- the maximum principle with a source, for `r ∈ (a,b]` -/
theorem uniqq_mp_pos {Q : Matrix (Fin d) (Fin d) ℝ} {ν M a b : ℝ} (hν : 0 ≤ ν)
    {w Dt : ℝ → Euc d → ℝ}
    (hc2 : ∀ r ∈ Icc a b, ContDiff ℝ 2 (w r))
    (hbd : ∃ B, ∀ r ∈ Icc a b, ∀ x, |w r x| ≤ B)
    (hcont : ContinuousOn (fun p : ℝ × Euc d => w p.1 p.2) (Icc a b ×ˢ univ))
    (hterm : ∀ x, w b x ≤ 0)
    (hder : ∀ x, ∀ r ∈ Ioo a b, HasDerivAt (fun r' => w r' x) (Dt r x) r)
    (hineq : ∀ x, ∀ r ∈ Ioo a b, -Dt r x ≤ ν * Laplacian.laplacian (w r) x +
        inner ℝ (-(Torus.matVec Q x)) (gradient (w r) x) + M)
    {r : ℝ} (hr : r ∈ Ioc a b) (x : Euc d) : w r x ≤ (b - r) * M := by
  set T : ℝ := b - r with hT
  have hT0 : 0 ≤ T := by linarith [hr.2]
  set K : ℝ := ‖(Matrix.toEuclideanLin Q).toContinuousLinearMap‖ with hK
  have hKb : ∀ z : Euc d, ‖Torus.matVec Q z‖ ≤ K * ‖z‖ := fun z =>
    ((Matrix.toEuclideanLin Q).toContinuousLinearMap).le_opNorm z
  have hK0 : 0 ≤ K := norm_nonneg _
  set lam : ℝ := 2 * d * ν + 2 * K + 1 with hlam
  set G : ℝ → Euc d → ℝ := fun τ z => w (b - τ) z - τ * M with hG
  set Gt : ℝ → Euc d → ℝ := fun τ z => -Dt (b - τ) z - M with hGt
  have hmem : ∀ τ ∈ Icc 0 T, b - τ ∈ Icc a b := fun τ hτ =>
    ⟨by linarith [hτ.2, hr.1], by linarith [hτ.1]⟩
  have hcontG : ContinuousOn (fun p : ℝ × Euc d => G p.1 p.2) (Icc 0 T ×ˢ univ) := by
    have hφ : Continuous fun p : ℝ × Euc d => ((b - p.1, p.2) : ℝ × Euc d) :=
      (continuous_const.sub continuous_fst).prodMk continuous_snd
    have h1 : ContinuousOn (fun p : ℝ × Euc d => w (b - p.1) p.2) (Icc 0 T ×ˢ univ) :=
      hcont.comp hφ.continuousOn (fun p hp => ⟨hmem _ hp.1, mem_univ _⟩)
    exact h1.sub ((continuous_fst.mul continuous_const).continuousOn)
  have hderG : ∀ τ ∈ Ioc 0 T, ∀ z, HasDerivWithinAt (fun s => G s z) (Gt τ z) (Icc 0 T) τ := by
    intro τ hτ z
    have hr' : b - τ ∈ Ioo a b := ⟨by linarith [hτ.2, hr.1], by linarith [hτ.1]⟩
    have hneg : HasDerivAt (fun x : ℝ => b - x) (-1) τ := by
      simpa using (hasDerivAt_id τ).const_sub b
    have d1 := (hder z (b - τ) hr').comp τ hneg
    have d2 : HasDerivAt (fun s : ℝ => s * M) M τ := by
      simpa using (hasDerivAt_id τ).mul_const M
    have hd := d1.sub d2
    refine (hd.congr_deriv ?_).hasDerivWithinAt
    simp only [hGt]
    ring
  have h0 : ∀ z, G 0 z ≤ 0 := by
    intro z
    simp [hG, hterm]
  have hgrow : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ t' ∈ Icc 0 T, ∀ z, G t' z ≤ C + δ * ‖z‖ ^ 2 := by
    obtain ⟨B, hB⟩ := hbd
    intro δ hδ
    refine ⟨B + T * |M|, fun t' ht' z => ?_⟩
    have h1 := hB _ (hmem t' ht') z
    have h2 := le_abs_self (w (b - t') z)
    have h3 : -(t' * M) ≤ T * |M| := by
      calc -(t' * M) ≤ |t' * M| := neg_le_abs _
        _ = t' * |M| := by rw [abs_mul, abs_of_nonneg ht'.1]
        _ ≤ T * |M| := mul_le_mul_of_nonneg_right ht'.2 (abs_nonneg _)
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
    have hr' : b - τ ∈ Ioo a b := ⟨by linarith [hτ.2, hr.1], by linarith [hτ.1]⟩
    set κ : ℝ := ε * Real.exp (lam * τ) with hκ
    have hκpos : 0 < κ := by positivity
    have ha : ContDiff ℝ 2 (w (b - τ)) := hc2 _ (hmem τ hτI)
    have hmax' : ∀ z', w (b - τ) z' - κ * (1 + ‖z'‖ ^ 2) ≤ w (b - τ) z - κ * (1 + ‖z‖ ^ 2) := by
      intro z'
      have h := hmax z'
      simp only [hG] at h
      have e1 : ε * (1 + ‖z'‖ ^ 2) * Real.exp (lam * τ) = κ * (1 + ‖z'‖ ^ 2) := by rw [hκ]; ring
      have e2 : ε * (1 + ‖z‖ ^ 2) * Real.exp (lam * τ) = κ * (1 + ‖z‖ ^ 2) := by rw [hκ]; ring
      linarith
    obtain ⟨hgrad, hlap⟩ := lu_max_point ha hmax'
    have hin := hineq z (b - τ) hr'
    have hdd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have h1 : ν * Laplacian.laplacian (w (b - τ)) z ≤ ν * (2 * κ * d) :=
      mul_le_mul_of_nonneg_left hlap hν
    have h2 : inner ℝ (-(Torus.matVec Q z)) (gradient (w (b - τ)) z) ≤ 2 * κ * (K * ‖z‖ ^ 2) := by
      rw [hgrad, real_inner_smul_right]
      have h3 : inner ℝ (-(Torus.matVec Q z)) z ≤ K * ‖z‖ ^ 2 := by
        refine (real_inner_le_norm _ _).trans ?_
        rw [norm_neg]
        calc ‖Torus.matVec Q z‖ * ‖z‖ ≤ (K * ‖z‖) * ‖z‖ :=
              mul_le_mul_of_nonneg_right (hKb z) (norm_nonneg _)
          _ = K * ‖z‖ ^ 2 := by ring
      exact mul_le_mul_of_nonneg_left h3 (by positivity)
    have hGt_le : Gt τ z ≤ ν * (2 * κ * d) + 2 * κ * (K * ‖z‖ ^ 2) := by
      simp only [hGt]
      linarith
    have hkey : ν * (2 * d) + 2 * (K * ‖z‖ ^ 2) < lam * (1 + ‖z‖ ^ 2) := by
      have hn := sq_nonneg ‖z‖
      have hdν : 0 ≤ (d : ℝ) * ν := mul_nonneg hdd hν
      rw [hlam]
      nlinarith [mul_nonneg hdν hn, mul_nonneg hK0 hn]
    have := mul_lt_mul_of_pos_left hkey hκpos
    calc Gt τ z ≤ _ := hGt_le
      _ = κ * (ν * (2 * d) + 2 * (K * ‖z‖ ^ 2)) := by ring
      _ < κ * (lam * (1 + ‖z‖ ^ 2)) := this
      _ = _ := by rw [hκ]; ring
  have key := lu_penalized_max_Ioc (E := Euc d) G Gt T hcontG hderG h0 hgrow hfail T
    ⟨hT0, le_rfl⟩ x
  have e : b - T = r := by rw [hT]; ring
  simp only [hG, e] at key
  linarith

/-- the maximum principle with a source, on the closed interval (continuity at the left endpoint) -/
theorem uniqq_mp {Q : Matrix (Fin d) (Fin d) ℝ} {ν M a b : ℝ} (hν : 0 ≤ ν)
    {w Dt : ℝ → Euc d → ℝ}
    (hc2 : ∀ r ∈ Icc a b, ContDiff ℝ 2 (w r))
    (hbd : ∃ B, ∀ r ∈ Icc a b, ∀ x, |w r x| ≤ B)
    (hcont : ContinuousOn (fun p : ℝ × Euc d => w p.1 p.2) (Icc a b ×ˢ univ))
    (hterm : ∀ x, w b x ≤ 0)
    (hder : ∀ x, ∀ r ∈ Ioo a b, HasDerivAt (fun r' => w r' x) (Dt r x) r)
    (hineq : ∀ x, ∀ r ∈ Ioo a b, -Dt r x ≤ ν * Laplacian.laplacian (w r) x +
        inner ℝ (-(Torus.matVec Q x)) (gradient (w r) x) + M)
    {r : ℝ} (hr : r ∈ Icc a b) (x : Euc d) : w r x ≤ (b - r) * M := by
  rcases hr.1.eq_or_lt with h0 | h0
  · subst h0
    rcases hr.2.eq_or_lt with hab | hab
    · subst hab
      simpa using hterm x
    · -- continuity at the left endpoint
      have hcol : ContinuousOn (fun r' => w r' x) (Icc a b) :=
        (hcont.comp (continuous_id.prodMk continuous_const).continuousOn
          (fun r' hr' => ⟨hr', mem_univ _⟩))
      have hcw : ContinuousWithinAt (fun r' => w r' x) (Ioc a b) a :=
        (hcol a ⟨le_rfl, hab.le⟩).mono Ioc_subset_Icc_self
      have hne : (𝓝[Ioc a b] a).NeBot := by
        rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioc hab.ne]
        exact ⟨le_rfl, hab.le⟩
      have hle : ∀ r' ∈ Ioc a b, w r' x ≤ (b - r') * M := fun r' hr' =>
        uniqq_mp_pos hν hc2 hbd hcont hterm hder hineq hr' x
      have hcw2 : ContinuousWithinAt (fun r' => (b - r') * M) (Ioc a b) a :=
        ((continuous_const.sub continuous_id).mul continuous_const).continuousWithinAt
      exact le_of_tendsto_of_tendsto hcw.tendsto hcw2.tendsto
        (eventually_nhdsWithin_of_forall hle)
  · exact uniqq_mp_pos hν hc2 hbd hcont hterm hder hineq ⟨h0, hr.2⟩ x

end HRS.MS.UniqQ
