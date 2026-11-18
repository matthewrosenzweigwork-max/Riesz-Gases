import HRS.Uniform.Q14Aux6
import HRS.Uniform.RelativeCov

/-!
# Q48c: the Fourier-feature covariance estimate (infrastructure for Lemma 3.31 `stationary_noise`)

**Statement proved** (`HRS.Uniform.Q48c.bures2_cov_estimate`).  For `β > 0`, `ρβ : Torus d → ℝ` smooth with `ρβ > 0`
(two of the hypotheses of `stationary_noise`), there is `m₀` (namely `d + 3`) such that for all `m ≥ m₀` and `Cv`
there is `C ≥ 0` with: for every probability space `(Ω, P)`, `N ≥ 1`, `δ`, random configuration `X : Ω → Config d N`
and probability `Q` on `Config d N` with `P.map X = Q`, one-body density `g` (`Measurable g`,
`(N : ℝ≥0∞)⁻¹ • ∑ i, Q.map (fun x => x i) = (withDensityReal ρβ).withDensity (ofReal ∘ g)`,
`∫⁻ ‖g - 1‖ₑ ^ 2 ∂(withDensityReal ρβ) ≤ ofReal ((Cv * δ) ^ 2)`) and the evariance hypothesis
(`∀ f measurable, MemLp f 2 (withDensityReal ρβ) → evariance (fun x => pair (empirical x) f) Q ≤
ofReal (Cv * N⁻¹ * ∫ f ^ 2 ∂(withDensityReal ρβ))`), exactly as in `stationary_noise`:

`∫⁻ ω, ofReal (bures2 (covForm m β⁻¹ (empirical (X ω))) (covForm m β⁻¹ (withDensityReal ρβ))) ∂P ≤
  ofReal (C * (N⁻¹ + δ ^ 2))`

(for `stationary_noise` apply it with `X := X r`, `r ≥ 0`; `X r` is automatically a.e. measurable, see
`aemeasurable_of_marginal`).  Route: Lemma 3.29 comparison form `RelCov.bures2_le` with the basis of `E_m`, the
reference `D₀ = covForm m q vol` (diagonal in the standard basis, eigenvalues `dd0`), `D ≥ c D₀` from
`ρβ ≥ c > 0`; the entries `(C_N - D)_{kl} = 2q w_k w_l (μ_N(F_{kl}) - μ(F_{kl}))`, `F_{kl} = ∇e_k·∇e_l`,
`|F_{kl}| ≤ 2d jp_k jp_l` (estimate (i): `E |(C_N-D)_{kl}|² ≤ C d_k d_l (N⁻¹+δ²)`, `d_k = jp_k^{2-2m}`),
and the summation (ii) `∑_{kl} d_k d_l/(d_k+d_l) ≤ (∑_k d_k^{1/2})² < ∞` (`m > d + 1`; AM-GM instead of the
rank-ordered `2∑ j d_j`).
-/

noncomputable section

open HRS HRS.Uniform HRS.Uniform.Q14
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q48c

section Basis

variable {d : ℕ} {m : ℝ}

/-- The identity isometry `E_m ≃ ℓ²`. -/
def negRepr (d : ℕ) (m : ℝ) : NegSobolev d m ≃ₗᵢ[ℝ] lp (fun _ : NonzeroLattice d => ℝ) 2 where
  toFun := id
  invFun := id
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  norm_map' := fun _ => rfl

/-- The standard Hilbert basis of `E_m`. -/
def basis (d : ℕ) (m : ℝ) : HilbertBasis (NonzeroLattice d) ℝ (NegSobolev d m) :=
  HilbertBasis.ofRepr (negRepr d m)

lemma inner_basis (k : NonzeroLattice d) (x : NegSobolev d m) :
    inner ℝ (basis d m k : NegSobolev d m) x = NegSobolev.coord x k := by
  have := HilbertBasis.repr_apply_apply (basis d m) x k
  rw [← this]; rfl

/-- the weight `⟨k⟩^{-m}`. -/
def wt (m : ℝ) (k : NonzeroLattice d) : ℝ := Lattice.jp k.1 ^ (-m)

lemma wt_pos (k : NonzeroLattice d) : 0 < wt m k := Real.rpow_pos_of_pos (Torus.jp_pos k.1) _

/-- `F_{kl} = ∑_j ∂_j e_k ∂_j e_l`. -/
def Fkl (k l : NonzeroLattice d) (u : Torus d) : ℝ :=
  ∑ j : Fin d, Torus.partialDeriv j (Torus.realMode k) u * Torus.partialDeriv j (Torus.realMode l) u

open Classical in
lemma continuous_partialDeriv_realMode (j : Fin d) (k : NonzeroLattice d) :
    Continuous (Torus.partialDeriv j (Torus.realMode k)) := by
  have : Torus.partialDeriv j (Torus.realMode k) = fun x =>
      2 * Real.pi * (k.1 j : ℝ) * Real.sqrt 2 *
        (if Lattice.IsPosHalf k.1 then -Torus.sinMode k.1 x else Torus.cosMode k.1 x) := by
    funext x; exact q14_partialDeriv_realMode j k x
  rw [this]
  by_cases hp : Lattice.IsPosHalf k.1
  · simp only [hp, if_true]
    exact continuous_const.mul (Torus.continuous_sinMode k.1).neg
  · simp only [hp, if_false]
    exact continuous_const.mul (Torus.continuous_cosMode k.1)

lemma continuous_Fkl (k l : NonzeroLattice d) : Continuous (Fkl k l) := by
  unfold Fkl
  exact continuous_finset_sum _ fun j _ =>
    (continuous_partialDeriv_realMode j k).mul (continuous_partialDeriv_realMode j l)

lemma abs_Fkl_le (k l : NonzeroLattice d) (u : Torus d) :
    |Fkl k l u| ≤ 2 * d * (Lattice.jp k.1 * Lattice.jp l.1) := by
  unfold Fkl
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j : Fin d, |Torus.partialDeriv j (Torus.realMode k) u * Torus.partialDeriv j (Torus.realMode l) u|
      ≤ ∑ _j : Fin d, 2 * (Lattice.jp k.1 * Lattice.jp l.1) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        have h1 := q14_coef_bound j k u
        have h2 := q14_coef_bound j l u
        calc _ ≤ (Real.sqrt 2 * Lattice.jp k.1) * (Real.sqrt 2 * Lattice.jp l.1) :=
              mul_le_mul h1 h2 (abs_nonneg _) (by have := Torus.jp_pos k.1; positivity)
          _ = 2 * (Lattice.jp k.1 * Lattice.jp l.1) := by
              have : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
              calc _ = (Real.sqrt 2 * Real.sqrt 2) * (Lattice.jp k.1 * Lattice.jp l.1) := by ring
                _ = _ := by rw [this]
    _ = 2 * d * (Lattice.jp k.1 * Lattice.jp l.1) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

lemma integrable_Fkl (k l : NonzeroLattice d) (μ : Measure (Torus d)) [IsFiniteMeasure μ] :
    Integrable (Fkl k l) μ :=
  (continuous_Fkl k l).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma covForm_basis (hm : (d : ℝ) / 2 + 2 < m) {q : ℝ} (hq : 0 ≤ q) (μ : Measure (Torus d))
    [IsFiniteMeasure μ] (k l : NonzeroLattice d) :
    covForm m q μ (basis d m k) (basis d m l) =
      2 * q * (wt m k * wt m l) * ∫ u, Fkl k l u ∂μ := by
  rw [q14_covForm_apply hm hq μ]
  have hc : Real.sqrt (2 * q) * Real.sqrt (2 * q) = 2 * q := Real.mul_self_sqrt (by positivity)
  have hj : ∀ j : Fin d, ∫ a, inner ℝ (Real.sqrt (2 * q) • bVec m j a) (basis d m k : NegSobolev d m) *
      inner ℝ (Real.sqrt (2 * q) • bVec m j a) (basis d m l : NegSobolev d m) ∂μ =
      2 * q * (wt m k * wt m l) * ∫ a, Torus.partialDeriv j (Torus.realMode k) a *
        Torus.partialDeriv j (Torus.realMode l) a ∂μ := by
    intro j
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only [inner_smul_left, conj_trivial]
    rw [real_inner_comm (basis d m k : NegSobolev d m), real_inner_comm (basis d m l : NegSobolev d m),
      inner_basis, inner_basis, q14_coord_bVec (by linarith) j a k, q14_coord_bVec (by linarith) j a l]
    unfold wt
    calc Real.sqrt (2 * q) * (Lattice.jp k.1 ^ (-m) * Torus.partialDeriv j (Torus.realMode k) a) *
          (Real.sqrt (2 * q) * (Lattice.jp l.1 ^ (-m) * Torus.partialDeriv j (Torus.realMode l) a))
        = (Real.sqrt (2 * q) * Real.sqrt (2 * q)) * (Lattice.jp k.1 ^ (-m) * Lattice.jp l.1 ^ (-m)) *
            (Torus.partialDeriv j (Torus.realMode k) a * Torus.partialDeriv j (Torus.realMode l) a) := by
          ring
      _ = _ := by rw [hc]
  simp_rw [hj]
  rw [← Finset.mul_sum]
  unfold Fkl
  congr 1
  rw [integral_finset_sum]
  intro j _
  exact ((continuous_partialDeriv_realMode j k).mul
    (continuous_partialDeriv_realMode j l)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

end Basis

section Diag

variable {d : ℕ} {m : ℝ}

open Classical in
/-- `∂_j e_k = 2π k_j e_{-k}`. -/
lemma partialDeriv_realMode_eq (j : Fin d) (k : NonzeroLattice d) (x : Torus d) :
    Torus.partialDeriv j (Torus.realMode k) x =
      2 * Real.pi * (k.1 j : ℝ) * Torus.realMode ⟨-k.1, neg_ne_zero.2 k.2⟩ x := by
  rw [q14_partialDeriv_realMode]
  unfold Torus.realMode
  by_cases hp : Lattice.IsPosHalf k.1
  · have hn : ¬ Lattice.IsPosHalf (-k.1) := fun h => ((Torus.isPosHalf_neg k.1 k.2).1 h) hp
    simp only [hp, hn, if_true, if_false, Torus.sinMode_neg]
    ring
  · have hn : Lattice.IsPosHalf (-k.1) := (Torus.isPosHalf_neg k.1 k.2).2 hp
    simp only [hp, hn, if_true, if_false, Torus.cosMode_neg]
    ring

lemma enorm_sq_eq (k : Lattice d) : Lattice.enorm k ^ 2 = ∑ j, (k j : ℝ) ^ 2 := by
  unfold Lattice.enorm
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

lemma one_le_enorm_sq (k : NonzeroLattice d) : 1 ≤ Lattice.enorm k.1 ^ 2 := by
  rw [enorm_sq_eq]
  have : ∃ j, k.1 j ≠ 0 := by
    by_contra h
    push_neg at h
    exact k.2 (funext h)
  obtain ⟨j, hj⟩ := this
  have h1 : (1 : ℝ) ≤ (k.1 j : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ (k.1 j) ^ 2 := by
      have := Int.one_le_abs hj
      nlinarith [sq_abs (k.1 j)]
    exact_mod_cast this
  exact h1.trans (Finset.single_le_sum (f := fun j => (k.1 j : ℝ) ^ 2) (fun i _ => sq_nonneg _)
    (Finset.mem_univ j))

lemma integral_Fkl_volume (k l : NonzeroLattice d) :
    ∫ u, Fkl k l u = if k = l then 4 * Real.pi ^ 2 * Lattice.enorm k.1 ^ 2 else 0 := by
  unfold Fkl
  rw [integral_finset_sum]
  swap
  · intro j _
    exact ((continuous_partialDeriv_realMode j k).mul
      (continuous_partialDeriv_realMode j l)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hj : ∀ j : Fin d, ∫ u : Torus d, Torus.partialDeriv j (Torus.realMode k) u *
      Torus.partialDeriv j (Torus.realMode l) u =
      (2 * Real.pi * (k.1 j : ℝ)) * (2 * Real.pi * (l.1 j : ℝ)) * (if k = l then 1 else 0) := by
    intro j
    have : ∀ u : Torus d, Torus.partialDeriv j (Torus.realMode k) u *
        Torus.partialDeriv j (Torus.realMode l) u =
        (2 * Real.pi * (k.1 j : ℝ)) * (2 * Real.pi * (l.1 j : ℝ)) *
          (Torus.realMode ⟨-k.1, neg_ne_zero.2 k.2⟩ u * Torus.realMode ⟨-l.1, neg_ne_zero.2 l.2⟩ u) := by
      intro u
      rw [partialDeriv_realMode_eq j k u, partialDeriv_realMode_eq j l u]; ring
    simp_rw [this]
    rw [integral_const_mul, Torus.realMode_orthonormal]
    congr 2
    by_cases h : k = l
    · simp [h]
    · have : (⟨-k.1, neg_ne_zero.2 k.2⟩ : NonzeroLattice d) ≠ ⟨-l.1, neg_ne_zero.2 l.2⟩ := by
        intro h'
        apply h
        apply Subtype.ext
        have := congrArg Subtype.val h'
        simpa using this
      simp [h, this]
  simp_rw [hj]
  by_cases h : k = l
  · subst h
    simp only [if_true, mul_one]
    rw [enorm_sq_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  · simp [h]

/-- the eigenvalues of `D₀ = covForm m q vol`. -/
def dd0 (m q : ℝ) (k : NonzeroLattice d) : ℝ :=
  2 * q * (wt m k * wt m k) * (4 * Real.pi ^ 2 * Lattice.enorm k.1 ^ 2)

lemma covForm_volume_basis (hm : (d : ℝ) / 2 + 2 < m) {q : ℝ} (hq : 0 ≤ q) (k l : NonzeroLattice d) :
    covForm m q (volume : Measure (Torus d)) (basis d m k) (basis d m l) =
      if k = l then dd0 m q k else 0 := by
  rw [covForm_basis hm hq, integral_Fkl_volume]
  by_cases h : k = l
  · subst h; simp [dd0]
  · simp [h]

lemma covForm_volume_diag (hm : (d : ℝ) / 2 + 2 < m) {q : ℝ} (hq : 0 ≤ q) (k : NonzeroLattice d)
    (y : NegSobolev d m) :
    covForm m q (volume : Measure (Torus d)) (basis d m k) y =
      dd0 m q k * inner ℝ (basis d m k : NegSobolev d m) y := by
  have h := RelCov.hasSum_form_right (basis d m) (covForm m q (volume : Measure (Torus d)))
    (basis d m k) y
  have h2 : HasSum (fun l => if l = k then inner ℝ (basis d m k : NegSobolev d m) y * dd0 m q k else 0)
      (inner ℝ (basis d m k : NegSobolev d m) y * dd0 m q k) := hasSum_ite_eq k _
  have h3 : (fun l => inner ℝ (basis d m l : NegSobolev d m) y *
      covForm m q (volume : Measure (Torus d)) (basis d m k) (basis d m l)) =
      fun l => if l = k then inner ℝ (basis d m k : NegSobolev d m) y * dd0 m q k else 0 := by
    funext l
    rw [covForm_volume_basis hm hq]
    by_cases hlk : l = k
    · subst hlk; simp
    · simp [hlk, Ne.symm hlk]
  rw [h3] at h
  rw [h.unique h2]; ring

end Diag

section Cmp

variable {d : ℕ} {m : ℝ}

lemma isFiniteMeasure_withDensityReal_of_cont {ρ : Torus d → ℝ} (hρ : Continuous ρ) :
    IsFiniteMeasure (withDensityReal ρ) := by
  have hi : Integrable ρ (volume : Measure (Torus d)) :=
    hρ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact isFiniteMeasure_withDensity_ofReal hi.hasFiniteIntegral

lemma measure_le_withDensityReal {ρ : Torus d → ℝ} {c : ℝ} (hc : ∀ x, c ≤ ρ x) :
    ENNReal.ofReal c • (volume : Measure (Torus d)) ≤ withDensityReal ρ := by
  rw [Measure.le_iff]
  intro s hs
  unfold withDensityReal
  rw [withDensity_apply _ hs, Measure.smul_apply, smul_eq_mul, ← setLIntegral_const]
  exact lintegral_mono fun u => ENNReal.ofReal_le_ofReal (hc u)

lemma covForm_cmp (hm : (d : ℝ) / 2 + 2 < m) {q : ℝ} (hq : 0 ≤ q) {ρ : Torus d → ℝ}
    (hρ : Continuous ρ) {c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ x, c ≤ ρ x) (x : NegSobolev d m) :
    c * covForm m q (volume : Measure (Torus d)) x x ≤ covForm m q (withDensityReal ρ) x x := by
  haveI := isFiniteMeasure_withDensityReal_of_cont hρ
  rw [q14_covForm_apply hm hq, q14_covForm_apply hm hq, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hcont : Continuous fun a : Torus d =>
      inner ℝ (Real.sqrt (2 * q) • bVec m j a) x * inner ℝ (Real.sqrt (2 * q) • bVec m j a) x :=
    (((q14_continuous_bVec hm j).const_smul (Real.sqrt (2 * q))).inner continuous_const).mul
      (((q14_continuous_bVec hm j).const_smul (Real.sqrt (2 * q))).inner continuous_const)
  have hint : Integrable (fun a : Torus d =>
      inner ℝ (Real.sqrt (2 * q) • bVec m j a) x * inner ℝ (Real.sqrt (2 * q) • bVec m j a) x)
      (withDensityReal ρ) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hnn : (0 : Torus d → ℝ) ≤ᵐ[withDensityReal ρ] fun a =>
      inner ℝ (Real.sqrt (2 * q) • bVec m j a) x * inner ℝ (Real.sqrt (2 * q) • bVec m j a) x :=
    Filter.Eventually.of_forall fun a => mul_self_nonneg _
  have := integral_mono_measure (measure_le_withDensityReal hc) hnn hint
  rw [integral_smul_measure, ENNReal.toReal_ofReal hc0, smul_eq_mul] at this
  exact this

lemma pair_empirical {N : ℕ} (x : Config d N) (f : Torus d → ℝ) :
    pair (empirical x) f = (N : ℝ)⁻¹ * ∑ i, f (x i) := by
  unfold pair empirical
  rw [integral_smul_measure, integral_finsetSum_measure, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul]
  · congr 1
    exact Finset.sum_congr rfl fun i _ => integral_dirac _ _
  · intro i _
    exact integrable_dirac (by simp)

lemma summable_s (hm : (d : ℝ) + 1 < m) :
    Summable fun k : NonzeroLattice d => wt m k * Lattice.jp k.1 := by
  have hs := summable_jp_rpow (d := d) ((m - 1) / 2) (by linarith)
  refine hs.congr fun k => ?_
  unfold wt
  have hj := Torus.jp_pos k.1
  rw [show -(2 * ((m - 1) / 2)) = -m + 1 by ring, Real.rpow_add hj, Real.rpow_one]

lemma dd0_ge (m : ℝ) {q : ℝ} (hq : 0 ≤ q) (k : NonzeroLattice d) :
    q * (wt m k * Lattice.jp k.1) ^ 2 ≤ dd0 m q k := by
  unfold dd0
  have h1 := one_le_enorm_sq k
  have hj : Lattice.jp k.1 ^ 2 = 1 + 4 * Real.pi ^ 2 * Lattice.enorm k.1 ^ 2 := by
    unfold Lattice.jp
    rw [Real.sq_sqrt (by positivity)]
  have hpi : (1 : ℝ) ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have h2 : Lattice.jp k.1 ^ 2 ≤ 2 * (4 * Real.pi ^ 2 * Lattice.enorm k.1 ^ 2) := by
    rw [hj]; nlinarith
  have hw := sq_nonneg (wt m k)
  calc q * (wt m k * Lattice.jp k.1) ^ 2 = q * (wt m k ^ 2 * Lattice.jp k.1 ^ 2) := by ring
    _ ≤ q * (wt m k ^ 2 * (2 * (4 * Real.pi ^ 2 * Lattice.enorm k.1 ^ 2))) := by gcongr
    _ = _ := by ring

lemma dd0_pos (m : ℝ) {q : ℝ} (hq : 0 < q) (k : NonzeroLattice d) : 0 < dd0 m q k := by
  unfold dd0
  have h1 := one_le_enorm_sq k
  have := wt_pos (m := m) k
  positivity

end Cmp

section Entry

variable {d : ℕ} {m : ℝ}

lemma weight_ineq {q D wk wl jk jl dk dl : ℝ} (hq : 0 < q) (hwk : 0 < wk) (hwl : 0 < wl)
    (hjk : 0 < jk) (hjl : 0 < jl) (hD : 0 ≤ D)
    (hDk : q * (wk * jk) ^ 2 ≤ dk) (hDl : q * (wl * jl) ^ 2 ≤ dl) :
    (2 * q * (wk * wl)) ^ 2 / (dk + dl) * (2 * D * (jk * jl)) ^ 2 ≤
      16 * q * D ^ 2 * ((wk * jk) * (wl * jl)) := by
  set sk := wk * jk with hsk
  set sl := wl * jl with hsl
  have hsk0 : 0 < sk := mul_pos hwk hjk
  have hsl0 : 0 < sl := mul_pos hwl hjl
  have hpos : 0 < dk + dl := by
    have : 0 < q * sk ^ 2 := by positivity
    have : 0 < q * sl ^ 2 := by positivity
    linarith
  have h1 : q * (sk * sl) ≤ dk + dl := by
    nlinarith [sq_nonneg (sk - sl), mul_pos hq hsk0, mul_pos hq hsl0, mul_pos hsk0 hsl0,
      mul_nonneg hq.le (sq_nonneg (sk - sl))]
  have e : (2 * q * (wk * wl)) ^ 2 / (dk + dl) * (2 * D * (jk * jl)) ^ 2 =
      16 * q ^ 2 * D ^ 2 * (sk ^ 2 * sl ^ 2) / (dk + dl) := by
    simp only [hsk, hsl]; field_simp; ring
  rw [e, div_le_iff₀ hpos]
  have h2 : 16 * q ^ 2 * D ^ 2 * (sk ^ 2 * sl ^ 2) =
      (16 * q * D ^ 2 * (sk * sl)) * (q * (sk * sl)) := by ring
  rw [h2]
  have h3 : 0 ≤ 16 * q * D ^ 2 * (sk * sl) := by positivity
  calc (16 * q * D ^ 2 * (sk * sl)) * (q * (sk * sl)) ≤ (16 * q * D ^ 2 * (sk * sl)) * (dk + dl) :=
        mul_le_mul_of_nonneg_left h1 h3
    _ = _ := by ring

lemma entry_eq (hm : (d : ℝ) / 2 + 2 < m) {q : ℝ} (hq : 0 ≤ q) {ρ : Torus d → ℝ}
    (hρ : Continuous ρ) {N : ℕ} (hN : 1 ≤ N) (x : Config d N) (k l : NonzeroLattice d) :
    (covForm m q (empirical x) - covForm m q (withDensityReal ρ)) (basis d m k) (basis d m l) =
      2 * q * (wt m k * wt m l) * ((N : ℝ)⁻¹ * ∑ i, Fkl k l (x i) -
        ∫ u, Fkl k l u ∂(withDensityReal ρ)) := by
  haveI : IsFiniteMeasure (empirical x) := ChartAux.isFiniteMeasure_empirical N hN x
  haveI := isFiniteMeasure_withDensityReal_of_cont hρ
  rw [_root_.sub_apply, ContinuousLinearMap.sub_apply, covForm_basis hm hq, covForm_basis hm hq]
  have := pair_empirical x (Fkl k l)
  unfold pair at this
  rw [this]
  ring

lemma sum_s_le (hm : (d : ℝ) + 1 < m) (K : ℝ) (hK : 0 ≤ K) :
    ∑' p : NonzeroLattice d × NonzeroLattice d, ENNReal.ofReal
      (K * ((wt m p.1 * Lattice.jp p.1.1) * (wt m p.2 * Lattice.jp p.2.1))) =
      ENNReal.ofReal (K * (∑' k : NonzeroLattice d, wt m k * Lattice.jp k.1) ^ 2) := by
  have hs := summable_s (d := d) hm
  have hnn : ∀ k : NonzeroLattice d, 0 ≤ wt m k * Lattice.jp k.1 := fun k =>
    mul_nonneg (wt_pos k).le (Torus.jp_pos k.1).le
  have hq : Summable fun p : NonzeroLattice d × NonzeroLattice d =>
      (wt m p.1 * Lattice.jp p.1.1) * (wt m p.2 * Lattice.jp p.2.1) := hs.mul_of_nonneg hs hnn hnn
  have htsum : ∑' p : NonzeroLattice d × NonzeroLattice d,
      (wt m p.1 * Lattice.jp p.1.1) * (wt m p.2 * Lattice.jp p.2.1) =
      (∑' k : NonzeroLattice d, wt m k * Lattice.jp k.1) ^ 2 := by
    rw [sq, tsum_mul_tsum_of_summable_norm (by simpa [Real.norm_of_nonneg (hnn _)] using hs)
      (by simpa [Real.norm_of_nonneg (hnn _)] using hs)]
  rw [← htsum, ← tsum_mul_left]
  exact (ENNReal.ofReal_tsum_of_nonneg (fun p => mul_nonneg hK (mul_nonneg (hnn _) (hnn _)))
    (hq.mul_left K)).symm

end Entry

section Prob

variable {d : ℕ} {m : ℝ}

open ProbabilityTheory in
lemma entry_bound (hm : (d : ℝ) / 2 + 2 < m) {q : ℝ} (hq : 0 < q) {ρ : Torus d → ℝ}
    (hρ : Continuous ρ) {N : ℕ} (hN : 1 ≤ N) (Q : Measure (Config d N)) [IsProbabilityMeasure Q]
    (g : Torus d → ℝ) (hg : Measurable g)
    (hmarg : (N : ℝ≥0∞)⁻¹ • ∑ i, Q.map (fun x : Config d N => x i) =
      (withDensityReal ρ).withDensity fun x => ENNReal.ofReal (g x))
    (Cv δ : ℝ)
    (hgL2 : ∫⁻ x, ‖g x - 1‖ₑ ^ 2 ∂(withDensityReal ρ) ≤ ENNReal.ofReal ((Cv * δ) ^ 2))
    (hvar : ∀ f : Torus d → ℝ, Measurable f → MemLp f 2 (withDensityReal ρ) →
      evariance (fun x : Config d N => pair (empirical x) f) Q ≤
        ENNReal.ofReal (Cv * (N : ℝ)⁻¹ * ∫ x, f x ^ 2 ∂(withDensityReal ρ)))
    (k l : NonzeroLattice d) :
    ∫⁻ x, ENNReal.ofReal (((covForm m q (empirical x) - covForm m q (withDensityReal ρ))
        (basis d m k) (basis d m l)) ^ 2 / (dd0 m q k + dd0 m q l)) ∂Q ≤
      ENNReal.ofReal (16 * q * (d : ℝ) ^ 2 * ((withDensityReal ρ) Set.univ).toReal *
        (|Cv| * (N : ℝ)⁻¹ + (Cv * δ) ^ 2) *
        ((wt m k * Lattice.jp k.1) * (wt m l * Lattice.jp l.1))) := by
  haveI hfin : IsFiniteMeasure (withDensityReal ρ) := isFiniteMeasure_withDensityReal_of_cont hρ
  set μ := withDensityReal ρ with hμ
  set F : Torus d → ℝ := Fkl k l with hF
  set B : ℝ := 2 * d * (Lattice.jp k.1 * Lattice.jp l.1) with hB
  have hFm : Measurable F := (continuous_Fkl k l).measurable
  have hFB : ∀ u, |F u| ≤ B := fun u => abs_Fkl_le k l u
  have hB0 : 0 ≤ B := by
    have := Torus.jp_pos k.1; have := Torus.jp_pos l.1; positivity
  set A : ℝ := ∫ u, F u ∂μ with hA
  set Y : Config d N → ℝ := fun x => (N : ℝ)⁻¹ * ∑ i, F (x i) with hY
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hYm : Measurable Y :=
    measurable_const.mul (Finset.measurable_sum _ fun i _ => hFm.comp (measurable_pi_apply i))
  set w : ℝ := (2 * q * (wt m k * wt m l)) ^ 2 / (dd0 m q k + dd0 m q l) with hw
  have hw0 : 0 ≤ w := by
    have := dd0_pos m hq k; have := dd0_pos m hq l; positivity
  have hentry : ∀ x : Config d N, ((covForm m q (empirical x) - covForm m q μ)
      (basis d m k) (basis d m l)) ^ 2 / (dd0 m q k + dd0 m q l) = w * (Y x - A) ^ 2 := by
    intro x
    rw [entry_eq hm hq.le hρ hN x k l]
    simp only [hw, hY, hA, hF]
    ring
  simp_rw [hentry]
  have hYB : ∀ x, |Y x| ≤ B := by
    intro x
    simp only [hY]
    rw [abs_mul, abs_of_pos (inv_pos.2 hN0)]
    have : |∑ i, F (x i)| ≤ N * B := by
      calc |∑ i, F (x i)| ≤ ∑ i, |F (x i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin N, B := Finset.sum_le_sum fun i _ => hFB _
        _ = N * B := by simp
    calc (N : ℝ)⁻¹ * |∑ i, F (x i)| ≤ (N : ℝ)⁻¹ * (N * B) :=
          mul_le_mul_of_nonneg_left this (inv_nonneg.2 hN0.le)
      _ = B := by field_simp
  have hint : Integrable (fun x => (Y x - A) ^ 2) Q := by
    refine Integrable.of_bound (C := (B + |A|) ^ 2) ((hYm.sub_const A).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    have : |Y x - A| ≤ B + |A| := (abs_sub _ _).trans (by linarith [hYB x])
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hvar' : ∀ f : Torus d → ℝ, Measurable f → MemLp f 2 μ →
      evariance (fun x : Config d N => (N : ℝ)⁻¹ * ∑ i, f ((fun (i : Fin N) (x : Config d N) => x i) i x)) Q ≤
        ENNReal.ofReal (Cv * (N : ℝ)⁻¹ * ∫ x, f x ^ 2 ∂μ) := by
    intro f hf hmem
    have := hvar f hf hmem
    have e : (fun x : Config d N => pair (empirical x) f) =
        fun x : Config d N => (N : ℝ)⁻¹ * ∑ i, f ((fun (i : Fin N) (x : Config d N) => x i) i x) := by
      funext x; exact pair_empirical x f
    rwa [e] at this
  have hsm := ChartAux.second_moment_bound μ Q N hN (fun (i : Fin N) (x : Config d N) => x i)
    (fun i => measurable_pi_apply i) g hg hmarg Cv δ hgL2 hvar' F hFm B hFB
  have hA2 : ∫ x, F x ^ 2 ∂μ ≤ B ^ 2 * (μ Set.univ).toReal := by
    have hi2 : Integrable (fun x => F x ^ 2) μ :=
      ((continuous_Fkl k l).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    calc ∫ x, F x ^ 2 ∂μ ≤ ∫ _x, B ^ 2 ∂μ := by
          refine integral_mono hi2 (integrable_const _) fun x => ?_
          rw [← sq_abs (F x)]
          exact pow_le_pow_left₀ (abs_nonneg _) (hFB x) 2
      _ = B ^ 2 * (μ Set.univ).toReal := by
          simp only [integral_const, smul_eq_mul, Measure.real]; ring
  have hA0 : 0 ≤ ∫ x, F x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  set Kn : ℝ := |Cv| * (N : ℝ)⁻¹ + (Cv * δ) ^ 2 with hKn
  have hKn0 : 0 ≤ Kn := by positivity
  have hbd : ∫ x, (Y x - A) ^ 2 ∂Q ≤ B ^ 2 * (μ Set.univ).toReal * Kn := by
    refine hsm.trans ?_
    calc |Cv| * (N : ℝ)⁻¹ * ∫ x, F x ^ 2 ∂μ + (∫ x, F x ^ 2 ∂μ) * (Cv * δ) ^ 2
        = (∫ x, F x ^ 2 ∂μ) * Kn := by simp only [hKn]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hA2 hKn0
  have hwi := weight_ineq (q := q) (D := (d : ℝ)) hq (wt_pos k) (wt_pos l)
    (Torus.jp_pos k.1) (Torus.jp_pos l.1) (Nat.cast_nonneg d)
    (dd0_ge m hq.le k) (dd0_ge m hq.le l)
  calc ∫⁻ x, ENNReal.ofReal (w * (Y x - A) ^ 2) ∂Q
      = ENNReal.ofReal w * ∫⁻ x, ENNReal.ofReal ((Y x - A) ^ 2) ∂Q := by
        rw [← lintegral_const_mul _ ((hYm.sub_const A).pow_const 2).ennreal_ofReal]
        exact lintegral_congr fun x => ENNReal.ofReal_mul hw0
    _ = ENNReal.ofReal w * ENNReal.ofReal (∫ x, (Y x - A) ^ 2 ∂Q) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => sq_nonneg _)]
    _ ≤ ENNReal.ofReal w * ENNReal.ofReal (B ^ 2 * (μ Set.univ).toReal * Kn) := by gcongr
    _ = ENNReal.ofReal (w * (B ^ 2 * (μ Set.univ).toReal * Kn)) := (ENNReal.ofReal_mul hw0).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hM0 : 0 ≤ (μ Set.univ).toReal * Kn := mul_nonneg ENNReal.toReal_nonneg hKn0
        have h1 : w * B ^ 2 ≤ 16 * q * (d : ℝ) ^ 2 * ((wt m k * Lattice.jp k.1) * (wt m l * Lattice.jp l.1)) := by
          simpa only [hw, hB, mul_pow] using hwi
        calc w * (B ^ 2 * (μ Set.univ).toReal * Kn) = (w * B ^ 2) * ((μ Set.univ).toReal * Kn) := by ring
          _ ≤ (16 * q * (d : ℝ) ^ 2 * ((wt m k * Lattice.jp k.1) * (wt m l * Lattice.jp l.1))) *
              ((μ Set.univ).toReal * Kn) := mul_le_mul_of_nonneg_right h1 hM0
          _ = _ := by ring

end Prob

section Main

variable {d : ℕ} {m : ℝ}

lemma exists_lower_bound {ρ : Torus d → ℝ} (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c ≤ ρ x := by
  obtain ⟨x0, -, hx0⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty (α := Torus d))
    hρ.continuousOn
  exact ⟨ρ x0, hpos x0, fun x => hx0 (Set.mem_univ x)⟩

lemma measurable_entry (hm : (d : ℝ) / 2 + 2 < m) {q : ℝ} (hq : 0 ≤ q) {ρ : Torus d → ℝ}
    (hρ : Continuous ρ) {N : ℕ} (hN : 1 ≤ N) (k l : NonzeroLattice d) :
    Measurable fun x : Config d N => ENNReal.ofReal (((covForm m q (empirical x) -
      covForm m q (withDensityReal ρ)) (basis d m k) (basis d m l)) ^ 2 /
        (dd0 m q k + dd0 m q l)) := by
  have hFm : Measurable (Fkl k l) := (continuous_Fkl k l).measurable
  have hfun : (fun x : Config d N => ENNReal.ofReal (((covForm m q (empirical x) -
      covForm m q (withDensityReal ρ)) (basis d m k) (basis d m l)) ^ 2 /
        (dd0 m q k + dd0 m q l))) = fun x : Config d N => ENNReal.ofReal
      ((2 * q * (wt m k * wt m l) * ((N : ℝ)⁻¹ * ∑ i, Fkl k l (x i) -
        ∫ u, Fkl k l u ∂(withDensityReal ρ))) ^ 2 / (dd0 m q k + dd0 m q l)) := by
    funext x; rw [entry_eq hm hq hρ hN x k l]
  rw [hfun]
  refine Measurable.ennreal_ofReal (Measurable.div_const (Measurable.pow_const ?_ 2) _)
  exact measurable_const.mul ((measurable_const.mul
    (Finset.measurable_sum _ fun i _ => hFm.comp (measurable_pi_apply i))).sub measurable_const)

lemma bures2_pointwise (hm : (d : ℝ) / 2 + 2 < m) {q : ℝ} (hq : 0 < q) {ρ : Torus d → ℝ}
    (hρ : Continuous ρ) {c : ℝ} (hc : 0 < c) (hcρ : ∀ x, c ≤ ρ x) {N : ℕ} (hN : 1 ≤ N)
    (x : Config d N) :
    ENNReal.ofReal (bures2 (covForm m q (empirical x)) (covForm m q (withDensityReal ρ))) ≤
      2 * ENNReal.ofReal c⁻¹ * Uniform.relQuad (basis d m) (dd0 m q)
        (covForm m q (empirical x) - covForm m q (withDensityReal ρ)) := by
  haveI : IsFiniteMeasure (empirical x) := ChartAux.isFiniteMeasure_empirical N hN x
  haveI := isFiniteMeasure_withDensityReal_of_cont hρ
  exact RelCov.bures2_le (basis d m) (dd0 m q) (dd0_pos m hq) (covForm m q (volume : Measure (Torus d)))
    (fun i y => covForm_volume_diag hm hq.le i y) c hc
    (fun y => covForm_cmp hm hq.le hρ hc.le hcρ y)
    (q14_covForm_trace hm hq.le (empirical x)).1 (q14_covForm_trace hm hq.le _).1

end Main

section Final

variable {d : ℕ} {m : ℝ}

/-- the pointwise relative-form majorant of `𝔟(C_N, D)²` (Lemma 3.29, first part). -/
def majorant (d : ℕ) (m q c : ℝ) (ρ : Torus d → ℝ) {N : ℕ} (x : Config d N) : ℝ≥0∞ :=
  2 * ENNReal.ofReal c⁻¹ * Uniform.relQuad (basis d m) (dd0 m q)
    (covForm m q (empirical x) - covForm m q (withDensityReal ρ))

lemma measurable_majorant (hm : (d : ℝ) / 2 + 2 < m) {q : ℝ} (hq : 0 ≤ q) {ρ : Torus d → ℝ}
    (hρ : Continuous ρ) (c : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    Measurable (majorant d m q c ρ (N := N)) := by
  unfold majorant Uniform.relQuad
  refine Measurable.const_mul (Measurable.ennreal_tsum fun p => ?_) _
  exact measurable_entry hm hq hρ hN p.1 p.2

open ProbabilityTheory in
/-- the estimate (i)+(ii): `E[𝒬_{D₀}(C_N - D)] ≤ C (N⁻¹ + δ²)` under the hypotheses of `stationary_noise`. -/
theorem lintegral_majorant_le (hm : (d : ℝ) + 3 ≤ m) {q : ℝ} (hq : 0 < q) {ρ : Torus d → ℝ}
    (hρ : Continuous ρ) (c : ℝ) (hc : 0 < c) (Cv : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (hN : 1 ≤ N) (δ : ℝ) (Q : Measure (Config d N))
      [IsProbabilityMeasure Q] (g : Torus d → ℝ) (hg : Measurable g)
      (hmarg : (N : ℝ≥0∞)⁻¹ • ∑ i, Q.map (fun x : Config d N => x i) =
        (withDensityReal ρ).withDensity fun x => ENNReal.ofReal (g x))
      (hgL2 : ∫⁻ x, ‖g x - 1‖ₑ ^ 2 ∂(withDensityReal ρ) ≤ ENNReal.ofReal ((Cv * δ) ^ 2))
      (hvar : ∀ f : Torus d → ℝ, Measurable f → MemLp f 2 (withDensityReal ρ) →
        evariance (fun x : Config d N => pair (empirical x) f) Q ≤
          ENNReal.ofReal (Cv * (N : ℝ)⁻¹ * ∫ x, f x ^ 2 ∂(withDensityReal ρ))),
      ∫⁻ x, majorant d m q c ρ x ∂Q ≤ ENNReal.ofReal (C * ((N : ℝ)⁻¹ + δ ^ 2)) := by
  have hm1 : (d : ℝ) / 2 + 2 < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hm2 : (d : ℝ) + 1 < m := by linarith
  haveI hfin : IsFiniteMeasure (withDensityReal ρ) := isFiniteMeasure_withDensityReal_of_cont hρ
  set S : ℝ := ∑' k : NonzeroLattice d, wt m k * Lattice.jp k.1 with hS
  set M : ℝ := ((withDensityReal ρ) Set.univ).toReal with hM
  set Kmax : ℝ := max |Cv| (Cv ^ 2) with hKmax
  set C : ℝ := 2 * c⁻¹ * (16 * q * (d : ℝ) ^ 2 * M * Kmax * S ^ 2) with hCdef
  have hS0 : 0 ≤ S := tsum_nonneg fun k => mul_nonneg (wt_pos k).le (Torus.jp_pos k.1).le
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hK0 : 0 ≤ Kmax := (abs_nonneg Cv).trans (le_max_left _ _)
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C, hC0, ?_⟩
  intro N hN δ Q _ g hg hmarg hgL2 hvar
  have hN0 : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  set Kn : ℝ := |Cv| * (N : ℝ)⁻¹ + (Cv * δ) ^ 2 with hKn
  have hKn : Kn ≤ Kmax * ((N : ℝ)⁻¹ + δ ^ 2) := by
    simp only [hKn, hKmax]
    rw [mul_pow]
    nlinarith [mul_nonneg hN0 (sub_nonneg.2 (le_max_left |Cv| (Cv ^ 2))),
      mul_nonneg (sq_nonneg δ) (sub_nonneg.2 (le_max_right |Cv| (Cv ^ 2)))]
  have hKn0 : 0 ≤ Kn := by positivity
  set K1 : ℝ := 16 * q * (d : ℝ) ^ 2 * M * Kn with hK1
  have hK10 : 0 ≤ K1 := by positivity
  have hrq : ∫⁻ x, Uniform.relQuad (basis d m) (dd0 m q)
      (covForm m q (empirical x) - covForm m q (withDensityReal ρ)) ∂Q ≤
      ENNReal.ofReal (K1 * S ^ 2) := by
    set f : NonzeroLattice d × NonzeroLattice d → Config d N → ℝ≥0∞ := fun p x => ENNReal.ofReal
          (((covForm m q (empirical x) - covForm m q (withDensityReal ρ))
            (basis d m p.1) (basis d m p.2)) ^ 2 / (dd0 m q p.1 + dd0 m q p.2)) with hf
    have hfm : ∀ p, AEMeasurable (f p) Q := fun p =>
      (measurable_entry hm1 hq.le hρ hN p.1 p.2).aemeasurable
    have e1 : ∫⁻ x, Uniform.relQuad (basis d m) (dd0 m q)
        (covForm m q (empirical x) - covForm m q (withDensityReal ρ)) ∂Q =
        ∑' p, ∫⁻ x, f p x ∂Q := lintegral_tsum hfm
    rw [e1]
    calc ∑' p, ∫⁻ x, f p x ∂Q
        ≤ ∑' p : NonzeroLattice d × NonzeroLattice d, ENNReal.ofReal
          (K1 * ((wt m p.1 * Lattice.jp p.1.1) * (wt m p.2 * Lattice.jp p.2.1))) :=
          ENNReal.tsum_le_tsum fun p =>
            entry_bound hm1 hq hρ hN Q g hg hmarg Cv δ hgL2 hvar p.1 p.2
      _ = ENNReal.ofReal (K1 * S ^ 2) := sum_s_le hm2 K1 hK10
  unfold majorant
  calc ∫⁻ x, 2 * ENNReal.ofReal c⁻¹ * Uniform.relQuad (basis d m) (dd0 m q)
        (covForm m q (empirical x) - covForm m q (withDensityReal ρ)) ∂Q
      = 2 * ENNReal.ofReal c⁻¹ * ∫⁻ x, Uniform.relQuad (basis d m) (dd0 m q)
        (covForm m q (empirical x) - covForm m q (withDensityReal ρ)) ∂Q :=
        lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
    _ ≤ 2 * ENNReal.ofReal c⁻¹ * ENNReal.ofReal (K1 * S ^ 2) := by gcongr
    _ = ENNReal.ofReal (2 * c⁻¹ * (K1 * S ^ 2)) := by
        have h2c : (0 : ℝ) ≤ 2 * c⁻¹ := by positivity
        rw [ENNReal.ofReal_mul h2c, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        simp
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have : K1 ≤ 16 * q * (d : ℝ) ^ 2 * M * (Kmax * ((N : ℝ)⁻¹ + δ ^ 2)) := by
          rw [hK1]
          have h16 : 0 ≤ 16 * q * (d : ℝ) ^ 2 * M := by have := hM0; positivity
          exact mul_le_mul_of_nonneg_left hKn h16
        calc 2 * c⁻¹ * (K1 * S ^ 2) ≤ 2 * c⁻¹ * (16 * q * (d : ℝ) ^ 2 * M * (Kmax * ((N : ℝ)⁻¹ + δ ^ 2)) * S ^ 2) := by
              gcongr
          _ = _ := by simp only [hCdef]; ring

end Final

section Meas

variable {d : ℕ}

lemma nebot_circle : (𝓝[≠] (0 : UnitAddCircle)).NeBot := by
  refine Filter.neBot_iff.2 fun h => ?_
  have hopen : IsOpen ({0} : Set UnitAddCircle) := (isOpen_singleton_iff_punctured_nhds 0).2 h
  have hclopen : IsClopen ({0} : Set UnitAddCircle) := ⟨isClosed_singleton, hopen⟩
  have hu := hclopen.eq_univ (Set.singleton_nonempty 0)
  have hy : ((1 / 2 : ℝ) : UnitAddCircle) ∈ ({0} : Set UnitAddCircle) := by rw [hu]; trivial
  rw [Set.mem_singleton_iff, AddCircle.coe_eq_zero_iff] at hy
  obtain ⟨n, hn⟩ := hy
  simp only [zsmul_eq_mul, mul_one] at hn
  have h1 : (n : ℝ) = 1 / 2 := hn
  have h2 : (2 * n : ℝ) = 1 := by linarith
  have h3 : (2 * n : ℤ) = 1 := by exact_mod_cast h2
  omega

lemma volume_singleton_torus (hd : 1 ≤ d) (a : Torus d) : (volume : Measure (Torus d)) {a} = 0 := by
  have := nebot_circle
  have e : (volume : Measure (Torus d)) =
      Measure.pi (fun _ : Fin d => (volume : Measure UnitAddCircle)) := rfl
  rw [e, Measure.pi_singleton]
  exact Finset.prod_eq_zero (Finset.mem_univ (⟨0, hd⟩ : Fin d)) (measure_singleton _)

/-- the one-body marginal condition forces `X` to be a.e. measurable (otherwise `P.map X` is the junk Dirac mass, which
is not absolutely continuous). -/
lemma aemeasurable_of_marginal {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] {N : ℕ} (hN : 1 ≤ N) (X : Ω → Config d N)
    (Q : Measure (Config d N)) (hX : P.map X = Q) (ρ g : Torus d → ℝ)
    (hmarg : (N : ℝ≥0∞)⁻¹ • ∑ i, Q.map (fun x : Config d N => x i) =
      (withDensityReal ρ).withDensity fun x => ENNReal.ofReal (g x)) :
    AEMeasurable X P := by
  by_cases hd : d = 0
  · subst hd
    haveI : Subsingleton (Config 0 N) := inferInstance
    exact (measurable_of_subsingleton_codomain X).aemeasurable
  by_contra h
  have h1 := Measure.map_of_not_aemeasurable_of_ne_zero h (IsProbabilityMeasure.ne_zero P)
  obtain ⟨a0, ha0⟩ : ∃ a0 : Config d N, Q = Measure.dirac a0 := ⟨_, hX.symm.trans h1⟩
  have hmap : ∀ i : Fin N, Q.map (fun x : Config d N => x i) = Measure.dirac (a0 i) := fun i => by
    rw [ha0]
    exact Measure.map_dirac' (measurable_pi_apply i) a0
  simp_rw [hmap] at hmarg
  set i0 : Fin N := ⟨0, hN⟩ with hi0
  have hL : (N : ℝ≥0∞)⁻¹ ≤ ((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (a0 i)) {a0 i0} := by
    rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
    calc (N : ℝ≥0∞)⁻¹ = (N : ℝ≥0∞)⁻¹ * 1 := (mul_one _).symm
      _ ≤ _ := by
        gcongr
        calc (1 : ℝ≥0∞) = (Measure.dirac (a0 i0)) {a0 i0} := by
              rw [Measure.dirac_apply_of_mem (Set.mem_singleton _)]
          _ ≤ _ := Finset.single_le_sum (f := fun i => (Measure.dirac (a0 i)) {a0 i0})
              (fun i _ => bot_le) (Finset.mem_univ i0)
  have hR : ((withDensityReal ρ).withDensity fun x => ENNReal.ofReal (g x)) {a0 i0} = 0 := by
    have hac := (withDensity_absolutelyContinuous (withDensityReal ρ) (fun x => ENNReal.ofReal (g x))).trans
      (withDensity_absolutelyContinuous (volume : Measure (Torus d)) (fun x => ENNReal.ofReal (ρ x)))
    exact hac (volume_singleton_torus (Nat.one_le_iff_ne_zero.2 hd) _)
  rw [hmarg, hR] at hL
  have := ENNReal.inv_eq_zero.1 (nonpos_iff_eq_zero.1 hL)
  exact ENNReal.natCast_ne_top N this

end Meas

section Theorem

universe u

variable {d : ℕ}

open ProbabilityTheory in
/-- **Fourier-feature covariance estimate** (Lemma 3.31 `stationary_noise`, the bound on the squared adapted coupling
cost, source L2776-2790).  Hypotheses are exactly those of `stationary_noise` (smooth positive thermal density `ρβ`, one
stationary law `Q` with the evariance bound on the empirical measure, the one-body marginal with density `g` relative
to `μ = ρβ dx`, `‖g - 1‖_{L²(μ)} ≤ Cv δ`).  For every `m ≥ d + 3` and `Cv` there is `C ≥ 0` such that, for every
random configuration `X` with `Law X = Q`,
`E[𝔟(C_N, D)²] ≤ C (N⁻¹ + δ²)`, `C_N = covForm m β⁻¹ μ_N(X)`, `D = covForm m β⁻¹ μ`. -/
theorem bures2_cov_estimate (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ) (hρs : Torus.IsSmooth ρβ)
    (hρp : ∀ x, 0 < ρβ x) :
    ∃ m₀ : ℝ, ∀ m : ℝ, m₀ ≤ m → ∀ Cv : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
        (N : ℕ) (_ : 1 ≤ N) (δ : ℝ)
        (X : Ω → Config d N) (Q : Measure (Config d N)) [IsProbabilityMeasure Q] (_ : P.map X = Q)
        (_ : ∀ f : Torus d → ℝ, Measurable f → MemLp f 2 (withDensityReal ρβ) →
          evariance (fun x : Config d N => pair (empirical x) f) Q ≤
            ENNReal.ofReal (Cv * (N : ℝ)⁻¹ * ∫ x, f x ^ 2 ∂(withDensityReal ρβ)))
        (g : Torus d → ℝ) (_ : Measurable g)
        (_ : (N : ℝ≥0∞)⁻¹ • ∑ i, Q.map (fun x : Config d N => x i) =
          (withDensityReal ρβ).withDensity fun x => ENNReal.ofReal (g x))
        (_ : ∫⁻ x, ‖g x - 1‖ₑ ^ 2 ∂(withDensityReal ρβ) ≤ ENNReal.ofReal ((Cv * δ) ^ 2)),
        ∫⁻ ω, ENNReal.ofReal (Uniform.bures2 (covForm m β⁻¹ (empirical (X ω)))
            (covForm m β⁻¹ (withDensityReal ρβ))) ∂P ≤
          ENNReal.ofReal (C * ((N : ℝ)⁻¹ + δ ^ 2)) := by
  refine ⟨(d : ℝ) + 3, fun m hm Cv => ?_⟩
  have hρ : Continuous ρβ := Torus.continuous_of_continuous_lift
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift ρβ) from hρs).continuous
  obtain ⟨c, hc, hcρ⟩ := exists_lower_bound hρ hρp
  have hq : 0 < β⁻¹ := inv_pos.2 hβ
  have hm1 : (d : ℝ) / 2 + 2 < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨C, hC0, hC⟩ := lintegral_majorant_le hm hq hρ c hc Cv
  refine ⟨C, hC0, ?_⟩
  intro Ω mΩ P _ N hN δ X Q _ hX hvar g hg hmarg hgL2
  have hXm : AEMeasurable X P := aemeasurable_of_marginal P hN X Q hX ρβ g hmarg
  calc ∫⁻ ω, ENNReal.ofReal (Uniform.bures2 (covForm m β⁻¹ (empirical (X ω)))
          (covForm m β⁻¹ (withDensityReal ρβ))) ∂P
      ≤ ∫⁻ ω, majorant d m β⁻¹ c ρβ (X ω) ∂P :=
        lintegral_mono fun ω => bures2_pointwise hm1 hq hρ hc hcρ hN (X ω)
    _ = ∫⁻ x, majorant d m β⁻¹ c ρβ x ∂(P.map X) :=
        (lintegral_map' (measurable_majorant hm1 hq.le hρ c hN).aemeasurable hXm).symm
    _ = ∫⁻ x, majorant d m β⁻¹ c ρβ x ∂Q := by rw [hX]
    _ ≤ _ := hC N hN δ Q g hg hmarg hgL2 hvar

end Theorem

end HRS.Uniform.Q48c
