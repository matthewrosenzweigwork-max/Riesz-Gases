import HRS.Sections.Sec7Quench
import HRS.Sections.Q38bAux4

/-!
# Packet QUENCH (Q27), part 1: mode algebra and spectral facts

## CHAIN PLAN (Proposition 7.13, TeX `M:E:prop:quench`, L9352-9393)

Files (dependency order): `QuenchAux1` ... `QuenchAuxN`, final assembly `QuenchFinal`
(`quench_modes_proof`, `quench_window_tensors_proof`, `quench_equal_temperature_proof`, statements
verbatim, relocation pattern; `Sec7Quench.lean` is NOT edited).  All helpers are in `namespace HRS.Qch`.

* **Aux1 (this file)**: indices `PosHalf d × Bool ≃ NonzeroLattice d` (`ψ_k = e_k`, `χ_k = -e_{-k}`);
  all analysis is done at the level `j : NonzeroLattice d` with the real basis `e_j = Torus.realMode j`;
  spectral facts (`ĝ>0`, `0<v≤1`, `δv≠0`, `λ_j ≥ 4π²/β`, `σ² = 2λv`, `λ_* > 0` attained, finite
  `ℐ_*`), unit vectors `esingle j ∈ E_m = ℓ²`, `ofFun m (c e_j) = c⟨j⟩^{-m} esingle j`, norms of `modePath`.
* **Aux2**: the propagator at general `r` (`U^{r,t}(c e_j) = e^{-λ(t-r)} c e_j`, homogeneous case, from
  `q38b_isClassical` + `classical_adjoint_unique_of_two`), `∫∇e·∇e' = (2π|j|)² δ_{jj'}`, the covariance
  matrix of the Gaussian part on modes (explicit, positive semidefinite), covariances
  `E[G_j(t)G_{j'}(r)] = δ_{jj'} v_β(e^{-λ|t-r|} - e^{-λ(t+r)})`, `E[Y_jY_{j'}] = δ v_{β₀,j}`.
* **Aux3**: Gaussian laws: `HasGaussianLaw` of finite coordinate vectors of `Z` (sum of independent Gaussians),
  `L²`-limits of Gaussian reals are Gaussian, Riemann sums of continuous paths.
* **Aux4**: one mode as a process: a.s. continuity, continuous jointly measurable modification,
  `B_j = (G_j + λ∫G_j)/σ_j` is a Brownian motion (Gaussian process with `cov = min`, via Fubini and the
  explicit covariance), independent of `Y_j` (jointly Gaussian + uncorrelated).  This gives
  `quench_modes` parts 1 (OU equation + independence of `B`) and 2 (`Var Z^0(e) = v_{β₀,k}`).
* **Aux5**: independence of the coordinate processes over `(k,b)` (Mathlib
  `IsGaussianProcess.iIndepFun_of_covariance_eq_zero`) and the covariance formula
  `E[Z^{a+t}(e)Z^{a+r}(e)] = v_β e^{-λ|t-r|} + δv e^{-2λa}e^{-λ(t+r)}`: `quench_modes` parts 3, 4.
* **Aux6**: Doob.  `B_j` has a Brownian filtration (`exists_isBrownianFiltration`), `doob_L2_continuous`
  gives `E sup_{t≤T}|B_j|² ≤ 4T`; `|G_j| ≤ 2σ_j sup|B_j|` pathwise (integrating factor);
  `E sup_{t≤T}‖Z^{a+t}‖²_{E_m} ≤ ∑_j ⟨j⟩^{-2m}(2 + C(1+|j|²)(a+T)) < ∞` for `m > d/2+1`.
* **Aux7**: Bernstein path operator `Π_n` on `𝒳_T = C([0,T];E_m)` (Mathlib `bernsteinApproximation_uniform`,
  valid for locally convex target): `‖Π_n w‖ ≤ ‖w‖`, `Π_n w → w`, `Π_n w = ∑ b_ν ⊗ w(t_ν)`.
* **Aux8**: abstract bilinear lemma (the Bochner projective tensor `E[Z⊗Z]`): for two `E_m`-valued
  second-order processes with a.s. continuous paths and `E sup‖W‖² < ∞` whose coordinate covariances are
  diagonal and differ by `κ_j f_j(t)f_j(r)`, `E M(W,W) - E' M(W',W') = ∑_j κ_j M(f_je_j,f_je_j)` for every
  bounded bilinear `M` on `𝒳_T` (Bernstein in time, then Hilbert-basis expansion, dominated convergence).
* **Aux9-10**: application to the quench windows; `quench_window_tensors` (i)-(iv) (`λ_*`, `ℐ_*`,
  `e^{2λ_*a}Δ_a → D_*`, `c_T e^{-2λ_*a} ≤ ‖Δ_a‖ ≤ C_T e^{-2λ_*a}` via the test form `ℓ_j ⊗ ℓ_j`).
* **Final**: `quench_equal_temperature` is the case `β₀ = β` (`δv = 0`) of the series identity.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Qch

open HRS.Sec7

variable {d : ℕ}

/-! ### Indices -/

lemma ne_zero_of_posHalf {k : Lattice d} (h : Lattice.IsPosHalf k) : k ≠ 0 := by
  intro hk
  subst hk
  exact lt_irrefl _ h

/-- The real mode index of `ψ_k` (`b = true`, index `k`) and `χ_k` (`b = false`, index `-k`). -/
def idx (k : PosHalf d) (b : Bool) : NonzeroLattice d :=
  if b then ⟨k.1, ne_zero_of_posHalf k.2⟩ else ⟨-k.1, neg_ne_zero.2 (ne_zero_of_posHalf k.2)⟩

/-- The sign with `modeFn k b = sgn b * e_{idx k b}`. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

lemma sgn_sq (b : Bool) : sgn b ^ 2 = 1 := by cases b <;> simp [sgn]

lemma modeFn_eq (k : PosHalf d) (b : Bool) :
    modeFn k.1 b = fun y => sgn b * Torus.realMode (idx k b) y := by
  funext y
  cases b
  · have hn : ¬ Lattice.IsPosHalf (-k.1) := fun h =>
      ((Torus.isPosHalf_neg k.1 (ne_zero_of_posHalf k.2)).1 h) k.2
    simp [modeFn, idx, sgn, Torus.realMode, hn, Torus.sinMode_neg]
  · simp [modeFn, idx, sgn, Torus.realMode, k.2]

lemma enorm_idx (k : PosHalf d) (b : Bool) : Lattice.enorm (idx k b).1 = Lattice.enorm k.1 := by
  cases b
  · simp [idx, PDE.enorm_neg']
  · simp [idx]

lemma jp_idx (k : PosHalf d) (b : Bool) : Lattice.jp (idx k b).1 = Lattice.jp k.1 := by
  unfold Lattice.jp
  rw [enorm_idx]

lemma rieszCoeff_idx (s : ℝ) (k : PosHalf d) (b : Bool) :
    rieszCoeff d s (idx k b).1 = rieszCoeff d s k.1 := by
  cases b
  · simp [idx, PDE.rieszCoeff_neg]
  · simp [idx]

open Classical in
/-- `ℤ^d_+ × {ψ,χ} ≃ ℤ^d ∖ {0}`. -/
def equiv (d : ℕ) : PosHalf d × Bool ≃ NonzeroLattice d where
  toFun p := idx p.1 p.2
  invFun j := if h : Lattice.IsPosHalf j.1 then (⟨j.1, h⟩, true)
    else (⟨-j.1, (Torus.isPosHalf_neg j.1 j.2).2 h⟩, false)
  left_inv := by
    rintro ⟨k, b⟩
    cases b
    · have hn : ¬ Lattice.IsPosHalf (-k.1) := fun h =>
        ((Torus.isPosHalf_neg k.1 (ne_zero_of_posHalf k.2)).1 h) k.2
      simp [idx, hn]
    · simp [idx, k.2]
  right_inv := by
    intro j
    by_cases h : Lattice.IsPosHalf j.1
    · simp [h, idx]
    · simp [h, idx]

lemma equiv_apply (p : PosHalf d × Bool) : equiv d p = idx p.1 p.2 := rfl

/-! ### Rates and variances at the level of `j : NonzeroLattice d` -/

section Spectral

variable {s : ℝ}

lemma lamMode_eq_rate (β : ℝ) (j : NonzeroLattice d) : lamMode d s β j.1 = q38b_rate d s β j := rfl

lemma lamMode_idx (β : ℝ) (k : PosHalf d) (b : Bool) :
    lamMode d s β k.1 = q38b_rate d s β (idx k b) := by
  unfold lamMode q38b_rate
  rw [enorm_idx, rieszCoeff_idx]

lemma varMode_idx (β : ℝ) (k : PosHalf d) (b : Bool) :
    varMode d s β k.1 = varMode d s β (idx k b).1 := by
  unfold varMode
  rw [rieszCoeff_idx]

lemma deltaVar_idx (β β₀ : ℝ) (k : PosHalf d) (b : Bool) :
    deltaVar d s β β₀ k.1 = deltaVar d s β β₀ (idx k b).1 := by
  unfold deltaVar
  rw [← varMode_idx, ← varMode_idx]

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)

include hd hs0 hsd in
lemma rieszCoeff_pos (j : NonzeroLattice d) : 0 < rieszCoeff d s j.1 :=
  PDE.rieszCoeff_pos' (by omega) hs0 hsd j.1 j.2

include hd hs0 hsd in
lemma one_add_pos {β : ℝ} (hβ : 0 < β) (j : NonzeroLattice d) : 0 < 1 + β * rieszCoeff d s j.1 := by
  have := rieszCoeff_pos hd hs0 hsd j
  positivity

include hd hs0 hsd in
lemma varMode_pos {β : ℝ} (hβ : 0 < β) (j : NonzeroLattice d) : 0 < varMode d s β j.1 :=
  inv_pos.2 (one_add_pos hd hs0 hsd hβ j)

include hd hs0 hsd in
lemma varMode_le_one {β : ℝ} (hβ : 0 < β) (j : NonzeroLattice d) : varMode d s β j.1 ≤ 1 := by
  have := rieszCoeff_pos hd hs0 hsd j
  unfold varMode
  rw [inv_le_one₀ (one_add_pos hd hs0 hsd hβ j)]
  nlinarith

include hd hs0 hsd in
lemma abs_deltaVar_le {β β₀ : ℝ} (hβ : 0 < β) (hβ₀ : 0 < β₀) (j : NonzeroLattice d) :
    |deltaVar d s β β₀ j.1| ≤ 1 := by
  have h1 := varMode_pos hd hs0 hsd hβ j
  have h2 := varMode_pos hd hs0 hsd hβ₀ j
  have h3 := varMode_le_one hd hs0 hsd hβ j
  have h4 := varMode_le_one hd hs0 hsd hβ₀ j
  unfold deltaVar
  rw [abs_le]
  constructor <;> linarith

include hd hs0 hsd in
lemma deltaVar_ne_zero {β β₀ : ℝ} (hβ : 0 < β) (hβ₀ : 0 < β₀) (hne : β₀ ≠ β) (j : NonzeroLattice d) :
    deltaVar d s β β₀ j.1 ≠ 0 := by
  intro h
  unfold deltaVar varMode at h
  have h1 := one_add_pos hd hs0 hsd hβ j
  have h2 := one_add_pos hd hs0 hsd hβ₀ j
  have h3 : (1 + β₀ * rieszCoeff d s j.1)⁻¹ = (1 + β * rieszCoeff d s j.1)⁻¹ := sub_eq_zero.1 h
  have h4 := inv_injective h3
  have h5 := rieszCoeff_pos hd hs0 hsd j
  apply hne
  have : β₀ * rieszCoeff d s j.1 = β * rieszCoeff d s j.1 := by linarith
  exact mul_right_cancel₀ h5.ne' this

include hd hs0 hsd in
lemma lamMode_ge {β : ℝ} (hβ : 0 < β) (j : NonzeroLattice d) :
    4 * Real.pi ^ 2 / β ≤ lamMode d s β j.1 := by
  have h1 : 1 ≤ Lattice.enorm j.1 := PDE.one_le_enorm_of_ne_zeroU j.2
  have h2 := rieszCoeff_pos hd hs0 hsd j
  unfold lamMode
  have h3 : 4 * Real.pi ^ 2 ≤ (2 * Real.pi * Lattice.enorm j.1) ^ 2 := by
    have : 2 * Real.pi ≤ 2 * Real.pi * Lattice.enorm j.1 := by
      nlinarith [Real.pi_pos]
    nlinarith [Real.pi_pos]
  have h4 : β⁻¹ ≤ β⁻¹ + rieszCoeff d s j.1 := by linarith
  calc 4 * Real.pi ^ 2 / β = 4 * Real.pi ^ 2 * β⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ (2 * Real.pi * Lattice.enorm j.1) ^ 2 * (β⁻¹ + rieszCoeff d s j.1) := by
        apply mul_le_mul h3 h4 (inv_nonneg.2 hβ.le) (sq_nonneg _)

include hd hs0 hsd in
lemma lamMode_pos {β : ℝ} (hβ : 0 < β) (j : NonzeroLattice d) : 0 < lamMode d s β j.1 :=
  lt_of_lt_of_le (by positivity) (lamMode_ge hd hs0 hsd hβ j)

include hd hs0 hsd in
/-- `λ_{β,j} v_{β,j} = β⁻¹ (2π|j|)²`. -/
lemma lamMode_mul_varMode {β : ℝ} (hβ : 0 < β) (j : NonzeroLattice d) :
    lamMode d s β j.1 * varMode d s β j.1 = β⁻¹ * (2 * Real.pi * Lattice.enorm j.1) ^ 2 := by
  have h1 := one_add_pos hd hs0 hsd hβ j
  unfold lamMode varMode
  field_simp

end Spectral

/-! ### Unit vectors of `E_m` and the coordinates of `ofFun` of a mode -/

section Basis

variable {m : ℝ}

/-- `E_m` is `ℓ²` (definitionally): the cast. -/
def ofLp' (m : ℝ) (F : lp (fun _ : NonzeroLattice d => ℝ) 2) : NegSobolev d m := F

lemma coord_ofLp' (F : lp (fun _ : NonzeroLattice d => ℝ) 2) (k : NonzeroLattice d) :
    NegSobolev.coord (ofLp' m F) k = F k := rfl

lemma ofLp'_smul (a : ℝ) (F : lp (fun _ : NonzeroLattice d => ℝ) 2) :
    ofLp' m (a • F) = a • ofLp' m F := rfl

lemma norm_ofLp' (F : lp (fun _ : NonzeroLattice d => ℝ) 2) : ‖ofLp' m F‖ = ‖F‖ := rfl

lemma ext_coord {F G : NegSobolev d m} (h : ∀ k, NegSobolev.coord F k = NegSobolev.coord G k) : F = G := by
  have : (show lp (fun _ : NonzeroLattice d => ℝ) 2 from F) = (show lp (fun _ : NonzeroLattice d => ℝ) 2 from G) :=
    lp.ext (funext h)
  exact this

/-- The `j`-th unit vector of `E_m = ℓ²(ℤ^d ∖ {0})`. -/
def esingle (m : ℝ) (j : NonzeroLattice d) : NegSobolev d m := ofLp' m (lp.single 2 j (1 : ℝ))

lemma coord_esingle (j j' : NonzeroLattice d) :
    NegSobolev.coord (esingle (d := d) m j) j' = if j' = j then 1 else 0 := by
  unfold esingle
  rw [coord_ofLp']
  by_cases h : j' = j
  · subst h; simp
  · simp [h, lp.single_apply_ne _ _ _ h]

lemma norm_esingle (j : NonzeroLattice d) : ‖esingle (d := d) m j‖ = 1 := by
  unfold esingle
  rw [norm_ofLp']
  have := lp.norm_single (p := (2 : ℝ≥0∞)) (E := fun _ : NonzeroLattice d => ℝ) (by norm_num) j (1 : ℝ)
  simpa using this

lemma coord_smul_esingle (j j' : NonzeroLattice d) (a : ℝ) :
    NegSobolev.coord (a • esingle (d := d) m j) j' = a * (if j' = j then 1 else 0) := by
  have h : a • esingle (d := d) m j = ofLp' m (a • lp.single 2 j (1 : ℝ)) := rfl
  rw [h, coord_ofLp']
  by_cases hj : j' = j
  · subst hj; simp
  · simp [hj, lp.single_apply_ne _ _ _ hj]

lemma funRealCoeff_mode (c : ℝ) (j j' : NonzeroLattice d) :
    Torus.funRealCoeff (fun y => c * Torus.realMode j y) j' = if j' = j then c else 0 := by
  unfold Torus.funRealCoeff
  have : ∀ x, Torus.realMode j' x * (c * Torus.realMode j x) = c * (Torus.realMode j' x * Torus.realMode j x) :=
    fun x => by ring
  simp_rw [this]
  rw [integral_const_mul, Torus.realMode_orthonormal j' j]
  split_ifs <;> simp

lemma ofFun_mode (c : ℝ) (j : NonzeroLattice d) :
    NegSobolev.ofFun m (fun y => c * Torus.realMode j y) =
      (c * Lattice.jp j.1 ^ (-m)) • esingle (d := d) m j := by
  classical
  set a := c * Lattice.jp j.1 ^ (-m) with ha
  have hseq : (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) *
      Torus.funRealCoeff (fun y => c * Torus.realMode j y) k) =
      ⇑(lp.single 2 j a : lp (fun _ : NonzeroLattice d => ℝ) 2) := by
    funext k
    rw [funRealCoeff_mode]
    by_cases h : k = j
    · subst h; simp [ha]; ring
    · simp [h, lp.single_apply_ne _ _ _ h]
  have hmem : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) *
      Torus.funRealCoeff (fun y => c * Torus.realMode j y) k) 2 := by
    have h2 := lp.memℓp (lp.single 2 j a : lp (fun _ : NonzeroLattice d => ℝ) 2)
    rw [← hseq] at h2
    exact h2
  apply ext_coord
  intro k
  unfold NegSobolev.ofFun
  rw [NegSobolev.coord_ofSeq_of_mem _ hmem, coord_smul_esingle, funRealCoeff_mode]
  by_cases h : k = j
  · subst h; simp [ha]; ring
  · simp [h]

lemma norm_ofFun_mode (c : ℝ) (j : NonzeroLattice d) :
    ‖NegSobolev.ofFun m (fun y => c * Torus.realMode j y)‖ = |c| * Lattice.jp j.1 ^ (-m) := by
  rw [ofFun_mode, norm_smul, norm_esingle, mul_one, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos (Torus.jp_pos _) _)]

end Basis

end Qch

end HRS
