import HRS.Uniform.Q48bAux5
import HRS.Uniform.Q48eAux2

/-!
# Q48e, part 3: weighted matrix bounds for the dual evolution at real levels

From the integer-level bounds of the frozen propagator (`frozen_bound`) and the duality `⟨V z, φ⟩ = ⟨z, U φ⟩`, the matrix
of `V` satisfies the weighted `ℓ²` bound `WBound` at every integer level `j ≥ m_*` with constant `e^{c_j (t-u)}`
(`q48e_wbound_of_duality`, the uncentered form of `Q48b.q48b_wbound_of_duality`), hence, by Hadamard's three lines
(`Q48b.q48b_wbound_interp`), at every real level `a ≥ m_*` (`q48e_level`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q48e

open HRS HRS.PDE HRS.Uniform.Q48b

variable {d : ℕ}

/-- The weighted bound at level `a` from duality and `H^a`-boundedness of the (uncentered) adjoint `U`. -/
theorem q48e_wbound_of_duality {m a : ℝ} (Up : (Torus d → ℝ) → Torus d → ℝ)
    (V : NegSobolev d m →L[ℝ] NegSobolev d m)
    (hdual : ∀ (z : NegSobolev d m) (φ : Torus d → ℝ), Torus.IsSmooth φ →
      NegSobolev.eval (V z) φ = NegSobolev.eval z (Up φ))
    (Cdec : ℝ) (hC : 0 ≤ Cdec)
    (hdec : ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
      MemSobolev a (Up φ) ∧ sobolevNorm a (Up φ) ≤ Cdec * sobolevNorm a φ) :
    ∀ S T : Finset (NonzeroLattice d), WBound q48bW (q48bMat m V) S T a Cdec := by
  intro S T ζ
  set Y : NonzeroLattice d → ℝ := fun l => ∑ k ∈ S, q48bMat m V l k * ζ k with hY
  set c : NonzeroLattice d → ℝ := fun l => q48bW l ^ (-2 * a) * Y l with hc
  set φ := q48bTest T c with hφ
  set z := q48bFin m S ζ with hz
  set X : ℝ := ∑ l ∈ T, q48bW l ^ (-2 * a) * Y l ^ 2 with hX
  set Nz : ℝ := ∑ k ∈ S, q48bW k ^ (-2 * a) * ζ k ^ 2 with hNz
  set M : ℝ := Cdec with hM
  have hM0 : 0 ≤ M := hC
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun l _ =>
    mul_nonneg (Real.rpow_nonneg (q48bW_pos l).le _) (sq_nonneg _)
  have hNz0 : 0 ≤ Nz := Finset.sum_nonneg fun l _ =>
    mul_nonneg (Real.rpow_nonneg (q48bW_pos l).le _) (sq_nonneg _)
  show X ≤ M ^ 2 * Nz
  -- the pairing `⟨V z, φ⟩ = X`
  have h1 : NegSobolev.eval (V z) φ = X := by
    rw [hφ, q48b_eval_test]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hz, q48bFin_V]
    simp only [hc, hY]
    have : (∑ k ∈ S, q48bMat m V l k * ζ k) = Y l := rfl
    rw [this]
    ring
  -- duality
  have hsm : Torus.IsSmooth φ := q48bTest_smooth T c
  have h2 : NegSobolev.eval (V z) φ = NegSobolev.eval z (Up φ) := hdual z φ hsm
  have hdφ := hdec φ hsm
  obtain ⟨hmem, hnorm⟩ := hdφ
  set ψ := Up φ with hψ
  have h3 : NegSobolev.eval z ψ = ∑ k ∈ S, ζ k * Torus.funRealCoeff ψ k := by
    rw [hz, q48b_eval_fin]
  -- Cauchy-Schwarz
  set Pψ := ψ with hPψ
  set sj : ℝ := Real.sqrt (∑ k ∈ S, q48bW k ^ (2 * a) * Torus.funRealCoeff Pψ k ^ 2) with hsj
  have hcs : (∑ k ∈ S, ζ k * Torus.funRealCoeff Pψ k) ^ 2 ≤ Nz *
      ∑ k ∈ S, q48bW k ^ (2 * a) * Torus.funRealCoeff Pψ k ^ 2 := by
    have hcs0 := Finset.sum_mul_sq_le_sq_mul_sq S (fun k => q48bW k ^ (-a) * ζ k)
      (fun k => q48bW k ^ a * Torus.funRealCoeff Pψ k)
    have e1 : ∀ k, (q48bW k ^ (-a) * ζ k) * (q48bW k ^ a * Torus.funRealCoeff Pψ k) =
        ζ k * Torus.funRealCoeff Pψ k := by
      intro k
      have := q48b_rpow_neg_mul (q48bW_pos k) a
      calc _ = (q48bW k ^ (-a) * q48bW k ^ a) * (ζ k * Torus.funRealCoeff Pψ k) := by ring
        _ = _ := by rw [this, one_mul]
    have e2 : ∀ k, (q48bW k ^ (-a) * ζ k) ^ 2 = q48bW k ^ (-2 * a) * ζ k ^ 2 := by
      intro k
      rw [mul_pow, q48b_rpow_sq (q48bW_pos k)]; congr 2; ring
    have e3 : ∀ k, (q48bW k ^ a * Torus.funRealCoeff Pψ k) ^ 2 =
        q48bW k ^ (2 * a) * Torus.funRealCoeff Pψ k ^ 2 := by
      intro k
      rw [mul_pow, q48b_rpow_sq (q48bW_pos k)]
    simp_rw [e1, e2, e3] at hcs0
    exact hcs0
  -- the Sobolev norm of `Pψ`
  have hsum_le : ∑ k ∈ S, q48bW k ^ (2 * a) * Torus.funRealCoeff Pψ k ^ 2 ≤
      sobolevNorm a Pψ ^ 2 := by
    have hs := hmem.2
    have hle : ∑ k ∈ S, q48bW k ^ (2 * a) * Torus.funRealCoeff Pψ k ^ 2 ≤
        ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * a) * Torus.funRealCoeff Pψ k ^ 2 :=
      Summable.sum_le_tsum S (fun k _ => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _)
        (sq_nonneg _)) hs
    have hpos : 0 ≤ Torus.mean Pψ ^ 2 + ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * a) *
        Torus.funRealCoeff Pψ k ^ 2 := add_nonneg (sq_nonneg _) (tsum_nonneg fun k =>
          mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _))
    unfold sobolevNorm
    rw [Real.sq_sqrt hpos]
    exact hle.trans (le_add_of_nonneg_left (sq_nonneg _))
  -- bound by `X`
  have hTc : ∑ l ∈ T, q48bW l ^ (2 * a) * c l ^ 2 = X := by
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [hc]
    have hw := q48bW_pos l
    have h2 : (q48bW l ^ (-2 * a)) ^ 2 = q48bW l ^ (-2 * a) * q48bW l ^ (-2 * a) := sq _
    have h3 : q48bW l ^ (2 * a) * q48bW l ^ (-2 * a) = 1 := by
      rw [← Real.rpow_add hw]; simp
    calc q48bW l ^ (2 * a) * (q48bW l ^ (-2 * a) * Y l) ^ 2
        = (q48bW l ^ (2 * a) * q48bW l ^ (-2 * a)) * (q48bW l ^ (-2 * a) * Y l ^ 2) := by ring
      _ = _ := by rw [h3, one_mul]
  have hKb : sobolevNorm a φ ≤ 1 * Real.sqrt X := by
    rw [hφ, q48bTest_sobolevNorm, hTc, one_mul]
  have hPn : sobolevNorm a Pψ ≤ M * Real.sqrt X := by
    have := hnorm.trans (mul_le_mul_of_nonneg_left hKb hC)
    simpa [hM, mul_assoc] using this
  have hPn0 : 0 ≤ sobolevNorm a Pψ := Real.sqrt_nonneg _
  have hsq : sobolevNorm a Pψ ^ 2 ≤ (M * Real.sqrt X) ^ 2 := pow_le_pow_left₀ hPn0 hPn 2
  have hE : X = ∑ k ∈ S, ζ k * Torus.funRealCoeff Pψ k := by
    rw [← h1, h2, h3]
  have hfin : X ^ 2 ≤ (M ^ 2 * Nz) * X := by
    have hh2 : (∑ k ∈ S, ζ k * Torus.funRealCoeff Pψ k) ^ 2 ≤ Nz * (M * Real.sqrt X) ^ 2 :=
      hcs.trans (mul_le_mul_of_nonneg_left (hsum_le.trans hsq) hNz0)
    rw [← hE, mul_pow, Real.sq_sqrt hX0] at hh2
    calc X ^ 2 ≤ Nz * (M ^ 2 * X) := hh2
      _ = (M ^ 2 * Nz) * X := by ring
  rcases eq_or_lt_of_le hX0 with h0 | hpos
  · rw [← h0]; positivity
  · have h5 : X * X ≤ (M ^ 2 * Nz) * X := by simpa [sq] using hfin
    exact le_of_mul_le_mul_right h5 hpos


theorem q48e_level (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ) (hprob : IsProbDensity ρβ)
    (hρ : Torus.IsSmooth ρβ) (hpos : ∀ x, 0 < ρβ x) (a : ℝ) (ha : (mStar d : ℝ) ≤ a) :
    ∃ c : ℝ, ∀ (m u t : ℝ), 0 ≤ u → u ≤ t → ∀ V' : NegSobolev d m →L[ℝ] NegSobolev d m,
      (∀ (z : NegSobolev d m) (φ : Torus d → ℝ), Torus.IsSmooth φ →
        NegSobolev.eval (V' z) φ = NegSobolev.eval z
          (propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) u t φ)) →
      ∀ S T : Finset (NonzeroLattice d), WBound q48bW (q48bMat m V') S T a (Real.exp (c * (t - u))) := by
  have ha0 : 0 ≤ a := le_trans (Nat.cast_nonneg _) ha
  obtain ⟨j, hjdef⟩ : ∃ j : ℕ, j = ⌊a⌋₊ := ⟨_, rfl⟩
  have hj : mStar d ≤ j := by rw [hjdef]; exact Nat.le_floor ha
  have hjle : (j : ℝ) ≤ a := by rw [hjdef]; exact Nat.floor_le ha0
  have hjlt : a < j + 1 := by rw [hjdef]; exact Nat.lt_floor_add_one a
  obtain ⟨c₁, h₁⟩ := frozen_bound hd s hs0 hsd β hβ V hV ρβ hprob hρ hpos j hj
  obtain ⟨c₂, h₂⟩ := frozen_bound hd s hs0 hsd β hβ V hV ρβ hprob hρ hpos (j + 1) (by omega)
  set θ : ℝ := a - j with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; linarith
  have hθ1 : θ ≤ 1 := by rw [hθ]; linarith
  refine ⟨(1 - θ) * c₁ + θ * c₂, fun m u t hu hut V' hdual S T => ?_⟩
  set τ : ℝ := t - u with hτ
  have W₁ := q48e_wbound_of_duality (a := (j : ℝ))
    (propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) u t) V' hdual (Real.exp (c₁ * τ))
    (Real.exp_pos _).le (fun φ hφ => h₁ φ hφ u t hu hut) S T
  have W₂ := q48e_wbound_of_duality (a := ((j + 1 : ℕ) : ℝ))
    (propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) u t) V' hdual (Real.exp (c₂ * τ))
    (Real.exp_pos _).le (fun φ hφ => h₂ φ hφ u t hu hut) S T
  have hi := q48b_wbound_interp q48bW_pos (Real.exp_pos _).le (Real.exp_pos _).le W₁ W₂ θ hθ0 hθ1
  have hα : (j : ℝ) + θ * (((j + 1 : ℕ) : ℝ) - j) = a := by rw [hθ]; push_cast; ring
  have hM : Real.exp (c₁ * τ) ^ (1 - θ) * Real.exp (c₂ * τ) ^ θ =
      Real.exp (((1 - θ) * c₁ + θ * c₂) * τ) := by
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]; congr 1; ring
  rw [hα, hM] at hi
  exact hi

/-! ### Generic facts about `E_m` -/

theorem fourierCoeff_eq_eval {m : ℝ} (F : NegSobolev d m) (l : NonzeroLattice d) :
    NegSobolev.fourierCoeff F l = NegSobolev.eval F (q48bTest {l} fun _ => 1) := by
  rw [q48b_eval_test]
  simp

/-- An element of `E_m` is determined by its pairings with smooth test functions. -/
theorem negSobolev_ext {m : ℝ} {F G : NegSobolev d m}
    (h : ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → NegSobolev.eval F φ = NegSobolev.eval G φ) : F = G := by
  have hfc : ∀ l, NegSobolev.fourierCoeff F l = NegSobolev.fourierCoeff G l := fun l => by
    rw [fourierCoeff_eq_eval, fourierCoeff_eq_eval]
    exact h _ (q48bTest_smooth _ _)
  refine lp.ext (funext fun l => ?_)
  have h1 := q48b_coord_eq_fourier F l
  have h2 := q48b_coord_eq_fourier G l
  show NegSobolev.coord F l = NegSobolev.coord G l
  rw [h1, h2, hfc l]

theorem coord_sub {m : ℝ} (F G : NegSobolev d m) (l : NonzeroLattice d) :
    NegSobolev.coord (F - G) l = NegSobolev.coord F l - NegSobolev.coord G l := by
  have h := congrFun (lp.coeFn_sub (E := fun _ : NonzeroLattice d => ℝ) (p := 2)
    (F : lp (fun _ : NonzeroLattice d => ℝ) 2) (G : lp (fun _ : NonzeroLattice d => ℝ) 2)) l
  rw [Pi.sub_apply] at h
  exact h

/-- The finite truncation `∑_{l ∈ G} F_l b_l`. -/
def truncE (m : ℝ) (G : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ) : NegSobolev d m :=
  ∑ l ∈ G, c l • q48bBasis m l

theorem coord_truncE (m : ℝ) (G : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ)
    (l : NonzeroLattice d) :
    NegSobolev.coord (truncE m G c) l = if l ∈ G then c l else 0 := by
  classical
  unfold truncE
  rw [q48b_coord_sum]
  simp_rw [q48b_coord_smul, q48b_coord_basis]
  by_cases hl : l ∈ G
  · rw [if_pos hl, Finset.sum_eq_single l]
    · simp
    · intro k _ hk; simp [Ne.symm hk]
    · intro h; exact absurd hl h
  · rw [if_neg hl]
    refine Finset.sum_eq_zero fun k hk => ?_
    have : l ≠ k := fun h => hl (h ▸ hk)
    simp [this]

/-- Coordinatewise continuity plus a uniform bound in the stronger norm `∑ ⟨l⟩^{2d} F_l²` gives norm
continuity into `E_m` (compactness of `E_{m-d} ↪ E_m`). -/
theorem continuousOn_of_tail (hd : 1 ≤ d) {X : Type*} [TopologicalSpace X] {S : Set X} {m : ℝ}
    (F : X → NegSobolev d m)
    (hc : ∀ l, ContinuousOn (fun p => NegSobolev.coord (F p) l) S) (B : ℝ)
    (hb : ∀ p ∈ S, ∀ G : Finset (NonzeroLattice d),
      ∑ l ∈ G, q48bW l ^ (2 * (d : ℝ)) * NegSobolev.coord (F p) l ^ 2 ≤ B ^ 2) :
    ContinuousOn F S := by
  classical
  have hsum : Summable fun l : NonzeroLattice d => Lattice.jp l.1 ^ (-(2 * (d : ℝ))) :=
    summable_jp_rpow (d := d) (d : ℝ) (by
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      linarith)
  have hlim := hsum.tendsto_cofinite_zero
  set FG : Finset (NonzeroLattice d) → X → NegSobolev d m :=
    fun G p => truncE m G (fun l => NegSobolev.coord (F p) l) with hFG
  have hFGc : ∀ G, ContinuousOn (FG G) S := by
    intro G
    refine continuousOn_finsetSum G fun l _ => ?_
    exact (hc l).smul continuousOn_const
  have hunif : TendstoUniformlyOn FG F Filter.atTop S := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    set η : ℝ := ε ^ 2 / (2 * (B ^ 2 + 1)) with hη
    have hη0 : 0 < η := by positivity
    have hev := hlim.eventually (gt_mem_nhds hη0)
    have hfin : {l : NonzeroLattice d | ¬ Lattice.jp l.1 ^ (-(2 * (d : ℝ))) < η}.Finite :=
      Filter.eventually_cofinite.1 hev
    refine Filter.eventually_atTop.2 ⟨hfin.toFinset, fun G hG p hp => ?_⟩
    rw [dist_eq_norm]
    -- the tail sum
    have hnorm : ‖F p - FG G p‖ ^ 2 = ∑' l, NegSobolev.coord (F p - FG G p) l ^ 2 :=
      (NegSobolev.coord_sq _).2
    have hcoord : ∀ l, NegSobolev.coord (F p - FG G p) l =
        if l ∈ G then 0 else NegSobolev.coord (F p) l := by
      intro l
      rw [coord_sub]
      simp only [hFG, coord_truncE]
      split_ifs <;> simp
    have htail : ‖F p - FG G p‖ ^ 2 ≤ η * B ^ 2 := by
      rw [hnorm]
      refine Real.tsum_le_of_sum_le (fun l => sq_nonneg _) fun H => ?_
      simp_rw [hcoord]
      have h1 : ∑ l ∈ H, (if l ∈ G then (0 : ℝ) else NegSobolev.coord (F p) l) ^ 2 =
          ∑ l ∈ H.filter (· ∉ G), NegSobolev.coord (F p) l ^ 2 := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun l _ => ?_
        split_ifs <;> simp
      rw [h1]
      have h2 : ∀ l ∈ H.filter (· ∉ G), NegSobolev.coord (F p) l ^ 2 ≤
          η * (q48bW l ^ (2 * (d : ℝ)) * NegSobolev.coord (F p) l ^ 2) := by
        intro l hl
        have hlG : l ∉ G := (Finset.mem_filter.1 hl).2
        have hlfin : l ∉ hfin.toFinset := fun h => hlG (hG h)
        have hlt : Lattice.jp l.1 ^ (-(2 * (d : ℝ))) < η := by
          by_contra hcon
          exact hlfin ((Set.Finite.mem_toFinset hfin).2 hcon)
        have hw := q48bW_pos l
        have hmul : q48bW l ^ (-(2 * (d : ℝ))) * q48bW l ^ (2 * (d : ℝ)) = 1 := by
          rw [← Real.rpow_add hw]; simp
        have hlt' : q48bW l ^ (-(2 * (d : ℝ))) < η := hlt
        have hc2 : 0 ≤ q48bW l ^ (2 * (d : ℝ)) * NegSobolev.coord (F p) l ^ 2 :=
          mul_nonneg (Real.rpow_nonneg hw.le _) (sq_nonneg _)
        calc NegSobolev.coord (F p) l ^ 2
            = (q48bW l ^ (-(2 * (d : ℝ))) * q48bW l ^ (2 * (d : ℝ))) * NegSobolev.coord (F p) l ^ 2 := by
              rw [hmul, one_mul]
          _ = q48bW l ^ (-(2 * (d : ℝ))) * (q48bW l ^ (2 * (d : ℝ)) * NegSobolev.coord (F p) l ^ 2) := by
              ring
          _ ≤ η * (q48bW l ^ (2 * (d : ℝ)) * NegSobolev.coord (F p) l ^ 2) :=
              mul_le_mul_of_nonneg_right hlt'.le hc2
      refine (Finset.sum_le_sum h2).trans ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hb p hp _) hη0.le
    have hB : η * B ^ 2 < ε ^ 2 := by
      rw [hη]
      have h3 : B ^ 2 / (2 * (B ^ 2 + 1)) < 1 := by
        rw [div_lt_one (by positivity)]; nlinarith [sq_nonneg B]
      calc ε ^ 2 / (2 * (B ^ 2 + 1)) * B ^ 2 = ε ^ 2 * (B ^ 2 / (2 * (B ^ 2 + 1))) := by ring
        _ < ε ^ 2 * 1 := mul_lt_mul_of_pos_left h3 (by positivity)
        _ = ε ^ 2 := mul_one _
    have : ‖F p - FG G p‖ ^ 2 < ε ^ 2 := lt_of_le_of_lt htail hB
    exact lt_of_pow_lt_pow_left₀ 2 hε.le this
  exact hunif.continuousOn (Filter.Eventually.of_forall hFGc).frequently

end HRS.Uniform.Q48e
