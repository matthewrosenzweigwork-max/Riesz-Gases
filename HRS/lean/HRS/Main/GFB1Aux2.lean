import HRS.Main.GFSpec3
import HRS.Main.GFB1Aux1
import HRS.Energy.StaticLimitTiltedGauss

/-!
# Packet GFB1, part 2: relocated proofs of `gf_norm_of_pairings` and `gf_measurable_modification`

Statements copied verbatim from `HRS/Main/GFSpec2.lean` / `GFSpec3.lean` (not edited).  Each proof is
`<name>_proof`, tied to its spec by an `example` (`type_of%`).  Helpers carry the prefix `gfb1_`.

* `gf_norm_of_pairings`: the `ℓ²`-norm of `F ∈ E_m` is the supremum of its pairings with the finite
  real-mode combinations `φ_p = ∑_{l∈S} (w_l ⟨l⟩^{-m}) e_l`, `w` rational on `S`.  These form a countable
  family, so the almost-sure hypotheses hold for all of them at once; rational times are then extended to `[0,T]`.
* `gf_measurable_modification`: `Z' t = 1_S Z t` on a measurable full-measure set `S` on which the paths are
  continuous and the rational-grid values agree; each `ω ↦ Z' t ω` is a pointwise limit of measurable functions.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS.Uniform

variable {d : ℕ}

/-! ### Rational grid `⌊(n+1) t⌋ / (n+1)` (shared by both packets) -/

/-- `⌊(n+1) t⌋ / (n+1)`: a rational grid point approximating `t` from below. -/
def gfb1Grid (n : ℕ) (t : ℝ) : ℝ := (⌊((n : ℝ) + 1) * t⌋ : ℝ) / ((n : ℝ) + 1)

theorem gfb1Grid_bounds (n : ℕ) (t : ℝ) :
    t - 1 / ((n : ℝ) + 1) ≤ gfb1Grid n t ∧ gfb1Grid n t ≤ t := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 := Int.floor_le (((n : ℝ) + 1) * t)
  have h2 := Int.lt_floor_add_one (((n : ℝ) + 1) * t)
  unfold gfb1Grid
  constructor
  · have e : (t - 1 / ((n : ℝ) + 1)) * ((n : ℝ) + 1) = ((n : ℝ) + 1) * t - 1 := by
      field_simp
    rw [le_div_iff₀ hpos, e]
    linarith
  · rw [div_le_iff₀ hpos]
    linarith

theorem gfb1Grid_tendsto (t : ℝ) : Tendsto (fun n : ℕ => gfb1Grid n t) atTop (𝓝 t) := by
  have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hg : Tendsto (fun n : ℕ => t - 1 / ((n : ℝ) + 1)) atTop (𝓝 t) := by
    simpa using (tendsto_const_nhds (x := t)).sub h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hg tendsto_const_nhds
    (fun n => (gfb1Grid_bounds n t).1) (fun n => (gfb1Grid_bounds n t).2)

theorem gfb1Grid_mem {t T : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (n : ℕ) :
    gfb1Grid n t ∈ Set.Icc (0 : ℝ) T := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  refine ⟨?_, (gfb1Grid_bounds n t).2.trans ht.2⟩
  have hfl : (0 : ℝ) ≤ (⌊((n : ℝ) + 1) * t⌋ : ℝ) := by
    exact_mod_cast Int.floor_nonneg.2 (mul_nonneg hpos.le ht.1)
  exact div_nonneg hfl hpos.le

/-! ### Test functions: finite real-mode combinations with rational weights -/

/-- Index of the countable family: a finite set of lattice modes with rational weights on it. -/
abbrev gfb1Idx (d : ℕ) : Type := Σ S : Finset (NonzeroLattice d), (S → ℚ)

open Classical in
/-- Real weight of the index `p` at the mode `l` (zero off `p.1`). -/
def gfb1W (p : gfb1Idx d) (l : NonzeroLattice d) : ℝ :=
  if h : l ∈ p.1 then ((p.2 ⟨l, h⟩ : ℚ) : ℝ) else 0

theorem gfb1W_of_mem (p : gfb1Idx d) {l : NonzeroLattice d} (h : l ∈ p.1) :
    gfb1W p l = ((p.2 ⟨l, h⟩ : ℚ) : ℝ) := by
  unfold gfb1W
  rw [dif_pos h]

theorem gfb1W_of_not_mem (p : gfb1Idx d) {l : NonzeroLattice d} (h : l ∉ p.1) :
    gfb1W p l = 0 := by
  unfold gfb1W
  rw [dif_neg h]

/-- The test function `φ_p = ∑_{l∈S} (w_l ⟨l⟩^{-m}) e_l` (real modes `e_l = realMode l`). -/
def gfb1Phi (m : ℝ) (p : gfb1Idx d) : Torus d → ℝ :=
  ∑ l ∈ p.1, (gfb1W p l * Lattice.jp l.1 ^ (-m)) • Torus.realMode l

theorem gfb1_isSmooth_sum {ι : Type*} (s : Finset ι) (f : ι → Torus d → ℝ)
    (h : ∀ i ∈ s, Torus.IsSmooth (f i)) : Torus.IsSmooth (∑ i ∈ s, f i) := by
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => ∑ i ∈ s, f i (Torus.mk x)) :=
    ContDiff.sum fun i hi => h i hi
  unfold Torus.IsSmooth Torus.IsCk Torus.lift
  have e : (∑ i ∈ s, f i) ∘ Torus.mk = fun x => ∑ i ∈ s, f i (Torus.mk x) := by
    funext x
    simp [Finset.sum_apply]
  rw [e]
  exact hc

theorem gfb1_isSmooth_smul {f : Torus d → ℝ} (c : ℝ) (hf : Torus.IsSmooth f) :
    Torus.IsSmooth (c • f) := by
  unfold Torus.IsSmooth Torus.IsCk Torus.lift at *
  exact hf.const_smul c

theorem gfb1_phi_smooth (m : ℝ) (p : gfb1Idx d) : Torus.IsSmooth (gfb1Phi m p) := by
  unfold gfb1Phi
  exact gfb1_isSmooth_sum _ _ fun l _ =>
    gfb1_isSmooth_smul _ (HRS.StaticLimitAux.isSmooth_realMode' l)

theorem gfb1_funRealCoeff_phi (m : ℝ) (p : gfb1Idx d) (k : NonzeroLattice d) :
    Torus.funRealCoeff (gfb1Phi m p) k = gfb1W p k * Lattice.jp k.1 ^ (-m) := by
  unfold gfb1Phi Torus.funRealCoeff
  have hexp : ∀ x, Torus.realMode k x *
      (∑ l ∈ p.1, (gfb1W p l * Lattice.jp l.1 ^ (-m)) • Torus.realMode l) x =
      ∑ l ∈ p.1, (gfb1W p l * Lattice.jp l.1 ^ (-m)) * (Torus.realMode k x * Torus.realMode l x) := by
    intro x
    rw [Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [hexp]
  rw [integral_finset_sum]
  · simp_rw [integral_const_mul, Torus.realMode_orthonormal]
    by_cases hk : k ∈ p.1
    · simp [mul_ite, Finset.sum_ite_eq, hk]
    · simp [mul_ite, Finset.sum_ite_eq, hk, gfb1W_of_not_mem p hk]
  · intro l _
    exact (continuous_const.mul ((continuous_realMode' k).mul (continuous_realMode' l))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem gfb1_mean_phi (m : ℝ) (p : gfb1Idx d) : Torus.mean (gfb1Phi m p) = 0 := by
  unfold Torus.mean gfb1Phi
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [integral_finset_sum]
  · refine Finset.sum_eq_zero fun l _ => ?_
    rw [integral_const_mul, Torus.integral_realMode, mul_zero]
  · intro l _
    exact (continuous_const.mul (continuous_realMode' l)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem gfb1_sobolev_phi (m : ℝ) (p : gfb1Idx d) :
    sobolevNorm m (gfb1Phi m p) = Real.sqrt (∑ l ∈ p.1, gfb1W p l ^ 2) := by
  unfold sobolevNorm
  rw [gfb1_mean_phi]
  have hterm : ∀ k : NonzeroLattice d,
      Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff (gfb1Phi m p) k ^ 2 = gfb1W p k ^ 2 := by
    intro k
    have hj := Torus.jp_pos k.1
    have hne : Lattice.jp k.1 ^ m ≠ 0 := (Real.rpow_pos_of_pos hj m).ne'
    rw [gfb1_funRealCoeff_phi, ← Torus.jp_rpow_sq m k.1, Real.rpow_neg hj.le]
    field_simp
  simp_rw [hterm]
  rw [tsum_eq_sum (s := p.1)]
  · simp
  · intro k hk
    rw [gfb1W_of_not_mem p hk]
    simp

theorem gfb1_eval_phi {m : ℝ} (F : NegSobolev d m) (p : gfb1Idx d) :
    NegSobolev.eval F (gfb1Phi m p) = ∑ l ∈ p.1, NegSobolev.coord F l * gfb1W p l := by
  unfold NegSobolev.eval
  have hz : ∀ k ∉ p.1, NegSobolev.fourierCoeff F k * Torus.funRealCoeff (gfb1Phi m p) k = 0 := by
    intro k hk
    rw [gfb1_funRealCoeff_phi, gfb1W_of_not_mem p hk, zero_mul, mul_zero]
  rw [tsum_eq_sum (s := p.1) hz]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [gfb1_funRealCoeff_phi]
  unfold NegSobolev.fourierCoeff
  have hj := Torus.jp_pos l.1
  have hne : Lattice.jp l.1 ^ m ≠ 0 := (Real.rpow_pos_of_pos hj m).ne'
  rw [Real.rpow_neg hj.le]
  field_simp

/-- Real-variable form of the approximation: the pairing inequality, valid for all rational indices,
extends to all real weights `y` on a finite set `S`. -/
theorem gfb1_approx (x : NonzeroLattice d → ℝ) (B : ℝ)
    (hH : ∀ p : gfb1Idx d, |∑ l ∈ p.1, x l * gfb1W p l| ≤ B * Real.sqrt (∑ l ∈ p.1, gfb1W p l ^ 2))
    (S : Finset (NonzeroLattice d)) (y : NonzeroLattice d → ℝ) :
    |∑ l ∈ S, x l * y l| ≤ B * Real.sqrt (∑ l ∈ S, y l ^ 2) := by
  have hrat : ∀ (n : ℕ) (r : ℝ), ∃ q : ℚ, |(q : ℝ) - r| < 1 / ((n : ℝ) + 1) := by
    intro n r
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨q, h1, h2⟩ := exists_rat_btwn
      (show r - 1 / ((n : ℝ) + 1) < r + 1 / ((n : ℝ) + 1) by linarith)
    exact ⟨q, abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩⟩
  choose rr hrr using hrat
  have hconv : ∀ l, Tendsto (fun n : ℕ => ((rr n (y l) : ℚ) : ℝ)) atTop (𝓝 (y l)) := by
    intro l
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hlim : Tendsto (fun n : ℕ => |((rr n (y l) : ℚ) : ℝ) - y l|) atTop (𝓝 0) :=
      squeeze_zero (fun n => abs_nonneg _) (fun n => (hrr n (y l)).le) h0
    exact tendsto_iff_norm_sub_tendsto_zero.2 (by simpa [Real.norm_eq_abs] using hlim)
  have hn : ∀ n : ℕ, |∑ l ∈ S, x l * ((rr n (y l) : ℚ) : ℝ)| ≤
      B * Real.sqrt (∑ l ∈ S, ((rr n (y l) : ℚ) : ℝ) ^ 2) := by
    intro n
    set pn : gfb1Idx d := ⟨S, fun l => rr n (y l.1)⟩ with hpn
    have h := hH pn
    have e1 : ∑ l ∈ S, x l * gfb1W pn l = ∑ l ∈ S, x l * ((rr n (y l) : ℚ) : ℝ) := by
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [gfb1W_of_mem pn hl]
    have e2 : ∑ l ∈ S, gfb1W pn l ^ 2 = ∑ l ∈ S, ((rr n (y l) : ℚ) : ℝ) ^ 2 := by
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [gfb1W_of_mem pn hl]
    have h' := h
    rw [e1, e2] at h'
    exact h'
  have hT : Tendsto (fun n : ℕ => |∑ l ∈ S, x l * ((rr n (y l) : ℚ) : ℝ)| -
      B * Real.sqrt (∑ l ∈ S, ((rr n (y l) : ℚ) : ℝ) ^ 2)) atTop
      (𝓝 (|∑ l ∈ S, x l * y l| - B * Real.sqrt (∑ l ∈ S, y l ^ 2))) := by
    have hs1 : Tendsto (fun n : ℕ => ∑ l ∈ S, x l * ((rr n (y l) : ℚ) : ℝ)) atTop
        (𝓝 (∑ l ∈ S, x l * y l)) :=
      tendsto_finset_sum _ fun l _ => (hconv l).const_mul (x l)
    have hs2 : Tendsto (fun n : ℕ => ∑ l ∈ S, ((rr n (y l) : ℚ) : ℝ) ^ 2) atTop
        (𝓝 (∑ l ∈ S, y l ^ 2)) :=
      tendsto_finset_sum _ fun l _ => (hconv l).pow 2
    exact hs1.abs.sub (((Real.continuous_sqrt.tendsto _).comp hs2).const_mul B)
  have hle : |∑ l ∈ S, x l * y l| - B * Real.sqrt (∑ l ∈ S, y l ^ 2) ≤ 0 :=
    le_of_tendsto hT (Filter.Eventually.of_forall fun n => sub_nonpos.2 (hn n))
  linarith

theorem gfb1_sq_le_of_le_mul_sqrt {a B : ℝ} (ha : 0 ≤ a) (hB : 0 ≤ B)
    (h : a ≤ B * Real.sqrt a) : a ≤ B ^ 2 := by
  have hs := Real.sq_sqrt ha
  have hsn := Real.sqrt_nonneg a
  set s := Real.sqrt a
  by_cases hsB : s ≤ B
  · calc a = s ^ 2 := hs.symm
      _ ≤ B ^ 2 := pow_le_pow_left₀ hsn hsB 2
  · push_neg at hsB
    have hspos : 0 < s := lt_of_le_of_lt hB hsB
    have : B * s < s * s := mul_lt_mul_of_pos_right hsB hspos
    nlinarith

/-- The `ℓ²`-norm is controlled by the rational pairings (deterministic core). -/
theorem gfb1_norm_le {m : ℝ} (F : NegSobolev d m) (B : ℝ) (hB : 0 ≤ B)
    (hH : ∀ p : gfb1Idx d, |NegSobolev.eval F (gfb1Phi m p)| ≤ B * sobolevNorm m (gfb1Phi m p)) :
    ‖F‖ ≤ B := by
  set x : NonzeroLattice d → ℝ := fun l => NegSobolev.coord F l with hx
  have hH' : ∀ p : gfb1Idx d, |∑ l ∈ p.1, x l * gfb1W p l| ≤
      B * Real.sqrt (∑ l ∈ p.1, gfb1W p l ^ 2) := by
    intro p
    have h := hH p
    rw [gfb1_eval_phi, gfb1_sobolev_phi] at h
    exact h
  have hS : ∀ S : Finset (NonzeroLattice d), ∑ l ∈ S, x l ^ 2 ≤ B ^ 2 := by
    intro S
    have h := gfb1_approx x B hH' S x
    have e : ∑ l ∈ S, x l * x l = ∑ l ∈ S, x l ^ 2 :=
      Finset.sum_congr rfl fun l _ => by ring
    rw [e, abs_of_nonneg (Finset.sum_nonneg fun l _ => sq_nonneg _)] at h
    exact gfb1_sq_le_of_le_mul_sqrt (Finset.sum_nonneg fun l _ => sq_nonneg _) hB h
  have htot : ∑' l, x l ^ 2 ≤ B ^ 2 :=
    Summable.tsum_le_of_sum_le (NegSobolev.coord_sq F).1 (fun S => hS S)
  have hn : ‖F‖ ^ 2 ≤ B ^ 2 := by
    rw [(NegSobolev.coord_sq F).2]
    exact htot
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hB two_ne_zero).1 hn

theorem gf_norm_of_pairings_proof {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (m T : ℝ)
    (R : ℝ → Ω → NegSobolev d m) (B : ℝ → Ω → ℝ)
    (hRc : ∀ᵐ ω ∂P, ContinuousOn (fun t => R t ω) (Set.Icc 0 T))
    (hBc : ∀ᵐ ω ∂P, ContinuousOn (fun t => B t ω) (Set.Icc 0 T))
    (hpair : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
      ∀ᵐ ω ∂P, |NegSobolev.eval (R t ω) φ| ≤ B t ω * sobolevNorm m φ) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, ‖R t ω‖ ≤ B t ω := by
  -- `B ≥ 0` from the constant test function (`sobolevNorm m 1 = 1`, probability volume)
  have hconst : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, 0 ≤ B t ω := by
    intro t ht
    have hsm : Torus.IsSmooth (fun _ : Torus d => (1 : ℝ)) := by
      unfold Torus.IsSmooth Torus.IsCk Torus.lift
      exact contDiff_const
    filter_upwards [hpair t ht (fun _ => (1 : ℝ)) hsm] with ω hω
    have hfc : ∀ k : NonzeroLattice d, Torus.funRealCoeff (fun _ : Torus d => (1 : ℝ)) k = 0 :=
      fun k => by
        unfold Torus.funRealCoeff
        simp [Torus.integral_realMode]
    have hmean : Torus.mean (fun _ : Torus d => (1 : ℝ)) = 1 := by
      unfold Torus.mean
      simp
    have hs1 : sobolevNorm m (fun _ : Torus d => (1 : ℝ)) = 1 := by
      unfold sobolevNorm
      simp [hfc, hmean]
    rw [hs1, mul_one] at hω
    exact le_trans (abs_nonneg _) hω
  -- countably many grid times and countably many test functions
  have hE : ∀ᵐ ω ∂P, ∀ (p : gfb1Idx d) (j : ℤ) (n : ℕ),
      (j : ℝ) / ((n : ℝ) + 1) ∈ Set.Icc (0 : ℝ) T →
      |NegSobolev.eval (R ((j : ℝ) / ((n : ℝ) + 1)) ω) (gfb1Phi m p)| ≤
        B ((j : ℝ) / ((n : ℝ) + 1)) ω * sobolevNorm m (gfb1Phi m p) := by
    refine ae_all_iff.2 fun p => ae_all_iff.2 fun j => ae_all_iff.2 fun n => ?_
    by_cases hmem : (j : ℝ) / ((n : ℝ) + 1) ∈ Set.Icc (0 : ℝ) T
    · filter_upwards [hpair _ hmem _ (gfb1_phi_smooth m p)] with ω hω
      exact fun _ => hω
    · exact Filter.Eventually.of_forall fun _ h => absurd h hmem
  have hB0 : ∀ᵐ ω ∂P, ∀ (j : ℤ) (n : ℕ),
      (j : ℝ) / ((n : ℝ) + 1) ∈ Set.Icc (0 : ℝ) T → 0 ≤ B ((j : ℝ) / ((n : ℝ) + 1)) ω := by
    refine ae_all_iff.2 fun j => ae_all_iff.2 fun n => ?_
    by_cases hmem : (j : ℝ) / ((n : ℝ) + 1) ∈ Set.Icc (0 : ℝ) T
    · filter_upwards [hconst _ hmem] with ω hω
      exact fun _ => hω
    · exact Filter.Eventually.of_forall fun _ h => absurd h hmem
  filter_upwards [hRc, hBc, hE, hB0] with ω hRω hBω hEω hB0ω
  -- the claim on the grid
  have hgrid : ∀ (j : ℤ) (n : ℕ), (j : ℝ) / ((n : ℝ) + 1) ∈ Set.Icc (0 : ℝ) T →
      ‖R ((j : ℝ) / ((n : ℝ) + 1)) ω‖ ≤ B ((j : ℝ) / ((n : ℝ) + 1)) ω := by
    intro j n hmem
    exact gfb1_norm_le (R _ ω) _ (hB0ω j n hmem) (fun p => hEω p j n hmem)
  intro t ht
  have hseq : Tendsto (fun n : ℕ => gfb1Grid n t) atTop (𝓝[Set.Icc 0 T] t) :=
    tendsto_nhdsWithin_iff.2 ⟨gfb1Grid_tendsto t, Filter.Eventually.of_forall fun n => gfb1Grid_mem ht n⟩
  have hconvR : Tendsto (fun n : ℕ => ‖R (gfb1Grid n t) ω‖) atTop (𝓝 ‖R t ω‖) :=
    ((hRω t ht).norm.tendsto).comp hseq
  have hconvB : Tendsto (fun n : ℕ => B (gfb1Grid n t) ω) atTop (𝓝 (B t ω)) :=
    ((hBω t ht).tendsto).comp hseq
  refine le_of_tendsto_of_tendsto hconvR hconvB (Filter.Eventually.of_forall fun n => ?_)
  -- `gfb1Grid n t = (⌊(n+1) t⌋ : ℝ)/(n+1)` is a grid point of the form in `hgrid`
  exact hgrid ⌊((n : ℝ) + 1) * t⌋ n (gfb1Grid_mem ht n)

example := (@gf_norm_of_pairings_proof : type_of% @HRS.GF.gf_norm_of_pairings)

theorem gf_measurable_modification_proof {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (T : ℝ) (Z : ℝ → Ω → E) (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 T))
    (hm : ∀ t ∈ Set.Icc (0 : ℝ) T, AEMeasurable (Z t) P) :
    ∃ Z' : ℝ → Ω → E, (∀ t, Measurable (Z' t)) ∧ (∀ ω, ContinuousOn (fun t => Z' t ω) (Set.Icc 0 T)) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, Z' t =ᵐ[P] Z t := by
  -- measurable versions of all the time sections
  have key : ∀ t : ℝ, ∃ g : Ω → E, Measurable g ∧ (t ∈ Set.Icc (0 : ℝ) T → g =ᵐ[P] Z t) := by
    intro t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) T
    · exact ⟨AEMeasurable.mk (Z t) (hm t ht), (hm t ht).measurable_mk,
        fun _ => (AEMeasurable.ae_eq_mk (hm t ht)).symm⟩
    · exact ⟨fun _ => 0, measurable_const, fun h => absurd h ht⟩
  choose g hgm hgae using key
  -- the good set: rational-grid values agree with `Z`, and the path is continuous
  have h1 : ∀ᵐ ω ∂P, ∀ (j : ℤ) (n : ℕ), (j : ℝ) / ((n : ℝ) + 1) ∈ Set.Icc (0 : ℝ) T →
      g ((j : ℝ) / ((n : ℝ) + 1)) ω = Z ((j : ℝ) / ((n : ℝ) + 1)) ω := by
    refine ae_all_iff.2 fun j => ae_all_iff.2 fun n => ?_
    by_cases hmem : (j : ℝ) / ((n : ℝ) + 1) ∈ Set.Icc (0 : ℝ) T
    · filter_upwards [hgae _ hmem] with ω hω
      exact fun _ => hω
    · exact Filter.Eventually.of_forall fun _ h => absurd h hmem
  set Gset : Set Ω := {ω | (∀ (j : ℤ) (n : ℕ), (j : ℝ) / ((n : ℝ) + 1) ∈ Set.Icc (0 : ℝ) T →
      g ((j : ℝ) / ((n : ℝ) + 1)) ω = Z ((j : ℝ) / ((n : ℝ) + 1)) ω) ∧
      ContinuousOn (fun t => Z t ω) (Set.Icc 0 T)} with hGset
  have hGae : ∀ᵐ ω ∂P, ω ∈ Gset := h1.and hc
  -- a measurable full-measure set inside `Gset`
  set S : Set Ω := (toMeasurable P Gsetᶜ)ᶜ with hS
  have hSm : MeasurableSet S := (measurableSet_toMeasurable P _).compl
  have hSG : S ⊆ Gset := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable P _ h)
  have hSae : ∀ᵐ ω ∂P, ω ∈ S := by
    rw [ae_iff]
    have h0 : P Gsetᶜ = 0 := ae_iff.1 hGae
    have : {ω | ¬ ω ∈ S} = toMeasurable P Gsetᶜ := by
      ext ω; simp [hS]
    rw [this, measure_toMeasurable, h0]
  -- the rational-grid limit
  have hlimit : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ω,
      Tendsto (fun n : ℕ => S.indicator (g (gfb1Grid n t)) ω) atTop (𝓝 (S.indicator (Z t) ω)) := by
    intro t ht ω
    by_cases hω : ω ∈ S
    · have hG := hSG hω
      simp only [Set.indicator_of_mem hω]
      have hval : ∀ n : ℕ, g (gfb1Grid n t) ω = Z (gfb1Grid n t) ω := by
        intro n
        exact hG.1 ⌊((n : ℝ) + 1) * t⌋ n (gfb1Grid_mem ht n)
      simp only [hval]
      have hcont : ContinuousWithinAt (fun s => Z s ω) (Set.Icc 0 T) t := hG.2 t ht
      exact hcont.tendsto.comp (tendsto_nhdsWithin_iff.2
        ⟨gfb1Grid_tendsto t, Filter.Eventually.of_forall fun n => gfb1Grid_mem ht n⟩)
    · simp only [Set.indicator_of_notMem hω]
      exact tendsto_const_nhds
  refine ⟨fun t ω => if t ∈ Set.Icc (0 : ℝ) T then S.indicator (Z t) ω else 0, ?_, ?_, ?_⟩
  · intro t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) T
    · have hmeasSeq : ∀ n : ℕ, Measurable (fun ω => S.indicator (g (gfb1Grid n t)) ω) :=
        fun n => (hgm _).indicator hSm
      have hlim : Tendsto (fun n : ℕ => fun ω => S.indicator (g (gfb1Grid n t)) ω) atTop
          (𝓝 (fun ω => S.indicator (Z t) ω)) :=
        tendsto_pi_nhds.2 fun ω => hlimit t ht ω
      have hmeas : Measurable (fun ω => S.indicator (Z t) ω) :=
        measurable_of_tendsto_metrizable hmeasSeq hlim
      simpa [ht] using hmeas
    · simpa [ht] using (measurable_const : Measurable fun _ : Ω => (0 : E))
  · intro ω
    by_cases hω : ω ∈ S
    · have hcont : ContinuousOn (fun t => Z t ω) (Set.Icc 0 T) := (hSG hω).2
      refine hcont.congr fun t ht => ?_
      simp [ht, Set.indicator_of_mem hω]
    · have h0 : (fun t : ℝ => if t ∈ Set.Icc (0 : ℝ) T then S.indicator (Z t) ω else 0) =
          fun _ => (0 : E) := by
        funext t
        split_ifs <;> simp [hω]
      rw [h0]
      exact continuousOn_const
  · intro t ht
    filter_upwards [hSae] with ω hω
    simp [ht, Set.indicator_of_mem hω]

example := (@gf_measurable_modification_proof : type_of% @HRS.GF.gf_measurable_modification)

end HRS.GF
