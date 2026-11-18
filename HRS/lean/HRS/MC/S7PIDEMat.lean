import HRS.MC.S7PIDMDecay
import HRS.MC.S7PIECont
import HRS.Main.A34Aux5

/-!
# Packet PI-D, sub-packet E: the matrix identity `⟨e_k, U^{u,t} φ⟩ = (V^{t,u} e_k)(φ)`

Helpers `S7PIDE_*` (namespace `HRS.MC.Sec7.S7PIDE`).  For a smooth `φ` and `0 ≤ u ≤ t ≤ T`:

* `S7PIDE_eval_V`: `(V^{t,u} e_k)(φ) = ∑_j T_{kj} φ̂_j = (U^{u,t} φ)^(k)`, where `T = pieT` is the propagator matrix.
  Route: the row `j ↦ ⟨j⟩^{-m} T_{kj}` lies in `ℓ²` (finite-section bound at the integer level `⌊m⌋`), so `Vprop` is the honest
  vector with these coefficients; the series `∑_j T_{kj} φ̂_j` converges to the coefficient of `Uφ` because
  `φ = mean φ + Π_K φ + (tail)` with `U` linear on `Dom J`, `U(const) = const`, and the `H^J`-bound `‖U tail‖ ≤ C ‖tail‖ → 0`.
* `S7PIDE_dom`: `U^{u,t} φ ∈ Dom J` (continuous, in `H^J`), including the degenerate time `t = u = 0`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDE

open HRS HRS.Sec7 HRS.MC.Sec7.PID HRS.MC.Sec7.PIE

variable {d : ℕ}

/-- `U^{0,0} = id` on `Dom J`. -/
theorem S7PIDE_prop_zero {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ}
    (H : PIEHyp J D μ T) {φ : Torus d → ℝ} (hφ : HRS.A33.Dom J φ) :
    propagator D μ 0 0 φ = φ := by
  obtain ⟨hd, hJ, Rg, MB, Λ, VB, ν₀, hA⟩ := H
  exact HRS.A34.a34_prop_zero hd J hJ Rg D.s MB Λ VB ν₀ T D μ hA hφ.1 hφ.2

/-- `U^{u,t} φ ∈ Dom J` for `0 ≤ u ≤ t ≤ T`. -/
theorem S7PIDE_dom {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ}
    (H : PIEHyp J D μ T) {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (htT : t ≤ T)
    {φ : Torus d → ℝ} (hφ : HRS.A33.Dom J φ) : HRS.A33.Dom J (propagator D μ u t φ) := by
  by_cases ht : 0 < t
  · exact pie_prop_dom H ⟨ht, htT⟩ ⟨hu, hut⟩ hφ
  · have ht0 : t = 0 := le_antisymm (not_lt.1 ht) (hu.trans hut)
    have hu0 : u = 0 := le_antisymm (ht0 ▸ hut) hu
    subst ht0
    subst hu0
    rw [S7PIDE_prop_zero H hφ]
    exact hφ

theorem S7PIDE_coeff_const (c : ℝ) (k : NonzeroLattice d) :
    Torus.funRealCoeff (fun _ : Torus d => c) k = 0 := by
  unfold Torus.funRealCoeff
  rw [integral_mul_const, Torus.integral_realMode, zero_mul]

theorem S7PIDE_mean_lin {f g : Torus d → ℝ} (hf : Continuous f) (hg : Continuous g) (a b : ℝ) :
    Torus.mean (fun x => a * f x + b * g x) = a * Torus.mean f + b * Torus.mean g := by
  unfold Torus.mean
  rw [integral_add, integral_const_mul, integral_const_mul]
  · exact (hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul a
  · exact (hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul b

theorem S7PIDE_mean_const (c : ℝ) : Torus.mean (fun _ : Torus d => c) = c := by
  unfold Torus.mean
  simp

/-- The sum of the tail weights tends to zero. -/
theorem S7PIDE_tail_tendsto (w : NonzeroLattice d → ℝ) (hw : Summable w) :
    Tendsto (fun K : Finset (NonzeroLattice d) => ∑' j, (if j ∈ K then (0 : ℝ) else w j)) atTop (𝓝 0) := by
  classical
  have h1 : ∀ K : Finset (NonzeroLattice d),
      ∑' j, (if j ∈ K then (0 : ℝ) else w j) = ∑' j, w j - ∑ j ∈ K, w j := by
    intro K
    have hA : HasSum (fun j => if j ∈ K then w j else 0) (∑ j ∈ K, w j) := by
      have key : ∀ j ∉ K, (if j ∈ K then w j else 0) = 0 := fun j hj => by simp [hj]
      have hA' : HasSum (fun j => if j ∈ K then w j else 0) (∑ j ∈ K, (if j ∈ K then w j else 0)) :=
        hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional (NonzeroLattice d)) key
      have hs : ∑ j ∈ K, (if j ∈ K then w j else 0) = ∑ j ∈ K, w j :=
        Finset.sum_congr rfl fun j hj => by simp [hj]
      rwa [hs] at hA'
    have hB := hw.hasSum.sub hA
    have e : (fun j => w j - if j ∈ K then w j else 0) = fun j => if j ∈ K then (0 : ℝ) else w j := by
      funext j; split_ifs <;> simp
    rw [e] at hB
    exact hB.tsum_eq
  simp_rw [h1]
  have hT : Tendsto (fun K : Finset (NonzeroLattice d) => ∑ j ∈ K, w j) atTop (𝓝 (∑' j, w j)) :=
    hw.hasSum
  have := (tendsto_const_nhds (x := ∑' j, w j) (f := (atTop : Filter (Finset (NonzeroLattice d))))).sub hT
  simpa using this

/-- Row summability of the propagator matrix at an integer level `n ≤ J`. -/
theorem S7PIDE_row_sq {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T)
    (n : ℕ) (hn1 : 1 ≤ n) (hnJ : n ≤ J) {t : ℝ} (ht : t ∈ Set.Ioc 0 T) {u : ℝ} (hu : u ∈ Set.Icc 0 t)
    (k : NonzeroLattice d) :
    Summable (fun j : NonzeroLattice d => (Lattice.jp j.1 ^ (-(n : ℝ)) * pieT D μ u t k j) ^ 2) := by
  classical
  obtain ⟨C, hC0, hC⟩ := pie_finBd H n hn1 hnJ
  have hS := hC t ht u hu
  set S := pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1) (pieT D μ u t) (n : ℝ) with hSdef
  have hrow2 : ∀ K : Finset (NonzeroLattice d), ∑ j ∈ K, S k j ^ 2 ≤ C ^ 2 := by
    intro K
    have h := hS K {k} (fun j => S k j)
    simp only [Finset.sum_singleton] at h
    have e : ∑ j ∈ K, S k j * S k j = ∑ j ∈ K, S k j ^ 2 :=
      Finset.sum_congr rfl fun j _ => (sq _).symm
    rw [e] at h
    have hs0 : 0 ≤ ∑ j ∈ K, S k j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_pos (sub_pos.2 hcon) (sub_pos.2 hcon), mul_nonneg (sq_nonneg C) (sub_pos.2 hcon).le]
  have hsq : Summable fun j => S k j ^ 2 :=
    summable_of_sum_le (fun j => sq_nonneg _) (fun K => hrow2 K)
  have hk : 0 < Lattice.jp k.1 := Torus.jp_pos k.1
  refine (hsq.mul_left ((Lattice.jp k.1 ^ (-(n : ℝ))) ^ 2)).congr fun j => ?_
  have hj : 0 < Lattice.jp j.1 := Torus.jp_pos j.1
  have hk1 : Lattice.jp k.1 ^ (-(n : ℝ)) * Lattice.jp k.1 ^ (n : ℝ) = 1 := by
    rw [← Real.rpow_add hk]; simp
  simp only [hSdef, pieWmat]
  have : Lattice.jp j.1 ^ (-(n : ℝ)) * pieT D μ u t k j =
      Lattice.jp k.1 ^ (-(n : ℝ)) * (Lattice.jp k.1 ^ (n : ℝ) * pieT D μ u t k j * Lattice.jp j.1 ^ (-(n : ℝ))) := by
    linear_combination (-(Lattice.jp j.1 ^ (-(n : ℝ)) * pieT D μ u t k j)) * hk1
  rw [this]
  ring

/-- The weighted row of the propagator matrix is in `ℓ²` (exponent `m ≥ n`). -/
theorem S7PIDE_row_mem {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T)
    (n : ℕ) (hn1 : 1 ≤ n) (hnJ : n ≤ J) (m : ℝ) (hnm : (n : ℝ) ≤ m) {t : ℝ} (ht : t ∈ Set.Ioc 0 T)
    {u : ℝ} (hu : u ∈ Set.Icc 0 t) (k : NonzeroLattice d) :
    Memℓp (fun j : NonzeroLattice d => Lattice.jp j.1 ^ (-m) *
      Torus.funRealCoeff (propagator D μ u t (Torus.realMode j)) k) 2 := by
  rw [Torus.memℓp_two_iff]
  refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => ?_)
    (S7PIDE_row_sq H n hn1 hnJ ht hu k)
  have hj1 : 1 ≤ Lattice.jp j.1 := Torus.jp_ge_one j.1
  have h1 : Lattice.jp j.1 ^ (-m) ≤ Lattice.jp j.1 ^ (-(n : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hj1 (by linarith)
  have h0 : 0 ≤ Lattice.jp j.1 ^ (-m) := Real.rpow_nonneg (Torus.jp_pos j.1).le _
  show (Lattice.jp j.1 ^ (-m) * pieT D μ u t k j) ^ 2 ≤ (Lattice.jp j.1 ^ (-(n : ℝ)) * pieT D μ u t k j) ^ 2
  rw [mul_pow, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h1 2) (sq_nonneg _)

/-- The row series `∑_j T_{kj} φ̂_j` converges to the `k`-th coefficient of `U^{u,t} φ` (`t > 0`). -/
theorem S7PIDE_hasSum_row {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T)
    (hJ1 : 1 ≤ J) {t : ℝ} (ht : t ∈ Set.Ioc 0 T) {u : ℝ} (hu : u ∈ Set.Icc 0 t)
    {φ : Torus d → ℝ} (hφ : HRS.A33.Dom J φ) (k : NonzeroLattice d) :
    HasSum (fun j : NonzeroLattice d => pieT D μ u t k j * Torus.funRealCoeff φ j)
      (Torus.funRealCoeff (propagator D μ u t φ) k) := by
  classical
  obtain ⟨hd, hJ, Rg, MB, Λ, VB, ν₀, hA⟩ := H
  have H' : PIEHyp J D μ T := ⟨hd, hJ, Rg, MB, Λ, VB, ν₀, hA⟩
  obtain ⟨C, hC0, hC⟩ := pie_level_bound H' J hJ1 le_rfl
  set c : NonzeroLattice d → ℝ := fun j => Torus.funRealCoeff φ j with hc
  set m0 : ℝ := Torus.mean φ with hm0
  have hdomC : HRS.A33.Dom J (fun _ : Torus d => m0) :=
    HRS.A33.dom_smooth (HRS.A33.a33_isSmooth_const m0)
  -- the three pieces
  let comb : Finset (NonzeroLattice d) → Torus d → ℝ :=
    fun K x => 1 * m0 + 1 * pieComb K c x
  let tl : Finset (NonzeroLattice d) → Torus d → ℝ := fun K x => 1 * φ x + (-1) * comb K x
  have hdomComb : ∀ K, HRS.A33.Dom J (comb K) := fun K =>
    HRS.A33.dom_closed hdomC (pieDom_comb J K c) 1 1
  have hdomTl : ∀ K, HRS.A33.Dom J (tl K) := fun K =>
    HRS.A33.dom_closed hφ (hdomComb K) 1 (-1)
  have hφsplit : ∀ K, φ = fun x => 1 * tl K x + 1 * comb K x := by
    intro K; funext x; simp only [tl]; ring
  have hcombsplit : ∀ K, comb K = fun x => 1 * (fun _ : Torus d => m0) x + 1 * pieComb K c x := by
    intro K; funext x; simp [comb]
  have hconst : propagator D μ u t (fun _ : Torus d => m0) = fun _ => m0 :=
    HRS.A33.prop_const hd D.s D.hs0 D.hsd J hJ Rg MB Λ VB D ν₀ T μ hA ht m0 hu
  have hcont : ∀ ψ, HRS.A33.Dom J ψ → Continuous (propagator D μ u t ψ) := fun ψ hψ =>
    pie_prop_continuous H' ht hu hψ
  -- coefficient identity
  have hid : ∀ K : Finset (NonzeroLattice d),
      Torus.funRealCoeff (propagator D μ u t φ) k =
        Torus.funRealCoeff (propagator D μ u t (tl K)) k + ∑ j ∈ K, pieT D μ u t k j * c j := by
    intro K
    have e1 : propagator D μ u t φ = fun x => 1 * propagator D μ u t (tl K) x +
        1 * propagator D μ u t (comb K) x := by
      conv_lhs => rw [hφsplit K]
      exact pie_prop_lin H' ht hu (hdomTl K) (hdomComb K) 1 1
    have e2 : propagator D μ u t (comb K) = fun x => 1 * m0 + 1 * propagator D μ u t (pieComb K c) x := by
      conv_lhs => rw [hcombsplit K]
      rw [pie_prop_lin H' ht hu hdomC (pieDom_comb J K c) 1 1, hconst]
    have hcK : Continuous (propagator D μ u t (pieComb K c)) := hcont _ (pieDom_comb J K c)
    have hc1 : Continuous (propagator D μ u t (tl K)) := hcont _ (hdomTl K)
    have hc2 : Continuous (propagator D μ u t (comb K)) := hcont _ (hdomComb K)
    rw [e1, pie_funRealCoeff_lin hc1 hc2, e2,
      pie_funRealCoeff_lin continuous_const hcK, pie_coeff_comb H' ht hu K c k]
    have h0 : Torus.funRealCoeff (fun _ : Torus d => m0) k = 0 := S7PIDE_coeff_const m0 k
    rw [h0]
    have : ∑ j ∈ K, c j * pieT D μ u t k j = ∑ j ∈ K, pieT D μ u t k j * c j :=
      Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [this]
    ring
  -- the tail has small `H^J` norm
  have htail : Tendsto (fun K : Finset (NonzeroLattice d) => sobolevNorm (J : ℝ) (tl K)) atTop (𝓝 0) := by
    have hw : Summable (fun j : NonzeroLattice d => Lattice.jp j.1 ^ (2 * (J : ℝ)) * c j ^ 2) := hφ.2.2
    have hcoef : ∀ (K : Finset (NonzeroLattice d)) (j : NonzeroLattice d),
        Torus.funRealCoeff (tl K) j = if j ∈ K then 0 else c j := by
      intro K j
      have := pie_funRealCoeff_lin (f := φ) (g := comb K) hφ.1 (hdomComb K).1 1 (-1) j
      simp only [tl]
      rw [this]
      have h2 := pie_funRealCoeff_lin (f := fun _ : Torus d => m0) (g := pieComb K c) continuous_const
        (pieComb_continuous K c) 1 1 j
      have h4 : Torus.funRealCoeff (comb K) j = 1 * Torus.funRealCoeff (fun _ : Torus d => m0) j +
          1 * Torus.funRealCoeff (pieComb K c) j := h2
      have h3 : Torus.funRealCoeff (comb K) j = (if j ∈ K then c j else 0) := by
        rw [h4, S7PIDE_coeff_const, pieComb_coeff]
        simp
      rw [h3]
      split_ifs <;> simp [hc]
    have hmean : ∀ K : Finset (NonzeroLattice d), Torus.mean (tl K) = 0 := by
      intro K
      simp only [tl]
      rw [S7PIDE_mean_lin hφ.1 (hdomComb K).1 1 (-1)]
      have hm1 : Torus.mean (comb K) = m0 := by
        simp only [comb]
        rw [S7PIDE_mean_lin continuous_const (pieComb_continuous K c) 1 1, S7PIDE_mean_const,
          pieComb_mean]
        ring
      rw [hm1, hm0]
      ring
    have hsq : Tendsto (fun K : Finset (NonzeroLattice d) => ∑' j : NonzeroLattice d,
        Lattice.jp j.1 ^ (2 * (J : ℝ)) * Torus.funRealCoeff (tl K) j ^ 2) atTop (𝓝 0) := by
      refine (S7PIDE_tail_tendsto _ hw).congr fun K => tsum_congr fun j => ?_
      rw [hcoef K j]
      split_ifs <;> simp
    have h2 : Tendsto (fun K : Finset (NonzeroLattice d) => Real.sqrt (Torus.mean (tl K) ^ 2 +
        ∑' j : NonzeroLattice d, Lattice.jp j.1 ^ (2 * (J : ℝ)) * Torus.funRealCoeff (tl K) j ^ 2))
        atTop (𝓝 (Real.sqrt (0 ^ 2 + 0))) := by
      refine (Real.continuous_sqrt.tendsto _).comp ?_
      simp only [hmean, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      simpa using hsq
    simpa [sobolevNorm] using h2
  -- conclude
  have hbd : ∀ K : Finset (NonzeroLattice d),
      ‖Torus.funRealCoeff (propagator D μ u t (tl K)) k‖ ≤ C * sobolevNorm (J : ℝ) (tl K) := by
    intro K
    obtain ⟨hm1, hm2⟩ := hC t ht u hu (tl K) (hdomTl K)
    rw [Real.norm_eq_abs]
    refine (S7PIDM.S7PIDM_coeff_le hm1 k).trans ?_
    have hj : Lattice.jp k.1 ^ (-(J : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (Torus.jp_ge_one k.1) (by simp)
    have hn : 0 ≤ sobolevNorm (J : ℝ) (propagator D μ u t (tl K)) := S7PIDM.S7PIDM_sob_nonneg _ _
    calc Lattice.jp k.1 ^ (-(J : ℝ)) * sobolevNorm (J : ℝ) (propagator D μ u t (tl K))
        ≤ 1 * sobolevNorm (J : ℝ) (propagator D μ u t (tl K)) := mul_le_mul_of_nonneg_right hj hn
      _ ≤ C * sobolevNorm (J : ℝ) (tl K) := by rw [one_mul]; exact hm2
  have herr : Tendsto (fun K : Finset (NonzeroLattice d) =>
      Torus.funRealCoeff (propagator D μ u t (tl K)) k) atTop (𝓝 0) := by
    refine squeeze_zero_norm hbd ?_
    simpa using htail.const_mul C
  have := (tendsto_const_nhds (x := Torus.funRealCoeff (propagator D μ u t φ) k)).sub herr
  rw [sub_zero] at this
  have hT : Tendsto (fun K : Finset (NonzeroLattice d) =>
      ∑ j ∈ K, pieT D μ u t k j * Torus.funRealCoeff φ j) atTop
      (𝓝 (Torus.funRealCoeff (propagator D μ u t φ) k)) := by
    refine this.congr fun K => ?_
    rw [hid K]
    ring
  exact hT

/-- The matrix identity: `(V^{t,u} e_k)(φ) = ⟨e_k, U^{u,t}φ⟩` for smooth `φ` and `0 ≤ u ≤ t ≤ T`. -/
theorem S7PIDE_eval_V (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (L : ℕ) (hL : PDE.mStar d ≤ L) (hLm : ⌊m⌋₊ ≤ L) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (htT : t ≤ T) (k : NonzeroLattice d) :
    NegSobolev.eval (Vprop R.D R.ρ m t u (modeVec m k)) φ =
      Torus.funRealCoeff (propagator R.D R.ρ u t φ) k := by
  have H := S7PIDM.S7PIDM_pie R T hT L hL
  have hdom : HRS.A33.Dom L φ := HRS.A33.dom_smooth hφ
  have hd3 : (3 : ℝ) ≤ 3 * (d : ℝ) + 8 := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hm0 : 0 ≤ m := by linarith
  have hn1 : 1 ≤ ⌊m⌋₊ := by
    apply Nat.le_floor
    push_cast
    linarith
  have hnm : ((⌊m⌋₊ : ℕ) : ℝ) ≤ m := Nat.floor_le hm0
  have hL1 : 1 ≤ L := hn1.trans hLm
  by_cases ht : 0 < t
  · have hmem := S7PIDE_row_mem H ⌊m⌋₊ hn1 hLm m hnm ⟨ht, htT⟩ ⟨hu, hut⟩ k
    rw [S7PIDM.S7PIDM_eval_vprop R m u t k φ hmem]
    exact (S7PIDE_hasSum_row H hL1 ⟨ht, htT⟩ ⟨hu, hut⟩ hdom k).tsum_eq
  · have ht0 : t = 0 := le_antisymm (not_lt.1 ht) (hu.trans hut)
    have hu0 : u = 0 := le_antisymm (ht0 ▸ hut) hu
    subst ht0
    subst hu0
    have hrealdom : ∀ j : NonzeroLattice d, HRS.A33.Dom L (Torus.realMode j) := fun j =>
      pieDom_realMode L j
    have hz : ∀ j : NonzeroLattice d, propagator R.D R.ρ 0 0 (Torus.realMode j) = Torus.realMode j :=
      fun j => S7PIDE_prop_zero H (hrealdom j)
    have hcoef : ∀ j : NonzeroLattice d,
        Torus.funRealCoeff (propagator R.D R.ρ 0 0 (Torus.realMode j)) k = if k = j then 1 else 0 := by
      intro j
      rw [hz j]
      unfold Torus.funRealCoeff
      exact Torus.realMode_orthonormal k j
    have hmem : Memℓp (fun j : NonzeroLattice d => Lattice.jp j.1 ^ (-m) *
        Torus.funRealCoeff (propagator R.D R.ρ 0 0 (Torus.realMode j)) k) 2 := by
      rw [Torus.memℓp_two_iff]
      refine summable_of_ne_finset_zero (s := {k}) fun j hj => ?_
      have hjk : k ≠ j := by
        intro h; apply hj; simp [h]
      rw [hcoef j, if_neg hjk]; simp
    rw [S7PIDM.S7PIDM_eval_vprop R m 0 0 k φ hmem, S7PIDE_prop_zero H hdom]
    rw [tsum_eq_single k]
    · rw [hcoef k, if_pos rfl, one_mul]
    · intro j hj
      rw [hcoef j, if_neg (Ne.symm hj), zero_mul]

end HRS.MC.Sec7.S7PIDE

end
