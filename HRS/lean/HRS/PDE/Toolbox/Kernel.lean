import HRS.PDE.ForwardEq
import HRS.Analysis.Category

/-!
# Appendix C helper lemmas: periodic kernels of smooth compactly supported symbols (Lemma C.7)

Auxiliary results for `HRS/PDE/Toolbox.lean`.

For `φ : ℝ^d → ℂ` smooth with `φ ξ = 0` for `‖ξ‖ ≥ 2` the periodic kernel `K_ε(z) = ∑_k φ(εk) e_k(z)`
(`Kern.kern φ ε`) satisfies `∫ |K_ε| ≤ C` and `∫ tdist(z,0) |K_ε(z)| ≤ C ε` for `ε ∈ (0,1]`
(`kern_L1_bound`, `kern_L1_moment_bound`).  Elementary proof (no Poisson summation): Cauchy–Schwarz
with the weight `W_ε = ∏_i (1 + |e_i - 1|²/ε²)`, `∫ W_ε^{-1} ≤ (πε/4)^d`, and the weighted second
moments of `K_ε` computed from mixed finite differences of `k ↦ φ(εk)`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate ContDiff

namespace HRS.PDE
namespace Kern

section FinDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- backward difference with step `v` -/
def fdiff (v : E) (g : E → F) : E → F := fun x => g (x - v) - g x

/-- iterated differences along a list of steps -/
def fdiffs : List E → (E → F) → (E → F)
  | [], g => g
  | v :: L, g => fdiffs L (fdiff v g)

theorem contDiff_fdiff (v : E) {g : E → F} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (fdiff v g) :=
  (hg.comp (contDiff_id.sub contDiff_const)).sub hg

theorem contDiff_fdiffs (L : List E) {g : E → F} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (fdiffs L g) := by
  induction L generalizing g with
  | nil => exact hg
  | cons v L ih => exact ih (contDiff_fdiff v hg)

theorem norm_iteratedFDeriv_fdiff_le (v : E) {g : E → F} (hg : ContDiff ℝ ∞ g) (B : ℕ → ℝ)
    (hB : ∀ m x, ‖iteratedFDeriv ℝ m g x‖ ≤ B m) (m : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ m (fdiff v g) x‖ ≤ ‖v‖ * B (m + 1) := by
  have h1 : iteratedFDeriv ℝ m (fdiff v g) x =
      iteratedFDeriv ℝ m g (x - v) - iteratedFDeriv ℝ m g x := by
    have : fdiff v g = (fun z => g (z - v)) - g := rfl
    rw [this, iteratedFDeriv_sub_apply, iteratedFDeriv_comp_sub]
    · exact ((hg.comp (contDiff_id.sub contDiff_const)).contDiffAt).of_le (by exact_mod_cast le_top)
    · exact hg.contDiffAt.of_le (by exact_mod_cast le_top)
  rw [h1]
  have hd : Differentiable ℝ (iteratedFDeriv ℝ m g) :=
    hg.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top m)
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := iteratedFDeriv ℝ m g) (s := Set.univ) (C := B (m+1))
    (fun y _ => hd y) (fun y _ => by rw [norm_fderiv_iteratedFDeriv]; exact hB _ _) convex_univ
    (Set.mem_univ x) (Set.mem_univ (x - v))
  simpa [mul_comm] using this

theorem norm_iteratedFDeriv_fdiffs_le (L : List E) {g : E → F} (hg : ContDiff ℝ ∞ g) (B : ℕ → ℝ)
    (hB : ∀ m x, ‖iteratedFDeriv ℝ m g x‖ ≤ B m) (m : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ m (fdiffs L g) x‖ ≤ (L.map (fun v => ‖v‖)).prod * B (m + L.length) := by
  induction L generalizing g B m with
  | nil => simpa [fdiffs] using hB m x
  | cons v L ih =>
    have := ih (contDiff_fdiff v hg) (fun m => ‖v‖ * B (m+1))
      (fun m x => norm_iteratedFDeriv_fdiff_le v hg B hB m x) m
    simp only [fdiffs, List.map_cons, List.prod_cons, List.length_cons]
    calc _ ≤ _ := this
      _ = _ := by rw [show m + L.length + 1 = m + (L.length + 1) by ring]; ring

end FinDiff

/-! ### Trigonometric polynomials and lattice differences -/

section TrigPoly

variable {d : ℕ}

/-- the unit lattice vector `e_i` -/
def eI (i : Fin d) : Lattice d := Pi.single i 1

/-- the finite box `{|k|_∞ ≤ n}` of the lattice -/
def boxF (d n : ℕ) : Finset (Lattice d) :=
  Fintype.piFinset fun _ : Fin d => Finset.Icc (-(n : ℤ)) n

theorem mem_boxF {n : ℕ} {k : Lattice d} : k ∈ boxF d n ↔ InBox n k := by
  simp [boxF, InBox, abs_le]

theorem card_boxF (n : ℕ) : (boxF d n).card = (2 * n + 1) ^ d := by
  simp only [boxF, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  congr 1
  omega

/-- the trigonometric polynomial `∑_k c(k) e_k(z)` (a `tsum`, finite for trigonometric
polynomials) -/
def trig (c : Lattice d → ℂ) (z : Torus d) : ℂ := ∑' k, c k * Torus.mode k z

theorem trig_eq_sum {n : ℕ} {c : Lattice d → ℂ} (hc : IsTrigPoly n c) (z : Torus d) :
    trig c z = ∑ k ∈ boxF d n, c k * Torus.mode k z := by
  unfold trig
  refine tsum_eq_sum fun k hk => ?_
  have : c k = 0 := by
    by_contra h
    exact hk (mem_boxF.2 (hc k h))
  simp [this]

theorem summable_trig {n : ℕ} {c : Lattice d → ℂ} (hc : IsTrigPoly n c) (z : Torus d) :
    Summable fun k => c k * Torus.mode k z := by
  refine summable_of_ne_finset_zero (s := boxF d n) fun k hk => ?_
  have : c k = 0 := by
    by_contra h
    exact hk (mem_boxF.2 (hc k h))
  simp [this]

theorem isTrigPoly_mono {n m : ℕ} {c : Lattice d → ℂ} (hc : IsTrigPoly n c) (h : n ≤ m) :
    IsTrigPoly m c := fun k hk j => (hc k hk j).trans (by exact_mod_cast h)

theorem isTrigPoly_sub {n : ℕ} {a b : Lattice d → ℂ} (ha : IsTrigPoly n a) (hb : IsTrigPoly n b) :
    IsTrigPoly n (a - b) := by
  intro k hk
  by_cases h : a k = 0
  · have : b k ≠ 0 := by intro h2; apply hk; simp [h, h2]
    exact hb k this
  · exact ha k h

theorem isTrigPoly_shift {n : ℕ} {c : Lattice d → ℂ} (hc : IsTrigPoly n c) (i : Fin d) :
    IsTrigPoly (n + 1) (fun k => c (k - eI i)) := by
  intro k hk j
  have := hc _ hk j
  simp only [eI, Pi.sub_apply, Pi.single_apply] at this
  rw [abs_le] at this ⊢
  push_cast
  split_ifs at this <;> omega

/-- the backward lattice difference `c(k - e_i) - c(k)` -/
def Dl (i : Fin d) (c : Lattice d → ℂ) : Lattice d → ℂ := fun k => c (k - eI i) - c k

/-- iterated lattice differences -/
def Dls : List (Fin d) → (Lattice d → ℂ) → (Lattice d → ℂ)
  | [], c => c
  | i :: L, c => Dls L (Dl i c)

theorem isTrigPoly_Dl {n : ℕ} {c : Lattice d → ℂ} (hc : IsTrigPoly n c) (i : Fin d) :
    IsTrigPoly (n + 1) (Dl i c) :=
  isTrigPoly_sub (isTrigPoly_shift hc i) (isTrigPoly_mono hc (Nat.le_succ n))

theorem isTrigPoly_Dls (L : List (Fin d)) {n : ℕ} {c : Lattice d → ℂ} (hc : IsTrigPoly n c) :
    IsTrigPoly (n + L.length) (Dls L c) := by
  induction L generalizing n c with
  | nil => simpa [Dls] using hc
  | cons i L ih =>
    have := ih (isTrigPoly_Dl hc i)
    simpa [Dls, add_assoc, add_comm 1] using this

theorem trig_shift (c : Lattice d → ℂ) (i : Fin d) (z : Torus d) :
    trig (fun k => c (k - eI i)) z = Torus.mode (eI i) z * trig c z := by
  unfold trig
  rw [← tsum_mul_left, ← Equiv.tsum_eq (Equiv.addRight (eI i))]
  refine tsum_congr fun k => ?_
  simp [Torus.mode_add]
  ring

theorem trig_Dl {n : ℕ} {c : Lattice d → ℂ} (hc : IsTrigPoly n c) (i : Fin d) (z : Torus d) :
    (Torus.mode (eI i) z - 1) * trig c z = trig (Dl i c) z := by
  have h1 := summable_trig (isTrigPoly_shift hc i) z
  have h2 := summable_trig hc z
  have : trig (Dl i c) z = trig (fun k => c (k - eI i)) z - trig c z := by
    unfold trig Dl
    rw [← h1.tsum_sub h2]
    refine tsum_congr fun k => ?_
    ring
  rw [this, trig_shift]; ring

theorem trig_Dls (L : List (Fin d)) {n : ℕ} {c : Lattice d → ℂ} (hc : IsTrigPoly n c) (z : Torus d) :
    (L.map fun i => Torus.mode (eI i) z - 1).prod * trig c z = trig (Dls L c) z := by
  induction L generalizing n c with
  | nil => simp [Dls]
  | cons i L ih =>
    simp only [Dls, List.map_cons, List.prod_cons]
    rw [← ih (isTrigPoly_Dl hc i), ← trig_Dl hc i]; ring

/-- Parseval for trigonometric polynomials. -/
theorem integral_norm_sq_trig {n : ℕ} {c : Lattice d → ℂ} (hc : IsTrigPoly n c) :
    ∫ z, ‖trig c z‖ ^ 2 = ∑ k ∈ boxF d n, ‖c k‖ ^ 2 := by
  have key : ∀ z, ((‖trig c z‖ ^ 2 : ℝ) : ℂ) =
      ∑ k ∈ boxF d n, ∑ l ∈ boxF d n, c k * conj (c l) * Torus.mode (k + -l) z := by
    intro z
    rw [Complex.ofReal_pow, ← Complex.mul_conj', trig_eq_sum hc, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, Torus.mode_add, Torus.mode_neg]
    ring
  have hint : ∀ k l : Lattice d, Integrable fun z : Torus d => c k * conj (c l) * Torus.mode (k + -l) z :=
    fun k l => (Torus.integrable_mode _).const_mul _
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [key]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l]
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [integral_finsetSum _ fun l _ => hint k l]
  simp_rw [integral_const_mul, Torus.integral_mode]
  have hh : ∀ x : Lattice d, (k + -x = 0 ↔ k = x) := fun x => add_neg_eq_zero
  simp_rw [hh]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp [hk, Complex.mul_conj']

end TrigPoly

/-! ### The kernels `K_ε` and their weighted second moments -/

section Kernel

variable {d : ℕ}

/-- coefficients `φ(εk)` -/
def kcoef (φ : Euc d → ℂ) (ε : ℝ) : Lattice d → ℂ := fun k => φ (ε • Lattice.toEuc k)

/-- the periodic kernel `K_ε(z) = ∑_k φ(εk) e_k(z)` -/
def kern (φ : Euc d → ℂ) (ε : ℝ) : Torus d → ℂ := trig (kcoef φ ε)

/-- `q_i(z) = |e_i(z) - 1|² = 4 sin²(π z_i)` -/
def qf (i : Fin d) (z : Torus d) : ℝ := ‖Torus.mode (eI i) z - 1‖ ^ 2

theorem isTrigPoly_kcoef {φ : Euc d → ℂ} (hsupp : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0) {ε : ℝ} (hε : 0 < ε) :
    IsTrigPoly ⌈2 / ε⌉₊ (kcoef φ ε) := by
  intro k hk j
  by_contra hj
  apply hk
  apply hsupp
  have h1 : ((⌈2 / ε⌉₊ : ℕ) : ℝ) < |(k j : ℝ)| := by
    have : ((⌈2 / ε⌉₊ : ℤ)) < |k j| := by simpa using not_le.1 hj
    exact_mod_cast this
  have h2 : 2 / ε < |(k j : ℝ)| := lt_of_le_of_lt (Nat.le_ceil _) h1
  have h3 : ‖(ε • Lattice.toEuc k) j‖ ≤ ‖ε • Lattice.toEuc k‖ := PiLp.norm_apply_le _ j
  have h4 : ‖(ε • Lattice.toEuc k) j‖ = ε * |(k j : ℝ)| := by
    simp [Lattice.toEuc, abs_of_pos hε]
  rw [h4] at h3
  calc (2 : ℝ) = ε * (2 / ε) := by field_simp
    _ ≤ ε * |(k j : ℝ)| := by gcongr
    _ ≤ _ := h3

theorem toEuc_sub_eI (k : Lattice d) (i : Fin d) :
    Lattice.toEuc (k - eI i) = Lattice.toEuc k - EuclideanSpace.single i (1 : ℝ) := by
  ext j
  by_cases h : j = i <;> simp [Lattice.toEuc, eI, h, Pi.single_apply]

theorem Dls_comp_toEuc (L : List (Fin d)) (g : Euc d → ℂ) :
    Dls L (g ∘ Lattice.toEuc) =
      (fdiffs (L.map fun i => EuclideanSpace.single i (1 : ℝ)) g) ∘ Lattice.toEuc := by
  induction L generalizing g with
  | nil => rfl
  | cons i L ih =>
    simp only [Dls, List.map_cons, fdiffs]
    rw [← ih]
    congr 1
    funext k
    simp [Dl, fdiff, toEuc_sub_eI]

theorem exists_bound_iteratedFDeriv {φ : Euc d → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hsupp : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0) :
    ∃ B : ℕ → ℝ, ∀ m x, ‖iteratedFDeriv ℝ m φ x‖ ≤ B m := by
  have hcs : HasCompactSupport φ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) 2) fun x hx => ?_
    apply hsupp
    exact (by simpa [not_le] using hx : 2 < ‖x‖).le
  have : ∀ m : ℕ, ∃ b : ℝ, ∀ x, ‖iteratedFDeriv ℝ m φ x‖ ≤ b := by
    intro m
    have hc : Continuous (iteratedFDeriv ℝ m φ) := hφ.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    obtain ⟨b, hb⟩ := (hcs.iteratedFDeriv m).exists_bound_of_continuous hc
    exact ⟨b, hb⟩
  choose B hB using this
  exact ⟨B, fun m x => hB m x⟩

theorem norm_Dls_kcoef_le {φ : Euc d → ℂ} (hφ : ContDiff ℝ ∞ φ) {B : ℕ → ℝ}
    (hB : ∀ m x, ‖iteratedFDeriv ℝ m φ x‖ ≤ B m) (L : List (Fin d)) {ε : ℝ} (hε : 0 < ε) (k : Lattice d) :
    ‖Dls L (kcoef φ ε) k‖ ≤ ε ^ L.length * B L.length := by
  have hg : ContDiff ℝ ∞ (fun x : Euc d => φ (ε • x)) := hφ.comp (contDiff_id.const_smul ε)
  have hB' : ∀ m x, ‖iteratedFDeriv ℝ m (fun x : Euc d => φ (ε • x)) x‖ ≤ ε ^ m * B m := by
    intro m x
    rw [iteratedFDeriv_comp_const_smul ε (hφ.of_le (by exact_mod_cast le_top))]
    simp only [norm_smul, norm_pow, Real.norm_eq_abs, abs_of_pos hε]
    exact mul_le_mul_of_nonneg_left (hB m _) (by positivity)
  have := norm_iteratedFDeriv_fdiffs_le (L.map fun i => EuclideanSpace.single i (1 : ℝ)) hg
    (fun m => ε ^ m * B m) hB' 0 (Lattice.toEuc k)
  have h2 : Dls L (kcoef φ ε) = (fdiffs (L.map fun i => EuclideanSpace.single i (1 : ℝ)) (fun x : Euc d => φ (ε • x))) ∘ Lattice.toEuc :=
    Dls_comp_toEuc L (fun x => φ (ε • x))
  rw [h2]
  simp only [Function.comp_apply]
  have h1 : ((L.map fun i => (EuclideanSpace.single i (1 : ℝ) : Euc d)).map fun v => ‖v‖).prod = 1 := by
    simp [List.map_map, Function.comp_def]
  rw [h1, one_mul, norm_iteratedFDeriv_zero] at this
  simpa [List.length_map] using this


theorem prod_qf_mul_norm_sq (L : List (Fin d)) (z : Torus d) (w : ℂ) :
    (L.map fun i => qf i z).prod * ‖w‖ ^ 2 =
      ‖(L.map fun i => Torus.mode (eI i) z - 1).prod * w‖ ^ 2 := by
  induction L with
  | nil => simp
  | cons i L ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, mul_assoc, ih]
    simp only [qf, norm_mul, mul_pow]
    ring

/-- Weighted second moments of `K_ε`: `∫ ∏_{i∈L} q_i |K_ε|² ≤ C ε^{2|L|-d}`. -/
theorem kern_moment {φ : Euc d → ℂ} (hφ : ContDiff ℝ ∞ φ) (hsupp : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0)
    (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ L : List (Fin d), L.length = n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∫ z, (L.map fun i => qf i z).prod * ‖kern φ ε z‖ ^ 2 ≤ C * (ε ^ (2 * n) / ε ^ d) := by
  obtain ⟨B, hB⟩ := exists_bound_iteratedFDeriv hφ hsupp
  refine ⟨(7 + 2 * n : ℝ) ^ d * B n ^ 2, by positivity, fun L hL ε hε hε1 => ?_⟩
  have hc := isTrigPoly_kcoef hsupp hε
  have hc' := isTrigPoly_Dls L hc
  have h1 : ∀ z, (L.map fun i => qf i z).prod * ‖kern φ ε z‖ ^ 2 = ‖trig (Dls L (kcoef φ ε)) z‖ ^ 2 := by
    intro z
    rw [prod_qf_mul_norm_sq, kern, trig_Dls L hc]
  simp_rw [h1]
  rw [integral_norm_sq_trig hc']
  have h2 : ∀ k, ‖Dls L (kcoef φ ε) k‖ ^ 2 ≤ (ε ^ n * B n) ^ 2 := by
    intro k
    have := norm_Dls_kcoef_le hφ hB L hε k
    rw [hL] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  calc ∑ k ∈ boxF d (⌈2 / ε⌉₊ + L.length), ‖Dls L (kcoef φ ε) k‖ ^ 2
      ≤ ∑ k ∈ boxF d (⌈2 / ε⌉₊ + L.length), (ε ^ n * B n) ^ 2 := Finset.sum_le_sum fun k _ => h2 k
    _ = (2 * (⌈2 / ε⌉₊ + n) + 1 : ℝ) ^ d * (ε ^ n * B n) ^ 2 := by
        rw [Finset.sum_const, card_boxF, hL, nsmul_eq_mul]; push_cast; ring
    _ ≤ ((7 + 2 * n) / ε) ^ d * (ε ^ n * B n) ^ 2 := by
        gcongr
        have hc1 : (⌈2 / ε⌉₊ : ℝ) < 2 / ε + 1 := Nat.ceil_lt_add_one (by positivity)
        have hu : (1 : ℝ) ≤ ε⁻¹ := one_le_inv_iff₀.2 ⟨hε, hε1⟩
        simp only [div_eq_mul_inv] at hc1 ⊢
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith [mul_nonneg hn (sub_nonneg.2 hu)]
    _ = (7 + 2 * n : ℝ) ^ d * B n ^ 2 * (ε ^ (2 * n) / ε ^ d) := by
        rw [div_pow, mul_pow, ← pow_mul]; field_simp; ring

end Kernel

/-! ### Geometry: `q_i`, the centred representative, the circle integral -/

section Geometry

variable {d : ℕ}

theorem mode_eI (i : Fin d) (z : Torus d) : Torus.mode (eI i) z = fourier 1 (z i) := by
  simp only [Torus.mode, UnitAddTorus.mFourier, ContinuousMap.coe_mk, eI]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · simp

theorem norm_fourier_sub_one_sq (x : ℝ) :
    ‖fourier 1 (x : UnitAddCircle) - 1‖ ^ 2 = 4 * Real.sin (Real.pi * x) ^ 2 := by
  rw [fourier_coe_apply]
  have : (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℤ) : ℂ) * (x : ℂ) / ((1 : ℝ) : ℂ)) =
      Complex.I * ((2 * Real.pi * x : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, mul_pow]
  simp only [Real.norm_eq_abs, sq_abs]
  rw [show 2 * Real.pi * x / 2 = Real.pi * x by ring]
  norm_num

theorem qf_mk (i : Fin d) (x : Euc d) : qf i (Torus.mk x) = 4 * Real.sin (Real.pi * x i) ^ 2 := by
  unfold qf
  rw [mode_eI]
  exact norm_fourier_sub_one_sq (x i)

theorem jordan (a : ℝ) (ha : |a| ≤ 1 / 2) : 2 * |a| ≤ |Real.sin (Real.pi * a)| := by
  have hpi := Real.pi_pos
  have key : ∀ b : ℝ, 0 ≤ b → b ≤ 1 / 2 → 2 * b ≤ Real.sin (Real.pi * b) := by
    intro b hb0 hb1
    have := Real.mul_le_sin (x := Real.pi * b) (by positivity) (by nlinarith)
    calc 2 * b = 2 / Real.pi * (Real.pi * b) := by field_simp
      _ ≤ _ := this
  rcases le_total 0 a with h | h
  · rw [abs_of_nonneg h] at ha ⊢
    exact (key a h ha).trans (le_abs_self _)
  · rw [abs_of_nonpos h] at ha ⊢
    have := key (-a) (by linarith) ha
    have h2 : Real.sin (Real.pi * -a) = - Real.sin (Real.pi * a) := by rw [mul_neg, Real.sin_neg]
    rw [h2] at this
    calc 2 * -a ≤ -Real.sin (Real.pi * a) := this
      _ ≤ _ := neg_le_abs _

theorem sixteen_sq_le_circle (a : ℝ) (ha : |a| ≤ 1 / 2) :
    16 * a ^ 2 ≤ 4 * Real.sin (Real.pi * a) ^ 2 := by
  have := jordan a ha
  have h2 : (2 * |a|) ^ 2 ≤ |Real.sin (Real.pi * a)| ^ 2 := pow_le_pow_left₀ (by positivity) this 2
  rw [sq_abs, mul_pow, sq_abs] at h2
  nlinarith

theorem rep_mem (z : Torus d) (i : Fin d) : 0 ≤ Torus.rep z i ∧ Torus.rep z i < 1 := by
  have := (AddCircle.equivIco (1 : ℝ) 0 (z i)).2
  simpa [Torus.rep] using this

theorem centeredRep_mk (z : Torus d) : Torus.mk (Torus.centeredRep z) = z := by
  funext i
  have h := congrFun (Torus.mk_rep z) i
  simp only [Torus.mk, Torus.centeredRep] at h ⊢
  split_ifs with hh
  · exact h
  · rw [← h]
    simp [sub_eq_add_neg]

theorem abs_centeredRep_le (z : Torus d) (i : Fin d) : |Torus.centeredRep z i| ≤ 1 / 2 := by
  have := rep_mem z i
  simp only [Torus.centeredRep]
  split_ifs with hh
  · rw [abs_le]; constructor <;> linarith [this.1]
  · rw [abs_le]; constructor <;> linarith [this.2]

theorem sixteen_le_qf (z : Torus d) (i : Fin d) : 16 * (Torus.centeredRep z i) ^ 2 ≤ qf i z := by
  conv_rhs => rw [← centeredRep_mk z]
  rw [qf_mk]
  exact sixteen_sq_le_circle _ (abs_centeredRep_le z i)

theorem tdist_sq_le (z : Torus d) : Torus.tdist z 0 ^ 2 ≤ (∑ i, qf i z) / 16 := by
  unfold Torus.tdist
  rw [sub_zero, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Finset.sum_div]
  refine Finset.sum_le_sum fun i _ => ?_
  have := sixteen_le_qf z i
  rw [Real.norm_eq_abs, sq_abs]
  linarith

theorem integral_circle_le {ε : ℝ} (hε : 0 < ε) :
    ∫ t : UnitAddCircle, (1 + ‖fourier 1 t - 1‖ ^ 2 / ε ^ 2)⁻¹ ≤ Real.pi * ε / 4 := by
  rw [← UnitAddCircle.integral_preimage (-1 / 2)]
  have hb : (4 / ε : ℝ) ≠ 0 := by positivity
  have hg := integrable_inv_one_add_mul_sq hb
  have hI := integral_univ_inv_one_add_mul_sq (4 / ε)
  calc ∫ a in Set.Ioc (-1 / 2 : ℝ) (-1 / 2 + 1), (1 + ‖fourier 1 (a : UnitAddCircle) - 1‖ ^ 2 / ε ^ 2)⁻¹
      ≤ ∫ a in Set.Ioc (-1 / 2 : ℝ) (-1 / 2 + 1), (1 + (4 / ε * a) ^ 2)⁻¹ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun a => by positivity)
          hg.integrableOn ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
        have ha' : |a| ≤ 1 / 2 := by
          rw [abs_le]; constructor <;> linarith [ha.1, ha.2]
        rw [norm_fourier_sub_one_sq]
        apply inv_anti₀ (by positivity)
        have := sixteen_sq_le_circle a ha'
        have h2 : (4 / ε * a) ^ 2 = 16 * a ^ 2 / ε ^ 2 := by field_simp; ring
        rw [h2]
        gcongr
    _ ≤ ∫ a : ℝ, (1 + (4 / ε * a) ^ 2)⁻¹ :=
        setIntegral_le_integral hg (Filter.Eventually.of_forall fun a => by positivity)
    _ = Real.pi * ε / 4 := by
        rw [hI, abs_of_pos (by positivity : (0 : ℝ) < 4 / ε)]; field_simp

end Geometry

/-! ### The weight `W_ε` and the `L¹` bounds -/

section Weights

variable {d : ℕ}

/-- `W_ε(z) = ∏_i (1 + q_i(z)/ε²)` -/
def Wf (ε : ℝ) (z : Torus d) : ℝ := ∏ i, (1 + qf i z / ε ^ 2)

theorem continuous_qf (i : Fin d) : Continuous (qf i) := by
  unfold qf
  have := (Torus.continuous_mode (eI i))
  fun_prop

theorem continuous_Wf (ε : ℝ) : Continuous (Wf (d := d) ε) := by
  unfold Wf
  exact continuous_finsetProd _ fun i _ => by have := continuous_qf i; fun_prop

theorem Wf_pos {ε : ℝ} (z : Torus d) : 0 < Wf ε z := by
  unfold Wf
  refine Finset.prod_pos fun i _ => ?_
  have : 0 ≤ qf i z := by unfold qf; positivity
  positivity

theorem continuous_trig {n : ℕ} {c : Lattice d → ℂ} (hc : IsTrigPoly n c) : Continuous (trig c) := by
  have : trig c = fun z => ∑ k ∈ boxF d n, c k * Torus.mode k z := funext (trig_eq_sum hc)
  rw [this]
  exact continuous_finsetSum _ fun k _ => (continuous_const.mul (Torus.continuous_mode k))

theorem continuous_kern {φ : Euc d → ℂ} (hsupp : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0) {ε : ℝ} (hε : 0 < ε) :
    Continuous (kern φ ε) := continuous_trig (isTrigPoly_kcoef hsupp hε)

theorem integral_Wf_inv_le {ε : ℝ} (hε : 0 < ε) :
    ∫ z : Torus d, (Wf ε z)⁻¹ ≤ (Real.pi * ε / 4) ^ d := by
  have h1 : ∀ z : Torus d, (Wf ε z)⁻¹ = ∏ i, (1 + ‖fourier 1 (z i) - 1‖ ^ 2 / ε ^ 2)⁻¹ := by
    intro z
    unfold Wf
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    unfold qf; rw [mode_eI]
  simp_rw [h1]
  have h2 := integral_fintype_prod_eq_prod (ι := Fin d) (𝕜 := ℝ)
    (E := fun _ => UnitAddCircle) (μ := fun _ => (volume : Measure UnitAddCircle))
    (fun _ t => (1 + ‖fourier 1 t - 1‖ ^ 2 / ε ^ 2)⁻¹)
  have h3 : (volume : Measure (Torus d)) = Measure.pi fun _ => (volume : Measure UnitAddCircle) := rfl
  rw [h3, h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact pow_le_pow_left₀ (integral_nonneg fun t => by positivity) (integral_circle_le hε) d


theorem Wf_mul_expand (ε : ℝ) (pre : List (Fin d)) (z : Torus d) (x : ℝ) :
    (pre.map fun i => qf i z).prod * (Wf ε z * x) =
      ∑ γ ∈ (Finset.univ : Finset (Fin d)).powerset,
        ((ε ^ 2)⁻¹) ^ γ.card * ((pre ++ γ.toList).map fun i => qf i z).prod * x := by
  unfold Wf
  rw [Finset.prod_one_add, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [List.map_append, List.prod_append, Finset.prod_map_toList, Finset.prod_div_distrib,
    Finset.prod_const, ← inv_pow]
  ring


theorem integrable_of_continuous_torus {f : Torus d → ℝ} (hf : Continuous f) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem measurable_rep_coord (i : Fin d) : Measurable fun z : Torus d => Torus.rep z i := by
  have h1 : Measurable fun t : UnitAddCircle => ((AddCircle.equivIco (1 : ℝ) 0 t : Set.Ico (0 : ℝ) (0 + 1)) : ℝ) :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable
  exact h1.comp (measurable_pi_apply i)

theorem measurable_tdist_zero : Measurable fun z : Torus d => Torus.tdist z 0 := by
  have : (fun z : Torus d => Torus.tdist z 0) = fun z =>
      Real.sqrt (∑ i, (if Torus.rep z i ≤ 1 / 2 then Torus.rep z i else Torus.rep z i - 1) ^ 2) := by
    funext z
    unfold Torus.tdist Torus.centeredRep
    rw [sub_zero, EuclideanSpace.norm_eq]
    simp [Real.norm_eq_abs, sq_abs]
  rw [this]
  refine Measurable.sqrt (Finset.measurable_sum _ fun i _ => ?_)
  refine Measurable.pow_const ?_ 2
  exact Measurable.ite (measurableSet_le (measurable_rep_coord i) measurable_const)
    (measurable_rep_coord i) ((measurable_rep_coord i).sub_const 1)

theorem amgm_pt (x W lam : ℝ) (_hx : 0 ≤ x) (hW : 0 < W) (hlam : 0 < lam) :
    x ≤ lam / 2 * (W * x ^ 2) + (1 / (2 * lam)) * W⁻¹ := by
  have hu : 0 < lam * W := mul_pos hlam hW
  have : lam * W * x ^ 2 + (lam * W)⁻¹ - 2 * x = (lam * W * x - 1) ^ 2 / (lam * W) := by
    field_simp; ring
  have h2 : 0 ≤ (lam * W * x - 1) ^ 2 / (lam * W) := by positivity
  have h3 : (lam * W)⁻¹ = 2 * (1 / (2 * lam)) * W⁻¹ := by field_simp
  nlinarith

/-- Weighted second moments with the weight `W_ε`. -/
theorem kern_W_moment {φ : Euc d → ℂ} (hφ : ContDiff ℝ ∞ φ) (hsupp : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0)
    (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ pre : List (Fin d), pre.length = m → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∫ z, (pre.map fun i => qf i z).prod * (Wf ε z * ‖kern φ ε z‖ ^ 2) ≤ C * (ε ^ (2 * m) / ε ^ d) := by
  choose Cn hCn0 hCn using fun n => kern_moment hφ hsupp n
  refine ⟨∑ γ ∈ (Finset.univ : Finset (Fin d)).powerset, Cn (m + γ.card),
    Finset.sum_nonneg fun γ _ => hCn0 _, fun pre hpre ε hε hε1 => ?_⟩
  simp_rw [Wf_mul_expand]
  have hcont : ∀ (L : List (Fin d)), Continuous fun z : Torus d => (L.map fun i => qf i z).prod := by
    intro L
    induction L with
    | nil => simpa using continuous_const
    | cons i L ih =>
      simp only [List.map_cons, List.prod_cons]
      exact (continuous_qf i).mul ih
  have hint : ∀ γ : Finset (Fin d), Integrable fun z : Torus d =>
      ((ε ^ 2)⁻¹) ^ γ.card * ((pre ++ γ.toList).map fun i => qf i z).prod * ‖kern φ ε z‖ ^ 2 := by
    intro γ
    refine integrable_of_continuous_torus ?_
    have := continuous_kern hsupp hε
    exact (continuous_const.mul (hcont _)).mul (this.norm.pow 2)
  rw [integral_finsetSum _ fun γ _ => hint γ, Finset.sum_mul]
  refine Finset.sum_le_sum fun γ _ => ?_
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  have := hCn (m + γ.card) ((pre ++ γ.toList)) (by simp [hpre]) ε hε hε1
  calc ((ε ^ 2)⁻¹) ^ γ.card * ∫ z, ((pre ++ γ.toList).map fun i => qf i z).prod * ‖kern φ ε z‖ ^ 2
      ≤ ((ε ^ 2)⁻¹) ^ γ.card * (Cn (m + γ.card) * (ε ^ (2 * (m + γ.card)) / ε ^ d)) := by
        gcongr
    _ = Cn (m + γ.card) * (ε ^ (2 * m) / ε ^ d) := by
        rw [mul_add, pow_add, ← inv_pow]
        have : ε ^ (2 * γ.card) = (ε ^ 2) ^ γ.card := by rw [pow_mul]
        rw [this]
        have hne : (ε ^ 2) ^ γ.card ≠ 0 := by positivity
        field_simp
        rw [div_pow, one_pow]; field_simp


/-- (K0) `‖K_ε‖_{L¹} ≤ C`. -/
theorem kern_L1_bound {φ : Euc d → ℂ} (hφ : ContDiff ℝ ∞ φ) (hsupp : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      Integrable (fun z => ‖kern φ ε z‖) ∧ ∫ z, ‖kern φ ε z‖ ≤ C := by
  obtain ⟨C0, hC0, h0⟩ := kern_W_moment hφ hsupp 0
  refine ⟨C0 / 2 + (Real.pi / 4) ^ d / 2, by positivity, fun ε hε hε1 => ?_⟩
  have hK := continuous_kern hsupp hε
  have hlam : 0 < ε ^ d := by positivity
  have hI1 : Integrable fun z : Torus d => ‖kern φ ε z‖ := integrable_of_continuous_torus hK.norm
  refine ⟨hI1, ?_⟩
  have hI2 : Integrable fun z : Torus d => Wf ε z * ‖kern φ ε z‖ ^ 2 :=
    integrable_of_continuous_torus ((continuous_Wf ε).mul (hK.norm.pow 2))
  have hI3 : Integrable fun z : Torus d => (Wf ε z)⁻¹ :=
    integrable_of_continuous_torus ((continuous_Wf ε).inv₀ fun z => (Wf_pos z).ne')
  calc ∫ z, ‖kern φ ε z‖
      ≤ ∫ z, (ε ^ d / 2 * (Wf ε z * ‖kern φ ε z‖ ^ 2) + (1 / (2 * ε ^ d)) * (Wf ε z)⁻¹) :=
        integral_mono hI1 ((hI2.const_mul _).add (hI3.const_mul _))
          fun z => amgm_pt _ _ _ (norm_nonneg _) (Wf_pos z) hlam
    _ = ε ^ d / 2 * (∫ z, Wf ε z * ‖kern φ ε z‖ ^ 2) + (1 / (2 * ε ^ d)) * ∫ z : Torus d, (Wf ε z)⁻¹ := by
        rw [integral_add (hI2.const_mul _) (hI3.const_mul _), integral_const_mul, integral_const_mul]
    _ ≤ ε ^ d / 2 * (C0 * (ε ^ (2 * 0) / ε ^ d)) + (1 / (2 * ε ^ d)) * (Real.pi * ε / 4) ^ d := by
        gcongr
        · simpa using h0 [] rfl ε hε hε1
        · exact integral_Wf_inv_le hε
    _ = C0 / 2 + (Real.pi / 4) ^ d / 2 := by
        rw [show Real.pi * ε / 4 = Real.pi / 4 * ε by ring, mul_pow]
        simp only [mul_zero, pow_zero]
        field_simp

/-- (K1) `∫ |z| |K_ε(z)| dz ≤ C ε`. -/
theorem kern_L1_moment_bound {φ : Euc d → ℂ} (hφ : ContDiff ℝ ∞ φ) (hsupp : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      Integrable (fun z => Torus.tdist z 0 * ‖kern φ ε z‖) ∧
        ∫ z, Torus.tdist z 0 * ‖kern φ ε z‖ ≤ C * ε := by
  obtain ⟨C1, hC1, h1⟩ := kern_W_moment hφ hsupp 1
  refine ⟨(d : ℝ) * C1 / 32 + (Real.pi / 4) ^ d / 2, by positivity, fun ε hε hε1 => ?_⟩
  have hK := continuous_kern hsupp hε
  have hlam : 0 < ε ^ d / ε := by positivity
  have hI2 : Integrable fun z : Torus d => (∑ j, qf j z) / 16 * (Wf ε z * ‖kern φ ε z‖ ^ 2) := by
    refine integrable_of_continuous_torus ?_
    have : Continuous fun z : Torus d => ∑ j, qf j z :=
      continuous_finsetSum _ fun j _ => continuous_qf j
    exact (this.div_const 16).mul ((continuous_Wf ε).mul (hK.norm.pow 2))
  have hI3 : Integrable fun z : Torus d => (Wf ε z)⁻¹ :=
    integrable_of_continuous_torus ((continuous_Wf ε).inv₀ fun z => (Wf_pos z).ne')
  have hpt : ∀ z : Torus d, Torus.tdist z 0 * ‖kern φ ε z‖ ≤
      ε ^ d / ε / 2 * ((∑ j, qf j z) / 16 * (Wf ε z * ‖kern φ ε z‖ ^ 2)) +
        (1 / (2 * (ε ^ d / ε))) * (Wf ε z)⁻¹ := by
    intro z
    have h1 := amgm_pt (Torus.tdist z 0 * ‖kern φ ε z‖) (Wf ε z) (ε ^ d / ε)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Wf_pos z) hlam
    have key : Wf ε z * (Torus.tdist z 0 * ‖kern φ ε z‖) ^ 2 ≤
        (∑ j, qf j z) / 16 * (Wf ε z * ‖kern φ ε z‖ ^ 2) := by
      have := tdist_sq_le z
      have hW := (Wf_pos (ε := ε) z).le
      calc Wf ε z * (Torus.tdist z 0 * ‖kern φ ε z‖) ^ 2
          = Torus.tdist z 0 ^ 2 * (Wf ε z * ‖kern φ ε z‖ ^ 2) := by ring
        _ ≤ _ := by gcongr
    refine h1.trans ?_
    have := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ ε ^ d / ε / 2)
    linarith
  have hbd : Integrable (fun z : Torus d => ε ^ d / ε / 2 * ((∑ j, qf j z) / 16 * (Wf ε z * ‖kern φ ε z‖ ^ 2)) +
        (1 / (2 * (ε ^ d / ε))) * (Wf ε z)⁻¹) := (hI2.const_mul _).add (hI3.const_mul _)
  have hmeas : AEStronglyMeasurable (fun z : Torus d => Torus.tdist z 0 * ‖kern φ ε z‖) volume :=
    (measurable_tdist_zero.mul hK.norm.measurable).aestronglyMeasurable
  have hint : Integrable (fun z : Torus d => Torus.tdist z 0 * ‖kern φ ε z‖) := by
    refine Integrable.mono' hbd hmeas ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (by unfold Torus.tdist; positivity) (norm_nonneg _))]
    exact hpt z
  refine ⟨hint, ?_⟩
  have hsum : ∫ z : Torus d, (∑ j, qf j z) / 16 * (Wf ε z * ‖kern φ ε z‖ ^ 2) ≤
      (d : ℝ) / 16 * (C1 * (ε ^ 2 / ε ^ d)) := by
    have : ∀ z : Torus d, (∑ j, qf j z) / 16 * (Wf ε z * ‖kern φ ε z‖ ^ 2) =
        1 / 16 * ∑ j, ([j].map fun i => qf i z).prod * (Wf ε z * ‖kern φ ε z‖ ^ 2) := by
      intro z
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [← Finset.sum_mul]; ring
    simp_rw [this]
    have hj : ∀ j : Fin d, Integrable fun z : Torus d =>
        ([j].map fun i => qf i z).prod * (Wf ε z * ‖kern φ ε z‖ ^ 2) := by
      intro j
      refine integrable_of_continuous_torus ?_
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      exact (continuous_qf j).mul ((continuous_Wf ε).mul (hK.norm.pow 2))
    rw [integral_const_mul, integral_finsetSum _ fun j _ => hj j]
    calc 1 / 16 * ∑ j, ∫ z : Torus d, ([j].map fun i => qf i z).prod * (Wf ε z * ‖kern φ ε z‖ ^ 2)
        ≤ 1 / 16 * ∑ _j : Fin d, C1 * (ε ^ (2 * 1) / ε ^ d) := by
          gcongr with j
          exact h1 [j] rfl ε hε hε1
      _ = (d : ℝ) / 16 * (C1 * (ε ^ 2 / ε ^ d)) := by simp; ring
  calc ∫ z, Torus.tdist z 0 * ‖kern φ ε z‖
      ≤ ∫ z, (ε ^ d / ε / 2 * ((∑ j, qf j z) / 16 * (Wf ε z * ‖kern φ ε z‖ ^ 2)) +
        (1 / (2 * (ε ^ d / ε))) * (Wf ε z)⁻¹) :=
        integral_mono hint hbd hpt
    _ = ε ^ d / ε / 2 * (∫ z, (∑ j, qf j z) / 16 * (Wf ε z * ‖kern φ ε z‖ ^ 2)) +
          (1 / (2 * (ε ^ d / ε))) * ∫ z : Torus d, (Wf ε z)⁻¹ := by
        rw [integral_add (hI2.const_mul _) (hI3.const_mul _), integral_const_mul, integral_const_mul]
    _ ≤ ε ^ d / ε / 2 * ((d : ℝ) / 16 * (C1 * (ε ^ 2 / ε ^ d))) +
          (1 / (2 * (ε ^ d / ε))) * (Real.pi * ε / 4) ^ d := by
        gcongr
        exact integral_Wf_inv_le hε
    _ = ((d : ℝ) * C1 / 32 + (Real.pi / 4) ^ d / 2) * ε := by
        rw [show Real.pi * ε / 4 = Real.pi / 4 * ε by ring, mul_pow]
        field_simp
        ring


end Weights

/-! ### (L) Lipschitz bound from the supremum of the derivative -/

section Lipschitz

variable {d : ℕ}

theorem bddAbove_norm_fderiv_lift {a : Torus d → ℝ} (ha : Torus.IsCk 1 a) :
    BddAbove (Set.range fun z : Euc d => ‖fderiv ℝ (Torus.lift a) z‖) := by
  have := Torus.bddAbove_norm_iteratedFDeriv_lift 1 a (by simpa [Torus.IsCk] using ha)
  simpa using this

theorem norm_fderiv_lift_le_iSup {a : Torus d → ℝ} (ha : Torus.IsCk 1 a) (z : Euc d) :
    ‖fderiv ℝ (Torus.lift a) z‖ ≤ ⨆ z : Euc d, ‖fderiv ℝ (Torus.lift a) z‖ :=
  le_ciSup (bddAbove_norm_fderiv_lift ha) z

theorem mk_add (x y : Euc d) : Torus.mk (x + y) = Torus.mk x + Torus.mk y := by
  funext i
  simp [Torus.mk]

/-- (L) Lipschitz bound: `|a x - a y| ≤ ‖∇a‖_∞ · tdist x y`. -/
theorem abs_sub_le_iSup_mul_tdist {a : Torus d → ℝ} (ha : Torus.IsCk 1 a) (x y : Torus d) :
    |a x - a y| ≤ (⨆ z : Euc d, ‖fderiv ℝ (Torus.lift a) z‖) * Torus.tdist x y := by
  have hd : Differentiable ℝ (Torus.lift a) := (ha.differentiable (by norm_num))
  set p := Torus.rep y
  set v := Torus.centeredRep (x - y)
  have h1 : Torus.lift a p = a y := by simp [Torus.lift, p, Torus.mk_rep]
  have h2 : Torus.lift a (v + p) = a x := by
    simp only [Torus.lift, Function.comp]
    rw [mk_add, Torus.mk_rep, centeredRep_mk]; congr 1; abel
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := Torus.lift a) (s := Set.univ)
    (C := ⨆ z : Euc d, ‖fderiv ℝ (Torus.lift a) z‖) (fun z _ => hd z)
    (fun z _ => norm_fderiv_lift_le_iSup ha z) convex_univ (Set.mem_univ p) (Set.mem_univ (v + p))
  rw [h1, h2, Real.norm_eq_abs] at this
  simpa [Torus.tdist, v] using this


end Lipschitz

/-! ### (Y) Young/Schur inequality on the torus -/

section Young

variable {d : ℕ}


instance instNegInvariantVolumeTorus (d : ℕ) : (volume : Measure (Torus d)).IsNegInvariant := by
  have : ∀ _i : Fin d, (volume : Measure UnitAddCircle).IsNegInvariant := fun _ => inferInstance
  exact Measure.pi.isNegInvariant (fun _ : Fin d => (volume : Measure UnitAddCircle))

/-- (Y) Young/Schur: for a bounded a.e.-measurable `ρ ≥ 0` and `G ≥ 0` in `L²`, the convolution
`x ↦ ∫ ρ(x-y) G(y) dy` is in `L²` with `‖ρ * G‖² ≤ (∫ρ)² ‖G‖²`. -/
theorem young_l2 {ρ G : Torus d → ℝ} (hρm : AEStronglyMeasurable ρ volume) (hρ0 : ∀ z, 0 ≤ ρ z)
    {M : ℝ} (hM : ∀ z, ρ z ≤ M) (hGm : AEStronglyMeasurable G volume) (hG0 : ∀ z, 0 ≤ G z)
    (hG : MemLp G 2 volume) :
    MemLp (fun x => ∫ y, ρ (x - y) * G y) 2 volume ∧
      ∫ x, (∫ y, ρ (x - y) * G y) ^ 2 ≤ (∫ z, ρ z) ^ 2 * ∫ y, G y ^ 2 := by
  have hM0 : 0 ≤ M := (hρ0 0).trans (hM 0)
  set m := ∫ z, ρ z with hm
  have hρi : Integrable ρ := Integrable.of_bound hρm M
    (Filter.Eventually.of_forall fun z => by rw [Real.norm_of_nonneg (hρ0 z)]; exact hM z)
  have hG1 : Integrable G := hG.integrable one_le_two
  have hG2 : Integrable (fun y => G y ^ 2) := hG.integrable_sq
  have hm0 : 0 ≤ m := integral_nonneg hρ0
  -- measurability of the integrands
  have hρ_sub : ∀ x : Torus d, AEStronglyMeasurable (fun y => ρ (x - y)) volume := fun x =>
    hρm.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left_of_right_invariant volume x)
  have ha : ∀ x, Integrable fun y => ρ (x - y) := fun x => hρi.comp_sub_left x
  have hb : ∀ x, Integrable fun y => ρ (x - y) * G y := fun x => by
    refine Integrable.mono' (hG1.const_mul M) ((hρ_sub x).mul hGm) ?_
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (hρ0 _) (hG0 _))]
    exact mul_le_mul_of_nonneg_right (hM _) (hG0 _)
  have hc : ∀ x, Integrable fun y => ρ (x - y) * G y ^ 2 := fun x => by
    refine Integrable.mono' (hG2.const_mul M) ((hρ_sub x).mul (hGm.pow 2)) ?_
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (hρ0 _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (hM _) (sq_nonneg _)
  have hmx : ∀ x : Torus d, ∫ y, ρ (x - y) = m := fun x => integral_sub_left_eq_self ρ volume x
  -- pointwise Cauchy–Schwarz
  have hCS : ∀ x, (∫ y, ρ (x - y) * G y) ^ 2 ≤ m * ∫ y, ρ (x - y) * G y ^ 2 := by
    intro x
    have key : ∀ t : ℝ, 0 ≤ m * (t * t) + (-2 * (∫ y, ρ (x - y) * G y)) * t + ∫ y, ρ (x - y) * G y ^ 2 := by
      intro t
      have h0 : 0 ≤ ∫ y, ρ (x - y) * (t - G y) ^ 2 :=
        integral_nonneg fun y => mul_nonneg (hρ0 _) (sq_nonneg _)
      have : ∫ y, ρ (x - y) * (t - G y) ^ 2 =
          t ^ 2 * m - 2 * t * (∫ y, ρ (x - y) * G y) + ∫ y, ρ (x - y) * G y ^ 2 := by
        have i1 : Integrable fun y => t ^ 2 * ρ (x - y) - 2 * t * (ρ (x - y) * G y) :=
          ((ha x).const_mul _).sub ((hb x).const_mul _)
        have e0 : ∫ y, ρ (x - y) * (t - G y) ^ 2 =
            ∫ y, (t ^ 2 * ρ (x - y) - 2 * t * (ρ (x - y) * G y) + ρ (x - y) * G y ^ 2) := by
          congr 1; funext y; ring
        have e1 : ∫ y, (t ^ 2 * ρ (x - y) - 2 * t * (ρ (x - y) * G y) + ρ (x - y) * G y ^ 2) =
            (∫ y, (t ^ 2 * ρ (x - y) - 2 * t * (ρ (x - y) * G y))) + ∫ y, ρ (x - y) * G y ^ 2 :=
          integral_add i1 (hc x)
        have e2 : ∫ y, (t ^ 2 * ρ (x - y) - 2 * t * (ρ (x - y) * G y)) =
            (∫ y, t ^ 2 * ρ (x - y)) - ∫ y, 2 * t * (ρ (x - y) * G y) :=
          integral_sub ((ha x).const_mul _) ((hb x).const_mul _)
        have e3 : ∫ y, t ^ 2 * ρ (x - y) = t ^ 2 * ∫ y, ρ (x - y) := integral_const_mul _ _
        have e4 : ∫ y, 2 * t * (ρ (x - y) * G y) = 2 * t * ∫ y, ρ (x - y) * G y :=
          integral_const_mul _ _
        rw [hmx] at e3
        linarith
      rw [this] at h0
      have e : m * (t * t) + (-2 * (∫ y, ρ (x - y) * G y)) * t + ∫ y, ρ (x - y) * G y ^ 2 =
          t ^ 2 * m - 2 * t * (∫ y, ρ (x - y) * G y) + ∫ y, ρ (x - y) * G y ^ 2 := by ring
      rw [e]; exact h0
    have := discrim_le_zero key
    unfold discrim at this
    nlinarith
  -- Fubini
  have hF_meas : AEStronglyMeasurable (fun p : Torus d × Torus d => ρ (p.1 - p.2) * G p.2 ^ 2)
      (volume.prod volume) :=
    (hρm.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant (volume : Measure (Torus d)) volume)).mul
      ((hGm.pow 2).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  have hF_int : Integrable (fun p : Torus d × Torus d => ρ (p.1 - p.2) * G p.2 ^ 2)
      (volume.prod volume) := by
    rw [integrable_prod_iff' hF_meas]
    refine ⟨Filter.Eventually.of_forall fun y => (hρi.comp_sub_right y).mul_const (G y ^ 2), ?_⟩
    refine (hG2.const_mul m).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only
    have : ∀ x : Torus d, ‖ρ (x - y) * G y ^ 2‖ = ρ (x - y) * G y ^ 2 := fun x => by
      rw [Real.norm_of_nonneg (mul_nonneg (hρ0 _) (sq_nonneg _))]
    simp_rw [this]
    rw [integral_mul_const, integral_sub_right_eq_self ρ y]
  have hB_int : Integrable (fun x : Torus d => ∫ y, ρ (x - y) * G y ^ 2) :=
    hF_int.integral_prod_left
  have hB_val : ∫ x : Torus d, (∫ y, ρ (x - y) * G y ^ 2) = m * ∫ y, G y ^ 2 := by
    rw [integral_integral_swap hF_int]
    have : ∀ y : Torus d, ∫ x : Torus d, ρ (x - y) * G y ^ 2 = m * G y ^ 2 := fun y => by
      rw [integral_mul_const, integral_sub_right_eq_self ρ y]
    simp_rw [this]
    rw [integral_const_mul]
  -- measurability of the convolution
  have hA_meas : AEStronglyMeasurable (fun x : Torus d => ∫ y, ρ (x - y) * G y) volume := by
    have : AEStronglyMeasurable (fun p : Torus d × Torus d => ρ (p.1 - p.2) * G p.2)
        (volume.prod volume) :=
      (hρm.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant (volume : Measure (Torus d)) volume)).mul
        (hGm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
    exact this.integral_prod_right'
  have hA2_int : Integrable (fun x : Torus d => (∫ y, ρ (x - y) * G y) ^ 2) := by
    refine Integrable.mono' (hB_int.const_mul m) (hA_meas.pow 2) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hCS x
  refine ⟨(memLp_two_iff_integrable_sq hA_meas).2 hA2_int, ?_⟩
  calc ∫ x : Torus d, (∫ y, ρ (x - y) * G y) ^ 2
      ≤ ∫ x : Torus d, m * ∫ y, ρ (x - y) * G y ^ 2 := integral_mono hA2_int (hB_int.const_mul m) hCS
    _ = (∫ z, ρ z) ^ 2 * ∫ y, G y ^ 2 := by
        rw [integral_const_mul, hB_val]; ring

end Young

/-! ### Data for applying (Y) to `tdist · |K_ε|` -/

section YoungData

variable {d : ℕ}

theorem qf_le_four (i : Fin d) (z : Torus d) : qf i z ≤ 4 := by
  unfold qf
  have h1 : ‖Torus.mode (eI i) z - 1‖ ≤ 2 := by
    calc ‖Torus.mode (eI i) z - 1‖ ≤ ‖Torus.mode (eI i) z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [Torus.norm_mode]; norm_num
  nlinarith [norm_nonneg (Torus.mode (eI i) z - 1)]

theorem tdist_zero_le (z : Torus d) : Torus.tdist z 0 ≤ d := by
  have h1 := tdist_sq_le z
  have h2 : (∑ i, qf i z) ≤ 4 * d := by
    calc (∑ i, qf i z) ≤ ∑ _i : Fin d, (4 : ℝ) := Finset.sum_le_sum fun i _ => qf_le_four i z
      _ = 4 * d := by simp; ring
  have h3 : Torus.tdist z 0 ^ 2 ≤ d / 4 := by linarith
  have h0 : 0 ≤ Torus.tdist z 0 := by unfold Torus.tdist; positivity
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp at h3; nlinarith
  · have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith

theorem aestronglyMeasurable_tdist_mul_kern {φ : Euc d → ℂ} (hsupp : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0)
    {ε : ℝ} (hε : 0 < ε) :
    AEStronglyMeasurable (fun z : Torus d => Torus.tdist z 0 * ‖kern φ ε z‖) volume :=
  (measurable_tdist_zero.mul (continuous_kern hsupp hε).norm.measurable).aestronglyMeasurable

theorem exists_bound_kern {φ : Euc d → ℂ} (hsupp : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0)
    {ε : ℝ} (hε : 0 < ε) : ∃ M : ℝ, ∀ z : Torus d, ‖kern φ ε z‖ ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn
    (continuous_kern hsupp hε).continuousOn
  exact ⟨C, fun z => hC z (Set.mem_univ z)⟩

theorem exists_bound_tdist_mul_kern {φ : Euc d → ℂ} (hsupp : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0)
    {ε : ℝ} (hε : 0 < ε) : ∃ M : ℝ, ∀ z : Torus d, Torus.tdist z 0 * ‖kern φ ε z‖ ≤ M := by
  obtain ⟨M, hM⟩ := exists_bound_kern hsupp hε
  refine ⟨d * M, fun z => ?_⟩
  have h0 : 0 ≤ Torus.tdist z 0 := by unfold Torus.tdist; positivity
  exact mul_le_mul (tdist_zero_le z) (hM z) (norm_nonneg _) (Nat.cast_nonneg d)

end YoungData
end Kern
end HRS.PDE
