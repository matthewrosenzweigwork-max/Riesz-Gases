import HRS.Kernel.SymbolClass
import HRS.Kernel.LatticeSums
import HRS.Kernel.Riesz

/-!
# Higher-derivative bounds for the mollified Riesz kernel (packet Q39, Lemma C.2)

For `g_δ(x) = ∑_k ĝ(k) χ(δk)² cos(2πk·x)` we bound `‖D^n g_δ‖` by a pure Fourier argument
(no convolution representation, no heat kernel): the `n`-th derivative applied to `v_1,…,v_n` is
`(2πi)^n ∑_k c_v(k) e_k`, `c_v(k) = ĝ(k) χ(δk)² ∏_j ⟨v_j,k⟩`; split `c_v = c_low + c_high` with the
radial cutoff `χ(ρk)` at the scale `ρ = min(1, |x|)`; the low part is bounded by the trivial lattice
sum `∑_{|k|≲1/ρ} |k|^{s+n-d} ≲ ρ^{-s-n}`, the high part by `N` summation-by-parts steps
(finite differences of the symbol, `Gsym_fdiffs_bound`) and the tail sum
`∑_{|k|≳1/ρ} |k|^{s+n-d-N} ≲ ρ^{N-s-n}`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators ComplexConjugate ContDiff

namespace HRS
namespace HDB

open HRS.PDE HRS.PDE.Kern

variable {d : ℕ}

/-- the constant in `ĝ(k) = κ ‖k‖^{s-d}` -/
def kapC (d : ℕ) (s : ℝ) : ℝ := rieszConst d s * (2 * Real.pi) ^ (s - d)

theorem rieszCoeff_eq {s : ℝ} (hsd : s < d) (k : Lattice d) :
    rieszCoeff d s k = kapC d s * ‖Lattice.toEuc k‖ ^ (s - d) := by
  unfold rieszCoeff kapC
  by_cases hk : k = 0
  · subst hk
    have h0 : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
    rw [if_pos rfl, h0, norm_zero, Real.zero_rpow (by linarith)]
    simp
  · have he : Lattice.enorm k = ‖Lattice.toEuc k‖ := rfl
    rw [if_neg hk, he, Real.mul_rpow (by positivity) (norm_nonneg _)]
    ring

/-- the coefficient of `e_k` in `D^n g_δ (v_1,…,v_n) / (2πi)^n` -/
def cV (d : ℕ) (s : ℝ) (χ : Euc d → ℝ) (δ : ℝ) {n : ℕ} (v : Fin n → Euc d) (k : Lattice d) : ℝ :=
  rieszCoeff d s k * χ (δ • Lattice.toEuc k) ^ 2 * ∏ j, inner ℝ (v j) (Lattice.toEuc k)

theorem isTrigPoly_of_enorm_lt {f : Lattice d → ℂ} {R : ℝ}
    (hf : ∀ k, f k ≠ 0 → Lattice.enorm k < R) : IsTrigPoly ⌈R⌉₊ f := by
  intro k hk i
  have h1 := hf k hk
  have h2 : ‖(Lattice.toEuc k) i‖ ≤ ‖Lattice.toEuc k‖ := PiLp.norm_apply_le _ i
  have h3 : ‖(Lattice.toEuc k) i‖ = |(k i : ℝ)| := by simp [Lattice.toEuc]
  have h4 : |(k i : ℝ)| ≤ ⌈R⌉₊ := by
    have := Nat.le_ceil R
    unfold Lattice.enorm at h1
    linarith
  have h5 : |k i| ≤ (⌈R⌉₊ : ℤ) := by
    have : ((|k i| : ℤ) : ℝ) ≤ (((⌈R⌉₊ : ℕ) : ℤ) : ℝ) := by push_cast; exact h4
    exact_mod_cast this
  exact h5


theorem norm_trig_le {n : ℕ} {c : Lattice d → ℂ} (hc : IsTrigPoly n c) (z : Torus d) :
    ‖trig c z‖ ≤ ∑ k ∈ boxF d n, ‖c k‖ := by
  rw [trig_eq_sum hc]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
  rw [norm_mul, Torus.norm_mode, mul_one]

variable {χ : Euc d → ℝ} {s : ℝ}

theorem abs_prod_inner_le {n : ℕ} (v : Fin n → Euc d) (hv : ∀ j, ‖v j‖ ≤ 1) (ξ : Euc d) :
    |∏ j, inner ℝ (v j) ξ| ≤ ‖ξ‖ ^ n := by
  rw [← Real.norm_eq_abs, norm_prod]
  calc ∏ j, ‖inner ℝ (v j) ξ‖ ≤ ∏ _j : Fin n, ‖ξ‖ := by
        refine Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j _ => ?_
        calc ‖inner ℝ (v j) ξ‖ ≤ ‖v j‖ * ‖ξ‖ := norm_inner_le_norm _ _
          _ ≤ 1 * ‖ξ‖ := by gcongr; exact hv j
          _ = ‖ξ‖ := one_mul _
    _ = ‖ξ‖ ^ n := by simp

/-- the weights `‖k‖^{σ-d}` (zero at `k = 0`) -/
def gW (d : ℕ) (σ : ℝ) (k : Lattice d) : ℝ := if k = 0 then 0 else Lattice.enorm k ^ (σ - (d : ℝ))

theorem toEuc_ne_zero {k : Lattice d} (hk : k ≠ 0) : Lattice.toEuc k ≠ 0 := by
  intro h
  apply hk
  funext i
  have := congrArg (fun z : Euc d => z i) h
  simpa [Lattice.toEuc] using this

theorem abs_cV_le (hsd : s < d) (h0 : ∀ ξ, 0 ≤ χ ξ ∧ χ ξ ≤ 1) (δ : ℝ) {n : ℕ}
    (v : Fin n → Euc d) (hv : ∀ j, ‖v j‖ ≤ 1) (k : Lattice d) :
    |cV d s χ δ v k| ≤ |kapC d s| * gW d (s + n) k := by
  by_cases hk : k = 0
  · subst hk
    have h0' : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
    simp [cV, gW, rieszCoeff]
  · have hkn : 0 < ‖Lattice.toEuc k‖ := norm_pos_iff.mpr (toEuc_ne_zero hk)
    unfold cV gW
    rw [if_neg hk, rieszCoeff_eq hsd, abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hkn.le _)]
    have h1 : |χ (δ • Lattice.toEuc k) ^ 2| ≤ 1 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      have := h0 (δ • Lattice.toEuc k)
      nlinarith [this.1, this.2]
    have h2 := abs_prod_inner_le v hv (Lattice.toEuc k)
    have h3 : Lattice.enorm k ^ (s + (n : ℝ) - (d : ℝ)) = ‖Lattice.toEuc k‖ ^ (s - d) * ‖Lattice.toEuc k‖ ^ n := by
      have he : Lattice.enorm k = ‖Lattice.toEuc k‖ := rfl
      rw [he, show s + (n : ℝ) - d = (s - d) + n by ring, Real.rpow_add hkn, Real.rpow_natCast]
    rw [h3]
    have hp : 0 ≤ ‖Lattice.toEuc k‖ ^ (s - d) := Real.rpow_nonneg hkn.le _
    calc |kapC d s| * ‖Lattice.toEuc k‖ ^ (s - d) * |χ (δ • Lattice.toEuc k) ^ 2| *
          |∏ j, inner ℝ (v j) (Lattice.toEuc k)|
        ≤ |kapC d s| * ‖Lattice.toEuc k‖ ^ (s - d) * 1 * ‖Lattice.toEuc k‖ ^ n := by
          gcongr
      _ = |kapC d s| * (‖Lattice.toEuc k‖ ^ (s - d) * ‖Lattice.toEuc k‖ ^ n) := by ring

/-- the low-frequency part of the coefficients -/
def cLow (d : ℕ) (s : ℝ) (χ : Euc d → ℝ) (δ ρ : ℝ) {n : ℕ} (v : Fin n → Euc d) (k : Lattice d) : ℝ :=
  cV d s χ δ v k * χ (ρ • Lattice.toEuc k)

theorem cLow_support (h2 : ∀ ξ : Euc d, 2 ≤ ‖ξ‖ → χ ξ = 0) {δ ρ : ℝ} (hρ : 0 < ρ) {n : ℕ}
    (v : Fin n → Euc d) (k : Lattice d) (hk : ((cLow d s χ δ ρ v k : ℝ) : ℂ) ≠ 0) :
    Lattice.enorm k < 2 / ρ := by
  by_contra hcon
  push Not at hcon
  apply hk
  have : χ (ρ • Lattice.toEuc k) = 0 := by
    apply h2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    rw [div_le_iff₀ hρ] at hcon
    unfold Lattice.enorm at hcon
    linarith
  simp [cLow, this]

theorem trig_cLow_le (hsd : s < d) (h0 : ∀ ξ, 0 ≤ χ ξ ∧ χ ξ ≤ 1)
    (h2 : ∀ ξ : Euc d, 2 ≤ ‖ξ‖ → χ ξ = 0) (δ : ℝ) {ρ : ℝ} (hρ : 0 < ρ) {n : ℕ}
    (v : Fin n → Euc d) (hv : ∀ j, ‖v j‖ ≤ 1) (z : Torus d) :
    ‖trig (fun k => ((cLow d s χ δ ρ v k : ℝ) : ℂ)) z‖ ≤
      |kapC d s| * ∑ k ∈ boxF d ⌈2 / ρ⌉₊, gW d (s + n) k := by
  have hT : IsTrigPoly ⌈2 / ρ⌉₊ (fun k => ((cLow d s χ δ ρ v k : ℝ) : ℂ)) :=
    isTrigPoly_of_enorm_lt (fun k hk => cLow_support h2 hρ v k hk)
  refine (norm_trig_le hT z).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  unfold cLow
  rw [abs_mul]
  have h1 : |χ (ρ • Lattice.toEuc k)| ≤ 1 := by
    rw [abs_of_nonneg (h0 _).1]; exact (h0 _).2
  calc |cV d s χ δ v k| * |χ (ρ • Lattice.toEuc k)| ≤ |cV d s χ δ v k| * 1 :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ ≤ _ := by rw [mul_one]; exact abs_cV_le hsd h0 δ v hv k


theorem fdiffs_ofReal (L : List (Euc d)) (H : Euc d → ℝ) :
    fdiffs L (fun ξ => ((H ξ : ℝ) : ℂ)) = fun ξ => ((fdiffs L H ξ : ℝ) : ℂ) := by
  induction L generalizing H with
  | nil => rfl
  | cons v L ih =>
    simp only [fdiffs]
    have : fdiff v (fun ξ => ((H ξ : ℝ) : ℂ)) = fun ξ => ((fdiff v H ξ : ℝ) : ℂ) := by
      funext ξ; simp [fdiff]
    rw [this, ih]

/-- the lattice coefficients of the high-frequency symbol -/
def cG (d : ℕ) (s : ℝ) (χ : Euc d → ℝ) (δ ρ : ℝ) {n : ℕ} (v : Fin n → Euc d) (k : Lattice d) : ℂ :=
  ((Gsym d s χ δ ρ v (Lattice.toEuc k) : ℝ) : ℂ)

theorem cG_support (h2 : ∀ ξ : Euc d, 2 ≤ ‖ξ‖ → χ ξ = 0) {δ : ℝ} (hδ : 0 < δ) (ρ : ℝ) {n : ℕ}
    (v : Fin n → Euc d) (k : Lattice d) (hk : cG d s χ δ ρ v k ≠ 0) : Lattice.enorm k < 2 / δ := by
  by_contra hcon
  push Not at hcon
  apply hk
  have : χ (δ • Lattice.toEuc k) = 0 := by
    apply h2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
    rw [div_le_iff₀ hδ] at hcon
    unfold Lattice.enorm at hcon
    linarith
  simp [cG, Gsym, this]

theorem Dls_cG (L : List (Fin d)) (δ ρ : ℝ) {n : ℕ} (v : Fin n → Euc d) (k : Lattice d) :
    Dls L (cG d s χ δ ρ v) k =
      ((fdiffs (L.map fun i => EuclideanSpace.single i (1 : ℝ)) (Gsym d s χ δ ρ v) (Lattice.toEuc k) : ℝ) : ℂ) := by
  have h := Dls_comp_toEuc L (fun ξ => ((Gsym d s χ δ ρ v ξ : ℝ) : ℂ))
  have e : cG d s χ δ ρ v = (fun ξ => ((Gsym d s χ δ ρ v ξ : ℝ) : ℂ)) ∘ Lattice.toEuc := rfl
  rw [e, h, fdiffs_ofReal]
  rfl


theorem centeredRep_ne_zero {z : Torus d} (hz : z ≠ 0) : Torus.centeredRep z ≠ 0 := by
  intro h
  apply hz
  rw [← centeredRep_mk z, h]
  funext i
  simp [Torus.mk]

theorem exists_qf_ge (hd : 1 ≤ d) (z : Torus d) :
    ∃ i : Fin d, 16 * Torus.tdist z 0 ^ 2 / d ≤ qf i z := by
  have h1 := tdist_sq_le z
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le hne (f := fun _ : Fin d => 16 * Torus.tdist z 0 ^ 2 / d)
    (g := fun i => qf i z) (by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
      linarith)
  exact ⟨i, hi⟩

theorem one_add_T_ge {ρ : ℝ} (hρ : 0 < ρ) (N : ℕ) :
    1 / (((N : ℝ) + 1) * ρ) ≤ 1 + max (1 / ρ - N) 0 := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [div_le_iff₀ (by positivity)]
  rcases le_total (N : ℝ) (1 / ρ) with h | h
  · rw [max_eq_left (by linarith)]
    have h1 : 1 / ρ * ρ = 1 := by field_simp
    have hNρ : (N : ℝ) * ρ ≤ 1 := by
      calc (N : ℝ) * ρ ≤ 1 / ρ * ρ := by gcongr
        _ = 1 := h1
    have h3 := mul_nonneg hN (sub_nonneg.2 hNρ)
    nlinarith
  · rw [max_eq_right (by linarith)]
    have h1 : 1 / ρ * ρ = 1 := by field_simp
    have : (1 / ρ) ≤ N := h
    nlinarith [mul_pos hρ hρ]


/-- the high-frequency part of the trigonometric sum -/
theorem trig_cG_le (hd : 1 ≤ d) (hχs : ContDiff ℝ ∞ χ) (h1 : ∀ ξ : Euc d, ‖ξ‖ ≤ 1 → χ ξ = 1)
    (h2 : ∀ ξ : Euc d, 2 ≤ ‖ξ‖ → χ ξ = 0) (n N : ℕ) (hp : 1 ≤ (N : ℝ) - (s + n)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ δ ρ : ℝ, 0 < δ → δ ≤ 1 → 0 < ρ → ρ ≤ 1 → ∀ v : Fin n → Euc d,
      (∀ j, ‖v j‖ ≤ 1) → ∀ z : Torus d, z ≠ 0 → ρ ≤ Torus.tdist z 0 →
        ‖trig (cG d s χ δ ρ v) z‖ ≤ K * ρ ^ (-(s + n)) := by
  obtain ⟨C1, hC1, hC⟩ := Gsym_fdiffs_bound s hχs h1 h2 n N (d := d)
  obtain ⟨At, hAt0, hAt⟩ := LatSum.tail_sum hd hp
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set pp : ℝ := (N : ℝ) - (s + n) with hpp
  refine ⟨C1 * At * ((d : ℝ) ^ N / 4 ^ N * (((N : ℝ) + 1) ^ pp)), by positivity,
    fun δ ρ hδ hδ1 hρ hρ1 v hv z hz hρr => ?_⟩
  set r := Torus.tdist z 0 with hr
  have hr0 : 0 < r := by
    rw [hr]
    unfold Torus.tdist
    rw [sub_zero]
    exact norm_pos_iff.mpr (centeredRep_ne_zero hz)
  obtain ⟨i0, hi0⟩ := exists_qf_ge hd z
  set L : List (Fin d) := List.replicate N i0 with hL
  have hTrig : IsTrigPoly ⌈2 / δ⌉₊ (cG d s χ δ ρ v) :=
    isTrigPoly_of_enorm_lt (fun k hk => cG_support h2 hδ ρ v k hk)
  have hidentity := trig_Dls L hTrig z
  have hTrig2 := isTrigPoly_Dls L hTrig
  -- bound of the sum of differences
  set T : ℝ := max (1 / ρ - N) 0 with hT
  have hT0 : 0 ≤ T := le_max_right _ _
  have hsum : ‖trig (Dls L (cG d s χ δ ρ v)) z‖ ≤ C1 * (At * (1 + T) ^ (-pp)) := by
    refine (norm_trig_le hTrig2 z).trans ?_
    have hterm : ∀ k : Lattice d, ‖Dls L (cG d s χ δ ρ v) k‖ ≤
        C1 * (if T ≤ Lattice.enorm k then (1 + Lattice.enorm k) ^ (-(d : ℝ) - pp) else 0) := by
      intro k
      rw [Dls_cG, Complex.norm_real, Real.norm_eq_abs, ← Real.norm_eq_abs]
      have hL' : L.map (fun i => (EuclideanSpace.single i (1 : ℝ) : Euc d)) =
          List.replicate N (EuclideanSpace.single i0 (1 : ℝ)) := by
        rw [hL, List.map_replicate]
      rw [hL']
      obtain ⟨hb, hz0⟩ := hC δ ρ hδ hδ1 hρ hρ1 v hv i0 (Lattice.toEuc k)
      by_cases hTk : T ≤ Lattice.enorm k
      · rw [if_pos hTk]
        refine hb.trans (le_of_eq ?_)
        have e : s - (d : ℝ) + n - N = -(d : ℝ) - pp := by rw [hpp]; ring
        rw [e]
        rfl
      · rw [if_neg hTk, mul_zero]
        have hlt : Lattice.enorm k < T := not_le.mp hTk
        have hTpos : T = 1 / ρ - N := by
          rcases le_or_gt (1 / ρ - N) 0 with h | h
          · exfalso
            have : T = 0 := by rw [hT]; exact max_eq_right h
            have : 0 ≤ Lattice.enorm k := norm_nonneg _
            linarith
          · rw [hT]; exact max_eq_left h.le
        have : ‖Lattice.toEuc k‖ < 1 / ρ - N := by
          have := hlt; unfold Lattice.enorm at this; rwa [hTpos] at this
        rw [hz0 this, norm_zero]
    calc ∑ k ∈ boxF d (⌈2 / δ⌉₊ + L.length), ‖Dls L (cG d s χ δ ρ v) k‖
        ≤ ∑ k ∈ boxF d (⌈2 / δ⌉₊ + L.length),
            C1 * (if T ≤ Lattice.enorm k then (1 + Lattice.enorm k) ^ (-(d : ℝ) - pp) else 0) :=
          Finset.sum_le_sum fun k _ => hterm k
      _ = C1 * ∑ k ∈ boxF d (⌈2 / δ⌉₊ + L.length),
            (if T ≤ Lattice.enorm k then (1 + Lattice.enorm k) ^ (-(d : ℝ) - pp) else 0) := by
          rw [Finset.mul_sum]
      _ ≤ C1 * (At * (1 + T) ^ (-pp)) :=
          mul_le_mul_of_nonneg_left (hAt _ T hT0) hC1
  -- lower bound of the product of the mode factors
  have hmode : (4 * r / d) ^ N ≤ ‖(L.map fun i => Torus.mode (eI i) z - 1).prod‖ := by
    rw [hL, List.map_replicate, List.prod_replicate, norm_pow]
    apply pow_le_pow_left₀ (by positivity)
    have hq : (4 * r / d) ^ 2 ≤ ‖Torus.mode (eI i0) z - 1‖ ^ 2 := by
      have : (4 * r / d) ^ 2 ≤ 16 * r ^ 2 / d := by
        rw [div_pow, mul_pow]
        norm_num
        rw [div_le_div_iff₀ (by positivity) hd0]
        have h1d : (1 : ℝ) ≤ d := by exact_mod_cast hd
        nlinarith [mul_nonneg (mul_nonneg (sq_nonneg r) hd0.le) (sub_nonneg.2 h1d)]
      exact this.trans hi0
    exact (abs_le_of_sq_le_sq' hq (norm_nonneg _)).2
  -- combine
  set X := ‖trig (cG d s χ δ ρ v) z‖ with hX
  have hX0 : 0 ≤ X := norm_nonneg _
  set Q : ℝ := (4 * r / d) ^ N with hQ
  have hQ0 : 0 < Q := by positivity
  have hmain : Q * X ≤ C1 * (At * (1 + T) ^ (-pp)) := by
    calc Q * X ≤ ‖(L.map fun i => Torus.mode (eI i) z - 1).prod‖ * X :=
          mul_le_mul_of_nonneg_right hmode hX0
      _ = ‖trig (Dls L (cG d s χ δ ρ v)) z‖ := by rw [← hidentity, norm_mul]
      _ ≤ _ := hsum
  have hpp0 : 0 ≤ pp := by rw [hpp]; linarith
  have hT1 : (1 + T) ^ (-pp) ≤ ((N : ℝ) + 1) ^ pp * (ρ ^ N * ρ ^ (-(s + n))) := by
    have hlow := one_add_T_ge hρ N
    have hNρ : (0 : ℝ) < ((N : ℝ) + 1) * ρ := by positivity
    calc (1 + T) ^ (-pp) ≤ (1 / (((N : ℝ) + 1) * ρ)) ^ (-pp) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hlow (by linarith)
      _ = (((N : ℝ) + 1) * ρ) ^ pp := by
          rw [one_div, Real.inv_rpow hNρ.le, Real.rpow_neg hNρ.le, inv_inv]
      _ = ((N : ℝ) + 1) ^ pp * ρ ^ pp := Real.mul_rpow (by positivity) hρ.le
      _ = ((N : ℝ) + 1) ^ pp * (ρ ^ N * ρ ^ (-(s + n))) := by
          congr 1
          rw [hpp, show (N : ℝ) - (s + n) = (N : ℝ) + (-(s + n)) by ring, Real.rpow_add hρ,
            Real.rpow_natCast]
  have hQr : (4 * r / d) ^ N * ((d : ℝ) ^ N / 4 ^ N) = r ^ N := by
    rw [← div_pow, ← mul_pow]
    congr 1
    field_simp
  have hρN : ρ ^ N ≤ r ^ N := pow_le_pow_left₀ hρ.le hρr N
  have hρσ : 0 ≤ ρ ^ (-(s + n)) := Real.rpow_nonneg hρ.le _
  have hNp : 0 ≤ ((N : ℝ) + 1) ^ pp := by positivity
  have key : Q * X ≤ Q * (C1 * At * ((d : ℝ) ^ N / 4 ^ N * (((N : ℝ) + 1) ^ pp)) * ρ ^ (-(s + n))) := by
    calc Q * X ≤ C1 * (At * (1 + T) ^ (-pp)) := hmain
      _ ≤ C1 * (At * (((N : ℝ) + 1) ^ pp * (ρ ^ N * ρ ^ (-(s + n))))) := by gcongr
      _ ≤ C1 * (At * (((N : ℝ) + 1) ^ pp * (r ^ N * ρ ^ (-(s + n))))) := by gcongr
      _ = Q * (C1 * At * ((d : ℝ) ^ N / 4 ^ N * (((N : ℝ) + 1) ^ pp)) * ρ ^ (-(s + n))) := by
          rw [← hQr]; ring
  exact le_of_mul_le_mul_left key hQ0


theorem cV_decomp (hsd : s < d) (h1 : ∀ ξ : Euc d, ‖ξ‖ ≤ 1 → χ ξ = 1)
    (h2 : ∀ ξ : Euc d, 2 ≤ ‖ξ‖ → χ ξ = 0) (δ : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {n : ℕ}
    (v : Fin n → Euc d) (k : Lattice d) :
    ((cV d s χ δ v k : ℝ) : ℂ) =
      ((cLow d s χ δ ρ v k : ℝ) : ℂ) + ((kapC d s : ℝ) : ℂ) * cG d s χ δ ρ v k := by
  unfold cG cLow cV
  rw [Gsym_eq s h1 h2 δ ρ hρ hρ1 v, rieszCoeff_eq hsd]
  push_cast
  ring

theorem trig_add_mul {a b : Lattice d → ℂ} {m : ℕ} (ha : IsTrigPoly m a) (hb : IsTrigPoly m b) (c : ℂ)
    (z : Torus d) : trig (fun k => a k + c * b k) z = trig a z + c * trig b z := by
  unfold trig
  simp only [add_mul, mul_assoc]
  rw [Summable.tsum_add (summable_trig ha z) ((summable_trig hb z).mul_left c), tsum_mul_left]

theorem cG_isTrigPoly (h2 : ∀ ξ : Euc d, 2 ≤ ‖ξ‖ → χ ξ = 0) {δ : ℝ} (hδ : 0 < δ) (ρ : ℝ) {n : ℕ}
    (v : Fin n → Euc d) : IsTrigPoly ⌈2 / δ⌉₊ (cG d s χ δ ρ v) :=
  isTrigPoly_of_enorm_lt (fun k hk => cG_support h2 hδ ρ v k hk)

theorem cLow_isTrigPoly (h2 : ∀ ξ : Euc d, 2 ≤ ‖ξ‖ → χ ξ = 0) (δ : ℝ) {ρ : ℝ} (hρ : 0 < ρ) {n : ℕ}
    (v : Fin n → Euc d) : IsTrigPoly ⌈2 / ρ⌉₊ (fun k => ((cLow d s χ δ ρ v k : ℝ) : ℂ)) :=
  isTrigPoly_of_enorm_lt (fun k hk => cLow_support h2 hρ v k hk)

/-- the coefficient sequence is itself a trigonometric polynomial -/
theorem cc_isTrigPoly (h2 : ∀ ξ : Euc d, 2 ≤ ‖ξ‖ → χ ξ = 0) {δ : ℝ} (hδ : 0 < δ) {n : ℕ}
    (v : Fin n → Euc d) : IsTrigPoly ⌈2 / δ⌉₊ (fun k => ((cV d s χ δ v k : ℝ) : ℂ)) := by
  refine isTrigPoly_of_enorm_lt (fun k hk => ?_)
  by_contra hcon
  push Not at hcon
  apply hk
  have : χ (δ • Lattice.toEuc k) = 0 := by
    apply h2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
    rw [div_le_iff₀ hδ] at hcon
    unfold Lattice.enorm at hcon
    linarith
  simp [cV, this]

/-- the main bound for `σ = s + n > 0` -/
theorem trig_bound_pos (hd : 1 ≤ d) (hsd : s < d) (hχs : ContDiff ℝ ∞ χ)
    (h0 : ∀ ξ, 0 ≤ χ ξ ∧ χ ξ ≤ 1) (h1 : ∀ ξ : Euc d, ‖ξ‖ ≤ 1 → χ ξ = 1)
    (h2 : ∀ ξ : Euc d, 2 ≤ ‖ξ‖ → χ ξ = 0) (n : ℕ) (hσ : 0 < s + n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ v : Fin n → Euc d, (∀ j, ‖v j‖ ≤ 1) →
      ∀ z : Torus d, z ≠ 0 →
        ‖trig (fun k => ((cV d s χ δ v k : ℝ) : ℂ)) z‖ ≤ K * (Torus.tdist z 0 ^ (-(s + n)) + 1) := by
  set N : ℕ := ⌈s + n⌉₊ + 1 with hN
  have hp : 1 ≤ (N : ℝ) - (s + n) := by
    have := Nat.le_ceil (s + n)
    rw [hN]; push_cast; linarith
  obtain ⟨Kh, hKh0, hKh⟩ := trig_cG_le hd hχs h1 h2 n N hp (s := s)
  obtain ⟨Al, hAl0, hAl⟩ := LatSum.low_sum hd hσ
  refine ⟨|kapC d s| * (Al * 3 ^ (s + n) + Kh), by positivity, fun δ hδ hδ1 v hv z hz => ?_⟩
  set r := Torus.tdist z 0 with hr
  have hr0 : 0 < r := by
    rw [hr]; unfold Torus.tdist; rw [sub_zero]
    exact norm_pos_iff.mpr (centeredRep_ne_zero hz)
  set ρ := min 1 r with hρdef
  have hρ : 0 < ρ := lt_min one_pos hr0
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρr : ρ ≤ r := min_le_right _ _
  have hdec : (fun k => ((cV d s χ δ v k : ℝ) : ℂ)) =
      fun k => ((cLow d s χ δ ρ v k : ℝ) : ℂ) + ((kapC d s : ℝ) : ℂ) * cG d s χ δ ρ v k :=
    funext fun k => cV_decomp hsd h1 h2 δ hρ hρ1 v k
  have hT1 : IsTrigPoly (max ⌈2 / ρ⌉₊ ⌈2 / δ⌉₊) (fun k => ((cLow d s χ δ ρ v k : ℝ) : ℂ)) :=
    isTrigPoly_mono (cLow_isTrigPoly h2 δ hρ v) (le_max_left _ _)
  have hT2 : IsTrigPoly (max ⌈2 / ρ⌉₊ ⌈2 / δ⌉₊) (cG d s χ δ ρ v) :=
    isTrigPoly_mono (cG_isTrigPoly h2 hδ ρ v) (le_max_right _ _)
  rw [hdec, trig_add_mul hT1 hT2]
  refine (norm_add_le _ _).trans ?_
  have hlow := trig_cLow_le hsd h0 h2 δ hρ v hv z
  have hhigh := hKh δ ρ hδ hδ1 hρ hρ1 v hv z hz hρr
  have hJ : (⌈2 / ρ⌉₊ : ℝ) ≤ 3 / ρ := by
    have h3 : (⌈2 / ρ⌉₊ : ℝ) < 2 / ρ + 1 := Nat.ceil_lt_add_one (by positivity)
    have h4 : (1 : ℝ) ≤ 1 / ρ := by rw [le_div_iff₀ hρ]; linarith
    have : 3 / ρ = 2 / ρ + 1 / ρ := by ring
    linarith
  have hsum := hAl ⌈2 / ρ⌉₊
  have hρσ : 0 < ρ ^ (-(s + n)) := Real.rpow_pos_of_pos hρ _
  have hJσ : (⌈2 / ρ⌉₊ : ℝ) ^ (s + n) ≤ 3 ^ (s + n) * ρ ^ (-(s + n)) := by
    calc (⌈2 / ρ⌉₊ : ℝ) ^ (s + n) ≤ (3 / ρ) ^ (s + n) :=
          Real.rpow_le_rpow (by positivity) hJ hσ.le
      _ = 3 ^ (s + n) * ρ ^ (-(s + n)) := by
          rw [Real.div_rpow (by norm_num) hρ.le, Real.rpow_neg hρ.le, div_eq_mul_inv]
  have hρr' : ρ ^ (-(s + n)) ≤ r ^ (-(s + n)) + 1 := by
    rcases le_total r 1 with h | h
    · have : ρ = r := by rw [hρdef]; exact min_eq_right h
      rw [this]; linarith
    · have : ρ = 1 := by rw [hρdef]; exact min_eq_left h
      rw [this, Real.one_rpow]
      have : 0 ≤ r ^ (-(s + n)) := Real.rpow_nonneg hr0.le _
      linarith
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h5 : ‖trig (fun k => ((cLow d s χ δ ρ v k : ℝ) : ℂ)) z‖ ≤
      |kapC d s| * (Al * (3 ^ (s + n) * ρ ^ (-(s + n)))) := by
    refine hlow.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine hsum.trans ?_
    exact mul_le_mul_of_nonneg_left hJσ hAl0
  have h6 : |kapC d s| * ‖trig (cG d s χ δ ρ v) z‖ ≤ |kapC d s| * (Kh * ρ ^ (-(s + n))) :=
    mul_le_mul_of_nonneg_left hhigh (abs_nonneg _)
  calc _ ≤ |kapC d s| * (Al * (3 ^ (s + n) * ρ ^ (-(s + n)))) + |kapC d s| * (Kh * ρ ^ (-(s + n))) :=
        add_le_add h5 h6
    _ = |kapC d s| * (Al * 3 ^ (s + n) + Kh) * ρ ^ (-(s + n)) := by ring
    _ ≤ |kapC d s| * (Al * 3 ^ (s + n) + Kh) * (r ^ (-(s + n)) + 1) := by
        gcongr


theorem log_ceil_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Real.log (⌈2 / ε⌉₊ : ℝ) ≤ Real.log 3 + |Real.log ε| := by
  have h3 : (⌈2 / ε⌉₊ : ℝ) < 2 / ε + 1 := Nat.ceil_lt_add_one (by positivity)
  have h4 : (1 : ℝ) ≤ 1 / ε := by rw [le_div_iff₀ hε]; linarith
  have h5 : (⌈2 / ε⌉₊ : ℝ) ≤ 3 / ε := by
    have : 3 / ε = 2 / ε + 1 / ε := by ring
    linarith
  have h6 : (1 : ℝ) ≤ (⌈2 / ε⌉₊ : ℝ) := by
    have : (2 : ℝ) ≤ 2 / ε := by rw [le_div_iff₀ hε]; linarith
    have := Nat.le_ceil (2 / ε)
    linarith
  calc Real.log (⌈2 / ε⌉₊ : ℝ) ≤ Real.log (3 / ε) := Real.log_le_log (by linarith) h5
    _ = Real.log 3 - Real.log ε := Real.log_div (by norm_num) hε.ne'
    _ ≤ Real.log 3 + |Real.log ε| := by
        have := neg_le_abs (Real.log ε)
        linarith

/-- the logarithmic case `s = 0`, `n = 0` -/
theorem trig_bound_log (hd : 1 ≤ d) (hsd : (0 : ℝ) < d) (hχs : ContDiff ℝ ∞ χ)
    (h0 : ∀ ξ, 0 ≤ χ ξ ∧ χ ξ ≤ 1) (h1 : ∀ ξ : Euc d, ‖ξ‖ ≤ 1 → χ ξ = 1)
    (h2 : ∀ ξ : Euc d, 2 ≤ ‖ξ‖ → χ ξ = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ z : Torus d, z ≠ 0 →
      ‖trig (fun k => ((cV d 0 χ δ (fun j : Fin 0 => (0 : Euc d)) k : ℝ) : ℂ)) z‖ ≤
        K * (1 + |Real.log (max δ (Torus.tdist z 0))|) := by
  obtain ⟨Kh, hKh0, hKh⟩ := trig_cG_le hd hχs h1 h2 0 1 (s := 0) (by norm_num)
  obtain ⟨Al, hAl0, hAl⟩ := LatSum.low_sum_log hd
  have hv : ∀ j : Fin 0, ‖(fun j : Fin 0 => (0 : Euc d)) j‖ ≤ 1 := fun j => j.elim0
  have hgW : ∀ k : Lattice d, gW d (0 + ((0 : ℕ) : ℝ)) k =
      if k = 0 then 0 else Lattice.enorm k ^ ((0 : ℝ) - (d : ℝ)) := by
    intro k; simp [gW]
  refine ⟨|kapC d 0| * (Al * (2 + Real.log 3) + Kh), by positivity, fun δ hδ hδ1 z hz => ?_⟩
  set v : Fin 0 → Euc d := fun j => 0 with hvdef
  set r := Torus.tdist z 0 with hr
  have hr0 : 0 < r := by
    rw [hr]; unfold Torus.tdist; rw [sub_zero]
    exact norm_pos_iff.mpr (centeredRep_ne_zero hz)
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  set Lg := |Real.log (max δ r)| with hLg
  have hLg0 : 0 ≤ Lg := abs_nonneg _
  by_cases hrδ : δ ≤ r
  · -- far field
    have hm : max δ r = r := max_eq_right hrδ
    set ρ := min 1 r with hρdef
    have hρ : 0 < ρ := lt_min one_pos hr0
    have hρ1 : ρ ≤ 1 := min_le_left _ _
    have hρr : ρ ≤ r := min_le_right _ _
    have hdec : (fun k => ((cV d 0 χ δ v k : ℝ) : ℂ)) =
        fun k => ((cLow d 0 χ δ ρ v k : ℝ) : ℂ) + ((kapC d 0 : ℝ) : ℂ) * cG d 0 χ δ ρ v k :=
      funext fun k => cV_decomp hsd h1 h2 δ hρ hρ1 v k
    have hT1 : IsTrigPoly (max ⌈2 / ρ⌉₊ ⌈2 / δ⌉₊) (fun k => ((cLow d 0 χ δ ρ v k : ℝ) : ℂ)) :=
      isTrigPoly_mono (cLow_isTrigPoly h2 δ hρ v) (le_max_left _ _)
    have hT2 : IsTrigPoly (max ⌈2 / ρ⌉₊ ⌈2 / δ⌉₊) (cG d 0 χ δ ρ v) :=
      isTrigPoly_mono (cG_isTrigPoly h2 hδ ρ v) (le_max_right _ _)
    rw [hdec, trig_add_mul hT1 hT2]
    refine (norm_add_le _ _).trans ?_
    have hlow := trig_cLow_le hsd h0 h2 δ hρ v hv z
    have hhigh := hKh δ ρ hδ hδ1 hρ hρ1 v hv z hz hρr
    have hJ1 : 1 ≤ ⌈2 / ρ⌉₊ := by
      have : (2 : ℝ) ≤ 2 / ρ := by rw [le_div_iff₀ hρ]; linarith
      have := Nat.le_ceil (2 / ρ)
      exact Nat.one_le_iff_ne_zero.mpr (by
        intro h; rw [h] at this; simp at this; linarith)
    have hsum := hAl ⌈2 / ρ⌉₊ hJ1
    have hlogρ : |Real.log ρ| ≤ Lg := by
      rcases le_total r 1 with h | h
      · have : ρ = r := by rw [hρdef]; exact min_eq_right h
        rw [this, hLg, hm]
      · have : ρ = 1 := by rw [hρdef]; exact min_eq_left h
        rw [this, Real.log_one, abs_zero]; exact hLg0
    have hlogJ := log_ceil_le hρ hρ1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    simp only [Nat.cast_zero, add_zero, neg_zero, Real.rpow_zero, mul_one] at hlow hhigh
    have hs' : ∑ k ∈ boxF d ⌈2 / ρ⌉₊, gW d (0 + ((0 : ℕ) : ℝ)) k ≤ Al * (1 + Real.log (⌈2 / ρ⌉₊ : ℝ)) := by
      rw [Finset.sum_congr rfl (fun k _ => hgW k)]; exact hsum
    have h5 : ‖trig (fun k => ((cLow d 0 χ δ ρ v k : ℝ) : ℂ)) z‖ ≤
        |kapC d 0| * (Al * (1 + (Real.log 3 + Lg))) := by
      refine hlow.trans ?_
      simp only [Nat.cast_zero, add_zero] at hs'
      refine mul_le_mul_of_nonneg_left (hs'.trans ?_) (abs_nonneg _)
      refine mul_le_mul_of_nonneg_left ?_ hAl0
      linarith
    have h6 : |kapC d 0| * ‖trig (cG d 0 χ δ ρ v) z‖ ≤ |kapC d 0| * Kh :=
      mul_le_mul_of_nonneg_left hhigh (abs_nonneg _)
    calc _ ≤ |kapC d 0| * (Al * (1 + (Real.log 3 + Lg))) + |kapC d 0| * Kh := add_le_add h5 h6
      _ ≤ |kapC d 0| * (Al * (2 + Real.log 3) + Kh) * (1 + Lg) := by
        have : 0 ≤ |kapC d 0| := abs_nonneg _
        nlinarith [mul_nonneg this hAl0, mul_nonneg (mul_nonneg this hAl0) hLg0,
          mul_nonneg (mul_nonneg this hAl0) hlog3, mul_nonneg (mul_nonneg (mul_nonneg this hAl0) hlog3) hLg0,
          mul_nonneg this hKh0, mul_nonneg (mul_nonneg this hKh0) hLg0]
  · -- near field: crude bound by the sum of the absolute values of the coefficients
    push Not at hrδ
    have hm : max δ r = δ := max_eq_left hrδ.le
    have hT : IsTrigPoly ⌈2 / δ⌉₊ (fun k => ((cV d 0 χ δ v k : ℝ) : ℂ)) := cc_isTrigPoly h2 hδ v
    refine (norm_trig_le hT z).trans ?_
    have hJ1 : 1 ≤ ⌈2 / δ⌉₊ := by
      have : (2 : ℝ) ≤ 2 / δ := by rw [le_div_iff₀ hδ]; linarith
      have := Nat.le_ceil (2 / δ)
      exact Nat.one_le_iff_ne_zero.mpr (by
        intro h; rw [h] at this; simp at this; linarith)
    have hsum := hAl ⌈2 / δ⌉₊ hJ1
    have hlogJ := log_ceil_le hδ hδ1
    have habs : ∑ k ∈ boxF d ⌈2 / δ⌉₊, ‖((cV d 0 χ δ v k : ℝ) : ℂ)‖ ≤
        |kapC d 0| * ∑ k ∈ boxF d ⌈2 / δ⌉₊, gW d (0 + ((0 : ℕ) : ℝ)) k := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_cV_le hsd h0 δ v hv k
    refine habs.trans ?_
    have hs' : ∑ k ∈ boxF d ⌈2 / δ⌉₊, gW d (0 + ((0 : ℕ) : ℝ)) k ≤ Al * (1 + Real.log (⌈2 / δ⌉₊ : ℝ)) := by
      rw [Finset.sum_congr rfl (fun k _ => hgW k)]; exact hsum
    rw [hm] at hLg
    have hLg' : Real.log 3 + |Real.log δ| = Real.log 3 + Lg := by rw [hLg]
    calc |kapC d 0| * ∑ k ∈ boxF d ⌈2 / δ⌉₊, gW d (0 + ((0 : ℕ) : ℝ)) k
        ≤ |kapC d 0| * (Al * (1 + (Real.log 3 + Lg))) := by
          refine mul_le_mul_of_nonneg_left (hs'.trans ?_) (abs_nonneg _)
          refine mul_le_mul_of_nonneg_left ?_ hAl0
          linarith
      _ ≤ |kapC d 0| * (Al * (2 + Real.log 3) + Kh) * (1 + Lg) := by
        have : 0 ≤ |kapC d 0| := abs_nonneg _
        nlinarith [mul_nonneg this hAl0, mul_nonneg (mul_nonneg this hAl0) hLg0,
          mul_nonneg (mul_nonneg this hAl0) hlog3, mul_nonneg (mul_nonneg (mul_nonneg this hAl0) hlog3) hLg0,
          mul_nonneg this hKh0, mul_nonneg (mul_nonneg this hKh0) hLg0]


section Deriv


theorem hasDerivAt_expI (t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) (Complex.I * Complex.exp ((t : ℂ) * Complex.I)) t := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I
  have := h1.cexp
  simpa [mul_comm] using this

theorem iteratedDeriv_expI (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) =
      fun t : ℝ => Complex.I ^ n * Complex.exp ((t : ℂ) * Complex.I) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have h := ((hasDerivAt_expI t).const_mul (Complex.I ^ n))
    rw [h.deriv]
    ring

theorem contDiff_expI : ContDiff ℝ ∞ (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) := by
  have h : ContDiff ℂ ∞ Complex.exp := Complex.contDiff_exp
  exact (h.restrict_scalars ℝ).comp (Complex.ofRealCLM.contDiff.mul contDiff_const)

theorem iteratedFDeriv_expI {d : ℕ} (ℓ : Euc d →L[ℝ] ℝ) (n : ℕ) (y : Euc d) (v : Fin n → Euc d) :
    iteratedFDeriv ℝ n (fun y : Euc d => Complex.exp ((ℓ y : ℂ) * Complex.I)) y v =
      (∏ j, (ℓ (v j) : ℂ)) * (Complex.I ^ n * Complex.exp ((ℓ y : ℂ) * Complex.I)) := by
  have h := ℓ.iteratedFDeriv_comp_right (f := fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
    (contDiff_expI.of_le (show (n : WithTop ℕ∞) ≤ ∞ by exact_mod_cast le_top)) y (i := n) le_rfl
  have h2 : (fun y : Euc d => Complex.exp ((ℓ y : ℂ) * Complex.I)) =
      (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) ∘ ℓ := rfl
  rw [h2, h]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, iteratedDeriv_expI]
  simp [Complex.real_smul]

theorem dot_eq_inner (k : Lattice d) (x : Euc d) : Lattice.dot k x = inner ℝ x (Lattice.toEuc k) := by
  simp [Lattice.dot, Lattice.toEuc, PiLp.inner_apply, mul_comm]

/-- the exponential `e^{2πi k·y}` on `ℝ^d` -/
def Ek (k : Lattice d) (y : Euc d) : ℂ := Complex.exp (((Torus.freqFunctional k y : ℝ) : ℂ) * Complex.I)

theorem mode_mk_eq (k : Lattice d) (y : Euc d) : Torus.mode k (Torus.mk y) = Ek k y := by
  rw [Torus.mode_mk, Ek, Torus.freqFunctional_apply]

theorem contDiff_Ek (k : Lattice d) : ContDiff ℝ ∞ (Ek k) := by
  have h := (contDiff_expI).comp (Torus.freqFunctional k).contDiff
  exact h

theorem iteratedFDeriv_Phi (F : Finset (Lattice d)) (c : Lattice d → ℂ) (n : ℕ) (y : Euc d)
    (v : Fin n → Euc d) :
    iteratedFDeriv ℝ n (fun y : Euc d => ∑ k ∈ F, c k * Ek k y) y v =
      ∑ k ∈ F, c k * ((∏ j, ((Torus.freqFunctional k (v j) : ℝ) : ℂ)) * (Complex.I ^ n * Ek k y)) := by
  have hc : ∀ k ∈ F, ContDiffAt ℝ n (fun y : Euc d => c k * Ek k y) y := fun k _ =>
    (contDiffAt_const.mul ((contDiff_Ek k).contDiffAt)).of_le (by exact_mod_cast le_top)
  rw [iteratedFDeriv_fun_sum_apply hc, sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h2 : (fun y : Euc d => c k * Ek k y) =
      (ContinuousLinearMap.mul ℝ ℂ (c k)) ∘ (Ek k) := rfl
  rw [h2, ContinuousLinearMap.iteratedFDeriv_comp_left _
    ((contDiff_Ek k).contDiffAt.of_le (by exact_mod_cast le_top)) le_rfl]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
  have h3 : iteratedFDeriv ℝ n (Ek k) y v =
      (∏ j, ((Torus.freqFunctional k (v j) : ℝ) : ℂ)) * (Complex.I ^ n * Ek k y) :=
    iteratedFDeriv_expI (Torus.freqFunctional k) n y v
  rw [h3]
  rfl


/-- the mollified kernel as a trigonometric series (this is `mollifiedRiesz`) -/
def mollSum (d : ℕ) (s : ℝ) (χ : Euc d → ℝ) (δ : ℝ) (x : Torus d) : ℝ :=
  ∑' k : Lattice d, rieszCoeff d s k * χ (δ • Lattice.toEuc k) ^ 2 * Torus.cosMode k x

/-- the plain coefficient `ĝ(k) χ(δk)²` -/
def bC (d : ℕ) (s : ℝ) (χ : Euc d → ℝ) (δ : ℝ) (k : Lattice d) : ℝ :=
  rieszCoeff d s k * χ (δ • Lattice.toEuc k) ^ 2

theorem cV_zero_eq (δ : ℝ) (v : Fin 0 → Euc d) (k : Lattice d) :
    cV d s χ δ v k = bC d s χ δ k := by
  simp [cV, bC]

theorem bC_support (h2 : ∀ ξ : Euc d, 2 ≤ ‖ξ‖ → χ ξ = 0) {δ : ℝ} (hδ : 0 < δ) (k : Lattice d)
    (hk : bC d s χ δ k ≠ 0) : Lattice.enorm k < 2 / δ := by
  by_contra hcon
  push Not at hcon
  apply hk
  have : χ (δ • Lattice.toEuc k) = 0 := by
    apply h2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
    rw [div_le_iff₀ hδ] at hcon
    unfold Lattice.enorm at hcon
    linarith
  simp [bC, this]

theorem mollSum_eq_sum (h2 : ∀ ξ : Euc d, 2 ≤ ‖ξ‖ → χ ξ = 0) {δ : ℝ} (hδ : 0 < δ) (x : Torus d) :
    mollSum d s χ δ x = ∑ k ∈ boxF d ⌈2 / δ⌉₊, bC d s χ δ k * Torus.cosMode k x := by
  unfold mollSum
  refine tsum_eq_sum fun k hk => ?_
  have hT : IsTrigPoly ⌈2 / δ⌉₊ (fun k => ((bC d s χ δ k : ℝ) : ℂ)) :=
    isTrigPoly_of_enorm_lt (fun k hk => bC_support h2 hδ k (by exact_mod_cast hk))
  have : bC d s χ δ k = 0 := by
    by_contra h
    exact hk (mem_boxF.2 (hT k (by simpa using h)))
  simp only [bC] at this
  simp [this]

theorem lift_mollSum (h2 : ∀ ξ : Euc d, 2 ≤ ‖ξ‖ → χ ξ = 0) {δ : ℝ} (hδ : 0 < δ) (y : Euc d) :
    Torus.lift (mollSum d s χ δ) y =
      (∑ k ∈ boxF d ⌈2 / δ⌉₊, ((bC d s χ δ k : ℝ) : ℂ) * Ek k y).re := by
  simp only [Torus.lift, Function.comp]
  rw [mollSum_eq_sum h2 hδ, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.re_ofReal_mul, ← mode_mk_eq]
  rfl

theorem contDiff_Phi (F : Finset (Lattice d)) (c : Lattice d → ℂ) :
    ContDiff ℝ ∞ (fun y : Euc d => ∑ k ∈ F, c k * Ek k y) :=
  ContDiff.sum fun k _ => contDiff_const.mul (contDiff_Ek k)

/-- the key identity for the derivatives of the mollified kernel -/
theorem iteratedFDeriv_mollSum_apply (h2 : ∀ ξ : Euc d, 2 ≤ ‖ξ‖ → χ ξ = 0) {δ : ℝ} (hδ : 0 < δ)
    (n : ℕ) (y : Euc d) (v : Fin n → Euc d) :
    |iteratedFDeriv ℝ n (Torus.lift (mollSum d s χ δ)) y v| ≤
      (2 * Real.pi) ^ n * ‖trig (fun k => ((cV d s χ δ v k : ℝ) : ℂ)) (Torus.mk y)‖ := by
  set F := boxF d ⌈2 / δ⌉₊ with hF
  have hfun : Torus.lift (mollSum d s χ δ) =
      Complex.reCLM ∘ (fun y : Euc d => ∑ k ∈ F, ((bC d s χ δ k : ℝ) : ℂ) * Ek k y) := by
    funext y
    rw [lift_mollSum h2 hδ]
    rfl
  have hcd : ContDiffAt ℝ n (fun y : Euc d => ∑ k ∈ F, ((bC d s χ δ k : ℝ) : ℂ) * Ek k y) y :=
    ((contDiff_Phi F _).contDiffAt).of_le (by exact_mod_cast le_top)
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_left _ hcd le_rfl]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
  rw [iteratedFDeriv_Phi]
  have hT : IsTrigPoly ⌈2 / δ⌉₊ (fun k => ((cV d s χ δ v k : ℝ) : ℂ)) := cc_isTrigPoly h2 hδ v
  have hsum : ∑ k ∈ F, ((bC d s χ δ k : ℝ) : ℂ) *
      ((∏ j, ((Torus.freqFunctional k (v j) : ℝ) : ℂ)) * (Complex.I ^ n * Ek k y)) =
      ((2 * Real.pi : ℝ) * Complex.I) ^ n *
        trig (fun k => ((cV d s χ δ v k : ℝ) : ℂ)) (Torus.mk y) := by
    rw [trig_eq_sum hT, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hprod : (∏ j, ((Torus.freqFunctional k (v j) : ℝ) : ℂ)) =
        ((2 * Real.pi : ℝ) : ℂ) ^ n * ((∏ j, inner ℝ (v j) (Lattice.toEuc k) : ℝ) : ℂ) := by
      have : ∀ j, ((Torus.freqFunctional k (v j) : ℝ) : ℂ) =
          ((2 * Real.pi : ℝ) : ℂ) * ((inner ℝ (v j) (Lattice.toEuc k) : ℝ) : ℂ) := by
        intro j
        rw [Torus.freqFunctional_apply, dot_eq_inner]
        push_cast; ring
      simp_rw [this]
      rw [Finset.prod_mul_distrib]
      push_cast
      simp
    rw [hprod, mode_mk_eq]
    simp only [cV, bC]
    push_cast
    ring
  rw [hsum]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_pow, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
    abs_of_pos Real.two_pi_pos]



theorem opNorm_le_of_unit_bound {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin n => V) ℝ) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ u : Fin n → V, (∀ j, ‖u j‖ ≤ 1) → |f u| ≤ M) : ‖f‖ ≤ M := by
  classical
  refine f.opNorm_le_bound hM fun m => ?_
  set u : Fin n → V := fun j => if m j = 0 then 0 else ‖m j‖⁻¹ • m j with hu
  have hu1 : ∀ j, ‖u j‖ ≤ 1 := by
    intro j
    by_cases hj : m j = 0
    · simp [hu, hj]
    · simp only [hu, hj, if_false, norm_smul, norm_inv, norm_norm]
      rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hj)]
  have hm : m = fun j => ‖m j‖ • u j := by
    funext j
    by_cases hj : m j = 0
    · simp [hu, hj]
    · simp only [hu, hj, if_false, smul_smul]
      rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr hj), one_smul]
  have : f m = (∏ j, ‖m j‖) • f u := by
    conv_lhs => rw [hm]
    rw [f.map_smul_univ]
  rw [this, norm_smul, norm_prod]
  simp only [abs_norm, Real.norm_eq_abs]
  calc (∏ j, ‖m j‖) * |f u| ≤ (∏ j, ‖m j‖) * M := by
        gcongr
        exact h u hu1
    _ = M * ∏ j, ‖m j‖ := by ring

/-- `‖D^n g_δ(y)‖ ≤ C (|y|^{-s-n} + 1)` for `s + n > 0` -/
theorem deriv_bound_pos (hd : 1 ≤ d) (hsd : s < d) (hχs : ContDiff ℝ ∞ χ)
    (h0 : ∀ ξ, 0 ≤ χ ξ ∧ χ ξ ≤ 1) (h1 : ∀ ξ : Euc d, ‖ξ‖ ≤ 1 → χ ξ = 1)
    (h2 : ∀ ξ : Euc d, 2 ≤ ‖ξ‖ → χ ξ = 0) (n : ℕ) (hσ : 0 < s + n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ y : Euc d, Torus.mk y ≠ 0 →
      ‖iteratedFDeriv ℝ n (Torus.lift (mollSum d s χ δ)) y‖ ≤
        C * (Torus.tdist (Torus.mk y) 0 ^ (-s - (n : ℝ)) + 1) := by
  obtain ⟨K, hK0, hK⟩ := trig_bound_pos hd hsd hχs h0 h1 h2 n hσ
  refine ⟨(2 * Real.pi) ^ n * K, mul_nonneg (by positivity) hK0, fun δ hδ hδ1 y hy => ?_⟩
  have e : -s - (n : ℝ) = -(s + n) := by ring
  rw [e]
  refine opNorm_le_of_unit_bound _ (mul_nonneg (mul_nonneg (by positivity) hK0) (add_nonneg (Real.rpow_nonneg (by unfold Torus.tdist; positivity) _) zero_le_one)) fun u hu => ?_
  refine (iteratedFDeriv_mollSum_apply h2 hδ n y u).trans ?_
  have := hK δ hδ hδ1 u hu (Torus.mk y) hy
  calc (2 * Real.pi) ^ n * ‖trig (fun k => ((cV d s χ δ u k : ℝ) : ℂ)) (Torus.mk y)‖
      ≤ (2 * Real.pi) ^ n * (K * (Torus.tdist (Torus.mk y) 0 ^ (-(s + n)) + 1)) := by gcongr
    _ = _ := by ring

/-- the zeroth-order bound, case `s > 0` -/
theorem zeroth_bound_pos (hd : 1 ≤ d) (hsd : s < d) (hχs : ContDiff ℝ ∞ χ)
    (h0 : ∀ ξ, 0 ≤ χ ξ ∧ χ ξ ≤ 1) (h1 : ∀ ξ : Euc d, ‖ξ‖ ≤ 1 → χ ξ = 1)
    (h2 : ∀ ξ : Euc d, 2 ≤ ‖ξ‖ → χ ξ = 0) (hs : 0 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x : Torus d, x ≠ 0 →
      |mollSum d s χ δ x| ≤ C * (Torus.tdist x 0 ^ (-s) + 1) := by
  obtain ⟨K, hK0, hK⟩ := trig_bound_pos hd hsd hχs h0 h1 h2 0 (by simpa using hs)
  refine ⟨K, hK0, fun δ hδ hδ1 x hx => ?_⟩
  set v0 : Fin 0 → Euc d := fun j => 0 with hv0
  have hv : ∀ j : Fin 0, ‖v0 j‖ ≤ 1 := fun j => j.elim0
  have hre : mollSum d s χ δ x = (trig (fun k => ((cV d s χ δ v0 k : ℝ) : ℂ)) x).re := by
    have hT : IsTrigPoly ⌈2 / δ⌉₊ (fun k => ((cV d s χ δ v0 k : ℝ) : ℂ)) := cc_isTrigPoly h2 hδ v0
    rw [trig_eq_sum hT, mollSum_eq_sum h2 hδ, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.re_ofReal_mul, cV_zero_eq]
    rfl
  rw [hre]
  refine (Complex.abs_re_le_norm _).trans ?_
  have := hK δ hδ hδ1 v0 hv x hx
  simpa using this


/-- the zeroth-order bound, logarithmic case `s = 0` -/
theorem zeroth_bound_log (hd : 1 ≤ d) (hsd : (0 : ℝ) < d) (hχs : ContDiff ℝ ∞ χ)
    (h0 : ∀ ξ, 0 ≤ χ ξ ∧ χ ξ ≤ 1) (h1 : ∀ ξ : Euc d, ‖ξ‖ ≤ 1 → χ ξ = 1)
    (h2 : ∀ ξ : Euc d, 2 ≤ ‖ξ‖ → χ ξ = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x : Torus d, x ≠ 0 →
      |mollSum d 0 χ δ x| ≤ C * (1 + |Real.log (max δ (Torus.tdist x 0))|) := by
  obtain ⟨K, hK0, hK⟩ := trig_bound_log hd hsd hχs h0 h1 h2
  refine ⟨K, hK0, fun δ hδ hδ1 x hx => ?_⟩
  set v0 : Fin 0 → Euc d := fun j => 0 with hv0
  have hre : mollSum d 0 χ δ x = (trig (fun k => ((cV d 0 χ δ v0 k : ℝ) : ℂ)) x).re := by
    have hT : IsTrigPoly ⌈2 / δ⌉₊ (fun k => ((cV d 0 χ δ v0 k : ℝ) : ℂ)) := cc_isTrigPoly h2 hδ v0
    rw [trig_eq_sum hT, Complex.re_sum, mollSum_eq_sum h2 hδ]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.re_ofReal_mul, cV_zero_eq]
    rfl
  rw [hre]
  exact (Complex.abs_re_le_norm _).trans (hK δ hδ hδ1 x hx)

end Deriv

end HDB
end HRS
