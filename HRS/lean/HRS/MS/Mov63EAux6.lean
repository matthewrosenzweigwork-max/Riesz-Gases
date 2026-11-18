import HRS.MS.Mov63EAux5

/-!
# S6.3, packet N6 (part 6): Gaussian majorants of `ρ_u`, `∇ρ_u`, the flux and its divergence

Namespace `HRS.MS.Mov63`, prefix `mne_`.  See `Mov63EAux1`.  `mne_flux_bound`: for `‖u‖ ≤ M` there is `K` with
`|ρ_u|, ‖∇ρ_u‖, |ρ_u|‖x‖², |ρ_u|‖x‖, |ρ_u|‖∇g*ρ_u‖, ‖Y_u‖, |div Y_u| ≤ K (1+‖x‖)^{-(d+1)}` (integrable majorant, `mne_integrableG`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

section Bounds

variable {m : ℕ} (hm : (d : ℝ) / 2 + 3 < m) (H : Mov2dTh d s β q ρ)

/-- The integrable majorant `(1+|x|)^{-(d+1)}`. -/
lemma mne_polyG {c : ℝ} (hc : 0 < c) : ∃ K : ℝ, 0 ≤ K ∧ ∀ x : Euc d,
    (1 + ‖x‖) ^ 2 * Real.exp (-c * ‖x‖ ^ 2) ≤ K * (1 + ‖x‖) ^ (-((d : ℝ) + 1)) := by
  obtain ⟨K, hK0, hK⟩ := mnc_gauss_poly hc (2 + (d + 1))
  refine ⟨K, hK0, fun x => ?_⟩
  have hpos : 0 < 1 + ‖x‖ := by positivity
  have h := hK ‖x‖ (norm_nonneg _)
  have e : (1 + ‖x‖) ^ (-((d : ℝ) + 1)) = ((1 + ‖x‖) ^ (d + 1))⁻¹ := by
    rw [Real.rpow_neg hpos.le]
    congr 1
    rw [← Real.rpow_natCast]
    push_cast
    rfl
  rw [e, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc (1 + ‖x‖) ^ 2 * Real.exp (-c * ‖x‖ ^ 2) * (1 + ‖x‖) ^ (d + 1)
      = (1 + ‖x‖) ^ (2 + (d + 1)) * Real.exp (-c * ‖x‖ ^ 2) := by ring
    _ ≤ K := h

lemma mne_integrableG : Integrable (fun x : Euc d => (1 + ‖x‖) ^ (-((d : ℝ) + 1))) := by
  have := integrable_one_add_norm (E := Euc d) (μ := (volume : Measure (Euc d))) (r := (d : ℝ) + 1) (by simp)
  exact this

include H in
lemma mne_gauss_rho (M : ℝ) :
    ∃ c K : ℝ, 0 < c ∧ 0 ≤ K ∧ ∀ u : OscSpace d (m : ℝ), ‖u‖ ≤ M → ∀ n ≤ 2, ∀ x : Euc d,
      ‖iteratedFDeriv ℝ n (mneRho ρ hm u) x‖ ≤ K * Real.exp (-c * ‖x‖ ^ 2) := by
  obtain ⟨c1, K1, hc1, hK1, hb1⟩ := mnc_rho_gauss H 2
  obtain ⟨c2, K0, hc2, hK0, h2⟩ := mnc_h_gauss H (mne_hn hm)
  refine ⟨min c1 c2, K1 + K0 * max M 0, lt_min hc1 hc2,
    add_nonneg hK1 (mul_nonneg hK0 (le_max_right _ _)), fun u hu n hn x => ?_⟩
  have hρ3 : ContDiff ℝ 3 ρ := (mnc_rho_smooth H).of_le (by simp)
  have hh3 := mne_hu_cd hm H u
  have e : iteratedFDeriv ℝ n (mneRho ρ hm u) x =
      iteratedFDeriv ℝ n ρ x + iteratedFDeriv ℝ n (mnc_hu ρ (mne_hn hm) u) x :=
    iteratedFDeriv_add_apply (hρ3.of_le (by exact_mod_cast (hn.trans (by norm_num : 2 ≤ 3)))).contDiffAt
      (hh3.of_le (by exact_mod_cast (hn.trans (by norm_num : 2 ≤ 3)))).contDiffAt
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have a1 := (hb1 n hn x).trans (mul_le_mul_of_nonneg_left (mnc_gauss_mono (min_le_left c1 c2) x) hK1)
  have a2 := ((h2 u).2 n (hn.trans (by norm_num)) x).trans
    (mul_le_mul_of_nonneg_left (mnc_gauss_mono (min_le_right c1 c2) x)
      (mul_nonneg hK0 (norm_nonneg u)))
  have a3 : K0 * ‖u‖ ≤ K0 * max M 0 := mul_le_mul_of_nonneg_left (hu.trans (le_max_left _ _)) hK0
  have hg := (Real.exp_pos (-(min c1 c2) * ‖x‖ ^ 2)).le
  calc _ ≤ K1 * Real.exp (-(min c1 c2) * ‖x‖ ^ 2) + K0 * ‖u‖ * Real.exp (-(min c1 c2) * ‖x‖ ^ 2) :=
        add_le_add a1 a2
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right a3 hg]


lemma mne_fin {X g P Gx T K2 : ℝ} (hX : X ≤ T * (P * g)) (hT : 0 ≤ T) (hPg : P * g ≤ K2 * Gx) :
    X ≤ T * K2 * Gx := by
  calc X ≤ T * (P * g) := hX
    _ ≤ T * (K2 * Gx) := mul_le_mul_of_nonneg_left hPg hT
    _ = T * K2 * Gx := by ring

lemma mne_h1 {K g P : ℝ} (hK : 0 ≤ K) (hg : 0 ≤ g) (hP : 1 ≤ P) : K * g ≤ K * (P * g) := by
  have : g ≤ P * g := by nlinarith
  exact mul_le_mul_of_nonneg_left this hK

lemma mne_h3 {K g P F : ℝ} (hK : 0 ≤ K) (hg : 0 ≤ g) (hF : 0 ≤ F) (hP : 1 ≤ P) :
    K * g * F ≤ K * F * (P * g) := by
  have h : g ≤ P * g := by nlinarith
  calc K * g * F = K * F * g := by ring
    _ ≤ K * F * (P * g) := mul_le_mul_of_nonneg_left h (mul_nonneg hK hF)

lemma mne_h5 {K g P F b q A B : ℝ} (hK : 0 ≤ K) (hg : 0 ≤ g) (hF : 0 ≤ F) (hP : 1 ≤ P) (hb : 0 ≤ b) (hq : 0 ≤ q)
    (hA : A ≤ b * (K * g)) (hB : B ≤ (K * g) * (q * P + F)) :
    A + B ≤ (b * K + q * K + K * F) * (P * g) := by
  have h1 : b * (K * g) ≤ (b * K) * (P * g) := by
    have : g ≤ P * g := by nlinarith
    calc b * (K * g) = (b * K) * g := by ring
      _ ≤ (b * K) * (P * g) := mul_le_mul_of_nonneg_left this (mul_nonneg hb hK)
  have h2 : (K * g) * (q * P + F) ≤ (q * K + K * F) * (P * g) := by
    have : g ≤ P * g := by nlinarith
    calc (K * g) * (q * P + F) = (q * K) * (P * g) + (K * F) * g := by ring
      _ ≤ (q * K) * (P * g) + (K * F) * (P * g) := by
          have := mul_le_mul_of_nonneg_left this (mul_nonneg hK hF)
          linarith
      _ = (q * K + K * F) * (P * g) := by ring
  calc A + B ≤ b * (K * g) + (K * g) * (q * P + F) := add_le_add hA hB
    _ ≤ (b * K) * (P * g) + (q * K + K * F) * (P * g) := add_le_add h1 h2
    _ = _ := by ring

lemma mne_h6 {K g P F b q A B Cc dd : ℝ} (hK : 0 ≤ K) (hg : 0 ≤ g) (hF : 0 ≤ F) (hP : 1 ≤ P) (hb : 0 ≤ b)
    (hq : 0 ≤ q) (hd : 0 ≤ dd) (hA : A ≤ b * (dd * K * g)) (hB : B ≤ (K * g) * (q * dd + dd * F))
    (hC : Cc ≤ (K * g) * (q * P + F)) :
    A + B + Cc ≤ (b * (dd * K) + K * (q * dd + dd * F) + K * (q + F)) * (P * g) := by
  have hPg : g ≤ P * g := by nlinarith
  have h1 : b * (dd * K * g) ≤ (b * (dd * K)) * (P * g) := by
    calc b * (dd * K * g) = (b * (dd * K)) * g := by ring
      _ ≤ (b * (dd * K)) * (P * g) := mul_le_mul_of_nonneg_left hPg (by positivity)
  have h2 : (K * g) * (q * dd + dd * F) ≤ (K * (q * dd + dd * F)) * (P * g) := by
    calc (K * g) * (q * dd + dd * F) = (K * (q * dd + dd * F)) * g := by ring
      _ ≤ (K * (q * dd + dd * F)) * (P * g) := mul_le_mul_of_nonneg_left hPg (by positivity)
  have h3 : (K * g) * (q * P + F) ≤ (K * (q + F)) * (P * g) := by
    calc (K * g) * (q * P + F) = (K * q) * (P * g) + (K * F) * g := by ring
      _ ≤ (K * q) * (P * g) + (K * F) * (P * g) := by
          have := mul_le_mul_of_nonneg_left hPg (mul_nonneg hK hF)
          linarith
      _ = (K * (q + F)) * (P * g) := by ring
  calc A + B + Cc ≤ b * (dd * K * g) + (K * g) * (q * dd + dd * F) + (K * g) * (q * P + F) :=
        add_le_add (add_le_add hA hB) hC
    _ ≤ (b * (dd * K)) * (P * g) + (K * (q * dd + dd * F)) * (P * g) + (K * (q + F)) * (P * g) :=
        add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
include H in
/-- Gaussian-polynomial majorants for `ρ_u`, `∇ρ_u`, the flux `Y_u` and its divergence, uniformly for `‖u‖ ≤ M`. -/
theorem mne_flux_bound (M : ℝ) :
    ∃ KG : ℝ, 0 ≤ KG ∧ ∀ u : OscSpace d (m : ℝ), ‖u‖ ≤ M → ∀ x : Euc d,
      |mneRho ρ hm u x| ≤ KG * (1 + ‖x‖) ^ (-((d : ℝ) + 1)) ∧
      ‖gradient (mneRho ρ hm u) x‖ ≤ KG * (1 + ‖x‖) ^ (-((d : ℝ) + 1)) ∧
      |mneRho ρ hm u x| * ‖x‖ ^ 2 ≤ KG * (1 + ‖x‖) ^ (-((d : ℝ) + 1)) ∧
      |mneRho ρ hm u x| * ‖x‖ ≤ KG * (1 + ‖x‖) ^ (-((d : ℝ) + 1)) ∧
      |mneRho ρ hm u x| * ‖movForce d s (mneRho ρ hm u) x‖ ≤ KG * (1 + ‖x‖) ^ (-((d : ℝ) + 1)) ∧
      ‖mneY d s q β ρ hm u x‖ ≤ KG * (1 + ‖x‖) ^ (-((d : ℝ) + 1)) ∧
      |movDiv (mneY d s q β ρ hm u) x| ≤ KG * (1 + ‖x‖) ^ (-((d : ℝ) + 1)) := by
  obtain ⟨c, K, hc, hK, hg⟩ := mne_gauss_rho hm H M
  obtain ⟨K2, hK2, hP⟩ := mne_polyG (d := d) hc
  obtain ⟨C, hC0, hC⟩ := mne_force_facts (s := s) (β := β) (q := q) (ρ := ρ) hm H
  set M' : ℝ := max M 0 with hM'
  set C0 : ℝ := C * ‖mneU0 m ρ‖ with hC0def
  have hC00 : 0 ≤ C0 := mul_nonneg hC0 (norm_nonneg _)
  have hF0 : ∀ x, movForce d s ρ x = mneFo d s ρ hm (mneU0 m ρ) x := fun x => congrFun (mneF0 hm H) x
  set T1 : ℝ := |β⁻¹| * K + |q| * K + K * (C0 + C * M') with hT1
  set T2 : ℝ := |β⁻¹| * (d * K) + K * (|q| * d + d * (C0 + C * M')) + K * (|q| + (C0 + C * M')) with hT2
  have hT10 : 0 ≤ T1 := by positivity
  have hT20 : 0 ≤ T2 := by positivity
  refine ⟨K * K2 + K * K2 + K * K2 + K * K2 + K * (C0 + C * M') * K2 + T1 * K2 + T2 * K2, by positivity,
    fun u hu x => ?_⟩
  set g : ℝ := Real.exp (-c * ‖x‖ ^ 2) with hgdef
  set P : ℝ := (1 + ‖x‖) ^ 2 with hPdef
  set Gx : ℝ := (1 + ‖x‖) ^ (-((d : ℝ) + 1)) with hGx
  have hg0 : 0 ≤ g := (Real.exp_pos _).le
  have hP1 : 1 ≤ P := by
    have : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    nlinarith
  have hPx : ‖x‖ ≤ P := by nlinarith [norm_nonneg x]
  have hPx2 : ‖x‖ ^ 2 ≤ P := by nlinarith [norm_nonneg x]
  have hPg := hP x
  have hGx0 : 0 ≤ Gx := by positivity
  have hKG0 : 0 ≤ K * K2 + K * K2 + K * K2 + K * K2 + K * (C0 + C * M') * K2 + T1 * K2 + T2 * K2 := by positivity
  -- basic bounds
  have a0 : |mneRho ρ hm u x| ≤ K * g := by
    have := hg u hu 0 (by norm_num) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have a1 : ‖gradient (mneRho ρ hm u) x‖ ≤ K * g := by
    have := hg u hu 1 (by norm_num) x
    rwa [norm_iteratedFDeriv_one, ← mnc_norm_gradient] at this
  have a2 : |Laplacian.laplacian (mneRho ρ hm u) x| ≤ d * K * g := by
    have := hg u hu 2 (by norm_num) x
    refine (mne_lap_bound _ x).trans ?_
    calc (d : ℝ) * ‖iteratedFDeriv ℝ 2 (mneRho ρ hm u) x‖ ≤ d * (K * g) :=
          mul_le_mul_of_nonneg_left this (Nat.cast_nonneg d)
      _ = d * K * g := by ring
  -- forces
  have hFu : ‖mneFo d s ρ hm u x‖ ≤ C * M' := by
    refine ((hC u).2.1 x).trans ?_
    exact mul_le_mul_of_nonneg_left (hu.trans (le_max_left _ _)) hC0
  have hF0n : ‖movForce d s ρ x‖ ≤ C0 := by rw [hF0 x]; exact (hC _).2.1 x
  have hFn : ‖movForce d s (mneRho ρ hm u) x‖ ≤ C0 + C * M' := by
    rw [mne_force_split hm H u x]
    exact (norm_add_le _ _).trans (add_le_add hF0n hFu)
  have hdFu : |movDiv (mneFo d s ρ hm u) x| ≤ d * (C * M') := by
    refine (mne_movDiv_bound _ x).trans ?_
    refine mul_le_mul_of_nonneg_left (((hC u).2.2 x).trans ?_) (Nat.cast_nonneg d)
    exact mul_le_mul_of_nonneg_left (hu.trans (le_max_left _ _)) hC0
  have hdF0 : |movDiv (movForce d s ρ) x| ≤ d * C0 := by
    rw [mneF0 hm H]
    exact (mne_movDiv_bound _ x).trans (mul_le_mul_of_nonneg_left ((hC _).2.2 x) (Nat.cast_nonneg d))
  -- the six bounds
  have b1 : |mneRho ρ hm u x| ≤ K * K2 * Gx := by
    refine mne_fin (g := g) (P := P) ?_ hK hPg
    exact a0.trans (mne_h1 hK hg0 hP1)
  have b2 : ‖gradient (mneRho ρ hm u) x‖ ≤ K * K2 * Gx := by
    refine mne_fin (g := g) (P := P) ?_ hK hPg
    exact a1.trans (mne_h1 hK hg0 hP1)
  have b3 : |mneRho ρ hm u x| * ‖x‖ ^ 2 ≤ K * K2 * Gx := by
    refine mne_fin (g := g) (P := P) ?_ hK hPg
    calc _ ≤ (K * g) * P := mul_le_mul a0 hPx2 (sq_nonneg _) (mul_nonneg hK hg0)
      _ = K * (P * g) := by ring
  have b3' : |mneRho ρ hm u x| * ‖x‖ ≤ K * K2 * Gx := by
    refine mne_fin (g := g) (P := P) ?_ hK hPg
    calc _ ≤ (K * g) * P := mul_le_mul a0 hPx (norm_nonneg _) (mul_nonneg hK hg0)
      _ = K * (P * g) := by ring
  have b4 : |mneRho ρ hm u x| * ‖movForce d s (mneRho ρ hm u) x‖ ≤ K * (C0 + C * M') * K2 * Gx := by
    refine mne_fin (g := g) (P := P) ?_ (by positivity) hPg
    calc _ ≤ (K * g) * (C0 + C * M') := mul_le_mul a0 hFn (norm_nonneg _) (mul_nonneg hK hg0)
      _ ≤ K * (C0 + C * M') * (P * g) := mne_h3 hK hg0 (by positivity) hP1
  have hG : ‖q • x + movForce d s (mneRho ρ hm u) x‖ ≤ |q| * P + (C0 + C * M') := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
    have := mul_le_mul_of_nonneg_left hPx (abs_nonneg q)
    linarith
  have b5 : ‖mneY d s q β ρ hm u x‖ ≤ T1 * K2 * Gx := by
    refine mne_fin (g := g) (P := P) ?_ hT10 hPg
    unfold mneY
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    have e1 : |β⁻¹| * ‖gradient (mneRho ρ hm u) x‖ ≤ |β⁻¹| * (K * g) :=
      mul_le_mul_of_nonneg_left a1 (abs_nonneg _)
    have e2 : |mneRho ρ hm u x| * ‖q • x + movForce d s (mneRho ρ hm u) x‖ ≤
        (K * g) * (|q| * P + (C0 + C * M')) :=
      mul_le_mul a0 hG (norm_nonneg _) (mul_nonneg hK hg0)
    exact mne_h5 hK hg0 (by positivity) hP1 (abs_nonneg _) (abs_nonneg _) e1 e2
  have b6 : |movDiv (mneY d s q β ρ hm u) x| ≤ T2 * K2 * Gx := by
    refine mne_fin (g := g) (P := P) ?_ hT20 hPg
    rw [mne_e_formulaR hm H u x]
    have hG2 : ‖q • x + (movForce d s ρ x + mneFo d s ρ hm u x)‖ ≤ |q| * P + (C0 + C * M') := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs]
      have h1 := mul_le_mul_of_nonneg_left hPx (abs_nonneg q)
      have h2 : ‖movForce d s ρ x + mneFo d s ρ hm u x‖ ≤ C0 + C * M' := (norm_add_le _ _).trans (add_le_add hF0n hFu)
      linarith
    refine (abs_add_le _ _).trans ?_
    refine (add_le_add_right (abs_add_le _ _) _).trans ?_
    rw [← add_assoc]
    have hdd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hA : |β⁻¹ * Laplacian.laplacian (mneRho ρ hm u) x| ≤ |β⁻¹| * (d * K * g) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left a2 (abs_nonneg _)
    have hB : |mneRho ρ hm u x * (q * d + (movDiv (movForce d s ρ) x + movDiv (mneFo d s ρ hm u) x))| ≤
        (K * g) * (|q| * d + d * (C0 + C * M')) := by
      rw [abs_mul]
      refine mul_le_mul a0 ?_ (abs_nonneg _) (mul_nonneg hK hg0)
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg hdd]
      have h1 := add_le_add hdF0 hdFu
      have h2 := abs_add_le (movDiv (movForce d s ρ) x) (movDiv (mneFo d s ρ hm u) x)
      linarith
    have hC : |inner ℝ (gradient (mneRho ρ hm u) x) (q • x + (movForce d s ρ x + mneFo d s ρ hm u x))| ≤
        (K * g) * (|q| * P + (C0 + C * M')) :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul a1 hG2 (norm_nonneg _) (mul_nonneg hK hg0))
    exact mne_h6 hK hg0 (by positivity) hP1 (abs_nonneg _) (abs_nonneg _) hdd hA hB hC
  have n1 : 0 ≤ K * K2 := mul_nonneg hK hK2
  have n4 : 0 ≤ K * (C0 + C * M') * K2 := by positivity
  have n5 : 0 ≤ T1 * K2 := mul_nonneg hT10 hK2
  have n6 : 0 ≤ T2 * K2 := mul_nonneg hT20 hK2
  exact ⟨b1.trans (mul_le_mul_of_nonneg_right (by linarith) hGx0),
    b2.trans (mul_le_mul_of_nonneg_right (by linarith) hGx0),
    b3.trans (mul_le_mul_of_nonneg_right (by linarith) hGx0),
    b3'.trans (mul_le_mul_of_nonneg_right (by linarith) hGx0),
    b4.trans (mul_le_mul_of_nonneg_right (by linarith) hGx0),
    b5.trans (mul_le_mul_of_nonneg_right (by linarith) hGx0),
    b6.trans (mul_le_mul_of_nonneg_right (by linarith) hGx0)⟩

end Bounds

end HRS.MS.Mov63

end
