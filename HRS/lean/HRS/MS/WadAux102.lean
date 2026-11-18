import HRS.MS.WadAux101

/-!
# S8.3, packet S8F-2: Gaussian bounds for the iterated flow-shifted differences of the density

`s8f_GB k C c g`: `g ∈ C^k` with `‖D^i g(x)‖ ≤ C e^{-c‖x‖²}` for `i ≤ k`.  Shifts and differences lose a factor `1/2` in `c`:
`s8f_GB_shift`, `s8f_GB_diff`.  `s8f_Dif a I g`: the iterated flow-shifted difference `s8e_u a ξ_1 (⋯ (s8e_u a ξ_n g))` of a family of functions
`g : ℝ → ℝ^d → ℝ`; `s8f_Dif_eq_dp` identifies it, at a fixed time, with `s8f_dp` along the flowed shifts.
`s8f_GB_dif`: `Dif_I ρ` has `s8f_GB n (C e^{c |I|} ∏‖ξ_i‖) (c/2^{|I|})` if `ρ` has `s8f_GB (n + |I|) C c`.
`s8f_thermal_GB`: the thermal density has `s8f_GB K C c` for every `K`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

def s8f_GB (k : ℕ) (C c : ℝ) (g : Euc d → ℝ) : Prop :=
  ContDiff ℝ k g ∧ ∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i g x‖ ≤ C * Real.exp (-c * ‖x‖ ^ 2)

theorem s8f_GB.nonneg {k : ℕ} {C c : ℝ} {g : Euc d → ℝ} (h : s8f_GB k C c g) : 0 ≤ C := by
  have := h.2 0 (Nat.zero_le _) 0
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, neg_zero,
    Real.exp_zero, mul_one] at this
  exact (norm_nonneg _).trans this

theorem s8f_GB.mono {k : ℕ} {C c C' c' : ℝ} {g : Euc d → ℝ} (h : s8f_GB k C c g) (hC : C ≤ C')
    (hc' : 0 ≤ c') (hcc : c' ≤ c) : s8f_GB k C' c' g := by
  refine ⟨h.1, fun i hi x => (h.2 i hi x).trans ?_⟩
  have hC0 := h.nonneg
  have hE : Real.exp (-c * ‖x‖ ^ 2) ≤ Real.exp (-c' * ‖x‖ ^ 2) :=
    Real.exp_le_exp.2 (by nlinarith [sq_nonneg ‖x‖])
  exact mul_le_mul hC hE (Real.exp_pos _).le (hC0.trans hC)

theorem s8f_GB_shift {k : ℕ} {C c : ℝ} {g : Euc d → ℝ} (h : s8f_GB k C c g) (hc : 0 ≤ c) {z : Euc d}
    (hz : ‖z‖ ≤ 1) : s8f_GB k (C * Real.exp c) (c / 2) (fun y => g (y + z)) := by
  refine ⟨h.1.comp (contDiff_id.add contDiff_const), fun i hi x => ?_⟩
  rw [iteratedFDeriv_comp_add_right]
  refine (h.2 i hi (x + z)).trans ?_
  have := s8e_exp_shift hc hz x
  calc C * Real.exp (-c * ‖x + z‖ ^ 2) ≤ C * (Real.exp c * Real.exp (-(c / 2) * ‖x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left this h.nonneg
    _ = C * Real.exp c * Real.exp (-(c / 2) * ‖x‖ ^ 2) := by ring

theorem s8f_GB_diff {k : ℕ} {C c : ℝ} {g : Euc d → ℝ} (h : s8f_GB (k + 1) C c g) (hc : 0 ≤ c) {z : Euc d}
    (hz : ‖z‖ ≤ 1) :
    s8f_GB k (‖z‖ * (C * Real.exp c)) (c / 2) (fun y => g (y + z) - g y) := by
  have hg : ContDiff ℝ (k + 1) g := h.1
  have hgz : ContDiff ℝ (k + 1) (fun y => g (y + z)) := hg.comp (contDiff_id.add contDiff_const)
  refine ⟨((hgz.sub hg).of_le (by norm_cast; omega)), fun i hi x => ?_⟩
  have hgi : ContDiff ℝ i g := hg.of_le (by norm_cast; omega)
  have hgzi : ContDiff ℝ i (fun y => g (y + z)) := hgz.of_le (by norm_cast; omega)
  have e1 : iteratedFDeriv ℝ i (fun y => g (y + z) - g y) x =
      iteratedFDeriv ℝ i g (x + z) - iteratedFDeriv ℝ i g x := by
    have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (x := x) (i := i) hgzi.contDiffAt hgi.contDiffAt
    simp only [Pi.sub_def] at this ⊢
    rw [this, iteratedFDeriv_comp_add_right]
  rw [e1]
  have hdiff : Differentiable ℝ (iteratedFDeriv ℝ i g) :=
    hg.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_of_le hi)
  have := s8e_shift_gauss hdiff hc h.nonneg (fun y => by
    rw [norm_fderiv_iteratedFDeriv]
    exact h.2 (i + 1) (by omega) y) hz x
  refine this.trans (le_of_eq ?_)
  ring

/-- The iterated flow-shifted difference along a list. -/
def s8f_Dif (a : ℝ) : List (Euc d) → (ℝ → Euc d → ℝ) → (ℝ → Euc d → ℝ)
  | [], g => g
  | ξ :: ξs, g => s8e_u a ξ (s8f_Dif a ξs g)

theorem s8f_Dif_cons (a : ℝ) (ξ : Euc d) (ξs : List (Euc d)) (g : ℝ → Euc d → ℝ) (s : ℝ) (y : Euc d) :
    s8f_Dif a (ξ :: ξs) g s y = s8f_Dif a ξs g s (y + s8e_zs a ξ s) - s8f_Dif a ξs g s y := rfl

theorem s8f_Dif_eq_dp (a : ℝ) (ξs : List (Euc d)) (g : ℝ → Euc d → ℝ) (s : ℝ) :
    s8f_Dif a ξs g s = s8f_dp (ξs.map (fun ξ => s8e_zs a ξ s)) (g s) := by
  induction ξs with
  | nil => rfl
  | cons ξ ξs ih =>
    funext y
    rw [s8f_Dif_cons, ih]
    rfl

theorem s8f_GB_dif (a : ℝ) (ha : 0 ≤ a) {C c : ℝ} {ρ : Euc d → ℝ} (hc : 0 ≤ c) :
    ∀ (I : List (Euc d)) (n : ℕ), s8f_GB (n + I.length) C c ρ → ∀ s, 0 ≤ s → (∀ ξ ∈ I, ‖ξ‖ ≤ 1) →
      s8f_GB n (C * (Real.exp c) ^ I.length * (I.map (fun ξ => ‖ξ‖)).prod) (c / 2 ^ I.length)
        (fun y => s8f_Dif a I (fun _ => ρ) s y) := by
  intro I
  induction I with
  | nil =>
    intro n h s hs hI
    simpa [s8f_Dif] using h
  | cons ξ I ih =>
    intro n h s hs hI
    have h1 : s8f_GB (n + 1 + I.length) C c ρ := by
      have : n + 1 + I.length = n + (ξ :: I).length := by simp; omega
      rwa [this]
    have hI' : ∀ ξ' ∈ I, ‖ξ'‖ ≤ 1 := fun ξ' hξ' => hI ξ' (List.mem_cons_of_mem _ hξ')
    have h2 := ih (n + 1) h1 s hs hI'
    have hcI : 0 ≤ c / 2 ^ I.length := by positivity
    have hz : ‖s8e_zs a ξ s‖ ≤ 1 := (s8e_zs_norm ha hs ξ).trans (hI ξ (List.mem_cons_self))
    have h3 := s8f_GB_diff h2 hcI hz
    have hzn : ‖s8e_zs a ξ s‖ ≤ ‖ξ‖ := s8e_zs_norm ha hs ξ
    refine (h3.mono ?_ (by positivity) (le_of_eq ?_))
    · set P : ℝ := (I.map (fun ξ => ‖ξ‖)).prod
      have hP : 0 ≤ P := List.prod_nonneg (by
        intro x hx
        obtain ⟨a', -, rfl⟩ := List.mem_map.1 hx
        exact norm_nonneg a')
      have hC0 := h.nonneg
      have hE : Real.exp (c / 2 ^ I.length) ≤ Real.exp c :=
        Real.exp_le_exp.2 (div_le_self hc (one_le_pow₀ (by norm_num)))
      have hCI : 0 ≤ C * Real.exp c ^ I.length * P := by positivity
      simp only [List.length_cons, List.map_cons, List.prod_cons]
      calc ‖s8e_zs a ξ s‖ * (C * Real.exp c ^ I.length * P * Real.exp (c / 2 ^ I.length))
          ≤ ‖ξ‖ * (C * Real.exp c ^ I.length * P * Real.exp c) :=
            mul_le_mul hzn (mul_le_mul_of_nonneg_left hE hCI) (by positivity) (norm_nonneg _)
        _ = _ := by ring
    · simp only [List.length_cons]
      rw [pow_succ]; field_simp

theorem s8f_GB_basic {k : ℕ} {C c : ℝ} {σ : Euc d → ℝ} (h : s8f_GB (k + 1) C c σ) :
    Differentiable ℝ σ ∧ ∀ x, |σ x| ≤ C * Real.exp (-c * ‖x‖ ^ 2) ∧
      ‖fderiv ℝ σ x‖ ≤ C * Real.exp (-c * ‖x‖ ^ 2) := by
  refine ⟨h.1.differentiable (by simp), fun x => ⟨?_, ?_⟩⟩
  · have := h.2 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  · have := h.2 1 (by omega) x
    rwa [norm_iteratedFDeriv_one] at this

theorem s8f_GB_gaussReg {k : ℕ} {C c : ℝ} {σ : Euc d → ℝ} (h : s8f_GB (k + 1) C c σ) (hc : 0 < c) :
    s84_GaussReg σ := by
  obtain ⟨hd, hb⟩ := s8f_GB_basic h
  exact ⟨hd, C, c, h.nonneg, hc, hb⟩

theorem s8f_thermal_GB (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ) (K : ℕ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ s8f_GB K C c ρ := by
  have hs0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨hsm, hg⟩ := HRS.MS.Mov0.mv0_hgauss hd hs0 hsd ha hβ hρ
  have hsmK : ∀ n : ℕ, ContDiff ℝ n ρ := fun n => contDiff_infty.1 hsm n
  induction K with
  | zero =>
    obtain ⟨C, c, hc, hb⟩ := hg 0
    have hC : 0 ≤ C := by
      have := (norm_nonneg (iteratedFDeriv ℝ 0 ρ 0)).trans (hb 0)
      simpa using this
    refine ⟨C, c, hC, hc, hsmK 0, fun i hi x => ?_⟩
    have : i = 0 := by omega
    subst this
    exact hb x
  | succ K ih =>
    obtain ⟨C, c, hC, hc, hGB⟩ := ih
    obtain ⟨C', c', hc', hb'⟩ := hg (K + 1)
    have hC' : 0 ≤ C' := by
      have := (norm_nonneg (iteratedFDeriv ℝ (K + 1) ρ 0)).trans (hb' 0)
      simpa using this
    refine ⟨max C C', min c c', le_max_of_le_left hC, lt_min hc hc', ?_, ?_⟩
    · exact hsmK (K + 1)
    · intro i hi x
      rcases Nat.lt_or_ge i (K + 1) with hlt | hge
      · exact ((hGB.mono (le_max_left C C') (le_min hc.le hc'.le) (min_le_left c c')).2 i (by omega)) x
      · have : i = K + 1 := by omega
        subst this
        refine (hb' x).trans ?_
        exact mul_le_mul (le_max_right _ _)
          (Real.exp_le_exp.2 (by nlinarith [min_le_right c c', sq_nonneg ‖x‖])) (Real.exp_pos _).le
          (hC.trans (le_max_left _ _))

end HRS.MS.Wad
