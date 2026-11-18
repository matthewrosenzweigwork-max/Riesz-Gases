/-
# HRS.Equilibrium.HeatSplit -- the heat split `g = g_L + q - c` and trigonometric features (EXT-3, E5)

Source: main paper `A:eq:heat`, `A:eq:split` (TeX lines 3398-3420) and the first sentence of the
calibration subsection (`Ψ`, lines 3474-3476).  Plan: `docs/external/variance-plan.md`, row E5.

For `d ≥ 2`, `0 ≤ s < d`, `α = (d - s)/2`, `A = subA d s`, the subordination formula
`g(x) = A ∫_0^∞ t^{α-1} Ψ(x,t) dt` (`KernelAux.periodicRiesz_eq_integral`, `Ψ = psiFn`, `1 + Ψ` the
periodic heat kernel) is split at the heat time `τ`:

* `h_τ(x) = A ∫_0^τ t^{α-1} (1 + Ψ(x,t)) dt ≥ 0`   (heat-kernel positivity, Poisson summation),
* `b_τ = A τ^α / α`   (`= ∫ h_τ`),
* `g_τ(x) = A ∫_τ^∞ t^{α-1} Ψ(x,t) dt = ∑_{k ≠ 0} ĝ_τ(k) cos(2π k·x)` with the positive Fourier
  coefficients `ĝ_τ(k) = A ∫_τ^∞ t^{α-1} e^{-t|k|²} dt` (absolutely summable);

so that `g = g_τ + h_τ - b_τ` off the origin.  For a mode cutoff `L` (the box `|k_i| ≤ L`),
`g_L = ∑_{0<|k|≤L} ĝ_τ(k) cos(2πk·x)` (the coefficients of `g_τ` are retained, as in the source) and
`r_L = g_τ - g_L`, which has `|r_L| ≤ r_L(0) → 0` as `L → ∞`.  Then
`q = h_τ + r_L + r_L(0) ≥ 0`, `c = b_τ + r_L(0)`, `g = g_L + q - c` off `0`, and `‖q‖₁ = c`
(the latter derived from `∫ g = 0`).

Everything is stated as a conclusion (never as a structure field assumed as a hypothesis): the
structure `WeakSplit` carries data only.
-/
import HRS.Equilibrium.RepulsivePositive
import HRS.Equilibrium.PoleCavity

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.External

open HRS

namespace HeatSplit

variable {d : ℕ} {s : ℝ}

/-- The Mellin weight `t^{α-1}` of the Riesz kernel, `α = (d - s)/2`. -/
def hW (d : ℕ) (s : ℝ) (t : ℝ) : ℝ := t ^ (((d : ℝ) - s) / 2 - 1)

/-- The near part `h_τ(x) = A ∫_0^τ t^{α-1} (1 + Ψ(x,t)) dt` (positive). -/
def hNear (d : ℕ) (s : ℝ) (τ : ℝ) (x : Torus d) : ℝ :=
  KernelAux.subA d s * ∫ t in Ioc 0 τ, hW d s t * (1 + psiFn x t)

/-- The mass `b_τ = A τ^α / α` of the near part. -/
def hMass (d : ℕ) (s : ℝ) (τ : ℝ) : ℝ :=
  KernelAux.subA d s * (τ ^ (((d : ℝ) - s) / 2) / (((d : ℝ) - s) / 2))

/-- Fourier coefficients `ĝ_τ(k) = A ∫_τ^∞ t^{α-1} e^{-t|k|²} dt` of the smooth part (`0` at `k = 0`). -/
def hCoeff (d : ℕ) (s : ℝ) (τ : ℝ) (k : Lattice d) : ℝ :=
  if k = 0 then 0 else
    KernelAux.subA d s * ∫ t in Ioi τ, hW d s t * Real.exp (-t * Lattice.enorm k ^ 2)

/-- The smooth positive-Fourier part `g_τ = ∑_k ĝ_τ(k) cos(2πk·x)`. -/
def hSmooth (d : ℕ) (s : ℝ) (τ : ℝ) (x : Torus d) : ℝ :=
  ∑' k : Lattice d, hCoeff d s τ k * Torus.cosMode k x

/-- The finite symmetric set of modes `0 < ‖k‖_∞ ≤ L`. -/
def hModes (d : ℕ) (L : ℕ) : Finset (Lattice d) :=
  (Fintype.piFinset fun _ : Fin d => Finset.Icc (-(L : ℤ)) (L : ℤ)).erase 0

open Classical in
/-- The Fourier coefficients of the remainder `r_L`: those of `g_τ` outside the modes `hModes d L`. -/
def hRestCoeff (d : ℕ) (s : ℝ) (τ : ℝ) (L : ℕ) (k : Lattice d) : ℝ :=
  if k ∈ hModes d L then 0 else hCoeff d s τ k

/-- The finite trigonometric polynomial `g_L = ∑_{0<|k|≤L} ĝ_τ(k) cos(2πk·x)`. -/
def hGL (d : ℕ) (s : ℝ) (τ : ℝ) (L : ℕ) (x : Torus d) : ℝ :=
  ∑ k ∈ hModes d L, hCoeff d s τ k * Torus.cosMode k x

/-- The remainder `r_L = g_τ - g_L`, written as the series over the modes outside `hModes d L`. -/
def hRest (d : ℕ) (s : ℝ) (τ : ℝ) (L : ℕ) (x : Torus d) : ℝ :=
  ∑' k : Lattice d, hRestCoeff d s τ L k * Torus.cosMode k x

/-- `r_L(0) = ∑_{|k|>L} ĝ_τ(k)`. -/
def hRest0 (d : ℕ) (s : ℝ) (τ : ℝ) (L : ℕ) : ℝ :=
  ∑' k : Lattice d, hRestCoeff d s τ L k

/-- The positive kernel `q = h_τ + r_L + r_L(0)`. -/
def hQ (d : ℕ) (s : ℝ) (τ : ℝ) (L : ℕ) (x : Torus d) : ℝ :=
  hNear d s τ x + hRest d s τ L x + hRest0 d s τ L

/-- The constant `c = b_τ + r_L(0)`. -/
def hC (d : ℕ) (s : ℝ) (τ : ℝ) (L : ℕ) : ℝ := hMass d s τ + hRest0 d s τ L

/-! ### Elementary facts about the weight, the constant and the coefficients -/

theorem hexp_pos (hsd : s < d) : 0 < ((d : ℝ) - s) / 2 := by linarith

theorem subA_pos' (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) : 0 < KernelAux.subA d s := by
  unfold KernelAux.subA
  have := rieszConst_pos hd hs0 hsd
  have := Real.Gamma_pos_of_pos (show 0 < ((d:ℝ) - s) / 2 by linarith)
  have : 0 < (2 * Real.pi) ^ (s - d) := Real.rpow_pos_of_pos (by positivity) _
  positivity

theorem hW_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ hW d s t := Real.rpow_nonneg ht.le _

theorem hW_pos {t : ℝ} (ht : 0 < t) : 0 < hW d s t := Real.rpow_pos_of_pos ht _

theorem measurable_hW : Measurable (hW d s) := by
  unfold hW; fun_prop

theorem hCoeff_zero (τ : ℝ) : hCoeff d s τ 0 = 0 := by simp [hCoeff]

theorem hCoeff_nonneg (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 ≤ τ) (k : Lattice d) :
    0 ≤ hCoeff d s τ k := by
  unfold hCoeff
  split_ifs with hk
  · exact le_rfl
  · refine mul_nonneg (KernelAux.subA_nonneg hd hs0 hsd) (setIntegral_nonneg measurableSet_Ioi fun t ht => ?_)
    exact mul_nonneg (hW_nonneg (lt_of_le_of_lt hτ ht)) (Real.exp_pos _).le


theorem hW_tail_pointwise {τ : ℝ} (hτ : 0 < τ) (k : Lattice d) (hk : k ≠ 0) {t : ℝ} (ht : τ < t) :
    hW d s t * Real.exp (-t * Lattice.enorm k ^ 2) ≤
      Real.exp τ * Real.exp (-τ * Lattice.enorm k ^ 2) * (Real.exp (-t) * hW d s t) := by
  have hw0 : 0 ≤ hW d s t := hW_nonneg (hτ.trans ht)
  have he1 : 1 ≤ Lattice.enorm k ^ 2 := by nlinarith [one_le_enorm k hk]
  have hE : Real.exp (-t * Lattice.enorm k ^ 2) ≤
      Real.exp τ * Real.exp (-τ * Lattice.enorm k ^ 2) * Real.exp (-t) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.2 ht.le) (sub_nonneg.2 he1)]
  calc hW d s t * Real.exp (-t * Lattice.enorm k ^ 2)
      ≤ hW d s t * (Real.exp τ * Real.exp (-τ * Lattice.enorm k ^ 2) * Real.exp (-t)) :=
        mul_le_mul_of_nonneg_left hE hw0
    _ = _ := by ring

theorem hW_tail_bound {τ : ℝ} (hτ : 0 < τ) (x : Torus d) (k : Lattice d) {t : ℝ} (ht : τ < t) :
    ‖hW d s t * (if k = 0 then 0 else Real.exp (-t * Lattice.enorm k ^ 2) * Torus.cosMode k x)‖ ≤
      Real.exp τ * Real.exp (-τ * Lattice.enorm k ^ 2) * (Real.exp (-t) * hW d s t) := by
  have ht0 : 0 < t := hτ.trans ht
  have hw0 : 0 ≤ hW d s t := hW_nonneg ht0
  have hM : 0 ≤ Real.exp τ * Real.exp (-τ * Lattice.enorm k ^ 2) * (Real.exp (-t) * hW d s t) :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (mul_nonneg (Real.exp_pos _).le hw0)
  by_cases hk : k = 0
  · rw [if_pos hk, mul_zero, norm_zero]
    exact hM
  · rw [if_neg hk, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hw0, abs_of_pos (Real.exp_pos _)]
    calc hW d s t * (Real.exp (-t * Lattice.enorm k ^ 2) * |Torus.cosMode k x|)
        ≤ hW d s t * (Real.exp (-t * Lattice.enorm k ^ 2) * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (abs_cosMode_le k x) (Real.exp_pos _).le) hw0
      _ = hW d s t * Real.exp (-t * Lattice.enorm k ^ 2) := by rw [mul_one]
      _ ≤ _ := hW_tail_pointwise hτ k hk ht

theorem integrableOn_exp_hW (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * hW d s t) (Ioi τ) :=
  (Real.GammaIntegral_convergent (hexp_pos hsd)).mono_set (Ioi_subset_Ioi hτ.le)

/-- `∑_k ĝ_τ(k) < ∞` for `τ > 0`. -/
theorem summable_hCoeff (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) :
    Summable (hCoeff d s τ) := by
  obtain ⟨C0, hC0⟩ : ∃ C0 : ℝ, C0 = ∫ t in Ioi τ, Real.exp (-t) * hW d s t := ⟨_, rfl⟩
  have hC0nn : 0 ≤ C0 := by
    rw [hC0]
    exact setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (Real.exp_pos _).le (hW_nonneg (hτ.trans ht))
  have hbd : ∀ k : Lattice d, hCoeff d s τ k ≤
      KernelAux.subA d s * ((Real.exp τ * C0) * Real.exp (-τ * Lattice.enorm k ^ 2)) := by
    intro k
    by_cases hk : k = 0
    · rw [hk, hCoeff_zero]
      exact mul_nonneg (KernelAux.subA_nonneg hd hs0 hsd)
        (mul_nonneg (mul_nonneg (Real.exp_pos _).le hC0nn) (Real.exp_pos _).le)
    · unfold hCoeff
      rw [if_neg hk]
      refine mul_le_mul_of_nonneg_left ?_ (KernelAux.subA_nonneg hd hs0 hsd)
      calc ∫ t in Ioi τ, hW d s t * Real.exp (-t * Lattice.enorm k ^ 2)
          ≤ ∫ t in Ioi τ, Real.exp τ * Real.exp (-τ * Lattice.enorm k ^ 2) *
              (Real.exp (-t) * hW d s t) :=
            integral_mono_of_nonneg
              (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
                mul_nonneg (hW_nonneg (hτ.trans ht)) (Real.exp_pos _).le)
              (Integrable.const_mul (integrableOn_exp_hW hsd hτ) _)
              (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => hW_tail_pointwise hτ k hk ht)
        _ = Real.exp τ * Real.exp (-τ * Lattice.enorm k ^ 2) * C0 := by
            rw [integral_const_mul, hC0]
        _ = (Real.exp τ * C0) * Real.exp (-τ * Lattice.enorm k ^ 2) := by ring
  refine Summable.of_nonneg_of_le (fun k => hCoeff_nonneg hd hs0 hsd hτ.le k) hbd ?_
  exact ((summable_gauss_lattice d τ hτ).mul_left (Real.exp τ * C0)).mul_left (KernelAux.subA d s)

/-- Fourier series of the smooth part: the lattice sum may be exchanged with the heat-time integral. -/
theorem hSmooth_eq_integral (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) (x : Torus d) :
    hSmooth d s τ x = KernelAux.subA d s * ∫ t in Ioi τ, hW d s t * psiFn x t := by
  obtain ⟨C0, hC0⟩ : ∃ C0 : ℝ, C0 = ∫ t in Ioi τ, Real.exp (-t) * hW d s t := ⟨_, rfl⟩
  have hMint : ∀ k : Lattice d, IntegrableOn (fun t : ℝ => Real.exp τ *
      Real.exp (-τ * Lattice.enorm k ^ 2) * (Real.exp (-t) * hW d s t)) (Ioi τ) :=
    fun k => Integrable.const_mul (integrableOn_exp_hW hsd hτ) _
  have hMsum : Summable fun k : Lattice d => ∫ t in Ioi τ, Real.exp τ *
      Real.exp (-τ * Lattice.enorm k ^ 2) * (Real.exp (-t) * hW d s t) := by
    have e : (fun k : Lattice d => ∫ t in Ioi τ, Real.exp τ *
        Real.exp (-τ * Lattice.enorm k ^ 2) * (Real.exp (-t) * hW d s t)) =
        fun k => (Real.exp τ * C0) * Real.exp (-τ * Lattice.enorm k ^ 2) := by
      funext k
      rw [integral_const_mul, ← hC0]
      ring
    rw [e]
    exact (summable_gauss_lattice d τ hτ).mul_left (Real.exp τ * C0)
  have key := Repulsive.rb_integral_psi_eq_tsum (d := d) (M := fun k t => Real.exp τ *
      Real.exp (-τ * Lattice.enorm k ^ 2) * (Real.exp (-t) * hW d s t)) measurableSet_Ioi x
    (measurable_hW (d := d) (s := s)) hMint hMsum (fun k t ht => hW_tail_bound hτ x k ht)
  rw [key, ← tsum_mul_left]
  unfold hSmooth
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0
  · simp [hk, hCoeff]
  · simp only [hCoeff, if_neg hk]
    have e2 : ∀ t : ℝ, hW d s t * (Real.exp (-t * Lattice.enorm k ^ 2) * Torus.cosMode k x) =
        hW d s t * Real.exp (-t * Lattice.enorm k ^ 2) * Torus.cosMode k x :=
      fun t => by ring
    simp only [e2]
    rw [integral_mul_const]
    ring


/-! ### The near part and the identity `g = g_τ + h_τ - b_τ` -/

theorem hNear_nonneg (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (τ : ℝ) (x : Torus d) :
    0 ≤ hNear d s τ x := by
  unfold hNear
  refine mul_nonneg (KernelAux.subA_nonneg hd hs0 hsd) (setIntegral_nonneg measurableSet_Ioc fun t ht => ?_)
  exact mul_nonneg (hW_nonneg ht.1) (Repulsive.one_add_psiFn_nonneg x ht.1)

theorem measurable_hNear (τ : ℝ) : Measurable (hNear d s τ) := by
  have hF : Measurable fun p : Torus d × ℝ => hW d s p.2 * (1 + psiFn p.1 p.2) :=
    ((measurable_hW (d := d) (s := s)).comp measurable_snd).mul
      (measurable_const.add Repulsive.measurable_psiFn_uncurry)
  unfold hNear
  exact (Repulsive.rb_measurable_integral hF).const_mul _

theorem integral_hW_Ioc (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) :
    ∫ t in Ioc 0 τ, hW d s t = τ ^ (((d : ℝ) - s) / 2) / (((d : ℝ) - s) / 2) := by
  have ha := hexp_pos hsd
  rw [← intervalIntegral.integral_of_le hτ.le]
  unfold hW
  rw [integral_rpow (Or.inl (by linarith))]
  rw [show ((d:ℝ) - s) / 2 - 1 + 1 = ((d:ℝ) - s) / 2 by ring, Real.zero_rpow ha.ne', sub_zero]

theorem integrableOn_hW_Ioc (hsd : s < d) (τ : ℝ) : IntegrableOn (hW d s) (Ioc 0 τ) := by
  have ha := hexp_pos hsd
  have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := τ) (r := ((d:ℝ) - s) / 2 - 1)
    (by linarith))
  rcases le_total 0 τ with h | h
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h).mp this
  · simp [Ioc_eq_empty_of_le h]

/-- The heat-split identity `g = g_τ + h_τ - b_τ` off the origin (`A:eq:heat`). -/
theorem periodicRiesz_eq_split (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ)
    (x : Torus d) (hx : x ≠ 0) :
    periodicRiesz d s x = hSmooth d s τ x + hNear d s τ x - hMass d s τ := by
  have hI : IntegrableOn (fun t : ℝ => hW d s t * psiFn x t) (Ioi 0) := KernelAux.integrableOn_psi hsd x hx
  have h1 : IntegrableOn (fun t : ℝ => hW d s t * psiFn x t) (Ioc 0 τ) := hI.mono_set Ioc_subset_Ioi_self
  have h2 : IntegrableOn (fun t : ℝ => hW d s t * psiFn x t) (Ioi τ) :=
    hI.mono_set (Ioi_subset_Ioi hτ.le)
  have hsplit : ∫ t in Ioi (0:ℝ), hW d s t * psiFn x t =
      (∫ t in Ioc 0 τ, hW d s t * psiFn x t) + ∫ t in Ioi τ, hW d s t * psiFn x t := by
    rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi h1 h2, Ioc_union_Ioi_eq_Ioi hτ.le]
  have hnear : ∫ t in Ioc 0 τ, hW d s t * (1 + psiFn x t) =
      (∫ t in Ioc 0 τ, hW d s t * psiFn x t) + ∫ t in Ioc 0 τ, hW d s t := by
    rw [← integral_add h1 (integrableOn_hW_Ioc hsd τ)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only; ring
  rw [KernelAux.periodicRiesz_eq_integral hd hs0 hsd x hx]
  show KernelAux.subA d s * ∫ t in Ioi (0:ℝ), hW d s t * psiFn x t = _
  rw [hsplit, hSmooth_eq_integral hd hs0 hsd hτ, hNear.eq_1, hMass, ← integral_hW_Ioc hsd hτ, hnear]
  ring

/-! ### The finite part `g_L`, the remainder `r_L` and the positive kernel `q` -/

theorem zero_notMem_hModes (L : ℕ) : (0 : Lattice d) ∉ hModes d L := by
  simp [hModes]

theorem ne_zero_of_mem_hModes {L : ℕ} {k : Lattice d} (hk : k ∈ hModes d L) : k ≠ 0 := by
  rintro rfl; exact zero_notMem_hModes L hk

theorem hRestCoeff_nonneg (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 ≤ τ) (L : ℕ)
    (k : Lattice d) : 0 ≤ hRestCoeff d s τ L k := by
  unfold hRestCoeff
  split_ifs
  · exact le_rfl
  · exact hCoeff_nonneg hd hs0 hsd hτ k

theorem hRestCoeff_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 ≤ τ) (L : ℕ)
    (k : Lattice d) : hRestCoeff d s τ L k ≤ hCoeff d s τ k := by
  unfold hRestCoeff
  split_ifs
  · exact hCoeff_nonneg hd hs0 hsd hτ k
  · exact le_rfl

theorem summable_hRestCoeff (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) (L : ℕ) :
    Summable (hRestCoeff d s τ L) :=
  Summable.of_nonneg_of_le (hRestCoeff_nonneg hd hs0 hsd hτ.le L) (hRestCoeff_le hd hs0 hsd hτ.le L)
    (summable_hCoeff hd hs0 hsd hτ)

theorem summable_hRestCoeff_mul (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) (L : ℕ)
    (x : Torus d) : Summable fun k : Lattice d => hRestCoeff d s τ L k * Torus.cosMode k x := by
  refine Summable.of_norm_bounded (summable_hRestCoeff hd hs0 hsd hτ L) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hRestCoeff_nonneg hd hs0 hsd hτ.le L k)]
  exact mul_le_of_le_one_right (hRestCoeff_nonneg hd hs0 hsd hτ.le L k) (abs_cosMode_le k x)

theorem summable_hCoeff_mul (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ)
    (x : Torus d) : Summable fun k : Lattice d => hCoeff d s τ k * Torus.cosMode k x := by
  refine Summable.of_norm_bounded (summable_hCoeff hd hs0 hsd hτ) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hCoeff_nonneg hd hs0 hsd hτ.le k)]
  exact mul_le_of_le_one_right (hCoeff_nonneg hd hs0 hsd hτ.le k) (abs_cosMode_le k x)

/-- `g_τ = g_L + r_L`. -/
theorem hSmooth_eq_add (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) (L : ℕ)
    (x : Torus d) : hSmooth d s τ x = hGL d s τ L x + hRest d s τ L x := by
  classical
  have h1 : (fun k : Lattice d => hCoeff d s τ k * Torus.cosMode k x) =
      fun k => (if k ∈ hModes d L then hCoeff d s τ k * Torus.cosMode k x else 0) +
        hRestCoeff d s τ L k * Torus.cosMode k x := by
    funext k
    unfold hRestCoeff
    by_cases hk : k ∈ hModes d L <;> simp [hk]
  have hfin : Summable fun k : Lattice d =>
      (if k ∈ hModes d L then hCoeff d s τ k * Torus.cosMode k x else 0) :=
    summable_of_finite_support (Set.Finite.subset (hModes d L).finite_toSet fun k hk => by
      by_contra h
      exact hk (if_neg (by simpa using h)))
  have hsum : ∑' k : Lattice d, (if k ∈ hModes d L then hCoeff d s τ k * Torus.cosMode k x else 0) =
      ∑ k ∈ hModes d L, hCoeff d s τ k * Torus.cosMode k x := by
    rw [tsum_eq_sum (s := hModes d L) (fun k hk => if_neg hk)]
    exact Finset.sum_congr rfl fun k hk => if_pos hk
  have hS : ∑' k : Lattice d, hCoeff d s τ k * Torus.cosMode k x = ∑' k : Lattice d,
      ((if k ∈ hModes d L then hCoeff d s τ k * Torus.cosMode k x else 0) +
        hRestCoeff d s τ L k * Torus.cosMode k x) := by rw [h1]
  unfold hSmooth hGL hRest
  rw [hS, hfin.tsum_add (summable_hRestCoeff_mul hd hs0 hsd hτ L x), hsum]

theorem hRest0_nonneg (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 ≤ τ) (L : ℕ) :
    0 ≤ hRest0 d s τ L :=
  tsum_nonneg fun k => hRestCoeff_nonneg hd hs0 hsd hτ L k

theorem abs_hRest_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) (L : ℕ)
    (x : Torus d) : |hRest d s τ L x| ≤ hRest0 d s τ L := by
  unfold hRest hRest0
  have := norm_tsum_le_tsum_norm (summable_hRestCoeff_mul hd hs0 hsd hτ L x).norm
  rw [Real.norm_eq_abs] at this
  refine this.trans ?_
  refine Summable.tsum_le_tsum (fun k => ?_) (summable_hRestCoeff_mul hd hs0 hsd hτ L x).norm
    (summable_hRestCoeff hd hs0 hsd hτ L)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hRestCoeff_nonneg hd hs0 hsd hτ.le L k)]
  exact mul_le_of_le_one_right (hRestCoeff_nonneg hd hs0 hsd hτ.le L k) (abs_cosMode_le k x)

theorem hRest_add_nonneg (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) (L : ℕ)
    (x : Torus d) : 0 ≤ hRest d s τ L x + hRest0 d s τ L := by
  have := abs_hRest_le hd hs0 hsd hτ L x
  have := neg_abs_le (hRest d s τ L x)
  linarith

theorem continuous_hRest (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) (L : ℕ) :
    Continuous (hRest d s τ L) := by
  unfold hRest
  refine continuous_tsum (fun k => continuous_const.mul (Torus.continuous_cosMode k))
    (summable_hRestCoeff hd hs0 hsd hτ L) fun k x => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hRestCoeff_nonneg hd hs0 hsd hτ.le L k)]
  exact mul_le_of_le_one_right (hRestCoeff_nonneg hd hs0 hsd hτ.le L k) (abs_cosMode_le k x)

theorem hQ_nonneg (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) (L : ℕ) (x : Torus d) :
    0 ≤ hQ d s τ L x := by
  unfold hQ
  have := hNear_nonneg hd hs0 hsd τ x
  have := hRest_add_nonneg hd hs0 hsd hτ L x
  linarith

theorem measurable_hQ (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) (L : ℕ) :
    Measurable (hQ d s τ L) := by
  unfold hQ
  exact ((measurable_hNear τ).add (continuous_hRest hd hs0 hsd hτ L).measurable).add measurable_const

/-- **The split** `g = g_L + q - c` off the origin (`A:eq:split`). -/
theorem periodicRiesz_eq_gL_add (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) (L : ℕ)
    (x : Torus d) (hx : x ≠ 0) :
    periodicRiesz d s x = hGL d s τ L x + hQ d s τ L x - hC d s τ L := by
  rw [periodicRiesz_eq_split hd hs0 hsd hτ x hx, hSmooth_eq_add hd hs0 hsd hτ L x]
  unfold hQ hC
  ring

/-- The coefficients of `g_L` are positive. -/
theorem hCoeff_pos (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) {k : Lattice d}
    (hk : k ≠ 0) : 0 < hCoeff d s τ k := by
  unfold hCoeff
  rw [if_neg hk]
  refine mul_pos (subA_pos' hd hs0 hsd) ?_
  have hint : IntegrableOn (fun t : ℝ => hW d s t * Real.exp (-t * Lattice.enorm k ^ 2)) (Ioi τ) := by
    refine Integrable.mono' ((integrableOn_exp_hW hsd hτ).const_mul (Real.exp τ * Real.exp (-τ * Lattice.enorm k ^ 2)))
      ((measurable_hW (d := d) (s := s)).mul (by fun_prop)).aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hW_nonneg (hτ.trans ht)) (Real.exp_pos _).le)]
    exact hW_tail_pointwise hτ k hk ht
  rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
    mul_nonneg (hW_nonneg (hτ.trans ht)) (Real.exp_pos _).le) hint]
  have : Function.support (fun t : ℝ => hW d s t * Real.exp (-t * Lattice.enorm k ^ 2)) ∩ Ioi τ = Ioi τ := by
    ext t
    simp only [mem_inter_iff, Function.mem_support, mem_Ioi]
    constructor
    · exact fun h => h.2
    · intro ht
      exact ⟨(mul_pos (hW_pos (hτ.trans ht)) (Real.exp_pos _)).ne', ht⟩
  rw [this]
  simp

/-! ### Smallness of `r_L(0)` and `b_τ` -/

theorem hCoeff_eq_split (hd : 2 ≤ d) (L : ℕ) (k : Lattice d) (τ : ℝ) :
    hCoeff d s τ k = (if k ∈ hModes d L then hCoeff d s τ k else 0) + hRestCoeff d s τ L k := by
  unfold hRestCoeff
  by_cases hk : k ∈ hModes d L <;> simp [hk]

theorem hRest0_eq (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) (L : ℕ) :
    hRest0 d s τ L = (∑' k : Lattice d, hCoeff d s τ k) - ∑ k ∈ hModes d L, hCoeff d s τ k := by
  classical
  have hfin : Summable fun k : Lattice d => (if k ∈ hModes d L then hCoeff d s τ k else 0) :=
    summable_of_finite_support (Set.Finite.subset (hModes d L).finite_toSet fun k hk => by
      by_contra h
      exact hk (if_neg (by simpa using h)))
  have hsum : ∑' k : Lattice d, (if k ∈ hModes d L then hCoeff d s τ k else 0) =
      ∑ k ∈ hModes d L, hCoeff d s τ k := by
    rw [tsum_eq_sum (s := hModes d L) (fun k hk => if_neg hk)]
    exact Finset.sum_congr rfl fun k hk => if_pos hk
  have hS : ∑' k : Lattice d, hCoeff d s τ k = ∑' k : Lattice d,
      ((if k ∈ hModes d L then hCoeff d s τ k else 0) + hRestCoeff d s τ L k) :=
    tsum_congr fun k => hCoeff_eq_split hd L k τ
  rw [hS, hfin.tsum_add (summable_hRestCoeff hd hs0 hsd hτ L), hsum]
  unfold hRest0
  ring

theorem tendsto_insert_hModes (d : ℕ) :
    Tendsto (fun L : ℕ => insert (0 : Lattice d) (hModes d L)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨b.sup fun k => Finset.univ.sup fun j => (k j).natAbs, fun L hL => ?_⟩
  intro k hk
  by_cases h0 : k = 0
  · simp [h0]
  · refine Finset.mem_insert_of_mem ?_
    simp only [hModes, Finset.mem_erase, Fintype.mem_piFinset, Finset.mem_Icc]
    refine ⟨h0, fun j => ?_⟩
    have h1 : (k j).natAbs ≤ b.sup fun k => Finset.univ.sup fun j => (k j).natAbs :=
      (Finset.le_sup (f := fun j => (k j).natAbs) (Finset.mem_univ j)).trans
        (Finset.le_sup (f := fun k : Lattice d => Finset.univ.sup fun j => (k j).natAbs) hk)
    have h2 : (k j).natAbs ≤ L := h1.trans hL
    have h3 : |k j| ≤ (L : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast h2
    exact abs_le.mp h3

theorem tendsto_hRest0 (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) :
    Tendsto (fun L : ℕ => hRest0 d s τ L) atTop (𝓝 0) := by
  have hT := (summable_hCoeff hd hs0 hsd hτ).hasSum
  have h1 := hT.comp (tendsto_insert_hModes d)
  have h2 : (fun L : ℕ => ∑ k ∈ insert (0 : Lattice d) (hModes d L), hCoeff d s τ k) =
      fun L : ℕ => ∑ k ∈ hModes d L, hCoeff d s τ k := by
    funext L
    rw [Finset.sum_insert (zero_notMem_hModes L), hCoeff_zero, zero_add]
  have h3 : Tendsto (fun L : ℕ => ∑ k ∈ hModes d L, hCoeff d s τ k) atTop
      (𝓝 (∑' k : Lattice d, hCoeff d s τ k)) := by
    have := h1
    simp only [Function.comp_def] at this
    rwa [h2] at this
  have h4 := (tendsto_const_nhds (x := ∑' k : Lattice d, hCoeff d s τ k)).sub h3
  rw [sub_self] at h4
  refine h4.congr fun L => ?_
  rw [hRest0_eq hd hs0 hsd hτ L]

theorem tendsto_hMass (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    Tendsto (fun τ : ℝ => hMass d s τ) (𝓝[>] 0) (𝓝 0) := by
  have ha := hexp_pos hsd
  have h1 : Tendsto (fun τ : ℝ => τ ^ (((d : ℝ) - s) / 2)) (𝓝 0) (𝓝 0) := by
    have := (Real.continuous_rpow_const ha.le).tendsto 0
    rwa [Real.zero_rpow ha.ne'] at this
  have h2 := ((h1.div_const (((d : ℝ) - s) / 2)).const_mul (KernelAux.subA d s))
  simp only [zero_div, mul_zero] at h2
  exact h2.mono_left nhdsWithin_le_nhds

/-- Smallness: for every `ε > 0` there are `τ ∈ (0, 1]` and `L` with `c = b_τ + r_L(0) ≤ ε`; and
then every larger `L` works too. -/
theorem exists_small_hC (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, hC d s τ L ≤ ε := by
  have h1 := (tendsto_hMass hd hs0 hsd).eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨τ, ⟨hm, hI⟩, hτ⟩ := ((h1.and (Ioo_mem_nhdsGT one_pos)).and self_mem_nhdsWithin).exists
  have hτ : 0 < τ := hτ
  have h3 := (tendsto_hRest0 hd hs0 hsd hτ).eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp h3
  refine ⟨τ, hτ, hI.2.le, L₀, fun L hL => ?_⟩
  have := hL₀ L hL
  unfold hC
  linarith


/-! ### `‖q‖₁ = c` -/

theorem integral_cosMode_of_ne {k : Lattice d} (hk : k ≠ 0) : ∫ x : Torus d, Torus.cosMode k x = 0 := by
  have h := Torus.integral_mode (d := d) k
  rw [if_neg hk] at h
  have h2 : ∫ x : Torus d, (Torus.mode k x).re = (∫ x : Torus d, Torus.mode k x).re :=
    integral_re (Torus.integrable_mode k)
  show ∫ x : Torus d, (Torus.mode k x).re = 0
  rw [h2, h]; simp

theorem continuous_hGL (τ : ℝ) (L : ℕ) : Continuous (hGL d s τ L) := by
  unfold hGL
  exact continuous_finset_sum _ fun k _ => continuous_const.mul (Torus.continuous_cosMode k)

theorem integral_hGL (τ : ℝ) (L : ℕ) : ∫ x : Torus d, hGL d s τ L x = 0 := by
  unfold hGL
  have hint : ∀ k ∈ hModes d L, Integrable (fun x : Torus d => hCoeff d s τ k * Torus.cosMode k x) :=
    fun k _ => (continuous_const.mul (Torus.continuous_cosMode k)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_finset_sum _ hint]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [integral_const_mul, integral_cosMode_of_ne (ne_zero_of_mem_hModes hk), mul_zero]

theorem integral_periodicRiesz (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∫ x : Torus d, periodicRiesz d s x = 0 := by
  have h := KernelAux.integral_periodicRiesz_mode hd hs0 hsd (0 : Lattice d)
  have h0 : rieszCoeff d s (0 : Lattice d) = 0 := by simp [rieszCoeff]
  simp only [neg_zero, Torus.mode_zero, one_mul, h0, Complex.ofReal_zero] at h
  have h2 : (∫ x : Torus d, ((periodicRiesz d s x : ℝ) : ℂ)) = ((∫ x : Torus d, periodicRiesz d s x : ℝ) : ℂ) :=
    integral_ofReal
  rw [h2] at h
  exact_mod_cast h

/-- `q = g - g_L + c` almost everywhere. -/
theorem hQ_ae_eq (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) (L : ℕ) :
    hQ d s τ L =ᵐ[volume] fun x => periodicRiesz d s x - hGL d s τ L x + hC d s τ L := by
  filter_upwards [KernelAux.torus_ae_ne (by omega : 0 < d)] with x hx
  rw [periodicRiesz_eq_gL_add hd hs0 hsd hτ L x hx]
  ring

theorem integrable_hQ (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) (L : ℕ) :
    Integrable (hQ d s τ L) := by
  have h1 : Integrable (fun x : Torus d => periodicRiesz d s x - hGL d s τ L x + hC d s τ L) :=
    ((KernelAux.integrable_periodicRiesz hd hs0 hsd).sub
      ((continuous_hGL τ L).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).add
      (integrable_const _)
  exact h1.congr (hQ_ae_eq hd hs0 hsd hτ L).symm

/-- `∫ q = c` (so `‖q‖_{L¹} = c`, as `q ≥ 0`). -/
theorem integral_hQ (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) (L : ℕ) :
    ∫ x : Torus d, hQ d s τ L x = hC d s τ L := by
  rw [integral_congr_ae (hQ_ae_eq hd hs0 hsd hτ L)]
  rw [integral_add (f := fun x => periodicRiesz d s x - hGL d s τ L x) (g := fun _ => hC d s τ L)
      ((KernelAux.integrable_periodicRiesz hd hs0 hsd).sub
      ((continuous_hGL τ L).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)))
      (integrable_const _),
    integral_sub (KernelAux.integrable_periodicRiesz hd hs0 hsd)
      ((continuous_hGL τ L).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
    integral_periodicRiesz hd hs0 hsd, integral_hGL]
  simp

theorem hC_nonneg (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) (L : ℕ) :
    0 ≤ hC d s τ L := by
  rw [← integral_hQ hd hs0 hsd hτ L]
  exact integral_nonneg fun x => hQ_nonneg hd hs0 hsd hτ L x

theorem eLpNorm_one_hQ (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) (L : ℕ) :
    eLpNorm (hQ d s τ L) 1 volume = ENNReal.ofReal (hC d s τ L) := by
  have h1 : ENNReal.ofReal (∫ x : Torus d, hQ d s τ L x) = ∫⁻ x, ENNReal.ofReal (hQ d s τ L x) :=
    ofReal_integral_eq_lintegral_ofReal (integrable_hQ hd hs0 hsd hτ L)
      (Filter.Eventually.of_forall (hQ_nonneg hd hs0 hsd hτ L))
  rw [integral_hQ hd hs0 hsd hτ L] at h1
  rw [h1, eLpNorm_one_eq_lintegral_enorm (measurable_hQ hd hs0 hsd hτ L).aestronglyMeasurable]
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_of_nonneg (hQ_nonneg hd hs0 hsd hτ L x)]

/-! ### Trigonometric features -/

/-- Cos/sin features of a finite trigonometric polynomial with nonnegative coefficients:
`∑_{k∈Λ} a_k cos(2πk·(x - y)) = ⟪Ψ x, Ψ y⟫` with `Ψ(x) = (√a_k cos(2πk·x), √a_k sin(2πk·x))_{k∈Λ}`. -/
theorem exists_features (Λ : Finset (Lattice d)) (a : Lattice d → ℝ) (ha : ∀ k ∈ Λ, 0 ≤ a k) :
    ∃ (M : ℕ) (Ψ : Torus d → EuclideanSpace ℝ (Fin M)),
      (∀ x y : Torus d, ∑ k ∈ Λ, a k * Torus.cosMode k (x - y) = inner ℝ (Ψ x) (Ψ y)) ∧
      ∀ x : Torus d, ‖Ψ x‖ ^ 2 = ∑ k ∈ Λ, a k * Torus.cosMode k 0 := by
  classical
  let ι := Λ × Bool
  let f : ι → Torus d → ℝ := fun i x =>
    if i.2 then Real.sqrt (a i.1) * Torus.cosMode i.1 x else Real.sqrt (a i.1) * Torus.sinMode i.1 x
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have key : ∀ x y : Torus d, ∑ k ∈ Λ, a k * Torus.cosMode k (x - y) =
      inner ℝ (WithLp.toLp 2 (fun m : Fin (Fintype.card ι) => f (e.symm m) x) :
        EuclideanSpace ℝ (Fin (Fintype.card ι)))
        (WithLp.toLp 2 (fun m : Fin (Fintype.card ι) => f (e.symm m) y)) := by
    intro x y
    rw [PiLp.inner_apply]
    simp only [WithLp.ofLp_toLp, RCLike.inner_apply, conj_trivial]
    rw [Equiv.sum_comp e.symm (fun i => f i y * f i x)]
    rw [Fintype.sum_prod_type]
    rw [← Finset.sum_coe_sort Λ (fun k => a k * Torus.cosMode k (x - y))]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Fintype.sum_bool, f, if_true, Bool.false_eq_true, if_false]
    rw [Repulsive.rp04_cosMode_sub]
    have hs := Real.mul_self_sqrt (ha k.1 k.2)
    linear_combination (-(Torus.cosMode (k : Lattice d) x * Torus.cosMode (k : Lattice d) y +
      Torus.sinMode (k : Lattice d) x * Torus.sinMode (k : Lattice d) y)) * hs
  refine ⟨Fintype.card ι, fun x => WithLp.toLp 2 (fun m => f (e.symm m) x), key, fun x => ?_⟩
  have h := key x x
  rw [sub_self] at h
  show ‖(WithLp.toLp 2 (fun m => f (e.symm m) x) : EuclideanSpace ℝ (Fin (Fintype.card ι)))‖ ^ 2 = _
  rw [← real_inner_self_eq_norm_sq]
  exact h.symm


/-! ### The singular envelope of `q`

For `y` in the box, `1 + Ψ(boxPt y, t) ≤ K t^{-d/2} exp(-π² |y_j|²/(2t))` (`t ≤ 1`, `j` any coordinate;
`KernelAux.theta_gauss_bound`).  Integrating against `t^{α-1}` over `(0, τ]` gives a bound by
`singEnvelope s |y|`: below the heat time `|y|²` use `e^{-v} ≤ C v^{-p}` with `p = (s+1)/2`, above it use
`e^{-v} ≤ 1`. -/

/-- `exp(-c/t) ≤ κ c^{-p} t^p` with `κ = p^p e^{-p}`. -/
theorem exp_neg_div_le {p c t : ℝ} (hp : 0 < p) (hc : 0 < c) (ht : 0 < t) :
    Real.exp (-(c / t)) ≤ (p ^ p * Real.exp (-p)) * c ^ (-p) * t ^ p := by
  have he := KernelAux.exp_neg_le_rpow hp (v := c / t) (by positivity)
  have hbu : (c / t) ^ (-p) = c ^ (-p) * t ^ p := by
    rw [Real.div_rpow hc.le ht.le, Real.rpow_neg ht.le, div_inv_eq_mul]
  rw [hbu] at he
  linarith

/-- Pointwise majorant of `t^{-s/2-1} exp(-c/t)` below the heat time `r²`: `κ c^{-p} t^{-1/2}`. -/
theorem majorant_one {s c t : ℝ} (hs : 0 ≤ s) (hc : 0 < c) (ht : 0 < t) :
    t ^ (-s / 2 - 1) * Real.exp (-(c / t)) ≤
      ((((s + 1) / 2) ^ ((s + 1) / 2) * Real.exp (-((s + 1) / 2))) * c ^ (-((s + 1) / 2))) *
        t ^ (-(1 / 2 : ℝ)) := by
  have hp : 0 < (s + 1) / 2 := by linarith
  have h := exp_neg_div_le hp hc ht
  have h0 : 0 ≤ t ^ (-s / 2 - 1) := Real.rpow_nonneg ht.le _
  calc t ^ (-s / 2 - 1) * Real.exp (-(c / t))
      ≤ t ^ (-s / 2 - 1) * ((((s + 1) / 2) ^ ((s + 1) / 2) * Real.exp (-((s + 1) / 2))) *
          c ^ (-((s + 1) / 2)) * t ^ ((s + 1) / 2)) := mul_le_mul_of_nonneg_left h h0
    _ = ((((s + 1) / 2) ^ ((s + 1) / 2) * Real.exp (-((s + 1) / 2))) * c ^ (-((s + 1) / 2))) *
          (t ^ (-s / 2 - 1) * t ^ ((s + 1) / 2)) := by ring
    _ = _ := by
        rw [← Real.rpow_add ht]
        congr 2
        ring


theorem integral_G1 {K r : ℝ} (hr : 0 < r) :
    ∫ t in Ioc (0:ℝ) (r ^ 2), K * t ^ (-(1 / 2 : ℝ)) = K * (2 * r) := by
  rw [integral_const_mul, ← intervalIntegral.integral_of_le (by positivity)]
  rw [integral_rpow (Or.inl (by norm_num))]
  have h1 : (-(1 / 2 : ℝ) + 1) = 1 / 2 := by norm_num
  rw [h1, Real.zero_rpow (by norm_num), sub_zero]
  have h2 : (r ^ 2) ^ (1 / 2 : ℝ) = r := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hr.le]
  rw [h2]
  ring

theorem integral_G2_le {s r : ℝ} (hs : 0 ≤ s) (hr : 0 < r) (hr1 : r ≤ 1 / 2) :
    ∫ t in Ioc (r ^ 2) 1, t ^ (-s / 2 - 1) ≤ (2 + 2 / s) * singEnvelope s r := by
  have hr2 : 0 < r ^ 2 := by positivity
  have hr21 : r ^ 2 ≤ 1 := by nlinarith
  rw [← intervalIntegral.integral_of_le hr21]
  by_cases hs0 : s = 0
  · subst hs0
    have e : (fun t : ℝ => t ^ (-(0:ℝ) / 2 - 1)) = fun t => t⁻¹ := by
      funext t; norm_num [Real.rpow_neg_one]
    rw [e, integral_inv_of_pos hr2 one_pos]
    simp only [singEnvelope, if_true]
    have : Real.log (1 / r ^ 2) = -2 * Real.log r := by
      rw [one_div, Real.log_inv, Real.log_pow]; push_cast; ring
    rw [this]
    have hlog : Real.log r ≤ 0 := Real.log_nonpos hr.le (by linarith)
    rw [abs_of_nonpos hlog]
    simp
    nlinarith [abs_nonneg (Real.log r)]
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    rw [integral_rpow (Or.inr ⟨by intro h; apply hs0; linarith, by
      rw [Set.mem_uIcc]; push Not; constructor <;> intro h <;> linarith⟩)]
    have e1 : (-s / 2 - 1 + 1) = -s / 2 := by ring
    rw [e1, Real.one_rpow]
    have e2 : (r ^ 2) ^ (-s / 2) = r ^ (-s) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]; congr 1; push_cast; ring
    rw [e2]
    simp only [singEnvelope, if_neg hs0]
    have hrs : 0 < r ^ (-s) := Real.rpow_pos_of_pos hr _
    have hrs1 : 1 ≤ r ^ (-s) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr (by linarith) (by linarith)
    have e3 : (1 - r ^ (-s)) / (-s / 2) = (2 / s) * (r ^ (-s) - 1) := by field_simp; ring
    rw [e3]
    have e4 : r ^ (-s) = r ^ (-s) := rfl
    have : (r ^ (-s)) = (r ^ s)⁻¹ := Real.rpow_neg hr.le s
    have hsq : (2 / s) * (r ^ (-s) - 1) ≤ (2 + 2 / s) * (1 + r ^ (-s)) := by
      have h2s : 0 < 2 / s := by positivity
      nlinarith
    exact hsq


theorem one_le_singEnvelope {s r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 2) (hs : 0 ≤ s) :
    1 ≤ singEnvelope s r ∧ r ^ (-s) ≤ singEnvelope s r := by
  unfold singEnvelope
  by_cases h : s = 0
  · simp only [h, if_true, neg_zero, Real.rpow_zero]
    constructor <;> linarith [abs_nonneg (Real.log r)]
  · simp only [h, if_false]
    have : 0 < r ^ (-s) := Real.rpow_pos_of_pos hr _
    constructor <;> linarith

/-- The sharp near-field integral bound. -/
theorem integral_near_le {s : ℝ} (hs : 0 ≤ s) {c r τ : ℝ} (hc : 0 < c) (hr : 0 < r) (hr1 : r ≤ 1 / 2)
    (hτ1 : τ ≤ 1) {f : ℝ → ℝ} (hf0 : ∀ t ∈ Ioc (0:ℝ) τ, 0 ≤ f t)
    (hf : ∀ t ∈ Ioc (0:ℝ) τ, f t ≤ t ^ (-s / 2 - 1) * Real.exp (-(c * r ^ 2 / t))) :
    ∫ t in Ioc (0:ℝ) τ, f t ≤
      ((2 * (((s + 1) / 2) ^ ((s + 1) / 2) * Real.exp (-((s + 1) / 2))) * c ^ (-((s + 1) / 2))) + 2 + 2 / s) *
        singEnvelope s r := by
  have hp : 0 < (s + 1) / 2 := by linarith
  have hr2 : 0 < r ^ 2 := by positivity
  have hr21 : r ^ 2 ≤ 1 := by nlinarith
  set κ : ℝ := ((s + 1) / 2) ^ ((s + 1) / 2) * Real.exp (-((s + 1) / 2)) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set K1 : ℝ := κ * (c * r ^ 2) ^ (-((s + 1) / 2)) with hK1
  have hK10 : 0 ≤ K1 := by positivity
  set G1 : ℝ → ℝ := fun t => K1 * t ^ (-(1 / 2 : ℝ)) with hG1
  set G2 : ℝ → ℝ := fun t => t ^ (-s / 2 - 1) with hG2
  set Φ : ℝ → ℝ := (Ioc (0:ℝ) (r ^ 2)).indicator G1 + (Ioc (r ^ 2) 1).indicator G2 with hΦ
  have hG1i : IntegrableOn G1 (Ioc (0:ℝ) (r ^ 2)) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := r ^ 2) (r := -(1 / 2 : ℝ))
      (by norm_num))
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hr2.le).mp this).const_mul K1
  have hG2i : IntegrableOn G2 (Ioc (r ^ 2) 1) := by
    have := (intervalIntegral.intervalIntegrable_rpow (μ := volume) (a := r ^ 2) (b := 1) (r := -s / 2 - 1)
      (Or.inr (by rw [Set.mem_uIcc]; push Not; constructor <;> intro h <;> linarith)))
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hr21).mp this
  have hΦi : Integrable Φ := (hG1i.integrable_indicator measurableSet_Ioc).add
    (hG2i.integrable_indicator measurableSet_Ioc)
  have hG10 : ∀ t, 0 < t → 0 ≤ G1 t := fun t ht => mul_nonneg hK10 (Real.rpow_nonneg ht.le _)
  have hG20 : ∀ t, 0 < t → 0 ≤ G2 t := fun t ht => Real.rpow_nonneg ht.le _
  have hΦ0 : ∀ t, 0 ≤ Φ t := by
    intro t
    simp only [hΦ, Pi.add_apply, indicator]
    split_ifs with h1 h2 h2
    · exact add_nonneg (hG10 t h1.1) (hG20 t (hr2.trans h2.1))
    · exact add_nonneg (hG10 t h1.1) le_rfl
    · exact add_nonneg le_rfl (hG20 t (hr2.trans h2.1))
    · simp
  have h1 : ∫ t in Ioc (0:ℝ) τ, f t ≤ ∫ t in Ioc (0:ℝ) τ, Φ t := by
    refine integral_mono_of_nonneg (ae_restrict_of_forall_mem measurableSet_Ioc hf0) hΦi.integrableOn
      (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
    have ht0 := ht.1
    refine le_trans (hf t ht) ?_
    simp only [hΦ, Pi.add_apply]
    by_cases hle : t ≤ r ^ 2
    · rw [indicator_of_mem (show t ∈ Ioc (0:ℝ) (r ^ 2) from ⟨ht0, hle⟩),
        indicator_of_notMem (show t ∉ Ioc (r ^ 2) 1 from fun h => absurd h.1 (not_lt.mpr hle)), add_zero]
      exact majorant_one hs (mul_pos hc hr2) ht0
    · push Not at hle
      rw [indicator_of_notMem (show t ∉ Ioc (0:ℝ) (r ^ 2) from fun h => absurd h.2 (not_le.mpr hle)),
        indicator_of_mem (show t ∈ Ioc (r ^ 2) 1 from ⟨hle, ht.2.trans hτ1⟩), zero_add]
      calc t ^ (-s / 2 - 1) * Real.exp (-(c * r ^ 2 / t)) ≤ t ^ (-s / 2 - 1) * 1 := by
            gcongr
            exact Real.exp_le_one_iff.mpr (by
              have : 0 ≤ c * r ^ 2 / t := by positivity
              linarith)
        _ = G2 t := mul_one _
  have h2 : ∫ t in Ioc (0:ℝ) τ, Φ t ≤ ∫ t, Φ t :=
    setIntegral_le_integral hΦi (Filter.Eventually.of_forall hΦ0)
  have h3 : ∫ t, Φ t = (∫ t in Ioc (0:ℝ) (r ^ 2), G1 t) + ∫ t in Ioc (r ^ 2) 1, G2 t := by
    simp only [hΦ, Pi.add_apply]
    rw [integral_add (hG1i.integrable_indicator measurableSet_Ioc)
      (hG2i.integrable_indicator measurableSet_Ioc),
      integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc]
  have h4 : ∫ t in Ioc (0:ℝ) (r ^ 2), G1 t = K1 * (2 * r) := integral_G1 hr
  have h5 := integral_G2_le hs hr hr1
  obtain ⟨hs1, hs2⟩ := one_le_singEnvelope hr hr1 hs
  have h6 : K1 = κ * c ^ (-((s + 1) / 2)) * r ^ (-(s + 1)) := by
    rw [hK1, Real.mul_rpow hc.le hr2.le, ← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    have : ((2:ℕ):ℝ) * (-((s + 1) / 2)) = -(s + 1) := by push_cast; ring
    rw [this]; ring
  have h7 : K1 * (2 * r) = 2 * κ * c ^ (-((s + 1) / 2)) * r ^ (-s) := by
    rw [h6]
    have : r ^ (-(s + 1)) * r = r ^ (-s) := by
      rw [← Real.rpow_add_one hr.ne']; congr 1; ring
    calc κ * c ^ (-((s + 1) / 2)) * r ^ (-(s + 1)) * (2 * r)
        = 2 * κ * c ^ (-((s + 1) / 2)) * (r ^ (-(s + 1)) * r) := by ring
      _ = _ := by rw [this]
  have hcp : 0 ≤ 2 * κ * c ^ (-((s + 1) / 2)) := by positivity
  calc _ ≤ _ := h1.trans h2
    _ = (∫ t in Ioc (0:ℝ) (r ^ 2), G1 t) + ∫ t in Ioc (r ^ 2) 1, G2 t := h3
    _ ≤ 2 * κ * c ^ (-((s + 1) / 2)) * r ^ (-s) + (2 + 2 / s) * singEnvelope s r := by
        rw [h4, h7]; linarith
    _ ≤ 2 * κ * c ^ (-((s + 1) / 2)) * singEnvelope s r + (2 + 2 / s) * singEnvelope s r := by
        gcongr
    _ = _ := by ring


/-- The Gaussian majorant constant of the periodic heat kernel. -/
def heatConst (d : ℕ) : ℝ :=
  (Real.sqrt Real.pi * ∑' n : ℤ, Real.exp (-(Real.pi ^ 2 / 8) * (n : ℝ) ^ 2)) ^ d

theorem heatConst_nonneg (d : ℕ) : 0 ≤ heatConst d := by
  unfold heatConst
  exact pow_nonneg (mul_nonneg (Real.sqrt_nonneg _) (tsum_nonneg fun _ => (Real.exp_pos _).le)) _

/-- Gaussian majorant of the periodic heat kernel on the box: for `0 < t ≤ 1`,
`0 ≤ 1 + Ψ(y,t) ≤ K t^{-d/2} exp(-(π²/2) |y_j|²/t)`. -/
theorem one_add_psi_le {y : Fin d → ℝ} (hy : ∀ i, |y i| ≤ 1 / 2) (j : Fin d) {t : ℝ} (ht : 0 < t)
    (ht1 : t ≤ 1) :
    1 + psiFn (KernelAux.boxPt y) t ≤
      heatConst d * t ^ (-(d : ℝ) / 2) * Real.exp (-((Real.pi ^ 2 / 2) * |y j| ^ 2 / t)) := by
  obtain ⟨_, hΘ⟩ := KernelAux.theta_gauss_bound y hy ht ht1 j
  rw [← psi_eq _ ht]
  refine hΘ.trans (le_of_eq ?_)
  rw [mul_pow, KernelAux.sqrt_div_pow_eq d ht, heatConst, mul_pow]
  have : (Real.pi ^ 2 * y j ^ 2 / (2 * t)) = (Real.pi ^ 2 / 2) * |y j| ^ 2 / t := by
    rw [sq_abs]; field_simp
  rw [this]
  ring


/-- Constant in the envelope bound of `h_τ`. -/
def nearConst (d : ℕ) (s : ℝ) : ℝ :=
  KernelAux.subA d s * max (heatConst d) 1 *
    ((2 * (((s + 1) / 2) ^ ((s + 1) / 2) * Real.exp (-((s + 1) / 2))) *
        (Real.pi ^ 2 / 2) ^ (-((s + 1) / 2))) + 2 + 2 / s)

theorem hNear_le_box (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    {y : Fin d → ℝ} (hy : ∀ i, |y i| ≤ 1 / 2) (j : Fin d) (hj : ∀ i, |y i| ≤ |y j|) (hy0 : y ≠ 0) :
    hNear d s τ (KernelAux.boxPt y) ≤ nearConst d s * singEnvelope s |y j| := by
  have hrpos : 0 < |y j| := by
    rcases Classical.em (y j = 0) with h | h
    · exfalso
      apply hy0
      funext i
      have := hj i
      rw [h, abs_zero] at this
      exact abs_nonpos_iff.mp this
    · exact abs_pos.mpr h
  have hr1 : |y j| ≤ 1 / 2 := hy j
  set K' : ℝ := max (heatConst d) 1 with hK'
  have hK'pos : 0 < K' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hpc : 0 < Real.pi ^ 2 / 2 := by positivity
  set f : ℝ → ℝ := fun t => hW d s t * (1 + psiFn (KernelAux.boxPt y) t) / K' with hf
  have hf0 : ∀ t ∈ Ioc (0:ℝ) τ, 0 ≤ f t := fun t ht =>
    div_nonneg (mul_nonneg (hW_nonneg ht.1) (Repulsive.one_add_psiFn_nonneg _ ht.1)) hK'pos.le
  have hfb : ∀ t ∈ Ioc (0:ℝ) τ, f t ≤
      t ^ (-s / 2 - 1) * Real.exp (-((Real.pi ^ 2 / 2) * |y j| ^ 2 / t)) := by
    intro t ht
    have ht0 := ht.1
    have h1 := one_add_psi_le hy j ht0 (ht.2.trans hτ1)
    have h2 : hW d s t * (1 + psiFn (KernelAux.boxPt y) t) ≤
        hW d s t * (heatConst d * t ^ (-(d : ℝ) / 2) * Real.exp (-((Real.pi ^ 2 / 2) * |y j| ^ 2 / t))) :=
      mul_le_mul_of_nonneg_left h1 (hW_nonneg ht0)
    have h3 : hW d s t * (heatConst d * t ^ (-(d : ℝ) / 2) * Real.exp (-((Real.pi ^ 2 / 2) * |y j| ^ 2 / t)))
        = heatConst d * (t ^ (-s / 2 - 1) * Real.exp (-((Real.pi ^ 2 / 2) * |y j| ^ 2 / t))) := by
      have : hW d s t * t ^ (-(d : ℝ) / 2) = t ^ (-s / 2 - 1) := by
        unfold hW
        rw [← Real.rpow_add ht0]; congr 1; ring
      calc _ = (hW d s t * t ^ (-(d : ℝ) / 2)) * (heatConst d * Real.exp (-((Real.pi ^ 2 / 2) * |y j| ^ 2 / t))) := by ring
        _ = _ := by rw [this]; ring
    have h4 : 0 ≤ t ^ (-s / 2 - 1) * Real.exp (-((Real.pi ^ 2 / 2) * |y j| ^ 2 / t)) :=
      mul_nonneg (Real.rpow_nonneg ht0.le _) (Real.exp_pos _).le
    simp only [hf]
    rw [div_le_iff₀ hK'pos]
    calc hW d s t * (1 + psiFn (KernelAux.boxPt y) t)
        ≤ heatConst d * (t ^ (-s / 2 - 1) * Real.exp (-((Real.pi ^ 2 / 2) * |y j| ^ 2 / t))) := h2.trans h3.le
      _ ≤ K' * (t ^ (-s / 2 - 1) * Real.exp (-((Real.pi ^ 2 / 2) * |y j| ^ 2 / t))) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) h4
      _ = _ := by ring
  have hint := integral_near_le hs0 hpc hrpos hr1 hτ1 hf0 hfb
  have e : ∫ t in Ioc (0:ℝ) τ, hW d s t * (1 + psiFn (KernelAux.boxPt y) t) =
      K' * ∫ t in Ioc (0:ℝ) τ, f t := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hf]
    field_simp
  unfold hNear
  rw [e]
  have hA := KernelAux.subA_nonneg hd hs0 hsd
  calc KernelAux.subA d s * (K' * ∫ t in Ioc (0:ℝ) τ, f t)
      ≤ KernelAux.subA d s * (K' * (((2 * (((s + 1) / 2) ^ ((s + 1) / 2) * Real.exp (-((s + 1) / 2))) *
        (Real.pi ^ 2 / 2) ^ (-((s + 1) / 2))) + 2 + 2 / s) * singEnvelope s |y j|)) := by gcongr
    _ = _ := by unfold nearConst; ring


theorem eucDist_boxPt {y : Fin d → ℝ} (hy : ∀ i, |y i| ≤ 1 / 2) :
    Torus.eucDist (KernelAux.boxPt y) 0 = Real.sqrt (∑ i, (y i) ^ 2) := by
  unfold Torus.eucDist
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : ‖((KernelAux.boxPt y : Torus d) i - (0 : Torus d) i)‖ = |y i| := by
    have : ((KernelAux.boxPt y : Torus d) i - (0 : Torus d) i) = ((y i : ℝ) : UnitAddCircle) := by
      simp
    rw [this]
    refine (AddCircle.norm_coe_eq_abs_iff (p := (1:ℝ)) one_ne_zero).2 ?_
    rw [abs_one]
    have := hy i
    linarith
  rw [h2, sq_abs]

theorem one_le_singEnvelope' {s e : ℝ} (he : 0 ≤ e) : 1 ≤ singEnvelope s e := by
  unfold singEnvelope
  by_cases h : s = 0
  · simp only [h, if_true]; linarith [abs_nonneg (Real.log e)]
  · simp only [h, if_false]
    have : 0 ≤ e ^ (-s) := Real.rpow_nonneg he _
    linarith

/-- Comparison of the envelope at the sup-norm `r = |y_j|` with the one at the Euclidean distance. -/
theorem singEnvelope_le_of_boxPt (hd : 1 ≤ d) (hs : 0 ≤ s) {y : Fin d → ℝ} (hy : ∀ i, |y i| ≤ 1 / 2)
    (j : Fin d) (hj : ∀ i, |y i| ≤ |y j|) (hr : 0 < |y j|) :
    singEnvelope s |y j| ≤
      (((d : ℝ) ^ (s / 2)) + Real.log d) * singEnvelope s (Torus.eucDist (KernelAux.boxPt y) 0) := by
  rw [eucDist_boxPt hy]
  set r := |y j| with hr_def
  set S : ℝ := ∑ i, (y i) ^ 2 with hS
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hSlow : r ^ 2 ≤ S := by
    rw [hr_def, sq_abs]
    have := Finset.single_le_sum (f := fun i => (y i) ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    simpa using this
  have hSup : S ≤ d * r ^ 2 := by
    calc S = ∑ i, (y i) ^ 2 := rfl
      _ ≤ ∑ _i : Fin d, r ^ 2 := Finset.sum_le_sum fun i _ => by
          rw [← sq_abs (y i)]; exact pow_le_pow_left₀ (abs_nonneg _) (hj i) 2
      _ = d * r ^ 2 := by simp
  set e := Real.sqrt S with he
  have he0 : 0 < e := Real.sqrt_pos.mpr (lt_of_lt_of_le (by positivity) hSlow)
  have her : r ≤ e := by
    rw [he]; exact Real.le_sqrt_of_sq_le hSlow
  have hed : e ≤ Real.sqrt d * r := by
    rw [he, ← Real.sqrt_sq hr.le, ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hSup
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg hd'
  have hsE := one_le_singEnvelope' (s := s) he0.le
  have hdpos : 0 < (d : ℝ) := by linarith
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdpos
  have hr_ge : e / Real.sqrt d ≤ r := by rw [div_le_iff₀ hsd]; linarith
  have hrpos : 0 < e / Real.sqrt d := by positivity
  unfold singEnvelope
  by_cases h0 : s = 0
  · simp only [h0, if_true, zero_div, Real.rpow_zero]
    have hr1 : r < 1 := by have := hy j; rw [hr_def]; linarith
    have hlr : Real.log r ≤ 0 := Real.log_nonpos hr.le hr1.le
    have h1 : Real.log (e / Real.sqrt d) ≤ Real.log r := Real.log_le_log hrpos hr_ge
    rw [Real.log_div he0.ne' hsd.ne', Real.log_sqrt hdpos.le] at h1
    rw [abs_of_nonpos hlr]
    have h2 : -Real.log e ≤ |Real.log e| := neg_le_abs _
    have h3 : 1 + -Real.log r ≤ (1 + Real.log d) * (1 + |Real.log e|) := by
      nlinarith [abs_nonneg (Real.log e), mul_nonneg hlogd (abs_nonneg (Real.log e))]
    simpa using h3
  · simp only [h0, if_false]
    have h1 : r ^ (-s) ≤ (e / Real.sqrt d) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos hrpos hr_ge (by linarith)
    have h2 : (e / Real.sqrt d) ^ (-s) = (d : ℝ) ^ (s / 2) * e ^ (-s) := by
      rw [Real.div_rpow he0.le hsd.le, Real.rpow_neg hsd.le, Real.rpow_neg he0.le, div_eq_mul_inv, inv_inv,
        Real.sqrt_eq_rpow, ← Real.rpow_mul hdpos.le]
      ring_nf
    rw [h2] at h1
    have hdp : 1 ≤ (d : ℝ) ^ (s / 2) := Real.one_le_rpow hd' (by linarith)
    have he1 : 0 ≤ e ^ (-s) := Real.rpow_nonneg he0.le _
    nlinarith [mul_nonneg hlogd (add_nonneg zero_le_one he1)]


theorem nearConst_nonneg (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) : 0 ≤ nearConst d s := by
  unfold nearConst
  have := KernelAux.subA_nonneg hd hs0 hsd
  have := heatConst_nonneg d
  have : 0 ≤ max (heatConst d) 1 := le_max_of_le_right zero_le_one
  positivity

/-- **Envelope**: `q(x) ≤ B · singEnvelope s |x|` for `x ≠ 0` (for `τ ≤ 1`). -/
theorem hQ_le_envelope (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (L : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : Torus d, x ≠ 0 → hQ d s τ L x ≤ B * singEnvelope s (Torus.eucDist x 0) := by
  have hd0 : 0 < d := by omega
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd0)
  have hCenv : 0 ≤ ((d : ℝ) ^ (s / 2)) + Real.log d := by
    have : 0 ≤ (d : ℝ) ^ (s / 2) := Real.rpow_nonneg (by positivity) _
    linarith
  refine ⟨nearConst d s * (((d : ℝ) ^ (s / 2)) + Real.log d) + 2 * hRest0 d s τ L,
    add_nonneg (mul_nonneg (nearConst_nonneg hd hs0 hsd) hCenv)
      (mul_nonneg zero_le_two (hRest0_nonneg hd hs0 hsd hτ.le L)), fun x hx => ?_⟩
  choose y hy1 hy2 using fun i => exists_rep (x i)
  have hxy : x = KernelAux.boxPt y := funext hy2
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hx
    rw [hxy]; funext i; simp
  obtain ⟨j, hj⟩ := KernelAux.exists_argmax hd0 y
  have hjmax : ∀ i, |y i| ≤ |y j| := fun i => by
    rw [← hj]
    have := norm_le_pi_norm y i
    rwa [Real.norm_eq_abs] at this
  have hrpos : 0 < |y j| := by
    rcases Classical.em (y j = 0) with h | h
    · exfalso
      apply hy0
      funext i
      have := hjmax i
      rw [h, abs_zero] at this
      exact abs_nonpos_iff.mp this
    · exact abs_pos.mpr h
  have h1 := hNear_le_box hd hs0 hsd hτ hτ1 hy1 j hjmax hy0
  have h2 := singEnvelope_le_of_boxPt (s := s) (by omega) hs0 hy1 j hjmax hrpos
  have h3 := abs_hRest_le hd hs0 hsd hτ L x
  have h4 := one_le_singEnvelope' (s := s) (e := Torus.eucDist x 0) (Real.sqrt_nonneg _)
  have h5 := hRest0_nonneg hd hs0 hsd hτ.le L
  rw [← hxy] at h1 h2
  unfold hQ
  have h6 : hNear d s τ x ≤ nearConst d s * (((d : ℝ) ^ (s / 2)) + Real.log d) *
      singEnvelope s (Torus.eucDist x 0) := by
    calc hNear d s τ x ≤ nearConst d s * singEnvelope s |y j| := h1
      _ ≤ nearConst d s * ((((d : ℝ) ^ (s / 2)) + Real.log d) * singEnvelope s (Torus.eucDist x 0)) := by
          gcongr
          exact nearConst_nonneg hd hs0 hsd
      _ = _ := by ring
  have := (abs_le.mp h3).2
  nlinarith


/-! ### Convolution bound -/

/-- `sup_x ∫ q(x - y) ρ(y) dy ≤ Λ ‖q‖₁` for a density `0 ≤ ρ ≤ Λ`. -/
theorem integral_hQ_conv_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) (L : ℕ)
    {ρ : Torus d → ℝ} (hρm : Measurable ρ) {Λ : ℝ} (hρ0 : ∀ y, 0 ≤ ρ y) (hρΛ : ∀ y, ρ y ≤ Λ)
    (x : Torus d) : ∫ y : Torus d, hQ d s τ L (x - y) * ρ y ≤ Λ * hC d s τ L := by
  haveI : (volume : Measure (Torus d)).IsNegInvariant :=
    MeasureTheory.Measure.pi.isNegInvariant (fun _ : Fin d => (volume : Measure UnitAddCircle))
  have hint : Integrable (fun y : Torus d => hQ d s τ L (x - y)) :=
    (integrable_hQ hd hs0 hsd hτ L).comp_sub_left x
  have hint2 : Integrable (fun y : Torus d => hQ d s τ L (x - y) * Λ) := hint.mul_const Λ
  have hΛ0 : 0 ≤ Λ := (hρ0 x).trans (hρΛ x)
  calc ∫ y : Torus d, hQ d s τ L (x - y) * ρ y ≤ ∫ y : Torus d, hQ d s τ L (x - y) * Λ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y =>
          mul_nonneg (hQ_nonneg hd hs0 hsd hτ L _) (hρ0 y)) hint2
          (Filter.Eventually.of_forall fun y => ?_)
        exact mul_le_mul_of_nonneg_left (hρΛ y) (hQ_nonneg hd hs0 hsd hτ L _)
    _ = Λ * hC d s τ L := by
        rw [integral_mul_const, integral_sub_left_eq_self (fun y => hQ d s τ L y) volume x,
          integral_hQ hd hs0 hsd hτ L]
        ring

end HeatSplit

/-! ### The packaged split -/

open HeatSplit

/-- **Weak split data** `g = g_L + q - c` (`A:eq:split`): the heat time `τ`, the mode cutoff `L`, the finite
trigonometric polynomial `g_L`, the positive kernel `q` and the constant `c`.  Only data; all properties are
conclusions of `weakSplit_spec` / `exists_weakSplit`. -/
structure WeakSplit (d : ℕ) (s : ℝ) where
  τ : ℝ
  L : ℕ
  gL : Torus d → ℝ
  q : Torus d → ℝ
  c : ℝ

/-- The split at heat time `τ` and mode cutoff `L`. -/
def weakSplit (d : ℕ) (s : ℝ) (τ : ℝ) (L : ℕ) : WeakSplit d s :=
  ⟨τ, L, hGL d s τ L, hQ d s τ L, hC d s τ L⟩

variable {d : ℕ} {s : ℝ}


/-- **The heat split** (`A:eq:heat`, `A:eq:split`): for every heat time `τ ∈ (0, 1]` and every mode cutoff
`L`, `weakSplit d s τ L` has all the properties of the weak split. -/
theorem weakSplit_spec (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (L : ℕ) :
    let sp := weakSplit d s τ L
    sp.τ = τ ∧ sp.L = L ∧
    (∀ x : Torus d, x ≠ 0 → periodicRiesz d s x = sp.gL x + sp.q x - sp.c) ∧
    (∀ᵐ x : Torus d, periodicRiesz d s x = sp.gL x + sp.q x - sp.c) ∧
    Measurable sp.q ∧ (∀ x, 0 ≤ sp.q x) ∧ Integrable sp.q ∧ ∫ x, sp.q x = sp.c ∧
    eLpNorm sp.q 1 volume = ENNReal.ofReal sp.c ∧ 0 ≤ sp.c ∧
    (∃ (h r : Torus d → ℝ) (b r₀ : ℝ), (∀ x, 0 ≤ h x) ∧ (∀ x, |r x| ≤ r₀) ∧ 0 ≤ b ∧ 0 ≤ r₀ ∧
      (∀ x, sp.q x = h x + r x + r₀) ∧ sp.c = b + r₀) ∧
    (∃ (Λ : Finset (Lattice d)) (a : Lattice d → ℝ), 0 ∉ Λ ∧ (∀ k ∈ Λ, 0 < a k) ∧
      ∀ x, sp.gL x = ∑ k ∈ Λ, a k * Torus.cosMode k x) ∧
    Continuous sp.gL ∧ (∫ x, sp.gL x = 0) ∧
    (∃ B : ℝ, 0 ≤ B ∧ ∀ x : Torus d, x ≠ 0 → sp.q x ≤ B * singEnvelope s (Torus.eucDist x 0)) ∧
    (∃ (M : ℕ) (Ψ : Torus d → EuclideanSpace ℝ (Fin M)),
      (∀ x y : Torus d, sp.gL (x - y) = inner ℝ (Ψ x) (Ψ y)) ∧ ∀ x : Torus d, ‖Ψ x‖ ^ 2 = sp.gL 0) ∧
    (∀ (ρ : Torus d → ℝ) (Λ : ℝ), Measurable ρ → (∀ y, 0 ≤ ρ y) → (∀ y, ρ y ≤ Λ) →
      ∀ x : Torus d, ∫ y : Torus d, sp.q (x - y) * ρ y ≤ Λ * sp.c) := by
  intro sp
  refine ⟨rfl, rfl, fun x hx => periodicRiesz_eq_gL_add hd hs0 hsd hτ L x hx, ?_,
    measurable_hQ hd hs0 hsd hτ L, hQ_nonneg hd hs0 hsd hτ L, integrable_hQ hd hs0 hsd hτ L,
    integral_hQ hd hs0 hsd hτ L, eLpNorm_one_hQ hd hs0 hsd hτ L, hC_nonneg hd hs0 hsd hτ L,
    ⟨hNear d s τ, hRest d s τ L, hMass d s τ, hRest0 d s τ L, hNear_nonneg hd hs0 hsd τ,
      abs_hRest_le hd hs0 hsd hτ L, ?_, hRest0_nonneg hd hs0 hsd hτ.le L, fun x => rfl, rfl⟩,
    ⟨hModes d L, hCoeff d s τ, zero_notMem_hModes L,
      fun k hk => hCoeff_pos hd hs0 hsd hτ (ne_zero_of_mem_hModes hk), fun x => rfl⟩,
    continuous_hGL τ L, integral_hGL τ L, hQ_le_envelope hd hs0 hsd hτ hτ1 L, ?_,
    fun ρ Λ hρm hρ0 hρΛ x => integral_hQ_conv_le hd hs0 hsd hτ L hρm hρ0 hρΛ x⟩
  · filter_upwards [KernelAux.torus_ae_ne (by omega : 0 < d)] with x hx
    exact periodicRiesz_eq_gL_add hd hs0 hsd hτ L x hx
  · have : 0 ≤ hMass d s τ := by
      unfold hMass
      have := hexp_pos hsd
      have := KernelAux.subA_nonneg hd hs0 hsd
      positivity
    exact this
  · obtain ⟨M, Ψ, h1, h2⟩ := exists_features (hModes d L) (hCoeff d s τ)
      (fun k hk => (hCoeff_pos hd hs0 hsd hτ (ne_zero_of_mem_hModes hk)).le)
    exact ⟨M, Ψ, h1, h2⟩

/-- **Existence of the weak split with small mass** (choose `τ`, then `L`): for every `ε > 0` there is a
split `g = g_L + q - c` with `‖q‖_{L¹} = c ≤ ε` (together with all the properties of `weakSplit_spec`). -/
theorem exists_weakSplit (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε) :
    ∃ sp : WeakSplit d s, 0 < sp.τ ∧ sp.τ ≤ 1 ∧ sp.c ≤ ε ∧
    (∀ x : Torus d, x ≠ 0 → periodicRiesz d s x = sp.gL x + sp.q x - sp.c) ∧
    (∀ᵐ x : Torus d, periodicRiesz d s x = sp.gL x + sp.q x - sp.c) ∧
    Measurable sp.q ∧ (∀ x, 0 ≤ sp.q x) ∧ Integrable sp.q ∧ ∫ x, sp.q x = sp.c ∧
    eLpNorm sp.q 1 volume = ENNReal.ofReal sp.c ∧ 0 ≤ sp.c ∧
    (∃ (h r : Torus d → ℝ) (b r₀ : ℝ), (∀ x, 0 ≤ h x) ∧ (∀ x, |r x| ≤ r₀) ∧ 0 ≤ b ∧ 0 ≤ r₀ ∧
      (∀ x, sp.q x = h x + r x + r₀) ∧ sp.c = b + r₀) ∧
    (∃ (Λ : Finset (Lattice d)) (a : Lattice d → ℝ), 0 ∉ Λ ∧ (∀ k ∈ Λ, 0 < a k) ∧
      ∀ x, sp.gL x = ∑ k ∈ Λ, a k * Torus.cosMode k x) ∧
    Continuous sp.gL ∧ (∫ x, sp.gL x = 0) ∧
    (∃ B : ℝ, 0 ≤ B ∧ ∀ x : Torus d, x ≠ 0 → sp.q x ≤ B * singEnvelope s (Torus.eucDist x 0)) ∧
    (∃ (M : ℕ) (Ψ : Torus d → EuclideanSpace ℝ (Fin M)),
      (∀ x y : Torus d, sp.gL (x - y) = inner ℝ (Ψ x) (Ψ y)) ∧ ∀ x : Torus d, ‖Ψ x‖ ^ 2 = sp.gL 0) ∧
    (∀ (ρ : Torus d → ℝ) (Λ : ℝ), Measurable ρ → (∀ y, 0 ≤ ρ y) → (∀ y, ρ y ≤ Λ) →
      ∀ x : Torus d, ∫ y : Torus d, sp.q (x - y) * ρ y ≤ Λ * sp.c) := by
  obtain ⟨τ, hτ, hτ1, L₀, hL₀⟩ := exists_small_hC hd hs0 hsd hε
  obtain ⟨-, -, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ :=
    weakSplit_spec hd hs0 hsd hτ hτ1 L₀
  exact ⟨weakSplit d s τ L₀, hτ, hτ1, hL₀ L₀ le_rfl, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, h16, h17⟩

/-- Smallness `‖q‖_{L¹} = c → 0`: choose `τ`, then `L`. -/
theorem weakSplit_small (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, (weakSplit d s τ L).c ≤ ε :=
  exists_small_hC hd hs0 hsd hε


end HRS.External

end
