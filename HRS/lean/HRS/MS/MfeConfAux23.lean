import HRS.MS.MfeConfAux22

/-!
# S.B.1, packet F3 (part 4): the Gibbs weight bound and the decay of the trajectory, its flux `J = ρ u_V` and `∂_t ρ`

* `sb1_E_le`: `exp(-βN F_N^k(X,ρ)) ≤ exp(βN(C_G + κM₁))` for every configuration, uniformly in the admissible kernel `k`.
* `Sb1Tr3 D T C B C3 ρ`: the trajectory bundle `Sb1Traj` with the sharper decay `‖D^l ρ_r(y)‖ ≤ C3 (1+|y|)^{-(d+3)}`, `l ≤ 3`
  (from `IsRegularDensityW`), and `ρ > 0`.
* `sb1J D h k y = h(y) (u_V)_k(y)` (flux component); `sb1_J_bound`, `sb1_dJ_bound`, `sb1_A_bound'`:
  `|J_k| ≤ C_J (1+|y|)^{-(d+2)}`, `|∂_k J_k| ≤ C_dJ (1+|y|)^{-(d+2)}`, `|A(h)| ≤ d C_dJ (1+|y|)^{-(d+2)}`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section Weight

variable {s : ℝ} {k : Euc d → ℝ} {ρ : Euc d → ℝ} {Cρ M1 : ℝ}

theorem sb1_E_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hN : 1 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    (hk : Sb1KerU d s k) (R : Sb1Rho ρ Cρ M1) (X : Whole.EucConfig d N) :
    Real.exp (-β * N * sb1En k ρ X) ≤ Real.exp (β * N * (sb1CG d s Cρ M1 + sb1kap s * M1)) := by
  apply Real.exp_le_exp.2
  have hκ := sb1kap_nonneg s
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  set A : ℝ := ∑ i, Real.log (1 + ‖X i‖) with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => sb1_log_nonneg _
  set S : ℝ := ∑ i, ∑ j ∈ Finset.univ.erase i, k (X i - X j) with hS
  have hS' : -S ≤ sb1kap s * (2 * ((N : ℝ) - 1)) * A := by
    have h1 : ∀ i, ∀ j ∈ Finset.univ.erase i,
        -(sb1kap s * (Real.log (1 + ‖X i‖) + Real.log (1 + ‖X j‖))) ≤ k (X i - X j) := by
      intro i j _
      have h2 := hk.lower (X i - X j)
      have h3 := sb1_log_sub (X i) (X j)
      have h4 : sb1kap s * Real.log (1 + ‖X i - X j‖) ≤
          sb1kap s * (Real.log (1 + ‖X i‖) + Real.log (1 + ‖X j‖)) := mul_le_mul_of_nonneg_left h3 hκ
      linarith
    have h5 : ∑ i, ∑ j ∈ Finset.univ.erase i,
        -(sb1kap s * (Real.log (1 + ‖X i‖) + Real.log (1 + ‖X j‖))) ≤ S :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => h1 i j hj
    have h6 : ∑ i, ∑ j ∈ Finset.univ.erase i,
        -(sb1kap s * (Real.log (1 + ‖X i‖) + Real.log (1 + ‖X j‖))) =
        -(sb1kap s * (2 * ((N : ℝ) - 1) * A)) := by
      have := sb1_double_sum (N := N) (fun i => Real.log (1 + ‖X i‖))
      simp only [Finset.sum_neg_distrib, ← Finset.mul_sum]
      rw [this, hA]
    nlinarith [h5, h6]
  have hG : ∑ i, sb1G k ρ (X i) ≤ -(sb1kap s * A) + N * sb1CG d s Cρ M1 := by
    have h1 : ∀ i, sb1G k ρ (X i) ≤ -(sb1kap s * Real.log (1 + ‖X i‖)) + sb1CG d s Cρ M1 :=
      fun i => sb1_G_upper hd hs0 hsd hk R (X i)
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h1 i)
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum] at this
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    linarith
  have hc := sb1_c_lower hd hs0 hsd hk R
  unfold sb1En
  rw [← hS]
  have key : -β * N * (1 / (2 * (N : ℝ) ^ 2) * S - 1 / (N : ℝ) * ∑ i, sb1G k ρ (X i) + 1 / 2 * sb1c k ρ) =
      -(β / (2 * N)) * S + β * ∑ i, sb1G k ρ (X i) - (β * N / 2) * sb1c k ρ := by
    field_simp
    ring
  rw [key]
  have hu : 0 ≤ β / (2 * N) := by positivity
  have e1 := mul_le_mul_of_nonneg_left hS' hu
  have e2 := mul_le_mul_of_nonneg_left hG hβ
  have e3 := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ β * N / 2)
  have e4 : β / (2 * N) * (sb1kap s * (2 * ((N : ℝ) - 1)) * A) = β * sb1kap s * A * (1 - 1 / N) := by
    field_simp
  have e5 : 0 ≤ β * sb1kap s * A / N := by positivity
  have e6 : β * sb1kap s * A * (1 - 1 / N) = β * sb1kap s * A - β * sb1kap s * A / N := by ring
  nlinarith [e1, e2, e3, e4, e5, e6]

end Weight

/-! ### The trajectory bundle -/

/-- `(1+|y|)^{-p}` -/
def sb1w (p : ℝ) (y : Euc d) : ℝ := (1 + ‖y‖) ^ (-p)

theorem sb1w_pos (p : ℝ) (y : Euc d) : 0 < sb1w p y := Real.rpow_pos_of_pos (by positivity) _

theorem sb1w_le_one {p : ℝ} (hp : 0 ≤ p) (y : Euc d) : sb1w p y ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by linarith)

theorem sb1w_succ (p : ℝ) (y : Euc d) : sb1w (p + 1) y * (1 + ‖y‖) = sb1w p y := by
  unfold sb1w
  have h : 0 < 1 + ‖y‖ := by positivity
  rw [show -(p + 1) = -p - 1 by ring, Real.rpow_sub h, Real.rpow_one]
  field_simp

theorem sb1w_meas (p : ℝ) : Measurable (sb1w p : Euc d → ℝ) :=
  (measurable_const.add measurable_norm).pow_const _

theorem sb1w_int (hd : 1 ≤ d) {p : ℝ} (hp : (d : ℝ) < p) : Integrable (sb1w p : Euc d → ℝ) := by
  unfold sb1w
  apply integrable_one_add_norm
  simpa using hp

theorem sb1w_mom (hd : 1 ≤ d) : Integrable (fun y : Euc d => sb1w ((d : ℝ) + 2) y * ‖y‖) := by
  refine (sb1w_int hd (p := (d : ℝ) + 1) (by linarith)).mono'
    ((sb1w_meas _).mul measurable_norm).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sb1w_pos _ _).le (norm_nonneg y))]
  have := sb1w_succ ((d : ℝ) + 1) y
  have h2 := sb1w_pos ((d : ℝ) + 2) y
  have e : (d : ℝ) + 1 + 1 = (d : ℝ) + 2 := by ring
  rw [e] at this
  nlinarith [norm_nonneg y]

/-- the trajectory data of the normaliser identity: `Sb1Traj`, the decay `(1+|y|)^{-(d+3)}` of `D^l ρ_r`, `ρ > 0`. -/
structure Sb1Tr3 (D : Whole.WholeDyn d) (T C B C3 : ℝ) (ρ : ℝ → Euc d → ℝ) : Prop where
  tr : Sb1Traj D T C B ρ
  dec : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ l, l ≤ 3 → ∀ y,
    ‖iteratedFDeriv ℝ l (ρ r) y‖ ≤ C3 * sb1w ((d : ℝ) + 3) y
  pos : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ y, 0 < ρ r y
  C3nn : 0 ≤ C3

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ}

theorem Sb1Tr3.rho_le (H : Sb1Tr3 D T C B C3 ρ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (y : Euc d) :
    ρ r y ≤ C3 * sb1w ((d : ℝ) + 3) y := by
  have := H.dec r hr 0 (by norm_num) y
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  exact (le_abs_self _).trans this

theorem Sb1Tr3.drho_le (H : Sb1Tr3 D T C B C3 ρ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (y : Euc d) :
    ‖fderiv ℝ (ρ r) y‖ ≤ C3 * sb1w ((d : ℝ) + 3) y := by
  have := H.dec r hr 1 (by norm_num) y
  rwa [norm_iteratedFDeriv_one] at this

theorem Sb1Tr3.ddrho_le (H : Sb1Tr3 D T C B C3 ρ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (y : Euc d) :
    ‖fderiv ℝ (fderiv ℝ (ρ r)) y‖ ≤ C3 * sb1w ((d : ℝ) + 3) y := by
  have := H.dec r hr 2 (by norm_num) y
  rwa [← sb1_norm_fderiv_fderiv] at this

/-- `ρ_r` is an `Sb1Rho` with `C_ρ = C3` and `M₁ = C3 ∫ (1+|y|)^{-(d+2)}`. -/
theorem Sb1Tr3.rho (hd : 1 ≤ d) (H : Sb1Tr3 D T C B C3 ρ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) :
    Sb1Rho (ρ r) C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y) where
  dens := (H.tr.slice r hr).dens
  le := fun y => (H.rho_le hr y).trans (mul_le_of_le_one_right H.C3nn (sb1w_le_one (by positivity) y))
  mom := by
    have hd2 := sb1w_int hd (p := (d : ℝ) + 2) (by linarith)
    refine (hd2.const_mul C3).mono' (((H.tr.slice r hr).dens.measurable).mul measurable_norm).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    have h0 := (H.tr.slice r hr).dens.nonneg y
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (norm_nonneg y))]
    have h1 := H.rho_le hr y
    have h2 := sb1w_succ ((d : ℝ) + 2) y
    have h3 := sb1w_pos ((d : ℝ) + 3) y
    have e : (d : ℝ) + 2 + 1 = (d : ℝ) + 3 := by ring
    rw [e] at h2
    nlinarith [norm_nonneg y, mul_le_mul_of_nonneg_right h1 (norm_nonneg y), H.C3nn]
  momle := by
    have hI := sb1w_int hd (p := (d : ℝ) + 2) (by linarith)
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun y =>
      mul_nonneg ((H.tr.slice r hr).dens.nonneg y) (norm_nonneg y)) (hI.const_mul C3) (Eventually.of_forall fun y => ?_)
    have h0 := (H.tr.slice r hr).dens.nonneg y
    have h1 := H.rho_le hr y
    have h2 := sb1w_succ ((d : ℝ) + 2) y
    have h3 := sb1w_pos ((d : ℝ) + 3) y
    have e : (d : ℝ) + 2 + 1 = (d : ℝ) + 3 := by ring
    rw [e] at h2
    nlinarith [norm_nonneg y, mul_le_mul_of_nonneg_right h1 (norm_nonneg y), H.C3nn]

end HRS.MS.MfeConf
