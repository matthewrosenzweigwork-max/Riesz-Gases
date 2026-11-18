import HRS.PDE.Toolbox.Kernel
import HRS.PDE.Toolbox.Product
import HRS.PDE.Toolbox.LocalInt

/-!
# Appendix C helper lemmas: the Levy kernel of a homogeneous symbol on the torus (Lemma C.3 (ii))

Auxiliary results for `HRS/PDE/Toolbox.lean`.

Dyadic (Littlewood–Paley) construction of the kernel: `𝔨 = -∑_{j≥0} K_j`,
`K_j = 2^{jθ} kern Φ 2^{-j}`, `Φ = m₀ ψ`, `ψ(ξ) = χ(ξ) - χ(2ξ)`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate ContDiff

namespace HRS.PDE.LevyAux

open HRS.PDE.Kern

variable {d : ℕ}

/-! ### (a) The Littlewood–Paley cutoff and the profile `Φ` -/

/-- the bump (`≡ 1` on the unit ball, supported in the ball of radius 2) -/
def bumpD (d : ℕ) : ContDiffBump (0 : Euc d) := ⟨1, 2, one_pos, one_lt_two⟩

/-- the radial cutoff `χ` -/
def chiF (d : ℕ) (ξ : Euc d) : ℝ := bumpD d ξ

theorem contDiff_chiF : ContDiff ℝ ∞ (chiF d) := (bumpD d).contDiff

theorem chiF_one {ξ : Euc d} (h : ‖ξ‖ ≤ 1) : chiF d ξ = 1 :=
  ContDiffBump.one_of_mem_closedBall (bumpD d) (by simpa [bumpD] using h)

theorem chiF_zero {ξ : Euc d} (h : 2 ≤ ‖ξ‖) : chiF d ξ = 0 :=
  ContDiffBump.zero_of_le_dist (bumpD d) (by simpa [bumpD] using h)

theorem chiF_neg (ξ : Euc d) : chiF d (-ξ) = chiF d ξ := ContDiffBump.neg (bumpD d) ξ

/-- `ψ(ξ) = χ(ξ) - χ(2ξ)` -/
def psiF (d : ℕ) (ξ : Euc d) : ℝ := chiF d ξ - chiF d ((2 : ℝ) • ξ)

theorem contDiff_psiF : ContDiff ℝ ∞ (psiF d) :=
  contDiff_chiF.sub (contDiff_chiF.comp (contDiff_id.const_smul (2 : ℝ)))

theorem psiF_neg (ξ : Euc d) : psiF d (-ξ) = psiF d ξ := by
  unfold psiF
  rw [smul_neg, chiF_neg, chiF_neg]

theorem psiF_small {ξ : Euc d} (h : ‖ξ‖ ≤ 1 / 2) : psiF d ξ = 0 := by
  unfold psiF
  rw [chiF_one (by linarith), chiF_one, sub_self]
  rw [norm_smul]; simp; linarith

theorem psiF_large {ξ : Euc d} (h : 2 ≤ ‖ξ‖) : psiF d ξ = 0 := by
  unfold psiF
  rw [chiF_zero h, chiF_zero, sub_self]
  rw [norm_smul]; simp; linarith

/-- the dyadic scale `2^{-j}` -/
def eps (j : ℕ) : ℝ := ((2 : ℝ) ^ j)⁻¹

theorem eps_pos (j : ℕ) : 0 < eps j := by unfold eps; positivity

theorem eps_le_one (j : ℕ) : eps j ≤ 1 := by
  unfold eps
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

theorem eps_succ (j : ℕ) : 2 * eps (j + 1) = eps j := by
  unfold eps; rw [pow_succ]; field_simp

theorem psiF_sum (ξ : Euc d) (J : ℕ) :
    ∑ j ∈ Finset.range (J + 1), psiF d (eps j • ξ) = chiF d (eps J • ξ) - chiF d ((2 : ℝ) • ξ) := by
  induction J with
  | zero => simp [psiF, eps]
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    have : (2 : ℝ) • eps (J + 1) • ξ = eps J • ξ := by rw [smul_smul, eps_succ]
    unfold psiF
    rw [this]; ring

theorem hasSum_psiF {ξ : Euc d} (hξ : 1 ≤ ‖ξ‖) : HasSum (fun j => psiF d (eps j • ξ)) 1 := by
  obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (2 * ‖ξ‖) (by norm_num : (1 : ℝ) < 2)
  have hnorm : ∀ j, J ≤ j → ‖eps j • ξ‖ < 1 / 2 := by
    intro j hj
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (eps_pos j)]
    unfold eps
    have h1 : (2 : ℝ) ^ J ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
    have h2 : 0 < (2 : ℝ) ^ j := by positivity
    rw [inv_mul_lt_iff₀ h2]
    linarith
  have hz : ∀ j ∉ Finset.range (J + 1), psiF d (eps j • ξ) = 0 := by
    intro j hj
    simp only [Finset.mem_range, not_lt] at hj
    exact psiF_small (hnorm j (by omega)).le
  have h : HasSum (fun j => psiF d (eps j • ξ)) (∑ j ∈ Finset.range (J + 1), psiF d (eps j • ξ)) :=
    hasSum_sum_of_ne_finset_zero hz
  rw [psiF_sum, chiF_one (by linarith [hnorm J le_rfl]), chiF_zero (by rw [norm_smul]; simp; linarith)] at h
  simpa using h

/-- `Φ_ℝ = m₀ ψ` -/
def PhiR (m₀ : Euc d → ℝ) (ξ : Euc d) : ℝ := m₀ ξ * psiF d ξ

/-- the complex-valued profile `Φ` fed to `kern` -/
def Phi (m₀ : Euc d → ℝ) (ξ : Euc d) : ℂ := ((PhiR m₀ ξ : ℝ) : ℂ)

theorem contDiff_PhiR {m₀ : Euc d → ℝ} (hsm : ContDiffOn ℝ ∞ m₀ {ξ | ξ ≠ 0}) :
    ContDiff ℝ ∞ (PhiR m₀) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  by_cases hξ : ξ = 0
  · subst hξ
    have hev : PhiR m₀ =ᶠ[𝓝 (0 : Euc d)] fun _ => 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : Euc d) (by norm_num : (0 : ℝ) < 1 / 2)] with ξ hξ
      have : ‖ξ‖ ≤ 1 / 2 := by rw [mem_ball_zero_iff] at hξ; exact hξ.le
      simp [PhiR, psiF_small this]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · exact (hsm.contDiffAt (isOpen_ne.mem_nhds hξ)).mul contDiff_psiF.contDiffAt

theorem contDiff_Phi {m₀ : Euc d → ℝ} (hsm : ContDiffOn ℝ ∞ m₀ {ξ | ξ ≠ 0}) :
    ContDiff ℝ ∞ (Phi m₀) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_PhiR hsm)

theorem PhiR_large (m₀ : Euc d → ℝ) {ξ : Euc d} (h : 2 ≤ ‖ξ‖) : PhiR m₀ ξ = 0 := by
  simp [PhiR, psiF_large h]

theorem Phi_large (m₀ : Euc d → ℝ) {ξ : Euc d} (h : 2 ≤ ‖ξ‖) : Phi m₀ ξ = 0 := by
  simp [Phi, PhiR_large m₀ h]

theorem PhiR_zero (m₀ : Euc d → ℝ) : PhiR m₀ 0 = 0 := by
  simp [PhiR, psiF_small (ξ := (0 : Euc d)) (by simp)]

theorem Phi_neg {m₀ : Euc d → ℝ} (he : ∀ ξ, m₀ (-ξ) = m₀ ξ) (ξ : Euc d) : Phi m₀ (-ξ) = Phi m₀ ξ := by
  simp [Phi, PhiR, he, psiF_neg]

/-- the symbol pieces `κ_j(ξ) = 2^{jθ} Φ(2^{-j} ξ)` -/
def kap (θ : ℝ) (m₀ : Euc d → ℝ) (j : ℕ) (ξ : Euc d) : ℝ := ((2 : ℝ) ^ j) ^ θ * PhiR m₀ (eps j • ξ)

theorem kap_eq {θ : ℝ} {m₀ : Euc d → ℝ} (hhom : ∀ c : ℝ, 0 < c → ∀ ξ, m₀ (c • ξ) = c ^ θ * m₀ ξ)
    (j : ℕ) (ξ : Euc d) : kap θ m₀ j ξ = m₀ ξ * psiF d (eps j • ξ) := by
  unfold kap PhiR
  rw [hhom _ (eps_pos j)]
  have : ((2 : ℝ) ^ j) ^ θ * eps j ^ θ = 1 := by
    unfold eps
    rw [Real.inv_rpow (by positivity), mul_inv_cancel₀]
    positivity
  calc ((2 : ℝ) ^ j) ^ θ * (eps j ^ θ * m₀ ξ * psiF d (eps j • ξ))
      = (((2 : ℝ) ^ j) ^ θ * eps j ^ θ) * m₀ ξ * psiF d (eps j • ξ) := by ring
    _ = _ := by rw [this, one_mul]

theorem one_le_norm_toEuc {k : Lattice d} (hk : k ≠ 0) : 1 ≤ ‖Lattice.toEuc k‖ := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h; push Not at h; exact hk (funext h)
  have h1 : (1 : ℝ) ≤ |(k i : ℝ)| := by
    have : (1 : ℤ) ≤ |k i| := Int.one_le_abs hi
    exact_mod_cast this
  have h2 : ‖(Lattice.toEuc k) i‖ ≤ ‖Lattice.toEuc k‖ := PiLp.norm_apply_le _ i
  simpa [Lattice.toEuc] using h1.trans (by simpa [Lattice.toEuc] using h2)

theorem hasSum_kap {θ : ℝ} {m₀ : Euc d → ℝ} (𝔪 : Lattice d → ℝ)
    (hhom : ∀ c : ℝ, 0 < c → ∀ ξ, m₀ (c • ξ) = c ^ θ * m₀ ξ)
    (hext : ∀ k : Lattice d, k ≠ 0 → 𝔪 k = m₀ (Lattice.toEuc k)) (h0 : 𝔪 0 = 0) (k : Lattice d) :
    HasSum (fun j => kap θ m₀ j (Lattice.toEuc k)) (𝔪 k) := by
  by_cases hk : k = 0
  · subst hk
    rw [h0]
    have : ∀ j, kap θ m₀ j (Lattice.toEuc (0 : Lattice d)) = 0 := by
      intro j
      have : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
      simp [kap, this, PhiR_zero]
    simp_rw [this]
    exact hasSum_zero
  · rw [hext k hk]
    simp_rw [kap_eq hhom]
    simpa using (hasSum_psiF (one_le_norm_toEuc hk)).mul_left (m₀ (Lattice.toEuc k))

/-! ### (b) Pointwise estimates for `kern φ ε` -/

section Pointwise

theorem box_card_le (n : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (2 * (⌈2 / ε⌉₊ + n) + 1 : ℝ) ≤ (7 + 2 * n) / ε := by
  have hc1 : (⌈2 / ε⌉₊ : ℝ) < 2 / ε + 1 := Nat.ceil_lt_add_one (by positivity)
  have hu : (1 : ℝ) ≤ ε⁻¹ := one_le_inv_iff₀.2 ⟨hε, hε1⟩
  simp only [div_eq_mul_inv] at hc1 ⊢
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_nonneg hn (sub_nonneg.2 hu)]

/-- (P0) `‖kern φ ε‖_∞ ≤ C ε^{-d}` -/
theorem kern_sup_bound {φ : Euc d → ℂ} (hφ : ContDiff ℝ ∞ φ) (hsupp : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ z : Torus d, ‖kern φ ε z‖ ≤ C / ε ^ d := by
  obtain ⟨B, hB⟩ := exists_bound_iteratedFDeriv hφ hsupp
  have hB0 : ∀ x, ‖φ x‖ ≤ B 0 := fun x => by simpa using hB 0 x
  have hB0' : 0 ≤ B 0 := (norm_nonneg _).trans (hB0 0)
  refine ⟨7 ^ d * B 0, by positivity, fun ε hε hε1 z => ?_⟩
  have hc := isTrigPoly_kcoef hsupp hε
  unfold kern
  rw [trig_eq_sum hc]
  calc ‖∑ k ∈ boxF d ⌈2 / ε⌉₊, kcoef φ ε k * Torus.mode k z‖
      ≤ ∑ k ∈ boxF d ⌈2 / ε⌉₊, ‖kcoef φ ε k * Torus.mode k z‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ boxF d ⌈2 / ε⌉₊, B 0 := Finset.sum_le_sum fun k _ => by
        rw [norm_mul, Torus.norm_mode, mul_one]; exact hB0 _
    _ = (2 * ⌈2 / ε⌉₊ + 1 : ℝ) ^ d * B 0 := by
        rw [Finset.sum_const, card_boxF, nsmul_eq_mul]; push_cast; ring
    _ ≤ (7 / ε) ^ d * B 0 := by
        gcongr
        have := box_card_le 0 hε hε1
        simpa using this
    _ = 7 ^ d * B 0 / ε ^ d := by rw [div_pow]; ring

theorem exists_coord_sq (hd : 0 < d) (z : Torus d) :
    ∃ i : Fin d, Torus.tdist z 0 ^ 2 ≤ d * Torus.centeredRep z i ^ 2 := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin d))
    (fun i => Torus.centeredRep z i ^ 2) Finset.univ_nonempty
  refine ⟨i, ?_⟩
  unfold Torus.tdist
  rw [sub_zero, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  calc ∑ j, ‖Torus.centeredRep z j‖ ^ 2 ≤ ∑ _j : Fin d, Torus.centeredRep z i ^ 2 :=
        Finset.sum_le_sum fun j hj => by rw [Real.norm_eq_abs, sq_abs]; exact hi j hj
    _ = d * Torus.centeredRep z i ^ 2 := by simp

/-- (PN) decay: `t^{2N} ‖kern φ ε z‖ ≤ C ε^{2N-d}` -/
theorem kern_decay_bound (hd : 0 < d) {φ : Euc d → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hsupp : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ z : Torus d,
      Torus.tdist z 0 ^ (2 * N) * ‖kern φ ε z‖ ≤ C * (ε ^ (2 * N) / ε ^ d) := by
  obtain ⟨B, hB⟩ := exists_bound_iteratedFDeriv hφ hsupp
  have hBn : 0 ≤ B (2 * N) := (norm_nonneg _).trans (hB (2 * N) 0)
  refine ⟨((d : ℝ) / 16) ^ N * ((7 + 2 * (2 * N : ℕ) : ℝ) ^ d * B (2 * N)), by positivity,
    fun ε hε hε1 z => ?_⟩
  obtain ⟨i, hi⟩ := exists_coord_sq hd z
  set L : List (Fin d) := List.replicate (2 * N) i with hL
  have hLlen : L.length = 2 * N := by simp [hL]
  have hc := isTrigPoly_kcoef hsupp hε
  have h1 : (L.map fun i => Torus.mode (eI i) z - 1).prod * trig (kcoef φ ε) z = trig (Dls L (kcoef φ ε)) z :=
    trig_Dls L hc z
  have h2 : (L.map fun i => Torus.mode (eI i) z - 1).prod = (Torus.mode (eI i) z - 1) ^ (2 * N) := by
    simp [hL, List.map_replicate, List.prod_replicate]
  rw [h2] at h1
  have h3 : qf i z ^ N * ‖kern φ ε z‖ = ‖trig (Dls L (kcoef φ ε)) z‖ := by
    rw [← h1, norm_mul, norm_pow, qf, ← pow_mul, mul_comm 2 N]
    rfl
  have h4 : ‖trig (Dls L (kcoef φ ε)) z‖ ≤ (2 * (⌈2 / ε⌉₊ + 2 * N) + 1 : ℝ) ^ d * (ε ^ (2 * N) * B (2 * N)) := by
    have hc' := isTrigPoly_Dls L hc
    rw [trig_eq_sum hc']
    calc ‖∑ k ∈ boxF d (⌈2 / ε⌉₊ + L.length), Dls L (kcoef φ ε) k * Torus.mode k z‖
        ≤ ∑ k ∈ boxF d (⌈2 / ε⌉₊ + L.length), ‖Dls L (kcoef φ ε) k * Torus.mode k z‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ boxF d (⌈2 / ε⌉₊ + L.length), (ε ^ (2 * N) * B (2 * N)) :=
          Finset.sum_le_sum fun k _ => by
            rw [norm_mul, Torus.norm_mode, mul_one]
            have := norm_Dls_kcoef_le hφ hB L hε k
            rwa [hLlen] at this
      _ = _ := by
          rw [Finset.sum_const, card_boxF, hLlen, nsmul_eq_mul]; push_cast; ring
  have h5 : (16 / d : ℝ) * Torus.tdist z 0 ^ 2 ≤ qf i z := by
    have := sixteen_le_qf z i
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    rw [div_mul_eq_mul_div, div_le_iff₀ hd']
    nlinarith
  have h6 : ((16 / d : ℝ) * Torus.tdist z 0 ^ 2) ^ N ≤ qf i z ^ N :=
    pow_le_pow_left₀ (by positivity) h5 N
  have hK : 0 ≤ ‖kern φ ε z‖ := norm_nonneg _
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  calc Torus.tdist z 0 ^ (2 * N) * ‖kern φ ε z‖
      = ((d : ℝ) / 16) ^ N * (((16 / d : ℝ) * Torus.tdist z 0 ^ 2) ^ N * ‖kern φ ε z‖) := by
        rw [mul_pow, pow_mul, ← mul_assoc, ← mul_assoc, ← mul_pow]
        have : (d : ℝ) / 16 * (16 / d) = 1 := by field_simp
        rw [this, one_pow, one_mul]
    _ ≤ ((d : ℝ) / 16) ^ N * (qf i z ^ N * ‖kern φ ε z‖) := by gcongr
    _ ≤ ((d : ℝ) / 16) ^ N * ((2 * (⌈2 / ε⌉₊ + 2 * N) + 1 : ℝ) ^ d * (ε ^ (2 * N) * B (2 * N))) := by
        rw [h3]; gcongr
    _ ≤ ((d : ℝ) / 16) ^ N * (((7 + 2 * (2 * N : ℕ)) / ε : ℝ) ^ d * (ε ^ (2 * N) * B (2 * N))) := by
        gcongr
        have := box_card_le (2 * N) hε hε1
        push_cast at this ⊢
        exact this
    _ = _ := by rw [div_pow (7 + 2 * ((2 * N : ℕ) : ℝ)) ε d]; ring

end Pointwise

/-! ### (M2) the second moment -/

section Moment2

theorem tdist_pow_four_le (z : Torus d) :
    Torus.tdist z 0 ^ 2 * Torus.tdist z 0 ^ 2 ≤ (∑ i, ∑ j, qf i z * qf j z) / 256 := by
  have h := tdist_sq_le z
  have h0 : 0 ≤ Torus.tdist z 0 ^ 2 := by positivity
  have h1 : Torus.tdist z 0 ^ 2 * Torus.tdist z 0 ^ 2 ≤ ((∑ i, qf i z) / 16) * ((∑ i, qf i z) / 16) :=
    mul_le_mul h h h0 (le_trans h0 h)
  have h2 : ((∑ i, qf i z) / 16) * ((∑ i, qf i z) / 16) = (∑ i, ∑ j, qf i z * qf j z) / 256 := by
    rw [← Finset.sum_mul_sum]; ring
  linarith

/-- (M2) `∫ t² |K_ε| ≤ C ε²` -/
theorem kern_L1_moment2_bound {φ : Euc d → ℂ} (hφ : ContDiff ℝ ∞ φ) (hsupp : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      Integrable (fun z : Torus d => Torus.tdist z 0 ^ 2 * ‖kern φ ε z‖) ∧
        ∫ z, Torus.tdist z 0 ^ 2 * ‖kern φ ε z‖ ≤ C * ε ^ 2 := by
  obtain ⟨C2, hC2, h2⟩ := kern_W_moment hφ hsupp 2
  refine ⟨(d : ℝ) ^ 2 * C2 / 512 + (Real.pi / 4) ^ d / 2, by positivity, fun ε hε hε1 => ?_⟩
  have hK := continuous_kern hsupp hε
  have hlam : 0 < ε ^ d / ε ^ 2 := by positivity
  have hq : ∀ (i j : Fin d), Continuous fun z : Torus d => qf i z * qf j z :=
    fun i j => (continuous_qf i).mul (continuous_qf j)
  have hI2 : Integrable fun z : Torus d => (∑ i, ∑ j, qf i z * qf j z) / 256 * (Wf ε z * ‖kern φ ε z‖ ^ 2) := by
    refine integrable_of_continuous_torus ?_
    have : Continuous fun z : Torus d => ∑ i, ∑ j, qf i z * qf j z :=
      continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => hq i j
    exact (this.div_const 256).mul ((continuous_Wf ε).mul (hK.norm.pow 2))
  have hI3 : Integrable fun z : Torus d => (Wf ε z)⁻¹ :=
    integrable_of_continuous_torus ((continuous_Wf ε).inv₀ fun z => (Wf_pos z).ne')
  have hpt : ∀ z : Torus d, Torus.tdist z 0 ^ 2 * ‖kern φ ε z‖ ≤
      ε ^ d / ε ^ 2 / 2 * ((∑ i, ∑ j, qf i z * qf j z) / 256 * (Wf ε z * ‖kern φ ε z‖ ^ 2)) +
        (1 / (2 * (ε ^ d / ε ^ 2))) * (Wf ε z)⁻¹ := by
    intro z
    have h1 := amgm_pt (Torus.tdist z 0 ^ 2 * ‖kern φ ε z‖) (Wf ε z) (ε ^ d / ε ^ 2)
      (mul_nonneg (by positivity) (norm_nonneg _)) (Wf_pos z) hlam
    have key : Wf ε z * (Torus.tdist z 0 ^ 2 * ‖kern φ ε z‖) ^ 2 ≤
        (∑ i, ∑ j, qf i z * qf j z) / 256 * (Wf ε z * ‖kern φ ε z‖ ^ 2) := by
      have := tdist_pow_four_le z
      have hW := (Wf_pos (ε := ε) z).le
      calc Wf ε z * (Torus.tdist z 0 ^ 2 * ‖kern φ ε z‖) ^ 2
          = (Torus.tdist z 0 ^ 2 * Torus.tdist z 0 ^ 2) * (Wf ε z * ‖kern φ ε z‖ ^ 2) := by ring
        _ ≤ _ := by gcongr
    refine h1.trans ?_
    have := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ ε ^ d / ε ^ 2 / 2)
    linarith
  have hbd : Integrable (fun z : Torus d => ε ^ d / ε ^ 2 / 2 *
      ((∑ i, ∑ j, qf i z * qf j z) / 256 * (Wf ε z * ‖kern φ ε z‖ ^ 2)) +
        (1 / (2 * (ε ^ d / ε ^ 2))) * (Wf ε z)⁻¹) := (hI2.const_mul _).add (hI3.const_mul _)
  have hmeas : AEStronglyMeasurable (fun z : Torus d => Torus.tdist z 0 ^ 2 * ‖kern φ ε z‖) volume :=
    ((measurable_tdist_zero.pow_const 2).mul hK.norm.measurable).aestronglyMeasurable
  have hint : Integrable (fun z : Torus d => Torus.tdist z 0 ^ 2 * ‖kern φ ε z‖) := by
    refine Integrable.mono' hbd hmeas ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (norm_nonneg _))]
    exact hpt z
  refine ⟨hint, ?_⟩
  have hsum : ∫ z : Torus d, (∑ i, ∑ j, qf i z * qf j z) / 256 * (Wf ε z * ‖kern φ ε z‖ ^ 2) ≤
      (d : ℝ) ^ 2 / 256 * (C2 * (ε ^ 4 / ε ^ d)) := by
    have : ∀ z : Torus d, (∑ i, ∑ j, qf i z * qf j z) / 256 * (Wf ε z * ‖kern φ ε z‖ ^ 2) =
        1 / 256 * ∑ i, ∑ j, ([i, j].map fun l => qf l z).prod * (Wf ε z * ‖kern φ ε z‖ ^ 2) := by
      intro z
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      have e : ∑ i, ∑ j, qf i z * qf j z * (Wf ε z * ‖kern φ ε z‖ ^ 2) =
          (∑ i, ∑ j, qf i z * qf j z) * (Wf ε z * ‖kern φ ε z‖ ^ 2) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
      rw [e]; ring
    have hj : ∀ i j : Fin d, Integrable fun z : Torus d =>
        ([i, j].map fun l => qf l z).prod * (Wf ε z * ‖kern φ ε z‖ ^ 2) := by
      intro i j
      refine integrable_of_continuous_torus ?_
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      exact (hq i j).mul ((continuous_Wf ε).mul (hK.norm.pow 2))
    simp_rw [this]
    rw [integral_const_mul, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hj i j]
    simp_rw [integral_finsetSum _ fun j _ => hj _ j]
    calc 1 / 256 * ∑ i, ∑ j, ∫ z : Torus d, ([i, j].map fun l => qf l z).prod * (Wf ε z * ‖kern φ ε z‖ ^ 2)
        ≤ 1 / 256 * ∑ _i : Fin d, ∑ _j : Fin d, C2 * (ε ^ (2 * 2) / ε ^ d) := by
          gcongr with i _ j _
          exact h2 [i, j] rfl ε hε hε1
      _ = (d : ℝ) ^ 2 / 256 * (C2 * (ε ^ 4 / ε ^ d)) := by simp; ring
  calc ∫ z, Torus.tdist z 0 ^ 2 * ‖kern φ ε z‖
      ≤ ∫ z, (ε ^ d / ε ^ 2 / 2 * ((∑ i, ∑ j, qf i z * qf j z) / 256 * (Wf ε z * ‖kern φ ε z‖ ^ 2)) +
        (1 / (2 * (ε ^ d / ε ^ 2))) * (Wf ε z)⁻¹) :=
        integral_mono hint hbd hpt
    _ = ε ^ d / ε ^ 2 / 2 * (∫ z, (∑ i, ∑ j, qf i z * qf j z) / 256 * (Wf ε z * ‖kern φ ε z‖ ^ 2)) +
          (1 / (2 * (ε ^ d / ε ^ 2))) * ∫ z : Torus d, (Wf ε z)⁻¹ := by
        rw [integral_add (hI2.const_mul _) (hI3.const_mul _), integral_const_mul, integral_const_mul]
    _ ≤ ε ^ d / ε ^ 2 / 2 * ((d : ℝ) ^ 2 / 256 * (C2 * (ε ^ 4 / ε ^ d))) +
          (1 / (2 * (ε ^ d / ε ^ 2))) * (Real.pi * ε / 4) ^ d := by
        gcongr
        exact integral_Wf_inv_le hε
    _ = ((d : ℝ) ^ 2 * C2 / 512 + (Real.pi / 4) ^ d / 2) * ε ^ 2 := by
        rw [show Real.pi * ε / 4 = Real.pi / 4 * ε by ring, mul_pow]
        field_simp
        ring

end Moment2

/-! ### (c) Dyadic sums -/

section Dyadic


theorem rpow_two_pow (j : ℕ) (a : ℝ) : ((2 : ℝ) ^ j) ^ a = ((2 : ℝ) ^ a) ^ j :=
  (Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) a j).symm

theorem dyadic_sum_le {a : ℝ} (ha : 0 < a) {M : ℕ} (hM : a < 2 * M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ), 0 < t → ∀ f : ℕ → ℝ, (∀ j, 0 ≤ f j) →
      (∀ j, f j ≤ ((2 : ℝ) ^ j) ^ a) → (∀ j, f j ≤ t ^ (-(2 * M : ℝ)) * ((2 : ℝ) ^ j) ^ (a - 2 * M)) →
      Summable f ∧ ∑' j, f j ≤ C * (t ^ (-a) + 1) := by
  set q : ℝ := (2 : ℝ) ^ a with hq
  set q' : ℝ := (2 : ℝ) ^ (a - 2 * M) with hq'
  have hq1 : 1 < q := Real.one_lt_rpow (by norm_num) ha
  have hq'0 : 0 < q' := by positivity
  have hq'1 : q' < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hqm : 0 < q - 1 := by linarith
  have hq'm : 0 < 1 - q' := by linarith
  have hC : 0 ≤ q / (q - 1) := by positivity
  have hB0 : 0 ≤ 1 / (1 - q') := by positivity
  refine ⟨q / (q - 1) + 1 / (1 - q'), by positivity, fun t ht f hf0 hfA hfB => ?_⟩
  have hgeo : Summable fun j : ℕ => t ^ (-(2 * M : ℝ)) * q' ^ j :=
    (summable_geometric_of_lt_one hq'0.le hq'1).mul_left _
  have hfs : Summable f := by
    refine Summable.of_nonneg_of_le hf0 (fun j => ?_) hgeo
    rw [← rpow_two_pow]; exact hfB j
  refine ⟨hfs, ?_⟩
  have h1 : 0 ≤ t ^ (-a) := by positivity
  by_cases ht1 : 1 ≤ t
  · -- large t
    have hc : t ^ (-(2 * M : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos ht1 (by linarith [(Nat.cast_nonneg M : (0:ℝ) ≤ M)])
    have hle : ∑' j, f j ≤ ∑' j : ℕ, q' ^ j := by
      refine hfs.tsum_le_tsum (fun j => ?_) (summable_geometric_of_lt_one hq'0.le hq'1)
      calc f j ≤ t ^ (-(2 * M : ℝ)) * ((2 : ℝ) ^ j) ^ (a - 2 * M) := hfB j
        _ ≤ 1 * ((2 : ℝ) ^ j) ^ (a - 2 * M) := by gcongr
        _ = q' ^ j := by rw [one_mul, rpow_two_pow]
    rw [tsum_geometric_of_lt_one hq'0.le hq'1] at hle
    have hle' : ∑' j, f j ≤ 1 / (1 - q') := by simpa [one_div] using hle
    nlinarith [mul_nonneg hC h1, mul_nonneg hB0 h1]
  · push Not at ht1
    have hx : 1 ≤ 1 / t := by rw [le_div_iff₀ ht]; linarith
    obtain ⟨J, hJ1, hJ2⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
    have hsplit := hfs.sum_add_tsum_nat_add (J + 1)
    -- first part
    have hA : ∑ j ∈ Finset.range (J + 1), f j ≤ q / (q - 1) * t ^ (-a) := by
      calc ∑ j ∈ Finset.range (J + 1), f j ≤ ∑ j ∈ Finset.range (J + 1), q ^ j :=
            Finset.sum_le_sum fun j _ => by rw [← rpow_two_pow]; exact hfA j
        _ = (q ^ (J + 1) - 1) / (q - 1) := geom_sum_eq hq1.ne' _
        _ ≤ q ^ (J + 1) / (q - 1) := by
            gcongr; linarith
        _ ≤ q / (q - 1) * t ^ (-a) := by
            have h2 : (2 : ℝ) ^ (J + 1) ≤ 2 / t := by
              rw [pow_succ]
              have := mul_le_mul_of_nonneg_right hJ1 (by norm_num : (0 : ℝ) ≤ 2)
              calc (2 : ℝ) ^ J * 2 ≤ 1 / t * 2 := this
                _ = 2 / t := by ring
            have h3 : q ^ (J + 1) ≤ q * t ^ (-a) := by
              have e : q ^ (J + 1) = ((2 : ℝ) ^ (J + 1)) ^ a := (rpow_two_pow (J + 1) a).symm
              rw [e]
              calc ((2 : ℝ) ^ (J + 1)) ^ a ≤ (2 / t) ^ a := Real.rpow_le_rpow (by positivity) h2 ha.le
                _ = q * t ^ (-a) := by
                    rw [div_eq_mul_inv, Real.mul_rpow (by norm_num) (by positivity), Real.inv_rpow ht.le,
                      Real.rpow_neg ht.le]
            rw [div_mul_eq_mul_div]
            gcongr
    -- second part
    have hB : ∑' i, f (i + (J + 1)) ≤ 1 / (1 - q') * t ^ (-a) := by
      have hs2 : Summable fun i => t ^ (-(2 * M : ℝ)) * q' ^ (i + (J + 1)) :=
        (hgeo.comp_injective (add_left_injective (J + 1)))
      calc ∑' i, f (i + (J + 1)) ≤ ∑' i : ℕ, t ^ (-(2 * M : ℝ)) * q' ^ (i + (J + 1)) := by
            refine (hfs.comp_injective (add_left_injective (J + 1))).tsum_le_tsum (fun i => ?_) hs2
            calc f (i + (J + 1)) ≤ t ^ (-(2 * M : ℝ)) * ((2 : ℝ) ^ (i + (J + 1))) ^ (a - 2 * M) := hfB _
              _ = _ := by rw [rpow_two_pow]
        _ = ∑' i : ℕ, (t ^ (-(2 * M : ℝ)) * q' ^ (J + 1)) * q' ^ i := by
            refine tsum_congr fun i => ?_
            rw [pow_add]; ring
        _ = t ^ (-(2 * M : ℝ)) * q' ^ (J + 1) / (1 - q') := by
            rw [tsum_mul_left, tsum_geometric_of_lt_one hq'0.le hq'1]; ring
        _ ≤ 1 / (1 - q') * t ^ (-a) := by
            have h3 : q' ^ (J + 1) ≤ t ^ (-(a - 2 * M)) := by
              have e : q' ^ (J + 1) = ((2 : ℝ) ^ (J + 1)) ^ (a - 2 * M) := (rpow_two_pow (J + 1) _).symm
              rw [e]
              calc ((2 : ℝ) ^ (J + 1)) ^ (a - 2 * M) ≤ (1 / t) ^ (a - 2 * M) :=
                    Real.rpow_le_rpow_of_nonpos (by positivity) hJ2.le (by linarith)
                _ = t ^ (-(a - 2 * M)) := by rw [one_div, Real.inv_rpow ht.le, Real.rpow_neg ht.le]
            calc t ^ (-(2 * M : ℝ)) * q' ^ (J + 1) / (1 - q')
                ≤ t ^ (-(2 * M : ℝ)) * t ^ (-(a - 2 * M)) / (1 - q') := by gcongr
              _ = 1 / (1 - q') * t ^ (-a) := by
                  have : -(2 * (M : ℝ)) + -(a - 2 * M) = -a := by ring
                  rw [← Real.rpow_add ht, this]; ring
    linarith

/-- the dyadic pieces `2^{js} kern Ψ 2^{-j}` -/
def Gt (s : ℝ) (Ψ : Euc d → ℂ) (j : ℕ) (z : Torus d) : ℂ :=
  (((2 : ℝ) ^ j) ^ s : ℝ) • kern Ψ (eps j) z

theorem Gt_bounds (hd : 0 < d) {Ψ : Euc d → ℂ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hsupp : ∀ ξ, 2 ≤ ‖ξ‖ → Ψ ξ = 0) (s : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (z : Torus d),
      ‖Gt s Ψ j z‖ ≤ C * ((2 : ℝ) ^ j) ^ (s + d) ∧
      Torus.tdist z 0 ^ (2 * N) * ‖Gt s Ψ j z‖ ≤ C * ((2 : ℝ) ^ j) ^ (s + d - 2 * N) := by
  obtain ⟨C1, hC1, h1⟩ := kern_sup_bound hΨ hsupp
  obtain ⟨C2, hC2, h2⟩ := kern_decay_bound hd hΨ hsupp N
  refine ⟨C1 + C2, by positivity, fun j z => ?_⟩
  have hx : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hs : 0 ≤ ((2 : ℝ) ^ j) ^ s := by positivity
  have hnorm : ‖Gt s Ψ j z‖ = ((2 : ℝ) ^ j) ^ s * ‖kern Ψ (eps j) z‖ := by
    unfold Gt; rw [norm_smul, Real.norm_of_nonneg hs]
  have hε := eps_pos j
  have hε1 := eps_le_one j
  have e0 : eps j ^ d = (((2 : ℝ) ^ j) ^ d)⁻¹ := by unfold eps; rw [inv_pow]
  have e1 : ((2 : ℝ) ^ j) ^ s * ((2 : ℝ) ^ j) ^ d = ((2 : ℝ) ^ j) ^ (s + d) := by
    rw [Real.rpow_add hx, Real.rpow_natCast]
  have e2 : ((2 : ℝ) ^ j) ^ s * (((2 : ℝ) ^ j) ^ d / ((2 : ℝ) ^ j) ^ (2 * N)) =
      ((2 : ℝ) ^ j) ^ (s + d - 2 * N) := by
    rw [show s + d - 2 * (N : ℝ) = s + (d - 2 * N) by ring, Real.rpow_add hx, Real.rpow_sub hx,
      Real.rpow_natCast]
    rw [show (2 * (N : ℝ)) = ((2 * N : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  constructor
  · rw [hnorm]
    calc ((2 : ℝ) ^ j) ^ s * ‖kern Ψ (eps j) z‖ ≤ ((2 : ℝ) ^ j) ^ s * (C1 / eps j ^ d) :=
          mul_le_mul_of_nonneg_left (h1 _ hε hε1 z) hs
      _ = C1 * ((2 : ℝ) ^ j) ^ (s + d) := by rw [e0, div_inv_eq_mul, ← e1]; ring
      _ ≤ (C1 + C2) * ((2 : ℝ) ^ j) ^ (s + d) := by gcongr; linarith
  · rw [hnorm]
    have h2' := h2 _ hε hε1 z
    have e3 : eps j ^ (2 * N) / eps j ^ d = ((2 : ℝ) ^ j) ^ d / ((2 : ℝ) ^ j) ^ (2 * N) := by
      unfold eps; rw [inv_pow, inv_pow, inv_div_inv]
    rw [e3] at h2'
    calc Torus.tdist z 0 ^ (2 * N) * (((2 : ℝ) ^ j) ^ s * ‖kern Ψ (eps j) z‖)
        = ((2 : ℝ) ^ j) ^ s * (Torus.tdist z 0 ^ (2 * N) * ‖kern Ψ (eps j) z‖) := by ring
      _ ≤ ((2 : ℝ) ^ j) ^ s * (C2 * (((2 : ℝ) ^ j) ^ d / ((2 : ℝ) ^ j) ^ (2 * N))) :=
          mul_le_mul_of_nonneg_left h2' hs
      _ = C2 * ((2 : ℝ) ^ j) ^ (s + d - 2 * N) := by rw [← e2]; ring
      _ ≤ (C1 + C2) * ((2 : ℝ) ^ j) ^ (s + d - 2 * N) := by gcongr; linarith

end Dyadic

/-! ### Basic identities for `trig` and `kern` -/

section TrigIdentities

theorem mode_zero_arg (k : Lattice d) : Torus.mode k (0 : Torus d) = 1 := by
  simp [Torus.mode, UnitAddTorus.mFourier]

theorem mode_neg_arg (k : Lattice d) (x : Torus d) : Torus.mode k (-x) = Torus.mode (-k) x := by
  have h := Torus.mode_add_arg k x (-x)
  rw [add_neg_cancel, mode_zero_arg] at h
  have h2 := Torus.mode_neg_lattice k x
  calc Torus.mode k (-x) = Torus.mode k (-x) * (Torus.mode (-k) x * Torus.mode k x) := by rw [h2, mul_one]
    _ = (Torus.mode k x * Torus.mode k (-x)) * Torus.mode (-k) x := by ring
    _ = _ := by rw [← h, one_mul]

theorem trig_neg (c : Lattice d → ℂ) (z : Torus d) :
    trig c (-z) = trig (fun k => c (-k)) z := by
  unfold trig
  rw [← Equiv.tsum_eq (Equiv.neg (Lattice d))]
  refine tsum_congr fun k => ?_
  simp [mode_neg_arg]

theorem kern_neg {φ : Euc d → ℂ} (he : ∀ ξ, φ (-ξ) = φ ξ) (ε : ℝ) (z : Torus d) :
    kern φ ε (-z) = kern φ ε z := by
  unfold kern
  rw [trig_neg]
  congr 1
  funext k
  unfold kcoef
  have : Lattice.toEuc (-k) = -Lattice.toEuc k := by ext i; simp [Lattice.toEuc]
  rw [this, smul_neg, he]

theorem integral_trig_mul_mode {n : ℕ} {c : Lattice d → ℂ} (hc : IsTrigPoly n c) (l : Lattice d) :
    ∫ z, trig c z * Torus.mode l z = c (-l) := by
  have e : ∀ z, trig c z * Torus.mode l z = ∑ k ∈ boxF d n, c k * (Torus.mode k z * Torus.mode l z) := by
    intro z; rw [trig_eq_sum hc, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun k _ => (Torus.integrable_mode_mul k l).const_mul _]
  simp_rw [integral_const_mul, Torus.integral_mode_mul]
  have hh : ∀ k : Lattice d, (k + l = 0 ↔ k = -l) := fun k => add_eq_zero_iff_eq_neg
  simp_rw [hh]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · by_contra hne
    exact h (mem_boxF.2 (hc _ (Ne.symm (Ne.symm (by simpa using fun h0 => hne h0.symm)))))

end TrigIdentities

/-! ### (c) The kernel as a sum -/

section Kernel

theorem tdist_pos_of_ne {z : Torus d} (hz : z ≠ 0) : 0 < Torus.tdist z 0 := by
  rcases (show 0 ≤ Torus.tdist z 0 by unfold Torus.tdist; positivity).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hz
    have h0 : Torus.centeredRep z = 0 := by
      have : ‖Torus.centeredRep (z - 0)‖ = 0 := h.symm
      simpa using this
    rw [← centeredRep_mk z, h0]
    funext i; simp [Torus.mk]

/-- the dyadic sum `∑_j 2^{js} kern Ψ 2^{-j}` -/
def GS (s : ℝ) (Ψ : Euc d → ℂ) (z : Torus d) : ℂ := ∑' j, Gt s Ψ j z

theorem Gt_summable_bound (hd : 0 < d) {Ψ : Euc d → ℂ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hsupp : ∀ ξ, 2 ≤ ‖ξ‖ → Ψ ξ = 0) (s : ℝ) (hs : 0 < s + d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Torus d, z ≠ 0 →
      Summable (fun j => ‖Gt s Ψ j z‖) ∧
        ∑' j, ‖Gt s Ψ j z‖ ≤ C * (Torus.tdist z 0 ^ (-(s + d)) + 1) := by
  set M : ℕ := ⌈s + d⌉₊ + 1 with hM
  have hM2 : s + d < 2 * M := by
    have := Nat.le_ceil (s + d)
    have h1 : (1 : ℝ) ≤ M := by rw [hM]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈s + d⌉₊]
    push_cast [hM] at h1 ⊢
    linarith
  obtain ⟨C0, hC0, hG⟩ := Gt_bounds hd hΨ hsupp s M
  obtain ⟨C1, hC1, hD⟩ := dyadic_sum_le hs hM2
  set K : ℝ := C0 + 1 with hK
  have hKpos : 0 < K := by positivity
  refine ⟨K * C1, by positivity, fun z hz => ?_⟩
  have ht := tdist_pos_of_ne hz
  set t := Torus.tdist z 0 with htdef
  have hf0 : ∀ j, 0 ≤ ‖Gt s Ψ j z‖ / K := fun j => by positivity
  have hfA : ∀ j, ‖Gt s Ψ j z‖ / K ≤ ((2 : ℝ) ^ j) ^ (s + d) := by
    intro j
    rw [div_le_iff₀ hKpos]
    calc ‖Gt s Ψ j z‖ ≤ C0 * ((2 : ℝ) ^ j) ^ (s + d) := (hG j z).1
      _ ≤ ((2 : ℝ) ^ j) ^ (s + d) * K := by
          rw [mul_comm]; gcongr; linarith
  have hfB : ∀ j, ‖Gt s Ψ j z‖ / K ≤ t ^ (-(2 * M : ℝ)) * ((2 : ℝ) ^ j) ^ (s + d - 2 * M) := by
    intro j
    rw [div_le_iff₀ hKpos]
    have h2 := (hG j z).2
    have htM : 0 < t ^ (2 * M) := by positivity
    have e : t ^ (-(2 * M : ℝ)) = (t ^ (2 * M))⁻¹ := by
      rw [Real.rpow_neg ht.le, show (2 * (M : ℝ)) = ((2 * M : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [e]
    have : ‖Gt s Ψ j z‖ ≤ (t ^ (2 * M))⁻¹ * (C0 * ((2 : ℝ) ^ j) ^ (s + d - 2 * M)) := by
      rw [← div_eq_inv_mul, le_div_iff₀ htM]; linarith
    calc ‖Gt s Ψ j z‖ ≤ (t ^ (2 * M))⁻¹ * (C0 * ((2 : ℝ) ^ j) ^ (s + d - 2 * M)) := this
      _ ≤ (t ^ (2 * M))⁻¹ * (K * ((2 : ℝ) ^ j) ^ (s + d - 2 * M)) := by
          gcongr; linarith
      _ = _ := by ring
  obtain ⟨hsum, hle⟩ := hD t ht (fun j => ‖Gt s Ψ j z‖ / K) hf0 hfA hfB
  refine ⟨(hsum.mul_left K).congr (fun j => by field_simp), ?_⟩
  have : ∑' j, ‖Gt s Ψ j z‖ = K * ∑' j, ‖Gt s Ψ j z‖ / K := by
    rw [← tsum_mul_left]; refine tsum_congr fun j => ?_; field_simp
  rw [this]
  calc K * ∑' j, ‖Gt s Ψ j z‖ / K ≤ K * (C1 * (t ^ (-(s + d)) + 1)) := by gcongr
    _ = _ := by ring

/-- the Lévy kernel candidate: `𝔨 = -Re ∑_j 2^{jθ} kern Φ 2^{-j}` -/
def levyK (θ : ℝ) (m₀ : Euc d → ℝ) (z : Torus d) : ℝ := -(GS θ (Phi m₀) z).re

theorem levyK_even {θ : ℝ} {m₀ : Euc d → ℝ} (he : ∀ ξ, m₀ (-ξ) = m₀ ξ) (z : Torus d) :
    levyK θ m₀ (-z) = levyK θ m₀ z := by
  unfold levyK GS Gt
  simp_rw [kern_neg (Phi_neg he)]

theorem levyK_bound (hd : 0 < d) {θ : ℝ} (hθ : 0 < θ) {m₀ : Euc d → ℝ}
    (hsm : ContDiffOn ℝ ∞ m₀ {ξ | ξ ≠ 0}) :
    ∃ C : ℝ, ∀ z : Torus d, z ≠ 0 → |levyK θ m₀ z| ≤ C * (Torus.tdist z 0 ^ (-(d : ℝ) - θ) + 1) := by
  obtain ⟨C, hC0, hC⟩ := Gt_summable_bound hd (contDiff_Phi hsm) (fun ξ h => Phi_large m₀ h) θ
    (by positivity)
  refine ⟨C, fun z hz => ?_⟩
  obtain ⟨hs, hle⟩ := hC z hz
  have e : -(d : ℝ) - θ = -(θ + d) := by ring
  rw [e]
  calc |levyK θ m₀ z| = |(GS θ (Phi m₀) z).re| := by unfold levyK; rw [abs_neg]
    _ ≤ ‖GS θ (Phi m₀) z‖ := Complex.abs_re_le_norm _
    _ ≤ ∑' j, ‖Gt θ (Phi m₀) j z‖ := norm_tsum_le_tsum_norm hs
    _ ≤ _ := hle

end Kernel

/-! ### (c) Smoothness off the origin -/

section Smooth


/-- `Ψ_i(ξ) = 2π i ξ_i Ψ(ξ)` -/
def Dpr (i : Fin d) (Ψ : Euc d → ℂ) (ξ : Euc d) : ℂ := (2 * Real.pi * Complex.I * (ξ i : ℂ)) * Ψ ξ

theorem contDiff_Dpr (i : Fin d) {Ψ : Euc d → ℂ} (hΨ : ContDiff ℝ ∞ Ψ) : ContDiff ℝ ∞ (Dpr i Ψ) := by
  unfold Dpr
  have : ContDiff ℝ ∞ fun ξ : Euc d => (ξ i : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff
  exact (contDiff_const.mul this).mul hΨ

theorem Dpr_large (i : Fin d) {Ψ : Euc d → ℂ} (hsupp : ∀ ξ, 2 ≤ ‖ξ‖ → Ψ ξ = 0) :
    ∀ ξ, 2 ≤ ‖ξ‖ → Dpr i Ψ ξ = 0 := fun ξ h => by simp [Dpr, hsupp ξ h]

/-- the real-linear phase `x ↦ 2π i k·x` as a continuous linear map -/
def phase (k : Lattice d) : Euc d →L[ℝ] ℂ :=
  ∑ i, ((2 * Real.pi * Complex.I * (k i : ℂ) : ℂ)) • (Complex.ofRealCLM.comp (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ))

theorem phase_apply (k : Lattice d) (x : Euc d) :
    phase k x = ((2 * Real.pi * Lattice.dot k x : ℝ) : ℂ) * Complex.I := by
  simp [phase, Lattice.dot, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem mode_mk_eq (k : Lattice d) (x : Euc d) : Torus.mode k (Torus.mk x) = Complex.exp (phase k x) := by
  rw [Torus.mode_mk, phase_apply]

theorem lift_kern_eq {Ψ : Euc d → ℂ} (hsupp : ∀ ξ, 2 ≤ ‖ξ‖ → Ψ ξ = 0) {ε : ℝ} (hε : 0 < ε) (x : Euc d) :
    Torus.lift (kern Ψ ε) x = ∑ k ∈ boxF d ⌈2 / ε⌉₊, kcoef Ψ ε k * Complex.exp (phase k x) := by
  simp only [Torus.lift, Function.comp, kern, trig_eq_sum (isTrigPoly_kcoef hsupp hε), mode_mk_eq]

theorem kcoef_Dpr (i : Fin d) (Ψ : Euc d → ℂ) (ε : ℝ) (k : Lattice d) :
    kcoef (Dpr i Ψ) ε k = (2 * Real.pi * Complex.I * ((ε : ℂ) * (k i : ℂ))) * kcoef Ψ ε k := by
  simp [kcoef, Dpr, Lattice.toEuc]

theorem hasFDerivAt_lift_kern {Ψ : Euc d → ℂ} (hsupp : ∀ ξ, 2 ≤ ‖ξ‖ → Ψ ξ = 0) {ε : ℝ} (hε : 0 < ε)
    (x : Euc d) :
    HasFDerivAt (Torus.lift (kern Ψ ε))
      (∑ i, (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).smulRight
        (ε⁻¹ • Torus.lift (kern (Dpr i Ψ) ε) x)) x := by
  have hfun : Torus.lift (kern Ψ ε) = fun x => ∑ k ∈ boxF d ⌈2 / ε⌉₊, kcoef Ψ ε k * Complex.exp (phase k x) :=
    funext (lift_kern_eq hsupp hε)
  rw [hfun]
  have hD : HasFDerivAt (fun x => ∑ k ∈ boxF d ⌈2 / ε⌉₊, kcoef Ψ ε k * Complex.exp (phase k x))
      (∑ k ∈ boxF d ⌈2 / ε⌉₊, kcoef Ψ ε k • (Complex.exp (phase k x) • phase k)) x :=
    HasFDerivAt.fun_sum fun k _ => ((phase k).hasFDerivAt.cexp).const_mul _
  convert hD using 1
  ext v
  have hphv : ∀ k : Lattice d, phase k v = ∑ i, (2 * Real.pi * Complex.I * (k i : ℂ)) * (v i : ℂ) := by
    intro k; simp [phase]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul,
    ContinuousLinearMap.smul_apply, hphv]
  simp_rw [lift_kern_eq (Dpr_large _ hsupp) hε, kcoef_Dpr]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hp : (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) v = v i := rfl
  simp only [Complex.real_smul, hp]
  have : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  push_cast
  field_simp

/-! ### geometry of the distance -/

theorem tdist_zero_eq_norm (z : Torus d) :
    Torus.tdist z 0 = ‖(WithLp.toLp 2 fun i => ‖z i‖ : Euc d)‖ := by
  unfold Torus.tdist
  rw [sub_zero, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have := HRS.PDE.ProdAux.abs_centeredRep z i
  simp only [Real.norm_eq_abs, this, abs_norm]

theorem norm_le_of_coord_le {u v : Euc d} (h0 : ∀ i, 0 ≤ u i) (h : ∀ i, u i ≤ v i) : ‖u‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  exact pow_le_pow_left₀ (h0 i) (h i) 2

theorem tdist_mk_sub_le (x y : Euc d) :
    Torus.tdist (Torus.mk y) 0 ≤ Torus.tdist (Torus.mk x) 0 + ‖y - x‖ := by
  set a : Euc d := WithLp.toLp 2 fun i => ‖(Torus.mk x) i‖ with ha
  set b : Euc d := WithLp.toLp 2 fun i => |y i - x i| with hb
  have hb' : ‖b‖ = ‖y - x‖ := by
    rw [hb, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Real.norm_eq_abs, sq_abs]
  rw [tdist_zero_eq_norm, tdist_zero_eq_norm, ← hb']
  have hle : ‖(WithLp.toLp 2 fun i => ‖(Torus.mk y) i‖ : Euc d)‖ ≤ ‖a + b‖ := by
    refine norm_le_of_coord_le (fun i => norm_nonneg _) (fun i => ?_)
    simp only [ha, hb, PiLp.add_apply]
    have : (Torus.mk y) i = (Torus.mk x) i + (((y i - x i : ℝ)) : UnitAddCircle) := by
      simp [Torus.mk]
    rw [this]
    exact (norm_add_le _ _).trans (add_le_add_right (HRS.PDE.ProdAux.norm_circle_le_abs _) _)
  exact hle.trans (norm_add_le _ _)


theorem Gt_uniform_bound (hd : 0 < d) {Ψ : Euc d → ℂ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hsupp : ∀ ξ, 2 ≤ ‖ξ‖ → Ψ ξ = 0) (s : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ (j : ℕ) (z : Torus d), δ ≤ Torus.tdist z 0 → ‖Gt s Ψ j z‖ ≤ u j := by
  set N : ℕ := ⌈s + d⌉₊ + 1 with hN
  have hN2 : s + d < 2 * N := by
    have := Nat.le_ceil (s + d)
    have h1 : (1 : ℝ) ≤ N := by rw [hN]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈s + d⌉₊]
    push_cast [hN] at h1 ⊢
    linarith
  obtain ⟨C, hC0, hC⟩ := Gt_bounds hd hΨ hsupp s N
  set q : ℝ := (2 : ℝ) ^ (s + d - 2 * N) with hq
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  refine ⟨fun j => C * (δ ^ (2 * N))⁻¹ * q ^ j, (summable_geometric_of_lt_one hq0.le hq1).mul_left _,
    fun j z hz => ?_⟩
  have h2 := (hC j z).2
  have hδN : 0 < δ ^ (2 * N) := by positivity
  have htN : δ ^ (2 * N) ≤ Torus.tdist z 0 ^ (2 * N) := pow_le_pow_left₀ hδ.le hz _
  have e : ((2 : ℝ) ^ j) ^ (s + d - 2 * N) = q ^ j := by rw [hq, rpow_two_pow]
  rw [e] at h2
  have : δ ^ (2 * N) * ‖Gt s Ψ j z‖ ≤ C * q ^ j :=
    le_trans (mul_le_mul_of_nonneg_right htN (norm_nonneg _)) h2
  show ‖Gt s Ψ j z‖ ≤ C * (δ ^ (2 * N))⁻¹ * q ^ j
  calc ‖Gt s Ψ j z‖ ≤ C * q ^ j * (δ ^ (2 * N))⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hδN]; linarith
    _ = _ := by ring


theorem hasFDerivAt_lift_Gt {Ψ : Euc d → ℂ} (hsupp : ∀ ξ, 2 ≤ ‖ξ‖ → Ψ ξ = 0) (s : ℝ) (j : ℕ)
    (x : Euc d) :
    HasFDerivAt (Torus.lift (Gt s Ψ j))
      (∑ i, (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).smulRight
        (Torus.lift (Gt (s + 1) (Dpr i Ψ) j) x)) x := by
  have h := (hasFDerivAt_lift_kern hsupp (eps_pos j) x).const_smul ((((2 : ℝ) ^ j) ^ s : ℝ))
  have hfun : Torus.lift (Gt s Ψ j) = fun y => (((2 : ℝ) ^ j) ^ s : ℝ) • Torus.lift (kern Ψ (eps j)) y := by
    funext y; rfl
  rw [hfun]
  convert h using 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext v
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply]
  have e : (((2 : ℝ) ^ j) ^ (s + 1) : ℝ) = ((2 : ℝ) ^ j) ^ s * (eps j)⁻¹ := by
    rw [Real.rpow_add (by positivity), Real.rpow_one]; unfold eps; rw [inv_inv]
  simp only [Torus.lift, Function.comp, Gt]
  rw [e]
  simp only [smul_smul]
  congr 1
  ring

theorem norm_proj_smulRight_le (i : Fin d) (v : ℂ) :
    ‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).smulRight v‖ ≤ ‖v‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun w => ?_
  rw [ContinuousLinearMap.smulRight_apply, norm_smul, mul_comm]
  gcongr
  have : (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) w = w i := rfl
  rw [this, Real.norm_eq_abs]
  exact PiLp.norm_apply_le w i

theorem tdist_lower_on_ball {x y : Euc d} (hy : y ∈ Metric.ball x (Torus.tdist (Torus.mk x) 0 / 2)) :
    Torus.tdist (Torus.mk x) 0 / 2 ≤ Torus.tdist (Torus.mk y) 0 := by
  have h := tdist_mk_sub_le y x
  have h2 : ‖x - y‖ < Torus.tdist (Torus.mk x) 0 / 2 := by
    rw [mem_ball_iff_norm'] at hy; exact hy
  linarith

theorem hasFDerivAt_lift_GS (hd : 0 < d) {Ψ : Euc d → ℂ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hsupp : ∀ ξ, 2 ≤ ‖ξ‖ → Ψ ξ = 0) (s : ℝ) {x : Euc d} (hx : Torus.mk x ≠ 0) :
    HasFDerivAt (Torus.lift (GS s Ψ))
      (∑ i, (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).smulRight
        (Torus.lift (GS (s + 1) (Dpr i Ψ)) x)) x := by
  set t₀ := Torus.tdist (Torus.mk x) 0 with ht₀def
  have ht₀ : 0 < t₀ := tdist_pos_of_ne hx
  choose u hu hub using fun i : Fin d =>
    Gt_uniform_bound hd (contDiff_Dpr i hΨ) (Dpr_large i hsupp) (s + 1) (half_pos ht₀)
  obtain ⟨u0, hu0, hub0⟩ := Gt_uniform_bound hd hΨ hsupp s ht₀
  set U : ℕ → ℝ := fun j => ∑ i, u i j with hUdef
  have hU : Summable U := summable_sum fun i _ => hu i
  have hbound : ∀ (j : ℕ) (y : Euc d), y ∈ Metric.ball x (t₀ / 2) →
      ‖∑ i, (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).smulRight (Torus.lift (Gt (s + 1) (Dpr i Ψ) j) y)‖ ≤ U j := by
    intro j y hy
    have hl := tdist_lower_on_ball hy
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact (norm_proj_smulRight_le i _).trans (hub i j _ hl)
  have hf0 : Summable fun j => Torus.lift (Gt s Ψ j) x :=
    Summable.of_norm_bounded hu0 fun j => hub0 j _ le_rfl
  have key := hasFDerivAt_tsum_of_isPreconnected (f := fun j y => Torus.lift (Gt s Ψ j) y)
    (f' := fun j y => ∑ i, (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).smulRight
      (Torus.lift (Gt (s + 1) (Dpr i Ψ) j) y))
    (u := U) (s := Metric.ball x (t₀ / 2)) hU Metric.isOpen_ball (convex_ball _ _).isPreconnected
    (fun j y _ => hasFDerivAt_lift_Gt hsupp s j y) (fun j y hy => hbound j y hy)
    (Metric.mem_ball_self (half_pos ht₀)) hf0 (Metric.mem_ball_self (half_pos ht₀))
  have hsum : ∀ i : Fin d, HasSum (fun j => Torus.lift (Gt (s + 1) (Dpr i Ψ) j) x)
      (Torus.lift (GS (s + 1) (Dpr i Ψ)) x) := fun i =>
    (Summable.of_norm_bounded (hu i) fun j => hub i j _ (by
      have := tdist_lower_on_ball (x := x) (y := x) (Metric.mem_ball_self (half_pos ht₀)); exact this)).hasSum
  have hS : HasSum (fun j => ∑ i, (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).smulRight
      (Torus.lift (Gt (s + 1) (Dpr i Ψ) j) x))
      (∑ i, (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).smulRight (Torus.lift (GS (s + 1) (Dpr i Ψ)) x)) :=
    hasSum_sum fun i _ => (hsum i).mapL (ContinuousLinearMap.smulRightL ℝ (Euc d) ℂ
      (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ))
  rw [hS.tsum_eq] at key
  exact key

theorem isOpen_mk_ne : IsOpen {x : Euc d | Torus.mk x ≠ 0} :=
  (isClosed_singleton.preimage Torus.continuous_mk).isOpen_compl

theorem contDiffOn_lift_GS_nat (hd : 0 < d) (n : ℕ) : ∀ (s : ℝ) (Ψ : Euc d → ℂ), ContDiff ℝ ∞ Ψ →
    (∀ ξ, 2 ≤ ‖ξ‖ → Ψ ξ = 0) →
    ContDiffOn ℝ (n : WithTop ℕ∞) (Torus.lift (GS s Ψ)) {x : Euc d | Torus.mk x ≠ 0} := by
  induction n with
  | zero =>
    intro s Ψ hΨ hsupp
    have : DifferentiableOn ℝ (Torus.lift (GS s Ψ)) {x : Euc d | Torus.mk x ≠ 0} := fun x hx =>
      (hasFDerivAt_lift_GS hd hΨ hsupp s hx).differentiableAt.differentiableWithinAt
    simpa using this.continuousOn
  | succ n ih =>
    intro s Ψ hΨ hsupp
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_mk_ne]
    refine ⟨fun x hx => (hasFDerivAt_lift_GS hd hΨ hsupp s hx).differentiableAt.differentiableWithinAt,
      fun h => by simp at h, ?_⟩
    have hfd : ∀ x ∈ {x : Euc d | Torus.mk x ≠ 0}, (∑ i, (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).smulRight
        (Torus.lift (GS (s + 1) (Dpr i Ψ)) x)) = fderiv ℝ (Torus.lift (GS s Ψ)) x := fun x hx =>
      (hasFDerivAt_lift_GS hd hΨ hsupp s hx).fderiv.symm
    refine ContDiffOn.congr ?_ (fun x hx => (hfd x hx).symm)
    refine ContDiffOn.sum fun i _ => ?_
    exact (ContinuousLinearMap.smulRightL ℝ (Euc d) ℂ
      (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)).contDiff.comp_contDiffOn
      (ih (s + 1) (Dpr i Ψ) (contDiff_Dpr i hΨ) (Dpr_large i hsupp))

theorem contDiffOn_lift_GS (hd : 0 < d) {Ψ : Euc d → ℂ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hsupp : ∀ ξ, 2 ≤ ‖ξ‖ → Ψ ξ = 0) (s : ℝ) :
    ContDiffOn ℝ ∞ (Torus.lift (GS s Ψ)) {x : Euc d | Torus.mk x ≠ 0} := by
  rw [contDiffOn_infty]
  exact fun n => contDiffOn_lift_GS_nat hd n s Ψ hΨ hsupp


theorem levyK_smooth (hd : 0 < d) (θ : ℝ) {m₀ : Euc d → ℝ} (hsm : ContDiffOn ℝ ∞ m₀ {ξ | ξ ≠ 0}) :
    Torus.IsSmoothOffZero (levyK θ m₀) := by
  have h := contDiffOn_lift_GS hd (contDiff_Phi hsm) (fun ξ h => Phi_large m₀ h) θ
  have h2 := (Complex.reCLM.contDiff.comp_contDiffOn h).neg
  exact h2

end Smooth

/-! ### (d) Integrability and the symbol identity -/

section Symbol


theorem integrable_of_cont {E : Type*} [NormedAddCommGroup E] {f : Torus d → E} (hf : Continuous f) :
    Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem cosMode_cplx (k : Lattice d) (z : Torus d) :
    ((Torus.cosMode k z : ℝ) : ℂ) = (Torus.mode k z + Torus.mode (-k) z) / 2 := by
  rw [Torus.cosMode, Torus.mode_neg, Complex.re_eq_add_conj]

theorem integral_kern_one_sub_cos {φ : Euc d → ℂ} (hsupp : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0)
    (he : ∀ ξ, φ (-ξ) = φ ξ) (h0 : φ 0 = 0) {ε : ℝ} (hε : 0 < ε) (k : Lattice d) :
    ∫ z, kern φ ε z * (1 - ((Torus.cosMode k z : ℝ) : ℂ)) = - kcoef φ ε k := by
  have hc := isTrigPoly_kcoef hsupp hε
  have hK : Continuous (kern φ ε) := continuous_kern hsupp hε
  have e : ∀ z, kern φ ε z * (1 - ((Torus.cosMode k z : ℝ) : ℂ)) =
      kern φ ε z * Torus.mode 0 z - (1 / 2 : ℂ) * (kern φ ε z * Torus.mode k z + kern φ ε z * Torus.mode (-k) z) := by
    intro z; rw [cosMode_cplx, Torus.mode_zero]; ring
  have i1 : ∀ l : Lattice d, Integrable fun z => kern φ ε z * Torus.mode l z := fun l =>
    integrable_of_cont (hK.mul (Torus.continuous_mode l))
  have i2 : Integrable fun z => (1 / 2 : ℂ) * (kern φ ε z * Torus.mode k z + kern φ ε z * Torus.mode (-k) z) :=
    ((i1 k).add (i1 (-k))).const_mul _
  simp_rw [e]
  rw [integral_sub (i1 0) i2, integral_const_mul, integral_add (i1 k) (i1 (-k))]
  unfold kern
  rw [integral_trig_mul_mode hc, integral_trig_mul_mode hc, integral_trig_mul_mode hc]
  have hneg : kcoef φ ε (-k) = kcoef φ ε k := by
    unfold kcoef
    have : Lattice.toEuc (-k) = -Lattice.toEuc k := by ext i; simp [Lattice.toEuc]
    rw [this, smul_neg, he]
  have hz : kcoef φ ε (-(0 : Lattice d)) = 0 := by
    unfold kcoef
    have : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
    simp [this, h0]
  rw [hz, neg_neg, hneg]
  ring

/-- the real terms `K_j = -Re (2^{jθ} kern Φ 2^{-j})` -/
def Kj (θ : ℝ) (m₀ : Euc d → ℝ) (j : ℕ) (z : Torus d) : ℝ := -(Gt θ (Phi m₀) j z).re

theorem continuous_Kj (θ : ℝ) (m₀ : Euc d → ℝ) (j : ℕ) :
    Continuous (Kj θ m₀ j) := by
  have hk := continuous_kern (fun ξ h => Phi_large m₀ h) (eps_pos j)
  unfold Kj Gt
  exact (Complex.continuous_re.comp (hk.const_smul (((2 : ℝ) ^ j) ^ θ))).neg

theorem integral_Kj_cos {θ : ℝ} {m₀ : Euc d → ℝ}
    (he : ∀ ξ, m₀ (-ξ) = m₀ ξ) (j : ℕ) (k : Lattice d) :
    ∫ z, Kj θ m₀ j z * (1 - Torus.cosMode k z) = kap θ m₀ j (Lattice.toEuc k) := by
  have hsupp : ∀ ξ, 2 ≤ ‖ξ‖ → Phi m₀ ξ = 0 := fun ξ h => Phi_large m₀ h
  have hK : Continuous (kern (Phi m₀) (eps j)) := continuous_kern hsupp (eps_pos j)
  have hcos := Torus.continuous_cosMode (d := d) k
  have e1 : ∀ z, Kj θ m₀ j z * (1 - Torus.cosMode k z) =
      (-(((2 : ℝ) ^ j) ^ θ) : ℝ) * (kern (Phi m₀) (eps j) z * (1 - ((Torus.cosMode k z : ℝ) : ℂ))).re := by
    intro z
    unfold Kj Gt
    have h1 : (1 - ((Torus.cosMode k z : ℝ) : ℂ)) = (((1 - Torus.cosMode k z : ℝ)) : ℂ) := by push_cast; ring
    rw [h1, Complex.re_mul_ofReal, Complex.smul_re]
    simp only [smul_eq_mul]
    ring
  simp_rw [e1]
  rw [integral_const_mul]
  have hi : Integrable fun z => kern (Phi m₀) (eps j) z * (1 - ((Torus.cosMode k z : ℝ) : ℂ)) :=
    integrable_of_cont (hK.mul (continuous_const.sub (Complex.continuous_ofReal.comp hcos)))
  have h2 : ∫ z, (kern (Phi m₀) (eps j) z * (1 - ((Torus.cosMode k z : ℝ) : ℂ))).re =
      (∫ z, kern (Phi m₀) (eps j) z * (1 - ((Torus.cosMode k z : ℝ) : ℂ))).re := integral_re hi
  rw [h2, integral_kern_one_sub_cos hsupp (Phi_neg he) (by simp [Phi, PhiR_zero]) (eps_pos j) k]
  unfold kap kcoef Phi
  simp only [Complex.neg_re, Complex.ofReal_re]
  ring

theorem tdist_zero_zero : Torus.tdist (0 : Torus d) 0 = 0 := by
  rw [tdist_zero_eq_norm]
  have : (WithLp.toLp 2 fun i => ‖(0 : Torus d) i‖ : Euc d) = 0 := by ext i; simp
  rw [this]; simp

theorem hasSum_Kj {θ : ℝ} {m₀ : Euc d → ℝ} (hd : 0 < d) (hθ : 0 < θ)
    (hsm : ContDiffOn ℝ ∞ m₀ {ξ | ξ ≠ 0}) {z : Torus d} (hz : z ≠ 0) :
    HasSum (fun j => Kj θ m₀ j z) (levyK θ m₀ z) := by
  obtain ⟨C, -, hC⟩ := Gt_summable_bound hd (contDiff_Phi hsm) (fun ξ h => Phi_large m₀ h) θ
    (by positivity)
  obtain ⟨hs, -⟩ := hC z hz
  have h1 : HasSum (fun j => Gt θ (Phi m₀) j z) (GS θ (Phi m₀) z) := (hs.of_norm).hasSum
  have h2 := (Complex.reCLM.hasSum h1).neg
  exact h2

theorem measurable_levyK {θ : ℝ} {m₀ : Euc d → ℝ} (hd : 0 < d) (hθ : 0 < θ)
    (hsm : ContDiffOn ℝ ∞ m₀ {ξ | ξ ≠ 0}) : Measurable (levyK θ m₀) := by
  set h : Torus d → ℝ := fun z => if z = 0 then 0 else levyK θ m₀ z with hh
  have hmeas : Measurable h := by
    refine measurable_of_tendsto_metrizable (f := fun n z => if z = 0 then 0 else ∑ j ∈ Finset.range n, Kj θ m₀ j z)
      (fun n => ?_) ?_
    · refine Measurable.ite (measurableSet_singleton _) measurable_const ?_
      exact (continuous_finsetSum _ fun j _ => continuous_Kj θ m₀ j).measurable
    · rw [tendsto_pi_nhds]
      intro z
      by_cases hz : z = 0
      · simp [hz, hh]
      · simp only [hz, ite_false, hh]
        exact (hasSum_Kj hd hθ hsm hz).tendsto_sum_nat
  have : levyK θ m₀ = fun z => if z = 0 then levyK θ m₀ 0 else h z := by
    funext z
    by_cases hz : z = 0
    · simp [hz]
    · simp [hz, hh]
  rw [this]
  exact Measurable.ite (measurableSet_singleton _) measurable_const hmeas

theorem Gt_moment2 {Ψ : Euc d → ℂ} (hΨ : ContDiff ℝ ∞ Ψ) (hsupp : ∀ ξ, 2 ≤ ‖ξ‖ → Ψ ξ = 0) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, Integrable (fun z : Torus d => Torus.tdist z 0 ^ 2 * ‖Gt s Ψ j z‖) ∧
      ∫ z, Torus.tdist z 0 ^ 2 * ‖Gt s Ψ j z‖ ≤ C * ((2 : ℝ) ^ (s - 2)) ^ j := by
  obtain ⟨C, hC0, hC⟩ := kern_L1_moment2_bound hΨ hsupp
  refine ⟨C, hC0, fun j => ?_⟩
  have hx : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hs : 0 ≤ ((2 : ℝ) ^ j) ^ s := by positivity
  have hnorm : ∀ z, ‖Gt s Ψ j z‖ = ((2 : ℝ) ^ j) ^ s * ‖kern Ψ (eps j) z‖ := by
    intro z; unfold Gt; rw [norm_smul, Real.norm_of_nonneg hs]
  obtain ⟨hi, hle⟩ := hC (eps j) (eps_pos j) (eps_le_one j)
  have e : ∀ z : Torus d, Torus.tdist z 0 ^ 2 * ‖Gt s Ψ j z‖ =
      ((2 : ℝ) ^ j) ^ s * (Torus.tdist z 0 ^ 2 * ‖kern Ψ (eps j) z‖) := by
    intro z; rw [hnorm]; ring
  simp_rw [e]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul]
  have e2 : ((2 : ℝ) ^ j) ^ s * eps j ^ 2 = ((2 : ℝ) ^ (s - 2)) ^ j := by
    rw [← rpow_two_pow, Real.rpow_sub hx, Real.rpow_two]
    unfold eps; rw [inv_pow]; ring
  calc ((2 : ℝ) ^ j) ^ s * ∫ z, Torus.tdist z 0 ^ 2 * ‖kern Ψ (eps j) z‖
      ≤ ((2 : ℝ) ^ j) ^ s * (C * eps j ^ 2) := mul_le_mul_of_nonneg_left hle hs
    _ = C * (((2 : ℝ) ^ j) ^ s * eps j ^ 2) := by ring
    _ = _ := by rw [e2]

theorem integrable_tsum_aux {α : Type*} [MeasurableSpace α] {μ : Measure α} {F : ℕ → α → ℝ}
    (hF : ∀ j, Integrable (F j) μ) (hs : Summable fun j => ∫ a, ‖F j a‖ ∂μ)
    (hmeas : AEStronglyMeasurable (fun a => ∑' j, F j a) μ) :
    Integrable (fun a => ∑' j, F j a) μ := by
  refine ⟨hmeas, ?_⟩
  unfold HasFiniteIntegral
  calc ∫⁻ a, ‖∑' j, F j a‖ₑ ∂μ ≤ ∫⁻ a, ∑' j, ‖F j a‖ₑ ∂μ :=
        lintegral_mono fun a => enorm_tsum_le_tsum_enorm
    _ = ∑' j, ∫⁻ a, ‖F j a‖ₑ ∂μ := lintegral_tsum fun j => (hF j).1.aemeasurable.enorm
    _ = ∑' j, ENNReal.ofReal (∫ a, ‖F j a‖ ∂μ) := by
        refine tsum_congr fun j => ?_
        rw [ofReal_integral_norm_eq_lintegral_enorm (hF j)]
    _ = ENNReal.ofReal (∑' j, ∫ a, ‖F j a‖ ∂μ) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun j => integral_nonneg fun a => norm_nonneg _) hs).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

theorem levyK_weighted {θ : ℝ} {m₀ : Euc d → ℝ} (hd : 0 < d) (hθ0 : 0 < θ) (hθ2 : θ < 2)
    (hsm : ContDiffOn ℝ ∞ m₀ {ξ | ξ ≠ 0}) {w : Torus d → ℝ} (hw : Measurable w) {c : ℝ}
    (hc0 : 0 ≤ c) (hwb : ∀ z, |w z| ≤ c * Torus.tdist z 0 ^ 2) :
    Integrable (fun z => levyK θ m₀ z * w z) ∧
      HasSum (fun j => ∫ z, Kj θ m₀ j z * w z) (∫ z, levyK θ m₀ z * w z) := by
  have hΦ := contDiff_Phi hsm
  have hsupp : ∀ ξ, 2 ≤ ‖ξ‖ → Phi m₀ ξ = 0 := fun ξ h => Phi_large m₀ h
  obtain ⟨C0, hC0, hM⟩ := Gt_moment2 hΦ hsupp θ
  obtain ⟨C1, hC1, hG⟩ := Gt_bounds hd hΦ hsupp θ 0
  set F : ℕ → Torus d → ℝ := fun j z => Kj θ m₀ j z * w z with hF
  have hKn : ∀ j z, ‖Kj θ m₀ j z‖ ≤ ‖Gt θ (Phi m₀) j z‖ := fun j z => by
    unfold Kj; rw [Real.norm_eq_abs, abs_neg]; exact Complex.abs_re_le_norm _
  have hFm : ∀ j, Measurable (F j) := fun j => (continuous_Kj θ m₀ j).measurable.mul hw
  have hFi : ∀ j, Integrable (F j) := by
    intro j
    refine Integrable.of_bound (hFm j).aestronglyMeasurable (C1 * ((2 : ℝ) ^ j) ^ (θ + d) * (c * (d : ℝ) ^ 2))
      (Filter.Eventually.of_forall fun z => ?_)
    rw [hF]
    simp only
    rw [norm_mul]
    have h1 : ‖Kj θ m₀ j z‖ ≤ C1 * ((2 : ℝ) ^ j) ^ (θ + d) := (hKn j z).trans (hG j z).1
    have h2 : ‖w z‖ ≤ c * (d : ℝ) ^ 2 := by
      rw [Real.norm_eq_abs]
      refine (hwb z).trans ?_
      have := tdist_zero_le z
      have h0 : 0 ≤ Torus.tdist z 0 := by unfold Torus.tdist; positivity
      gcongr
    exact mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
  have hbound : ∀ j z, ‖F j z‖ ≤ c * (Torus.tdist z 0 ^ 2 * ‖Gt θ (Phi m₀) j z‖) := by
    intro j z
    rw [hF]; simp only
    rw [norm_mul]
    calc ‖Kj θ m₀ j z‖ * ‖w z‖ ≤ ‖Gt θ (Phi m₀) j z‖ * (c * Torus.tdist z 0 ^ 2) := by
          apply mul_le_mul (hKn j z) _ (norm_nonneg _) (norm_nonneg _)
          rw [Real.norm_eq_abs]; exact hwb z
      _ = _ := by ring
  have hFn : ∀ j, ∫ z, ‖F j z‖ ≤ c * (C0 * ((2 : ℝ) ^ (θ - 2)) ^ j) := by
    intro j
    obtain ⟨hi, hle⟩ := hM j
    calc ∫ z, ‖F j z‖ ≤ ∫ z, c * (Torus.tdist z 0 ^ 2 * ‖Gt θ (Phi m₀) j z‖) :=
          integral_mono (hFi j).norm (hi.const_mul c) (fun z => hbound j z)
      _ = c * ∫ z, Torus.tdist z 0 ^ 2 * ‖Gt θ (Phi m₀) j z‖ := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hle hc0
  have hq1 : (2 : ℝ) ^ (θ - 2) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hsum : Summable fun j => ∫ z, ‖F j z‖ :=
    Summable.of_nonneg_of_le (fun j => integral_nonneg fun z => norm_nonneg _) hFn
      ((summable_geometric_of_lt_one (by positivity) hq1).mul_left C0 |>.mul_left c)
  have htsum : ∀ z, ∑' j, F j z = levyK θ m₀ z * w z := by
    intro z
    by_cases hz : z = 0
    · have hw0 : w z = 0 := by
        have := hwb z
        rw [hz, tdist_zero_zero] at this
        subst hz
        simpa using this
      simp [hF, hw0]
    · exact ((hasSum_Kj hd hθ0 hsm hz).mul_right (w z)).tsum_eq
  have hmeas : AEStronglyMeasurable (fun z => levyK θ m₀ z * w z) volume :=
    ((measurable_levyK hd hθ0 hsm).mul hw).aestronglyMeasurable
  refine ⟨?_, ?_⟩
  · have := integrable_tsum_aux hFi hsum (by simpa [htsum] using hmeas)
    simpa [htsum] using this
  · have := hasSum_integral_of_summable_integral_norm hFi hsum
    simpa [htsum] using this

theorem one_sub_cosMode_le (k : Lattice d) (z : Torus d) :
    1 - Torus.cosMode k z ≤ 2 * Real.pi ^ 2 * Lattice.enorm k ^ 2 * Torus.tdist z 0 ^ 2 := by
  set c := Torus.centeredRep z with hc
  have hz : z = Torus.mk c := (centeredRep_mk z).symm
  have h1 : Torus.cosMode k z = Real.cos (Torus.freqFunctional k c) := by
    rw [hz, Torus.cosMode_mk, Torus.freqFunctional_apply]
  have h2 : Torus.tdist z 0 = ‖c‖ := by unfold Torus.tdist; rw [sub_zero]
  have h3 : |Torus.freqFunctional k c| ≤ 2 * Real.pi * Lattice.enorm k * ‖c‖ := by
    rw [← Real.norm_eq_abs]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (Torus.norm_freqFunctional_le k) (norm_nonneg _))
  have h4 := Real.one_sub_sq_div_two_le_cos (x := Torus.freqFunctional k c)
  have h5 : (Torus.freqFunctional k c) ^ 2 ≤ (2 * Real.pi * Lattice.enorm k * ‖c‖) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h3 2
  rw [h1, h2]
  nlinarith

theorem levyK_symbol {θ : ℝ} {m₀ : Euc d → ℝ} (𝔪 : Lattice d → ℝ) (hd : 0 < d) (hθ0 : 0 < θ) (hθ2 : θ < 2)
    (hsm : ContDiffOn ℝ ∞ m₀ {ξ | ξ ≠ 0}) (he : ∀ ξ, m₀ (-ξ) = m₀ ξ)
    (hhom : ∀ c : ℝ, 0 < c → ∀ ξ, m₀ (c • ξ) = c ^ θ * m₀ ξ)
    (hext : ∀ k : Lattice d, k ≠ 0 → 𝔪 k = m₀ (Lattice.toEuc k)) (h0 : 𝔪 0 = 0) (k : Lattice d) :
    Integrable (fun z => levyK θ m₀ z * (1 - Torus.cosMode k z)) ∧
      ∫ z, levyK θ m₀ z * (1 - Torus.cosMode k z) = 𝔪 k := by
  have hw : Measurable (fun z : Torus d => 1 - Torus.cosMode k z) :=
    (measurable_const.sub (Torus.continuous_cosMode k).measurable)
  have hwb : ∀ z : Torus d, |1 - Torus.cosMode k z| ≤
      (2 * Real.pi ^ 2 * Lattice.enorm k ^ 2) * Torus.tdist z 0 ^ 2 := by
    intro z
    have h1 : 0 ≤ 1 - Torus.cosMode k z := by
      have := Real.cos_le_one (2 * Real.pi * Lattice.dot k (Torus.centeredRep z))
      have h2 : Torus.cosMode k z = Real.cos (2 * Real.pi * Lattice.dot k (Torus.centeredRep z)) := by
        conv_lhs => rw [← centeredRep_mk z]
        exact Torus.cosMode_mk _ _
      linarith
    rw [abs_of_nonneg h1]
    exact one_sub_cosMode_le k z
  obtain ⟨hi, hs⟩ := levyK_weighted hd hθ0 hθ2 hsm hw (by positivity) hwb
  refine ⟨hi, ?_⟩
  simp_rw [integral_Kj_cos he] at hs
  exact hs.unique (hasSum_kap 𝔪 hhom hext h0 k)

theorem levyK_integrable_sq {θ : ℝ} {m₀ : Euc d → ℝ} (hd : 0 < d) (hθ0 : 0 < θ) (hθ2 : θ < 2)
    (hsm : ContDiffOn ℝ ∞ m₀ {ξ | ξ ≠ 0}) :
    Integrable (fun z => levyK θ m₀ z * Torus.tdist z 0 ^ 2) := by
  have := (levyK_weighted (w := fun z : Torus d => Torus.tdist z 0 ^ 2) hd hθ0 hθ2 hsm
    (measurable_tdist_zero.pow_const 2) (c := 1) zero_le_one
    (fun z => by rw [one_mul, abs_of_nonneg (by positivity)])).1
  exact this


end Symbol

/-! ### (e) The principal value formula -/

section PV


theorem mk_neg' (x : Euc d) : Torus.mk (-x) = -Torus.mk x := by
  funext i; simp [Torus.mk]

theorem add_eq_mk (x z : Torus d) : x + z = Torus.mk (Torus.rep x + Torus.centeredRep z) := by
  rw [mk_add, Torus.mk_rep, centeredRep_mk]

theorem sub_eq_mk (x z : Torus d) : x - z = Torus.mk (Torus.rep x - Torus.centeredRep z) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, mk_add, mk_neg', Torus.mk_rep, centeredRep_mk]

/-- second-order estimate for `C^{1,1}` functions -/
theorem second_diff_le {L : ℝ} {u : Torus d → ℝ} (hu1 : Torus.IsCk 1 u)
    (hL : LipschitzWith (Real.toNNReal L) (fun x => fderiv ℝ (Torus.lift u) x)) (x z : Torus d) :
    |u x - (u (x + z) + u (x - z)) / 2| ≤ (Real.toNNReal L : ℝ) * Torus.tdist z 0 ^ 2 := by
  set U := Torus.lift u with hU
  have hd : Differentiable ℝ U := hu1.differentiable (by norm_num)
  set p := Torus.rep x
  set v := Torus.centeredRep z
  have e0 : U p = u x := by simp [hU, Torus.lift, p, Torus.mk_rep]
  have e1 : U (p + v) = u (x + z) := by rw [add_eq_mk]; rfl
  have e2 : U (p - v) = u (x - z) := by rw [sub_eq_mk]; rfl
  have ht : Torus.tdist z 0 = ‖v‖ := by unfold Torus.tdist; rw [sub_zero]
  set K : ℝ := (Real.toNNReal L : ℝ) with hK
  set h : ℝ → ℝ := fun s => U (p + s • v) + U (p - s • v) - 2 * U p with hh
  have hderiv : ∀ s : ℝ, HasDerivAt h (fderiv ℝ U (p + s • v) v - fderiv ℝ U (p - s • v) v) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => p + s • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add p
    have h2 : HasDerivAt (fun s : ℝ => p - s • v) (-v) s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_sub p
    have a1 := (hd (p + s • v)).hasFDerivAt.comp_hasDerivAt s h1
    have a2 := (hd (p - s • v)).hasFDerivAt.comp_hasDerivAt s h2
    have := (a1.add a2).sub_const (2 * U p)
    exact this.congr_deriv (by simp [map_neg, sub_eq_add_neg])
  have hbound : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖deriv h s‖ ≤ 2 * K * ‖v‖ ^ 2 := by
    intro s hs
    rw [(hderiv s).deriv, ← ContinuousLinearMap.sub_apply]
    have hl : ‖fderiv ℝ U (p + s • v) - fderiv ℝ U (p - s • v)‖ ≤ K * (2 * s * ‖v‖) := by
      have := hL.dist_le_mul (p + s • v) (p - s • v)
      rw [dist_eq_norm, dist_eq_norm] at this
      have e : p + s • v - (p - s • v) = (2 * s) • v := by
        rw [two_mul, add_smul]; abel
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.1])] at this
      exact this
    calc _ ≤ ‖fderiv ℝ U (p + s • v) - fderiv ℝ U (p - s • v)‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * (2 * s * ‖v‖) * ‖v‖ := by gcongr
      _ ≤ K * (2 * 1 * ‖v‖) * ‖v‖ := by gcongr; exact hs.2
      _ = 2 * K * ‖v‖ ^ 2 := by ring
  have hdiff : ∀ s ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ h s := fun s _ => (hderiv s).differentiableAt
  have := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_Icc 0 1)
    (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
  have h0 : h 0 = 0 := by simp [hh]; ring
  have h1 : h 1 = u (x + z) + u (x - z) - 2 * u x := by simp [hh, e0, e1, e2]
  rw [h0, h1, sub_zero, Real.norm_eq_abs, sub_zero, norm_one, mul_one] at this
  rw [ht]
  have e : u x - (u (x + z) + u (x - z)) / 2 = -((u (x + z) + u (x - z) - 2 * u x) / 2) := by ring
  rw [e, abs_neg, abs_div, abs_two]
  linarith

/-! ### principal value -/

theorem measurableSet_far (ε : ℝ) : MeasurableSet {z : Torus d | ε < Torus.tdist z 0} :=
  measurableSet_lt measurable_const measurable_tdist_zero

theorem integrableOn_far {𝔨 : Torus d → ℝ} (hm : Measurable 𝔨)
    (hI : Integrable (fun z => 𝔨 z * Torus.tdist z 0 ^ 2)) {ε : ℝ} (hε : 0 < ε) {v : Torus d → ℝ}
    (hv : Measurable v) {B : ℝ} (hB : ∀ z, |v z| ≤ B) :
    IntegrableOn (fun z => 𝔨 z * v z) {z | ε < Torus.tdist z 0} := by
  have hS := measurableSet_far (d := d) ε
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  refine Integrable.mono' ((hI.norm.integrableOn (s := {z | ε < Torus.tdist z 0})).const_mul (B / ε ^ 2))
    (hm.mul hv).aestronglyMeasurable ?_
  refine (ae_restrict_iff' hS).2 (Filter.Eventually.of_forall fun z hz => ?_)
  have hz' : ε < Torus.tdist z 0 := hz
  have h1 : ε ^ 2 ≤ Torus.tdist z 0 ^ 2 := pow_le_pow_left₀ hε.le hz'.le 2
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ Torus.tdist z 0 ^ 2)]
  have h2 : 1 ≤ Torus.tdist z 0 ^ 2 / ε ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
  calc |𝔨 z| * |v z| ≤ |𝔨 z| * B := by gcongr; exact hB z
    _ ≤ |𝔨 z| * B * (Torus.tdist z 0 ^ 2 / ε ^ 2) := by
        have : 0 ≤ |𝔨 z| * B := by positivity
        nlinarith
    _ = B / ε ^ 2 * (|𝔨 z| * Torus.tdist z 0 ^ 2) := by ring

theorem setIntegral_neg_symm (S : Set (Torus d)) (hS : MeasurableSet S) (hsym : ∀ z, -z ∈ S ↔ z ∈ S)
    (g : Torus d → ℝ) : ∫ z in S, g (-z) = ∫ z in S, g z := by
  rw [← integral_indicator hS, ← integral_indicator hS]
  have : ∀ z, S.indicator (fun z => g (-z)) z = (S.indicator g) (-z) := by
    intro z
    by_cases h : z ∈ S
    · simp [Set.indicator_of_mem h, Set.indicator_of_mem ((hsym z).2 h)]
    · simp [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hsym z).1 h'))]
  simp_rw [this]
  exact integral_neg_eq_self (S.indicator g) volume

theorem exists_abs_bound {u : Torus d → ℝ} (hu : Continuous u) : ∃ B, ∀ y, |u y| ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hu.continuousOn
  exact ⟨B, fun y => by simpa using hB y (Set.mem_univ y)⟩

theorem pv_tendsto {𝔨 : Torus d → ℝ} (hm : Measurable 𝔨) (he : ∀ z, 𝔨 (-z) = 𝔨 z)
    (hI : Integrable (fun z => 𝔨 z * Torus.tdist z 0 ^ 2)) {u : Torus d → ℝ} (hu : Continuous u) {K : ℝ}
    (hK : ∀ x z, |u x - (u (x + z) + u (x - z)) / 2| ≤ K * Torus.tdist z 0 ^ 2) (x : Torus d) :
    Integrable (fun z => 𝔨 z * (u x - (u (x + z) + u (x - z)) / 2)) ∧
    Tendsto (fun ε : ℝ => ∫ z in {z | ε < Torus.tdist z 0}, 𝔨 z * (u x - u (x - z)))
      (𝓝[>] 0) (𝓝 (∫ z, 𝔨 z * (u x - (u (x + z) + u (x - z)) / 2))) := by
  have hc1 : Continuous fun z : Torus d => u (x + z) := hu.comp (continuous_const.add continuous_id)
  have hc2 : Continuous fun z : Torus d => u (x - z) := hu.comp (continuous_const.sub continuous_id)
  have hma : Measurable fun z : Torus d => u x - (u (x + z) + u (x - z)) / 2 :=
    (measurable_const.sub ((hc1.measurable.add hc2.measurable).div_const 2))
  have hbound : ∀ z, ‖𝔨 z * (u x - (u (x + z) + u (x - z)) / 2)‖ ≤ |K| * ‖𝔨 z * Torus.tdist z 0 ^ 2‖ := by
    intro z
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ Torus.tdist z 0 ^ 2)]
    have := (hK x z).trans (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity))
    calc |𝔨 z| * |u x - (u (x + z) + u (x - z)) / 2| ≤ |𝔨 z| * (|K| * Torus.tdist z 0 ^ 2) := by gcongr
      _ = _ := by ring
  have hint : Integrable (fun z => 𝔨 z * (u x - (u (x + z) + u (x - z)) / 2)) :=
    Integrable.mono' (hI.norm.const_mul |K|) (hm.mul hma).aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  refine ⟨hint, ?_⟩
  obtain ⟨B, hB⟩ := exists_abs_bound hu
  have hv1 : Measurable fun z : Torus d => u x - u (x - z) := measurable_const.sub hc2.measurable
  have hv2 : Measurable fun z : Torus d => u x - u (x + z) := measurable_const.sub hc1.measurable
  have hBv : ∀ y, |u x - u y| ≤ 2 * B := fun y => by
    calc |u x - u y| ≤ |u x| + |u y| := abs_sub _ _
      _ ≤ 2 * B := by linarith [hB x, hB y]
  have key : ∀ ε : ℝ, 0 < ε → ∫ z in {z | ε < Torus.tdist z 0}, 𝔨 z * (u x - u (x - z)) =
      ∫ z in {z | ε < Torus.tdist z 0}, 𝔨 z * (u x - (u (x + z) + u (x - z)) / 2) := by
    intro ε hε
    have hS := measurableSet_far (d := d) ε
    have hsym : ∀ z : Torus d, -z ∈ {z : Torus d | ε < Torus.tdist z 0} ↔ z ∈ {z : Torus d | ε < Torus.tdist z 0} := by
      intro z; simp only [Set.mem_setOf_eq, LocInt.tdist_neg]
    have i1 := integrableOn_far hm hI hε hv1 (fun z => hBv (x - z))
    have i2 := integrableOn_far hm hI hε hv2 (fun z => hBv (x + z))
    have e2 : ∫ z in {z | ε < Torus.tdist z 0}, 𝔨 z * (u x - u (x + z)) =
        ∫ z in {z | ε < Torus.tdist z 0}, 𝔨 z * (u x - u (x - z)) := by
      rw [← setIntegral_neg_symm _ hS hsym (fun z => 𝔨 z * (u x - u (x - z)))]
      refine setIntegral_congr_fun hS fun z _ => ?_
      simp [he z]
    have e3 : ∀ z, 𝔨 z * (u x - (u (x + z) + u (x - z)) / 2) =
        (1 / 2) * (𝔨 z * (u x - u (x - z))) + (1 / 2) * (𝔨 z * (u x - u (x + z))) := fun z => by ring
    simp_rw [e3]
    rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul, e2]
    ring
  -- dominated convergence
  have hlim : Tendsto (fun ε : ℝ => ∫ z in {z | ε < Torus.tdist z 0}, 𝔨 z * (u x - (u (x + z) + u (x - z)) / 2))
      (𝓝[>] 0) (𝓝 (∫ z, 𝔨 z * (u x - (u (x + z) + u (x - z)) / 2))) := by
    simp_rw [← integral_indicator (measurableSet_far _)]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun z => |K| * ‖𝔨 z * Torus.tdist z 0 ^ 2‖) ?_ ?_ (hI.norm.const_mul |K|) ?_
    · refine Filter.Eventually.of_forall fun ε => ?_
      exact ((hm.mul hma).indicator (measurableSet_far ε)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ε => Filter.Eventually.of_forall fun z => ?_
      by_cases hz : ε < Torus.tdist z 0
      · rw [Set.indicator_of_mem (show z ∈ {z : Torus d | ε < Torus.tdist z 0} from hz)]; exact hbound z
      · rw [Set.indicator_of_notMem (show z ∉ {z : Torus d | ε < Torus.tdist z 0} from hz)]
        simp only [norm_zero]; positivity
    · refine Filter.Eventually.of_forall fun z => ?_
      by_cases hz : Torus.tdist z 0 = 0
      · have h0 : 𝔨 z * (u x - (u (x + z) + u (x - z)) / 2) = 0 := by
          have := hK x z
          rw [hz] at this
          have h' : u x - (u (x + z) + u (x - z)) / 2 = 0 := by simpa using this
          rw [h', mul_zero]
        simp only [h0]
        refine tendsto_const_nhds.congr (fun ε => ?_)
        symm
        simp only [Set.indicator]
        split_ifs <;> simp [h0]
      · have hpos : 0 < Torus.tdist z 0 := lt_of_le_of_ne (LocInt.tdist_nonneg z 0) (Ne.symm hz)
        refine tendsto_const_nhds.congr' ?_
        have : Set.Ioo (0 : ℝ) (Torus.tdist z 0) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hpos
        filter_upwards [this] with ε hε
        rw [Set.indicator_of_mem (show z ∈ {z : Torus d | ε < Torus.tdist z 0} from hε.2)]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (key ε hε).symm

/-! ### the operator `K u` and its coefficients -/

/-- `Ku(x) = ∫ 𝔨(z) (u(x) - ½(u(x+z)+u(x-z))) dz` -/
def Kop (𝔨 : Torus d → ℝ) (u : Torus d → ℝ) (x : Torus d) : ℝ :=
  ∫ z, 𝔨 z * (u x - (u (x + z) + u (x - z)) / 2)

theorem continuous_Kop {𝔨 : Torus d → ℝ} (hm : Measurable 𝔨)
    (hI : Integrable (fun z => 𝔨 z * Torus.tdist z 0 ^ 2)) {u : Torus d → ℝ} (hu : Continuous u) {K : ℝ}
    (hK : ∀ x z, |u x - (u (x + z) + u (x - z)) / 2| ≤ K * Torus.tdist z 0 ^ 2) :
    Continuous (Kop 𝔨 u) := by
  unfold Kop
  refine continuous_of_dominated (bound := fun z => |K| * ‖𝔨 z * Torus.tdist z 0 ^ 2‖) (fun x => ?_)
    (fun x => Filter.Eventually.of_forall fun z => ?_) (hI.norm.const_mul |K|)
    (Filter.Eventually.of_forall fun z => ?_)
  · have hc1 : Continuous fun z : Torus d => u (x + z) := hu.comp (continuous_const.add continuous_id)
    have hc2 : Continuous fun z : Torus d => u (x - z) := hu.comp (continuous_const.sub continuous_id)
    exact (hm.mul (measurable_const.sub ((hc1.measurable.add hc2.measurable).div_const 2))).aestronglyMeasurable
  · rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ Torus.tdist z 0 ^ 2)]
    have := (hK x z).trans (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity))
    calc |𝔨 z| * |u x - (u (x + z) + u (x - z)) / 2| ≤ |𝔨 z| * (|K| * Torus.tdist z 0 ^ 2) := by gcongr
      _ = _ := by ring
  · exact continuous_const.mul (hu.sub (((hu.comp (continuous_id.add continuous_const)).add
      (hu.comp (continuous_id.sub continuous_const))).div_const 2))

theorem coeff_Kop {𝔨 : Torus d → ℝ} (hm : Measurable 𝔨)
    (hI : Integrable (fun z => 𝔨 z * Torus.tdist z 0 ^ 2)) {u : Torus d → ℝ} (hu : Continuous u) {K : ℝ}
    (hK : ∀ x z, |u x - (u (x + z) + u (x - z)) / 2| ≤ K * Torus.tdist z 0 ^ 2)
    (𝔪 : Lattice d → ℝ) (hs : ∀ k, ∫ z, 𝔨 z * (1 - Torus.cosMode k z) = 𝔪 k) (k : Lattice d) :
    coeffOf (Kop 𝔨 u) k = ((𝔪 k : ℝ) : ℂ) * coeffOf u k := by
  set F : Torus d → ℂ := fun x => (u x : ℂ) with hF
  have hFc : Continuous F := Complex.continuous_ofReal.comp hu
  let f : Torus d → Torus d → ℂ := fun x z =>
    conj (Torus.mode k x) * ((𝔨 z * (u x - (u (x + z) + u (x - z)) / 2) : ℝ) : ℂ)
  have hfi : Integrable (Function.uncurry f) (volume.prod volume) := by
    have hmeas : Measurable (Function.uncurry f) := by
      have hmk : Measurable fun p : Torus d × Torus d => conj (Torus.mode k p.1) :=
        (Complex.continuous_conj.comp ((Torus.continuous_mode k).comp continuous_fst)).measurable
      have hr : Measurable fun p : Torus d × Torus d => 𝔨 p.2 * (u p.1 - (u (p.1 + p.2) + u (p.1 - p.2)) / 2) :=
        (hm.comp measurable_snd).mul ((hu.measurable.comp measurable_fst).sub
          (((hu.measurable.comp (measurable_fst.add measurable_snd)).add
            (hu.measurable.comp (measurable_fst.sub measurable_snd))).div_const 2))
      exact hmk.mul (Complex.measurable_ofReal.comp hr)
    refine Integrable.mono' ((hI.norm.const_mul |K|).comp_snd (volume : Measure (Torus d)))
      hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, f]
    rw [norm_mul, Complex.norm_conj, Torus.norm_mode, one_mul, Complex.norm_real, norm_mul, norm_mul, Real.norm_eq_abs,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ Torus.tdist p.2 0 ^ 2)]
    have := (hK p.1 p.2).trans (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity))
    calc |𝔨 p.2| * |u p.1 - (u (p.1 + p.2) + u (p.1 - p.2)) / 2| ≤ |𝔨 p.2| * (|K| * Torus.tdist p.2 0 ^ 2) := by gcongr
      _ = _ := by ring
  have hL : coeffOf (Kop 𝔨 u) k = ∫ x, ∫ z, f x z := by
    rw [coeffOf_eq_coeffOfC, coeffOfC_eq_integral']
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [f, Kop]
    rw [integral_const_mul]
    congr 1
    exact (integral_ofReal).symm
  rw [hL, integral_integral_swap hfi]
  have hû : coeffOf u k = ∫ x, conj (Torus.mode k x) * F x := by
    rw [coeffOf_eq_coeffOfC, coeffOfC_eq_integral']
  have hcm : Continuous fun x : Torus d => conj (Torus.mode k x) :=
    Complex.continuous_conj.comp (Torus.continuous_mode k)
  have hT : ∀ h : Torus d, ∫ x, conj (Torus.mode k x) * F (x + h) = Torus.mode k h * coeffOf u k := by
    intro h
    have := ProdAux.coeffOfC_translate F h k
    rw [coeffOfC_eq_integral', coeffOfC_eq_integral'] at this
    rw [coeffOf_eq_coeffOfC, coeffOfC_eq_integral']
    exact this
  have hi0 : Integrable fun x : Torus d => conj (Torus.mode k x) * F x :=
    integrable_of_cont (hcm.mul hFc)
  have hi1 : ∀ h : Torus d, Integrable fun x : Torus d => conj (Torus.mode k x) * F (x + h) := fun h =>
    integrable_of_cont (hcm.mul (hFc.comp (continuous_id.add continuous_const)))
  have hinner : ∀ z : Torus d, ∫ x, f x z = ((𝔨 z * (1 - Torus.cosMode k z) : ℝ) : ℂ) * coeffOf u k := by
    intro z
    have e : ∀ x, f x z = ((𝔨 z : ℝ) : ℂ) * (conj (Torus.mode k x) * F x -
        (1 / 2 : ℂ) * (conj (Torus.mode k x) * F (x + z)) -
        (1 / 2 : ℂ) * (conj (Torus.mode k x) * F (x + -z))) := by
      intro x
      simp only [f, F, ← sub_eq_add_neg]
      push_cast
      ring
    have iB : Integrable fun x : Torus d => (1 / 2 : ℂ) * (conj (Torus.mode k x) * F (x + z)) :=
      (hi1 z).const_mul _
    have iC : Integrable fun x : Torus d => (1 / 2 : ℂ) * (conj (Torus.mode k x) * F (x + -z)) :=
      (hi1 (-z)).const_mul _
    have iA : Integrable fun x : Torus d => conj (Torus.mode k x) * F x -
        (1 / 2 : ℂ) * (conj (Torus.mode k x) * F (x + z)) := hi0.sub iB
    simp_rw [e]
    rw [integral_const_mul, integral_sub iA iC, integral_sub hi0 iB, integral_const_mul,
      integral_const_mul, hT, hT, ← hû, mode_neg_arg]
    push_cast
    rw [cosMode_cplx]
    ring
  simp_rw [hinner]
  rw [integral_mul_const, integral_complex_ofReal, hs k]

/-- the principal value part of the Lévy-kernel representation, for an abstract kernel -/
theorem levy_pv {𝔨 : Torus d → ℝ} (hm : Measurable 𝔨) (he : ∀ z, 𝔨 (-z) = 𝔨 z)
    (hI : Integrable (fun z => 𝔨 z * Torus.tdist z 0 ^ 2))
    (𝔪 : Lattice d → ℝ) (hs : ∀ k, ∫ z, 𝔨 z * (1 - Torus.cosMode k z) = 𝔪 k)
    {L : ℝ} {u : Torus d → ℝ} (hu1 : Torus.IsCk 1 u)
    (hL : LipschitzWith (Real.toNNReal L) (fun x => fderiv ℝ (Torus.lift u) x)) :
    ∃ Ku : Torus d → ℝ, MemLp Ku 2 volume ∧ coeffOf Ku = (fun k => ((𝔪 k : ℝ) : ℂ) * coeffOf u k) ∧
      ∀ x, Tendsto (fun ε : ℝ => ∫ z in {z | ε < Torus.tdist z 0}, 𝔨 z * (u x - u (x - z)))
        (𝓝[>] 0) (𝓝 (Ku x)) := by
  have hu : Continuous u := continuous_of_isCk hu1
  have hK := second_diff_le hu1 hL
  have hc := continuous_Kop hm hI hu hK
  refine ⟨Kop 𝔨 u, hc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _), ?_, fun x => ?_⟩
  · funext k
    exact coeff_Kop hm hI hu hK 𝔪 hs k
  · exact (pv_tendsto hm he hI hu hK x).2

theorem memHs_one_of_lipschitz {L : ℝ} {u : Torus d → ℝ} (hu : Torus.IsLipschitz L u) :
    Summable fun k => Lattice.enorm k ^ 2 * ‖coeffOf u k‖ ^ 2 := by
  obtain ⟨C, -, hC⟩ := ProdAux.frac_bound_one (d := d)
  have hδ : MemHs 1 (deltaCoeff (0 : Lattice d)) := by
    unfold MemHs
    refine summable_of_ne_finset_zero (s := {0}) fun k hk => ?_
    have : k ≠ 0 := by simpa using hk
    simp [deltaCoeff, this]
  obtain ⟨h1, -⟩ := hC u _ _ (ProdAux.prodHyp_of_lipschitz hu) _ hδ
  have e : mulCoeff (coeffOf u) (deltaCoeff (0 : Lattice d)) = coeffOf u := by
    funext k
    unfold mulCoeff
    rw [tsum_eq_single 0]
    · simp [deltaCoeff]
    · intro j hj; simp [deltaCoeff, hj]
  rw [e] at h1
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) h1
  unfold sobWeight
  rw [Real.rpow_one]
  have : 1 ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have h0 : 0 ≤ Lattice.enorm k ^ 2 * ‖coeffOf u k‖ ^ 2 := by positivity
  nlinarith [mul_nonneg (sq_nonneg (Lattice.enorm k)) (sq_nonneg ‖coeffOf u k‖), mul_nonneg (sq_nonneg ‖coeffOf u k‖) (sub_nonneg.2 this)]


end PV

/-! ### (f) The bilinear identity -/

section Bilinear

theorem weight_cos_bound {𝔨 : Torus d → ℝ} (hm : Measurable 𝔨)
    (hI : Integrable (fun z => 𝔨 z * Torus.tdist z 0 ^ 2)) (k : Lattice d) :
    Integrable (fun z => 𝔨 z * (1 - Torus.cosMode k z)) ∧
      ∫ z, ‖𝔨 z * (1 - Torus.cosMode k z)‖ ≤ 2 * Real.pi ^ 2 * Lattice.enorm k ^ 2 * ∫ z, ‖𝔨 z * Torus.tdist z 0 ^ 2‖ := by
  have hw : Measurable (fun z : Torus d => 1 - Torus.cosMode k z) :=
    (measurable_const.sub (Torus.continuous_cosMode k).measurable)
  have hpt : ∀ z : Torus d, ‖𝔨 z * (1 - Torus.cosMode k z)‖ ≤
      (2 * Real.pi ^ 2 * Lattice.enorm k ^ 2) * ‖𝔨 z * Torus.tdist z 0 ^ 2‖ := by
    intro z
    have h1 : 0 ≤ 1 - Torus.cosMode k z := by
      have h2 : Torus.cosMode k z = Real.cos (2 * Real.pi * Lattice.dot k (Torus.centeredRep z)) := by
        conv_lhs => rw [← centeredRep_mk z]
        exact Torus.cosMode_mk _ _
      linarith [Real.cos_le_one (2 * Real.pi * Lattice.dot k (Torus.centeredRep z))]
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg h1, abs_of_nonneg (by positivity : (0:ℝ) ≤ Torus.tdist z 0 ^ 2)]
    calc |𝔨 z| * (1 - Torus.cosMode k z) ≤ |𝔨 z| * (2 * Real.pi ^ 2 * Lattice.enorm k ^ 2 * Torus.tdist z 0 ^ 2) := by
          gcongr; exact one_sub_cosMode_le k z
      _ = _ := by ring
  have hint : Integrable (fun z => 𝔨 z * (1 - Torus.cosMode k z)) :=
    Integrable.mono' (hI.norm.const_mul _) (hm.mul hw).aestronglyMeasurable (Filter.Eventually.of_forall hpt)
  refine ⟨hint, ?_⟩
  calc ∫ z, ‖𝔨 z * (1 - Torus.cosMode k z)‖ ≤ ∫ z, (2 * Real.pi ^ 2 * Lattice.enorm k ^ 2) * ‖𝔨 z * Torus.tdist z 0 ^ 2‖ :=
        integral_mono hint.norm (hI.norm.const_mul _) hpt
    _ = _ := integral_const_mul _ _

theorem norm_mode_neg_sub_one_sq (n : Lattice d) (z : Torus d) :
    ‖Torus.mode n (-z) - 1‖ ^ 2 = 2 * (1 - Torus.cosMode n z) := by
  rw [mode_neg_arg, Torus.mode_neg, Complex.sq_norm, Complex.normSq_apply]
  have h1 : (Torus.mode n z).re * (Torus.mode n z).re + (Torus.mode n z).im * (Torus.mode n z).im = 1 := by
    have h := Torus.norm_mode n z
    have h2 : Complex.normSq (Torus.mode n z) = 1 := by
      rw [Complex.normSq_eq_norm_sq, h]; norm_num
    rwa [Complex.normSq_apply] at h2
  simp only [Complex.sub_re, Complex.conj_re, Complex.one_re, Complex.sub_im, Complex.conj_im, Complex.one_im,
    Torus.cosMode]
  nlinarith

theorem hasSum_diff_pair {u v : Torus d → ℝ} (hu : Continuous u) (hv : Continuous v) (z : Torus d) :
    HasSum (fun n : Lattice d => ((2 * (1 - Torus.cosMode n z) : ℝ) : ℂ) *
        (conj (coeffOf u n) * coeffOf v n))
      ((∫ x, (u x - u (x - z)) * (v x - v (x - z)) : ℝ) : ℂ) := by
  set F : Torus d → ℂ := fun x => (u x : ℂ) with hF
  set G : Torus d → ℂ := fun x => (v x : ℂ) with hG
  have hFc : Continuous F := Complex.continuous_ofReal.comp hu
  have hGc : Continuous G := Complex.continuous_ofReal.comp hv
  have hFm := memLp_two_of_continuous hFc
  have hGm := memLp_two_of_continuous hGc
  set Fz : Torus d → ℂ := fun x => F (x + -z) - F x with hFz
  set Gz : Torus d → ℂ := fun x => G (x + -z) - G x with hGz
  have hFzm : MemLp Fz 2 volume := (ProdAux.memLp_translate hFm (-z)).sub hFm
  have hGzm : MemLp Gz 2 volume := (ProdAux.memLp_translate hGm (-z)).sub hGm
  have hP := hasSum_parseval Fz Gz hFzm hGzm
  have hcF : ∀ n, Torus.funFourierCoeff Fz n = (Torus.mode n (-z) - 1) * coeffOf u n := fun n =>
    ProdAux.coeffOfC_sub_translate hFm (-z) n
  have hcG : ∀ n, Torus.funFourierCoeff Gz n = (Torus.mode n (-z) - 1) * coeffOf v n := fun n =>
    ProdAux.coeffOfC_sub_translate hGm (-z) n
  have hterm : ∀ n : Lattice d, conj (Torus.funFourierCoeff Fz n) * Torus.funFourierCoeff Gz n =
      ((2 * (1 - Torus.cosMode n z) : ℝ) : ℂ) * (conj (coeffOf u n) * coeffOf v n) := by
    intro n
    rw [hcF, hcG, map_mul]
    have h1 : conj (Torus.mode n (-z) - 1) * (Torus.mode n (-z) - 1) = ((2 * (1 - Torus.cosMode n z) : ℝ) : ℂ) := by
      rw [Complex.conj_mul', ← norm_mode_neg_sub_one_sq n z]; push_cast; rfl
    rw [← h1]; ring
  have hval : ∫ t, conj (Fz t) * Gz t = ((∫ x, (u x - u (x - z)) * (v x - v (x - z)) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hFz, hGz, hF, hG, ← sub_eq_add_neg]
    simp [Complex.conj_ofReal]
    ring
  simp_rw [hterm] at hP
  rwa [hval] at hP

theorem lip_diff_le {L : ℝ} {u : Torus d → ℝ} (hu : Torus.IsLipschitz L u) (x z : Torus d) :
    |u x - u (x - z)| ≤ L * Torus.tdist z 0 := by
  have h := hu x (x - z)
  have e : Torus.tdist x (x - z) = Torus.tdist z 0 := by
    unfold Torus.tdist; rw [sub_sub_cancel, sub_zero]
  rwa [e] at h

theorem levy_bilinear {𝔨 : Torus d → ℝ} (hm : Measurable 𝔨)
    (hI : Integrable (fun z => 𝔨 z * Torus.tdist z 0 ^ 2))
    (𝔪 : Lattice d → ℝ) (hs : ∀ k, ∫ z, 𝔨 z * (1 - Torus.cosMode k z) = 𝔪 k)
    {Lu Lv : ℝ} {u v : Torus d → ℝ} (hu : Torus.IsLipschitz Lu u) (hv : Torus.IsLipschitz Lv v) :
    Integrable (fun p : Torus d × Torus d => 𝔨 p.2 * (u p.1 - u (p.1 - p.2)) * (v p.1 - v (p.1 - p.2))) ∧
    (bilinForm 𝔪 (coeffOf u) (coeffOf v)).re =
      (1 / 2) * ∫ p : Torus d × Torus d, 𝔨 p.2 * (u p.1 - u (p.1 - p.2)) * (v p.1 - v (p.1 - p.2)) := by
  have huc := LocInt.continuous_of_isLipschitz hu
  have hvc := LocInt.continuous_of_isLipschitz hv
  have hmeas : Measurable fun p : Torus d × Torus d =>
      𝔨 p.2 * (u p.1 - u (p.1 - p.2)) * (v p.1 - v (p.1 - p.2)) :=
    ((hm.comp measurable_snd).mul ((huc.measurable.comp measurable_fst).sub
      (huc.measurable.comp (measurable_fst.sub measurable_snd)))).mul
      ((hvc.measurable.comp measurable_fst).sub (hvc.measurable.comp (measurable_fst.sub measurable_snd)))
  have hfi : Integrable (fun p : Torus d × Torus d =>
      𝔨 p.2 * (u p.1 - u (p.1 - p.2)) * (v p.1 - v (p.1 - p.2))) := by
    refine Integrable.mono' ((hI.norm.const_mul |Lu * Lv|).comp_snd (volume : Measure (Torus d)))
      hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    have h1 := lip_diff_le hu p.1 p.2
    have h2 := lip_diff_le hv p.1 p.2
    rw [norm_mul, norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ Torus.tdist p.2 0 ^ 2)]
    have h3 : |u p.1 - u (p.1 - p.2)| * |v p.1 - v (p.1 - p.2)| ≤ |Lu * Lv| * Torus.tdist p.2 0 ^ 2 := by
      calc _ ≤ (Lu * Torus.tdist p.2 0) * (Lv * Torus.tdist p.2 0) :=
            mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
        _ = (Lu * Lv) * Torus.tdist p.2 0 ^ 2 := by ring
        _ ≤ |Lu * Lv| * Torus.tdist p.2 0 ^ 2 := by gcongr; exact le_abs_self _
    calc |𝔨 p.2| * |u p.1 - u (p.1 - p.2)| * |v p.1 - v (p.1 - p.2)|
        = |𝔨 p.2| * (|u p.1 - u (p.1 - p.2)| * |v p.1 - v (p.1 - p.2)|) := by ring
      _ ≤ |𝔨 p.2| * (|Lu * Lv| * Torus.tdist p.2 0 ^ 2) := by gcongr
      _ = _ := by ring
  refine ⟨hfi, ?_⟩
  set c' : Lattice d → ℂ := fun n => conj (coeffOf u n) * coeffOf v n with hc'
  set D : Torus d → ℝ := fun z => ∫ x, (u x - u (x - z)) * (v x - v (x - z)) with hD
  set A : ℝ := ∫ z, ‖𝔨 z * Torus.tdist z 0 ^ 2‖ with hA
  have hu1 := memHs_one_of_lipschitz hu
  have hv1 := memHs_one_of_lipschitz hv
  have hsum_c : Summable fun n => Lattice.enorm n ^ 2 * ‖c' n‖ := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((hu1.add hv1).mul_left (1 / 2))
    simp only [hc', norm_mul, Complex.norm_conj]
    nlinarith [sq_nonneg (‖coeffOf u n‖ - ‖coeffOf v n‖), sq_nonneg (Lattice.enorm n),
      mul_nonneg (sq_nonneg (Lattice.enorm n)) (sq_nonneg (‖coeffOf u n‖ - ‖coeffOf v n‖))]
  -- Fubini
  have hfub : ∫ p : Torus d × Torus d, 𝔨 p.2 * (u p.1 - u (p.1 - p.2)) * (v p.1 - v (p.1 - p.2)) =
      ∫ z, 𝔨 z * D z := by
    refine (integral_prod_symm _ hfi).trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hD]
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  let F : Lattice d → Torus d → ℂ := fun n z => ((𝔨 z * (2 * (1 - Torus.cosMode n z)) : ℝ) : ℂ) * c' n
  have hFi : ∀ n, Integrable (F n) := by
    intro n
    have := (weight_cos_bound hm hI n).1.const_mul 2
    have h2 : Integrable (fun z => 𝔨 z * (2 * (1 - Torus.cosMode n z))) :=
      this.congr (Filter.Eventually.of_forall fun z => by dsimp only; ring)
    exact (h2.ofReal).mul_const _
  have hFn : ∀ n, ∫ z, ‖F n z‖ ≤ (4 * Real.pi ^ 2 * A) * (Lattice.enorm n ^ 2 * ‖c' n‖) := by
    intro n
    have e : ∀ z, ‖F n z‖ = (2 * ‖c' n‖) * ‖𝔨 z * (1 - Torus.cosMode n z)‖ := by
      intro z
      simp only [F]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have : 𝔨 z * (2 * (1 - Torus.cosMode n z)) = 2 * (𝔨 z * (1 - Torus.cosMode n z)) := by ring
      rw [this, abs_mul, abs_two, ← Real.norm_eq_abs]; ring
    simp_rw [e]
    rw [integral_const_mul]
    have := (weight_cos_bound hm hI n).2
    calc 2 * ‖c' n‖ * ∫ z, ‖𝔨 z * (1 - Torus.cosMode n z)‖
        ≤ 2 * ‖c' n‖ * (2 * Real.pi ^ 2 * Lattice.enorm n ^ 2 * A) := by gcongr
      _ = _ := by ring
  have hsum : Summable fun n => ∫ z, ‖F n z‖ :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun z => norm_nonneg _) hFn
      (hsum_c.mul_left _)
  have hH := hasSum_integral_of_summable_integral_norm hFi hsum
  have hF_int : ∀ n, ∫ z, F n z = c' n * ((2 * 𝔪 n : ℝ) : ℂ) := by
    intro n
    simp only [F]
    rw [integral_mul_const, integral_complex_ofReal]
    have e : (fun z => 𝔨 z * (2 * (1 - Torus.cosMode n z))) = fun z => 2 * (𝔨 z * (1 - Torus.cosMode n z)) := by
      funext z; ring
    rw [e, integral_const_mul, hs n]; ring
  have hF_tsum : ∀ z, ∑' n, F n z = ((𝔨 z * D z : ℝ) : ℂ) := by
    intro z
    have h := (hasSum_diff_pair huc hvc z).mul_left ((𝔨 z : ℝ) : ℂ)
    have : (fun n => F n z) = fun n => ((𝔨 z : ℝ) : ℂ) * (((2 * (1 - Torus.cosMode n z) : ℝ) : ℂ) *
        (conj (coeffOf u n) * coeffOf v n)) := by
      funext n; simp only [F, hc']; push_cast; ring
    rw [this, h.tsum_eq]
    simp only [hD]; push_cast; ring
  simp_rw [hF_int, hF_tsum, integral_complex_ofReal] at hH
  -- hH : HasSum (fun n => c' n * ↑(2 𝔪 n)) ↑(∫ 𝔨 D)
  have hH2 : HasSum (fun n => conj (((𝔪 n : ℝ) : ℂ) * (coeffOf u n * conj (coeffOf v n))))
      (((1 / 2 * ∫ z, 𝔨 z * D z : ℝ)) : ℂ) := by
    have := hH.mul_right ((1 / 2 : ℝ) : ℂ)
    convert this using 1
    · funext n; simp only [hc']; push_cast; simp [map_mul]; ring
    · push_cast; ring
  have hH3 : HasSum (fun n => ((𝔪 n : ℝ) : ℂ) * (coeffOf u n * conj (coeffOf v n)))
      (((1 / 2 * ∫ z, 𝔨 z * D z : ℝ)) : ℂ) := by
    exact (Complex.hasSum_conj' (f := fun n => ((𝔪 n : ℝ) : ℂ) * (coeffOf u n * conj (coeffOf v n)))
      (x := ((1 / 2 * ∫ z, 𝔨 z * D z : ℝ) : ℂ))).1 (by rw [Complex.conj_ofReal]; exact hH2)
  rw [hfub]
  unfold bilinForm
  rw [hH3.tsum_eq, Complex.ofReal_re]

end Bilinear

end HRS.PDE.LevyAux
