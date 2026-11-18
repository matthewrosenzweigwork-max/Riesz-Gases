import HRS.Main.A8Final

/-!
# Packet A9, part 2: bookkeeping from `TorusStanding` at the level `γ`; mode tests `φ_k = ⟨k⟩^{-γ} e_k`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A9

open HRS.GF HRS.Uniform HRS.A33

variable {d : ℕ}

section Standing

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ}

/-- `TorusStanding` is monotone in the level `m`. -/
theorem a9_standing_mono {m m' : ℕ} (hmm : m' ≤ m)
    (h : TorusStanding S R Rg ν₀ MB Λ VB m C₀ Cc 𝔈) : TorusStanding S R Rg ν₀ MB Λ VB m' C₀ Cc 𝔈 where
  flow := h.flow
  regime := h.regime
  mean_field :=
    { solution := h.mean_field.solution
      datum := h.mean_field.datum
      regular := fun N hN => ⟨gfb2_isRegularMF_mono (by omega) (h.mean_field.regular N hN).1,
        (h.mean_field.regular N hN).2⟩
      time_derivative := h.mean_field.time_derivative }
  matrix_bound := h.matrix_bound
  potential := by
    have hle : ((m' + 3 : ℕ) : WithTop ℕ∞) ≤ ((m + 3 : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast (by omega : m' + 3 ≤ m + 3)
    exact ⟨(h.potential.1).of_le hle, (gfb2_cbNorm_mono (by omega) _).trans h.potential.2⟩
  energy := h.energy
  filtered := h.filtered

/-- The coefficient hypothesis at the level `m ≥ m_*`. -/
theorem a9_coeffHyp {m : ℕ} (hm : PDE.mStar d ≤ m)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB m C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N) :
    PDE.CoeffHyp m Λ S.T (S.ρ N) := by
  have hS' := a9_standing_mono hm hS
  refine ⟨fun r hr => (hS.mean_field.solution N hN).density r hr, fun r hr => ?_, fun r hr => ?_, ?_⟩
  · have := ((hS.mean_field.regular N hN).1 r hr).1
    exact_mod_cast this
  · have := ((hS.mean_field.regular N hN).1 r hr).2
    exact_mod_cast this
  · intro ψ hψ
    obtain ⟨Bψ, hBψ⟩ : ∃ B, ∀ x, |ψ x| ≤ B := by
      obtain ⟨B, hB⟩ := (isCompact_range hψ.abs).bddAbove
      exact ⟨B, fun x => hB ⟨x, rfl⟩⟩
    refine continuousOn_of_dominated (bound := fun _ => Bψ * Λ) (fun r hr => ?_) (fun r hr => ?_)
      (integrable_const _) (Eventually.of_forall fun x => ?_)
    · have h1 := ((hS'.mean_field.regular N hN).1 r hr).1
      have h2 : Continuous (S.ρ N r) := Q54c.isCk_continuous h1
      exact (hψ.mul h2).aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      have hρ0 := ((hS.mean_field.solution N hN).density r hr).nonneg x
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hρ0]
      exact mul_le_mul (hBψ x) (A8P.a8p_rho_le hS' hN hr x) hρ0 ((abs_nonneg _).trans (hBψ x))
    · exact continuousOn_const.mul (A8P.a8p_rho_cont_time hS' hN x)

/-- The adjoint data at the level `m ≥ m_*`. -/
theorem a9_adjointData {m : ℕ} (hm : PDE.mStar d ≤ m)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB m C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N) :
    PDE.AdjointData S.s m Rg MB Λ VB (S.dyn N) ν₀ S.T (S.ρ N) where
  hs := rfl
  hM := hS.matrix_bound
  hV := hS.potential
  hμ := a9_coeffHyp hm hS hN
  hT := S.hT
  regime := hS.regime N hN

theorem a9_mStar_le_gamma : PDE.mStar d ≤ gammaIdx d := by unfold gammaIdx; omega

theorem a9_standing_mStar (hS : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈) :
    TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈 :=
  a9_standing_mono a9_mStar_le_gamma hS

end Standing

/-! ### The mode tests -/

/-- `⟨k⟩^{-γ}` for the field level `γ = gammaIdx d`. -/
def a9wt (d : ℕ) (k : NonzeroLattice d) : ℝ := Lattice.jp k.1 ^ (-(gammaIdx d : ℝ))

theorem a9wt_pos (k : NonzeroLattice d) : 0 < a9wt d k :=
  Real.rpow_pos_of_pos (Torus.jp_pos k.1) _

/-- The mode test `φ_k = ⟨k⟩^{-γ} e_k`. -/
def a9phi (d : ℕ) (k : NonzeroLattice d) : Torus d → ℝ := fun x => a9wt d k * Torus.realMode k x

theorem a9phi_smooth (k : NonzeroLattice d) : Torus.IsSmooth (a9phi d k) := by
  have h := HRS.FieldSingAux.isSmooth_realMode k
  unfold Torus.IsSmooth Torus.IsCk at *
  exact contDiff_const.mul h

theorem a9phi_cont (k : NonzeroLattice d) : Continuous (a9phi d k) := a33_cont (a9phi_smooth k)

theorem a9phi_mem (m : ℝ) (k : NonzeroLattice d) : MemSobolev m (a9phi d k) :=
  a33_memSob m (a9phi_smooth k)

theorem a9_sobolevNorm_smul (m c : ℝ) (f : Torus d → ℝ) :
    sobolevNorm m (fun x => c * f x) = |c| * sobolevNorm m f := by
  unfold sobolevNorm
  have h1 : Torus.mean (fun x => c * f x) = c * Torus.mean f := by
    unfold Torus.mean; rw [integral_const_mul]
  have h2 : ∀ k : NonzeroLattice d, Torus.funRealCoeff (fun x => c * f x) k =
      c * Torus.funRealCoeff f k := by
    intro k
    unfold Torus.funRealCoeff
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  have h3 : (Torus.mean (fun x => c * f x)) ^ 2 +
      ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff (fun x => c * f x) k ^ 2 =
      c ^ 2 * ((Torus.mean f) ^ 2 +
        ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff f k ^ 2) := by
    rw [h1, mul_add, ← tsum_mul_left]
    congr 1
    · ring
    · refine tsum_congr fun k => ?_
      rw [h2 k]; ring
  rw [h3, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem a9phi_sobolevNorm (m : ℝ) (k : NonzeroLattice d) :
    sobolevNorm m (a9phi d k) = Lattice.jp k.1 ^ (-(gammaIdx d : ℝ) + m) := by
  unfold a9phi
  rw [a9_sobolevNorm_smul, a33_sobolevNorm_realMode, abs_of_pos (a9wt_pos k), a9wt,
    Real.rpow_add (Torus.jp_pos k.1)]

/-- `γ - m_* = d + 3`. -/
theorem a9_gamma_sub : (gammaIdx d : ℝ) - PDE.mStar d = (d : ℝ) + 3 := by
  unfold gammaIdx; push_cast; ring

theorem a9phi_sobolevNorm_mStar (k : NonzeroLattice d) :
    sobolevNorm (PDE.mStar d : ℝ) (a9phi d k) = Lattice.jp k.1 ^ (-((d : ℝ) + 3)) := by
  rw [a9phi_sobolevNorm]
  congr 1
  have := a9_gamma_sub (d := d)
  linarith

theorem a9_summable_modes : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-((d : ℝ) + 3)) := by
  have h := HRS.summable_jp_rpow (d := d) (((d : ℝ) + 3) / 2) (by linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)])
  refine h.congr fun k => ?_
  congr 1; ring

end HRS.Main.A9
