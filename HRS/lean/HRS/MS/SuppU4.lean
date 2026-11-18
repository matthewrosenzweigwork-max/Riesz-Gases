import HRS.Whole.Moving
import HRS.Whole.Oscillator
import HRS.Whole.Basic
import HRS.MS.SuppU4Aux1

/-!
# Worker U4: proof of `HRS.Whole.mov_scope_infinite_dim` (frozen in `HRS/Whole/Moving.lean`)

Route (see the brief): `ρ₀ > 0` everywhere follows from the Gibbs formula and `∫ ρ₀ = 1`, so
`√ρ₀` is smooth.  Bump functions `χ_k` with disjoint supports (centres on the first coordinate axis,
distance at least `1`, radius `1/2`) give `m_k = ∫ χ_k ρ₀ > 0`; the `n` functions
`ψ_i = m_{i+1}⁻¹ χ_{i+1} - m_0⁻¹ χ_0` are smooth with compact support, have `∫ ψ_i ρ₀ = 0`, and are
linearly independent (evaluate at the centres).  Smallness: for `|c_i| ≤ δ` the `C_b^{j+1}` norm and the
`Σ^m` norm of `√ρ₀ ∑ c_i ψ_i` are bounded by `∑ |c_i| (‖ψ_i‖_{C_b} + ‖√ρ₀ ψ_i‖_{Σ^m})`, which is at most
`δ K`, and `δ = εstar / (K+1)` makes this at most `εstar`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d : ℕ}

/-- Centre of the `k`-th bump: `k` times a unit vector on the first coordinate axis. -/
def u4Center (hd : 0 < d) (k : ℕ) : Euc d :=
  (k : ℝ) • EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ)

/-- The `k`-th bump: radius `1/4` inside, `1/2` outside. -/
def u4Bump (hd : 0 < d) (k : ℕ) : ContDiffBump (u4Center hd k) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

lemma u4_dist_centers (hd : 0 < d) {k l : ℕ} (hkl : k ≠ l) :
    1 ≤ dist (u4Center hd k) (u4Center hd l) := by
  have hdist : dist (u4Center hd k) (u4Center hd l) = |(k : ℝ) - l| := by
    simp only [dist_eq_norm, u4Center]
    rw [← sub_smul, norm_smul, EuclideanSpace.norm_single]
    simp
  rw [hdist]
  rcases lt_or_gt_of_ne hkl with h | h
  · have h1 : k + 1 ≤ l := h
    have h' : (k : ℝ) + 1 ≤ l := by exact_mod_cast h1
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have h1 : l + 1 ≤ k := h
    have h' : (l : ℝ) + 1 ≤ k := by exact_mod_cast h1
    rw [abs_of_nonneg (by linarith)]
    linarith

lemma u4_bump_center (hd : 0 < d) (k : ℕ) : u4Bump hd k (u4Center hd k) = 1 :=
  (u4Bump hd k).one_of_mem_closedBall (Metric.mem_closedBall_self (u4Bump hd k).rIn_pos.le)

lemma u4_bump_zero (hd : 0 < d) {k l : ℕ} (hkl : k ≠ l) : u4Bump hd k (u4Center hd l) = 0 := by
  apply (u4Bump hd k).zero_of_le_dist
  have h1 := u4_dist_centers hd hkl
  have h2 : (u4Bump hd k).rOut = 1 / 2 := rfl
  rw [dist_comm, h2]
  linarith

lemma u4_bump_cs (hd : 0 < d) (k : ℕ) : U4CS (u4Bump hd k) :=
  ⟨(u4Bump hd k).contDiff, (u4Bump hd k).hasCompactSupport⟩

lemma u4_int {g : Euc d → ℝ} (hg : U4CS g) {ρ : Euc d → ℝ} (hρc : Continuous ρ) :
    Integrable (fun x => g x * ρ x) := by
  refine (hg.1.continuous.mul hρc).integrable_of_hasCompactSupport ?_
  have h : HasCompactSupport (g * ρ) := hg.2.mul_right
  exact h

/-- `m_k = ∫ χ_k ρ₀`. -/
def u4M (hd : 0 < d) (ρ : Euc d → ℝ) (k : ℕ) : ℝ := ∫ x, u4Bump hd k x * ρ x

lemma u4_m_pos (hd : 0 < d) {ρ : Euc d → ℝ} (hρc : Continuous ρ) (hρp : ∀ x, 0 < ρ x) (k : ℕ) :
    0 < u4M hd ρ k := by
  unfold u4M
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := u4Center hd k) ?_ ?_ ?_ ?_
  · exact (u4Bump hd k).continuous.mul hρc
  · exact (u4_bump_cs hd k).2.mul_right
  · exact fun x => mul_nonneg (u4Bump hd k).nonneg (hρp x).le
  · show u4Bump hd k (u4Center hd k) * ρ (u4Center hd k) ≠ 0
    rw [u4_bump_center, one_mul]
    exact (hρp _).ne'

/-- `ψ_i = m_{i+1}⁻¹ χ_{i+1} - m_0⁻¹ χ_0`. -/
def u4Psi (hd : 0 < d) (ρ : Euc d → ℝ) (i : ℕ) (x : Euc d) : ℝ :=
  (u4M hd ρ (i + 1))⁻¹ * u4Bump hd (i + 1) x + (-(u4M hd ρ 0)⁻¹) * u4Bump hd 0 x

lemma u4Psi_cs (hd : 0 < d) (ρ : Euc d → ℝ) (i : ℕ) : U4CS (u4Psi hd ρ i) :=
  u4_cs_add (u4_cs_const_mul _ (u4_bump_cs hd (i + 1))) (u4_cs_const_mul _ (u4_bump_cs hd 0))

lemma u4Psi_mean (hd : 0 < d) {ρ : Euc d → ℝ} (hρc : Continuous ρ) (hρp : ∀ x, 0 < ρ x) (i : ℕ) :
    ∫ x, u4Psi hd ρ i x * ρ x = 0 := by
  have hfun : (fun x => u4Psi hd ρ i x * ρ x) = fun x =>
      (u4M hd ρ (i + 1))⁻¹ * (u4Bump hd (i + 1) x * ρ x) +
        (-(u4M hd ρ 0)⁻¹) * (u4Bump hd 0 x * ρ x) := by
    funext x
    unfold u4Psi
    ring
  rw [hfun, integral_add ((u4_int (u4_bump_cs hd (i + 1)) hρc).const_mul _)
    ((u4_int (u4_bump_cs hd 0) hρc).const_mul _), integral_const_mul, integral_const_mul]
  have h1 : ∫ x, u4Bump hd (i + 1) x * ρ x = u4M hd ρ (i + 1) := rfl
  have h0 : ∫ x, u4Bump hd 0 x * ρ x = u4M hd ρ 0 := rfl
  rw [h1, h0]
  have hm1 : u4M hd ρ (i + 1) ≠ 0 := (u4_m_pos hd hρc hρp _).ne'
  have hm0 : u4M hd ρ 0 ≠ 0 := (u4_m_pos hd hρc hρp _).ne'
  linear_combination (inv_mul_cancel₀ hm1) - (inv_mul_cancel₀ hm0)

lemma u4Psi_eval (hd : 0 < d) (ρ : Euc d → ℝ) (i j : ℕ) :
    u4Psi hd ρ i (u4Center hd (j + 1)) = if i = j then (u4M hd ρ (j + 1))⁻¹ else 0 := by
  unfold u4Psi
  rw [u4_bump_zero hd (show (0 : ℕ) ≠ j + 1 by omega)]
  by_cases hij : i = j
  · subst hij
    rw [u4_bump_center]
    simp
  · rw [u4_bump_zero hd (show i + 1 ≠ j + 1 by omega)]
    simp [hij]

lemma u4_lin_indep (hd : 0 < d) {ρ : Euc d → ℝ} (hρc : Continuous ρ) (hρp : ∀ x, 0 < ρ x)
    (n : ℕ) : LinearIndependent ℝ (fun i : Fin n => u4Psi hd ρ (i : ℕ)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i0
  have hsum := congrFun hg (u4Center hd ((i0 : ℕ) + 1))
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hsum
  have hval : ∀ i : Fin n, g i * u4Psi hd ρ (i : ℕ) (u4Center hd ((i0 : ℕ) + 1)) =
      if i = i0 then g i * (u4M hd ρ ((i0 : ℕ) + 1))⁻¹ else 0 := by
    intro i
    rw [u4Psi_eval]
    by_cases h : i = i0
    · subst h
      simp
    · have h' : (i : ℕ) ≠ (i0 : ℕ) := fun e => h (Fin.ext e)
      simp [h, h']
  rw [Finset.sum_congr rfl (fun i _ => hval i), Finset.sum_eq_single i0] at hsum
  · rw [if_pos rfl] at hsum
    exact (mul_eq_zero.1 hsum).resolve_right (inv_ne_zero (u4_m_pos hd hρc hρp _).ne')
  · intro b _ hb
    exact if_neg hb
  · intro h
    exact absurd (Finset.mem_univ i0) h

lemma u4_thermal_pos {s q β : ℝ} {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρ) (x : Euc d) :
    0 < ρ x := by
  obtain ⟨_, hthd⟩ := hρ
  obtain ⟨hprob, hden⟩ := hthd
  have hint : ∫ y, ρ y = 1 := hprob.integral_one
  have hZ0 : 0 ≤ ∫ y, Real.exp (-β * (confinement q y +
      convMeasure (rieszKernel d s) (withDensityReal ρ) y)) :=
    integral_nonneg fun y => (Real.exp_pos _).le
  have hZ : 0 < ∫ y, Real.exp (-β * (confinement q y +
      convMeasure (rieszKernel d s) (withDensityReal ρ) y)) := by
    rcases hZ0.lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 : ∀ y, ρ y = 0 := fun y => by rw [hden y, ← h, div_zero]
      simp [h0] at hint
  rw [hden x]
  exact div_pos (Real.exp_pos _) hZ

/-- The smallness and the initial-class membership for the family `∑ c_i ψ_i`. -/
lemma u4_small (j m : ℕ) {ρ : Euc d → ℝ} (hρc : Continuous ρ)
    (hsq : ContDiff ℝ ∞ (fun x => Real.sqrt (ρ x))) (εstar : ℝ) (hε : 0 < εstar) {n : ℕ}
    (ψ : Fin n → Euc d → ℝ) (hψ : ∀ i, U4CS (ψ i)) (hint : ∀ i, ∫ x, ψ i x * ρ x = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c : Fin n → ℝ, (∀ i, |c i| ≤ δ) →
      MovInitialClass ρ j m εstar (fun x => ∑ i, c i * ψ i x) := by
  have hP1_0 : cbNorm (j + 1) (fun _ : Euc d => (0 : ℝ)) ≤ 0 := (u4_cbNorm_zero _).le
  have hP1_add : ∀ f g : Euc d → ℝ, U4CS f → U4CS g →
      cbNorm (j + 1) (fun x => f x + g x) ≤ cbNorm (j + 1) f + cbNorm (j + 1) g :=
    fun f g hf hg => u4_cbNorm_add_le (j + 1) hf hg
  have hP1_mul : ∀ (a : ℝ) (f : Euc d → ℝ), U4CS f →
      cbNorm (j + 1) (fun x => a * f x) = |a| * cbNorm (j + 1) f :=
    fun a f hf => cbNorm_const_mul (j + 1) a f hf.1
  have hP2_0 : oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * (0 : ℝ)) ≤ 0 := by
    have e : (fun x => Real.sqrt (ρ x) * (0 : ℝ)) = fun _ : Euc d => (0 : ℝ) := by
      funext x
      ring
    rw [e, u4_oscNorm_zero]
  have hP2_add : ∀ f g : Euc d → ℝ, U4CS f → U4CS g →
      oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * (f x + g x)) ≤
        oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * f x) +
          oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * g x) := by
    intro f g hf hg
    have e : (fun x => Real.sqrt (ρ x) * (f x + g x)) =
        fun x => Real.sqrt (ρ x) * f x + Real.sqrt (ρ x) * g x := by
      funext x
      ring
    rw [e]
    exact u4_oscNorm_add_le (m : ℝ) (u4_cs_mul hsq hf) (u4_cs_mul hsq hg)
  have hP2_mul : ∀ (a : ℝ) (f : Euc d → ℝ), U4CS f →
      oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * (a * f x)) =
        |a| * oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * f x) := by
    intro a f _
    have e : (fun x => Real.sqrt (ρ x) * (a * f x)) = fun x => a * (Real.sqrt (ρ x) * f x) := by
      funext x
      ring
    rw [e, oscNorm_const_mul]
  -- the constant `K = ∑ (‖ψ_i‖_{C_b} + ‖√ρ ψ_i‖_{Σ^m})`
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ∑ i, (cbNorm (j + 1) (ψ i) +
      oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * ψ i x)) := ⟨_, rfl⟩
  have hnn : ∀ i, 0 ≤ cbNorm (j + 1) (ψ i) +
      oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * ψ i x) :=
    fun i => add_nonneg (u4_cbNorm_nonneg _ _) (u4_oscNorm_nonneg _ _)
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact Finset.sum_nonneg fun i _ => hnn i
  have hK1 : (0 : ℝ) < K + 1 := by linarith
  have hδ : 0 < εstar / (K + 1) := div_pos hε hK1
  refine ⟨εstar / (K + 1), hδ, fun c hc => ?_⟩
  obtain ⟨hcs, hle1⟩ := u4_sum_bound (fun f => cbNorm (j + 1) f) hP1_0 hP1_add hP1_mul c ψ hψ
    Finset.univ
  obtain ⟨-, hle2⟩ := u4_sum_bound (fun f => oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * f x))
    hP2_0 hP2_add hP2_mul c ψ hψ Finset.univ
  dsimp only at hle1 hle2
  have hsplit : ∑ i, |c i| * (cbNorm (j + 1) (ψ i) +
      oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * ψ i x)) =
      ∑ i, |c i| * cbNorm (j + 1) (ψ i) +
        ∑ i, |c i| * oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * ψ i x) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => mul_add _ _ _
  have hdelta : ∑ i, |c i| * (cbNorm (j + 1) (ψ i) +
      oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * ψ i x)) ≤
      ∑ i, εstar / (K + 1) * (cbNorm (j + 1) (ψ i) +
        oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * ψ i x)) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hc i) (hnn i)
  have hsumK : ∑ i, εstar / (K + 1) * (cbNorm (j + 1) (ψ i) +
      oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * ψ i x)) = εstar / (K + 1) * K := by
    rw [hK, Finset.mul_sum]
  have hfin : εstar / (K + 1) * K ≤ εstar := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hK1]
    nlinarith
  have hsmall : cbNorm (j + 1) (fun x => ∑ i, c i * ψ i x) +
      oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * ∑ i, c i * ψ i x) ≤ εstar := by
    calc cbNorm (j + 1) (fun x => ∑ i, c i * ψ i x) +
          oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * ∑ i, c i * ψ i x)
        ≤ ∑ i, |c i| * cbNorm (j + 1) (ψ i) +
            ∑ i, |c i| * oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * ψ i x) :=
          add_le_add hle1 hle2
      _ = ∑ i, |c i| * (cbNorm (j + 1) (ψ i) +
            oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * ψ i x)) := hsplit.symm
      _ ≤ _ := hdelta
      _ = εstar / (K + 1) * K := hsumK
      _ ≤ εstar := hfin
  have hcs' : U4CS (fun x => ∑ i, c i * ψ i x) := by
    have := hcs
    exact this
  refine ⟨u4_memCb (j + 1) hcs', u4_memOsc (m : ℝ) (u4_cs_mul hsq hcs'), ?_, ?_⟩
  · show ∫ x, (∑ i, c i * ψ i x) * ρ x = 0
    have e : ∀ x, (∑ i, c i * ψ i x) * ρ x = ∑ i, c i * (ψ i x * ρ x) := by
      intro x
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _
    simp_rw [e]
    rw [integral_finsetSum]
    · have hmean : ∑ i, ∫ x, c i * (ψ i x * ρ x) = ∑ i, c i * ∫ x, ψ i x * ρ x :=
        Finset.sum_congr rfl fun i _ => integral_const_mul _ _
      rw [hmean]
      simp [hint]
    · intro i _
      exact (u4_int (hψ i) hρc).const_mul (c i)
  · exact hsmall

/-- The linearly independent family and the smallness statement (`n` bumps). -/
lemma u4_main (hd : 0 < d) (j m : ℕ) {ρ : Euc d → ℝ} (hρc : Continuous ρ) (hρp : ∀ x, 0 < ρ x)
    (hsq : ContDiff ℝ ∞ (fun x => Real.sqrt (ρ x))) (εstar : ℝ) (hε : 0 < εstar) (n : ℕ) :
    ∃ ψ : Fin n → Euc d → ℝ, LinearIndependent ℝ ψ ∧
      (∀ i, ContDiff ℝ ∞ (ψ i) ∧ HasCompactSupport (ψ i) ∧ ∫ x, ψ i x * ρ x = 0) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ c : Fin n → ℝ, (∀ i, |c i| ≤ δ) →
        MovInitialClass ρ j m εstar (fun x => ∑ i, c i * ψ i x) := by
  have hψcs : ∀ i : Fin n, U4CS (u4Psi hd ρ (i : ℕ)) := fun i => u4Psi_cs hd ρ (i : ℕ)
  have hint : ∀ i : Fin n, ∫ x, u4Psi hd ρ (i : ℕ) x * ρ x = 0 :=
    fun i => u4Psi_mean hd hρc hρp (i : ℕ)
  obtain ⟨δ, hδ, hsmall⟩ := u4_small j m hρc hsq εstar hε (fun i : Fin n => u4Psi hd ρ (i : ℕ))
    hψcs hint
  exact ⟨fun i : Fin n => u4Psi hd ρ (i : ℕ), u4_lin_indep hd hρc hρp n,
    fun i => ⟨(hψcs i).1, (hψcs i).2, hint i⟩, δ, hδ, hsmall⟩

end HRS.Whole

/-- Worker U4: the frozen statement `HRS.Whole.mov_scope_infinite_dim` (repair P11 form). -/
theorem mov_scope_infinite_dim_proof : type_of% @HRS.Whole.mov_scope_infinite_dim := by
  intro d s hd hs0 hsd β q hβ hq j m hj hm ρ₀ hρ hρsm εstar hε n
  have hd0 : 0 < d := by omega
  have hpos : ∀ x, 0 < ρ₀ x := fun x => HRS.Whole.u4_thermal_pos hρ x
  have hsq : ContDiff ℝ ∞ (fun x => Real.sqrt (ρ₀ x)) :=
    hρsm.sqrt (fun x => (hpos x).ne')
  exact HRS.Whole.u4_main hd0 j m hρsm.continuous hpos hsq εstar hε n
