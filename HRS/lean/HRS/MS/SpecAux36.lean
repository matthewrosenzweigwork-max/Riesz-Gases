import HRS.MS.SpecAux33
import HRS.MS.SpecAux34
import HRS.MS.SpecAux35
import HRS.MS.SpecAux28
import HRS.MS.SpecAux26
import HRS.MS.SpecAux29
import HRS.MS.MovLinTie

/-!
# S8P: Schwartz eigenvectors of the S6.2 semigroup in the `A`-inner product (S8.7, packets b2-b4)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_spectral_vectors`: for the thermal data (`Mov2dTh`, `S8pRho`) the S6.2 semigroup
`T = mov2d_T` on `L²_0 = MovL2Zero ρ` has an `A`-orthonormal, `A`-complete sequence `v_n` of eigenvectors; each `v_n` is a Schwartz
function `φ_n` (a.e.) with `S φ_n = ω_n φ_n` a.e., `ω_n ≥ lam > 0` nondecreasing, where `A = s8p_Asub h (MovL2Zero ρ) β⁻¹`.
Route: `s8p_semigroup_eigenbasis` (`T(1)` compact, `A`-symmetric by `s8p_T_symm`), `s8p_eigen_memOsc` + `s8p_schwartz_of_memOsc`
(eigenvectors lie in every `Σ^m`, hence are Schwartz), `s8p_semigroup_pow_eig` (`T(t) v = μ^t v`), and uniqueness of the right
derivative at `0` against the generator of the Schwartz core.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal RealInnerProductSpace

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovLin

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

theorem s8p_K_infinite (hd : 1 ≤ d) (ρ : Euc d → ℝ) : ¬ FiniteDimensional ℝ (MovL2Zero ρ) := by
  intro hfin
  set K : Submodule ℝ (Lp ℝ 2 (volume : Measure (Euc d))) := MovL2Zero ρ with hK
  have hKK : Kᗮ = Submodule.span ℝ {movSqrtLp ρ} := by
    rw [hK]; unfold MovL2Zero
    exact Submodule.orthogonal_orthogonal _
  have hsup : K ⊔ Kᗮ = ⊤ := Submodule.sup_orthogonal_of_hasOrthogonalProjection
  rw [hKK] at hsup
  haveI : FiniteDimensional ℝ K := hfin
  haveI : FiniteDimensional ℝ (K ⊔ Submodule.span ℝ {movSqrtLp ρ} : Submodule ℝ _) := inferInstance
  rw [hsup] at this
  haveI : FiniteDimensional ℝ (Lp ℝ 2 (volume : Measure (Euc d))) :=
    Module.Finite.equiv (Submodule.topEquiv (R := ℝ) (M := Lp ℝ 2 (volume : Measure (Euc d))))
  obtain ⟨b, -⟩ := exists_hermiteHilbertBasisD (d := d)
  obtain ⟨e⟩ := S45.s45_exists_enum hd
  haveI : Infinite (MultiIndex d) := Infinite.of_injective e e.injective
  have hli : LinearIndependent ℝ (fun α : MultiIndex d => (b α : Lp ℝ 2 (volume : Measure (Euc d)))) :=
    b.orthonormal.linearIndependent
  have := hli.finite_of_isNoetherian
  exact not_finite (MultiIndex d)

theorem s8p_isGen_of_pow {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : ℝ → E →L[ℝ] E) {μ : ℝ} (hμ : 0 < μ) {x : E}
    (hpow : ∀ t : ℝ, 0 ≤ t → T t x = (μ ^ t) • x) (hmul : ∀ t : ℝ, 0 ≤ t → ∀ c : ℝ, T t (c • x) = c • T t x) :
    s8p_IsGen T x ((-Real.log μ) • x) := by
  intro t ht
  have h2 : HasDerivWithinAt (fun τ : ℝ => (μ ^ τ) • x) ((μ ^ t * Real.log μ) • x) (Set.Ici t) t :=
    ((Real.hasStrictDerivAt_const_rpow hμ t).hasDerivAt.smul_const x).hasDerivWithinAt
  have e1 : -(T t ((-Real.log μ) • x)) = (μ ^ t * Real.log μ) • x := by
    rw [hmul t ht, hpow t ht, smul_smul, ← neg_smul]
    congr 1
    ring
  rw [e1]
  exact h2.congr (fun τ hτ => hpow τ (ht.trans hτ)) (hpow t ht)

theorem s8p_movA_ge_one (d : ℕ) (s : ℝ) : 1 ≤ movA d s := le_max_left _ _

set_option maxHeartbeats 1600000 in
theorem s8p_spectral_vectors (H : Mov2dTh d s β q ρ) {M : ℝ} (h : S8pRho d s ρ M) :
    ∃ (v : ℕ → MovL2Zero ρ) (φ : ℕ → 𝓢R) (ω : ℕ → ℝ) (lam : ℝ), 0 < lam ∧ (∀ n, lam ≤ ω n) ∧
      Monotone ω ∧
      (∀ n, ∀ᵐ x ∂(volume : Measure (Euc d)), movFun (v n) x = φ n x) ∧
      (∀ n, ∀ᵐ x ∂(volume : Measure (Euc d)), movS d s β ρ (φ n) x = ω n * φ n x) ∧
      (∀ n m, ⟪v n, s8p_Asub h (MovL2Zero ρ) β⁻¹ (v m)⟫ = if n = m then 1 else 0) ∧
      (∀ f : MovL2Zero ρ, (∀ n, ⟪f, s8p_Asub h (MovL2Zero ρ) β⁻¹ (v n)⟫ = 0) → f = 0) := by
  have hd1 : 1 ≤ d := by have := H.hd; omega
  obtain ⟨ψ0, hψ0⟩ := mov2d_sqrt_schwartz H
  have hTs := mov2d_isSemigroup H ψ0 hψ0
  obtain ⟨lam, hlam, C0, hC0, hdec⟩ := movlin_L2_decay H ψ0 hψ0
  have hall : ∀ m : ℝ, movA d s ≤ m → ∃ c C : ℝ, MovSmoothingBounds d s ρ m c C (mov2d_T H ψ0 hψ0) :=
    fun m hm => ⟨lam, _, (movlin_part_T H ψ0 hψ0 lam C0 hlam hC0 hdec hm).choose_spec⟩
  obtain ⟨c1, C1, hb1⟩ := hall (movA d s) le_rfl
  have hcompact := s8p_T1_compact (mov2d_T H ψ0 hψ0) hb1
  have hν : 0 < β⁻¹ := inv_pos.2 H.hβ
  set Dd := s8p_AData h (MovL2Zero ρ) hd1 hν with hDd
  have hsymm : ∀ t, 0 ≤ t → ∀ x y : MovL2Zero ρ,
      ⟪mov2d_T H ψ0 hψ0 t x, Dd.B y⟫ = ⟪x, Dd.B (mov2d_T H ψ0 hψ0 t y)⟫ :=
    fun t ht x y => s8p_T_symm H ψ0 hψ0 h x y ht
  obtain ⟨e, μ, hμpos, hanti, hlim, heig, horth, hcomp⟩ := s8p_semigroup_eigenbasis Dd
    (mov2d_T H ψ0 hψ0) hsymm hTs.zero (fun a b ha hb => hTs.add a b ha hb) hTs.cont hcompact
    (s8p_K_infinite hd1 ρ)
  have hpow : ∀ n, ∀ t : ℝ, 0 ≤ t → mov2d_T H ψ0 hψ0 t (e n) = (μ n ^ t) • e n := fun n t ht =>
    s8p_semigroup_pow_eig (mov2d_T H ψ0 hψ0) Dd.B Dd.c_pos Dd.low hsymm hTs.zero
      (fun a b ha hb => hTs.add a b ha hb) hTs.cont (hμpos n) (heig n) t ht
  have hne : ∀ n, e n ≠ 0 := by
    intro n hn
    have := horth n n
    rw [hn] at this
    simp at this
  have hmu_le : ∀ n, μ n ≤ Real.exp (-lam) := by
    intro n
    by_contra hlt
    push Not at hlt
    have hq : 1 < μ n * Real.exp lam := by
      have := mul_lt_mul_of_pos_right hlt (Real.exp_pos lam)
      rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at this
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C0 hq
    have hnorm : 0 < ‖e n‖ := norm_pos_iff.2 (hne n)
    have h1 := hdec (k : ℝ) (Nat.cast_nonneg k) (e n)
    rw [hpow n k (Nat.cast_nonneg k), norm_smul, Real.norm_eq_abs, Real.rpow_natCast,
      abs_of_nonneg (pow_nonneg (hμpos n).le _)] at h1
    have h2 : μ n ^ k ≤ C0 * Real.exp (-lam * k) := le_of_mul_le_mul_right h1 hnorm
    have h3 : (μ n * Real.exp lam) ^ k = μ n ^ k * Real.exp (lam * k) := by
      rw [mul_pow, ← Real.exp_nat_mul, mul_comm (k : ℝ) lam]
    have h4 : μ n ^ k * Real.exp (lam * k) ≤ C0 := by
      calc μ n ^ k * Real.exp (lam * k) ≤ C0 * Real.exp (-lam * k) * Real.exp (lam * k) :=
            mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
        _ = C0 := by rw [mul_assoc, ← Real.exp_add]; simp
    linarith
  -- Schwartz representatives
  have hmem : ∀ n, ∀ k : ℕ, MemOsc (k : ℝ) (movFun (e n)) := by
    intro n k
    have := s8p_eigen_memOsc (mov2d_T H ψ0 hψ0) hall (hμpos n).ne' (e n) (heig n) k
    exact (HRS.MS.MovOsc.mo_mono (by
      have := s8p_movA_ge_one d s
      nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) this).1
  have hschw : ∀ n, ∃ φ : 𝓢R, movFun (e n) =ᵐ[volume] ⇑φ := fun n =>
    s8p_schwartz_of_memOsc hd1 (hmem n)
  choose φ hφ using hschw
  refine ⟨e, φ, fun n => -Real.log (μ n), lam, hlam, fun n => ?_, fun n m hnm => ?_, hφ, fun n => ?_,
    horth, hcomp⟩
  · have := (Real.log_le_iff_le_exp (hμpos n)).2 (hmu_le n)
    linarith
  · have := Real.log_le_log (hμpos m) (hanti hnm)
    linarith
  · obtain ⟨w, hw, hder⟩ := hTs.generator (φ n) (e n) (hφ n)
    have hgen2 : s8p_IsGen (mov2d_T H ψ0 hψ0) (e n) ((-Real.log (μ n)) • e n) :=
      s8p_isGen_of_pow (mov2d_T H ψ0 hψ0) (hμpos n) (hpow n) (fun t ht c => map_smul _ c _)
    have hw0 : w = (-Real.log (μ n)) • e n := s8p_isGen_unique hTs.zero hder hgen2
    set ωn : ℝ := -Real.log (μ n) with hωn
    have hw' : w = ωn • (e n : MovL2Zero ρ) := hw0
    have hcoe : ∀ᵐ x ∂(volume : Measure (Euc d)), movFun w x = ωn * movFun (e n) x := by
      rw [hw']
      filter_upwards [Lp.coeFn_smul ωn ((e n : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d)))] with x hx
      exact hx
    filter_upwards [hw, hcoe, hφ n] with x h1 h2 h3
    rw [← h1, h2, h3]

end HRS.MS.Spec
