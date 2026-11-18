import HRS.Main.A34Aux26

/-!
# Packet A34, helper 27: uniform bound for the transported field and mode-wise stability
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A34

open HRS HRS.PDE HRS.PDE.ET HRS.A33 HRS.Main

variable {d : ℕ}

/-- norm bound for the transported field from a bound for the functional `ψ ↦ F(U^{0,t}ψ)`. -/
theorem a34_transport_norm_le (S : A33Setup d) {t : ℝ} (ht : t ∈ Set.Icc 0 S.T)
    (F : NegSobolev d (S.J : ℝ)) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ {ψ : Torus d → ℝ}, Torus.IsSmooth ψ →
      |S.ell t F ψ| ≤ ‖F‖ * (K * sobolevNorm (S.J : ℝ) ψ)) :
    ‖a33_transport S t F‖ ≤ ‖F‖ * K := by
  classical
  have hmem := S.transport_memℓp ht F
  set a : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ (-(S.J : ℝ)) *
    NegSobolev.eval F (propagator S.D S.ρ 0 t (Torus.realMode k)) with ha
  have hell : ∀ k, S.ell t F (Torus.realMode k) = Lattice.jp k.1 ^ (S.J : ℝ) * a k := by
    intro k
    have hj := Torus.jp_pos k.1
    simp only [ha, A33Setup.ell]
    rw [← mul_assoc, ← Real.rpow_add hj]
    simp
  have hps : ∀ s : Finset (NonzeroLattice d), ∑ k ∈ s, a k ^ 2 ≤ (‖F‖ * K) ^ 2 := by
    intro s
    set c : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ (-(S.J : ℝ)) * a k with hc
    set A : ℝ := ∑ k ∈ s, a k ^ 2 with hA
    have hA0 : 0 ≤ A := Finset.sum_nonneg fun k _ => sq_nonneg _
    have hpoly : S.ell t F (HRS.FieldSingAux.trigPoly s c) = A := by
      rw [S.ell_trigPoly ht F s c, hA]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hell k, hc]
      have hj := Torus.jp_pos k.1
      simp only
      rw [show Lattice.jp k.1 ^ (-(S.J : ℝ)) * a k * (Lattice.jp k.1 ^ (S.J : ℝ) * a k) =
        (Lattice.jp k.1 ^ (-(S.J : ℝ)) * Lattice.jp k.1 ^ (S.J : ℝ)) * a k ^ 2 by ring,
        ← Real.rpow_add hj]
      simp
    have hsob : sobolevNorm (S.J : ℝ) (HRS.FieldSingAux.trigPoly s c) = Real.sqrt A := by
      unfold sobolevNorm
      rw [HRS.FieldSingAux.mean_trigPoly]
      congr 1
      have : ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * (S.J : ℝ)) *
          Torus.funRealCoeff (HRS.FieldSingAux.trigPoly s c) k ^ 2 = A := by
        simp_rw [HRS.FieldSingAux.funRealCoeff_trigPoly]
        rw [tsum_eq_sum (s := s)]
        · refine Finset.sum_congr rfl fun k hk => ?_
          rw [if_pos hk, hc]
          have hj := Torus.jp_pos k.1
          simp only
          rw [mul_pow, ← Real.rpow_natCast (Lattice.jp k.1 ^ (-(S.J : ℝ))) 2, ← Real.rpow_mul hj.le,
            ← mul_assoc, ← Real.rpow_add hj]
          have : (2 * (S.J : ℝ) + -(S.J : ℝ) * ((2 : ℕ) : ℝ)) = 0 := by push_cast; ring
          rw [this]; simp
        · intro k hk; simp [hk]
      rw [this]; simp
    have hb := hK (HRS.FieldSingAux.isSmooth_trigPoly s c)
    rw [hpoly, hsob] at hb
    have hb' : A ≤ ‖F‖ * K * Real.sqrt A := by
      calc A = |A| := (abs_of_nonneg hA0).symm
        _ ≤ _ := hb
        _ = _ := by ring
    by_cases h0 : A = 0
    · rw [h0]; positivity
    · have hpos : 0 < Real.sqrt A := Real.sqrt_pos.2 (lt_of_le_of_ne hA0 (Ne.symm h0))
      have h1 : Real.sqrt A ≤ ‖F‖ * K := by
        by_contra hcon
        push_neg at hcon
        have := mul_lt_mul_of_pos_right hcon hpos
        have h2 : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt hA0
        nlinarith
      calc A = Real.sqrt A * Real.sqrt A := (Real.mul_self_sqrt hA0).symm
        _ ≤ (‖F‖ * K) * (‖F‖ * K) := mul_self_le_mul_self hpos.le h1
        _ = _ := by ring
  have hsq := NegSobolev.coord_sq (a33_transport S t F)
  have hcd : ∀ k, NegSobolev.coord (a33_transport S t F) k = a k := fun k =>
    NegSobolev.coord_ofSeq_of_mem _ hmem k
  have hsum : Summable fun k => a k ^ 2 := (Torus.memℓp_two_iff _).1 hmem
  have : ‖a33_transport S t F‖ ^ 2 ≤ (‖F‖ * K) ^ 2 := by
    rw [hsq.2]
    simp_rw [hcd]
    exact hsum.tsum_le_of_sum_le hps
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) hK0) two_ne_zero).mp this

/-- uniform bound for the transported field. -/
theorem a34_transport_unif (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (Rg : Regime)
    (MB Λ VB ν₀ T : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (D : DynData d) (ρ : ℝ → Torus d → ℝ),
      AdjointData s (gammaIdx d) Rg MB Λ VB D ν₀ T ρ → ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ F : NegSobolev d (gammaIdx d : ℝ),
        ‖transportField D ρ t (gammaIdx d : ℝ) F‖ ≤ ‖F‖ * K := by
  have hm3 := ClassicalPart.three_le_mStar d
  have hγ : gammaIdx d = mStar d + d + 3 := rfl
  have hJ : mStar d ≤ gammaIdx d := by omega
  have hJ2 : mStar d + d ≤ gammaIdx d := by omega
  obtain ⟨K, K₂, hK0, hK₂0, hu⟩ := a34_unif hd s hs0 hsd (gammaIdx d) hJ Rg MB Λ VB ν₀ T
  refine ⟨max (K (gammaIdx d)) 1, le_trans zero_le_one (le_max_right _ _), ?_⟩
  intro D ρ hA t ht F
  have hA' : AdjointData D.s (gammaIdx d) Rg MB Λ VB D ν₀ T ρ := by rw [hA.hs]; exact hA
  let S : A33Setup d := ⟨gammaIdx d, hJ, hJ2, hd, Rg, MB, Λ, VB, ν₀, D, T, ρ, hA'⟩
  have hT : S.T = T := rfl
  have h1 : 1 ≤ gammaIdx d := by omega
  have key := a34_transport_norm_le S (t := t) ht F (K := max (K (gammaIdx d)) 1)
    (le_trans zero_le_one (le_max_right _ _)) ?_
  · exact key
  · intro ψ hψ
    unfold A33Setup.ell
    rcases ht.1.eq_or_lt with h0 | hpos
    · rw [← h0, S.U_zero hψ]
      refine (a33_abs_eval_le F (a33_ws_of_memSobolev (a33_memSob _ hψ))).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      calc sobolevNorm (S.J : ℝ) ψ = 1 * sobolevNorm (S.J : ℝ) ψ := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)
    · obtain ⟨-, hr⟩ := hu D ρ hA ⟨hpos, ht.2⟩ (a33_cont hψ) (a33_memSob _ hψ)
      obtain ⟨hm, hb⟩ := (hr 0 ⟨le_rfl, hpos.le⟩).1 (gammaIdx d) h1 le_rfl
      refine (a33_abs_eval_le F (a33_ws_of_memSobolev hm)).trans ?_
      refine mul_le_mul_of_nonneg_left (hb.trans ?_) (norm_nonneg _)
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)

/-- mode-wise stability of the transported functional. -/
theorem a34_aco_diff (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (Rg : Regime)
    (MB Λ VB ν₀ T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (D₁ D₂ : DynData d) (ρ₁ ρ₂ : ℝ → Torus d → ℝ),
      AdjointData s (gammaIdx d + 2) Rg MB Λ VB D₁ ν₀ T ρ₁ →
      AdjointData s (gammaIdx d + 2) Rg MB Λ VB D₂ ν₀ T ρ₂ → D₁.M = D₂.M → D₁.V = D₂.V →
      ∀ δ : ℝ, 0 ≤ δ →
      (∀ r ∈ Set.Icc (0 : ℝ) T, Torus.cbNorm (gammaIdx d + 2) (ρ₁ r - ρ₂ r) ≤ δ) →
      |D₁.invβ - D₂.invβ| ≤ δ → ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ F : NegSobolev d (gammaIdx d : ℝ), ∀ k : NonzeroLattice d,
        |NegSobolev.eval F (propagator D₁ ρ₁ 0 t (Torus.realMode k)) -
          NegSobolev.eval F (propagator D₂ ρ₂ 0 t (Torus.realMode k))| ≤
        ‖F‖ * (C * δ * sobolevNorm ((gammaIdx d + 2 : ℕ) : ℝ) (Torus.realMode k)) := by
  have hm3 := ClassicalPart.three_le_mStar d
  have hγ : gammaIdx d = mStar d + d + 3 := rfl
  have hms : mStar d ≤ gammaIdx d + 2 := by omega
  have hm1 : 1 ≤ gammaIdx d := by omega
  obtain ⟨K, K₂, hK0, hK₂0, hu⟩ := a34_unif hd s hs0 hsd (gammaIdx d + 2) hms Rg MB Λ VB ν₀ T
  obtain ⟨C, hC, hst⟩ := a34_stab hd s hs0 hsd (gammaIdx d) hm1 hms Rg MB Λ VB ν₀ T
  refine ⟨2 * C, by positivity, ?_⟩
  intro D₁ D₂ ρ₁ ρ₂ hA₁ hA₂ hM hV δ hδ hδρ hβ t ht F k
  have hφs : Torus.IsSmooth (Torus.realMode k : Torus d → ℝ) := HRS.FieldSingAux.isSmooth_realMode k
  have hφc : Continuous (Torus.realMode k : Torus d → ℝ) := a33_cont hφs
  have hφ : MemSobolev ((gammaIdx d + 2 : ℕ) : ℝ) (Torus.realMode k : Torus d → ℝ) := a33_memSob _ hφs
  have hN0 : 0 ≤ sobolevNorm ((gammaIdx d + 2 : ℕ) : ℝ) (Torus.realMode k : Torus d → ℝ) :=
    Real.sqrt_nonneg _
  have hRHS0 : 0 ≤ ‖F‖ * (2 * C * δ * sobolevNorm ((gammaIdx d + 2 : ℕ) : ℝ)
      (Torus.realMode k : Torus d → ℝ)) := by positivity
  rcases ht.1.eq_or_lt with h0 | hpos
  · rw [← h0, a34_prop_zero hd (gammaIdx d + 2) hms Rg s MB Λ VB ν₀ T D₁ ρ₁ hA₁ hφc hφ,
      a34_prop_zero hd (gammaIdx d + 2) hms Rg s MB Λ VB ν₀ T D₂ ρ₂ hA₂ hφc hφ, sub_self,
      abs_zero]
    exact hRHS0
  · have htI : t ∈ Set.Ioc 0 T := ⟨hpos, ht.2⟩
    have hr0 : (0 : ℝ) ∈ Set.Icc 0 t := ⟨le_rfl, hpos.le⟩
    obtain ⟨-, hc₁, -⟩ := a34_prop_coeff hd s hs0 hsd (gammaIdx d + 2) hms Rg MB Λ VB D₁ ν₀ T ρ₁
      hA₁ htI hφc hφ hr0
    obtain ⟨-, hc₂, -⟩ := a34_prop_coeff hd s hs0 hsd (gammaIdx d + 2) hms Rg MB Λ VB D₂ ν₀ T ρ₂
      hA₂ htI hφc hφ hr0
    obtain ⟨-, hr₁⟩ := hu D₁ ρ₁ hA₁ htI hφc hφ
    obtain ⟨-, hr₂⟩ := hu D₂ ρ₂ hA₂ htI hφc hφ
    obtain ⟨hm₁, -⟩ := (hr₁ 0 hr0).1 (gammaIdx d) hm1 (by omega)
    obtain ⟨hm₂, -⟩ := (hr₂ 0 hr0).1 (gammaIdx d) hm1 (by omega)
    obtain ⟨hmw, hnw⟩ := hst D₁ D₂ ρ₁ ρ₂ hA₁ hA₂ hM hV δ hδρ htI hφc hφ hr0
    have hlin := a33_eval_lin F hc₁ hc₂ (a33_ws_of_memSobolev hm₁) (a33_ws_of_memSobolev hm₂) 1 (-1)
    have e : (fun x => 1 * propagator D₁ ρ₁ 0 t (Torus.realMode k) x +
        (-1) * propagator D₂ ρ₂ 0 t (Torus.realMode k) x) =
        fun x => propagator D₁ ρ₁ 0 t (Torus.realMode k) x -
          propagator D₂ ρ₂ 0 t (Torus.realMode k) x := by
      funext x; ring
    rw [e] at hlin
    have e2 : NegSobolev.eval F (propagator D₁ ρ₁ 0 t (Torus.realMode k)) -
        NegSobolev.eval F (propagator D₂ ρ₂ 0 t (Torus.realMode k)) =
        NegSobolev.eval F (fun x => propagator D₁ ρ₁ 0 t (Torus.realMode k) x -
          propagator D₂ ρ₂ 0 t (Torus.realMode k) x) := by
      rw [hlin]; ring
    rw [e2]
    refine (a33_abs_eval_le F (a33_ws_of_memSobolev hmw)).trans ?_
    refine mul_le_mul_of_nonneg_left (hnw.trans ?_) (norm_nonneg _)
    have : C * (|D₁.invβ - D₂.invβ| + δ) ≤ 2 * C * δ := by nlinarith
    exact mul_le_mul_of_nonneg_right this hN0

end HRS.A34
