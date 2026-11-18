import HRS.Main.A9Aux24

/-!
# Packet A9, part 25: mode-wise convergence `F(U_N^{0,t} e_k) → F(U_∞^{0,t} e_k)` at the adjoint level `γ`
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Main.A9

open HRS HRS.PDE HRS.A33 HRS.Main HRS.A34

variable {d : ℕ}

theorem a9_mode_conv (S : MainData d) (L : LimitCoeffs d) (Rg : Regime) (ν₀ MB Λ VB : ℝ)
    (hcoef : CoeffConvergence S L Rg ν₀ MB Λ VB (gammaIdx d) (gammaIdx d))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) (F : NegSobolev d (gammaIdx d : ℝ))
    (k : NonzeroLattice d) :
    Tendsto (fun N => NegSobolev.eval F (propagator (S.dyn N) (S.ρ N) 0 t (Torus.realMode k)))
      atTop (𝓝 (NegSobolev.eval F (propagator (L.dyn S) L.ρ 0 t (Torus.realMode k)))) := by
  classical
  have hd := S.hd
  have hs0 := S.hs0
  have hsd := S.hsd
  obtain ⟨K', hK'0, hK'⟩ := a34_transport_unif hd S.s hs0 hsd Rg MB Λ VB ν₀ S.T
  have hm3 := ClassicalPart.three_le_mStar d
  have hγdef : gammaIdx d = mStar d + d + 3 := rfl
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m + 2 = gammaIdx d := ⟨gammaIdx d - 2, by omega⟩
  have hm1 : 1 ≤ m := by omega
  have hms : mStar d ≤ m + 2 := by omega
  obtain ⟨Cst, hCst, hst⟩ := a34_stab hd S.s hs0 hsd m hm1 hms Rg MB Λ VB ν₀ S.T
  set Δ : ℕ → ℝ := fun N => S.coeffDiscrepancy L (gammaIdx d) N with hΔ
  have hΔt : Tendsto Δ atTop (𝓝 0) := hcoef.tendsto
  have hAN : ∀ N, 1 ≤ N → AdjointData S.s (gammaIdx d) Rg MB Λ VB (S.dyn N) ν₀ S.T (S.ρ N) :=
    fun N hN => hcoef.seq_adjoint N hN
  have hAL : AdjointData S.s (gammaIdx d) Rg MB Λ VB (L.dyn S) ν₀ S.T L.ρ := hcoef.limit_adjoint
  have hfacts := fun N (hN : 1 ≤ N) =>
    a9_delta_facts S L (gammaIdx d) N Rg ν₀ MB Λ VB (hAN N hN) hAL
  set ψ : ℕ → Torus d → ℝ := fun N => propagator (S.dyn N) (S.ρ N) 0 t (Torus.realMode k) with hψ
  set ψ0 : Torus d → ℝ := propagator (L.dyn S) L.ρ 0 t (Torus.realMode k) with hψ0
  have hmemN : ∀ N, 1 ≤ N → MemSobolev (gammaIdx d : ℝ) (ψ N) ∧ Continuous (ψ N) := fun N hN =>
    a9_U_mem hd Rg MB Λ VB ν₀ S.T (S.dyn N) (S.ρ N) (hAN N hN) ht k
  have hmem0 := a9_U_mem hd Rg MB Λ VB ν₀ S.T (L.dyn S) L.ρ hAL ht k
  -- the difference at the output level `m`
  have hdiff : ∀ N, 1 ≤ N → MemSobolev (m : ℝ) (fun x => ψ N x - ψ0 x) ∧
      sobolevNorm (m : ℝ) (fun x => ψ N x - ψ0 x) ≤
        Cst * (Δ N + Δ N) * sobolevNorm (gammaIdx d : ℝ) (Torus.realMode k) := by
    intro N hN
    have hs := HRS.FieldSingAux.isSmooth_realMode (d := d) k
    rcases ht.1.eq_or_lt with h0 | hpos
    · -- t = 0
      have hz : ∀ (D : DynData d) (ρ : ℝ → Torus d → ℝ)
          (hA : AdjointData D.s (gammaIdx d) Rg MB Λ VB D ν₀ S.T ρ),
          propagator D ρ 0 t (Torus.realMode k) = Torus.realMode k := by
        intro D ρ hA
        let hSu := a9Setup hd Rg MB Λ VB ν₀ D S.T ρ hA
        have := hSu.U_zero hs
        rw [← h0]
        exact this
      have e : (fun x => ψ N x - ψ0 x) = fun _ => (0 : ℝ) := by
        funext x
        simp only [hψ, hψ0]
        rw [hz (S.dyn N) (S.ρ N) (hAN N hN), hz (L.dyn S) L.ρ hAL]; simp
      rw [e]
      refine ⟨a33_memSob _ (a33_isSmooth_const 0), ?_⟩
      have : sobolevNorm (m : ℝ) (fun _ : Torus d => (0 : ℝ)) = 0 := by
        unfold sobolevNorm
        simp [Torus.mean, Torus.funRealCoeff]
      rw [this]
      have h1 := (hfacts N hN).1
      have h2 : 0 ≤ sobolevNorm (gammaIdx d : ℝ) (Torus.realMode k) := Real.sqrt_nonneg _
      positivity
    · have hAN' : AdjointData S.s (m + 2) Rg MB Λ VB (S.dyn N) ν₀ S.T (S.ρ N) := by
        rw [hm]; exact hAN N hN
      have hAL' : AdjointData S.s (m + 2) Rg MB Λ VB (L.dyn S) ν₀ S.T L.ρ := by
        rw [hm]; exact hAL
      obtain ⟨hmem, hnorm⟩ := hst (S.dyn N) (L.dyn S) (S.ρ N) L.ρ hAN' hAL' rfl rfl (Δ N)
        (fun r hr => (HRS.PDE.cbNorm_mono' (by omega) _).trans ((hfacts N hN).2.1 r hr)) ⟨hpos, ht.2⟩
        (a33_cont hs) (by rw [show ((m + 2 : ℕ) : ℝ) = (gammaIdx d : ℝ) by rw [hm]]; exact a33_memSob _ hs)
        (r := 0) ⟨le_rfl, hpos.le⟩
      refine ⟨hmem, hnorm.trans ?_⟩
      have hb := (hfacts N hN).2.2.1
      rw [show ((m + 2 : ℕ) : ℝ) = (gammaIdx d : ℝ) by rw [hm]]
      have h2 : 0 ≤ sobolevNorm (gammaIdx d : ℝ) (Torus.realMode k) := Real.sqrt_nonneg _
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add hb le_rfl) hCst.le) h2
  -- convergence of the truncated pairings
  have htrunc : ∀ E : Finset (NonzeroLattice d), Tendsto (fun N =>
      NegSobolev.eval (a9trunc E F) (ψ N) - NegSobolev.eval (a9trunc E F) ψ0) atTop (𝓝 0) := by
    intro E
    set A : ℝ := ∑ j ∈ E, |NegSobolev.fourierCoeff F j| with hA
    have hA0 : 0 ≤ A := Finset.sum_nonneg fun j _ => abs_nonneg _
    refine squeeze_zero_norm' (a := fun N => A * (Cst * (Δ N + Δ N) *
      sobolevNorm (gammaIdx d : ℝ) (Torus.realMode k))) ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with N hN
      rw [Real.norm_eq_abs, a9_eval_trunc, a9_eval_trunc, ← Finset.sum_sub_distrib]
      have hcoefs : ∀ j, |Torus.funRealCoeff (ψ N) j - Torus.funRealCoeff ψ0 j| ≤
          Cst * (Δ N + Δ N) * sobolevNorm (gammaIdx d : ℝ) (Torus.realMode k) := by
        intro j
        obtain ⟨hm', hn'⟩ := hdiff N hN
        have e : Torus.funRealCoeff (fun x => ψ N x - ψ0 x) j =
            Torus.funRealCoeff (ψ N) j - Torus.funRealCoeff ψ0 j := by
          have := a33_funRealCoeff_lin (hmemN N hN).2 hmem0.2 1 (-1) j
          simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at this
          exact this
        rw [← e]
        exact (a9_funRealCoeff_le (by positivity) hm' j).trans hn'
      calc |∑ j ∈ E, (NegSobolev.fourierCoeff F j * Torus.funRealCoeff (ψ N) j -
            NegSobolev.fourierCoeff F j * Torus.funRealCoeff ψ0 j)|
          ≤ ∑ j ∈ E, |NegSobolev.fourierCoeff F j * Torus.funRealCoeff (ψ N) j -
            NegSobolev.fourierCoeff F j * Torus.funRealCoeff ψ0 j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ E, |NegSobolev.fourierCoeff F j| * (Cst * (Δ N + Δ N) *
              sobolevNorm (gammaIdx d : ℝ) (Torus.realMode k)) := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [← mul_sub, abs_mul]
            exact mul_le_mul_of_nonneg_left (hcoefs j) (abs_nonneg _)
        _ = A * (Cst * (Δ N + Δ N) * sobolevNorm (gammaIdx d : ℝ) (Torus.realMode k)) := by
            rw [hA, Finset.sum_mul]
    · have := ((hΔt.add hΔt).const_mul Cst).mul_const (sobolevNorm (gammaIdx d : ℝ) (Torus.realMode k))
      have := this.const_mul A
      simpa using this
  -- the density argument
  rw [Metric.tendsto_atTop]
  intro ε hε
  set B : ℝ := Lattice.jp k.1 ^ (gammaIdx d : ℝ) * K' with hB
  have hB0 : 0 ≤ B := mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) hK'0
  obtain ⟨E, hE⟩ := a9_trunc_tail_small F (ε := ε / (8 * (B + 1))) (by positivity)
  have hsplit : ∀ N, 1 ≤ N → |NegSobolev.eval F (ψ N) - NegSobolev.eval F ψ0| ≤
      |NegSobolev.eval (a9trunc E F) (ψ N) - NegSobolev.eval (a9trunc E F) ψ0| +
        2 * (B * ‖F - a9trunc E F‖) := by
    intro N hN
    have e1 : NegSobolev.eval F (ψ N) = NegSobolev.eval (a9trunc E F) (ψ N) +
        NegSobolev.eval (F - a9trunc E F) (ψ N) := by
      rw [a9_eval_sub F (a9trunc E F) (a33_ws_of_memSobolev (hmemN N hN).1)]; ring
    have e2 : NegSobolev.eval F ψ0 = NegSobolev.eval (a9trunc E F) ψ0 +
        NegSobolev.eval (F - a9trunc E F) ψ0 := by
      rw [a9_eval_sub F (a9trunc E F) (a33_ws_of_memSobolev hmem0.1)]; ring
    have b1 := a9_eval_bound hd Rg MB Λ VB ν₀ S.T (S.dyn N) (S.ρ N) (hAN N hN) ht
      (hK' (S.dyn N) (S.ρ N) (hAN N hN) t ht) (F - a9trunc E F) k
    have b2 := a9_eval_bound hd Rg MB Λ VB ν₀ S.T (L.dyn S) L.ρ hAL ht
      (hK' (L.dyn S) L.ρ hAL t ht) (F - a9trunc E F) k
    have hB' : Lattice.jp k.1 ^ (gammaIdx d : ℝ) * (‖F - a9trunc E F‖ * K') = B * ‖F - a9trunc E F‖ := by
      rw [hB]; ring
    rw [hB'] at b1 b2
    rw [e1, e2]
    have h3 : NegSobolev.eval (a9trunc E F) (ψ N) + NegSobolev.eval (F - a9trunc E F) (ψ N) -
        (NegSobolev.eval (a9trunc E F) ψ0 + NegSobolev.eval (F - a9trunc E F) ψ0) =
        (NegSobolev.eval (a9trunc E F) (ψ N) - NegSobolev.eval (a9trunc E F) ψ0) +
        (NegSobolev.eval (F - a9trunc E F) (ψ N) - NegSobolev.eval (F - a9trunc E F) ψ0) := by ring
    rw [h3]
    refine (abs_add_le _ _).trans ?_
    have h4 := abs_sub (NegSobolev.eval (F - a9trunc E F) (ψ N)) (NegSobolev.eval (F - a9trunc E F) ψ0)
    linarith
  have hsmall : 2 * (B * ‖F - a9trunc E F‖) < ε / 2 := by
    have h1 : B * ‖F - a9trunc E F‖ ≤ B * (ε / (8 * (B + 1))) :=
      mul_le_mul_of_nonneg_left hE.le hB0
    have h2 : B * (ε / (8 * (B + 1))) ≤ ε / 8 := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 (htrunc E) (ε / 2) (by positivity)
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have h1 := hN₀ N hN0
  rw [Real.dist_eq, sub_zero] at h1
  rw [Real.dist_eq]
  calc |NegSobolev.eval F (ψ N) - NegSobolev.eval F ψ0|
      ≤ |NegSobolev.eval (a9trunc E F) (ψ N) - NegSobolev.eval (a9trunc E F) ψ0| +
        2 * (B * ‖F - a9trunc E F‖) := hsplit N hN1
    _ < ε / 2 + ε / 2 := add_lt_add h1 hsmall
    _ = ε := by ring

end HRS.Main.A9
