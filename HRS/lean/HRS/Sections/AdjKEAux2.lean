import HRS.Sections.AdjKEAux1
import HRS.Main.A34Aux11

/-!
# ADJKE part 2: stability of the adjoint propagator in the terminal time

For smooth `φ`, `0 ≤ r ≤ t' ≤ t ≤ T`, `t - t' ≤ 1`:
`‖U^{r,t}φ - U^{r,t'}φ‖_{C²} ≤ K (t - t')`, with `K` depending on `(T, φ)` only.

Route: `U^{r,t}φ = U^{r,t'}(U^{t',t}φ)` (`propagator_semigroup`), additivity (`a34_prop_sub`), the `H^j` contraction-type bound
of `adjoint_torus_classical`, the diagonal Lipschitz bound `adjka_traj_lip` and `H^j ↪ C²`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.AdjK

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem adjke_sobolevNorm_zero (j : ℝ) : sobolevNorm j (fun _ : Torus d => (0 : ℝ)) = 0 := by
  unfold sobolevNorm
  rw [mean_const']
  have : ∀ k : NonzeroLattice d, Torus.funRealCoeff (fun _ : Torus d => (0 : ℝ)) k = 0 := by
    intro k
    unfold Torus.funRealCoeff
    simp
  simp [this]

/-- `C²` smoothness of `U^{r,t}φ` for smooth `φ` and `0 ≤ r ≤ t`. -/
theorem adjke_prop_isCk (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {φ : Torus d → ℝ}
    (hφ : Torus.IsSmooth φ) {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) :
    Torus.IsCk 2 (propagator htr.dyn ρ r t φ) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨ρβ, hth, hsm, hpos, -⟩ := MovLog.movlog_relax2 hd htr
  obtain ⟨hex, -⟩ := Q40b.q40b_adjoint hd htr hth hsm hpos (j := 2 * d + 10) ⟨d + 5, by ring⟩
    (by push_cast; have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith) hφ
  obtain ⟨F, hF, hFp⟩ := hex t (hr.trans hrt)
  rw [hFp r ⟨hr, hrt⟩]
  exact hF.c2 r ⟨hr, hrt⟩

theorem adjke_prop_stab (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (T : ℝ) (hT : 0 < T)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r t' t : ℝ, 0 ≤ r → r ≤ t' → t' ≤ t → t ≤ T → t - t' ≤ 1 →
      Torus.IsCk 2 (fun x => propagator htr.dyn ρ r t φ x - propagator htr.dyn ρ r t' φ x) ∧
      Torus.cbNorm 2 (fun x => propagator htr.dyn ρ r t φ x - propagator htr.dyn ρ r t' φ x) ≤
        K * (t - t') := by
  have hd1 : 1 ≤ d := by omega
  set j : ℕ := d + 2 with hjdef
  have hj : (d : ℝ) + 2 ≤ j := by rw [hjdef]; push_cast; exact le_rfl
  have hdd : (0 : ℝ) < d := by exact_mod_cast hd1
  have hjemb : (d : ℝ) / 2 + (2 : ℕ) < (j : ℝ) := by
    rw [hjdef]; push_cast; linarith
  obtain ⟨Ce, hCe⟩ := cbNorm_le_sobolevNorm (d := d) 2 (j : ℝ) hjemb
  obtain ⟨M, hM0, hM⟩ := adjka_traj_lip hd htr j hj
  obtain ⟨R, Λ, hA⟩ := adjke_adjData hd htr j hj
  have hJm := adjke_mStar_le d j hj
  have hAT := hA T hT
  obtain ⟨C, Cs, hC, hCs, hmain⟩ := adjoint_torus_classical hd1 s htr.hs0 htr.hsd (j + 5) hJm R 1 Λ
    (Torus.cbNorm (j + 5 + 3) V)
  set lam : ℝ := R.lambdaM (Cs j) β⁻¹ (thetaOrder d s) with hlam
  have hj1 : 1 ≤ j := by rw [hjdef]; omega
  have hjJ : j ≤ j + 5 := by omega
  set Nφ : ℝ := sobolevNorm ((j : ℝ) + 2) φ with hNφ
  have hNφ0 : 0 ≤ Nφ := Real.sqrt_nonneg _
  have hDφ : Dom (j + 5) φ := dom_smooth hφ
  refine ⟨|Ce| * (Real.exp (|lam| * T) * (M * Nφ)), by positivity, ?_⟩
  intro r t' t hr hrt' ht't htT htt'
  -- the key `H^j` bound of the difference
  have key : Torus.IsCk 2 (fun x => propagator htr.dyn ρ r t φ x - propagator htr.dyn ρ r t' φ x) ∧
      MemSobolev (j : ℝ) (fun x => propagator htr.dyn ρ r t φ x - propagator htr.dyn ρ r t' φ x) ∧
      sobolevNorm (j : ℝ) (fun x => propagator htr.dyn ρ r t φ x - propagator htr.dyn ρ r t' φ x) ≤
        Real.exp (|lam| * T) * (M * Nφ) * (t - t') := by
    rcases ht't.eq_or_lt with heq | hlt
    · subst heq
      have e : (fun x => propagator htr.dyn ρ r t' φ x - propagator htr.dyn ρ r t' φ x) =
          fun _ : Torus d => (0 : ℝ) := by funext x; ring
      rw [e]
      refine ⟨?_, MFSemigroup.memSobolev_of_isSmooth (isSmooth_const' 0) _, ?_⟩
      · exact MFSemigroup.isCk_nat_of_isSmooth (isSmooth_const' 0) 2
      · rw [adjke_sobolevNorm_zero]; simp
    · have ht0 : 0 < t := lt_of_le_of_lt (hr.trans hrt') hlt
      rcases (hr.trans hrt').eq_or_lt with h0 | hpos
      · -- `t' = 0`, hence `r = 0`
        have hr0 : r = 0 := le_antisymm (hrt'.trans h0.symm.le) hr
        subst hr0
        have ht'0 : t' = 0 := by linarith
        subst ht'0
        have hself : propagator htr.dyn ρ 0 0 φ = φ :=
          prop_self_zero hd1 s htr.hs0 htr.hsd (j + 5) R 1 Λ _ htr.dyn β⁻¹ 1 _ (hA 1 one_pos) hφ
        rw [hself]
        obtain ⟨h1, h2, h3⟩ := hM φ hφ 0 t le_rfl ht0.le (by linarith)
        refine ⟨(adjke_prop_isCk hd htr hφ le_rfl ht0.le).sub
          (MFSemigroup.isCk_nat_of_isSmooth hφ 2), h2, ?_⟩
        refine h3.trans ?_
        have hE : (1 : ℝ) ≤ Real.exp (|lam| * T) := Real.one_le_exp (by positivity)
        have : M * (t - 0) * Nφ ≤ Real.exp (|lam| * T) * (M * Nφ) * (t - 0) := by
          have h4 : 0 ≤ M * Nφ * (t - 0) := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hE h4]
        exact this
      · -- `t' > 0`
        have ht'T : t' ∈ Set.Ioc (0 : ℝ) T := ⟨hpos, hlt.le.trans htT⟩
        have htT' : t ∈ Set.Ioc (0 : ℝ) T := ⟨ht0, htT⟩
        set ψ : Torus d → ℝ := propagator htr.dyn ρ t' t φ with hψ
        have hψd : Continuous ψ ∧ MemSobolev ((j + 5 : ℕ) : ℝ) ψ := by
          have := prop_dom hd1 s htr.hs0 htr.hsd (j + 5) hJm R 1 Λ _ htr.dyn β⁻¹ T ρ hAT htT' hDφ
            ⟨hpos.le, hlt.le⟩
          exact ⟨this.1, this.2⟩
        have hsem : propagator htr.dyn ρ r t φ = propagator htr.dyn ρ r t' ψ :=
          propagator_semigroup hd1 s htr.hs0 htr.hsd (j + 5) hJm R 1 Λ _ htr.dyn β⁻¹ T ρ hAT t htT' φ
            hDφ.1 hDφ.2 r t' hr hrt' hlt
        have hsub := HRS.A34.a34_prop_sub hd1 s htr.hs0 htr.hsd (j + 5) hJm R 1 Λ _ htr.dyn β⁻¹ T ρ
          hAT ht'T hψd.1 hψd.2 hDφ.1 hDφ.2 (r := r) ⟨hr, hrt'⟩
        have hfun : (fun x => propagator htr.dyn ρ r t φ x - propagator htr.dyn ρ r t' φ x) =
            propagator htr.dyn ρ r t' (fun x => ψ x - φ x) := by
          rw [hsub, hsem]
        -- the difference datum
        obtain ⟨hψm, hψdiff, hψn⟩ := hM φ hφ t' t hpos.le hlt.le htt'
        have hgc : Continuous (fun x => ψ x - φ x) := hψd.1.sub hDφ.1
        have hgm : MemSobolev ((j + 5 : ℕ) : ℝ) (fun x => ψ x - φ x) := by
          exact MFLinear.memSobolev_sub hψd.1 hDφ.1 hψd.2 hDφ.2
        obtain ⟨hcls, hpe, h3, -⟩ := hmain htr.dyn β⁻¹ T ρ hAT t' ht'T _ hgc hgm
        obtain ⟨hmem, hbd⟩ := h3 j hj1 hjJ r ⟨hr, hrt'⟩
        rw [hfun]
        have hCk : Torus.IsCk 2 (propagator htr.dyn ρ r t' (fun x => ψ x - φ x)) := by
          rw [hpe r ⟨hr, hrt'⟩]
          exact hcls.c2 r ⟨hr, hrt'⟩
        refine ⟨hCk, hmem, hbd.trans ?_⟩
        have hexp : Real.exp (lam * (t' - r)) ≤ Real.exp (|lam| * T) := by
          refine Real.exp_le_exp.2 ?_
          calc lam * (t' - r) ≤ |lam| * (t' - r) :=
                mul_le_mul_of_nonneg_right (le_abs_self lam) (by linarith)
            _ ≤ |lam| * T := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg lam)
        calc Real.exp (lam * (t' - r)) * sobolevNorm (j : ℝ) (fun x => ψ x - φ x)
            ≤ Real.exp (|lam| * T) * (M * (t - t') * Nφ) :=
              mul_le_mul hexp hψn (Real.sqrt_nonneg _) (Real.exp_pos _).le
          _ = Real.exp (|lam| * T) * (M * Nφ) * (t - t') := by ring
  obtain ⟨hCk, hmem, hn⟩ := key
  refine ⟨hCk, ?_⟩
  calc _ ≤ Ce * sobolevNorm (j : ℝ) _ := hCe _ hmem hCk
    _ ≤ |Ce| * sobolevNorm (j : ℝ) _ :=
        mul_le_mul_of_nonneg_right (le_abs_self Ce) (Real.sqrt_nonneg _)
    _ ≤ |Ce| * (Real.exp (|lam| * T) * (M * Nφ) * (t - t')) :=
        mul_le_mul_of_nonneg_left hn (abs_nonneg Ce)
    _ = |Ce| * (Real.exp (|lam| * T) * (M * Nφ)) * (t - t') := by ring

end HRS.AdjK
