import HRS.MS.WadAux151

/-!
# S8.3, packet S8G-3: the tensor pairing `Φ(x,y) = (ℓ(x) + m)(ψ_s(ℓ(y)))`

A *section* is a continuous `s : ℝ^d → C_0` with `‖s x'‖ ≤ N₀` and `‖s x'‖ → 0` at infinity (`S8gSec`); `ψ_s λ = (x' ↦ λ(s x'))`
is a bounded operator `C_0^* → C_0` (`s8g_psi`).  For the `C^n` family `ℓ` of `s8g_ell` and a fixed functional `m`, the function
`Φ(x,y) = (ℓ(x) + m)(ψ_s(ℓ(y)))` on `ℝ^d × ℝ^d` is `C^n` with
`‖D^kΦ(x,y)‖ ≤ 2^k (cA + ‖m‖) N₀ cA ⟨x⟩^M⟨y⟩^M` (`c = (d+1)^{n+1}`), `s8g_Phi_contDiff`, `s8g_Phi_bound`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

structure S8gSec (s : Euc d → S8gV d) (N0 : ℝ) : Prop where
  cont : Continuous s
  bdd : ∀ x', ‖s x'‖ ≤ N0
  decay : Tendsto (fun x' => ‖s x'‖) (cocompact (Euc d)) (𝓝 0)

theorem S8gSec.nonneg {s : Euc d → S8gV d} {N0 : ℝ} (hs : S8gSec s N0) : 0 ≤ N0 :=
  (norm_nonneg _).trans (hs.bdd 0)

/-- `ψ_s λ = (x' ↦ λ(s x'))`. -/
def s8g_psi {s : Euc d → S8gV d} {N0 : ℝ} (hs : S8gSec s N0) : (S8gV d →L[ℝ] ℝ) →L[ℝ] S8gV d :=
  LinearMap.mkContinuous
    { toFun := fun (ξ : S8gV d →L[ℝ] ℝ) => s8g_mk (fun x' => ξ (s x')) (ξ.continuous.comp hs.cont) (by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        refine squeeze_zero (fun x' => norm_nonneg _) (fun x' => ξ.le_opNorm (s x'))
          (by simpa using hs.decay.const_mul ‖ξ‖))
      map_add' := fun a b => by exact s8g_ext fun x' => by simp [map_add]; rfl
      map_smul' := fun c a => by exact s8g_ext fun x' => by simp; rfl }
    N0 (fun ξ => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      refine s8g_norm_le (mul_nonneg hs.nonneg (norm_nonneg ξ)) fun x' => ?_
      simp only [s8g_mk_apply]
      calc |ξ (s x')| ≤ ‖ξ‖ * ‖s x'‖ := by simpa using ξ.le_opNorm (s x')
        _ ≤ ‖ξ‖ * N0 := mul_le_mul_of_nonneg_left (hs.bdd x') (norm_nonneg _)
        _ = _ := by ring)

theorem s8g_psi_apply {s : Euc d → S8gV d} {N0 : ℝ} (hs : S8gSec s N0) (ξ : S8gV d →L[ℝ] ℝ) (x' : Euc d) :
    s8g_psi hs ξ x' = ξ (s x') := rfl

theorem s8g_psi_norm {s : Euc d → S8gV d} {N0 : ℝ} (hs : S8gSec s N0) : ‖s8g_psi hs‖ ≤ N0 :=
  ContinuousLinearMap.opNorm_le_bound _ hs.nonneg fun ξ => by
    simp only [s8g_psi, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
    refine s8g_norm_le (mul_nonneg hs.nonneg (norm_nonneg ξ)) fun x' => ?_
    simp only [s8g_mk_apply]
    calc |ξ (s x')| ≤ ‖ξ‖ * ‖s x'‖ := by simpa using ξ.le_opNorm (s x')
      _ ≤ ‖ξ‖ * N0 := mul_le_mul_of_nonneg_left (hs.bdd x') (norm_nonneg _)
      _ = _ := by ring

theorem s8g_iter_fst {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {f : Euc d → W} {n : ℕ}
    (hf : ContDiff ℝ (n : WithTop ℕ∞) f) {k : ℕ} (hk : k ≤ n) (z : Euc d × Euc d) :
    ‖iteratedFDeriv ℝ k (fun z : Euc d × Euc d => f z.1) z‖ ≤ ‖iteratedFDeriv ℝ k f z.1‖ := by
  have e := ContinuousLinearMap.iteratedFDeriv_comp_right (ContinuousLinearMap.fst ℝ (Euc d) (Euc d)) hf z
    (i := k) (by exact_mod_cast hk)
  have e' : iteratedFDeriv ℝ k (fun z : Euc d × Euc d => f z.1) z =
      (iteratedFDeriv ℝ k f z.1).compContinuousLinearMap fun _ => ContinuousLinearMap.fst ℝ (Euc d) (Euc d) := e
  rw [e']
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have : ∏ _i : Fin k, ‖ContinuousLinearMap.fst ℝ (Euc d) (Euc d)‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => ContinuousLinearMap.norm_fst_le _ _ _
  calc _ ≤ ‖iteratedFDeriv ℝ k f z.1‖ * 1 := mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = _ := mul_one _

theorem s8g_iter_snd {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {f : Euc d → W} {n : ℕ}
    (hf : ContDiff ℝ (n : WithTop ℕ∞) f) {k : ℕ} (hk : k ≤ n) (z : Euc d × Euc d) :
    ‖iteratedFDeriv ℝ k (fun z : Euc d × Euc d => f z.2) z‖ ≤ ‖iteratedFDeriv ℝ k f z.2‖ := by
  have e := ContinuousLinearMap.iteratedFDeriv_comp_right (ContinuousLinearMap.snd ℝ (Euc d) (Euc d)) hf z
    (i := k) (by exact_mod_cast hk)
  have e' : iteratedFDeriv ℝ k (fun z : Euc d × Euc d => f z.2) z =
      (iteratedFDeriv ℝ k f z.2).compContinuousLinearMap fun _ => ContinuousLinearMap.snd ℝ (Euc d) (Euc d) := e
  rw [e']
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have : ∏ _i : Fin k, ‖ContinuousLinearMap.snd ℝ (Euc d) (Euc d)‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => ContinuousLinearMap.norm_snd_le _ _ _
  calc _ ≤ ‖iteratedFDeriv ℝ k f z.2‖ * 1 := mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = _ := mul_one _

/-- The pairing function on `ℝ^d × ℝ^d`. -/
def s8g_Phi {M : ℝ} {T : (Euc d → ℝ) → Euc d → ℝ} {J : ℕ} {A : ℝ} (hT : S8gOp M T J A) {s : Euc d → S8gV d}
    {N0 : ℝ} (hs : S8gSec s N0) (m : S8gV d →L[ℝ] ℝ) (z : Euc d × Euc d) : ℝ :=
  (s8g_ell hT z.1 + m) (s8g_psi hs (s8g_ell hT z.2))

theorem s8g_Phi_contDiff {M : ℝ} {T : (Euc d → ℝ) → Euc d → ℝ} {n : ℕ} {A : ℝ} (hT : S8gOp M T (n + 1) A)
    {s : Euc d → S8gV d} {N0 : ℝ} (hs : S8gSec s N0) (m : S8gV d →L[ℝ] ℝ) :
    ContDiff ℝ (n : WithTop ℕ∞) (s8g_Phi hT hs m) := by
  have hl := s8g_ell_contDiff hT
  have h1 : ContDiff ℝ (n : WithTop ℕ∞) (fun z : Euc d × Euc d => s8g_ell hT z.1 + m) :=
    (hl.comp contDiff_fst).add contDiff_const
  have h2 : ContDiff ℝ (n : WithTop ℕ∞) (fun z : Euc d × Euc d => s8g_psi hs (s8g_ell hT z.2)) :=
    (s8g_psi hs).contDiff.comp (hl.comp contDiff_snd)
  exact h1.clm_apply h2

theorem s8g_const_iter (m : S8gV d →L[ℝ] ℝ) (i : ℕ) (z : Euc d × Euc d) :
    ‖iteratedFDeriv ℝ i (fun _ : Euc d × Euc d => m) z‖ ≤ ‖m‖ := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · rw [iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.1 hi)]
    simp [norm_nonneg]

theorem s8g_Phi_bound {M : ℝ} {T : (Euc d → ℝ) → Euc d → ℝ} {n : ℕ} {A : ℝ} (hM : 0 ≤ M) (hT : S8gOp M T (n + 1) A)
    {s : Euc d → S8gV d} {N0 : ℝ} (hs : S8gSec s N0) (m : S8gV d →L[ℝ] ℝ) {k : ℕ} (hk : k ≤ n)
    (z : Euc d × Euc d) :
    ‖iteratedFDeriv ℝ k (s8g_Phi hT hs m) z‖ ≤
      2 ^ k * ((((d : ℝ) + 1) ^ (n + 1) * A + ‖m‖) * N0 * (((d : ℝ) + 1) ^ (n + 1) * A)) *
        (jbracket z.1 ^ M * jbracket z.2 ^ M) := by
  have hl := s8g_ell_contDiff hT
  set c : ℝ := ((d : ℝ) + 1) ^ (n + 1) with hc
  have hc0 : 0 ≤ c := by positivity
  have hA := hT.nonneg
  have hjx := Real.rpow_nonneg (s83_jb_pos z.1).le M
  have hjy := Real.rpow_nonneg (s83_jb_pos z.2).le M
  have hjx1 : 1 ≤ jbracket z.1 ^ M := Real.one_le_rpow (s83_one_le_jb z.1) hM
  have h1 : ContDiff ℝ (n : WithTop ℕ∞) (fun z : Euc d × Euc d => s8g_ell hT z.1 + m) :=
    (hl.comp contDiff_fst).add contDiff_const
  have h2 : ContDiff ℝ (n : WithTop ℕ∞) (fun z : Euc d × Euc d => s8g_psi hs (s8g_ell hT z.2)) :=
    (s8g_psi hs).contDiff.comp (hl.comp contDiff_snd)
  have hmain := norm_iteratedFDeriv_clm_apply h1 h2 z (n := k) (N := (n : WithTop ℕ∞)) (by exact_mod_cast hk)
  have hf : ∀ i ≤ k, ‖iteratedFDeriv ℝ i (fun z : Euc d × Euc d => s8g_ell hT z.1 + m) z‖ ≤
      (c * A + ‖m‖) * jbracket z.1 ^ M := by
    intro i hi
    have e : (fun z : Euc d × Euc d => s8g_ell hT z.1 + m) =
        (fun z : Euc d × Euc d => s8g_ell hT z.1) + (fun _ : Euc d × Euc d => m) := rfl
    have hc1 : ContDiffAt ℝ (i : WithTop ℕ∞) (fun z : Euc d × Euc d => s8g_ell hT z.1) z :=
      ((hl.comp contDiff_fst).of_le (by exact_mod_cast hi.trans hk)).contDiffAt
    have hc2 : ContDiffAt ℝ (i : WithTop ℕ∞) (fun _ : Euc d × Euc d => m) z := contDiffAt_const
    rw [e, iteratedFDeriv_add_apply hc1 hc2]
    refine (norm_add_le _ _).trans ?_
    have a1 := (s8g_iter_fst hl (hi.trans hk) z).trans (s8g_ell_iter_bound hT (hi.trans hk) z.1)
    have a2 := s8g_const_iter m i z
    have a3 : s8g_w d M A (n + 1) z.1 = c * A * jbracket z.1 ^ M := by simp [s8g_w, hc]; ring
    rw [a3] at a1
    calc _ ≤ c * A * jbracket z.1 ^ M + ‖m‖ := add_le_add a1 a2
      _ ≤ c * A * jbracket z.1 ^ M + ‖m‖ * jbracket z.1 ^ M := by
          have := mul_le_mul_of_nonneg_left hjx1 (norm_nonneg m)
          linarith
      _ = _ := by ring
  have hg : ∀ i ≤ k, ‖iteratedFDeriv ℝ i (fun z : Euc d × Euc d => s8g_psi hs (s8g_ell hT z.2)) z‖ ≤
      N0 * (c * A * jbracket z.2 ^ M) := by
    intro i hi
    have hc3 : ContDiffAt ℝ (n : WithTop ℕ∞) (fun z : Euc d × Euc d => s8g_ell hT z.2) z :=
      (hl.comp contDiff_snd).contDiffAt
    have b1 := (s8g_psi hs).norm_iteratedFDeriv_comp_left hc3 (n := i) (by exact_mod_cast hi.trans hk)
    have a1 := (s8g_iter_snd hl (hi.trans hk) z).trans (s8g_ell_iter_bound hT (hi.trans hk) z.2)
    have a3 : s8g_w d M A (n + 1) z.2 = c * A * jbracket z.2 ^ M := by simp [s8g_w, hc]; ring
    rw [a3] at a1
    calc _ ≤ ‖s8g_psi hs‖ * ‖iteratedFDeriv ℝ i (fun z : Euc d × Euc d => s8g_ell hT z.2) z‖ := b1
      _ ≤ N0 * (c * A * jbracket z.2 ^ M) := mul_le_mul (s8g_psi_norm hs) a1 (norm_nonneg _) hs.nonneg
  have hX : 0 ≤ (c * A + ‖m‖) * jbracket z.1 ^ M * (N0 * (c * A * jbracket z.2 ^ M)) := by
    have := hs.nonneg
    positivity
  refine hmain.trans ?_
  calc _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ((c * A + ‖m‖) * jbracket z.1 ^ M * (N0 * (c * A * jbracket z.2 ^ M))) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        exact mul_le_mul (hf i hik) (hg (k - i) (Nat.sub_le _ _)) (norm_nonneg _)
          (mul_nonneg (by positivity) hjx)
    _ = 2 ^ k * ((c * A + ‖m‖) * jbracket z.1 ^ M * (N0 * (c * A * jbracket z.2 ^ M))) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose k
    _ = _ := by ring

end HRS.MS.Wad
