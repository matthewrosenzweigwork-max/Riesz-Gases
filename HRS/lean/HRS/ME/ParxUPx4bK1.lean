import HRS.ME.ParxUKernel2
import HRS.Equilibrium.Parametrix.Packets

/-!
# Packet P3b (part 1): uniform `px4b_Kc_class`

Uniform version (constant chosen before `β, V, ρ`, through the bundle `ParxU`) of
`HRS.Parx.px4b_Kc_class` (Packets:684 region).  The ρ-dependent constants of the old proof were

* `jop_general H` (the nonlocal `Jop` bound): replaced by `jop_engine_unif` (ParxUKernel2), whose
  constant is uniform; `jop_general` has no finished `_unif` wrapper, so its three-line proof is
  reproduced inline from `jop_engine_unif` (the exponent `τ + 2 + s - d` is `≤ τ + 2` by `s < d`);
* `M = ∑ⱼ cbNorm2 (m-1) (∂ⱼρ/ρ)` (from `conormal_mul_smooth`): bounded by `(m-1+1) · Aⱼ`, where
  `Aⱼ` is the uniform bound `ParxU.partial_div_cbNorm_bound` of `cbNorm (m-1) (∂ⱼρ/ρ)`, through the
  general extractor `cbNorm2_fst_le`;
* `|β⁻¹|` (the inverse temperature): bounded by `|νm| + |νp|` via `ParxU.beta_bounds`.

The kernel is called `Nk` here (the name `N` is the derivative level of the bundle).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.ParxU

open HRS.Parx

variable {d : ℕ} {s : ℝ} {N : ℕ} {νm νp c₀ Λ₀ : ℝ}

/-- Extractor (no bundle needed): the two-variable `C^k` norm of `(x, y) ↦ f x` is at most
`(k + 1)` times the one-variable `C^k` norm of `f`. -/
theorem cbNorm2_fst_le {k : ℕ} (f : Torus d → ℝ) (hf : Torus.IsCk (k : WithTop ℕ∞) f) :
    PDE.cbNorm2 k (fun x _ => f x) ≤ ((k : ℝ) + 1) * Torus.cbNorm k f := by
  have hci : ContDiff ℝ (k : WithTop ℕ∞) (Torus.lift f) := hf
  unfold PDE.cbNorm2
  have hterm : ∀ j ∈ Finset.range (k + 1),
      (⨆ p : Euc d × Euc d, ‖iteratedFDeriv ℝ j (PDE.lift2 (fun x _ => f x)) p‖) ≤ Torus.cbNorm k f := by
    intro j hj
    have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
    refine ciSup_le fun p => ?_
    have e : PDE.lift2 (fun x _ => f x) = fun q : Euc d × Euc d => Torus.lift f q.1 := rfl
    rw [e]
    exact (HRS.PDE.MFPair.norm_iter_comp_fst_ps hci hjk p).trans
      (HRS.PDE.MFPair.norm_iter_le_cb_ps hf hjk p.1)
  calc _ ≤ ∑ _j ∈ Finset.range (k + 1), Torus.cbNorm k f := Finset.sum_le_sum hterm
    _ = ((k : ℝ) + 1) * Torus.cbNorm k f := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

set_option maxHeartbeats 1600000 in
/-- **Uniform version of `px4b_Kc_class`.** The constant depends only on `(d, s, N, νm, νp, Λ₀, b', m, τ)`
and on the parameter facts `2 ≤ d`, `0 < s < d`, `τ + 2 < d`, `m ≤ N`; it is chosen before `β, V, ρ`. -/
theorem px4b_Kc_class_unif (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) {τ : ℝ} (hτ : τ + 2 < d)
    (b' m : ℕ) (hm : 2 ≤ m) (hN : m ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ (B' : ℝ) (Nk : Torus d → Torus d → ℝ), 0 ≤ B' → Conormal τ b' m B' Nk →
        ConormalL (τ + 2) (fun _ => b' + 2) (m - 2) (C * B') (px4b_Kc d s β ρ Nk) := by
  obtain ⟨Cj, hCj0, hCj⟩ := jop_engine_unif (d := d) (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hd hs0 hsd hτ b' (m - 2) (by omega)
  obtain ⟨Cm, hCm0, hCm⟩ := conormal_mul_smooth (d := d) (m - 1) (τ + 1) (fun _ => b')
  choose Aj hAj0 hAj using fun j : Fin d => ParxU.partial_div_cbNorm_bound (d := d) (s := s) (N := N)
    (νm := νm) (νp := νp) (c₀ := c₀) (Λ₀ := Λ₀) j (m - 1) (by omega)
  set K1 : ℝ := ((m - 1 : ℕ) : ℝ) + 1 with hK1def
  have hK10 : 0 ≤ K1 := by rw [hK1def]; positivity
  set Bb : ℝ := |νm| + |νp| with hBb
  have hBb0 : 0 ≤ Bb := by rw [hBb]; positivity
  have hQ0 : ∀ j : Fin d, 0 ≤ Cm * (K1 * Aj j) := fun j => mul_nonneg hCm0 (mul_nonneg hK10 (hAj0 j))
  have hMu0 : 0 ≤ ∑ j : Fin d, Cm * (K1 * Aj j) := Finset.sum_nonneg fun j _ => hQ0 j
  refine ⟨Bb * ((d : ℝ) * 4) + Bb * ((∑ j : Fin d, Cm * (K1 * Aj j)) * 2) + Cj,
    add_nonneg (add_nonneg (mul_nonneg hBb0 (by positivity)) (mul_nonneg hBb0 (by linarith))) hCj0,
    fun β V ρ U B' Nk hB' hNk => ?_⟩
  have hNk2 : ConormalL τ (fun _ => b') (m - 2 + 2) B' Nk := by
    rw [show m - 2 + 2 = m by omega]; exact hNk
  have hβb : |β⁻¹| ≤ Bb := by
    obtain ⟨h1, h2, -, -⟩ := U.beta_bounds
    rw [hBb]
    exact abs_le.mpr ⟨by linarith [neg_abs_le νm, abs_nonneg νp], by linarith [le_abs_self νp, abs_nonneg νm]⟩
  have hq : ∀ j : Fin d, Torus.IsCk ((m - 1 : ℕ) : WithTop ℕ∞) (fun u => Torus.partialDeriv j ρ u / ρ u) :=
    fun j => PDE.MFPair.isCk_of_smooth_ps (px4b_q_smooth U.H.rho_smooth j) _
  -- the second-derivative terms
  have hK2 : ∀ i : Fin d, ConormalL (τ + 2) (fun _ => b') (m - 2) (4 * B') (offZero (px4b_K2 i Nk)) := by
    intro i
    have h'' : ConormalL (τ + 2) (fun _ => b') (m - 2) (4 * B') (px4b_K2 i Nk) :=
      ConormalL.mono (px4b_K2_conormal hm hNk i) (by positivity) (by linarith) (fun c => by simp)
        (by omega) (by linarith)
    exact conormalL_congr_offDiag (fun x y hxy => by simp [offZero, hxy]) h''
  have sumK2 := conormal_finset_sum px4b_hAdd (τ + 2) (fun _ => b') (m - 2) Finset.univ
    (fun i => offZero (px4b_K2 i Nk)) (fun _ => 4 * B') (fun i _ => hK2 i)
  have sK2 := ConormalL.smul sumK2 β⁻¹
  -- the first-derivative terms
  have hK1 : ∀ j : Fin d, ConormalL (τ + 1) (fun _ => b') (m - 1) (2 * B') (offZero (px4b_K1 j Nk)) := by
    intro j
    have h'' : ConormalL (τ + 1) (fun _ => b') (m - 1) (2 * B') (px4b_K1 j Nk) :=
      ConormalL.mono (px4b_K1_conormal (by omega) hNk j) (by positivity) le_rfl (fun c => by simp)
        le_rfl le_rfl
    exact conormalL_congr_offDiag (fun x y hxy => by simp [offZero, hxy]) h''
  have hsup : (fun c : ℕ => (Finset.range (c + 1)).sup (fun _ : ℕ => b')) = fun _ => b' :=
    funext fun c => Finset.sup_const (Finset.nonempty_range_iff.2 (Nat.succ_ne_zero c)) _
  have hterm : ∀ j : Fin d, ConormalL (τ + 1) (fun _ => b') (m - 1)
      (Cm * (K1 * Aj j) * (2 * B'))
      (fun x y => (Torus.partialDeriv j ρ x / ρ x) * offZero (px4b_K1 j Nk) x y) := by
    intro j
    have a1 := hCm (2 * B') _ (fun x _ => Torus.partialDeriv j ρ x / ρ x) (hK1 j)
      (px4b_isCk2_fst (hq j))
    rw [hsup] at a1
    have hcb : PDE.cbNorm2 (m - 1) (fun x _ => Torus.partialDeriv j ρ x / ρ x) ≤ K1 * Aj j :=
      (cbNorm2_fst_le _ (hq j)).trans (mul_le_mul_of_nonneg_left (hAj j β V ρ U) hK10)
    have hle : Cm * PDE.cbNorm2 (m - 1) (fun x _ => Torus.partialDeriv j ρ x / ρ x) * (2 * B')
        ≤ Cm * (K1 * Aj j) * (2 * B') :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcb hCm0) (by linarith)
    exact ConormalL.mono a1
      (mul_nonneg (mul_nonneg hCm0 (PDE.MFPair.cbNorm2_nonneg _ _)) (by linarith))
      le_rfl (fun _ => le_rfl) le_rfl hle
  have sumK1 := conormal_finset_sum px4b_hAdd (τ + 1) (fun _ => b') (m - 1) Finset.univ
    (fun j x y => (Torus.partialDeriv j ρ x / ρ x) * offZero (px4b_K1 j Nk) x y)
    (fun j => Cm * (K1 * Aj j) * (2 * B')) (fun j _ => hterm j)
  have sK1 := ConormalL.smul sumK1 β⁻¹
  -- the nonlocal term (`jop_general`, from `jop_engine_unif`)
  have hJ : ConormalL (τ + 2) (fun _ => b' + 2) (m - 2) (Cj * B')
      (offZero fun x y => Jop d s ρ (fun z => Nk z y) x) :=
    ConormalL.mono (hCj β V ρ U B' Nk hB' hNk2) (mul_nonneg hCj0 hB') (by linarith)
      (fun c => by omega) le_rfl le_rfl
  -- bring everything to `(τ + 2, b' + 2, m - 2)`
  have e1 : ConormalL (τ + 2) (fun _ => b' + 2) (m - 2) (|β⁻¹| * ∑ _i : Fin d, 4 * B')
      (fun x y => β⁻¹ * ∑ i : Fin d, offZero (px4b_K2 i Nk) x y) :=
    ConormalL.mono sK2 (by positivity) le_rfl (fun c => by omega) le_rfl le_rfl
  have hQ2 : ∀ j : Fin d, 0 ≤ Cm * (K1 * Aj j) * (2 * B') := fun j => mul_nonneg (hQ0 j) (by linarith)
  have e2 : ConormalL (τ + 2) (fun _ => b' + 2) (m - 2)
      (|β⁻¹| * ∑ j : Fin d, Cm * (K1 * Aj j) * (2 * B'))
      (fun x y => β⁻¹ * ∑ j : Fin d, (Torus.partialDeriv j ρ x / ρ x) * offZero (px4b_K1 j Nk) x y) :=
    ConormalL.mono sK1 (mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun j _ => hQ2 j))
      (by linarith) (fun c => by omega) (by omega) le_rfl
  have e12 := conormalL_add e1 e2
  have e123 := conormalL_add e12 hJ
  have hsum1 : 0 ≤ ∑ _i : Fin d, 4 * B' := Finset.sum_nonneg fun _ _ => by linarith
  have hsum2 : 0 ≤ ∑ j : Fin d, Cm * (K1 * Aj j) * (2 * B') := Finset.sum_nonneg fun j _ => hQ2 j
  have hE0 : 0 ≤ |β⁻¹| * ∑ _i : Fin d, 4 * B' + |β⁻¹| * ∑ j : Fin d, Cm * (K1 * Aj j) * (2 * B')
      + Cj * B' :=
    add_nonneg (add_nonneg (mul_nonneg (abs_nonneg _) hsum1) (mul_nonneg (abs_nonneg _) hsum2))
      (mul_nonneg hCj0 hB')
  refine conormalL_mono_B e123 hE0 ?_
  have hsumK : ∑ _i : Fin d, 4 * B' = (d : ℝ) * (4 * B') := by simp
  have hsumQ : ∑ j : Fin d, Cm * (K1 * Aj j) * (2 * B')
      = (∑ j : Fin d, Cm * (K1 * Aj j)) * (2 * B') := by
    rw [Finset.sum_mul]
  rw [hsumK, hsumQ]
  have hX : 0 ≤ (d : ℝ) * (4 * B') + (∑ j : Fin d, Cm * (K1 * Aj j)) * (2 * B') :=
    add_nonneg (mul_nonneg (by positivity) (by linarith)) (mul_nonneg hMu0 (by linarith))
  calc |β⁻¹| * ((d : ℝ) * (4 * B')) + |β⁻¹| * ((∑ j : Fin d, Cm * (K1 * Aj j)) * (2 * B')) + Cj * B'
      = |β⁻¹| * ((d : ℝ) * (4 * B') + (∑ j : Fin d, Cm * (K1 * Aj j)) * (2 * B')) + Cj * B' := by ring
    _ ≤ Bb * ((d : ℝ) * (4 * B') + (∑ j : Fin d, Cm * (K1 * Aj j)) * (2 * B')) + Cj * B' := by
        have := mul_le_mul_of_nonneg_right hβb hX
        linarith
    _ = (Bb * ((d : ℝ) * 4) + Bb * ((∑ j : Fin d, Cm * (K1 * Aj j)) * 2) + Cj) * B' := by ring

end HRS.ME.ParxU

end
