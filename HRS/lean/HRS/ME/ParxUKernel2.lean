import HRS.ME.ParxUKernel1
import HRS.Equilibrium.Parametrix.PX4aAuxU

/-!
# Packet P1b (part 2): uniform `jop_engine`

Uniform version (constant chosen before `β, V, ρ`, through the bundle `ParxU`) of
`HRS.Parx.jop_engine` (PX4aAuxU:35). The ρ-dependent constants of the original proof were the
constants `C i` of `psii_conormal` and `K` of `snsrc_srcCls`; they are replaced by their uniform
versions `psii_conormal_unif` and `snsrc_srcCls_unif`. The remaining constants (`kpot_chart_conormal`,
`kPot_Lam_bounds`, `fsrc_smooth`, `conormal_of_ck2`, `locKer_riesz`) do not depend on `ρ`.
The smoothness of `ρ` (only used in the qualitative identity `jop_formula`) comes from the bundle.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.ParxU

open HRS.Parx

variable {d : ℕ} {s : ℝ} {N : ℕ} {νm νp c₀ Λ₀ : ℝ}

set_option maxHeartbeats 3200000 in
/-- **Uniform version of `jop_engine`.** The constant depends only on `(d, s, N, Λ₀, b, m')`
and the parameter facts `2 ≤ d`, `0 < s < d`, `τ + 2 < d`, `m' + 2 ≤ N`; it is chosen before
`β, V, ρ`. -/
theorem jop_engine_unif (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) {τ : ℝ} (hτ : τ + 2 < d)
    (b m' : ℕ) (hN : m' + 2 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ (B : ℝ) (Ψ : Torus d → Torus d → ℝ), 0 ≤ B →
      ConormalL τ (fun _ => b) (m' + 2) B Ψ →
      ConormalL (τ + 2 + s - d) (fun _ => b + 1) m' (C * B)
        (offZero fun x y => Jop d s ρ (fun z => Ψ z y) x) := by
  classical
  have hm : 1 ≤ m' + 2 := by omega
  obtain ⟨K, hK0, hK⟩ := snsrc_srcCls_unif (d := d) (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) m' hN τ b
  obtain ⟨Ck, hCk0, hCk⟩ := kpot_chart_conormal hd (locKer_riesz hd hs0 hsd) (σ := τ + 2) hτ b m'
  obtain ⟨NL, hNL0, hNL⟩ := kPot_Lam_bounds hd hs0.le hsd (σ := τ + 2) hτ b m'
  choose C hC0 hC using fun i : Fin d => psii_conormal_unif (d := d) (s := s) (N := N) (νm := νm)
    (νp := νp) (c₀ := c₀) (Λ₀ := Λ₀) (m' + 2) hm hN τ b i
  obtain ⟨Kf, hKf0, hKf⟩ := fsrc_smooth (d := d) (σ := τ + 1) (b := b) (m' + 1)
  set Cs : ℝ := ∑ i, C i with hCs
  have hCs0 : 0 ≤ Cs := Finset.sum_nonneg fun i _ => hC0 i
  have hCle : ∀ i, C i ≤ Cs := fun i =>
    Finset.single_le_sum (f := C) (fun j _ => hC0 j) (Finset.mem_univ i)
  set I : ℝ := ∫ w in LocalDivAux.cube d, |ghat d s w| with hI
  have hI0 : 0 ≤ I := setIntegral_nonneg LocalDivAux.measurableSet_cube fun w _ => abs_nonneg _
  obtain ⟨Cc, hCc0, hCc⟩ := conormal_of_ck2 (d := d) (τ + 2 + s - d) (fun _ => b + 1) m'
  set S2 : ℝ := ∑ j ∈ Finset.range (m' + 1), (2 : ℝ) ^ j with hS2
  have hS20 : 0 ≤ S2 := Finset.sum_nonneg fun j _ => by positivity
  set c1 : ℝ := NL * K + I * ((d : ℝ) * (Kf * (Cs + 1))) with hc1
  have hc10 : 0 ≤ c1 := by positivity
  refine ⟨Ck * K + Cc * (S2 * c1), by positivity, fun β V ρ U B Ψ hB hΨ => ?_⟩
  have hρ : Torus.IsSmooth ρ := U.H.rho_smooth.smooth
  obtain ⟨hSrc, hz, hper, hGi⟩ := hK β V ρ U B Ψ hB hΨ
  have hA : 0 ≤ K * B := mul_nonneg hK0 hB
  have hPsi : ∀ i : Fin d, Conormal (τ + 1) b (m' + 1) ((Cs + 1) * B) (Psii ρ Ψ i) := by
    intro i
    have h1 := hC i β V ρ U B Ψ hB hΨ
    have e : m' + 2 - 1 = m' + 1 := by omega
    rw [e] at h1
    refine conormalL_mono_B h1 (mul_nonneg (hC0 i) hB) ?_
    nlinarith [hCle i, mul_nonneg hCs0 hB]
  have hCsB : 0 ≤ (Cs + 1) * B := mul_nonneg (by linarith) hB
  have hF : ∀ i, ContDiff ℝ ((m' + 1 : ℕ) : WithTop ℕ∞) (Fsrc (Psii ρ Ψ i)) ∧
      ∀ j ≤ m' + 1, ∀ p : Euc d × Euc d,
        ‖iteratedFDeriv ℝ j (Fsrc (Psii ρ Ψ i)) p‖ ≤ Kf * ((Cs + 1) * B) :=
    fun i => hKf hCsB (hPsi i)
  obtain ⟨hSFc, hSFb⟩ := sf_bounds (m := m') (fun i => (hF i).1) (Kf := Kf * ((Cs + 1) * B))
    (fun i => (hF i).2)
  obtain ⟨hFc, hFb, -, -⟩ := farConv_smooth hd hs0.le hsd (M := m') hSFc
    (N := fun _ => (d : ℝ) * (Kf * ((Cs + 1) * B))) hSFb
  obtain ⟨hLc, hLb⟩ := hNL hSrc hA
  set Q : Euc d × Euc d → ℝ := fun p => kPot d (Lam d s) (SNsrc ρ Ψ) p + farConv d s (SFsrc ρ Ψ) p
    with hQdef
  have hQc : ContDiff ℝ (m' : WithTop ℕ∞) Q := hLc.add hFc
  have hQb : ∀ j ≤ m', ∀ p : Euc d × Euc d, ‖iteratedFDeriv ℝ j Q p‖ ≤ c1 * B := by
    intro j hj p
    have e : Q = kPot d (Lam d s) (SNsrc ρ Ψ) + farConv d s (SFsrc ρ Ψ) := rfl
    rw [e, iteratedFDeriv_add_apply (hLc.contDiffAt.of_le (by exact_mod_cast hj)) (hFc.contDiffAt.of_le (by exact_mod_cast hj))]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (hLb j hj p) (hFb j hj p)).trans (le_of_eq ?_)
    rw [hc1]; ring
  have hY : ∀ Y z n : Euc d, IsLat n → Q (Y + n, z) = Q (Y, z) := by
    intro Y z n hn
    show kPot d (Lam d s) (SNsrc ρ Ψ) (Y + n, z) + farConv d s (SFsrc ρ Ψ) (Y + n, z) =
      kPot d (Lam d s) (SNsrc ρ Ψ) (Y, z) + farConv d s (SFsrc ρ Ψ) (Y, z)
    rw [kPot_periodic hper Y z n hn, farConv_periodic_fst s Y z n (fun w => SFsrc_periodic_fst ρ Ψ Y w n hn)]
  have hZ : ∀ Y z n : Euc d, IsLat n → Q (Y, z + n) = Q (Y, z) := by
    intro Y z n hn
    show kPot d (Lam d s) (SNsrc ρ Ψ) (Y, z + n) + farConv d s (SFsrc ρ Ψ) (Y, z + n) =
      kPot d (Lam d s) (SNsrc ρ Ψ) (Y, z) + farConv d s (SFsrc ρ Ψ) (Y, z)
    rw [kPot_Lam_periodic_snd s Y z n hn,
      farConv_periodic_snd s Y z n (fun w => SFsrc_periodic_snd ρ Ψ Y w n hn)]
  have hcb := cbNorm2_chartKer_le hQc hY hZ (N := fun _ => c1 * B) hQb
  have hcb' : PDE.cbNorm2 m' (chartKer Q) ≤ S2 * (c1 * B) := by
    refine hcb.trans (le_of_eq ?_)
    rw [hS2, Finset.sum_mul]
  have hR := hCc (chartKer Q) (isCk2_chartKer hQc hY hZ) (S2 * (c1 * B)) hcb'
  have hT1 := hCk (K * B) (SNsrc ρ Ψ) hA hSrc hz hper
  have hsum := conormalL_add hT1 hR
  have hfin := conormalL_mono_B hsum (by positivity : 0 ≤ Ck * (K * B) + Cc * (S2 * (c1 * B)))
    (le_of_eq (by ring) : Ck * (K * B) + Cc * (S2 * (c1 * B)) ≤ (Ck * K + Cc * (S2 * c1)) * B)
  refine conormalL_congr_offDiag (fun x y hxy => ?_) hfin
  have hσ : τ + 1 < (d : ℝ) - 1 := by linarith
  have hjf := jop_formula hd hs0 hsd hρ (A := K * B) (m := m') hA hσ (fun i => (hGi i).1)
    (fun i => (hF i).1) (N := fun _ => Kf * ((Cs + 1) * B)) (fun i => (hF i).2) x y hxy
  show ofChart (fun p => kPot d (rieszK d s) (SNsrc ρ Ψ) (shearCLM d (-(1 / 2 : ℝ)) p)) x y +
      chartKer Q x y = offZero (fun x y => Jop d s ρ (fun z => Ψ z y) x) x y
  simp only [offZero, if_neg hxy]
  rw [ofChart_kPot_eq _ _ x y hxy, chartKer_eq hZ, hjf]
  simp only [hQdef]
  ring

end HRS.ME.ParxU

end
