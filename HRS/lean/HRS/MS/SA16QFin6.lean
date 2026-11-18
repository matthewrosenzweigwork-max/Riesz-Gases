import HRS.MS.SA16QFin5
import HRS.MS.SA16StrongLimit

/-!
# S.A.16 (SA16Q), E6: `sub_nonlocal_bound`

The full-kernel operator `∑ M_{ji} ∂_i (g * (μ ∂_j u))`, `0 ≤ s ≤ d - 2`, `d < p (s+1)`, is bounded on `W^{m,p}`
for Schwartz `u` and `(m+3, Λ)`-regular `μ`.  Proof: mollify `μ` (`sa16q_mol`), prove the estimate for the smooth
coefficients (integration by parts, HLS and Calderon-Zygmund), show the mollified images are Cauchy in the weak norm
and converge pointwise (`sa16y_wnorm_limit`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16

lemma sa16q_SB_C1 {d : ℕ} {a : Euc d → ℝ} (ha : sa16q_SB a) :
    ContDiff ℝ 1 a ∧ ∃ B0 B1 : ℝ, (∀ x, |a x| ≤ B0) ∧ (∀ x, ‖fderiv ℝ a x‖ ≤ B1) := by
  obtain ⟨B0, h0⟩ := ha.2 0
  obtain ⟨B1, h1⟩ := ha.2 1
  refine ⟨ha.1.of_le (by exact_mod_cast le_top), B0, B1, fun x => ?_, fun x => ?_⟩
  · have := h0 x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  · have := h1 x
    rwa [norm_iteratedFDeriv_one] at this

end HRS.Whole.AppendixA.Phase2SA16Q

namespace HRS.Whole.AppendixA.Phase2SA16Evolution
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16 HRS.Whole.AppendixA.Phase2SA16Q
open HRS.MH.AdjointRd

/-- E6: all subcritical matrices, including the Coulomb/logarithmic
endpoint, with the exact strict far-field threshold. -/
theorem sub_nonlocal_bound (d m : ℕ) (hd : 1 ≤ d) (s p MB Λ : ℝ)
    (hs0 : 0 ≤ s) (hs2 : s ≤ (d : ℝ)-2) [Fact (2 ≤ p)]
    (hfar : (d : ℝ)<p*(s+1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Matrix (Fin d) (Fin d) ℝ,
      (∀ i j, |M i j| ≤ MB) → ∀ μ : Euc d → ℝ,
      IsRegularDensityW (m+3) Λ μ → ∀ u : SchwartzMap (Euc d) ℝ,
      wNormE m p (eucNonlocal s M μ u) ≤ ENNReal.ofReal C*wNormE m p u := by
  have hp2 : 2 ≤ p := Fact.out
  have hd2 : 2 ≤ d := by
    have : (2 : ℝ) ≤ d := by linarith
    exact_mod_cast this
  have hd1 : 1 ≤ d := by omega
  have hLp : 0 ≤ max Λ 0 := le_max_right _ _
  set W : ℝ := (d : ℝ) ^ (m + 1) * (2 ^ (d + 3) * (2 ^ (d + 3) * max Λ 0)) with hWdef
  have hW : 0 ≤ W := by positivity
  obtain ⟨K, hK, hKb⟩ := sa16q_unif_master hd2 hs0 hs2 hp2 hfar m MB W hW
  obtain ⟨q, r, C1, C2, hq1, hqp, hqa, hr1, hr, hC1, hC2, hmaster⟩ :=
    sa16q_master_exps hd2 hs0 hs2 hp2 hfar
  set card : ℝ≥0∞ := (Fintype.card (WIndex d m) : ℝ≥0∞) with hcard
  have hcardt : card ≠ ⊤ := ENNReal.natCast_ne_top _
  refine ⟨(card * K).toReal + 1, by positivity, ?_⟩
  intro M hM μ hμ u
  obtain ⟨hC, hbd, hw⟩ := sa16q_reg_data hμ
  have hμc : Continuous μ := hC.continuous
  have hμ1 : ContDiff ℝ 1 μ := hC.of_le (by exact_mod_cast (by omega : 1 ≤ m + 3))
  have hdata := fun N => sa16q_mol_data hd1 hμ N
  have hMB : 0 ≤ MB := (abs_nonneg _).trans (hM ⟨0, by omega⟩ ⟨0, by omega⟩)
  -- the weak norm of `u`
  have hS : MemLp (sa16j_S d m ⇑u) (ENNReal.ofReal p) volume := sa16j_S_memLp m p u
  have hWjeq : wNormE m p ⇑u = eLpNorm (wJet m ⇑u) (ENNReal.ofReal p) volume :=
    sa16j_wNormE_eq d m p u.smooth' hS
  set Wj := eLpNorm (wJet m ⇑u) (ENNReal.ofReal p) volume with hWj
  have hWjt : Wj ≠ ⊤ := (sa16j_jet_memLp d m p u.smooth' hS).eLpNorm_lt_top.ne
  set Fseq : ℕ → Euc d → ℝ := fun N => eucNonlocal s M (sa16q_mol N μ) ⇑u with hFseq
  -- uniform bound
  have hunif : ∀ N, wNormE m p (Fseq N) ≤ card * (K * Wj) := by
    intro N
    obtain ⟨hSB, hwt⟩ := hdata N
    have hb := sa16y_wnorm_of_pd d m p (f := Fseq N) (sa16q_F_smooth hd2 hs0 hs2 M hSB u)
      (K := K * Wj) (ENNReal.mul_lt_top hK.lt_top hWjt.lt_top)
      (fun {j} hj idx => hKb M hM hSB hwt u hj idx)
    exact hb
  -- pointwise convergence
  have hlimpt : ∀ x, Tendsto (fun N => Fseq N x) atTop (𝓝 (eucNonlocal s M μ ⇑u x)) := by
    intro x
    refine sa16q_F_tendsto hd2 hs0 hs2 M hμ1 (B0 := max Λ 0) (B1 := max Λ 0) (sa16q_reg_abs hμ)
      (sa16q_reg_fderiv hμ) (fun N => sa16q_mol N μ)
      (fun N => (sa16q_SB_C1 (hdata N).1).1) (fun N y => ?_) (fun N => ?_) (fun y => ?_) u x
    · exact sa16q_mol_bound N hμc (sa16q_reg_abs hμ) y
    · obtain ⟨_, B0, B1, -, hB1⟩ := sa16q_SB_C1 (hdata N).1
      exact ⟨B1, hB1⟩
    · exact sa16y_mollify_tendsto hμc y
  -- the Cauchy property
  set TS := sa16q_TS μ u m q r with hTS
  have hTSt : Tendsto TS atTop (𝓝 0) :=
    sa16q_TS_tendsto hC (Λ1 := 2 ^ (d + 3) * max Λ 0) (by positivity) hw u hq1.le hr1.le
  set K3 : ℝ≥0∞ := ((d : ℝ≥0∞) * (d : ℝ≥0∞) * ENNReal.ofReal MB) * ENNReal.ofReal (2 ^ m) *
    (ENNReal.ofReal C2 + ENNReal.ofReal C1) with hK3
  have hK3t : K3 ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.natCast_ne_top d) (ENNReal.natCast_ne_top d)) ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top |> fun h => ENNReal.mul_ne_top h
        (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
  have hKC : ∀ n l, TS n < ⊤ → TS l < ⊤ →
      wNormE m p (fun x => Fseq n x - Fseq l x) ≤ (card * K3) * (TS n + TS l) := by
    intro n l hn hl
    obtain ⟨hSBn, -⟩ := hdata n
    obtain ⟨hSBl, -⟩ := hdata l
    have hSBb : sa16q_SB (fun y => sa16q_mol n μ y - sa16q_mol l μ y) := sa16q_SB_sub hSBn hSBl
    obtain ⟨h1n, B0n, B1n, hB0n, hB1n⟩ := sa16q_SB_C1 hSBn
    obtain ⟨h1l, B0l, B1l, hB0l, hB1l⟩ := sa16q_SB_C1 hSBl
    have hfun : (fun x => Fseq n x - Fseq l x) =
        eucNonlocal s M (fun y => sa16q_mol n μ y - sa16q_mol l μ y) ⇑u :=
      funext fun x => (sa16q_F_sub hd2 hs0 hs2 M h1n h1l hB0n hB1n hB0l hB1l u x).symm
    rw [hfun]
    have hb := sa16y_wnorm_of_pd d m p
      (f := eucNonlocal s M (fun y => sa16q_mol n μ y - sa16q_mol l μ y) ⇑u)
      (sa16q_F_smooth hd2 hs0 hs2 M hSBb u) (K := K3 * (TS n + TS l))
      (ENNReal.mul_lt_top hK3t.lt_top (ENNReal.add_lt_top.2 ⟨hn, hl⟩)) ?_
    · calc _ ≤ card * (K3 * (TS n + TS l)) := hb
        _ = _ := (mul_assoc card K3 _).symm
    · intro j hj idx
      have h2l : ENNReal.ofReal (2 ^ j) ≤ ENNReal.ofReal (2 ^ m) :=
        ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ (by norm_num) hj)
      have hNP : sa16q_NP (fun y => sa16q_mol n μ y - sa16q_mol l μ y) u j r ≤
          ENNReal.ofReal (2 ^ m) * (TS n + TS l) := by
        refine (sa16q_NP_le (TS n + TS l) (fun k hk => ?_)).trans (mul_le_mul' h2l le_rfl)
        have hμk : ContDiff ℝ k μ := hC.of_le (by exact_mod_cast (by omega : k ≤ m + 3))
        refine (sa16q_tri hμk n l u (j - k) hr1.le).trans (add_le_add ?_ ?_)
        · exact (sa16q_T_le_TS μ u q r n (κ := k) (n := j - k) (by omega) (by omega)).1
        · exact (sa16q_T_le_TS μ u q r l (κ := k) (n := j - k) (by omega) (by omega)).1
      have hNQ : sa16q_NQ (fun y => sa16q_mol n μ y - sa16q_mol l μ y) u j q ≤
          ENNReal.ofReal (2 ^ m) * (TS n + TS l) := by
        refine (sa16q_NQ_le (TS n + TS l) (fun k hk => ?_)).trans (mul_le_mul' h2l le_rfl)
        have hμk : ContDiff ℝ (k + 1) μ := hC.of_le (by exact_mod_cast (by omega : k + 1 ≤ m + 3))
        refine (sa16q_tri hμk n l u (j - k) hq1.le).trans (add_le_add ?_ ?_)
        · exact (sa16q_T_le_TS μ u q r n (κ := k + 1) (n := j - k) (by omega) (by omega)).2
        · exact (sa16q_T_le_TS μ u q r l (κ := k + 1) (n := j - k) (by omega) (by omega)).2
      refine (hmaster M MB hM hSBb u idx).trans ?_
      calc ((d : ℝ≥0∞) * (d : ℝ≥0∞) * ENNReal.ofReal MB) *
            (ENNReal.ofReal C2 * sa16q_NP (fun y => sa16q_mol n μ y - sa16q_mol l μ y) u j r +
              ENNReal.ofReal C1 * sa16q_NQ (fun y => sa16q_mol n μ y - sa16q_mol l μ y) u j q)
          ≤ ((d : ℝ≥0∞) * (d : ℝ≥0∞) * ENNReal.ofReal MB) *
            (ENNReal.ofReal C2 * (ENNReal.ofReal (2 ^ m) * (TS n + TS l)) +
              ENNReal.ofReal C1 * (ENNReal.ofReal (2 ^ m) * (TS n + TS l))) :=
            sa16q_mul_le6 (add_le_add (sa16q_mul_le6 hNP) (sa16q_mul_le6 hNQ))
        _ = K3 * (TS n + TS l) := by rw [hK3]; ring
  -- Cauchy
  have hCauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ l ≥ N,
      wNormE m p (fun x => Fseq n x - Fseq l x) ≤ ENNReal.ofReal ε := by
    intro ε hε
    have hKct : card * K3 ≠ ⊤ := ENNReal.mul_ne_top hcardt hK3t
    have hZ : Tendsto (fun N => (card * K3) * TS N) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hTSt (Or.inr hKct)
    have hev1 := (tendsto_order.1 hZ).2 (ENNReal.ofReal (ε / 2))
      (by simpa using ENNReal.ofReal_pos.2 (half_pos hε))
    have hev2 := (tendsto_order.1 hTSt).2 1 (by simp)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hev1.and hev2)
    refine ⟨N, fun n hn l hl => ?_⟩
    have h1 := hN n hn
    have h2 := hN l hl
    refine (hKC n l (h1.2.trans ENNReal.one_lt_top) (h2.2.trans ENNReal.one_lt_top)).trans ?_
    rw [mul_add]
    calc (card * K3) * TS n + (card * K3) * TS l ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
          add_le_add h1.1.le h2.1.le
      _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  have hlim := sa16y_wnorm_limit m p Fseq (eucNonlocal s M μ ⇑u) (card * (K * Wj))
    (ENNReal.mul_lt_top hcardt.lt_top (ENNReal.mul_lt_top hK.lt_top hWjt.lt_top)) hunif
    (Eventually.of_forall hlimpt) hCauchy
  rw [hWjeq]
  refine hlim.trans ?_
  calc card * (K * Wj) = (card * K) * Wj := (mul_assoc _ _ _).symm
    _ ≤ ENNReal.ofReal ((card * K).toReal + 1) * Wj := by
        refine mul_le_mul' ?_ le_rfl
        have hcK : card * K ≠ ⊤ := ENNReal.mul_ne_top hcardt hK
        calc card * K = ENNReal.ofReal (card * K).toReal := (ENNReal.ofReal_toReal hcK).symm
          _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)

end HRS.Whole.AppendixA.Phase2SA16Evolution
