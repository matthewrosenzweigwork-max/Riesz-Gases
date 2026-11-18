import HRS.MS.SA16Y4Io8
import HRS.MS.SA16QFin6

/-!
# S.A.16 (SA16Y4) Io9: the order-one nonlocal bound `W^{m+1,p} → W^{m,p}` for regular densities (`0 ≤ s < d-1`)

`sa16y4io_nonlocal_bound`: for `1 ≤ d`, `0 ≤ s < d-1`, `d < p(s+1)`, `p ≥ 2`, `|M_{ij}| ≤ MB`, `μ` a `(m+3,Λ)`-regular density and Schwartz `u`:
`wNormE m p (eucNonlocal s M μ u) ≤ C wNormE (m+1) p u` (the proof of `sub_nonlocal_bound` with the order-one master estimate).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Evolution
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16 HRS.Whole.AppendixA.Phase2SA16Q
open HRS.MH.AdjointRd

theorem sa16y4io_nonlocal_bound (d m : ℕ) (hd : 1 ≤ d) (s p MB Λ : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s < (d : ℝ) - 1) [Fact (2 ≤ p)]
    (hfar : (d : ℝ) < p * (s + 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Matrix (Fin d) (Fin d) ℝ,
      (∀ i j, |M i j| ≤ MB) → ∀ μ : Euc d → ℝ,
      IsRegularDensityW (m + 3) Λ μ → ∀ u : SchwartzMap (Euc d) ℝ,
      wNormE m p (eucNonlocal s M μ u) ≤ ENNReal.ofReal C * wNormE (m + 1) p u := by
  have hp2 : 2 ≤ p := Fact.out
  have hd1 : 1 ≤ d := hd
  have hLp : 0 ≤ max Λ 0 := le_max_right Λ 0
  set W : ℝ := (d : ℝ) ^ (m + 2) * (2 ^ (d + 3) * (2 ^ (d + 3) * max Λ 0)) with hWdef
  have hW : 0 ≤ W := by positivity
  obtain ⟨K, hK, hKb⟩ := sa16y4io_master hd hs0 hs1 hp2 hfar m MB W hW
  obtain ⟨q, C1, hq1, hqp, hqa, hC1, hmaster⟩ := sa16y4io_master_exp hd hs0 hs1 hp2 hfar
  set card : ℝ≥0∞ := (Fintype.card (WIndex d m) : ℝ≥0∞) with hcard
  have hcardt : card ≠ ⊤ := ENNReal.natCast_ne_top _
  refine ⟨(card * K).toReal + 1, by positivity, ?_⟩
  intro M hM μ hμ u
  obtain ⟨hC, hbd, hw⟩ := sa16q_reg_data hμ
  have hμc : Continuous μ := hC.continuous
  have hμ1 : ContDiff ℝ 1 μ := hC.of_le (by exact_mod_cast (by omega : 1 ≤ m + 3))
  have hdata := fun N => sa16y4io_mol_data hd1 hμ N
  have hMB : 0 ≤ MB := (abs_nonneg _).trans (hM ⟨0, by omega⟩ ⟨0, by omega⟩)
  have hS : MemLp (sa16j_S d (m + 1) ⇑u) (ENNReal.ofReal p) volume := sa16j_S_memLp (m + 1) p u
  have hWjeq : wNormE (m + 1) p ⇑u = eLpNorm (wJet (m + 1) ⇑u) (ENNReal.ofReal p) volume :=
    sa16j_wNormE_eq d (m + 1) p u.smooth' hS
  set Wj := eLpNorm (wJet (m + 1) ⇑u) (ENNReal.ofReal p) volume with hWj
  have hWjt : Wj ≠ ⊤ := (sa16j_jet_memLp d (m + 1) p u.smooth' hS).eLpNorm_lt_top.ne
  set Fseq : ℕ → Euc d → ℝ := fun N => eucNonlocal s M (sa16q_mol N μ) ⇑u with hFseq
  have hunif : ∀ N, wNormE m p (Fseq N) ≤ card * (K * Wj) := by
    intro N
    obtain ⟨hSB, hwt⟩ := hdata N
    exact sa16y_wnorm_of_pd d m p (f := Fseq N) (sa16y4io_F_smooth hd hs0 hs1 M hSB u)
      (K := K * Wj) (ENNReal.mul_lt_top hK.lt_top hWjt.lt_top)
      (fun {j} hj idx => hKb M hM hSB hwt u hj idx)
  have hlimpt : ∀ x, Tendsto (fun N => Fseq N x) atTop (𝓝 (eucNonlocal s M μ ⇑u x)) := by
    intro x
    refine sa16y4io_F_tendsto hd hs0 hs1 M hμ1 (B0 := max Λ 0) (B1 := max Λ 0) (sa16q_reg_abs hμ)
      (sa16q_reg_fderiv hμ) (fun N => sa16q_mol N μ)
      (fun N => (sa16q_SB_C1 (hdata N).1).1) (fun N y => ?_) (fun N => ?_) (fun y => ?_) u x
    · exact sa16q_mol_bound N hμc (sa16q_reg_abs hμ) y
    · obtain ⟨_, B0, B1, -, hB1⟩ := sa16q_SB_C1 (hdata N).1
      exact ⟨B1, hB1⟩
    · exact sa16y_mollify_tendsto hμc y
  set TS := sa16y4io_TS μ u m q with hTS
  have hTSt : Tendsto TS atTop (𝓝 0) :=
    sa16y4io_TS_tendsto hC (Λ1 := 2 ^ (d + 3) * max Λ 0) (by positivity) hw u hq1.le
  set K3 : ℝ≥0∞ := ((d : ℝ≥0∞) * (d : ℝ≥0∞) * ENNReal.ofReal MB) * ENNReal.ofReal (2 ^ m) *
    ENNReal.ofReal C1 with hK3
  have hK3t : K3 ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.natCast_ne_top d) (ENNReal.natCast_ne_top d)) ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top |> fun h => ENNReal.mul_ne_top h ENNReal.ofReal_ne_top
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
      funext fun x => (sa16y4io_F_sub hd hs0 hs1 M h1n h1l hB0n hB1n hB0l hB1l u x).symm
    rw [hfun]
    have hb := sa16y_wnorm_of_pd d m p
      (f := eucNonlocal s M (fun y => sa16q_mol n μ y - sa16q_mol l μ y) ⇑u)
      (sa16y4io_F_smooth hd hs0 hs1 M hSBb u) (K := K3 * (TS n + TS l))
      (ENNReal.mul_lt_top hK3t.lt_top (ENNReal.add_lt_top.2 ⟨hn, hl⟩)) ?_
    · calc _ ≤ card * (K3 * (TS n + TS l)) := hb
        _ = _ := (mul_assoc card K3 _).symm
    · intro j hj idx
      have h2l : ENNReal.ofReal (2 ^ j) ≤ ENNReal.ofReal (2 ^ m) :=
        ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ (by norm_num) hj)
      have hsum : ∑ k ∈ Finset.range (j + 1), ENNReal.ofReal (j.choose k : ℝ) *
          eLpNorm (fun x => ‖iteratedFDeriv ℝ k (fun y => sa16q_mol n μ y - sa16q_mol l μ y) x‖ *
            ‖iteratedFDeriv ℝ (j - k + 1) u x‖) (ENNReal.ofReal q) volume ≤
          ENNReal.ofReal (2 ^ m) * (TS n + TS l) := by
        calc _ ≤ ∑ k ∈ Finset.range (j + 1), ENNReal.ofReal (j.choose k : ℝ) * (TS n + TS l) := by
              refine Finset.sum_le_sum fun k hk => sa16q_mul_le6 ?_
              have hkj : k ≤ j := by have := Finset.mem_range.1 hk; omega
              have hμk : ContDiff ℝ k μ := hC.of_le (by exact_mod_cast (by omega : k ≤ m + 3))
              refine (sa16q_tri hμk n l u (j - k + 1) hq1.le).trans (add_le_add ?_ ?_)
              · exact sa16y4io_T_le_TS μ u q n (κ := k) (n := j - k + 1) (by omega) (by omega)
              · exact sa16y4io_T_le_TS μ u q l (κ := k) (n := j - k + 1) (by omega) (by omega)
          _ = ENNReal.ofReal (2 ^ j) * (TS n + TS l) := by rw [← Finset.sum_mul, sa16q_choose_sum]
          _ ≤ _ := mul_le_mul' h2l le_rfl
      refine (hmaster M MB hM hSBb u idx).trans ?_
      calc ((d : ℝ≥0∞) * (d : ℝ≥0∞) * ENNReal.ofReal MB) * (ENNReal.ofReal C1 *
            ∑ k ∈ Finset.range (j + 1), ENNReal.ofReal (j.choose k : ℝ) *
              eLpNorm (fun x => ‖iteratedFDeriv ℝ k (fun y => sa16q_mol n μ y - sa16q_mol l μ y) x‖ *
                ‖iteratedFDeriv ℝ (j - k + 1) u x‖) (ENNReal.ofReal q) volume)
          ≤ ((d : ℝ≥0∞) * (d : ℝ≥0∞) * ENNReal.ofReal MB) *
            (ENNReal.ofReal C1 * (ENNReal.ofReal (2 ^ m) * (TS n + TS l))) :=
            sa16q_mul_le6 (sa16q_mul_le6 hsum)
        _ = K3 * (TS n + TS l) := by rw [hK3]; ring
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
