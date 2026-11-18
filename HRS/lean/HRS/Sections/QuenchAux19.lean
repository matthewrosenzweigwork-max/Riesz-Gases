import HRS.Sections.QuenchAux18

/-!
# Packet QUENCH (Q27), part 19: expectation of a bounded bilinear form of a window path

For an `E_m`-valued process `Wt` with a.s. continuous paths on `[0,T]`, `L²`-dominated supremum and
diagonal coordinate covariances `c_j(t,r)`:  `E M(W,W) = lim_n ∑_{k,l} E B_{n,k,l}(W(t_k),W(t_l))` with
`E B_{n,k,l}(W(t_k),W(t_l)) = ∑_j B_{n,k,l}(e_j,e_j) c_j(t_k,t_l)` (Bernstein in time, Hilbert basis in space).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Qch

variable {d : ℕ} {m T : ℝ}

/-- The coordinate-diagonal second-order window process data. -/
structure WinData {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (m T : ℝ)
    (Wt : ℝ → Ω → NegSobolev d m) (c : NonzeroLattice d → ℝ → ℝ → ℝ) : Prop where
  meas : ∀ t, Measurable (Wt t)
  cont : ∀ᵐ ω ∂P, ContinuousOn (fun t => Wt t ω) (Set.Icc 0 T)
  dom : ∃ H : Ω → ℝ, Integrable H P ∧ ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, ‖Wt t ω‖ ^ 2 ≤ H ω
  cov : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ j j' : NonzeroLattice d,
    ∫ ω, NegSobolev.coord (Wt t ω) j * NegSobolev.coord (Wt r ω) j' ∂P = if j = j' then c j t r else 0

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma toPath_at {Wt : ℝ → Ω → NegSobolev d m} {ω : Ω} (hc : ContinuousOn (fun t => Wt t ω) (Set.Icc 0 T))
    (t : Set.Icc (0 : ℝ) T) : (toPath m T Wt ω).at' t = Wt t ω := by
  have h : Continuous fun t : Set.Icc (0 : ℝ) T => Wt t ω := hc.restrict
  have e : toPath m T Wt ω = (⟨fun t : Set.Icc (0 : ℝ) T => Wt t ω, h⟩ : C(Set.Icc (0 : ℝ) T, NegSobolev d m)) := by
    unfold toPath
    exact dif_pos h
  rw [e]
  rfl

/-- The curried bilinear form of `M` pulled back along the `(k,l)`-th Bernstein embeddings. -/
def bk (hT : 0 < T) (M : PathSpace d m T [×2]→L[ℝ] ℝ) (n : ℕ) (k l : Fin (n + 1)) :
    NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ :=
  (bilinOfMulti M).bilinearComp (bemb hT n k) (bemb hT n l)

lemma bInterp_bilin (hT : 0 < T) (M : PathSpace d m T [×2]→L[ℝ] ℝ) (n : ℕ) (w : PathSpace d m T) :
    M ![bInterp hT n w, bInterp hT n w] =
      ∑ k : Fin (n + 1), ∑ l : Fin (n + 1), bk hT M n k l (w.at' (bnode hT n k)) (w.at' (bnode hT n l)) := by
  rw [← bilinOfMulti_apply]
  unfold bInterp
  have h1 : bilinOfMulti M (∑ k : Fin (n + 1), bemb hT n k (w.at' (bnode hT n k))) =
      ∑ k : Fin (n + 1), bilinOfMulti M (bemb hT n k (w.at' (bnode hT n k))) := map_sum _ _ _
  rw [h1, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rfl

section WinLimit

variable {Wt : ℝ → Ω → NegSobolev d m} {c : NonzeroLattice d → ℝ → ℝ → ℝ}

lemma WinData.integrable_norm_mul (hW : WinData P m T Wt c) {t r : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    (hr : r ∈ Set.Icc (0 : ℝ) T) : Integrable (fun ω => ‖Wt t ω‖ * ‖Wt r ω‖) P := by
  obtain ⟨H, hH, hbd⟩ := hW.dom
  refine hH.mono' (((hW.meas t).norm).mul ((hW.meas r).norm)).aestronglyMeasurable ?_
  filter_upwards [hbd] with ω h
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  nlinarith [h t ht, h r hr, sq_nonneg (‖Wt t ω‖ - ‖Wt r ω‖)]

theorem win_hasSum (hT : 0 < T) (hW : WinData P m T Wt c) (M : PathSpace d m T [×2]→L[ℝ] ℝ) (n : ℕ)
    (k l : Fin (n + 1)) :
    HasSum (fun j => bk hT M n k l (esingle m j) (esingle m j) * c j (bnode hT n k) (bnode hT n l))
      (∫ ω, bk hT M n k l (Wt (bnode hT n k) ω) (Wt (bnode hT n l) ω) ∂P) :=
  expect_bilinear (bk hT M n k l) (hW.meas _) (hW.meas _) (hW.integrable_norm_mul (bnode hT n k).2
    (bnode hT n l).2) _ (hW.cov _ (bnode hT n k).2 _ (bnode hT n l).2)

lemma WinData.integrable_bk (hT : 0 < T) (hW : WinData P m T Wt c) (M : PathSpace d m T [×2]→L[ℝ] ℝ)
    (n : ℕ) (k l : Fin (n + 1)) :
    Integrable (fun ω => bk hT M n k l (Wt (bnode hT n k) ω) (Wt (bnode hT n l) ω)) P := by
  have hint := (hW.integrable_norm_mul (bnode hT n k).2 (bnode hT n l).2).const_mul ‖bk hT M n k l‖
  refine hint.mono' ?_ (Eventually.of_forall fun ω => ?_)
  · exact ((bk hT M n k l).continuous₂.measurable.comp
      ((hW.meas _).prodMk (hW.meas _))).aestronglyMeasurable
  · have := (bk hT M n k l).le_opNorm₂ (Wt (bnode hT n k) ω) (Wt (bnode hT n l) ω)
    calc ‖bk hT M n k l (Wt (bnode hT n k) ω) (Wt (bnode hT n l) ω)‖
        ≤ ‖bk hT M n k l‖ * ‖Wt (bnode hT n k) ω‖ * ‖Wt (bnode hT n l) ω‖ := this
      _ = ‖bk hT M n k l‖ * (‖Wt (bnode hT n k) ω‖ * ‖Wt (bnode hT n l) ω‖) := by ring

theorem win_limit (hT : 0 < T) (hW : WinData P m T Wt c) (M : PathSpace d m T [×2]→L[ℝ] ℝ) :
    Tendsto (fun n : ℕ => ∑ k : Fin (n + 1), ∑ l : Fin (n + 1),
        ∫ ω, bk hT M n k l (Wt (bnode hT n k) ω) (Wt (bnode hT n l) ω) ∂P) atTop
      (𝓝 (∫ ω, M ![toPath m T Wt ω, toPath m T Wt ω] ∂P)) := by
  obtain ⟨H, hH, hbd⟩ := hW.dom
  set pth : Ω → PathSpace d m T := fun ω => toPath m T Wt ω with hpth
  set F : ℕ → Ω → ℝ := fun n ω => M ![bInterp hT n (pth ω), bInterp hT n (pth ω)] with hF
  have hgood : ∀ᵐ ω ∂P, ContinuousOn (fun t => Wt t ω) (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, ‖Wt t ω‖ ^ 2 ≤ H ω := by
    filter_upwards [hW.cont, hbd] with ω h1 h2 using ⟨h1, h2⟩
  -- (i) the identity `F n = ∑∑ B(W(t_k),W(t_l))`
  have hFn : ∀ n, ∀ᵐ ω ∂P, F n ω = ∑ k : Fin (n + 1), ∑ l : Fin (n + 1),
      bk hT M n k l (Wt (bnode hT n k) ω) (Wt (bnode hT n l) ω) := by
    intro n
    filter_upwards [hgood] with ω h
    simp only [hF, hpth]
    rw [bInterp_bilin]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [toPath_at h.1, toPath_at h.1]
  have hmeasF : ∀ n, AEStronglyMeasurable (F n) P := by
    intro n
    refine AEStronglyMeasurable.congr ?_ (show F n =ᵐ[P] _ from hFn n).symm
    exact (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ =>
      (bk hT M n k l).continuous₂.measurable.comp ((hW.meas _).prodMk (hW.meas _))).aestronglyMeasurable
  -- (ii) the integrals
  have hint : ∀ n, ∫ ω, F n ω ∂P = ∑ k : Fin (n + 1), ∑ l : Fin (n + 1),
      ∫ ω, bk hT M n k l (Wt (bnode hT n k) ω) (Wt (bnode hT n l) ω) ∂P := by
    intro n
    rw [integral_congr_ae (hFn n), integral_finset_sum _ fun k _ => integrable_finset_sum _ fun l _ =>
      hW.integrable_bk hT M n k l]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finset_sum _ fun l _ => hW.integrable_bk hT M n k l]
  simp_rw [← hint]
  -- (iii) dominated convergence
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (M ![pth ω, pth ω])) := by
    filter_upwards with ω
    have h1 : Tendsto (fun n => ![bInterp hT n (pth ω), bInterp hT n (pth ω)]) atTop (𝓝 ![pth ω, pth ω]) := by
      refine tendsto_pi_nhds.2 fun i => ?_
      fin_cases i <;> simpa using bInterp_tendsto hT (pth ω)
    exact (M.cont.tendsto _).comp h1
  have hbound : ∀ n, ∀ᵐ ω ∂P, ‖F n ω‖ ≤ ‖M‖ * H ω := by
    intro n
    filter_upwards [hgood] with ω h
    have hH0 : 0 ≤ H ω := le_trans (sq_nonneg _) (h.2 0 ⟨le_rfl, hT.le⟩)
    have hnorm : ‖pth ω‖ ^ 2 ≤ H ω := by
      have : ‖pth ω‖ ≤ Real.sqrt (H ω) := by
        refine (ContinuousMap.norm_le (pth ω : C(Set.Icc (0 : ℝ) T, NegSobolev d m)) (Real.sqrt_nonneg _)).2
          fun t => ?_
        show ‖(pth ω).at' t‖ ≤ _
        rw [hpth]
        simp only
        rw [toPath_at h.1]
        exact Real.le_sqrt_of_sq_le (h.2 t t.2)
      calc ‖pth ω‖ ^ 2 ≤ Real.sqrt (H ω) ^ 2 := by gcongr
        _ = H ω := Real.sq_sqrt hH0
    have h1 := abs_multi_le M (bInterp hT n (pth ω)) (bInterp hT n (pth ω))
    rw [Real.norm_eq_abs]
    calc |F n ω| ≤ ‖M‖ * ‖bInterp hT n (pth ω)‖ * ‖bInterp hT n (pth ω)‖ := h1
      _ ≤ ‖M‖ * ‖pth ω‖ * ‖pth ω‖ := by
          gcongr
          · exact norm_bInterp_le hT n _
          · exact norm_bInterp_le hT n _
      _ = ‖M‖ * ‖pth ω‖ ^ 2 := by ring
      _ ≤ ‖M‖ * H ω := by gcongr
  exact tendsto_integral_of_dominated_convergence (fun ω => ‖M‖ * H ω) hmeasF (hH.const_mul _) hbound hlim

end WinLimit

end Qch

end HRS
