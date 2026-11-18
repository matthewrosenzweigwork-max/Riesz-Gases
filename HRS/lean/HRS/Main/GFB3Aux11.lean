import HRS.Main.GFB3Aux10

/-!
# Packet GFB3, part 11: uniform time-continuity of `∇f_r` and the `L²` bound of the Riemann-sum integrand error
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS

variable {d : ℕ}

lemma gfb3_uc {t : ℝ} {f ft : ℝ → Torus d → ℝ} (hf : IsC12Test t f ft) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ r ∈ Set.Icc 0 t, ∀ s ∈ Set.Icc 0 t, |r - s| < δ → ∀ (x : Torus d) (j : Fin d),
      |Torus.partialDeriv j (f r) x - Torus.partialDeriv j (f s) x| < ε := by
  have hK : IsCompact (Set.Icc 0 t ×ˢ Metric.closedBall (0 : Euc d) (Real.sqrt d)) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hc : ContinuousOn (fun p : ℝ × Euc d => gradient (Torus.lift (f p.1)) p.2)
      (Set.Icc 0 t ×ˢ Metric.closedBall (0 : Euc d) (Real.sqrt d)) :=
    (continuousOn_gradient_time hf).mono (Set.prod_mono subset_rfl (Set.subset_univ _))
  have hu := hK.uniformContinuousOn_of_continuous hc
  rw [Metric.uniformContinuousOn_iff] at hu
  obtain ⟨δ, hδ, h⟩ := hu ε hε
  refine ⟨δ, hδ, fun r hr s hs hrs x j => ?_⟩
  have hx : Torus.rep x ∈ Metric.closedBall (0 : Euc d) (Real.sqrt d) :=
    mem_closedBall_zero_iff.2 (rep_norm_le x)
  have h1 := h (r, Torus.rep x) ⟨hr, hx⟩ (s, Torus.rep x) ⟨hs, hx⟩
    (by simpa [Prod.dist_eq, Real.dist_eq] using hrs)
  rw [dist_eq_norm] at h1
  have h2 : |Torus.partialDeriv j (f r) x - Torus.partialDeriv j (f s) x| =
      |(Torus.grad (f r) x - Torus.grad (f s) x) j| := by
    rw [PiLp.sub_apply, HRS.Commutator.StressAux.grad_apply, HRS.Commutator.StressAux.grad_apply]
  rw [h2, ← Real.norm_eq_abs]
  exact (PiLp.norm_apply_le _ _).trans_lt h1

open Classical in
lemma gfb3_Xi_pointwise (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (N : ℕ) {Ω : Type*}
    (X : ℝ≥0 → Ω → Config d N) {t : ℝ} (ht : 0 ≤ t) {f ft : ℝ → Torus d → ℝ} {n : ℕ} (hn : 1 ≤ n)
    {ε' δ' : ℝ}
    (huc : ∀ r ∈ Set.Icc 0 t, ∀ s ∈ Set.Icc 0 t, |r - s| < δ' → ∀ (x : Torus d) (j : Fin d),
      |Torus.partialDeriv j (f r) x - Torus.partialDeriv j (f s) x| < ε')
    (hstep : t / n < δ') {s : ℝ} (hs : s ∈ Set.Ioc 0 t) (ω : Ω) (k : Fin N × Fin d) :
    |(∑ i : Fin n, restrictFun (gfb3_eta S N X (f (gfb3_part t n i.castSucc)))
        (gfb3_part t n i.castSucc) (gfb3_part t n i.succ) Set.univ s ω k) +
      (-(sigN S N)) * empiricalNoiseIntegrand (S.dynM M N) t f X s ω k| ≤
      |noiseScale S N / N| * ε' := by
  obtain ⟨i₀, hi₀⟩ := gfb3_part_cover ht hn hs
  have hsum : (∑ i : Fin n, restrictFun (gfb3_eta S N X (f (gfb3_part t n i.castSucc)))
        (gfb3_part t n i.castSucc) (gfb3_part t n i.succ) Set.univ s ω k) =
      gfb3_eta S N X (f (gfb3_part t n i₀.castSucc)) s ω k := by
    rw [Finset.sum_eq_single i₀]
    · unfold restrictFun
      rw [if_pos ⟨trivial, hi₀⟩]
    · intro j _ hj
      unfold restrictFun
      rw [if_neg (fun h => gfb3_part_disjoint ht (Ne.symm hj) hi₀ h.2)]
      rfl
    · intro h; exact absurd (Finset.mem_univ _) h
  have hE : empiricalNoiseIntegrand (S.dynM M N) t f X s ω k =
      (Real.sqrt (2 * S.invβ N) / N) *
        Torus.partialDeriv k.2 (f s) (X (Real.toNNReal s) ω k.1) := by
    unfold empiricalNoiseIntegrand
    rw [if_pos ⟨hs.1.le, hs.2⟩, HRS.Commutator.StressAux.grad_apply]
    rfl
  rw [hsum, hE]
  have hkey : gfb3_eta S N X (f (gfb3_part t n i₀.castSucc)) s ω k +
      (-(sigN S N)) * ((Real.sqrt (2 * S.invβ N) / N) *
        Torus.partialDeriv k.2 (f s) (X (Real.toNNReal s) ω k.1)) =
      (noiseScale S N / N) * (Torus.partialDeriv k.2 (f (gfb3_part t n i₀.castSucc))
          (X (Real.toNNReal s) ω k.1) -
        Torus.partialDeriv k.2 (f s) (X (Real.toNNReal s) ω k.1)) := by
    unfold gfb3_eta noiseScale
    ring
  rw [hkey, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have hab := gfb3_part_step (t := t) hn i₀
  have h0 : gfb3_part t n i₀.castSucc ∈ Set.Icc 0 t :=
    ⟨gfb3_part_nonneg ht _, gfb3_part_le ht hn _⟩
  refine (huc _ h0 s ⟨hs.1.le, hs.2⟩ ?_ _ _).le
  rw [abs_sub_comm, abs_of_nonneg (by linarith [hi₀.1])]
  linarith [hi₀.2]

end HRS.GF
