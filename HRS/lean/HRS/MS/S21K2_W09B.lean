import HRS.MS.S21K2_W09A

/-!
# S21K2 W09B -- Rellich-type compactness (R26-T3.W09)

Continuous compactly supported functions in a ball `B_L` with `∫ u² <= K` and `∫ (1+4π²|ξ|²)|F u|² <= K` form a totally bounded set of
`L²` (Arzela-Ascoli for the Fourier transforms on `B_R`, uniform Fourier tails), and a finite family of such sequences has a common
subsequence that is `L²`-Cauchy in every member.  Helper prefix `s21k2_w09_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators FourierTransform
noncomputable section
namespace HRS.MS.R26T3
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux
variable {d : ℕ}

theorem s21k2_w09_totallyBounded {L K : ℝ} (hL : 0 ≤ L) (u : ℕ → HRS.Euc d → ℝ)
    (hcont : ∀ n, Continuous (u n)) (hcs : ∀ n, HasCompactSupport (u n))
    (hsupp : ∀ n, tsupport (u n) ⊆ Metric.closedBall 0 L) (hL2 : ∀ n, ∫ x, u n x ^ 2 ≤ K)
    (hs : ∀ n, HRS.PDE.ToolboxRd.MemSobolev (1 : ℝ) (u n))
    (hK : ∀ n, ∫ ξ, (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (1 : ℝ) * ‖fourierL2 (u n) ξ‖ ^ 2 ≤ K) :
    TotallyBounded (Set.range fun n => s21k2_w09_lp (hcont n) (hcs n)) := by
  have hK0 : 0 ≤ K := (integral_nonneg fun x => sq_nonneg _).trans (hL2 0)
  set A : ℝ := ((volume (Metric.closedBall (0 : HRS.Euc d) L)).toReal + K) / 2 with hA
  have hA0 : 0 ≤ A := by positivity
  have hint : ∀ n, ∫ v, |u n v| ≤ A := fun n =>
    (s21k2_w09_L1 (hcont n) (hcs n) (hsupp n)).trans (by rw [hA]; linarith [hL2 n])
  have hbd : ∀ n ξ, ‖s21k2_w09_F (u n) ξ‖ ≤ A := fun n ξ =>
    (s21k2_w09_F_bound (hcont n) (hcs n) ξ).trans (hint n)
  set Kl : ℝ := 2 * Real.pi * L * A with hKl
  have hKl0 : 0 ≤ Kl := by positivity
  have hlip : ∀ n ξ ξ', ‖s21k2_w09_F (u n) ξ - s21k2_w09_F (u n) ξ'‖ ≤ Kl * ‖ξ - ξ'‖ := fun n ξ ξ' => by
    refine (s21k2_w09_F_lip (hcont n) (hcs n) (hsupp n) ξ ξ').trans ?_
    have := mul_le_mul_of_nonneg_left (hint n) (by positivity : 0 ≤ 2 * Real.pi * L * ‖ξ - ξ'‖)
    calc _ ≤ _ := this
      _ = _ := by rw [hKl]; ring
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (16 * K / ε ^ 2)
  set R : ℝ := (N : ℝ) with hRdef
  have hR0 : 0 ≤ R := Nat.cast_nonneg N
  have hRbig : 16 * K / ε ^ 2 < 1 + 4 * Real.pi ^ 2 * R ^ 2 := by
    refine hN.trans_le ?_
    have hp : (1 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    nlinarith [mul_nonneg (sq_nonneg R) (by nlinarith : (0 : ℝ) ≤ 4 * Real.pi ^ 2 - 1), sq_nonneg (R - 1)]
  have htail : 4 * K / (1 + 4 * Real.pi ^ 2 * R ^ 2) ≤ ε ^ 2 / 4 := by
    have hpos : 0 < 1 + 4 * Real.pi ^ 2 * R ^ 2 := by positivity
    rw [div_le_iff₀ hpos]
    have := (div_lt_iff₀ (by positivity : 0 < ε ^ 2)).1 hRbig
    nlinarith
  set V : ℝ := (volume (Metric.closedBall (0 : HRS.Euc d) R)).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  set δ : ℝ := ε / (2 * (Real.sqrt V + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hVδ : V * δ ^ 2 ≤ ε ^ 2 / 4 := by
    have h1 : V ≤ (Real.sqrt V + 1) ^ 2 := by nlinarith [Real.sq_sqrt hV0, Real.sqrt_nonneg V]
    have hd : δ * (Real.sqrt V + 1) = ε / 2 := by rw [hδ]; field_simp
    have h2 : δ ^ 2 * (Real.sqrt V + 1) ^ 2 = ε ^ 2 / 4 := by
      calc δ ^ 2 * (Real.sqrt V + 1) ^ 2 = (δ * (Real.sqrt V + 1)) ^ 2 := by ring
        _ = ε ^ 2 / 4 := by rw [hd]; ring
    calc V * δ ^ 2 ≤ (Real.sqrt V + 1) ^ 2 * δ ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = ε ^ 2 / 4 := by rw [mul_comm, h2]
  haveI : CompactSpace (Metric.closedBall (0 : HRS.Euc d) R) :=
    isCompact_iff_compactSpace.1 (isCompact_closedBall _ _)
  let g : ℕ → BoundedContinuousFunction (Metric.closedBall (0 : HRS.Euc d) R) ℂ := fun n =>
    BoundedContinuousFunction.mkOfCompact ⟨fun ξ => s21k2_w09_F (u n) ξ.1,
      (s21k2_w09_F_cont (hcont n) (hcs n)).comp continuous_subtype_val⟩
  have hg : ∀ n ξ, g n ξ = s21k2_w09_F (u n) ξ.1 := fun n ξ => rfl
  have hcomp : IsCompact (closure (Set.range g)) := by
    refine BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : ℂ) A) (isCompact_closedBall _ _)
      (Set.range g) ?_ ?_
    · rintro _ ξ ⟨n, rfl⟩
      rw [hg]; exact mem_closedBall_zero_iff.2 (hbd n _)
    · have hl : ∀ f : Set.range g, LipschitzWith (Real.toNNReal Kl) (⇑(f : BoundedContinuousFunction (Metric.closedBall (0 : HRS.Euc d) R) ℂ)) := by
        rintro ⟨_, n, rfl⟩
        refine LipschitzWith.of_dist_le_mul fun x y => ?_
        rw [Real.coe_toNNReal _ hKl0, dist_eq_norm, hg, hg, Subtype.dist_eq, dist_eq_norm]
        exact hlip n _ _
      exact (LipschitzWith.uniformEquicontinuous (fun (f : Set.range g) => ⇑(f : BoundedContinuousFunction (Metric.closedBall (0 : HRS.Euc d) R) ℂ)) _ hl).equicontinuous
  have htb : TotallyBounded (Set.range g) := hcomp.totallyBounded.subset subset_closure
  obtain ⟨t, htA, htf, hcov⟩ := totallyBounded_iff_subset.1 htb {p | dist p.1 p.2 < δ}
    (Metric.dist_mem_uniformity hδpos)
  have hex : ∀ y ∈ t, ∃ i, g i = y := fun y hy => htA hy
  choose! idx hidx using hex
  refine ⟨(fun y => s21k2_w09_lp (hcont (idx y)) (hcs (idx y))) '' t, htf.image _, ?_⟩
  rintro _ ⟨n, rfl⟩
  obtain ⟨y, hyt, hy⟩ := Set.mem_iUnion₂.1 (hcov (⟨n, rfl⟩ : g n ∈ Set.range g))
  refine Set.mem_iUnion₂.2 ⟨_, ⟨y, hyt, rfl⟩, ?_⟩
  rw [Metric.mem_ball]
  have hdist : dist (g n) (g (idx y)) < δ := by rw [hidx y hyt]; exact hy
  have hnear : ∀ ξ ∈ Metric.closedBall (0 : HRS.Euc d) R,
      ‖s21k2_w09_F (u n) ξ - s21k2_w09_F (u (idx y)) ξ‖ ≤ δ := fun ξ hξ => by
    have := BoundedContinuousFunction.dist_coe_le_dist (f := g n) (g := g (idx y)) ⟨ξ, hξ⟩
    rw [hg, hg, dist_eq_norm] at this
    exact this.trans hdist.le
  have hest := s21k2_w09_estimate (hcont n) (hcs n) (hcont (idx y)) (hcs (idx y)) (hs n) (hK n)
    (hs (idx y)) (hK (idx y)) hR0 hnear
  have hsq := s21k2_w09_lp_dist (hcont n) (hcs n) (hcont (idx y)) (hcs (idx y))
  have : dist (s21k2_w09_lp (hcont n) (hcs n)) (s21k2_w09_lp (hcont (idx y)) (hcs (idx y))) ^ 2 < ε ^ 2 := by
    rw [hsq]; linarith [pow_pos hε 2]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le this


theorem s21k2_w09_cauchy_subseq {L K : ℝ} (hL : 0 ≤ L) (u : ℕ → HRS.Euc d → ℝ)
    (hcont : ∀ n, Continuous (u n)) (hcs : ∀ n, HasCompactSupport (u n))
    (hsupp : ∀ n, tsupport (u n) ⊆ Metric.closedBall 0 L) (hL2 : ∀ n, ∫ x, u n x ^ 2 ≤ K)
    (hs : ∀ n, HRS.PDE.ToolboxRd.MemSobolev (1 : ℝ) (u n))
    (hK : ∀ n, ∫ ξ, (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (1 : ℝ) * ‖fourierL2 (u n) ξ‖ ^ 2 ≤ K) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ CauchySeq (fun n => s21k2_w09_lp (hcont (σ n)) (hcs (σ n))) := by
  have htb := s21k2_w09_totallyBounded hL u hcont hcs hsupp hL2 hs hK
  have hcl : IsCompact (closure (Set.range fun n => s21k2_w09_lp (hcont n) (hcs n))) :=
    htb.closure.isCompact_of_isClosed isClosed_closure
  obtain ⟨a, -, σ, hσ, hlim⟩ := hcl.tendsto_subseq (x := fun n => s21k2_w09_lp (hcont n) (hcs n))
    (fun n => subset_closure ⟨n, rfl⟩)
  exact ⟨σ, hσ, hlim.cauchySeq⟩

theorem s21k2_w09_cauchy_subseq_fin {L K : ℝ} (hL : 0 ≤ L) {ι : Type*} (s : Finset ι)
    (u : ℕ → ι → HRS.Euc d → ℝ)
    (hcont : ∀ n i, Continuous (u n i)) (hcs : ∀ n i, HasCompactSupport (u n i))
    (hsupp : ∀ n i, tsupport (u n i) ⊆ Metric.closedBall 0 L) (hL2 : ∀ n i, ∫ x, u n i x ^ 2 ≤ K)
    (hs : ∀ n i, HRS.PDE.ToolboxRd.MemSobolev (1 : ℝ) (u n i))
    (hK : ∀ n i, ∫ ξ, (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (1 : ℝ) * ‖fourierL2 (u n i) ξ‖ ^ 2 ≤ K) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ i ∈ s, ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      ∫ x, (u (σ m) i x - u (σ n) i x) ^ 2 < ε := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨id, strictMono_id, by simp⟩
  | insert a s ha ih =>
    obtain ⟨σ, hσ, hc⟩ := ih
    obtain ⟨τ, hτ, hcτ⟩ := s21k2_w09_cauchy_subseq hL (fun n => u (σ n) a) (fun n => hcont _ _)
      (fun n => hcs _ _) (fun n => hsupp _ _) (fun n => hL2 _ _) (fun n => hs _ _) (fun n => hK _ _)
    refine ⟨σ ∘ τ, hσ.comp hτ, ?_⟩
    intro i hi ε hε
    rcases Finset.mem_insert.1 hi with rfl | his
    · obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hcτ (Real.sqrt ε) (Real.sqrt_pos.2 hε)
      refine ⟨N, fun m hm n hn => ?_⟩
      have h := hN m hm n hn
      have e := s21k2_w09_lp_dist (hcont (σ (τ m)) i) (hcs (σ (τ m)) i) (hcont (σ (τ n)) i) (hcs (σ (τ n)) i)
      show ∫ x, (u (σ (τ m)) i x - u (σ (τ n)) i x) ^ 2 < ε
      rw [← e]
      calc _ < Real.sqrt ε ^ 2 := pow_lt_pow_left₀ h dist_nonneg two_ne_zero
        _ = ε := Real.sq_sqrt hε.le
    · obtain ⟨N, hN⟩ := hc i his ε hε
      exact ⟨N, fun m hm n hn => hN (τ m) (hm.trans (hτ.id_le m)) (τ n) (hn.trans (hτ.id_le n))⟩

end HRS.MS.R26T3
