import HRS.MC.WinJSpecDefs
import HRS.MC.WinJP7

/-!
# WJ8: P8 `p8_series_diff`, P9 `p9_L1_diff` (difference series, `L¹` extension)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.WinJ

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.E214Plan HRS.MC.Sec7.PID HRS.MC.E213U3 HRS.MC.Sec7.S7PIDS

section P8

variable {d : ℕ}

set_option maxSynthPendingDepth 3

/-- evaluation of a `CovEval` tensor in the form of the series terms -/
lemma p_wj8_cov_F (Rb : Regime d) (r m T : ℝ) (zr : ℝ → NegSobolev d r) (a b : ℝ) (ha : 0 ≤ a)
    (hbT : b ≤ T) (p q : ℝ → ℝ) (pr : NonzeroLattice d × NonzeroLattice d)
    (hpq : ∀ u ∈ Set.Icc (0 : ℝ) T, p u * q u = NegSobolev.eval
      (NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k) : NegSobolev d m)
        (gradProd pr.1 pr.2))
    (τ : TensorDual (PathSpace d m T) 2) (hτ : CovEval Rb m T p q a b pr.1 pr.2 τ) :
    ∀ (ta tb : ℝ) (φa φb : Torus d → ℝ) (l₁ l₂ : StrongDual ℝ (PathSpace d m T)),
      Torus.IsSmooth φa → Torus.IsSmooth φb →
      ta ∈ Set.Icc (0 : ℝ) T → tb ∈ Set.Icc (0 : ℝ) T →
      (∀ w, l₁ w = NegSobolev.eval (pathAt w ta) φa) → (∀ w, l₂ w = NegSobolev.eval (pathAt w tb) φb) →
      τ (prodForm l₁ l₂) = ∫ u in Set.Ioc a b ∩ Set.Icc 0 (min ta tb),
        Fterm Rb r m zr ta tb φa φb pr u := by
  intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
  rw [hτ.2 ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂]
  refine setIntegral_congr_fun (measurableSet_Ioc.inter measurableSet_Icc) fun u hu => ?_
  have := hpq u ⟨hu.2.1, hu.1.2.trans hbT⟩
  beta_reduce
  unfold Fterm
  rw [this]

/-- a summable family of tensors with the right evaluations sums to an `SJ` tensor -/
lemma p_wj8_sumSJ (Rb : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (m : ℝ)
    (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) (zr : ℝ → NegSobolev d r) (hzr : Measurable zr)
    (M : ℝ) (hM : ∀ u ∈ Set.Icc (0 : ℝ) T, ‖zr u‖ ≤ M) (a b : ℝ) (ha : 0 ≤ a) (hbT : b ≤ T)
    (w : NonzeroLattice d × NonzeroLattice d → ℝ) (hw : Summable w)
    (τ : NonzeroLattice d × NonzeroLattice d → TensorDual (PathSpace d m T) 2)
    (hτm : ∀ pr, τ pr ∈ projTensor (PathSpace d m T) 2) (hτn : ∀ pr, ‖τ pr‖ ≤ w pr)
    (hτe : ∀ pr, ∀ (ta tb : ℝ) (φa φb : Torus d → ℝ) (l₁ l₂ : StrongDual ℝ (PathSpace d m T)),
      Torus.IsSmooth φa → Torus.IsSmooth φb →
      ta ∈ Set.Icc (0 : ℝ) T → tb ∈ Set.Icc (0 : ℝ) T →
      (∀ w, l₁ w = NegSobolev.eval (pathAt w ta) φa) → (∀ w, l₂ w = NegSobolev.eval (pathAt w tb) φb) →
      τ pr (prodForm l₁ l₂) = ∫ u in Set.Ioc a b ∩ Set.Icc 0 (min ta tb),
        Fterm Rb r m zr ta tb φa φb pr u) :
    SJ Rb r m T zr (Set.Ioc a b) ((2 * Rb.D.invβ) • ∑' pr, τ pr) := by
  classical
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hrm : r ≤ m := by rw [hr]; linarith
  obtain ⟨Cg, -, hCg⟩ := HRS.MC.Sec7.S7PIDR.s7_PID_gradprod_proof (d := d) r hr0
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hT.le⟩)
  have hsumN : Summable fun pr => ‖τ pr‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hτn hw
  have hS : HasSum τ (∑' pr, τ pr) := (Summable.of_norm hsumN).hasSum
  have hcl : IsClosed (projTensor (PathSpace d m T) 2 : Set (TensorDual (PathSpace d m T) 2)) := by
    unfold projTensor
    exact Submodule.isClosed_topologicalClosure _
  have hSmem : (∑' pr, τ pr) ∈ projTensor (PathSpace d m T) 2 :=
    hcl.mem_of_tendsto hS
      (Filter.Eventually.of_forall fun s => Submodule.sum_mem _ fun pr _ => hτm pr)
  refine ⟨Submodule.smul_mem _ _ hSmem, ?_⟩
  intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
  obtain ⟨H, hHs, hH0, hHb⟩ := u3_term_bound Rb r hr m hm T hT ta tb hta htb φa φb hφa hφb
  set S : Set ℝ := Set.Ioc a b ∩ Set.Icc 0 (min ta tb) with hSdef
  have hSm : MeasurableSet S := measurableSet_Ioc.inter measurableSet_Icc
  have hSsub : S ⊆ Set.Ioc 0 T := fun u hu => ⟨lt_of_le_of_lt ha hu.1.1, hu.1.2.trans hbT⟩
  have hSa : ∀ u ∈ S, u ≤ ta := fun u hu => hu.2.2.trans (min_le_left _ _)
  have hSb : ∀ u ∈ S, u ≤ tb := fun u hu => hu.2.2.trans (min_le_right _ _)
  have hFm : ∀ pr, AEStronglyMeasurable (fun u => Fterm Rb r m zr ta tb φa φb pr u)
      (volume.restrict S) := by
    intro pr
    obtain ⟨hmemS, -⟩ := hCg pr.1 pr.2
    unfold Fterm
    exact ((S7PIDS_meas_eval hrm hmemS hzr).aestronglyMeasurable.mul
      (S7PIDS_meas_V Rb m hm T hT hφa hta pr.1 hSm hSsub hSa)).mul
      (S7PIDS_meas_V Rb m hm T hT hφb htb pr.2 hSm hSsub hSb)
  have hFb : ∀ pr, ∀ u ∈ S, ‖Fterm Rb r m zr ta tb φa φb pr u‖ ≤ M * H pr := by
    intro pr u hu
    rw [Real.norm_eq_abs]
    refine (hHb zr u hu.2.1 (hSa u hu) (hSb u hu) pr).trans ?_
    exact mul_le_mul_of_nonneg_right (hM u ⟨hu.2.1, (hSsub hu).2⟩) (hH0 pr)
  haveI : IsFiniteMeasure (volume.restrict S) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    refine lt_of_le_of_lt (measure_mono Set.inter_subset_left) ?_
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hFae : ∀ pr, ∀ᵐ u ∂(volume.restrict S), ‖Fterm Rb r m zr ta tb φa φb pr u‖ ≤ M * H pr :=
    fun pr => (ae_restrict_iff' hSm).2 (Filter.Eventually.of_forall fun u hu => hFb pr u hu)
  have hFint : ∀ pr, Integrable (fun u => Fterm Rb r m zr ta tb φa φb pr u) (volume.restrict S) :=
    fun pr => Integrable.mono' (integrable_const _) (hFm pr) (hFae pr)
  have hFsum : Summable fun pr => ∫ u, ‖Fterm Rb r m zr ta tb φa φb pr u‖ ∂(volume.restrict S) := by
    refine Summable.of_nonneg_of_le (fun pr => integral_nonneg fun u => norm_nonneg _)
      (fun pr => ?_) ((hHs.mul_left M).mul_right ((volume.restrict S).real Set.univ))
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le_const (by
      filter_upwards [hFae pr] with u hu
      rw [norm_norm]
      exact hu)
  have key := hasSum_integral_of_summable_integral_norm hFint hFsum
  have H2 : HasSum (fun pr => τ pr (prodForm l₁ l₂)) ((∑' pr, τ pr) (prodForm l₁ l₂)) :=
    hS.mapL (ContinuousLinearMap.apply ℝ ℝ (prodForm l₁ l₂))
  have H3 : HasSum (fun pr => τ pr (prodForm l₁ l₂))
      (∫ u in S, ∑' pr, Fterm Rb r m zr ta tb φa φb pr u) := by
    have : (fun pr => τ pr (prodForm l₁ l₂)) =
        fun pr => ∫ u in S, Fterm Rb r m zr ta tb φa φb pr u :=
      funext fun pr => hτe pr ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
    rw [this]
    exact key
  have hEq := H2.unique H3
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul, hEq]
  rfl

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m}

set_option maxHeartbeats 1600000 in
set_option maxSynthPendingDepth 3 in
theorem p8_series_diff (sd : StatDatum S β₀ m hE) (T : ℝ) (hT : 0 < T) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ (b₀ : ℝ) (hb₀ : 0 ≤ b₀) (zr : ℝ → NegSobolev d (rLvl d)), Measurable zr →
      ∀ M : ℝ, (∀ u ∈ Set.Icc (0 : ℝ) T, ‖zr u‖ ≤ M) → ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T →
      ∃ J J' : TensorDual (PathSpace d m T) 2,
        SJ (Rp sd b₀ hb₀) (rLvl d) m T zr (Set.Ioc a b) J ∧ SJ (Rs sd b₀ hb₀) (rLvl d) m T zr (Set.Ioc a b) J' ∧
        ‖J - J'‖ ≤ C * M * (b - a) * Real.exp (-κ * b₀) := by
  classical
  obtain ⟨K, κ, hK, hκ, h7⟩ := p7_cov_diff sd T hT
  have hm : 3 * (d : ℝ) + 8 < m := hE.m_gt
  have hms : 3 * (d : ℝ) + 8 < m := sd.hEs.m_gt
  obtain ⟨K1, hK1, hc1⟩ := HRS.MC.E213M.e213m_cov (regime S β₀ hE) m hm T hT
  obtain ⟨K2, hK2, hc2⟩ := HRS.MC.E213M.e213m_cov (regime sd.Ss S.β sd.hEs) m hms T hT
  have hr : rLvl d = 2 * (d : ℝ) + 6 := rfl
  set r : ℝ := rLvl d with hrdef
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hrm : r ≤ m := by rw [hr]; linarith
  have hmr : (d : ℝ) < m - r - 2 := by rw [hr]; linarith
  obtain ⟨Cg, hCg0, hCg⟩ := HRS.MC.Sec7.S7PIDR.s7_PID_gradprod_proof (d := d) r hr0
  obtain ⟨g, hgdef⟩ : ∃ g : NonzeroLattice d → ℝ, ∀ k, g k = Lattice.jp k.1 ^ (-(m - r - 2)) :=
    ⟨fun k => Lattice.jp k.1 ^ (-(m - r - 2)), fun _ => rfl⟩
  have hg0 : ∀ k, 0 ≤ g k := fun k => by rw [hgdef]; exact Real.rpow_nonneg (Torus.jp_pos k.1).le _
  have hg : Summable g := by
    have h := summable_jp_rpow (d := d) ((m - r - 2) / 2) (by linarith)
    refine h.congr fun k => ?_
    rw [hgdef]
    congr 1
    ring
  have hgg : Summable fun pr : NonzeroLattice d × NonzeroLattice d => g pr.1 * g pr.2 :=
    Summable.mul_of_nonneg hg hg (fun k => hg0 k) (fun k => hg0 k)
  obtain ⟨Gs, hGs⟩ : ∃ G : ℝ, G = ∑' pr : NonzeroLattice d × NonzeroLattice d, g pr.1 * g pr.2 :=
    ⟨_, rfl⟩
  have hGs0 : 0 ≤ Gs := by
    rw [hGs]; exact tsum_nonneg fun pr => mul_nonneg (hg0 _) (hg0 _)
  refine ⟨2 * |(regime S β₀ hE).D.invβ| * K * Cg * Gs, κ, by positivity, hκ, ?_⟩
  intro b₀ hb₀ zr hzr M hM a b ha hab hbT
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hT.le⟩)
  have hex : ∀ pr : NonzeroLattice d × NonzeroLattice d,
      ∃ τ τ' : TensorDual (PathSpace d m T) 2,
        τ ∈ projTensor (PathSpace d m T) 2 ∧ τ' ∈ projTensor (PathSpace d m T) 2 ∧
        ‖τ‖ ≤ K1 * Cg * M * (b - a) * (g pr.1 * g pr.2) ∧
        ‖τ'‖ ≤ K2 * Cg * M * (b - a) * (g pr.1 * g pr.2) ∧
        ‖τ - τ'‖ ≤ K * Real.exp (-κ * b₀) * Cg * M * (b - a) * (g pr.1 * g pr.2) ∧
        (∀ (ta tb : ℝ) (φa φb : Torus d → ℝ) (l₁ l₂ : StrongDual ℝ (PathSpace d m T)),
          Torus.IsSmooth φa → Torus.IsSmooth φb →
          ta ∈ Set.Icc (0 : ℝ) T → tb ∈ Set.Icc (0 : ℝ) T →
          (∀ w, l₁ w = NegSobolev.eval (pathAt w ta) φa) →
          (∀ w, l₂ w = NegSobolev.eval (pathAt w tb) φb) →
          τ (prodForm l₁ l₂) = ∫ u in Set.Ioc a b ∩ Set.Icc 0 (min ta tb),
            Fterm (Rp sd b₀ hb₀) r m zr ta tb φa φb pr u) ∧
        (∀ (ta tb : ℝ) (φa φb : Torus d → ℝ) (l₁ l₂ : StrongDual ℝ (PathSpace d m T)),
          Torus.IsSmooth φa → Torus.IsSmooth φb →
          ta ∈ Set.Icc (0 : ℝ) T → tb ∈ Set.Icc (0 : ℝ) T →
          (∀ w, l₁ w = NegSobolev.eval (pathAt w ta) φa) →
          (∀ w, l₂ w = NegSobolev.eval (pathAt w tb) φb) →
          τ' (prodForm l₁ l₂) = ∫ u in Set.Ioc a b ∩ Set.Icc 0 (min ta tb),
            Fterm (Rs sd b₀ hb₀) r m zr ta tb φa φb pr u) := by
    intro pr
    obtain ⟨hmemS, hnormS⟩ := hCg pr.1 pr.2
    obtain ⟨B, hB⟩ : ∃ B : ℝ, B = M * (Cg * Lattice.jp pr.1.1 ^ (r + 1) * Lattice.jp pr.2.1 ^ (r + 1)) :=
      ⟨_, rfl⟩
    have hB0 : 0 ≤ B := by
      rw [hB]
      exact mul_nonneg hM0 (mul_nonneg (mul_nonneg hCg0 (Real.rpow_nonneg (Torus.jp_pos _).le _))
        (Real.rpow_nonneg (Torus.jp_pos _).le _))
    obtain ⟨Ai, hAi⟩ : ∃ Ai : ℝ → ℝ, Ai = (Set.Icc (0 : ℝ) T).indicator (fun u => NegSobolev.eval
        (NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k) : NegSobolev d m)
          (gradProd pr.1 pr.2)) := ⟨_, rfl⟩
    have hmeasA : Measurable fun u => NegSobolev.eval
        (NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k) : NegSobolev d m)
          (gradProd pr.1 pr.2) := S7PIDS_meas_eval hrm hmemS hzr
    have hAimeas : Measurable Ai := by rw [hAi]; exact hmeasA.indicator measurableSet_Icc
    have hAibd : ∀ u, |Ai u| ≤ B := by
      intro u
      by_cases hu : u ∈ Set.Icc (0 : ℝ) T
      · rw [hAi, Set.indicator_of_mem hu, hB]
        exact S7PIDS_bound_eval hrm hmemS hnormS (hM u hu)
      · rw [hAi, Set.indicator_of_notMem hu, abs_zero]; exact hB0
    obtain ⟨p, q, hp, hq, hpb, hqb, hpq⟩ := S7PIDS_pq hAimeas hAibd
    have hpq' : ∀ u ∈ Set.Icc (0 : ℝ) T, p u * q u = NegSobolev.eval
        (NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k) : NegSobolev d m)
          (gradProd pr.1 pr.2) := by
      intro u hu
      rw [hpq u, hAi, Set.indicator_of_mem hu]
    obtain ⟨τ, τ', hτc, hτ'c, hdiff⟩ := h7 b₀ hb₀ p q (Real.sqrt B) (Real.sqrt B) hp hq hpb hqb a b ha hab
      hbT pr.1 pr.2
    obtain ⟨τ0, hτ0m, hτ0n, hτ0e⟩ := hc1 b₀ hb₀ p q (Real.sqrt B) (Real.sqrt B) hp hq hpb hqb a b ha hab
      hbT pr.1 pr.2
    obtain ⟨τ0', hτ0'm, hτ0'n, hτ0'e⟩ := hc2 b₀ hb₀ p q (Real.sqrt B) (Real.sqrt B) hp hq hpb hqb a b ha
      hab hbT pr.1 pr.2
    have hτeq : τ = τ0 := u3_eq_of_eval (Rp sd b₀ hb₀) m T hτc.1 hτ0m
      (fun ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂ =>
        (hτc.2 ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂).trans
          (hτ0e ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂).symm)
    have hτ'eq : τ' = τ0' := u3_eq_of_eval (Rs sd b₀ hb₀) m T hτ'c.1 hτ0'm
      (fun ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂ =>
        (hτ'c.2 ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂).trans
          (hτ0'e ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂).symm)
    have hs : Real.sqrt B * Real.sqrt B = B := Real.mul_self_sqrt hB0
    have e1 : Lattice.jp pr.1.1 ^ (r + 1) * Lattice.jp pr.1.1 ^ (-(m - 1)) = g pr.1 := by
      rw [← Real.rpow_add (Torus.jp_pos _), hgdef]; congr 1; ring
    have e2 : Lattice.jp pr.2.1 ^ (r + 1) * Lattice.jp pr.2.1 ^ (-(m - 1)) = g pr.2 := by
      rw [← Real.rpow_add (Torus.jp_pos _), hgdef]; congr 1; ring
    have hconv : ∀ c : ℝ, c * Real.sqrt B * Real.sqrt B * Lattice.jp pr.1.1 ^ (-(m - 1)) *
        Lattice.jp pr.2.1 ^ (-(m - 1)) * (b - a) = c * Cg * M * (b - a) * (g pr.1 * g pr.2) := by
      intro c
      calc c * Real.sqrt B * Real.sqrt B * Lattice.jp pr.1.1 ^ (-(m - 1)) *
            Lattice.jp pr.2.1 ^ (-(m - 1)) * (b - a)
          = c * (Real.sqrt B * Real.sqrt B) * Lattice.jp pr.1.1 ^ (-(m - 1)) *
            Lattice.jp pr.2.1 ^ (-(m - 1)) * (b - a) := by ring
        _ = c * B * Lattice.jp pr.1.1 ^ (-(m - 1)) * Lattice.jp pr.2.1 ^ (-(m - 1)) * (b - a) := by
            rw [hs]
        _ = c * Cg * M * (b - a) * ((Lattice.jp pr.1.1 ^ (r + 1) * Lattice.jp pr.1.1 ^ (-(m - 1))) *
            (Lattice.jp pr.2.1 ^ (r + 1) * Lattice.jp pr.2.1 ^ (-(m - 1)))) := by rw [hB]; ring
        _ = c * Cg * M * (b - a) * (g pr.1 * g pr.2) := by rw [e1, e2]
    refine ⟨τ, τ', hτc.1, hτ'c.1, ?_, ?_, ?_,
      p_wj8_cov_F (Rp sd b₀ hb₀) r m T zr a b ha hbT p q pr hpq' τ hτc,
      p_wj8_cov_F (Rs sd b₀ hb₀) r m T zr a b ha hbT p q pr hpq' τ' hτ'c⟩
    · rw [hτeq, ← hconv K1]; exact hτ0n
    · rw [hτ'eq, ← hconv K2]; exact hτ0'n
    · have := hdiff
      rw [show K * Real.sqrt B * Real.sqrt B * Real.exp (-κ * b₀) * Lattice.jp pr.1.1 ^ (-(m - 1)) *
          Lattice.jp pr.2.1 ^ (-(m - 1)) * (b - a) =
          (K * Real.exp (-κ * b₀)) * Real.sqrt B * Real.sqrt B * Lattice.jp pr.1.1 ^ (-(m - 1)) *
          Lattice.jp pr.2.1 ^ (-(m - 1)) * (b - a) by ring, hconv] at this
      exact this
  choose τ τ' hτm hτ'm hτn hτ'n hdn hτe hτ'e using hex
  have hs1 : Summable fun pr : NonzeroLattice d × NonzeroLattice d =>
      K1 * Cg * M * (b - a) * (g pr.1 * g pr.2) := hgg.mul_left _
  have hs2 : Summable fun pr : NonzeroLattice d × NonzeroLattice d =>
      K2 * Cg * M * (b - a) * (g pr.1 * g pr.2) := hgg.mul_left _
  have hs3 : Summable fun pr : NonzeroLattice d × NonzeroLattice d =>
      K * Real.exp (-κ * b₀) * Cg * M * (b - a) * (g pr.1 * g pr.2) := hgg.mul_left _
  refine ⟨(2 * (Rp sd b₀ hb₀).D.invβ) • ∑' pr, τ pr, (2 * (Rs sd b₀ hb₀).D.invβ) • ∑' pr, τ' pr,
    p_wj8_sumSJ (Rp sd b₀ hb₀) r hr m hm T hT zr hzr M hM a b ha hbT _ hs1 τ hτm hτn hτe,
    p_wj8_sumSJ (Rs sd b₀ hb₀) r hr m hms T hT zr hzr M hM a b ha hbT _ hs2 τ' hτ'm hτ'n hτ'e, ?_⟩
  have hinv : (Rs sd b₀ hb₀).D.invβ = (Rp sd b₀ hb₀).D.invβ := by
    show (regime sd.Ss S.β sd.hEs).D.invβ = (regime S β₀ hE).D.invβ
    rw [sd.hD]
  have hsN1 : Summable fun pr => ‖τ pr‖ := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hτn hs1
  have hsN2 : Summable fun pr => ‖τ' pr‖ := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hτ'n hs2
  have hsN3 : Summable fun pr => ‖τ pr - τ' pr‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hdn hs3
  rw [hinv, ← smul_sub, ← (Summable.of_norm hsN1).tsum_sub (Summable.of_norm hsN2), norm_smul]
  have h1 : ‖∑' pr, (τ pr - τ' pr)‖ ≤
      (K * Real.exp (-κ * b₀) * Cg * M * (b - a)) * Gs := by
    refine (norm_tsum_le_tsum_norm hsN3).trans ?_
    calc ∑' pr, ‖τ pr - τ' pr‖ ≤ ∑' pr : NonzeroLattice d × NonzeroLattice d,
          (K * Real.exp (-κ * b₀) * Cg * M * (b - a)) * (g pr.1 * g pr.2) :=
          hsN3.tsum_le_tsum hdn (hgg.mul_left _)
      _ = (K * Real.exp (-κ * b₀) * Cg * M * (b - a)) * Gs := by rw [tsum_mul_left, hGs]
  have h2 : ‖2 * (Rp sd b₀ hb₀).D.invβ‖ = 2 * |(regime S β₀ hE).D.invβ| := by
    rw [Real.norm_eq_abs, abs_mul, abs_two]
    rfl
  rw [h2]
  calc 2 * |(regime S β₀ hE).D.invβ| * ‖∑' pr, (τ pr - τ' pr)‖
      ≤ 2 * |(regime S β₀ hE).D.invβ| * ((K * Real.exp (-κ * b₀) * Cg * M * (b - a)) * Gs) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 * |(regime S β₀ hE).D.invβ| * K * Cg * Gs * M * (b - a) * Real.exp (-κ * b₀) := by ring

end P8

section P9

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m}

set_option maxSynthPendingDepth 3

/-- the bounded-coefficient statement `p8_series_diff` at horizon `G`, with named constants -/
def p_wj8_P8Stmt (sd : StatDatum S β₀ m hE) (G C κ : ℝ) : Prop :=
  ∀ (b₀ : ℝ) (hb₀ : 0 ≤ b₀) (zr : ℝ → NegSobolev d (rLvl d)), Measurable zr →
    ∀ M : ℝ, (∀ u ∈ Set.Icc (0 : ℝ) G, ‖zr u‖ ≤ M) → ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ G →
    ∃ J J' : TensorDual (PathSpace d m G) 2,
      SJ (Rp sd b₀ hb₀) (rLvl d) m G zr (Set.Ioc a b) J ∧ SJ (Rs sd b₀ hb₀) (rLvl d) m G zr (Set.Ioc a b) J' ∧
      ‖J - J'‖ ≤ C * M * (b - a) * Real.exp (-κ * b₀)

/-- one cell for the difference -/
lemma p_wj8_cell (sd : StatDatum S β₀ m hE) (G : ℝ) (hG : 0 < G) (C κ : ℝ) (h8 : p_wj8_P8Stmt sd G C κ) :
    ∀ (b₀ : ℝ) (hb₀ : 0 ≤ b₀) (g : ℝ → NegSobolev d (rLvl d)), Measurable g → ∀ M : ℝ,
      (∀ u ∈ Set.Icc (0 : ℝ) G, ‖g u‖ ≤ M) → ∀ (x : NegSobolev d (rLvl d)) (ε : ℝ), 0 ≤ ε →
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ G → (∀ u ∈ Set.Ioc a b, ‖g u - x‖ ≤ ε) →
      ∃ J J' : TensorDual (PathSpace d m G) 2,
        SJ (Rp sd b₀ hb₀) (rLvl d) m G g (Set.Ioc a b) J ∧ SJ (Rs sd b₀ hb₀) (rLvl d) m G g (Set.Ioc a b) J' ∧
        ‖J - J'‖ ≤ C * Real.exp (-κ * b₀) * (‖x‖ + ε) * (b - a) := by
  classical
  intro b₀ hb₀ g hg M hM x ε hε a b ha hab hbG hgx
  have hr : rLvl d = 2 * (d : ℝ) + 6 := rfl
  have hmp : 3 * (d : ℝ) + 8 < m := hE.m_gt
  have hms : 3 * (d : ℝ) + 8 < m := sd.hEs.m_gt
  have hsub : Set.Ioc a b ⊆ Set.Ioc 0 G := fun u hu => ⟨lt_of_le_of_lt ha hu.1, hu.2.trans hbG⟩
  obtain ⟨Jg, Jg', hJg, hJg', -⟩ := h8 b₀ hb₀ g hg M hM a b ha hab hbG
  obtain ⟨Jx, Jx', hJx, hJx', hJxn⟩ := h8 b₀ hb₀ (fun _ => x) measurable_const ‖x‖
    (fun u _ => le_rfl) a b ha hab hbG
  set z' : ℝ → NegSobolev d (rLvl d) := fun u => if u ∈ Set.Ioc a b then g u - x else 0 with hz'
  have hz'm : Measurable z' := by
    refine Measurable.ite measurableSet_Ioc (hg.sub measurable_const) measurable_const
  have hz'b : ∀ u ∈ Set.Icc (0 : ℝ) G, ‖z' u‖ ≤ ε := by
    intro u _
    by_cases hu : u ∈ Set.Ioc a b
    · simp only [hz', if_pos hu]; exact hgx u hu
    · simp only [hz', if_neg hu, norm_zero]; exact hε
  obtain ⟨Jz, Jz', hJz, hJz', hJzn⟩ := h8 b₀ hb₀ z' hz'm ε hz'b a b ha hab hbG
  have hcx : ∀ Rb : Regime d, 3 * (d : ℝ) + 8 < m → ∀ (Jg Jx Jz : TensorDual (PathSpace d m G) 2),
      SJ Rb (rLvl d) m G g (Set.Ioc a b) Jg → SJ Rb (rLvl d) m G (fun _ => x) (Set.Ioc a b) Jx →
      SJ Rb (rLvl d) m G z' (Set.Ioc a b) Jz → Jg - Jx = Jz := by
    intro Rb hmR Jg Jx Jz hJg hJx hJz
    have hdiff : SJ Rb (rLvl d) m G (fun v => g v - (fun _ => x) v) (Set.Ioc a b) (Jg - Jx) :=
      u3_SJ_sub Rb (rLvl d) hr m hmR G hG measurableSet_Ioc hJg hJx
        (u3_intOK_bdd Rb (rLvl d) hr m hmR G hG hg hM measurableSet_Ioc hsub)
        (u3_intOK_bdd Rb (rLvl d) hr m hmR G hG (measurable_const : Measurable fun _ : ℝ => x)
          (fun u _ => le_rfl : ∀ u ∈ Set.Icc (0 : ℝ) G, ‖(fun _ : ℝ => x) u‖ ≤ ‖x‖)
          measurableSet_Ioc hsub)
    have hdiff' : SJ Rb (rLvl d) m G z' (Set.Ioc a b) (Jg - Jx) :=
      u3_SJ_congr Rb (rLvl d) m G measurableSet_Ioc (fun u hu _ => by simp only [hz', if_pos hu]) hdiff
    exact u3_SJ_unique Rb (rLvl d) m G hdiff' hJz
  have e1 := hcx (Rp sd b₀ hb₀) hmp Jg Jx Jz hJg hJx hJz
  have e2 := hcx (Rs sd b₀ hb₀) hms Jg' Jx' Jz' hJg' hJx' hJz'
  refine ⟨Jg, Jg', hJg, hJg', ?_⟩
  have hba : 0 ≤ b - a := sub_nonneg.2 hab
  have hJe : Jg - Jg' = (Jx - Jx') + (Jz - Jz') := by
    have h1 : Jg = Jx + Jz := by rw [← e1]; abel
    have h2 : Jg' = Jx' + Jz' := by rw [← e2]; abel
    rw [h1, h2]; abel
  calc ‖Jg - Jg'‖ = ‖(Jx - Jx') + (Jz - Jz')‖ := by rw [hJe]
    _ ≤ ‖Jx - Jx'‖ + ‖Jz - Jz'‖ := norm_add_le _ _
    _ ≤ C * ‖x‖ * (b - a) * Real.exp (-κ * b₀) + C * ε * (b - a) * Real.exp (-κ * b₀) :=
        add_le_add hJxn hJzn
    _ = C * Real.exp (-κ * b₀) * (‖x‖ + ε) * (b - a) := by ring

/-- the `L¹` bound for continuous coefficients, difference version (the Riemann-cell induction of `u3_cont_L1`) -/
lemma p_wj8_cont (sd : StatDatum S β₀ m hE) (G : ℝ) (hG : 0 < G) (C κ : ℝ) (hC0 : 0 ≤ C)
    (h8 : p_wj8_P8Stmt sd G C κ) :
    ∀ (b₀ : ℝ) (hb₀ : 0 ≤ b₀) (g : ℝ → NegSobolev d (rLvl d)), Continuous g →
      ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ G →
      ∃ J J' : TensorDual (PathSpace d m G) 2,
        SJ (Rp sd b₀ hb₀) (rLvl d) m G g (Set.Ioc α β) J ∧ SJ (Rs sd b₀ hb₀) (rLvl d) m G g (Set.Ioc α β) J' ∧
        ‖J - J'‖ ≤ C * Real.exp (-κ * b₀) * ∫ u in Set.Ioc α β, ‖g u‖ := by
  classical
  have hcell := p_wj8_cell sd G hG C κ h8
  have hr : rLvl d = 2 * (d : ℝ) + 6 := rfl
  have hmp : 3 * (d : ℝ) + 8 < m := hE.m_gt
  have hms : 3 * (d : ℝ) + 8 < m := sd.hEs.m_gt
  intro b₀ hb₀ g hg α β hα hαβ hβG
  set Cb : ℝ := C * Real.exp (-κ * b₀) with hCb
  have hCb0 : 0 ≤ Cb := mul_nonneg hC0 (Real.exp_pos _).le
  set Rq := Rp sd b₀ hb₀ with hRq
  set Rt := Rs sd b₀ hb₀ with hRt
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) G)).exists_bound_of_continuousOn hg.continuousOn
  have hgm : Measurable g := hg.measurable
  have hsubG : ∀ a b : ℝ, 0 ≤ a → b ≤ G → Set.Ioc a b ⊆ Set.Ioc 0 G :=
    fun a b ha hb u hu => ⟨lt_of_le_of_lt ha hu.1, hu.2.trans hb⟩
  have hintg : ∀ a b : ℝ, 0 ≤ a → b ≤ G → IntegrableOn (fun u => ‖g u‖) (Set.Ioc a b) :=
    fun a b ha hb => u3_integrableOn_bdd hgm hM measurableSet_Ioc (hsubG a b ha hb)
  have hclaim : ∀ ε : ℝ, 0 < ε → ∃ J J' : TensorDual (PathSpace d m G) 2,
      SJ Rq (rLvl d) m G g (Set.Ioc α β) J ∧ SJ Rt (rLvl d) m G g (Set.Ioc α β) J' ∧
      ‖J - J'‖ ≤ Cb * (∫ u in Set.Ioc α β, ‖g u‖) + 2 * Cb * ε * (β - α) := by
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuousOn_iff.1
      ((isCompact_Icc : IsCompact (Set.Icc α β)).uniformContinuousOn_of_continuous hg.continuousOn) ε hε
    obtain ⟨n, hn⟩ : ∃ n : ℕ, 0 < n ∧ (β - α) / n < δ := by
      refine ⟨⌈(β - α) / δ⌉₊ + 1, Nat.succ_pos _, ?_⟩
      have h1 : (β - α) / δ ≤ ⌈(β - α) / δ⌉₊ := Nat.le_ceil _
      have h2 : (β - α) / δ < ((⌈(β - α) / δ⌉₊ + 1 : ℕ) : ℝ) := by
        push_cast; linarith
      have hn0 : (0 : ℝ) < ((⌈(β - α) / δ⌉₊ + 1 : ℕ) : ℝ) := by positivity
      rw [div_lt_iff₀ hn0]
      rw [div_lt_iff₀ hδ] at h2
      linarith
    obtain ⟨hnpos, hnδ⟩ := hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    set h : ℝ := (β - α) / n with hh
    have hh0 : 0 ≤ h := div_nonneg (sub_nonneg.2 hαβ) hnR.le
    have hnh : (n : ℝ) * h = β - α := by rw [hh]; field_simp
    have key : ∀ k : ℕ, k ≤ n → ∃ J J' : TensorDual (PathSpace d m G) 2,
        SJ Rq (rLvl d) m G g (Set.Ioc α (α + k * h)) J ∧ SJ Rt (rLvl d) m G g (Set.Ioc α (α + k * h)) J' ∧
        ‖J - J'‖ ≤ Cb * (∫ u in Set.Ioc α (α + k * h), ‖g u‖) + 2 * Cb * ε * (k * h) := by
      intro k
      induction k with
      | zero =>
        intro _
        refine ⟨0, 0, ?_, ?_, ?_⟩
        · simpa using u3_SJ_empty Rq (rLvl d) m G g
        · simpa using u3_SJ_empty Rt (rLvl d) m G g
        · simp
      | succ k ih =>
        intro hk
        obtain ⟨J, J', hJ, hJ', hJn⟩ := ih (Nat.le_of_succ_le hk)
        set a : ℝ := α + k * h with ha
        set b : ℝ := α + ((k + 1 : ℕ) : ℝ) * h with hb
        have hkh : (k : ℝ) * h ≥ 0 := by positivity
        have hαa : α ≤ a := by rw [ha]; linarith
        have hab : a ≤ b := by rw [ha, hb]; push_cast; nlinarith
        have hk1 : ((k + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hk
        have hbβ : b ≤ β := by
          rw [hb]
          have : ((k + 1 : ℕ) : ℝ) * h ≤ n * h := mul_le_mul_of_nonneg_right hk1 hh0
          linarith
        have hba : b - a = h := by rw [ha, hb]; push_cast; ring
        have ha0 : 0 ≤ a := hα.trans hαa
        have hbG : b ≤ G := hbβ.trans hβG
        have hgx : ∀ u ∈ Set.Ioc a b, ‖g u - g a‖ ≤ ε := by
          intro u hu
          have hua : u - a ≤ h := by linarith [hu.2]
          have hu1 : u ∈ Set.Icc α β := ⟨hαa.trans hu.1.le, hu.2.trans hbβ⟩
          have ha1 : a ∈ Set.Icc α β := ⟨hαa, hab.trans hbβ⟩
          have hd : dist u a < δ := by
            rw [Real.dist_eq, abs_of_nonneg (by linarith [hu.1])]
            linarith
          have := hδε u hu1 a ha1 hd
          rw [dist_eq_norm] at this
          exact this.le
        obtain ⟨Jc, Jc', hJc, hJc', hJcn⟩ := hcell b₀ hb₀ g hgm M hM (g a) ε hε.le a b ha0 hab hbG hgx
        have hcellint : h * (‖g a‖ - ε) ≤ ∫ u in Set.Ioc a b, ‖g u‖ := by
          have h1 : ∫ u in Set.Ioc a b, (‖g a‖ - ε) ≤ ∫ u in Set.Ioc a b, ‖g u‖ := by
            refine setIntegral_mono_on (integrable_const _) (hintg a b ha0 hbG) measurableSet_Ioc ?_
            intro u hu
            have := hgx u hu
            have h2 : ‖g a‖ ≤ ‖g u‖ + ‖g u - g a‖ := by
              have := norm_sub_norm_le (g a) (g u)
              rw [norm_sub_rev] at this
              linarith [norm_sub_rev (g a) (g u)]
            linarith
          rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hab, hba] at h1
          exact h1
        have hunion : Set.Ioc α a ∪ Set.Ioc a b = Set.Ioc α b := Set.Ioc_union_Ioc_eq_Ioc hαa hab
        have hdisj : Disjoint (Set.Ioc α a) (Set.Ioc a b) := by
          refine Set.disjoint_left.2 fun x hx hx' => ?_
          exact absurd hx.2 (not_le.2 hx'.1)
        refine ⟨J + Jc, J' + Jc', ?_, ?_, ?_⟩
        · have := u3_SJ_union Rq (rLvl d) m G hdisj measurableSet_Ioc hJ hJc
            (u3_intOK_bdd Rq (rLvl d) hr m hmp G hG hgm hM measurableSet_Ioc (hsubG α a hα (hab.trans hbG)))
            (u3_intOK_bdd Rq (rLvl d) hr m hmp G hG hgm hM measurableSet_Ioc (hsubG a b ha0 hbG))
          rwa [hunion] at this
        · have := u3_SJ_union Rt (rLvl d) m G hdisj measurableSet_Ioc hJ' hJc'
            (u3_intOK_bdd Rt (rLvl d) hr m hms G hG hgm hM measurableSet_Ioc (hsubG α a hα (hab.trans hbG)))
            (u3_intOK_bdd Rt (rLvl d) hr m hms G hG hgm hM measurableSet_Ioc (hsubG a b ha0 hbG))
          rwa [hunion] at this
        · have hI : ∫ u in Set.Ioc α b, ‖g u‖ =
              (∫ u in Set.Ioc α a, ‖g u‖) + ∫ u in Set.Ioc a b, ‖g u‖ := by
            rw [← hunion]
            exact setIntegral_union hdisj measurableSet_Ioc (hintg α a hα (hab.trans hbG)) (hintg a b ha0 hbG)
          rw [hI]
          have e1 : ((k + 1 : ℕ) : ℝ) * h = k * h + h := by push_cast; ring
          have hCn : Cb * (‖g a‖ + ε) * (b - a) ≤ Cb * (∫ u in Set.Ioc a b, ‖g u‖) + 2 * Cb * ε * h := by
            rw [hba]
            nlinarith [mul_le_mul_of_nonneg_left hcellint hCb0]
          have hJcn' : ‖Jc - Jc'‖ ≤ Cb * (‖g a‖ + ε) * (b - a) := hJcn
          have hsplit : (J + Jc) - (J' + Jc') = (J - J') + (Jc - Jc') := by abel
          rw [hsplit]
          calc ‖(J - J') + (Jc - Jc')‖ ≤ ‖J - J'‖ + ‖Jc - Jc'‖ := norm_add_le _ _
            _ ≤ (Cb * (∫ u in Set.Ioc α a, ‖g u‖) + 2 * Cb * ε * (k * h)) +
                (Cb * (∫ u in Set.Ioc a b, ‖g u‖) + 2 * Cb * ε * h) := add_le_add hJn (hJcn'.trans hCn)
            _ = Cb * ((∫ u in Set.Ioc α a, ‖g u‖) + ∫ u in Set.Ioc a b, ‖g u‖) +
                2 * Cb * ε * (((k + 1 : ℕ) : ℝ) * h) := by rw [e1]; ring
    obtain ⟨J, J', hJ, hJ', hJn⟩ := key n le_rfl
    have hend : α + (n : ℝ) * h = β := by linarith
    rw [hend] at hJ hJ' hJn
    exact ⟨J, J', hJ, hJ', by rw [hnh] at hJn; exact hJn⟩
  obtain ⟨J₀, J₀', hJ₀, hJ₀', -⟩ := h8 b₀ hb₀ g hgm M hM α β hα hαβ hβG
  refine ⟨J₀, J₀', hJ₀, hJ₀', ?_⟩
  have hall : ∀ ε : ℝ, 0 < ε → ‖J₀ - J₀'‖ ≤ Cb * (∫ u in Set.Ioc α β, ‖g u‖) + ε * (2 * Cb * (β - α)) := by
    intro ε hε
    obtain ⟨J, J', hJ, hJ', hJn⟩ := hclaim ε hε
    have e1 : J = J₀ := u3_SJ_unique Rq (rLvl d) m G hJ hJ₀
    have e2 : J' = J₀' := u3_SJ_unique Rt (rLvl d) m G hJ' hJ₀'
    rw [← e1, ← e2]
    linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  by_cases hz : 2 * Cb * (β - α) = 0
  · have := hall 1 one_pos
    rw [hz] at this
    linarith
  · have hpos : 0 < 2 * Cb * (β - α) := by
      have : 0 ≤ 2 * Cb * (β - α) := by
        have := sub_nonneg.2 hαβ
        positivity
      exact lt_of_le_of_ne this (Ne.symm hz)
    have := hall (ε / (2 * Cb * (β - α))) (div_pos hε hpos)
    rwa [div_mul_cancel₀ _ hpos.ne'] at this

set_option maxHeartbeats 1600000 in
theorem p9_L1_diff (sd : StatDatum S β₀ m hE) (G : ℝ) (hG : 0 < G) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ (b₀ : ℝ) (hb₀ : 0 ≤ b₀) (zr : ℝ → NegSobolev d (rLvl d)), Measurable zr →
      ∀ α β : ℝ, 0 ≤ α → β ≤ G → IntegrableOn (fun u => ‖zr u‖) (Set.Ioc α β) →
      ∃ J J' : TensorDual (PathSpace d m G) 2,
        SJ (Rp sd b₀ hb₀) (rLvl d) m G zr (Set.Ioc α β) J ∧ SJ (Rs sd b₀ hb₀) (rLvl d) m G zr (Set.Ioc α β) J' ∧
        ‖J - J'‖ ≤ C * Real.exp (-κ * b₀) * ∫ u in Set.Ioc α β, ‖zr u‖ := by
  classical
  obtain ⟨C, κ, hC, hκ, h8⟩ := p8_series_diff sd G hG
  have h8' : p_wj8_P8Stmt sd G C κ := h8
  have hr : rLvl d = 2 * (d : ℝ) + 6 := rfl
  have hmp : 3 * (d : ℝ) + 8 < m := hE.m_gt
  have hms : 3 * (d : ℝ) + 8 < m := sd.hEs.m_gt
  obtain ⟨C1p, hC1p, hL1p⟩ := u3_L1 (regime S β₀ hE) (rLvl d) hr m hmp G hG
  obtain ⟨C1s, hC1s, hL1s⟩ := u3_L1 (regime sd.Ss S.β sd.hEs) (rLvl d) hr m hms G hG
  refine ⟨C, κ, hC, hκ, ?_⟩
  intro b₀ hb₀ zr hzr α β hα hβG hint
  set Rq := Rp sd b₀ hb₀ with hRq
  set Rt := Rs sd b₀ hb₀ with hRt
  set Cb : ℝ := C * Real.exp (-κ * b₀) with hCb
  have hCb0 : 0 ≤ Cb := mul_nonneg hC (Real.exp_pos _).le
  by_cases hαβ : α ≤ β
  swap
  · refine ⟨0, 0, ?_, ?_, ?_⟩
    · rw [Set.Ioc_eq_empty (not_lt.2 (not_le.1 hαβ).le)]
      exact u3_SJ_empty Rq (rLvl d) m G zr
    · rw [Set.Ioc_eq_empty (not_lt.2 (not_le.1 hαβ).le)]
      exact u3_SJ_empty Rt (rLvl d) m G zr
    · rw [Set.Ioc_eq_empty (not_lt.2 (not_le.1 hαβ).le)]
      simp
  have hsubG : Set.Ioc α β ⊆ Set.Ioc 0 G := fun u hu => ⟨lt_of_le_of_lt hα hu.1, hu.2.trans hβG⟩
  have hzint : IntegrableOn zr (Set.Ioc α β) :=
    (integrable_norm_iff hzr.aestronglyMeasurable).1 hint
  set f : ℝ → NegSobolev d (rLvl d) := Set.indicator (Set.Ioc α β) zr with hf
  have hfi : Integrable f := (integrable_indicator_iff measurableSet_Ioc).2 hzint
  have hex : ∀ n : ℕ, ∃ g : ℝ → NegSobolev d (rLvl d), HasCompactSupport g ∧
      (∫ x, ‖f x - g x‖) ≤ 1 / ((n : ℝ) + 1) ∧ Continuous g ∧ Integrable g :=
    fun n => hfi.exists_hasCompactSupport_integral_sub_le (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  choose g hgs hgI hgc hgi using hex
  have hdist : ∀ n, IntegrableOn (fun u => ‖zr u - g n u‖) (Set.Ioc α β) :=
    fun n => (hzint.sub (hgi n).integrableOn).norm
  have hdistb : ∀ n, (∫ u in Set.Ioc α β, ‖zr u - g n u‖) ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    have h1 : (∫ u in Set.Ioc α β, ‖f u - g n u‖) = ∫ u in Set.Ioc α β, ‖zr u - g n u‖ := by
      refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
      simp only [hf, Set.indicator_of_mem hu]
    rw [← h1]
    refine le_trans (setIntegral_le_integral ((hfi.sub (hgi n)).norm)
      (Filter.Eventually.of_forall fun u => norm_nonneg _)) (hgI n)
  have hdist0 : ∀ n, 0 ≤ ∫ u in Set.Ioc α β, ‖zr u - g n u‖ :=
    fun n => setIntegral_nonneg measurableSet_Ioc fun u _ => norm_nonneg _
  have hex2 : ∀ n, ∃ J J' : TensorDual (PathSpace d m G) 2,
      SJ Rq (rLvl d) m G (g n) (Set.Ioc α β) J ∧ SJ Rt (rLvl d) m G (g n) (Set.Ioc α β) J' ∧
      ‖J - J'‖ ≤ Cb * ∫ u in Set.Ioc α β, ‖g n u‖ :=
    fun n => p_wj8_cont sd G hG C κ hC h8' b₀ hb₀ (g n) (hgc n) α β hα hαβ hβG
  choose J J' hJ hJ' hJn using hex2
  obtain ⟨Jz, hJz, -⟩ := hL1p b₀ hb₀ zr hzr α β hα hβG hint
  obtain ⟨Jz', hJz', -⟩ := hL1s b₀ hb₀ zr hzr α β hα hβG hint
  refine ⟨Jz, Jz', hJz, hJz', ?_⟩
  have hIz : IntOK Rq (rLvl d) m G zr (Set.Ioc α β) :=
    u3_intOK Rq (rLvl d) hr m hmp G hG zr hzr measurableSet_Ioc hsubG hint
  have hIz' : IntOK Rt (rLvl d) m G zr (Set.Ioc α β) :=
    u3_intOK Rt (rLvl d) hr m hms G hG zr hzr measurableSet_Ioc hsubG hint
  -- closeness of the approximants
  have hclose : ∀ n, ‖Jz - J n‖ ≤ C1p * (1 / ((n : ℝ) + 1)) ∧ ‖Jz' - J' n‖ ≤ C1s * (1 / ((n : ℝ) + 1)) := by
    intro n
    have hzg : Measurable fun v => zr v - g n v := hzr.sub (hgc n).measurable
    have hzgi : IntegrableOn (fun u => ‖zr u - g n u‖) (Set.Ioc α β) := hdist n
    constructor
    · have hs := u3_SJ_sub Rq (rLvl d) hr m hmp G hG measurableSet_Ioc hJz (hJ n) hIz
        (u3_intOK_cont Rq (rLvl d) hr m hmp G hG (hgc n) hα hβG)
      obtain ⟨K, hK, hKn⟩ := hL1p b₀ hb₀ (fun v => zr v - g n v) hzg α β hα hβG hzgi
      have heq : Jz - J n = K := u3_SJ_unique Rq (rLvl d) m G hs hK
      rw [heq]
      exact hKn.trans (mul_le_mul_of_nonneg_left (hdistb n) hC1p)
    · have hs := u3_SJ_sub Rt (rLvl d) hr m hms G hG measurableSet_Ioc hJz' (hJ' n) hIz'
        (u3_intOK_cont Rt (rLvl d) hr m hms G hG (hgc n) hα hβG)
      obtain ⟨K, hK, hKn⟩ := hL1s b₀ hb₀ (fun v => zr v - g n v) hzg α β hα hβG hzgi
      have heq : Jz' - J' n = K := u3_SJ_unique Rt (rLvl d) m G hs hK
      rw [heq]
      exact hKn.trans (mul_le_mul_of_nonneg_left (hdistb n) hC1s)
  have hgint : ∀ n, (∫ u in Set.Ioc α β, ‖g n u‖) ≤
      (∫ u in Set.Ioc α β, ‖zr u‖) + 1 / ((n : ℝ) + 1) := by
    intro n
    have h1 : (∫ u in Set.Ioc α β, ‖g n u‖) ≤
        (∫ u in Set.Ioc α β, ‖zr u‖) + ∫ u in Set.Ioc α β, ‖zr u - g n u‖ := by
      rw [← integral_add hint (hdist n)]
      refine setIntegral_mono_on ((hgi n).integrableOn.norm) (hint.add (hdist n)) measurableSet_Ioc
        fun u _ => ?_
      calc ‖g n u‖ = ‖zr u - (zr u - g n u)‖ := by congr 1; abel
        _ ≤ ‖zr u‖ + ‖zr u - g n u‖ := norm_sub_le _ _
    linarith [hdistb n]
  have hfin : ∀ n : ℕ, ‖Jz - Jz'‖ ≤
      Cb * (∫ u in Set.Ioc α β, ‖zr u‖) + (C1p + C1s + Cb) * (1 / ((n : ℝ) + 1)) := by
    intro n
    obtain ⟨h1, h2⟩ := hclose n
    have h3 : ‖Jz - Jz'‖ ≤ ‖Jz - J n‖ + ‖J n - J' n‖ + ‖J' n - Jz'‖ := by
      calc ‖Jz - Jz'‖ = ‖(Jz - J n) + (J n - J' n) + (J' n - Jz')‖ := by congr 1; abel
        _ ≤ ‖(Jz - J n) + (J n - J' n)‖ + ‖J' n - Jz'‖ := norm_add_le _ _
        _ ≤ ‖Jz - J n‖ + ‖J n - J' n‖ + ‖J' n - Jz'‖ := by gcongr; exact norm_add_le _ _
    rw [norm_sub_rev (J' n) Jz'] at h3
    have h4 := mul_le_mul_of_nonneg_left (hgint n) hCb0
    have h5 := hJn n
    nlinarith
  have hlim : Tendsto (fun n : ℕ => Cb * (∫ u in Set.Ioc α β, ‖zr u‖) +
      (C1p + C1s + Cb) * (1 / ((n : ℝ) + 1))) atTop
      (𝓝 (Cb * (∫ u in Set.Ioc α β, ‖zr u‖))) := by
    simpa using ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      (C1p + C1s + Cb)).const_add (Cb * (∫ u in Set.Ioc α β, ‖zr u‖))
  exact ge_of_tendsto' hlim hfin

end P9

end HRS.MC.WinJ

end
