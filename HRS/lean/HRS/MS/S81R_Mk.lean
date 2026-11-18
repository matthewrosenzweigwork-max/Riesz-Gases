import HRS.MS.PoisMarkovAux2
import HRS.MS.S81R_Alg
import HRS.MS.S81R_Cls

/-!
# S81R, packet R3: the Markov property of the pathwise flow in chain form, for a random `ℱ₀`-measurable start

For a Brownian filtration `(P, ℱ, W)` and `q > 0`, `B ∈ C_b²`:
* `s81r_markov_step`: `E F(θ_a W, flow_a(z)) = E ∫ F(c, flow_a(z)) d Wiener(c)` for `ℱ₀`-measurable `z` and bounded measurable `F`
  (the general form of `HRS.MS.PoisMarkov.mk_markov_core`);
* `s81r_chain`: for sorted times `u₁ ≤ ⋯ ≤ uₙ` and test functions `fₖ ∈ s81r_S`,
  `E ∏ fₖ(flow_{uₖ}(z)) = E (foldT sg 0 L)(z)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.PoisFlow HRS.MS.PoisSg
  HRS.MS.PoisMarkov HRS.MD.EQLawPath HRS.MS.Gap

namespace HRS.MS.S81R

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {d : ℕ} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → Fin d → ℝ}

/-- `flow_c(z)` is `ℱ_c`-measurable for `ℱ_c`-measurable `z` -/
theorem s81r_measurable_V (hW : IsBrownianFiltration P ℱ W) {q Mb : ℝ} (hq : 0 ≤ q) {m : ℕ}
    (hm : 1 ≤ m) {B : Euc d → Euc d} (hB : HasCbBound m Mb B) (c : ℝ≥0) {z : Ω → Euc d}
    (hz : Measurable[ℱ c] z) :
    Measurable[ℱ c] (fun ω => flowMap q B (fun u => W u ω) (c : ℝ) (z ω)) := by
  have key : Measurable[ℱ c]
      (fun ω => flowMap q B (fun u => W (min u c) ω) (c : ℝ) (z ω)) := by
    letI : MeasurableSpace Ω := ℱ c
    have hN : SgNoise (fun (u : ℝ≥0) (ω : Ω) => W (min u c) ω) :=
      { meas := fun u => (hW.adapted (min u c)).mono
          (ℱ.mono (by exact_mod_cast min_le_right u c)) le_rfl
        cont := fun ω => (hW.cont ω).comp (continuous_id.min continuous_const)
        zero := fun ω => by simp [hW.zero ω] }
    have h1 : Measurable (fun p : Ω × Euc d =>
        flowMap q B (fun u => (fun (u : ℝ≥0) (ω : Ω) => W (min u c) ω) u p.1) (c : ℝ) p.2) :=
      sg_measurable_flowMap hN hq hm hB c.coe_nonneg
    have hz' : Measurable z := hz
    have h2 : Measurable (fun ω : Ω => (ω, z ω)) := Measurable.prodMk measurable_id hz'
    have h3 := h1.comp h2
    exact h3
  have e : (fun ω => flowMap q B (fun u => W u ω) (c : ℝ) (z ω)) =
      fun ω => flowMap q B (fun u => W (min u c) ω) (c : ℝ) (z ω) := by
    funext ω
    exact (mk_flow_stopped ⟨hq, hm, hB, hW.cont ω, hW.zero ω⟩ c c.coe_nonneg le_rfl (z ω)).symm
  rw [e]
  exact key

/-- one step of the Markov property for a random start -/
theorem s81r_markov_step [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {q Mb : ℝ}
    (hq : 0 ≤ q) {m : ℕ} (hm : 1 ≤ m) {B : Euc d → Euc d} (hB : HasCbBound m Mb B)
    {z : Ω → Euc d} (hz : Measurable[ℱ 0] z) (a : ℝ≥0)
    {F : C(ℝ≥0, Fin d → ℝ) × Euc d → ℝ} (hF : Measurable F) {M : ℝ} (hM : ∀ p, ‖F p‖ ≤ M) :
    ∫ ω, F (bfPath (isBrownianFiltration_shift hW a) ω,
        flowMap q B (fun u => W u ω) (a : ℝ) (z ω)) ∂P =
      ∫ ω, (∫ c, F (c, flowMap q B (fun u => W u ω) (a : ℝ) (z ω)) ∂(P.map (bfPath hW))) ∂P := by
  have hW' := isBrownianFiltration_shift hW a
  set Θ := bfPath hW' with hΘ
  have hΘm : Measurable Θ := measurable_bfPath hW'
  set V : Ω → Euc d := fun ω => flowMap q B (fun u => W u ω) (a : ℝ) (z ω) with hV
  have hz' : Measurable[ℱ a] z := hz.mono (ℱ.mono a.coe_nonneg) le_rfl
  have hVm : Measurable[ℱ a] V := s81r_measurable_V hW hq hm hB a hz'
  have hVm' : Measurable V := hVm.mono (ℱ.le _) le_rfl
  have hind : IndepFun Θ V P := mk_indep hW a hVm
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hΘm.aemeasurable hVm'.aemeasurable).1 hind
  have hFint : Integrable F ((P.map Θ).prod (P.map V)) :=
    Integrable.of_bound hF.aestronglyMeasurable M (ae_of_all _ fun p => hM p)
  have hstep1 : ∫ ω, F (Θ ω, V ω) ∂P = ∫ p, F p ∂((P.map Θ).prod (P.map V)) := by
    rw [← hprod, integral_map (hΘm.prodMk hVm').aemeasurable hF.aestronglyMeasurable]
  have hstep2 := integral_prod_symm F hFint
  have hsm : AEStronglyMeasurable (fun y => ∫ c, F (c, y) ∂(P.map Θ)) (P.map V) :=
    hF.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
  have hstep3 : ∫ y, (∫ c, F (c, y) ∂(P.map Θ)) ∂(P.map V) =
      ∫ ω, (∫ c, F (c, V ω) ∂(P.map Θ)) ∂P := integral_map hVm'.aemeasurable hsm
  have hlaw : P.map Θ = P.map (bfPath hW) := bf_path_law_eq hW' hW
  show ∫ ω, F (Θ ω, V ω) ∂P = _
  rw [hstep1, hstep2, hstep3, hlaw]

theorem s81r_listprod {α X : Type*} [MeasurableSpace X] (L : List α) (g : α → X → ℝ)
    (hm : ∀ a ∈ L, Measurable (g a)) (hb : ∀ a ∈ L, ∃ M, ∀ x, |g a x| ≤ M) :
    Measurable (fun x => (L.map (fun a => g a x)).prod) ∧
      ∃ M, ∀ x, |(L.map (fun a => g a x)).prod| ≤ M := by
  induction L with
  | nil => exact ⟨measurable_const, 1, fun x => by simp⟩
  | cons a r ih =>
    obtain ⟨h1, M1, h1b⟩ := ih (fun b hb' => hm b (List.mem_cons_of_mem _ hb'))
      (fun b hb' => hb b (List.mem_cons_of_mem _ hb'))
    obtain ⟨M0, h0b⟩ := hb a (List.mem_cons_self ..)
    refine ⟨?_, M0 * M1, fun x => ?_⟩
    · simp only [List.map_cons, List.prod_cons]
      exact (hm a (List.mem_cons_self ..)).mul h1
    · simp only [List.map_cons, List.prod_cons, abs_mul]
      exact mul_le_mul (h0b x) (h1b x) (abs_nonneg _) ((abs_nonneg _).trans (h0b x))

theorem s81r_Pw_shift (c : ℝ) {L : List (ℝ × (Euc d → ℝ))} (h : s81r_Pw L) :
    s81r_Pw (L.map (fun p => (p.1 - c, p.2))) := by
  unfold s81r_Pw at h ⊢
  rw [List.map_map]
  rw [List.pairwise_map] at h ⊢
  refine h.imp fun {a b} hab => ?_
  simp only [Function.comp]
  linarith

theorem s81r_foldT_shift {E : Type*} (T : ℝ → (E → ℝ) → (E → ℝ)) (c : ℝ) :
    ∀ (L : List (ℝ × (E → ℝ))) (s : ℝ),
      s81r_foldT T s L = s81r_foldT T (s - c) (L.map (fun p => (p.1 - c, p.2)))
  | [], s => rfl
  | (v, f) :: r, s => by
    simp only [List.map_cons, s81r_foldT]
    have e : v - c - (s - c) = v - s := by ring
    rw [e, s81r_foldT_shift T c r v]

/-- the Markov chain formula for a random `ℱ₀`-measurable start -/
theorem s81r_chain [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {q Mb : ℝ}
    (hq : 0 < q) {B : Euc d → Euc d} (hB : HasCbBound 2 Mb B) :
    ∀ (n : ℕ) (L : List (ℝ × (Euc d → ℝ))), L.length = n → s81r_Pw L → (∀ p ∈ L, 0 ≤ p.1) →
      s81r_AllS s81r_S L → ∀ {z : Ω → Euc d}, Measurable[ℱ 0] z →
      ∫ ω, (L.map (fun p => p.2 (flowMap q B (fun u => W u ω) p.1 (z ω)))).prod ∂P =
        ∫ ω, s81r_foldT (sg P W q B) 0 L (z ω) ∂P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L hn hP hnn hA z hz
  match L, hn, hP, hnn, hA with
  | [], _, _, _, _ => simp [s81r_foldT]
  | (u, f) :: r, hn, hP, hnn, hA =>
    obtain ⟨hP', hGe⟩ := s81r_Pw_tail hP
    have hu : 0 ≤ u := hnn (u, f) (by simp)
    obtain ⟨a, rfl⟩ : ∃ a : ℝ≥0, (a : ℝ) = u := ⟨u.toNNReal, Real.coe_toNNReal u hu⟩
    have hq0 : 0 ≤ q := hq.le
    have hf : s81r_S f := hA ((a : ℝ), f) (by simp)
    set r' : List (ℝ × (Euc d → ℝ)) := r.map (fun p => (p.1 - (a : ℝ), p.2)) with hr'
    have hlen : r'.length < n := by rw [← hn]; simp [hr']
    have hPw' : s81r_Pw r' := s81r_Pw_shift _ hP'
    have hnn' : ∀ p ∈ r', 0 ≤ p.1 := by
      intro p hp
      obtain ⟨p0, hp0, rfl⟩ := List.mem_map.1 hp
      exact sub_nonneg.2 (hGe p0 hp0)
    have hA' : s81r_AllS s81r_S r' := by
      intro p hp
      obtain ⟨p0, hp0, rfl⟩ := List.mem_map.1 hp
      exact hA p0 (List.mem_cons_of_mem _ hp0)
    have hrA : s81r_AllS s81r_S r := fun p hp => hA p (List.mem_cons_of_mem _ hp)
    have hClos : ClosOp (sg P W q B) s81r_S :=
      ⟨s81r_S_one, fun f g hf hg => s81r_S_mul hf hg, fun t f ht hf => s81r_S_sg hW hq hB ht hf⟩
    have hFold : s81r_S (s81r_foldT (sg P W q B) 0 r') :=
      s81r_foldT_mem hClos r' 0 hPw' (fun p hp => hnn' p hp) hA'
    -- the function `g = f * foldT 0 r'`
    set g : Euc d → ℝ := fun y => f y * s81r_foldT (sg P W q B) 0 r' y with hg
    have hgS : s81r_S g := s81r_S_mul hf hFold
    let W₀ : ℝ≥0 → C(ℝ≥0, Fin d → ℝ) → Fin d → ℝ := fun u c => c u - c 0
    have hN : SgNoise W₀ :=
      { meas := fun u => (ContinuousMap.measurable_eval u).sub (ContinuousMap.measurable_eval 0)
        cont := fun c => c.continuous.sub continuous_const
        zero := fun c => sub_self _ }
    have hfl : ∀ τ : ℝ, 0 ≤ τ → Measurable (fun x : C(ℝ≥0, Fin d → ℝ) × Euc d =>
        flowMap q B (fun u' => W₀ u' x.1) τ x.2) :=
      fun τ hτ => sg_measurable_flowMap hN hq0 (by norm_num : 1 ≤ 2) hB hτ
    obtain ⟨hprodm, M1, hM1⟩ := s81r_listprod r'
      (fun p (x : C(ℝ≥0, Fin d → ℝ) × Euc d) => p.2 (flowMap q B (fun u' => W₀ u' x.1) p.1 x.2))
      (fun p hp => (s81r_S_cont (hA' p hp)).measurable.comp (hfl p.1 (hnn' p hp)))
      (fun p hp => by
        obtain ⟨M, hM⟩ := s81r_S_bdd (hA' p hp)
        exact ⟨M, fun x => hM _⟩)
    let F : C(ℝ≥0, Fin d → ℝ) × Euc d → ℝ := fun x =>
      f x.2 * (r'.map (fun p => p.2 (flowMap q B (fun u' => W₀ u' x.1) p.1 x.2))).prod
    have hFm : Measurable F := ((s81r_S_cont hf).measurable.comp measurable_snd).mul hprodm
    obtain ⟨Mf, hMf⟩ := s81r_S_bdd hf
    have hFb : ∀ x, ‖F x‖ ≤ Mf * M1 := fun x => by
      show ‖f x.2 * (r'.map (fun p => p.2 (flowMap q B (fun u' => W₀ u' x.1) p.1 x.2))).prod‖ ≤ Mf * M1
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hMf _) (hM1 x) (abs_nonneg _) ((abs_nonneg _).trans (hMf x.2))
    have hstep := s81r_markov_step hW hq0 (by norm_num : 1 ≤ 2) hB hz a hFm hFb
    have hpt : ∀ ω, ((((a : ℝ), f) :: r).map
        (fun p => p.2 (flowMap q B (fun u => W u ω) p.1 (z ω)))).prod =
        F (bfPath (isBrownianFiltration_shift hW a) ω,
          flowMap q B (fun u => W u ω) (a : ℝ) (z ω)) := by
      intro ω
      have H : PfHyp q Mb 2 B (fun u => W u ω) := ⟨hq0, by norm_num, hB, hW.cont ω, hW.zero ω⟩
      have e2 : mkShift (fun u => W u ω) a =
          fun u' => W₀ u' (bfPath (isBrownianFiltration_shift hW a) ω) := by
        funext u
        simp [mkShift, W₀, bfPath, shiftProc]
      have hmap : r.map (fun p => p.2 (flowMap q B (fun u => W u ω) p.1 (z ω))) =
          r'.map (fun p => p.2 (flowMap q B
            (fun u' => W₀ u' (bfPath (isBrownianFiltration_shift hW a) ω)) p.1
            (flowMap q B (fun u => W u ω) (a : ℝ) (z ω)))) := by
        rw [hr', List.map_map]
        refine List.map_congr_left fun p hp => ?_
        have hb : 0 ≤ p.1 - (a : ℝ) := sub_nonneg.2 (hGe p hp)
        have hco := mk_cocycle H a hb (z ω)
        have e1 : (a : ℝ) + (p.1 - (a : ℝ)) = p.1 := by ring
        rw [e1, e2] at hco
        simp only [Function.comp]
        rw [hco]
      simp only [List.map_cons, List.prod_cons, F]
      rw [hmap]
    have hinner : ∀ y : Euc d, ∫ c, F (c, y) ∂(P.map (bfPath hW)) = g y := by
      intro y
      have hFy : AEStronglyMeasurable (fun c => F (c, y)) (P.map (bfPath hW)) :=
        (hFm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      rw [integral_map (measurable_bfPath hW).aemeasurable hFy]
      have hpt2 : ∀ ω, F (bfPath hW ω, y) =
          f y * (r'.map (fun p => p.2 (flowMap q B (fun u => W u ω) p.1 y))).prod := by
        intro ω
        have e : (fun u' => W₀ u' (bfPath hW ω)) = fun u => W u ω := by
          funext u'
          simp [W₀, bfPath, hW.zero ω]
        show f y * (r'.map (fun p => p.2 (flowMap q B (fun u' => W₀ u' (bfPath hW ω)) p.1 y))).prod = _
        rw [e]
      simp_rw [hpt2]
      rw [integral_const_mul]
      have hih : ∫ ω, (r'.map (fun p => p.2 (flowMap q B (fun u => W u ω) p.1 y))).prod ∂P =
          ∫ ω, s81r_foldT (sg P W q B) 0 r' y ∂P :=
        ih r'.length hlen r' rfl hPw' hnn' hA' (z := fun _ => y) measurable_const
      rw [hih]
      simp [hg]
    have hLHS : ∫ ω, ((((a : ℝ), f) :: r).map
        (fun p => p.2 (flowMap q B (fun u => W u ω) p.1 (z ω)))).prod ∂P =
        ∫ ω, g (flowMap q B (fun u => W u ω) (a : ℝ) (z ω)) ∂P := by
      simp_rw [hpt]
      rw [hstep]
      exact integral_congr_ae (Eventually.of_forall fun ω => hinner _)
    have hlast : ∫ ω, g (flowMap q B (fun u => W u ω) (a : ℝ) (z ω)) ∂P =
        ∫ ω, sg P W q B (a : ℝ) g (z ω) ∂P := by
      obtain ⟨Mg, hMg⟩ := s81r_S_bdd hgS
      let F2 : C(ℝ≥0, Fin d → ℝ) × Euc d → ℝ := fun x =>
        g (flowMap q B (fun u' => W₀ u' x.1) (a : ℝ) x.2)
      have hF2m : Measurable F2 := (s81r_S_cont hgS).measurable.comp (hfl a a.coe_nonneg)
      have hstep0 := s81r_markov_step hW hq0 (by norm_num : 1 ≤ 2) hB hz 0 hF2m
        (M := Mg) (fun x => by
          show ‖g (flowMap q B (fun u' => W₀ u' x.1) (a : ℝ) x.2)‖ ≤ Mg
          rw [Real.norm_eq_abs]
          exact hMg _)
      have h0 : ∀ ω x, flowMap q B (fun u => W u ω) ((0 : ℝ≥0) : ℝ) x = x := fun ω x =>
        (pf_flowMap_isPathSolution (⟨hq0, by norm_num, hB, hW.cont ω, hW.zero ω⟩ :
          PfHyp q Mb 2 B (fun u => W u ω)) x).1
      simp_rw [h0] at hstep0
      have hL : ∀ ω, F2 (bfPath (isBrownianFiltration_shift hW 0) ω, z ω) =
          g (flowMap q B (fun u => W u ω) (a : ℝ) (z ω)) := by
        intro ω
        have e : (fun u' => W₀ u' (bfPath (isBrownianFiltration_shift hW 0) ω)) =
            fun u => W u ω := by
          funext u'
          simp [W₀, bfPath, shiftProc, hW.zero ω]
        show g (flowMap q B (fun u' => W₀ u' (bfPath (isBrownianFiltration_shift hW 0) ω)) (a : ℝ) (z ω)) = _
        rw [e]
      simp_rw [hL] at hstep0
      rw [hstep0]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      beta_reduce
      have hFy : AEStronglyMeasurable (fun c => F2 (c, z ω)) (P.map (bfPath hW)) :=
        (hF2m.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      rw [integral_map (measurable_bfPath hW).aemeasurable hFy]
      unfold sg
      refine integral_congr_ae (Eventually.of_forall fun ω' => ?_)
      have e : (fun u' => W₀ u' (bfPath hW ω')) = fun u => W u ω' := by
        funext u'
        simp [W₀, bfPath, hW.zero ω']
      show g (flowMap q B (fun u' => W₀ u' (bfPath hW ω')) (a : ℝ) (z ω)) =
        g (flowMap q B (fun s => W s ω') (a : ℝ) (z ω))
      rw [e]
    have e3 : s81r_foldT (sg P W q B) (a : ℝ) r = s81r_foldT (sg P W q B) 0 r' := by
      rw [s81r_foldT_shift (sg P W q B) (a : ℝ) r (a : ℝ), sub_self]
    rw [hLHS, hlast]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [s81r_foldT, sub_zero, e3]
    try rfl

end HRS.MS.S81R
