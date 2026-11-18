import HRS.MS.S104eC1J

/-!
# S104E route C, packet C1 (part K): joint continuity in `(h, v, x)` (`VolHyp.P_jc`)

`c1_P_jc`: for a family `G v ∈ Bd j B` (`v ∈ [0,t]`) with jointly continuous jets `≤ j`, the jets `≤ j+1` of
`(h,v,x) ↦ P_h (G v)(x)` are jointly continuous on `(0,H] × [0,t] × ℝ^d`.  Orders `≤ j` from `s104c1_Drep`; order `j+1` from
the Stein formula `s104c1_top`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ContDiff RealInnerProductSpace

namespace HRS.MS.S104e.C
open HRS HRS.Whole HRS.MS.R2WinOrbNL HRS.MS.Ul HRS.MS.Wad
variable {d : ℕ}

theorem s104c1_cmm_cont {X : Type*} [TopologicalSpace X] (n : ℕ)
    {F : X → ContinuousMultilinearMap ℝ (fun _ : Fin n => Euc d) ℝ}
    (h : ∀ m, Continuous fun p => F p m) : Continuous F := by
  induction n with
  | zero =>
    have e : F = fun p => (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).symm (F p default) := by
      funext p; ext m
      simp [Subsingleton.elim m default]
    rw [e]
    exact (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).symm.continuous.comp (h default)
  | succ n ih =>
    have e : F = fun p => (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => Euc d) ℝ).symm
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => Euc d) ℝ) (F p)) := by
      funext p; simp
    rw [e]
    refine (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => Euc d) ℝ).symm.continuous.comp ?_
    rw [continuous_clm_apply]
    intro y
    refine ih fun m' => ?_
    simpa using h (Fin.cons y m')

theorem s104c1_cmm_continuousOn {X : Type*} [TopologicalSpace X] (n : ℕ) {S : Set X}
    {F : X → ContinuousMultilinearMap ℝ (fun _ : Fin n => Euc d) ℝ}
    (h : ∀ m, ContinuousOn (fun p => F p m) S) : ContinuousOn F S := by
  rw [continuousOn_iff_continuous_restrict]
  exact s104c1_cmm_cont n fun m => (continuousOn_iff_continuous_restrict.1 (h m))

theorem s104c1_avg_cont {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {t : ℝ} {S : Set (ℝ × ℝ × Euc d)} (cf sf : ℝ → ℝ) (hcf : Continuous cf) (hsf : Continuous sf)
    (hS : ∀ q ∈ S, q.2.1 ∈ Icc 0 t) (Ψ : ℝ → Euc d → F) (hΨc : ∀ v ∈ Icc 0 t, Continuous (Ψ v))
    (hΨ : ContinuousOn (fun p : ℝ × Euc d => Ψ p.1 p.2) (Icc 0 t ×ˢ univ)) {M : ℝ}
    (hM : ∀ v ∈ Icc 0 t, ∀ y, ‖Ψ v y‖ ≤ M) {w : Euc d → ℝ} (hwc : Continuous w)
    (hw : Integrable w (stdGaussian (Euc d))) :
    ContinuousOn (fun q : ℝ × ℝ × Euc d =>
      ∫ z, w z • Ψ q.2.1 (cf q.1 • q.2.2 + sf q.1 • z) ∂(stdGaussian (Euc d))) S := by
  refine continuousOn_of_dominated (bound := fun z => M * ‖w z‖) (fun q hq => ?_) (fun q hq => ?_)
    (hw.norm.const_mul M) (Filter.Eventually.of_forall fun z => ?_)
  · exact (hwc.smul ((hΨc _ (hS q hq)).comp (by fun_prop))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun z => ?_
    rw [norm_smul]
    calc ‖w z‖ * ‖Ψ q.2.1 (cf q.1 • q.2.2 + sf q.1 • z)‖ ≤ ‖w z‖ * M :=
          mul_le_mul_of_nonneg_left (hM _ (hS q hq) _) (norm_nonneg _)
      _ = M * ‖w z‖ := mul_comm _ _
  · refine ContinuousOn.const_smul ?_ (w z)
    have hcm : Continuous fun q : ℝ × ℝ × Euc d => (q.2.1, cf q.1 • q.2.2 + sf q.1 • z) := by fun_prop
    exact hΨ.comp hcm.continuousOn fun q hq => ⟨hS q hq, mem_univ _⟩

theorem c1_P_jc (a ν : ℝ) (ha : 0 < a) (hν : 0 < ν) {j : ℕ} (H : ℝ) :
    ∀ t ∈ Icc (0 : ℝ) H, ∀ (B : ℝ) (G : ℝ → Euc d → ℝ), (∀ v ∈ Icc 0 t, Bd j B (G v)) →
      (∀ i ≤ j, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (G p.1) p.2) (Icc 0 t ×ˢ univ)) →
      ∀ i ≤ j + 1, ContinuousOn
        (fun q : ℝ × ℝ × Euc d => iteratedFDeriv ℝ i (ouSg (ouQ d a) ν q.1 (G q.2.1)) q.2.2)
        (Ioc 0 H ×ˢ Icc 0 t ×ˢ univ) := by
  intro t ht B G hG hGc i hi
  set S : Set (ℝ × ℝ × Euc d) := Ioc 0 H ×ˢ Icc 0 t ×ˢ univ with hSdef
  have hS : ∀ q ∈ S, q.2.1 ∈ Icc 0 t := fun q hq => hq.2.1
  have hcf : Continuous fun h : ℝ => Real.exp (-a * h) := by fun_prop
  have hsf : Continuous (s83_ms a ν) := s104c1_ms_cont a ν
  rcases Nat.lt_or_ge i (j + 1) with hi' | hi'
  · -- order `≤ j`
    have hB := fun v hv => hG v hv
    have hψc : ∀ v ∈ Icc 0 t, Continuous (iteratedFDeriv ℝ i (G v)) := fun v hv =>
      (hB v hv).1.continuous_iteratedFDeriv (by exact_mod_cast (by omega : i ≤ j))
    have h1 := s104c1_avg_cont (S := S) (t := t) (fun h => Real.exp (-a * h)) (s83_ms a ν) hcf hsf hS
      (fun v => iteratedFDeriv ℝ i (G v)) hψc (hGc i (by omega)) (M := B)
      (fun v hv y => (hB v hv).2 i (by omega) y) (w := fun _ => (1 : ℝ)) continuous_const (integrable_const _)
    have h2 : ContinuousOn (fun q : ℝ × ℝ × Euc d => Real.exp (-a * q.1) ^ i) S := by fun_prop
    refine (h2.smul (by simpa using h1)).congr fun q hq => ?_
    beta_reduce
    rw [s104c1_Drep ha hν.le (hG q.2.1 hq.2.1) hq.1.1.le (by omega) q.2.2]
    simp
  · have hij : i = j + 1 := le_antisymm hi hi'
    subst hij
    refine s104c1_cmm_continuousOn (j + 1) fun m => ?_
    set V : Fin j → Euc d := Fin.tail m with hV
    have hψc : ∀ v ∈ Icc 0 t, Continuous fun y => iteratedFDeriv ℝ j (G v) y V := fun v hv =>
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ V).continuous.comp
        ((hG v hv).1.continuous_iteratedFDeriv (by exact_mod_cast le_rfl))
    have hψ : ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ j (G p.1) p.2 V) (Icc 0 t ×ˢ univ) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ V).continuous.comp_continuousOn
        (hGc j le_rfl)
    have hwc : Continuous fun z : Euc d => ⟪z, m 0⟫ := continuous_id.inner continuous_const
    have hw : Integrable (fun z : Euc d => ⟪z, m 0⟫) (stdGaussian (Euc d)) :=
      (s104c1_int_norm.mul_const ‖m 0‖).mono' hwc.aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs]; exact (abs_real_inner_le_norm _ _))
    have h1 := s104c1_avg_cont (S := S) (t := t) (fun h => Real.exp (-a * h)) (s83_ms a ν) hcf hsf hS
      (fun v y => iteratedFDeriv ℝ j (G v) y V) hψc hψ
      (M := B * ∏ i, ‖V i‖)
      (fun v hv y => ((iteratedFDeriv ℝ j (G v) y).le_opNorm V).trans
        (mul_le_mul_of_nonneg_right ((hG v hv).2 j le_rfl y) (Finset.prod_nonneg fun _ _ => norm_nonneg _)))
      hwc hw
    have hpre : ContinuousOn (fun q : ℝ × ℝ × Euc d =>
        Real.exp (-a * q.1) ^ (j + 1) / s83_ms a ν q.1) S := by
      refine ContinuousOn.div (by fun_prop) (hsf.comp continuous_fst).continuousOn fun q hq => ?_
      exact (s83_ms_pos ha hν hq.1.1).ne'
    refine (hpre.mul (by simpa using h1)).congr fun q hq => ?_
    beta_reduce
    rw [s104c1_top ha hν hq.1.1 (hG q.2.1 hq.2.1) q.2.2 m]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [smul_eq_mul, hV]
    ring

end HRS.MS.S104e.C
