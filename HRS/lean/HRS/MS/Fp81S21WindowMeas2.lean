import HRS.MS.Fp81S21WindowMeas

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.CovMeas HRS.MS.GenPath
  HRS.MS.Go HRS.MS.FixEq HRS.MS.U9

variable {d : ℕ} {m L : ℝ}

/- Exact Lean interface of the reconstruction identity:
lemma fp81s21_evalA_coord_eq_W (hL : 0 ≤ L) (x : KSpace d m L)
    (hAB : x.A₀ = x.B) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) L) (α : MultiIndex d) :
    OscDual.coord (x.evalA t) α = inner ℝ x (s101W m L t α)
-/
lemma fp81s21_evalA_coord_eq_W (hL : 0 ≤ L) (x : KSpace d m L)
    (hAB : x.A₀ = x.B) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) L) (α : MultiIndex d) :
    OscDual.coord (x.evalA t) α = inner ℝ x (s101W m L t α) := by
  let y : PathSp L (KSpace d m L) := ⟨fun _ => x, continuous_const⟩
  have hpath : r2PathAt (s56_reconCLM hL y : OscPath d m L) t = x.evalA t := by
    unfold r2PathAt
    rw [dif_pos ht, OscPath.at', s56_reconCLM_apply]
    simp [pcm, y]
  have hrec := s101_recon_coord hL y ht α
  rw [hpath] at hrec
  have hcoord : OscDual.coord (x.evalA t) α =
      inner ℝ x (s101P m L t α) + inner ℝ x (s101Q m L α) := by
    simpa [pcm, y] using hrec
  have hpq : inner ℝ x (s101P m L t α) + inner ℝ x (s101Q m L α) =
      inner ℝ x (s101W m L t α) := by
    change inner ℝ (KSpace.mk x.A₀ x.A' x.B)
          (KSpace.mk (s101e m α) (s101Ind m L t (s101e m α)) (-(s101e m α))) +
        inner ℝ (KSpace.mk x.A₀ x.A' x.B) (KSpace.mk 0 0 (s101e m α)) =
      inner ℝ (KSpace.mk x.A₀ x.A' x.B)
        (KSpace.mk 0 (s101Ind m L t (s101e m α)) (s101e m α))
    rw [s101_inner_mk, s101_inner_mk, s101_inner_mk]
    rw [inner_neg_right]
    have hcoeff : inner ℝ x.A₀ (s101e m α) = inner ℝ x.B (s101e m α) := by
      rw [hAB]
    rw [hcoeff]
    simp only [inner_zero_right, zero_add, add_zero]
    ring
  exact hcoord.trans hpq

private lemma fp81s21_window_A0_eq_evalA_le
    {C : WholeCoeff d} {m H a v : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}
    (ha : 0 ≤ a) (hH : 0 ≤ H) (hD : S101Data C m (a + H) r c)
    (hv : v ∈ Icc (0 : ℝ) (a + H)) (hle : v ≤ a) (x : Euc d) :
    fp81s21_window_feature_A0 C m a v x =
      (s101Gamma C m (a + H) v x).evalA a := by
  let L : ℝ := a + H
  have haL : a ∈ Icc (0 : ℝ) (a + H) := ⟨ha, by linarith⟩
  have hmem : Memℓp (fun α : MultiIndex d => propagatorW C v a (oscTestFun m α) x) 2 :=
    s101_memℓp_of_bound hD.summable fun α => by
      have hbound := hD.bddU α v hv a ⟨hle, by linarith⟩ 0 (Nat.zero_le _) x
      simpa using hbound
  apply s101_ellVec_ext
  intro α
  change OscDual.coord (ellVec m (fun β => if v ≤ a then
      propagatorW C v a (oscTestFun m β) x else oscTestFun m β x)) α =
    OscDual.coord ((s101Gamma C m (a + H) v x).evalA a) α
  rw [s101_ellVec_coord (by simpa [hle] using hmem) α]
  rw [fp81s21_evalA_coord_eq_W (by linarith)
    (s101Gamma C m (a + H) v x) rfl haL α]
  change (if v ≤ a then propagatorW C v a (oscTestFun m α) x else oscTestFun m α x) =
    s101g C m (a + H) v
      (KSpace.mk 0 (s101Ind m (a + H) a (s101e m α)) (s101e m α)) x
  rw [s101g_W hD hv haL α x]
  by_cases hlt : v < a
  · simp [hle, hlt]
  · have hva : v = a := le_antisymm hle (le_of_not_gt hlt)
    subst v
    simp

private lemma fp81s21_window_A0_eq_evalA_gt
    {C : WholeCoeff d} {m H a v : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}
    (ha : 0 ≤ a) (hH : 0 ≤ H) (hD : S101Data C m (a + H) r c)
    (hv : v ∈ Icc (0 : ℝ) (a + H))
    (hterminal : ∀ v ∈ Icc (0 : ℝ) (a + H), ∀ α : MultiIndex d, ∀ x : Euc d,
      propagatorW C v v (oscTestFun m α) x = oscTestFun m α x)
    (hgt : a < v) (x : Euc d) :
    fp81s21_window_feature_A0 C m a v x =
      (s101Gamma C m (a + H) v x).evalA a := by
  have hmem : Memℓp (fun α : MultiIndex d => oscTestFun m α x) 2 :=
    s101_memℓp_of_bound hD.summable fun α => by
      have hbound := hD.bddU α v hv v ⟨le_rfl, hv.2⟩ 0 (Nat.zero_le _) x
      have hfun : propagatorW C v v (oscTestFun m α) = oscTestFun m α :=
        funext (hterminal v hv α)
      simpa [hfun] using hbound
  have haL : a ∈ Icc (0 : ℝ) (a + H) := by constructor <;> linarith
  apply s101_ellVec_ext
  intro α
  change OscDual.coord (ellVec m (fun β => if v ≤ a then
      propagatorW C v a (oscTestFun m β) x else oscTestFun m β x)) α =
    OscDual.coord ((s101Gamma C m (a + H) v x).evalA a) α
  rw [s101_ellVec_coord (by simpa [not_le_of_gt hgt] using hmem) α]
  rw [fp81s21_evalA_coord_eq_W (by linarith)
    (s101Gamma C m (a + H) v x) rfl haL α]
  change (if v ≤ a then propagatorW C v a (oscTestFun m α) x else oscTestFun m α x) =
    s101g C m (a + H) v
      (KSpace.mk 0 (s101Ind m (a + H) a (s101e m α)) (s101e m α)) x
  rw [s101g_W hD hv haL α x]
  have hnot : ¬v < a := not_lt_of_ge hgt.le
  simp [not_le_of_gt hgt, hnot, hterminal v hv α x]

private lemma fp81s21_window_Aprime_eq_shift
    {C : WholeCoeff d} {m H a v : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}
    (ha : 0 ≤ a) (hH : 0 ≤ H) (hD : S101Data C m (a + H) r c)
    (hv : v ∈ Icc (0 : ℝ) (a + H)) (x : Euc d) :
    (fp81s21_window_feature C m H a v x).A' =
      fp81s21_window_shiftLp (d := d) (m := m) (a := a) (H := H) ha
        (s101Gamma C m (a + H) v x).A' := by
  let L : ℝ := a + H
  let μfull : Measure ℝ := volume.restrict (Icc (0 : ℝ) L)
  let μseg : Measure ℝ := volume.restrict (Icc a L)
  let μwin : Measure ℝ := volume.restrict (Icc (0 : ℝ) H)
  have hseg : μseg ≤ μfull := by
    apply Measure.restrict_mono
    · intro t ht
      exact ⟨by linarith [ht.1], ht.2⟩
    · exact le_rfl
  have hmp : MeasurePreserving (fun t : ℝ => a + t) μwin μseg :=
    fp81s21_window_shift_measurePreserving a H
  have hfl : MemLp (fun s => s101Fl C m L v s x) 2 μfull := by
    dsimp [μfull, L]
    exact s101_Fl_memLp hD hv x
  have hcomp : MemLp (fun t => s101Fl C m L v (a + t) x) 2 μwin := by
    exact (hfl.mono_measure hseg).comp_measurePreserving hmp
  have hraw : (fun t : ℝ => fp81s21_window_feature_Aprime C m H a v t x) =ᵐ[μwin]
      fun t => s101Fl C m L v (a + t) x := by
    filter_upwards [ae_restrict_mem (measurableSet_Icc (a := (0 : ℝ)) (b := H))]
      with t ht
    have hupper : a + t ≤ a + H := by linarith [ht.2]
    simp [fp81s21_window_feature_Aprime, s101Fl, s101Th, L, hupper]
  have hwin : MemLp (fun t : ℝ => fp81s21_window_feature_Aprime C m H a v t x) 2 μwin :=
    (memLp_congr_ae hraw).2 hcomp
  have hAv : s101Av C m L v x = (s101_Fl_memLp hD hv x).toLp _ := by
    exact s101_Av_eq hD hv x
  have hshift := fp81s21_window_shiftLp_apply_ae (d := d) (m := m)
    (a := a) (H := H) ha (s101Av C m L v x)
  have hflrep : ((hfl.toLp (fun s => s101Fl C m L v s x) : L2Path d m L) :
      ℝ → OscDual d m) =ᵐ[μfull] fun s => s101Fl C m L v s x :=
    MemLp.coeFn_toLp hfl
  have hflseg := hflrep.filter_mono (Measure.absolutelyContinuous_of_le hseg).ae_le
  have hflpull := hmp.quasiMeasurePreserving.ae hflseg
  have hAvFun : (s101Av C m L v x : ℝ → OscDual d m) =
      (hfl.toLp (fun s => s101Fl C m L v s x) : ℝ → OscDual d m) := by
    exact congrArg (fun y : L2Path d m L => (y : ℝ → OscDual d m)) hAv
  have hshiftRaw :
      (fun t : ℝ => ((fp81s21_window_shiftLp (d := d) (m := m)
          (a := a) (H := H) ha (s101Av C m L v x) : L2Path d m H) :
          ℝ → OscDual d m) t) =ᵐ[μwin]
        fun t => fp81s21_window_feature_Aprime C m H a v t x := by
    filter_upwards [hshift, hflpull, hraw] with t hs hf hr
    calc
      ((fp81s21_window_shiftLp (d := d) (m := m) (a := a) (H := H) ha
          (s101Av C m L v x) : L2Path d m H) : ℝ → OscDual d m) t
          = (s101Av C m L v x : ℝ → OscDual d m) (a + t) := hs
      _ = (hfl.toLp (fun s => s101Fl C m L v s x) : ℝ → OscDual d m) (a + t) :=
        congrFun hAvFun (a + t)
      _ = s101Fl C m L v (a + t) x := hf
      _ = fp81s21_window_feature_Aprime C m H a v t x := hr.symm
  have hLpEq : (hwin.toLp (fun t => fp81s21_window_feature_Aprime C m H a v t x) :
      L2Path d m H) = fp81s21_window_shiftLp (d := d) (m := m)
        (a := a) (H := H) ha (s101Av C m L v x) := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp hwin).trans hshiftRaw.symm
  have hfeature : (fp81s21_window_feature C m H a v x).A' =
      hwin.toLp (fun t => fp81s21_window_feature_Aprime C m H a v t x) := by
    unfold fp81s21_window_feature
    rw [dif_pos hwin]
    rfl
  rw [hfeature]
  change hwin.toLp (fun t => fp81s21_window_feature_Aprime C m H a v t x) =
    fp81s21_window_shiftLp (d := d) (m := m) (a := a) (H := H) ha
      (s101Av C m L v x)
  exact hLpEq

private lemma fp81s21_KSpace_mk_eq {H : ℝ}
    {a₀ a₁ : OscDual d m} {f₀ f₁ : L2Path d m H} {b₀ b₁ : OscDual d m}
    (ha : a₀ = a₁) (hf : f₀ = f₁) (hb : b₀ = b₁) :
    KSpace.mk a₀ f₀ b₀ = KSpace.mk a₁ f₁ b₁ := by
  change WithLp.toLp 2 (a₀, WithLp.toLp 2 (f₀, b₀)) =
    WithLp.toLp 2 (a₁, WithLp.toLp 2 (f₁, b₁))
  apply congrArg (WithLp.toLp 2)
  apply Prod.ext
  · exact ha
  · exact congrArg (WithLp.toLp 2) (Prod.ext hf hb)

/- Exact feature-equality interface:
theorem fp81s21_window_feature_eq_compression
    (ha : 0 ≤ a) (hH : 0 ≤ H) (hD : S101Data C m (a + H) r c)
    (hterminal : ∀ v ∈ Icc (0 : ℝ) (a + H), ∀ α : MultiIndex d, ∀ x : Euc d,
      propagatorW C v v (oscTestFun m α) x = oscTestFun m α x)
    (hv : v ∈ Icc (0 : ℝ) (a + H)) (x : Euc d) :
    fp81s21_window_feature C m H a v x =
      (if v ≤ a then fp81s21_windowCompressionMinus ha hH
          else fp81s21_windowCompressionPlus ha hH) (s101Gamma C m (a + H) v x)
-/
theorem fp81s21_window_feature_eq_compression
    {C : WholeCoeff d} {m H a v : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}
    (ha : 0 ≤ a) (hH : 0 ≤ H) (hD : S101Data C m (a + H) r c)
    (hterminal : ∀ v ∈ Icc (0 : ℝ) (a + H), ∀ α : MultiIndex d, ∀ x : Euc d,
      propagatorW C v v (oscTestFun m α) x = oscTestFun m α x)
    (hv : v ∈ Icc (0 : ℝ) (a + H)) (x : Euc d) :
    fp81s21_window_feature C m H a v x =
      (if v ≤ a then fp81s21_windowCompressionMinus ha hH
          else fp81s21_windowCompressionPlus ha hH) (s101Gamma C m (a + H) v x) := by
  have hAprime := fp81s21_window_Aprime_eq_shift ha hH hD hv x
  by_cases hle : v ≤ a
  · rw [if_pos hle]
    have hA0 := fp81s21_window_A0_eq_evalA_le ha hH hD hv hle x
    have hB : fp81s21_window_feature_B m a v x = 0 := by
      have hnot : ¬ a < v := not_lt_of_ge hle
      simp [fp81s21_window_feature_B, hnot, s55f_ellVec_zero]
    change KSpace.mk (fp81s21_window_feature_A0 C m a v x)
        (fp81s21_window_feature C m H a v x).A'
        (fp81s21_window_feature_B m a v x) = _
    rw [fp81s21_windowCompressionMinus_apply, hB]
    exact fp81s21_KSpace_mk_eq hA0 hAprime rfl
  · have hgt : a < v := lt_of_not_ge hle
    rw [if_neg hle]
    have hA0 := fp81s21_window_A0_eq_evalA_gt ha hH hD hv hterminal hgt x
    have hB : fp81s21_window_feature_B m a v x =
        (s101Gamma C m (a + H) v x).B := by
      change ellVec m (fun α => if a < v then oscTestFun m α x else 0) =
        ellVec m (fun α => propagatorW C v v (oscTestFun m α) x)
      exact congrArg (ellVec m) (funext (fun α => by
        simp [hgt, hterminal v hv α x]))
    change KSpace.mk (fp81s21_window_feature_A0 C m a v x)
        (fp81s21_window_feature C m H a v x).A'
        (fp81s21_window_feature_B m a v x) = _
    rw [fp81s21_windowCompressionPlus_apply, hB]
    exact fp81s21_KSpace_mk_eq hA0 hAprime rfl

#print axioms fp81s21_evalA_coord_eq_W
#print axioms fp81s21_window_feature_eq_compression

end HRS.Fp81.S21

end
