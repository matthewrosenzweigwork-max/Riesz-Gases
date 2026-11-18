import HRS.MS.R26T8AP06t
import HRS.MS.R26T8AP11wt

/-!
# S8.2 Taylor split (T), step B1: the Taylor coefficient functions in the centre variable
For `F` with `Conormal (k+m+1) b M σ A F`, `σ < 0`, `m < -σ`: the limits `c ℓ Y = lim_{z→0} D_w^ℓ midPair F (Y,z)` (`ℓ ≤ m`) are `C^k` in `Y`,
their iterated centre derivatives are the limits of the nested jets, and `‖D^p c_ℓ (Y)‖ ≤ C A jb(Y)^(2M)`.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_conormal_jets_mono {K K' b : ℕ} {M σ A : ℝ} {F : Euc d → Euc d → ℝ} (h : K' ≤ K)
    (hF : Conormal K b M σ A F) : Conormal K' b M σ A F :=
  And.intro (hF.1.of_le (by exact_mod_cast h)) fun p q hpq X z hz => hF.2 p q (hpq.trans h) X z hz

theorem r26t8a_Phi_contDiff {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {F : Euc d → Euc d → ℝ} {n ℓ : ℕ}
    (hF : ContDiffOn ℝ (n + ℓ : ℕ) (Function.uncurry F) {p | p.1 ≠ p.2}) {w : Euc d} (hw : w ≠ 0) :
    ContDiff ℝ (n : WithTop ℕ∞) (fun Y : Euc d => iteratedFDeriv ℝ ℓ (fun w' => midPair F Y w') w) := by
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  set R : ℝ := 2 * ‖w‖ with hR
  have hRpos : 0 < R := by rw [hR]; positivity
  have hΨ := r26t8a_gtilde_contDiff hchi hRpos hF
  have hJ := r26t8a_Jq_contDiff ℓ n (fun Yw : Euc d × Euc d => r26t8a_psiCut chi R Yw.2 * midPair F Yw.1 Yw.2) hΨ
  have hc := hJ.comp (contDiff_id.prodMk contDiff_const : ContDiff ℝ (n : WithTop ℕ∞) fun Y : Euc d => (Y, w))
  have heq : (fun Y : Euc d => iteratedFDeriv ℝ ℓ (fun w' => midPair F Y w') w) =
      (fun Yw : Euc d × Euc d => iteratedFDeriv ℝ ℓ
        (fun w' => r26t8a_psiCut chi R w' * midPair F Yw.1 w') Yw.2) ∘ (fun Y : Euc d => (Y, w)) := by
    funext Y
    simp only [Function.comp]
    have hev : (fun w' => midPair F Y w') =ᶠ[𝓝 w] fun w' => r26t8a_psiCut chi R w' * midPair F Y w' := by
      have hopen : IsOpen {w' : Euc d | R / 4 < ‖w'‖} := isOpen_lt continuous_const continuous_norm
      filter_upwards [hopen.mem_nhds (show R / 4 < ‖w‖ by rw [hR]; linarith)] with w' hw'
      simp only [r26t8a_psiCut_one hchi hRpos (le_of_lt hw'), one_mul]
    exact ((hev.iteratedFDeriv ℝ ℓ).self_of_nhds)
  rw [heq]
  exact hc

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 3200000 in
theorem r26t8a_taylor_coeff (hd : 2 ≤ d) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (k b : ℕ) (M σ : ℝ)
    (hM : 0 ≤ M) (m : ℕ) (hm : (m : ℝ) < -σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 0 ≤ A → ∀ F : Euc d → Euc d → ℝ, Conormal (k + m + 1) b M σ A F →
      ∃ c : (ℓ : ℕ) → Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin ℓ => Euc d) ℝ,
        (∀ ℓ ≤ m, ContDiff ℝ (k : WithTop ℕ∞) (c ℓ)) ∧
        (∀ ℓ ≤ m, ∀ p ≤ k, ∀ Y : Euc d, ‖iteratedFDeriv ℝ p (c ℓ) Y‖ ≤ C * A * jbracket Y ^ (2 * M)) ∧
        (∀ ℓ ≤ m, ∀ p ≤ k, ∀ (X : Euc d) (u : Fin p → Euc d),
          Tendsto (fun z : Euc d => r26t8a_nest p ℓ (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) X z u)
            (𝓝[≠] (0 : Euc d)) (𝓝 (iteratedFDeriv ℝ p (c ℓ) X u))) := by
  haveI : Nontrivial (Euc d) := ⟨⟨0, EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ), by
    intro h; have := congrArg (fun v : Euc d => v ⟨0, by omega⟩) h; simp at this⟩⟩
  set Cm : ℝ := ∑ ℓ ∈ Finset.range (m + 1), r26t8a_p06_M (-σ - ℓ) b with hCm
  have hMc0 : ∀ ℓ ≤ m, 0 ≤ r26t8a_p06_M (-σ - ℓ) b := fun ℓ h => by
    have : 0 < -σ - (ℓ : ℝ) := by
      have : (ℓ : ℝ) ≤ m := by exact_mod_cast h
      linarith
    unfold r26t8a_p06_M; positivity
  have hCm0 : 0 ≤ Cm := Finset.sum_nonneg fun ℓ hℓ => hMc0 ℓ (by rw [Finset.mem_range] at hℓ; omega)
  refine ⟨3 ^ (2 * M) * (1 + Cm), by positivity, ?_⟩
  intro A hA F hF
  have hmain : ∀ ℓ : ℕ, ∃ c : Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin ℓ => Euc d) ℝ, ℓ ≤ m →
      (ContDiff ℝ (k : WithTop ℕ∞) c ∧
        (∀ p ≤ k, ∀ Y : Euc d, ‖iteratedFDeriv ℝ p c Y‖ ≤ 3 ^ (2 * M) * (1 + Cm) * A * jbracket Y ^ (2 * M)) ∧
        (∀ p ≤ k, ∀ (X : Euc d) (u : Fin p → Euc d),
          Tendsto (fun z : Euc d => r26t8a_nest p ℓ (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) X z u)
            (𝓝[≠] (0 : Euc d)) (𝓝 (iteratedFDeriv ℝ p c X u)))) := by
    intro ℓ
    by_cases hℓ : ℓ ≤ m
    swap
    · exact ⟨fun _ => 0, fun h => absurd h hℓ⟩
    have hℓs : (ℓ : ℝ) < -σ := lt_of_le_of_lt (by exact_mod_cast hℓ) hm
    have hext : ∀ p : ℕ, p ≤ k → ∃ g : Euc d × Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin p => Euc d)
        (ContinuousMultilinearMap ℝ (fun _ : Fin ℓ => Euc d) ℝ),
        Continuous g ∧ ∀ w : Euc d × Euc d, w.2 ≠ 0 →
          g w = r26t8a_nest p ℓ (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) w.1 w.2 :=
      fun p hp => r26t8a_nest_ext_relaxed hd hchi b M σ hM p ℓ hℓs hA
        (r26t8a_conormal_jets_mono (by omega) hF)
    choose! g hgc hge using hext
    haveI : CompleteSpace (ContinuousMultilinearMap ℝ (fun _ : Fin ℓ => Euc d) ℝ) :=
      ContinuousMultilinearMap.instCompleteSpace
    obtain ⟨f₀, hf₀, -, hf₀p⟩ := r26t8a_limit_taylor (E := Euc d) k
      (fun w Y => iteratedFDeriv ℝ ℓ (fun w' => midPair F Y w') w)
      (fun w hw => r26t8a_Phi_contDiff hchi (hF.1.of_le (by exact_mod_cast (by omega : k + ℓ ≤ k + m + 1))) hw)
      g (fun p hp => hgc p hp)
      (fun p hp Y w hw => by rw [hge p hp (Y, w) hw]; rfl)
    have hTu : ∀ (p : ℕ), p ≤ k → ∀ (Y : Euc d) (u : Fin p → Euc d),
        Tendsto (fun z : Euc d => g p (Y, z) u) (𝓝[≠] (0 : Euc d)) (𝓝 (g p (Y, 0) u)) := by
      intro p hp Y u
      have hev : Continuous (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin p => Euc d)
          (ContinuousMultilinearMap ℝ (fun _ : Fin ℓ => Euc d) ℝ) => T u) :=
        (ContinuousMultilinearMap.apply ℝ (fun _ : Fin p => Euc d) _ u).continuous
      exact ((hev.comp ((hgc p hp).comp (continuous_const.prodMk continuous_id))).tendsto (0 : Euc d)).mono_left
        nhdsWithin_le_nhds
    have hbd : ∀ (p : ℕ), p ≤ k → ∀ Y : Euc d, ‖g p (Y, 0)‖ ≤ 3 ^ (2 * M) * (1 + Cm) * A * jbracket Y ^ (2 * M) := by
      intro p hp Y
      have hB0 : 0 ≤ 3 ^ (2 * M) * (1 + Cm) * A * jbracket Y ^ (2 * M) := by
        have := s83_jb_pos Y; positivity
      refine ContinuousMultilinearMap.opNorm_le_bound hB0 fun u => ?_
      refine le_of_tendsto (hTu p hp Y u).norm ?_
      have h1 : ∀ᶠ z in 𝓝[≠] (0 : Euc d), dist z 0 < 1 :=
        eventually_nhdsWithin_of_eventually_nhds
          (Metric.eventually_nhds_iff.2 ⟨1, one_pos, fun y hy => hy⟩ : ∀ᶠ w in 𝓝 (0 : Euc d), dist w 0 < 1)
      filter_upwards [(eventually_mem_nhdsWithin : ∀ᶠ w in 𝓝[≠] (0 : Euc d), w ∈ ({0}ᶜ : Set (Euc d))), h1] with z hz hz1
      have hz0 : z ≠ 0 := hz
      have hzn : ‖z‖ ≤ 1 := by simpa using hz1.le
      have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
      have hnest : ‖g p (Y, z)‖ ≤ 3 ^ (2 * M) * (1 + Cm) * A * jbracket Y ^ (2 * M) := by
        rw [hge p hp (Y, z) hz0]
        have hb := hF.2 p ℓ (by omega) Y z hz0
        have hmj : r26t8a_nest p ℓ (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) Y z = mixedJet p ℓ F Y z := rfl
        rw [hmj]
        refine le_trans (le_of_eq rfl) (hb.trans ?_)
        rw [min_eq_right hzn]
        have hc : 0 < -σ - (ℓ : ℝ) := by linarith
        have hsl := r26t8a_p06_slog b hc hzpos hzn
        have e : -(σ + (ℓ : ℝ)) = -σ - ℓ := by ring
        rw [e]
        have hMle : r26t8a_p06_M (-σ - ℓ) b ≤ Cm :=
          Finset.single_le_sum (f := fun ℓ : ℕ => r26t8a_p06_M (-σ - ℓ) b) (fun ℓ' hℓ' =>
            hMc0 ℓ' (by rw [Finset.mem_range] at hℓ'; omega)) (Finset.mem_range.2 (by omega))
        have hpw := r26t8a_p01_weight hM (X := Y) (z := z) (by linarith)
        have hpw0 : 0 ≤ pairWeight M (Y + (1 / 2 : ℝ) • z) (Y - (1 / 2 : ℝ) • z) :=
          mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (s83_jb_pos _).le _)
        have hjb0 : 0 ≤ jbracket Y ^ (2 * M) := Real.rpow_nonneg (s83_jb_pos Y).le _
        calc A * pairWeight M (Y + (1 / 2 : ℝ) • z) (Y - (1 / 2 : ℝ) • z) *
              (1 + ‖z‖ ^ (-σ - (ℓ : ℝ)) * (1 + |Real.log ‖z‖|) ^ b)
            ≤ A * (3 ^ (2 * M) * jbracket Y ^ (2 * M)) * (1 + Cm) := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left hpw hA) (by linarith) (by positivity) (by positivity)
          _ = 3 ^ (2 * M) * (1 + Cm) * A * jbracket Y ^ (2 * M) := by ring
      calc ‖g p (Y, z) u‖ ≤ ‖g p (Y, z)‖ * ∏ i, ‖u i‖ := (g p (Y, z)).le_opNorm u
        _ ≤ _ := mul_le_mul_of_nonneg_right hnest (Finset.prod_nonneg fun i _ => norm_nonneg _)
    refine ⟨f₀, fun _ => ⟨hf₀, ?_, ?_⟩⟩
    · intro p hp Y
      rw [hf₀p p hp Y]
      exact hbd p hp Y
    · intro p hp X u
      rw [hf₀p p hp X]
      refine (hTu p hp X u).congr' ?_
      filter_upwards [(eventually_mem_nhdsWithin : ∀ᶠ w in 𝓝[≠] (0 : Euc d), w ∈ ({0}ᶜ : Set (Euc d)))] with z hz
      rw [hge p hp (X, z) hz]
  choose c hc using hmain
  exact ⟨c, fun ℓ hℓ => (hc ℓ hℓ).1, fun ℓ hℓ => (hc ℓ hℓ).2.1, fun ℓ hℓ => (hc ℓ hℓ).2.2⟩

end HRS.MS.R26T8A
