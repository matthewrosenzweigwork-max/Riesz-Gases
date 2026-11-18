import HRS.Equilibrium.Parametrix.Defs
import HRS.Kernel.GradSmooth
import HRS.Kernel.SymbolClass

/-!
# Packet PX2a auxiliaries: conormal bounds for translation-invariant kernels `H₀(x - y)`

Imports only `Defs` (not `Packets`).  The chart of `(x, y) ↦ H₀(x - y)` is `(X, z) ↦ H₀(mk z)`
(independent of `X`), so the conormal bounds reduce to the global derivative bounds of `H₀`
in the box representative.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- Derivative bounds of a periodic kernel off the lattice, in terms of the box representative. -/
structure KerBound (σ : ℝ) (m : ℕ) (H₀ : Torus d → ℝ) : Prop where
  smooth : ContDiffOn ℝ ∞' (Torus.lift H₀) {y : Euc d | Torus.mk y ≠ 0}
  bound : ∀ n : ℕ, n ≤ m → ∃ C : ℝ, 0 ≤ C ∧ ∀ y w : Euc d, Torus.mk y ≠ 0 → Torus.mk w = Torus.mk y →
    (∀ i, |w i| ≤ 1 / 2) → ‖iteratedFDeriv ℝ n (Torus.lift H₀) y‖ ≤ C * (‖w‖ ^ (-σ - n) + 1)

theorem mk_add_eq (x y : Euc d) : Torus.mk (x + y) = Torus.mk x + Torus.mk y := by
  funext i; simp [Torus.mk]

theorem mk_sub_eq (x y : Euc d) : Torus.mk (x - y) = Torus.mk x - Torus.mk y := by
  funext i; simp [Torus.mk]

theorem mk_toEuc_eq (m : Lattice d) : Torus.mk (Lattice.toEuc m) = 0 :=
  KernelGrad.mk_toEuc m

/-- Periodicity of the derivatives of a lifted torus function. -/
theorem iteratedFDeriv_lift_add_lattice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H₀ : Torus d → E) (n : ℕ) (w : Euc d) (m : Lattice d) :
    iteratedFDeriv ℝ n (Torus.lift H₀) (w + Lattice.toEuc m) = iteratedFDeriv ℝ n (Torus.lift H₀) w := by
  have h : (fun z => Torus.lift H₀ (z + Lattice.toEuc m)) = Torus.lift H₀ := by
    funext z
    simp [Torus.lift, mk_add_eq, mk_toEuc_eq]
  rw [← iteratedFDeriv_comp_add_right (f := Torus.lift H₀) n (Lattice.toEuc m) w, h]

theorem iteratedFDeriv_lift_eq_of_mk_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H₀ : Torus d → E) (n : ℕ) {y w : Euc d} (h : Torus.mk y = Torus.mk w) :
    iteratedFDeriv ℝ n (Torus.lift H₀) y = iteratedFDeriv ℝ n (Torus.lift H₀) w := by
  obtain ⟨m, hm⟩ := KernelGrad.exists_lattice_of_mk_eq h
  rw [hm, iteratedFDeriv_lift_add_lattice]

theorem box_ne_zero {w : Euc d} (hw : w ≠ 0) (hb : ∀ i, |w i| ≤ 1 / 2) : Torus.mk w ≠ 0 := by
  intro h
  obtain ⟨m, hm⟩ := KernelGrad.exists_lattice_of_mk_eq (x := w) (y := 0) (by rw [h]; rfl)
  apply hw
  ext i
  have h1 : w i = (m i : ℝ) := by
    have := congrArg (fun v : Euc d => v i) hm
    simpa [Lattice.toEuc] using this
  have h2 : |(m i : ℝ)| ≤ 1 / 2 := by rw [← h1]; exact hb i
  have h3 : m i = 0 := by
    by_contra hne
    have : (1 : ℝ) ≤ |(m i : ℝ)| := by
      have : (1 : ℤ) ≤ |m i| := Int.one_le_abs hne
      exact_mod_cast this
    linarith
  simp [h1, h3]

theorem KerBound.of_box {σ : ℝ} {m : ℕ} {H₀ : Torus d → ℝ}
    (hs : ContDiffOn ℝ ∞' (Torus.lift H₀) {y : Euc d | Torus.mk y ≠ 0})
    (hb : ∀ n : ℕ, n ≤ m → ∃ C : ℝ, 0 ≤ C ∧ ∀ w : Euc d, w ≠ 0 → (∀ i, |w i| ≤ 1 / 2) →
      ‖iteratedFDeriv ℝ n (Torus.lift H₀) w‖ ≤ C * (‖w‖ ^ (-σ - n) + 1)) :
    KerBound σ m H₀ := by
  refine ⟨hs, fun n hn => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hb n hn
  refine ⟨C, hC0, fun y w hy hw hwb => ?_⟩
  have hw0 : w ≠ 0 := by
    rintro rfl
    apply hy
    rw [← hw]
    funext i; simp [Torus.mk]
  rw [iteratedFDeriv_lift_eq_of_mk_eq H₀ n hw.symm]
  exact hC w hw0 hwb


theorem isOpen_mk_ne_zero' : IsOpen {y : Euc d | Torus.mk y ≠ 0} :=
  KernelGrad.isOpen_mk_ne_zero

/-- Continuity of the iterated derivatives of a function smooth off the lattice. -/
theorem continuousOn_iteratedFDeriv_offZero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Euc d → E} (hf : ContDiffOn ℝ ∞' f {y : Euc d | Torus.mk y ≠ 0}) (n : ℕ) :
    ContinuousOn (iteratedFDeriv ℝ n f) {y : Euc d | Torus.mk y ≠ 0} := by
  have h1 := hf.continuousOn_iteratedFDerivWithin (m := n) (by exact_mod_cast le_top)
    isOpen_mk_ne_zero'.uniqueDiffOn
  exact h1.congr (iteratedFDerivWithin_of_isOpen n isOpen_mk_ne_zero').symm

theorem isCompact_box_far {δ : ℝ} (hδ : 0 < δ) :
    IsCompact {w : Euc d | (∀ i, |w i| ≤ 1 / 2) ∧ δ ≤ ‖w‖} := by
  have hc1 : IsClosed {w : Euc d | ∀ i, |w i| ≤ 1 / 2} := by
    have : {w : Euc d | ∀ i, |w i| ≤ 1 / 2} = ⋂ i, {w : Euc d | |w i| ≤ 1 / 2} := by
      ext w; simp
    rw [this]
    exact isClosed_iInter fun i => isClosed_le
      ((continuous_apply i).comp (PiLp.continuous_ofLp 2 _) |>.abs) continuous_const
  have hc2 : IsClosed {w : Euc d | δ ≤ ‖w‖} := isClosed_le continuous_const continuous_norm
  have hc : IsClosed {w : Euc d | (∀ i, |w i| ≤ 1 / 2) ∧ δ ≤ ‖w‖} := hc1.inter hc2
  refine (isCompact_closedBall (0 : Euc d) (d : ℝ)).of_isClosed_subset hc ?_
  intro w hw
  rw [mem_closedBall_zero_iff]
  exact KernelGrad.norm_le_card_of_box hw.1

/-- Lemma A: global derivative bounds of `g` away from the lattice (box representative). -/
theorem kerBound_periodicRiesz {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (m : ℕ) :
    KerBound s m (periodicRiesz d s) := by
  obtain ⟨r, δ, hδ, hr, hloc⟩ := periodicRiesz_local_singularity hd hs0 hsd
  have hsm : ContDiffOn ℝ ∞' (Torus.lift (periodicRiesz d s)) {y : Euc d | Torus.mk y ≠ 0} :=
    KernelGrad.contDiffOn_periodicRiesz hd hs0.le hsd
  refine KerBound.of_box hsm fun n hn => ?_
  set δ₁ : ℝ := min (δ / 2) (1 / 2) with hδ₁
  have hδ₁0 : 0 < δ₁ := lt_min (by linarith) (by norm_num)
  have hδ₁δ : δ₁ < δ := by have := min_le_left (δ / 2) (1 / 2); linarith
  have hrc : ContDiff ℝ ∞' (Torus.lift r) := hr
  obtain ⟨M1, hM1⟩ := (isCompact_closedBall (0 : Euc d) δ₁).exists_bound_of_continuousOn
    (hrc.continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)).continuousOn
  obtain ⟨C1, hC10, hC1⟩ := norm_iteratedFDeriv_rpow_norm_le (V := Euc d) (-s) n
  have hK := isCompact_box_far (d := d) hδ₁0
  obtain ⟨M2, hM2⟩ := hK.exists_bound_of_continuousOn
    ((continuousOn_iteratedFDeriv_offZero hsm n).mono (by
      intro w hw
      exact box_ne_zero (norm_pos_iff.mp (lt_of_lt_of_le hδ₁0 hw.2)) hw.1))
  refine ⟨max (max C1 M1) (max M2 0), le_trans (le_max_right _ _) (le_max_right _ _), fun w hw0 hwb => ?_⟩
  have hp : 0 ≤ ‖w‖ ^ (-s - (n : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  by_cases hnear : ‖w‖ ≤ δ₁
  · -- near region: `g = ‖w‖^{-s} + r`
    have hev : (Torus.lift (periodicRiesz d s)) =ᶠ[𝓝 w]
        fun y => ‖y‖ ^ (-s) + Torus.lift r y := by
      have hopen : IsOpen (Metric.ball (0 : Euc d) δ ∩ {(0 : Euc d)}ᶜ) :=
        Metric.isOpen_ball.inter isOpen_compl_singleton
      have hw' : w ∈ Metric.ball (0 : Euc d) δ ∩ {(0 : Euc d)}ᶜ :=
        ⟨by rw [mem_ball_zero_iff]; linarith, hw0⟩
      filter_upwards [hopen.mem_nhds hw'] with y hy
      have hy1 : ‖y‖ < δ := by simpa using hy.1
      exact hloc y hy1 hy.2
    have hcd1 : ContDiffAt ℝ ∞' (fun y : Euc d => ‖y‖ ^ (-s)) w := contDiffAt_rpow_norm (-s) hw0
    have hcd2 : ContDiffAt ℝ ∞' (Torus.lift r) w := hrc.contDiffAt
    rw [(hev.iteratedFDeriv ℝ n).eq_of_nhds]
    rw [show (fun y : Euc d => ‖y‖ ^ (-s) + Torus.lift r y) = (fun y : Euc d => ‖y‖ ^ (-s)) + Torus.lift r from rfl,
      iteratedFDeriv_add_apply (hcd1.of_le (by exact_mod_cast le_top))
      (hcd2.of_le (by exact_mod_cast le_top))]
    refine (norm_add_le _ _).trans ?_
    have h1 := hC1 w hw0
    have h2 := hM1 w (by rw [mem_closedBall_zero_iff]; exact hnear)
    have e : -s - (n : ℝ) = -s - n := rfl
    calc ‖iteratedFDeriv ℝ n (fun y : Euc d => ‖y‖ ^ (-s)) w‖ +
          ‖iteratedFDeriv ℝ n (Torus.lift r) w‖
        ≤ C1 * ‖w‖ ^ (-s - (n : ℝ)) + M1 := add_le_add h1 h2
      _ ≤ max (max C1 M1) (max M2 0) * (‖w‖ ^ (-s - (n : ℝ)) + 1) := by
          have hm1 : C1 ≤ max (max C1 M1) (max M2 0) := (le_max_left _ _).trans (le_max_left _ _)
          have hm2 : M1 ≤ max (max C1 M1) (max M2 0) := (le_max_right _ _).trans (le_max_left _ _)
          nlinarith [mul_le_mul_of_nonneg_right hm1 hp]
  · push Not at hnear
    have hwK : w ∈ {w : Euc d | (∀ i, |w i| ≤ 1 / 2) ∧ δ₁ ≤ ‖w‖} := ⟨hwb, hnear.le⟩
    have h2 := hM2 w hwK
    have hm2 : M2 ≤ max (max C1 M1) (max M2 0) := (le_max_left _ _).trans (le_max_right _ _)
    have hm0 : 0 ≤ max (max C1 M1) (max M2 0) := (le_max_right M2 0).trans (le_max_right _ _)
    calc ‖iteratedFDeriv ℝ n (Torus.lift (periodicRiesz d s)) w‖ ≤ M2 := h2
      _ ≤ max (max C1 M1) (max M2 0) := hm2
      _ = max (max C1 M1) (max M2 0) * 1 := (mul_one _).symm
      _ ≤ max (max C1 M1) (max M2 0) * (‖w‖ ^ (-s - (n : ℝ)) + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) hm0


/-- The components of `∇g` have derivative bounds of order `s + 1`. -/
theorem kerBound_periodicRieszGrad {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (m : ℕ)
    (j : Fin d) : KerBound (s + 1) m (fun x => periodicRieszGrad d s x j) := by
  have hsm : ContDiffOn ℝ ∞' (Torus.lift (periodicRiesz d s)) {y : Euc d | Torus.mk y ≠ 0} :=
    KernelGrad.contDiffOn_periodicRiesz hd hs0.le hsd
  have hgrad := KernelGrad.periodicRieszGrad_smoothOffZero' hd hs0.le hsd
  have hsmooth : ContDiffOn ℝ ∞' (Torus.lift (fun x => periodicRieszGrad d s x j))
      {y : Euc d | Torus.mk y ≠ 0} := by
    have := (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).contDiff.comp_contDiffOn hgrad
    exact this
  refine ⟨hsmooth, fun n hn => ?_⟩
  have hA := kerBound_periodicRiesz (d := d) hd hs0 hsd (m + 1)
  obtain ⟨C, hC0, hC⟩ := hA.bound (n + 1) (by omega)
  refine ⟨C, hC0, fun y w hy hw hwb => ?_⟩
  have hev : Torus.lift (fun x => periodicRieszGrad d s x j) =ᶠ[𝓝 y]
      fun y' => (fderiv ℝ (fun y'' : Euc d => periodicRiesz d s (Torus.mk y'')) y')
        (EuclideanSpace.single j 1) := by
    filter_upwards [isOpen_mk_ne_zero'.mem_nhds hy] with y' hy'
    have := KernelGrad.lift_periodicRieszGrad_eq_gradient hd hs0.le hsd hy'
    change (Torus.lift (periodicRieszGrad d s) y') j = _
    rw [this]
    set φ := fderiv ℝ (fun y'' : Euc d => periodicRiesz d s (Torus.mk y'')) y' with hφ
    have h3 := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := Euc d) (x := (EuclideanSpace.single j (1:ℝ))) (y := φ)
    rw [← h3, EuclideanSpace.inner_single_right]
    simp
  rw [(hev.iteratedFDeriv ℝ n).eq_of_nhds]
  have hcd : ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞)
      (fun y'' : Euc d => periodicRiesz d s (Torus.mk y'')) y :=
    (hsm.contDiffAt (isOpen_mk_ne_zero'.mem_nhds hy)).of_le (by exact_mod_cast le_top)
  have hcd' : ContDiffAt ℝ (n : WithTop ℕ∞)
      (fderiv ℝ (fun y'' : Euc d => periodicRiesz d s (Torus.mk y''))) y :=
    hcd.fderiv_right (by norm_cast)
  refine (norm_iteratedFDeriv_clm_apply_const hcd' le_rfl).trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  have h1 : ‖(EuclideanSpace.single j (1 : ℝ) : Euc d)‖ = 1 := by simp
  rw [h1, one_mul]
  refine (hC y w hy hw hwb).trans (le_of_eq ?_)
  congr 3
  push_cast; ring


/-! ### The conormal class of a translation-invariant kernel -/

theorem toChart_transl (H₀ : Torus d → ℝ) :
    toChart (fun x y => H₀ (x - y)) = fun p => Torus.lift H₀ p.2 := by
  funext p
  simp only [toChart, Torus.lift, Function.comp_apply]
  congr 1
  rw [← mk_sub_eq]
  congr 1
  module

theorem norm_mixedDeriv_transl (φ : Euc d → ℝ) (a c : ℕ) (X z : Euc d) :
    ‖mixedDeriv a c (fun p : Euc d × Euc d => φ p.2) X z‖ =
      if a = 0 then ‖iteratedFDeriv ℝ c φ z‖ else 0 := by
  have key : mixedDeriv a c (fun p : Euc d × Euc d => φ p.2) X z =
      iteratedFDeriv ℝ a (fun _ : Euc d => iteratedFDeriv ℝ c φ z) X := rfl
  rw [key]
  by_cases ha : a = 0
  · subst ha
    simp [norm_iteratedFDeriv_zero]
  · simp only [ha, if_false]
    have := iteratedFDeriv_const_of_ne (𝕜 := ℝ) (E := Euc d) ha (iteratedFDeriv ℝ c φ z)
    rw [this]
    exact norm_zero (E := ContinuousMultilinearMap ℝ (fun _ : Fin a => Euc d)
      (ContinuousMultilinearMap ℝ (fun _ : Fin c => Euc d) ℝ))

theorem lift2_transl (H₀ : Torus d → ℝ) :
    lift2 (fun x y => H₀ (x - y)) = fun p => Torus.lift H₀ (p.1 - p.2) := by
  funext p
  simp only [lift2, Torus.lift, Function.comp_apply, mk_sub_eq]

theorem px2_mem_offDiag_iff {p : Euc d × Euc d} :
    p ∈ offDiag d ↔ Torus.mk (p.1 - p.2) ≠ 0 := by
  simp only [offDiag, mk_sub_eq, ne_eq, sub_eq_zero]
  rfl

/-- iterated derivative of a composition with a continuous linear map, `f` smooth on an open set -/
theorem iteratedFDeriv_comp_clm_of_open {E G F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ ∞' f U) (L : G →L[ℝ] E) {x : G}
    (hx : L x ∈ U) (i : ℕ) :
    iteratedFDeriv ℝ i (f ∘ L) x = (iteratedFDeriv ℝ i f (L x)).compContinuousLinearMap fun _ => L := by
  have h1 := L.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn
    (hU.preimage L.continuous).uniqueDiffOn hx (i := i) (by exact_mod_cast le_top)
  have e1 := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f ∘ L) i (hU.preimage L.continuous)
    (show x ∈ L ⁻¹' U from hx)
  have e2 := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f) i hU hx
  rw [e1, e2] at h1
  exact h1

theorem rpow_le_of_mem {t a b : ℝ} (e : ℝ) (ha : 0 < a) (hat : a ≤ t) (htb : t ≤ b) :
    t ^ e ≤ a ^ e + b ^ e := by
  have ht : 0 < t := lt_of_lt_of_le ha hat
  have h1 : 0 ≤ a ^ e := Real.rpow_nonneg ha.le _
  have h2 : 0 ≤ b ^ e := Real.rpow_nonneg (ht.le.trans htb) _
  rcases le_total 0 e with he | he
  · have := Real.rpow_le_rpow ht.le htb he
    linarith
  · have := Real.rpow_le_rpow_of_nonpos ha hat he
    linarith

/-- For a box vector, the distance of `mk w` to `0` is `‖w‖`. -/
theorem eucDist_mk_sub_eq {x y : Torus d} {w : Euc d} (hw : Torus.mk w = x - y)
    (hb : ∀ i, |w i| ≤ 1 / 2) : Torus.eucDist x y = ‖w‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold Torus.eucDist
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : ‖x i - y i‖ = |w i| := by
    have : x i - y i = ((w i : ℝ) : UnitAddCircle) := by
      have := congrFun hw i
      simpa [Torus.mk] using this.symm
    rw [this]
    refine (AddCircle.norm_coe_eq_abs_iff (p := (1:ℝ)) one_ne_zero).2 ?_
    rw [abs_one]
    have := hb i
    linarith
  rw [h2, Real.norm_eq_abs]

theorem conormal_of_kerBound {σ : ℝ} {m : ℕ} {H₀ : Torus d → ℝ} (h : KerBound σ m H₀) :
    ∃ C : ℝ, 0 ≤ C ∧ Conormal σ 0 m C (fun x y => H₀ (x - y)) := by
  choose! Cc hCc0 hCc using h.bound
  set Cn : ℝ := ∑ c ∈ Finset.range (m + 1), Cc c with hCn
  have hCn0 : 0 ≤ Cn := Finset.sum_nonneg fun c hc => hCc0 c (by
    have := Finset.mem_range.mp hc; omega)
  set Cf : ℝ := ∑ k ∈ Finset.range (m + 1),
    2 ^ k * Cc k * (((1 / 8 : ℝ) ^ (-σ - k) + (d : ℝ) ^ (-σ - k)) + 1) with hCf
  have hCf0 : 0 ≤ Cf := by
    refine Finset.sum_nonneg fun k hk => ?_
    have hk' : k ≤ m := by have := Finset.mem_range.mp hk; omega
    have := hCc0 k hk'
    have h1 : 0 ≤ (1 / 8 : ℝ) ^ (-σ - k) := Real.rpow_nonneg (by norm_num) _
    have h2 : 0 ≤ (d : ℝ) ^ (-σ - k) := Real.rpow_nonneg (by positivity) _
    positivity
  refine ⟨Cn + Cf, add_nonneg hCn0 hCf0, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · -- smoothness off the diagonal
    rw [lift2_transl]
    refine ContDiffOn.comp (g := Torus.lift H₀) (f := fun p : Euc d × Euc d => p.1 - p.2)
      (h.smooth.of_le (by exact_mod_cast le_top)) (contDiff_fst.sub contDiff_snd).contDiffOn ?_
    intro p hp
    exact px2_mem_offDiag_iff.mp hp
  · -- near the diagonal
    intro a c hac X z hz hzr
    rw [toChart_transl, norm_mixedDeriv_transl]
    have hw : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
    have hzb : ∀ i, |z i| ≤ 1 / 2 := by
      intro i
      have := PiLp.norm_apply_le z i
      rw [Real.norm_eq_abs] at this
      unfold r0 at hzr
      linarith
    have hweight : 0 ≤ (Cn + Cf) * (1 + ‖z‖ ^ (-(σ + c)) * (1 + |Real.log ‖z‖|) ^ (0 : ℕ)) := by
      positivity
    split_ifs with ha0
    · have hc : c ≤ m := by omega
      obtain ⟨hh⟩ := Nat.exists_eq_add_of_le hc
      have h1 := hCc c hc z z (by
        exact box_ne_zero hz hzb) rfl hzb
      refine h1.trans ?_
      have hle : Cc c ≤ Cn + Cf := by
        have : Cc c ≤ Cn := Finset.single_le_sum (f := Cc) (fun i hi => hCc0 i (by
          have := Finset.mem_range.mp hi; omega)) (Finset.mem_range.mpr (by omega))
        linarith
      have e1 : ‖z‖ ^ (-σ - (c : ℝ)) = ‖z‖ ^ (-(σ + c)) := by ring_nf
      rw [e1, pow_zero, mul_one]
      calc Cc c * (‖z‖ ^ (-(σ + c)) + 1) ≤ (Cn + Cf) * (‖z‖ ^ (-(σ + c)) + 1) :=
            mul_le_mul_of_nonneg_right hle (by positivity)
        _ = (Cn + Cf) * (1 + ‖z‖ ^ (-(σ + c))) := by ring
    · exact hweight
  · -- far from the diagonal
    intro k hk p hp hdist
    rw [lift2_transl]
    have hp' := px2_mem_offDiag_iff.mp hp
    set L : Euc d × Euc d →L[ℝ] Euc d := ContinuousLinearMap.fst ℝ _ _ - ContinuousLinearMap.snd ℝ _ _
      with hL
    have hLp : L p = p.1 - p.2 := rfl
    have hfun : (fun p : Euc d × Euc d => Torus.lift H₀ (p.1 - p.2)) = Torus.lift H₀ ∘ L := rfl
    rw [hfun, iteratedFDeriv_comp_clm_of_open isOpen_mk_ne_zero' (h.smooth) L (by
      rw [hLp]; exact hp') k]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have hLn : ‖L‖ ≤ 2 := by
      calc ‖L‖ ≤ ‖ContinuousLinearMap.fst ℝ (Euc d) (Euc d)‖ + ‖ContinuousLinearMap.snd ℝ (Euc d) (Euc d)‖ :=
            norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add (ContinuousLinearMap.norm_fst_le _ _ _) (ContinuousLinearMap.norm_snd_le _ _ _)
        _ = 2 := by norm_num
    have hprod : ∏ _i : Fin k, ‖L‖ ≤ 2 ^ k := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact pow_le_pow_left₀ (norm_nonneg _) hLn k
    obtain ⟨w, hwm, hwb⟩ := KernelGrad.exists_mk_box (Torus.mk (p.1 - p.2))
    have hwd : Torus.eucDist (Torus.mk p.1) (Torus.mk p.2) = ‖w‖ :=
      eucDist_mk_sub_eq (by rw [hwm, mk_sub_eq]) hwb
    have hw1 : r0 ≤ ‖w‖ := by rw [← hwd]; exact hdist
    have hw2 : ‖w‖ ≤ d := KernelGrad.norm_le_card_of_box hwb
    have hk' : k ≤ m := hk
    have h1 := hCc k hk' (p.1 - p.2) w hp' hwm hwb
    have h2 := rpow_le_of_mem (-σ - k) (a := 1 / 8) (b := d) (by norm_num) (by unfold r0 at hw1; exact hw1) hw2
    have hCk0 := hCc0 k hk'
    have hterm : 2 ^ k * Cc k * (((1 / 8 : ℝ) ^ (-σ - k) + (d : ℝ) ^ (-σ - k)) + 1) ≤ Cf := by
      refine Finset.single_le_sum (f := fun k => 2 ^ k * Cc k *
        (((1 / 8 : ℝ) ^ (-σ - k) + (d : ℝ) ^ (-σ - k)) + 1)) (fun i hi => ?_) (Finset.mem_range.mpr (by omega))
      have hi' : i ≤ m := by have := Finset.mem_range.mp hi; omega
      have := hCc0 i hi'
      have h1 : 0 ≤ (1 / 8 : ℝ) ^ (-σ - i) := Real.rpow_nonneg (by norm_num) _
      have h2 : 0 ≤ (d : ℝ) ^ (-σ - i) := Real.rpow_nonneg (by positivity) _
      positivity
    calc ‖iteratedFDeriv ℝ k (Torus.lift H₀) (L p)‖ * ∏ _i : Fin k, ‖L‖
        ≤ (Cc k * (‖w‖ ^ (-σ - k) + 1)) * 2 ^ k := by
          rw [hLp]
          exact mul_le_mul h1 hprod (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity)
      _ ≤ (Cc k * (((1 / 8 : ℝ) ^ (-σ - k) + (d : ℝ) ^ (-σ - k)) + 1)) * 2 ^ k := by
          gcongr
      _ = 2 ^ k * Cc k * (((1 / 8 : ℝ) ^ (-σ - k) + (d : ℝ) ^ (-σ - k)) + 1) := by ring
      _ ≤ Cf := hterm
      _ ≤ Cn + Cf := by linarith

end HRS.Parx

end
