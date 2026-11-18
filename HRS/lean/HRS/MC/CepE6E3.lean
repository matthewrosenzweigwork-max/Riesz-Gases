import HRS.MC.CepE6E2

/-!
# Packet CEPE6E, file 3: S5 (Minty with a continuous path)

For a continuous path `y` in the open alcove, `∫⟨Zl - y, ∇Φ(Zl)⟩ ≤ Λ(Zl - y)`, i.e. `Λ_R(Zl - y) ≥ 0` for `Λ_R = Λ - ∇Φ(Zl) ds`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace Interval

noncomputable section

namespace HRS.MC.CepE6E

open HRS HRS.MC.Cepa HRS.MC.CepE6D

variable {N : ℕ}

/-- The cutoff profile `ψ = 1` on `(-∞,1]`, `0` on `[2,∞)`. -/
def psi (x : ℝ) : ℝ := max 0 (min 1 (2 - x))

theorem psi_continuous : Continuous psi :=
  continuous_const.max (continuous_const.min (continuous_const.sub continuous_id))

theorem psi_nonneg (x : ℝ) : 0 ≤ psi x := le_max_left _ _

theorem psi_le_one (x : ℝ) : psi x ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem psi_eq_one {x : ℝ} (h : x ≤ 1) : psi x = 1 := by
  unfold psi
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem psi_eq_zero {x : ℝ} (h : 2 ≤ x) : psi x = 0 := by
  unfold psi
  rw [min_eq_right (by linarith)]
  exact max_eq_left (by linarith)

/-- The time cutoff `φ_j(s) = ψ((j+1) dd(Zl s))`. -/
def phi (N : ℕ) (Zl : ℝ → Ch N) (j : ℕ) (s : ℝ) : ℝ := psi (((j : ℝ) + 1) * dd N (Zl s))

theorem phi_continuous {Zl : ℝ → Ch N} (hZl : Continuous Zl) (j : ℕ) : Continuous (phi N Zl j) :=
  psi_continuous.comp (continuous_const.mul (dd_continuous.comp hZl))

theorem phi_nonneg (Zl : ℝ → Ch N) (j : ℕ) (s : ℝ) : 0 ≤ phi N Zl j s := psi_nonneg _

theorem phi_le_one (Zl : ℝ → Ch N) (j : ℕ) (s : ℝ) : phi N Zl j s ≤ 1 := psi_le_one _

theorem phi_supp (Zl : ℝ → Ch N) (j : ℕ) {s : ℝ} (h : 1 - phi N Zl j s ≠ 0) :
    1 / ((j : ℝ) + 1) ≤ dd N (Zl s) := by
  by_contra hlt
  push Not at hlt
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have : ((j : ℝ) + 1) * dd N (Zl s) ≤ 1 := by
    rw [lt_div_iff₀ hj] at hlt
    linarith
  exact h (by rw [phi, psi_eq_one this]; ring)

theorem phi_tendsto_zero (Zl : ℝ → Ch N) {s : ℝ} (hs : Zl s ∈ cep_Alcove N) :
    Tendsto (fun j : ℕ => phi N Zl j s) atTop (𝓝 0) := by
  have hpos := dd_pos_of_mem hs
  refine tendsto_const_nhds.congr' ?_
  have : ∀ᶠ j : ℕ in atTop, 2 / dd N (Zl s) ≤ (j : ℝ) := by
    obtain ⟨m, hm⟩ := exists_nat_ge (2 / dd N (Zl s))
    filter_upwards [eventually_ge_atTop m] with j hj
    exact hm.trans (by exact_mod_cast hj)
  filter_upwards [this] with j hj
  symm
  unfold phi
  refine psi_eq_zero ?_
  rw [div_le_iff₀ hpos] at hj
  nlinarith

/-- The pointwise Minty inequality for the resolvent. -/
theorem cepe6e_minty_pt {a : ℝ} (ha : 0 < a) {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida a N J) {n : ℝ}
    (hn : 0 < n) {y : Ch N} (hy : y ∈ cep_Alcove N) (z : Ch N) :
    -(‖gradient (cep_chamberPot a N) y‖ * ‖n • (z - J n z)‖ / n) ≤
      ⟪n • (z - J n z) - gradient (cep_chamberPot a N) y, z - y⟫ := by
  set w := J n z with hw
  set G : Ch N := n • (z - w) with hG
  have hmono := cepe6e_gr_monotone ha.le (hJ.mem n z hn) hy
  rw [← hJ.force n z hn] at hmono
  have e : z - y = (w - y) + n⁻¹ • G := by
    rw [hG, smul_smul, inv_mul_cancel₀ hn.ne', one_smul]; abel
  rw [e, inner_add_right, inner_smul_right]
  have h1 : 0 ≤ ⟪G - gradient (cep_chamberPot a N) y, w - y⟫ := by
    have := hmono
    simpa [hG, hw] using this
  have h2 : ⟪G - gradient (cep_chamberPot a N) y, G⟫ =
      ‖G‖ ^ 2 - ⟪gradient (cep_chamberPot a N) y, G⟫ := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq]
  have h3 : ⟪gradient (cep_chamberPot a N) y, G⟫ ≤ ‖gradient (cep_chamberPot a N) y‖ * ‖G‖ :=
    real_inner_le_norm _ _
  have hn' : 0 < n⁻¹ := inv_pos.2 hn
  have h4 : -(‖gradient (cep_chamberPot a N) y‖ * ‖G‖ / n) ≤ n⁻¹ * ⟪G - gradient (cep_chamberPot a N) y, G⟫ := by
    rw [h2, div_eq_inv_mul]
    have : 0 ≤ ‖G‖ ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg hn'.le this]
  linarith

theorem cepe6e_unif_smul {T : ℝ} {Zs : ℕ → ℝ → Ch N} {Zl : ℝ → Ch N}
    (hu : TendstoUniformlyOn Zs Zl atTop (Icc 0 T)) {φ : ℝ → ℝ} (hφ : ∀ s, |φ s| ≤ 1) (y : ℝ → Ch N) :
    TendstoUniformlyOn (fun i s => φ s • (Zs i s - y s)) (fun s => φ s • (Zl s - y s)) atTop
      (Icc 0 T) := by
  rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
  intro ε hε
  filter_upwards [hu ε hε] with i hi s hs
  have h := hi s hs
  rw [dist_eq_norm] at h ⊢
  have e : φ s • (Zl s - y s) - φ s • (Zs i s - y s) = φ s • (Zl s - Zs i s) := by
    rw [← smul_sub]; congr 1; abel
  rw [e, norm_smul, Real.norm_eq_abs]
  calc |φ s| * ‖Zl s - Zs i s‖ ≤ 1 * ‖Zl s - Zs i s‖ :=
        mul_le_mul_of_nonneg_right (hφ s) (norm_nonneg _)
    _ < ε := by rw [one_mul]; exact h

theorem cepe6e_unif_inner {T : ℝ} {Zs : ℕ → ℝ → Ch N} {Zl : ℝ → Ch N}
    (hu : TendstoUniformlyOn Zs Zl atTop (Icc 0 T)) {φ : ℝ → ℝ} (hφ : ∀ s, |φ s| ≤ 1) (y G : ℝ → Ch N)
    {C : ℝ} (hC : ∀ s ∈ Icc (0 : ℝ) T, ‖G s‖ ≤ C) :
    TendstoUniformlyOn (fun i s => φ s * ⟪G s, Zs i s - y s⟫) (fun s => φ s * ⟪G s, Zl s - y s⟫)
      atTop (Icc 0 T) := by
  rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
  intro ε hε
  have hC0 : 0 ≤ |C| := abs_nonneg _
  filter_upwards [hu (ε / (|C| + 1)) (by positivity)] with i hi s hs
  have h := hi s hs
  rw [dist_eq_norm] at h
  rw [Real.dist_eq]
  have e : φ s * ⟪G s, Zl s - y s⟫ - φ s * ⟪G s, Zs i s - y s⟫ = φ s * ⟪G s, Zl s - Zs i s⟫ := by
    have hab : (Zl s - y s) - (Zs i s - y s) = Zl s - Zs i s := by abel
    rw [← mul_sub, ← inner_sub_right, hab]
  rw [e, abs_mul]
  have h1 : |⟪G s, Zl s - Zs i s⟫| ≤ ‖G s‖ * ‖Zl s - Zs i s‖ := abs_real_inner_le_norm _ _
  have h2 : ‖G s‖ ≤ |C| + 1 := (hC s hs).trans (by linarith [le_abs_self C])
  have h3 : ‖G s‖ * ‖Zl s - Zs i s‖ < ε := by
    calc ‖G s‖ * ‖Zl s - Zs i s‖ ≤ (|C| + 1) * ‖Zl s - Zs i s‖ :=
          mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ < (|C| + 1) * (ε / (|C| + 1)) := by
          exact mul_lt_mul_of_pos_left h (by positivity)
      _ = ε := by field_simp
  calc |φ s| * |⟪G s, Zl s - Zs i s⟫| ≤ 1 * |⟪G s, Zl s - Zs i s⟫| :=
        mul_le_mul_of_nonneg_right (hφ s) (abs_nonneg _)
    _ < ε := by rw [one_mul]; exact lt_of_le_of_lt h1 h3

/-- Integrated Minty inequality with a cutoff `φ ∈ [0,1]`. -/
theorem cepe6e_minty_phi {a : ℝ} {J : ℝ → Ch N → Ch N} {T : ℝ} {nn : ℕ → ℝ} {Zs : ℕ → ℝ → Ch N}
    {Zl : ℝ → Ch N} (D : Det a J T nn Zs Zl) {Λ : C(Icc (0 : ℝ) T, Ch N) →L[ℝ] ℝ}
    (hW : IsWL J nn Zs T Λ) {K : ℝ} (hK : ∀ᶠ i in atTop, ∫ s in (0 : ℝ)..T, ‖bF J nn Zs i s‖ ≤ K)
    {y : ℝ → Ch N} (hy : Continuous y) (hyA : ∀ s ∈ Icc (0 : ℝ) T, y s ∈ cep_Alcove N)
    {φ : ℝ → ℝ} (hφ : Continuous φ) (hφ0 : ∀ s, 0 ≤ φ s) (hφ1 : ∀ s, φ s ≤ 1) :
    ∫ s in (0 : ℝ)..T, φ s * ⟪gradient (cep_chamberPot a N) (y s), Zl s - y s⟫ ≤
      Λ (ofFun (fun s => φ s • (Zl s - y s)) ((hφ.smul (D.hZl.sub hy)).continuousOn)) := by
  have hT := D.hT
  set Gy : ℝ → Ch N := fun s => gradient (cep_chamberPot a N) (y s) with hGy
  have hGyc : ContinuousOn Gy (Icc 0 T) := (cepe6e_gr_continuousOn a).comp hy.continuousOn hyA
  obtain ⟨Cy0, hCy0⟩ := isCompact_Icc.exists_bound_of_continuousOn hGyc
  set Cy : ℝ := |Cy0| with hCy
  have hCy0' : 0 ≤ Cy := abs_nonneg _
  have hCyb : ∀ s ∈ Icc (0 : ℝ) T, ‖Gy s‖ ≤ Cy := fun s hs => (hCy0 s hs).trans (le_abs_self _)
  have hφabs : ∀ s, |φ s| ≤ 1 := fun s => by rw [abs_of_nonneg (hφ0 s)]; exact hφ1 s
  have hbc : ∀ i, Continuous (bF J nn Zs i) := D.bF_cont
  have hfn : ∀ i, Continuous fun s => φ s • (Zs i s - y s) := fun i =>
    hφ.smul ((D.hZs i).sub hy)
  have hxi : ∀ i, IntervalIntegrable (fun s => ⟪φ s • (Zs i s - y s), bF J nn Zs i s⟫) volume 0 T :=
    fun i => ((hfn i).inner (hbc i)).continuousOn.intervalIntegrable_of_Icc hT
  have hxc2 : ∀ i, ContinuousOn (fun s => φ s * ⟪Gy s, Zs i s - y s⟫) (Icc 0 T) := fun i =>
    hφ.continuousOn.mul (hGyc.inner ((D.hZs i).sub hy).continuousOn)
  have hxi2 : ∀ i, IntervalIntegrable (fun s => φ s * ⟪Gy s, Zs i s - y s⟫) volume 0 T := fun i =>
    (hxc2 i).intervalIntegrable_of_Icc hT
  set x : ℕ → ℝ := fun i => (∫ s in (0 : ℝ)..T, ⟪φ s • (Zs i s - y s), bF J nn Zs i s⟫) -
    ∫ s in (0 : ℝ)..T, φ s * ⟪Gy s, Zs i s - y s⟫ with hx
  have hlow : ∀ᶠ i in atTop, -(Cy * K / nn i) ≤ x i := by
    filter_upwards [hK] with i hKi
    have hnpos := D.hnn i
    have hpt : ∀ s ∈ Icc (0 : ℝ) T,
        -(Cy / nn i * ‖bF J nn Zs i s‖) ≤
          ⟪φ s • (Zs i s - y s), bF J nn Zs i s⟫ - φ s * ⟪Gy s, Zs i s - y s⟫ := by
      intro s hs
      have h := cepe6e_minty_pt D.ha D.hJ hnpos (hyA s hs) (Zs i s)
      change -(‖Gy s‖ * ‖bF J nn Zs i s‖ / nn i) ≤ ⟪bF J nn Zs i s - Gy s, Zs i s - y s⟫ at h
      have hgy : ‖Gy s‖ * ‖bF J nn Zs i s‖ / nn i ≤ Cy / nn i * ‖bF J nn Zs i s‖ := by
        rw [div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hCyb s hs) (norm_nonneg _)) hnpos.le
      rw [inner_sub_left] at h
      set c := Cy / nn i * ‖bF J nn Zs i s‖ with hc
      have hc0 : 0 ≤ c := by positivity
      have h' : -c ≤ ⟪bF J nn Zs i s, Zs i s - y s⟫ - ⟪Gy s, Zs i s - y s⟫ := by linarith
      rw [real_inner_smul_left, real_inner_comm (bF J nn Zs i s) (Zs i s - y s), ← mul_sub]
      nlinarith [mul_nonneg (hφ0 s) (by linarith : 0 ≤ ⟪bF J nn Zs i s, Zs i s - y s⟫ -
        ⟪Gy s, Zs i s - y s⟫ + c), mul_nonneg hc0 (by linarith [hφ1 s] : 0 ≤ 1 - φ s)]
    have hint1 : IntervalIntegrable (fun s => -(Cy / nn i * ‖bF J nn Zs i s‖)) volume 0 T :=
      (((hbc i).continuousOn.norm.const_mul (Cy / nn i)).neg).intervalIntegrable_of_Icc hT
    have hint2 : IntervalIntegrable (fun s => ⟪φ s • (Zs i s - y s), bF J nn Zs i s⟫ -
        φ s * ⟪Gy s, Zs i s - y s⟫) volume 0 T := (hxi i).sub (hxi2 i)
    have hm := intervalIntegral.integral_mono_on hT hint1 hint2 hpt
    rw [intervalIntegral.integral_sub (hxi i) (hxi2 i), intervalIntegral.integral_neg,
      intervalIntegral.integral_const_mul] at hm
    have hnorm : IntervalIntegrable (fun s => ‖bF J nn Zs i s‖) volume 0 T :=
      (hbc i).continuousOn.norm.intervalIntegrable_of_Icc hT
    have : Cy / nn i * ∫ s in (0 : ℝ)..T, ‖bF J nn Zs i s‖ ≤ Cy / nn i * K :=
      mul_le_mul_of_nonneg_left hKi (by positivity)
    have e : Cy * K / nn i = Cy / nn i * K := by ring
    rw [e]
    simp only [hx]
    linarith
  have hlim : Tendsto x atTop (𝓝 (Λ (ofFun (fun s => φ s • (Zl s - y s))
      ((hφ.smul (D.hZl.sub hy)).continuousOn)) - ∫ s in (0 : ℝ)..T, φ s * ⟪Gy s, Zl s - y s⟫)) := by
    refine Tendsto.sub ?_ ?_
    · exact hW (fun i s => φ s • (Zs i s - y s)) (fun s => φ s • (Zl s - y s))
        (fun i => (hfn i).continuousOn) ((hφ.smul (D.hZl.sub hy)).continuousOn)
        (cepe6e_unif_smul D.hunif hφabs y)
    · exact cepe6e_integral_tuo hT hxc2
        (hφ.continuousOn.mul (hGyc.inner (D.hZl.sub hy).continuousOn))
        (cepe6e_unif_inner D.hunif hφabs y Gy hCyb)
  have hzero : Tendsto (fun i => -(Cy * K / nn i)) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := Cy * K)).div_atTop D.hnn_top
    simpa using this.neg
  have := le_of_tendsto_of_tendsto hzero hlim hlow
  linarith

/-- **S5 (Minty with a continuous path).**  For `y` continuous with values in the open alcove on `[0,T]`,
`∫⟨Zl - y, ∇Φ(Zl)⟩ ≤ Λ(Zl - y)`. -/
theorem cepe6e_minty {a : ℝ} {J : ℝ → Ch N → Ch N} {T : ℝ} {nn : ℕ → ℝ} {Zs : ℕ → ℝ → Ch N}
    {Zl : ℝ → Ch N} (D : Det a J T nn Zs Zl) {Λ : C(Icc (0 : ℝ) T, Ch N) →L[ℝ] ℝ}
    (hW : IsWL J nn Zs T Λ) {K : ℝ} (hK : ∀ᶠ i in atTop, ∫ s in (0 : ℝ)..T, ‖bF J nn Zs i s‖ ≤ K)
    {y : ℝ → Ch N} (hy : Continuous y) (hyA : ∀ s ∈ Icc (0 : ℝ) T, y s ∈ cep_Alcove N) :
    ∫ s in (0 : ℝ)..T, ⟪Zl s - y s, gradient (cep_chamberPot a N) (Zl s)⟫ ≤
      Λ (ofFun (fun s => Zl s - y s) (D.hZl.sub hy).continuousOn) := by
  have hT := D.hT
  set f : ℝ → Ch N := fun s => Zl s - y s with hf
  have hfc : Continuous f := D.hZl.sub hy
  set Gz : ℝ → Ch N := fun s => gradient (cep_chamberPot a N) (Zl s) with hGz
  set Gy : ℝ → Ch N := fun s => gradient (cep_chamberPot a N) (y s) with hGy
  have hGyc : ContinuousOn Gy (Icc 0 T) := (cepe6e_gr_continuousOn a).comp hy.continuousOn hyA
  obtain ⟨Cy0, hCy0⟩ := isCompact_Icc.exists_bound_of_continuousOn hGyc
  set Cy : ℝ := |Cy0| with hCy
  have hCyb : ∀ s ∈ Icc (0 : ℝ) T, ‖Gy s‖ ≤ Cy := fun s hs => (hCy0 s hs).trans (le_abs_self _)
  obtain ⟨Mf0, hMf0⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc.continuousOn
  set Mf : ℝ := |Mf0| with hMf
  have hMfb : ∀ s ∈ Icc (0 : ℝ) T, ‖f s‖ ≤ Mf := fun s hs => (hMf0 s hs).trans (le_abs_self _)
  have key : ∀ j : ℕ, -(∫ s in (0 : ℝ)..T, phi N Zl j s * ⟪Gz s - Gy s, f s⟫) ≤
      Λ (ofFun f hfc.continuousOn) - ∫ s in (0 : ℝ)..T, ⟪f s, Gz s⟫ := by
    intro j
    set φ := phi N Zl j with hφdef
    have hφc : Continuous φ := phi_continuous D.hZl j
    have hA := cepe6e_minty_phi D hW hK hy hyA hφc (phi_nonneg Zl j) (phi_le_one Zl j)
    have hfφ : ContinuousOn (fun s => φ s • f s) (Icc 0 T) := (hφc.smul hfc).continuousOn
    have hg : ContinuousOn (fun s => (1 - φ s) • f s) (Icc 0 T) :=
      ((continuous_const.sub hφc).smul hfc).continuousOn
    have hB := cepe6e_local_identity D Λ hW (r := 1 / ((j : ℝ) + 1)) (by positivity) hg
      (fun s hs hne => phi_supp Zl j (fun h0 => hne (by rw [h0, zero_smul])))
    have hsplit : ofFun f hfc.continuousOn = ofFun (fun s => φ s • f s) hfφ +
        ofFun (fun s => (1 - φ s) • f s) hg := by
      refine ContinuousMap.ext fun x => ?_
      show f x.1 = φ x.1 • f x.1 + (1 - φ x.1) • f x.1
      rw [← add_smul]; simp
    rw [hsplit, map_add, hB]
    -- the integrals
    have hI1 : IntervalIntegrable (fun s => ⟪φ s • f s, Gz s⟫) volume 0 T := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]; exact D.integrableOn_inner hfφ
    have hI2 : IntervalIntegrable (fun s => ⟪(1 - φ s) • f s, Gz s⟫) volume 0 T := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]; exact D.integrableOn_inner hg
    have hsum : ∫ s in (0 : ℝ)..T, ⟪f s, Gz s⟫ = (∫ s in (0 : ℝ)..T, ⟪φ s • f s, Gz s⟫) +
        ∫ s in (0 : ℝ)..T, ⟪(1 - φ s) • f s, Gz s⟫ := by
      rw [← intervalIntegral.integral_add hI1 hI2]
      refine intervalIntegral.integral_congr fun s _ => ?_
      rw [← inner_add_left, ← add_smul]; simp
    have hI3 : IntervalIntegrable (fun s => φ s * ⟪Gy s, f s⟫) volume 0 T :=
      (hφc.continuousOn.mul (hGyc.inner hfc.continuousOn)).intervalIntegrable_of_Icc hT
    have hc : ∫ s in (0 : ℝ)..T, φ s * ⟪Gz s - Gy s, f s⟫ =
        (∫ s in (0 : ℝ)..T, ⟪φ s • f s, Gz s⟫) - ∫ s in (0 : ℝ)..T, φ s * ⟪Gy s, f s⟫ := by
      rw [← intervalIntegral.integral_sub hI1 hI3]
      refine intervalIntegral.integral_congr fun s _ => ?_
      rw [inner_sub_left, real_inner_smul_left, real_inner_comm (f s) (Gz s)]
      ring
    have hA' : ∫ s in (0 : ℝ)..T, φ s * ⟪Gy s, f s⟫ ≤ Λ (ofFun (fun s => φ s • f s) hfφ) := hA
    linarith
  have hlim : Tendsto (fun j : ℕ => -(∫ s in (0 : ℝ)..T, phi N Zl j s * ⟪Gz s - Gy s, f s⟫))
      atTop (𝓝 0) := by
    have hbi : IntervalIntegrable (fun s => Mf * (‖Gz s‖ + Cy)) volume 0 T := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
      exact (D.hint.add (integrableOn_const (by simp))).const_mul Mf
    have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ι (0 : ℝ) T → Zl s ∈ cep_Alcove N := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 D.hnull] with s hs hsI
      by_contra hz
      rw [uIoc_of_le hT] at hsI
      exact hs ⟨⟨hsI.1.le, hsI.2⟩, hz⟩
    have := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume)
      (l := atTop) (a := 0) (b := T)
      (F := fun (j : ℕ) s => phi N Zl j s * ⟪Gz s - Gy s, f s⟫) (f := fun _ => (0 : ℝ))
      (fun s => Mf * (‖Gz s‖ + Cy)) ?_ ?_ hbi ?_
    · simpa using this.neg
    · refine Eventually.of_forall fun j => ?_
      have hGy' : AEStronglyMeasurable Gy (volume.restrict (Ι (0 : ℝ) T)) := by
        rw [uIoc_of_le hT]
        exact (hGyc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
      exact (phi_continuous D.hZl j).aestronglyMeasurable.mul
        ((D.grZl_meas.aestronglyMeasurable.sub hGy').inner hfc.aestronglyMeasurable)
    · refine Eventually.of_forall fun j => ?_
      refine Eventually.of_forall fun s hs => ?_
      rw [uIoc_of_le hT] at hs
      have hsI : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2⟩
      rw [norm_mul, Real.norm_of_nonneg (phi_nonneg Zl j s)]
      have h1 : ‖⟪Gz s - Gy s, f s⟫‖ ≤ ‖Gz s - Gy s‖ * ‖f s‖ := norm_inner_le_norm _ _
      have h2 : ‖Gz s - Gy s‖ ≤ ‖Gz s‖ + Cy := (norm_sub_le _ _).trans (by linarith [hCyb s hsI])
      have h3 := hMfb s hsI
      calc phi N Zl j s * ‖⟪Gz s - Gy s, f s⟫‖ ≤ 1 * ‖⟪Gz s - Gy s, f s⟫‖ :=
            mul_le_mul_of_nonneg_right (phi_le_one Zl j s) (norm_nonneg _)
        _ ≤ ‖Gz s - Gy s‖ * ‖f s‖ := by rw [one_mul]; exact h1
        _ ≤ (‖Gz s‖ + Cy) * Mf := mul_le_mul h2 h3 (norm_nonneg _) (by positivity)
        _ = Mf * (‖Gz s‖ + Cy) := by ring
    · filter_upwards [hae] with s hs hsI
      have := (phi_tendsto_zero Zl (hs hsI)).mul_const ⟪Gz s - Gy s, f s⟫
      simpa using this
  have := le_of_tendsto' hlim key
  linarith

end HRS.MC.CepE6E
