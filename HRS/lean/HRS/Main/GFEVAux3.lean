import HRS.Main.GFEVAux2

/-!
# Packet GFEVG, part 3: the Galerkin approximation in the abstract layer

Finite-rank orthogonal projections `P n` into `D`, the Galerkin generator `B_n(t) = P_n A_t P_n` (a bounded operator on `H`,
continuous in `t`), its evolution `Φ_n` (a linear ODE in the Banach algebra `H →L H`), the uniform bound from
quasi-dissipativity, and the strong convergence `Φ_n(t,r) P_n x → V(t,r) x` (energy/Gronwall on `x ∈ D`, density).
-/

noncomputable section

open MeasureTheory Set Filter Topology intervalIntegral

namespace HRS.GF

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The projection hypotheses. -/
structure GFProj (D : Submodule ℝ H) (P : ℕ → H →L[ℝ] H) : Prop where
  idem : ∀ n x, P n (P n x) = P n x
  symm : ∀ n x y, inner ℝ (P n x) y = inner ℝ x (P n y)
  findim : ∀ n, FiniteDimensional ℝ (LinearMap.range (P n : H →ₗ[ℝ] H))
  mem : ∀ n x, P n x ∈ D
  tendsto : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x)

theorem GFProj.norm_le {D : Submodule ℝ H} {P : ℕ → H →L[ℝ] H} (hP : GFProj D P) (n : ℕ) (x : H) :
    ‖P n x‖ ≤ ‖x‖ := by
  have h1 : ‖P n x‖ ^ 2 = inner ℝ x (P n x) := by
    rw [← real_inner_self_eq_norm_sq, hP.symm n x (P n x), hP.idem]
  have h2 : inner ℝ x (P n x) ≤ ‖x‖ * ‖P n x‖ := real_inner_le_norm _ _
  by_cases h0 : ‖P n x‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖P n x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

theorem GFProj.inner_proj {D : Submodule ℝ H} {P : ℕ → H →L[ℝ] H} (hP : GFProj D P) (n : ℕ) {w : H}
    (hw : P n w = w) (z : H) : inner ℝ w (P n z) = inner ℝ w z := by
  rw [← hP.symm n w z, hw]

theorem gfevAt_sum {D : Submodule ℝ H} {A : ℝ → D →ₗ[ℝ] H} (t : ℝ) {ι : Type*} (S : Finset ι) (c : ι → ℝ)
    (y : ι → H) (hy : ∀ i, y i ∈ D) :
    gfevAt D A t (∑ i ∈ S, c i • y i) = ∑ i ∈ S, c i • gfevAt D A t (y i) := by
  have hmem : (∑ i ∈ S, c i • y i) ∈ D := D.sum_mem fun i _ => D.smul_mem _ (hy i)
  have e : (⟨∑ i ∈ S, c i • y i, hmem⟩ : D) = ∑ i ∈ S, c i • (⟨y i, hy i⟩ : D) := by
    apply Subtype.ext; simp
  rw [gfevAt_of_mem t hmem, e, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, gfevAt_of_mem t (hy i)]

/-- The Galerkin generator `B_n(t) x = P_n A_t P_n x`, as a bounded operator continuous in `t`. -/
theorem gfev_exists_B {V : ℝ → ℝ → H →L[ℝ] H} {D : Submodule ℝ H} {A : ℝ → D →ₗ[ℝ] H} {C : ℝ}
    (h : GFAbs V D A C) {P : ℕ → H →L[ℝ] H} (hP : GFProj D P) (n : ℕ) :
    ∃ B : ℝ → H →L[ℝ] H, Continuous B ∧ ∀ t x, B t x = P n (gfevAt D A t (P n x)) := by
  haveI := hP.findim n
  set W : Submodule ℝ H := LinearMap.range (P n : H →ₗ[ℝ] H) with hW
  set b := Module.finBasis ℝ W with hb
  set Q : H →L[ℝ] W := (P n).codRestrict W (fun x => LinearMap.mem_range_self (P n : H →ₗ[ℝ] H) x) with hQ
  set ℓ : Fin (Module.finrank ℝ W) → H →L[ℝ] ℝ :=
    fun i => (LinearMap.toContinuousLinearMap (b.coord i)).comp Q with hℓ
  have hbmem : ∀ i, ((b i : W) : H) ∈ D := by
    intro i
    obtain ⟨z, hz⟩ := (b i).2
    rw [← hz]; exact hP.mem n z
  refine ⟨fun t => ∑ i, (ℓ i).smulRight (P n (gfevAt D A t ((b i : W) : H))), ?_, ?_⟩
  · refine continuous_finset_sum _ fun i _ => ?_
    have hc : Continuous fun t => P n (gfevAt D A t ((b i : W) : H)) :=
      (P n).continuous.comp (h.contA _ (hbmem i))
    exact ((ContinuousLinearMap.smulRightL ℝ H H (ℓ i)).continuous).comp hc
  · intro t x
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]
    have hx : P n x = ∑ i, ℓ i x • ((b i : W) : H) := by
      have := b.sum_repr (Q x)
      have h2 : ((Q x : W) : H) = P n x := rfl
      calc P n x = ((Q x : W) : H) := h2.symm
        _ = ((∑ i, b.repr (Q x) i • b i : W) : H) := by rw [this]
        _ = _ := by
          rw [Submodule.coe_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [hℓ, Module.Basis.coord_apply]
    have := gfevAt_sum (A := A) t Finset.univ (fun i => ℓ i x) (fun i => ((b i : W) : H)) hbmem
    conv_rhs => rw [hx, this]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]

/-- The evolution of a bounded generator with values in `range Pn`, as a linear ODE in `H →L H` with `Φ r = Pn`. -/
theorem gfev_exists_flow (B : ℝ → H →L[ℝ] H) (hB : Continuous B) (Pn : H →L[ℝ] H)
    (hPB : ∀ t x, Pn (B t x) = B t x) (hPP : ∀ x, Pn (Pn x) = Pn x) (r T : ℝ) (hrT : r ≤ T) :
    ∃ Φ : ℝ → H →L[ℝ] H, Φ r = Pn ∧ ContinuousOn Φ (Icc r T) ∧
      (∀ t ∈ Icc r T, HasDerivWithinAt Φ ((B t).comp (Φ t)) (Icc r T) t) ∧
      ∀ t ∈ Icc r T, ∀ x, Pn (Φ t x) = Φ t x := by
  set Aop : ℝ → (H →L[ℝ] H) →L[ℝ] (H →L[ℝ] H) := fun s => ContinuousLinearMap.mul ℝ (H →L[ℝ] H) (B (r + s)) with hAop
  have hA : ContinuousOn Aop (Icc 0 (T - r)) :=
    (((ContinuousLinearMap.mul ℝ (H →L[ℝ] H)).continuous.comp (hB.comp (continuous_const.add continuous_id)))).continuousOn
  obtain ⟨x, hx0, hxc, hxe, hxd⟩ := HRS.PDE.linear_ode_exists Aop (T - r) (by linarith) hA Pn
  have hshift : ∀ t ∈ Icc r T, t - r ∈ Icc (0 : ℝ) (T - r) := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨fun t => x (t - r), by simpa using hx0, ?_, ?_, ?_⟩
  · exact hxc.comp (continuous_id.sub continuous_const).continuousOn hshift
  · intro t ht
    have h1 := hxd (t - r) (hshift t ht)
    have h2 : HasDerivWithinAt (fun t' : ℝ => t' - r) 1 (Icc r T) t := (hasDerivWithinAt_id t _).sub_const r
    have h3 := h1.scomp t h2 (fun t' ht' => hshift t' ht')
    have h5 : Aop (t - r) (x (t - r)) = B t * x (t - r) := by
      simp [hAop, ContinuousLinearMap.mul_apply', add_sub_cancel]
    rw [h5, one_smul] at h3
    exact h3
  · intro t ht y
    have hs := hshift t ht
    have hint : (x (t - r)) = Pn + ∫ s in (0:ℝ)..(t - r), B (r + s) * x s := by
      have := hxe (t - r) hs
      simpa [hAop] using this
    have hcont : ContinuousOn (fun s => B (r + s) * x s) (Icc 0 (t - r)) := by
      have hxs : ContinuousOn x (Icc 0 (t - r)) := hxc.mono (Icc_subset_Icc le_rfl (by linarith [ht.2]))
      exact ((ContinuousLinearMap.mul ℝ (H →L[ℝ] H)).continuous.comp (hB.comp (continuous_const.add continuous_id))).continuousOn.clm_apply hxs
    have hii : IntervalIntegrable (fun s => B (r + s) * x s) volume 0 (t - r) :=
      (hcont.mono (by rw [uIcc_of_le hs.1]) : ContinuousOn _ (uIcc 0 (t - r))).intervalIntegrable
    have hL := (ContinuousLinearMap.mul ℝ (H →L[ℝ] H) Pn).intervalIntegral_comp_comm hii
    have hPx : Pn * x (t - r) = x (t - r) := by
      calc Pn * x (t - r) = Pn * Pn + ∫ s in (0:ℝ)..(t - r), Pn * (B (r + s) * x s) := by
            rw [hint, mul_add]
            congr 1
            have := hL
            simpa using this.symm
        _ = x (t - r) := by
            have e1 : Pn * Pn = Pn := ContinuousLinearMap.ext hPP
            have e2 : ∀ s, Pn * (B (r + s) * x s) = B (r + s) * x s := fun s =>
              ContinuousLinearMap.ext fun z => hPB _ _
            simp_rw [e2]; rw [e1, hint]
    have := congrArg (fun F : H →L[ℝ] H => F y) hPx
    simpa using this

/-- Energy/Gronwall: `⟨u, u'⟩ ≤ C ‖u‖² + ε/2` gives `‖u t‖² ≤ gronwallBound ‖u r‖² (2C) ε (t - r)`. -/
theorem gfev_gronwall_sq {u u' : ℝ → H} {r T C ε : ℝ}
    (hc : ContinuousOn u (Icc r T)) (hd : ∀ t ∈ Icc r T, HasDerivWithinAt u (u' t) (Icc r T) t)
    (hb : ∀ t ∈ Ico r T, inner ℝ (u t) (u' t) ≤ C * ‖u t‖ ^ 2 + ε / 2) :
    ∀ t ∈ Icc r T, ‖u t‖ ^ 2 ≤ gronwallBound (‖u r‖ ^ 2) (2 * C) ε (t - r) := by
  have hcont : ContinuousOn (fun t => ‖u t‖ ^ 2) (Icc r T) := (hc.norm).pow 2
  refine le_gronwallBound_of_liminf_deriv_right_le (f' := fun t => 2 * inner ℝ (u t) (u' t)) hcont ?_ le_rfl ?_
  · intro t ht q hq
    have h1 := (hd t (Ico_subset_Icc_self ht)).norm_sq
    have h2 : HasDerivWithinAt (fun t => ‖u t‖ ^ 2) (2 * inner ℝ (u t) (u' t)) (Ici t) t :=
      h1.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
    have := h2.liminf_right_slope_le hq
    refine this.mono fun z hz => ?_
    simpa [slope, smul_eq_mul] using hz
  · intro t ht
    have := hb t ht
    nlinarith

variable {V : ℝ → ℝ → H →L[ℝ] H} {D : Submodule ℝ H} {A : ℝ → D →ₗ[ℝ] H} {C : ℝ}
  {P : ℕ → H →L[ℝ] H}

/-- The Galerkin evolution for fixed `n`. -/
theorem gfev_galerkin_flow (h : GFAbs V D A C) (hP : GFProj D P) (n : ℕ) (T : ℝ) :
    ∃ Φ : ℝ → ℝ → H →L[ℝ] H,
      (∀ r ∈ Icc 0 T, Φ r r = P n) ∧
      (∀ r ∈ Icc 0 T, ∀ t ∈ Icc r T, ∀ x, P n (Φ t r x) = Φ t r x) ∧
      (∀ r ∈ Icc 0 T, ∀ t ∈ Icc r T, ∀ x,
        HasDerivWithinAt (fun t' => Φ t' r x) (P n (gfevAt D A t (Φ t r x))) (Icc r T) t) ∧
      (∀ r ∈ Icc 0 T, ∀ t ∈ Icc r T, ‖Φ t r‖ ≤ Real.exp (C * (t - r))) := by
  obtain ⟨B, hBc, hBe⟩ := gfev_exists_B h hP n
  have hPB : ∀ t x, P n (B t x) = B t x := fun t x => by rw [hBe, hP.idem]
  have hex : ∀ r : ℝ, ∃ Φ : ℝ → H →L[ℝ] H, r ∈ Icc 0 T →
      (Φ r = P n ∧ (∀ t ∈ Icc r T, ∀ x, P n (Φ t x) = Φ t x) ∧
        (∀ t ∈ Icc r T, ∀ x, HasDerivWithinAt (fun t' => Φ t' x) (B t (Φ t x)) (Icc r T) t)) := by
    intro r
    by_cases hr : r ∈ Icc 0 T
    · obtain ⟨Φ, h1, -, h3, h4⟩ := gfev_exists_flow B hBc (P n) hPB (hP.idem n) r T hr.2
      refine ⟨Φ, fun _ => ⟨h1, h4, fun t ht x => ?_⟩⟩
      have := (h3 t ht).clm_apply (hasDerivWithinAt_const t (Icc r T) x)
      simpa using this
    · exact ⟨0, fun h' => absurd h' hr⟩
  choose Φ hΦ using hex
  refine ⟨fun t r => Φ r t, fun r hr => (hΦ r hr).1, fun r hr t ht x => (hΦ r hr).2.1 t ht x, ?_, ?_⟩
  · intro r hr t ht x
    have := (hΦ r hr).2.2 t ht x
    have hu : P n (Φ r t x) = Φ r t x := (hΦ r hr).2.1 t ht x
    have hmem : Φ r t x ∈ D := by rw [← hu]; exact hP.mem n _
    have e : B t (Φ r t x) = P n (gfevAt D A t (Φ r t x)) := by rw [hBe, hu]
    rwa [e] at this
  · intro r hr t ht
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le fun x => ?_
    set u : ℝ → H := fun t' => Φ r t' x with hu
    have hd : ∀ t' ∈ Icc r T, HasDerivWithinAt u (B t' (u t')) (Icc r T) t' :=
      fun t' ht' => (hΦ r hr).2.2 t' ht' x
    have hc : ContinuousOn u (Icc r T) := fun t' ht' => (hd t' ht').continuousWithinAt
    have hb : ∀ t' ∈ Ico r T, inner ℝ (u t') (B t' (u t')) ≤ C * ‖u t'‖ ^ 2 + 0 / 2 := by
      intro t' ht'
      have ht'' : t' ∈ Icc r T := Ico_subset_Icc_self ht'
      have hpu : P n (u t') = u t' := (hΦ r hr).2.1 t' ht'' x
      have hmem : u t' ∈ D := by rw [← hpu]; exact hP.mem n _
      rw [hBe, hpu, hP.inner_proj n hpu]
      have := h.quasi (hr.1.trans ht''.1) hmem
      simp only [zero_div, add_zero]
      nlinarith
    have hg := gfev_gronwall_sq hc hd hb t ht
    rw [gronwallBound_ε0] at hg
    have hur : u r = P n x := by simp [hu, (hΦ r hr).1]
    have hn : ‖u r‖ ≤ ‖x‖ := by rw [hur]; exact hP.norm_le n x
    have hsq : ‖u t‖ ^ 2 ≤ (Real.exp (C * (t - r)) * ‖x‖) ^ 2 := by
      calc ‖u t‖ ^ 2 ≤ ‖u r‖ ^ 2 * Real.exp (2 * C * (t - r)) := hg
        _ ≤ ‖x‖ ^ 2 * Real.exp (2 * C * (t - r)) := by gcongr
        _ = (Real.exp (C * (t - r)) * ‖x‖) ^ 2 := by
          rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
theorem gfevAt_sub (s : ℝ) {y z : H} (hy : y ∈ D) (hz : z ∈ D) :
    gfevAt D A s (y - z) = gfevAt D A s y - gfevAt D A s z := by
  rw [gfevAt_of_mem s (D.sub_mem hy hz), gfevAt_of_mem s hy, gfevAt_of_mem s hz, ← map_sub]
  rfl

theorem gfevAt_add (s : ℝ) {y z : H} (hy : y ∈ D) (hz : z ∈ D) :
    gfevAt D A s (y + z) = gfevAt D A s y + gfevAt D A s z := by
  rw [gfevAt_of_mem s (D.add_mem hy hz), gfevAt_of_mem s hy, gfevAt_of_mem s hz, ← map_add]
  rfl

/-- Strong convergence of the Galerkin evolutions on `D`. -/
theorem gfev_galerkin_conv (h : GFAbs V D A C) (hP : GFProj D P) {N : H → ℝ} {ε : ℕ → ℝ} {M4 : ℝ}
    (hN : ∀ x, 0 ≤ N x) (hε0 : ∀ n, 0 ≤ ε n) (hε : Tendsto ε atTop (𝓝 0))
    (htail : ∀ n (s : ℝ), 0 ≤ s → ∀ x ∈ D, ‖gfevAt D A s (x - P n x)‖ ≤ ε n * N x)
    {T : ℝ} (hprop : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ x ∈ D, N (V t r x) ≤ M4 * N x)
    {Φ : ℕ → ℝ → ℝ → H →L[ℝ] H}
    (hΦ0 : ∀ n, ∀ r ∈ Icc 0 T, Φ n r r = P n)
    (hΦr : ∀ n, ∀ r ∈ Icc 0 T, ∀ t ∈ Icc r T, ∀ x, P n (Φ n t r x) = Φ n t r x)
    (hΦd : ∀ n, ∀ r ∈ Icc 0 T, ∀ t ∈ Icc r T, ∀ x,
      HasDerivWithinAt (fun t' => Φ n t' r x) (P n (gfevAt D A t (Φ n t r x))) (Icc r T) t)
    {r : ℝ} (hr : r ∈ Icc 0 T) {t : ℝ} (ht : t ∈ Icc r T) {x : H} (hx : x ∈ D) :
    Tendsto (fun n => Φ n t r x) atTop (𝓝 (V t r x)) := by
  have hrT : r ≤ T := hr.2
  have hv : ∀ s ∈ Icc r T, HasDerivWithinAt (fun s' => V s' r x) (gfevAt D A s (V s r x)) (Icc r T) s :=
    h.forward hr.1 hrT hx
  have hvD : ∀ s ∈ Icc r T, V s r x ∈ D := fun s hs => h.inv r s hr.1 hs.1 x hx
  set a : ℕ → ℝ := fun n => ε n * (M4 * N x) with ha
  have ha0 : Tendsto a atTop (𝓝 0) := by simpa [ha] using hε.mul_const (M4 * N x)
  have hkey : ∀ n, ‖P n (V t r x) - Φ n t r x‖ ^ 2 ≤
      gronwallBound 0 (2 * (C + 1 / 2)) ((a n) ^ 2) (t - r) := by
    intro n
    set u : ℝ → H := fun s => Φ n s r x with hu
    set e : ℝ → H := fun s => P n (V s r x) - u s with he
    set e' : ℝ → H := fun s => P n (gfevAt D A s (V s r x)) - P n (gfevAt D A s (u s)) with he'
    have hud : ∀ s ∈ Icc r T, HasDerivWithinAt e (e' s) (Icc r T) s := by
      intro s hs
      have h1 := (P n).hasFDerivAt.comp_hasDerivWithinAt s (hv s hs)
      exact h1.sub (hΦd n r hr s hs x)
    have hec : ContinuousOn e (Icc r T) := fun s hs => (hud s hs).continuousWithinAt
    have hPu : ∀ s ∈ Icc r T, P n (u s) = u s := fun s hs => hΦr n r hr s hs x
    have huD : ∀ s ∈ Icc r T, u s ∈ D := fun s hs => by rw [← hPu s hs]; exact hP.mem n _
    have hPe : ∀ s ∈ Icc r T, P n (e s) = e s := by
      intro s hs
      simp only [he, map_sub, hP.idem, hPu s hs]
    have hb : ∀ s ∈ Ico r T, inner ℝ (e s) (e' s) ≤ (C + 1 / 2) * ‖e s‖ ^ 2 + (a n) ^ 2 / 2 := by
      intro s hs
      have hs' : s ∈ Icc r T := Ico_subset_Icc_self hs
      have hs0 : 0 ≤ s := hr.1.trans hs'.1
      have hvs := hvD s hs'
      have hus := huD s hs'
      have heD : e s ∈ D := by rw [← hPe s hs']; exact hP.mem n _
      have e1 : e' s = P n (gfevAt D A s (V s r x - u s)) := by
        rw [gfevAt_sub s hvs hus, map_sub]
      have e2 : V s r x - u s = (V s r x - P n (V s r x)) + e s := by simp [he]
      have e3 : gfevAt D A s (V s r x - u s) =
          gfevAt D A s (V s r x - P n (V s r x)) + gfevAt D A s (e s) := by
        rw [e2, gfevAt_add s (D.sub_mem hvs (hP.mem n _)) heD]
      rw [e1, hP.inner_proj n (hPe s hs'), e3, inner_add_right]
      have hq := h.quasi hs0 heD
      have hail := htail n s hs0 _ hvs
      have hN := hprop r s hr.1 hs'.1 hs'.2 x hx
      have hnn := norm_nonneg (e s)
      have h1 : inner ℝ (e s) (gfevAt D A s (V s r x - P n (V s r x))) ≤ ‖e s‖ * a n := by
        refine (real_inner_le_norm _ _).trans ?_
        refine mul_le_mul_of_nonneg_left (hail.trans ?_) hnn
        calc ε n * N (V s r x) ≤ ε n * (M4 * N x) := mul_le_mul_of_nonneg_left hN (hε0 n)
          _ = a n := rfl
      nlinarith [sq_nonneg (‖e s‖ - a n)]
    have hg := gfev_gronwall_sq hec hud hb t ht
    have her : e r = 0 := by
      simp only [he, hu]
      rw [h.self r hr.1, hΦ0 n r hr]; simp
    rw [her, norm_zero] at hg
    simpa [he, hu] using hg
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hG : Tendsto (fun n => gronwallBound 0 (2 * (C + 1 / 2)) ((a n) ^ 2) (t - r)) atTop (𝓝 0) := by
    have hc := (gronwallBound_continuous_ε 0 (2 * (C + 1 / 2)) (t - r)).tendsto 0
    have h2 : Tendsto (fun n => (a n) ^ 2) atTop (𝓝 0) := by simpa using ha0.pow 2
    rw [gronwallBound_ε0_δ0] at hc
    exact hc.comp h2
  have hE : Tendsto (fun n => ‖P n (V t r x) - Φ n t r x‖) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hG
    simp only [Real.sqrt_zero] at this
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) this
    exact Real.le_sqrt_of_sq_le (hkey n) |>.trans_eq rfl
  have hT : Tendsto (fun n => ‖P n (V t r x) - V t r x‖) atTop (𝓝 0) := by
    have := (hP.tendsto (V t r x))
    rw [tendsto_iff_norm_sub_tendsto_zero] at this
    exact this
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using hE.add hT)
  calc ‖Φ n t r x - V t r x‖ = ‖(P n (V t r x) - V t r x) - (P n (V t r x) - Φ n t r x)‖ := by
        congr 1; abel
    _ ≤ _ := by
        rw [add_comm]; exact norm_sub_le _ _

/-- The Galerkin conjunct, in the abstract layer. -/
theorem gfev_galerkin (h : GFAbs V D A C) (hP : GFProj D P) (hD : Dense (D : Set H)) {N : H → ℝ}
    {ε : ℕ → ℝ} {M4 : ℝ}
    (hN : ∀ x, 0 ≤ N x) (hε0 : ∀ n, 0 ≤ ε n) (hε : Tendsto ε atTop (𝓝 0))
    (htail : ∀ n (s : ℝ), 0 ≤ s → ∀ x ∈ D, ‖gfevAt D A s (x - P n x)‖ ≤ ε n * N x)
    (T : ℝ) (hprop : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ x ∈ D, N (V t r x) ≤ M4 * N x) :
    ∃ Vn : ℕ → ℝ → ℝ → H →L[ℝ] H,
      (∀ n r x, r ∈ Icc 0 T → Vn n r r x = P n x) ∧
      (∀ n t r x, ∃ y, P n y = Vn n t r x) ∧
      (∀ n r t x y, r ∈ Icc 0 T → t ∈ Icc r T → (∃ z, P n z = y) →
        HasDerivWithinAt (fun t' => inner ℝ y (Vn n t' r x))
          (inner ℝ y (gfevAt D A t (Vn n t r x))) (Icc r T) t) ∧
      (∀ r ∈ Icc 0 T, ∀ t ∈ Icc r T, ∀ x,
        Tendsto (fun n => Vn n t r x) atTop (𝓝 (V t r x))) := by
  classical
  have hfl := fun n => gfev_galerkin_flow h hP n T
  choose Φ hΦ0 hΦr hΦd hΦb using hfl
  let Vn : ℕ → ℝ → ℝ → H →L[ℝ] H := fun n t r =>
    if r ∈ Icc 0 T ∧ t ∈ Icc r T then Φ n t r else 0
  have hVn : ∀ n, ∀ r ∈ Icc 0 T, ∀ t ∈ Icc r T, Vn n t r = Φ n t r := by
    intro n r hr t ht
    simp only [Vn, if_pos (And.intro hr ht)]
  refine ⟨Vn, ?_, ?_, ?_, ?_⟩
  · intro n r x hr
    rw [hVn n r hr r ⟨le_rfl, hr.2⟩, hΦ0 n r hr]
  · intro n t r x
    by_cases hc : r ∈ Icc 0 T ∧ t ∈ Icc r T
    · refine ⟨Φ n t r x, ?_⟩
      simp only [Vn, if_pos hc]
      exact hΦr n r hc.1 t hc.2 x
    · refine ⟨0, ?_⟩
      simp only [Vn, if_neg hc]; simp
  · intro n r t x y hr ht ⟨z, hz⟩
    have hy : P n y = y := by rw [← hz, hP.idem]
    have h1 := (hasDerivWithinAt_const t (Icc r T) y).inner ℝ (hΦd n r hr t ht x)
    have e : inner ℝ y (P n (gfevAt D A t (Φ n t r x))) = inner ℝ y (gfevAt D A t (Φ n t r x)) :=
      hP.inner_proj n hy _
    rw [inner_zero_left, add_zero, e] at h1
    rw [hVn n r hr t ht]
    refine h1.congr (fun t' ht' => ?_) ?_
    · rw [hVn n r hr t' ht']
    · rw [hVn n r hr t ht]
  · intro r hr t ht x
    have hbd : ∀ n, ‖Vn n t r‖ ≤ Real.exp (|C| * T) := fun n => by
      rw [hVn n r hr t ht]
      exact (hΦb n r hr t ht).trans (gfev_exp_le C (by linarith [ht.1]) (by linarith [ht.2, hr.1]))
    have hVb : ‖V t r‖ ≤ Real.exp (|C| * T) :=
      (h.bound r t hr.1 ht.1).trans (gfev_exp_le C (by linarith [ht.1]) (by linarith [ht.2, hr.1]))
    set M := Real.exp (|C| * T) with hM
    have hM0 : 0 < M := Real.exp_pos _
    rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨x', hx'D, hx'⟩ : ∃ x' ∈ (D : Set H), dist x x' < η / (3 * M) := by
      have := Metric.mem_closure_iff.1 (hD.closure_eq ▸ Set.mem_univ x) (η / (3 * M)) (by positivity)
      obtain ⟨b, hb, hb'⟩ := this
      exact ⟨b, hb, hb'⟩
    have hconv := gfev_galerkin_conv h hP hN hε0 hε htail hprop hΦ0 hΦr hΦd hr ht hx'D
    rw [Metric.tendsto_atTop] at hconv
    obtain ⟨n0, hn0⟩ := hconv (η / 3) (by positivity)
    refine ⟨n0, fun n hn => ?_⟩
    have h3 := hn0 n hn
    rw [dist_eq_norm] at h3 hx' ⊢
    have e1 : ‖Vn n t r (x - x')‖ ≤ M * ‖x - x'‖ := ((Vn n t r).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hbd n) (norm_nonneg _))
    have e2 : ‖V t r (x - x')‖ ≤ M * ‖x - x'‖ := ((V t r).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hVb (norm_nonneg _))
    have e3 : Vn n t r x - V t r x = Vn n t r (x - x') + (Vn n t r x' - V t r x') - V t r (x - x') := by
      simp only [map_sub]; abel
    have hx'' : M * ‖x - x'‖ < η / 3 := by
      calc M * ‖x - x'‖ < M * (η / (3 * M)) := mul_lt_mul_of_pos_left hx' hM0
        _ = η / 3 := by field_simp
    rw [hVn n r hr t ht] at e3 e1 ⊢
    rw [e3]
    calc ‖Φ n t r (x - x') + (Φ n t r x' - V t r x') - V t r (x - x')‖
        ≤ ‖Φ n t r (x - x') + (Φ n t r x' - V t r x')‖ + ‖V t r (x - x')‖ := norm_sub_le _ _
      _ ≤ ‖Φ n t r (x - x')‖ + ‖Φ n t r x' - V t r x'‖ + ‖V t r (x - x')‖ := by
          gcongr; exact norm_add_le _ _
      _ < η := by linarith

end HRS.GF
