import HRS.Torus.Basic

/-!
# Packet SCRN, part 2: lattice sums `∑_{k ∈ ℤ^d} (max 1 |k|)^{-g} (1 + ℓ|k|)^{-L} ≤ C ℓ^{-(d-g)}`

One-dimensional comparison with `∫_0^∞ u^{-γ}(1+u)^{-a} du` (`scrn_sum_pos`), then the product trick
`(1+ℓ|k|)^{-L} ≤ ∏_i (1+ℓ|k_i|)^{-L/d}`, `(max 1 |k|)^{-g} ≤ ∏_i (max 1 |k_i|)^{-g/d}` over boxes
(`scrn_latsum`).  Used for the Fourier ℓ¹/ℓ² norms of the mesoscopic test and for the Riemann sum.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace HRS

/-- the integrand `u^{-γ}(1+u)^{-a}` is integrable on `(0,∞)` for `γ<1`, `a>1`. -/
lemma scrn_integrableOn_g {γ a : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ < 1) (ha : 1 < a) :
    IntegrableOn (fun u : ℝ => u ^ (-γ) * (1 + u) ^ (-a)) (Ioi 0) := by
  have h1 : IntegrableOn (fun u : ℝ => u ^ (-γ) * (1 + u) ^ (-a)) (Ioc 0 1) := by
    have hi : IntegrableOn (fun u : ℝ => u ^ (-γ)) (Ioc 0 1) := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := -γ) (by linarith))
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 this
    refine Integrable.mono' hi ?_ ?_
    · exact (((measurable_id.pow_const _).mul ((measurable_const.add measurable_id).pow_const _))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have h0 : 0 < u := hu.1
      have : (1 + u) ^ (-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hu.1]) (by linarith)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc u ^ (-γ) * (1 + u) ^ (-a) ≤ u ^ (-γ) * 1 := by gcongr
        _ = u ^ (-γ) := mul_one _
  have h2 : IntegrableOn (fun u : ℝ => u ^ (-γ) * (1 + u) ^ (-a)) (Ioi 1) := by
    have hi : IntegrableOn (fun u : ℝ => u ^ (-a)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    refine Integrable.mono' hi ?_ ?_
    · exact (((measurable_id.pow_const _).mul ((measurable_const.add measurable_id).pow_const _))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have h0 : 1 < u := hu
      have e1 : u ^ (-γ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h0.le (by linarith)
      have e2 : (1 + u) ^ (-a) ≤ u ^ (-a) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc u ^ (-γ) * (1 + u) ^ (-a) ≤ 1 * u ^ (-a) := by
            gcongr
        _ = u ^ (-a) := one_mul _
  have := h1.union h2
  rwa [Ioc_union_Ioi_eq_Ioi zero_le_one] at this


/-- `J γ a = ∫_0^∞ u^{-γ}(1+u)^{-a} du`. -/
noncomputable def scrnJ (γ a : ℝ) : ℝ := ∫ u in Ioi (0:ℝ), u ^ (-γ) * (1 + u) ^ (-a)

lemma scrn_h_eq {γ a ℓ : ℝ} (hℓ : 0 < ℓ) (x : ℝ) (hx : 0 < x) :
    x ^ (-γ) * (1 + ℓ * x) ^ (-a) =
      ℓ ^ γ * ((ℓ * x) ^ (-γ) * (1 + ℓ * x) ^ (-a)) := by
  rw [Real.mul_rpow hℓ.le hx.le, Real.rpow_neg hℓ.le]
  have : ℓ ^ γ * (ℓ ^ γ)⁻¹ = 1 := mul_inv_cancel₀ (Real.rpow_pos_of_pos hℓ γ).ne'
  calc x ^ (-γ) * (1 + ℓ * x) ^ (-a) = (ℓ ^ γ * (ℓ ^ γ)⁻¹) * (x ^ (-γ) * (1 + ℓ * x) ^ (-a)) := by
        rw [this, one_mul]
    _ = _ := by ring

lemma scrn_integrableOn_h {γ a ℓ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ < 1) (ha : 1 < a) (hℓ : 0 < ℓ) :
    IntegrableOn (fun x : ℝ => x ^ (-γ) * (1 + ℓ * x) ^ (-a)) (Ioi 0) := by
  have hg := scrn_integrableOn_g hγ0 hγ ha
  have h2 : IntegrableOn (fun x : ℝ => (ℓ * x) ^ (-γ) * (1 + ℓ * x) ^ (-a)) (Ioi 0) := by
    rw [integrableOn_Ioi_comp_mul_left_iff (fun u : ℝ => u ^ (-γ) * (1 + u) ^ (-a)) 0 hℓ]
    simpa using hg
  have h3 : IntegrableOn (fun x : ℝ => ℓ ^ γ * ((ℓ * x) ^ (-γ) * (1 + ℓ * x) ^ (-a))) (Ioi 0) :=
    Integrable.const_mul h2 _
  exact h3.congr_fun (fun x hx => (scrn_h_eq hℓ x hx).symm) measurableSet_Ioi

lemma scrn_int_scaled {γ a ℓ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ < 1) (ha : 1 < a) (hℓ : 0 < ℓ) :
    ∫ x in Ioi (0:ℝ), x ^ (-γ) * (1 + ℓ * x) ^ (-a) = ℓ ^ (γ - 1) * scrnJ γ a := by
  have e := integral_comp_mul_left_Ioi (fun u : ℝ => u ^ (-γ) * (1 + u) ^ (-a)) 0 hℓ
  simp only [mul_zero, smul_eq_mul] at e
  calc ∫ x in Ioi (0:ℝ), x ^ (-γ) * (1 + ℓ * x) ^ (-a)
      = ∫ x in Ioi (0:ℝ), ℓ ^ γ * ((ℓ * x) ^ (-γ) * (1 + ℓ * x) ^ (-a)) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => scrn_h_eq hℓ x hx)
    _ = ℓ ^ γ * (ℓ⁻¹ * scrnJ γ a) := by rw [integral_const_mul, e]; rfl
    _ = ℓ ^ (γ - 1) * scrnJ γ a := by
        rw [Real.rpow_sub hℓ, Real.rpow_one]; ring

lemma scrnJ_nonneg (γ a : ℝ) : 0 ≤ scrnJ γ a := by
  unfold scrnJ
  exact setIntegral_nonneg measurableSet_Ioi (fun u hu => by
    have : 0 < u := hu
    positivity)

/-- Partial sums of `j^{-γ}(1+ℓj)^{-a}`. -/
lemma scrn_sum_pos {γ a : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ < 1) (ha : 1 < a) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, ((j : ℝ) ^ (-γ) * (1 + ℓ * j) ^ (-a)) ≤ ℓ ^ (γ - 1) * scrnJ γ a := by
  set h : ℝ → ℝ := fun x => x ^ (-γ) * (1 + ℓ * x) ^ (-a) with hh
  have hint := scrn_integrableOn_h hγ0 hγ ha hℓ
  have hanti : AntitoneOn h (Ioc 0 (0 + (n : ℝ))) := by
    intro x hx y hy hxy
    have hx0 : 0 < x := hx.1
    simp only [hh]
    have e1 : y ^ (-γ) ≤ x ^ (-γ) := Real.rpow_le_rpow_of_nonpos hx0 hxy (by linarith)
    have e2 : (1 + ℓ * y) ^ (-a) ≤ (1 + ℓ * x) ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos (by nlinarith) (by nlinarith) (by linarith)
    have p2 : 0 ≤ (1 + ℓ * y) ^ (-a) := Real.rpow_nonneg (by nlinarith [hy.1]) _
    exact mul_le_mul e1 e2 p2 (Real.rpow_nonneg hx0.le _)
  have hIcc : IntegrableOn h (Icc 0 (0 + (n : ℝ))) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact hint.mono_set (by intro x hx; exact hx.1)
  have key := hanti.sum_le_integral_of_integrableOn hIcc
  have hsum : ∑ i ∈ Finset.range n, h (0 + ((i + 1 : ℕ) : ℝ)) =
      ∑ j ∈ Finset.Icc 1 n, ((j : ℝ) ^ (-γ) * (1 + ℓ * j) ^ (-a)) := by
    have gen : ∀ m : ℕ, ∑ i ∈ Finset.range m, h (0 + ((i + 1 : ℕ) : ℝ)) =
        ∑ j ∈ Finset.Icc 1 m, ((j : ℝ) ^ (-γ) * (1 + ℓ * j) ^ (-a)) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]
        simp [hh]
    exact gen n
  rw [hsum] at key
  refine key.trans ?_
  rw [zero_add, intervalIntegral.integral_of_le (by positivity), ← scrn_int_scaled hγ0 hγ ha hℓ]
  refine setIntegral_mono_set hint ?_ ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have : 0 < x := hx
    have : 0 ≤ 1 + ℓ * x := by nlinarith
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg this _)
  · exact Filter.Eventually.of_forall (fun x hx => hx.1)



section Lat

/-- The one-dimensional weight `(max 1 |j|)^{-γ} (1 + ℓ|j|)^{-a}`. -/
def scrnU (γ a ℓ : ℝ) (j : ℤ) : ℝ := (max 1 |(j : ℝ)|) ^ (-γ) * (1 + ℓ * |(j : ℝ)|) ^ (-a)

lemma scrnU_nonneg (γ a : ℝ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (j : ℤ) : 0 ≤ scrnU γ a ℓ j := by
  unfold scrnU
  have h1 : 0 < max 1 |(j : ℝ)| := lt_of_lt_of_le one_pos (le_max_left _ _)
  have h2 : 0 ≤ 1 + ℓ * |(j : ℝ)| := by positivity
  exact mul_nonneg (Real.rpow_nonneg h1.le _) (Real.rpow_nonneg h2 _)

lemma scrnU_neg (γ a ℓ : ℝ) (j : ℤ) : scrnU γ a ℓ (-j) = scrnU γ a ℓ j := by
  simp [scrnU]

lemma scrnU_zero (γ a ℓ : ℝ) : scrnU γ a ℓ 0 = 1 := by
  simp [scrnU]

lemma scrnU_nat {γ a : ℝ} (ℓ : ℝ) {i : ℕ} (hi : 1 ≤ i) :
    scrnU γ a ℓ (i : ℤ) = (i : ℝ) ^ (-γ) * (1 + ℓ * i) ^ (-a) := by
  have : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have h0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  simp [scrnU, abs_of_nonneg h0, max_eq_right this]

lemma scrn_box_sum_eq (u : ℤ → ℝ) (hu : ∀ j, u (-j) = u j) (n : ℕ) :
    ∑ j ∈ Finset.Icc (-(n : ℤ)) n, u j = u 0 + 2 * ∑ i ∈ Finset.Icc 1 n, u (i : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : Finset.Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) =
        insert (-((n + 1 : ℕ) : ℤ)) (insert ((n + 1 : ℕ) : ℤ) (Finset.Icc (-(n : ℤ)) n)) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    have n1 : (-((n + 1 : ℕ) : ℤ)) ∉ insert ((n + 1 : ℕ) : ℤ) (Finset.Icc (-(n : ℤ)) n) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have n2 : ((n + 1 : ℕ) : ℤ) ∉ Finset.Icc (-(n : ℤ)) n := by
      simp only [Finset.mem_Icc]; omega
    rw [e, Finset.sum_insert n1, Finset.sum_insert n2, ih,
      Finset.sum_Icc_succ_top (by omega), hu]
    ring

lemma scrn_sum_box1 {γ a : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ < 1) (ha : 1 < a) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (n : ℕ) :
    ∑ j ∈ Finset.Icc (-(n : ℤ)) n, scrnU γ a ℓ j ≤ 1 + 2 * (ℓ ^ (γ - 1) * scrnJ γ a) := by
  rw [scrn_box_sum_eq _ (scrnU_neg γ a ℓ) n, scrnU_zero]
  have : ∑ i ∈ Finset.Icc 1 n, scrnU γ a ℓ (i : ℤ) =
      ∑ i ∈ Finset.Icc 1 n, ((i : ℝ) ^ (-γ) * (1 + ℓ * i) ^ (-a)) :=
    Finset.sum_congr rfl fun i hi => scrnU_nat ℓ (Finset.mem_Icc.1 hi).1
  rw [this]
  have := scrn_sum_pos hγ0 hγ ha hℓ n
  linarith

variable {d : ℕ}

/-- The `d`-dimensional weight `(max 1 |k|)^{-g} (1 + ℓ|k|)^{-L}` on `ℤ^d`. -/
def scrnW (d : ℕ) (g L ℓ : ℝ) (k : Lattice d) : ℝ :=
  (max 1 (Lattice.enorm k)) ^ (-g) * (1 + ℓ * Lattice.enorm k) ^ (-L)

lemma scrnW_nonneg (g L : ℝ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (k : Lattice d) : 0 ≤ scrnW d g L ℓ k := by
  unfold scrnW
  have h1 : 0 < max 1 (Lattice.enorm k) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have h2 : 0 ≤ 1 + ℓ * Lattice.enorm k := by
    have : 0 ≤ Lattice.enorm k := norm_nonneg _
    positivity
  exact mul_nonneg (Real.rpow_nonneg h1.le _) (Real.rpow_nonneg h2 _)

lemma abs_le_enorm (k : Lattice d) (i : Fin d) : |(k i : ℝ)| ≤ Lattice.enorm k := by
  unfold Lattice.enorm Lattice.toEuc
  have := PiLp.norm_apply_le (WithLp.toLp 2 fun i : Fin d => (k i : ℝ)) i
  simpa using this

lemma scrnW_le_prod (hd : 0 < d) {g L ℓ : ℝ} (hg : 0 ≤ g) (hL : 0 ≤ L) (hℓ : 0 ≤ ℓ)
    (k : Lattice d) :
    scrnW d g L ℓ k ≤ ∏ i, scrnU (g / d) (L / d) ℓ (k i) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  set E := Lattice.enorm k with hE
  have hE0 : 0 ≤ E := norm_nonneg _
  have hM : 0 < max 1 E := lt_of_lt_of_le one_pos (le_max_left _ _)
  have each : ∀ i : Fin d, ((max 1 E) ^ (-(g / d)) * (1 + ℓ * E) ^ (-(L / d))) ≤
      scrnU (g / d) (L / d) ℓ (k i) := by
    intro i
    unfold scrnU
    have hi := abs_le_enorm k i
    have h1 : (max 1 E) ^ (-(g / d)) ≤ (max 1 |(k i : ℝ)|) ^ (-(g / d)) :=
      Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le one_pos (le_max_left _ _))
        (max_le_max le_rfl hi) (by have : 0 ≤ g / d := by positivity
                                   linarith)
    have h2 : (1 + ℓ * E) ^ (-(L / d)) ≤ (1 + ℓ * |(k i : ℝ)|) ^ (-(L / d)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [abs_nonneg (k i : ℝ)])
        (by have : 0 ≤ L / d := by positivity
            linarith)
    have p2 : 0 ≤ (1 + ℓ * E) ^ (-(L / d)) := Real.rpow_nonneg (by positivity) _
    have p1 : 0 ≤ (max 1 |(k i : ℝ)|) ^ (-(g / d)) :=
      Real.rpow_nonneg (lt_of_lt_of_le one_pos (le_max_left _ _)).le _
    exact mul_le_mul h1 h2 p2 p1
  calc scrnW d g L ℓ k
      = ((max 1 E) ^ (-(g / d)) * (1 + ℓ * E) ^ (-(L / d))) ^ d := by
        unfold scrnW
        rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hM.le,
          ← Real.rpow_mul (by positivity)]
        congr 2 <;> · field_simp
    _ = ∏ _i : Fin d, ((max 1 E) ^ (-(g / d)) * (1 + ℓ * E) ^ (-(L / d))) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∏ i, scrnU (g / d) (L / d) ℓ (k i) := by
        have p2 : 0 ≤ (1 + ℓ * E) ^ (-(L / d)) := Real.rpow_nonneg (by positivity) _
        have p0 : 0 ≤ (max 1 E) ^ (-(g / d)) * (1 + ℓ * E) ^ (-(L / d)) :=
          mul_nonneg (Real.rpow_nonneg hM.le _) p2
        exact Finset.prod_le_prod₀ (fun i _ => p0) (fun i _ => each i)

/-- Lattice sums: `∑_{k∈ℤ^d} (max 1 |k|)^{-g} (1+ℓ|k|)^{-L} ≤ C ℓ^{-(d-g)}` for `ℓ ∈ (0,1]`,
`0 ≤ g < d`, `L > d` (and the sum is summable). -/
theorem scrn_latsum (hd : 0 < d) {g L : ℝ} (hg0 : 0 ≤ g) (hgd : g < d) (hL : (d : ℝ) < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 →
      Summable (scrnW d g L ℓ) ∧ ∑' k, scrnW d g L ℓ k ≤ C * ℓ ^ (-((d : ℝ) - g)) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hγ0 : 0 ≤ g / d := by positivity
  have hγ1 : g / d < 1 := (div_lt_one hd').2 hgd
  have ha : 1 < L / d := by rw [lt_div_iff₀ hd']; linarith
  refine ⟨(1 + 2 * scrnJ (g / d) (L / d)) ^ d, by have := scrnJ_nonneg (g / d) (L / d); positivity,
    fun ℓ hℓ hℓ1 => ?_⟩
  have hL0 : 0 ≤ L := by linarith
  have hbox : ∀ n : ℕ, ∑ k ∈ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(n : ℤ)) n),
      scrnW d g L ℓ k ≤ (1 + 2 * (ℓ ^ (g / d - 1) * scrnJ (g / d) (L / d))) ^ d := by
    intro n
    calc ∑ k ∈ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(n : ℤ)) n), scrnW d g L ℓ k
        ≤ ∑ k ∈ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(n : ℤ)) n),
            ∏ i, scrnU (g / d) (L / d) ℓ (k i) :=
          Finset.sum_le_sum fun k _ => scrnW_le_prod hd hg0 hL0 hℓ.le k
      _ = ∏ _i : Fin d, ∑ j ∈ Finset.Icc (-(n : ℤ)) n, scrnU (g / d) (L / d) ℓ j := by
          rw [Finset.prod_univ_sum]
      _ ≤ ∏ _i : Fin d, (1 + 2 * (ℓ ^ (g / d - 1) * scrnJ (g / d) (L / d))) :=
          Finset.prod_le_prod₀ (fun _ _ => Finset.sum_nonneg fun j _ => scrnU_nonneg _ _ hℓ.le j)
            (fun _ _ => scrn_sum_box1 hγ0 hγ1 ha hℓ n)
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hfin : ∀ F : Finset (Lattice d), ∑ k ∈ F, scrnW d g L ℓ k ≤
      (1 + 2 * (ℓ ^ (g / d - 1) * scrnJ (g / d) (L / d))) ^ d := by
    intro F
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ k ∈ F, ∀ i, |k i| ≤ n := by
      refine ⟨F.sup fun k => Finset.univ.sup fun i => (k i).natAbs, fun k hk i => ?_⟩
      have h1 : (k i).natAbs ≤ Finset.univ.sup fun i => (k i).natAbs :=
        Finset.le_sup (f := fun i => (k i).natAbs) (Finset.mem_univ i)
      have h2 : (Finset.univ.sup fun i => (k i).natAbs) ≤ F.sup fun k => Finset.univ.sup fun i => (k i).natAbs :=
        Finset.le_sup (f := fun k => Finset.univ.sup fun i => (k i).natAbs) hk
      have := h1.trans h2
      rw [Int.abs_eq_natAbs]
      exact_mod_cast this
    calc ∑ k ∈ F, scrnW d g L ℓ k
        ≤ ∑ k ∈ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(n : ℤ)) n), scrnW d g L ℓ k := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => scrnW_nonneg g L hℓ.le k)
          intro k hk
          rw [Fintype.mem_piFinset]
          intro i
          have := hn k hk i
          rw [Finset.mem_Icc]
          exact ⟨by linarith [neg_abs_le (k i)], le_trans (le_abs_self _) this⟩
      _ ≤ _ := hbox n
  have hsum : Summable (scrnW d g L ℓ) :=
    summable_of_sum_le (fun k => scrnW_nonneg g L hℓ.le k) hfin
  refine ⟨hsum, ?_⟩
  refine (hsum.tsum_le_of_sum_le hfin).trans ?_
  have hJ := scrnJ_nonneg (g / d) (L / d)
  have hpow : ℓ ^ (g / d - 1) ≥ 1 := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hℓ hℓ1 (by linarith)
  have h1 : 1 + 2 * (ℓ ^ (g / d - 1) * scrnJ (g / d) (L / d)) ≤
      (1 + 2 * scrnJ (g / d) (L / d)) * ℓ ^ (g / d - 1) := by nlinarith
  calc (1 + 2 * (ℓ ^ (g / d - 1) * scrnJ (g / d) (L / d))) ^ d
      ≤ ((1 + 2 * scrnJ (g / d) (L / d)) * ℓ ^ (g / d - 1)) ^ d :=
        pow_le_pow_left₀ (by positivity) h1 d
    _ = (1 + 2 * scrnJ (g / d) (L / d)) ^ d * ℓ ^ (-((d : ℝ) - g)) := by
        rw [mul_pow]
        congr 1
        rw [← Real.rpow_natCast (ℓ ^ (g / d - 1)) d, ← Real.rpow_mul hℓ.le]
        congr 1
        field_simp
        ring

end Lat

end HRS
