import HRS.Equilibrium.Parametrix.PX7AuxD

/-!
# Packet PX7, file E: generator bridge, time derivative of the pair semigroup, PDE and left inverse
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.PX7

open HRS.PDE.MFAdjoint

variable {d : ℕ}

/-! ### Two-level passage of operators through convergent sums -/

section Pass2

variable {ι : Type*} {ma mb : ℝ} {F : Coeff d → Coeff d} {M : ℝ}

theorem px7_F_fin2 (hF : OpOK2 ma mb F M) (ha : 0 ≤ ma) (v : ι → Coeff d)
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) (hv : ∀ i, MemHs ma (v i)) (I : Finset ι) :
    F (fun k => ∑ i ∈ I, z i * v i k) = fun k => ∑ i ∈ I, z i * F (v i) k := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have : (fun _ : Lattice d => (0 : ℂ)) = (0 : Coeff d) := rfl
    rw [this, hF.zero]
  | insert a I ha' ih =>
    have e : (fun k => ∑ i ∈ insert a I, z i * v i k) =
        (z a • v a) + fun k => ∑ i ∈ I, z i * v i k := by
      funext k; simp [Finset.sum_insert ha']
    rw [e, hF.add _ _ (MFAdjoint.memHs_smul_coeff (hv a) (z a)) (px7_fin_sum_Hs ha v z hz hv I).1,
      hF.smul _ _ (hv a), ih]
    funext k; simp [Finset.sum_insert ha']

theorem px7_pass2 (hF : OpOK2 ma mb F M) (ha : 0 ≤ ma) (hb : 0 ≤ mb) (v : ι → Coeff d)
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) (hv : ∀ i, MemHs ma (v i))
    (hs : Summable fun i => hsNorm ma (v i)) (k : Lattice d) :
    HasSum (fun i => z i * F (v i) k) (F (fun k' => ∑' i, z i * v i k') k) := by
  classical
  obtain ⟨hH, hcm, hcn⟩ := px7_sum_Hs ha v z hz hv hs
  set c : Coeff d := fun k' => ∑' i, z i * v i k' with hc
  have hM := hF.nonneg
  have hcoord : ∀ k', Summable fun i => z i * v i k' := fun k' => (hH k').summable
  have htail : ∀ I : Finset ι, ‖F c k - ∑ i ∈ I, z i * F (v i) k‖ ≤
      M * ∑' i : {i // i ∉ I}, hsNorm ma (v i) := by
    intro I
    have hs' : Summable fun i : {i // i ∉ I} => hsNorm ma (v i) := hs.subtype _
    obtain ⟨hH', hm', hn'⟩ := px7_sum_Hs ha (fun i : {i // i ∉ I} => v i) (fun i => z i)
      (fun i => hz i) (fun i => hv i) hs'
    set tl : Coeff d := fun k' => ∑' i : {i // i ∉ I}, z i * v i k' with htl
    have hsplit : c = (fun k' => ∑ i ∈ I, z i * v i k') + tl := by
      funext k'
      exact ((hcoord k').sum_add_tsum_subtype_compl I).symm
    have hFc : F c = F (fun k' => ∑ i ∈ I, z i * v i k') + F tl := by
      rw [hsplit]; exact hF.add _ _ (px7_fin_sum_Hs ha v z hz hv I).1 hm'
    have : F c k - ∑ i ∈ I, z i * F (v i) k = F tl k := by
      rw [hFc, px7_F_fin2 hF ha v z hz hv I]; simp
    rw [this]
    calc ‖F tl k‖ ≤ hsNorm mb (F tl) := norm_coeff_le_hsNorm_of_nonneg hb (hF.mem _ hm') k
      _ ≤ M * hsNorm ma tl := hF.bound _ hm'
      _ ≤ M * ∑' i : {i // i ∉ I}, hsNorm ma (v i) := mul_le_mul_of_nonneg_left hn' hM
  have hlim : Tendsto (fun I : Finset ι => M * ∑' i : {i // i ∉ I}, hsNorm ma (v i)) atTop (𝓝 0) := by
    simpa using (tendsto_tsum_compl_atTop_zero (fun i => hsNorm ma (v i))).const_mul M
  have : Tendsto (fun I : Finset ι => ∑ i ∈ I, z i * F (v i) k) atTop (𝓝 (F c k)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun I => norm_nonneg _) (fun I => ?_) hlim
    rw [norm_sub_rev]; exact htail I
  simpa [HasSum] using this

end Pass2

/-! ### Reality, two-level -/

section Real2

variable {ma : ℝ} {F : Coeff d → Coeff d}

theorem px7_colOp_RS2 (hrc : ∀ x, MemHs ma x → F (reflConj x) = reflConj (F x))
    {b : ℝ} {u : Arr d} (hu : Mem2 ma b u) (h : RS u) : RS (colOp F u) := by
  intro k l
  show F (col u (-l)) (-k) = conj (F (col u l) k)
  rw [px7_col_neg h, hrc _ (px7_mem2_col hu l)]
  simp [reflConj]

theorem px7_rowOp_RS2 (hrc : ∀ x, MemHs ma x → F (reflConj x) = reflConj (F x))
    {a : ℝ} {u : Arr d} (hu : Mem2 a ma u) (h : RS u) : RS (rowOp F u) := by
  have := px7_colOp_RS2 hrc (Mem2.transp hu).1 (px7_RS_tr h)
  rw [px7_rowOp_eq]
  exact px7_RS_tr this

end Real2

/-! ### The bridge: classical generator of an `ev` slice -/

section Bridge

variable {D : DynData d} {ρ : Torus d → ℝ} {m : ℕ} {T : ℝ → Coeff d → Coeff d} {Ah : Coeff d → Coeff d}

theorem OV.reflAh (hOV : OV D ρ m T Ah) {x : Coeff d} (hx : MemHs ((m + 2 : ℕ) : ℝ) x) :
    Ah (reflConj x) = reflConj (Ah x) := by
  obtain ⟨ha, -⟩ := px7_hs_reP hx
  obtain ⟨hb, -⟩ := px7_hs_imP hx
  set a := px7_reP x with hadef
  set b := px7_imP x with hbdef
  have har : ∀ k, a (-k) = conj (a k) := px7_reP_real x
  have hbr : ∀ k, b (-k) = conj (b k) := px7_imP_real x
  have hTa := hOV.Ah_real a ha (px7_reP_real x)
  have hTb := hOV.Ah_real b hb (px7_imP_real x)
  have hxs : x = a + Complex.I • b := by
    funext k; have := congrFun (px7_split x) k; simpa using this
  have hrx : reflConj x = a + (-Complex.I) • b := by
    funext k
    have e1 : x (-k) = a (-k) + Complex.I * b (-k) := by
      have := congrFun (px7_split x) (-k); simpa using this
    simp only [reflConj, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [e1]
    simp only [map_add, map_mul, Complex.conj_I, har, hbr, Complex.conj_conj]
  have hIb : MemHs ((m + 2 : ℕ) : ℝ) (Complex.I • b) := MFAdjoint.memHs_smul_coeff hb _
  have hnIb : MemHs ((m + 2 : ℕ) : ℝ) ((-Complex.I) • b) := MFAdjoint.memHs_smul_coeff hb _
  have l1 : Ah x = Ah a + Complex.I • Ah b := by
    conv_lhs => rw [hxs]
    rw [hOV.Ah_add _ _ ha hIb, hOV.Ah_smul]
  have l2 : Ah (reflConj x) = Ah a + (-Complex.I) • Ah b := by
    rw [hrx, hOV.Ah_add _ _ ha hnIb, hOV.Ah_smul]
  rw [l2, l1]
  funext k
  simp only [reflConj, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, Complex.conj_I]
  have ea : conj (Ah a (-k)) = Ah a k := by
    have := hTa (-k); rw [neg_neg] at this; rw [← this]
  have eb : conj (Ah b (-k)) = Ah b k := by
    have := hTb (-k); rw [neg_neg] at this; rw [← this]
  rw [ea, eb]

theorem px7_acol_Hs2 {ma mb : ℝ} (ha : 0 ≤ ma) (hd : (d : ℝ) < 2 * mb) {u : Arr d} (hu : Mem2 ma mb u)
    (y : Torus d) : MemHs ma (acol u y) := by
  obtain ⟨C, hC, h⟩ := px7_col_norm_summable (m := ma) (b := mb) hd
  obtain ⟨hs, -⟩ := h u hu
  obtain ⟨-, hmem, -⟩ := px7_sum_Hs ha (fun l => col u l) (fun l => Torus.mode l y)
    (fun l => (Torus.norm_mode l y).le) (px7_mem2_col hu) hs
  have e : acol u y = fun k => ∑' l, Torus.mode l y * col u l k := by
    funext k; exact tsum_congr fun l => by simp [col, mul_comm]
  rw [e]; exact hmem

theorem px7_Ah_acol (hOV : OV D ρ m T Ah) {w : Arr d} (hw : Mem2 ((m + 2 : ℕ) : ℝ) (m : ℝ) w)
    (y : Torus d) : Ah (acol w y) = acol (colOp Ah w) y := by
  obtain ⟨K, hF⟩ := hOV.opokAh
  obtain ⟨C, hC, h⟩ := px7_col_norm_summable (m := ((m + 2 : ℕ) : ℝ)) (b := (m : ℝ)) hOV.hd
  obtain ⟨hs, -⟩ := h w hw
  have e : acol w y = fun k => ∑' l, Torus.mode l y * col w l k := by
    funext k; exact tsum_congr fun l => by simp [col, mul_comm]
  rw [e]
  funext k
  have := px7_pass2 hF (by positivity) hOV.hm0 (fun l => col w l) (fun l => Torus.mode l y)
    (fun l => (Torus.norm_mode l y).le) (px7_mem2_col hw) hs k
  rw [← this.tsum_eq]
  refine tsum_congr fun l => ?_
  simp only [colOp]
  ring

theorem px7_bridge_x (hOV : OV D ρ m T Ah) {w : Arr d} (hw : Mem2 ((m + 2 : ℕ) : ℝ) (m : ℝ) w)
    (hRS : RS w) (y : Torus d) :
    centeredGen D ρ (fun x' => ev w x' y) = fun x => ev (colOp Ah w) x y := by
  obtain ⟨K, hF⟩ := hOV.opokAh
  have hmR : (m : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by push_cast; linarith
  have hw0 : Mem2 (m : ℝ) (m : ℝ) w := (Mem2.mono hmR le_rfl hw).1
  have hs := px7_summable_of_mem2 hOV.hd hw0
  have hc0 : Mem2 (m : ℝ) (m : ℝ) (colOp Ah w) := (px7_colOp_mem hF hw).1
  have hs' := px7_summable_of_mem2 hOV.hd hc0
  have e : (fun x' => ev w x' y) = toFun (acol w y) := funext fun x => px7_ev_eq_toFun hs x y
  have hmem := px7_acol_Hs2 (by positivity) hOV.hd hw y
  have hreal := px7_acol_real hRS hs y
  obtain ⟨-, hbr⟩ := hOV.bridge _ hreal hmem
  rw [e, hbr, px7_Ah_acol hOV hw y]
  funext x
  exact (px7_ev_eq_toFun hs' x y).symm

theorem px7_bridge_AA (hOV : OV D ρ m T Ah) {w : Arr d} (hw1 : Mem2 ((m + 2 : ℕ) : ℝ) (m : ℝ) w)
    (hw2 : Mem2 (m : ℝ) ((m + 2 : ℕ) : ℝ) w) (hRS : RS w) (x y : Torus d) :
    centeredGen D ρ (fun x' => ev w x' y) x + centeredGen D ρ (fun y' => ev w x y') y =
      ev (AA Ah w) x y := by
  obtain ⟨K, hF⟩ := hOV.opokAh
  have h1 := congrFun (px7_bridge_x hOV hw1 hRS y) x
  have e : (fun y' => ev w x y') = fun y' => ev (tr w) y' x := funext fun y' => (px7_ev_tr w y' x).symm
  have hw2' : Mem2 ((m + 2 : ℕ) : ℝ) (m : ℝ) (tr w) := (Mem2.transp hw2).1
  have h2 := congrFun (px7_bridge_x hOV hw2' (px7_RS_tr hRS) x) y
  rw [e]
  rw [h1, h2, ← px7_ev_tr (colOp Ah (tr w)) x y, ← px7_rowOp_eq]
  have hc := (px7_colOp_mem hF hw1).1
  have hr := (px7_rowOp_mem hF hw2).1
  rw [← px7_ev_add (px7_summable_of_mem2 hOV.hd hc) (px7_summable_of_mem2 hOV.hd hr)]
  rfl

end Bridge

/-! ### Scalar and array calculus -/

theorem px7_deriv_of_right {f g : ℝ → ℝ} (hf : ContinuousOn f (Set.Ici 0))
    (hg : ContinuousOn g (Set.Ici 0))
    (hr : ∀ t, 0 ≤ t → HasDerivWithinAt f (g t) (Set.Ici t) t) :
    ∀ t, 0 ≤ t → HasDerivWithinAt f (g t) (Set.Ici 0) t := by
  intro t ht
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0; exact hr 0 le_rfl
  · set g' : ℝ → ℝ := fun u => g (max u 0) with hg'def
    have hg' : Continuous g' :=
      hg.comp_continuous (continuous_id.max continuous_const) (fun u => Set.mem_Ici.2 (le_max_right _ _))
    set I : ℝ → ℝ := fun s => ∫ u in (0 : ℝ)..s, g' u with hIdef
    have hI : ∀ s, HasDerivAt I (g' s) s := fun s => (hg'.integral_hasStrictDerivAt 0 s).hasDerivAt
    have hIc : Continuous I := continuous_iff_continuousAt.2 fun s => (hI s).continuousAt
    have hF : ∀ b : ℝ, ∀ s ∈ Set.Icc 0 b, f s - I s = f 0 - I 0 := by
      intro b s hs
      refine constant_of_has_deriv_right_zero (f := fun s => f s - I s) (a := 0) (b := b)
        ((hf.mono Set.Icc_subset_Ici_self).sub hIc.continuousOn) (fun x hx => ?_) s hs
      have h1 := hr x hx.1
      have h2 := (hI x).hasDerivWithinAt (s := Set.Ici x)
      have := h1.sub h2
      have h4 : g x - g' x = 0 := by simp [hg'def, max_eq_left hx.1]
      rw [h4] at this
      exact this
    have hI0 : I 0 = 0 := intervalIntegral.integral_same
    have hev : f =ᶠ[𝓝 t] fun s => f 0 + I s := by
      filter_upwards [Ioi_mem_nhds hpos] with s hs
      have := hF s s ⟨le_of_lt hs, le_rfl⟩
      simp only [hI0] at this
      linarith
    have h3 : HasDerivAt (fun s => f 0 + I s) (g' t) t := (hI t).const_add _
    have e : g t = g' t := by simp [hg'def, max_eq_left hpos.le]
    rw [e]
    exact (h3.congr_of_eventuallyEq hev).hasDerivWithinAt

theorem px7_ev_bound {ma : ℝ} (hd : (d : ℝ) < 2 * ma) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u : Arr d, Mem2 ma ma u → ∀ x y : Torus d, |ev u x y| ≤ A * nrm2 ma ma u := by
  obtain ⟨C, hC, hcs⟩ := px7_cs (d := d) ma ma 0 0 (by simpa using hd) (by simpa using hd)
  refine ⟨C, hC, fun u hu x y => ?_⟩
  obtain ⟨h1, h2⟩ := hcs u hu
  have hs : Summable fun p : Lattice d × Lattice d => ‖u p.1 p.2‖ := by simpa using h1
  refine (px7_abs_ev_le hs x y).trans ?_
  simpa using h2

theorem px7_mem2_quot {a b : ℝ} {u v w : Arr d} (hu : Mem2 a b u) (hv : Mem2 a b v) (hw : Mem2 a b w)
    (h : ℝ) : Mem2 a b (fun k l => (u k l - v k l) / (h : ℂ) - w k l) := by
  have e : (fun k l => (u k l - v k l) / (h : ℂ) - w k l) =
      ((1 / (h : ℂ)) • (u + (-1 : ℂ) • v)) + (-1 : ℂ) • w := by
    funext k l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e]
  exact (Mem2.add ((Mem2.add hu (Mem2.smul hv _).1).1.smul _).1 (Mem2.smul hw _).1).1

theorem px7_summ_smul {u : Arr d} (hu : Summable fun p : Lattice d × Lattice d => ‖u p.1 p.2‖) (c : ℂ) :
    Summable fun p : Lattice d × Lattice d => ‖(c • u) p.1 p.2‖ := by
  refine (hu.mul_left ‖c‖).congr fun p => ?_
  simp [norm_mul]

theorem px7_summ_add {u v : Arr d} (hu : Summable fun p : Lattice d × Lattice d => ‖u p.1 p.2‖)
    (hv : Summable fun p : Lattice d × Lattice d => ‖v p.1 p.2‖) :
    Summable fun p : Lattice d × Lattice d => ‖(u + v) p.1 p.2‖ :=
  Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => norm_add_le _ _) (hu.add hv)

theorem px7_ev_quot {u v w : Arr d} (hu : Summable fun p : Lattice d × Lattice d => ‖u p.1 p.2‖)
    (hv : Summable fun p : Lattice d × Lattice d => ‖v p.1 p.2‖)
    (hw : Summable fun p : Lattice d × Lattice d => ‖w p.1 p.2‖) {h : ℝ} (hh : h ≠ 0) (x y : Torus d) :
    ev (fun k l => (u k l - v k l) / (h : ℂ) - w k l) x y = (ev u x y - ev v x y) / h - ev w x y := by
  have hh' : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hh
  have e : (fun k l => (u k l - v k l) / (h : ℂ) - w k l) =
      (((1 / h : ℝ) : ℂ) • u + ((-1 / h : ℝ) : ℂ) • v) + ((-1 : ℝ) : ℂ) • w := by
    funext k l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    field_simp
    ring
  have s1 := px7_summ_smul hu ((1 / h : ℝ) : ℂ)
  have s2 := px7_summ_smul hv ((-1 / h : ℝ) : ℂ)
  have s3 := px7_summ_smul hw ((-1 : ℝ) : ℂ)
  rw [e, px7_ev_add (px7_summ_add s1 s2) s3, px7_ev_add s1 s2, px7_ev_smul, px7_ev_smul, px7_ev_smul]
  push_cast
  field_simp
  ring

/-! ### Time derivative of the tensor semigroup -/

section Deriv

variable {D : DynData d} {ρ : Torus d → ℝ} {m : ℕ} {T : ℝ → Coeff d → Coeff d} {Ah : Coeff d → Coeff d}

theorem px7_PP_D (hOV : OV D ρ m T Ah) {τ : ℝ} (hτ : 0 ≤ τ) {u : Arr d}
    (h1 : Mem2 ((m + 2 : ℕ) : ℝ) (m : ℝ) u) (h2 : Mem2 (m : ℝ) ((m + 2 : ℕ) : ℝ) u) :
    Mem2 ((m + 2 : ℕ) : ℝ) (m : ℝ) (PP T τ u) ∧ Mem2 (m : ℝ) ((m + 2 : ℕ) : ℝ) (PP T τ u) := by
  obtain ⟨M, c, hM, hc, hop⟩ := hOV.opok
  obtain ⟨M', c', hM', hc', hop2⟩ := hOV.opok2
  exact ⟨(px7_rowOp_mem (hop τ hτ) (px7_colOp_mem (hop2 τ hτ) h1).1).1,
    (px7_rowOp_mem (hop2 τ hτ) (px7_colOp_mem (hop τ hτ) h2).1).1⟩

theorem px7_PP_add' (hOV : OV D ρ m T Ah) {τ : ℝ} (hτ : 0 ≤ τ) {u v : Arr d}
    (hu : Mem2 (m : ℝ) (m : ℝ) u) (hv : Mem2 (m : ℝ) (m : ℝ) v) :
    PP T τ (u + v) = PP T τ u + PP T τ v := by
  have := px7_PP_lin hOV hτ hu hv 1 1
  simpa using this

theorem px7_PP_smul' (hOV : OV D ρ m T Ah) {τ : ℝ} (hτ : 0 ≤ τ) {u : Arr d}
    (hu : Mem2 (m : ℝ) (m : ℝ) u) (c : ℂ) : PP T τ (c • u) = c • PP T τ u := by
  obtain ⟨M, cc, hM, hc, hop⟩ := hOV.opok
  have hF := hop τ hτ
  unfold PP
  rw [px7_colOp_smul hF hu c, px7_rowOp_smul hF (px7_colOp_mem hF hu).1 c]

theorem px7_PP_quot (hOV : OV D ρ m T Ah) {t h : ℝ} (ht : 0 ≤ t) (hh : 0 ≤ h) {u w : Arr d}
    (hu : Mem2 (m : ℝ) (m : ℝ) u) (hw : Mem2 (m : ℝ) (m : ℝ) w) :
    PP T t (fun k l => (PP T h u k l - u k l) / (h : ℂ) - w k l) =
      fun k l => (PP T (t + h) u k l - PP T t u k l) / (h : ℂ) - PP T t w k l := by
  obtain ⟨M, c, hM, hc, hP⟩ := px7_PP_bound hOV
  have hX := (hP h hh u hu).1
  have e : (fun k l => (PP T h u k l - u k l) / (h : ℂ) - w k l) =
      ((1 / (h : ℂ)) • (PP T h u + (-1 : ℂ) • u)) + (-1 : ℂ) • w := by
    funext k l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h1 : Mem2 (m : ℝ) (m : ℝ) (PP T h u + (-1 : ℂ) • u) := (Mem2.add hX (Mem2.smul hu _).1).1
  have h2 : Mem2 (m : ℝ) (m : ℝ) ((1 / (h : ℂ)) • (PP T h u + (-1 : ℂ) • u)) := (Mem2.smul h1 _).1
  rw [e, px7_PP_add' hOV ht h2 (Mem2.smul hw _).1, px7_PP_smul' hOV ht h1, px7_PP_smul' hOV ht hw,
    px7_PP_add' hOV ht hX (Mem2.smul hu _).1, px7_PP_smul' hOV ht hu, px7_PP_semi hOV ht hh hu]
  funext k l
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem px7_ev_hasDeriv_Ici {ma : ℝ} (hd : (d : ℝ) < 2 * ma) {a : ℝ → Arr d} {a' : Arr d} {t : ℝ}
    (ha : ∀ s, t ≤ s → Mem2 ma ma (a s)) (ha' : Mem2 ma ma a')
    (hlim : Tendsto (fun h : ℝ => nrm2 ma ma (fun k l => (a (t + h) k l - a t k l) / (h : ℂ) - a' k l))
      (𝓝[>] 0) (𝓝 0)) (x y : Torus d) :
    HasDerivWithinAt (fun s => ev (a s) x y) (ev a' x y) (Set.Ici t) t := by
  obtain ⟨A, hA, hev⟩ := px7_ev_bound hd
  rw [← hasDerivWithinAt_Ioi_iff_Ici, hasDerivWithinAt_iff_tendsto_slope' (by simp)]
  have hh : Tendsto (fun s : ℝ => s - t) (𝓝[>] t) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun s : ℝ => s - t) (𝓝 t) (𝓝 (t - t)) :=
        ((continuous_id.sub continuous_const).tendsto t)
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simpa using hs
  have hlim' : Tendsto (fun s : ℝ => nrm2 ma ma
      (fun k l => (a s k l - a t k l) / ((s - t : ℝ) : ℂ) - a' k l)) (𝓝[>] t) (𝓝 0) := by
    have := hlim.comp hh
    simpa only [Function.comp_def, add_sub_cancel] using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbd : ∀ᶠ s in 𝓝[>] t, ‖slope (fun s => ev (a s) x y) t s - ev a' x y‖ ≤
      A * nrm2 ma ma (fun k l => (a s k l - a t k l) / ((s - t : ℝ) : ℂ) - a' k l) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : t < s := hs
    have hne : s - t ≠ 0 := (sub_pos.2 hs').ne'
    have m1 := ha s hs'.le
    have m0 := ha t le_rfl
    have hq := px7_mem2_quot m1 m0 ha' (s - t)
    have e := px7_ev_quot (px7_summable_of_mem2 hd m1) (px7_summable_of_mem2 hd m0)
      (px7_summable_of_mem2 hd ha') hne x y
    have := hev _ hq x y
    rw [e] at this
    rw [slope_def_field, Real.norm_eq_abs]
    exact this
  exact squeeze_zero' (Filter.Eventually.of_forall fun s => norm_nonneg _) hbd (by simpa using hlim'.const_mul A)

theorem px7_PP_ev_cont (hOV : OV D ρ m T Ah) {v : Arr d} (hv : Mem2 (m : ℝ) (m : ℝ) v) (x y : Torus d) :
    ContinuousOn (fun s => ev (PP T s v) x y) (Set.Ici 0) := by
  obtain ⟨A, hA, hev⟩ := px7_ev_bound (ma := (m : ℝ)) hOV.hd
  obtain ⟨M, c, hM, hc, hP⟩ := px7_PP_bound hOV
  intro σ hσ
  have hσ' : 0 ≤ σ := hσ
  have hbound : ∀ᶠ τ in 𝓝[Set.Ici 0] σ, ‖ev (PP T τ v) x y - ev (PP T σ v) x y‖ ≤
      A * nrm2 (m : ℝ) (m : ℝ) (PP T τ v - PP T σ v) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτ' : 0 ≤ τ := hτ
    have ma := (hP τ hτ' v hv).1
    have mb := (hP σ hσ' v hv).1
    rw [← px7_ev_sub (px7_summable_of_mem2 hOV.hd ma) (px7_summable_of_mem2 hOV.hd mb), Real.norm_eq_abs]
    exact hev _ (ma.sub mb).1 x y
  have hlim : Tendsto (fun τ => A * nrm2 (m : ℝ) (m : ℝ) (PP T τ v - PP T σ v)) (𝓝[Set.Ici 0] σ) (𝓝 0) := by
    simpa using (px7_PP_cont hOV hσ' hv).const_mul A
  have : Tendsto (fun τ => ev (PP T τ v) x y) (𝓝[Set.Ici 0] σ) (𝓝 (ev (PP T σ v) x y)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero' (Filter.Eventually.of_forall fun τ => norm_nonneg _) hbound hlim
  exact this

theorem px7_PP_fwd (hOV : OV D ρ m T Ah) {u : Arr d} (hu1 : Mem2 ((m + 2 : ℕ) : ℝ) (m : ℝ) u)
    (hu2 : Mem2 (m : ℝ) ((m + 2 : ℕ) : ℝ) u) (hc : ∀ l, px7_mC ρ (col u l) = 0)
    (hr : ∀ k, px7_mC ρ (fun l => u k l) = 0) {t : ℝ} (ht : 0 ≤ t) (x y : Torus d) :
    HasDerivWithinAt (fun s => ev (PP T s u) x y) (ev (PP T t (AA Ah u)) x y) (Set.Ici t) t := by
  obtain ⟨hmAA, hlim⟩ := px7_PP_deriv hOV hu1 hu2 hc hr
  have hmR : (m : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by push_cast; linarith
  have hu0 : Mem2 (m : ℝ) (m : ℝ) u := (Mem2.mono hmR le_rfl hu1).1
  obtain ⟨M, c, hM, hc', hP⟩ := px7_PP_bound hOV
  obtain ⟨M1, hM1, hmem⟩ := px7_PP_mem hOV ht
  refine px7_ev_hasDeriv_Ici (a := fun s => PP T s u) hOV.hd
    (fun s hs => (hP s (ht.trans hs) u hu0).1) (hmem _ hmAA).1 ?_ x y
  refine squeeze_zero' (Filter.Eventually.of_forall fun h => ?_) ?_ (by simpa using hlim.const_mul M1)
  · exact Real.sqrt_nonneg _
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 ≤ h := le_of_lt hh
    have mz := px7_mem2_quot (hP h hh' u hu0).1 hu0 hmAA h
    rw [← px7_PP_quot hOV ht hh' hu0 hmAA]
    exact (hmem _ mz).2

theorem px7_PP_bwd (hOV : OV D ρ m T Ah) {u : Arr d} (hu1 : Mem2 ((m + 2 : ℕ) : ℝ) (m : ℝ) u)
    (hu2 : Mem2 (m : ℝ) ((m + 2 : ℕ) : ℝ) u) {t : ℝ} (ht : 0 ≤ t) (x y : Torus d) :
    HasDerivWithinAt (fun s => ev (PP T s u) x y) (ev (AA Ah (PP T t u)) x y) (Set.Ici t) t := by
  have hmR : (m : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by push_cast; linarith
  have hu0 : Mem2 (m : ℝ) (m : ℝ) u := (Mem2.mono hmR le_rfl hu1).1
  obtain ⟨M, c, hM, hc', hP⟩ := px7_PP_bound hOV
  obtain ⟨hv1, hv2⟩ := px7_PP_D hOV ht hu1 hu2
  obtain ⟨hcv, hrv⟩ := px7_PP_cen hOV ht hu0
  obtain ⟨hmAA, hlim⟩ := px7_PP_deriv hOV hv1 hv2 hcv hrv
  refine px7_ev_hasDeriv_Ici (a := fun s => PP T s u) hOV.hd
    (fun s hs => (hP s (ht.trans hs) u hu0).1) hmAA ?_ x y
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : 0 ≤ h := le_of_lt hh
  have e : PP T (t + h) u = PP T h (PP T t u) := by
    rw [add_comm]; exact px7_PP_semi hOV hh' ht hu0
  rw [e]

theorem px7_PP_hasDeriv (hOV : OV D ρ m T Ah) {u : Arr d} (hu1 : Mem2 ((m + 2 : ℕ) : ℝ) (m : ℝ) u)
    (hu2 : Mem2 (m : ℝ) ((m + 2 : ℕ) : ℝ) u) (hc : ∀ l, px7_mC ρ (col u l) = 0)
    (hr : ∀ k, px7_mC ρ (fun l => u k l) = 0) (x y : Torus d) :
    ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt (fun s => ev (PP T s u) x y) (ev (AA Ah (PP T t u)) x y)
      (Set.Ici 0) t := by
  have hmR : (m : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by push_cast; linarith
  have hu0 : Mem2 (m : ℝ) (m : ℝ) u := (Mem2.mono hmR le_rfl hu1).1
  obtain ⟨hmAA, -⟩ := px7_PP_deriv hOV hu1 hu2 hc hr
  have key := px7_deriv_of_right (f := fun s => ev (PP T s u) x y)
    (g := fun s => ev (PP T s (AA Ah u)) x y) (px7_PP_ev_cont hOV hu0 x y)
    (px7_PP_ev_cont hOV hmAA x y) (fun t ht => px7_PP_fwd hOV hu1 hu2 hc hr ht x y)
  intro t ht
  have e : ev (PP T t (AA Ah u)) x y = ev (AA Ah (PP T t u)) x y :=
    (uniqueDiffWithinAt_Ici t).eq_deriv _ (px7_PP_fwd hOV hu1 hu2 hc hr ht x y) (px7_PP_bwd hOV hu1 hu2 ht x y)
  rw [← e]
  exact key t ht

theorem px7_u0 (hOV : OV D ρ m T Ah) {R : Torus d → Torus d → ℝ} (hR1 : IsCk2 (m + 2 + m) R)
    (hR2 : IsCk2 (m + (m + 2)) R) :
    Mem2 ((m + 2 : ℕ) : ℝ) (m : ℝ) (PP T 0 (arr R)) ∧ Mem2 (m : ℝ) ((m + 2 : ℕ) : ℝ) (PP T 0 (arr R)) ∧
      Mem2 (m : ℝ) (m : ℝ) (PP T 0 (arr R)) ∧
      (∀ l, px7_mC ρ (col (PP T 0 (arr R)) l) = 0) ∧
      (∀ k, px7_mC ρ (fun l => PP T 0 (arr R) k l) = 0) ∧ RS (PP T 0 (arr R)) ∧
      ∀ t : ℝ, 0 ≤ t → PP T t (PP T 0 (arr R)) = PP T t (arr R) := by
  have hRm : IsCk2 (m + m) R := hR1.of_le (by exact_mod_cast (by omega : m + m ≤ m + 2 + m))
  obtain ⟨K, hK, hdata⟩ := px7_arr_data hOV
  obtain ⟨h0, hrs, -⟩ := hdata R hRm
  obtain ⟨K1, -, hK1⟩ := px7_parseval (d := d) (m + 2) m
  obtain ⟨K2, -, hK2⟩ := px7_parseval (d := d) m (m + 2)
  have hD1 := (hK1 R hR1).1
  have hD2 := (hK2 R hR2).1
  obtain ⟨p1, p2⟩ := px7_PP_D hOV (le_refl (0 : ℝ)) hD1 hD2
  obtain ⟨M, -, hmem⟩ := px7_PP_mem hOV (le_refl (0 : ℝ))
  obtain ⟨hc, hr⟩ := px7_PP_cen hOV (le_refl (0 : ℝ)) h0
  refine ⟨p1, p2, (hmem _ h0).1, hc, hr, px7_PP_RS hOV (le_refl (0 : ℝ)) h0 hrs, fun t ht => ?_⟩
  have := px7_PP_semi hOV ht (le_refl (0 : ℝ)) h0
  simpa using this.symm

theorem px7_inv_pde (hd2 : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (hρβ : IsThermalDensity (periodicRiesz d s) V β ρ)
    (hρC : Torus.IsSmooth ρ) (hpos : ∀ x, 0 < ρ x)
    (hOV : OV (mfData d s hs0 hsd V β hβ) ρ m T Ah) {R : Torus d → Torus d → ℝ}
    (hR : IsCk2 (m + m + 2) R) (hcen : DoublyCentered (withDensityReal ρ) R) (x y : Torus d) :
    -(centeredGen (mfData d s hs0 hsd V β hβ) ρ
        (fun x' => pairInverse (mfData d s hs0 hsd V β hβ) ρ R x' y) x +
      centeredGen (mfData d s hs0 hsd V β hβ) ρ
        (fun y' => pairInverse (mfData d s hs0 hsd V β hβ) ρ R x y') y) = R x y := by
  set D := mfData d s hs0 hsd V β hβ with hD
  have hR1 : IsCk2 (m + 2 + m) R := hR.of_le (by exact_mod_cast (by omega : m + 2 + m ≤ m + m + 2))
  have hR2 : IsCk2 (m + (m + 2)) R := hR.of_le (by exact_mod_cast (by omega : m + (m + 2) ≤ m + m + 2))
  have hRm : IsCk2 (m + m) R := hR.of_le (by exact_mod_cast (by omega : m + m ≤ m + m + 2))
  have hR0 : IsCk2 2 R := hR.of_le (by exact_mod_cast (by omega : 2 ≤ m + m + 2))
  obtain ⟨q1, q2, q3, qc, qr, qrs, qeq⟩ := px7_u0 hOV hR1 hR2
  obtain ⟨C0, c0, hC0, hc0, hC2⟩ := px7_pair_C2 hOV
  have hev0 : ∀ t : ℝ, 0 ≤ t → pairSemigroup D ρ t R = ev (PP T t (PP T 0 (arr R))) := by
    intro t ht
    rw [qeq t ht]; exact px7_pair_ev hOV hRm ht
  have := MFPair.centeredGen_integral_family hd2 s hs0 hsd β hβ V hV ρ hρβ hρC hpos
    (fun t => pairSemigroup D ρ t R) (C0 * cbNorm2 (m + m) R) c0 hc0
    (fun t ht => (hC2 R hRm t ht).1) (fun t ht => (hC2 R hRm t ht).2)
    (fun i hi p => px7_pair_jets hOV hRm i hi p) ?_ x y
  · rw [MFPair.pairSemigroup_zero hd2 s hs0 hsd β hβ V hV ρ hρβ hρC hpos R hR0 hcen] at this
    exact this
  · intro x y t ht
    have hv := px7_PP_hasDeriv hOV q1 q2 qc qr x y t ht
    have hb := px7_bridge_AA hOV (px7_PP_D hOV ht q1 q2).1 (px7_PP_D hOV ht q1 q2).2
      (px7_PP_RS hOV ht q3 qrs) x y
    have hfun : ∀ t' : ℝ, 0 ≤ t' → ∀ a b, pairSemigroup D ρ t' R a b = ev (PP T t' (PP T 0 (arr R))) a b :=
      fun t' ht' a b => congrFun (congrFun (hev0 t' ht') a) b
    have e1 : (fun x' => pairSemigroup D ρ t R x' y) = fun x' => ev (PP T t (PP T 0 (arr R))) x' y :=
      funext fun x' => hfun t ht x' y
    have e2 : (fun y' => pairSemigroup D ρ t R x y') = fun y' => ev (PP T t (PP T 0 (arr R))) x y' :=
      funext fun y' => hfun t ht x y'
    rw [e1, e2, hb]
    refine hv.congr (fun t' ht' => ?_) (hfun t ht x y)
    exact hfun t' ht' x y

theorem px7_left_inverse (hd2 : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (hρβ : IsThermalDensity (periodicRiesz d s) V β ρ)
    (hρC : Torus.IsSmooth ρ) (hpos : ∀ x, 0 < ρ x)
    (hOV : OV (mfData d s hs0 hsd V β hβ) ρ m T Ah) {Δ R' : Torus d → Torus d → ℝ}
    (hΔ : IsCk2 (m + m + 2) Δ) (hR' : IsCk2 (m + m) R')
    (hΔc : DoublyCentered (withDensityReal ρ) Δ)
    (heq : ∀ x y, centeredGen (mfData d s hs0 hsd V β hβ) ρ (fun x' => Δ x' y) x +
      centeredGen (mfData d s hs0 hsd V β hβ) ρ (fun y' => Δ x y') y = R' x y) :
    pairInverse (mfData d s hs0 hsd V β hβ) ρ R' = fun x y => -Δ x y := by
  set D := mfData d s hs0 hsd V β hβ with hD
  have hR1 : IsCk2 (m + 2 + m) Δ := hΔ.of_le (by exact_mod_cast (by omega : m + 2 + m ≤ m + m + 2))
  have hR2 : IsCk2 (m + (m + 2)) Δ := hΔ.of_le (by exact_mod_cast (by omega : m + (m + 2) ≤ m + m + 2))
  have hRm : IsCk2 (m + m) Δ := hΔ.of_le (by exact_mod_cast (by omega : m + m ≤ m + m + 2))
  have hR0 : IsCk2 2 Δ := hΔ.of_le (by exact_mod_cast (by omega : 2 ≤ m + m + 2))
  obtain ⟨q1, q2, q3, qc, qr, qrs, qeq⟩ := px7_u0 hOV hR1 hR2
  set u0 := PP T 0 (arr Δ) with hu0def
  have hev0 : ev u0 = Δ := by
    have := px7_pair_ev hOV hRm (le_refl (0 : ℝ))
    rw [← this]
    exact MFPair.pairSemigroup_zero hd2 s hs0 hsd β hβ V hV ρ hρβ hρC hpos Δ hR0 hΔc
  obtain ⟨hmAA, -⟩ := px7_PP_deriv hOV q1 q2 qc qr
  have hRSv : RS (AA Ah u0) := by
    have h1 := px7_colOp_RS2 (F := Ah) (fun x hx => hOV.reflAh hx) q1 qrs
    have h2 := px7_rowOp_RS2 (F := Ah) (fun x hx => hOV.reflAh hx) q2 qrs
    intro k l
    show colOp Ah u0 (-k) (-l) + rowOp Ah u0 (-k) (-l) = conj (colOp Ah u0 k l + rowOp Ah u0 k l)
    rw [h1 k l, h2 k l, map_add]
  have hvR : ev (AA Ah u0) = R' := by
    funext x y
    rw [← px7_bridge_AA hOV q1 q2 qrs x y, hev0]
    exact heq x y
  have key : ∀ t : ℝ, 0 ≤ t → ∀ x y, pairSemigroup D ρ t R' x y = ev (PP T t (AA Ah u0)) x y := by
    intro t ht x y
    rw [← hvR]
    exact px7_key hOV ht hmAA hRSv x y
  obtain ⟨Cinv, -, hinv⟩ := px7_inv_C2 hOV
  have hint0 := (hinv R' hR').2.2
  obtain ⟨A, hA, hev⟩ := px7_ev_bound (ma := (m : ℝ)) hOV.hd
  obtain ⟨M, c, hM, hc, hP⟩ := px7_PP_bound hOV
  funext x y
  set f : ℝ → ℝ := fun t => ev (PP T t u0) x y with hf
  set g : ℝ → ℝ := fun t => ev (PP T t (AA Ah u0)) x y with hg
  have hint : IntegrableOn g (Set.Ici 0) :=
    (hint0 x y).congr_fun (fun t ht => key t ht x y) measurableSet_Ici
  have hcontf : ContinuousOn f (Set.Ici 0) := px7_PP_ev_cont hOV q3 x y
  have hftc : ∀ T : ℝ, 0 ≤ T → ∫ t in (0 : ℝ)..T, g t = f T - f 0 := by
    intro T hT
    refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT
      (hcontf.mono Set.Icc_subset_Ici_self)
      (fun t ht => (px7_PP_fwd hOV q1 q2 qc qr ht.1.le x y).mono Set.Ioi_subset_Ici_self) ?_
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2
      (hint.mono_set (fun t ht => Set.mem_Ici.2 ht.1.le))
  have hT1 : Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, g t) atTop (𝓝 (∫ t in Set.Ioi (0 : ℝ), g t)) :=
    intervalIntegral_tendsto_integral_Ioi 0 (hint.mono_set Set.Ioi_subset_Ici_self) tendsto_id
  have hexp : Tendsto (fun T : ℝ => A * (M ^ 2 * Real.exp (-(2 * c) * T) * nrm2 (m : ℝ) (m : ℝ) u0))
      atTop (𝓝 0) := by
    have h1 := (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (show -(2 * c) < 0 by linarith)))
    have h2 := ((h1.const_mul (M ^ 2)).mul_const (nrm2 (m : ℝ) (m : ℝ) u0)).const_mul A
    simpa using h2
  have huT : Tendsto f atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hexp
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    obtain ⟨hm1, hn1⟩ := hP T hT u0 q3
    rw [Real.norm_eq_abs]
    exact (hev _ hm1 x y).trans (mul_le_mul_of_nonneg_left hn1 hA)
  have hf0 : f 0 = Δ x y := by
    simp only [hf]
    rw [qeq 0 le_rfl]
    exact congrFun (congrFun hev0 x) y
  have hT2 : Tendsto (fun T : ℝ => f T - f 0) atTop (𝓝 (0 - f 0)) := huT.sub tendsto_const_nhds
  have hT1' : Tendsto (fun T : ℝ => f T - f 0) atTop (𝓝 (∫ t in Set.Ioi (0 : ℝ), g t)) := by
    refine hT1.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact hftc T hT
  have hI : pairInverse D ρ R' x y = ∫ t in Set.Ioi (0 : ℝ), g t := by
    unfold pairInverse
    rw [integral_Ici_eq_integral_Ioi]
    exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => key t (le_of_lt ht) x y)
  rw [hI, tendsto_nhds_unique hT1' hT2, hf0]
  ring

end Deriv

theorem px7_m_le (d : ℕ) : px7_m d + px7_m d + 2 ≤ d + 12 := by
  unfold px7_m
  have h : (⌊(d : ℝ) / 2⌋₊ : ℝ) ≤ (d : ℝ) / 2 := Nat.floor_le (by positivity)
  have h2 : 2 * ⌊(d : ℝ) / 2⌋₊ ≤ d := by
    have : (2 * ⌊(d : ℝ) / 2⌋₊ : ℝ) ≤ d := by linarith
    exact_mod_cast this
  omega

/-- The packet PX7 statement (`PairInverseSpec`) for `D = mfData`. -/
theorem px7_spec (hd2 : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρC : Torus.IsSmooth ρ)
    (hpos : ∀ x, 0 < ρ x) (J : ℕ) (hJ : px7_m d + px7_m d + 2 ≤ J) :
    ∃ Cinv : ℝ, 0 ≤ Cinv ∧
      (∀ R : Torus d → Torus d → ℝ, IsCk2 J R → DoublyCentered (withDensityReal ρ) R →
        IsCk2 2 (pairInverse (mfData d s hs0 hsd V β hβ) ρ R) ∧
        DoublyCentered (withDensityReal ρ) (pairInverse (mfData d s hs0 hsd V β hβ) ρ R) ∧
        cbNorm2 2 (pairInverse (mfData d s hs0 hsd V β hβ) ρ R) ≤ Cinv * cbNorm2 J R ∧
        ∀ x y, -(centeredGen (mfData d s hs0 hsd V β hβ) ρ
            (fun x' => pairInverse (mfData d s hs0 hsd V β hβ) ρ R x' y) x +
          centeredGen (mfData d s hs0 hsd V β hβ) ρ
            (fun y' => pairInverse (mfData d s hs0 hsd V β hβ) ρ R x y') y) = R x y) ∧
      (∀ (R R' : Torus d → Torus d → ℝ) (a b : ℝ), IsCk2 J R → IsCk2 J R' →
        pairInverse (mfData d s hs0 hsd V β hβ) ρ (fun x y => a * R x y + b * R' x y) =
          fun x y => a * pairInverse (mfData d s hs0 hsd V β hβ) ρ R x y +
            b * pairInverse (mfData d s hs0 hsd V β hβ) ρ R' x y) ∧
      (∀ R : Torus d → Torus d → ℝ, IsCk2 J R → (∀ x y, R x y = R y x) →
        ∀ x y, pairInverse (mfData d s hs0 hsd V β hβ) ρ R x y =
          pairInverse (mfData d s hs0 hsd V β hβ) ρ R y x) ∧
      (∀ Δ R' : Torus d → Torus d → ℝ, IsCk2 (J + 2) Δ → IsCk2 J R' →
        DoublyCentered (withDensityReal ρ) Δ → DoublyCentered (withDensityReal ρ) R' →
        (∀ x y, centeredGen (mfData d s hs0 hsd V β hβ) ρ (fun x' => Δ x' y) x +
          centeredGen (mfData d s hs0 hsd V β hβ) ρ (fun y' => Δ x y') y = R' x y) →
        pairInverse (mfData d s hs0 hsd V β hβ) ρ R' = fun x y => -Δ x y) := by
  have hd1 : 1 ≤ d := by omega
  have hOV := px7_oneVar hd1 s hs0 hsd β hβ V hV ρ hρβ hρC hpos
  obtain ⟨Cinv, hC, hinv⟩ := px7_inv_C2 hOV
  have hJm : ∀ R : Torus d → Torus d → ℝ, IsCk2 J R → IsCk2 (px7_m d + px7_m d) R :=
    fun R hR => hR.of_le (by exact_mod_cast (by omega : px7_m d + px7_m d ≤ J))
  refine ⟨Cinv, hC, fun R hR hcen => ?_,
    fun R R' a b hR hR' => px7_inv_lin hOV (hJm R hR) (hJm R' hR') a b,
    fun R hR hs x y => px7_inv_symm hOV (hJm R hR) hs x y,
    fun Δ R' hΔ hR' hΔc hR'c heq => ?_⟩
  · obtain ⟨h1, h2, -⟩ := hinv R (hJm R hR)
    refine ⟨h1, px7_inv_cen hOV (hJm R hR), ?_, fun x y => px7_inv_pde hd2 s hs0 hsd β hβ V hV hρβ hρC hpos hOV
      (hR.of_le (by exact_mod_cast (by omega : px7_m d + px7_m d + 2 ≤ J))) hcen x y⟩
    exact h2.trans (mul_le_mul_of_nonneg_left (px7_cbNorm2_mono (by omega) R) hC)
  · exact px7_left_inverse hd2 s hs0 hsd β hβ V hV hρβ hρC hpos hOV
      (hΔ.of_le (by exact_mod_cast (by omega : px7_m d + px7_m d + 2 ≤ J + 2))) (hJm R' hR') hΔc heq

end HRS.PDE.PX7

end
