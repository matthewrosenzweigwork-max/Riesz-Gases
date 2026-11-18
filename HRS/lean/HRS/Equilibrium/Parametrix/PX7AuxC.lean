import HRS.Equilibrium.Parametrix.PX7AuxA
import HRS.Equilibrium.Parametrix.PX7AuxB

/-!
# Packet PX7, file C: the one-variable operator acting on coefficient arrays, and the key identity

`colOp F` applies a one-variable operator `F` to every column `k ↦ u k l` of an array, `rowOp F` to every
row.  The pair semigroup is `rowOp T ∘ colOp T` (`px7_key`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.PX7

open HRS.PDE.MFAdjoint

variable {d : ℕ}

/-! ### Columns and rows -/

/-- Column `l` of an array. -/
def col (u : Arr d) (l : Lattice d) : Coeff d := fun k => u k l

/-- Apply `F` to every column. -/
def colOp (F : Coeff d → Coeff d) (u : Arr d) : Arr d := fun k l => F (col u l) k

/-- Apply `F` to every row. -/
def rowOp (F : Coeff d → Coeff d) (u : Arr d) : Arr d := fun k l => F (fun l' => u k l') l

theorem px7_rowOp_eq (F : Coeff d → Coeff d) (u : Arr d) : rowOp F u = tr (colOp F (tr u)) := rfl

theorem px7_colOp_eq (F : Coeff d → Coeff d) (u : Arr d) : colOp F u = tr (rowOp F (tr u)) := rfl

theorem px7_tr_tr (u : Arr d) : tr (tr u) = u := rfl

theorem px7_summable_swap {f : Lattice d × Lattice d → ℝ} :
    Summable (fun q : Lattice d × Lattice d => f (q.2, q.1)) ↔ Summable f :=
  (Equiv.prodComm (Lattice d) (Lattice d)).summable_iff (f := f)

theorem px7_tsum_swap (f : Lattice d × Lattice d → ℝ) :
    ∑' q : Lattice d × Lattice d, f (q.2, q.1) = ∑' p, f p :=
  (Equiv.prodComm (Lattice d) (Lattice d)).tsum_eq f

theorem px7_mem2_col {a b : ℝ} {u : Arr d} (hu : Mem2 a b u) (l : Lattice d) : MemHs a (col u l) := by
  have h : Summable fun q : Lattice d × Lattice d =>
      sobWeight a q.2 * sobWeight b q.1 * ‖u q.2 q.1‖ ^ 2 :=
    px7_summable_swap (f := fun p : Lattice d × Lattice d =>
      sobWeight a p.1 * sobWeight b p.2 * ‖u p.1 p.2‖ ^ 2) |>.2 hu
  have h2 := h.prod_factor l
  have h3 := h2.mul_left (sobWeight b l)⁻¹
  have := sobWeight_pos b l
  refine h3.congr fun k => ?_
  simp only [col]
  field_simp

theorem px7_mem2_iff_col {a b : ℝ} {u : Arr d} :
    Mem2 a b u ↔ (∀ l, MemHs a (col u l)) ∧
      Summable fun l => sobWeight b l * hsNormSq a (col u l) := by
  constructor
  · intro hu
    refine ⟨px7_mem2_col hu, ?_⟩
    have h : Summable fun q : Lattice d × Lattice d =>
        sobWeight a q.2 * sobWeight b q.1 * ‖u q.2 q.1‖ ^ 2 :=
      px7_summable_swap (f := fun p : Lattice d × Lattice d =>
        sobWeight a p.1 * sobWeight b p.2 * ‖u p.1 p.2‖ ^ 2) |>.2 hu
    refine h.prod.congr fun l => ?_
    unfold hsNormSq col
    rw [← tsum_mul_left]
    exact tsum_congr fun k => by ring
  · rintro ⟨h1, h2⟩
    have hnn : ∀ q : Lattice d × Lattice d, 0 ≤ sobWeight a q.2 * sobWeight b q.1 * ‖u q.2 q.1‖ ^ 2 :=
      fun q => mul_nonneg (mul_nonneg (sobWeight_pos a _).le (sobWeight_pos b _).le) (sq_nonneg _)
    have hs : Summable fun q : Lattice d × Lattice d =>
        sobWeight a q.2 * sobWeight b q.1 * ‖u q.2 q.1‖ ^ 2 := by
      refine (summable_prod_of_nonneg (fun q => hnn q)).2 ⟨fun l => ?_, ?_⟩
      · have := (h1 l).mul_left (sobWeight b l)
        refine this.congr fun k => ?_
        simp only [col]; ring
      · refine h2.congr fun l => ?_
        unfold hsNormSq col
        rw [← tsum_mul_left]
        exact tsum_congr fun k => by ring
    exact (px7_summable_swap (f := fun p : Lattice d × Lattice d =>
      sobWeight a p.1 * sobWeight b p.2 * ‖u p.1 p.2‖ ^ 2)).1 hs

theorem px7_tsum_col {a b : ℝ} {u : Arr d} (hu : Mem2 a b u) :
    ∑' p : Lattice d × Lattice d, sobWeight a p.1 * sobWeight b p.2 * ‖u p.1 p.2‖ ^ 2 =
      ∑' l, sobWeight b l * hsNormSq a (col u l) := by
  have h : Summable fun q : Lattice d × Lattice d =>
      sobWeight a q.2 * sobWeight b q.1 * ‖u q.2 q.1‖ ^ 2 :=
    px7_summable_swap (f := fun p : Lattice d × Lattice d =>
      sobWeight a p.1 * sobWeight b p.2 * ‖u p.1 p.2‖ ^ 2) |>.2 hu
  rw [← px7_tsum_swap (fun p : Lattice d × Lattice d =>
      sobWeight a p.1 * sobWeight b p.2 * ‖u p.1 p.2‖ ^ 2)]
  rw [h.tsum_prod]
  refine tsum_congr fun l => ?_
  unfold hsNormSq col
  rw [← tsum_mul_left]
  exact tsum_congr fun k => by ring


/-! ### Operators on `H^m` and their column action -/

/-- `F` is a bounded complex-linear operator `H^a → H^b`. -/
structure OpOK2 (a b : ℝ) (F : Coeff d → Coeff d) (M : ℝ) : Prop where
  mem : ∀ x, MemHs a x → MemHs b (F x)
  bound : ∀ x, MemHs a x → hsNorm b (F x) ≤ M * hsNorm a x
  add : ∀ x y, MemHs a x → MemHs a y → F (x + y) = F x + F y
  smul : ∀ (c : ℂ) x, MemHs a x → F (c • x) = c • F x

/-- A bounded complex-linear operator on `H^m`. -/
abbrev OpOK (m : ℝ) (F : Coeff d → Coeff d) (M : ℝ) : Prop := OpOK2 m m F M

theorem OpOK2.nonneg {a b : ℝ} {F : Coeff d → Coeff d} {M : ℝ} (h : OpOK2 a b F M) : 0 ≤ M := by
  have h0 := h.bound (deltaCoeff 0) (deltaCoeff_memHs _ _)
  have h1 : 0 ≤ hsNorm b (F (deltaCoeff 0)) := hsNorm_nonneg' _ _
  have h2 : 0 < hsNorm a (deltaCoeff (0 : Lattice d)) := by
    rw [hsNorm_deltaCoeff]; positivity
  by_contra hneg; push_neg at hneg; nlinarith

theorem OpOK2.zero {a b : ℝ} {F : Coeff d → Coeff d} {M : ℝ} (h : OpOK2 a b F M) : F 0 = 0 := by
  have := h.smul 0 0 (by unfold MemHs; simp)
  simpa using this

theorem px7_colOp_mem {a b β : ℝ} {F : Coeff d → Coeff d} {M : ℝ} (hF : OpOK2 a b F M) {u : Arr d}
    (hu : Mem2 a β u) : Mem2 b β (colOp F u) ∧ nrm2 b β (colOp F u) ≤ M * nrm2 a β u := by
  have hM := hF.nonneg
  obtain ⟨h1, h2⟩ := px7_mem2_iff_col.1 hu
  have hcol : ∀ l, col (colOp F u) l = F (col u l) := fun l => rfl
  have hle : ∀ l, hsNormSq b (F (col u l)) ≤ M ^ 2 * hsNormSq a (col u l) := by
    intro l
    have := hF.bound _ (h1 l)
    unfold hsNorm at this
    have h3 : Real.sqrt (hsNormSq b (F (col u l))) ≤ Real.sqrt (M ^ 2 * hsNormSq a (col u l)) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hM]; exact this
    exact (Real.sqrt_le_sqrt_iff (mul_nonneg (sq_nonneg _) (hsNormSq_nonneg _ _))).1 h3
  have hs : Summable fun l => sobWeight β l * hsNormSq b (col (colOp F u) l) := by
    refine Summable.of_nonneg_of_le (fun l => mul_nonneg (sobWeight_pos β l).le (hsNormSq_nonneg _ _))
      (fun l => ?_) (h2.mul_left (M ^ 2))
    rw [hcol]
    calc sobWeight β l * hsNormSq b (F (col u l)) ≤ sobWeight β l * (M ^ 2 * hsNormSq a (col u l)) :=
          mul_le_mul_of_nonneg_left (hle l) (sobWeight_pos β l).le
      _ = _ := by ring
  have hmem : Mem2 b β (colOp F u) :=
    px7_mem2_iff_col.2 ⟨fun l => by rw [hcol]; exact hF.mem _ (h1 l), hs⟩
  refine ⟨hmem, ?_⟩
  unfold nrm2
  rw [px7_tsum_col hmem, px7_tsum_col hu]
  have : ∑' l, sobWeight β l * hsNormSq b (col (colOp F u) l) ≤
      ∑' l, M ^ 2 * (sobWeight β l * hsNormSq a (col u l)) := by
    refine Summable.tsum_le_tsum (fun l => ?_) hs (h2.mul_left _)
    rw [hcol]
    calc sobWeight β l * hsNormSq b (F (col u l)) ≤ sobWeight β l * (M ^ 2 * hsNormSq a (col u l)) :=
          mul_le_mul_of_nonneg_left (hle l) (sobWeight_pos β l).le
      _ = _ := by ring
  rw [tsum_mul_left] at this
  calc Real.sqrt _ ≤ Real.sqrt (M ^ 2 * ∑' l, sobWeight β l * hsNormSq a (col u l)) := Real.sqrt_le_sqrt this
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hM]

theorem px7_rowOp_mem {a b β : ℝ} {F : Coeff d → Coeff d} {M : ℝ} (hF : OpOK2 a b F M) {u : Arr d}
    (hu : Mem2 β a u) : Mem2 β b (rowOp F u) ∧ nrm2 β b (rowOp F u) ≤ M * nrm2 β a u := by
  obtain ⟨h1, h2⟩ := Mem2.transp hu
  obtain ⟨h3, h4⟩ := px7_colOp_mem hF h1
  obtain ⟨h5, h6⟩ := Mem2.transp h3
  refine ⟨h5, ?_⟩
  rw [px7_rowOp_eq]
  rw [h6]
  rw [h2] at h4
  exact h4

theorem px7_colOp_add {a b β : ℝ} {F : Coeff d → Coeff d} {M : ℝ} (hF : OpOK2 a b F M) {u v : Arr d}
    (hu : Mem2 a β u) (hv : Mem2 a β v) : colOp F (u + v) = colOp F u + colOp F v := by
  funext k l
  have e : col (u + v) l = col u l + col v l := rfl
  show F (col (u + v) l) k = F (col u l) k + F (col v l) k
  rw [e, hF.add _ _ (px7_mem2_col hu l) (px7_mem2_col hv l)]
  rfl

theorem px7_colOp_smul {a b β : ℝ} {F : Coeff d → Coeff d} {M : ℝ} (hF : OpOK2 a b F M) {u : Arr d}
    (hu : Mem2 a β u) (c : ℂ) : colOp F (c • u) = c • colOp F u := by
  funext k l
  have e : col (c • u) l = c • col u l := rfl
  show F (col (c • u) l) k = c * F (col u l) k
  rw [e, hF.smul c _ (px7_mem2_col hu l)]
  rfl

theorem px7_rowOp_add {a b β : ℝ} {F : Coeff d → Coeff d} {M : ℝ} (hF : OpOK2 a b F M) {u v : Arr d}
    (hu : Mem2 β a u) (hv : Mem2 β a v) : rowOp F (u + v) = rowOp F u + rowOp F v := by
  have := px7_colOp_add hF (Mem2.transp hu).1 (Mem2.transp hv).1
  rw [px7_rowOp_eq, px7_rowOp_eq, px7_rowOp_eq]
  have e : tr (u + v) = tr u + tr v := rfl
  rw [e, this]; rfl

theorem px7_rowOp_smul {a b β : ℝ} {F : Coeff d → Coeff d} {M : ℝ} (hF : OpOK2 a b F M) {u : Arr d}
    (hu : Mem2 β a u) (c : ℂ) : rowOp F (c • u) = c • rowOp F u := by
  have := px7_colOp_smul hF (Mem2.transp hu).1 c
  rw [px7_rowOp_eq, px7_rowOp_eq]
  have e : tr (c • u) = c • tr u := rfl
  rw [e, this]; rfl

theorem px7_colOp_sub {a b β : ℝ} {F : Coeff d → Coeff d} {M : ℝ} (hF : OpOK2 a b F M) {u v : Arr d}
    (hu : Mem2 a β u) (hv : Mem2 a β v) : colOp F (u - v) = colOp F u - colOp F v := by
  have hv' := (hv.smul (-1)).1
  have e : u - v = u + (-1 : ℂ) • v := by funext k l; simp [sub_eq_add_neg]
  rw [e, px7_colOp_add hF hu hv', px7_colOp_smul hF hv]
  funext k l; simp [sub_eq_add_neg]

theorem px7_rowOp_sub {a b β : ℝ} {F : Coeff d → Coeff d} {M : ℝ} (hF : OpOK2 a b F M) {u v : Arr d}
    (hu : Mem2 β a u) (hv : Mem2 β a v) : rowOp F (u - v) = rowOp F u - rowOp F v := by
  have hv' := (hv.smul (-1)).1
  have e : u - v = u + (-1 : ℂ) • v := by funext k l; simp [sub_eq_add_neg]
  rw [e, px7_rowOp_add hF hu hv', px7_rowOp_smul hF hv]
  funext k l; simp [sub_eq_add_neg]

theorem px7_entry_le {a b : ℝ} {v : Arr d} (hv : Mem2 a b v) (k l : Lattice d) :
    Real.sqrt (sobWeight a k * sobWeight b l) * ‖v k l‖ ≤ nrm2 a b v := by
  have h1 : sobWeight a k * sobWeight b l * ‖v k l‖ ^ 2 ≤
      ∑' p : Lattice d × Lattice d, sobWeight a p.1 * sobWeight b p.2 * ‖v p.1 p.2‖ ^ 2 :=
    hv.le_tsum (k, l) (fun p _ => mul_nonneg (px7_w_nonneg a b p) (sq_nonneg _))
  unfold nrm2
  calc Real.sqrt (sobWeight a k * sobWeight b l) * ‖v k l‖
      = Real.sqrt (sobWeight a k * sobWeight b l * ‖v k l‖ ^ 2) := by
        rw [Real.sqrt_mul (mul_nonneg (sobWeight_pos a _).le (sobWeight_pos b _).le),
          Real.sqrt_sq (norm_nonneg _)]
    _ ≤ _ := Real.sqrt_le_sqrt h1

/-- Single-entry array. -/
def eArr (a b : Lattice d) : Arr d := fun k l => if k = a ∧ l = b then 1 else 0

/-- Finite truncation of an array. -/
def uTr (S : Finset (Lattice d × Lattice d)) (u : Arr d) : Arr d := fun k l => if (k, l) ∈ S then u k l else 0

theorem px7_mem2_of_finite {a b : ℝ} (S : Finset (Lattice d × Lattice d)) (u : Arr d)
    (hu : ∀ k l, (k, l) ∉ S → u k l = 0) : Mem2 a b u := by
  refine summable_of_ne_finset_zero (s := S) fun p hp => ?_
  rw [hu p.1 p.2 (by simpa using hp)]; simp

theorem px7_uTr_eq (S : Finset (Lattice d × Lattice d)) (u : Arr d) :
    uTr S u = ∑ s ∈ S, u s.1 s.2 • eArr s.1 s.2 := by
  funext k l
  simp only [uTr, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, eArr]
  by_cases h : (k, l) ∈ S
  · rw [if_pos h, Finset.sum_eq_single (k, l)]
    · simp
    · intro b _ hb
      have : ¬ (k = b.1 ∧ l = b.2) := fun ⟨h1, h2⟩ => hb (by ext <;> simp [h1, h2])
      simp [this]
    · intro hn; exact absurd h hn
  · rw [if_neg h]
    symm
    refine Finset.sum_eq_zero fun s hs => ?_
    have : ¬ (k = s.1 ∧ l = s.2) := fun ⟨h1, h2⟩ => h (by
      have : s = (k, l) := by ext <;> simp [h1, h2]
      rw [← this]; exact hs)
    simp [this]


theorem px7_colOp_eArr {m : ℝ} {F : Coeff d → Coeff d} {M : ℝ} (hF : OpOK m F M) (a b : Lattice d) :
    colOp F (eArr a b) = fun k l => if l = b then F (deltaCoeff a) k else 0 := by
  funext k l
  have : col (eArr a b) l = if l = b then deltaCoeff a else 0 := by
    funext k'
    by_cases hl : l = b <;> by_cases hk : k' = a <;> simp [col, eArr, deltaCoeff, hl, hk]
  show F (col (eArr a b) l) k = _
  rw [this]
  by_cases hl : l = b
  · simp [hl]
  · simp [hl, hF.zero]

theorem px7_rowOp_eArr {m : ℝ} {G : Coeff d → Coeff d} {M : ℝ} (hG : OpOK m G M) (a b : Lattice d) :
    rowOp G (eArr a b) = fun k l => if k = a then G (deltaCoeff b) l else 0 := by
  funext k l
  have : (fun l' => eArr a b k l') = if k = a then deltaCoeff b else 0 := by
    funext l'
    by_cases hl : l' = b <;> by_cases hk : k = a <;> simp [eArr, deltaCoeff, hl, hk]
  show G (fun l' => eArr a b k l') l = _
  rw [this]
  by_cases hk : k = a
  · simp [hk]
  · simp [hk, hG.zero]

theorem px7_comm_single {m : ℝ} {F G : Coeff d → Coeff d} {MF MG : ℝ} (hF : OpOK m F MF)
    (hG : OpOK m G MG) (a b : Lattice d) :
    colOp F (rowOp G (eArr a b)) = rowOp G (colOp F (eArr a b)) := by
  funext k l
  rw [px7_rowOp_eArr hG, px7_colOp_eArr hF]
  have hδa : MemHs m (deltaCoeff a) := deltaCoeff_memHs _ _
  have hδb : MemHs m (deltaCoeff b) := deltaCoeff_memHs _ _
  -- left side
  have L : colOp F (fun k' l' => if k' = a then G (deltaCoeff b) l' else 0) k l =
      F (deltaCoeff a) k * G (deltaCoeff b) l := by
    have : col (fun k' l' => if k' = a then G (deltaCoeff b) l' else 0) l =
        (G (deltaCoeff b) l) • deltaCoeff a := by
      funext k'
      by_cases hk : k' = a <;> simp [col, deltaCoeff, hk]
    show F (col _ l) k = _
    rw [this, hF.smul _ _ hδa]
    simp [mul_comm]
  have R : rowOp G (fun k' l' => if l' = b then F (deltaCoeff a) k' else 0) k l =
      F (deltaCoeff a) k * G (deltaCoeff b) l := by
    have : (fun l' => (fun k' l'' => if l'' = b then F (deltaCoeff a) k' else 0) k l') =
        (F (deltaCoeff a) k) • deltaCoeff b := by
      funext l'
      by_cases hl : l' = b <;> simp [deltaCoeff, hl]
    show G (fun l' => _) l = _
    rw [this, hG.smul _ _ hδb]
    simp
  rw [L, R]


section Comm

variable {m : ℝ} {F G : Coeff d → Coeff d} {MF MG : ℝ}

theorem px7_comm_add (hF : OpOK m F MF) (hG : OpOK m G MG) {u v : Arr d} (hu : Mem2 m m u)
    (hv : Mem2 m m v) (cu : colOp F (rowOp G u) = rowOp G (colOp F u))
    (cv : colOp F (rowOp G v) = rowOp G (colOp F v)) :
    colOp F (rowOp G (u + v)) = rowOp G (colOp F (u + v)) := by
  have r1 := (px7_rowOp_mem hG hu).1
  have r2 := (px7_rowOp_mem hG hv).1
  have c1 := (px7_colOp_mem hF hu).1
  have c2 := (px7_colOp_mem hF hv).1
  rw [px7_rowOp_add hG hu hv, px7_colOp_add hF r1 r2, px7_colOp_add hF hu hv,
    px7_rowOp_add hG c1 c2, cu, cv]

theorem px7_comm_smul (hF : OpOK m F MF) (hG : OpOK m G MG) {u : Arr d} (hu : Mem2 m m u) (c : ℂ)
    (cu : colOp F (rowOp G u) = rowOp G (colOp F u)) :
    colOp F (rowOp G (c • u)) = rowOp G (colOp F (c • u)) := by
  rw [px7_rowOp_smul hG hu, px7_colOp_smul hF (px7_rowOp_mem hG hu).1, px7_colOp_smul hF hu,
    px7_rowOp_smul hG (px7_colOp_mem hF hu).1, cu]

theorem px7_comm_fin (hF : OpOK m F MF) (hG : OpOK m G MG) (S : Finset (Lattice d × Lattice d))
    (c : Lattice d × Lattice d → ℂ) :
    Mem2 m m (∑ s ∈ S, c s • eArr s.1 s.2) ∧
    colOp F (rowOp G (∑ s ∈ S, c s • eArr s.1 s.2)) = rowOp G (colOp F (∑ s ∈ S, c s • eArr s.1 s.2)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h0 : Mem2 m m (0 : Arr d) := px7_mem2_of_finite ∅ 0 (fun _ _ _ => rfl)
    refine ⟨by simpa using h0, ?_⟩
    simp only [Finset.sum_empty]
    funext k l
    show F (col (rowOp G 0) l) k = G (fun l' => colOp F 0 k l') l
    have e1 : col (rowOp G (0 : Arr d)) l = 0 := by
      funext k'; show G (fun l' => (0 : Arr d) k' l') l = 0
      have : (fun l' => (0 : Arr d) k' l') = 0 := rfl
      rw [this, hG.zero]; rfl
    have e2 : (fun l' => colOp F (0 : Arr d) k l') = 0 := by
      funext l'; show F (col 0 l') k = 0
      have : col (0 : Arr d) l' = 0 := rfl
      rw [this, hF.zero]; rfl
    rw [e1, e2, hF.zero, hG.zero]; rfl
  | insert a S ha ih =>
    obtain ⟨hm, hc⟩ := ih
    rw [Finset.sum_insert ha]
    have he : Mem2 m m (eArr a.1 a.2) := px7_mem2_of_finite {a} _ (fun k l h => by
      simp only [eArr]
      have : ¬ (k = a.1 ∧ l = a.2) := fun ⟨h1, h2⟩ => h (by simp [h1, h2])
      simp [this])
    have h1 := (he.smul (c a)).1
    refine ⟨(h1.add hm).1, px7_comm_add hF hG h1 hm ?_ hc⟩
    exact px7_comm_smul hF hG he (c a) (px7_comm_single hF hG a.1 a.2)


theorem px7_nrm2_uTr_tendsto {a b : ℝ} {u : Arr d} (hu : Mem2 a b u) :
    Tendsto (fun S : Finset (Lattice d × Lattice d) => nrm2 a b (u - uTr S u)) atTop (𝓝 0) := by
  set f : Lattice d × Lattice d → ℝ := fun p => sobWeight a p.1 * sobWeight b p.2 * ‖u p.1 p.2‖ ^ 2 with hf
  have h1 := tendsto_tsum_compl_atTop_zero f
  have e : ∀ S : Finset (Lattice d × Lattice d), nrm2 a b (u - uTr S u) =
      Real.sqrt (∑' b : {x // x ∉ S}, f b) := by
    intro S
    unfold nrm2
    congr 1
    have : ∀ p : Lattice d × Lattice d, sobWeight a p.1 * sobWeight b p.2 * ‖(u - uTr S u) p.1 p.2‖ ^ 2 =
        Set.indicator {x | x ∉ S} f p := by
      intro p
      by_cases hp : p ∈ S
      · simp [uTr, hp, hf]
      · simp [uTr, hp, hf, Set.indicator]
    simp_rw [this]
    exact (tsum_subtype {x | x ∉ S} f).symm
  simp_rw [e]
  have := (Real.continuous_sqrt.tendsto 0).comp h1
  rw [Real.sqrt_zero] at this
  exact this

theorem px7_arr_comm (hF : OpOK m F MF) (hG : OpOK m G MG) {u : Arr d} (hu : Mem2 m m u) :
    colOp F (rowOp G u) = rowOp G (colOp F u) := by
  funext k l
  have hMF := hF.nonneg
  have hMG := hG.nonneg
  set K : ℝ := (Real.sqrt (sobWeight m k * sobWeight m l))⁻¹ with hK
  have hKpos : 0 < Real.sqrt (sobWeight m k * sobWeight m l) :=
    Real.sqrt_pos.2 (mul_pos (sobWeight_pos _ _) (sobWeight_pos _ _))
  have hK0 : 0 ≤ K := by positivity
  -- entry bounds
  have ent : ∀ v : Arr d, Mem2 m m v → ∀ w : Arr d, nrm2 m m w ≤ MF * MG * nrm2 m m v → Mem2 m m w →
      ‖w k l‖ ≤ K * (MF * MG * nrm2 m m v) := by
    intro v hv w hw hwm
    have := px7_entry_le hwm k l
    rw [hK]
    rw [inv_mul_eq_div, le_div_iff₀ hKpos, mul_comm]
    nlinarith [this, hw]
  have hbd : ∀ S : Finset (Lattice d × Lattice d),
      ‖colOp F (rowOp G u) k l - rowOp G (colOp F u) k l‖ ≤ 2 * (K * (MF * MG * nrm2 m m (u - uTr S u))) := by
    intro S
    have huS : Mem2 m m (uTr S u) := px7_mem2_of_finite S _ (fun k l h => by simp [uTr, h])
    have hd := (hu.sub huS).1
    have hcomm := (px7_comm_fin hF hG S (fun s => u s.1 s.2)).2
    rw [← px7_uTr_eq] at hcomm
    have eΦ : colOp F (rowOp G (u - uTr S u)) = colOp F (rowOp G u) - colOp F (rowOp G (uTr S u)) := by
      rw [px7_rowOp_sub hG hu huS, px7_colOp_sub hF (px7_rowOp_mem hG hu).1 (px7_rowOp_mem hG huS).1]
    have eΨ : rowOp G (colOp F (u - uTr S u)) = rowOp G (colOp F u) - rowOp G (colOp F (uTr S u)) := by
      rw [px7_colOp_sub hF hu huS, px7_rowOp_sub hG (px7_colOp_mem hF hu).1 (px7_colOp_mem hF huS).1]
    have bΦ : nrm2 m m (colOp F (rowOp G (u - uTr S u))) ≤ MF * MG * nrm2 m m (u - uTr S u) := by
      refine (px7_colOp_mem hF (px7_rowOp_mem hG hd).1).2.trans ?_
      calc MF * nrm2 m m (rowOp G (u - uTr S u)) ≤ MF * (MG * nrm2 m m (u - uTr S u)) :=
            mul_le_mul_of_nonneg_left (px7_rowOp_mem hG hd).2 hMF
        _ = _ := by ring
    have bΨ : nrm2 m m (rowOp G (colOp F (u - uTr S u))) ≤ MF * MG * nrm2 m m (u - uTr S u) := by
      refine (px7_rowOp_mem hG (px7_colOp_mem hF hd).1).2.trans ?_
      calc MG * nrm2 m m (colOp F (u - uTr S u)) ≤ MG * (MF * nrm2 m m (u - uTr S u)) :=
            mul_le_mul_of_nonneg_left (px7_colOp_mem hF hd).2 hMG
        _ = _ := by ring
    have a1 := ent _ hd _ bΦ (px7_colOp_mem hF (px7_rowOp_mem hG hd).1).1
    have a2 := ent _ hd _ bΨ (px7_rowOp_mem hG (px7_colOp_mem hF hd).1).1
    rw [eΦ] at a1
    rw [eΨ] at a2
    have e3 : colOp F (rowOp G u) k l - rowOp G (colOp F u) k l =
        (colOp F (rowOp G u) k l - colOp F (rowOp G (uTr S u)) k l) -
        (rowOp G (colOp F u) k l - rowOp G (colOp F (uTr S u)) k l) := by
      rw [hcomm]; ring
    rw [e3]
    refine (norm_sub_le _ _).trans ?_
    have a1' : ‖colOp F (rowOp G u) k l - colOp F (rowOp G (uTr S u)) k l‖ ≤ K * (MF * MG * nrm2 m m (u - uTr S u)) := a1
    have a2' : ‖rowOp G (colOp F u) k l - rowOp G (colOp F (uTr S u)) k l‖ ≤ K * (MF * MG * nrm2 m m (u - uTr S u)) := a2
    linarith
  have hlim : Tendsto (fun S : Finset (Lattice d × Lattice d) => 2 * (K * (MF * MG * nrm2 m m (u - uTr S u))))
      atTop (𝓝 0) := by
    simpa using (((px7_nrm2_uTr_tendsto hu).const_mul (MF * MG)).const_mul K).const_mul 2
  have : ‖colOp F (rowOp G u) k l - rowOp G (colOp F u) k l‖ ≤ 0 :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall hbd)
  have h0 : colOp F (rowOp G u) k l - rowOp G (colOp F u) k l = 0 := norm_le_zero_iff.1 this
  exact sub_eq_zero.1 h0

end Comm


/-! ### Norm-convergent sums in `H^m` -/

section Pass

variable {ι : Type*} {m : ℝ}

theorem px7_fin_sum_Hs (hm : 0 ≤ m) (v : ι → Coeff d) (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1)
    (hv : ∀ i, MemHs m (v i)) (I : Finset ι) :
    MemHs m (fun k => ∑ i ∈ I, z i * v i k) ∧
      hsNorm m (fun k => ∑ i ∈ I, z i * v i k) ≤ ∑ i ∈ I, hsNorm m (v i) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨by unfold MemHs; simp, ?_⟩
    have : hsNorm m (fun _ : Lattice d => (0 : ℂ)) = 0 := by unfold hsNorm hsNormSq; simp
    rw [this]
  | insert a I ha ih =>
    obtain ⟨h1, h2⟩ := ih
    have e : (fun k => ∑ i ∈ insert a I, z i * v i k) =
        fun k => (z a * v a k) + ∑ i ∈ I, z i * v i k := by
      funext k; rw [Finset.sum_insert ha]
    rw [e]
    have hza : MemHs m (fun k => z a * v a k) := MFThermalReg.memHs_smul (hv a) _
    obtain ⟨h3, h4⟩ := hs_add_le m hza h1
    refine ⟨h3, h4.trans ?_⟩
    rw [Finset.sum_insert ha, MFThermalReg.hsNorm_smul]
    have := mul_le_mul_of_nonneg_right (hz a) (hsNorm_nonneg' m (v a))
    linarith

theorem px7_sum_Hs (hm : 0 ≤ m) (v : ι → Coeff d) (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1)
    (hv : ∀ i, MemHs m (v i)) (hs : Summable fun i => hsNorm m (v i)) :
    (∀ k, HasSum (fun i => z i * v i k) (∑' i, z i * v i k)) ∧
      MemHs m (fun k => ∑' i, z i * v i k) ∧
      hsNorm m (fun k => ∑' i, z i * v i k) ≤ ∑' i, hsNorm m (v i) := by
  classical
  have hcoord : ∀ k, Summable fun i => z i * v i k := by
    intro k
    refine Summable.of_norm_bounded hs fun i => ?_
    rw [norm_mul]
    calc ‖z i‖ * ‖v i k‖ ≤ 1 * hsNorm m (v i) :=
          mul_le_mul (hz i) (norm_coeff_le_hsNorm_of_nonneg hm (hv i) k) (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hH : ∀ k, HasSum (fun i => z i * v i k) (∑' i, z i * v i k) := fun k => (hcoord k).hasSum
  refine ⟨hH, ?_⟩
  set c : Coeff d := fun k => ∑' i, z i * v i k with hc
  set B := ∑' i, hsNorm m (v i) with hB
  have hB0 : 0 ≤ B := tsum_nonneg fun i => hsNorm_nonneg' _ _
  have hKbound : ∀ K : Finset (Lattice d), ∑ k ∈ K, sobWeight m k * ‖c k‖ ^ 2 ≤ B ^ 2 := by
    intro K
    have hlim : Tendsto (fun I : Finset ι => ∑ k ∈ K, sobWeight m k *
        ‖∑ i ∈ I, z i * v i k‖ ^ 2) atTop (𝓝 (∑ k ∈ K, sobWeight m k * ‖c k‖ ^ 2)) := by
      refine tendsto_finset_sum _ fun k _ => ?_
      have hk : Tendsto (fun I : Finset ι => ∑ i ∈ I, z i * v i k) atTop (𝓝 (c k)) := by
        simpa [HasSum] using hH k
      exact (hk.norm.pow 2).const_mul _
    refine le_of_tendsto hlim (Filter.Eventually.of_forall fun I => ?_)
    obtain ⟨h1, h2⟩ := px7_fin_sum_Hs hm v z hz hv I
    have h3 := sum_le_hsNormSq h1 K
    have h4 : hsNormSq m (fun k => ∑ i ∈ I, z i * v i k) ≤ B ^ 2 := by
      have h5 : hsNorm m (fun k => ∑ i ∈ I, z i * v i k) ≤ B := by
        refine h2.trans ?_
        exact Summable.sum_le_tsum I (fun i _ => hsNorm_nonneg' _ _) hs
      have h6 := hsNorm_nonneg' m (fun k => ∑ i ∈ I, z i * v i k)
      have : hsNormSq m (fun k => ∑ i ∈ I, z i * v i k) =
          hsNorm m (fun k => ∑ i ∈ I, z i * v i k) ^ 2 := by
        unfold hsNorm; rw [Real.sq_sqrt (hsNormSq_nonneg _ _)]
      rw [this]
      exact pow_le_pow_left₀ h6 h5 2
    exact h3.trans h4
  obtain ⟨hmem, hnsq⟩ := memHs_of_sum_le hKbound
  refine ⟨hmem, ?_⟩
  unfold hsNorm
  calc Real.sqrt (hsNormSq m c) ≤ Real.sqrt (B ^ 2) := Real.sqrt_le_sqrt hnsq
    _ = B := Real.sqrt_sq hB0


theorem px7_F_fin {F : Coeff d → Coeff d} {M : ℝ} (hF : OpOK m F M) (hm : 0 ≤ m) (v : ι → Coeff d)
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) (hv : ∀ i, MemHs m (v i)) (I : Finset ι) :
    F (fun k => ∑ i ∈ I, z i * v i k) = fun k => ∑ i ∈ I, z i * F (v i) k := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have : (fun _ : Lattice d => (0 : ℂ)) = (0 : Coeff d) := rfl
    rw [this, hF.zero]
  | insert a I ha ih =>
    have e : (fun k => ∑ i ∈ insert a I, z i * v i k) =
        (z a • v a) + fun k => ∑ i ∈ I, z i * v i k := by
      funext k; simp [Finset.sum_insert ha]
    rw [e, hF.add _ _ (MFAdjoint.memHs_smul_coeff (hv a) (z a)) (px7_fin_sum_Hs hm v z hz hv I).1,
      hF.smul _ _ (hv a), ih]
    funext k; simp [Finset.sum_insert ha]

theorem px7_pass {F : Coeff d → Coeff d} {M : ℝ} (hF : OpOK m F M) (hm : 0 ≤ m) (v : ι → Coeff d)
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) (hv : ∀ i, MemHs m (v i))
    (hs : Summable fun i => hsNorm m (v i)) (k : Lattice d) :
    HasSum (fun i => z i * F (v i) k) (F (fun k' => ∑' i, z i * v i k') k) := by
  classical
  obtain ⟨hH, hcm, hcn⟩ := px7_sum_Hs hm v z hz hv hs
  set c : Coeff d := fun k' => ∑' i, z i * v i k' with hc
  have hM := hF.nonneg
  have hcoord : ∀ k', Summable fun i => z i * v i k' := fun k' => (hH k').summable
  -- tail estimates
  have htail : ∀ I : Finset ι, ‖F c k - ∑ i ∈ I, z i * F (v i) k‖ ≤
      M * ∑' i : {i // i ∉ I}, hsNorm m (v i) := by
    intro I
    have hs' : Summable fun i : {i // i ∉ I} => hsNorm m (v i) := hs.subtype _
    obtain ⟨hH', hm', hn'⟩ := px7_sum_Hs hm (fun i : {i // i ∉ I} => v i) (fun i => z i)
      (fun i => hz i) (fun i => hv i) hs'
    set tl : Coeff d := fun k' => ∑' i : {i // i ∉ I}, z i * v i k' with htl
    have hsplit : c = (fun k' => ∑ i ∈ I, z i * v i k') + tl := by
      funext k'
      exact ((hcoord k').sum_add_tsum_subtype_compl I).symm
    have hFc : F c = F (fun k' => ∑ i ∈ I, z i * v i k') + F tl := by
      rw [hsplit]; exact hF.add _ _ (px7_fin_sum_Hs hm v z hz hv I).1 hm'
    have : F c k - ∑ i ∈ I, z i * F (v i) k = F tl k := by
      rw [hFc, px7_F_fin hF hm v z hz hv I]; simp
    rw [this]
    calc ‖F tl k‖ ≤ hsNorm m (F tl) := norm_coeff_le_hsNorm_of_nonneg hm (hF.mem _ hm') k
      _ ≤ M * hsNorm m tl := hF.bound _ hm'
      _ ≤ M * ∑' i : {i // i ∉ I}, hsNorm m (v i) := mul_le_mul_of_nonneg_left hn' hM
  have hlim : Tendsto (fun I : Finset ι => M * ∑' i : {i // i ∉ I}, hsNorm m (v i)) atTop (𝓝 0) := by
    simpa using (tendsto_tsum_compl_atTop_zero (fun i => hsNorm m (v i))).const_mul M
  have : Tendsto (fun I : Finset ι => ∑ i ∈ I, z i * F (v i) k) atTop (𝓝 (F c k)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun I => norm_nonneg _) (fun I => ?_) hlim
    rw [norm_sub_rev]; exact htail I
  simpa [HasSum] using this

end Pass


/-! ### Reality -/

section Real

variable {m : ℝ} {F : Coeff d → Coeff d} {M : ℝ}

theorem px7_RS_tr {u : Arr d} (h : RS u) : RS (tr u) := by
  intro k l
  have := h l k
  simpa [tr] using this

theorem px7_col_neg {u : Arr d} (h : RS u) (l : Lattice d) : col u (-l) = reflConj (col u l) := by
  funext k'
  have := h (-k') l
  simp only [neg_neg] at this
  simp only [col, reflConj]
  rw [this]

theorem px7_colOp_RS (hF : OpOK m F M) (hrc : ∀ x, MemHs m x → F (reflConj x) = reflConj (F x))
    {b : ℝ} {u : Arr d} (hu : Mem2 m b u) (h : RS u) : RS (colOp F u) := by
  intro k l
  show F (col u (-l)) (-k) = conj (F (col u l) k)
  rw [px7_col_neg h, hrc _ (px7_mem2_col hu l)]
  simp [reflConj]

theorem px7_rowOp_RS (hF : OpOK m F M) (hrc : ∀ x, MemHs m x → F (reflConj x) = reflConj (F x))
    {a : ℝ} {u : Arr d} (hu : Mem2 a m u) (h : RS u) : RS (rowOp F u) := by
  have := px7_colOp_RS hF hrc (Mem2.transp hu).1 (px7_RS_tr h)
  have e := px7_rowOp_eq F u
  rw [e]
  exact px7_RS_tr this

end Real


/-! ### The operator `T` of the bundle -/

section OVsec

variable {D : DynData d} {ρ : Torus d → ℝ} {m : ℕ} {T : ℝ → Coeff d → Coeff d} {Ah : Coeff d → Coeff d}

theorem OV.opok (hOV : OV D ρ m T Ah) :
    ∃ M c : ℝ, 0 < M ∧ 0 < c ∧ ∀ τ : ℝ, 0 ≤ τ → OpOK (m : ℝ) (T τ) (M * Real.exp (-c * τ)) := by
  obtain ⟨M, c, hM, hc, h⟩ := hOV.dec0
  refine ⟨M, c, hM, hc, fun τ hτ => ⟨fun x hx => (h τ hτ x hx).1, fun x hx => ?_,
    fun x y hx hy => hOV.add τ hτ x y hx hy, fun a x hx => hOV.smul τ hτ x hx a⟩⟩
  have := (h τ hτ x hx).2
  linarith

theorem OV.refl (hOV : OV D ρ m T Ah) {τ : ℝ} (hτ : 0 ≤ τ) {x : Coeff d} (hx : MemHs (m : ℝ) x) :
    T τ (reflConj x) = reflConj (T τ x) := by
  obtain ⟨ha, -⟩ := px7_hs_reP hx
  obtain ⟨hb, -⟩ := px7_hs_imP hx
  set a := px7_reP x with hadef
  set b := px7_imP x with hbdef
  have har : ∀ k, a (-k) = conj (a k) := px7_reP_real x
  have hbr : ∀ k, b (-k) = conj (b k) := px7_imP_real x
  have hTa := hOV.real τ hτ a ha (px7_reP_real x)
  have hTb := hOV.real τ hτ b hb (px7_imP_real x)
  have hxs : x = a + Complex.I • b := by
    funext k; have := congrFun (px7_split x) k; simpa using this
  have hrx : reflConj x = a + (-Complex.I) • b := by
    funext k
    have e1 : x (-k) = a (-k) + Complex.I * b (-k) := by
      have := congrFun (px7_split x) (-k); simpa using this
    simp only [reflConj, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [e1]
    simp only [map_add, map_mul, Complex.conj_I, har, hbr, Complex.conj_conj]
  have hIb : MemHs (m : ℝ) (Complex.I • b) := MFAdjoint.memHs_smul_coeff hb _
  have hnIb : MemHs (m : ℝ) ((-Complex.I) • b) := MFAdjoint.memHs_smul_coeff hb _
  have l1 : T τ x = T τ a + Complex.I • T τ b := by
    conv_lhs => rw [hxs]
    rw [hOV.add τ hτ _ _ ha hIb, hOV.smul τ hτ _ hb]
  have l2 : T τ (reflConj x) = T τ a + (-Complex.I) • T τ b := by
    rw [hrx, hOV.add τ hτ _ _ ha hnIb, hOV.smul τ hτ _ hb]
  rw [l2, l1]
  funext k
  simp only [reflConj, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, Complex.conj_I]
  have ea : conj (T τ a (-k)) = T τ a k := by
    have := hTa (-k); rw [neg_neg] at this; rw [← this]
  have eb : conj (T τ b (-k)) = T τ b k := by
    have := hTb (-k); rw [neg_neg] at this; rw [← this]
  rw [ea, eb]

end OVsec


/-! ### Slices of `ev` -/

section Slice

variable {m : ℝ}

theorem px7_col_norm_summable {b : ℝ} (hb : (d : ℝ) < 2 * b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Arr d, Mem2 m b u →
      Summable (fun l => hsNorm m (col u l)) ∧ ∑' l, hsNorm m (col u l) ≤ C * nrm2 m b u := by
  set f : Lattice d → ℝ := fun l => Lattice.jp l ^ (-b) with hf
  have hf2 : Summable fun l : Lattice d => f l ^ 2 := by
    refine (MFPair.summable_jp_rpow_ps (d := d) (2 * (-b)) (by linarith)).congr fun k => ?_
    simp only [hf]; rw [Torus.jp_rpow_sq]
  refine ⟨Real.sqrt (∑' l, f l ^ 2), Real.sqrt_nonneg _, fun u hu => ?_⟩
  obtain ⟨h1, h2⟩ := px7_mem2_iff_col.1 hu
  set g : Lattice d → ℝ := fun l => Real.sqrt (sobWeight b l * hsNormSq m (col u l)) with hg
  have hg2 : ∀ l, g l ^ 2 = sobWeight b l * hsNormSq m (col u l) := fun l =>
    Real.sq_sqrt (mul_nonneg (sobWeight_pos b l).le (hsNormSq_nonneg _ _))
  have hgs : Summable fun l => g l ^ 2 := h2.congr fun l => (hg2 l).symm
  have f0 : ∀ l, 0 ≤ f l := fun l => Real.rpow_nonneg (Torus.jp_pos _).le _
  have g0 : ∀ l, 0 ≤ g l := fun l => Real.sqrt_nonneg _
  obtain ⟨hs, hle⟩ := Torus.cs_tsum f g f0 g0 hf2 hgs
  have hfg : ∀ l, f l * g l = hsNorm m (col u l) := by
    intro l
    simp only [hf, hg]
    rw [Real.sqrt_mul (sobWeight_pos b l).le, px7_sqrt_sobWeight]
    unfold hsNorm
    rw [← mul_assoc, ← Real.rpow_add (Torus.jp_pos _)]
    simp
  refine ⟨hs.congr fun l => hfg l, ?_⟩
  have e : ∑' l, hsNorm m (col u l) = ∑' l, f l * g l := tsum_congr fun l => (hfg l).symm
  rw [e]
  refine hle.trans (le_of_eq ?_)
  unfold nrm2
  rw [px7_tsum_col hu]
  congr 2
  exact tsum_congr hg2

theorem px7_acol_Hs (hm0 : 0 ≤ m) (hd : (d : ℝ) < 2 * m) {u : Arr d} (hu : Mem2 m m u) (y : Torus d) :
    MemHs m (acol u y) := by
  obtain ⟨C, hC, h⟩ := px7_col_norm_summable (m := m) (b := m) hd
  obtain ⟨hs, -⟩ := h u hu
  obtain ⟨-, hmem, -⟩ := px7_sum_Hs hm0 (fun l => col u l) (fun l => Torus.mode l y)
    (fun l => (Torus.norm_mode l y).le) (px7_mem2_col hu) hs
  have e : acol u y = fun k => ∑' l, Torus.mode l y * col u l k := by
    funext k; exact tsum_congr fun l => by simp [col, mul_comm]
  rw [e]; exact hmem

theorem px7_acol_real {u : Arr d} (h : RS u) (hsum : Summable fun p : Lattice d × Lattice d => ‖u p.1 p.2‖)
    (y : Torus d) : IsRealCoeff (acol u y) := by
  intro k
  unfold acol
  rw [Complex.conj_tsum]
  rw [← (Equiv.neg (Lattice d)).tsum_eq (fun l => conj (u k l * Torus.mode l y))]
  refine tsum_congr fun l => ?_
  simp only [Equiv.neg_apply, map_mul, Torus.mode_neg, Complex.conj_conj]
  have := h k (-l)
  simp only [neg_neg] at this
  rw [this]

theorem px7_slice_x (hm0 : 0 ≤ m) (hd : (d : ℝ) < 2 * m) {u : Arr d} (hu : Mem2 m m u) (h : RS u)
    (y : Torus d) :
    Continuous (fun x => ev u x y) ∧ MemSobolev m (fun x => ev u x y) ∧
      coeffOf (fun x => ev u x y) = acol u y := by
  obtain ⟨C, hC, hcs⟩ := px7_cs (d := d) m m 0 0 (by simpa using hd) (by simpa using hd)
  have hsum : Summable fun p : Lattice d × Lattice d => ‖u p.1 p.2‖ := by simpa using (hcs u hu).1
  have hmem := px7_acol_Hs hm0 hd hu y
  have hreal := px7_acol_real h hsum y
  have hdm : (d : ℝ) / 2 < m := by linarith
  have hsc := summable_norm_of_memHs m hdm _ hmem
  have e : (fun x => ev u x y) = toFun (acol u y) := funext fun x => px7_ev_eq_toFun hsum x y
  rw [e]
  exact ⟨MFPair.continuous_toFun' _ hsc, (ClassicalPart.memSobolev_toFun hsc hmem hreal).1,
    coeffOf_toFun _ hreal hsc⟩

end Slice


/-! ### The pair semigroup as a tensor operator -/

section Key

variable {D : DynData d} {ρ : Torus d → ℝ} {m : ℕ} {T : ℝ → Coeff d → Coeff d} {Ah : Coeff d → Coeff d}

theorem px7_summable_of_mem2 {m : ℝ} (hd : (d : ℝ) < 2 * m) {u : Arr d} (hu : Mem2 m m u) :
    Summable fun p : Lattice d × Lattice d => ‖u p.1 p.2‖ := by
  obtain ⟨C, hC, hcs⟩ := px7_cs (d := d) m m 0 0 (by simpa using hd) (by simpa using hd)
  simpa using (hcs u hu).1

theorem OV.hd (hOV : OV D ρ m T Ah) : (d : ℝ) < 2 * (m : ℝ) := by
  have := hOV.hm_gt
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith [hOV.hm_gt]

theorem OV.hm0 (hOV : OV D ρ m T Ah) : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m

/-- `T τ (acol u y) = acol (colOp (T τ) u) y`. -/
theorem px7_T_acol (hOV : OV D ρ m T Ah) {τ : ℝ} (hτ : 0 ≤ τ) {u : Arr d} (hu : Mem2 (m : ℝ) (m : ℝ) u)
    (y : Torus d) : T τ (acol u y) = acol (colOp (T τ) u) y := by
  obtain ⟨M, c, hM, hc, hop⟩ := hOV.opok
  have hF := hop τ hτ
  obtain ⟨C, hC, h⟩ := px7_col_norm_summable (m := (m : ℝ)) (b := (m : ℝ)) hOV.hd
  obtain ⟨hs, -⟩ := h u hu
  have e : acol u y = fun k => ∑' l, Torus.mode l y * col u l k := by
    funext k; exact tsum_congr fun l => by simp [col, mul_comm]
  rw [e]
  funext k
  have := px7_pass hF hOV.hm0 (fun l => col u l) (fun l => Torus.mode l y)
    (fun l => (Torus.norm_mode l y).le) (px7_mem2_col hu) hs k
  rw [← this.tsum_eq]
  refine tsum_congr fun l => ?_
  simp only [colOp]
  ring

/-- The pair semigroup in tensor form (x-variable first). -/
theorem px7_key (hOV : OV D ρ m T Ah) {τ : ℝ} (hτ : 0 ≤ τ) {u : Arr d}
    (hu : Mem2 (m : ℝ) (m : ℝ) u) (hRS : RS u) (x y : Torus d) :
    pairSemigroup D ρ τ (ev u) x y = ev (rowOp (T τ) (colOp (T τ) u)) x y := by
  obtain ⟨M, c, hM, hc, hop⟩ := hOV.opok
  have hF := hop τ hτ
  have hrc : ∀ z, MemHs (m : ℝ) z → T τ (reflConj z) = reflConj (T τ z) := fun z hz => hOV.refl hτ hz
  set v := colOp (T τ) u with hv
  have hvm : Mem2 (m : ℝ) (m : ℝ) v := (px7_colOp_mem hF hu).1
  have hvRS : RS v := px7_colOp_RS hF hrc hu hRS
  set w := rowOp (T τ) v with hw
  have hwm : Mem2 (m : ℝ) (m : ℝ) w := (px7_rowOp_mem hF hvm).1
  have hsv := px7_summable_of_mem2 hOV.hd hvm
  have hsw := px7_summable_of_mem2 hOV.hd hwm
  -- the inner function
  have inner : ∀ y' : Torus d, equilibriumSemigroup D ρ τ (fun x' => ev u x' y') x = ev v x y' := by
    intro y'
    obtain ⟨hc1, hS, hco⟩ := px7_slice_x hOV.hm0 hOV.hd hu hRS y'
    rw [hOV.hS _ hc1 hS τ hτ, hco, px7_T_acol hOV hτ hu y', ← px7_ev_eq_toFun hsv x y']
  have hpair : pairSemigroup D ρ τ (ev u) x y =
      equilibriumSemigroup D ρ τ (fun y' => ev v x y') y := by
    unfold pairSemigroup
    congr 1
    funext y'
    exact inner y'
  rw [hpair]
  -- the outer function
  have hvt : Mem2 (m : ℝ) (m : ℝ) (tr v) := (Mem2.transp hvm).1
  have hvtRS : RS (tr v) := px7_RS_tr hvRS
  obtain ⟨hc2, hS2, hco2⟩ := px7_slice_x hOV.hm0 hOV.hd hvt hvtRS x
  have egfun : (fun y' => ev v x y') = fun y' => ev (tr v) y' x := funext fun y' => (px7_ev_tr v y' x).symm
  rw [egfun, hOV.hS _ hc2 hS2 τ hτ, hco2]
  -- pass over rows
  have hrow : T τ (acol (tr v) x) = acol (tr w) x := by
    obtain ⟨C, hC, h⟩ := px7_col_norm_summable (m := (m : ℝ)) (b := (m : ℝ)) hOV.hd
    obtain ⟨hs, -⟩ := h (tr v) hvt
    have e : acol (tr v) x = fun l => ∑' k, Torus.mode k x * col (tr v) k l := by
      funext l; exact tsum_congr fun k => by simp [col, tr, mul_comm]
    rw [e]
    funext l
    have := px7_pass hF hOV.hm0 (fun k => col (tr v) k) (fun k => Torus.mode k x)
      (fun k => (Torus.norm_mode k x).le) (px7_mem2_col hvt) hs l
    rw [← this.tsum_eq]
    refine tsum_congr fun k => ?_
    simp only [acol, tr, hw, rowOp, col]
    rw [mul_comm]; rfl
  rw [hrow]
  have hwt : Summable fun p : Lattice d × Lattice d => ‖tr w p.1 p.2‖ := by
    have := (px7_summable_swap (f := fun p : Lattice d × Lattice d => ‖w p.1 p.2‖)).2 hsw
    exact this
  rw [← px7_ev_eq_toFun hwt y x, px7_ev_tr]

end Key


/-! ### Strong convergence of column operators -/

section Tannery

theorem px7_hsNormSq_eq_sq (b : ℝ) (c : Coeff d) : hsNormSq b c = hsNorm b c ^ 2 := by
  unfold hsNorm; rw [Real.sq_sqrt (hsNormSq_nonneg _ _)]

theorem px7_colOp_tendsto {ι' : Type*} {𝓕 : Filter ι'} {a b β M : ℝ} (F : ι' → Coeff d → Coeff d)
    (F₀ : Coeff d → Coeff d) (hF : ∀ᶠ i in 𝓕, OpOK2 a b (F i) M) (hF0 : OpOK2 a b F₀ M)
    (hlim : ∀ x, MemHs a x → Tendsto (fun i => hsNorm b (F i x - F₀ x)) 𝓕 (𝓝 0)) {u : Arr d}
    (hu : Mem2 a β u) :
    Tendsto (fun i => nrm2 b β (colOp (F i) u - colOp F₀ u)) 𝓕 (𝓝 0) := by
  obtain ⟨h1, h2⟩ := px7_mem2_iff_col.1 hu
  have hM := hF0.nonneg
  set f : ι' → Lattice d → ℝ := fun i l =>
    sobWeight β l * hsNormSq b (F i (col u l) - F₀ (col u l)) with hf
  have hbound : Summable fun l => (2 * M) ^ 2 * (sobWeight β l * hsNormSq a (col u l)) := h2.mul_left _
  have hlim' : ∀ l, Tendsto (fun i => f i l) 𝓕 (𝓝 0) := by
    intro l
    have := (hlim _ (h1 l)).pow 2
    simp only [zero_pow two_ne_zero] at this
    simpa [hf, px7_hsNormSq_eq_sq] using this.const_mul (sobWeight β l)
  have hbd : ∀ᶠ i in 𝓕, ∀ l, ‖f i l‖ ≤ (2 * M) ^ 2 * (sobWeight β l * hsNormSq a (col u l)) := by
    filter_upwards [hF] with i hi l
    have hm1 := hi.mem _ (h1 l)
    have hm2 := hF0.mem _ (h1 l)
    have t1 := MFAdjoint.hsNorm_sub_le_add hm1 hm2
    have t2 := hi.bound _ (h1 l)
    have t3 := hF0.bound _ (h1 l)
    have hn0 := hsNorm_nonneg' a (col u l)
    have hle : hsNorm b (F i (col u l) - F₀ (col u l)) ≤ 2 * M * hsNorm a (col u l) := by linarith
    have hn1 := hsNorm_nonneg' b (F i (col u l) - F₀ (col u l))
    have hsq := pow_le_pow_left₀ hn1 hle 2
    simp only [hf]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sobWeight_pos β l).le (hsNormSq_nonneg _ _)),
      px7_hsNormSq_eq_sq, px7_hsNormSq_eq_sq a]
    calc sobWeight β l * hsNorm b (F i (col u l) - F₀ (col u l)) ^ 2
        ≤ sobWeight β l * (2 * M * hsNorm a (col u l)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (sobWeight_pos β l).le
      _ = _ := by ring
  have hT := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓕) (f := f) (g := fun _ => (0 : ℝ))
    hbound hlim' hbd
  simp only [tsum_zero] at hT
  have hrep : ∀ᶠ i in 𝓕, nrm2 b β (colOp (F i) u - colOp F₀ u) = Real.sqrt (∑' l, f i l) := by
    filter_upwards [hF] with i hi
    have hm := (px7_colOp_mem hi hu).1
    have hm0 := (px7_colOp_mem hF0 hu).1
    have hsub := (hm.sub hm0).1
    unfold nrm2
    rw [px7_tsum_col hsub]
    rfl
  refine Tendsto.congr' (Filter.EventuallyEq.symm hrep) ?_
  have := (Real.continuous_sqrt.tendsto 0).comp hT
  rw [Real.sqrt_zero] at this
  exact this

theorem px7_nrm2_tr (a b : ℝ) (X : Arr d) : nrm2 b a (tr X) = nrm2 a b X := by
  unfold nrm2
  rw [px7_tsum_transp]

theorem px7_rowOp_tendsto {ι' : Type*} {𝓕 : Filter ι'} {a b β M : ℝ} (F : ι' → Coeff d → Coeff d)
    (F₀ : Coeff d → Coeff d) (hF : ∀ᶠ i in 𝓕, OpOK2 a b (F i) M) (hF0 : OpOK2 a b F₀ M)
    (hlim : ∀ x, MemHs a x → Tendsto (fun i => hsNorm b (F i x - F₀ x)) 𝓕 (𝓝 0)) {u : Arr d}
    (hu : Mem2 β a u) :
    Tendsto (fun i => nrm2 β b (rowOp (F i) u - rowOp F₀ u)) 𝓕 (𝓝 0) := by
  have := px7_colOp_tendsto F F₀ hF hF0 hlim (Mem2.transp hu).1
  refine this.congr fun i => ?_
  have e : rowOp (F i) u - rowOp F₀ u = tr (colOp (F i) (tr u) - colOp F₀ (tr u)) := rfl
  rw [e, px7_nrm2_tr]

end Tannery


/-! ### The pair operator -/

section Pair

variable {D : DynData d} {ρ : Torus d → ℝ} {m : ℕ} {T : ℝ → Coeff d → Coeff d} {Ah : Coeff d → Coeff d}

theorem OV.opok2 (hOV : OV D ρ m T Ah) :
    ∃ M c : ℝ, 0 < M ∧ 0 < c ∧ ∀ τ : ℝ, 0 ≤ τ →
      OpOK2 ((m + 2 : ℕ) : ℝ) ((m + 2 : ℕ) : ℝ) (T τ) (M * Real.exp (-c * τ)) := by
  obtain ⟨M, c, hM, hc, h⟩ := hOV.dec2
  have hmR : (m : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by push_cast; linarith
  refine ⟨M, c, hM, hc, fun τ hτ => ⟨fun x hx => (h τ hτ x hx).1, fun x hx => ?_,
    fun x y hx hy => hOV.add τ hτ x y (hx.mono hmR) (hy.mono hmR),
    fun a x hx => hOV.smul τ hτ x (hx.mono hmR) a⟩⟩
  have := (h τ hτ x hx).2
  linarith

theorem OV.opokAh (hOV : OV D ρ m T Ah) :
    ∃ K : ℝ, OpOK2 ((m + 2 : ℕ) : ℝ) (m : ℝ) Ah K := by
  obtain ⟨K, hK, h⟩ := hOV.Ah_bound
  exact ⟨K, fun x hx => (h x hx).1, fun x hx => (h x hx).2, fun x y hx hy => hOV.Ah_add x y hx hy,
    fun a x hx => hOV.Ah_smul a x⟩

/-- The difference quotient operator. -/
def qh (T : ℝ → Coeff d → Coeff d) (h : ℝ) (x : Coeff d) : Coeff d :=
  fun k => (T h x k - T 0 x k) / ((h : ℝ) : ℂ)

theorem OV.opokQ (hOV : OV D ρ m T Ah) :
    ∃ Kt : ℝ, 0 ≤ Kt ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → OpOK2 ((m + 2 : ℕ) : ℝ) (m : ℝ) (qh T h) Kt := by
  obtain ⟨Kt, hKt, hq⟩ := hOV.quot
  have hmR : (m : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by push_cast; linarith
  refine ⟨Kt, hKt, fun h hh0 hh1 => ⟨fun x hx => (hq x hx h hh0 hh1).1,
    fun x hx => (hq x hx h hh0 hh1).2, fun x y hx hy => ?_, fun c x hx => ?_⟩⟩
  · have hx' := hx.mono hmR
    have hy' := hy.mono hmR
    funext k
    simp only [qh, Pi.add_apply]
    rw [hOV.add h hh0.le x y hx' hy', hOV.add 0 le_rfl x y hx' hy']
    simp only [Pi.add_apply]; ring
  · have hx' := hx.mono hmR
    funext k
    simp only [qh, Pi.smul_apply, smul_eq_mul]
    rw [hOV.smul h hh0.le x hx' c, hOV.smul 0 le_rfl x hx' c]
    simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem OV.tcont_nrm (hOV : OV D ρ m T Ah) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ τ : ℝ, 0 ≤ τ → OpOK (m : ℝ) (T τ) M) ∧
      ∀ x, MemHs (m : ℝ) x →
        Tendsto (fun τ => hsNorm (m : ℝ) (T τ x - T σ x)) (𝓝[Set.Ici 0] σ) (𝓝 0) := by
  obtain ⟨M, c, hM, hc, hop⟩ := hOV.opok
  refine ⟨M, hM.le, fun τ hτ => ?_, fun x hx => hOV.tcont x hx σ hσ⟩
  have := hop τ hτ
  have hE : Real.exp (-c * τ) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  exact ⟨this.mem, fun x hx => (this.bound x hx).trans (mul_le_mul_of_nonneg_right
    (by nlinarith [Real.exp_pos (-c * τ)]) (hsNorm_nonneg' _ _)), this.add, this.smul⟩

/-- `PP τ u`: the pair semigroup on arrays (x-variable first). -/
def PP (T : ℝ → Coeff d → Coeff d) (τ : ℝ) (u : Arr d) : Arr d := rowOp (T τ) (colOp (T τ) u)

theorem px7_PP_mem (hOV : OV D ρ m T Ah) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : Arr d, Mem2 (m : ℝ) (m : ℝ) u →
      Mem2 (m : ℝ) (m : ℝ) (PP T τ u) ∧ nrm2 (m : ℝ) (m : ℝ) (PP T τ u) ≤ M * nrm2 (m : ℝ) (m : ℝ) u := by
  obtain ⟨M, c, hM, hc, hop⟩ := hOV.opok
  have hF := hop τ hτ
  refine ⟨(M * Real.exp (-c * τ)) ^ 2, by positivity, fun u hu => ?_⟩
  obtain ⟨h1, h2⟩ := px7_colOp_mem hF hu
  obtain ⟨h3, h4⟩ := px7_rowOp_mem hF h1
  refine ⟨h3, ?_⟩
  unfold PP
  calc _ ≤ (M * Real.exp (-c * τ)) * nrm2 (m : ℝ) (m : ℝ) (colOp (T τ) u) := h4
    _ ≤ (M * Real.exp (-c * τ)) * ((M * Real.exp (-c * τ)) * nrm2 (m : ℝ) (m : ℝ) u) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

theorem px7_PP_comm (hOV : OV D ρ m T Ah) {τ : ℝ} (hτ : 0 ≤ τ) {u : Arr d}
    (hu : Mem2 (m : ℝ) (m : ℝ) u) : PP T τ u = colOp (T τ) (rowOp (T τ) u) := by
  obtain ⟨M, c, hM, hc, hop⟩ := hOV.opok
  have hF := hop τ hτ
  exact (px7_arr_comm hF hF hu).symm

theorem px7_PP_RS (hOV : OV D ρ m T Ah) {τ : ℝ} (hτ : 0 ≤ τ) {u : Arr d}
    (hu : Mem2 (m : ℝ) (m : ℝ) u) (h : RS u) : RS (PP T τ u) := by
  obtain ⟨M, c, hM, hc, hop⟩ := hOV.opok
  have hF := hop τ hτ
  have hrc : ∀ z, MemHs (m : ℝ) z → T τ (reflConj z) = reflConj (T τ z) := fun z hz => hOV.refl hτ hz
  exact px7_rowOp_RS hF hrc (px7_colOp_mem hF hu).1 (px7_colOp_RS hF hrc hu h)

theorem px7_PP_semi (hOV : OV D ρ m T Ah) {σ τ : ℝ} (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) {u : Arr d}
    (hu : Mem2 (m : ℝ) (m : ℝ) u) : PP T (σ + τ) u = PP T σ (PP T τ u) := by
  obtain ⟨M, c, hM, hc, hop⟩ := hOV.opok
  have hFσ := hop σ hσ
  have hFτ := hop τ hτ
  have e1 : colOp (T (σ + τ)) u = colOp (T σ) (colOp (T τ) u) := by
    funext k l
    show T (σ + τ) (col u l) k = T σ (col (colOp (T τ) u) l) k
    rw [hOV.semi σ τ hσ hτ _ (px7_mem2_col hu l)]; rfl
  have hu1 := (px7_colOp_mem hFτ hu).1
  have e2 : ∀ w : Arr d, Mem2 (m : ℝ) (m : ℝ) w → rowOp (T (σ + τ)) w = rowOp (T σ) (rowOp (T τ) w) := by
    intro w hw
    rw [px7_rowOp_eq, px7_rowOp_eq, px7_rowOp_eq]
    have e : colOp (T (σ + τ)) (tr w) = colOp (T σ) (colOp (T τ) (tr w)) := by
      funext k l
      show T (σ + τ) (col (tr w) l) k = T σ (col (colOp (T τ) (tr w)) l) k
      rw [hOV.semi σ τ hσ hτ _ (px7_mem2_col (Mem2.transp hw).1 l)]; rfl
    rw [e]; rfl
  unfold PP
  rw [e1, e2 _ (px7_colOp_mem hFσ hu1).1, px7_arr_comm hFσ hFτ hu1]


theorem px7_PP_cont (hOV : OV D ρ m T Ah) {σ : ℝ} (hσ : 0 ≤ σ) {u : Arr d}
    (hu : Mem2 (m : ℝ) (m : ℝ) u) :
    Tendsto (fun τ => nrm2 (m : ℝ) (m : ℝ) (PP T τ u - PP T σ u)) (𝓝[Set.Ici 0] σ) (𝓝 0) := by
  obtain ⟨M, hM, hop, hlim⟩ := hOV.tcont_nrm hσ
  have hev : ∀ᶠ τ in 𝓝[Set.Ici 0] σ, 0 ≤ τ := self_mem_nhdsWithin
  have hF : ∀ᶠ τ in 𝓝[Set.Ici 0] σ, OpOK2 (m : ℝ) (m : ℝ) (T τ) M := by
    filter_upwards [hev] with τ hτ using hop τ hτ
  have hFσ := hop σ hσ
  have hw : Mem2 (m : ℝ) (m : ℝ) (colOp (T σ) u) := (px7_colOp_mem hFσ hu).1
  have t1 := px7_colOp_tendsto (𝓕 := 𝓝[Set.Ici 0] σ) T (T σ) hF hFσ hlim hu
  have t2 := px7_rowOp_tendsto (𝓕 := 𝓝[Set.Ici 0] σ) T (T σ) hF hFσ hlim hw
  have hb : ∀ᶠ τ in 𝓝[Set.Ici 0] σ, nrm2 (m : ℝ) (m : ℝ) (PP T τ u - PP T σ u) ≤
      M * nrm2 (m : ℝ) (m : ℝ) (colOp (T τ) u - colOp (T σ) u) +
        nrm2 (m : ℝ) (m : ℝ) (rowOp (T τ) (colOp (T σ) u) - rowOp (T σ) (colOp (T σ) u)) := by
    filter_upwards [hev] with τ hτ
    have hFτ := hop τ hτ
    have hcτ := (px7_colOp_mem hFτ hu).1
    have hcσ := hw
    have hA : Mem2 (m : ℝ) (m : ℝ) (colOp (T τ) u - colOp (T σ) u) := (hcτ.sub hcσ).1
    have hrτ := (px7_rowOp_mem hFτ hcσ).1
    have hrσ := (px7_rowOp_mem hFσ hcσ).1
    have hB : Mem2 (m : ℝ) (m : ℝ) (rowOp (T τ) (colOp (T σ) u) - rowOp (T σ) (colOp (T σ) u)) :=
      (hrτ.sub hrσ).1
    have e : PP T τ u - PP T σ u = rowOp (T τ) (colOp (T τ) u - colOp (T σ) u) +
        (rowOp (T τ) (colOp (T σ) u) - rowOp (T σ) (colOp (T σ) u)) := by
      rw [px7_rowOp_sub hFτ hcτ hcσ]
      unfold PP
      funext k l; simp only [Pi.sub_apply, Pi.add_apply]; ring
    rw [e]
    obtain ⟨hm1, hm2⟩ := (px7_rowOp_mem hFτ hA)
    obtain ⟨hm3, hm4⟩ := (hm1.add hB)
    exact hm4.trans (add_le_add hm2 le_rfl)
  refine squeeze_zero' (Filter.Eventually.of_forall fun τ => px7_nrm2_nonneg _ _ _) hb ?_
  simpa using (t1.const_mul M).add t2

theorem px7_PP_zero (hOV : OV D ρ m T Ah) {u : Arr d} (hu : Mem2 (m : ℝ) (m : ℝ) u)
    (hc : ∀ l, px7_mC ρ (col u l) = 0) (hr : ∀ k, px7_mC ρ (fun l => u k l) = 0) :
    PP T 0 u = u := by
  have hcol : colOp (T 0) u = u := by
    funext k l
    show T 0 (col u l) k = u k l
    rw [hOV.zero _ (px7_mem2_col hu l)]
    simp [px7_centerC, hc l, col]
  obtain ⟨M, c, hM, hc', hop⟩ := hOV.opok
  have hF := hop 0 le_rfl
  have hrow : rowOp (T 0) u = u := by
    funext k l
    show T 0 (fun l' => u k l') l = u k l
    have hk : MemHs (m : ℝ) (fun l' => u k l') := px7_mem2_col (Mem2.transp hu).1 k
    rw [hOV.zero _ hk]
    simp [px7_centerC, hr k]
  unfold PP
  rw [hcol, hrow]


theorem OpOK2.mono_M {a b : ℝ} {F : Coeff d → Coeff d} {M M' : ℝ} (h : OpOK2 a b F M) (hM : M ≤ M') :
    OpOK2 a b F M' :=
  ⟨h.mem, fun x hx => (h.bound x hx).trans (mul_le_mul_of_nonneg_right hM (hsNorm_nonneg' _ _)),
    h.add, h.smul⟩

/-- Generator on arrays. -/
def AA (Ah : Coeff d → Coeff d) (u : Arr d) : Arr d := colOp Ah u + rowOp Ah u

theorem px7_PP_deriv (hOV : OV D ρ m T Ah) {u : Arr d}
    (hu1 : Mem2 ((m + 2 : ℕ) : ℝ) (m : ℝ) u) (hu2 : Mem2 (m : ℝ) ((m + 2 : ℕ) : ℝ) u)
    (hc : ∀ l, px7_mC ρ (col u l) = 0) (hr : ∀ k, px7_mC ρ (fun l => u k l) = 0) :
    Mem2 (m : ℝ) (m : ℝ) (AA Ah u) ∧
    Tendsto (fun h : ℝ => nrm2 (m : ℝ) (m : ℝ) (fun k l =>
      (PP T h u k l - u k l) / ((h : ℝ) : ℂ) - AA Ah u k l)) (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
  have hmR : (m : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by push_cast; linarith
  have hu0 : Mem2 (m : ℝ) (m : ℝ) u := (hu1.mono hmR le_rfl).1
  obtain ⟨M, c, hM, hcc, hop⟩ := hOV.opok
  obtain ⟨KA, hKA⟩ := hOV.opokAh
  obtain ⟨Kt, hKt, hQ⟩ := hOV.opokQ
  have hKA0 := hKA.nonneg
  set K := max Kt KA with hK
  have hAh : OpOK2 ((m + 2 : ℕ) : ℝ) (m : ℝ) Ah K := hKA.mono_M (le_max_right _ _)
  have hpos : ∀ᶠ h in 𝓝[Set.Ioi (0 : ℝ)] 0, 0 < h ∧ h ≤ 1 := by
    have : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[Set.Ioi (0 : ℝ)] 0 := Ioc_mem_nhdsGT one_pos
    filter_upwards [this] with h hh using hh
  have hqF : ∀ᶠ h in 𝓝[Set.Ioi (0 : ℝ)] 0, OpOK2 ((m + 2 : ℕ) : ℝ) (m : ℝ) (qh T h) K := by
    filter_upwards [hpos] with h hh using (hQ h hh.1 hh.2).mono_M (le_max_left _ _)
  have hlimq : ∀ x, MemHs ((m + 2 : ℕ) : ℝ) x →
      Tendsto (fun h => hsNorm (m : ℝ) (qh T h x - Ah x)) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) := fun x hx =>
    hOV.deriv x hx
  have hmem_col : Mem2 (m : ℝ) (m : ℝ) (colOp Ah u) := (px7_colOp_mem hAh hu1).1
  have hmem_row : Mem2 (m : ℝ) (m : ℝ) (rowOp Ah u) := (px7_rowOp_mem hAh hu2).1
  refine ⟨(hmem_col.add hmem_row).1, ?_⟩
  -- convergence pieces
  have L_row := px7_rowOp_tendsto (𝓕 := 𝓝[Set.Ioi (0 : ℝ)] 0) (qh T) Ah hqF hAh hlimq hu2
  have L_col := px7_colOp_tendsto (𝓕 := 𝓝[Set.Ioi (0 : ℝ)] 0) (qh T) Ah hqF hAh hlimq hu1
  obtain ⟨M0, hM0, hop0, hlim0⟩ := hOV.tcont_nrm (σ := 0) le_rfl
  have hF0 : ∀ᶠ h in 𝓝[Set.Ioi (0 : ℝ)] 0, OpOK2 (m : ℝ) (m : ℝ) (T h) M0 := by
    filter_upwards [hpos] with h hh using hop0 h hh.1.le
  have hT0 := hop0 0 le_rfl
  have hlim0' : ∀ x, MemHs (m : ℝ) x →
      Tendsto (fun h => hsNorm (m : ℝ) (T h x - T 0 x)) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) := fun x hx =>
    (hlim0 x hx).mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
  have L_w := px7_rowOp_tendsto (𝓕 := 𝓝[Set.Ioi (0 : ℝ)] 0) (β := ((m + 2 : ℕ) : ℝ)) T (T 0) hF0 hT0 hlim0' hu1
  -- centering identities
  have hrow0 : rowOp (T 0) u = u := by
    funext k l
    show T 0 (fun l' => u k l') l = u k l
    have hk : MemHs (m : ℝ) (fun l' => u k l') := px7_mem2_col (Mem2.transp hu0).1 k
    rw [hOV.zero _ hk]
    simp [px7_centerC, hr k]
  have hcol0 : colOp (T 0) u = u := by
    funext k l
    show T 0 (col u l) k = u k l
    rw [hOV.zero _ (px7_mem2_col hu0 l)]
    simp [px7_centerC, hc l, col]
  have hbound : ∀ᶠ h in 𝓝[Set.Ioi (0 : ℝ)] 0,
      nrm2 (m : ℝ) (m : ℝ) (fun k l => (PP T h u k l - u k l) / ((h : ℝ) : ℂ) - AA Ah u k l) ≤
        K * nrm2 ((m + 2 : ℕ) : ℝ) (m : ℝ) (rowOp (T h) u - rowOp (T 0) u) +
        nrm2 (m : ℝ) (m : ℝ) (colOp (qh T h) u - colOp Ah u) +
        nrm2 (m : ℝ) (m : ℝ) (rowOp (qh T h) u - rowOp Ah u) := by
    filter_upwards [hpos, hqF, hF0] with h hh hqh hFh
    have hFh' := hop0 h hh.1.le
    have hwh : Mem2 ((m + 2 : ℕ) : ℝ) (m : ℝ) (rowOp (T h) u) := (px7_rowOp_mem hFh' hu1).1
    have hw0 : Mem2 ((m + 2 : ℕ) : ℝ) (m : ℝ) (rowOp (T 0) u) := (px7_rowOp_mem hT0 hu1).1
    have hwu : Mem2 ((m + 2 : ℕ) : ℝ) (m : ℝ) (rowOp (T h) u - u) := by
      have := (hwh.sub hu1).1; exact this
    have hcomm : colOp (T 0) (rowOp (T h) u) = rowOp (T h) u := by
      rw [px7_arr_comm hT0 hFh' hu0, hcol0]
    have hPP : PP T h u = colOp (T h) (rowOp (T h) u) := px7_PP_comm hOV hh.1.le hu0
    have X1 := px7_colOp_mem hqh hwu
    have hX2 : Mem2 (m : ℝ) (m : ℝ) (colOp (qh T h) u - colOp Ah u) :=
      ((px7_colOp_mem hqh hu1).1.sub hmem_col).1
    have hX3 : Mem2 (m : ℝ) (m : ℝ) (rowOp (qh T h) u - rowOp Ah u) :=
      ((px7_rowOp_mem hqh hu2).1.sub hmem_row).1
    have hdecomp : (fun k l => (PP T h u k l - u k l) / ((h : ℝ) : ℂ) - AA Ah u k l) =
        (colOp (qh T h) (rowOp (T h) u - u) + (colOp (qh T h) u - colOp Ah u)) +
          (rowOp (qh T h) u - rowOp Ah u) := by
      funext k l
      have e3 := congrFun (congrFun (px7_colOp_sub hqh hwh hu1) k) l
      simp only [Pi.sub_apply] at e3
      have ea : colOp (T 0) (rowOp (T h) u) k l = rowOp (T h) u k l := by rw [hcomm]
      have hh0 : ((h : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hh.1.ne'
      simp only [Pi.add_apply, Pi.sub_apply, AA, hPP, e3]
      have q1 : colOp (qh T h) (rowOp (T h) u) k l =
          (colOp (T h) (rowOp (T h) u) k l - colOp (T 0) (rowOp (T h) u) k l) / ((h : ℝ) : ℂ) := rfl
      have q2 : rowOp (qh T h) u k l =
          (rowOp (T h) u k l - rowOp (T 0) u k l) / ((h : ℝ) : ℂ) := rfl
      rw [q1, q2, ea, hrow0]
      field_simp
      ring
    rw [hdecomp]
    have hm1 : Mem2 (m : ℝ) (m : ℝ) (colOp (qh T h) (rowOp (T h) u - u)) := X1.1
    have hm12 := (hm1.add hX2)
    have hm123 := (hm12.1.add hX3)
    refine hm123.2.trans ?_
    have a1 := hm12.2
    have a2 := X1.2
    have e5 : rowOp (T h) u - u = rowOp (T h) u - rowOp (T 0) u := by rw [hrow0]
    rw [← e5]
    linarith
  refine squeeze_zero' (Filter.Eventually.of_forall fun h => px7_nrm2_nonneg _ _ _) hbound ?_
  have := ((L_w.const_mul K).add L_col).add L_row
  simpa using this

end Pair

end HRS.PDE.PX7

end
