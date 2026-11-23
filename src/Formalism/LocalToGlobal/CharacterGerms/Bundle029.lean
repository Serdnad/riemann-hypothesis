module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle016
public import Formalism.LocalToGlobal.CharacterGerms.Bundle023
public import Formalism.LocalToGlobal.CharacterGerms.Bundle022
import Formalism.LocalToGlobal.CharacterGerms.ConstMemTypeSetOfNonneg
public import Formalism.LocalToGlobal.CharacterGerms.GeOfPowEqOne
public import Formalism.LocalToGlobal.CharacterGerms.Bundle008
public import Formalism.LocalToGlobal.CharacterGerms.Bundle026
public import Formalism.LocalToGlobal.CharacterGerms.Bundle015
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C]

section Col

variable {dd : ℕ}

theorem hasSubst_col (col : Fin 2) :
    HasSubst (fun x : Fin dd => (X (col, x) : MvPowerSeries (Fin 2 × Fin dd) C)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem col_inj (col : Fin 2) : Function.Injective (fun x : Fin dd => (col, x)) :=
  fun _ _ h => (Prod.ext_iff.1 h).2

theorem subst_inCol {τ : Type} {a : Fin 2 × Fin dd → MvPowerSeries τ C} (ha : ∀ x, constantCoeff (a x) = 0)
    (col : Fin 2) (f : MvPowerSeries (Fin dd) C) :
    subst a (inCol col f) = subst (fun i => a (col, i)) f := by
  have hS := hasSubst_of_constantCoeff_zero ha
  unfold inCol
  rw [subst_comp_subst_apply (hasSubst_col col) hS]
  congr 1
  funext i
  rw [subst_X hS]

theorem inCol_X (col : Fin 2) (i : Fin dd) : inCol col (X i : MvPowerSeries (Fin dd) C) = X (col, i) := by
  unfold inCol
  rw [subst_X (hasSubst_col col)]

theorem coeff_subst_rename_out {σ τ : Type} [Finite σ] (φ : σ → τ) (F : MvPowerSeries σ C) (e : τ →₀ ℕ)
    (he : ∀ e' : σ →₀ ℕ, e'.mapDomain φ ≠ e) :
    coeff e (subst (fun s => (X (φ s) : MvPowerSeries τ C)) F) = 0 := by
  rw [coeff_subst (hasSubst_of_constantCoeff_zero fun s => constantCoeff_X _)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e'
  rw [prod_X_rename, coeff_monomial, if_neg (fun h => he e' h.symm), smul_zero]

theorem coeff_inCol_lin (col : Fin 2) (f f' : MvPowerSeries (Fin dd) C)
    (h : ∀ μ : Fin dd →₀ ℕ, μ.degree ≤ 1 → coeff μ f = coeff μ f') (μ : Fin 2 × Fin dd →₀ ℕ) (hμ : μ.degree ≤ 1) :
    coeff μ (inCol col f) = coeff μ (inCol col f') := by
  unfold inCol
  by_cases hr : ∃ μ' : Fin dd →₀ ℕ, μ'.mapDomain (fun x => (col, x)) = μ
  · obtain ⟨μ', rfl⟩ := hr
    rw [coeff_subst_rename_inj _ (col_inj col), coeff_subst_rename_inj _ (col_inj col)]
    exact h μ' (by rw [Finsupp.degree_mapDomain] at hμ; exact hμ)
  · push_neg at hr
    rw [coeff_subst_rename_out _ _ _ hr, coeff_subst_rename_out _ _ _ hr]

end Col

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (Y : FBChart C V O dd) {d : ℕ}
  {I0 : Type} [Fintype I0] (p : SelfData Y d I0)

theorem FBChart.self_chart_log_constantCoeff (x : Fin 2 × Fin dd) : constantCoeff ((Y.rawSelf p).lg x) = 0 := by
  show constantCoeff (inCol x.1 (un1 (Y.lg x.2))) = 0
  apply constantCoeff_inCol
  rw [constantCoeff_uncurry]
  exact Y.lg_const x.2

theorem FBChart.self_chart_exp_constantCoeff (x : Fin 2 × Fin dd) : constantCoeff ((Y.rawSelf p).ex x) = 0 := by
  show constantCoeff (inCol x.1 (un1 (Y.ex x.2))) = 0
  apply constantCoeff_inCol
  rw [constantCoeff_uncurry]
  exact Y.ex_const x.2

theorem FBChart.rawSelf_axis0 (e : Fin 2 × (Fin 2 × Fin dd) →₀ ℕ) (he : ∀ s ∈ e.support, s.1 ≠ 0) :
    coeff e (Y.rawSelf p).h = 0 := by
  show coeff e (∑ col, hCol col Y.h) = 0
  exact van_sum Finset.univ _ (fun col _ => van_hCol col 0 Y.h (gauge_axes Y 0)) e he

theorem FBChart.rawSelf_exlg (x : Fin 2 × Fin dd) :
    subst (Y.rawSelf p).lg ((Y.rawSelf p).ex x) = (X x : MvPowerSeries (Fin 2 × Fin dd) C) := by
  obtain ⟨col, i⟩ := x
  show subst (Y.rawSelf p).lg (inCol col (un1 (Y.ex i))) = _
  rw [subst_inCol (Y.self_chart_log_constantCoeff p)]
  show subst (fun j => inCol col (un1 (Y.lg j))) (un1 (Y.ex i)) = _
  have hL : HasSubst (fun j => un1 (Y.lg j)) :=
    hasSubst_of_constantCoeff_zero fun j => by rw [constantCoeff_uncurry, Y.lg_const]
  have hx : un1 (comp1 Y.ex Y.lg i) = (X i : MvPowerSeries (Fin dd) C) := by rw [Y.ex_lg]; exact uncurry_X i
  unfold inCol
  rw [← subst_comp_subst_apply hL (hasSubst_col col), uncurry_comp Y.lg_const, hx, subst_X (hasSubst_col col)]

theorem FBChart.rawSelf_lgex (x : Fin 2 × Fin dd) :
    subst (Y.rawSelf p).ex ((Y.rawSelf p).lg x) = (X x : MvPowerSeries (Fin 2 × Fin dd) C) := by
  obtain ⟨col, i⟩ := x
  show subst (Y.rawSelf p).ex (inCol col (un1 (Y.lg i))) = _
  rw [subst_inCol (Y.self_chart_exp_constantCoeff p)]
  show subst (fun j => inCol col (un1 (Y.ex j))) (un1 (Y.lg i)) = _
  have hL : HasSubst (fun j => un1 (Y.ex j)) :=
    hasSubst_of_constantCoeff_zero fun j => by rw [constantCoeff_uncurry, Y.ex_const]
  have hx : un1 (comp1 Y.lg Y.ex i) = (X i : MvPowerSeries (Fin dd) C) := by rw [Y.lg_ex]; exact uncurry_X i
  unfold inCol
  rw [← subst_comp_subst_apply hL (hasSubst_col col), uncurry_comp Y.ex_const, hx, subst_X (hasSubst_col col)]

theorem FBChart.rawSelf_lin (x : Fin 2 × Fin dd) (μ : Fin 2 × Fin dd →₀ ℕ) (hμ : μ.degree ≤ 1) :
    coeff μ ((Y.rawSelf p).lg x) = coeff μ (X x : MvPowerSeries (Fin 2 × Fin dd) C) := by
  obtain ⟨col, i⟩ := x
  show coeff μ (inCol col (un1 (Y.lg i))) = _
  rw [← inCol_X col i]
  refine coeff_inCol_lin col _ _ (fun ν hν => ?_) μ hμ
  show coeff (ν.mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (Y.lg i) = _
  rw [Y.lg_lin i _ (by rw [Finsupp.degree_mapDomain]; exact hν), ← uncurry_X i]
  rfl

theorem SelfData.gm_int (a : ZMod d) (r s : Fin 2) : V.Ge 0 (p.gm a r s) := by
  obtain ⟨M, hM⟩ := p.gm_lim 0
  have h := hM a r s
  rw [Nat.cast_zero] at h
  have e : p.gm a r s = (p.gm a r s - p.em a (M r s)) + p.em a (M r s) := by ring
  rw [e]
  exact h.add (p.em_int a _)

theorem FBChart.rawSelf_u_integral (g : Fin 2) (c : I0) (x : Fin 2 × Fin dd) : V.Ge 0 ((Y.rawSelf p).u g c x) :=
  VF.Ge.mul_int (SelfData.gm_int Y p _ _ _) (p.e_int c x.2)

theorem SelfData.gm_pair (a : ZMod d) (g : Fin 2) :
    ∑ col, p.gm a col g * p.gm (a + p.hd) col (1 - g) = 1 := by
  have h := p.gm_hyp (a + p.hd) g (1 - g)
  rw [add_assoc, p.hd_two, add_zero, if_neg (by fin_cases g <;> decide)] at h
  exact h

theorem FBChart.exists_integral_right_inverse (g : Fin 2) :
    ∃ w : Fin 2 × Fin dd → I0 → C, (∀ x c, V.Ge 0 (w x c)) ∧
      ∀ c c' : I0, ∑ x, (Y.rawSelf p).u g c x * w x c' = if c = c' then 1 else 0 := by
  obtain ⟨w0, hw0, huw⟩ := p.e_sat
  refine ⟨fun x c' => p.gm (p.ty0 c' + p.hd) x.1 (1 - g) * w0 x.2 c',
    fun x c' => VF.Ge.mul_int (SelfData.gm_int Y p _ _ _) (hw0 _ _), fun c c' => ?_⟩
  show ∑ x : Fin 2 × Fin dd, (p.gm (p.ty0 c) x.1 g * p.e c x.2) * (p.gm (p.ty0 c' + p.hd) x.1 (1 - g) * w0 x.2 c') = _
  have e1 : ∀ x : Fin 2 × Fin dd, (p.gm (p.ty0 c) x.1 g * p.e c x.2) * (p.gm (p.ty0 c' + p.hd) x.1 (1 - g) * w0 x.2 c') =
      (p.gm (p.ty0 c) x.1 g * p.gm (p.ty0 c' + p.hd) x.1 (1 - g)) * (p.e c x.2 * w0 x.2 c') := fun x => by ring
  simp_rw [e1]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, huw c c']
  by_cases hc : c = c'
  · subst hc
    rw [if_pos rfl]
    simp only [mul_one]
    exact SelfData.gm_pair Y p _ g
  · simp [hc]

def PTSelfSt : Prop :=
  AllSelf fun C _ V d I _ _ X => ∀ (g : Fin 2) (a : ZMod d) (w : I g → C), (∀ c, V.Ge 0 (w c)) →
    (∀ c, X.tyC g (Sum.inl c) ≠ a → w c = 0) →
    ∃ x ∈ X.TySet V g, x 0 = Sum.elim w 0 ∧ ∀ (i : ℕ) n, X.tyC g n ≠ a + i → x i n = 0

def AddCvSelfSt : Prop := AllSelf fun _ _ V _ _ _ _ X => X.AddCvSt V

def HStabSelfSt : Prop :=
  AllSelf fun _ _ V _ I _ _ X => ∀ (g : Fin 2) (c : I g) (q : JJ I g), X.ty g c ≠ X.ty (1 - g) q →
    V.Ge 0 (X.sg1 (X.u g c) (X.u (1 - g) q))

theorem cartSelf_of (hPT : PTSelfSt) (hAdd : AddCvSelfSt) (hStab : HStabSelfSt) : CartSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p g
  have := Y.algClosed
  have : NeZero (V.l : C) := ⟨VF.l_ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C V.l
  have h0 := (Y.rawSelf p).zero_mem (Y.self_chart_log_constantCoeff p) (Y.rawSelf_axis0 p) V g
  have hadd := (Y.rawSelf p).add_mem V g (hAdd C V O dd Y d I0 p) (fun g c x => Y.rawSelf_u_integral p g c x)
  exact
    { zero := h0
      add := hadd
      neg := (Y.rawSelf p).neg_mem V g Y.l_odd
      teich := (Y.rawSelf p).teich_mem V g
      Vm := (Y.rawSelf p).V_mem V g
      Fm := (Y.rawSelf p).F_mem V g (Y.self_chart_log_constantCoeff p) (Y.rawSelf_exlg p) hζ h0 hadd
      sumV := (Y.rawSelf p).sumV_mem V g (Y.self_chart_log_constantCoeff p) (Y.self_chart_exp_constantCoeff p) (Y.rawSelf_exlg p) (Y.rawSelf_lgex p) h0 hadd
      t2 := (Y.rawSelf p).val_nonneg_leading_coeff_of_mem_tySet V g (Y.rawSelf_lin p) (Y.rawSelf_axis0 p) (Y.exists_integral_right_inverse p g) (hStab C V O dd Y d I0 p g)
      t3 := (Y.rawSelf p).const_mem_type_set_of_nonneg (Y.self_chart_log_constantCoeff p) (Y.rawSelf_axis0 p) V g
      t4 := hPT C V O dd Y d I0 p g }

end Formalism.L2.FormalSeriesBounds
end
end

section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}

structure LabS (E : Type) [Field E] (C : Type) (Orb : Type) (d : ℕ) where
  tau : Orb → ZMod d → (E →+* ℂ)
  hd : ZMod d
  gm : Orb → ZMod d → Matrix (Fin 2) (Fin 2) C
  n : ℕ
  j : ℕ
  j' : ℕ
  big : Orb → Fin 2 → ZMod d → Prop

abbrev LabS.II {Orb : Type} {d : ℕ} (lab : LabS E C Orb d) (Dw : Datum H) (o : Orb) : Type :=
  Σ a : ZMod d, Fin (Dw.mult (lab.tau o a))

section Pairs

variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} {d : ℕ} [NeZero d]

def selfLieBasisVector (C3 : IntChart T io y) (ι : T.Fr →+* C) (lab : LabS E C Orb d) (o : Orb) (x : lab.II Dw o) :
    Fin (chD C3.ch) → C := fun i => ι (chartUnitVectors C3 ⟨lab.tau o x.1, x.2⟩ i)

structure LabSArith (V : VF C) (io : c.F →+* T.Fr) (ι : T.Fr →+* C) (lab : LabS E C Orb d) : Prop where
  inj : Function.Injective fun x : Orb × ZMod d => lab.tau x.1 x.2
  hd_ne : lab.hd ≠ 0
  hd_two : lab.hd + lab.hd = 0
  conj : ∀ o a, ComplexEmbedding.conjugate (lab.tau o a) = lab.tau o (a + lab.hd)
  frob : ∀ o a x, V.MM (emA3 io ι (lab.tau o (a + 1)) x - emA3 io ι (lab.tau o a) x ^ V.l)
  sep : ∀ x x' : Orb × ZMod d, x ≠ x' →
    ∃ a : 𝓞 E, V.v (emA3 io ι (lab.tau x.1 x.2) a - emA3 io ι (lab.tau x'.1 x'.2) a) = 0
  unr : ∀ o, ∃ ε : 𝓞 E, (∃ y, ε * ε - ε = (V.l : 𝓞 E) * y) ∧ (∀ a, V.MM (emA3 io ι (lab.tau o a) ε - 1)) ∧
    ∀ x : 𝓞 E, (∀ a, V.MM (emA3 io ι (lab.tau o a) x)) → ∃ y, ε * x = (V.l : 𝓞 E) * y
  gm_lim : ∀ o (N : ℕ), ∃ M : Matrix (Fin 2) (Fin 2) (𝓞 E), ∀ a r s,
    V.Ge N (lab.gm o a r s - emA3 io ι (lab.tau o a) (M r s))
  gm_hyp : ∀ o a (s s' : Fin 2), ∑ r, lab.gm o (a + lab.hd) r s * lab.gm o a r s' = if s = s' then 0 else 1

structure LabSGeo (C3 : IntChart T io y) (ι : T.Fr →+* C) (Y : FBChart C V (𝓞 E) (chD C3.ch)) (lab : LabS E C Orb d) :
    Prop where
  em_int : ∀ o a x, V.Ge 0 (emA3 io ι (lab.tau o a) x)
  em_conj : ∀ o a x, emA3 io ι (lab.tau o a) (star x) = emA3 io ι (lab.tau o (a + lab.hd)) x
  e_int : ∀ o x i, V.Ge 0 (selfLieBasisVector C3 ι lab o x i)
  e_eig : ∀ o (x : lab.II Dw o) a, linAct (Y.B.A.act a) (selfLieBasisVector C3 ι lab o x) =
    emA3 io ι (lab.tau o x.1) a • selfLieBasisVector C3 ι lab o x
  e_sat : ∀ o, ∃ w : Fin (chD C3.ch) → lab.II Dw o → C, (∀ x q, V.Ge 0 (w x q)) ∧
    ∀ q q' : lab.II Dw o, ∑ x, selfLieBasisVector C3 ι lab o q x * w x q' = if q = q' then 1 else 0
  e_full : ∀ o a (v : Fin (chD C3.ch) → C), (∀ x, linAct (Y.B.A.act x) v = emA3 io ι (lab.tau o a) x • v) →
    ∃ b : lab.II Dw o → C, (∀ q, q.1 ≠ a → b q = 0) ∧ v = ∑ q, b q • selfLieBasisVector C3 ι lab o q

def selfOfLab {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb d}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) (o : Orb) : SelfData Y d (lab.II Dw o) where
  em := fun a => emA3 io ι (lab.tau o a)
  em_int := hg.em_int o
  em_frob := ha.frob o
  em_sep := fun a a' h => ha.sep (o, a) (o, a') (fun e => h (Prod.mk.inj e).2)
  em_unr := ha.unr o
  hd := lab.hd
  hd_ne := ha.hd_ne
  hd_two := ha.hd_two
  em_conj := hg.em_conj o
  e := selfLieBasisVector C3 ι lab o
  ty0 := fun x => x.1
  e_int := hg.e_int o
  e_eig := hg.e_eig o
  e_sat := by
    obtain ⟨w, h1, h2⟩ := hg.e_sat o
    exact ⟨w, h1, fun q q' => by convert h2 q q'⟩
  e_full := hg.e_full o
  gm := lab.gm o
  gm_lim := ha.gm_lim o
  gm_hyp := ha.gm_hyp o
  n := lab.n
  j := lab.j
  j' := lab.j'
  big := lab.big o

theorem selfSep_ofLab {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb d}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) : SelfSep Y (selfOfLab ha hg) := by
  intro x x' hne
  exact ha.sep x x' hne

def LabS.RankOK (lab : LabS E C Orb d) (Dw : Datum H) : Prop :=
  ∀ o, (∀ g a, lab.big o (1 - g) a ↔ ¬ lab.big o g a) ∧
    (∀ a, lab.big o 0 a → Dw.mult (lab.tau o a) = lab.n + lab.j) ∧
    (∀ a, ¬ lab.big o 0 a → Dw.mult (lab.tau o a) = lab.j') ∧
    (∀ a, lab.big o 1 a → Dw.mult (lab.tau o (a - lab.hd)) = lab.n + lab.j) ∧
    (∀ a, ¬ lab.big o 1 a → Dw.mult (lab.tau o (a - lab.hd)) = lab.j')

theorem card_sigma_shift (m : ZMod d → ℕ) (h a : ZMod d) :
    (Finset.univ.filter fun x : (Σ a : ZMod d, Fin (m a)) => x.1 + h = a).card = m (a - h) := by
  have e1 : (Finset.univ.filter fun x : (Σ a : ZMod d, Fin (m a)) => x.1 + h = a) =
      (Finset.univ.filter fun b : ZMod d => b + h = a).sigma fun b => Finset.univ := by
    ext ⟨b, i⟩
    simp
  have e2 : (Finset.univ.filter fun b : ZMod d => b + h = a) = {a - h} := by
    ext b
    simp [eq_sub_iff_add_eq]
  rw [e1, Finset.card_sigma, e2, Finset.sum_singleton, Finset.card_univ, Fintype.card_fin]

theorem rankHyp_ofLabS {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb d}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) (hr : lab.RankOK Dw) (o : Orb) :
    (Y.rawSelf (selfOfLab ha hg o)).RankHyp := by
  refine { big_compl := (hr o).1, rk_big := ?_, rk_small := ?_ }
  · refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · intro a hb
      simp only [FBChart.rawSelf, selfOfLab]
      convert (card_sigma_fst (fun b => Dw.mult (lab.tau o b)) a).trans ((hr o).2.1 a hb) using 2
      exact Finset.filter_congr (fun _ _ => Iff.rfl)
    · intro a hb
      simp only [FBChart.rawSelf, selfOfLab, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
      exact (card_sigma_shift (fun b => Dw.mult (lab.tau o b)) lab.hd a).trans ((hr o).2.2.2.1 a hb)
  · refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · intro a hb
      simp only [FBChart.rawSelf, selfOfLab]
      convert (card_sigma_fst (fun b => Dw.mult (lab.tau o b)) a).trans ((hr o).2.2.1 a hb) using 2
      exact Finset.filter_congr (fun _ _ => Iff.rfl)
    · intro a hb
      simp only [FBChart.rawSelf, selfOfLab, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
      exact (card_sigma_shift (fun b => Dw.mult (lab.tau o b)) lab.hd a).trans ((hr o).2.2.2.2 a hb)

end Pairs

section Named

variable (Xo c)

def GmExSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) → V.l ≠ 2 →
    ∀ (Orb : Type) (d : ℕ) [NeZero d] (tau : Orb → ZMod d → (E →+* ℂ)) (hd : ZMod d), hd ≠ 0 → hd + hd = 0 →
    (∀ o a, ComplexEmbedding.conjugate (tau o a) = tau o (a + hd)) →
    (∀ o a x, V.MM (emA3 io ι (tau o (a + 1)) x - emA3 io ι (tau o a) x ^ V.l)) →
    (∀ x x' : Orb × ZMod d, x ≠ x' → ∃ a : 𝓞 E, V.v (emA3 io ι (tau x.1 x.2) a - emA3 io ι (tau x'.1 x'.2) a) = 0) →
    ∃ gm : Orb → ZMod d → Matrix (Fin 2) (Fin 2) C,
      (∀ o (N : ℕ), ∃ M : Matrix (Fin 2) (Fin 2) (𝓞 E), ∀ a r s, V.Ge N (gm o a r s - emA3 io ι (tau o a) (M r s))) ∧
      ∀ o a (s s' : Fin 2), ∑ r, gm o (a + hd) r s * gm o a r s' = if s = s' then 0 else 1

def AllSelfConjugateCharts (Φ : ∀ (C : Type) [Field C] (_V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (dd : ℕ),
    RawChart C d I (Fin 2 × Fin dd) → Prop) : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : LabS E C Orb d) (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab),
    lab.RankOK Dw → ∀ o, Φ C V d (fun _ => lab.II Dw o) (chD C3.ch) (Y.rawSelf (selfOfLab ha hg o))

def RankMaximalSelfCharts : Prop := AllSelfConjugateCharts Xo c fun _ _ V _ _ _ _ X => ∀ Hc : ∀ g, X.CartHyp V g, RawChart.RankMaximalCondition Hc

end Named

section Top

variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} {d : ℕ} [NeZero d]

end Top

end Formalism.L2.FormalSeriesBounds
end
end
