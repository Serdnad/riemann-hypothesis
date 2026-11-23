module

import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle063
public import Formalism.LocalToGlobal.CharacterGerms.Bundle023
public import Formalism.LocalToGlobal.CharacterGerms.Bundle030
public import Formalism.LocalToGlobal.CharacterGerms.Bundle006
public import Formalism.LocalToGlobal.CharacterGerms.Bundle032
public import Formalism.LocalToGlobal.CharacterGerms.Bundle031
public import Formalism.LocalToGlobal.CharacterGerms.Bundle018
import Formalism.LocalToGlobal.CharacterGerms.UncurryLogConstantCoeff
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem ge_of_isIntegral {C : Type} [Field C] (V : VF C) {x : C} (hx : IsIntegral ℤ x) : V.Ge 0 x := by
  apply GlobalTheory.LabelledDirections.ge_zero_of_isIntegral <;> assumption

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

theorem embedding_integral (ι : T.Fr →+* C) (τ : E →+* ℂ) (x : 𝓞 E) : V.Ge 0 (emA3 io ι τ x) := by
  exact ge_of_isIntegral V ((Algebra.IsIntegral.isIntegral (R := ℤ) x).map (emA3 io ι τ).toIntAlgHom)

theorem embK_conj (hstar : ∀ a : 𝓞 E, star a = H.bar a) (τ : E →+* ℂ) (x : 𝓞 E) :
    embK c (ComplexEmbedding.conjugate τ) x = embK c τ (star x) := by
  unfold embK
  apply Subtype.ext
  simp [embF]
  rw [hstar]
  rw [show (algebraMap (𝓞 E) E) (H.bar x) = ((H.bar x : 𝓞 E) : E) from rfl, H.bar_eq x,
    IsCMField.complexEmbedding_complexConj]

theorem embedding_conjugate (hstar : ∀ a : 𝓞 E, star a = H.bar a) (ι : T.Fr →+* C) (τ : E →+* ℂ) (x : 𝓞 E) :
    emA3 io ι (ComplexEmbedding.conjugate τ) x = emA3 io ι τ (star x) := by
  simp only [emA3, RingHom.coe_comp, Function.comp_apply, embK_conj hstar]

theorem a3uvec_int (C3 : IntChart T io y) {ι : T.Fr →+* C} (hι : EmbOK T V ι) (ℓ : Lt1 Dw) (i : Fin (chD C3.ch)) :
    V.Ge 0 (ι (chartUnitVectors C3 ℓ i)) := by
  rw [show chartUnitVectors C3 ℓ i = algebraMap T.V T.Fr (C3.uvecT ℓ i) from C3.gen.1.2.2.2.2.2.2 ℓ i]
  exact embIntSt_holds T C V ι hι _

section Core

variable {Orb : Type} {d : ℕ} [NeZero d]

end Core

variable (Xo c)

end Formalism.L2.FormalSeriesBounds
end
end

section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Defs

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

def FBChart.FirstVanishingAt (Y : FBChart C V O dd) (u : Fin dd → C) : Prop :=
  ∀ k : Fin dd,
    V.MM (∑ i, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) (mulL Y.B.G.F V.l k) * u i ^ V.l)

def FBChart.aLin (Y : FBChart C V O dd) (u v : Fin dd → C) : C :=
  ∑ j, v j * MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (Y.aOf u)

def FBChart.LgLin (Y : FBChart C V O dd) (γ : Fin dd → PowerSeries C) (U : Fin dd → C) : Prop :=
  ∀ i, Agr (V.l ^ 2) (alongCv γ (un1 (Y.lg i))) (U i • (MvPowerSeries.X () : PowerSeries C))

end Defs

def FirstVanishingCore : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (γ : Fin dd → PowerSeries C) (U : Fin dd → C),
    IsCv V γ → Y.LgLin γ U → Y.FirstVanishingAt U

def FunEqCoreSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (u : Fin dd → C), (∀ i, V.Ge 0 (u i)) → Y.FirstVanishingAt u →
    ∀ μ, V.MM (MvPowerSeries.coeff μ (cobd Y.B.G.F (Y.aOf u) - frobTw V.l (Y.chartLinearTerm u)))

def CurveLinearTermCondition : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (γ : Fin dd → PowerSeries C) (U : Fin dd → C),
    IsCv V γ → Y.LgLin γ U → ∀ v : Fin dd → C, (∀ i, V.Ge 0 (v i)) →
    V.MM ((V.l : C) * PowerSeries.coeff V.l (alongCv γ (un1 (Y.sgP v))) - Y.aLin U v)

def ALinAdjSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (e eb : Pt C 1 dd),
    (∀ i, IntS V (e i)) → (∀ i, IntS V (eb i)) →
    (∀ i, MvPowerSeries.constantCoeff (e i) = 0) → (∀ i, MvPowerSeries.constantCoeff (eb i) = 0) →
    comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)) →
    IntS V (FB.expS C (ev (n := 2) ![comp1 e (pt C dd 0), pt C dd 1] Y.h -
      ev (n := 2) ![pt C dd 0, comp1 eb (pt C dd 1)] Y.h)) →
    ∀ u : Fin dd → C, (∀ i, V.Ge 0 (u i)) → Y.FirstVanishingAt u → ∀ v : Fin dd → C, (∀ i, V.Ge 0 (v i)) →
    V.MM (Y.aLin (linAct e u) v - Y.aLin u (linAct eb v))

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

section Chain

variable {C : Type} [Field C] {T Orb : Type} [Fintype Orb] {r : T → ℕ} {tau : Orb → ZMod 2 → T}
  {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C} {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

theorem chain_aeval {σ τ : Type} [Fintype σ] (S : MvPolynomial σ C →ₐ[C] MvPolynomial τ C) (ℓ : τ) (p : MvPolynomial σ C) :
    pderiv ℓ (S p) = ∑ y, S (pderiv y p) * pderiv ℓ (S (X y)) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp [MvPolynomial.algHom_C, MvPolynomial.pderiv_C]
  | add p q hp hq =>
    simp only [map_add (f := _), hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p i hp =>
    have key : ∀ y, S (pderiv y (p * X i)) = (if i = y then S p else 0) + S (X i) * S (pderiv y p) := by
      intro y
      rw [Derivation.leibniz, pderiv_X]
      by_cases h : i = y
      · subst h
        simp
      · simp [Pi.single_apply, h]
    conv_lhs => rw [map_mul S p (X i), Derivation.leibniz, hp]
    simp only [key, smul_eq_mul, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum, mul_assoc]
    try ring

theorem pderiv_subG_off {p : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C} {ℓ : Letter T r n}
    (h : ∀ z, ℓ ≠ lam r tau plc z) : pderiv ℓ (subG r tau gm plc p) = 0 := by
  rw [chain_aeval]
  refine Finset.sum_eq_zero fun y _ => ?_
  have hX : pderiv ℓ (subG r tau gm plc (X y)) = 0 := by
    unfold subG

    rw [MvPolynomial.aeval_X, map_sum]
    refine Finset.sum_eq_zero fun col _ => ?_
    rw [Derivation.leibniz, MvPolynomial.pderiv_C, smul_zero, add_zero, MvPolynomial.pderiv_X]
    have hne : (⟨tau y.2.1 y.2.2.2.1, y.2.2.2.2, plc (y.1, col)⟩ : Letter T r n) ≠ ℓ := by
      intro heq
      apply h (((eW r tau N) y).1, col)
      rw [← heq]
      rfl
    simp [Pi.single_apply, hne]
  rw [hX, mul_zero]

private theorem lam_injective_of_tau_injective (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2)
    (z z' : AA r tau N × Fin 2) (h : lam r tau plc z = lam r tau plc z') : z = z' := by
  obtain ⟨⟨n1, o1, s1, i1⟩, c1⟩ := z
  obtain ⟨⟨n2, o2, s2, i2⟩, c2⟩ := z'
  injection h with h0 h3
  have h1 : tau o1 s1 = tau o2 s2 := h0
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (@inj (o1, s1) (o2, s2) h1)
  have h4 : (i1, plc (n1, c1)) = (i2, plc (n2, c2)) := eq_of_heq h3
  obtain ⟨rfl, h5⟩ := Prod.mk.inj h4
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (plc.injective h5)
  rfl

private theorem pderiv_lam_subG_X_eq_ite (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2)
    (α0 : AA r tau N) (col0 : Fin 2) (y : Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) :
    pderiv (lam r tau plc (α0, col0)) (subG r tau gm plc (X y)) =
      if (eW r tau N y).1 = α0 then MvPolynomial.C (gm y.2.1 y.2.2.2.1 col0 y.2.2.1) else 0 := by
  unfold subG

  rw [MvPolynomial.aeval_X, map_sum]
  have key : ∀ col : Fin 2, pderiv (lam r tau plc (α0, col0))
      (MvPolynomial.C (gm y.2.1 y.2.2.2.1 col y.2.2.1) *
        MvPolynomial.X (⟨tau y.2.1 y.2.2.2.1, y.2.2.2.2, plc (y.1, col)⟩ : Letter T r n)) =
      if ((eW r tau N y).1, col) = (α0, col0) then MvPolynomial.C (gm y.2.1 y.2.2.2.1 col y.2.2.1) else 0 := by
    intro col
    rw [Derivation.leibniz, MvPolynomial.pderiv_C, smul_zero, add_zero, MvPolynomial.pderiv_X]
    have e1 : (⟨tau y.2.1 y.2.2.2.1, y.2.2.2.2, plc (y.1, col)⟩ : Letter T r n) =
        lam r tau plc ((eW r tau N y).1, col) := rfl
    rw [e1, Pi.single_apply]
    by_cases hz : ((eW r tau N y).1, col) = (α0, col0)
    · rw [if_pos (congrArg (lam r tau plc) hz), if_pos hz, smul_eq_mul, mul_one]
    · rw [if_neg (fun h' => hz (lam_injective_of_tau_injective plc inj _ _ h')), if_neg hz, smul_zero]
  simp only [key]
  by_cases ha : (eW r tau N y).1 = α0
  · simp [ha]
  · simp [ha]

theorem pderiv_subG_lam (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) (α0 : AA r tau N) (col0 : Fin 2)
    (p : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C) :
    pderiv (lam r tau plc (α0, col0)) (subG r tau gm plc p) =
      ∑ g, MvPolynomial.C (Gm r tau gm α0 col0 g) * subG r tau gm plc (pderiv ((eW r tau N).symm (α0, g)) p) := by
  rw [chain_aeval, ← (eW r tau N).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single α0]
  · refine Finset.sum_congr rfl fun g _ => ?_
    rw [pderiv_lam_subG_X_eq_ite plc inj]
    simp only [Equiv.apply_symm_apply]
    first | rw [if_pos rfl] | skip
    exact mul_comm _ _
  · intro α _ hα
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [pderiv_lam_subG_X_eq_ite plc inj]
    simp only [Equiv.apply_symm_apply]
    first | rw [if_neg hα] | simp [hα]
    first | exact mul_zero _ | simp
  · intro h
    exact absurd (Finset.mem_univ _) h

end Chain

end Formalism.L2.FormalSeriesBounds.RF
end
end

section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ CharacteristicFromRanks ValuationFitting
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (IsCh dl res HasAF)

variable {C : Type} [Field C] [CharZero C] {V : VF C} {OE : Type} [CommRing OE] [StarRing OE] {dd : ℕ} {d : ℕ} [NeZero d]
  {I0 : Type} [Fintype I0]

def UPCharSelfSt (Y : FBChart C V OE dd) (p : SelfData Y d I0) (Hc : ∀ g, (Y.rawSelf p).CartHyp V g) : Prop :=
  ∃ (h : Fin 2 → ℕ) (χ : ∀ g, Fin (h g) → Fin 2 → PS C 1 dd), (∀ g i col, Y.IsChar (χ g i col)) ∧
    ∀ g a, p.big g a →
      ∃ e : Fin (pT (fun g => RawChart.cart (Hc g)) g a) ≃ {x : I0 // (RawChart.cart (Hc g)).ty (Sum.inl x) = a},
        ((Y.rawSelf p).AltC →
          S4.lenCoker V.v (Matrix.of fun c i => p.yOf g (χ g i) (e c)) ≤
            ((upB V.l (p.n + p.j) p.j' (gam V.l) : ℝ) : WithTop ℝ)) ∧
        ((∀ b, p.big g b) →
          S4.lenCoker V.v (Matrix.of fun c i => p.yOf g (χ g i) (e c)) ≤
            ((upB V.l (p.n + p.j) p.j' 0 : ℝ) : WithTop ℝ))

theorem chStSelf_of_upChar (Y : FBChart C V OE dd) (p : SelfData Y d I0) (hr : (Y.rawSelf p).RankHyp)
    (Hc : ∀ g, (Y.rawSelf p).CartHyp V g) (h : UPCharSelfSt Y p Hc) : RawChart.CHSt Hc := by
  obtain ⟨hh, χ, hχ, hUP⟩ := h
  exact CH_of_UP (fun g => RawChart.cart (Hc g)) p.n p.j p.j' p.big hr.big_compl hh
    (fun g i x => p.yOf g (χ g i) x) (fun g i x => p.yOf_int g (hχ g i) x) hUP
    (fun g i S t ht => charGermSelf_holds C V OE dd Y d I0 p Hc (χ g i) (hχ g i) g S t ht)

theorem isChar_one (Y : FBChart C V OE dd) : Y.IsChar (1 : PS C 1 dd) := by
  refine ⟨fun mu => ?_, map_one _, ?_⟩
  · rw [MvPowerSeries.coeff_one]
    split_ifs
    · exact VF.Ge.one
    · exact VF.Ge.zero 0
  · simp only [ev_one, mul_one]

theorem dlogC_one (i : Fin dd) : dlogC (1 : PS C 1 dd) i = 0 := by
  simp [dlogC, MvPowerSeries.coeff_one]

theorem lenCoker_smul {v : AddValuation C (WithTop ℝ)} {m h : ℕ} (B : Matrix (Fin m) (Fin h) C) {γ : C} (hγ : v γ = 0) :
    S4.lenCoker v (γ • B) = S4.lenCoker v B := by
  unfold S4.lenCoker
  congr 1
  funext g
  have e : (γ • B).submatrix id g = γ • B.submatrix id g := Matrix.ext fun i j => rfl
  rw [e, Matrix.det_smul, AddValuation.map_mul, AddValuation.map_pow, hγ, smul_zero, zero_add]

def rk0 {Y : FBChart C V OE dd} (p : SelfData Y d I0) (b : ZMod d) : ℕ :=
  (Finset.univ.filter fun c : I0 => p.ty0 c = b).card

def rkS {Y : FBChart C V OE dd} (p : SelfData Y d I0) (g : Fin 2) (b : ZMod d) : ℕ :=
  (Finset.univ.filter fun c : I0 => (Y.rawSelf p).ty g c = b).card

def a0Of {Y : FBChart C V OE dd} (p : SelfData Y d I0) (g : Fin 2) (a : ZMod d) : ZMod d := if g = 0 then a else a + p.hd

theorem ty_iff {Y : FBChart C V OE dd} (p : SelfData Y d I0) (g : Fin 2) (a : ZMod d) (c : I0) :
    (Y.rawSelf p).ty g c = a ↔ p.ty0 c = a0Of p g a := by
  show (if g = 0 then p.ty0 c else p.ty0 c + p.hd) = a ↔ p.ty0 c = (if g = 0 then a else a + p.hd)
  split_ifs with hg
  · exact Iff.rfl
  · constructor
    · intro h
      rw [← h, add_assoc, p.hd_two, add_zero]
    · intro h
      rw [h, add_assoc, p.hd_two, add_zero]

theorem rk_shift {Y : FBChart C V OE dd} (p : SelfData Y d I0) (g : Fin 2) (a k : ZMod d) :
    rk0 p (a0Of p g a + k + p.hd) = rkS p (1 - g) (a + k) := by
  have h : a0Of p g a + k + p.hd = a0Of p (1 - g) (a + k) := by
    have h2 := p.hd_two
    fin_cases g <;> simp [a0Of] <;> linear_combination h2
  unfold rk0 rkS
  simp only [ty_iff, h]

def AFBoundS (Y : FBChart C V OE dd) (p : SelfData Y d I0) (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C]
    (FR : Fin dd → PS R 2 dd) : Prop :=
  ∀ a0 : ZMod d, ∃ (s : ℕ) (e : Fin s ≃ {x : I0 // p.ty0 x = a0}) (W : Fin s → Fin dd → R) (xs : NNReal),
    (∀ c i, algebraMap R C (W c i) = p.e (e c) i) ∧ HasAF vm FR W xs ∧
      vm (V.l : C) ^ (S4.frobSum V.l (fun b => rk0 p (b + p.hd)) a0) ≤ xs

theorem exists_unit_col {Y : FBChart C V OE dd} (p : SelfData Y d I0) (a0 : ZMod d) (g : Fin 2) :
    ∃ col : Fin 2, V.v (p.gm a0 col g) = 0 := by
  by_contra hno
  push Not at hno
  have hpos : ∀ col, V.MM (p.gm a0 col g) := fun col =>
    lt_of_le_of_ne (SelfConjugateGermZero.gm_int Y p a0 col g) (Ne.symm (hno col))
  have h1 := p.gm_hyp a0 (1 - g) g
  have hne : (1 - g : Fin 2) ≠ g := by fin_cases g <;> decide
  rw [if_neg hne] at h1
  have h2 : V.MM (∑ r, p.gm (a0 + p.hd) r (1 - g) * p.gm a0 r g) := by
    rw [Fin.sum_univ_two]
    have t : ∀ r, V.MM (p.gm (a0 + p.hd) r (1 - g) * p.gm a0 r g) := fun r => by
      unfold VF.MM
      rw [V.v.map_mul]
      exact lt_of_lt_of_le (hpos r) (le_add_of_nonneg_left (SelfConjugateGermZero.gm_int Y p _ r _))
    exact lt_of_lt_of_le (lt_min (t 0) (t 1)) (V.v.map_add _ _)
  rw [h1] at h2
  unfold VF.MM at h2
  rw [V.v.map_one] at h2
  exact lt_irrefl _ h2

theorem upCharS_of_afBound (Y : FBChart C V OE dd) (p : SelfData Y d I0) (hr : (Y.rawSelf p).RankHyp)
    (Hc : ∀ g, (Y.rawSelf p).CartHyp V g) (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C]
    (hT : ValTie V vm) (hv : vm.Integers R) (h0 : 0 < (vm (V.l : C) : ℝ)) (h1 : (vm (V.l : C) : ℝ) < 1)
    (FR : Fin dd → PS R 2 dd) (hF : ∀ i, Y.B.G.F i = toC (FR i))
    (hF0 : ∀ i, MvPowerSeries.constantCoeff (FR i) = 0) (h : AFBoundS Y p vm R FR) : UPCharSelfSt Y p Hc := by
  have hR : ∀ x : R, V.Ge 0 (algebraMap R C x) := fun x => vA_nonneg hT hv h0 h1 x
  have hl1 : 1 < V.l := V.l_prime.one_lt
  have key : ∀ g a, ∃ (N : ℕ) (u : Fin N → Fin 2 → PS C 1 dd), (∀ k col, Y.IsChar (u k col)) ∧
      ∃ e : Fin (pT (fun g => RawChart.cart (Hc g)) g a) ≃ {x : I0 // (RawChart.cart (Hc g)).ty (Sum.inl x) = a},
        S4.lenCoker V.v (Matrix.of fun c k => p.yOf g (u k) (e c)) ≤
          ((S4.frobSum V.l (rkS p (1 - g)) a : ℝ) : WithTop ℝ) := by
    intro g a
    obtain ⟨s, e0, W, xs, hW, ⟨N, u, hu, hx⟩, hS⟩ := h (a0Of p g a)
    let e1 : Fin s ≃ {x : I0 // (Y.rawSelf p).ty g x = a} :=
      e0.trans (Equiv.subtypeEquivRight fun x => (ty_iff p g a x).symm)
    have he1 : ∀ c, ((e1 c : {x : I0 // (Y.rawSelf p).ty g x = a}) : I0) = e0 c := fun _ => rfl
    have hs : s = pT (fun g => RawChart.cart (Hc g)) g a := by
      have := Fintype.card_congr e1
      rw [Fintype.card_fin, Fintype.card_subtype] at this
      exact this
    subst hs
    obtain ⟨col0, hcol⟩ := exists_unit_col p (a0Of p g a) g
    refine ⟨N, fun k col => if col = col0 then toC (u k) else 1, fun k col => ?_, e1, ?_⟩
    · show Y.IsChar (if col = col0 then toC (u k) else 1)
      split_ifs
      · exact isChar_of_isCh Y hR FR hF hF0 (hu k)
      · exact isChar_one Y
    · have hb := lenCoker_le_of_hasLen hT hv h0 h1 W u hx hS
      have hsum : S4.frobSum V.l (fun b => rk0 p (b + p.hd)) (a0Of p g a) = S4.frobSum V.l (rkS p (1 - g)) a := by
        unfold S4.frobSum
        exact tsum_congr fun k => by beta_reduce; rw [rk_shift]
      rw [hsum] at hb
      have hm : (Matrix.of fun c k => p.yOf g (fun col => if col = col0 then toC (u k) else 1) (e1 c)) =
          p.gm (a0Of p g a) col0 g •
            (Matrix.of fun c k => ∑ i, dlogC (toC (C := C) (u k)) i * algebraMap R C (W c i)) := by
        ext c k
        simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
        unfold SelfData.yOf
        rw [Finset.sum_eq_single col0]
        · beta_reduce
          rw [if_pos rfl, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          show _ * (p.gm (p.ty0 (e1 c)) col0 g * p.e (e1 c) i) = _
          rw [he1, (e0 c).2, hW]
          ring
        · intro col _ hne
          beta_reduce
          rw [if_neg hne]
          exact Finset.sum_eq_zero fun i _ => by rw [dlogC_one, zero_mul]
        · intro hne
          exact absurd (Finset.mem_univ _) hne
      have hfin : S4.lenCoker V.v
          (Matrix.of fun c k => p.yOf g (fun col => if col = col0 then toC (u k) else 1) (e1 c)) ≤
          ((S4.frobSum V.l (rkS p (1 - g)) a : ℝ) : WithTop ℝ) := by
        rw [hm, lenCoker_smul _ hcol]
        exact hb
      exact hfin
  choose N u hu e he using key
  let eq : ∀ g, (Σ a : ZMod d, Fin (N g a)) ≃ Fin (Fintype.card (Σ a : ZMod d, Fin (N g a))) := fun g => Fintype.equivFin _
  refine ⟨fun g => Fintype.card (Σ a : ZMod d, Fin (N g a)),
    fun g i => u g ((eq g).symm i).1 ((eq g).symm i).2, fun g i col => hu g _ _ col, fun g a hb => ?_⟩
  have hle' : S4.lenCoker V.v (Matrix.of fun c i => p.yOf g (u g ((eq g).symm i).1 ((eq g).symm i).2) (e g a c)) ≤
      ((S4.frobSum V.l (rkS p (1 - g)) a : ℝ) : WithTop ℝ) := by
    refine le_trans (lenCoker_mono V.v _ (fun k : Fin (N g a) => eq g ⟨a, k⟩)) ?_
    have e3 : (Matrix.of fun c i => p.yOf g (u g ((eq g).symm i).1 ((eq g).symm i).2) (e g a c)).submatrix id
        (fun k : Fin (N g a) => eq g ⟨a, k⟩) = Matrix.of fun c k => p.yOf g (u g a k) (e g a c) := by
      ext c k
      simp only [Matrix.submatrix_apply, Matrix.of_apply, id]
      rw [Equiv.symm_apply_apply]
    rw [e3]
    exact he g a
  have hc1 : ∀ b, p.big g b → rkS p (1 - g) b = p.j' := fun b hb' =>
    hr.rk_small (1 - g) b (fun hh => (hr.big_compl g b).mp hh hb')
  have hc2 : ∀ b, ¬ p.big g b → rkS p (1 - g) b = p.n + p.j := fun b hb' =>
    hr.rk_big (1 - g) b ((hr.big_compl g b).mpr hb')
  refine ⟨e g a, fun hA => ?_, fun hB => ?_⟩
  · rw [← frobSum_conj_alt hl1 p.n p.j p.j' (p.big g) (alt_step p.big hr.big_compl hA g) (rkS p (1 - g)) hc1 hc2 a hb]
    exact hle'
  · rw [← frobSum_conj_all hl1 p.n p.j p.j' (rkS p (1 - g)) (fun b => hc1 b (hB b)) a]
    exact hle'

end UpFBr

end Formalism.L2.FormalSeriesBounds
end
end
