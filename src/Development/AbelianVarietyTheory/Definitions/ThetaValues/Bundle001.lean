module

public import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GalTw

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

structure Fixes (c : Coeff l) (ta : c.F ≃+* c.F) : Prop where
  emb : ∀ (τ : E →+* ℂ) (a : E), ta (embF c τ a) = embF c τ a
  base : ∀ a : KA l, ta (IntermediateField.inclusion c.le a) = IntermediateField.inclusion c.le a

def Tw {K : Type} [Field K] (_ta : K ≃+* K) (S : Type) : Type := S

instance {K : Type} [Field K] (ta : K ≃+* K) (S : Type) [h : CommRing S] : CommRing (Tw ta S) := h

instance {K : Type} [Field K] (ta : K ≃+* K) (S : Type) [CommRing S] [Algebra K S] : Algebra K (Tw ta S) :=
  RingHom.toAlgebra (R := K) (S := S) ((algebraMap K S).comp ta.toRingHom)

def Tw.val {K : Type} [Field K] {ta : K ≃+* K} {S : Type} (s : Tw ta S) : S := s

theorem sOf_tw {ta : c.F ≃+* c.F} (h : Fixes c ta) (S : Type) [CommRing S] [Algebra c.F S] :
    sOf c (Tw ta S) = sOf c S := by
  unfold sOf
  congr 1
  ext a
  exact congrArg (algebraMap c.F S) (h.base a)

theorem isEigAt_tw {ta : c.F ≃+* c.F} (h : Fixes c ta) {S : Type} [CommRing S] [Algebra c.F S] (τ : E →+* ℂ)
    (v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) :
    IsEigAt (Xo := Xo) c (S := Tw ta S) τ v ↔ IsEigAt (Xo := Xo) c (S := S) τ v := by
  have e : ∀ a : 𝓞 E, algebraMap c.F (Tw ta S) (embK c τ a) = algebraMap c.F S (embK c τ a) :=
    fun a => congrArg (algebraMap c.F S) (h.emb τ a)
  unfold IsEigAt
  refine forall_congr' fun a => ?_
  rw [e a]
  rfl

def twPt {ta : c.F ≃+* c.F} (h : Fixes c ta) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    FrPt Xo c (Tw ta S) where
  x := y.x
  x_over := y.x_over.trans (sOf_tw h S).symm
  u := y.u
  tan := y.tan
  eig τ i := (isEigAt_tw (S := S) h τ _).2 (y.eig τ i)
  basis τ w ht he := y.basis τ w ht ((isEigAt_tw (S := S) h τ w).1 he)
  s := y.s
  gen := y.gen

def galRul {ta : c.F ≃+* c.F} (h : Fixes c ta) (f : Rul Xo c) : Rul Xo c :=
  fun p y => (evR Xo c f (twPt h y)).val

def covAut {n : ℕ} (d : DeltaDat Xo c n) (ta : c.F ≃+* c.F) : d.c₂.F ≃+* d.c₂.F :=
  (d.eF.symm.toRingEquiv.trans ta).trans d.eF.toRingEquiv

theorem Tw.val_algebraMap {K : Type} [Field K] (ta : K ≃+* K) (S : Type) [CommRing S] [Algebra K S] (a : K) :
    (algebraMap K (Tw ta S) a).val = algebraMap K S (ta a) := rfl

theorem fixes_of_le {c c' : Coeff l} (ta : c'.F ≃+* c'.F)
    (h : ∀ x : c'.F, (x : ℂ) ∈ c.F → ta x = x) : Fixes c' ta :=
  ⟨fun τ a => h _ (c.conj τ a), fun a => h _ (c.le a.2)⟩

theorem galRul_smul {ta : c.F ≃+* c.F} (h : Fixes c ta) (a : c.F) (f : Rul Xo c) :
    galRul h (a • f) = ta a • galRul h f := by
  funext p y
  show (evR Xo c (a • f) (twPt h y)).val = ta a • (evR Xo c f (twPt h y)).val
  unfold evR
  rw [evalAt_smul, Algebra.smul_def]
  rfl

theorem covAut_apply_eF {n : ℕ} (d : DeltaDat Xo c n) (ta : c.F ≃+* c.F) (a : c.F) :
    covAut d ta (d.eF a) = d.eF (ta a) := by
  show d.eF (ta (d.eF.symm (d.eF a))) = _
  rw [AlgEquiv.symm_apply_apply]

theorem fixes_covAut {n : ℕ} (d : DeltaDat Xo c n) (hA : d.l₂.A = 1) {ta : c.F ≃+* c.F} (h : Fixes c ta) :
    Fixes d.c₂ (covAut d ta) := by
  have key : ∀ (x : d.c₂.F), ta (d.eF.symm x) = d.eF.symm x → covAut d ta x = x := fun x hx => by
    show d.eF (ta (d.eF.symm x)) = x
    rw [hx, AlgEquiv.apply_symm_apply]
  refine ⟨fun τ a => key _ (h.emb τ a), fun a => key _ ?_⟩
  have hle : KA d.l₂ ≤ KA l := by
    unfold KA
    rw [IntermediateField.adjoin_le_iff]
    rintro x (rfl | rfl)
    · exact IntermediateField.subset_adjoin _ _ (by simp)
    · have : zeta d.l₂.A = 1 := by rw [hA]; simp [zeta]
      rw [this]; exact one_mem _
  exact h.base ⟨a, hle a.2⟩

end GlobalTheory.GalTw
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaForm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

abbrev LatMod (Dw : Datum H) (k : ℕ) : Type :=
  Dw.La ⧸ (Ideal.span {(k : 𝓞 E)} • ⊤ : Submodule (𝓞 E) Dw.La)

abbrev LevGrp (Dw : Datum H) (k : ℕ) : Type := LatMod Dw k ≃ₗ[𝓞 E] LatMod Dw k

variable (Xo : Moduli Dw l) (c : Coeff l)

def IsFullLev (k : ℕ) {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X)
    (ev : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)) : Prop :=
  (∀ a b, ev (a + b) = ev a * ev b) ∧ (∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ Xo.univ.t.act.act o) ∧
    ∀ (K : Type) [Field K] (χ : S →+* K) (a b : LatMod Dw k),
      spMap χ ≫ (ev a).left = spMap χ ≫ (ev b).left → a = b

def IsNullVal (N : ℕ) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (p : ptO Xo y.x ⟶ Xo.univ.t.G) (w : S) : Prop :=
  ∃ F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x)),
    IsVtOver Xo.univ.t.G Xo.univ.t.PP N (fun t => t = p) y.s (p ^ N) F ∧
    IsValueAt Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) F 1
      (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (ptO Xo y.x) ((N : ℤ) ^ 2)) (toΓ S w)

def etaExpr {S : Type} [CommRing S] (k : ℕ) {J : Type} [Fintype J] {n : ℕ} (cf : J → ℤ)
    (x : J → Fin n → LatMod Dw k) (w : LatMod Dw k → S) : S :=
  ∏ᶠ g : LevGrp Dw k, ∑ j, (cf j : S) * ∏ b, w (g (x j b))

def EtaValAt (R : ℕ) {J : Type} [Fintype J] {n : ℕ} (cf : J → ℤ) (x : J → Fin n → LatMod Dw (R ^ 4))
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) : Prop :=
  ∃ (S' : Type) (_ : CommRing S') (_ : Algebra c.F S') (φ : S →ₐ[c.F] S') (y' : FrPt Xo c S')
    (ev : LatMod Dw (R ^ 4) → (ptO Xo y'.x ⟶ Xo.univ.t.G)) (w : LatMod Dw (R ^ 4) → S'),
    φ.toRingHom.FaithfullyFlat ∧ FrMap φ y y' ∧ IsFullLev Xo (R ^ 4) y'.x ev ∧
    (∀ q, IsNullVal Xo c (R ^ 2) y' (ev q) (w q)) ∧ φ v = etaExpr (R ^ 4) cf x w

def IsEtaRule (R : ℕ) {J : Type} [Fintype J] {n : ℕ} (cf : J → ℤ) (x : J → Fin n → LatMod Dw (R ^ 4))
    (f : Rul Xo c) : Prop :=
  ∀ (p : TRing c.F) (y : FrPt Xo c p.R), EtaValAt Xo c R cf x y (f p y)

def shiftFam (R : ℕ) {n : ℕ} (x₀ : Fin n → Dw.La) (y : Fin n → LatMod Dw R) : Fin n → LatMod Dw (R ^ 4) :=
  fun b => Submodule.Quotient.mk (x₀ b + R • qRep (y b))

end GlobalTheory.EtaForm
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BlockTh

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

structure Bk (Dw : Datum H) (n : ℕ) where
  τ : E →+* ℂ
  i : ℕ
  hi : i ≤ Dw.mult τ
  c : ℕ
  hc : 1 ≤ c
  col : Fin i → Fin n
  col_inj : Function.Injective col

variable {Dw : Datum H} {n : ℕ}

def Bk.poly (K : Type) [CommRing K] (B : Bk Dw n) : MvPolynomial (LtN Dw n) K :=
  (Matrix.of fun a b : Fin B.i => MvPolynomial.X (⟨B.τ, Fin.castLE B.hi a, B.col b⟩ : LtN Dw n)).det ^ B.c

def IsBlockProd {K : Type} [CommRing K] (P : MvPolynomial (LtN Dw n) K) : Prop :=
  ∃ (nb : ℕ) (bs : Fin nb → Bk Dw n), (∀ j j', j ≠ j' → ∀ a a', (bs j).col a ≠ (bs j').col a') ∧
    P = ∏ j, (bs j).poly K

variable {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

def ContainsTh (nab : NabV Xo c) (s : c.F) (P : MvPolynomial (LtN Dw n) c.F) {J : Type} (w : J → Rul Xo c) : Prop :=
  ∃ jb : (Fin n → LevQ Dw l) → J, Function.Injective jb ∧
    ∀ q, ∃ f : Rul Xo c, IsThRule Xo c nab (fun b => levRep (q b)) P f ∧ ∀ (p : TRing c.F) (y : FrPt Xo c p.R), w (jb q) p y = algebraMap c.F p.R s * f p y


variable (E) in
def p14 (r n m : ℕ) : ℝ :=
  (Real.log Real.pi + n * (Real.log 24 + (I2.dstar (E := E) m : ℝ) / 2 * Real.log (2 * (I2.dstar (E := E) m : ℝ))) +
    (r + 2) * Real.log 2) / 2

end GlobalTheory.BlockTh
end
end
