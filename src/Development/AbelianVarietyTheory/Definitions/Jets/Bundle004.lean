module

public import Formalism.HermitianCurvature.StatementTL
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IsMixedOver
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle013
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle005

@[expose] public section

section

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

noncomputable section

section alg

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

def hats {r : ℕ} (L : LevelData A r) : Set A :=
  Set.range L.Ahat ∪ Set.range L.R0 ∪ Set.range L.Ahatv ∪ Set.range L.R0v

def SameFns {r : ℕ} (L L' : LevelData A r) : Prop :=
  L.p = L'.p ∧ L.pb = L'.pb ∧ L.c = L'.c ∧ L.ci = L'.ci ∧ L.cb = L'.cb ∧ L.cbi = L'.cbi ∧ L.ζ = L'.ζ ∧ L.ζi = L'.ζi ∧
    L.ζb = L'.ζb ∧ L.ζbi = L'.ζbi ∧ L.GG = L'.GG ∧ L.GGi = L'.GGi ∧ L.TT = L'.TT

def MulRel {r : ℕ} (L : LevelData A r) (m : ℕ → A) : Prop :=
  ∀ q, (∀ f ∈ L.fns, Commute f (m q)) ∧ (∀ l, L.p l * m q = m q * L.p l + m (q + 1)) ∧
    (∀ l, L.pb l * m q = m q * L.pb l + m (q + 1)) ∧
    L.nab * m q = m q * L.nab + L.ζb * L.GGi * m (q + 1) ∧
    L.nabs * m q = m q * L.nabs - L.ζ * L.GGi * m (q + 1)

variable {P : M.Par}

def ssn (d : Q.NFData P A) (l : ℕ) : A := d.L.Drb * d.L.Dri * d.SS l

def bset (d : Q.NFData P A) : Set A :=
  {d.L.ζi, d.L.ζbi, d.L.D * d.L.Dbi, d.L.Db * d.L.Di} ∪ Set.range d.κ ∪
    ssn d '' Set.Icc 1 (P.k - 1) ∪ (fun l => star (ssn d l)) '' Set.Icc 1 (P.k - 1)

def bmon (d : Q.NFData P A) : Submonoid A := Submonoid.closure (bset d)

def HatHyp (d : Q.NFData P A) : Prop :=
  P.OK ∧ IsStarLevel d.L ∧ d.Rel ∧ (∀ l, star (d.L.p l) = -d.L.pb l) ∧ (∀ l, star (d.L.c l) = d.L.cb l) ∧
    (∀ l, star (d.L.ci l) = d.L.cbi l) ∧ ∀ f : M.Ty P → ℂ, ∀ g ∈ TL.siteOps d.L, Commute (d.κ f) g

def Comparison₂ (d : Q.NFData P A) (L : LevelData A P.r) (st : Start A) (s : ℂ) : Prop :=
  TL.AHyp L st ∧ SameFns L d.L ∧ (s = 1 ∨ s = -1) ∧ (∀ Y, st.QQ Y = s • d.QQ Y) ∧
    st.inv = {Y | ∀ ρ : M.Ty P, M.xC P ρ Y ≠ 0}

def nfSpan (d : Q.NFData P A) (T : Set A) (i j n : ℕ) : Submodule ℂ A :=
  Submodule.span ℂ {x | ∃ b ∈ bmon d, ∃ H : List A, H.length = n ∧ (∀ h ∈ H, h ∈ T) ∧
    x = b * d.L.Di ^ i * TL.gI d.L ^ j * H.prod}

def rh (d : Q.NFData P A) (y : ℂ) : A := d.L.Drb * (d.QQ y 1 0 * d.L.Ar y + d.QQ y 1 1 * d.L.Br y)

def rhv (d : Q.NFData P A) (y : ℂ) : A := d.L.Dr * (d.QQ y 0 1 * d.L.Avr y + d.QQ y 1 1 * d.L.Bvr y)

def basics (d : Q.NFData P A) : Set A :=
  {x | ∃ y : ℝ, (∀ ρ : M.Ty P, M.xC P ρ (y : ℂ) ≠ 0 ∧ M.xC P ρ ((y : ℂ) - 1) ≠ 0 ∧ M.xC P ρ ((y : ℂ) + 1) ≠ 0) ∧
    (x = d.L.Ahat y ∨ x = d.L.Ahatv y ∨ x = rh d y ∨ x = rhv d y)}

end alg

section actual

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

abbrev RA (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) : Type := Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')

def nv {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (x : (Fin P.r → ℂ) × Q.Mx P.k P.r) : ℝ :=
  ‖B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)‖

def IsNF {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (d : Q.NFData P (RA P Bs)) : Prop :=
  Q.IsActualLevel X d.L ∧ IsStarLevel d.L ∧ d.Rel ∧ ∀ Y : ℂ, X.QQ Y = d.QQ Y

def PtB (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (b : RA P Bs) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
    nv (b.1 Φ) x ≤ C * nv Φ x

def PtAdj (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (b : RA P Bs) : Prop :=
  ∀ Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
    B.hsInner ((b.1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) ((Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) =
      B.hsInner ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) (((star b).1 Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)

def gR (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (c : Fin P.r → ℂ) (g : Q.Mx P.k P.r) : ℝ :=
  Complex.normSq (∏ a, c a) * Q.GGl P.k P.r Bs.z Bs.z' g

def dR (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (c : Fin P.r → ℂ) (g : Q.Mx P.k P.r) : ℝ :=
  ‖(∏ a, c a) * P5.zeta P.k P.r Bs.z Bs.z' g‖

def IsMulG (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (φ : ℝ → ℝ)
    (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) : Prop :=
  ∀ q, P5.multiplicationOperator (W q) fun c g => ((LE.ld q φ (gR P Bs c g) : ℝ) : ℂ)

end actual

end

end GlobalTheory.HatNF
end

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.PullbackSections (endT IsNormEnd IsMixedOver)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PtTie

section Cast
variable {X Y : Scheme.{0}}

def isoCast {L L' : LB X} (h : L = L') {M : LB Y} (f : Y ⟶ X) (w : LB.Iso M (L.pull f)) : LB.Iso M (L'.pull f) := h ▸ w
end Cast

section End
variable {X : Scheme.{0}} (A : Over X) [GrpObj A] [IsCommMonObj A] (L : RigLB A)

abbrev endOver (T : Over X) (φ : A ⟶ A) : T ⊗ A ⟶ T ⊗ A := endT A T φ

def IsNormPull (φ : A ⟶ A) (a b : ℤ) {T : Over X} (s : LB.Sec (LPow A L.L b T)) (s' : LB.Sec (LPow A L.L a T)) : Prop :=
  ∃ (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b]))
    (α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd T A).left, (snd T A ≫ φ).left] ![a, -b])),
    α₀.IsGen ∧ IsNormEnd A L φ a b α₀ ∧
    LB.Gen.Corr L.L _ _ _ _ α (LB.pullGen L.L _ _ α₀ (snd T A).left) ∧
    IsTwistPull A L.L (endT A T φ) (snd T A ≫ φ) (lift_snd _ _) a b α s s'

def IsSymAct (N : ℕ) {T : Over X} (b : T ⟶ A) (s s' : LB.Sec (LPow A L.L (N : ℤ) T)) : Prop :=
  b ^ N = 1 ∧ ∃ U : ThetaGrp A L.L (N : ℤ) T, SymLift A L.L (N : ℤ) N b U ∧ IsActOf A L.L (N : ℤ) U s s'

def IsTransPull (φ : A ⟶ A) (N : ℕ) {T : Over X} (s : LB.Sec (LPow A L.L 1 T)) (b : T ⟶ A)
    (hh : LB.Sec (LPow A L.L (N : ℤ) T)) : Prop :=
  ∃ h₁ : LB.Sec (LPow A L.L (N : ℤ) T), IsNormPull A L φ (N : ℤ) 1 s h₁ ∧ IsSymAct A L N b h₁ hh

theorem IsSymAct.pow_eq_one {N : ℕ} {T : Over X} {b : T ⟶ A} {s s' : LB.Sec (LPow A L.L (N : ℤ) T)}
    (h : IsSymAct A L N b s s') : b ^ N = 1 := h.1

theorem IsTransPull.pow_eq_one {φ : A ⟶ A} {N : ℕ} {T : Over X} {s : LB.Sec (LPow A L.L 1 T)} {b : T ⟶ A}
    {hh : LB.Sec (LPow A L.L (N : ℤ) T)} (h : IsTransPull A L φ N s b hh) : b ^ N = 1 := h.choose_spec.2.1
end End

section Comparison₂
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {y : letI := io.toAlgebra; FrPt Xo c T.Fr}
  (I : IntData Xo c T io y) (P : PELUnif (maximalIdeal T.V) I.G)
  (F : Type) [Field F] [Algebra T.Fr F] (xF : Sp F ⟶ Xo.X)

def PtTieF (x : TFK (R := T.V) F ⟶ P.A.A) (b : ptO Xo xF ⟶ Xo.univ.t.G) : Prop :=
  ∃ r : Sp F ⟶ I.t'.G.left, r ≫ I.t'.G.hom = spMap (algebraMap T.Fr F) ∧ r ≫ I.m1.φ = b.left ∧
    r ≫ I.m2.φ = (x ≫ P.U.gen.inv).left ≫ pullback.fst I.G.G.hom (jK T.V)

def SecTieF (q : ℕ) (σ : P.U.toUnifPre.SecGF F q)
    (hh : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (q : ℤ) (ptO Xo xF))) : Prop :=
  xF = spMap (algebraMap T.Fr F) ≫ (letI := io.toAlgebra; y.x) ∧
  ∀ (Z : Scheme.{0}) (r : Z ⟶ I.t'.G.left) (zG : Z ⟶ (UnifPre.GF (R := T.V) (G := I.G.G) F).left)
    (zU : Z ⟶ (ptO Xo xF ⊗ Xo.univ.t.G).left),
    zG ≫ UnifPre.gFK (R := T.V) (G := I.G.G) F = r ≫ I.m2.φ →
    zU ≫ (snd (ptO Xo xF) Xo.univ.t.G).left = r ≫ I.m1.φ →
    zG ≫ (fst (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G)).left = zU ≫ (fst (ptO Xo xF) Xo.univ.t.G).left →
    zU ≫ (fst (ptO Xo xF) Xo.univ.t.G).left ≫ spMap (algebraMap T.Fr F) = r ≫ I.t'.G.hom →
    ∀ (z : Z) (J₁ : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι) (J₂ : (Z ⟶ I.G.G.left) → P.U.LG.L.ι) (j' : I.t'.PP.L.ι),
      Good Xo.univ.t.PP.L z J₁ → Good P.U.LG.L z J₂ → r z ∈ I.t'.PP.L.U j' →
      sval σ zG z J₂ * ((gv I.w1 r z (fun _ => J₁ (r ≫ I.m1.φ)) j').val) ^ q =
        sval hh zU z J₁ *
          ((gv (isoCast (congrArg RigLB.L P.bundle).symm I.m2.φ I.w2) r z (fun _ => J₂ (r ≫ I.m2.φ)) j').val) ^ q
variable {I P F xF}

theorem SecTieF.base {q : ℕ} {σ : P.U.toUnifPre.SecGF F q}
    {hh : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (q : ℤ) (ptO Xo xF))} (h : SecTieF I P F xF q σ hh) :
    xF = spMap (algebraMap T.Fr F) ≫ (letI := io.toAlgebra; y.x) := h.1

variable (I P)

end Comparison₂

section Num
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}

def nrm (Dw : Datum H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (α : 𝓞 E) : c.F :=
  ∏ τ : E →+* ℂ, embK c τ α ^ (∑ i : Fin (Dw.mult τ), a (τ, i))

def SplitsIn (E : Type) [Field E] [NumberField E] (g : ℕ) : Prop :=
  (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card = Module.finrank ℚ E ∧
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup

def ShortBasis {X : Type} [AddCommGroup X] (Q : X → ℤ) (r : ℕ) (Φ M0 : ℝ) : Prop :=
  0 ≤ Φ ∧ ∃ b : Module.Basis (Fin r) ℤ X, (∀ j, (Q (b j) : ℝ) ≤ Φ) ∧
    ∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z

end Num

section Run
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons IsDedekindDomain

def rr0 (D : D7) : ℝ :=
  (|(NumberField.discr D.host.E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ D.host.E)) / (2 * Module.finrank ℚ D.host.E)

def RunNum (D : D7) {j : ℕ} (w : WeightFamilies.Wt D j) (c : ℝ) : Prop :=
  w.LastPos ∧ 2 * D.R.f * D.R.r ≤ w.n ∧ (∀ i, 4 * WeightAlgebra.DF w + 4 ≤ D.host.g i) ∧ 0 ≤ c ∧
    (j < D.R.m → ∀ i, (WeightAlgebra.DF w : ℝ) * (2 * Real.sqrt (2 * D.R.f * D.R.m)) < (D.host.g i : ℝ) ∧
      rr0 D * ((2 * D.R.f * D.R.m : ℝ) ^ 4 * w.n + 2 * (2 * D.R.f * D.R.m : ℝ) ^ 3) * (WeightAlgebra.DF w : ℝ) ^ 2 / (D.host.g i : ℝ) ≤ c)

variable {D : D7}

def Oriented (T : Top D) (EX : ErrX D) : Prop := ∀ i, T.Q.l.Mb ≤ Ideal.span {piBarO EX i}

def nuWt (T : Top D) {j : ℕ} (w : WeightFamilies.Wt D j) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) : ℝ :=
  letI := T.Q.H.starRing
  (nuW (T.Q.Xo j) T.Q.c la T.Q.l.M (wtA w) w.n).toReal / (ramOverZ la : ℝ)

def sWt (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) {j : ℕ} (w : WeightFamilies.Wt D j) : 𝓞 B.KO :=
  nnW B hinj EX w * (pPow D (c2 D w) (cHalf w) (cHalf w) : 𝓞 B.KO)

end Run
end GlobalTheory.PtTie
end
end
