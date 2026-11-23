module

public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Bundle001
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.Bundle001
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle009

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def tauE {l : Level H} (c : Coeff l) (τ : E →+* ℂ) : E →+* c.F := (τ.codRestrict c.F.toSubfield (c.conj τ) :)

def IsLocBasis (O : Type) [CommRing O] {M : Type} [AddCommGroup M] [Module O M] (p : ℕ) {I : Type} (x : I → M) : Prop :=
  LinearIndependent O x ∧ ∃ n : ℕ, ¬ p ∣ n ∧ ∀ y, n • y ∈ Submodule.span O (Set.range x)

def gramE (D : Datum H) {I : Type} (x : I → D.La) : Matrix I I E := Matrix.of fun m n => sesq D (x m) (x n)

def IsTransition (D : Datum H) {I : Type} [Fintype I] (x e : I → D.La) (T : Matrix I I E) : Prop :=
  ∀ m y, sesq D (x m) y = ∑ n, T m n * sesq D (e n) y

def sgnRt (H : Host E) (b : Bool) : ℂ := if b then H.rt0 else -H.rt0

def IsPure {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) {p q : ℕ}
    (x : Fin p ⊕ Fin q → D.La) : Prop :=
  (∀ a, x (.inl a) ∈ PureType.lat hP (sgnRt H true)) ∧ ∀ j, x (.inr j) ∈ PureType.lat hP (sgnRt H false)

end GlobalTheory.CompanionTheory.Ar.Fl
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

open GroundTheory.Heights₂.Heights.LowerBoundFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {II : IntersectionSystem} {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
  [Algebra ℚ Ω] {W : CMType H → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]

structure CptOrigin (Y : Model Xo c β) (S₀ : Finset ℕ) (Dc : ComponentData II (CMType H) K J Ω W)
    (Hd : HodgeData Dc) where

  𝔐 : HodgeCpt Y S₀ Dc.y

  deg : ℕ
  cover : 𝔐.IsCover deg

  bg : CMType H → CMType H ⊕ CMType H

  sm : CMType H → CMType H ⊕ CMType H
  side : (bg = Sum.inl ∧ sm = Sum.inr ∧ Dc.j = D.p) ∨ (bg = Sum.inr ∧ sm = Sum.inl ∧ Dc.j = D.q)
  N_eq : Dc.N = D.p + D.q

  i : ∀ τ, W τ →ₗ[Ω] 𝔐.Li
  i_inj : ∀ τ, Function.Injective (i τ)
  i_range : ∀ τ, LinearMap.range (i τ) = 𝔐.Vgen (bg τ) ⊔ 𝔐.Vgen (sm τ)
  F_eq : ∀ τ, Hd.F τ = (𝔐.Vgen (bg τ)).comap (i τ)
  lat : ∀ τ, (Lat.comap (fun p => 𝔐.V (bg τ) p ⊔ 𝔐.V (sm τ) p) (i τ)).IsChartOf (segreCoord Dc.y) (Dc.W τ).lat
  bd : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ Dc.y z w → (w ∈ Dc.Bd ↔ ¬ 𝔐.Interior z)
  metric : ∀ τ a (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ Dc.y z w → 𝔐.Interior z →
    InFrameDomain Dc.y ((Dc.h τ).chart a) ((Dc.h τ).fr a) w →
      𝔐.M.GramAt 𝔐.t.PP.L z (fun k => i τ ((Dc.h τ).b a k)) ((Dc.h τ).gram a w)
  S_disj : Disjoint Dc.S S₀
  R_ge : ∀ p ∈ Dc.S, 4 ≤ 𝔐.R p
  tors : ∀ p ∈ Dc.S, FullTorsion 𝔐.t.G 𝔐.ξ (p ^ 𝔐.R p)
  ht_vb : ∀ p ∈ Dc.S, ∀ s, (𝔐.HT p s).IsVBOn {q | ∀ r : ℕ, r.Prime → r ≠ p → ¬ InFibre 𝔐.ξ r q} (labelRk D s)
    (𝔐.Vgen s)
  vert : ∀ p ∈ Dc.S, ∀ q : Cpt 𝔐.ξ, InFibre 𝔐.ξ p q → ∀ ch, InChart 𝔐.ξ (segreCoord Dc.y) ch q →
    ∀ (b b' : ∀ τ, Fin (labelRk D (sm τ)) → 𝔐.Li)
      (T : ∀ τ, Matrix (Fin (labelRk D (sm τ))) (Fin (labelRk D (sm τ))) Ω),
      (∀ τ, (𝔐.V (sm τ)).IsFrameAt (b τ) q) → (∀ τ, (𝔐.HT p (sm τ)).IsFrameAt (b' τ) q) →
      (∀ τ k, b' τ k = ∑ k', T τ k' k • b τ k') →
        unitAt 𝔐.ξ q ((∏ τ, (T τ).det) / (MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) *
          chartMono Dc.y ch (-Dc.vdeg p)))

section Ranks

variable {Y : Model Xo c β} {S₀ : Finset ℕ} {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc}
  (Or : CptOrigin Y S₀ Dc Hd)

theorem CptOrigin.rk_bg (τ : CMType H) : labelRk D (Or.bg τ) = Dc.j := by
  rcases Or.side with ⟨h, -, hj⟩ | ⟨h, -, hj⟩ <;> simp [h, hj]

theorem CptOrigin.rk_sm (τ : CMType H) : labelRk D (Or.sm τ) = Dc.N - Dc.j := by
  rcases Or.side with ⟨-, h, hj⟩ | ⟨-, h, hj⟩ <;> simp [h, hj, Or.N_eq]

theorem CptOrigin.bg_ne_sm (τ τ' : CMType H) : Or.bg τ ≠ Or.sm τ' := by
  rcases Or.side with ⟨h, h', -⟩ | ⟨h, h', -⟩ <;> simp [h, h']


include Or in
theorem CptOrigin.n_eq : Dc.n = Fintype.card (CMType H) * D.p * D.q := by
  rcases Or.side with ⟨-, -, hj⟩ | ⟨-, -, hj⟩ <;> simp [ComponentData.n, hj, Or.N_eq]
  ring

end Ranks

namespace Origin

section Period

variable {Ψ : Type} [Fintype Ψ] {V : Ψ → Type} [∀ τ, AddCommGroup (V τ)] [∀ τ, Module Ω (V τ)]
  {Dc : ComponentData II Ψ K J Ω V} {T T' : Set ((Σ k, J k) → ℂ)} {O' Lt : Type} [CommRing O'] [AddCommGroup Lt]
  [Module O' Lt]

end Period

section Plane

open Line GaussianInt

variable (II) (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

end Plane

end Origin

section Comparison₂

variable {Y : Model Xo c β} {S₀ : Finset ℕ} {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc}
  (Or : CptOrigin Y S₀ Dc Hd) {T T' : Set ((Σ k, J k) → ℂ)} {O' Lt : Type} [CommRing O'] [AddCommGroup Lt]
  [Module O' Lt]

variable {Or}

end Comparison₂

end GlobalTheory.CompanionTheory.Ar
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}

structure GermAt [StarRing (𝓞 E)] (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) where

  B : Germ.FB S d (𝓞 E)

  x : ∀ m, jOG x0 d m 1 ⟶ t.G

  e : ∀ m, FrTyG t x0 d x m

  tg : Fin d → (Sp (DualNumber S) ⟶ t.G.left)
  chart : IsChartG t x0 d B.G.F B.A.act tg (fun l j => if l = j then 1 else 0) x
  tan : ∀ l, IsTanAtG t x0 (tg l)
  basis : ∀ w, IsTanAtG t x0 w → ∃! a : Fin d → S, IsCombAtG t x0 tg a w
  frame : IsFrameG t x0 d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e
  trunc : FrTrunc t x0 d x e
  axes : FrAxes t x0 d x e

def PowFns (t : SAB H X0) : Prop := ∀ n, Function.Bijective (Out.powObj t.G n).hom.appTop.hom

def GeomPF (t : SAB H X0) {k : Type} [Field k] (x : Sp k ⟶ X0) : Prop :=
  ∃ (T : TorusExtension ((Over.pullback x).obj t.G)) (M : LB T.B.left),
    letI := T.grpB
    M.IsLB ∧ Out.KTriv T.B M ∧ LBIso (t.PP.L.pull (pullback.fst t.G.hom x)) (M.pull T.q.left)

def FibPF (t : SAB H X0) (z : X0) : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (x : Sp k ⟶ X0), x (IsLocalRing.closedPoint k) = z ∧ GeomPF t x

def toFirst (k : Type) [CommRing k] (m : ℕ) (hm : 1 ≤ m) : Jet k Unit m →ₐ[k] Jet k Unit 1 :=
  Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right (by omega))

def TanPF (t : SAB H X0) {k : Type} [Field k] (x : Sp k ⟶ X0) (p : ℕ) : Prop :=
  ∀ (hp : 1 ≤ p) (y : overAt x (Jet k Unit p) ⟶ t.G), homAt x (jetAug : Jet k Unit p →ₐ[k] k) ≫ y = 1 → y ^ p = 1 →
    (∃ c : LB.Gen (Out.translDiff t.G t.PP.L (homAt x (toFirst k p hp) ≫ y)), c.IsGen) →
      homAt x (toFirst k p hp) ≫ y = 1

end GlobalTheory.CompanionTheory.Ar.Conj
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ref

open NumberField IsDedekindDomain IsLocalRing Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def cjE (E : Type) [Field E] [NumberField E] [IsCMField E] (x : E) : E := IsCMField.complexConj E x

abbrev SymB {E : Type} [Field E] [NumberField E] (cj : E → E) (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] :
    Submodule ℝ (Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) :=
  Formalism.MainNotions.ModuliIntegralCharts.SymB cj Y

abbrev phiC {E : Type} [Field E] [NumberField E] (cj : E → E) {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]
    (b : SymB cj Y) : ℝ :=
  Formalism.MainNotions.ModuliIntegralCharts.phiC cj b

def IsPhiAt (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (t : ℝ) : Prop :=
  ∃ (e : ℕ) (_ : OverLa la T.V io e) (I : IntData Xo c T io y.1) (P : PELUnif (maximalIdeal T.V) I.G)
    (ϖ : T.V) (Q : P.D.toPre.X → ℤ) (β : SymB (cjE E) P.D.toPre.X),
    P.TorsionIso ∧ Irreducible ϖ ∧ QForm.IsQ P.D.toPre ϖ Q ∧
    (∀ a b, (β : P.D.toPre.X →ₗ[ℤ] P.D.toPre.X →ₗ[ℤ] ℝ) a b = QForm.bOf P.D.toPre Q a b) ∧
    (∀ a, (β : P.D.toPre.X →ₗ[ℤ] P.D.toPre.X →ₗ[ℤ] ℝ) a a = 2 * (Q a : ℝ)) ∧
    (∀ a, 0 ≤ (β : P.D.toPre.X →ₗ[ℤ] P.D.toPre.X →ₗ[ℤ] ℝ) a a) ∧
    phiC (cjE E) β = e * t

abbrev PtU (la : HeightOneSpectrum (𝓞 c.F)) : Type :=
  PtV Xo c (fun _ _ y => y.IsAlg) ℝ (IsPhiAt Xo c la) la

def pjSys : PtSys c.F (Rul Xo c) where
  Pt := PtU Xo c
  val y f := vAtV y f
  val_zero y := vAtV_zero y
  val_ne_bot y f := vAtV_ne_bot y f
  val_add y f g := vAtV_add y f g
  val_smul y a f ha := vAtV_smul y a f ha
  val_mul y f g := vAtV_mul y f g


variable {Xo c} in
def IsBC {T T' : CDVR} {io : c.F →+* T.Fr} (φ : T.Fr →+* T'.Fr) (y : IntFr Xo c T io)
    (z : IntFr Xo c T' (φ.comp io)) : Prop :=
  letI := io.toAlgebra
  letI := (φ.comp io).toAlgebra
  FrMap ({ φ with commutes' := fun _ => rfl } : T.Fr →ₐ[c.F] T'.Fr) y.1 z.1

def IsFinExt {T T' : CDVR} (φV : T.V →+* T'.V) (φ : T.Fr →+* T'.Fr) (r : ℕ) : Prop :=
  Function.Injective φV ∧ IsLocalHom φV ∧ φV.Finite ∧
    φ.comp (algebraMap T.V T.Fr) = (algebraMap T'.V T'.Fr).comp φV ∧
    0 < r ∧ ∀ x, vV T'.V (φ x) = (r : ℤ) * vV T.V x

def UnifAll : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e →
    ∀ y : IntFr Xo c T io, y.IsAlg →
      ∃ (T' : CDVR) (φV : T.V →+* T'.V) (φ : T.Fr →+* T'.Fr) (r : ℕ) (z : IntFr Xo c T' (φ.comp io)) (t : ℝ),
        IsFinExt φV φ r ∧ IsBC φ y z ∧ z.IsAlg ∧ IsPhiAt Xo c la T' (φ.comp io) z t

variable [StarRing (𝓞 E)]


section Basic

omit [StarRing (𝓞 E)]

theorem cjE_coe (H : Host E) (a : 𝓞 E) : cjE E (a : E) = (H.bar a : E) := (H.bar_eq a).symm


variable {c} in
theorem IsFinExt.overLa {T T' : CDVR} {φV : T.V →+* T'.V} {φ : T.Fr →+* T'.Fr} {r : ℕ} (h : IsFinExt φV φ r)
    {la : HeightOneSpectrum (𝓞 c.F)} {io : c.F →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e) :
    OverLa la T'.V (φ.comp io) (r * e) :=
  ho.bc φ h.2.2.2.2.1 h.2.2.2.2.2


theorem pjSys_val_mk (la : HeightOneSpectrum (𝓞 c.F)) {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ}
    (ho : OverLa la T.V io e) (y : IntFr Xo c T io) (hy : y.IsAlg) (t : ℝ) (ht : IsPhiAt Xo c la T io y t)
    (f : Rul Xo c) :
    (pjSys Xo c).val (show PtU Xo c la from PtV.mk la ho y hy t ht) f = nval T.V e (evI y f) := rfl

theorem phiC_nonneg {E : Type} [Field E] [NumberField E] (cj : E → E) {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]
    (b : SymB cj Y) (hb : ∀ a, 0 ≤ (b : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) : 0 ≤ phiC cj b := by
  refine Real.sInf_nonneg ?_
  rintro _ ⟨l, -, h, rfl⟩
  by_cases h0 : b = 0
  · simp [h0]
  · exact (h b hb h0).le


end Basic

end GlobalTheory.CompanionTheory.Ar.Ref
end
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.GaExp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieInh

def ev {A : Type} [CommRing A] {T : Scheme.{0}} (x : Sp A ⟶ T) : Γ(T, ⊤) →+* A :=
  (x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom

private theorem ev_eps_eq_ev {T : Scheme.{0}} (x : Sp (DualNumber ℂ) ⟶ T) (h) (f : Γ(T, ⊤)) :
    GlobalTheory.FibreDeriv.evEps x ⊤ h f = ev x f := by
  have hx : x.appLE ⊤ ⊤ h = x.app ⊤ := by
    rw [Scheme.Hom.app_eq_appLE]
    rfl
  simp only [GlobalTheory.FibreDeriv.evEps, ev, hx]

theorem valAt'_top {T : Scheme.{0}} (x : Sp ℂ ⟶ T) (f : Γ(T, ⊤)) : valAt' x ⊤ f = ev x f := by
  have hx : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x) = x := by
    have e : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ := by
      ext z
      simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    simp
  have h1 := GlobalTheory.FibreDeriv.fst_evEps (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x) x hx ⊤ le_rfl f
  rw [← h1, ev_eps_eq_ev]
  have key : (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom =
      (x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) ≫ CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) := by
    rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality, Category.assoc]
  have h2 := congrArg (fun g => (g.hom f).fst) key
  simpa [ev, TrivSqZeroExt.algebraMap_eq_inl] using h2

variable {R : Type} [CommRing R]

variable {G : Over (Sp R)} [GrpObj G] {g n : ℕ} {M : LieModel G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)}
  {ψ : (Fin n → ℂ) → (R →+* ℂ)}

end GlobalTheory.CompanionTheory.Ar.Flat.GaExp
end
end
