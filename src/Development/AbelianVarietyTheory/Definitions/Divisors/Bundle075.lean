module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle073
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.FinitePosDefFormSublevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2654
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2939
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

section

noncomputable section

open IsLocalRing GlobalTheory.PolFan GlobalTheory.LocM

namespace GlobalTheory.Poinc.PreModel

section
variable {O : Type} [CommRing O] {bar : O → O} {q s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ} {A : Type} [CommRing A] [IsLocalRing A]
  (Φ : VPre bar q W A)

theorem low_finite (y : Φ.Y) (P : (Fin s → Φ.X y) → Prop) (j : ℕ) :
    {mu | P mu ∧ ∑ i, qW W (Φ.δ y i) mu < (j : ℤ)}.Finite := by
  obtain ⟨c₀, hc₀, hq⟩ := GlobalTheory.Poinc.QWDom.qW_ge s W Φ.posW
  let D : LinearMap.BilinForm ℤ (Φ.X y) := ∑ i, Φ.δ y i
  have hD : ∀ x, D x x = ∑ i, Φ.δ y i x x := fun x => by simp [D, LinearMap.sum_apply]
  have hDs : ∀ a b, D a b = D b a := fun a b => by
    simp only [D, LinearMap.sum_apply]; exact Finset.sum_congr rfl fun i _ => (Φ.bal y i).1 a b
  have hDp : ∀ x, x ≠ 0 → 0 < D x x := fun x hx => by
    rw [hD]
    obtain ⟨i, hi⟩ := Φ.pos y x hx
    exact lt_of_lt_of_le hi (Finset.single_le_sum (f := fun i => Φ.δ y i x x) (fun i _ => Φ.nonneg y i x) (Finset.mem_univ i))
  refine (Set.Finite.pi' fun _ : Fin s => GlobalTheory.CompanionTheory.Ar.Fan.sublevel_finite _ D hDs hDp ⌈(j : ℝ) / c₀⌉).subset ?_
  rintro mu ⟨-, hmu⟩ u
  have h1 : ∀ i, c₀ * ((∑ u, Φ.δ y i (mu u) (mu u) : ℤ) : ℝ) ≤ (qW W (Φ.δ y i) mu : ℝ) := fun i =>
    hq _ (Φ.δ y i) (Φ.bal y i).1 (Φ.nonneg y i) mu
  have h2 : c₀ * ((∑ u, D (mu u) (mu u) : ℤ) : ℝ) ≤ ((∑ i, qW W (Φ.δ y i) mu : ℤ) : ℝ) := by
    have : ((∑ u, D (mu u) (mu u) : ℤ) : ℝ) = ∑ i, ((∑ u, Φ.δ y i (mu u) (mu u) : ℤ) : ℝ) := by
      simp only [hD]; push_cast; exact Finset.sum_comm
    rw [this, Finset.mul_sum]; push_cast
    exact Finset.sum_le_sum fun i _ => by exact_mod_cast h1 i
  have h3 : (D (mu u) (mu u) : ℝ) ≤ ((∑ u, D (mu u) (mu u) : ℤ) : ℝ) := by
    exact_mod_cast Finset.single_le_sum (f := fun u => D (mu u) (mu u)) (fun u _ => by
      by_cases h : mu u = 0
      · simp [h]
      · exact (hDp _ h).le) (Finset.mem_univ u)
  have h4 : ((∑ i, qW W (Φ.δ y i) mu : ℤ) : ℝ) < j := by exact_mod_cast hmu
  have h5 : (D (mu u) (mu u) : ℝ) ≤ (j : ℝ) / c₀ := by
    rw [le_div_iff₀' hc₀]; nlinarith
  show D (mu u) (mu u) ≤ ⌈(j : ℝ) / c₀⌉
  exact_mod_cast h5.trans (Int.le_ceil _)

end

end GlobalTheory.Poinc.PreModel
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

variable {R : Type} [CommRing R] [IsDomain R]

def fnF (F : Type) [Field F] [Algebra (FractionRing R) F] (c : F) : Γ((TFK (R := R) F).left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c

structure Eqv (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ)
    (lab : QkPt D F N → (TFK (R := R) F ⟶ A.A)) (E : Fam D F N → SecK A.L (snd (TFK (R := R) F) A.A).left N) : Prop where
  bij : Function.Bijective E
  add : ∀ s s' s'' : Fam D F N, (∀ α j, (s''.s α).f j = (s.s α).f j + (s'.s α).f j) →
    ∀ j, (E s'').f j = (E s).f j + (E s').f j
  smul : ∀ (c : F) (s s' : Fam D F N), Fam.IsSmul D F c s s' → ∀ j, (E s').f j = liftFun A.A _ (fnF F c) * (E s).f j
  onto : ∀ x : TFK (R := R) F ⟶ A.A, x ^ N = 1 ↔ ∃ p, lab p = x
  frame : ∀ p : QkPt D F N, ∃ w, GlobalTheory.UT.TXFrame N p w
  lift : ∀ p, ∃ θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F), SymLift A.A A.L N N (lab p) θ
  act : ∀ (p : QkPt D F N) w (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)) (s s' : Fam D F N), GlobalTheory.UT.TXFrame N p w →
    SymLift A.A A.L N N (lab p) θ → PhiRel D F N p w s s' → IsActOf A.A A.L N θ (E s) (E s')

def LabExt {D : DegPre R} {A : PolAV (Sp (FractionRing R))} {F : Type} [Field F] [Algebra (FractionRing R) F] {N : ℕ}
    (em : Kb R →ₐ[FractionRing R] F) (lab : QkPt D (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A))
    (lab' : QkPt D F N → (TFK (R := R) F ⟶ A.A)) : Prop :=
  ∀ p p', QkExt em.toRingHom p p' → (lab' p').left = spMap em.toRingHom ≫ (lab p).left

def IntFam.Over {I : Ideal R} {D : DegPre R} {k : ℕ} (F₀ : IntFam I D k) {F : Type} [Field F] [Algebra (FractionRing R) F]
    (s : Fam D F k) : Prop :=
  ∀ α : D.X, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) (s.s α) (D.famφB α) (DegPre.famε k) (F₀.f α)
    (DegPre.prB D F).left 1

end GlobalTheory.Mum
end
end

section

noncomputable section
open IsLocalRing

namespace GlobalTheory.TChart

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {φ : GlobalTheory.LocM.InvFun ℤ}

theorem Taut.s_ne_zero (C : Taut ζ g n φ) (k : Fin C.m ⊕ Fin C.N) : C.s k ≠ 0 := by
  intro h
  have hflat : C.ψ.Flat := C.compl.2.2.1
  algebraize [C.ψ]

  have hreg : IsSMulRegular C.R
      (algebraMap (MvPolynomial (Fin C.m ⊕ Fin C.N) C.W) C.R (MvPolynomial.X k)) :=
    IsSMulRegular.of_flat (MvPolynomial.isRegular_X (n := k) (R := C.W)).left.isSMulRegular
  have h0 : algebraMap (MvPolynomial (Fin C.m ⊕ Fin C.N) C.W) C.R (MvPolynomial.X k) = 0 := h
  rw [h0] at hreg
  exact one_ne_zero (hreg (a₁ := (1 : C.R)) (a₂ := 0) (by simp))

end GlobalTheory.TChart
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}

def cpt {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) (a : Q.X) : Sp V ⟶ Q.P.A.left := (Q.c a).left

def FromBase {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) (τ₀ : Gens Q) {W₀ : Type} [CommRing W₀] (ιb : W₀ →+* V) :
    Prop :=
  ∃ (B₀ : Over (Sp W₀)) (_ : GrpObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (Sp W₀ ⟶ B₀.left))
    (τ₁ : ∀ a b : Q.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
    (β : Q.P.A.left ⟶ B₀.left) (w : LB.Iso Q.P.L (M₀.pull β)),
    IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback Q.P.A B₀ (spMap ιb) β ∧ w.IsGen ∧
    (∀ a, cpt Q a ≫ β = spMap ιb ≫ c₀ a) ∧ (∀ a b, (τ₁ a b).IsGen) ∧
    ∀ (a b : Q.X) zz (J : (Sp V ⟶ Q.P.A.left) → Q.P.L.ι) (J₀ : (Sp V ⟶ B₀.left) → M₀.ι),
      Good Q.P.L zz J → Good M₀ zz J₀ →
      val (τ₀ a b) (𝟙 (Sp V)) zz J =
        gm (cpt Q (a + b)) zz _ (w.s (fun _ => J₀ (cpt Q (a + b) ≫ β), J (cpt Q (a + b)))) *
        (gm (cpt Q a) zz _ (w.s (fun _ => J₀ (cpt Q a ≫ β), J (cpt Q a))))⁻¹ *
        (gm (cpt Q b) zz _ (w.s (fun _ => J₀ (cpt Q b ≫ β), J (cpt Q b))))⁻¹ *
        gm (cpt Q 0) zz _ (w.s (fun _ => J₀ (cpt Q 0 ≫ β), J (cpt Q 0))) *
        val (τ₁ a b) (spMap ιb) zz J₀

def SepAtB {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) (τ₀ : Gens Q) {m N : ℕ} (s : Fin m ⊕ Fin N → V) {K : Type}
    [Field K] (ev : V →+* K) (k₀ : Subfield K) : Prop :=
  (∀ i, ev (s (.inl i)) = 0) ∧
  (∃ (B₀ : Over (Sp k₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (Sp k₀ ⟶ B₀.left))
    (B' : Over (Sp K)) (_ : GrpObj B') (π₁ : B'.left ⟶ Q.P.A.left) (π₀ : B'.left ⟶ B₀.left)
    (w : LB.Iso (Q.P.L.pull π₁) (M₀.pull π₀)) (c' : Q.X → (Sp K ⟶ B'.left)),
    IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback B' Q.P.A (spMap ev) π₁ ∧ IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ ∧
    w.IsGen ∧ ∀ a, c' a ≫ B'.hom = 𝟙 _ ∧ c' a ≫ π₁ = spMap ev ≫ (Q.c a).left ∧ c' a ≫ π₀ = spMap k₀.subtype ≫ c₀ a) ∧
  ∀ (W₀ : Type) [CommRing W₀] (ιb : W₀ →+* V), FromBase Q τ₀ ιb → (∀ a, ev (ιb a) ∈ k₀) → ∀ i, ev (s (.inr i)) ∈ k₀

def SepB (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) {S : Scheme.{0}} (j : Xo.XF c ⟶ S) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (C : MonoFam Xo c φ V), GlobalTheory.Mum.Base V →
    ∀ ξ : Sp V ⟶ S, C.y ≫ j = jK V ≫ ξ →
    ∀ (N : ℕ) (s : Fin C.m ⊕ Fin N → V) (ε : Module.Basis (Fin C.m ⊕ Fin N) ℤ (balForms H.bar C.P.D.toPre.X))
      (τ₀ : Gens C.P.D.toPre), (∀ i, s (.inl i) = C.s i) → (∀ i, (ε (.inl i) : LinearMap.BilinForm ℤ _) = C.δ i) →
      (∀ k, IsUnit (s (.inr k))) →
      TauIn C.P.D.toPre τ₀ (fun k => s (finSumFinEquiv.symm k))
        (fun k => (l.M' : ℤ) • (ε (finSumFinEquiv.symm k) : LinearMap.BilinForm ℤ C.P.D.toPre.X)) →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
      (∀ p, (spMap ev ≫ ξ) p = ξ (closedPoint V)) → DefOver k₀ (spMap ev ≫ ξ) →
      SepAtB C.P.D.toPre τ₀ s ev k₀

def UStB : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
    ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ →
      ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l),
        ∃ (Z : Scheme.{0}) (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData)
          (S : Scheme.{0}) (π : S ⟶ Z) (j : Xo.XF c ⟶ S) (BD : GlobalTheory.EffCartierData S),
          GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD ∧ SepB Xo c φ j

end GlobalTheory.UChart
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {cf : Coeff l} {C : UCompact Xo cf}

structure UWit (X : USetup C) where

  G : Over (Sp X.Ω₁)
  [grp : GrpObj G]

  α : G.left ⟶ X.ρ.P.A.left

  β : G.left ⟶ Xo.univ.t.G.left
  hα : IsGrpPullback G X.ρ.P.A (spMap X.S.R.val.toRingHom) α
  hβ : IsGrpPullback G Xo.univ.t.G (X.uΩ ≫ pullback.fst _ _) β
  hL : LBIso (X.ρ.P.L.pull α) (Xo.univ.t.PP.L.pull β)

attribute [instance] UWit.grp

theorem nonempty_uWit (X : USetup C) : Nonempty (UWit X) := by
  obtain ⟨G, _, α, β, hα, hβ, hL⟩ := X.pulled_uΩ
  exact ⟨{ G := G, α := α, β := β, hα := hα, hβ := hβ, hL := hL }⟩

def UIsLabW (X : USetup C) (wi : UWit X) {p : ℕ} [Fact p.Prime] {z : X.M.Z} (ct : UCTrait X p z)
    (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X) : Prop :=
  ∃ (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b)
    (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R')
    (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real) (u' : Sp (ratHull R') ⟶ Xo.XF cf),
    USame X.ρ ρ' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧ spMap (ratHull R').val.toRingHom ≫ u' = X.uΩ ∧
    R' ≤ X.M.O ((gPt p ≫ ct.y) (closedPoint (PadicAlgCl p))) ∧
    ∃ (G : Over (Sp (ratHull R'))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left),
      IsGrpPullback G ρ'.P.A (spMap (toRat R')) α ∧ IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧
      LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧
      (∃ m : wi.G.left ⟶ G.left, IsGrpPullback wi.G G (spMap (ratHull R').val.toRingHom) m ∧ m ≫ β = wi.β ∧
        ∀ x, ∃ w : Sp X.Ω₁ ⟶ wi.G.left, w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧
          w ≫ m ≫ α = spMap R'.val.toRingHom ≫ (ρ'.pt x).left) ∧
      ∃ y₀ : R' →+* PadicAlgCl p, (∀ a : R', y₀ a = X.M.val (gPt p ≫ ct.y) a) ∧
        ∃ (u : ρ'.UTest p y₀) (lb : u.Lab) (j : u.D.toPre.X ≃+ ct.T.P.D.toPre.X),
          (∀ χ, lb.q χ = ct.sc * (ct.T.be (j χ) (j χ) : ℝ) / 2) ∧
          (∀ a χ, lb.yy a = QuotientAddGroup.mk χ → yy a = QuotientAddGroup.mk (j χ)) ∧
          ∀ (m : ℕ) (a : 𝓞 E) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)
            (w w' : Sp (PadicAlgCl p) ⟶ G.left), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x →
            QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → w ≫ α = x.left ≫ u.φ → w' ≫ α = x'.left ≫ u.φ →
            w' ≫ β = w ≫ β ≫ (Xo.univ.t.act.act a).left → CongMod m (j pk'.y) (a • j pk.y)

theorem UIsLabW.uIsLab {X : USetup C} {wi : UWit X} {p : ℕ} [Fact p.Prime] {z : X.M.Z} {ct : UCTrait X p z}
    {yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X} (h : UIsLabW X wi ct yy) : UIsLab X ct yy := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', u', h₁, h₂, h₃, h₄, G, _, α, β, h₅, h₆, h₇, -, h₈⟩ := h
  exact ⟨c₀, hc, R', fg, frac, hth, hev, ρ', u', h₁, h₂, h₃, h₄, G, _, α, β, h₅, h₆, h₇, h₈⟩

def UDeep.Comparison₂ {X₁ : USetup C} (Dp : UDeep X₁) (w₁ : UWit X₁) (w₂ : UWit Dp.X) : Prop :=
  ∃ m : w₂.G.left ⟶ w₁.G.left, IsGrpPullback w₂.G w₁.G (spMap (algebraMap X₁.Ω₁ Dp.X.Ω₁)) m ∧ m ≫ w₁.β = w₂.β ∧
    ∀ x, ∃ w : Sp Dp.X.Ω₁ ⟶ w₂.G.left,
      w ≫ m ≫ w₁.α = spMap (algebraMap X₁.Ω₁ Dp.X.Ω₁) ≫ spMap X₁.S.R.val.toRingHom ≫ (X₁.ρ.pt x).left ∧
      w ≫ w₂.α = spMap Dp.X.S.R.val.toRingHom ≫ (Dp.X.ρ.pt (Dp.lab x)).left

end GlobalTheory.UPoinc
end
end
