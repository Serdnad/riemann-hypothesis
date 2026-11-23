module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
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
import Mathlib.RingTheory.DualNumber
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
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
noncomputable section
namespace GlobalTheory.KS

def IsDer {R : Type} [CommRing R] (x₀ : R →+* ℂ) (D : R → ℂ) : Prop :=
  (∀ a b, D (a + b) = D a + D b) ∧ ∀ a b, D (a * b) = x₀ a * D b + x₀ b * D a

structure PtDer {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (δ : ∀ W : X.Opens, Γ(X, W) → ℂ) : Prop where
  add : ∀ W, ⊤ ≤ y ⁻¹ᵁ W → ∀ f f', δ W (f + f') = δ W f + δ W f'
  mul : ∀ W, ⊤ ≤ y ⁻¹ᵁ W → ∀ f f', δ W (f * f') = valAt' y W f * δ W f' + valAt' y W f' * δ W f
  res : ∀ W W' (h : W' ≤ W), ⊤ ≤ y ⁻¹ᵁ W' → ∀ f, δ W' (resG X h f) = δ W f

structure LocDer {R : Type} [CommRing R] {Y X : Scheme.{0}} (q : Y ⟶ Sp ℂ) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → ℂ)
    (W₀ : X.Opens) (d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)) : Prop where
  add : ∀ W, W ≤ W₀ → ∀ f f', d W (f + f') = d W f + d W f'
  mul : ∀ W, W ≤ W₀ → ∀ f f', d W (f * f') = (m.app W).hom f * d W f' + (m.app W).hom f' * d W f
  res : ∀ W W' (h : W' ≤ W), W ≤ W₀ → ∀ f, d W' (resG X h f) = resG Y (fun _ hy => h hy) (d W f)
  base : ∀ W, W ≤ W₀ → ∀ r, d W (constFn p W r) = constFn q (m ⁻¹ᵁ W) (D r)
variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g) {X : Scheme.{0}}

def dom (m : A₀.left ⟶ X) (W : X.Opens) : Set (Fin g → ℂ) := {z | ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ W}

def fn (m : A₀.left ⟶ X) (W : X.Opens) (f : Γ(X, W)) (z : Fin g → ℂ) : ℂ := valAt' ((u.ex z).left ≫ m) W f

structure GoodU (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) : Prop where
  ah : u.IsAH Hm χ
  tan₁ : ∀ v, IsTangent v → ∃! w, u.IsDiff w v
  tan₂ : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v
  endo : ∀ f : A₀ ⟶ A₀, IsMonHom f → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F z) = u.ex z ≫ f
  sec : ∀ (n : ℕ) θ, u.IsThetaFn Hm χ n θ → ∃ s, u.IsFnPow n s θ

structure KSRel {R : Type} [CommRing R] (p : X ⟶ Sp R) (m : A₀.left ⟶ X) (D : R → ℂ) (Θ : Matrix (Fin g) (Fin g) ℂ)
    (s : (Fin g → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ) : Prop where
  der : ∀ z, PtDer ((u.ex z).left ≫ m) (s z)
  base : ∀ z r, s z ⊤ (constFn p ⊤ r) = D r
  hol : ∀ W f, DifferentiableOn ℂ (fun z => s z W f) (dom u m W)
  per : ∀ (l : u.Λ) W f, ∀ z ∈ dom u m W,
    s (z + l) W f = s z W f + fderiv ℂ (fn u m W f) z (Θ.mulVec (star (l : Fin g → ℂ)))

def IsSymm (Hm Θ : Matrix (Fin g) (Fin g) ℂ) : Prop :=
  ∀ z w, hermForm Hm (Θ.mulVec (star z)) w = hermForm Hm (Θ.mulVec (star w)) z

def Comm (Θ : Matrix (Fin g) (Fin g) ℂ) (F : (Fin g → ℂ) → (Fin g → ℂ)) : Prop :=
  ∀ z, F (Θ.mulVec (star z)) = Θ.mulVec (star (F z))

def IsConst (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (A₀ : Over (Sp ℂ)) [GrpObj A₀] (ρ : A'.left ⟶ A₀.left)
    (j : A₀.left ⟶ A'.left) : Prop :=
  IsGrpPullback A' A₀ (spMap (algebraMap ℂ (DualNumber ℂ))) ρ ∧
    IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) j ∧ j ≫ ρ = 𝟙 _
end GlobalTheory.KS
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.ZM

variable {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}

structure SFam (h k : ℕ) {o : Type} [CommRing o] (ζ : o) where

  X : Scheme.{0}

  s : X ⟶ Sp o

  smooth : SmoothOfRelativeDimension (h * (h + 1) / 2) s

  qproj : IsQProjOver s

  univ : SiegPre h k ζ s

  princ : univ.Principal

  rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp o) (c : SiegPre h k ζ s'), IsReduced S → Dense {x : S | (s' x).asIdeal = ⊥} →
    c.Principal → ∃ f : S ⟶ X, f ≫ s = s' ∧ SiegPB c univ f

  inj : ∀ (R : Type) [CommRing R] [IsLocalRing R] (x y : Sp R ⟶ X) (s' : Sp R ⟶ Sp o) (c : SiegPre h k ζ s'),
    x ≫ s = y ≫ s → SiegPB c univ x → SiegPB c univ y → x = y

def SRep {h p M : ℕ} (Ag : SiegelFamily h p M) : Prop :=
  IsSeparated Ag.s ∧ ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (ZP p M)) (c : SiegPre h M (zetaZP p M) s'), IsReduced S →
    Dense {x : S | (s' x).asIdeal = ⊥} → c.Principal → ∃ f : S ⟶ Ag.X, f ≫ Ag.s = s' ∧ SiegPB c Ag.univ f

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isSeparated_of_isQProjOver {X : Scheme.{0}} {f : X ⟶ Sp o} (h : IsQProjOver f) : IsSeparated f := by
  obtain ⟨N, i, hi, -, rfl⟩ := h
  have : IsImmersion i := hi
  unfold PSpace.str
  infer_instance

theorem SFam.isSeparated {h : ℕ} {ζ : o} (F : SFam h k ζ) : IsSeparated F.s := isSeparated_of_isQProjOver F.qproj

theorem SFam.eq_constPt {h : ℕ} {ζ : o} (F : SFam h k ζ) (K : Type) [Field K] (x : Sp (DualNumber K) ⟶ F.X)
    (c : SiegPre h k ζ (x ≫ F.s)) (hs : x ≫ F.s = constPt x ≫ F.s) (h₁ : SiegPB c F.univ x)
    (h₂ : SiegPB c F.univ (constPt x)) : x = constPt x := F.inj (DualNumber K) x (constPt x) (x ≫ F.s) c hs h₁ h₂

theorem SFam.sRep {h p M : ℕ} (F : SFam h M (zetaZP p M))
    (sm : SmoothOfRelativeDimension (h * (h + 1) / 2) F.s) (qc : QuasiCompact F.s) (pr : F.univ.Principal) (pts unr) :
    SRep (⟨F.X, F.s, sm, qc, F.univ, pr, pts, unr⟩ : SiegelFamily h p M) := ⟨F.isSeparated, fun S s' c hS hd hc => F.rep S s' c hS hd hc⟩

end GlobalTheory.ZM
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
noncomputable section
namespace GlobalTheory.HkFam
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

def admitted (l : Level H) (𝔓 : Ideal (𝓞 E)) (p : ℕ) : Prop :=
  𝔓.IsMaximal ∧ 𝔓 ⊔ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ ∧ p.Prime ∧ (p : 𝓞 E) ∈ 𝔓 ∧ ¬ p ∣ l.M'

abbrev Ob (D : Datum H) (l : Level H) {S : Scheme.{0}} (s : S ⟶ Sp (KA l)) := Obj D l (baseKA l) s
variable {S : Scheme.{0}}

def HeckeSet (D : Datum H) (t : SAB H S) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (K : Set t.G.left) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃ C : Subgroup (Over.mk x ⟶ t.G),
    (∀ z, z ∈ C ↔ Set.range z.left ⊆ K) ∧ t.HeckeKer (Over.mk x) D 𝔓 p i C

def KerSet {G G' : Over S} [GrpObj G'] (ψ : G ⟶ G') (K : Set G.left) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (z : Over.mk x ⟶ G), z ≫ ψ = 1 ↔ Set.range z.left ⊆ K

def EtSet (G : Over S) (K : Set G.left) : Prop :=
  ∃ (C : Over S) (j : C ⟶ G), IsFinite C.hom ∧ Etale C.hom ∧ IsClosedImmersion j.left ∧ Set.range j.left = K

def Lists {G : Over S} [GrpObj G] (N : ℕ) {n : ℕ} (σ : Fin n → (𝟙_ (Over S) ⟶ G)) (K : Set G.left) : Prop :=
  (∀ j, σ j ^ N = 1) ∧ K = (⋃ j, Set.range (σ j).left) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), Function.Injective fun j => x ≫ (σ j).left

def IsIsogT (t t' : SAB H S) (p : ℕ) (ψ : t.G ⟶ t'.G) : Prop :=
  IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ a, t.act.act a ≫ ψ = ψ ≫ t'.act.act a) ∧
    LBIso (lbPow t.PP.L (p ^ 2)) (t'.PP.L.pull ψ.left)
variable {s : S ⟶ Sp (KA l)}

def IsIsog (o o' : Ob D l s) (p : ℕ) (ψ : o.t.G ⟶ o'.t.G) : Prop :=
  IsIsogT o.t o'.t p ψ ∧ ∀ p' : ℕ, p * p' ≡ 1 [MOD l.M'] → ∀ a, o.eta (p' • a) ≫ ψ = o'.eta a ∧ o.etaA (p' • a) ≫ ψ = o'.etaA a

def IsHecke (o o' : Ob D l s) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (ψ : o.t.G ⟶ o'.t.G) : Prop :=
  IsIsog o o' p ψ ∧ ∃ K, KerSet ψ K ∧ HeckeSet D o.t 𝔓 p i K

def HasQuot (o : Ob D l s) (p : ℕ) (K : Set o.t.G.left) : Prop :=
  ∃ (o' : Ob D l s) (ψ : o.t.G ⟶ o'.t.G), IsIsog o o' p ψ ∧ KerSet ψ K

structure KerScheme (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) where

  Hk : Scheme.{0}

  π₁ : Hk ⟶ Xo.X
  fin₁ : IsFinite π₁
  et₁ : Etale π₁

  o₁ : Ob D l (π₁ ≫ Xo.s)

  m₁ : ObjMap o₁ Xo.univ π₁

  K : Set o₁.t.G.left
  hecke : HeckeSet D o₁.t 𝔓 p i K
  et : EtSet o₁.t.G K
  rep : ∀ (S : Scheme.{0}) (s : S ⟶ Sp (KA l)), IsReduced S → ∀ (o : Ob D l s) (K' : Set o.t.G.left), EtSet o.t.G K' →
    HeckeSet D o.t 𝔓 p i K' → ∃! h : S ⟶ Hk, h ≫ π₁ ≫ Xo.s = s ∧ ∃ n : ObjMap o o₁ h, K' = n.toSABMap.φ ⁻¹' K

structure Corr (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) extends KerScheme Xo 𝔓 p i where

  π₂ : Hk ⟶ Xo.X
  base₂ : π₂ ≫ Xo.s = π₁ ≫ Xo.s

  o₂ : Ob D l (π₁ ≫ Xo.s)

  m₂ : ObjMap o₂ Xo.univ π₂

  ψ : o₁.t.G ⟶ o₂.t.G
  isog : IsIsog o₁ o₂ p ψ
  ker : KerSet ψ K
  univ : ∀ (S : Scheme.{0}) (s : S ⟶ Sp (KA l)), IsReduced S → ∀ (o o' : Ob D l s) (ψ' : o.t.G ⟶ o'.t.G), IsHecke o o' 𝔓 p i ψ' →
    ∃! h : S ⟶ Hk, h ≫ π₁ ≫ Xo.s = s ∧ ∃ (n₁ : ObjMap o o₁ h) (n₂ : ObjMap o' o₂ h),
      ψ'.left ≫ n₂.toSABMap.φ = n₁.toSABMap.φ ≫ ψ.left

def PointQuot (Xo : Moduli D l) (p : ℕ) {k : Type} [Field k] (y y'' : Sp k ⟶ Xo.X) (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G)) : Prop :=
  y'' ≫ Xo.s = y ≫ Xo.s ∧
    ∃ (ψ : pullback Xo.univ.t.G.hom y ⟶ pullback Xo.univ.t.G.hom y'')
      (ψp : (Over.mk y ⟶ Xo.univ.t.G) →* (Over.mk y'' ⟶ Xo.univ.t.G)),
      ψ ≫ pullback.snd _ _ = pullback.snd _ _ ∧ (∀ x, fibPt _ x ≫ ψ = fibPt _ (ψp x)) ∧
      (∀ a x, ψp (x ≫ Xo.univ.t.act.act a) = ψp x ≫ Xo.univ.t.act.act a) ∧
      Function.Surjective ψp ∧ ψp.ker = C ∧
      (∀ (n : ℕ) (x x' : Over.mk y ⟶ Xo.univ.t.G) (c : kˣ), n.Coprime p →
        Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L n x x' (unitOn c) →
        Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L n (ψp x) (ψp x') (unitOn (c ^ (p ^ 2)))) ∧
      ∀ p' : ℕ, p * p' ≡ 1 [MOD l.M'] → ∀ a,
        ψp (toUnit _ ≫ Xo.univ.eta (p' • a)) = toUnit _ ≫ Xo.univ.eta a ∧
        ψp (toUnit _ ≫ Xo.univ.etaA (p' • a)) = toUnit _ ≫ Xo.univ.etaA a

def KerScheme.Carries {Xo : Moduli D l} {𝔓 : Ideal (𝓞 E)} {p i : ℕ} (Z : KerScheme Xo 𝔓 p i) {k : Type} [Field k]
    (z : Sp k ⟶ Z.Hk) (y : Sp k ⟶ Xo.X) (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G)) : Prop :=
  z ≫ Z.π₁ = y ∧ ∀ (u : Over.mk z ⟶ Z.o₁.t.G) (v : Over.mk y ⟶ Xo.univ.t.G), v.left = u.left ≫ Z.m₁.toSABMap.φ →
    (Set.range u.left ⊆ Z.K ↔ v ∈ C)

end GlobalTheory.HkFam
end
end
