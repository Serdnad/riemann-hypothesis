module

public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
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

namespace GlobalTheory.CompanionTheory.Ar.Fl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

abbrev under {Xo : Moduli D l} {c : Coeff l} {T : Scheme.{0}} (y : T ⟶ Xo.XF c) : T ⟶ Xo.X := y ≫ pullback.fst _ _

abbrev Vecs {Xo : Moduli D l} {c : Coeff l} {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c) (n : ℕ) : Type :=
  Fin n → (epsAt (under y) ⟶ Xo.univ.t.G)

abbrev FrameFn (Xo : Moduli D l) (c : Coeff l) : Type 1 :=
  ∀ (F : Type) [Field F] (y : Sp F ⟶ Xo.XF c), Vecs y D.p → Vecs y D.q → F

variable {Xo : Moduli D l} {c : Coeff l}

def IsFramed (U : Set (Xo.XF c)) (τ : E →+* ℂ) {F : Type} [Field F] (β : c.F →+* F) (y : Sp F ⟶ Xo.XF c)
    (v : Vecs y D.p) (w : Vecs y D.q) : Prop :=
  y ≫ pullback.snd _ _ = spMap β ∧ Set.range y ⊆ U ∧
    IsEigFrame Xo.univ.t.act (under y) (β.comp (tauIn c τ)) v ∧
    IsEigFrame Xo.univ.t.act (under y) (β.comp (tauIn c (ComplexEmbedding.conjugate τ))) w

structure IsLineFn (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) : Prop where
  ne : ∀ (F : Type) [Field F] (β : c.F →+* F) y v w, IsFramed U τ β y v w → φ F y v w ≠ 0
  chg : ∀ (F : Type) [Field F] (β : c.F →+* F) y v w v' w' (A : Matrix (Fin D.p) (Fin D.p) F)
    (B : Matrix (Fin D.q) (Fin D.q) F), IsFramed U τ β y v w → IsFramed U τ β y v' w' →
    (∀ i, IsComb (A i) v (v' i)) → (∀ j, IsComb (B j) w (w' j)) → φ F y v' w' * A.det = φ F y v w * B.det
  nat : ∀ (F F' : Type) [Field F] [Field F'] (f : F →+* F') (β : c.F →+* F) y v w (y' : Sp F' ⟶ Xo.XF c) v' w',
    IsFramed U τ β y v w → y' = spMap f ≫ y → (∀ i, (v' i).left = spMap (dualMap f) ≫ (v i).left) →
    (∀ j, (w' j).left = spMap (dualMap f) ≫ (w j).left) → φ F' y' v' w' = f (φ F y v w)

def IsConstMul (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ) : Prop :=
  ∀ (P : (FU.Di i).La →+ (Fin g → ℂ)) (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q)
    (V : Fin D.p → Fin g → ℂ) (W : Fin D.q → Fin g → ℂ) (C : Matrix (Fin D.p) (Fin D.p ⊕ Fin D.q) ℂ)
    (Fm B : Matrix (Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ),
    IsPeriod (FU.Di i) ty P → under y = FU.u i P → IsFramed U τ (algebraMap c.F ℂ) y v w →
    (∀ a, IsDerivAt0 (fun z => (FU.ex i P z).left) (V a) (v a).left) →
    (∀ j, IsDerivAt0 (fun z => (FU.ex i P z).left) (W j) (w j).left) →
    (∀ a, tyPart ty τ (∑ m, C a m • P (e m)) = V a) →
    (∀ n, tyPart ty (ComplexEmbedding.conjugate τ) (P (e n)) = ∑ j, B j n • W j) →
    (∀ j n, ∑ m, Fm j m * τ (sesq (FU.Di i) (e m) (e n)) = B j n) →
    φ ℂ y v w * (Matrix.fromRows C Fm).det = ρ

structure IsFlatGen (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) : Prop where
  mem : ∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P →
    y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U
  line : IsLineFn U τ φ
  flat : ∃ (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ), LinearIndependent (𝓞 E) e ∧ IsConstMul U τ φ FU i e ρ

def HasInfNorm (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (s : c.F →+* ℂ) (t : ℝ) : Prop :=
  ∀ (y : Sp ℂ ⟶ Xo.XF c) v w (Γ : Matrix (Fin D.p) (Fin D.p) ℂ) (Δ : Matrix (Fin D.q) (Fin D.q) ℂ),
    IsFramed U τ s y v w → IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y) v Γ →
    IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y) w Δ →
    Real.log ‖φ ℂ y v w‖ + (Real.log ‖Γ.det‖ - Real.log ‖Δ.det‖) / 2 = t

def IsIntFrame {V K : Type} [CommRing V] [Field K] [Algebra V K] {y : Sp K ⟶ Xo.XF c} {t : SAB H (Sp V)}
    {tK : SAB H (Sp K)} (m : SABMap tK Xo.univ.t (under y)) (m' : SABMap tK t (spMap (algebraMap V K)))
    (σ : 𝓞 E →+* K) {n : ℕ} (v : Vecs y n) : Prop :=
  ∃ (σV : 𝓞 E →+* V) (vV : Fin n → (epsAt (𝟙 (Sp V)) ⟶ t.G)), (algebraMap V K).comp σV = σ ∧
    IsEigFrame t.act (𝟙 (Sp V)) σV vV ∧ ∀ a, ∃ u : Sp (DualNumber K) ⟶ tK.G.left,
      u ≫ m.φ = (v a).left ∧ u ≫ m'.φ = spMap (dualMap (algebraMap V K)) ≫ (vV a).left

def HasFinNorm (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (t : ℝ) : Prop :=
  ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (j : K →+* ℂ_[p]) (β : c.F →+* K) (y : Sp K ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q) (T : SAB H (Sp V))
    (tK : SAB H (Sp K)) (m : SABMap tK Xo.univ.t (under y)) (m' : SABMap tK T (spMap (algebraMap V K))),
    (∀ a : K, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V K).range) → j.comp β = κ → IsFramed U τ β y v w →
    IsIntFrame m m' (β.comp (tauIn c τ)) v → IsIntFrame m m' (β.comp (tauIn c (ComplexEmbedding.conjugate τ))) w →
    Real.log ‖j (φ K y v w)‖ = t

def HasNorms (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (N : LogNorms c.F) : Prop :=
  (∀ s, HasInfNorm U τ φ s (N.inf s)) ∧ ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), HasFinNorm U τ φ p κ
    (N.fin p κ + D.q * (logIdeal (κ.comp (tauIn c τ)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖((H.d : ℕ) : ℂ_[p])‖))

end GlobalTheory.CompanionTheory.Ar.Fl
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct

section Metric

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Sp Ω ⟶ X}
  {Li : Type} [AddCommGroup Li] [Module Ω Li]

structure LieMetric (M : LieModel G ξ Li) {K : Type} {J : K → Type} (y : (Σ k, J k) → Ω) where

  ip : ∀ z : Sp ℂ ⟶ X, (epsAt z ⟶ G) → (epsAt z ⟶ G) → ℂ
  herm : ∀ (z : Sp ℂ ⟶ X) (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel G z V),
    ∃ core : InnerProductSpace.Core ℂ V, ∀ a b, core.inner a b = ip z (Mz.pt a) (Mz.pt b)
  conj : ∀ (z : Sp ℂ ⟶ X) (v w : epsAt z ⟶ G) (v' w' : epsAt (spMap (starRingEnd ℂ) ≫ z) ⟶ G),
    v'.left = spMap (dualMap (starRingEnd ℂ)) ≫ v.left → w'.left = spMap (dualMap (starRingEnd ℂ)) ≫ w.left →
      ip _ v' w' = starRingEnd ℂ (ip z v w)
  cont : ∀ a b : Li, ∃ F : ((Σ k, J k) → ℂ) → ℂ,
    ContinuousOn F {w | ∃ (z : Sp ℂ ⟶ X) (va vb : epsAt z ⟶ G), CoordsAt ξ y z w ∧ M.ValAt z a va ∧ M.ValAt z b vb} ∧
      ∀ (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ) (va vb : epsAt z ⟶ G), CoordsAt ξ y z w → M.ValAt z a va →
        M.ValAt z b vb → F w = ip z va vb

def LieMetric.Orth {M : LieModel G ξ Li} {K : Type} {J : K → Type} {y : (Σ k, J k) → Ω} (h : LieMetric M y)
    {O : Type} [CommRing O] (act : OAct O G) : Prop :=
  ∀ (z : Sp ℂ ⟶ X) (τ τ' : O →+* ℂ) (v w : epsAt z ⟶ G), τ ≠ τ' → IsLieEigen act z τ v → IsLieEigen act z τ' w →
    h.ip z v w = 0

variable {L : Type} [Field L] [NumberField L]

def IsFibre (rel : ∀ z : Sp ℂ ⟶ X, (epsAt z ⟶ G) → (epsAt z ⟶ G) → ℂ → Prop) (z : Sp (𝓞 L) ⟶ X)
    (B : HermitianBundle.{0} L) (MB : LieModel G z B.carrier) : Prop :=
  ∀ (σ : L →+* ℂ) (x x' : B.carrier) (v v' : epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) ⟶ G),
    (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt x).left) → (v'.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt x').left) →
      rel _ v v' ((B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x'))

def IsSubFibre (M : LieModel G ξ Li) (U : Submodule Ω Li) (z : Sp (𝓞 L) ⟶ X) {V : Type} [AddCommGroup V]
    [Module (𝓞 L) V] (MB : LieModel G z V) (F : Submodule (𝓞 L) V) : Prop :=
  ∀ x, x ∈ F ↔ ∃ a : 𝓞 L, a ≠ 0 ∧ a • x ∈ Submodule.span (𝓞 L)
    {x' | ∃ e ∈ U, ∃ v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G,
      M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e v ∧ (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x').left)}

end Metric

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

structure AbPart {S : Scheme.{0}} (t : SAB H S) {K : Type} [Field K] (z : Sp K ⟶ S) where

  tK : SAB H (Sp K)
  m : SABMap tK t z

  τ : TorusExtension tK.G

  tB : SAB H (Sp K)

  e : τ.B ≅ tB.G
  e_hom : letI := τ.grpB; IsMonHom e.hom
  act : ∀ a, tK.act.act a ≫ τ.q ≫ e.hom = τ.q ≫ e.hom ≫ tB.act.act a
  pp : LBIso tK.PP.L (tB.PP.L.pull (τ.q ≫ e.hom).left)

def IsPrincipal {K : Type} [Field K] (t : SAB H (Sp K)) : Prop :=
  IsProper t.G.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L

def SlopeBoundSt : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L]
    (t : SAB H (Sp (𝓞 L))) (tK : SAB H (Sp L)) (_ : SABMap tK t (spMap (algebraMap (𝓞 L) L))), IsPrincipal tK →
    ∀ (B : HermitianBundle.{0} L) (MB : LieModel t.G (𝟙 _) B.carrier), IsFibre (HodgeIP t.G t.PP.L) (𝟙 _) B MB →
      B.slopeMax ≤ ((C * Real.log (2 + Module.finrank (𝓞 L) B.carrier + max (-B.normDegree ⊤) 0) : ℝ) : EReal)

end GlobalTheory.CompanionTheory.Ar
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

abbrev CMType (H : Host E) : Type := {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}

def labelEmb (c : Coeff l) : CMType H ⊕ CMType H → (𝓞 E →+* c.F)
  | .inl τ => (τ.1.codRestrict c.F (c.conj τ.1)).comp (algebraMap (𝓞 E) E)
  | .inr τ => ((τ.1.codRestrict c.F (c.conj τ.1)).comp (algebraMap (𝓞 E) E)).comp (H.bar : 𝓞 E →+* 𝓞 E)

abbrev labelRk (D : Datum H) : CMType H ⊕ CMType H → ℕ := Sum.elim (fun _ => D.p) (fun _ => D.q)

def htLabel {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {G : Over X} [GrpObj G]
    {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : LB G.left) (n : ℕ)
    (ρ : 𝓞 E →+* Module.End Ω Li) (σ : CMType H ⊕ CMType H → (𝓞 E →+* Ω)) : CMType H ⊕ CMType H → Lat ξ Li
  | .inl τ => M.htW L n ρ (σ (.inl τ)) (differentIdeal ℤ (𝓞 E))
  | .inr τ => M.htDual L n ρ (σ (.inr τ))

variable {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

structure HodgeCpt (Y : Model Xo c β) (S : Finset ℕ) {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
    (y : (Σ k, J k) → Ω) where

  X : Scheme.{0}

  ξ : Spec (CommRingCat.of Ω) ⟶ X
  all : ∀ q : X, genPt ξ ⤳ q
  tie : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩
  normal : IsNormalScheme X

  f : X ⟶ Y.X

  Ω₀ : Type
  [fld₀ : Field Ω₀]

  ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X
  gen₀ : IsCptGen ξ₀

  cst : c.F →+* Ω
  cst_over : ξ ≫ f ≫ Y.s = spMap (cst.comp β)

  fn : Ω₀ →+* Ω
  fn_over : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f fn

  t : SAB H X
  m : SABMap t Y.t f

  Li : Type
  [acg : AddCommGroup Li]
  [mod : Module Ω Li]
  M : LieModel t.G ξ Li

  ρ : 𝓞 E →+* Module.End Ω Li
  act : M.IsActOf t.act.act ρ
  S_prime : ∀ p ∈ S, p.Prime

  R : ℕ → ℕ
  R_ge : ∀ p ∈ S, 4 ≤ R p
  tors : ∀ p ∈ S, FullTorsion t.G ξ (p ^ R p)
  vb : ∀ s, (Lat.patch S (M.eigLat ρ (cst.comp (labelEmb c s)))
      fun p => htLabel M t.PP.L (p ^ R p) ρ (fun s' => cst.comp (labelEmb c s')) s).IsVB (labelRk D s)
    (eigSp ρ (cst.comp (labelEmb c s)))

attribute [instance] HodgeCpt.fld₀ HodgeCpt.acg HodgeCpt.mod

namespace HodgeCpt

variable {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
  {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)

def emb (s : CMType H ⊕ CMType H) : 𝓞 E →+* Ω := 𝔐.cst.comp (labelEmb c s)

def Vgen (s : CMType H ⊕ CMType H) : Submodule Ω 𝔐.Li := eigSp 𝔐.ρ (𝔐.emb s)

def dR (s : CMType H ⊕ CMType H) : Lat 𝔐.ξ 𝔐.Li := 𝔐.M.eigLat 𝔐.ρ (𝔐.emb s)

def HT (p : ℕ) (s : CMType H ⊕ CMType H) : Lat 𝔐.ξ 𝔐.Li := htLabel 𝔐.M 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ 𝔐.emb s

def V (s : CMType H ⊕ CMType H) : Lat 𝔐.ξ 𝔐.Li := Lat.patch S (𝔐.dR s) fun p => 𝔐.HT p s

def IsCover (d : ℕ) : Prop :=
  0 < d ∧ letI := 𝔐.fn.toAlgebra; Module.finrank 𝔐.Ω₀ Ω = d

def Interior {R : Type} [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ 𝔐.X) : Prop :=
  centre z ∈ abLocus 𝔐.t.G

structure Flag where

  b : ∀ s, Fin (labelRk D s) → 𝔐.Li
  sub : ∀ s, (𝔐.V s).IsFlagVBOn Set.univ (b s)

  Li₀ : Type
  [acg : AddCommGroup Li₀]
  [mod : Module 𝔐.Ω₀ Li₀]
  M₀ : LieModel Y.t.G 𝔐.ξ₀ Li₀

  j : Li₀ →+ 𝔐.Li
  j_pt : ∀ e, (𝔐.M.pt (j e)).left ≫ 𝔐.m.φ = spMap (dualMap 𝔐.fn) ≫ (M₀.pt e).left

  V₀ : CMType H ⊕ CMType H → Submodule 𝔐.Ω₀ Li₀
  V₀_mem : ∀ s e, e ∈ V₀ s ↔ j e ∈ 𝔐.Vgen s

  deg : ℕ
  generic : letI := 𝔐.fn.toAlgebra; IsGenericFlag (Ω' := Ω) j V₀ b deg

attribute [instance] Flag.acg Flag.mod

variable {𝔐}

def rootIdx (D : Datum H) (r : CMType H × Fin (D.p + D.q)) : Σ s, Fin (labelRk D s) :=
  if h : (r.2 : ℕ) < D.p then ⟨.inl r.1, ⟨r.2, h⟩⟩
  else ⟨.inr r.1, ⟨D.p + D.q - 1 - r.2, by have := r.2.2; show _ < D.q; omega⟩⟩

def rootSgn (D : Datum H) (r : CMType H × Fin (D.p + D.q)) : ℤ := if (r.2 : ℕ) < D.p then 1 else -1

def Flag.rootLat (Fl : 𝔐.Flag) (r : CMType H × Fin (D.p + D.q)) : Lat 𝔐.ξ Ω :=
  Lat.tens (fun _ : Unit => (𝔐.V (rootIdx D r).1).gr (Fl.b (rootIdx D r).1) (rootIdx D r).2) fun _ => rootSgn D r

def Flag.RootLines (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ)
    (e : CMType H × Fin (D.p + D.q) → Ω) : Prop :=
  ∀ r, (Fl.rootLat r).IsDegOn Set.univ y (xdeg r) (e r)

def Flag.IsHodgeLine [∀ k, Fintype (J k)] (Fl : 𝔐.Flag) (r : CMType H × Fin (D.p + D.q)) (e₀ : Ω)
    (A : HermLine J) : Prop :=
  ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → 𝔐.Interior z →
    ∀ t ν, 𝔐.M.IsGrNorm 𝔐.t.PP.L (𝔐.V (rootIdx D r).1) (Fl.b (rootIdx D r).1) (rootIdx D r).2 z t ν →
      SecNorm 𝔐.ξ y A e₀ z w (t ^ rootSgn D r) (ν ^ rootSgn D r)

end HodgeCpt

end GlobalTheory.CompanionTheory.Ar
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Filter Topology

def IsHolPts {R : Type} [CommRing R] {n : ℕ} (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) : Prop :=
  IsOpen B ∧ ∀ r : R, DifferentiableOn ℂ (fun b => ψ b r) B

structure FamExp {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] {g n : ℕ}
    (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) where

  ex : ∀ b : Fin n → ℂ, (Fin g → ℂ) → (Over.mk (spMap (ψ b)) ⟶ G)
  add : ∀ b ∈ B, ∀ z w, ex b (z + w) = ex b z * ex b w
  hol : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => (ex bz.1 bz.2).left)
  diff : ∀ b ∈ B, ∀ a : Fin g, IsDerivAt0 (fun z => (ex b z).left) (Pi.single a 1)
    (spMap (dualMap (ψ b)) ≫ (M.pt (Pi.single a 1)).left)
  log : ∀ b₀ ∈ B, ∃ (V : G.left.Opens) (N : ℕ) (f : Fin N → Γ(G.left, V))
    (L : (Fin n → ℂ) × (Fin N → ℂ) → (Fin g → ℂ)), ⊤ ≤ (ex b₀ 0).left ⁻¹ᵁ V ∧
    AnalyticAt ℂ L (b₀, fun j => valAt' (ex b₀ 0).left V (f j)) ∧
    (∀ᶠ bz : (Fin n → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0),
      L (bz.1, fun j => valAt' (ex bz.1 bz.2).left V (f j)) = bz.2) ∧
    ∀ᶠ p : (Fin n → ℂ) × (Fin N → ℂ) in 𝓝 (b₀, fun j => valAt' (ex b₀ 0).left V (f j)),
      ∀ x : Over.mk (spMap (ψ p.1)) ⟶ G, ⊤ ≤ x.left ⁻¹ᵁ V → (∀ j, valAt' x.left V (f j) = p.2 j) →
        x = ex p.1 (L p)

def FamExp.per {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {g n : ℕ}
    {M : LieModel G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}
    (e : FamExp G M B ψ) (b : Fin n → ℂ) : Set (Fin g → ℂ) := {z | e.ex b z = 1}

end GlobalTheory.CompanionTheory.Ar.Flat
end
end
