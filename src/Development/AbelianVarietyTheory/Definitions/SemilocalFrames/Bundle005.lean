module

public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle006
public import Formalism.LocalRingCardinality.Bundle002
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

@[expose] public section

section

noncomputable section

namespace GlobalTheory.SA

open NumberField Module Formalism.BasicNotions

def CMStar (E : Type) [Field E] [StarRing E] : Prop :=
  ∀ (τ : E →+* ℂ) (x : E), τ (star x) = starRingEnd ℂ (τ x)

section AnySpace

variable {E : Type} [Field E] [NumberField E] [StarRing E]
  {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

def NDLat (h : V →ₗ⋆[E] V →ₗ[E] E) (M : Submodule (𝓞 E) V) : Prop :=
  M.FG ∧ ∀ x ∈ Submodule.span E (M : Set V), (∀ y ∈ M, h y x = 0) → x = 0




omit [NumberField E] [IsScalarTower (𝓞 E) E V] in
theorem orth_span (h : V →ₗ⋆[E] V →ₗ[E] E) {M : Submodule (𝓞 E) V} {x : V} (hx : ∀ y ∈ M, h y x = 0) :
    ∀ y ∈ Submodule.span E (M : Set V), h y x = 0 := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy => exact hx y hy
  | zero => simp
  | add a b _ _ ha hb => rw [map_add (f := _), LinearMap.add_apply, ha, hb, add_zero]
  | smul c a _ ha => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, ha, smul_zero]


omit [NumberField E] in
theorem ndLat_of_isLattice {h : V →ₗ⋆[E] V →ₗ[E] E} (hn : h.Nondegenerate) {M : Submodule (𝓞 E) V}
    (hM : Submodule.IsFullLattice E M) : NDLat h M :=
  ⟨hM.fg, fun x _ h0 => hn.2 x fun y => orth_span h h0 y (by rw [hM.span_eq_top]; trivial)⟩

end AnySpace

variable {E : Type} [Field E] [NumberField E] [StarRing E]

structure Amb (S : HSpace E) (k r : ℕ) : Prop where
  cm : CMStar E
  dim : finrank E S.V = k + 2 * r + 1
  neg : ∀ (τ : E →+* ℂ) (U : Submodule E S.V), (∀ x ∈ U, (τ (S.hT x x)).re ≤ 0) → finrank E U ≤ r + 1

section Diagonal

open Formalism.BasicNotions.Examples₂

def wittSigns (k r : ℕ) : Fin (k + 2 * r + 1) → Bool := fun i => decide ((i : ℕ) < r + 1)

def wittSpace (E : Type) [Field E] [NumberField E] [StarRing E] (k r : ℕ) : HSpace E :=
  stdSpace star_isIntegral (k + 2 * r + 1) (wittSigns k r) (k + r) (r + 1)

end Diagonal

end GlobalTheory.SA

end
end

section

noncomputable section

namespace GlobalTheory.RowLev

open Formalism.MainNotions.S Formalism.BasicNotions NumberField Matrix
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def coordLat (W : HSpace E) : Submodule (𝓞 E) (Fin W.rank → E) :=
  W.L0.map (W.frame.equivFun.toLinearMap.restrictScalars (𝓞 E))

def congSet (cm : CMData F E) (W : HSpace E) (g : ℕ) : Set (Formalism.UG.UPts cm.sig W.gram (Af F)) :=
  {x | (x : GL (Fin W.rank) (E ⊗[F] Af F)) ∈ Formalism.UG.stabGL (lamAf (F := F) (coordLat W)) ∧
    ∀ y ∈ lamAf (F := F) (coordLat W), ∃ z ∈ lamAf (F := F) (coordLat W),
      ((x : GL (Fin W.rank) (E ⊗[F] Af F)) - 1 : Matrix (Fin W.rank) (Fin W.rank) (E ⊗[F] Af F)) *ᵥ y =
        (g : E ⊗[F] Af F) • z}

structure InstData (cm : CMData F E) (W : HSpace E) (ε : InfinitePlace F → Fin W.rank → Bool)
    (φ : InfinitePlace F → (E →+* ℂ)) where
  J_herm : Formalism.UG.IsHerm (starRingEnd E) W.gram
  J_det : W.gram.det ≠ 0
  L_span : Submodule.span E (coordLat W : Set (Fin W.rank → E)) = ⊤
  L_fg : (coordLat W).FG
  L_dual : ∀ x : Fin W.rank → E, x ∈ coordLat W ↔
    ∀ y ∈ coordLat W, Formalism.UG.hform (starRingEnd E) W.gram y x ∈ (algebraMap (𝓞 E) E).range
  φ_over : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a
  P : InfinitePlace F → Matrix (Fin W.rank) (Fin W.rank) ℂ
  P_unit : ∀ v, IsUnit (P v)
  P_spec : ∀ v, (P v)ᴴ * W.gram.map (φ v) * P v = Formalism.REAL.Jm (ε v)
  topf : TopologicalSpace (Formalism.UG.UPts cm.sig W.gram (Af F))
  topf_group : @IsTopologicalGroup _ topf _
  topf_open : ∀ g : ℕ, 1 ≤ g → @IsOpen _ topf (congSet cm W g)
  topf_basis : ∀ U ∈ @nhds _ topf 1, ∃ g : ℕ, 1 ≤ g ∧ congSet cm W g ⊆ U

end GlobalTheory.RowLev
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace GlobalTheory.St.G

abbrev Ad (F : Type) [Field F] [NumberField F] : Type := FiniteAdeleRing (𝓞 F) F

abbrev OAd (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] : Subring (E ⊗[F] Ad F) :=
  tensInt (F := F) (Ad F) (intOE E) (intAd F)

def SplitsIn (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop :=
  (placesOver E p).ncard = Module.finrank ℚ E

section Lat

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

abbrev hat (L : Submodule (𝓞 E) (Fin n → E)) : Submodule (OAd F E) (Fin n → E ⊗[F] Ad F) :=
  latS (F := F) (Ad F) (OAd F E) L

variable {F}

abbrev loc (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (intV E v) (Fin n → E ⊗[F] v.adicCompletion F) :=
  latS (F := F) (v.adicCompletion F) (intV E v) L

def IsLat (L : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  Module.Finite (𝓞 E) L ∧ Submodule.span E (L : Set (Fin n → E)) = ⊤

def prVec (v : HeightOneSpectrum (𝓞 F)) (x : Fin n → E ⊗[F] Ad F) : Fin n → E ⊗[F] v.adicCompletion F :=
  fun i => prV (E := E) v (x i)

variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)

abbrev dualL (L : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) :=
  Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J L)

def hR (R : Type) [CommRing R] [Algebra F R] (x y : Fin n → E ⊗[F] R) : E ⊗[F] R :=
  hform (sigR σ R) (J.map (inclE (F := F) R)) x y

def TLat (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  IsLat L ∧ (∀ x ∈ L, x ∈ dualSet (σ : E →+* E) J L) ∧ (∀ y ∈ dualSet (σ : E →+* E) J L, (T : E) • y ∈ L) ∧
  L.toAddSubgroup.relIndex (dualL σ J L).toAddSubgroup = T ^ (2 * f) ∧
  ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → ∃ x ∈ loc v (dualL σ J L), x ∉ loc v L

def SelfDualAt (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ y, y ∈ loc v L ↔ ∀ z ∈ loc v L, hR σ J (v.adicCompletion F) z y ∈ intV E v

end Lat

def InModL {A : Type} [CommRing A] {O : Subring A} {n : ℕ} (Λ : Submodule O (Fin n → A)) (m : ℕ)
    (S : Set (Fin n → A)) (x : Fin n → A) : Prop :=
  ∃ s ∈ Submodule.span O S, ∃ z ∈ Λ, x = s + (m : A) • z

def supSum {A : Type} [CommRing A] {n k : ℕ} (h : (Fin n → A) → (Fin n → A) → A) (b bd : Fin k → Fin n → A)
    (y : Matrix (Fin n) (Fin n) A) : A :=
  ∑ i : Fin k, if hi : i.1 + 1 < k then h (bd i) (y *ᵥ b ⟨i.1 + 1, hi⟩) else 0

section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)

structure AdFrame (Λ : Submodule (OAd F E) (Fin n → E ⊗[F] Ad F)) (g k : ℕ) where
  eps : E ⊗[F] Ad F
  eps_idem : eps * eps = eps
  eps_orth : eps * sigR σ (Ad F) eps = 0
  eps_int : eps ∈ OAd F E
  eps_full : ∀ y ∈ Λ, ∃ z ∈ Λ, (1 - eps - sigR σ (Ad F) eps) • y = (g : E ⊗[F] Ad F) • z
  b : Fin k → Fin n → E ⊗[F] Ad F
  bd : Fin k → Fin n → E ⊗[F] Ad F
  b_mem : ∀ i, b i ∈ Λ
  bd_mem : ∀ i, bd i ∈ Λ
  b_eps : ∀ i, b i = eps • b i
  bd_eps : ∀ i, bd i = sigR σ (Ad F) eps • bd i
  dual : ∀ i j, ∃ t ∈ OAd F E, hR σ J (Ad F) (bd i) (b j) - (if i = j then eps else 0) = (g : E ⊗[F] Ad F) * t
  span : ∀ y ∈ Λ, InModL Λ g (Set.range b ∪ Set.range bd) y
  psi : E ⊗[F] Ad F → ℂ
  psi_add : ∀ x y, psi (x + y) = psi x * psi y
  psi_int : ∀ x ∈ OAd F E, psi x = 1
  psi_rat : ∀ x : E, psi (inclE (F := F) (Ad F) x) *
    Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ E x : ℚ) : ℂ)) = 1

variable {σ J} {Λ : Submodule (OAd F E) (Fin n → E ⊗[F] Ad F)} {g k : ℕ}

def AdFrame.InK (Fr : AdFrame σ J Λ g k) (y : GL (Fin n) (E ⊗[F] Ad F)) : Prop :=
  y ∈ stabGL Λ ∧
  (∀ x, (∀ z ∈ Λ, hR σ J (Ad F) z x ∈ OAd F E) → (y.1 - 1) *ᵥ x ∈ Λ) ∧
  ∀ i : Fin k, InModL Λ g (Fr.b '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ Fr.b i)

def AdFrame.chi (Fr : AdFrame σ J Λ g k) (y : GL (Fin n) (E ⊗[F] Ad F)) : ℂ :=
  Fr.psi (algebraMap F (E ⊗[F] Ad F) ((g : F)⁻¹) * supSum (hR σ J (Ad F)) Fr.b Fr.bd y.1)

def AdFrame.LocK (Fr : AdFrame σ J Λ g k) (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F))
    (y : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Prop :=
  ∀ i : Fin k, InModL (loc v L) g ((fun j => prVec v (Fr.b j)) '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ prVec v (Fr.b i))

def AdFrame.locChi (Fr : AdFrame σ J Λ g k) (v : HeightOneSpectrum (𝓞 F))
    (y : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : ℂ :=
  Fr.psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((g : F)⁻¹) *
    supSum (hR σ J (v.adicCompletion F)) (fun j => prVec v (Fr.b j)) (fun j => prVec v (Fr.bd j)) y.1))

end Frame

end GlobalTheory.St.G

end
end
