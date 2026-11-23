module

public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle003
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ConjugateFieldNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
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

namespace GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice
open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def indexIdeal (L' L : Submodule (𝓞 E) (Fin n → E)) : Ideal (𝓞 E) :=
  Ideal.span {a | ∃ g : (Fin n → E) →ₗ[E] (Fin n → E), (∀ x ∈ L', g x ∈ L) ∧ (a : E) = LinearMap.det g}

def latIdeal (Λ : Lat E n) : Ideal (𝓞 E) := indexIdeal Λ.L Λ.inter

omit [IsCMField E] in
theorem latIdeal_ne_bot (Λ : Lat E n) : latIdeal Λ ≠ ⊥ := by
  classical
  obtain ⟨S, hS⟩ := Λ.fg
  obtain ⟨k, hk⟩ := IsLocalization.exist_integer_multiples (𝓞 E)⁰ (S ×ˢ (Finset.univ : Finset (Fin n)))
    (fun t => (t.1 t.2 : E))
  have hL : ∀ x ∈ Λ.L, (k : 𝓞 E) • x ∈ stdMod E n := by
    have : Λ.L ≤ (stdMod E n).comap (LinearMap.lsmul (𝓞 E) (Fin n → E) (k : 𝓞 E)) := by
      rw [← hS, Submodule.span_le]
      intro x hx
      refine mem_stdMod.2 fun j => ?_
      obtain ⟨a, ha⟩ := hk (x, j) (by simpa using hx)
      exact ⟨a, ha⟩
    exact fun x hx => this hx
  intro h
  have hm : (k : 𝓞 E) ^ n ∈ latIdeal Λ := by
    refine Ideal.subset_span ⟨((k : 𝓞 E) : E) • LinearMap.id, fun x hx => ⟨hL x hx, Λ.L.smul_mem _ hx⟩, ?_⟩
    rw [LinearMap.det_smul]
    simp
  rw [h, Ideal.mem_bot] at hm
  exact pow_ne_zero n (nonZeroDivisors.coe_ne_zero k) hm


variable {H : Host E} (Dw : Datum H) {l : Level H} (c : Coeff l)

def reflexNorm (γ : E) : c.F := ∏ σ : E →+* ℂ, embF c σ γ ^ Dw.mult σ

def reflexIdeal (𝔞 : Ideal (𝓞 E)) : Ideal (𝓞 c.F) :=
  ∏ σ : E →+* ℂ, 𝔞.map (RingOfIntegers.mapRingHom (embF c σ)) ^ Dw.mult σ

def IsBe (𝔞 : Ideal (𝓞 E)) (β : c.F) : Prop :=
  (∃ b : 𝓞 c.F, (b : c.F) = β ∧ Ideal.span {b} = reflexIdeal Dw c 𝔞) ∧
    ∀ s : c.F →+* ℂ, ‖s β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ (Dw.p + Dw.q)

def IsBeLat (Λ : Lat E n) (β : c.F) : Prop := IsBe Dw c (latIdeal Λ) β

def ReflexLe : Prop := ∀ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ → ∃ β : c.F, IsBe Dw c 𝔞 β

theorem isBe_top : IsBe Dw c ⊤ 1 :=
  ⟨⟨1, rfl, by
    simp only [reflexIdeal, Ideal.map_top, Ideal.span_singleton_one]
    simp [← Ideal.one_eq_top]⟩, fun s => by simp⟩

variable {Dw c}


open scoped Classical in
def beIdeal (hK : ReflexLe Dw c) (𝔞 : Ideal (𝓞 E)) (h𝔞 : 𝔞 ≠ ⊥) : c.F :=
  if 𝔞 = ⊤ then 1 else (hK 𝔞 h𝔞).choose

def be (hK : ReflexLe Dw c) (Λ : Lat E n) : c.F := beIdeal hK (latIdeal Λ) (latIdeal_ne_bot Λ)

variable (Dw c)

end GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AutomorphismGroupTopologies

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateFieldNorm
open scoped TensorProduct

section Quot

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra F E] {r : ℕ}

@[reducible] def topU (A : Type) [CommRing A] [Algebra F A] [t : TopologicalSpace A] (V : HSpace E r) :
    TopologicalSpace (UA F A V) :=
  ⨅ (a : Fin r) (b : Fin r) (φ : E →ₗ[F] F),
    t.induced fun g => TensorProduct.rid F A (LinearMap.lTensor A φ (g.1.val a b))

@[reducible] def topG (V : HSpace E r) : TopologicalSpace (GA F V) :=
  (topU F (Ai F) V).induced Prod.fst ⊓ (topU F (Af F) V).induced Prod.snd

def ratG (V : HSpace E r) : Subgroup (GA F V) where
  carrier := {g | ∃ γ, IsRat F V γ g}
  one_mem' := ⟨1, by simp [IsRat, Matrix.map_one]⟩
  mul_mem' := by
    rintro g h ⟨γ, g1, g2⟩ ⟨δ, h1, h2⟩
    refine ⟨γ * δ, ?_, ?_⟩
    · rw [Units.val_mul, Matrix.map_mul, ← g1, ← h1]; rfl
    · rw [Units.val_mul, Matrix.map_mul, ← g2, ← h2]; rfl
  inv_mem' := by
    rintro g ⟨γ, g1, g2⟩
    have e1 : g.1.1 = Matrix.GeneralLinearGroup.map (incl F (Ai F)) γ := Units.ext g1
    have e2 : g.2.1 = Matrix.GeneralLinearGroup.map (incl F (Af F)) γ := Units.ext g2
    refine ⟨γ⁻¹, ?_, ?_⟩
    · change (g.1.1⁻¹).val = _
      rw [e1, ← map_inv]; rfl
    · change (g.2.1⁻¹).val = _
      rw [e2, ← map_inv]; rfl

def AutQ (V : HSpace E r) : Type := Quotient (QuotientGroup.rightRel (ratG F V))

def autMk (V : HSpace E r) (g : GA F V) : AutQ F V := Quotient.mk _ g

instance (V : HSpace E r) : MeasurableSpace (AutQ F V) := (@borel _ (topG F V)).map (autMk F V)

def autRt (V : HSpace E r) (h : GA F V) : AutQ F V → AutQ F V :=
  Quotient.map' (· * h) fun a b hab => by
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    simpa [mul_assoc] using hab

def IsAutProb (V : HSpace E r) (ν : Measure (AutQ F V)) : Prop :=
  IsProbabilityMeasure ν ∧ ∀ h s, MeasurableSet s → ν (autRt F V h ⁻¹' s) = ν s

def FinVol (V : HSpace E r) : Prop := ∃ ν, IsAutProb F V ν

end Quot

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] [Algebra F E] {R : Nums E} (Q : CorePar F R)

variable {Q}

end GlobalTheory.IndefiniteRowSideFullHecke.AutomorphismGroupTopologies
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing

open Formalism.L2.Pj Formalism.L2.PjFree NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {c c' : Coeff l}

def incl (h : c.F ≤ c'.F) : c.F →+* c'.F := (IntermediateField.inclusion h).toRingHom

def Res (_h : c.F ≤ c'.F) (S : Type) : Type := S

instance (h : c.F ≤ c'.F) (S : Type) [CommRing S] : CommRing (Res h S) := inferInstanceAs (CommRing S)

instance (h : c.F ≤ c'.F) (S : Type) [CommRing S] [Algebra c'.F S] : Algebra c.F (Res h S) :=
  ((algebraMap c'.F S).comp (incl h)).toAlgebra

def unRes {h : c.F ≤ c'.F} {S : Type} [CommRing S] : Res h S ≃+* S := RingEquiv.refl S

variable {Xo : Moduli Dw l}

def ptDown (h : c.F ≤ c'.F) {S : Type} [CommRing S] [Algebra c'.F S] (y : FrPt Xo c' S) :
    FrPt Xo c (Res h S) where
  x := y.x
  x_over := y.x_over
  u := y.u
  tan := y.tan
  eig := y.eig
  basis := y.basis
  s := y.s
  gen := y.gen

def ptUp (h : c.F ≤ c'.F) {S : Type} [CommRing S] [Algebra c'.F S] (y : FrPt Xo c (Res h S)) :
    FrPt Xo c' S where
  x := y.x
  x_over := y.x_over
  u := y.u
  tan := y.tan
  eig := y.eig
  basis := y.basis
  s := y.s
  gen := y.gen

def embRes (h : c.F ≤ c'.F) (σ' : c'.F →+* ℂ) : c.F →+* ℂ := σ'.comp (incl h)

variable {r : ℕ}

def unfUp (h : c.F ≤ c'.F) (σ' : c'.F →+* ℂ) (U : Unf Xo c (embRes h σ') r) : Unf Xo c' σ' r where
  Comp := U.Comp
  fin := U.fin
  X := U.X
  un k x := ptUp h (S := CAt σ') (U.un k x)

def unfFamUp (h : c.F ≤ c'.F) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : ∀ σ' : c'.F →+* ℂ, Unf Xo c' σ' r :=
  fun σ' => unfUp h σ' (U (embRes h σ'))

def ruleUp (h : c.F ≤ c'.F) : Rul Xo c →ₛₗ[incl h] Rul Xo c' where
  toFun f := fun p y => unRes (evR Xo c f (ptDown h y))
  map_add' f g := by
    funext p y
    exact evalAt_add (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f g (ptDown h y)
  map_smul' a f := by
    funext p y
    have e := evalAt_smul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) a f (ptDown h y)
    show _ = incl h a • (unRes (evR Xo c f (ptDown h y)) : p.R)
    exact e.trans (Algebra.smul_def (incl h a) (unRes (evR Xo c f (ptDown h y)) : p.R)).symm

def IsComb (h : c.F ≤ c'.F) {m : ℕ} (b : Fin m → c'.F) (f : Fin m → Rul Xo c) (f' : Rul Xo c') : Prop :=
  ∀ (p : TRing c'.F) (y : FrPt Xo c' p.R),
    f' p y = ∑ i, algebraMap c'.F p.R (b i) * unRes (evR Xo c (f i) (ptDown h y))


variable (Xo)

def ActionExtends (h : c.F ≤ c'.F) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    {G : Type} [Group G] (ρ : G →* Module.End c.F (cusp Xo c U a n))
    (ρ' : G →* Module.End c'.F (cusp Xo c' (unfFamUp h U) a n)) : Prop :=
  ∀ (g : G) (m : ℕ) (b : Fin m → c'.F) (f : Fin m → cusp Xo c U a n) (f' : cusp Xo c' (unfFamUp h U) a n),
    IsComb h b (fun i => (f i : Rul Xo c)) (f' : Rul Xo c') →
      IsComb h b (fun i => (ρ g (f i) : Rul Xo c)) (ρ' g f' : Rul Xo c')

end GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing
end
end
