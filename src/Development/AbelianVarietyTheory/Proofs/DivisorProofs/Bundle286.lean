module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle160
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.CharP.Algebra

@[expose] public section

section

open NumberField
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.LatFibre

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.SlopeTestRemainingChoices.EisFibre

variable {F : Type} [Field F] [NumberField F]

theorem unit_eq_one_of_mul {ε : (𝓞 F)ˣ} {b : F} (hb : b ≠ 0) (h : ((ε : 𝓞 F) : F) * b = b) : ε = 1 := by
  have h1 : ((ε : 𝓞 F) : F) = 1 := mul_right_cancel₀ hb (by rw [h, one_mul])
  apply Units.ext
  apply RingOfIntegers.coe_injective
  simp [h1]

def pairOf {𝔞 𝔟 : Frac F} (x : Σ _β : NzCls 𝔟, (latM 𝔞 : Set F)) : LatPair 𝔞 𝔟 :=
  ⟨((x.2 : F), rep x.1), x.2.2, rep_mem x.1, fun h => rep_ne_zero x.1 (congrArg Prod.snd h)⟩

theorem out_mk {𝔞 𝔟 : Frac F} (p : LatPair 𝔞 𝔟) :
    ∃ ε : (𝓞 F)ˣ, (Quotient.mk (latRel 𝔞 𝔟) p).out.1.1 = ((ε : 𝓞 F) : F) * p.1.1 ∧
      (Quotient.mk (latRel 𝔞 𝔟) p).out.1.2 = ((ε : 𝓞 F) : F) * p.1.2 :=
  Quotient.exact (Quotient.out_eq (Quotient.mk (latRel 𝔞 𝔟) p)).symm

private lemma ringOfIntegers_unit_coe_ne_zero (ε : (𝓞 F)ˣ) : ((ε : 𝓞 F) : F) ≠ 0 :=
  right_ne_zero_of_mul_eq_one (unit_inv_mul ε)

theorem out_mk_ne {𝔞 𝔟 : Frac F} (x : Σ _β : NzCls 𝔟, (latM 𝔞 : Set F)) :
    (Quotient.mk (latRel 𝔞 𝔟) (pairOf x)).out.1.2 ≠ 0 := by
  obtain ⟨ε, -, h2⟩ := out_mk (pairOf x)
  rw [h2]
  exact mul_ne_zero (ringOfIntegers_unit_coe_ne_zero ε) (rep_ne_zero x.1)

def fibreMap (𝔞 𝔟 : Frac F) (x : Σ _β : NzCls 𝔟, (latM 𝔞 : Set F)) :
    {c : Quotient (latRel 𝔞 𝔟) // c.out.1.2 ≠ 0} :=
  ⟨Quotient.mk _ (pairOf x), out_mk_ne x⟩

theorem fibreMap_injective (𝔞 𝔟 : Frac F) : Function.Injective (fibreMap 𝔞 𝔟) := by
  rintro ⟨β, a⟩ ⟨β', a'⟩ h
  have h' : Quotient.mk (latRel 𝔞 𝔟) (pairOf ⟨β, a⟩) = Quotient.mk (latRel 𝔞 𝔟) (pairOf ⟨β', a'⟩) :=
    congrArg Subtype.val h
  obtain ⟨ε, h1, h2⟩ := Quotient.exact h'
  have hβ : β = β' :=
    (Quotient.out_eq (s := unitRel 𝔟) β).symm.trans
      ((Quotient.sound (s := unitRel 𝔟) (a := Quotient.out (s := unitRel 𝔟) β)
        (b := Quotient.out (s := unitRel 𝔟) β') ⟨ε, h2⟩).trans (Quotient.out_eq (s := unitRel 𝔟) β'))
  subst hβ
  have hε : ε = 1 := unit_eq_one_of_mul (rep_ne_zero β) h2.symm
  subst hε
  have haa : a = a' := Subtype.ext (by simpa [pairOf] using h1.symm)
  subst haa
  rfl

theorem fibreMap_surjective (𝔞 𝔟 : Frac F) : Function.Surjective (fibreMap 𝔞 𝔟) := by
  rintro ⟨c, hc⟩
  let b : NzElt 𝔟 := ⟨c.out.1.2, c.out.2.2.1, hc⟩
  obtain ⟨ε, hε⟩ : ∃ ε : (𝓞 F)ˣ,
      rep (Quotient.mk (unitRel 𝔟) b : NzCls 𝔟) = ((ε : 𝓞 F) : F) * c.out.1.2 :=
    Quotient.exact (Quotient.out_eq (Quotient.mk (unitRel 𝔟) b)).symm
  have ha : ((ε : 𝓞 F) : F) * c.out.1.1 ∈ latM 𝔞 := by
    have hs := (latM 𝔞 : Submodule (𝓞 F) F).smul_mem (ε : 𝓞 F) c.out.2.1
    rwa [Algebra.smul_def] at hs
  refine ⟨⟨(Quotient.mk (unitRel 𝔟) b : NzCls 𝔟), ⟨_, ha⟩⟩, ?_⟩
  apply Subtype.ext
  show Quotient.mk (latRel 𝔞 𝔟) (pairOf _) = c
  conv_rhs => rw [← Quotient.out_eq c]
  exact (Quotient.sound (s := latRel 𝔞 𝔟) (a := c.out) ⟨ε, rfl, hε⟩).symm

theorem exists_equiv : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F),
    ∃ e : (Σ _β : GlobalTheory.SlopeTestRemainingChoices.EisFibre.NzCls 𝔟, (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 : Set F)) ≃
      {c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) // c.out.1.2 ≠ 0},
      ∀ (k : ℕ), Even k → ∀ (σ : ℂ) (z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) (x : Σ _β : GlobalTheory.SlopeTestRemainingChoices.EisFibre.NzCls 𝔟, (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 : Set F)),
        GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k σ z (e x).1 = GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm k σ z ((x.2 : F), GlobalTheory.SlopeTestRemainingChoices.EisFibre.rep x.1) := by
  intro F _ _ _ 𝔞 𝔟
  refine ⟨Equiv.ofBijective (fibreMap 𝔞 𝔟) ⟨fibreMap_injective 𝔞 𝔟, fibreMap_surjective 𝔞 𝔟⟩, ?_⟩
  intro k hk σ z x
  exact eisClass_mk 𝔞 𝔟 hk σ z (pairOf x)

end GlobalTheory.LatFibre
end
end

section

open NumberField
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.Div.QFibre

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.SlopeTestRemainingChoices.EisFibre

variable {F : Type} [Field F] [NumberField F]

theorem unit_mul_mem (𝔞 : Frac F) (ε : (𝓞 F)ˣ) {x : F} (hx : x ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F)) :
    ((ε : 𝓞 F) : F) * x ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) := by
  have := Submodule.smul_mem (𝔞 : FractionalIdeal (𝓞 F)⁰ F).coeToSubmodule (ε : 𝓞 F) hx
  rw [Algebra.smul_def] at this
  exact this

def toQ (𝔞 𝔟 : Frac F) (x : Σ β : NzCls 𝔟, posCone 𝔞 (rep β)) : Quotient (qRel 𝔞 𝔟) :=
  Quotient.mk _ ⟨(x.2.1, rep x.1), x.2.2.1, rep_mem x.1, x.2.2.2⟩

theorem toQ_injective (𝔞 𝔟 : Frac F) : Function.Injective (toQ 𝔞 𝔟) := by
  rintro ⟨β, ν, hν⟩ ⟨β', ν', hν'⟩ h
  obtain ⟨ε, h1, h2⟩ := Quotient.exact h
  simp only at h1 h2
  have hβ : β = β' := by
    rw [← Quotient.out_eq β, ← Quotient.out_eq β']
    exact Quotient.sound ⟨ε, h2⟩
  subst hβ
  have hε : ((ε : 𝓞 F) : F) = 1 := by
    have h0 := rep_ne_zero β
    have : (((ε : 𝓞 F) : F) - 1) * rep β = 0 := by unfold rep at h2 ⊢; rw [sub_mul, ← h2]; ring
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right h0)
  have hε' : (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = 1 := by
    have := unit_inv_mul ε; rw [hε, mul_one] at this; exact this
  rw [hε', one_mul] at h1
  have : (⟨ν, hν⟩ : posCone 𝔞 (rep β)) = ⟨ν', hν'⟩ := Subtype.ext h1.symm
  rw [this]

theorem exists_emb [IsTotallyReal F] : Nonempty (Emb F) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  exact ⟨(IsTotallyReal.complexEmbedding_isReal w.embedding).embedding⟩

theorem toQ_surjective [IsTotallyReal F] (𝔞 𝔟 : Frac F) : Function.Surjective (toQ 𝔞 𝔟) := by
  intro c
  induction c using Quotient.ind with
  | _ p =>
  obtain ⟨⟨ν, b⟩, hν, hb, hpos⟩ := p
  have hb0 : b ≠ 0 := by
    rintro rfl
    obtain ⟨τ⟩ := exists_emb (F := F)
    have := hpos τ; simp at this
  let β : NzCls 𝔟 := Quotient.mk _ ⟨b, hb, hb0⟩
  obtain ⟨ε, hε⟩ : (unitRel 𝔟).r (Quotient.out β) ⟨b, hb, hb0⟩ := Quotient.exact (Quotient.out_eq β)
  have h4 := unit_inv_mul ε
  have hrep : rep β = (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * b := by
    unfold rep; simp only at hε; rw [hε, ← mul_assoc, h4, one_mul]
  have hprod : ((ε : 𝓞 F) : F) * ν * rep β = ν * b := by
    rw [hrep]; linear_combination (ν * b) * h4
  refine ⟨⟨β, ((ε : 𝓞 F) : F) * ν, unit_mul_mem 𝔞 ε hν, fun τ => by rw [hprod]; exact hpos τ⟩, ?_⟩
  apply Quotient.sound
  refine ⟨ε, ?_, ?_⟩
  · show ν = _ * (((ε : 𝓞 F) : F) * ν)
    rw [← mul_assoc, h4, one_mul]
  · show b = ((ε : 𝓞 F) : F) * rep β
    rw [hrep, ← mul_assoc, mul_comm ((ε : 𝓞 F) : F), h4, one_mul]

theorem qFibres : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F),
    ∃ e : (Σ β : GlobalTheory.SlopeTestRemainingChoices.EisFibre.NzCls 𝔟, GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 (GlobalTheory.SlopeTestRemainingChoices.EisFibre.rep β)) ≃ Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qRel 𝔞 𝔟),
      ∀ (k : ℕ) (z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) (x : Σ β : GlobalTheory.SlopeTestRemainingChoices.EisFibre.NzCls 𝔟, GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 (GlobalTheory.SlopeTestRemainingChoices.EisFibre.rep β)),
        GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 k z (e x) = GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qTerm 𝔞 k z (x.2.1, GlobalTheory.SlopeTestRemainingChoices.EisFibre.rep x.1) := by
  intro F _ _ _ 𝔞 𝔟
  refine ⟨Equiv.ofBijective (toQ 𝔞 𝔟) ⟨toQ_injective 𝔞 𝔟, toQ_surjective 𝔞 𝔟⟩, fun k z x => ?_⟩
  exact qClass_mk 𝔞 𝔟 k z _

end GlobalTheory.Div.QFibre
end
end

section

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.AdeleZ

open Rat.HeightOneSpectrum GlobalTheory.NormLevelCompare

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

theorem padic_ccast {p q : Nat.Primes} (h : p = q) :
    ∃ e : ℚ_[p] ≃A[ℚ] ℚ_[q], ∀ x, e x ∈ PadicInt.subring q ↔ x ∈ PadicInt.subring p := by
  subst h
  exact ⟨ContinuousAlgEquiv.refl ℚ _, fun _ => Iff.rfl⟩

theorem exists_clocal (w : HeightOneSpectrum ℤ) :
    ∃ e : (primeCorr w).adicCompletion ℚ ≃A[ℚ] w.adicCompletion ℚ,
      ∀ x, e x ∈ w.adicCompletionIntegers ℚ ↔ x ∈ (primeCorr w).adicCompletionIntegers ℚ := by
  have h : primesEquiv (primeCorr w) = primesEquiv w := by simp [primeCorr]
  obtain ⟨c, hc⟩ := padic_ccast h
  refine ⟨((adicCompletion.padicEquiv (primeCorr w)).trans c).trans
    (adicCompletion.padicEquiv w).symm, fun x => ?_⟩
  rw [← padicEquiv_mem w, ← padicEquiv_mem (primeCorr w), ← hc]
  change adicCompletion.padicEquiv w ((adicCompletion.padicEquiv w).symm _) ∈ _ ↔ _
  rw [ContinuousAlgEquiv.apply_symm_apply]
  rfl

variable (e : ∀ w : HeightOneSpectrum ℤ, (primeCorr w).adicCompletion ℚ ≃A[ℚ] w.adicCompletion ℚ)
  (he : ∀ w x, e w x ∈ w.adicCompletionIntegers ℚ ↔ x ∈ (primeCorr w).adicCompletionIntegers ℚ)

theorem tendsto_primeCorr : Filter.Tendsto primeCorr Filter.cofinite Filter.cofinite :=
  primeCorr.injective.tendsto_cofinite

include he in
theorem maps_int : ∀ᶠ w in Filter.cofinite, Set.MapsTo
    (fun x => ((e w).toRingHom : (primeCorr w).adicCompletion ℚ →+* w.adicCompletion ℚ) x)
      ((primeCorr w).adicCompletionIntegers ℚ) (w.adicCompletionIntegers ℚ) :=
  .of_forall fun w x hx => (he w x).2 hx

def adeleMap : FiniteAdeleRing (𝓞 ℚ) ℚ →+* FiniteAdeleRing ℤ ℚ :=
  RestrictedProduct.mapAlongRingHom (fun v : HeightOneSpectrum (𝓞 ℚ) => v.adicCompletion ℚ)
      (fun w : HeightOneSpectrum ℤ => w.adicCompletion ℚ)
      (B₁ := fun v => v.adicCompletionIntegers ℚ) (B₂ := fun w => w.adicCompletionIntegers ℚ)
      primeCorr tendsto_primeCorr (fun w => (e w).toRingHom) (maps_int e he)

theorem continuous_adeleMap : Continuous (adeleMap e he) :=
  RestrictedProduct.mapAlong_continuous _ _ primeCorr tendsto_primeCorr _ (maps_int e he)
    fun w => (e w).continuous

def adeleAlgHom : FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] FiniteAdeleRing ℤ ℚ where
  toFun a := ⟨fun w => e w (a (primeCorr w)), by
    have h1 := primeCorr.injective.tendsto_cofinite.eventually a.2
    exact h1.mono fun w hw => (he w _).2 hw⟩
  map_one' := FiniteAdeleRing.ext _ fun w => map_one (e w)
  map_mul' := fun a b => FiniteAdeleRing.ext _ fun w => map_mul (e w) _ _
  map_zero' := FiniteAdeleRing.ext _ fun w => map_zero (e w)
  map_add' := fun a b => FiniteAdeleRing.ext _ fun w => map_add (e w) _ _
  commutes' := fun r => FiniteAdeleRing.ext _ fun w => (e w).commutes r

theorem adeleAlgHom_apply (a : FiniteAdeleRing (𝓞 ℚ) ℚ) (w : HeightOneSpectrum ℤ) :
    adeleAlgHom e he a w = e w (a (primeCorr w)) := rfl

theorem adeleAlgHom_eq : ⇑(adeleAlgHom e he) = ⇑(adeleMap e he) := by
  funext a
  exact FiniteAdeleRing.ext _ fun w => rfl

theorem adeleAlgHom_injective : Function.Injective (adeleAlgHom e he) := by
  intro a b hab
  refine FiniteAdeleRing.ext _ fun v => ?_
  obtain ⟨w, rfl⟩ := primeCorr.surjective v
  have h := congrArg (fun x : FiniteAdeleRing ℤ ℚ => x w) hab
  simp only [adeleAlgHom_apply] at h
  exact (e w).injective h

theorem adeleAlgHom_surjective : Function.Surjective (adeleAlgHom e he) := by
  intro b
  obtain ⟨f, hf⟩ : ∃ f : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletion ℚ,
      ∀ w, f (primeCorr w) = (e w).symm (b w) :=
    ⟨_, fun w => Equiv.piCongrLeft_apply_apply
      (fun v : HeightOneSpectrum (𝓞 ℚ) => v.adicCompletion ℚ) primeCorr
      (fun w => (e w).symm (b w)) w⟩
  have hfi : ∀ᶠ v in Filter.cofinite, f v ∈ v.adicCompletionIntegers ℚ := by
    have h1 := primeCorr.symm.injective.tendsto_cofinite.eventually b.2
    refine h1.mono fun v hv => ?_
    obtain ⟨w, rfl⟩ := primeCorr.surjective v
    rw [Equiv.symm_apply_apply] at hv
    rw [hf, ← he, ContinuousAlgEquiv.apply_symm_apply]
    exact hv
  obtain ⟨a, ha⟩ : ∃ a : FiniteAdeleRing (𝓞 ℚ) ℚ, ∀ v, a v = f v := ⟨⟨f, hfi⟩, fun _ => rfl⟩
  refine ⟨a, FiniteAdeleRing.ext _ fun w => ?_⟩
  rw [adeleAlgHom_apply, ha, hf, ContinuousAlgEquiv.apply_symm_apply]


omit e he in
theorem exists_continuous_adele_equiv :
    ∃ e : FiniteAdeleRing (𝓞 ℚ) ℚ ≃ₐ[ℚ] FiniteAdeleRing ℤ ℚ, Continuous e := by
  choose e he using exists_clocal
  refine ⟨AlgEquiv.ofBijective (adeleAlgHom e he)
    ⟨adeleAlgHom_injective e he, adeleAlgHom_surjective e he⟩, ?_⟩
  change Continuous (adeleAlgHom e he)
  rw [adeleAlgHom_eq]
  exact continuous_adeleMap e he

end GlobalTheory.AdeleZ
end
end

section

open GlobalTheory.UnitLemma Polynomial Matrix

namespace GlobalTheory.InertUnitOrb

theorem conj_of_norm_class (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ)
    (γ γ' : Matrix (Fin n) (Fin n) K.E) (x x' v : B.Aˣ) (ψ ψ' : B.A ≃ₗ[K.E] (Fin n → K.E))
    (h : GlobalTheory.InertUnitOrb.IsModel B γ x ψ) (h' : GlobalTheory.InertUnitOrb.IsModel B γ' x' ψ')
    (hx : (x' : B.A) = x * (v * B.σ v)) :
    ∃ u : Matrix (Fin n) (Fin n) K.E, (u.map K.c)ᵀ * u = 1 ∧ γ * u = u * γ' := by
  obtain ⟨-, hg, hh⟩ := h
  obtain ⟨-, hg', hh'⟩ := h'
  set f : (Fin n → K.E) →ₗ[K.E] (Fin n → K.E) :=
    ψ.toLinearMap ∘ₗ LinearMap.mulLeft K.E (v : B.A) ∘ₗ ψ'.symm.toLinearMap with hf
  have key : ∀ a b, stdH K n (f a) (f b) = stdH K n a b := by
    intro a b
    obtain ⟨y, rfl⟩ := ψ'.surjective a
    obtain ⟨z, rfl⟩ := ψ'.surjective b
    simp only [hf, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.mulLeft_apply]
    rw [hh, hh', hx]
    unfold InvAlg.herm
    congr 1
    rw [map_mul]
    ring
  refine ⟨LinearMap.toMatrix' f, ?_, ?_⟩
  · ext i j
    have k := key (Pi.single j 1) (Pi.single i 1)
    simp only [stdH] at k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, LinearMap.toMatrix'_apply,
      Matrix.one_apply]
    rw [show (∑ x, K.c (f (Pi.single i 1) x) * f (Pi.single j 1) x)
        = ∑ x, f (Pi.single j 1) x * K.c (f (Pi.single i 1) x) from
        Finset.sum_congr rfl fun _ _ => mul_comm _ _, k]
    simp [Pi.single_apply, eq_comm]
  · apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
    refine LinearMap.ext fun a => ?_
    obtain ⟨y, rfl⟩ := ψ'.surjective a
    simp only [hf, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.mulLeft_apply, Matrix.toLin'_apply]
    rw [← hg, ← hg', LinearEquiv.symm_apply_apply, ← mul_assoc, ← mul_assoc, mul_comm B.g]

end GlobalTheory.InertUnitOrb
end

section

open GlobalTheory.UnitLemma Polynomial Matrix

noncomputable section

namespace GlobalTheory.ModelCharpoly
open GlobalTheory.InertUnitOrb

theorem charpoly_eq (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (γ : Matrix (Fin n) (Fin n) K.E)
    (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)) (h : ∀ y, ψ (B.g * y) = γ *ᵥ ψ y) : γ.charpoly = B.P := by
  let b : Module.Basis (Fin n) K.E B.A := (Pi.basisFun K.E (Fin n)).map ψ.symm
  have hm : LinearMap.toMatrix b b (LinearMap.mulLeft K.E B.g) = γ := by
    ext i j
    simp [b, LinearMap.toMatrix_apply, h]
  rw [InvAlg.P, ← LinearMap.charpoly_toMatrix (LinearMap.mulLeft K.E B.g) b, hm]

theorem unitary (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (γ : Matrix (Fin n) (Fin n) K.E)
    (x : B.Aˣ) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)) (h : ∀ y, ψ (B.g * y) = γ *ᵥ ψ y)
    (hh : ∀ y z, stdH K n (ψ y) (ψ z) = B.herm x y z) (hg : B.g * B.σ B.g = 1) :
    (γ.map K.c)ᵀ * γ = 1 := by
  have key : ∀ a b : Fin n → K.E, stdH K n (γ *ᵥ a) (γ *ᵥ b) = stdH K n a b := by
    intro a b
    obtain ⟨y, rfl⟩ := ψ.surjective a
    obtain ⟨z, rfl⟩ := ψ.surjective b
    rw [← h, ← h, hh, hh, InvAlg.herm, InvAlg.herm]
    congr 1
    rw [map_mul B.σ]
    calc (x : B.A) * (B.g * y) * (B.σ B.g * B.σ z) = (x : B.A) * y * B.σ z * (B.g * B.σ B.g) := by ring
      _ = _ := by rw [hg, mul_one]
  ext i j
  have := key (Pi.single j 1) (Pi.single i 1)
  simp [stdH, Matrix.mulVec_single, Pi.single_apply, Matrix.mul_apply, Matrix.one_apply, mul_comm] at this
  simp [Matrix.mul_apply, Matrix.one_apply]
  simpa [mul_comm, eq_comm] using this

theorem model_charpoly_unitary : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ)
    (γ : Matrix (Fin n) (Fin n) K.E) (x : B.Aˣ) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)),
    GlobalTheory.InertUnitOrb.IsModel B γ x ψ → γ.charpoly = B.P ∧ (B.g * B.σ B.g = 1 → (γ.map K.c)ᵀ * γ = 1) := by
  intro K B n γ x ψ hM
  exact ⟨charpoly_eq K B n γ ψ hM.2.1, unitary K B n γ x ψ hM.2.1 hM.2.2⟩

end GlobalTheory.ModelCharpoly

end
end

section

noncomputable section

open IsDedekindDomain GlobalTheory.LKTrip
open scoped TensorProduct

namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

def iotaF (G : HTGroup p) (v : AwayP p) : Qv v ⊗[ℚ] G.F →ₐ[Qv v] Qv v ⊗[ℚ] G.C :=
  Algebra.TensorProduct.map (AlgHom.id (Qv v) (Qv v)) (IsScalarTower.toAlgHom ℚ G.F G.C)

theorem iotaF_tmul (G : HTGroup p) (v : AwayP p) (a : Qv v) (x : G.F) :
    iotaF G v (a ⊗ₜ[ℚ] x) = a ⊗ₜ[ℚ] algebraMap G.F G.C x := rfl

theorem isIntV_zero (G : HTGroup p) (v : AwayP p) : IsIntV G v 0 := fun i => by
  rw [map_zero, Finsupp.zero_apply]; exact zero_mem _

theorem isIntV_add' (G : HTGroup p) (v : AwayP p) {a b : Qv v ⊗[ℚ] G.C} (ha : IsIntV G v a)
    (hb : IsIntV G v b) : IsIntV G v (a + b) := fun i => by
  rw [map_add (f := _), Finsupp.add_apply]; exact add_mem (ha i) (hb i)

theorem isIntV_neg (G : HTGroup p) (v : AwayP p) {a : Qv v ⊗[ℚ] G.C} (ha : IsIntV G v a) :
    IsIntV G v (-a) := fun i => by
  rw [map_neg, Finsupp.neg_apply]; exact neg_mem (ha i)

theorem isIntV_sum (G : HTGroup p) (v : AwayP p) {ι : Type*} (s : Finset ι) (f : ι → Qv v ⊗[ℚ] G.C)
    (h : ∀ i ∈ s, IsIntV G v (f i)) : IsIntV G v (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact isIntV_zero G v
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isIntV_add' G v (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

def intF (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1)
    (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) :
    Subring (Qv v ⊗[ℚ] G.F) where
  carrier := {m | IsIntV G v (iotaF G v m)}
  one_mem' := by simp only [Set.mem_setOf_eq, map_one]; exact h1
  mul_mem' {a b} ha hb := by simp only [Set.mem_setOf_eq, map_mul] at *; exact hm _ _ ha hb
  zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]; exact isIntV_zero G v
  add_mem' {a b} ha hb := by simp only [Set.mem_setOf_eq, map_add (f := _)] at *; exact isIntV_add' G v ha hb
  neg_mem' {a} ha := by simp only [Set.mem_setOf_eq, map_neg] at *; exact isIntV_neg G v ha

theorem mem_intF (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1)
    (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) (m : Qv v ⊗[ℚ] G.F) :
    m ∈ intF G v h1 hm ↔ IsIntV G v (iotaF G v m) := Iff.rfl

end GlobalTheory.OrbFinAf
end
end

section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.charZero_stalk_imageOfGenericPoint : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y], CharZero Γ(Y, ⊤) →
    ∀ (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))),
    letI := GlobalTheory.NormSheafDescent.fieldK π hK;
    CharZero (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) := by
  intro Y Z π _ hY hK
  have : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  have hL : CharZero Y.functionField :=
    charZero_of_injective_ringHom (f := (Y.germToFunctionField ⊤).hom)
      (Y.germToFunctionField_injective ⊤)
  exact (π.stalkMap (genericPoint Y)).hom.charZero
end
