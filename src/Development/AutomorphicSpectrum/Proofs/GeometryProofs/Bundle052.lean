module

import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharacterSectionMultiplicative
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmTypeEigenMultiplicityOfDensePrimes
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfSec
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle008
public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle038
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle037
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.TranslateEq

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT
open scoped TensorProduct

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

theorem valAt_top {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (s : Γ(X, ⊤)) :
    valAt x ⊤ le_top s = (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (x.appTop.hom s) := by
  have hle : x.appLE ⊤ ⊤ le_top = x.appTop := by
    simp only [Scheme.Hom.appLE]
    exact Category.comp_id _
  simp only [valAt]
  rw [hle]

theorem chart_sep [Finite T] (Γ : QFGroup R T) (B : Type) [CommRing B] [Algebra R B]
    (c : Spec (CommRingCat.of B) ⟶ Γ.G.left) [IsOpenImmersion c]
    (hc : c ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R B))) :
    ∃ (I : Type) (_ : Finite I) (τ : I → T) (e : I → B →ₐ[R] FractionRing R),
      (∀ i, Spec.map (CommRingCat.ofHom (e i).toRingHom) ≫ c = (Γ.pt (τ i)).left) ∧
      ∀ b, (∀ i, e i b = 0) → b = 0 := by
  apply GlobalTheory.CompanionTheory.Ar.BT.CharMul.chart_sep <;> assumption

theorem sec_zero [Finite T] (Γ : QFGroup R T) (s : Γ(Γ.G.left, ⊤))
    (hs : ∀ t, valAt (Γ.pt t).left ⊤ le_top s = 0) : s = 0 := by
  let 𝒰 := Γ.G.left.affineOpenCover
  refine Scheme.OpenCover.ext_elem s 0 𝒰.openCover fun k => ?_
  rw [map_zero]
  let c : Spec (CommRingCat.of (𝒰.X k)) ⟶ Γ.G.left := 𝒰.f k
  haveI : IsOpenImmersion c := 𝒰.openCover.map_prop k
  letI : Algebra R (𝒰.X k) := (Spec.preimage (c ≫ Γ.G.hom)).hom.toAlgebra
  obtain ⟨I, _, τ, e, he, hi⟩ := chart_sep Γ (𝒰.X k) c (Spec.map_preimage (c ≫ Γ.G.hom)).symm
  have h0 := hi ((Scheme.ΓSpecIso (CommRingCat.of (𝒰.X k))).hom (c.appTop s)) fun i => by
    have h1 := hs (τ i)
    rw [← he i, valAt_top, Scheme.Hom.comp_appTop] at h1
    exact (congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (e i).toRingHom)) (c.appTop s))).symm.trans h1
  have h2 := congr((Scheme.ΓSpecIso (CommRingCat.of (𝒰.X k))).inv $h0)
  rw [Iso.hom_inv_id_apply, map_zero] at h2
  exact h2

def pullSec {A : Type} [CommRing A] {X : Scheme.{0}} (j : X ⟶ Spec (CommRingCat.of A)) (f : A) : Γ(X, ⊤) :=
  j.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom f)

theorem valAt_sub' {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X)
    (a b : Γ(X, ⊤)) : valAt x ⊤ le_top (a - b) = valAt x ⊤ le_top a - valAt x ⊤ le_top b := by
  simp only [valAt_top, map_sub]

theorem valAt_mul {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) : valAt x U h (a * b) = valAt x U h a * valAt x U h b := by
  simp [valAt]

section Omega

variable (Γ : QFGroup R T) {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S}
  (i : Γ.G.left ⟶ G.left) {L : Type} [AddCommGroup L] [Module R L] (M : LieModel G x L) (N : ℕ)


end Omega


end GlobalTheory.CompanionTheory.Ar.BT.TranslateEq
end
end

section

open NumberField GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.EigExact

theorem mem_eigSp_iff {k V O : Type} [Field k] [AddCommGroup V] [Module k V] [CommRing O]
    {ρ : O →+* Module.End k V} {τ : O →+* k} {x : V} : x ∈ eigSp ρ τ ↔ ∀ a, ρ a x = τ a • x := by
  simp [eigSp, sub_eq_zero]

theorem eigSp_eq_eigenSub {k V O : Type} [Field k] [AddCommGroup V] [Module k V] [CommRing O]
    (ρ : O →+* Module.End k V) (τ : O →+* k) : eigSp ρ τ = EigenSplit.eigenSub ρ τ := by
  ext x
  rw [mem_eigSp_iff, EigenSplit.mem_eigenSub]

theorem map_eigSp_eq {E : Type} [Field E] [NumberField E] {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {V₂ V₃ : Type} [AddCommGroup V₂] [Module k V₂] [AddCommGroup V₃] [Module k V₃]
    {ρ₂ : 𝓞 E →+* Module.End k V₂} {ρ₃ : 𝓞 E →+* Module.End k V₃} {g : V₂ →ₗ[k] V₃}
    (hg : Function.Surjective g) (hgρ : ∀ a x, g (ρ₂ a x) = ρ₃ a (g x)) (τ : 𝓞 E →+* k) :
    (eigSp ρ₂ τ).map g = eigSp ρ₃ τ := by
  classical
  obtain ⟨φ, rfl⟩ := GlobalTheory.TraceSpread.exists_embedding τ
  have hs := GlobalTheory.TraceSpread.isSplitting_embeddings (E := E) k
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_eigSp_iff] at hx
    rw [mem_eigSp_iff]
    intro a
    rw [← hgρ, hx, map_smul]
  · intro y hy
    obtain ⟨x, rfl⟩ := hg y
    rw [eigSp_eq_eigenSub] at hy
    refine ⟨EigenSplit.proj hs ρ₂ φ x, ?_, ?_⟩
    · rw [SetLike.mem_coe, eigSp_eq_eigenSub]
      exact EigenSplit.proj_mem hs ρ₂ φ x
    · have he : EigenSplit.IsEquivariant ρ₂ ρ₃ g := hgρ
      rw [he.proj hs φ x]
      exact EigenSplit.proj_of_mem hs hy

theorem eigSp_inf_ker {O k V₁ V₂ V₃ : Type} [CommRing O] [Field k] [AddCommGroup V₁] [Module k V₁]
    [AddCommGroup V₂] [Module k V₂] [AddCommGroup V₃] [Module k V₃]
    {ρ₁ : O →+* Module.End k V₁} {ρ₂ : O →+* Module.End k V₂} {f : V₁ →ₗ[k] V₂} {g : V₂ →ₗ[k] V₃}
    (hf : Function.Injective f) (hfg : LinearMap.range f = LinearMap.ker g)
    (hfρ : ∀ a x, f (ρ₁ a x) = ρ₂ a (f x)) (τ : O →+* k) :
    eigSp ρ₂ τ ⊓ LinearMap.ker g = (eigSp ρ₁ τ).map f := by
  apply le_antisymm
  · rintro x ⟨hx, hk⟩
    rw [SetLike.mem_coe, mem_eigSp_iff] at hx
    have hk' : x ∈ LinearMap.range f := by rw [hfg]; exact hk
    obtain ⟨z, rfl⟩ := hk'
    refine ⟨z, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_eigSp_iff]
    intro a
    apply hf
    rw [hfρ, hx, map_smul]
  · rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, mem_eigSp_iff] at hz
    refine ⟨?_, ?_⟩
    · rw [SetLike.mem_coe, mem_eigSp_iff]
      intro a
      rw [← hfρ, hz, map_smul]
    · change f z ∈ LinearMap.ker g
      rw [← hfg]
      exact ⟨z, rfl⟩

theorem finrank_map_add_inf_ker {k V W : Type} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (g : V →ₗ[k] W) (S : Submodule k V) [FiniteDimensional k S] :
    Module.finrank k (S.map g) + Module.finrank k ↥(S ⊓ LinearMap.ker g) = Module.finrank k S := by
  have h := LinearMap.finrank_range_add_finrank_ker (g.domRestrict S)
  rw [LinearMap.range_domRestrict] at h
  rw [← h, LinearMap.ker_domRestrict, ← Submodule.finrank_map_subtype_eq S (Submodule.comap S.subtype (LinearMap.ker g)),
    Submodule.map_comap_subtype]

theorem exists_basis_eigSp_quot : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (V₁ V₂ V₃ : Type) [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂] [AddCommGroup V₃] [Module k V₃] (ρ₁ : 𝓞 E →+* Module.End k V₁) (ρ₂ : 𝓞 E →+* Module.End k V₂) (ρ₃ : 𝓞 E →+* Module.End k V₃) (f : V₁ →ₗ[k] V₂) (g : V₂ →ₗ[k] V₃), Function.Injective f → Function.Surjective g → LinearMap.range f = LinearMap.ker g → (∀ a x, f (ρ₁ a x) = ρ₂ a (f x)) → (∀ a x, g (ρ₂ a x) = ρ₃ a (g x)) → ∀ (τ : 𝓞 E →+* k) (r n : ℕ) (b₁ : Fin r → V₁) (b₂ : Fin n → V₂), LinearIndependent k b₁ → Submodule.span k (Set.range b₁) = eigSp ρ₁ τ → LinearIndependent k b₂ → Submodule.span k (Set.range b₂) = eigSp ρ₂ τ → r ≤ n ∧ ∃ b₃ : Fin (n - r) → V₃, LinearIndependent k b₃ ∧ Submodule.span k (Set.range b₃) = eigSp ρ₃ τ := by
  intro E _ _ k _ _ _ V₁ V₂ V₃ _ _ _ _ _ _ ρ₁ ρ₂ ρ₃ f g hf hg hfg hfρ hgρ τ r n b₁ b₂ hb₁ hs₁ hb₂ hs₂
  have hr : Module.finrank k (eigSp ρ₁ τ) = r := by
    rw [← hs₁, finrank_span_eq_card hb₁, Fintype.card_fin]
  have hn : Module.finrank k (eigSp ρ₂ τ) = n := by
    rw [← hs₂, finrank_span_eq_card hb₂, Fintype.card_fin]
  haveI : FiniteDimensional k (eigSp ρ₂ τ) := by
    rw [← hs₂]
    exact FiniteDimensional.span_of_finite k (Set.finite_range b₂)
  have hsum := finrank_map_add_inf_ker g (eigSp ρ₂ τ)
  rw [map_eigSp_eq hg hgρ τ, eigSp_inf_ker hf hfg hfρ τ, ← (Submodule.equivMapOfInjective f hf (eigSp ρ₁ τ)).finrank_eq, hr, hn] at hsum
  haveI : FiniteDimensional k (eigSp ρ₃ τ) := by
    rw [← map_eigSp_eq hg hgρ τ]
    infer_instance
  have h3 : Module.finrank k (eigSp ρ₃ τ) = n - r := by omega
  refine ⟨by omega, ?_⟩
  let B := Module.finBasisOfFinrankEq k (eigSp ρ₃ τ) h3
  refine ⟨fun i => (B i : V₃), ?_, ?_⟩
  · exact B.linearIndependent.map' (eigSp ρ₃ τ).subtype (Submodule.ker_subtype _)
  · have : Set.range (fun i => (B i : V₃)) = (eigSp ρ₃ τ).subtype '' Set.range B := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, B.span_eq, Submodule.map_top, Submodule.range_subtype]

end GlobalTheory.CompanionTheory.Ar.EigExact
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

abbrev OCp (p : Nat.Primes) : Type :=
  (NormedField.valuation (K := ℂ_[p])).valuationSubring

def inE {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) (τ : E →+* ℂ) :
    E →+* c.F := τ.codRestrict c.F.toSubfield (c.conj τ)

def stdLat (A C : Type) [CommRing A] [Field C] [Algebra A C] (g : ℕ) : Submodule A (Fin g → C) where
  carrier := {x | ∀ i, x i ∈ (algebraMap A C).range}
  add_mem' := fun ha hb i => add_mem (ha i) (hb i)
  zero_mem' := fun _ => zero_mem _
  smul_mem' := fun a x hx i => by
    rw [Pi.smul_apply, Algebra.smul_def]
    exact mul_mem ⟨a, rfl⟩ (hx i)

section Eval

variable {E : Type} [Field E] [NumberField E] {Ω : Type} [Field Ω] {Vs : Type} [AddCommGroup Vs] [Module Ω Vs]
  {C : Type} [Field C] {g : ℕ}

def comb {R : Subring Ω} (ℓ : Fin g → Vs) (x : Fin g → R) : Vs := ∑ i, (x i : Ω) • ℓ i

def Tied {R : Subring Ω} (ℓ : Fin g → Vs) (ψ : R →+* C) (ρ : 𝓞 E →+* Module.End Ω Vs)
    (ρC : 𝓞 E →+* Module.End C (Fin g → C)) : Prop :=
  ∀ (a : 𝓞 E) (x x' : Fin g → R), ρ a (comb ℓ x) = comb ℓ x' → ρC a (fun i => ψ (x i)) = fun i => ψ (x' i)

def HodgeAt {R : Subring Ω} {N : ℕ} (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (HL : Submodule R (Vs × Module.Dual Ω Vs)) (ℓ : Fin g → Vs) (t : Fin N → Vs × Module.Dual Ω Vs) : Prop :=
  HT.IsFreeOn ρH HL t ∧
    HL.map ((LinearMap.fst Ω Vs (Module.Dual Ω Vs)).restrictScalars R) = Submodule.span R (Set.range ℓ) ∧
    ∀ f : Module.Dual Ω Vs, ((0 : Vs), f) ∈ HL ↔ ∀ e ∈ Submodule.span R (Set.range ℓ), f e ∈ R

def IsEval {R : Subring Ω} (ℓ : Fin g → Vs) (ψ : R →+* C) (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (ρHC : 𝓞 E →+* Module.End C ((Fin g → C) × Module.Dual C (Fin g → C)))
    (HL : Submodule R (Vs × Module.Dual Ω Vs))
    (ev : HL →ₛₗ[ψ] (Fin g → C) × Module.Dual C (Fin g → C)) : Prop :=
  (∀ (a : 𝓞 E) (h : HL) (h' : ρH a (h : Vs × Module.Dual Ω Vs) ∈ HL), ev ⟨_, h'⟩ = ρHC a (ev h)) ∧
  (∀ (h : HL) (x : Fin g → R), (h : Vs × Module.Dual Ω Vs).1 = comb ℓ x → (ev h).1 = fun i => ψ (x i)) ∧
  (∀ (h : HL) (x : Fin g → R) (r : R), (h : Vs × Module.Dual Ω Vs).1 = 0 →
    (h : Vs × Module.Dual Ω Vs).2 (comb ℓ x) = r → (ev h).2 (fun i => ψ (x i)) = ψ r)

end Eval
end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.isFinOpenSub_of_finite : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (T : Type) [CommGroup T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), IsFinite (U.ι ≫ Γ.G.hom) → (∀ x : Γ.G.left, Γ.G.hom x = IsLocalRing.closedPoint R → x ∈ U) → Γ.IsFinOpenSub U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.QFGroup.isFinOpenSub_of_closedFibre | exact GlobalTheory.CompanionTheory.Ar.BT.QFGroup.isFinOpenSub_of_closedFibre | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.QFGroup.isFinOpenSub_of_closedFibre <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem mem_btOrder_iff_mem_btSet : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (f : T → R), f ∈ Γ.btOrder U ↔ f ∈ Γ.btSet U :=
  PositivityTheory.HtPt.Twhopf.mem_order

end GlobalTheory.CompanionTheory.Ar.BT
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_centre_of_isProper : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → ∀ V : ValuationSubring Ω, (∀ o : O, algebraMap O Ω o ∈ V) → ∃ p : Cpt ξ, regAt ξ p ≤ V.toSubring ∧ ∀ a ∈ regAt ξ p, a ≠ 0 → a⁻¹ ∈ V → ∃ g : X.presheaf.stalk p.1, IsUnit g ∧ genMap ξ p g = a :=
  @PositivityTheory.Xgn.valuation_centre_exists

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem _root_.GlobalTheory.T.generic_point_generic_fibre : ∀ (F : Type) [Field F] [NumberField F] (P : Scheme.{0}) (s : P ⟶ Sp (𝓞 F)) (Ω : Type) [Field Ω] [CharZero Ω] (ξ₀ : Sp Ω ⟶ P), IsCptGen ξ₀ → ∃ (b : F →+* Ω) (ξF : Sp Ω ⟶ pullback s (spMap (algebraMap (𝓞 F) F))), ξF ≫ pullback.fst _ _ = ξ₀ ∧ ξF ≫ pullback.snd _ _ = spMap b ∧ IsCptGen ξF := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GenFibre.exists_point | exact GlobalTheory.CompanionTheory.Ar.GenFibre.exists_point | (intros; apply GlobalTheory.CompanionTheory.Ar.GenFibre.exists_point <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.CharZeroModel

theorem charZero_of_flat {X : Scheme.{0}} {R : Type} [CommRing R] [IsDomain R] [CharZero R]
    (s : X ⟶ Spec (CommRingCat.of R)) [Flat s] {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (h : Function.Injective (Scheme.stalkClosedPointTo ξ).hom) : CharZero Ω := by
  classical
  set x := ξ.base (IsLocalRing.closedPoint Ω) with hx
  have hfl : (s.stalkMap x).hom.Flat := Flat.stalkMap s x
  have hinv : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.injective
  have hgerm := germ_injective_of_isIntegral (X := Spec (CommRingCat.of R)) (U := ⊤) (x := s.base x)
    (hx := trivial)
  have hA : ∀ n : ℕ, n ≠ 0 → (n : (Spec (CommRingCat.of R)).presheaf.stalk (s.base x)) ≠ 0 := by
    intro n hn h0
    apply (Nat.cast_ne_zero (R := R)).mpr hn
    apply hinv
    apply hgerm
    simp only [map_zero, map_natCast]
    exact h0
  have hO : ∀ n : ℕ, n ≠ 0 → (n : X.presheaf.stalk x) ≠ 0 := by
    intro n hn h0
    let _ := (s.stalkMap x).hom.toAlgebra
    have : Module.Flat ((Spec (CommRingCat.of R)).presheaf.stalk (s.base x)) (X.presheaf.stalk x) := hfl
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := X.presheaf.stalk x)
      (mem_nonZeroDivisors_of_ne_zero (hA n hn))
    have h3 : (n : (Spec (CommRingCat.of R)).presheaf.stalk (s.base x)) • (1 : X.presheaf.stalk x) =
        (n : (Spec (CommRingCat.of R)).presheaf.stalk (s.base x)) • (0 : X.presheaf.stalk x) := by
      rw [smul_zero, Algebra.smul_def, _root_.mul_one, map_natCast]
      exact h0
    exact one_ne_zero (hreg h3)
  exact charZero_of_inj_zero fun n hn => by
    by_contra hne
    apply hO n hne
    apply h
    rw [map_natCast, map_zero]
    exact hn

theorem charZero_function_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → CharZero Ω₀ := by
  intro E _ _ _ H D l Xo c Y Ω₀ _ ξ₀ hξ
  have := Y.flat
  exact charZero_of_flat Y.s ξ₀ hξ.bij.1

end GlobalTheory.CompanionTheory.Ar.CharZeroModel
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.GenPtModel

theorem mem_genericPoints_of_eq {X : Scheme.{0}} {x : X}
    (h : ∀ p : X, p ⤳ x → p = x) : x ∈ genericPoints X := by
  show closure {x} ∈ irreducibleComponents X
  rw [irreducibleComponents_eq_maximals_closed]
  refine ⟨⟨isClosed_closure, isIrreducible_singleton.closure⟩, fun T hT hxT => ?_⟩
  obtain ⟨p, hp⟩ := QuasiSober.sober hT.2 hT.1
  have hpx : p = x := h p ((hp.specializes_iff_mem).2 (hxT (subset_closure (Set.mem_singleton x))))
  intro y hy
  rw [← hpx]
  exact specializes_iff_mem_closure.1 ((hp.specializes_iff_mem).2 hy)

theorem genPt_mem_genericPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → GlobalTheory.CompanionTheory.Ar.genPt ξ₀ ∈ genericPoints Y.X := by
  intro E _ _ _ H D l Xo c Y Ω₀ _ ξ₀ hξ
  apply mem_genericPoints_of_eq
  intro p hp
  have hp' : p ∈ Set.range (Y.X.fromSpecStalk (GlobalTheory.CompanionTheory.Ar.genPt ξ₀)) := by
    rw [Scheme.range_fromSpecStalk]
    exact hp
  obtain ⟨q, rfl⟩ := hp'
  have hfield : IsField (Y.X.presheaf.stalk (GlobalTheory.CompanionTheory.Ar.genPt ξ₀)) :=
    MulEquiv.isField (Field.toIsField Ω₀)
      (RingEquiv.ofBijective (CommRingCat.Hom.hom (Scheme.stalkClosedPointTo ξ₀)) hξ.bij).toMulEquiv
  have hq : q = IsLocalRing.closedPoint _ := by
    apply PrimeSpectrum.ext
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal q.isPrime.ne_top
    · intro a ha
      by_cases h0 : a = 0
      · rw [h0]
        exact q.asIdeal.zero_mem
      · obtain ⟨b, hb⟩ := hfield.mul_inv_cancel h0
        exact absurd ⟨⟨a, b, hb, by rw [mul_comm]; exact hb⟩, rfl⟩ ((IsLocalRing.mem_maximalIdeal a).1 ha)
  rw [hq, Scheme.fromSpecStalk_closedPoint]

end GlobalTheory.CompanionTheory.Ar.GenPtModel
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieBaseChange

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieTangent

theorem existsUnique_semilinear_lifts :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R R' : Type) [CommRing R] [CommRing R'] (c : R →+* R')
      (x : Sp R ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (E' : Type) [AddCommGroup E'] [Module R' E']
      (M : LieModel G x E) (M' : LieModel G (spMap c ≫ x) E'),
      ∃! j : E →ₛₗ[c] E', ∀ e, ((M'.pt (j e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap c) ≫ (M.pt e).left) := by
  intro S G _ R R' _ _ c x E _ _ E' _ _ M M'
  have hc : Spec.map (CommRingCat.ofHom c) ≫ x = spMap c ≫ x := rfl
  have h : ∀ e, ∃ e', M'.pt e' = epsBase c hc ≫ M.pt e :=
    fun e => M'.onto _ (isTanAt_base c hc (M.tan e))
  choose a ha using h
  refine ⟨{ toFun := a, map_add' := ?_, map_smul' := ?_ }, ?_, ?_⟩
  · intro e e'
    apply M'.inj
    rw [M'.add, ha, ha, ha, M.add, MonObj.comp_mul]
  · intro r e
    apply M'.inj
    rw [M'.pt_smul, ha, ha, M.pt_smul, ← Category.assoc, base_scale, Category.assoc]
  · intro e
    change (M'.pt (a e)).left ≫ 𝟙 G.left = spMap (dualMap c) ≫ (M.pt e).left
    rw [Category.comp_id, ha]
    rfl
  · intro j hj
    ext e
    refine M'.inj ((?_ : M'.pt (j e) = epsBase c hc ≫ M.pt e).trans (ha e).symm)
    apply Over.OverMorphism.ext
    have := hj e
    change _ ≫ _ = _ ≫ _ at this
    rw [Category.comp_id] at this
    exact this

end GlobalTheory.CompanionTheory.Ar.LieBaseChange
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_model_push_along_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t' : SAB H S') (t : SAB H S) (f : S' ⟶ S) (m : SABMap t' t f) (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S') (V : Type) [AddCommGroup V] [Module R V] (M : LieModel t'.G x V), ∃ Mf : LieModel t.G (x ≫ f) V, ∀ e, (Mf.pt e).left = (M.pt e).left ≫ m.φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SabLie.lieModel_of_sabMap | exact GlobalTheory.CompanionTheory.Ar.SabLie.lieModel_of_sabMap | (intros; apply GlobalTheory.CompanionTheory.Ar.SabLie.lieModel_of_sabMap <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.regAt_iff_chart_localization : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) (x : κ → Ω), CoordTie o ξ x → ∀ (c : κ) (p : Cpt ξ), InChart ξ x c p → ∀ a : Ω, a ∈ regAt ξ p ↔ ∃ s ∈ Algebra.adjoin o (Set.range fun j => x j / x c), unitAt ξ p s ∧ s * a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.regAt_iff_exists_chart_fraction | exact GlobalTheory.CompanionTheory.Ar.regAt_iff_exists_chart_fraction | (intros; apply GlobalTheory.CompanionTheory.Ar.regAt_iff_exists_chart_fraction <;> assumption)
end
