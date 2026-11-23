module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle265
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle318
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.LesFirst

section
variable {R : Type} [CommRing R]

theorem ofHom_comp_comp {K L M I : Cx R} (φ : K ⟶ L) (ψ : L ⟶ M) {n : ℤ} (z : Cochain M I n) :
    (Cochain.ofHom φ).comp ((Cochain.ofHom ψ).comp z (zero_add n)) (zero_add n) =
      (Cochain.ofHom (φ ≫ ψ)).comp z (zero_add n) := by
  ext p q hpq; simp

theorem δ_ofHom_comp' {K L I : Cx R} (φ : K ⟶ L) {n m : ℤ} (z : Cochain L I n) :
    δ n m ((Cochain.ofHom φ).comp z (zero_add n)) = (Cochain.ofHom φ).comp (δ n m z) (zero_add m) := by
  by_cases h : n + 1 = m
  · rw [δ_comp _ _ (zero_add n) 1 m m h (zero_add 1) h]; simp
  · simp [δ_shape _ _ h]

theorem cpull_mk {K L I : Cx R} (φ : K ⟶ L) {n : ℤ} (z : Cocycle L I n) :
    cpull φ I n (CohomologyClass.mk z) = CohomologyClass.mk (zcomp (Cocycle.ofHom φ) z (zero_add n)) := rfl

theorem cpull_comp {K L M I : Cx R} (φ : K ⟶ L) (ψ : L ⟶ M) (n : ℤ) (x : CohomologyClass M I n) :
    cpull φ I n (cpull ψ I n x) = cpull (φ ≫ ψ) I n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  exact congrArg CohomologyClass.mk (Cocycle.ext (ofHom_comp_comp φ ψ x.1))

theorem cpull_zero' {K L I : Cx R} (n : ℤ) (x : CohomologyClass L I n) :
    cpull (0 : K ⟶ L) I n x = 0 := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [cpull_mk, ← CohomologyClass.mk_zero]
  exact congrArg CohomologyClass.mk (Cocycle.ext (by simp [zcomp]))

variable {I : Cx R} (S : ShortComplex (Cx R))

def Snake {n : ℤ} (a : Cochain S.X₁ I n) (c : Cochain S.X₃ I (n + 1)) : Prop :=
  ∃ b : Cochain S.X₂ I n, (Cochain.ofHom S.f).comp b (zero_add n) = a ∧
    (Cochain.ofHom S.g).comp c (zero_add (n + 1)) = δ n (n + 1) b

theorem fg_zero {n : ℤ} (e : Cochain S.X₃ I n) :
    (Cochain.ofHom S.f).comp ((Cochain.ofHom S.g).comp e (zero_add n)) (zero_add n) = 0 := by
  rw [ofHom_comp_comp, S.zero]; simp

theorem snake_add {n : ℤ} {a a' : Cochain S.X₁ I n} {c c' : Cochain S.X₃ I (n + 1)}
    (h : Snake S a c) (h' : Snake S a' c') : Snake S (a + a') (c + c') := by
  obtain ⟨b, hb, hc⟩ := h; obtain ⟨b', hb', hc'⟩ := h'
  exact ⟨b + b', by rw [Cochain.comp_add, hb, hb'], by rw [Cochain.comp_add, hc, hc', δ_add]⟩

theorem snake_sub {n : ℤ} {a a' : Cochain S.X₁ I n} {c c' : Cochain S.X₃ I (n + 1)}
    (h : Snake S a c) (h' : Snake S a' c') : Snake S (a - a') (c - c') := by
  obtain ⟨b, hb, hc⟩ := h; obtain ⟨b', hb', hc'⟩ := h'
  exact ⟨b - b', by rw [Cochain.comp_sub, hb, hb'], by rw [Cochain.comp_sub, hc, hc', δ_sub]⟩

variable (hI : ∀ n, Injective (I.X n)) (hS : S.ShortExact)
include hI hS

theorem snake_exists {n : ℤ} (a : Cocycle S.X₁ I n) : ∃ c : Cocycle S.X₃ I (n + 1), Snake S a.1 c.1 := by
  have L := cochain_shortExact_of_injective R I hI S hS
  obtain ⟨b, hb⟩ := (L n).1 a.1
  have h1 : (Cochain.ofHom S.f).comp (δ n (n + 1) b) (zero_add (n + 1)) = 0 := by
    rw [← δ_ofHom_comp', hb]; exact a.δ_eq_zero (n + 1)
  obtain ⟨c, hc⟩ := (L (n + 1)).2.1 _ h1
  have h2 : δ (n + 1) (n + 1 + 1) c = 0 := by
    apply (L (n + 1 + 1)).2.2
    rw [← δ_ofHom_comp', hc, δ_δ]
  exact ⟨Cocycle.mk c (n + 1 + 1) rfl h2, b, hb, hc⟩

theorem snake_bdry {n m : ℤ} (hm : m + 1 = n) {a : Cochain S.X₁ I n} {c : Cochain S.X₃ I (n + 1)}
    (h : Snake S a c) (β : Cochain S.X₁ I m) (hβ : δ m n β = a) :
    ∃ e : Cochain S.X₃ I n, δ n (n + 1) e = c := by
  have L := cochain_shortExact_of_injective R I hI S hS
  obtain ⟨b, hb, hc⟩ := h
  obtain ⟨β₂, hβ₂⟩ := (L m).1 β
  have h1 : (Cochain.ofHom S.f).comp (b - δ m n β₂) (zero_add n) = 0 := by
    rw [Cochain.comp_sub, ← δ_ofHom_comp', hβ₂, hβ, hb, sub_self]
  obtain ⟨e, he⟩ := (L n).2.1 _ h1
  refine ⟨e, ?_⟩
  rw [← sub_eq_zero]
  apply (L (n + 1)).2.2
  rw [Cochain.comp_sub, ← δ_ofHom_comp', he, hc, δ_sub, δ_δ, sub_zero, sub_self]

theorem snake_unique {n : ℤ} {a : Cochain S.X₁ I n} {c c' : Cocycle S.X₃ I (n + 1)}
    (h : Snake S a c.1) (h' : Snake S a c'.1) :
    CohomologyClass.mk c = CohomologyClass.mk c' := by
  have h0 := snake_sub S h h'
  rw [sub_self] at h0
  obtain ⟨e, he⟩ := snake_bdry S hI hS (sub_add_cancel n 1) h0 0 (by simp)
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ n rfl]
  exact ⟨e, by rw [he]; rfl⟩

def conn0 (n : ℤ) (a : Cocycle S.X₁ I n) : CohomologyClass S.X₃ I (n + 1) :=
  CohomologyClass.mk (Classical.choose (snake_exists S hI hS a))

theorem etaleSnakeConnectingOnCocycles_eq {n : ℤ} (a : Cocycle S.X₁ I n) (c : Cocycle S.X₃ I (n + 1)) (h : Snake S a.1 c.1) :
    conn0 S hI hS n a = CohomologyClass.mk c :=
  snake_unique S hI hS (Classical.choose_spec (snake_exists S hI hS a)) h

def conn (n : ℤ) : CohomologyClass S.X₁ I n →+ CohomologyClass S.X₃ I (n + 1) :=
  CohomologyClass.descAddMonoidHom
    (AddMonoidHom.mk' (conn0 S hI hS n) (fun a a' => by
      obtain ⟨c, hc⟩ := snake_exists S hI hS a
      obtain ⟨c', hc'⟩ := snake_exists S hI hS a'
      rw [etaleSnakeConnectingOnCocycles_eq S hI hS a c hc, etaleSnakeConnectingOnCocycles_eq S hI hS a' c' hc',
        etaleSnakeConnectingOnCocycles_eq S hI hS (a + a') (c + c') (snake_add S hc hc'), CohomologyClass.mk_add]))
    (by
      intro a ha
      rw [mem_coboundaries_iff a (n - 1) (sub_add_cancel n 1)] at ha
      obtain ⟨β, hβ⟩ := ha
      obtain ⟨c, hc⟩ := snake_exists S hI hS a
      obtain ⟨e, he⟩ := snake_bdry S hI hS (sub_add_cancel n 1) hc β hβ
      rw [AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply, etaleSnakeConnectingOnCocycles_eq S hI hS a c hc,
        CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n rfl]
      exact ⟨e, he⟩)

end

end GlobalTheory.EtC.LesFirst

namespace GlobalTheory.EtC


open LesFirst in
theorem longExact_first_of_injective :
    ∀ (R : Type) [CommRing R] (I : Cx R), (∀ n, Injective (I.X n)) → ∃ d : ∀ (S : ShortComplex (Cx R)), S.ShortExact → ∀ n : ℤ, CohomologyClass S.X₁ I n →+ CohomologyClass S.X₃ I (n + 1), (∀ (S : ShortComplex (Cx R)) (hS : S.ShortExact) n, Function.Exact (cpull S.g I n) (cpull S.f I n) ∧ Function.Exact (cpull S.f I n) (d S hS n) ∧ Function.Exact (d S hS n) (cpull S.g I (n + 1))) ∧ ∀ (S S' : ShortComplex (Cx R)) (hS : S.ShortExact) (hS' : S'.ShortExact) (φ : S ⟶ S') n x, cpull φ.τ₃ I (n + 1) (d S' hS' n x) = d S hS n (cpull φ.τ₁ I n x) := by
  intro R _ I hI
  refine ⟨fun S hS n => conn S hI hS n, fun S hS n => ⟨?_, ?_, ?_⟩, ?_⟩
  · have L := cochain_shortExact_of_injective R I hI S hS
    intro y
    constructor
    · intro hy
      obtain ⟨y, rfl⟩ := y.mk_surjective
      rw [cpull_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (sub_add_cancel n 1)] at hy
      obtain ⟨β, hβ⟩ := hy
      obtain ⟨β₂, hβ₂⟩ := (L (n - 1)).1 β
      have h1 : (Cochain.ofHom S.f).comp (y.1 - δ (n - 1) n β₂) (zero_add n) = 0 := by
        rw [Cochain.comp_sub, ← δ_ofHom_comp', hβ₂, hβ]; exact sub_self _
      obtain ⟨c, hc⟩ := (L n).2.1 _ h1
      have h2 : δ n (n + 1) c = 0 := by
        apply (L (n + 1)).2.2
        rw [← δ_ofHom_comp', hc, δ_sub, δ_δ, y.δ_eq_zero, sub_zero]
      refine ⟨CohomologyClass.mk (Cocycle.mk c (n + 1) rfl h2), ?_⟩
      rw [cpull_mk, ← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
        mem_coboundaries_iff _ (n - 1) (sub_add_cancel n 1)]
      refine ⟨-β₂, ?_⟩
      rw [δ_neg]
      change -(δ (n - 1) n β₂) = (Cochain.ofHom S.g).comp c (zero_add n) - y.1
      rw [hc]; abel
    · rintro ⟨x, rfl⟩
      rw [cpull_comp, S.zero, cpull_zero']
  · intro y
    constructor
    · intro hy
      obtain ⟨a, rfl⟩ := y.mk_surjective
      obtain ⟨c, b, hb, hc⟩ := snake_exists S hI hS a
      change conn0 S hI hS n a = 0 at hy
      rw [etaleSnakeConnectingOnCocycles_eq S hI hS a c ⟨b, hb, hc⟩, CohomologyClass.mk_eq_zero_iff,
        mem_coboundaries_iff _ n rfl] at hy
      obtain ⟨e, he⟩ := hy
      have h : δ n (n + 1) (b - (Cochain.ofHom S.g).comp e (zero_add n)) = 0 := by
        rw [δ_sub, δ_ofHom_comp', he, ← hc, sub_self]
      refine ⟨CohomologyClass.mk (Cocycle.mk _ (n + 1) rfl h), ?_⟩
      rw [cpull_mk]
      refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
      change (Cochain.ofHom S.f).comp (b - (Cochain.ofHom S.g).comp e (zero_add n)) (zero_add n) = a.1
      rw [Cochain.comp_sub, fg_zero, sub_zero, hb]
    · rintro ⟨x, rfl⟩
      obtain ⟨b, rfl⟩ := x.mk_surjective
      change conn0 S hI hS n _ = 0
      rw [etaleSnakeConnectingOnCocycles_eq S hI hS _ 0 ⟨b.1, rfl, by simp⟩, CohomologyClass.mk_zero]
  · intro z
    constructor
    · intro hz
      obtain ⟨c, rfl⟩ := z.mk_surjective
      rw [cpull_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n rfl] at hz
      obtain ⟨β, hβ⟩ := hz
      have h : δ n (n + 1) ((Cochain.ofHom S.f).comp β (zero_add n)) = 0 := by
        rw [δ_ofHom_comp', hβ]; exact fg_zero S c.1
      refine ⟨CohomologyClass.mk (Cocycle.mk _ (n + 1) rfl h), ?_⟩
      exact etaleSnakeConnectingOnCocycles_eq S hI hS _ c ⟨β, rfl, hβ.symm⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨a, rfl⟩ := x.mk_surjective
      obtain ⟨c, hs⟩ := snake_exists S hI hS a
      change cpull S.g I (n + 1) (conn0 S hI hS n a) = 0
      rw [etaleSnakeConnectingOnCocycles_eq S hI hS a c hs, cpull_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n rfl]
      obtain ⟨b, hb, hc⟩ := hs
      exact ⟨b, hc.symm⟩
  · intro S S' hS hS' φ n x
    obtain ⟨a, rfl⟩ := x.mk_surjective
    obtain ⟨c, b, hb, hc⟩ := snake_exists S' hI hS' a
    change cpull φ.τ₃ I (n + 1) (conn0 S' hI hS' n a) = conn0 S hI hS n _
    rw [etaleSnakeConnectingOnCocycles_eq S' hI hS' a c ⟨b, hb, hc⟩, cpull_mk,
      etaleSnakeConnectingOnCocycles_eq S hI hS _ _ ⟨(Cochain.ofHom φ.τ₂).comp b (zero_add n), ?_, ?_⟩]
    · change _ = (Cochain.ofHom φ.τ₁).comp a.1 (zero_add n)
      rw [ofHom_comp_comp, ← φ.comm₁₂, ← ofHom_comp_comp, hb]
    · change (Cochain.ofHom S.g).comp ((Cochain.ofHom φ.τ₃).comp c.1 (zero_add (n + 1))) (zero_add (n + 1)) = _
      rw [ofHom_comp_comp, ← φ.comm₂₃, ← ofHom_comp_comp, hc, δ_ofHom_comp']

end GlobalTheory.EtC
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.ResBasic

variable (R : Type) [CommRing R]

def resHom {F G : Shv R} (φ : F ⟶ G) :
    InjectiveResolution.Hom (injectiveResolution F) (injectiveResolution G) φ :=
  ⟨InjectiveResolution.desc φ (injectiveResolution G) (injectiveResolution F),
    congrArg (fun f => HomologicalComplex.Hom.f f 0)
      (InjectiveResolution.desc_commutes φ (injectiveResolution G) (injectiveResolution F))⟩

theorem mono_ι_f_zero (F : Shv R) : Mono ((injectiveResolution F).ι.f 0) :=
  mono_of_isLimit_fork (injectiveResolution F).isLimitKernelFork

theorem mono_resι (F : Shv R) : Mono (resι R F) := by
  have h1 := mono_ι_f_zero R F
  change Mono ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ (injectiveResolution F).ι'.f 0)
  rw [InjectiveResolution.ι'_f_zero, Iso.inv_hom_id_assoc]
  exact @mono_comp _ _ _ _ _ _ h1 _ inferInstance

theorem sglι_comp_single_map {F G : Shv R} (φ : F ⟶ G) :
    sglι F ≫ ((CochainComplex.singleFunctor (Shv R) 0).map φ).f 0 = φ ≫ sglι G := by
  have := HomologicalComplex.single_map_f_self (V := Shv R) (ComplexShape.up ℤ) 0 φ
  change (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫
    ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map φ).f 0 = _
  rw [this, Iso.inv_hom_id_assoc]
  rfl

theorem res_basic : ∀ (R : Type) [CommRing R] (F : Shv R), (res R F).IsKInjective ∧ (∀ n, Injective ((res R F).X n)) ∧
    (res R F).IsStrictlyGE 0 ∧ QuasiIso (resAug F) ∧ sglι F ≫ (resAug F).f 0 = resι R F ∧ Mono (resι R F) ∧
    resι R F ≫ (res R F).d 0 1 = 0 ∧ ∀ (G : Shv R) (φ : F ⟶ G),
      resAug F ≫ resMap R φ = (CochainComplex.singleFunctor (Shv R) 0).map φ ≫ resAug G ∧
      resι R F ≫ (resMap R φ).f 0 = φ ≫ resι R G := by
  intro R _ F
  have hinj : ∀ n, Injective ((res R F).X n) := fun n =>
    inferInstanceAs (Injective ((injectiveResolution F).cochainComplex.X n))
  have hge : (res R F).IsStrictlyGE 0 := inferInstanceAs ((injectiveResolution F).cochainComplex.IsStrictlyGE 0)
  have hq : QuasiIso (resAug F) := inferInstanceAs (QuasiIso (injectiveResolution F).ι')
  have hι : ∀ F : Shv R, sglι F ≫ (resAug F).f 0 = resι R F := fun _ => rfl
  have hcomm : ∀ (G : Shv R) (φ : F ⟶ G),
      resAug F ≫ resMap R φ = (CochainComplex.singleFunctor (Shv R) 0).map φ ≫ resAug G :=
    fun G φ => (resHom R φ).ι'_comp_hom'
  refine ⟨CochainComplex.isKInjective_of_injective _ 0, hinj, hge, hq, hι F, mono_resι R F, ?_,
    fun G φ => ⟨hcomm G φ, ?_⟩⟩
  · rw [← hι F, Category.assoc, (resAug F).comm 0 1]
    simp
  · rw [← hι F, Category.assoc, ← HomologicalComplex.comp_f, hcomm G φ, HomologicalComplex.comp_f, ← hι G,
      ← Category.assoc, sglι_comp_single_map, Category.assoc]

end GlobalTheory.EtC.ResBasic
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ConeConn


set_option backward.isDefEq.respectTransparency false in
theorem cone_connecting_class : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R))
    (hc : (CochainComplex.singleFunctor (Shv R) 0).map S.f ≫ resAug S.X₂ = resAug S.X₁ ≫ resMap R S.f)
    (φ : S.X₂ ⟶ (res R S.X₁).X 0) (ψ : S.X₃ ⟶ (res R S.X₁).X 1),
    S.f ≫ φ = resι R S.X₁ → S.g ≫ ψ = φ ≫ (res R S.X₁).d 0 1 →
    ∀ w : Cocycle (sgl S.X₃) (res R S.X₁) 1, sglι S.X₃ ≫ w.1.v 0 1 (zero_add 1) = ψ →
    CohomologyClass.mk (zcomp (Cocycle.ofHom (mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc))
        (mappingCone.fst (resMap R S.f)) (zero_add 1)) =
      CohomologyClass.mk (zcomp (Cocycle.ofHom
        (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0)))) w (zero_add 1)) := by
  intro R _ S hc φ ψ hφ hψ w hw
  let Φ : Cochain (sgl S.X₂) (res R S.X₁) 0 := Cochain.fromSingleMk φ (zero_add 0)
  have hw1 : w.1 = Cochain.fromSingleMk ψ (zero_add 1) := by
    obtain ⟨f, hf⟩ := Cochain.fromSingleMk_surjective w.1 1 (zero_add 1)
    rw [← hf]; congr 1
    rw [← hw, ← hf, Cochain.fromSingleMk_v]; exact (Iso.inv_hom_id_assoc _ _).symm
  have h1 : δ 0 1 Φ = (Cochain.ofHom (S.map (CochainComplex.singleFunctor (Shv R) 0)).g).comp w.1 (zero_add 1) := by
    rw [hw1, Cochain.δ_fromSingleMk φ (zero_add 0) 1 1 (zero_add 1), ← hψ]
    exact Cochain.fromSingleMk_precomp S.g ψ (zero_add 1)
  have h2 : (Cochain.ofHom (S.map (CochainComplex.singleFunctor (Shv R) 0)).f).comp Φ (zero_add 0) =
      Cochain.ofHom (resAug S.X₁) := by
    refine (Cochain.fromSingleMk_precomp S.f φ (zero_add 0)).symm.trans ?_
    rw [hφ]
    apply (Cochain.fromSingleEquiv (X := S.X₁) (K := res R S.X₁) (p := 0) (zero_add 0)).injective
    rw [Cochain.fromSingleEquiv_fromSingleMk]
    change resι R S.X₁ = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 S.X₁).inv ≫ (Cochain.ofHom (resAug S.X₁)).v 0 0 (add_zero 0)
    rw [Cochain.ofHom_v]; rfl
  have h3 : Cochain.ofHom (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0))) =
      (mappingCone.snd (S.map (CochainComplex.singleFunctor (Shv R) 0)).f).comp
        (Cochain.ofHom (S.map (CochainComplex.singleFunctor (Shv R) 0)).g) (zero_add 0) := by
    rw [mappingCone.descShortComplex, mappingCone.ofHom_desc, mappingCone.descCochain]
    simp
  have h4 : (Cochain.ofHom (mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc)).comp
      (mappingCone.fst (resMap R S.f)).1 (zero_add 1) =
      (mappingCone.fst (S.map (CochainComplex.singleFunctor (Shv R) 0)).f).1.comp
        (Cochain.ofHom (resAug S.X₁)) (add_zero 1) := by
    simp [mappingCone.map, mappingCone.ofHom_desc, mappingCone.descCochain, Cochain.add_comp]
  symm
  refine sub_eq_zero.1 ((CohomologyClass.mk_sub _ _).symm.trans ?_)
  refine (CohomologyClass.mk_eq_zero_iff _).2 ((mem_coboundaries_iff _ 0 (zero_add 1)).2
    ⟨(mappingCone.snd (S.map (CochainComplex.singleFunctor (Shv R) 0)).f).comp Φ (zero_add 0), ?_⟩)
  have e1 := δ_zero_cochain_comp (mappingCone.snd (S.map (CochainComplex.singleFunctor (Shv R) 0)).f) Φ 1 (zero_add 1)
  rw [h1, mappingCone.δ_snd, Int.negOnePow_zero, one_smul, Cochain.neg_comp,
    Cochain.comp_assoc_of_second_is_zero_cochain, h2,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, ← h3, ← h4] at e1
  refine e1.trans ?_
  simp [zcomp, sub_eq_add_neg]

end GlobalTheory.EtC.ConeConn
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.InjFlat

instance evalLeft_preservesMono (S : Type 1) [Ring S] (c : Scheme.{0}ᵒᵖ) :
    (evaluationLeftAdjoint (ModuleCat.{1} S) c).PreservesMonomorphisms where
  preserves {a b} f _ := by
    have : AB4OfSize.{0} (ModuleCat.{1} S) := AB4OfSize_shrink.{0, 1} _
    rw [NatTrans.mono_iff_mono_app']
    intro t
    have h : ((evaluationLeftAdjoint (ModuleCat.{1} S) c).map f).app t =
        colim.map (Discrete.natTrans (fun _ => f) :
          Discrete.functor (fun _ : c ⟶ t => a) ⟶ Discrete.functor (fun _ : c ⟶ t => b)) := by
      apply Sigma.hom_ext
      intro g
      simp only [evaluationLeftAdjoint_map_app]
      erw [colimit.ι_desc]
      try rfl
    rw [h]
    have : HasExactColimitsOfShape (Discrete (c ⟶ t)) (ModuleCat.{1} S) := inferInstance
    have : PreservesFiniteLimits (colim : (Discrete (c ⟶ t) ⥤ ModuleCat.{1} S) ⥤ _) := inferInstance
    have hm : Mono (Discrete.natTrans (fun _ => f) :
        Discrete.functor (fun _ : c ⟶ t => a) ⟶ Discrete.functor (fun _ : c ⟶ t => b)) :=
      have : ∀ X, Mono ((Discrete.natTrans (fun _ => f) :
          Discrete.functor (fun _ : c ⟶ t => a) ⟶ Discrete.functor (fun _ : c ⟶ t => b)).app X) :=
        fun _ => inferInstanceAs (Mono f)
      NatTrans.mono_of_mono_app _
    exact Functor.map_mono colim _

theorem sec_injective (S : Type) [CommRing S] (M : Shv S) [Injective M] (U : Scheme.{0}) :
    Injective (M.obj.obj (op U)) := by
  have h1 : Injective M.obj :=
    (sheafificationAdjunction Scheme.etaleTopology (ModuleCat.{1} (ULift.{1} S))).map_injective M inferInstance
  exact (evaluationAdjunctionRight (ModuleCat.{1} (ULift.{1} S)) (op U)).map_injective M.obj h1

end GlobalTheory.EtC.InjFlat

namespace GlobalTheory.EtC.InjFlat

theorem zmod_mul_eq_zero (q d e : ℕ) [NeZero q] (hde : d * e = q) (z : ZMod q) (hz : (e : ZMod q) * z = 0) :
    ∃ c : ZMod q, z = c * d := by
  have hq : q ≠ 0 := NeZero.ne q
  have he : e ≠ 0 := by rintro rfl; simp at hde; exact hq hde.symm
  have h1 : q ∣ e * z.val := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, ZMod.natCast_zmod_val, hz]
  have h1' : e * d ∣ e * z.val := by rw [mul_comm e d, hde]; exact h1
  obtain ⟨k, hk⟩ := (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero he)).mp h1'
  refine ⟨k, ?_⟩
  rw [← ZMod.natCast_zmod_val z, hk, Nat.cast_mul, mul_comm]

theorem div_of_injective (q : ℕ) [NeZero q] (N : ModuleCat.{1} (ULift.{1} (ZMod q))) [Injective N] :
    ∀ d e : ℕ, d * e = q → ∀ x : N, d • x = 0 → ∃ y : N, x = e • y := by
  intro d e hde x hx
  let R := ULift.{1} (ZMod q)
  let I : Submodule R R := Submodule.span R {(d : R)}
  have hI : I ≤ LinearMap.ker (LinearMap.lsmul R R (e : R)) := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    change (e : R) • (d : R) = 0
    rw [smul_eq_mul, ← Nat.cast_mul, mul_comm, hde]
    ext; simp
  have hJ : I ≤ LinearMap.ker (LinearMap.toSpanSingleton R N x) := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    change (d : R) • x = 0
    rw [Nat.cast_smul_eq_nsmul, hx]
  let i : (R ⧸ I) →ₗ[R] R := I.liftQ _ hI
  let f : (R ⧸ I) →ₗ[R] N := I.liftQ _ hJ
  have hmono : Mono (ModuleCat.ofHom i) := by
    rw [ModuleCat.mono_iff_injective]
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro r hr
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective I r
    rw [LinearMap.mem_ker] at hr
    change (e : R) • r = 0 at hr
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    obtain ⟨c, hc⟩ := zmod_mul_eq_zero q d e hde r.down (by
      have := congrArg ULift.down hr
      rw [smul_eq_mul, ULift.mul_down, ULift.down_natCast] at this
      exact this)
    rw [Submodule.mem_span_singleton]
    refine ⟨ULift.up c, ?_⟩
    apply ULift.down_injective
    rw [hc]
    change (ULift.up c * (d : R)).down = _
    rw [ULift.mul_down, ULift.down_natCast]
  let g := Injective.factorThru (ModuleCat.ofHom f) (ModuleCat.ofHom i)
  have hg := Injective.comp_factorThru (ModuleCat.ofHom f) (ModuleCat.ofHom i)
  refine ⟨g.hom 1, ?_⟩
  have h2 := congrArg (fun φ => φ.hom (Submodule.Quotient.mk (p := I) (1 : R))) hg
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at h2
  have hi1 : i (Submodule.Quotient.mk 1) = (e : R) := by
    simp only [i]
    erw [Submodule.liftQ_apply]
    simp
  have hf1 : f (Submodule.Quotient.mk 1) = x := by
    simp only [f]
    erw [Submodule.liftQ_apply]
    simp
  rw [hi1, hf1] at h2
  rw [← h2, ← Nat.cast_smul_eq_nsmul R, ← map_smul, smul_eq_mul, mul_one]

theorem flat_of_injective : ∀ (q : ℕ) [NeZero q] (M : Shv (ZMod q)) [Injective M],
    (∀ U : Scheme.{0}, Module.Flat (ULift.{1} (ZMod q)) (Sec M U)) ∧ FlatS M := by
  intro q _ M _
  have hflat : ∀ U : Scheme.{0}, Module.Flat (ULift.{1} (ZMod q)) (Sec M U) := fun U => by
    have := sec_injective (ZMod q) M U
    exact GlobalTheory.ZModFlat.flat_of_divisibility q (Sec M U) (div_of_injective q (M.obj.obj (op U)))
  refine ⟨hflat, M.obj, 𝟙 _, ?_, ?_, fun U _ => hflat U⟩
  · intro U y
    exact ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => ⟨(M.obj.map g.op).hom y, rfl⟩⟩
  · intro U x hx
    have hx0 : x = 0 := hx
    exact ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => by beta_reduce; rw [hx0, map_zero]⟩

end GlobalTheory.EtC.InjFlat
end
