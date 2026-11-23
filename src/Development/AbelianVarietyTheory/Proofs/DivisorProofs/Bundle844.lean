module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle816
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle030
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.WittVector.Frobenius
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle814
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle435
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle815
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle320
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
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.Compare
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Mathlib.CategoryTheory.Preadditive.EndoFunctor
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Filtration

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.IsoSpread

theorem spMap_inclusion_comp {S : Type} [CommRing S] {A B C : Subring S} (h₁ : A ≤ B)
    (h₂ : B ≤ C) :
    spMap (Subring.inclusion h₂) ≫ spMap (Subring.inclusion h₁) =
      spMap (Subring.inclusion (h₁.trans h₂)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem spMap_subtype_comp {S : Type} [CommRing S] {A B : Subring S} (h : A ≤ B) :
    spMap B.subtype ≫ spMap (Subring.inclusion h) = spMap A.subtype := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem exists_isPullback_lift {X₀ X₁ T₀ T₁ T₂ : Scheme.{0}} {f₀ : X₀ ⟶ T₀} {f₁ : X₁ ⟶ T₁}
    {π₁ : X₁ ⟶ X₀} {u : T₁ ⟶ T₂} {v : T₂ ⟶ T₀} {w : T₁ ⟶ T₀} (huv : u ≫ v = w)
    (hp : IsPullback π₁ f₁ f₀ w) :
    ∃ m : X₁ ⟶ pullback f₀ v, m ≫ pullback.fst _ _ = π₁ ∧ m ≫ pullback.snd _ _ = f₁ ≫ u ∧
      IsPullback m f₁ (pullback.snd f₀ v) u := by
  subst huv
  refine ⟨pullback.lift π₁ (f₁ ≫ u) (by rw [Category.assoc, hp.w]), pullback.lift_fst _ _ _,
    pullback.lift_snd _ _ _, ?_⟩
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rw [pullback.lift_fst]
  exact hp

end GlobalTheory.IsoSpread

namespace GlobalTheory


open GlobalTheory.IsoSpread in
theorem iso_spreads_to_subring :
    ∀ (S : Type) [CommRing S] (R₀ : Subring S) (X X₀ Z : Scheme.{0}) (f : X ⟶ Sp S) (f₀ : X₀ ⟶ Sp R₀) (q : Z ⟶ Sp R₀) (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀] [LocallyOfFinitePresentation f₀] [QuasiCompact q] [QuasiSeparated q] [LocallyOfFinitePresentation q] (φ : X ⟶ Z), IsPullback π f f₀ (spMap R₀.subtype) → IsPullback φ f q (spMap R₀.subtype) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion hle)) → j ≫ π₁ = π → j ≫ f₁ = f ≫ spMap R₁.subtype → ∃ ψ : X₁ ⟶ Z, j ≫ ψ = φ ∧ IsPullback ψ f₁ q (spMap (Subring.inclusion hle)) := by
  classical
  intro S _ R₀ X X₀ Z f f₀ q π _ _ _ _ _ _ φ hπ hφ

  obtain ⟨Fa, ha⟩ := morphism_descends_to_subring S R₀ X X₀ Z f f₀ q π φ hπ
    (hφ.w.trans hπ.w.symm)
  obtain ⟨Fb, hb⟩ := morphism_descends_to_subring S R₀ X Z X₀ f q f₀ φ π hφ
    (hπ.w.trans hφ.w.symm)

  let R₂ : Subring S := Subring.closure ((R₀ : Set S) ∪ (Fa : Set S) ∪ (Fb : Set S))
  have h₀₂ : R₀ ≤ R₂ := fun x hx ↦ Subring.subset_closure (Or.inl (Or.inl hx))
  have hFa : (Fa : Set S) ⊆ R₂ := fun x hx ↦ Subring.subset_closure (Or.inl (Or.inr hx))
  have hFb : (Fb : Set S) ⊆ R₂ := fun x hx ↦ Subring.subset_closure (Or.inr hx)
  obtain ⟨j₂, hj₂f, hj₂s, hj₂⟩ := exists_isPullback_lift (spMap_subtype_comp h₀₂) hπ
  obtain ⟨k₂, hk₂f, hk₂s, hk₂⟩ := exists_isPullback_lift (spMap_subtype_comp h₀₂) hφ
  obtain ⟨ψ₂, hψ₂, hψ₂q⟩ := ha R₂ h₀₂ hFa _ _ _ j₂ (IsPullback.of_hasPullback _ _) hj₂f hj₂s
  obtain ⟨χ₂, hχ₂, hχ₂q⟩ := hb R₂ h₀₂ hFb _ _ _ k₂ (IsPullback.of_hasPullback _ _) hk₂f hk₂s
  let α₂ := pullback.lift ψ₂ (pullback.snd f₀ (spMap (Subring.inclusion h₀₂)))
    (by rw [hψ₂q, pullback.condition])
  let β₂ := pullback.lift χ₂ (pullback.snd q (spMap (Subring.inclusion h₀₂)))
    (by rw [hχ₂q, pullback.condition])
  have hα₂f : α₂ ≫ pullback.fst _ _ = ψ₂ := pullback.lift_fst _ _ _
  have hα₂s : α₂ ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hβ₂f : β₂ ≫ pullback.fst _ _ = χ₂ := pullback.lift_fst _ _ _
  have hβ₂s : β₂ ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hjα : j₂ ≫ α₂ = k₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hα₂f, hψ₂, hk₂f]
    · rw [Category.assoc, hα₂s, hj₂s, hk₂s]
  have hkβ : k₂ ≫ β₂ = j₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hβ₂f, hχ₂, hj₂f]
    · rw [Category.assoc, hβ₂s, hj₂s, hk₂s]

  obtain ⟨Fc, hc⟩ := morphisms_eq_spread_to_subring S R₂ X _ _ f _ _ j₂ (α₂ ≫ β₂) (𝟙 _) hj₂
    (by rw [Category.assoc, hβ₂s, hα₂s]) (Category.id_comp _)
    (by rw [reassoc_of% hjα, hkβ, Category.comp_id])
  obtain ⟨Fd, hd⟩ := morphisms_eq_spread_to_subring S R₂ X _ _ f _ _ k₂ (β₂ ≫ α₂) (𝟙 _) hk₂
    (by rw [Category.assoc, hα₂s, hβ₂s]) (Category.id_comp _)
    (by rw [reassoc_of% hkβ, hjα, Category.comp_id])
  refine ⟨Fa ∪ Fb ∪ Fc ∪ Fd, fun R₁ hle hF X₁ f₁ π₁ j hp₁ hj₁ hjf ↦ ?_⟩
  simp only [Finset.coe_union, Set.union_subset_iff] at hF
  obtain ⟨⟨⟨hFa₁, hFb₁⟩, hFc₁⟩, hFd₁⟩ := hF
  have h₂₁ : R₂ ≤ R₁ := Subring.closure_le.mpr
    (Set.union_subset (Set.union_subset (fun x hx ↦ hle hx) hFa₁) hFb₁)
  obtain ⟨m, hmf, hms, hm⟩ := exists_isPullback_lift (w := spMap (Subring.inclusion hle))
    (spMap_inclusion_comp h₀₂ h₂₁) hp₁
  obtain ⟨n, hnf, hns, hn⟩ := exists_isPullback_lift (w := spMap (Subring.inclusion hle))
    (spMap_inclusion_comp h₀₂ h₂₁) (IsPullback.of_hasPullback q (spMap (Subring.inclusion hle)))
  have hmc : m ≫ α₂ ≫ β₂ = m := (hc R₁ h₂₁ hFc₁ X₁ f₁ m hm).trans (Category.comp_id _)
  have hnd : n ≫ β₂ ≫ α₂ = n := (hd R₁ h₂₁ hFd₁ _ _ n hn).trans (Category.comp_id _)
  have hjm : j ≫ m = j₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hmf, hj₁, hj₂f]
    · rw [Category.assoc, hms, reassoc_of% hjf, spMap_subtype_comp, hj₂s]
  have hw : (m ≫ ψ₂) ≫ q = f₁ ≫ spMap (Subring.inclusion hle) := by
    rw [Category.assoc, hψ₂q, reassoc_of% hmf, hp₁.w]
  let α : X₁ ⟶ pullback q (spMap (Subring.inclusion hle)) := pullback.lift (m ≫ ψ₂) f₁ hw
  let β : pullback q (spMap (Subring.inclusion hle)) ⟶ X₁ :=
    hp₁.lift (n ≫ χ₂) (pullback.snd _ _) (by rw [Category.assoc, hχ₂q, reassoc_of% hnf,
      pullback.condition])
  have hαf : α ≫ pullback.fst _ _ = m ≫ ψ₂ := pullback.lift_fst _ _ _
  have hαs : α ≫ pullback.snd _ _ = f₁ := pullback.lift_snd _ _ _
  have hβf : β ≫ π₁ = n ≫ χ₂ := hp₁.lift_fst _ _ _
  have hβs : β ≫ f₁ = pullback.snd _ _ := hp₁.lift_snd _ _ _
  have hαn : α ≫ n = m ≫ α₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hnf, hαf, Category.assoc, hα₂f]
    · rw [Category.assoc, hns, reassoc_of% hαs, Category.assoc, hα₂s, hms]
  have hβm : β ≫ m = n ≫ β₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hmf, hβf, Category.assoc, hβ₂f]
    · rw [Category.assoc, hms, reassoc_of% hβs, Category.assoc, hβ₂s, hns]
  have h₁ : α ≫ β = 𝟙 X₁ := by
    apply hp₁.hom_ext
    · rw [Category.assoc, hβf, reassoc_of% hαn, Category.id_comp, ← hβ₂f, ← Category.assoc m,
        ← Category.assoc, Category.assoc m, hmc, hmf]
    · rw [Category.assoc, hβs, hαs, Category.id_comp]
  have h₂ : β ≫ α = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hαf, reassoc_of% hβm, Category.id_comp, ← hα₂f, ← Category.assoc n,
        ← Category.assoc, Category.assoc n, hnd, hnf]
    · rw [Category.assoc, hαs, hβs, Category.id_comp]
  exact ⟨m ≫ ψ₂, by rw [reassoc_of% hjm, hψ₂],
    IsPullback.of_iso_pullback ⟨hw⟩ ⟨α, β, h₁, h₂⟩ hαf hαs⟩

end GlobalTheory
end

section

open Polynomial

namespace GlobalTheory.PicDiv

theorem classGroup_divisible : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B]
    [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), (q : k) ≠ 0 →
    ∀ c : ClassGroup B, ∃ d : ClassGroup B, d ^ q = c := by
  intro k B _ _ _ _ _ _ _ q hq c
  obtain ⟨d, hd⟩ := GlobalTheory.T.pic_divisible_dedekind_finiteType_algClosed k B q (Ne.isUnit hq) (ClassGroup.equivPic B c)
  refine ⟨(ClassGroup.equivPic B).symm d, ?_⟩
  apply (ClassGroup.equivPic B).injective
  rw [map_pow, MulEquiv.apply_symm_apply, hd]

end GlobalTheory.PicDiv
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.DieuCharpoly

open Polynomial

theorem mem_range_zmod_of_pow_eq_self (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p]
    (c : k) (hc : c ^ p = c) : c ∈ Set.range ((ZMod.castHom (dvd_refl p) k)) := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hroots := FiniteField.roots_X_pow_card_sub_X (ZMod p)
  rw [ZMod.card p] at hroots
  have hdeg : (X ^ p - X : (ZMod p)[X]).natDegree = p := Polynomial.natDegree_X_pow_sub_X hp
  have hcard : Multiset.card (X ^ p - X : (ZMod p)[X]).roots = (X ^ p - X : (ZMod p)[X]).natDegree := by
    rw [hroots, hdeg, Finset.card_val, Finset.card_univ, ZMod.card]
  have hmap := Polynomial.roots_map_of_injective_of_card_eq_natDegree
    ((ZMod.castHom (dvd_refl p) k)).injective hcard
  have hmem : c ∈ ((X ^ p - X : (ZMod p)[X]).map ((ZMod.castHom (dvd_refl p) k))).roots := by
    rw [Polynomial.mem_roots]
    · simp [hc]
    · simpa using (Polynomial.X_pow_sub_X_ne_zero hp : (X ^ p - X : k[X]) ≠ 0)
  rw [← hmap, hroots, Multiset.mem_map] at hmem
  obtain ⟨a, -, ha⟩ := hmem
  exact ⟨a, ha⟩

theorem exists_map_eq_of_frobenius_eq (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p]
    (x : WittVector p k) (hx : WittVector.frobenius x = x) :
    ∃ y : WittVector p (ZMod p), WittVector.map ((ZMod.castHom (dvd_refl p) k)) y = x := by
  have hc : ∀ n, ∃ a : ZMod p, (ZMod.castHom (dvd_refl p) k) a = x.coeff n := by
    intro n
    have h := congrArg (fun z => z.coeff n) hx
    simp only [WittVector.frobenius_eq_map_frobenius, WittVector.map_coeff, frobenius_def] at h
    exact mem_range_zmod_of_pow_eq_self p _ h
  choose a ha using hc
  refine ⟨WittVector.mk p a, ?_⟩
  ext n
  simp [WittVector.map_coeff, ha]

theorem padicInt_ringHom_ext (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p]
    [PerfectRing k p] (f g : ℤ_[p] →+* WittVector p k) : f = g := by
  refine RingHom.ext fun x => ?_
  rw [← sub_eq_zero]
  have hI : Ideal.span {(p : WittVector p k)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]; exact (WittVector.irreducible p).not_isUnit
  have h := Ideal.iInf_pow_eq_bot_of_isDomain _ hI
  rw [← Ideal.mem_bot, ← h, Ideal.mem_iInf]
  intro m
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec m x)
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  refine ⟨f y - g y, ?_⟩
  have h1 : x = ((x.appr m : ℕ) : ℤ_[p]) + y * (p : ℤ_[p]) ^ m := by rw [hy]; ring
  rw [h1]
  simp only [map_add (f := _), map_mul, map_pow, map_natCast]
  ring

end GlobalTheory.DieuCharpoly

namespace GlobalTheory.DieuCharpoly

open Polynomial

theorem charpoly_map_eq_of_commute_semilinear {R : Type} [CommRing R] [IsDomain R]
    (σ : R →+* R) (hσ : Function.Surjective σ) (N : Type) [AddCommGroup N] [Module R N]
    [Module.Free R N] [Module.Finite R N] (F : N →ₛₗ[σ] N) (u : N →ₗ[R] N)
    (hF : Function.Injective F) (hu : ∀ x, u (F x) = F (u x)) :
    u.charpoly.map σ = u.charpoly := by
  classical
  let b := Module.Free.chooseBasis R N
  let U := LinearMap.toMatrix b b u
  let Φ : Matrix _ _ R := fun i j => b.repr (F (b j)) i
  have hFrepr : ∀ x i, b.repr (F x) i = ∑ j, Φ i j * σ (b.repr x j) := by
    intro x i
    conv_lhs => rw [← b.sum_repr x]

    simp only [map_sum, LinearMap.map_smulₛₗ, Finset.sum_apply',
    map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hurepr : ∀ y i, b.repr (u y) i = ∑ l, U i l * b.repr y l := by
    intro y i
    rw [← LinearMap.toMatrix_mulVec_repr b b u y]
    rfl
  have hcomm : U * Φ = Φ * U.map σ := by
    refine Matrix.ext fun i j => ?_
    have h := congrArg (fun z => b.repr z i) (hu (b j))
    rw [hurepr, hFrepr] at h
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine h.trans (Finset.sum_congr rfl fun l _ => ?_)
    rw [Matrix.map_apply, show U l j = b.repr (u (b j)) l from LinearMap.toMatrix_apply b b u l j]
  have hdet : Φ.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    choose w hw using fun j => hσ (v j)
    let x := b.repr.symm (Finsupp.equivFunOnFinite.symm w)
    have hx : ∀ j, b.repr x j = w j := by simp [x]
    have hFx : F x = 0 := by
      apply b.repr.injective
      refine Finsupp.ext fun i => ?_
      rw [hFrepr, map_zero, Finsupp.coe_zero, Pi.zero_apply]
      have := congrFun hv i
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => by rw [hx, hw]
    have hx0 : x = 0 := hF (by rw [hFx, map_zero])
    apply hv0
    funext j
    rw [← hw j, Pi.zero_apply, ← hx j, hx0, map_zero, Finsupp.coe_zero, Pi.zero_apply, map_zero]
  rw [← LinearMap.charpoly_toMatrix u b, ← Matrix.charpoly_map]
  have hm : U.charmatrix * (Polynomial.C : R →+* _).mapMatrix Φ =
      (Polynomial.C : R →+* _).mapMatrix Φ * (U.map σ).charmatrix := by
    rw [Matrix.charmatrix, Matrix.charmatrix, sub_mul, mul_sub, ← map_mul, hcomm, map_mul,
      (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq]
  have hd := congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_mul, ← RingHom.map_det] at hd
  have hC : Polynomial.C Φ.det ≠ 0 := Polynomial.C_ne_zero.2 hdet
  rw [mul_comm] at hd
  exact (mul_left_cancel₀ hC hd).symm

end GlobalTheory.DieuCharpoly

namespace GlobalTheory.DieuCharpoly

open Polynomial

theorem exists_monic_map_eq_charpoly : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (N : Type) [AddCommGroup N] [Module (WittVector p k) N]
    [Module.Free (WittVector p k) N] [Module.Finite (WittVector p k) N]
    (F : N →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] N)
    (ψ : ℤ_[p] →+* (WittVector p k)) (u : N →ₗ[(WittVector p k)] N),
    Function.Injective F → (∀ x, u (F x) = F (u x)) →
      ∃ P : Polynomial ℤ_[p], P.Monic ∧ P.map ψ = u.charpoly := by
  intro p _ k _ _ _ N _ _ _ _ F ψ u hF hu
  have hfix := charpoly_map_eq_of_commute_semilinear _
    (WittVector.frobenius_bijective p k).surjective N F u hF hu
  have hψ : ψ = (WittVector.map (ZMod.castHom (dvd_refl p) k)).comp
      (WittVector.equiv p).symm.toRingHom := padicInt_ringHom_ext p _ _
  have hl : u.charpoly ∈ Polynomial.lifts ψ := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    have h : WittVector.frobenius (u.charpoly.coeff n) = u.charpoly.coeff n := by
      conv_rhs => rw [← hfix]
      rw [Polynomial.coeff_map]
    obtain ⟨y, hy⟩ := exists_map_eq_of_frobenius_eq p _ h
    refine ⟨WittVector.equiv p y, ?_⟩
    rw [hψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.symm_apply_apply, hy]
  obtain ⟨P, hP, -, hPm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (LinearMap.charpoly_monic u)
  exact ⟨P, hPm, hP⟩

end GlobalTheory.DieuCharpoly
end

section

open NumberField

theorem _root_.GlobalTheory.T.relIndex_iSup_map_eq_relIndex_pow : ∀ (K : Type) [Field K] [NumberField K] (W V : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
  [IsScalarTower (𝓞 K) K W] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (p : ℕ)
  (M : Fin p → (W →ₗ[K] V)) (ℓ N : Submodule (𝓞 K) W), N ≤ ℓ → (∀ a, Function.Injective (M a)) →
  iSupIndep (fun a => Submodule.span K ((ℓ.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V)) →
  (⨆ a, N.map ((M a).restrictScalars (𝓞 K))).toAddSubgroup.relIndex
      (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))).toAddSubgroup =
    (N.toAddSubgroup.relIndex ℓ.toAddSubgroup) ^ p := by
  first | exact @GlobalTheory.SumIndex.relIndex_iSup_map_eq_pow | exact GlobalTheory.SumIndex.relIndex_iSup_map_eq_pow | (intros; apply GlobalTheory.SumIndex.relIndex_iSup_map_eq_pow <;> assumption)
end

section

open IsLocalRing

namespace GlobalTheory.CurvePoint

theorem exists_ringHom_padicAlgCl_ne_zero : ∀ (B : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [CharZero B], Finite (ResidueField B) → ∀ h : B, h ≠ 0 → ∃ (p : ℕ) (_ : Fact p.Prime) (χ : B →+* PadicAlgCl p), (∀ b, ‖χ b‖ ≤ 1) ∧ (∀ b ∈ maximalIdeal B, ‖χ b‖ < 1) ∧ χ h ≠ 0 := by
  intro B _ _ _ _ _ hfin h hh

  set p := ringChar (ResidueField B) with hpdef
  have hp0 : p ≠ 0 := by
    intro h0
    haveI : CharP (ResidueField B) 0 := by rw [← h0]; exact ringChar.charP _
    haveI : CharZero (ResidueField B) := CharP.charP_to_charZero _
    exact not_finite (ResidueField B)
  have hp : p.Prime := (CharP.char_is_prime_or_zero (ResidueField B) p).resolve_right hp0
  haveI hF : Fact p.Prime := ⟨hp⟩
  have hpm : (p : B) ∈ maximalIdeal B := by
    rw [← residue_eq_zero_iff, map_natCast]
    exact ringChar.Nat.cast_ringChar
  have hpB : (p : B) ≠ 0 := Nat.cast_ne_zero.2 hp0

  obtain ⟨q, hq, hxq, hmax⟩ := GlobalTheory.T.exists_prime_not_mem_forall_gt_eq_maximalIdeal' B (h * p) (mul_ne_zero hh hpB) (Ideal.mul_mem_left _ _ hpm)
  have hhq : h ∉ q := fun hq' => hxq (Ideal.mul_mem_right _ _ hq')
  have hpq : (p : B) ∉ q := fun hq' => hxq (Ideal.mul_mem_left _ _ hq')
  have hqm : q ≤ maximalIdeal B := le_maximalIdeal hq.ne_top
  set C := B ⧸ q
  haveI : Nontrivial C := Ideal.Quotient.nontrivial_iff.2 hq.ne_top
  haveI : IsLocalRing C := IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  let π : B →+* C := Ideal.Quotient.mk q
  have hπm : ∀ b ∈ maximalIdeal B, π b ∈ maximalIdeal C := by
    intro b hb hu
    obtain ⟨c, hc⟩ := hu.exists_right_inv
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
    have h1 : b * c' - 1 ∈ q := Ideal.Quotient.eq.1 (by simpa [π] using hc)
    have h2 : b * c' - 1 ∈ maximalIdeal B := hqm h1
    have h3 : b * c' ∈ maximalIdeal B := Ideal.mul_mem_right _ _ hb
    exact (maximalIdeal.isMaximal B).ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using Ideal.sub_mem _ h3 h2))
  have hmC : ∀ c ∈ maximalIdeal C, ∃ b ∈ maximalIdeal B, π b = c := by
    intro c hc
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨b, fun hb => hc ?_, rfl⟩
    exact hb.map π
  have hfinC : Finite (ResidueField C) := by
    let f : ResidueField B → ResidueField C :=
      Ideal.Quotient.lift (maximalIdeal B) ((residue C).comp π) (fun b hb => by
        rw [RingHom.comp_apply, residue_eq_zero_iff]; exact hπm b hb)
    refine Finite.of_surjective f ?_
    intro y
    obtain ⟨c, rfl⟩ := residue_surjective y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact ⟨residue B b, rfl⟩
  have hpC : (p : C) ≠ 0 := by
    rw [← map_natCast π, Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hpq
  have hpmC : (p : C) ∈ maximalIdeal C := by rw [← map_natCast π]; exact hπm _ hpm
  have hdim : ∀ P : Ideal C, P.IsPrime → P ≠ ⊥ → P = maximalIdeal C := by
    intro P hP hP0
    refine le_antisymm (le_maximalIdeal hP.ne_top) ?_
    have hlt : q < P.comap π := by
      refine lt_of_le_of_ne (fun b hb => ?_) (fun he => hP0 ?_)
      · show π b ∈ P; rw [Ideal.Quotient.eq_zero_iff_mem.2 hb]; exact P.zero_mem
      · rw [eq_bot_iff]; intro c hc
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
        have : b ∈ q := he ▸ hc
        exact (Submodule.mem_bot _).2 (Ideal.Quotient.eq_zero_iff_mem.2 this)
    have hc := hmax _ (Ideal.comap_isPrime π P) hlt
    intro c hc'
    obtain ⟨b, hb, rfl⟩ := hmC c hc'
    have : b ∈ P.comap π := hc ▸ hb
    exact this

  obtain ⟨N, hN⟩ : ∃ N : ℕ, maximalIdeal C ^ N ≤ Ideal.span {(p : C)} := by
    refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (IsNoetherian.noetherian _)
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P ⟨hle, hP⟩ => ?_
    have hP0 : P ≠ ⊥ := fun h0 => hpC (by rw [h0] at hle; exact (Submodule.mem_bot _).1 (hle (Ideal.mem_span_singleton_self _)))
    exact (hdim P hP hP0).ge
  obtain ⟨D, _, _, _, hDfin, ι, hι⟩ := GlobalTheory.T.exists_finite_padicInt_domain_embedding p C hfinC hpC hpmC hdim
  have hpD : (p : D) ≠ 0 := by
    rw [← map_natCast ι]; exact fun h0 => hpC (hι (by rw [h0, map_zero]))
  obtain ⟨φ, hφ, hφ1⟩ := GlobalTheory.T.exists_injective_norm_le_one_of_finite_padicInt_domain p D hpD
  refine ⟨p, hF, (φ.comp ι).comp π, fun b => hφ1 _, fun b hb => ?_, ?_⟩
  · have hc := hπm b hb
    have hcN : π b ^ N ∈ Ideal.span {(p : C)} := hN (Ideal.pow_mem_pow hc N)
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hcN
    have key : ‖(φ.comp ι) (π b)‖ ^ N < 1 ^ N := by
      rw [← norm_pow, ← map_pow, ← hd, map_mul, norm_mul, one_pow, map_natCast]
      calc ‖(φ.comp ι) d‖ * ‖(p : PadicAlgCl p)‖ ≤ 1 * ‖(p : PadicAlgCl p)‖ :=
            mul_le_mul_of_nonneg_right (hφ1 _) (norm_nonneg _)
        _ < 1 := by
          rw [one_mul]
          have e : ((p : ℚ_[p]) : PadicAlgCl p) = (p : PadicAlgCl p) := by simp
          rw [← e, norm_algebraMap']; exact Padic.norm_p_lt_one
    exact lt_of_pow_lt_pow_left₀ N zero_le_one key
  · intro h0
    apply hhq
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact hι (hφ (by simpa using h0))

end GlobalTheory.CurvePoint
end
