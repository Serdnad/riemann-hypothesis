module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1173
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle846
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1172
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiRegularAlongOfEtale
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section


open Classical in
theorem GlobalTheory.ResEtaOfPow.resEta_of_resEtaPow : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ),
    GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χ n → ResEta D χ n := by
  intro D χ n h
  refine ⟨GlobalTheory.VolHeckeCompare.exists_isEta D, fun η hη a => ?_⟩
  have hsq : ∀ x, η x * η x = 1 := GlobalTheory.VolHeckeCompare.IsEta_mul_self hη
  obtain ⟨-, h1, h2, h3⟩ := hη
  set S := (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range ⊔
    (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F)).range with hSdef
  have key : ∀ x, ((χ (idF D x) : Circle) : ℂ) = if x ∈ S then 1 else (-1) ^ n := fun x => h x
  have hS : ∀ x ∈ S, η x = 1 := by
    have : S ≤ η.ker := sup_le (by rintro _ ⟨y, rfl⟩; exact h1 y) (by rintro _ ⟨y, rfl⟩; exact h2 y)
    exact fun x hx => this hx
  apply Circle.ext
  rw [key a, Circle.coe_pow]
  by_cases ha : a ∈ S
  · rw [if_pos ha, hS a ha]; simp
  rw [if_neg ha]
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | hn
  · rw [← two_mul, pow_mul, pow_mul, neg_one_sq, one_pow, ← Circle.coe_pow, sq, hsq a]; simp
  have hn1 : ((-1 : ℂ)) ^ n = -1 := hn.neg_one_pow
  obtain ⟨b, hb⟩ : ∃ b, η b ≠ 1 := by
    by_contra hh
    push_neg at hh
    exact h3 (MonoidHom.ext hh)
  have hbS : b ∉ S := fun hm => hb (hS b hm)
  have hab : a * b ∈ S := by
    by_contra hn2
    have e := key (a * b)
    rw [map_mul, map_mul, Circle.coe_mul, key a, key b, if_neg ha, if_neg hbS, if_neg hn2, hn1] at e
    norm_num at e
  have hηb : (η b : ℂ) = -1 := GlobalTheory.VolHeckeCompare.circle_eq_neg_one (hsq b) hb
  have e2 : (η a : ℂ) * η b = 1 := by rw [← Circle.coe_mul, ← map_mul, hS _ hab]; simp
  rw [hηb] at e2
  have hηa : (η a : ℂ) = -1 := by linear_combination -e2
  rw [hηa]
end
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.h1_dim_bound_of_no_sections_nonneg_interNum : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X), L.IsLB → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → (∀ m : ℕ, 1 ≤ m → hdim k (twist F (lbPow L m)) 0 = 0) → 0 ≤ interNum k F (fun _ : Fin (d + 1) => L) → (∀ i, 2 ≤ i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d))) → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) 1 ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  first | exact @GlobalTheory.noSection_H1_bound_riemann_roch | exact GlobalTheory.noSection_H1_bound_riemann_roch | (intros; apply GlobalTheory.noSection_H1_bound_riemann_roch <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.nonempty_smoothLiftPresystem_squareZero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀), (∀ T, Algebra.Smooth R₀ (F.obj T)) → Nonempty (Pre I π F) := by
  first | exact @GlobalTheory.Obs.pre_nonempty | exact GlobalTheory.Obs.pre_nonempty | (intros; apply GlobalTheory.Obs.pre_nonempty <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DimRed

variable {R R₀ : Type} [CommRing R] [CommRing R₀]

abbrev qmap (π : R →+* R₀) (f : R) : R ⧸ Ideal.span {f} →+* R₀ ⧸ Ideal.span {π f} :=
  Ideal.quotientMap _ π (Ideal.span_le.2 (Set.singleton_subset_iff.2 (by
    rw [SetLike.mem_coe, Ideal.mem_comap]; exact Ideal.mem_span_singleton_self _)))

theorem qmap_facts (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π)
    (hk : RingHom.ker π = I) (f : R) :
    Function.Surjective (qmap π f) ∧ RingHom.ker (qmap π f) = I.map (Ideal.Quotient.mk _) ∧
      (I.map (Ideal.Quotient.mk (Ideal.span {f}))) ^ 2 = 0 ∧
      (qmap π f).comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp π := by
  refine ⟨Ideal.quotientMap_surjective hπ, ?_, ?_, Ideal.quotientMap_comp_mk _⟩
  · ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
    constructor
    · intro hx
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hx
      obtain ⟨r, rfl⟩ := hπ c
      refine ⟨x - r * f, ?_, ?_⟩
      · rw [← hk, RingHom.mem_ker, map_sub, map_mul, hc, sub_self]
      · rw [Ideal.Quotient.eq]
        simpa using Ideal.mul_mem_left _ r (Ideal.mem_span_singleton_self f)
    · rintro ⟨y, hy, hyx⟩
      rw [Ideal.Quotient.eq] at hyx
      have h1 : π (y - x) ∈ Ideal.span {π f} := by
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hyx
        rw [← hc, map_mul]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
      have h2 : π y = 0 := by rw [← RingHom.mem_ker, hk]; exact hy
      rw [map_sub, h2, zero_sub] at h1
      simpa using (Ideal.span {π f}).neg_mem h1
  · rw [← Ideal.map_pow, hI, Ideal.zero_eq_bot, Ideal.map_bot]; exact Ideal.zero_eq_bot.symm

theorem smooth_paste {X Y Z S T : Scheme.{0}} (p : X ⟶ S) (u : Y ⟶ S) (v : Z ⟶ Y) (w : T ⟶ S) (d : Z ⟶ T)
    (hw : d ≫ w = v ≫ u) (g : ℕ) (h : SmoothOfRelativeDimension g (pullback.snd p w)) :
    SmoothOfRelativeDimension g (pullback.snd (pullback.snd p u) v) := by
  have outer := (IsPullback.of_hasPullback (pullback.snd p u) v).paste_horiz (IsPullback.of_hasPullback p u)
  rw [← hw] at outer
  have sq := IsPullback.of_right
    (h₁₁ := pullback.lift (pullback.fst (pullback.snd p u) v ≫ pullback.fst p u)
      (pullback.snd (pullback.snd p u) v ≫ d) (by rw [Category.assoc]; exact outer.w))
    (by rw [pullback.lift_fst]; exact outer) (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback p w)
  exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback sq h

theorem smooth_zero_of_subsingleton [Subsingleton R₀] {X : Scheme.{0}} (p : X ⟶ Sp R₀) :
    SmoothOfRelativeDimension 0 p :=
  ⟨fun x ↦ absurd (Subsingleton.elim (⊤ : Ideal R₀) (p x).asIdeal) (p x).isPrime.ne_top.symm⟩

theorem lift_of_split (hU : UnobDim) (n : ℕ) : ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = 0 →
    ∀ (R₀ : Type) [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (A₀ : Over (Sp R₀)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ e : Fin n → R₀, CompleteOrthogonalIdempotents e →
    (∀ k, ∃ g : ℕ, SmoothOfRelativeDimension g
      (pullback.snd A₀.hom (spMap (Ideal.Quotient.mk (Ideal.span {1 - e k}))))) →
    ∃ (A : Over (Sp R)) (_ : GrpObj A) (i : A₀.left ⟶ A.left), IsGrpPullback A₀ A (spMap π) i ∧ IsAbelianScheme A := by
  induction n with
  | zero =>
    intro R _ I hI R₀ _ π hπ hk A₀ _ hA e he _
    have h01 : (0 : R₀) = 1 := by simpa using he.complete
    haveI : Subsingleton R₀ := subsingleton_of_zero_eq_one h01
    exact hU R I hI R₀ π hπ hk A₀ 0 hA (smooth_zero_of_subsingleton _)
  | succ n ih =>
    intro R _ I hI R₀ _ π hπ hk A₀ _ hA e he hsm
    have hnil : ∀ x ∈ RingHom.ker π, IsNilpotent x := fun x hx ↦ ⟨2, by
      rw [hk] at hx
      have h2 := Ideal.pow_mem_pow hx 2
      rw [hI] at h2
      simpa using h2⟩
    obtain ⟨ε, hε, hπε⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent π hnil (e 0) (hπ _) (he.idem 0)
    refine GlobalTheory.T.exists_abelianScheme_lift_of_splitRing R R₀ I hI π hπ hk ε hε A₀ hA ?_
    intro f hf
    obtain ⟨hρs, hρk, hρ2, hρc⟩ := qmap_facts I hI π hπ hk f
    let B : Over (Sp (R₀ ⧸ Ideal.span {π f})) := (Over.pullback (spMap (Ideal.Quotient.mk _))).obj A₀
    letI : GrpObj B := Functor.grpObjObj
    have hB : IsGrpPullback B A₀ (spMap (Ideal.Quotient.mk _)) (pullback.fst _ _) := isGrpPullback_pullback A₀ _
    have hBa : IsAbelianScheme B := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hB
    suffices H : ∃ (A : Over (Sp (R ⧸ Ideal.span {f}))) (_ : GrpObj A) (i : B.left ⟶ A.left),
        IsGrpPullback B A (spMap (qmap π f)) i ∧ IsAbelianScheme A by
      obtain ⟨A, _, i, h1, h2⟩ := H
      exact ⟨A, _, B, _, i, pullback.fst _ _, qmap π f, hρc, h1, hB, h2⟩
    rcases hf with rfl | rfl
    · have hm := he.map (Ideal.Quotient.mk (Ideal.span {π f}))
      refine ih (R ⧸ Ideal.span {f}) (I.map (Ideal.Quotient.mk _)) hρ2 (R₀ ⧸ Ideal.span {π f}) (qmap π f) hρs hρk
        B hBa (fun k ↦ Ideal.Quotient.mk _ (e k.succ)) ⟨⟨fun k ↦ hm.idem k.succ,
          fun i j hij ↦ hm.ortho ((Fin.succ_injective _).ne hij)⟩, ?_⟩ ?_
      · have hc := hm.complete
        rw [Fin.sum_univ_succ] at hc
        have h0 : Ideal.Quotient.mk (Ideal.span {π f}) (e 0) = 0 := by
          rw [Ideal.Quotient.eq_zero_iff_mem, ← hπε]; exact Ideal.mem_span_singleton_self _
        simpa [h0] using hc
      · intro k
        obtain ⟨g, hg⟩ := hsm k.succ
        refine ⟨g, smooth_paste A₀.hom _ _ _
          (spMap (Ideal.Quotient.lift (Ideal.span {1 - e k.succ})
            ((Ideal.Quotient.mk (Ideal.span {1 - Ideal.Quotient.mk (Ideal.span {π f}) (e k.succ)})).comp
              (Ideal.Quotient.mk (Ideal.span {π f}))) ?_)) ?_ g hg⟩
        · intro a ha
          obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
          have h0 : (Ideal.Quotient.mk (Ideal.span {1 - Ideal.Quotient.mk (Ideal.span {π f}) (e k.succ)}))
              (Ideal.Quotient.mk (Ideal.span {π f}) (1 - e k.succ)) = 0 := by
            rw [Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one]; exact Ideal.mem_span_singleton_self _
          rw [RingHom.comp_apply, map_mul, map_mul, h0, mul_zero]
        · rw [← Spec.map_comp, ← Spec.map_comp]
          congr 1
    · obtain ⟨g, hg⟩ := hsm 0
      have h1 : π (1 - ε) = 1 - e 0 := by rw [map_sub, map_one, hπε]
      rw [← h1] at hg
      exact hU _ _ hρ2 _ _ hρs hρk B g hBa hg

theorem abelianUnobstructed_of_unobDim : UnobDim → GlobalTheory.Published.AbelianUnobstructed := by
  intro hU R _ I hI R₀ _ π hπ hk A₀ _ hA
  obtain ⟨n, e, he, hsm⟩ := GlobalTheory.T.exists_idempotents_abelianScheme_constant_dimension R₀ A₀ hA
  exact lift_of_split hU n R I hI R₀ π hπ hk A₀ hA e he hsm

end GlobalTheory.DimRed
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etale_neighbourhood_kills_class : ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], IsUnit (q : B) → ∀ (P : Ideal B) [P.IsMaximal], IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime P)) → ∀ (m i : ℤ), 0 < m → ∀ y : Ht q (sp B) m i, ∃ (D : Type) (_ : CommRing D) (_ : Algebra B D) (_ : Algebra.Etale B D) (Q : Ideal D), Q.IsPrime ∧ Q.comap (algebraMap B D) = P ∧ (∀ d : D, ∃ b : B, d - algebraMap B D b ∈ Q) ∧ pull _ (spMap (algebraMap B D)) _ _ y = 0 := by
  first | (exact @GlobalTheory.EtC.oneCoh_main) | (exact GlobalTheory.EtC.oneCoh_main) | (intros; apply GlobalTheory.EtC.oneCoh_main <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Vanishing

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LB GlobalTheory.CechPic GlobalTheory.TangentOrigin
open H0

theorem eq_zero_of_forall_algHom_eq_zero {E A : Type} (Ω : Type) [Field E] [CommRing A]
    [Algebra E A] [Algebra.Etale E A] [Field Ω] [IsAlgClosed Ω] [Algebra E Ω] {a : A}
    (h : ∀ φ : A →ₐ[E] Ω, φ a = 0) : a = 0 := by
  have := Algebra.FormallyUnramified.finite_of_free E A
  have : IsReduced A := Algebra.FormallyUnramified.isReduced_of_field E A
  have : IsArtinianRing A := .of_finite E A
  refine IsNilpotent.eq_zero (nilpotent_iff_mem_prime.2 fun J hJ => ?_)
  have hm : J.IsMaximal := IsArtinianRing.isMaximal_of_isPrime J
  let := Ideal.Quotient.field J
  let ψ : (A ⧸ J) →ₐ[E] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have := h (ψ.comp (Ideal.Quotient.mkₐ E J))
  rw [AlgHom.comp_apply, map_eq_zero_iff ψ ψ.toRingHom.injective] at this
  exact Ideal.Quotient.eq_zero_iff_mem.1 this

section Points

variable {k R : Type} [CommRing k] [CommRing R] {S : Scheme.{0}}

theorem evalPt_algX (q : S ⟶ Sp k) (x : Sp R ⟶ S) (U : S.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (c : k) :
    evalPt x U h (algX q U c) =
      evalPt (x ≫ q) ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c) :=
  congrArg (fun g => (g ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c))
    (Scheme.Hom.appLE_comp_appLE x q ⊤ U ⊤ le_top h)

theorem evalPt_algX_of_eq (q : S ⟶ Sp k) (x : Sp R ⟶ S) {φ : k →+* R} (hx : x ≫ q = spMap φ)
    (U : S.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (c : k) : evalPt x U h (algX q U c) = φ c := by
  rw [evalPt_algX, hx, evalPt_spMap]

theorem H0.val_smul {q : S ⟶ Sp k} {N : LB S} {O : S.Opens} (x : Sp R ⟶ S) {φ : k →+* R}
    (hx : x ≫ q = spMap φ) (i : N.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ N.U i) (c : k)
    (f : H0 q N O) : val x i hO hi (c • f) = φ c * val x i hO hi f := by
  rw [base_smul, val_fun_smul, evalPt_algX_of_eq q x hx]


variable (R) in
abbrev PtsOver [Algebra k R] (q : S ⟶ Sp k) : Type :=
  {x : Sp R ⟶ S // x ≫ q = spMap (algebraMap k R)}

def ptsOverEquiv [Algebra k R] [IsAffine S] (q : S ⟶ Sp k) :
    letI := (algX q ⊤).toAlgebra
    PtsOver R q ≃ (Γ(S, ⊤) →ₐ[k] R) :=
  letI := (algX q ⊤).toAlgebra
  Equiv.ofBijective
    (fun x => ⟨evalPt x.1 ⊤ le_top, fun c => evalPt_algX_of_eq q x.1 x.2 ⊤ le_top c⟩)
    ⟨fun x y e => Subtype.ext (ext_evalPt (isAffineOpen_top S) le_top le_top
      (congrArg AlgHom.toRingHom e)), fun ψ => by
      obtain ⟨x, h, e⟩ := exists_evalPt_eq (isAffineOpen_top S) ψ.toRingHom
      refine ⟨⟨x, eq_spMap_of_evalPt _ _ fun c => ?_⟩, AlgHom.ext fun a => DFunLike.congr_fun e a⟩
      rw [← evalPt_algX q x ⊤ h, e]
      exact ψ.commutes c⟩

end Points

section FiniteEtale

variable {E : Type} [Field E] {S : Scheme.{0}} (q : S ⟶ Sp E)

theorem etale_algX [IsAffine S] [Etale q] : (algX q ⊤).Etale :=
  RingHom.Etale.respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of E)).symm.commRingCatIsoToRingEquiv
    (HasRingHomProperty.appLE @Etale q ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨⊤, isAffineOpen_top _⟩ le_top)

variable {N : LB S}

theorem exists_generator [IsFinite q] [Etale q] (hN : N.IsLB) : ∃ e : H0 q N ⊤,
    (Function.Bijective fun a : Γ(S, ⊤) => a • e) ∧ ∀ i, IsUnit (e.loc i) := by
  have : IsAffine S := isAffine_of_isAffineHom q
  let := (algX q ⊤).toAlgebra
  have : Algebra.Etale E Γ(S, ⊤) := etale_algX q
  have := Algebra.FormallyUnramified.finite_of_free E Γ(S, ⊤)
  have : IsArtinianRing Γ(S, ⊤) := .of_finite E _
  obtain ⟨t, ht⟩ := exists_isGen_of_subsingleton_pic_top hN
  refine ⟨H0.ofSec q ⊤ (DVR.genSec t ht), ?_, fun i => (Units.isUnit (t.s i)).map (resG S inf_le_right)⟩
  have := isQuasicoherent_toMod hN
  exact (isFrame_iff_bijective (isAffineOpen_top S) _).1 (isFrame_genSec hN ht ⊤)

variable (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra E Ω] [IsFinite q] [Etale q]


omit [IsAlgClosed Ω] in
theorem finite_ptsOver : Finite (PtsOver Ω q) := by
  have : IsAffine S := isAffine_of_isAffineHom q
  let := (algX q ⊤).toAlgebra
  have : Algebra.Etale E Γ(S, ⊤) := etale_algX q
  have := Algebra.FormallyUnramified.finite_of_free E Γ(S, ⊤)
  exact Finite.of_equiv _ (ptsOverEquiv q).symm

theorem finite_finrank_lineBundleSections_finiteEtale (hN : N.IsLB) :
    Module.Finite E (H0 q N ⊤) ∧ Module.finrank E (H0 q N ⊤) = Nat.card (PtsOver Ω q) := by
  have : IsAffine S := isAffine_of_isAffineHom q
  let := (algX q ⊤).toAlgebra
  have : Algebra.Etale E Γ(S, ⊤) := etale_algX q
  have := Algebra.FormallyUnramified.finite_of_free E Γ(S, ⊤)
  obtain ⟨e, he, -⟩ := exists_generator q hN
  let ψ : Γ(S, ⊤) →ₗ[E] H0 q N ⊤ :=
    { toFun a := a • e
      map_add' a b := add_smul a b e
      map_smul' c a := mul_smul (algX q ⊤ c) a e }
  let φ := LinearEquiv.ofBijective ψ he
  exact ⟨.equiv φ, by
    rw [← φ.finrank_eq, Nat.card_congr (ptsOverEquiv q), natCard_algHom_eq_finrank_of_etale]⟩

variable {q Ω}

theorem H0.eq_zero_of_forall_val_eq_zero (hN : N.IsLB) (i : PtsOver Ω q → N.ι)
    (hi : ∀ x : PtsOver Ω q, ⊤ ≤ x.1 ⁻¹ᵁ N.U (i x)) {g : H0 q N ⊤}
    (h : ∀ x : PtsOver Ω q, val x.1 (i x) le_top (hi x) g = 0) : g = 0 := by
  have : IsAffine S := isAffine_of_isAffineHom q
  let := (algX q ⊤).toAlgebra
  have : Algebra.Etale E Γ(S, ⊤) := etale_algX q
  obtain ⟨e, he, hu⟩ := exists_generator q hN
  obtain ⟨a, rfl⟩ := he.2 g
  have : a = 0 := eq_zero_of_forall_algHom_eq_zero (E := E) Ω fun ψ => by
    obtain ⟨x, rfl⟩ := (ptsOverEquiv q).surjective ψ
    have := (val_fun_smul x.1 (i x) le_top (hi x) a e).symm.trans (h x)
    exact (((hu (i x)).map (evalPt x.1 _ _)).mul_left_eq_zero).1 this
  simp only [this, zero_smul]

end FiniteEtale

section Subscheme

variable {E : Type} [Field E] {Y : Scheme.{0}} {p : Y ⟶ Sp E} {I : Y.IdealSheafData} {B : LB Y}

theorem exists_chart_of_field {F : Type} [Field F] (hB : B.IsLB) (x : Sp F ⟶ Y) :
    ∃ i, ⊤ ≤ x ⁻¹ᵁ B.U i := by
  obtain ⟨i, hi⟩ := exists_chart hB (x (default : PrimeSpectrum F))
  exact ⟨i, fun z _ => (Subsingleton.elim (α := PrimeSpectrum F) default z) ▸ hi⟩

theorem valOn_smul {k R : Type} [CommRing k] [CommRing R] {p : Y ⟶ Sp k}
    (x : Sp R ⟶ I.subscheme) {φ : k →+* R} (hx : x ≫ I.subschemeι ≫ p = spMap φ) (i : B.ι)
    (hi : ⊤ ≤ (x ≫ I.subschemeι) ⁻¹ᵁ B.U i) (c : k) (g : sectionsOnClosedSubscheme p B I) :
    valOn x i hi (c • g) = φ c * valOn x i hi g :=
  H0.val_smul x hx _ _ _ c g

variable [IsFinite (I.subschemeι ≫ p)] [Etale (I.subschemeι ≫ p)] (hB : B.IsLB)
  (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra E Ω]

include hB

theorem finite_H0On : Module.Finite E (sectionsOnClosedSubscheme p B I) :=
  (finite_finrank_lineBundleSections_finiteEtale _ (AlgebraicClosure E) (LB.isLB_pull hB _)).1

theorem finrank_H0On :
    Module.finrank E (sectionsOnClosedSubscheme p B I) = Nat.card (PtsOver Ω (I.subschemeι ≫ p)) :=
  (finite_finrank_lineBundleSections_finiteEtale _ Ω (LB.isLB_pull hB _)).2


variable {Ω} in
theorem eq_zero_of_forall_valOn_eq_zero (i : PtsOver Ω (I.subschemeι ≫ p) → B.ι)
    (hi : ∀ x : PtsOver Ω (I.subschemeι ≫ p), ⊤ ≤ (x.1 ≫ I.subschemeι) ⁻¹ᵁ B.U (i x))
    {g : sectionsOnClosedSubscheme p B I} (h : ∀ x : PtsOver Ω (I.subschemeι ≫ p), valOn x.1 (i x) (hi x) g = 0) : g = 0 :=
  H0.eq_zero_of_forall_val_eq_zero (LB.isLB_pull hB _) (fun x _ => i x) _ h

end Subscheme

end GlobalTheory.Vanishing
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.FiberTwo

theorem eq_or_eq_of_under_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (w u u' : Pl E) (hu : u ≠ w)
    (h : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)))
    (h' : u'.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) : u' = w ∨ u' = u := by
  have hr := Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E
  have hc := IsCMField.complexConj_ne_one (K := E)
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E) hr hc w u).1 h with h1 | h1
  · exact absurd h1 hu
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E) hr hc w u').1 h' with h2 | h2
  · exact Or.inl h2
  · exact Or.inr ((GlobalTheory.Mem.Chr.existsUnique_conjPl _ w).unique h2 h1)

end GlobalTheory.BCT.FiberTwo
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

theorem exists_mem_section_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Set (Pl E)), IsSection S →
    ∀ u : Pl E, u ∉ S → ∃ w ∈ S, ∀ x : E, u.valuation E x = w.valuation E (IsCMField.complexConj E x) := by
  intro E _ _ _ S hS u hu
  obtain ⟨w, ⟨hwS, hwu⟩, -⟩ := hS u
  refine ⟨w, hwS, ?_⟩
  have hr : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E) hr (IsCMField.complexConj_ne_one E) u w).1 hwu
    with h | h
  · exact absurd (h ▸ hwS) hu
  · intro x
    exact (h x).symm

end GlobalTheory.BCT
end
