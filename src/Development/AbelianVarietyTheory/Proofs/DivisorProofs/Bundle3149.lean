module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3139
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3090
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1089
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1061
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3089
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle032
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1773
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2593
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle932
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3092
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
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MoveNear

theorem exists_section_translate_mem : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (N : Near π G') (e : Sp R ⟶ N.U.left), e ≫ N.U.hom = 𝟙 _ → N.Pt (𝟙 S) (π ≫ e) (1 : Over.mk (𝟙 S) ⟶ G').left → ∀ (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (g : Over.mk s ⟶ G'), IrreducibleSpace (pullback G'.hom s : Scheme.{0}) → closedPoint R ∉ Set.range (s ≫ π) → ∃ (a : Sp R ⟶ N.U.left) (x : Over.mk (𝟙 S) ⟶ G'), a ≫ N.U.hom = 𝟙 _ ∧ N.Pt (𝟙 S) (π ≫ a) x.left ∧ Set.range (g * (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x).left ⊆ Set.range N.u := by
  intro R _ _ _ hR S π G' _ _ _ N e he hPt Ω _ s g hT hs
  haveI := N.isOpen
  haveI := hR.1
  let xR := s ≫ π
  let UΩ := pullback N.U.hom xR
  let T := pullback G'.hom s
  let m : UΩ ⟶ pullback N.U.hom π := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ s)
    (by rw [Category.assoc]; exact pullback.condition)
  let k : UΩ ⟶ T := pullback.lift (m ≫ N.u) (pullback.snd _ _)
    (by rw [Category.assoc, N.u_over, pullback.lift_snd])
  have sqP : IsPullback m (pullback.snd N.U.hom xR) (pullback.snd N.U.hom π) s := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback N.U.hom π)
    rw [pullback.lift_fst]
    exact IsPullback.of_hasPullback N.U.hom xR
  have sqk : IsPullback m k N.u (pullback.fst G'.hom s) := by
    refine IsPullback.of_bot (v₂₁ := pullback.snd G'.hom s) (v₂₂ := G'.hom) (h₃₁ := s) ?_ (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback G'.hom s)
    rw [pullback.lift_snd, N.u_over]
    exact sqP
  have hk : IsOpenImmersion k := MorphismProperty.of_isPullback (P := @IsOpenImmersion) sqk N.isOpen
  let TO : Over S := Over.mk (pullback.snd G'.hom s ≫ s)
  let yT : TO ⟶ G' := Over.homMk (pullback.fst G'.hom s) pullback.condition
  let qT : TO ⟶ Over.mk s := Over.homMk (pullback.snd G'.hom s) rfl
  let zT : TO ⟶ G' := (qT ≫ g) * yT
  let UO : Over S := Over.mk (pullback.snd N.U.hom xR ≫ s)
  let kO : UO ⟶ TO := Over.homMk k (by
    change k ≫ pullback.snd _ _ ≫ s = _
    rw [pullback.lift_snd_assoc]
    rfl)
  have sec : ∀ h : Over.mk s ⟶ G', ∃ σ : Over.mk s ⟶ TO, σ ≫ yT = h ∧ σ ≫ qT = 𝟙 _ := fun h =>
    ⟨Over.homMk (pullback.lift h.left (𝟙 _) ((Over.w h).trans (Category.id_comp _).symm))
      (by
        change pullback.lift _ _ _ ≫ pullback.snd G'.hom s ≫ s = s
        rw [pullback.lift_snd_assoc]
        exact Category.id_comp _),
      Over.OverMorphism.ext (pullback.lift_fst _ _ _), Over.OverMorphism.ext (pullback.lift_snd _ _ _)⟩
  have hone : ∀ p, (1 : Over.mk s ⟶ G').left p ∈ Set.range N.u := by
    obtain ⟨x₀, -, -, hx₀⟩ := hPt
    have e₁ : (1 : Over.mk s ⟶ G').left = s ≫ (1 : Over.mk (𝟙 S) ⟶ G').left := congrArg (fun f => f.left)
      (MonObj.comp_one (M := G') (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S))).symm
    intro p
    rw [e₁, ← hx₀]
    exact ⟨x₀ (s p), rfl⟩
  have hoU : IsOpen (Set.range N.u) := N.u.isOpenEmbedding.isOpen_range
  obtain ⟨σ₁, h₁, -⟩ := sec 1
  obtain ⟨σ₂, h₂, h₂'⟩ := sec g⁻¹
  have e₂ : σ₂ ≫ zT = 1 := by
    rw [MonObj.comp_mul, h₂, ← Category.assoc, h₂', Category.id_comp, mul_inv_cancel]
  have : IrreducibleSpace T := hT
  obtain ⟨t, ⟨p₀, hp₀⟩, ht⟩ := nonempty_preirreducible_inter (hoU.preimage (pullback.fst G'.hom s).continuous)
    (hoU.preimage zT.left.continuous)
    ⟨σ₁.left (IsLocalRing.closedPoint _), by
      have := hone (IsLocalRing.closedPoint _)
      rw [← h₁] at this
      exact this⟩
    ⟨σ₂.left (IsLocalRing.closedPoint _), by
      have := hone (IsLocalRing.closedPoint _)
      rw [← e₂] at this
      exact this⟩
  obtain ⟨w, -, hw⟩ := Scheme.exists_preimage_of_isPullback sqk p₀ t hp₀
  let O : UΩ.Opens := ⟨(kO ≫ zT).left ⁻¹' Set.range N.u, hoU.preimage (kO ≫ zT).left.continuous⟩
  have hwO : w ∈ O := by
    show (kO ≫ zT).left w ∈ Set.range N.u
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    change zT.left (k w) ∈ Set.range N.u
    rw [hw]; exact ht
  have hirr : IrreducibleSpace UΩ := by
    refine (irreducibleSpace_def _).2 ⟨⟨w, trivial⟩, ?_⟩
    have := (IrreducibleSpace.isIrreducible_univ T).2.preimage k.isOpenEmbedding
    simpa using this
  obtain ⟨a, aΩ, ha, haf, has, hao⟩ := GlobalTheory.T.smoothGroup_sections_dense_in_fibres R hR.2.2.2 N.U N.smooth e he Ω xR hs hirr O ⟨w, hwO⟩
  let x : Over.mk (𝟙 S) ⟶ G' := Over.homMk
    (pullback.lift (π ≫ a) (𝟙 S) (by rw [Category.assoc, ha, Category.comp_id]; exact (Category.id_comp π).symm) ≫ N.u)
    (by rw [Category.assoc, N.u_over, pullback.lift_snd]; rfl)
  refine ⟨a, x, ha, ⟨_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, rfl⟩, ?_⟩
  let rO : Over.mk s ⟶ UO := Over.homMk aΩ (by
    change aΩ ≫ pullback.snd _ _ ≫ s = s
    rw [← Category.assoc, has, Category.id_comp])
  have hq : rO ≫ kO ≫ qT = 𝟙 _ := by
    ext
    change aΩ ≫ k ≫ pullback.snd _ _ = 𝟙 _
    rw [pullback.lift_snd, has]
  have hy : rO ≫ kO ≫ yT = (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x := by
    ext
    change aΩ ≫ k ≫ pullback.fst _ _ = s ≫ pullback.lift (π ≫ a) (𝟙 S) _ ≫ N.u
    rw [pullback.lift_fst, ← Category.assoc, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      show aΩ ≫ pullback.lift (pullback.fst N.U.hom xR) _ _ ≫ pullback.fst N.U.hom π = s ≫ π ≫ a
      rw [pullback.lift_fst, haf]
      simp only [xR, Category.assoc]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc, has,
        Category.id_comp, Category.comp_id]
  have hz : g * ((Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x) = rO ≫ kO ≫ zT := by
    have hq' : (rO ≫ kO) ≫ qT = 𝟙 _ := by rw [Category.assoc]; exact hq
    have hy' : (rO ≫ kO) ≫ yT = (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x := by
      rw [Category.assoc]; exact hy
    rw [← Category.assoc, MonObj.comp_mul, ← Category.assoc, hq', Category.id_comp, hy']
  rintro _ ⟨p, rfl⟩
  rw [hz]
  exact hao ⟨p, rfl⟩

end GlobalTheory.MoveNear
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem _root_.GlobalTheory.T.twistedRelation_cocycle_in_translation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (n j : ℤ) (ν mu β₀ β₁ β₂ : D.toPre.X) (s₀ : SecT D.toPre a n j β₀) (s₁ : SecT D.toPre a n j β₁) (s₂ : SecT D.toPre a n j β₂), β₁ = β₀ + shift h h' n j ν → β₂ = β₁ + shift h h' n j mu → TRel h ν s₀ s₁ → TRel h (ν + mu) s₀ s₂ → TRel h mu s₁ s₂ := by
  first | exact @GlobalTheory.TwFam.trel_cocycle | exact GlobalTheory.TwFam.trel_cocycle | (intros; apply GlobalTheory.TwFam.trel_cocycle <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem _root_.GlobalTheory.T.twistedRelation_mul_of_related_pairs : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (n j n' j' n'' j'' : ℤ), n'' = n + n' → j'' = j + j' → ∀ (mu β β' β₁ β₁' : D.toPre.X) (f : SecT D.toPre a n j β) (g : SecT D.toPre a n' j' β') (p : SecT D.toPre a n'' j'' (β + β')) (f₁ : SecT D.toPre a n j β₁) (g₁ : SecT D.toPre a n' j' β₁') (p₁ : SecT D.toPre a n'' j'' (β₁ + β₁')), β₁ = β + shift h h' n j mu → β₁' = β' + shift h h' n' j' mu → IsProdT f g p → IsProdT f₁ g₁ p₁ → TRel h mu f f₁ → TRel h mu g g₁ → TRel h mu p p₁ := by
  first | exact @GlobalTheory.TwFam.ProdRel.trel_prod | exact GlobalTheory.TwFam.ProdRel.trel_prod | (intros; apply GlobalTheory.TwFam.ProdRel.trel_prod <;> assumption)
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.Step

theorem exists_sq_zero (R : Type) [CommRing R] [IsNoetherianRing R] (h : ¬ IsReduced R) :
    ∃ J : Ideal R, J ≠ ⊥ ∧ J ^ 2 = ⊥ := by
  classical
  set N := nilradical R with hNdef
  have hN : N ≠ ⊥ := by
    intro h0
    apply h
    refine ⟨fun x hx => ?_⟩
    have : x ∈ N := (mem_nilradical).2 hx
    rw [h0] at this
    exact (Submodule.mem_bot R).1 this
  have hnil : IsNilpotent N := IsNoetherianRing.isNilpotent_nilradical R
  let n := Nat.find hnil
  have hn : N ^ n = 0 := Nat.find_spec hnil
  have hn0 : n ≠ 0 := by
    intro h0
    have : N ^ 0 = 0 := h0 ▸ hn
    rw [pow_zero] at this
    apply hN
    rw [eq_bot_iff, ← Ideal.zero_eq_bot, ← this, Ideal.one_eq_top]
    exact le_top
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hN
    rw [hk] at hn
    simpa using hn
  refine ⟨N ^ k, ?_, ?_⟩
  · intro h0
    have := Nat.find_min hnil (show k < n by omega)
    exact this h0
  · rw [← pow_mul]
    apply le_bot_iff.1
    calc N ^ (k * 2) ≤ N ^ (k + 1) := Ideal.pow_le_pow_right (by omega)
      _ = ⊥ := by rw [← Nat.succ_eq_add_one, ← hk]; exact hn

theorem hasRep_opens {S X : Scheme.{0}} (i : X ⟶ S) [IsOpenImmersion i] (A : Over S) [GrpObj A] (g : ℕ)
    (V : S.Opens) (hV : (V : Set S) ⊆ Set.range i) (h : HasRep A g (Over.mk i)) : HasRep A g (Over.mk V.ι) := by
  have hr : Set.range V.ι ⊆ Set.range i := by
    rw [Scheme.Opens.range_ι]; exact hV
  let m : Over.mk V.ι ⟶ Over.mk i := Over.homMk (IsOpenImmersion.lift i V.ι hr) (IsOpenImmersion.lift_fac _ _ _)
  exact GlobalTheory.T.baseChangeBis S A (Over.mk i) (Over.mk V.ι) g m h

theorem comap_ne_bot_away {R : Type} [CommRing R] (f : R) (J' : Ideal (Localization.Away f)) (h : J' ≠ ⊥) :
    J'.comap (algebraMap R (Localization.Away f)) ≠ ⊥ := by
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) y
  have hx : algebraMap R (Localization.Away f) x ∈ J' := by
    rw [← IsLocalization.mk'_spec (Localization.Away f) x s]
    exact J'.mul_mem_right _ hy
  have hx0 : algebraMap R (Localization.Away f) x ≠ 0 := by
    intro h0
    apply hy0
    rw [IsLocalization.mk'_eq_zero_iff]
    exact (IsLocalization.map_eq_zero_iff (Submonoid.powers f) _ x).1 h0
  intro hb
  have : x ∈ J'.comap (algebraMap R (Localization.Away f)) := hx
  rw [hb, Submodule.mem_bot] at this
  exact hx0 (by rw [this, map_zero])

theorem hasRep_quot {R R' : Type} [CommRing R] [CommRing R'] (a : R →+* R')
    (ha : ∀ J' : Ideal R', J' ≠ ⊥ → J'.comap a ≠ ⊥) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A']
    (φ : A'.left ⟶ A.left) (hφ : IsGrpPullback A' A (spMap a) φ) (g : ℕ)
    (hJ : ∀ J : Ideal R, J ≠ ⊥ → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk J)))) :
    ∀ J' : Ideal R', J' ≠ ⊥ → HasRep A' g (Over.mk (spMap (Ideal.Quotient.mk J'))) := by
  intro J' hJ'
  set J := J'.comap a
  let q : R ⧸ J →+* R' ⧸ J' := Ideal.quotientMap J' a le_rfl
  have hq : q.comp (Ideal.Quotient.mk J) = (Ideal.Quotient.mk J').comp a := by
    ext x; rfl
  have w : spMap q ≫ spMap (Ideal.Quotient.mk J) = (Over.mk (spMap (Ideal.Quotient.mk J') ≫ spMap a)).hom := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  let m : Over.mk (spMap (Ideal.Quotient.mk J') ≫ spMap a) ⟶ Over.mk (spMap (Ideal.Quotient.mk J)) :=
    Over.homMk (spMap q) w
  have h1 := GlobalTheory.T.baseChangeBis _ A _ _ g m (hJ J (ha J' hJ'))
  exact ((GlobalTheory.T.hasProperSmoothDualRepresentative_grpPullback_iff _ _ (spMap a) A A' φ hφ g (Over.mk (spMap (Ideal.Quotient.mk J')))).1).2 h1

theorem local_rep (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] [IsReduced R] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (hJ : ∀ J : Ideal R, J ≠ ⊥ → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk J)))) (s : Sp R) :
    ∃ V : (Sp R).Opens, s ∈ V ∧ HasRep A g (Over.mk V.ι) := by
  obtain ⟨f, hs, W, hW, hWf⟩ := GlobalTheory.T.exists_basicOpen_affineOpen_meeting_fibres_grpScheme R A s
  let a := algebraMap R (Localization.Away f)
  let A' := (Over.pullback (spMap a)).obj A
  letI : (Over.pullback (spMap a)).Monoidal := (Over.instBraidedPullback (f := spMap a)).toMonoidal
  letI : GrpObj A' := Functor.grpObjObj
  have hφ : IsGrpPullback A' A (spMap a) (pullback.fst _ _) := isGrpPullback_pullback A (spMap a)
  obtain ⟨hA', hg'⟩ := GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback a A A' _ g hφ hA hg
  obtain ⟨V, hV, hVs⟩ := GlobalTheory.T.affineOpen_meeting_fibres_pullback_specRingHom a A W hW hWf
  haveI : @Algebra.FiniteType ℤ (Localization.Away f) _ _ (Ring.toIntAlgebra _) := by
    have h := Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType ℤ R)
      (IsLocalization.finiteType_of_monoid_fg (Submonoid.powers f) (Localization.Away f))
    convert h using 1 <;> first | rfl | exact Subsingleton.elim _ _
  have h1 : HasRep A' g (𝟙_ _) :=
    GlobalTheory.T.hasProperSmoothDualRepresentative_noetherianInduction (Localization.Away f) A' g hA' hg' V hV hVs
      (hasRep_quot a (comap_ne_bot_away f) A A' _ hφ g hJ)
  have h2 := ((GlobalTheory.T.hasProperSmoothDualRepresentative_grpPullback_iff _ _ (spMap a) A A' _ hφ g (𝟙_ _)).1).1 h1
  have h3 : HasRep A g (Over.mk (spMap a)) := by
    convert h2 using 2 <;> first | rfl | exact (Category.id_comp _).symm
  have : IsOpenImmersion (spMap a) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))))
  refine ⟨(spMap a).opensRange, hs, hasRep_opens (spMap a) A g _ (fun x hx => hx) h3⟩

theorem step : ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (∀ J : Ideal R, J ≠ ⊥ → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk J)))) → HasRep A g (𝟙_ _) := by
  intro R _ _ A _ g hA hg hJ
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  by_cases hr : IsReduced R
  · exact GlobalTheory.T.hasProperSmoothDualRepresentative_of_local _ A g hA (local_rep R A g hA hg hJ)
  · obtain ⟨J, hJ0, hJ2⟩ := exists_sq_zero R hr
    exact GlobalTheory.T.hasProperSmoothDualRepresentative_of_sqZero R A g hA hg J hJ2 (hJ J hJ0)

end GlobalTheory.DualCon.Step
end
end

section

set_option autoImplicit false

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.FlatCore.NonzeroCusp

theorem laU_const {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (V : Unf Xo c σ r) (m n : ℕ) (k : V.Comp) :
    laU V (fun _ => m) n k = laU V 0 (n + 2 * m) k := by
  funext τ j
  have e : (n + 2 * m) / 2 = n / 2 + m := by omega
  simp only [laU, Pi.zero_apply, e]
  split_ifs <;> push_cast <;> ring

theorem exists_cuspOn_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c), ∃ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n ∧ (∀ τ i, i < Dw.mult τ → 2 ≤ a (τ, i)) ∧ 4 * (finrank ℚ E * r) + 4 ≤ n ∧ ∃ f ∈ cuspOn U Z (wtZ a n), f ≠ 0 := by
  intro E _ _ _ H Dw l Xo c r U x hL Z
  have hσ : GoodEmb c c.F.val.toRingHom := rfl
  obtain ⟨n₀, hn₀, hev, f₀, hf₀, ⟨k, y⟩, hz, hne⟩ := GlobalTheory.T.exists_nonzero_scalarWeight_cuspForm_component E H Dw l Xo c r U x hL _ hσ Z
  obtain ⟨hy, hlies⟩ := hz
  have hM : CuspMul Xo c U := cusp_mul_of_M5 siegelSpaceAlgebra_holds U
  have hD0 : ∀ m, Even m → Dom (0 : (E →+* ℂ) × ℕ → ℕ) m := fun m hm => ⟨fun _ => antitone_const, hm⟩
  have hpow : ∀ j : ℕ, f₀ ^ (j + 1) ∈ cusp Xo c U 0 ((j + 1) * n₀) := by
    intro j
    induction j with
    | zero => simpa using hf₀
    | succ j ih =>
      have h := hM 0 0 ((j + 1) * n₀) n₀ (f₀ ^ (j + 1)) f₀ (hD0 _ (hev.mul_left _)) (hD0 _ hev) ih hf₀
      have e1 : ((j + 1) * n₀ + n₀) = (j + 1 + 1) * n₀ := by ring
      rw [add_zero, e1] at h
      rw [pow_succ]
      exact h
  have hrd : ∀ j : ℕ, rdU (U c.F.val.toRingHom) (f₀ ^ (j + 1)) k y = (rdU (U c.F.val.toRingHom) f₀ k y) ^ (j + 1) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, Formalism.L2.Pj.rdU_mul, Pi.mul_apply, Pi.mul_apply, ih]
      ring
  set M : ℕ := 4 * (finrank ℚ E * r) + 7 with hMdef
  obtain ⟨t, ht⟩ := hev
  have hMt : (M + 1) * n₀ = (M + 1) * t + (M + 1) * t := by rw [ht]; ring
  have ht1 : 1 ≤ t := by omega
  have hMt1 : M + 1 ≤ (M + 1) * t := Nat.le_mul_of_pos_right _ ht1
  set n : ℕ := (M + 1) * n₀ - 4 with hndef
  have hnev : Even n := ⟨(M + 1) * t - 2, by omega⟩
  have hnb : 4 * (finrank ℚ E * r) + 4 ≤ n := by omega
  have hn4 : n + 2 * 2 = (M + 1) * n₀ := by omega
  have hP : rdU (U c.F.val.toRingHom) (f₀ ^ (M + 1)) ∈
      holSub0 (U c.F.val.toRingHom).X (laU (U c.F.val.toRingHom) (fun _ => 2) n) := by
    have e : laU (U c.F.val.toRingHom) (fun _ => 2) n = laU (U c.F.val.toRingHom) 0 ((M + 1) * n₀) :=
      funext fun k' => by rw [laU_const, hn4]
    rw [e]
    exact ⟨((mem_cusp Xo c U 0 _ _).1 (hpow M)).2 _ hσ, rdU_mem_offZero _ _⟩
  have hspan := hL.onto _ hσ (fun _ => 2) n ⟨fun _ => antitone_const, hnev⟩ (fun _ _ _ => by norm_num) hnb hP
  obtain ⟨f, hf, hfy⟩ : ∃ f ∈ cusp Xo c U (fun _ => 2) n, rdU (U c.F.val.toRingHom) f k y ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    let ev : FDSec (U c.F.val.toRingHom).X →ₗ[ℂ] ℂ :=
      { toFun := fun P => P k y, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hle : Submodule.span ℂ (rdU (U c.F.val.toRingHom) '' (cusp Xo c U (fun _ => 2) n : Set (Rul Xo c))) ≤
        LinearMap.ker ev := by
      rw [Submodule.span_le]
      rintro _ ⟨f, hf, rfl⟩
      exact hcon f hf
    have h0 : ev (rdU (U c.F.val.toRingHom) (f₀ ^ (M + 1))) = 0 := hle hspan
    have h1 : ev (rdU (U c.F.val.toRingHom) (f₀ ^ (M + 1))) = (rdU (U c.F.val.toRingHom) f₀ k y) ^ (M + 1) := hrd M
    exact pow_ne_zero _ hne (h1.symm.trans h0)
  obtain ⟨g, hg, -⟩ := GlobalTheory.CompRestr.exists_cuspOn_restrict E H Dw l Xo c r U hL.unf Z (wtZ (fun _ => 2) n)
    ⟨f, by rw [cuspW_wtZ]; exact hf⟩
  refine ⟨fun _ => 2, n, ⟨fun _ => antitone_const, hnev⟩, fun _ _ _ => le_rfl, hnb, g, g.2, ?_⟩
  intro h0
  have e : rdU (U c.F.val.toRingHom) (g : Rul Xo c) k y = rdU (U c.F.val.toRingHom) f k y := by
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hy]
    rw [hg _ _ hlies]
  rw [h0, map_zero] at e
  exact hfy e.symm

end GlobalTheory.FlatCore.NonzeroCusp
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem _root_.GlobalTheory.T.flatLineDegree_eq_eigenLattice_degree_sub : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (ρ : HeightOneSpectrum (𝓞 c.F) → ℝ), (∀ la, ∀ w ∈ valOn Z la, w s.sig = (ρ la : EReal)) → ∀ (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → ∀ (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)), Nonempty (SABMap t₀ Xo.univ.t y.x) → Nonempty (SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) → ∀ (F : GlobalTheory.CM.GenFib B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ t : 𝓞 E →+* 𝓞 K, (∀ a, ((t a : 𝓞 K) : K) = algebraMap c.F K (embK c τ.1 a)) → (Function.support ρ).Finite ∧ lineDeg s.cInf ρ = ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat B.t.act t) - ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat B.t.act (t.comp (H.bar : 𝓞 E →+* 𝓞 E))) := by
  first | exact @GlobalTheory.PtDeg.lineDeg_eq_deg_eigLat_sub | exact GlobalTheory.PtDeg.lineDeg_eq_deg_eigLat_sub | (intros; apply GlobalTheory.PtDeg.lineDeg_eq_deg_eigLat_sub <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.mixedIntegral_pullback_genericallyFinite : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ), Measurable f → (Intg (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) ↔ Intg L f) ∧ Mix.int (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) = π.residueDegree (genericPoint Y) * Mix.int L f := by
  first | exact @GlobalTheory.PushInt.mixInt_pull | exact GlobalTheory.PushInt.mixInt_pull | (intros; apply GlobalTheory.PushInt.mixInt_pull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Ex.OneGen
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.uniformised_trait_theta_constants_two_levels_integral : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W], IsAdicComplete (IsLocalRing.maximalIdeal W) W → ∀ (D : DegData W (IsLocalRing.maximalIdeal W)) (A : PolAV (Sp (FractionRing W))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (_ : Unif (IsLocalRing.maximalIdeal W) D A G) (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] (io : FractionRing W →+* K) (m m' N N' : ℕ) (d : Fin N → K) (d' : Fin N' → K), Odd m → 3 ≤ m → IsUnit (m : W) → Odd m' → 3 ≤ m' → IsUnit (m' : W) → (letI := A.isAb.comm; HasTh₂ A.A A.L ρ m m' (spMap io) d d') → ∃ a : K, a ≠ 0 ∧ Prim (io.comp (algebraMap W (FractionRing W))) (fun b => d b / a) ∧ Prim (io.comp (algebraMap W (FractionRing W))) (fun b => d' b / a) := by
  first | exact @GlobalTheory.SiegTh.CmpUnif.cmp_unif | exact GlobalTheory.SiegTh.CmpUnif.cmp_unif | (intros; apply GlobalTheory.SiegTh.CmpUnif.cmp_unif <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_theta_symmetric_function_values_in_ground_field : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (x : Sp Ω ⟶ S) (θ : SecAt G L x), Odd m → N = m ^ (4 * g) → PolFib G L g x → ∃ e : Fin N → Ω, SymAt G L ρ m x θ e := by
  first | exact @GlobalTheory.UMin.SymRat.symAt_exists | exact GlobalTheory.UMin.SymRat.symAt_exists | (intros; apply GlobalTheory.UMin.SymRat.symAt_exists <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaMap_coords_of_symmetric_theta_isomorphic_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m n : ℕ) (o : Type) [CommRing o] (X : Scheme.{0}) (q : X ⟶ S) (f : X ⟶ PSpace o n) (S' : Scheme.{0}) (A : Over S') [GrpObj A] [IsCommMonObj A] (L' : LB A.left) (ρ' : LB.Gen (L'.pull (eSec A))) (Ω : Type) [Field Ω] [CharZero Ω] (x : Sp Ω ⟶ X) (x' : Sp Ω ⟶ S') (P : PolAV (Sp Ω)) (α : P.A.left ⟶ G.left) (α' : P.A.left ⟶ A.left) (θ : SecAt A L' x') (e : Fin (n + 1) → Ω), Odd m → n + 1 = m ^ (4 * g) → ThMap G L ρ m q f → L'.IsLB → ρ'.IsGen → P.g = g → IsGrpPullback P.A G (x ≫ q) α → LBIso P.L (L.pull α) → IsGrpPullback P.A A x' α' → LBIso P.L (L'.pull α') → IsGenSec A L' _ θ → SymAt A L' ρ' m x' θ e → PCrd (x ≫ f) e := by
  first | exact @GlobalTheory.UMin.pCrd_of_symAt | exact GlobalTheory.UMin.pCrd_of_symAt | (intros; apply GlobalTheory.UMin.pCrd_of_symAt <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.exists_good_hermitian_lineBundle_pair : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L : HermLB p, ∃ (P : Pair p) (b : ℕ) (s t : X.functionField), P.L = L ∧ P.Good D b s t := by
  first | exact @GlobalTheory.VolBr.exists_good_pair | exact GlobalTheory.VolBr.exists_good_pair | (intros; apply GlobalTheory.VolBr.exists_good_pair <;> assumption)
end
