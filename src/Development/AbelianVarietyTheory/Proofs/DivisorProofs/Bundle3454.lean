module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3336
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3368
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2788
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle017
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3453
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle129
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2694
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2918
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2697
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2695
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle630
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SFamCompl

theorem glue : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (X : Scheme.{0}) (x : ∀ e : ℕ, Sp (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) ⟶ X), (∀ e, Out.thickTrans R (IsLocalRing.maximalIdeal R) e ≫ x (e + 1) = x e) → ∃ f : Sp R ⟶ X, ∀ e, Out.thick R (IsLocalRing.maximalIdeal R) e ≫ f = x e :=
  GlobalTheory.T.exists_glue_spec_complete_localRing_thickenings

theorem ext_affine : ∀ (R : Type) [CommRing R] (I : Ideal R), IsHausdorff I R → ∀ (A : Type) [CommRing A]
    (f f' : Sp R ⟶ Sp A), (∀ e, Out.thick R I e ≫ f = Out.thick R I e ≫ f') → f = f' := by
  intro R _ I hI A _ f f' h
  rw [← Spec.map_preimage f, ← Spec.map_preimage f']
  congr 1
  ext a
  refine (IsHausdorff.eq_iff_smodEq (I := I)).2 fun k => ?_
  cases k with
  | zero =>
    rw [SModEq, Submodule.Quotient.eq, pow_zero, Ideal.one_eq_top, smul_eq_mul, Ideal.mul_top]
    trivial
  | succ e =>
    have he := h e
    rw [← Spec.map_preimage f, ← Spec.map_preimage f', Out.thick, ← Spec.map_comp, ← Spec.map_comp] at he
    have he' := congrArg (fun q => q.hom a) (Spec.map_injective he)
    simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at he'
    rw [SModEq, Submodule.Quotient.eq, smul_eq_mul, Ideal.mul_top]
    exact Ideal.Quotient.eq.1 he'

theorem srel_comp {h k : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
    {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}
    {c : SiegPre h k ζ s} {c' : SiegPre h k ζ' s'} {c'' : SiegPre h k ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} {φ : c'.A.left ⟶ c.A.left} {ψ : c''.A.left ⟶ c'.A.left}
    (m : SRelBy c' c 1 1 f φ) (m' : SRelBy c'' c' 1 1 f' ψ) : SRelBy c'' c 1 1 (f' ≫ f) (ψ ≫ φ) := by
  obtain ⟨hφ, ⟨φ₂, hs, hw⟩, hl⟩ := m
  obtain ⟨hψ, ⟨ψ₂, hs', hw'⟩, hl'⟩ := m'
  simp only [pow_one] at hl hl' ⊢
  refine ⟨hψ.comp hφ, ⟨ψ₂ ≫ φ₂, ⟨?_, ?_⟩, ?_⟩, fun a => ?_⟩
  · rw [Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc]
  · rw [Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]
  · exact (hw'.trans c''.isLB (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _)
      (GlobalTheory.SiegelPullComp.iso_pull ψ₂ hw)).trans c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _)
      (GlobalTheory.SiegelPullComp.iso_pull_pull c.isLB φ₂ ψ₂)
  · rw [pow_one, pow_one]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) (hl' a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (f' ≫ ·) (hl a)).trans (Category.assoc _ _ _).symm)))

theorem tower : ∀ (g n : ℕ) (B : Type) [CommRing B] (b : TBase B n) (R : Type) [CommRing R] (I : Ideal R) (s s' : Sp R ⟶ Sp B) (c : SiegPre g n (b.ζ : B) s) (c' : SiegPre g n (b.ζ : B) s') (t : ∀ e : ℕ, Sp (R ⧸ I ^ (e + 1)) ⟶ Sp B) (ce : ∀ e, SiegPre g n (b.ζ : B) (t e)) (φ : ∀ e, (ce e).A.left ⟶ c.A.left) (ψ : ∀ e, (ce e).A.left ⟶ c'.A.left), 3 ≤ n → Odd n → c.Principal → c'.Principal → (∀ e, SRelBy (ce e) c 1 1 (Out.thick R I e) (φ e)) → (∀ e, SRelBy (ce e) c' 1 1 (Out.thick R I e) (ψ e)) → ∃ β : ∀ e, (ce e).A.left ⟶ (ce (e + 1)).A.left, ∀ e, β e ≫ φ (e + 1) = φ e ∧ β e ≫ ψ (e + 1) = ψ e := by
  intro g n B _ b R _ I s s' c c' t ce φ ψ hn hodd hc hc' hφ hψ
  have key : ∀ e, ∃ β : (ce e).A.left ⟶ (ce (e + 1)).A.left, β ≫ φ (e + 1) = φ e ∧ β ≫ ψ (e + 1) = ψ e := by
    intro e
    have h1 : SiegPB (ce e) (ce (e + 1)) (Out.thickTrans R I e) :=
      GlobalTheory.SiegelPullComp.pb_cancel ((sRel_one_one_iff _ _ _).1 ⟨_, hφ (e + 1)⟩)
        (by rw [Out.thickTrans_comp]; exact (sRel_one_one_iff _ _ _).1 ⟨_, hφ e⟩)
    obtain ⟨β, hβ⟩ := (sRel_one_one_iff _ _ _).2 h1
    refine ⟨β, ?_, ?_⟩
    · have := srel_comp (hφ (e + 1)) hβ
      rw [Out.thickTrans_comp] at this
      exact GlobalTheory.SiegRigid.eq_of_sRelBy g n n 1 B B b (b.ζ : B) _ _ s (t e) c (ce e) _ _ _ hn hodd hc this (hφ e)
    · have := srel_comp (hψ (e + 1)) hβ
      rw [Out.thickTrans_comp] at this
      exact GlobalTheory.SiegRigid.eq_of_sRelBy g n n 1 B B b (b.ζ : B) _ _ s' (t e) c' (ce e) _ _ _ hn hodd hc' this (hψ e)
  choose β hβ using key
  exact ⟨β, hβ⟩

theorem assemble : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (s s' : Sp R ⟶ Sp B) (c : SiegPre g n ζ s) (c' : SiegPre g n ζ s') (t : ∀ e : ℕ, Sp (R ⧸ I ^ (e + 1)) ⟶ Sp B) (ce : ∀ e, SiegPre g n ζ (t e)) (φ : ∀ e, (ce e).A.left ⟶ c.A.left) (ψ : ∀ e, (ce e).A.left ⟶ c'.A.left) (β : ∀ e, (ce e).A.left ⟶ (ce (e + 1)).A.left), c.Principal → (∀ e, SRelBy (ce e) c 1 1 (Out.thick R I e) (φ e)) → (∀ e, SRelBy (ce e) c' 1 1 (Out.thick R I e) (ψ e)) → (∀ e, β e ≫ φ (e + 1) = φ e) → (∀ e, β e ≫ ψ (e + 1) = ψ e) → SiegPB c c' (𝟙 _) :=
  GlobalTheory.T.siegelObjects_pullback_of_compatibleTower_adic

theorem alg : ∀ (g n : ℕ) (B : Type) [CommRing B] (b : TBase B n) (R : Type) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R), IsAdicComplete I R → 3 ≤ n → Odd n → ∀ (s s' : Sp R ⟶ Sp B) (c : SiegPre g n (b.ζ : B) s)
    (c' : SiegPre g n (b.ζ : B) s'), c.Principal → c'.Principal →
    (∀ e, ∃ (t : Sp (R ⧸ I ^ (e + 1)) ⟶ Sp B) (ce : SiegPre g n (b.ζ : B) t),
      SiegPB ce c (Out.thick R I e) ∧ SiegPB ce c' (Out.thick R I e)) → SiegPB c c' (𝟙 _) := by
  intro g n B _ b R _ _ I hI hn hodd s s' c c' hc hc' h
  choose t ce hce hce' using h
  choose φ hφ using fun e => (sRel_one_one_iff (ce e) c _).2 (hce e)
  choose ψ hψ using fun e => (sRel_one_one_iff (ce e) c' _).2 (hce' e)
  obtain ⟨β, hβ⟩ := tower g n B b R I s s' c c' t ce φ ψ hn hodd hc hc' hφ hψ
  exact assemble g n B (b.ζ : B) R I hI s s' c c' t ce φ ψ β hc hφ hψ (fun e => (hβ e).1) (fun e => (hβ e).2)

theorem quot_local (R : Type) [CommRing R] [IsLocalRing R] (e : ℕ) :
    IsLocalRing (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) :=
  have : Nontrivial (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top (Ideal.pow_le_self (Nat.succ_ne_zero e)))
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

theorem quot_artin {R : Type} [CommRing R] [IsNoetherianRing R] (m : Ideal R) (hm : m.IsMaximal)
    (N : ℕ) : IsArtinianRing (R ⧸ m ^ (N + 1)) := by
  have : Ring.KrullDimLE 0 (R ⧸ m ^ (N + 1)) := by
    refine Ring.KrullDimLE.mk₀ fun P hP => ?_
    have h1 : m ^ (N + 1) ≤ P.comap (Ideal.Quotient.mk (m ^ (N + 1))) := by
      intro a ha
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 ha]
      exact P.zero_mem
    have hp : (P.comap (Ideal.Quotient.mk (m ^ (N + 1)))).IsPrime := Ideal.comap_isPrime _ _
    have h2 : m ≤ P.comap (Ideal.Quotient.mk (m ^ (N + 1))) := hp.le_of_pow_le h1
    have h3 := hm.eq_of_le hp.ne_top h2
    have h4 : (P.comap (Ideal.Quotient.mk (m ^ (N + 1)))).IsMaximal := h3 ▸ hm
    have h5 := Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk (m ^ (N + 1)))
      Ideal.Quotient.mk_surjective h4
    rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h5
    exact h5.resolve_left hP.ne_top
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

theorem spMap_comp_ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_id_ {A : Type} [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp [spMap]

end GlobalTheory.SFamCompl

namespace GlobalTheory.SFamCompl

theorem classified_of_complete : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp R ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F R _ _ _ hR β c hc
  have hn0 : n ≠ 0 := by omega
  set m := IsLocalRing.maximalIdeal R with hm
  haveI : ∀ e : ℕ, IsLocalRing (R ⧸ m ^ (e + 1)) := fun e => quot_local R e
  haveI : ∀ e : ℕ, IsArtinianRing (R ⧸ m ^ (e + 1)) := fun e => quot_artin m (IsLocalRing.maximalIdeal.isMaximal R) e
  let βe : ∀ e : ℕ, cycAway n →+* (R ⧸ m ^ (e + 1)) := fun e => (Ideal.Quotient.mk _).comp β
  have hthick : ∀ e, Out.thick R m e ≫ spMap β = spMap (βe e) ≫ spMap (RingHom.id (cycAway n)) := by
    intro e
    rw [spMap_id_, Category.comp_id]
    exact (spMap_comp_ β (Ideal.Quotient.mk (m ^ (e + 1)))).symm
  have hpull := fun e => GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n)
    (zetaAway n) (RingHom.id _) (Sp R) (Sp (R ⧸ m ^ (e + 1))) (spMap β) (spMap (βe e)) (Out.thick R m e) rfl (hthick e)
  choose ce hce using fun e => (hpull e).1 c
  have hcep : ∀ e, (ce e).Principal := fun e => (hpull e).2.1 c (ce e) (hce e) hc
  choose x hxs hxpb using fun e => GlobalTheory.T.siegel_point_lifts_to_artinian g n hg hn hodd F (R ⧸ m ^ (e + 1)) (βe e) (ce e) (hcep e)
  have hcomp : ∀ e, Out.thickTrans R m e ≫ x (e + 1) = x e := by
    intro e
    have h1 : SiegPB (ce e) (ce (e + 1)) (Out.thickTrans R m e) :=
      GlobalTheory.SiegelPullComp.pb_cancel (hce (e + 1)) (by rw [Out.thickTrans_comp]; exact hce e)
    refine GlobalTheory.T.siegelFamily_classifyingMap_unique g n hg hn hodd F _ (spMap (βe e)) (ce e) _ _ ?_ (hxs e)
      (GlobalTheory.SiegelPullComp.pb_comp (hxpb (e + 1)) h1) (hxpb e)
    rw [Category.assoc, hxs (e + 1)]
    exact (spMap_comp_ _ _).symm.trans (congrArg spMap (by ext a; rfl))
  obtain ⟨f, hf⟩ := glue R hR F.X x hcomp
  have hfs : f ≫ F.s = spMap β := by
    refine ext_affine R m hR.toIsHausdorff (cycAway n) _ _ fun e => ?_
    rw [← Category.assoc, hf e, hxs e, hthick e, spMap_id_, Category.comp_id]
  have hpf := GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n)
    (zetaAway n) (RingHom.id _) F.X (Sp R) F.s (spMap β) f rfl (by rw [hfs, spMap_id_, Category.comp_id])
  obtain ⟨c', hc'⟩ := hpf.1 F.univ
  have hc'p : c'.Principal := hpf.2.1 F.univ c' hc' F.princ
  have key : SiegPB c c' (𝟙 _) := by
    refine alg g n (cycAway n) (cycBase hn0) R m hR hn hodd (spMap β) (spMap β) c c' hc hc'p fun e => ?_
    refine ⟨_, ce e, hce e, GlobalTheory.SiegelPullComp.pb_cancel hc' ?_⟩
    rw [hf e]
    exact hxpb e
  refine ⟨f, hfs, ?_⟩
  simpa using GlobalTheory.SiegelPullComp.pb_comp hc' key

end GlobalTheory.SFamCompl
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc.DescentPow

theorem exists_cTrait_norm_eqAt {g n : ℕ} {F : SFam g n (zetaAway n)} {Z : Scheme.{0}} {i : F.X ⟶ Z} (hi : IsOpenImmersion i)
    {W8 : Matrix (Fin 8) (Fin 8) ℤ} (X₁ : Setup F W8 i) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z)
    (φ : InvFun ℤ) (ι : ℕ) (D : EffCartierData Y.Z)
    (hord : ∀ (T : Trait F) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i →
      ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a})
    (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ Y.Z) (hy : Set.range (gPt p ≫ y ≫ πY ≫ X₁.π) ⊆ Set.range i)
    (z₁ : X₁.M.Z) (hz : πY (y (cPt p)) = z₁) :
    ∃ c : CTrait X₁ p z₁, c.y = y ≫ πY ∧ ∀ f, EqAt Y D (y (cPt p)) f →
      ‖Y.val (gPt p ≫ y) f‖ = Real.exp (-(c.sc * (ι * φ.evalZ c.T.β))) := by
  obtain ⟨T, ι', j, ξ, hint, hj, hloc, hξ, hT⟩ := GlobalTheory.T.classicalPoint_factors_through_siegelModuli_trait g n F Z i hi W8 X₁ Y πY p y hy
  have hgen : gPt p ≫ y = spMap ι' ≫ jK T.V ≫ ξ := by
    rw [← hξ, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext v
    exact hj v
  refine ⟨⟨y ≫ πY, ?_, T, ι', hint, ?_⟩, rfl, fun f hf => ?_⟩
  · rw [Scheme.Hom.comp_apply]; exact hz
  · rw [← Category.assoc, ← Category.assoc, hgen]
    simp only [Category.assoc]
    rw [hT]
  · obtain ⟨a, ha, hI⟩ := hord T ξ hT
    have hc : ξ (closedPoint T.V) = y (cPt p) := by
      rw [← hξ, Scheme.Hom.comp_apply]
      exact congrArg ξ (IsLocalRing.comap_closedPoint j).symm
    rw [← hc] at hf
    have key := GlobalTheory.T.norm_localEquation_eq_uniformiser_pow_classicalPoint _ _ Y D T.V T.ϖ a ξ p ι' j hint hj hI f hf
    rw [hξ] at key
    have hpos : 0 < ‖ι' (algebraMap T.V (FractionRing T.V) T.ϖ)‖ := by
      refine norm_pos_iff.2 ?_
      rw [map_ne_zero, Ne, IsFractionRing.to_map_eq_zero_iff]
      exact T.irr.ne_zero
    show _ = Real.exp (-(-Real.log ‖ι' (algebraMap T.V (FractionRing T.V) T.ϖ)‖ * (ι * φ.evalZ T.β)))
    rw [key, ← ha, neg_mul, neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log hpos]

theorem val_comp_of_centre {g n : ℕ} {F : SFam g n (zetaAway n)} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    {W8 : Matrix (Fin 8) (Fin 8) ℤ} (X₁ : Setup F W8 i) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z)
    (hHom : X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY) {q : ℕ} [Fact q.Prime] (y : Sp (OO q) ⟶ Y.Z) {z : X₁.M.Z}
    (hz : πY (y (cPt q)) = z) {a : X₁.Ω₁} (ha : a ∈ X₁.M.O z) :
    Y.val (gPt q ≫ y) a = X₁.M.val (gPt q ≫ y ≫ πY) a := by
  have hs : πY ((gPt q ≫ y) (closedPoint (PadicAlgCl q))) ⤳ z :=
    hz ▸ (RatModel.gPt_specializes (M := Y) rfl _).map πY.continuous
  have := hHom.val_comp (gPt q ≫ y) (closedPoint (PadicAlgCl q)) (RatModel.O_le_of_specializes hs ha)
  rw [← Category.assoc]
  exact this.symm

theorem exists_idealSheaf_comap_orders : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W8 : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W8 → ThetaInt F W8 i → ∀ (X₁ : Setup F W8 i) (ι : ℕ) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) (D : GlobalTheory.EffCartierData Y.Z), 1 ≤ ι → IsProjOver X₁.M.s → X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → IsProper πY → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y.Z → (∀ y ∈ D.idealSheaf.support, X₁.π (πY y) ∉ Set.range i) → (∀ (T : Trait F) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a}) → ∃ (ι' : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι' ∧ (∀ y ∈ (J₁.comap πY).support, X₁.π (πY y) ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι' * φ.evalZ T.β ∧ idlAlong (J₁.comap πY) ξ = Ideal.span {T.ϖ ^ a} := by
  intro g n hg hn hodd F Z z i hθ φ hφ W8 hE hθi X₁ ι Y πY D hι hP hHom hprop hnorm hsupp hord
  have hi : IsOpenImmersion i := hθ.2.2.1
  obtain ⟨d, hd, hA⟩ := GlobalTheory.T.exists_approxPoincareSeries_at_thetaSetup_points g n F W8 Z i X₁ hE hθi hg φ hφ
  obtain ⟨k, hk⟩ : ι ∣ Nat.lcm ι d := Nat.dvd_lcm_left ι d
  obtain ⟨m, hm⟩ : d ∣ Nat.lcm ι d := Nat.dvd_lcm_right ι d
  have hL0 : 0 < Nat.lcm ι d := Nat.lcm_pos hι hd
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hk; omega
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hm; omega
  have hAL : ApproxAt X₁ φ (Nat.lcm ι d) := hm ▸ GlobalTheory.T.hasApproxPoincareSeries_nat_multiple g n F W8 Z i X₁ φ d m hm0 hA

  have hord' : ∀ (T : Trait F) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i →
      ∃ a : ℕ, (a : ℝ) = (Nat.lcm ι d : ℕ) * φ.evalZ T.β ∧ idlAlong (D.nsmul k).idealSheaf ξ = Ideal.span {T.ϖ ^ a} := by
    intro T ξ h
    obtain ⟨a, ha, hI⟩ := hord T ξ h
    refine ⟨k * a, ?_, ?_⟩
    · rw [hk]; push_cast; rw [ha]; ring
    · rw [GlobalTheory.TorRef.Scale.idlAlong_nsmul, hI, Ideal.span_singleton_pow, ← pow_mul, mul_comm a k]
  have hsub : ∀ y ∈ (D.nsmul k).idealSheaf.support, y ∈ D.idealSheaf.support := by
    intro y hy
    obtain ⟨j, hj⟩ := D.exists_mem y
    rw [(D.nsmul k).mem_support_iff j hj] at hy
    rw [D.mem_support_iff j hj]
    intro h
    apply hy
    change y ∈ Y.Z.basicOpen (D.f j ^ k)
    rw [Scheme.basicOpen_pow _ _ hk0]
    exact h

  let U : Y.Z.Opens := (πY ≫ X₁.π) ⁻¹ᵁ i.opensRange
  have hmemU : ∀ y : Y.Z, y ∈ U ↔ X₁.π (πY y) ∈ Set.range i := fun y => by
    show (πY ≫ X₁.π) y ∈ Set.range i ↔ _
    rw [Scheme.Hom.comp_apply]
  have hU : (U : Set Y.Z).Nonempty := by
    refine ⟨Y.pt (closedPoint X₁.Ω₁), (hmemU _).2 ?_⟩
    have e : Y.pt ≫ πY ≫ X₁.π = spMap (AlgHom.id X₁.o₁ X₁.Ω₁).toRingHom ≫ spMap X₁.S.R.val.toRingHom ≫ X₁.u ≫ i := by
      rw [← Category.assoc, hHom, Category.assoc, X₁.comp]
    have e' := congrArg (fun h : Sp X₁.Ω₁ ⟶ Z => h (closedPoint X₁.Ω₁)) e
    simp only [Scheme.Hom.comp_apply] at e'
    exact ⟨_, e'.symm⟩
  have hDU : ∀ x ∈ (D.nsmul k).idealSheaf.support, x ∉ U := fun x hx hxU => hsupp x (hsub x hx) ((hmemU x).1 hxU)
  have hrange : ∀ {q : ℕ} [Fact q.Prime] (y : Sp (OO q) ⟶ Y.Z), Set.range (gPt q ≫ y) ⊆ U →
      Set.range (gPt q ≫ y ≫ πY ≫ X₁.π) ⊆ Set.range i := by
    rintro q _ y hy _ ⟨w, rfl⟩
    have := (hmemU _).1 (hy ⟨w, rfl⟩)
    simpa only [← Category.assoc, Scheme.Hom.comp_apply] using this
  obtain ⟨J, hJ⟩ := GlobalTheory.T.exists_idealSheaf_pullback_eq_divisor_of_approx X₁.o₁ X₁.Ω₁ X₁.M Y πY hHom hprop (@GlobalTheory.IsNormalScheme.pred _ X₁.normal) hnorm U (D.nsmul k) hU hDU (by
    intro z₀ _ x hxz hx
    obtain ⟨p, hp, y₀, hcen⟩ := GlobalTheory.T.exists_classicalPoint_centred_closedPoint_arithmetic _ _ Y x hx U hU
    obtain ⟨c₀, hc₀y, hc₀⟩ := exists_cTrait_norm_eqAt hi X₁ Y πY φ (Nat.lcm ι d) (D.nsmul k) hord' p y₀ (hrange y₀ hcen.2) z₀
      (by rw [hcen.1, hxz])
    refine ⟨p, hp, y₀, hcen, fun e => ?_⟩
    obtain ⟨f, hf0, hfall⟩ := hAL p z₀ c₀ e
    have hfO : X₁.M.stalkHom z₀ f ∈ X₁.M.O z₀ := (X₁.M.stalkEquiv z₀ f).2
    refine ⟨X₁.M.stalkHom z₀ f, hfO, fun f' hf' => ?_, ?_⟩
    · rw [hc₀ f' (hcen.1 ▸ hf'), val_comp_of_centre X₁ Y πY hHom y₀ (by rw [hcen.1, hxz]) hfO, ← hf0]
      show _ = ‖X₁.M.val (gPt p ≫ c₀.y) _‖
      rw [hc₀y]
    · intro q hq y hyz hyU f' hf'
      have hpq : p = q := GlobalTheory.T.prime_eq_of_classicalPoint_same_centre X₁.M.Z p q (y₀ ≫ πY) (y ≫ πY) (by
        rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hcen.1, hxz, hyz])
      subst hpq
      obtain ⟨c, hcy, hc⟩ := exists_cTrait_norm_eqAt hi X₁ Y πY φ (Nat.lcm ι d) (D.nsmul k) hord' p y (hrange y hyU) z₀ hyz
      have hcv : ∀ a, c.val a = Y.val (gPt p ≫ y) (X₁.M.stalkHom z₀ a) := fun a => by
        rw [val_comp_of_centre X₁ Y πY hHom y hyz (a := X₁.M.stalkHom z₀ a) (X₁.M.stalkEquiv z₀ a).2]
        show X₁.M.val (gPt p ≫ c.y) _ = _
        rw [hcy]
      rcases hfall c with h1 | ⟨h, hh, h2⟩
      · left
        rw [← hcv, hc f' hf']
        exact h1
      · right
        refine ⟨X₁.M.stalkHom z₀ h, ⟨(X₁.M.stalkEquiv z₀ h).2, ?_⟩, ?_⟩
        · by_contra hne
          push_neg at hne
          apply (IsLocalRing.mem_maximalIdeal _).1 hh
          have hu : IsUnit (X₁.M.stalkEquiv z₀ h) :=
            (RatModel.isUnit_O_iff _).2 ⟨hne.1, hne.2⟩
          exact (MulEquiv.isUnit_map (X₁.M.stalkEquiv z₀)).1 hu
        · rw [← hcv, ← hcv]
          exact h2)
  refine ⟨Nat.lcm ι d, J, hL0, ?_, ?_⟩
  · rw [hJ]
    intro y hy
    exact hsupp y (hsub y hy)
  · rw [hJ]
    exact hord'

end GlobalTheory.Poinc.DescentPow
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.canonical_mumford_family_uniformises_refinements : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsSemiAbelian G → Canon Q G P → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), IsCN R' → Function.Injective ρ → ρ.Finite → ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε → ∃ (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G.left) (π₂ : (G2 G').left ⟶ (G2 G).left) (A : PolAV (Sp (FractionRing R'))) (U : Unif (maximalIdeal R') D A G'), IsGrpPullback G' G (spMap ρ) π ∧ IsSquare π π₂ ∧ LBIso (abelian₂ G' U.LG.L) (P.pull π₂) := by
  first | exact @GlobalTheory.Mum.CanonFam.exists_unif_refines | exact GlobalTheory.Mum.CanonFam.exists_unif_refines | (intros; apply GlobalTheory.Mum.CanonFam.exists_unif_refines <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.mumford_family_from_regular_base_coordinates : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (iw : L.W →+* R), Function.Injective iw → ∀ (m N : ℕ) (s : Fin m ⊕ Fin N → R) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ i, s (.inl i) ∈ maximalIdeal R ∧ s (.inl i) ≠ 0) → (∀ j, IsUnit (s (.inr j))) → (∀ i y, 0 ≤ ε (.inl i) y y) → (∀ y, y ≠ 0 → 0 < ∑ i, ε (.inl i) y y) → Nontrivial L.D.X → ∃ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), DivFrom L P.D.toPre P.oD iw s ε e ∧ IsMonomial P.D.toPre (fun i => s (.inl i)) (fun i => (l.M' : ℤ) • pull e.toLinearMap (ε (.inl i))) := by
  first | exact @GlobalTheory.UCanon.FamFrom.main | exact GlobalTheory.UCanon.FamFrom.main | (intros; apply GlobalTheory.UCanon.FamFrom.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem _root_.GlobalTheory.T.exists_unitaryThetaSetup_ideal_over_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (A : Set C.Z), IsClopen A → IsIrreducible A → (A ∩ Set.range C.i).Nonempty → ∃ (X₁ : USetup C) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι ∧ Set.range X₁.π = A ∧ (∀ x ∈ J₁.support, X₁.π x ∉ Set.range C.i) ∧ UValThru Xo c C.i X₁.π Set.univ φ J₁ ι := by
  first | exact @GlobalTheory.UPoinc.exists_uSetup_ideal_over_component | exact GlobalTheory.UPoinc.exists_uSetup_ideal_over_component | (intros; apply GlobalTheory.UPoinc.exists_uSetup_ideal_over_component <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory

theorem pointSeparationPair_of_vanishing :
    GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics →
      GlobalTheory.Published.PointSeparationPair := by
  intro hP hV hN X _ _ _ p n hproj hdim M Δ m G r N₀ x₁ x₂ c hM hΔ hklt hm hG hr hnef hbig hC
    h₁ h₂ hx hc hZ hs
  letI := algebraΓOfHom p
  obtain ⟨h, hpos, hsum, hh⟩ := GlobalTheory.T.exists_rational_budgets_twoPointInduction n r c hr hc hs
  have hr' : (0 : ℚ) < (r : ℚ) := by exact_mod_cast hr
  refine GlobalTheory.T.separate_two_points_nef_big hP hV hN X p n hproj hdim M Δ m G N₀ (1 / (r : ℚ)) h x₁ x₂ hM hΔ hklt hm hG
    hnef hbig ?_ h₁ h₂ hx hpos ?_ hsum (by positivity)
  · intro C hCc
    rw [hC C hCc]
    ring
  · intro z e hz he hze
    have hle : e ≤ n := by
      have h1 := topologicalKrullDim_subspace_le X (closure ({z} : Set X))
      rw [hze, hdim] at h1
      exact_mod_cast h1
    have hmem : x₁ ∈ Closeds.closure ({z} : Set X) ∨ x₂ ∈ Closeds.closure ({z} : Set X) := by
      rcases hz with hz | hz
      · exact Or.inl (specializes_iff_mem_closure.1 hz)
      · exact Or.inr (specializes_iff_mem_closure.1 hz)
    have hZ' := hZ (Closeds.closure ({z} : Set X)) e isIrreducible_singleton.closure hmem he hze
    exact hh e (Finset.mem_Icc.2 ⟨he, hle⟩) _ hZ'

end GlobalTheory
end
