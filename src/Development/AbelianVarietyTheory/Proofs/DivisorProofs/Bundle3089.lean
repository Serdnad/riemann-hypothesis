module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2697
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.OverHomEqIffForallIsAlgClosedAlgebra
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3009
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3008
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2779
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.QuotFamRep

theorem spMap_rid (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _

section Calc

variable {h n n' n'' : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}
  {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {c'' : SiegPre h n'' ζ'' s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
  {d d' d'' : ℕ}

theorem sRel_comp (h₁ : SRel c' c d' d f) (h₂ : SRel c'' c' d'' d' f') : SRel c'' c d'' d (f' ≫ f) :=
  ((GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n'' B B' B'' ζ ζ' ζ'' S S' S'' s s' s'' c c' c'' f f' d d' d'' h₁).1).1 h₂

theorem sRel_cancel (h₁ : SRel c' c d' d f) (h₂ : SRel c'' c d'' d (f' ≫ f)) : SRel c'' c' d'' d' f' :=
  ((GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n'' B B' B'' ζ ζ' ζ'' S S' S'' s s' s'' c c' c'' f f' d d' d'' h₁).1).2 h₂

theorem sRel_principal (h₁ : SRel c' c d' d f) (hc : c.Principal) : c'.Principal :=
  (GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n' B B' B' ζ ζ' ζ' S S' S' s s' s' c c' c' f (𝟙 S') d d' d' h₁).2.1 hc

theorem sRel_scale (h₁ : SRel c' c 1 1 f) (e : ℕ) : SRel c' c e e f := by
  simpa using (GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n' B B' B' ζ ζ' ζ' S S' S' s s' s' c c' c' f (𝟙 S') 1 1 1 h₁).2.2 e

end Calc

theorem exists_pull {h k : ℕ} {B : Type} [CommRing B] {ζ : B} {S S' : Scheme.{0}} {s : S ⟶ Sp B}
    (c : SiegPre h k ζ s) (f : S' ⟶ S) : ∃ c' : SiegPre h k ζ (f ≫ s), SiegPB c' c f :=
  (GlobalTheory.T.siegelPre_pullback_principal_ringChange h k B B ζ ζ (RingHom.id B) S S' s (f ≫ s) f rfl (by rw [spMap_rid, Category.comp_id])).1 c

theorem asIdeal_eq_bot_iff {A A' : Type} [CommRing A] [CommRing A'] [IsDomain A] [IsDomain A'] (j : A →+* A')
    (hj : Function.Injective j) (hf : IsFinite (spMap j)) (y : Sp A') :
    ((spMap j) y).asIdeal = ⊥ ↔ y.asIdeal = ⊥ := by
  algebraize [j]
  have hm : Module.Finite A A' := by rw [IsFinite.SpecMap_iff] at hf; exact hf
  have : Algebra.IsIntegral A A' := inferInstance
  show Ideal.comap (algebraMap A A') y.asIdeal = ⊥ ↔ _
  refine ⟨fun e => Ideal.eq_bot_of_comap_eq_bot e, fun e => ?_⟩
  rw [e]; exact Ideal.comap_bot_of_injective (algebraMap A A') hj

end GlobalTheory.QuotFamRep

namespace GlobalTheory


open QuotFamRep in
theorem quotFam_represents : ∀ (h n N : ℕ) (F : SFam h N (zetaAway N)) (j : cycAway n →+* cycAway N) (Q : SQuot F n (zetaAway n) j), 3 ≤ n → Odd N → n ∣ N → Function.Injective j → j (zetaAway n) = zetaAway N ^ (N / n) → IsFinite (spMap j) → Etale (spMap j) → Surjective (spMap j) → ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (cycAway n)) (c : SiegPre h n (zetaAway n) s'), IsReduced S → Dense {x : S | (s' x).asIdeal = ⊥} → c.Principal → ∃ f : S ⟶ Q.X, f ≫ Q.s = s' ∧ SiegPB c Q.univ f := by
  intro h n N F j Q hn hN hnN hj hjz hfin het hsurj S s' c hS hd hc
  have hN0 : N ≠ 0 := hN.pos.ne'
  have hn0 : n ≠ 0 := by omega

  let S' := pullback s' (spMap j)
  let q : S' ⟶ S := pullback.fst s' (spMap j)
  let t : S' ⟶ Sp (cycAway N) := pullback.snd s' (spMap j)
  have hq := GlobalTheory.T.siegelPre_pullback_principal_ringChange h n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n) (RingHom.id _) S S' s' (t ≫ spMap j) q
    rfl (by rw [spMap_rid, Category.comp_id]; exact pullback.condition)
  obtain ⟨c', hc'⟩ := hq.1 c
  have hc'P : c'.Principal := hq.2.1 c c' hc' hc

  obtain ⟨S₁, π₁, C, hπf, hπe, hπs, hCrel, -⟩ := GlobalTheory.T.exists_finite_etale_deeper_level_siegel_cover h n N (cycAway n) (cycAway N) (zetaAway n)
    (cycBase hN0) j S' t c' hn hN hnN (by rw [cycBase_ζ]; exact hjz) hc'P
  let p : S₁ ⟶ S := π₁ ≫ q
  have : IsFinite p := by dsimp [p, q]; infer_instance
  have : Etale p := by dsimp [p, q]; infer_instance
  have : Surjective p := by dsimp [p, q]; infer_instance
  have hp : p ≫ s' = (π₁ ≫ t) ≫ spMap j := by
    simp only [p, q, t, Category.assoc, pullback.condition]
  have hred : IsReduced S₁ := GlobalTheory.isReduced_of_smooth_of_isReduced p
  have hden : Dense {x : S₁ | ((π₁ ≫ t) x).asIdeal = ⊥} := by
    have : UniversallyOpen p := UniversallyOpen.of_flat p
    have e : ∀ x, s' (p x) = spMap j ((π₁ ≫ t) x) := fun x => by
      rw [← Scheme.Hom.comp_apply, hp, Scheme.Hom.comp_apply]
    convert hd.preimage p.isOpenMap using 1
    ext x
    show ((π₁ ≫ t) x).asIdeal = ⊥ ↔ (s' (p x)).asIdeal = ⊥
    rw [e, asIdeal_eq_bot_iff j hj hfin]
  have hCP : C.Principal := sRel_principal hCrel hc'P
  obtain ⟨f₁, hf₁s, hf₁⟩ := F.rep S₁ (π₁ ≫ t) C hred hden hCP

  obtain ⟨c₀, hC0, h0C⟩ := GlobalTheory.T.exists_siegelObject_lowered_level h n N (cycAway n) (cycAway N) (zetaAway n) (zetaAway N) j S₁ (π₁ ≫ t) C hN0
    (isUnit_natCast hN0) hnN hjz
  have hf₁N : SRel C F.univ (N / n) (N / n) f₁ := sRel_scale ((sRel_one_one_iff _ _ _).2 hf₁) _
  have h0F : SRel c₀ F.univ 1 (N / n) f₁ := by simpa using sRel_comp hf₁N h0C
  obtain ⟨g, hg⟩ : ∃ g : S₁ ⟶ Q.X, g = f₁ ≫ Q.π := ⟨_, rfl⟩
  have hgQ : SRel C Q.univ (N / n) 1 g := hg ▸ sRel_comp Q.low hf₁N
  have h0Q : SiegPB c₀ Q.univ g := (sRel_one_one_iff _ _ _).1 (by simpa using sRel_comp hgQ h0C)
  have hCc : SRel C c (N / n) 1 p := sRel_comp ((sRel_one_one_iff _ _ _).2 hc') hCrel
  have h0c₁ : SRel c₀ c 1 1 p := by simpa using sRel_comp hCc h0C
  have hf₁p : f₁ ≫ F.s ≫ spMap j = p ≫ s' := by rw [← Category.assoc, hf₁s, hp]
  have hgs : g ≫ Q.s = p ≫ s' := by rw [hg, Category.assoc, Q.base]; exact hf₁p

  have key : pullback.fst p p ≫ g = pullback.snd p p ≫ g := by
    have : IsReduced (pullback p p) := GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.fst p p)
    have : IsSeparated Q.s := isSeparated_of_isQProjOver Q.qproj
    refine (GlobalTheory.hom_eq_iff_forall_isAlgClosed Q.s ?_).2 fun K _ _ x => ?_
    · simp only [Category.assoc, hgs, pullback.condition_assoc]
    obtain ⟨cx, hcx⟩ := exists_pull c₀ (x ≫ pullback.fst p p)
    have hx₁ := (sRel_one_one_iff _ _ _).2 hcx
    have hx₂ : SRel cx c₀ 1 1 (x ≫ pullback.snd p p) := by
      refine sRel_cancel h0c₁ ?_
      have := sRel_comp h0c₁ hx₁
      convert this using 1
      rw [Category.assoc, Category.assoc, pullback.condition]
    have e := Q.fibre K (x ≫ pullback.fst p p ≫ f₁) (x ≫ pullback.snd p p ≫ f₁) _ cx
      (by simp only [Category.assoc, hf₁p, pullback.condition_assoc])
      (by simpa only [Category.assoc] using sRel_comp h0F hx₁)
      (by simpa only [Category.assoc] using sRel_comp h0F hx₂)
    simpa only [hg, Category.assoc] using e
  have hcoeq : ∀ {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ S₁), g₁ ≫ p = g₂ ≫ p → g₁ ≫ g = g₂ ≫ g := fun g₁ g₂ e => by
    have := pullback.lift g₁ g₂ e ≫= key
    rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc] at this
  have hfac : p ≫ EffectiveEpi.desc p g hcoeq = g := EffectiveEpi.fac p g hcoeq
  refine ⟨EffectiveEpi.desc p g hcoeq, ?_, ?_⟩
  · rw [← cancel_epi p, ← Category.assoc, hfac, hgs]
  · exact GlobalTheory.T.siegPB_of_finite_etale_surjective_cover h n (cycAway n) (cycBase hn0) S S₁ Q.X s' ((π₁ ≫ t) ≫ spMap j) Q.s c c₀ Q.univ p _ hn
      (hN.of_dvd_nat hnN) Q.princ inferInstance inferInstance inferInstance ((sRel_one_one_iff _ _ _).1 h0c₁)
      (hfac.symm ▸ h0Q)

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.rosati_adjoint_iff_biextension_pullbacks_isomorphic : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (La : Type) [AddCommGroup La] (Q : La →+ (Fin g → ℂ)) (EF : LinearMap.BilinForm ℤ La), IsExp (𝟙 (Sp ℂ)) e → Function.Injective Q → (∀ z, e z = 1 ↔ z ∈ Q.range) → (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → ∀ (f f' : A ⟶ A) (u u' : La →+ La), IsMonHom f → IsMonHom f' → (∀ (k : ℕ) x, 0 < k → e ((k : ℂ)⁻¹ • Q (u x)) = e ((k : ℂ)⁻¹ • Q x) ≫ f) → (∀ (k : ℕ) x, 0 < k → e ((k : ℂ)⁻¹ • Q (u' x)) = e ((k : ℂ)⁻¹ • Q x) ≫ f') → (LBIso (P.pull (lift (fst A A ≫ f) (snd A A)).left) (P.pull (lift (fst A A) (snd A A ≫ f')).left) ↔ ∀ x y, EF (u x) y = EF x (u' y)) := by
  first | (exact @GlobalTheory.RosatiFormAdj.lbIso_pull_iff_adjoint) | (exact GlobalTheory.RosatiFormAdj.lbIso_pull_iff_adjoint) | (intros; apply GlobalTheory.RosatiFormAdj.lbIso_pull_iff_adjoint <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.galoisBaseChange_semiAbelian_invariant_units_descend : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (G' : Over (Sp R')) [GrpObj G'] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (act : Gal ρ → (G'.left ⟶ G'.left)), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, IsGrpPullback G' G' (spMap (Gal.hom σ)) (act σ)) → (∀ σ, act σ ≫ β = β) → ∀ O : G.left.Opens, Function.Injective (β.app O).hom ∧ ∀ u : Γ(G'.left, β ⁻¹ᵁ O)ˣ, (∀ σ (h : β ⁻¹ᵁ O ≤ act σ ⁻¹ᵁ (β ⁻¹ᵁ O)), ((act σ).appLE _ _ h).hom u.val = u.val) → ∃ g : Γ(G.left, O)ˣ, pullU β O g = u := by
  first | exact @GlobalTheory.Mum.InvUnit.invariant_units | exact GlobalTheory.Mum.InvUnit.invariant_units | (intros; apply GlobalTheory.Mum.InvUnit.invariant_units <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.galoisDescent_invariant_morphism_flat_existsUnique : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (Y Y' : Scheme.{0}) (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (β : Y' ⟶ Y), Flat y → IsPullback β y' y (spMap ρ) → ∀ (act : Gal ρ → (Y' ⟶ Y')), (∀ σ, act σ ≫ β = β) → (∀ σ, act σ ≫ y' = y' ≫ spMap (Gal.hom σ)) → ∀ (W : Scheme.{0}) (h : Y' ⟶ W), (∀ σ, act σ ≫ h = h) → ∃! h₀ : Y ⟶ W, β ≫ h₀ = h := by
  first | exact @GlobalTheory.GalDescent.descend | exact GlobalTheory.GalDescent.descend | (intros; apply GlobalTheory.GalDescent.descend <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isSymmetric_of_galoisPullback_uniformisationBundle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∀ (L : LB G.left) (hL : L.IsLB), LBIso U'.LG.L (L.pull β) → ∀ (rig : LB.Gen (L.pull (eSec G))) (hr : rig.IsGen), RigLB.IsSymmetric (⟨L, rig, hL, hr⟩ : RigLB G) := by
  first | exact @GlobalTheory.Mum.isSymmetric_of_pull_iso_unif | exact GlobalTheory.Mum.isSymmetric_of_pull_iso_unif | (intros; apply GlobalTheory.Mum.isSymmetric_of_pull_iso_unif <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_selfPullback_degenerationData_ringAutOver : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R'), Function.Injective ρ →
    ∀ (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg ρ D D') (σ : Gal ρ),
      ∃ h : IsPullDeg (Gal.hom σ) D' D', PullOver hD h := by
  first | exact @GlobalTheory.Mum.SelfPull.exists_isPullDeg_self_pullOver | exact GlobalTheory.Mum.SelfPull.exists_isPullDeg_self_pullOver | (intros; apply GlobalTheory.Mum.SelfPull.exists_isPullDeg_self_pullOver <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section
namespace GlobalTheory.FormalAlg

theorem glue_chart {X X' : Scheme.{0}} (φ : X' ⟶ X) {M L' : LB X} {L : LB X'} (ω : LB.Iso L' M)
    (hω : ω.IsGen) (u : LB.Iso L (L'.pull φ)) (hu : PGen u) (hM : M.IsLB) (hL' : L'.IsLB) (hL : L.IsLB)
    (σ : LB.Sec L) (i : M.ι) :
    ∃ a : Γ(X', φ ⁻¹ᵁ M.U i), ∀ z b c, φ z ∈ M.U i → φ z ∈ L'.U b → z ∈ L.U c →
      gs (𝟙 _) z _ a = (gv ω φ z i b).val * ((gw u (𝟙 _) z b c).val * gs (𝟙 _) z _ (σ.f c)) := by
  let W : L'.ι × L.ι → X'.Opens := fun p => φ ⁻¹ᵁ (M.U i ⊓ L'.U p.1) ⊓ L.U p.2
  have l₀ : ∀ p, W p ≤ φ ⁻¹ᵁ M.U i := fun p x hx => hx.1.1
  have l₁ : ∀ p, W p ≤ φ ⁻¹ᵁ (M.U i ⊓ L'.U p.1) := fun p x hx => hx.1
  have l₂ : ∀ p, W p ≤ (L'.pull φ).U (fun _ => p.1) ⊓ L.U p.2 := fun p x hx => ⟨mem_pull.2 hx.1.2, hx.2⟩
  have l₃ : ∀ p, W p ≤ L.U p.2 := fun p x hx => hx.2
  have key : ∀ (y : X') (b b' : L'.ι) (c c' : L.ι), φ y ∈ M.U i → φ y ∈ L'.U b → φ y ∈ L'.U b' →
      y ∈ L.U c → y ∈ L.U c' →
      (gv ω φ y i b).val * ((gw u (𝟙 _) y b c).val * gs (𝟙 _) y _ (σ.f c)) =
        (gv ω φ y i b').val * ((gw u (𝟙 _) y b' c').val * gs (𝟙 _) y _ (σ.f c')) := by
    intro y b b' c c' hi hb hb' hc hc'
    have h1 := gm_isGen hω φ y i i b b' hi hi hb hb'
    have h2 := hu X' (𝟙 _) y b b' c c' hb hb' hc hc'
    have h3 := GlobalTheory.SecPullIso.gs_sec_trans σ (𝟙 _) y hc hc'
    rw [gm_self hM φ y hi, one_mul] at h1
    rw [Category.id_comp] at h2
    rw [h1, h2, h3]
    generalize gm φ y _ (L'.g b b') = B
    generalize gm (𝟙 X') y _ (L.g c c') = C
    generalize gv ω φ y i b' = D
    generalize gw u (𝟙 _) y b' c' = E
    generalize gs (𝟙 X') y _ (σ.f c') = s
    simp only [Units.val_mul]
    have hB := B.inv_mul
    have hC := C.inv_mul
    linear_combination ((D : _) * E * s * (C⁻¹ : _ˣ) * C) * hB + ((D : _) * E * s) * hC
  obtain ⟨v, hv⟩ : ∃ v : ∀ p, Γ(X', W p), ∀ z p, z ∈ W p →
      gs (𝟙 _) z (W p) (v p) = (gv ω φ z i p.1).val * ((gw u (𝟙 _) z p.1 p.2).val * gs (𝟙 _) z _ (σ.f p.2)) :=
    ⟨fun p => (res (l₁ p) (pullU φ _ (ω.s (i, p.1)))).val * ((res (l₂ p) (u.s (fun _ => p.1, p.2))).val *
        (X'.presheaf.map (homOfLE (l₃ p)).op).hom (σ.f p.2)), fun z p hz => by
      rw [gs_mul _ z _ hz, gs_mul _ z _ hz, gs_unit _ z _ hz, gs_unit _ z _ hz, gm_res (𝟙 X') z (l₁ p) hz,
        show gm (𝟙 X') z (W p) (res (l₂ p) (u.s (fun _ => p.1, p.2))) = gw u (𝟙 _) z p.1 p.2 from gm_res (𝟙 X') z (l₂ p) hz _, gs_res (𝟙 X') z (l₃ p) hz, show gm (𝟙 X') z (φ ⁻¹ᵁ (M.U i ⊓ L'.U p.1)) (pullU φ _ (ω.s (i, p.1))) = gv ω φ z i p.1 from
          (gm_pull (𝟙 _) φ z _ (l₁ p hz) _).trans (by rw [Category.id_comp]; rfl)]⟩
  obtain ⟨a, ha, -⟩ := X'.sheaf.existsUnique_gluing' W (φ ⁻¹ᵁ M.U i) (fun p => homOfLE (l₀ p)) (fun y hy => by
      obtain ⟨b, hb⟩ := exists_chart hL' (φ y)
      obtain ⟨c, hc⟩ := exists_chart hL y
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(b, c), ⟨hy, hb⟩, hc⟩) v
    (fun p q => fn_ext (V := W p ⊓ W q) fun y hy => by
      refine (gs_res (𝟙 _) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 _) y inf_le_right hy _).symm)
      rw [hv y p hy.1, hv y q hy.2]
      exact key y p.1 q.1 p.2 q.2 hy.1.1.1 hy.1.1.2 hy.2.1.2 hy.1.2 hy.2.2)
  refine ⟨a, fun z b c h₁ h₂ h₃ => ?_⟩
  have hz : z ∈ W (b, c) := ⟨⟨h₁, h₂⟩, h₃⟩
  exact (gs_res (𝟙 _) z (l₀ (b, c)) hz a).symm.trans ((congrArg (gs (𝟙 _) z (W (b, c))) (ha (b, c))).trans
    (hv z (b, c) hz))

theorem lift_step : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (H₀ : LB (Y 0).left) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → ((∀ i, C.D 0 i = nonzeroLocus (s₀ i)) ∧ ∀ i j (m : H₀.ι), rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ j).f m) = rs (Y 0).left (inf_le_left : C.D 0 i ⊓ H₀.U m ≤ C.D 0 i) (C.ρ 0 i j) * rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ i).f m)) → ∀ γ : ∀ e, (Y 0).left ⟶ (Y e).left, γ 0 = 𝟙 _ → (∀ e, γ e ≫ β e = γ (e + 1)) → ∀ (e k : ℕ), (∀ c : ∀ i j, Γ((Y (e + 1)).left, C.D (e + 1) i ⊓ C.D (e + 1) j), (∀ i j, c i j ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _) → (∀ i j l, rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) j) (c i j) + rs (Y (e + 1)).left (inf_le_left.trans inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) j ⊓ C.D (e + 1) l) (c j l) = rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) l) (c i l)) → ∃ a : ∀ i, Γ((Y (e + 1)).left, C.D (e + 1) i), (∀ i, a i ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _) ∧ ∀ i j, c i j = rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (a i) - rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (a j)) → ∀ (L : LB (Y e).left) (L' : LB (Y (e + 1)).left) (u : LB.Iso L (L'.pull (β e))), L.IsLB → L'.IsLB → u.IsGen → LBIso (L'.pull (γ (e + 1))) (GlobalTheory.AbLaw.pw H₀ k) → ∀ σ : LB.Sec L, ∃ σ' : LB.Sec L', Rel (β e) u σ' σ := by
  intro R _ I Y β hβ n C H₀ s₀ hH₀ hs₀ γ hγ0 hγ e k hc L L' u hL hL' hu hpw σ
  obtain ⟨g, hMLB, ⟨ω, hω⟩, hcong⟩ := GlobalTheory.T.exists_chart_cocycle_of_pullback_power_standard R I Y β hβ n C H₀ s₀ hH₀ hs₀ γ hγ0 hγ (e + 1) k L' hL' hpw
  have hup : PGen u := (isGen_iff u).1 hu
  choose σi hσi using fun i => glue_chart (M := (⟨Fin (n + 1), C.D (e + 1), g⟩ : LB (Y (e + 1)).left)) (β e) ω hω u
    hup hMLB hL' hL σ i
  have hcoc : ∀ z i j, β e z ∈ C.D (e + 1) i → β e z ∈ C.D (e + 1) j →
      gs (𝟙 _) z _ (σi i) = gs (β e) z _ (g i j).val * gs (𝟙 _) z _ (σi j) := by
    intro z i j hi hj
    obtain ⟨b, hb⟩ := exists_chart hL' (β e z)
    obtain ⟨c, hc'⟩ := exists_chart hL z
    rw [hσi i z b c hi hb hc', hσi j z b c hj hb hc']
    have h1 := gm_isGen hω (β e) z i j b b hi hj hb hb
    rw [gm_self hL' (β e) z hb, inv_one, mul_one] at h1
    rw [h1, gs_unit (β e) z (C.D (e + 1) i ⊓ C.D (e + 1) j) ⟨hi, hj⟩, Units.val_mul, mul_assoc]
  obtain ⟨σ'', hσ''⟩ := GlobalTheory.T.lift_sections_next_thickening_standardCharts R I Y β hβ n C e k hc g hMLB hcong σi hcoc
  let w := isoPullId ω (F := 𝟙 _) rfl
  have hw : w.IsGen := (isGen_iff w).2 (isoPullId_pgen hω rfl)
  obtain ⟨σ', hσ'⟩ := GlobalTheory.SecPullIso.exists_pull (𝟙 _) _ L' w hMLB hL' hw σ''
  refine ⟨σ', fun z b c hb hc' => ?_⟩
  obtain ⟨i, hi⟩ := exists_chart hMLB (β e z)
  have hR : Rel (𝟙 _) w σ'' σ' := hσ'
  have e1 := hR.pull (β e) z i b hi hb
  rw [Category.comp_id, gw_isoPullId ω rfl (β e) z i b hi hb] at e1
  have e2 : gs (β e) z _ (σ''.f i) = gs (𝟙 _) z _ (σi i) := by
    rw [← hσ'' i, gs_pull (𝟙 _) (β e) z _ hi, Category.id_comp]
  rw [e2, hσi i z b c hi hb hc'] at e1
  exact ((Units.mul_right_inj (gv ω (β e) z i b)).1 e1).symm

end GlobalTheory.FormalAlg
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg.JFrac

open MvPolynomial

theorem exists_rs_eq_pow_mul {X : Scheme} {U V : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))
    (hV : X.basicOpen f = V) (h : V ≤ U) (b : Γ(X, V)) :
    ∃ (M : ℕ) (a : Γ(X, U)), rs X h a = rs X h f ^ M * b := by
  subst hV
  obtain ⟨M, a, ha⟩ :=
    exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X U hU.isCompact hU.isQuasiSeparated f b
  exact ⟨M, a, ha⟩

theorem exists_form : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (e : ℕ) (i j : Fin (n + 1)) (c : Γ((Y e).left, C.D e i ⊓ C.D e j)), c ∈ towerIdeal Y e (I ^ e) _ → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ k : ℕ, ∃ F : MvPolynomial (Fin (n + 1)) R, F.IsHomogeneous (k + 2 * N) ∧ (∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) ∧ rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ev e i F) = rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ N * c := by
  intro R _ I Y β hP n C e i j c hc
  obtain ⟨hbasic, -, -⟩ := GlobalTheory.T.thickeningTower_liftedRatios_projective_relations R I Y β hP n C
  obtain ⟨-, hsurj⟩ := GlobalTheory.T.thickeningTower_liftedRatios_generate_surjective R I Y β hP n C
  have hVU : C.D e i ⊓ C.D e j ≤ C.D e i := inf_le_left
  have hX : ∀ l, C.ev e i (X l) = C.ρ e i l := fun l => by simp [Charts.ev]
  let J : Ideal (MvPolynomial (Fin (n + 1)) R) := Ideal.map MvPolynomial.C (I ^ e)
  let S : Ideal Γ((Y e).left, C.D e i ⊓ C.D e j) :=
    { carrier := {c | ∃ N₁ : ℕ, ∃ G ∈ J,
        rs (Y e).left hVU (C.ev e i G) = rs (Y e).left hVU (C.ρ e i j) ^ N₁ * c}
      add_mem' := by
        rintro a b ⟨N₁, G, hG, h1⟩ ⟨N₂, G', hG', h2⟩
        refine ⟨N₁ + N₂, X j ^ N₂ * G + X j ^ N₁ * G',
          J.add_mem (J.mul_mem_left _ hG) (J.mul_mem_left _ hG'), ?_⟩
        simp only [map_add (f := _), map_mul, map_pow, hX, h1, h2]
        ring
      zero_mem' := ⟨0, 0, J.zero_mem, by simp⟩
      smul_mem' := by
        rintro b a ⟨N₁, G, hG, h1⟩
        obtain ⟨M, a', ha'⟩ := exists_rs_eq_pow_mul (C.aff e i) (C.ρ e i j) (hbasic e i j) hVU b
        obtain ⟨H, rfl⟩ := hsurj e i a'
        refine ⟨M + N₁, H * G, J.mul_mem_left _ hG, ?_⟩
        simp only [map_mul, ha', h1, smul_eq_mul]
        ring }
  have hcS : c ∈ S := by
    refine (Ideal.map_le_iff_le_comap.2 (fun r hr => ?_)) hc
    refine ⟨0, MvPolynomial.C r, Ideal.mem_map_of_mem _ hr, ?_⟩
    simp [Charts.ev, rs_cst]
  obtain ⟨N₁, G, hG, hN₁⟩ := hcS
  have hGc : ∀ d, homogeneousComponent d G ∈ J := fun d => by
    refine MvPolynomial.mem_map_C_iff.2 fun m => ?_
    rw [coeff_homogeneousComponent]
    split_ifs
    · exact MvPolynomial.mem_map_C_iff.1 hG m
    · exact (I ^ e).zero_mem
  have hfix : ∀ d t, C.ρ e i i ^ t * C.ev e i (homogeneousComponent d G) =
      C.ev e i (homogeneousComponent d G) := fun d t => by
    have h1 := (GlobalTheory.T.homogeneousForm_chart_change_coeff_ideal_pow R I Y β hP n C e d (homogeneousComponent d G)
      (homogeneousComponent_isHomogeneous d G) (MvPolynomial.mem_map_C_iff.1 (hGc d)) i i).2.1
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ (C.ρ e i i) t, mul_assoc, h1, ih]
  refine ⟨N₁ + G.totalDegree, fun N hN k => ?_⟩
  refine ⟨X j ^ (N - N₁) * ∑ d ∈ Finset.range (G.totalDegree + 1),
      X i ^ (k + N + N₁ - d) * homogeneousComponent d G, ?_, ?_, ?_⟩
  · have hdeg : k + 2 * N = (N - N₁) + (k + N + N₁) := by omega
    rw [hdeg]
    refine (isHomogeneous_X_pow _ _).mul (IsHomogeneous.sum _ _ _ fun d hd => ?_)
    have hd' : d ≤ k + N + N₁ := by
      have := Finset.mem_range.1 hd
      omega
    have := (isHomogeneous_X_pow i (k + N + N₁ - d)).mul (homogeneousComponent_isHomogeneous d G)
    rwa [Nat.sub_add_cancel hd'] at this
  · exact MvPolynomial.mem_map_C_iff.1
      (J.mul_mem_left _ (J.sum_mem fun d _ => J.mul_mem_left _ (hGc d)))
  · have hsum : C.ev e i (∑ d ∈ Finset.range (G.totalDegree + 1),
        X i ^ (k + N + N₁ - d) * homogeneousComponent d G) = C.ev e i G := by

      rw [map_sum]

      conv_rhs => rw [← sum_homogeneousComponent G, map_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [map_mul, map_pow, hX, hfix]
    rw [map_mul, hsum, map_mul, hN₁, map_pow, map_pow, hX, ← mul_assoc, ← pow_add,
      Nat.sub_add_cancel (by omega : N₁ ≤ N)]

end GlobalTheory.FormalAlg.JFrac
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

namespace GlobalTheory.FormalAlg.TripleKill

theorem rs_rs {X : Scheme} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(X, U)) :
    rs X h2 (rs X h1 x) = rs X (h2.trans h1) x := by
  simp only [rs]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem ev_triple_kill : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (e d : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous d → (∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) → ∀ i j l, rs (Y e).left (inf_le_left.trans inf_le_left : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i) (C.ev e i F) = 0 → ∃ L : ℕ, ∀ m, C.ev e m ((MvPolynomial.X i * MvPolynomial.X j * MvPolynomial.X l) ^ L * F) = 0 := by
  intro R _ I Y β hpb n C e d F hF hI i j l h0
  have hlev := (GlobalTheory.T.thickeningTower_liftedRatios_projective_relations R I Y β hpb n C).1
  have htr := GlobalTheory.T.homogeneousForm_chart_change_coeff_ideal_pow R I Y β hpb n C e d F hF hI
  have key : ∀ m, ∃ L : ℕ, (C.ρ e m i * C.ρ e m j * C.ρ e m l) ^ L * C.ev e m F = 0 := by
    intro m
    apply exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen _ (C.aff e m)
    have hb : (Y e).left.basicOpen (C.ρ e m i * C.ρ e m j * C.ρ e m l) =
        (C.D e m ⊓ C.D e i) ⊓ (C.D e m ⊓ C.D e j) ⊓ (C.D e m ⊓ C.D e l) := by
      rw [Scheme.basicOpen_mul, Scheme.basicOpen_mul, hlev, hlev, hlev]
    have hW1 : (Y e).left.basicOpen (C.ρ e m i * C.ρ e m j * C.ρ e m l) ≤ C.D e m ⊓ C.D e i :=
      hb.le.trans (inf_le_left.trans inf_le_left)
    have hW2 : (Y e).left.basicOpen (C.ρ e m i * C.ρ e m j * C.ρ e m l) ≤ C.D e i ⊓ C.D e j ⊓ C.D e l :=
      hb.le.trans (le_inf (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_right))
        (inf_le_left.trans (inf_le_right.trans inf_le_right))) (inf_le_right.trans inf_le_right))
    change rs (Y e).left ((Y e).left.basicOpen_le _) (C.ev e m F) = 0
    have h1 := (htr m i).2.2
    have h2 : rs (Y e).left hW1 (rs (Y e).left (inf_le_left : C.D e m ⊓ C.D e i ≤ C.D e m) (C.ev e m F)) = 0 := by
      rw [h1, map_mul, rs_rs, ← rs_rs (inf_le_left.trans inf_le_left : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i) hW2, h0,
        map_zero, mul_zero]
    rw [rs_rs] at h2
    exact h2
  choose Lf hL using key
  refine ⟨Finset.univ.sup Lf, fun m => ?_⟩
  have hle : Lf m ≤ Finset.univ.sup Lf := Finset.le_sup (Finset.mem_univ m)
  have hev : C.ev e m ((MvPolynomial.X i * MvPolynomial.X j * MvPolynomial.X l) ^ Finset.univ.sup Lf * F) =
      (C.ρ e m i * C.ρ e m j * C.ρ e m l) ^ Finset.univ.sup Lf * C.ev e m F := by
    simp [Charts.ev, map_mul, map_pow]
  rw [hev, ← Nat.sub_add_cancel hle, pow_add (C.ρ e m i * C.ρ e m j * C.ρ e m l), mul_assoc, hL m, mul_zero]

end GlobalTheory.FormalAlg.TripleKill
end

section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem _root_.GlobalTheory.T.exists_nonzero_scalarWeight_cuspForm_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (Z : Comp Xo c), ∃ n₀ : ℕ, 0 < n₀ ∧ Even n₀ ∧ ∃ f₀ ∈ cusp Xo c U 0 n₀, ∃ z ∈ framesOn (U σ) Z, rdU (U σ) f₀ z.1 z.2 ≠ 0 := by
  first | exact @GlobalTheory.ScalarCusp.exists_scalar_cusp_ne_zero | exact GlobalTheory.ScalarCusp.exists_scalar_cusp_ne_zero | (intros; apply GlobalTheory.ScalarCusp.exists_scalar_cusp_ne_zero <;> assumption)
end
