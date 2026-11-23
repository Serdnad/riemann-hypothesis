module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionsPowVeryAmpleAreFormsOfClosedFibre
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyFormalUniformisationTower
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle156
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle029
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSplitTorusKernelGenericFibre
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusStableWeightsGenericFibre
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SvalEqZeroOfExpandsAt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle042
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle155
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle080
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
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

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_section_lift_closed_baseChange_of_h1Vanishes : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)), Flat f → IsProjBy f → ∀ M : LB X, M.IsLB → ∀ (K : Type) [Field K] (g₀ : A →+* K), Function.Surjective g₀ → ∀ (X₀ : Scheme.{0}) (π : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ f (Spec.map (CommRingCat.ofHom g₀)) → ∀ (M₀ : LB X₀) (w₀ : LB.Iso M₀ (M.pull π)), M₀.IsLB → w₀.IsGen → FirstCohomologyVanishes M₀ → ∀ (A' : Type) [CommRing A'] (g : A →+* A'), Function.Surjective g → ∀ (X' : Scheme.{0}) (β : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of A')), IsPullback β f' f (Spec.map (CommRingCat.ofHom g)) → ∀ (M' : LB X') (w : LB.Iso M' (M.pull β)), M'.IsLB → w.IsGen → ∀ s' : LB.Sec M', ∃ s : LB.Sec M, (∀ z (k : (M).ι) (k' : (M').ι), (β) z ∈ (M).U k → z ∈ (M').U k' → gs (β) z _ ((s).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s').f k')) := by
  first | exact @GlobalTheory.SecLiftClosed.exists_lift | exact GlobalTheory.SecLiftClosed.exists_lift | (intros; apply GlobalTheory.SecLiftClosed.exists_lift <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.sections_pow_veryAmple_are_forms_of_closedFibre : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)), Flat f → ∀ (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (K : Type) [Field K] (g₀ : A →+* K), Function.Surjective g₀ → ∀ (X₀ : Scheme.{0}) (π : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ f (Spec.map (CommRingCat.ofHom g₀)) → ∀ (H₀ : LB X₀) (w₀ : LB.Iso H₀ (H.pull π)) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → w₀.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H₀).ι), (π) z ∈ (H).U k → z ∈ (H₀).U k' → gs (π) z _ ((s j).f k) = (Geo.Tor.gw (w₀) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s₀ j).f k'))) → ∀ t : ℕ, FirstCohomologyVanishes (pw H₀ t) → (∀ σ : LB.Sec (pw H₀ t), ∃ P : MvPolynomial (Fin (n + 1)) K, P.IsHomogeneous t ∧ ∀ k : H₀.ι, σ.f k = MvPolynomial.eval₂Hom (cst (f₀) ((H₀).U k)) (fun j => (s₀ j).f k) (P)) → ∀ σ : LB.Sec (pw H t), ∃ P : MvPolynomial (Fin (n + 1)) A, P.IsHomogeneous t ∧ ∀ k : H.ι, σ.f k = MvPolynomial.eval₂Hom (cst (f) ((H).U k)) (fun j => (s j).f k) (P) := by
  first | exact @GlobalTheory.Degen.sections_pw_are_forms_of_closed_fibre | exact GlobalTheory.Degen.sections_pw_are_forms_of_closed_fibre | (intros; apply GlobalTheory.Degen.sections_pw_are_forms_of_closed_fibre <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.fullTorsionObject_existsUnique_moduliPoint : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype), ∀ (K : Type) [Field K] [IsAlgClosed K] (bF : c.F →+* K), (∀ o : Full D K, (∀ r : c.F, (r : ℂ) = H.rt0 → o.ρ = bF r) → (∀ z : c.F, (z : ℂ) = zeta l.A → (o.I.ζ l.A : K) = bF z) → ∃! y : Sp K ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap bF ∧ FullAt Y y o) ∧ (∀ y : Sp K ⟶ Xo.XF c, ∃ o, FullAt Y y o) ∧ ∀ (K' : Type) [Field K'] (f : K →+* K') y o o', FullAt Y y o → FullExt f o o' → FullAt Y (spMap f ≫ y) o' := by
  first | exact @GlobalTheory.FullPoint.fullAt_existsUnique_exists_ext | exact GlobalTheory.FullPoint.fullAt_existsUnique_exists_ext | (intros; apply GlobalTheory.FullPoint.fullAt_existsUnique_exists_ext <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.exists_arcLift_extension_larger_closed_field : Laws → BrGtSt → BrWpSt → AllA fun {_} _ _ _ {_} {_} {_} {_} {_} {_} _ {O'} _ _ {_} a => ∀ (F F' : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing O') F] [Field F'] [IsAlgClosed F'] [Algebra (FractionRing O') F'] (f : F →+* F'), f.comp (algebraMap (FractionRing O') F) = algebraMap (FractionRing O') F' → ∀ S : ValuationSubring F', (∀ r : O', algebraMap (FractionRing O') F' (algebraMap O' _ r) ∈ S) → ∀ A : Lift a F, ∃ A' : Lift a F', A'.ν.Integral S ∧ ∃ I : NumD.Hom f A.N A'.N, I.lam = 1 ∧ f A.ρ = A'.ρ ∧ (∀ n, 0 < n → f (A.I.ζ n) = A'.I.ζ n) ∧ (∀ y, A'.ν.eX (I.e y) = A.ν.eX y) ∧ ∀ n v, (A'.q n v).1.1.toAdd = I.e (A.q n v).1.1.toAdd ∧ I.Rel (A.q n v).1.2 (A'.q n v).1.2 := by
  first | exact @GlobalTheory.LiftExt.exists_lift_ext | exact GlobalTheory.LiftExt.exists_lift_ext | (intros; apply GlobalTheory.LiftExt.exists_lift_ext <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.nonempty_algebraisation_formal_tower_ample : Laws → Laws2 → Ega → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G) (X : Type) [AddCommGroup X] (T : TowerR I P X), RelAmple (T.l 0).Q.B (T.l 0).D.M.L.L → Nonempty T.Alg := by
  first | exact @GlobalTheory.TowerAlg.nonempty_alg | exact GlobalTheory.TowerAlg.nonempty_alg | (intros; apply GlobalTheory.TowerAlg.nonempty_alg <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.nonempty_formalUniformisationTower : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G), IsSemiAbelian G → HypW G P.L.L → IsProper (pullback.snd G.hom (jK R)) → SplitOver G I → ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X), Nonempty (TowerR I P X) := by
  first | exact @GlobalTheory.FormalTower.nonempty_towerR | exact GlobalTheory.FormalTower.nonempty_towerR | (intros; apply GlobalTheory.FormalTower.nonempty_towerR <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem nonempty_torusExtension_of_surjective_points : ∀ (k : Type) [Field k] [IsAlgClosed k] (G G₁ : Over (Sp k)) [GrpObj G] [GrpObj G₁], SmConn G₁ → Nonempty (TorusExtension G) → ∀ r : G ⟶ G₁, IsMonHom r → (∀ y : (𝟙_ (Over (Sp k)) ⟶ G₁), ∃ x : (𝟙_ (Over (Sp k)) ⟶ G), x ≫ r = y) → Nonempty (TorusExtension G₁) := by
  intro k _ _ G G₁ _ _ hG₁ ⟨E⟩ r hr hsurj
  obtain ⟨X, _, _, _, B₁, _, i₁, q₁, ⟨hi, hq, hfl, hsu, haf, hker, hc, hsm, hsep, hqc, hgc⟩, hno⟩ :=
    MaxTorus.exists_quot_no_cocharacter k G₁ hG₁
  let _ := E.addCommGroup
  let _ := E.free
  let _ := E.finite
  let _ := E.grpB
  have := E.i_hom
  have := E.q_hom
  have hkill : E.i ≫ r ≫ q₁ = 1 := GlobalTheory.T.splitTorus_hom_eq_one_of_no_cocharacter' _ B₁ E.X hno _ inferInstance
  obtain ⟨⟨ψ, -, hψ⟩, -⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective _ G E.B B₁ E.q (r ≫ q₁)
    E.q_hom inferInstance E.q_flat E.q_surjective E.q_quasiCompact (fun T x hx => by
      have h := E.isKernel.lift_fst x (toUnit T) hx
      rw [← h, Category.assoc, hkill, MonObj.comp_one])
  have := E.isAbelian.proper
  have : UniversallyClosed (ψ.left ≫ B₁.hom) := by rw [Over.w]; infer_instance
  have : UniversallyClosed ψ.left := .of_comp_of_isSeparated _ B₁.hom
  have := hG₁.2.1
  have : JacobsonSpace G₁.left := LocallyOfFiniteType.jacobsonSpace G₁.hom
  have hZ : IsClosed (q₁.left ⁻¹' Set.range ψ.left) :=
    ψ.left.isClosedMap.isClosed_range.preimage q₁.left.continuous
  let pt : Spec (CommRingCat.of k) := IsLocalRing.closedPoint k
  have hsub : closedPoints G₁.left ⊆ q₁.left ⁻¹' Set.range ψ.left := by
    intro y hy
    obtain ⟨x, hx⟩ := hsurj (Over.homMk (pointOfClosedPoint (K := k) G₁.hom y hy)
      (pointOfClosedPoint_comp (K := k) G₁.hom y hy))
    have hy' : r.left (x.left pt) = y := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hx]
      exact pointOfClosedPoint_apply (K := k) G₁.hom y hy pt
    refine ⟨E.q.left (x.left pt), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hψ, Over.comp_left, Scheme.Hom.comp_apply, hy']
  have hall := closure_minimal hsub hZ
  rw [closure_closedPoints] at hall
  have : Surjective ψ.left := ⟨fun b => by
    obtain ⟨g, rfl⟩ := q₁.left.surjective b
    exact hall (Set.mem_univ g)⟩
  have : UniversallyClosed B₁.hom := .of_comp_surjective ψ.left _
  have : IsProper B₁.hom := {}
  exact ⟨{ X := X, B := B₁, isAbelian := ⟨hc, hsm, this, hgc⟩, q := q₁, q_hom := hq, q_flat := hfl,
           q_surjective := hsu, q_quasiCompact := inferInstance, i := i₁, i_hom := hi,
           isKernel := hker }⟩

end GlobalTheory.SS
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_torusQuotient_no_cocharacter : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X) (B : Over (Sp k)) (_ : GrpObj B) (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), IsQuot i q ∧ ∀ f : Gm (Sp k) ⟶ B, IsMonHom f → f = 1 := by
  first | exact @GlobalTheory.SS.MaxTorus.exists_quot_no_cocharacter | exact GlobalTheory.SS.MaxTorus.exists_quot_no_cocharacter | (intros; apply GlobalTheory.SS.MaxTorus.exists_quot_no_cocharacter <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

theorem _root_.GlobalTheory.T.exists_splitTorus_kernel_genericFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → ∀ (a) (j : Fin d → C.I), C.Based c a j → ∃ i : splitTorus (Sp (FractionRing R)) (Fin d → ℤ) ⟶ ((Over.pullback (Out.jK R)).obj G), Charts.KerIs (H := ((Over.pullback (Out.jK R)).obj G)) (C.pull (pullback.fst G.hom (Out.jK R))) a j i := by
  first | exact @GlobalTheory.ZJ.GenericTorus.exists_kerIs_generic | exact GlobalTheory.ZJ.GenericTorus.exists_kerIs_generic | (intros; apply GlobalTheory.ZJ.GenericTorus.exists_kerIs_generic <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

theorem _root_.GlobalTheory.T.torusStable_weights_genericFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → ∀ (a) (j : Fin d → C.I), C.Based c a j → ∀ i : splitTorus (Sp (FractionRing R)) (Fin d → ℤ) ⟶ ((Over.pullback (Out.jK R)).obj G), Charts.KerIs (H := ((Over.pullback (Out.jK R)).obj G)) (C.pull (pullback.fst G.hom (Out.jK R))) a j i → (∀ a', Stable i ((C.pull (pullback.fst G.hom (Out.jK R))).W a')) ∧ (∀ a' j', C.wt j' = C.c₀ → HasWt i ((C.pull (pullback.fst G.hom (Out.jK R))).W a') ((C.pull (pullback.fst G.hom (Out.jK R))).r a' j') 0) ∧ ∀ a' j' n, C.wt j' = c n → HasWt i ((C.pull (pullback.fst G.hom (Out.jK R))).W a') ((C.pull (pullback.fst G.hom (Out.jK R))).r a' j') (Pi.single n 1) := by
  first | exact @GlobalTheory.ZJ.GenericWt.stable_and_hasWt_generic | exact GlobalTheory.ZJ.GenericWt.stable_and_hasWt_generic | (intros; apply GlobalTheory.ZJ.GenericWt.stable_and_hasWt_generic <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ZH.AdaptedSpan

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldBaseChange GlobalTheory.PullbackValuation GlobalTheory.IntegralCombination

variable {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} {D : DegData V I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))} [GrpObj G]
  [IsCommMonObj G]

abbrev SecGen (U : UnifPre I D A G) (k : ℕ) : Type :=
  SecOver (R := FractionRing V) (pullback.snd G.hom (jK V))
    (LB.LinComb U.LG.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ)))

def toGen (U : UnifPre I D A G) (k : ℕ) : SecG U k →ₛₗ[algebraMap V (FractionRing V)] SecGen U k :=
  pullOver U.LG.L (fun _ : Fin 1 => (k : ℤ)) (pullback.condition : pullback.fst G.hom (jK V) ≫ G.hom = _)
    (fun _ => (Category.comp_id _).symm)

def famAt (D : DegPre V) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) (α : D.X) :
    Fam D F k →ₗ[F] SecAbF D F k α where
  toFun s := s.s α
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem secScal_iff_pullAb (D : DegPre V) (F : Type) [Field F] [Algebra (FractionRing V) F] {k : ℕ} {α : D.X}
    (s : SecAbF D F k α) (g : SecAb D k α) (r : V) :
    GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) s (D.famφB α) (DegPre.famε k) g (DegPre.prB D F).left
      (scal (DegPre.BF D F).hom r) ↔ pullAb D F k α g = toF V F r • s :=
  secScal_iff (prB_over D F) (GC.famφ_eq D F α) D.P.isLB s g _ (toF V F)
    ((Over.w (DegPre.prB D F)).symm.trans (prB_over D F)) r

theorem expandsAt_sum (U : UnifPre I D A G) (e k : ℕ) {J : Type} [Fintype J] (σ : J → SecG U k)
    (f : J → ∀ α, SecAb D.toPre k α) (h : ∀ p, U.ExpandsAt e k (σ p) (f p)) (b : J → V) :
    U.ExpandsAt e k (∑ p, b p • σ p : SecG U k) (fun α => (∑ p, b p • f p α : SecAb D.toPre k α)) := by
  have E := (Fintype.equivFin J).symm
  have H := expandsAt_comb U e k (fun p => σ (E p)) (fun p => f (E p)) (fun p => h (E p)) (fun p => b (E p))
  rw [E.sum_comp (fun p => b p • σ p)] at H
  exact (congrArg (U.ExpandsAt e k _) (funext fun α => E.sum_comp (fun p => b p • f p α))).mp H

theorem expands_toGen (U : UnifPre I D A G) (k : ℕ) (τ : SecG U k) (g : ∀ α, SecAb D.toPre k α)
    (s : Fam D.toPre (FractionRing V) k) (hτ : ∀ e, U.ExpandsAt e k τ g)
    (hs : ∀ α, pullAb D.toPre _ k α (g α) = famAt D.toPre _ k α s) : U.Expands k (toGen U k τ) s := by
  refine ⟨1, one_ne_zero, τ, g, ?_, fun α => ?_, hτ⟩
  · exact (secScal_iff pullback.condition _ U.LG.isLB _ _ _ (algebraMap V (FractionRing V)) rfl 1).2
      (by rw [map_one, one_smul]; rfl)
  · exact (secScal_iff_pullAb _ _ (famAt D.toPre _ k α s) _ 1).2 (by rw [map_one, one_smul]; exact hs α)


open Classical in
theorem exists_comb (hG : GlobalFnsSt) (U : Unif I D A G) {k : ℕ} (hk : 1 ≤ k) {J : Type} [Fintype J]
    (σ : J → SecG U.toUnifPre k) (cls : J → D.toPre.X) (f : J → ∀ α, SecAb D.toPre k α)
    (h₂ : ∀ i i', (∃ m, cls i = cls i' + k • m) → cls i = cls i') (h₃ : ∀ α, ∃ i m, α = cls i + k • m)
    (h₄ : ∀ i e, U.toUnifPre.ExpandsAt e k (σ i) (f i))
    (h₅ : ∀ i, ∃ s : Fam D.toPre (FractionRing V) k, FamOf D.toPre _ (f i) s)
    (h₆ : ∀ i α, (∀ m, α ≠ cls i + k • m) → ∀ j, LB.Sec.f (f i α) j = 0)
    (h₇ : ∀ i₀, IsBasisB D.toPre (fun i : {i // cls i = cls i₀} => f i (cls i₀)))
    (s : SecGen U.toUnifPre k) : ∃ a : J → FractionRing V, s = ∑ i, a i • toGen U.toUnifPre k (σ i) := by
  obtain ⟨F, ⟨r, hr, τ, g, hτ, hg, hE⟩, -⟩ := (U.expand k hk).1 s
  have hτ' : toGen U.toUnifPre k τ = algebraMap V (FractionRing V) r • s :=
    (secScal_iff pullback.condition _ U.LG.isLB s τ _ (algebraMap V (FractionRing V)) rfl r).1 hτ
  have hg' : ∀ α, pullAb D.toPre _ k α (g α) = famAt D.toPre _ k α (toF V (FractionRing V) r • F) := fun α => by
    rw [map_smul]; exact (secScal_iff_pullAb _ _ _ _ r).1 (hg α)
  choose t ht using h₅
  have ht' : ∀ i α, pullAb D.toPre _ k α (f i α) = famAt D.toPre _ k α (t i) := fun i α => by
    have := (secScal_iff_pullAb _ _ (famAt D.toPre _ k α (t i)) (f i α) 1).1 (by
      have e : scal (DegPre.BF D.toPre (FractionRing V)).hom (1 : V) = 1 := by
        unfold scal; rw [map_one, map_one]
      rw [e]; exact ht i α)
    rwa [map_one, one_smul] at this
  have hb : ∀ c : D.toPre.X, ∃ b : J → V, (∃ i₀, cls i₀ = c) →
      (show SecAb D.toPre k c from g c) = ∑ i, (if cls i = c then b i else 0) • f i c := fun c => by
    by_cases hc : ∃ i₀, cls i₀ = c
    · obtain ⟨i₀, rfl⟩ := hc
      obtain ⟨a, ha, -⟩ := h₇ i₀ (g (cls i₀))
      refine ⟨fun i => if h : cls i = cls i₀ then a ⟨i, h⟩ else 0, fun _ => ?_⟩
      have e : (show SecAb D.toPre k (cls i₀) from g (cls i₀)) =
          ∑ i : {i // cls i = cls i₀}, a i • f i (cls i₀) :=
        SecOver.ext _ _ fun j => (ha j).trans
          (map_sum (chartLin D.toPre.P.A.hom _ j) (fun i : {i // cls i = cls i₀} => a i • f i (cls i₀)) _).symm
      rw [e, ← Fintype.sum_subtype_add_sum_subtype (fun i => cls i = cls i₀),
        Finset.sum_eq_zero (s := (Finset.univ : Finset {i // ¬ cls i = cls i₀}))
          (fun i _ => by rw [if_neg i.2, zero_smul]), add_zero]
      exact Finset.sum_congr rfl fun i _ => by rw [if_pos i.2]; beta_reduce; rw [dite_eq_left i.2]
    · exact ⟨0, fun h => absurd h hc⟩
  choose b hb using hb
  have key : toF V (FractionRing V) r • F = ∑ i, toF V (FractionRing V) (b (cls i) i) • t i := by
    refine fam_ext fun α j => ?_
    obtain ⟨i₀, m, rfl⟩ := h₃ α
    refine congrArg (LB.Sec.f · j) (GlobalTheory.FamFree.eq_of_eq_add_nsmul hG _ _ ⟨m, rfl⟩ ?_)
    refine (hg' _).symm.trans (Eq.trans ?_ (map_sum (famAt D.toPre _ k (cls i₀)) _ _).symm)
    refine (congrArg (pullAb D.toPre _ k (cls i₀)) (hb _ ⟨i₀, rfl⟩)).trans ?_

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smulₛₗ, map_smul, ← ht']
    split_ifs with h
    · rw [h]
    · have z : f i (cls i₀) = 0 := SecOver.ext _ _ (h₆ i _ fun m e => h (h₂ i₀ i ⟨m, e⟩).symm)
      rw [z, map_zero (pullAb D.toPre _ k (cls i₀)), smul_zero, smul_zero]
  have E₁ := expands_toGen U.toUnifPre k τ g _ hE hg'
  have E₂ := expands_toGen U.toUnifPre k _ _ (∑ i, toF V (FractionRing V) (b (cls i) i) • t i)
    (fun e => expandsAt_sum U.toUnifPre e k σ f (fun i => h₄ i e) (fun i => b (cls i) i)) (fun α => by

      rw [map_sum, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smulₛₗ, map_smul, ← ht'])
  rw [key] at E₁
  have e : toGen U.toUnifPre k τ = toGen U.toUnifPre k (∑ i, b (cls i) i • σ i) :=
    ((U.expand k hk).2 _).unique E₁ E₂
  have hr' : algebraMap V (FractionRing V) r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V _)).2 hr
  refine ⟨fun i => (algebraMap V (FractionRing V) r)⁻¹ * algebraMap V _ (b (cls i) i), ?_⟩

  rw [hτ', map_sum] at e
  rw [← inv_smul_smul₀ hr' s, e, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smulₛₗ, smul_smul]

end GlobalTheory.ZH.AdaptedSpan
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.ThetaFibre

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J}

theorem proj_mulVec_mem (hB : BaseFacts S M U₀ EE) (z : M.Z) {v : S.J → Ω} (hv : v ∈ EE.E z) :
    ((S.proj (S.TT M z) 0).map (algebraMap o Ω)).mulVec v ∈ EE.E z := by
  have hT : S.TT M z ≤ S.HH M z := (hB.free z).2 ▸ (hB.free z).1.1
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  have := Fintype.ofFinite (S.TT M z)
  have e : ((S.proj (S.TT M z) 0).map (algebraMap o Ω)).mulVec v =
      algebraMap o (M.O z) (Ring.inverse (Nat.card (S.TT M z) : o)) •
        ∑ t : S.TT M z, ((S.ρ t).map (algebraMap o Ω)).mulVec v := by
    ext i
    simp [ThetaSys.proj, finsum_eq_sum_of_fintype, Matrix.mulVec, dotProduct, Matrix.sum_apply,
      Algebra.smul_def (A := Ω), Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]
    rw [Finset.sum_comm]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun t _ => hB.stab z _ (hT t.2) v hv)

theorem proj_mulVec_regular (hB : BaseFacts S M U₀ EE) {z : M.Z} (hz : IsClosed ({z} : Set M.Z))
    {v : S.J → Ω} (hv : v ∈ EE.E z) (j : S.J) :
    ((S.proj (S.TT M z) 0).map (algebraMap o Ω)).mulVec v j ∈ M.O z := by
  refine hB.zero z hz _ (proj_mulVec_mem hB z hv) ?_ j
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul,
    GlobalTheory.ThetaBound.proj_mul_proj S _ _ le_rfl (hB.free z).1.1 (hB.free z).1 0 0 fun _ => rfl]

theorem proj_col_eq_zero (hB : BaseFacts S M U₀ EE) {z : M.Z} (hz : IsClosed ({z} : Set M.Z))
    {K : Type} [Field K] (y : M.O z →+* K) (B : Matrix S.J S.J Ω) (hBm : ∀ k, B k ∈ EE.E z)
    (a : S.J → M.O z) (i : S.J) (ha : ∀ j, ∑ k, (a k : Ω) * B k j = (1 : Matrix S.J S.J Ω) i j)
    (h0 : ∀ k, y (a k) = 0) (j : S.J) :
    y (algebraMap o (M.O z) (S.proj (S.TT M z) 0 j i)) = 0 := by
  have e : algebraMap o (M.O z) (S.proj (S.TT M z) 0 j i) =
      ∑ k, a k * ⟨_, proj_mulVec_regular hB hz (hBm k) j⟩ := by
    apply Subtype.ext
    have h1 : ∑ m, algebraMap o Ω (S.proj (S.TT M z) 0 j m) * (1 : Matrix S.J S.J Ω) i m =
        algebraMap o Ω (S.proj (S.TT M z) 0 j i) := by
      simp [Matrix.one_apply]
    simp only [Subalgebra.coe_algebraMap, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul,
      Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum]
    rw [← h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← ha, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

  rw [e, map_sum]
  exact Finset.sum_eq_zero fun k _ => by rw [map_mul, h0, zero_mul]

theorem exists_mem_nonzeroLocus_fibre : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), S.Big → ρ.HasGeo → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → ∃ x ∈ nonzeroLocus (Q.st ρ.i₀), x ∈ Q.G ∧ Q.P.hom x = z := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q hbig hgeo z hz
  by_contra hne
  have hzc : z ∈ ⨆ l, Q.W l := by rw [Q.cover]; trivial
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hzc
  obtain ⟨K, _, x, hx, hind⟩ := GlobalTheory.T.thetaSections_independent_on_closed_fibre hL o Ω S ρ M U₀ EE hB Q hbig hgeo l z hl hz
  have hc : (fun k => valF x (Q.W l) (Q.c l ρ.i₀ k)) = 0 := by
    refine hind _ fun g j hg hgx => ?_
    by_cases hj : ⊤ ≤ g ⁻¹ᵁ (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι).U j
    · have hw : Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) g
          (fun i => valF g _ ((Q.σ l i).f j)) :=
        ⟨j, 1, hj, fun i => by rw [Units.val_one, _root_.one_mul]; rfl⟩
      have hr := Q.rel l K g _ hw
      rw [hgx] at hr
      by_contra h0
      have hu := (CrdCalc.crd_isUnit_iff ρ.i₀ hr).1 (isUnit_iff_ne_zero.2 h0)
      refine hne ⟨(g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) (IsLocalRing.closedPoint K), hu (Set.mem_univ _),
        hg ⟨_, rfl⟩, ?_⟩
      have hm : x (IsLocalRing.closedPoint K) ∈ Set.range x := ⟨_, rfl⟩
      rw [hx] at hm
      rw [← hgx] at hm
      exact hm
    · exact Finset.sum_eq_zero fun i _ => mul_eq_zero_of_right _ (dif_neg hj)
  obtain ⟨j, hj⟩ := GlobalTheory.proj_zero_pullback_ne_zero hL o Ω S ρ K
    ((RatModel.valHom x z hx).comp (algebraMap o (M.O z))) _ (hB.free z).1
  refine hj (proj_col_eq_zero hB hz (RatModel.valHom x z hx) (Q.B l)
    (fun k => by rw [Q.basis l z hl]; exact Submodule.subset_span ⟨k, rfl⟩)
    (fun k => ⟨_, RatModel.valF_mem_O hl (Q.c l ρ.i₀ k)⟩) ρ.i₀
    (fun j => congrFun (congrFun (Q.c_inv l) ρ.i₀) j) (fun k => ?_) j)
  rw [RatModel.valHom_apply, RatModel.val_valF (by rw [hx]; exact Set.singleton_subset_iff.2 hl)]
  exact congrFun hc k

end GlobalTheory.ZH.ThetaFibre
end
