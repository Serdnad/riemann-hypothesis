module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle109
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2995
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2985
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2908
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2907
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegPBOfFiniteEtaleCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2671
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle102
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle111
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle137
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle105
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2920
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2909
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2910
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumExt

theorem exists_extLam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R], ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ L : LB ((Over.pullback (jK R)).obj G).left, L.IsLB → ∃ PP : LB (G2 G).left, ExtLam G L PP := by
  intro R _ _ _ G _ _ hG L hL
  haveI := hG.smooth
  haveI := hG.separated
  haveI := hG.quasiCompact
  haveI : GeometricallyIntegral G.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hG.smooth hG.geomConnected
  obtain ⟨L', hL', hb⟩ := GlobalTheory.T.lineBundle_generic_fibre_extends_over_dvr R G L hL
  refine ⟨abelian₂ G L', DVR.linComb_isLB _ hL' _ _, fun κ₂ hκ => ?_⟩
  have h := isGrpPullback_pullback G (jK R)
  let V := lift (pushPt h.1.w (fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)))
    (pushPt h.1.w (snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)))
  have hV : V.left = κ₂ := by
    apply pullback.hom_ext
    · show (V ≫ fst G G).left = κ₂ ≫ (fst G G).left
      rw [hκ.1, lift_fst]
      rfl
    · show (V ≫ snd G G).left = κ₂ ≫ (snd G G).left
      rw [hκ.2, lift_snd]
      rfl
  have c := GlobalTheory.SymSpread.lbIso_cube h hL' hL hb (x2 G) (x2 _) V (fun i => by fin_cases i <;> simp [x2, V])
  rw [hV] at c
  exact c

end GlobalTheory.MumExt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum



theorem lbIso_lam_of_extLam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (L' : LB G.left) (N : LB ((Over.pullback (jK R)).obj G).left) (PP : LB (G2 G).left), L'.IsLB → N.IsLB → LBIso N (L'.pull (pullback.fst G.hom (jK R))) → ExtLam G N PP → LBIso (abelian₂ G L') PP := by
  intro R _ _ _ _ _ G _ _ hG L' N PP hL' hN hNL hE
  have hsm : Smooth G.hom := hG.smooth
  have hgc : GeometricallyConnected G.hom := hG.geomConnected
  have hsm₂ : Smooth (G ⊗ G).hom := by
    show Smooth (pullback.fst G.hom G.hom ≫ G.hom)
    infer_instance
  have hgc₂ : GeometricallyConnected (G ⊗ G).hom := by
    show GeometricallyConnected (pullback.fst G.hom G.hom ≫ G.hom)
    exact GeometricallyConnected.comp _ _
  have hgi₂ : GeometricallyIntegral (G2 G).hom := GlobalTheory.geometricallyIntegral_of_smooth _
  have hLam : (abelian₂ G L').IsLB := DVR.linComb_isLB _ hL' _ _
  have hPP : PP.IsLB := hE.1

  have hpb := isGrpPullback_pullback G (jK R)
  obtain ⟨β₂, hsq, hβ⟩ := GlobalTheory.T.exists_mumfordBundle_pullback_grpPullback _ _ (jK R) G ((Over.pullback (jK R)).obj G) (pullback.fst G.hom (jK R)) hpb
  have h1 : LBIso (abelian₂ G L') ((abelian₂ G L').pull (𝟙 _)) :=
    LBIso.chartPull (chartPullId _) (Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) (GlobalTheory.PolBaseChange.lbIso_refl hLam)
  have h2 := hβ L' N _ (abelian₂ G L') (𝟙 _) hL' hN hLam hNL h1
  rw [Category.comp_id] at h2
  have h3 := hE.2 β₂ hsq
  have hgen : LBIso ((abelian₂ G L').pull β₂) (PP.pull β₂) :=
    LBIso.trans (pull_isLB hLam _) (DVR.linComb_isLB _ hN _ _) (pull_isLB hPP _) (LBIso.symm h2) h3

  let p1 := pullback.fst (G2 G).hom (jK R)
  let p2 := pullback.snd (G2 G).hom (jK R)
  let T : Over (Spec (CommRingCat.of (FractionRing R))) := Over.mk p2
  have wx : (p1 ≫ (fst G G).left) ≫ G.hom = p2 ≫ jK R := by
    rw [Category.assoc, Over.w (fst G G)]; exact pullback.condition
  have wy : (p1 ≫ (snd G G).left) ≫ G.hom = p2 ≫ jK R := by
    rw [Category.assoc, Over.w (snd G G)]; exact pullback.condition
  let x : T ⟶ (Over.pullback (jK R)).obj G := Over.homMk (hpb.1.lift _ _ wx) (hpb.1.lift_snd _ _ _)
  let y : T ⟶ (Over.pullback (jK R)).obj G := Over.homMk (hpb.1.lift _ _ wy) (hpb.1.lift_snd _ _ _)
  let i : pullback (G2 G).hom (jK R) ⟶ (G2 ((Over.pullback (jK R)).obj G)).left := (lift x y).left
  have hi : i ≫ β₂ = p1 := by
    apply pullback.hom_ext
    · show i ≫ β₂ ≫ (fst G G).left = p1 ≫ (fst G G).left
      rw [hsq.1, ← Category.assoc]
      show (lift x y ≫ fst _ _).left ≫ _ = _
      rw [lift_fst]
      exact hpb.1.lift_fst _ _ _
    · show i ≫ β₂ ≫ (snd G G).left = p1 ≫ (snd G G).left
      rw [hsq.2, ← Category.assoc]
      show (lift x y ≫ snd _ _).left ≫ _ = _
      rw [lift_snd]
      exact hpb.1.lift_fst _ _ _
  have hK : LBIso ((abelian₂ G L').pull p1) (PP.pull p1) :=
    LBIso.chartPull (chartPullSame (abelian₂ G L') (fun _ => p1) (fun _ => β₂) (fun _ => 1) i (fun _ => hi.symm))
      (chartPullSame PP (fun _ => p1) (fun _ => β₂) (fun _ => 1) i (fun _ => hi.symm)) hgen
  exact GlobalTheory.T.lineBundleIso_of_generic_normal_local_base R (G2 G) (lift η[G] η[G]).left (Over.w (lift η[G] η[G])) (abelian₂ G L') PP hLam hPP hK

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_bundle_extension_translate_open : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : LB ((Over.pullback (jK R)).obj G).left) (PP : LB (G2 G).left), L.IsLB → ExtLam G L PP → ∀ (O : G.left.Opens) (N : LB O.toScheme), N.IsLB → LBIso (N.pull (pullback.fst O.ι (pullback.fst G.hom (jK R)))) (L.pull (pullback.snd O.ι (pullback.fst G.hom (jK R)))) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, ∃ N' : LB ((𝟙 G * (toUnit G ≫ a)).left ⁻¹ᵁ O).toScheme, N'.IsLB ∧ LBIso (N'.pull (pullback.fst ((𝟙 G * (toUnit G ≫ a)).left ⁻¹ᵁ O).ι (pullback.fst G.hom (jK R)))) (L.pull (pullback.snd ((𝟙 G * (toUnit G ≫ a)).left ⁻¹ᵁ O).ι (pullback.fst G.hom (jK R)))) := by
  first | exact @GlobalTheory.Mum.exists_ext_translate | exact GlobalTheory.Mum.exists_ext_translate | (intros; apply GlobalTheory.Mum.exists_ext_translate <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.transport_polarisedVariety_finiteExtension_fraction : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∀ (K' : Type) [Field K'] (io : FractionRing R →+* K') (A₁ : PolAV (Sp K')) (α₁ : A₁.A.left ⟶ A.A.left) (α₁₂ : (G2 A₁.A).left ⟶ (G2 A.A).left), IsGrpPullback A₁.A A.A (spMap io) α₁ → Geo.Tor.IsSquare α₁ α₁₂ → LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A.A A.L).pull α₁₂) → ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (ρ : R →+* R₂) (i : K' ≃+* FractionRing R₂), Function.Injective ρ → (∀ r, i (io (algebraMap R _ r)) = algebraMap R₂ _ (ρ r)) → ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left) (β₂ : (G2 G₂).left ⟶ (G2 G).left), IsGrpPullback G₂ G (spMap ρ) β → Geo.Tor.IsSquare β β₂ → ∃ (A₂ : PolAV (Sp (FractionRing R₂))) (gen₂ : ((Over.pullback (jK R₂)).obj G₂) ≅ A₂.A) (q : A₂.A.left ⟶ A₁.A.left), IsMonHom gen₂.hom ∧ ExtLam G₂ (A₂.L.pull gen₂.hom.left) (PP.pull β₂) ∧ IsGrpPullback A₂.A A₁.A (spMap i.toRingHom) q ∧ LBIso A₂.L (A₁.L.pull q) ∧ gen₂.inv.left ≫ pullback.fst G₂.hom (jK R₂) ≫ β = q ≫ α₁ ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) := by
  first | exact @GlobalTheory.Mum.transport_extLam | exact GlobalTheory.Mum.transport_extLam | (intros; apply GlobalTheory.Mum.transport_extLam <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.two_smul_polarisation_class_generic_diagonal_doubling : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∀ (c : GlobalTheory.CechPic.Pic (pullback G.hom (jK R))) (d : GlobalTheory.CechPic.Pic G.left) (hL : (A.L.pull gen.hom.left).IsLB) (hP : (PP.pull (lift (𝟙 G) (𝟙 G) : G ⟶ G2 G).left).IsLB), c = GlobalTheory.CechPic.cls (A.L.pull gen.hom.left) hL → d = GlobalTheory.CechPic.cls (PP.pull (lift (𝟙 G) (𝟙 G) : G ⟶ G2 G).left) hP → 2 • c = GlobalTheory.CechPic.pull (pullback.fst G.hom (jK R)) d ∧ ∃ φ : pullback G.hom (jK R) ⟶ pullback G.hom (jK R), φ ≫ pullback.fst G.hom (jK R) = pullback.fst G.hom (jK R) ≫ ((𝟙 G) ^ 2 : G ⟶ G).left ∧ GlobalTheory.CechPic.pull φ c = 4 • c := by
  first | exact @GlobalTheory.Mum.two_smul_cls_eq_pull_diag_and_pull_sq | exact GlobalTheory.Mum.two_smul_cls_eq_pull_diag_and_pull_sq | (intros; apply GlobalTheory.Mum.two_smul_cls_eq_pull_diag_and_pull_sq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_adjointEndomorphisms_action_uniformisedThickenings : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∃ b, FormalEnd U.toUnifPre a h' b := by
  first | exact @GlobalTheory.Mum.EndThick.formalEnd_exists | exact GlobalTheory.Mum.EndThick.formalEnd_exists | (intros; apply GlobalTheory.Mum.EndThick.formalEnd_exists <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegZar
open GlobalTheory.SiegPBDescent

theorem comp_eq_of_pair : ∀ (h n : ℕ) (B B' B₁ B₂ : Type) [CommRing B] [CommRing B'] [CommRing B₁] [CommRing B₂] (b : TBase B n) (ζ' : B') (ζ₁ : B₁) (ζ₂ : B₂) (T T₁ T₂ : Scheme.{0}) (sc : T ⟶ Sp B') (su : T ⟶ Sp B) (s₁ : T₁ ⟶ Sp B₁) (s₂ : T₂ ⟶ Sp B₂) (c : SiegPre h n ζ' sc) (u : SiegPre h n (b.ζ : B) su) (c₁ : SiegPre h n ζ₁ s₁) (c₂ : SiegPre h n ζ₂ s₂) (p₁ : T₁ ⟶ T) (p₂ : T₂ ⟶ T) (φ₁ : c₁.A.left ⟶ c.A.left) (ψ₁ : c₁.A.left ⟶ u.A.left) (φ₂ : c₂.A.left ⟶ c.A.left) (ψ₂ : c₂.A.left ⟶ u.A.left), 3 ≤ n → Odd n → u.Principal → SRelBy c₁ c 1 1 p₁ φ₁ → SRelBy c₁ u 1 1 p₁ ψ₁ → SRelBy c₂ c 1 1 p₂ φ₂ → SRelBy c₂ u 1 1 p₂ ψ₂ → ∀ (Z : Scheme.{0}) (g₁ : Z ⟶ c₁.A.left) (g₂ : Z ⟶ c₂.A.left), g₁ ≫ φ₁ = g₂ ≫ φ₂ → g₁ ≫ ψ₁ = g₂ ≫ ψ₂ := by
  intro h n B B' B₁ B₂ _ _ _ _ b ζ' ζ₁ ζ₂ T T₁ T₂ sc su s₁ s₂ c u c₁ c₂ p₁ p₂ φ₁ ψ₁ φ₂ ψ₂ hn ho hu m₁ k₁ m₂ k₂ Z g₁ g₂ e
  obtain ⟨-, hφ₁, -⟩ := (sRelBy_one_iff _ _ _ _).1 m₁
  obtain ⟨-, hφ₂, -⟩ := (sRelBy_one_iff _ _ _ _).1 m₂
  have hz : (g₁ ≫ c₁.A.hom) ≫ p₁ = (g₂ ≫ c₂.A.hom) ≫ p₂ := by
    rw [Category.assoc, Category.assoc, ← hφ₁.1.w, ← hφ₂.1.w, reassoc_of% e]
  obtain ⟨⟨o, ho'⟩, -⟩ := GlobalTheory.siegPre_pullback h n B₁ ζ₁ T₁ Z s₁ ((g₁ ≫ c₁.A.hom) ≫ s₁) (g₁ ≫ c₁.A.hom) c₁ rfl
  obtain ⟨κ, hκ⟩ := exists_of_siegPB ho'
  have a₁ := comp_by m₁ hκ
  rw [hz] at a₁
  obtain ⟨κ', hκ', hκ'b⟩ := cancel_by m₂ a₁
  have n₁ := comp_by k₁ hκ
  have n₂ := comp_by k₂ hκ'b
  rw [← hz] at n₂
  have r := GlobalTheory.SiegRigid.eq_of_sRelBy h n n 1 B B₁ b ζ₁ T Z su _ u o _ _ _ hn ho hu n₁ n₂
  obtain ⟨-, hκg, -⟩ := (sRelBy_one_iff _ _ _ _).1 hκ
  obtain ⟨-, hκ'g, -⟩ := (sRelBy_one_iff _ _ _ _).1 hκ'b
  have hl : g₁ ≫ c₁.A.hom = 𝟙 Z ≫ g₁ ≫ c₁.A.hom := (Category.id_comp _).symm
  have h₁ : hκg.1.lift g₁ (𝟙 Z) hl ≫ κ = g₁ := hκg.1.lift_fst _ _ _
  have h₀ : hκg.1.lift g₁ (𝟙 Z) hl ≫ o.A.hom = 𝟙 Z := hκg.1.lift_snd _ _ _
  have h₂ : hκg.1.lift g₁ (𝟙 Z) hl ≫ κ' = g₂ := by
    apply hφ₂.1.hom_ext
    · rw [Category.assoc, hκ', ← Category.assoc, h₁, e]
    · rw [Category.assoc, hκ'g.1.w, ← Category.assoc, h₀, Category.id_comp]
  calc g₁ ≫ ψ₁ = hκg.1.lift g₁ (𝟙 Z) hl ≫ κ ≫ ψ₁ := by rw [← Category.assoc, h₁]
    _ = hκg.1.lift g₁ (𝟙 Z) hl ≫ κ' ≫ ψ₂ := by rw [r]
    _ = g₂ ≫ ψ₂ := by rw [← Category.assoc, h₂]

end GlobalTheory.SiegZar

namespace GlobalTheory.SiegZar
open GlobalTheory.SiegPBDescent

theorem isPullback_of_sRelBy {h n : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} {S S' : Scheme.{0}}
    {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {c' : SiegPre h n ζ' s'} {c : SiegPre h n ζ s} {f : S' ⟶ S}
    {φ : c'.A.left ⟶ c.A.left} (m : SRelBy c' c 1 1 f φ) : IsPullback φ c'.A.hom c.A.hom f :=
  ((sRelBy_one_iff _ _ _ _).1 m).choose_spec.1.1

theorem iso_of_local : ∀ (g n : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (b : TBase B n) (ζ' : B') (S : Scheme.{0}) (sc : S ⟶ Sp B') (su : S ⟶ Sp B) (c : SiegPre g n ζ' sc) (u : SiegPre g n (b.ζ : B) su), 3 ≤ n → Odd n → u.Principal → (∀ x : S, ∃ (V : Scheme.{0}) (j : V ⟶ S) (cV : SiegPre g n ζ' (j ≫ sc)), IsOpenImmersion j ∧ x ∈ Set.range j ∧ SiegPB cV c j ∧ SiegPB cV u j) → ∃ φ : c.A.left ⟶ u.A.left, IsIso φ ∧ φ ≫ u.A.hom = c.A.hom ∧ ∀ x : S, ∃ (V : Scheme.{0}) (j : V ⟶ S) (cV : SiegPre g n ζ' (j ≫ sc)) (φV : cV.A.left ⟶ c.A.left), IsOpenImmersion j ∧ x ∈ Set.range j ∧ SRelBy cV c 1 1 j φV ∧ SRelBy cV u 1 1 j (φV ≫ φ) := by
  intro g n B B' _ _ b ζ' S sc su c u hn ho hu hloc
  choose V j cV hj hx m k using hloc
  choose φV hm using fun x => exists_of_siegPB (m x)
  choose ψV hk using fun x => exists_of_siegPB (k x)
  have pφ : ∀ x, IsPullback (φV x) (cV x).A.hom c.A.hom (j x) := fun x => isPullback_of_sRelBy (hm x)
  have pψ : ∀ x, IsPullback (ψV x) (cV x).A.hom u.A.hom (j x) := fun x => isPullback_of_sRelBy (hk x)
  have oφ : ∀ x, IsOpenImmersion (φV x) := fun x => MorphismProperty.of_isPullback (pφ x).flip (hj x)
  have oψ : ∀ x, IsOpenImmersion (ψV x) := fun x => MorphismProperty.of_isPullback (pψ x).flip (hj x)
  let 𝒰 : c.A.left.OpenCover := Scheme.Cover.mkOfCovers S (fun x => (cV x).A.left) φV
    (fun a => ⟨c.A.hom a, (GlobalTheory.GrpLoc.range_of_isPullback (pφ (c.A.hom a)) a).2 (hx _)⟩) oφ
  let 𝒰' : u.A.left.OpenCover := Scheme.Cover.mkOfCovers S (fun x => (cV x).A.left) ψV
    (fun a => ⟨u.A.hom a, (GlobalTheory.GrpLoc.range_of_isPullback (pψ (u.A.hom a)) a).2 (hx _)⟩) oψ
  have pair := fun x y => comp_eq_of_pair g n B B' B' B' b ζ' ζ' ζ' S (V x) (V y) sc su (j x ≫ sc) (j y ≫ sc) c u
    (cV x) (cV y) (j x) (j y) (φV x) (ψV x) (φV y) (ψV y) hn ho hu (hm x) (hk x) (hm y) (hk y)
  have compat : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ ψV x = pullback.snd (𝒰.f x) (𝒰.f y) ≫ ψV y :=
    fun x y => pair x y _ _ _ pullback.condition
  let φ := 𝒰.glueMorphisms ψV compat
  have hφ : ∀ x, φV x ≫ φ = ψV x := fun x => 𝒰.ι_glueMorphisms ψV compat x
  have hw : φ ≫ u.A.hom = c.A.hom := by
    refine 𝒰.hom_ext _ _ fun x => ?_
    show φV x ≫ φ ≫ u.A.hom = φV x ≫ c.A.hom
    rw [reassoc_of% (hφ x), (pψ x).w, (pφ x).w]
  have key : ∀ x y (Z : Scheme.{0}) (g₁ : Z ⟶ (cV x).A.left) (g₂ : Z ⟶ (cV y).A.left),
      g₁ ≫ ψV x = g₂ ≫ ψV y → g₁ ≫ φV x = g₂ ≫ φV y := by
    intro x y Z g₁ g₂ e
    have e₁ : (g₁ ≫ φV x) ≫ c.A.hom = (g₂ ≫ (cV y).A.hom) ≫ j y := by
      calc (g₁ ≫ φV x) ≫ c.A.hom = g₁ ≫ φV x ≫ φ ≫ u.A.hom := by rw [hw, Category.assoc]
        _ = g₁ ≫ ψV x ≫ u.A.hom := by rw [reassoc_of% (hφ x)]
        _ = g₂ ≫ ψV y ≫ u.A.hom := by rw [reassoc_of% e]
        _ = _ := by rw [(pψ y).w, Category.assoc]
    let t := (pφ y).lift (g₁ ≫ φV x) (g₂ ≫ (cV y).A.hom) e₁
    have t₁ : t ≫ φV y = g₁ ≫ φV x := (pφ y).lift_fst _ _ _
    have t₂ : t ≫ (cV y).A.hom = g₂ ≫ (cV y).A.hom := (pφ y).lift_snd _ _ _
    have t₃ : t ≫ ψV y = g₁ ≫ ψV x := pair y x _ t g₁ t₁
    have tg : t = g₂ := (pψ y).hom_ext (t₃.trans e) t₂
    rw [← t₁, tg]
  have compat' : ∀ x y, pullback.fst (𝒰'.f x) (𝒰'.f y) ≫ φV x = pullback.snd (𝒰'.f x) (𝒰'.f y) ≫ φV y :=
    fun x y => key x y _ _ _ pullback.condition
  let ψ := 𝒰'.glueMorphisms φV compat'
  have hψ : ∀ x, ψV x ≫ ψ = φV x := fun x => 𝒰'.ι_glueMorphisms φV compat' x
  have i₁ : φ ≫ ψ = 𝟙 _ := 𝒰.hom_ext _ _ fun x => by
    show φV x ≫ φ ≫ ψ = φV x ≫ 𝟙 _
    rw [reassoc_of% (hφ x), hψ x, Category.comp_id]
  have i₂ : ψ ≫ φ = 𝟙 _ := 𝒰'.hom_ext _ _ fun x => by
    show ψV x ≫ ψ ≫ φ = ψV x ≫ 𝟙 _
    rw [reassoc_of% (hψ x), hφ x, Category.comp_id]
  exact ⟨φ, ⟨ψ, i₁, i₂⟩, hw, fun x => ⟨V x, j x, cV x, φV x, hj x, hx x, hm x, by rw [hφ x]; exact hk x⟩⟩

end GlobalTheory.SiegZar

namespace GlobalTheory.SiegZar
open GlobalTheory.SiegPBDescent

theorem siegPB_id_of_local : ∀ (g n : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (S : Scheme.{0}) (sc : S ⟶ Sp B') (su : S ⟶ Sp B) (c : SiegPre g n ζ' sc) (u : SiegPre g n ζ su) (φ : c.A.left ⟶ u.A.left), IsIso φ → φ ≫ u.A.hom = c.A.hom → (∀ x : S, ∃ (V : Scheme.{0}) (j : V ⟶ S) (cV : SiegPre g n ζ' (j ≫ sc)) (φV : cV.A.left ⟶ c.A.left), IsOpenImmersion j ∧ x ∈ Set.range j ∧ SRelBy cV c 1 1 j φV ∧ SRelBy cV u 1 1 j (φV ≫ φ)) → SiegPB c u (𝟙 S) := by
  intro g n B B' _ _ ζ ζ' S sc su c u φ hi hw hloc
  have gp : IsGrpPullback c.A u.A (𝟙 S) φ := GlobalTheory.GrpLoc.isGrpPullback_local_on_base S c.A u.A φ hi hw fun p => by
    obtain ⟨V, j, cV, φV, hj, hx, m, k⟩ := hloc p
    exact ⟨V, j, cV.A, inferInstance, φV, hj, hx, ((sRelBy_one_iff _ _ _ _).1 m).choose_spec.1,
      ((sRelBy_one_iff _ _ _ _).1 k).choose_spec.1⟩
  obtain ⟨φ₂, sq⟩ := GlobalTheory.SiegDesc.exists_isSquare gp.1.w
  have lev : ∀ a, (c.lev a).left ≫ φ = 𝟙 S ≫ (u.lev a).left := fun a => by
    refine GlobalTheory.GrpLoc.hom_ext_loc fun p => ?_
    obtain ⟨V, j, cV, φV, hj, hx, m, k⟩ := hloc p
    obtain ⟨-, -, -, -, lm⟩ := (sRelBy_one_iff _ _ _ _).1 m
    obtain ⟨-, -, -, -, lk⟩ := (sRelBy_one_iff _ _ _ _).1 k
    refine ⟨V, j, hj, hx, ?_⟩
    rw [Category.id_comp, ← reassoc_of% (lm a), ← lk a]
  have gp₂ : IsGrpPullback (G2 c.A) (G2 u.A) (𝟙 S) φ₂ := GlobalTheory.ShearLift.isGrpPullback_tensor gp gp sq.1 sq.2
  have rig (d : SiegPre g n ζ' sc) : Out.Rigidified (G2 d.A) d.P := by
    have he : eSec d.A ≫ (lift (1 : d.A ⟶ d.A) (𝟙 d.A)).left = eSec (G2 d.A) := by
      unfold eSec
      rw [← Over.comp_left]
      congr 1
      ext <;> simp [Hom.one_def]
    have z := (CechPic.cls_eq_zero_iff (pull_isLB d.isLB _)).2 d.rig₁
    rw [CechPic.cls_pull d.isLB] at z
    apply (CechPic.cls_eq_zero_iff (pull_isLB d.isLB _)).1
    rw [CechPic.cls_pull d.isLB, ← he, CechPic.pull_comp, z, map_zero]
  have rL : Out.Rigidified (G2 c.A) c.P := rig c
  have rL' : Out.Rigidified (G2 u.A) u.P := by
    have he : eSec u.A ≫ (lift (1 : u.A ⟶ u.A) (𝟙 u.A)).left = eSec (G2 u.A) := by
      unfold eSec
      rw [← Over.comp_left]
      congr 1
      ext <;> simp [Hom.one_def]
    have z := (CechPic.cls_eq_zero_iff (pull_isLB u.isLB _)).2 u.rig₁
    rw [CechPic.cls_pull u.isLB] at z
    apply (CechPic.cls_eq_zero_iff (pull_isLB u.isLB _)).1
    rw [CechPic.cls_pull u.isLB, ← he, CechPic.pull_comp, z, map_zero]
  have hiso : LBIso c.P (u.P.pull φ₂) :=
    GlobalTheory.RigidLocal.lbIso_of_local GlobalTheory.abelianSchemeLaws_all.1.globalFns S (G2 c.A) (G2 u.A) c.P u.P φ₂
      (AbelianSchemeGerms.isAbelianScheme_tensor _ _ c.ab c.ab) c.isLB u.isLB rL rL' gp₂ fun p => by
        obtain ⟨V, j, cV, φV, hj, hx, m, k⟩ := hloc p
        obtain ⟨φV₂, gm, sm, im, -⟩ := (sRelBy_one_iff _ _ _ _).1 m
        obtain ⟨ψV₂, -, sk, ik, -⟩ := (sRelBy_one_iff _ _ _ _).1 k
        have e₂ : φV₂ ≫ φ₂ = ψV₂ := GlobalTheory.SiegDesc.isSquare_comp rfl sm sq sk
        refine ⟨V, (G2 cV.A).left, j, (G2 cV.A).hom, φV₂, hj, hx, GlobalTheory.SiegDesc.isPullback_of_isSquare gm.1 sm, ?_⟩
        rw [e₂]
        exact im.symm.trans (pull_isLB c.isLB _) cV.isLB (pull_isLB u.isLB _) ik
  exact ⟨φ, φ₂, gp, sq, hiso, lev⟩

end GlobalTheory.SiegZar

namespace GlobalTheory.SiegZar
open GlobalTheory.SiegelPullComp

theorem glue_classifying : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (cycAway n)) (c : SiegPre g n (zetaAway n) s'), (∀ x : S, ∃ (V : Scheme.{0}) (j : V ⟶ S) (cV : SiegPre g n (zetaAway n) (j ≫ s')), IsOpenImmersion j ∧ x ∈ Set.range j ∧ SiegPB cV c j ∧ ∃ f : V ⟶ F.X, f ≫ F.s = j ≫ s' ∧ SiegPB cV F.univ f) → ∃ f : S ⟶ F.X, f ≫ F.s = s' ∧ ∀ x : S, ∃ (V : Scheme.{0}) (j : V ⟶ S) (cV : SiegPre g n (zetaAway n) (j ≫ s')), IsOpenImmersion j ∧ x ∈ Set.range j ∧ SiegPB cV c j ∧ SiegPB cV F.univ (j ≫ f) := by
  intro g n hg hn ho F S s' c hloc
  choose V j cV hj hx m f hfs hpb using hloc
  let 𝒰 : S.OpenCover := Scheme.Cover.mkOfCovers S V j (fun x => ⟨x, hx x⟩) hj
  have key : ∀ x y, pullback.fst (j x) (j y) ≫ f x = pullback.snd (j x) (j y) ≫ f y := by
    intro x y
    obtain ⟨⟨cP, hcP⟩, -⟩ := GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) S (pullback (j x) (j y)) s'
      (pullback.fst (j x) (j y) ≫ j x ≫ s') (pullback.fst (j x) (j y) ≫ j x) c (Category.assoc _ _ _)
    have hcP' : SiegPB cP c (pullback.snd (j x) (j y) ≫ j y) := by rw [← pullback.condition]; exact hcP
    have h₁ := pb_comp (hpb x) (pb_cancel (m x) hcP)
    have h₂ := pb_comp (hpb y) (pb_cancel (m y) hcP')
    refine GlobalTheory.SiegUniq.eq_of_siegPB g n hg hn ho F _ _ cP _ _ ?_ ?_ h₁ h₂
    · rw [Category.assoc, hfs x]
    · rw [Category.assoc, hfs y, pullback.condition_assoc]
  let φ := 𝒰.glueMorphisms f key
  have hφ : ∀ x, j x ≫ φ = f x := fun x => 𝒰.ι_glueMorphisms f key x
  refine ⟨φ, 𝒰.hom_ext _ _ fun x => ?_, fun x => ⟨V x, j x, cV x, hj x, hx x, m x, by rw [hφ x]; exact hpb x⟩⟩
  show j x ≫ φ ≫ F.s = j x ≫ s'
  rw [reassoc_of% (hφ x), hfs x]

end GlobalTheory.SiegZar

namespace GlobalTheory.SiegZar
open GlobalTheory.SiegelPullComp

theorem classified_of_local : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (cycAway n)) (c : SiegPre g n (zetaAway n) s'), c.Principal → (∀ x : S, ∃ (V : Scheme.{0}) (j : V ⟶ S) (cV : SiegPre g n (zetaAway n) (j ≫ s')), IsOpenImmersion j ∧ x ∈ Set.range j ∧ SiegPB cV c j ∧ ∃ f : V ⟶ F.X, f ≫ F.s = j ≫ s' ∧ SiegPB cV F.univ f) → ∃ f : S ⟶ F.X, f ≫ F.s = s' ∧ SiegPB c F.univ f := by
  intro g n hg hn ho F S s' c _ hloc
  obtain ⟨f, hf, hl⟩ := glue_classifying g n hg hn ho F S s' c hloc
  have hn0 : n ≠ 0 := by omega
  obtain ⟨⟨u, hu⟩, hpr⟩ := GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) F.X S F.s (f ≫ F.s) f F.univ rfl
  have hup : u.Principal := hpr u hu F.princ
  obtain ⟨φ, hi, hw, hφ⟩ := iso_of_local g n (cycAway n) (cycAway n) (cycBase hn0) (zetaAway n) S s' (f ≫ F.s) c u
    hn ho hup fun x => by
      obtain ⟨V, j, cV, hj, hx, h₁, h₂⟩ := hl x
      exact ⟨V, j, cV, hj, hx, h₁, pb_cancel hu h₂⟩
  have e := pb_comp hu (siegPB_id_of_local g n (cycAway n) (cycAway n) _ (zetaAway n) S s' (f ≫ F.s) c u φ hi hw hφ)
  rw [Category.id_comp] at e
  exact ⟨f, hf, e⟩

end GlobalTheory.SiegZar
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.exists_open_theta_descent : ∀ (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), Surjective π → ∀ (G' : Over S) [GrpObj G'] (E : Emb π G') (N : Near π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → ∀ (L : LB G'.left), E.Theta L → ∀ (G : Over (Sp R)) (β : G'.left ⟶ G.left) (i : N.U ⟶ G), β ≫ G.hom = G'.hom ≫ π → IsOpenImmersion i.left → N.u ≫ β = pullback.fst _ _ ≫ i.left → ∃ (θ : L.Sec) (O : G.left.Opens), (∃ g ∈ O, G.hom g = closedPoint R) ∧ ∀ g : G'.left, β g ∈ O → G.hom (β g) = closedPoint R → ∃ k, g ∈ G'.left.basicOpen (θ.f k) := by
  intro R _ _ S π hπ G' _ E N fU l hl hlf L hT G β i hβ hi hu
  obtain ⟨θ, OY, ⟨y₀, hy₀⟩, hθ⟩ := hT
  haveI := E.imm
  obtain ⟨W, hW, hWY⟩ := (E.j.isEmbedding.isInducing.isOpen_iff).1 OY.isOpen
  have hrng := GlobalTheory.T.closedPoint_range_eq_fixedGroup_image R S π G' E
  have e1 : ∀ z, E.H.ι (l z) = N.u z := fun z => by rw [← Scheme.Hom.comp_apply, hl]
  have e2 : ∀ z, E.f (l z) = fU (pullback.fst N.U.hom π z) := fun z => by
    rw [← Scheme.Hom.comp_apply, hlf, Scheme.Hom.comp_apply]
  have e3 : ∀ z, β (N.u z) = i.left (pullback.fst N.U.hom π z) := fun z => by
    rw [← Scheme.Hom.comp_apply, hu, Scheme.Hom.comp_apply]
  have e4 : ∀ x, G.hom (β x) = π (G'.hom x) := fun x => by
    rw [← Scheme.Hom.comp_apply, hβ, Scheme.Hom.comp_apply]
  have hWj : ∀ y, y ∈ OY ↔ E.j y ∈ W := fun y => by
    show y ∈ (OY : Set E.Y.left) ↔ _
    rw [← hWY]; rfl
  refine ⟨θ, ⟨i.left '' (fU ⁻¹' W), i.left.isOpenEmbedding.isOpenMap _ (hW.preimage fU.continuous)⟩, ?_, ?_⟩
  · obtain ⟨g₀, hg₀c, hg₀f⟩ := hrng.2 hπ y₀
    obtain ⟨z, hz⟩ := N.all (E.H.ι g₀) hg₀c
    have hlz : l z = g₀ := E.H.ι.isOpenEmbedding.injective (by rw [e1, hz])
    refine ⟨i.left (pullback.fst N.U.hom π z), ⟨pullback.fst N.U.hom π z, ?_, rfl⟩, ?_⟩
    · show fU (pullback.fst N.U.hom π z) ∈ W
      rw [← e2 z, hlz, hg₀f]
      exact (hWj y₀).1 hy₀
    · rw [← e3, e4, hz]
      exact hg₀c
  · rintro g ⟨w, hw, hwg⟩ hc
    have hc' : π (G'.hom g) = closedPoint R := by rw [← e4]; exact hc
    obtain ⟨z, rfl⟩ := N.all g hc'
    have hzw : pullback.fst N.U.hom π z = w := i.left.isOpenEmbedding.injective (by rw [hwg, ← e3])
    have hc'' : π (G'.hom (E.H.ι (l z))) = closedPoint R := by rw [e1]; exact hc'
    obtain ⟨y, hy⟩ := hrng.1 (l z) hc''
    have hyO : y ∈ OY := (hWj y).2 (by rw [← hy, e2, hzw]; exact hw)
    obtain ⟨k, hk⟩ := hθ (l z) y hyO hc'' hy
    exact ⟨k, by rwa [e1] at hk⟩
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.homogeneousForm_chart_change_coeff_ideal_pow : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (e d : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous d → (∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) → ∀ i j, C.ev e i F ∈ towerIdeal Y e (I ^ e) (C.D e i) ∧ C.ρ e i i * C.ev e i F = C.ev e i F ∧ rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ev e i F) = rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ d * rs (Y e).left (inf_le_right : C.D e i ⊓ C.D e j ≤ C.D e j) (C.ev e j F) := by
  first | exact @GlobalTheory.FormalAlg.Charts.ev_change | exact GlobalTheory.FormalAlg.Charts.ev_change | (intros; apply GlobalTheory.FormalAlg.Charts.ev_change <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.exists_chart_cocycle_of_pullback_power_standard : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (H₀ : LB (Y 0).left) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → ((∀ i, C.D 0 i = nonzeroLocus (s₀ i)) ∧ ∀ i j (m : H₀.ι), rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ j).f m) = rs (Y 0).left (inf_le_left : C.D 0 i ⊓ H₀.U m ≤ C.D 0 i) (C.ρ 0 i j) * rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ i).f m)) → ∀ γ : ∀ e, (Y 0).left ⟶ (Y e).left, γ 0 = 𝟙 _ → (∀ e, γ e ≫ β e = γ (e + 1)) → ∀ (e k : ℕ) (L : LB (Y e).left), L.IsLB → LBIso (L.pull (γ e)) (GlobalTheory.AbLaw.pw H₀ k) → ∃ g : ∀ i j, Γ((Y e).left, C.D e i ⊓ C.D e j)ˣ, (⟨Fin (n + 1), C.D e, g⟩ : LB (Y e).left).IsLB ∧ LBIso L ⟨Fin (n + 1), C.D e, g⟩ ∧ ∀ i j, (g i j).val - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k ∈ towerIdeal Y e I (C.D e i ⊓ C.D e j) := by
  first | exact @GlobalTheory.FormalAlg.exists_chart_cocycle_of_pull | exact GlobalTheory.FormalAlg.exists_chart_cocycle_of_pull | (intros; apply GlobalTheory.FormalAlg.exists_chart_cocycle_of_pull <;> assumption)
end
