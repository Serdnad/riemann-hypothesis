module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2779
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle582
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2791
public import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2674
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2794
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenRelNeZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2861
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle189
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelStructureOfWeilPairing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2809
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCpLinComb
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2810
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.DescHom

theorem ext_of_open {T : Scheme.{0}} {W X Y : Over T} (j : W ⟶ X) [IsOpenImmersion j.left] [Surjective W.hom]
    [Smooth X.hom] [GeometricallyIrreducible X.hom] [IsSeparated Y.hom] {f g : X ⟶ Y} (h : j ≫ f = j ≫ g) : f = g := by
  have hfib : ∀ x : X.left, x ∈ closure ((j.left.opensRange : Set X.left) ∩ X.hom ⁻¹' {X.hom x}) := by
    intro x
    have hirr : IsIrreducible (X.hom ⁻¹' {X.hom x}) :=
      X.hom.isIrreducible_preimage X.hom.isOpenMap isIrreducible_singleton
    obtain ⟨w, hw⟩ := W.hom.surjective (X.hom x)
    have hne : (X.hom ⁻¹' {X.hom x} ∩ (j.left.opensRange : Set X.left)).Nonempty := by
      refine ⟨j.left w, ?_, ⟨w, rfl⟩⟩
      show X.hom (j.left w) = X.hom x
      rw [← Scheme.Hom.comp_apply, Over.w]
      exact hw
    have hsub := subset_closure_inter_of_isPreirreducible_of_isOpen hirr.isPreirreducible
      j.left.opensRange.isOpen hne (show x ∈ X.hom ⁻¹' {X.hom x} from rfl)
    rwa [Set.inter_comm] at hsub
  have hl : j.left ≫ f.left = j.left ≫ g.left := by
    simpa only [Over.comp_left] using congrArg CommaMorphism.left h
  apply Over.OverMorphism.ext
  refine GlobalTheory.FibreDense.main X.left T Y.left X.hom Y.hom j.left.opensRange hfib f.left g.left
    (by rw [Over.w f, Over.w g]) ?_
  rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, Category.assoc, hl]

theorem isMonHom_of_open {T : Scheme.{0}} {W X Y : Over T} [GrpObj X] [GrpObj Y] (j : W ⟶ X) [IsOpenImmersion j.left]
    [Surjective W.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom] [IsSeparated Y.hom] (φ : X ⟶ Y)
    (h : ((fst W W ≫ j) * (snd W W ≫ j)) ≫ φ = (fst W W ≫ j ≫ φ) * (snd W W ≫ j ≫ φ)) : IsMonHom φ := by
  have hmuX : (μ : X ⊗ X ⟶ X) = fst X X * snd X X := by
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  have hmuY : (μ : Y ⊗ Y ⟶ Y) = fst Y Y * snd Y Y := by
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  have hoi : IsOpenImmersion (j ⊗ₘ j).left := by
    rw [Over.tensorHom_left]
    exact MorphismProperty.pullbackMap (P := @IsOpenImmersion) ‹_› ‹_› (by simp) (by simp)
  have hsurj : Surjective (W ⊗ W).hom := by
    rw [Over.tensorObj_hom]; infer_instance
  have hsm : Smooth (X ⊗ X).hom := by
    rw [Over.tensorObj_hom]; infer_instance
  have hgi : GeometricallyIrreducible (X ⊗ X).hom := by
    rw [Over.tensorObj_hom]
    exact GeometricallyIrreducible.comp _ _
  have hmul : μ ≫ φ = (φ ⊗ₘ φ) ≫ μ := by
    apply ext_of_open (j ⊗ₘ j)
    have lhs : (j ⊗ₘ j) ≫ μ ≫ φ = ((fst W W ≫ j) * (snd W W ≫ j)) ≫ φ := by
      rw [hmuX, ← Category.assoc, MonObj.comp_mul, tensorHom_fst, tensorHom_snd]
    have rhs : (j ⊗ₘ j) ≫ (φ ⊗ₘ φ) ≫ μ = (fst W W ≫ j ≫ φ) * (snd W W ≫ j ≫ φ) := by
      rw [hmuY, MonObj.comp_mul, tensorHom_fst, tensorHom_snd, MonObj.comp_mul, tensorHom_fst_assoc,
        tensorHom_snd_assoc]
    rw [lhs, rhs, h]
  have hcomp : ∀ {Z : Over T} (a b : Z ⟶ X), (a * b) ≫ φ = (a ≫ φ) * (b ≫ φ) := by
    intro Z a b
    rw [Hom.mul_def, Hom.mul_def, Category.assoc, hmul, ← Category.assoc, lift_map]
  have hone : η ≫ φ = η := by
    have h1 : ((1 : 𝟙_ (Over T) ⟶ X) ≫ φ) * ((1 : 𝟙_ (Over T) ⟶ X) ≫ φ) = (1 : 𝟙_ (Over T) ⟶ X) ≫ φ := by
      rw [← hcomp, _root_.mul_one]
    have h2 : (1 : 𝟙_ (Over T) ⟶ X) ≫ φ = 1 := _root_.mul_eq_left.mp h1
    have e1 : ∀ {M : Over T} [MonObj M], (1 : 𝟙_ (Over T) ⟶ M) = η := by
      intro M _
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    rw [← e1, ← e1]
    exact h2
  exact ⟨hone, hmul⟩

theorem geometricallyIrreducible_of_semiAbelian {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) :
    GeometricallyIrreducible G.hom := by
  obtain ⟨_, hsm, _, _, hgc, _⟩ := hG
  have := GlobalTheory.grpObj_geometricallyIntegral_of_smooth S G
  infer_instance

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

theorem surjective_near [GrpObj G] [Surjective π] (N : Near π G) : Surjective N.U.hom := by
  have := N.smooth
  have hcl : closedPoint R ∈ Set.range N.U.hom := by
    obtain ⟨s, hs⟩ := π.surjective (closedPoint R)
    have he : (η[G] : 𝟙_ (Over S) ⟶ G).left ≫ G.hom = 𝟙 S := Over.w η[G]
    have hGs : G.hom ((η[G] : 𝟙_ (Over S) ⟶ G).left s) = s := by
      rw [← Scheme.Hom.comp_apply, he]; rfl
    obtain ⟨y, hy⟩ := N.all _ (by rw [hGs, hs])
    refine ⟨pullback.fst N.U.hom π y, ?_⟩
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, ← N.u_over,
      Scheme.Hom.comp_apply, hy, hGs, hs]
  exact ⟨fun x => (Flat.generalizingMap N.U.hom).stableUnderGeneralization_range
    (specializes_closedPoint x) hcl⟩

theorem isPullback_embL (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    IsPullback (Desc.toS N p hp) (Desc.embL N p hp) N.u (pullback.fst G.hom p) := by
  have hA : IsPullback (Desc.toS N p hp) (pullback.snd N.U.hom (pullback.fst π π ≫ π))
      (pullback.snd N.U.hom π) p := by
    have outer : IsPullback (Desc.toS N p hp ≫ pullback.fst N.U.hom π)
        (pullback.snd N.U.hom (pullback.fst π π ≫ π)) N.U.hom (p ≫ π) := by
      rw [Desc.toS, pullback.lift_fst, hp]
      exact IsPullback.of_hasPullback _ _
    exact IsPullback.of_right outer (by rw [Desc.toS, pullback.lift_snd]) (IsPullback.of_hasPullback _ _)
  refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback G.hom p)
  · rw [Desc.embL, pullback.lift_snd, N.u_over]
    exact hA
  · rw [Desc.embL, pullback.lift_fst]

theorem isOpenImmersion_emb (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    IsOpenImmersion (Desc.emb N p hp).left := by
  have := N.isOpen
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_embL N p hp) N.isOpen

theorem isMonHom_of_sum_of_emb : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', ∀ (p p' : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) (hp' : p' ≫ π = pullback.fst π π ≫ π), ∀ φ : (Over.pullback p).obj G' ⟶ (Over.pullback p').obj G', Desc.sum N p hp ≫ φ = Desc.sum N p' hp' → Desc.emb N p hp ≫ φ = Desc.emb N p' hp' → IsMonHom φ := by
  intro R _ _ _ _ S π _ _ _ G' _ _ hG N p p' hp hp' φ hsum hemb
  have : Surjective N.U.hom := surjective_near N
  have : GeometricallyIrreducible G'.hom := geometricallyIrreducible_of_semiAbelian G' hG
  obtain ⟨_, hsm, hsep, _, _, _⟩ := hG
  have : IsOpenImmersion (Desc.emb N p hp).left := isOpenImmersion_emb N p hp
  have : Surjective (Desc.UT N).hom := by
    show Surjective (pullback.snd N.U.hom (pullback.fst π π ≫ π)); infer_instance
  have : Smooth ((Over.pullback p).obj G').hom := by
    show Smooth (pullback.snd G'.hom p); infer_instance
  have : GeometricallyIrreducible ((Over.pullback p).obj G').hom := by
    show GeometricallyIrreducible (pullback.snd G'.hom p); infer_instance
  have : IsSeparated ((Over.pullback p').obj G').hom := by
    show IsSeparated (pullback.snd G'.hom p'); infer_instance
  refine isMonHom_of_open (Desc.emb N p hp) φ ?_
  change Desc.sum N p hp ≫ φ = _
  rw [hsum, Desc.sum, ← hemb]

end GlobalTheory.Mum.DescHom
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.TestAtPt

theorem norm_psi_coord : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left) (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (ev : R →+* OO p) (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev u ε → ∀ (l : u.Lab) α s, PsiCoord D.toPre α s → ‖(ev s : PadicAlgCl p)‖ = Real.exp (-l.q (ε α)) := by
  intro o' Ω _ _ _ S ρ M U₀ EE FinalForm R _ _ _ G _ _ gm D A U p _ y₀ ev u ε hBC l α s hs
  obtain ⟨ev₀, _, hD, bc, -, -, hx, hev, -⟩ := hBC
  have hs' : PsiCoord D.toPre (hD.xe (ε α)) s := by rw [hx]; exact hs
  obtain ⟨w, hw⟩ := GlobalTheory.PelCoordPull.psiCoord_pull hD (ε α) s hs'
  obtain ⟨j, hj, hv⟩ := GlobalTheory.Poinc.valF_psi_of_psiCoord u.V u.D.toPre (ε α) _ hw
  have hq := l.q_eq (ε α) j hj
  rw [hv] at hq
  have unit_norm : ∀ v : u.Vˣ, ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) (v : u.V))‖ = 1 := by
    intro v
    have h1 := (u.norm_le _).2 ⟨(v : u.V), rfl⟩
    have h2 := (u.norm_le _).2 ⟨((v⁻¹ : u.Vˣ) : u.V), rfl⟩
    have hm : algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) (v : u.V)) *
        algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) ((v⁻¹ : u.Vˣ) : u.V)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    have hn := congrArg norm hm
    rw [norm_mul, norm_one] at hn
    nlinarith [norm_nonneg (algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) (v : u.V))),
      norm_nonneg (algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) ((v⁻¹ : u.Vˣ) : u.V)))]
  rw [map_mul, map_mul, norm_mul, unit_norm w, _root_.one_mul, hev] at hq
  exact hq

end GlobalTheory.Poinc.TestAtPt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.LabelRigid

open GlobalTheory.LevelOfPairing

section Abstract

variable {G U : Type} [Group G] [CommGroup U] {W : G → G → U → Prop} {M : ℕ}

theorem eq_of_pairing (cm : ∀ a b : G, Commute a b)
    (hu : ∀ x y : G, x ^ M = 1 → y ^ M = 1 → ∃! c, W x y c)
    (hm : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c'))
    (hn : ∀ x : G, x ^ M = 1 → (∀ y, y ^ M = 1 → W x y 1) → x = 1) {a b : G} (ha : a ^ M = 1) (hb : b ^ M = 1)
    (h : ∀ y, y ^ M = 1 → ∃ c, W a y c ∧ W b y c) : a = b := by
  have ha' : a⁻¹ ^ M = 1 := by rw [inv_pow, ha, inv_one]
  refine inv_mul_eq_one.1 (hn _ (by rw [(cm _ _).mul_pow, ha', hb, _root_.mul_one]) fun y hy => ?_)
  obtain ⟨c, h₁, h₂⟩ := h y hy
  obtain ⟨d, hd, -⟩ := hu _ y ha' hy
  have e := hm _ _ _ _ _ hd h₁
  rw [inv_mul_cancel] at e
  exact (hu 1 y (one_pow _) hy).unique e (rel_one hu hm hy) ▸ hm _ _ _ _ _ hd h₂

theorem comb_eq (cm : ∀ a b : G, Commute a b)
    (hu : ∀ x y : G, x ^ M = 1 → y ^ M = 1 → ∃! c, W x y c)
    (hm : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c'))
    (hn : ∀ x : G, x ^ M = 1 → (∀ y, y ^ M = 1 → W x y 1) → x = 1) {I : Type} {y₁ y₂ : I → G}
    (t₁ : ∀ p, y₁ p ^ M = 1) (t₂ : ∀ p, y₂ p ^ M = 1) (s₂ : ∀ y, y ^ M = 1 → ∃ p, y₂ p = y)
    (hw : ∀ p q c, W (y₁ p) (y₁ q) c → W (y₂ p) (y₂ q) c) {r : ℕ} (b : Fin r → I) (a : Fin r → ℕ) (p : I)
    (hp : y₁ p = (List.ofFn fun i => y₁ (b i) ^ a i).prod) : y₂ p = (List.ofFn fun i => y₂ (b i) ^ a i).prod := by
  refine eq_of_pairing cm hu hm hn (t₂ p) (prod_pow_eq_one cm _ (fun i => t₂ (b i)) a) fun y hy => ?_
  obtain ⟨q, rfl⟩ := s₂ y hy
  choose c hc using fun i => (hu _ _ (t₁ (b i)) (t₁ q)).exists
  have o₁ := rel_one hu hm (t₁ q)
  have o₂ := rel_one hu hm (t₂ q)
  refine ⟨∏ i, c i ^ a i, hw _ _ _ ?_, rel_prod hm o₂ _ _ fun i => rel_pow hm o₂ (hw _ _ _ (hc i)) _⟩
  rw [hp]
  exact rel_prod hm o₁ _ _ fun i => rel_pow hm o₁ (hc i) _

end Abstract

theorem eq_of_isAlgClosed {K : Type} [Field K] [IsAlgClosed K] [CharZero K] (P : PolAV (Sp K)) {n j m : ℕ}
    (hn : n.Prime) (ho : Odd n) (hm : m = n ^ j * (n ^ 2) ^ 2) (hb : ((n ^ 2) ^ 2) ^ P.g * P.g.factorial < m)
    {I : Type} {y₁ y₂ : I → (baseOver (Sp K) ⟶ P.A)}
    (t₁ : ∀ p, y₁ p ^ (m ^ 2) = 1) (t₂ : ∀ p, y₂ p ^ (m ^ 2) = 1)
    (s₁ : ∀ y, y ^ (m ^ 2) = 1 → ∃ p, y₁ p = y) (s₂ : ∀ y, y ^ (m ^ 2) = 1 → ∃ p, y₂ p = y)
    (hw : ∀ p q c, WeilIs P.A P.L (m ^ 2 : ℕ) (y₁ p) (y₁ q) c → WeilIs P.A P.L (m ^ 2 : ℕ) (y₂ p) (y₂ q) c)
    (hfix : ∀ p, y₁ p ^ n = 1 → y₂ p = y₁ p) {v : I → Γ((baseOver (Sp K)).left, ⊤)}
    (v₁ : IsThetaPt P m y₁ v) (v₂ : IsThetaPt P m y₂ v) (p : I) : y₂ p = y₁ p := by
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  have := P.isAb.comm
  have cm : ∀ a b : baseOver (Sp K) ⟶ P.A, Commute a b := fun a b => _root_.mul_comm a b
  have hm0 : m ^ 2 ≠ 0 := pow_ne_zero _ (by omega)
  have hK : ((m ^ 2 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 hm0
  have : NeZero (m ^ 2) := ⟨hm0⟩
  have : NeZero ((m ^ 2 : ℕ) : K) := ⟨hK⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K (m ^ 2)
  have hζ := hz.isUnit_unit (NeZero.ne _)
  generalize (hz.isUnit (NeZero.ne _)).unit = ζ at hζ
  obtain ⟨lev⟩ := GlobalTheory.nonempty_level_of_isAlgClosed K P (m ^ 2) ζ hK hζ
  obtain ⟨hu, hmul, -⟩ := hL.weil _ P (m ^ 2) (baseOver (Sp K))
  have hnd := hL.weilNondeg K P (m ^ 2) hK
  choose b hb' using fun i => s₁ _ (lev.torsion i)
  have eb : lev.pt = fun i => y₁ (b i) := funext fun i => (hb' i).symm
  have comb : ∀ (a : Fin (2 * P.g) → ℕ) (q : I), y₁ q = linComb lev.pt a → y₂ q = linComb (fun i => y₂ (b i)) a :=
    fun a q h => comb_eq (W := fun a b u => WeilIs P.A P.L (m ^ 2 : ℕ) a b u) cm hu hmul hnd t₁ t₂ s₂ hw b a q
      (by rw [h, eb]; rfl)
  have prim : ∀ {T : Type} [CommRing T] [Nontrivial T] (φ : K →+* T),
      IsPrimitiveRoot (Units.map φ.toMonoidHom ζ) (m ^ 2) := fun φ =>
    hζ.map_of_injective (f := Units.map φ.toMonoidHom) (Units.map_injective φ.injective)
  obtain ⟨lev', hl'⟩ := GlobalTheory.exists_level_of_pairing hL.globalFns hL.weil hL.mulN (Sp K) P (m ^ 2) (unitOn ζ) lev.prim
    (fun F _ s => by
      have : Nontrivial Γ(Spec (CommRingCat.of F), ⊤) :=
        (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
      refine ⟨?_, prim (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)⟩
      rw [← map_natCast (Spec.preimage s).hom]
      exact (map_ne_zero _).2 hK) (fun i => y₂ (b i)) (fun i => t₂ _)
    (fun i k => hw _ _ _ (by rw [hb', hb']; exact lev.pairing i k))
  choose q hq using fun a => s₁ _ (ThetaPtDet.levelPoint_pow lev rfl a)
  have e₁ : (fun a => y₁ (q a)) = GlobalTheory.levelPoint lev rfl := funext hq
  have e₂ : (fun a => y₂ (q a)) = GlobalTheory.levelPoint lev' rfl := funext fun a =>
    (comb _ _ (hq a)).trans (by rw [← hl']; rfl)
  have w₁ := ThetaDescentLevel.isThetaPt_reindex v₁ q
  have w₂ := ThetaDescentLevel.isThetaPt_reindex v₂ q
  rw [e₁] at w₁
  rw [e₂] at w₂
  obtain ⟨φ, ⟨hφ, t, ht⟩, hl⟩ := GlobalTheory.thetaPtDetermines_and_endDeterminedOnTorsion.1 P.g n 2 j _ m hn ho le_rfl rfl hm hb K
    (Nat.cast_ne_zero.2 hn.ne_zero) P P rfl rfl _ lev lev' _ w₁ w₂
  have key : ∀ p, y₁ p ≫ φ.hom = y₂ p := fun p => by
    obtain ⟨d, hd⟩ := lev.span K (𝟙 _) (y₁ p) (t₁ p)
    have hd' : linComb lev.pt (fun i => (d i : ℕ)) = y₁ p :=
      (congrArg (linComb · _) (funext fun i => (Category.id_comp (lev.pt i)).symm)).trans hd
    rw [comb _ _ hd'.symm, ← hd', ThetaPtDet.linComb_comp, ← hl']
    exact congrArg (linComb · _) (funext hl)
  obtain ⟨w, hw'⟩ := LBIso.symm (⟨t, ht⟩ : LBIso _ _)
  have h3 : 3 ≤ n := by
    have := hn.two_le
    obtain ⟨c, rfl⟩ := ho
    omega
  have hid := MatchRigid.aut_eq_id hL P (𝟙 _) h3 (Nat.cast_ne_zero.2 hn.ne_zero) φ w hw' fun x hx => by
    have hd : n ∣ m ^ 2 := by
      rw [hm]
      exact dvd_pow (Dvd.dvd.mul_left (dvd_pow (dvd_pow_self n two_ne_zero) two_ne_zero) _) two_ne_zero
    obtain ⟨c, hc⟩ := hd
    obtain ⟨r, rfl⟩ := s₁ x (by rw [hc, pow_mul]; erw [hx]; exact one_pow _)
    exact (key r).trans (hfix r hx)
  rw [← key, hid, Category.comp_id]

theorem labels_eq : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (n j m : ℕ), n.Prime → Odd n → m = n ^ j * (n ^ 2) ^ 2 → ((n ^ 2) ^ 2) ^ A.g * A.g.factorial < m → ∀ (x₁ x₂ : QkPt D (Kb R) (m ^ 2) → (TFK (R := R) (Kb R) ⟶ A.A)), LabTors D A (m ^ 2) x₁ → LabTors D A (m ^ 2) x₂ → (∀ p, x₁ p ^ n = 1 → x₂ p = x₁ p) → ∀ v : QkPt D (Kb R) (m ^ 2) → Kb R, IsThetaPt A m x₁ (fun p => GlobalTheory.Ex.fnOf (v p)) → IsThetaPt A m x₂ (fun p => GlobalTheory.Ex.fnOf (v p)) → ∀ p, x₂ p = x₁ p := by
  intro R _ _ _ D A n j m hn ho hm hb x₁ x₂ ⟨s₁, t₁, _, _, w₁⟩ ⟨s₂, t₂, _, _, w₂⟩ hfix v v₁ v₂ p
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  have : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R _)
  obtain ⟨P, g, hg, hP, hmul, hs⟩ := hL.polBaseChange _ (Sp (Kb R)) (jFK (R := R) (Kb R)) A
  have hp : IsGrpPullback P.A A.A _ g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hg.w x), (Over.OverMorphism.ext hy : y₀ = toBase hg.w y), ← hmul]
    rfl⟩
  have hl : LBIso P.L (A.L.pull g) := LBIso.symm hs
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback hp (𝟙 (Sp (Kb R))) (jFK (R := R) (Kb R)) (Category.id_comp _).symm
  have hE : ∀ x, x.left = (e.symm x).left ≫ g := fun x =>
    (congrArg (fun z => z.left) (e.apply_symm_apply x).symm).trans (he _)
  have kW : ∀ (s : Sp (Kb R) ⟶ Sp (FractionRing R)) (_ : s = 𝟙 _ ≫ jFK (R := R) (Kb R))
      (x y : baseOver (Sp (Kb R)) ⟶ P.A) (x₀ y₀ : Over.mk s ⟶ A.A) (c : Γ(Sp (Kb R), ⊤)ˣ),
      x₀.left = x.left ≫ g → y₀.left = y.left ≫ g →
      (WeilIs P.A P.L (m ^ 2 : ℕ) x y c ↔ WeilIs A.A A.L (m ^ 2 : ℕ) x₀ y₀ c) := by
    rintro s rfl x y x₀ y₀ c hx hy
    have := P.isAb.comm
    exact weilIs_grpPullback_of_comm' _ _ _ _ _ g _ _ A.isLB P.isLB hp hl (baseOver _) _ x y x₀ y₀ c hx hy
  have kT : ∀ (s : Sp (Kb R) ⟶ Sp (FractionRing R)) (_ : s = 𝟙 _ ≫ jFK (R := R) (Kb R))
      (x : QkPt D (Kb R) (m ^ 2) → (baseOver (Sp (Kb R)) ⟶ P.A)) (x₀ : QkPt D (Kb R) (m ^ 2) → (Over.mk s ⟶ A.A))
      (u : QkPt D (Kb R) (m ^ 2) → Γ(Sp (Kb R), ⊤)), (∀ i, (x₀ i).left = (x i).left ≫ g) →
      (∀ i, x i ^ m ^ 2 = 1) → IsThetaPt A m x₀ u → IsThetaPt P m x u := by
    rintro s rfl x x₀ u hx ht h
    exact (ThetaPtUp.isThetaPt_iff (T := baseOver (Sp (Kb R))) hp hl hx ht _).2 h
  have tor : ∀ {k : ℕ} (x), x ^ k = 1 → e.symm x ^ k = 1 := fun x h => by rw [← map_pow, h, map_one]
  have tor' : ∀ {k : ℕ} (x), x ^ k = 1 → e x ^ k = 1 := fun x h => by rw [← map_pow, h, map_one]
  refine e.symm.injective (eq_of_isAlgClosed P hn ho hm (by rw [hP]; exact hb) (y₁ := fun p => e.symm (x₁ p))
    (y₂ := fun p => e.symm (x₂ p)) (fun p => tor _ (t₁ p)) (fun p => tor _ (t₂ p))
    (fun y hy => (s₁ _ (tor' y hy)).imp fun q h => (congrArg e.symm h).trans (e.symm_apply_apply y))
    (fun y hy => (s₂ _ (tor' y hy)).imp fun q h => (congrArg e.symm h).trans (e.symm_apply_apply y))
    (fun q q' c h => ?_) (fun q h => congrArg e.symm (hfix q ?_))
    (kT _ (Category.id_comp _).symm _ _ _ (fun i => hE _) (fun i => tor _ (t₁ i)) v₁)
    (kT _ (Category.id_comp _).symm _ _ _ (fun i => hE _) (fun i => tor _ (t₂ i)) v₂) p)
  · obtain ⟨z, rfl⟩ : ∃ z : (Kb R)ˣ, unitOn z = c :=
      ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of (Kb R))).hom.hom.toMonoidHom c, Units.ext
        ((Scheme.ΓSpecIso (CommRingCat.of (Kb R))).commRingCatIsoToRingEquiv.symm_apply_apply c.val)⟩
    exact (kW _ (Category.id_comp _).symm _ _ _ _ _ (hE _) (hE _)).2 ((w₂ _ _ _).1 ((w₁ _ _ _).2
      ((kW _ (Category.id_comp _).symm _ _ _ _ _ (hE _) (hE _)).1 h)))
  · exact (congrArg (· ^ n) (e.apply_symm_apply _).symm).trans (tor' _ h)

end GlobalTheory.Mum.LabelRigid
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowE8

theorem exists_cp_e8LB : ∀ (S : Scheme.{0}) (G₀ : Over S) [GrpObj G₀] [IsCommMonObj G₀] (P : GlobalTheory.UU.CP G₀) (W : Matrix (Fin 8) (Fin 8) ℤ), ∃ Q : GlobalTheory.UU.CP (powObj G₀ 8), Q.L.L = GlobalTheory.PowE8.e8LB G₀ P.L.L W := by
  intro S G₀ _ _ P W
  haveI hm : ∀ k : (Fin 8 × Fin 8) × Fin 4,
      IsMonHom ((![powPr G₀ k.1.1 * powPr G₀ k.1.2, powPr G₀ k.1.1, powPr G₀ k.1.2, 1] :
        Fin 4 → (powObj G₀ 8 ⟶ G₀)) k.2) := by
    rintro ⟨⟨a, b⟩, i⟩
    fin_cases i <;> dsimp <;>
      first
        | infer_instance
        | exact (inferInstance : IsMonHom (lift (powPr G₀ a) (powPr G₀ b) ≫ μ))
        | exact (inferInstance : IsMonHom (toUnit (powObj G₀ 8) ≫ η[G₀]))
  obtain ⟨Q, hQ⟩ := GlobalTheory.LinCombCP.exists_cp_linComb P (K := (Fin 8 × Fin 8) × Fin 4)
    (fun k => (![powPr G₀ k.1.1 * powPr G₀ k.1.2, powPr G₀ k.1.1, powPr G₀ k.1.2, 1] :
      Fin 4 → (powObj G₀ 8 ⟶ G₀)) k.2)
    (fun k => -(W k.1.1 k.1.2 * negε k.2))
  refine ⟨Q, hQ.trans ?_⟩
  unfold GlobalTheory.PowE8.e8LB GlobalTheory.LinCombCP.cpLB
  congr 1
  funext k
  rcases k with ⟨⟨a, b⟩, i⟩
  fin_cases i <;> rfl

end GlobalTheory.PowE8
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.E8Fibration

theorem isProd_pullback_iso : ∀ {S S' : Scheme.{0}} (f : S' ⟶ S) {A B : Over S} [GrpObj A] [GrpObj B] (pr : Fin 8 → (A ⟶ B)), E8Fibration.IsProd pr → ∀ (P : Over S') [GrpObj P] (i : (Over.pullback f).obj A ≅ P), IsMonHom i.hom → E8Fibration.IsProd (fun a => i.inv ≫ (Over.pullback f).map (pr a)) := by
  intro S S' f A B _ _ pr hpr P _ i hi
  obtain ⟨hmon, huniv⟩ := hpr
  refine ⟨fun a => ?_, fun T y => ?_⟩
  · haveI := hmon a
    infer_instance
  · let adj := Over.mapPullbackAdj f
    obtain ⟨x', hx', hu⟩ := huniv ((Over.map f).obj T) (fun a => (adj.homEquiv T B).symm (y a))
    refine ⟨adj.homEquiv T A x' ≫ i.hom, fun a => ?_, fun x hx => ?_⟩
    · simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [← Adjunction.homEquiv_naturality_right, hx' a, Equiv.apply_symm_apply]
    · have h1 : (adj.homEquiv T A).symm (x ≫ i.inv) = x' := by
        apply hu
        intro a
        rw [← Adjunction.homEquiv_naturality_right_symm, Category.assoc, hx a]
      rw [← h1, Equiv.apply_symm_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end GlobalTheory.Poinc.Sep.E8Fibration

end
end
