module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle016
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle010
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle041
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsGoodModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2082
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1395
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1903
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1905
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementHasRationalWeilOperatorAdelicFourier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementOperatorBijective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle197
import GroundTheory.GlobalFields.LocalFieldAtPlace
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2234
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical

@[expose] public section

section

open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

theorem _root_.GlobalTheory.T.torsion_cmUnitaryShimura_mem_closure_linearHom_images : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (n : ℕ), 0 < n →
    ∀ y : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G, y ^ n = 1 →
    y ∈ Submonoid.closure {w : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G |
      ∃ (x : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G) (f : (X.A true).t.G ⟶ X.B.t.G),
        x ^ n = 1 ∧ GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f ∧
        (∃ m : ℕ, 0 < m ∧ ∃ z : Fin p → 𝓞 E, f ^ m = ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a)) ∧
        w = x ≫ f} := by
  first | exact @GlobalTheory.FlatCM.TorsGen.gen | exact GlobalTheory.FlatCM.TorsGen.gen | (intros; apply GlobalTheory.FlatCM.TorsGen.gen <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDual

section Fibre

open GlobalTheory.NearFibreIso

theorem near_isIso_of_isProper_of_finitePresentation {R : Type} [CommRing R] {Y X : Scheme.{0}} (s : X ⟶ Sp R)
    (f : Y ⟶ X) (K : Type) [Field K] [Algebra R K] [IsProper f]
    [LocallyOfFinitePresentation s] [LocallyOfFinitePresentation (f ≫ s)] [Flat (f ≫ s)]
    [IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K))))]
    (x : X) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) :
    Near f (MorphismProperty.isomorphisms _) x := by
  obtain ⟨T, T', g, g', f', H, _, ⟨y, rfl⟩, hQ⟩ := near_isFinite s f K x hx
  have := isIso_fibre_of_pullback s f (spMap (algebraMap R K)) H
  obtain ⟨U, U', k, k', f'', H', _, ⟨z, rfl⟩, hQ'⟩ :=
    near_isClosedImmersion (g ≫ s) f' K y (by rw [Scheme.Hom.comp_apply]; exact hx)
  have H'' := H'.paste_vert H
  have := isIso_fibre_of_pullback s f (spMap (algebraMap R K)) H''
  have : IsOpenImmersion (k' ≫ g') :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) H'' inferInstance
  have : Flat (f'' ≫ (k ≫ g) ≫ s) := by
    rw [H''.w_assoc]; infer_instance
  have : LocallyOfFinitePresentation (f'' ≫ (k ≫ g) ≫ s) := by
    rw [H''.w_assoc]; infer_instance
  have h := GlobalTheory.AbMonoIsoAny.near_isIso_of_finitePresentation ((k ≫ g) ≫ s) f'' K z
    (by rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]; exact hx)
  have h' := Near.of_pullback f H'' h
  rwa [Scheme.Hom.comp_apply] at h'

theorem isIso_of_geometric_fibres {S X Y : Scheme.{0}} (p : X ⟶ S) (f : Y ⟶ X) [IsProper f]
    [LocallyOfFinitePresentation p] [LocallyOfFinitePresentation (f ≫ p)] [Flat (f ≫ p)]
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S), IsIso (pullback.snd f (pullback.fst p t))) :
    IsIso f := by
  have hn : ∀ y : X, Near f (MorphismProperty.isomorphisms _) y := by
    intro y
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (p y)) isOpen_univ
    replace hU : IsAffineOpen U := hU
    let j : Sp Γ(S, U) ⟶ S := hU.fromSpec
    obtain ⟨z, hz⟩ : p y ∈ Set.range j := by rw [hU.range_fromSpec]; exact hyU
    let gX := pullback.fst p j
    let s := pullback.snd p j
    let f' := pullback.snd f gX
    have HX := IsPullback.of_hasPullback p j
    have HY := IsPullback.of_hasPullback f gX
    have HYS := HY.paste_vert HX
    obtain ⟨y', hy', hy's⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := j) y z hz.symm
    have : Flat (f' ≫ s) := MorphismProperty.of_isPullback HYS ‹_›
    have : LocallyOfFinitePresentation (f' ≫ s) := MorphismProperty.of_isPullback HYS ‹_›
    have : IsProper f' := MorphismProperty.of_isPullback HY (inferInstanceAs (IsProper f))
    have : (s y').asIdeal.IsPrime := (s y').isPrime
    let K := AlgebraicClosure (s y').asIdeal.ResidueField
    have hK : RingHom.ker (algebraMap Γ(S, U) K) = (s y').asIdeal := by
      rw [IsScalarTower.algebraMap_eq Γ(S, U) (s y').asIdeal.ResidueField K, ← RingHom.comap_ker,
        (RingHom.injective_iff_ker_eq_bot _).1 (algebraMap (s y').asIdeal.ResidueField K).injective,
        ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]
    let t : Sp K ⟶ Sp Γ(S, U) := spMap (algebraMap Γ(S, U) K)
    have hi := h K (t ≫ j)
    have : IsIso (pullback.snd f' (pullback.fst s t)) := by
      have H := (IsPullback.of_hasPullback f' (pullback.fst s t)).flip.paste_vert HY.flip
      have H₀ := (IsPullback.of_hasPullback f (pullback.fst p (t ≫ j))).flip
      have hu : (pullback.fst s t ≫ gX) ≫ p = pullback.snd s t ≫ t ≫ j := by
        rw [Category.assoc, HX.w, pullback.condition_assoc]
      have e : pullback.lift _ _ hu ≫ pullback.fst p (t ≫ j) = pullback.fst s t ≫ gX := pullback.lift_fst _ _ _
      have H₁ := IsPullback.of_bot' (h₁₁ := pullback.snd f' (pullback.fst s t)) (v₁₂ := pullback.lift _ _ hu)
        (by rw [e]; exact H) H₀
      exact (MorphismProperty.isomorphisms Scheme.{0}).of_isPullback H₁.flip hi
    have h := near_isIso_of_isProper_of_finitePresentation s f' K y' hK
    have h' := Near.of_pullback f HY.flip h
    rwa [hy'] at h'
  have h := isIso_of_near f (𝟙 _) (fun y => by simpa using hn y)
  have e : f = inv (pullback.fst f (𝟙 X)) ≫ pullback.snd f (𝟙 X) := by
    rw [IsIso.eq_inv_comp, pullback.condition, Category.comp_id]
  rw [e]
  infer_instance

end Fibre

variable {S : Scheme.{0}} {A B D : Over S} [GrpObj A] [GrpObj B] [GrpObj D]

theorem isIso_of_isIso_pullback (hB : IsAbelianScheme B) (hD : IsAbelianScheme D) (x : B ⟶ D)
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S), IsIso ((Over.pullback t).map x)) : IsIso x := by
  have := hB.proper
  have := hB.smooth
  have := hD.proper
  have := hD.smooth
  have : IsProper (x.left ≫ D.hom) := by rw [Over.w]; infer_instance
  have : IsProper x.left := IsProper.of_comp x.left D.hom
  have : Flat (x.left ≫ D.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFinitePresentation (x.left ≫ D.hom) := by rw [Over.w]; infer_instance
  have : IsIso x.left := isIso_of_geometric_fibres D.hom x.left fun Ω _ _ t ↦ by
    have := h Ω t
    have hi : IsIso ((Over.pullback t).map x).left :=
      (Over.forget _).map_isIso ((Over.pullback t).map x)
    have H : IsPullback (pullback.fst B.hom t) ((Over.pullback t).map x).left x.left (pullback.fst D.hom t) := by
      refine IsPullback.of_bot (h₃₁ := t) (v₂₁ := pullback.snd D.hom t) (v₂₂ := D.hom) ?_ ?_
        (IsPullback.of_hasPullback D.hom t)
      · have e : ((Over.pullback t).map x).left ≫ pullback.snd D.hom t = pullback.snd B.hom t :=
          Over.w ((Over.pullback t).map x)
        rw [e, Over.w]
        exact IsPullback.of_hasPullback B.hom t
      · exact (pullback.lift_fst _ _ _).symm
    rw [← H.isoPullback_inv_snd]
    infer_instance
  have : IsIso ((Over.forget _).map x) := ‹_›
  exact isIso_of_reflects_iso x (Over.forget _)

theorem additive_of_cube (hC : GlobalTheory.Published.CubeTheorem) (hA : IsAbelianScheme A) (hB : IsAbelianScheme B)
    {P : LB (A ⊗ B).left} (hP : P.IsLB) (h₁ : Triv (ev P (1 : B ⟶ A) (𝟙 B)))
    (h₂ : Triv (ev P (𝟙 A) (1 : A ⟶ B))) : IsAdditive P ∧ IsAdditive (swap P) := by
  have key : ∀ (T : Over S) (a b c : T ⟶ A ⊗ B),
      evc hP ((a * b * c) ≫ fst A B) ((a * b * c) ≫ snd A B) - evc hP ((a * b) ≫ fst A B) ((a * b) ≫ snd A B) -
        evc hP ((a * c) ≫ fst A B) ((a * c) ≫ snd A B) - evc hP ((b * c) ≫ fst A B) ((b * c) ≫ snd A B) +
        evc hP (a ≫ fst A B) (a ≫ snd A B) + evc hP (b ≫ fst A B) (b ≫ snd A B) +
        evc hP (c ≫ fst A B) (c ≫ snd A B) - evc hP ((1 : T ⟶ A ⊗ B) ≫ fst A B) ((1 : T ⟶ A ⊗ B) ≫ snd A B) = 0 := by
    intro T a b c
    have h := hC S (A ⊗ B) (AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB) P hP T a b c
    have hl := LB.isLB_linComb hP (fun k : Fin 8 ↦ (![a * b * c, a * b, a * c, b * c, a, b, c, 1] k).left)
      ![1, -1, -1, -1, 1, 1, 1, -1]
    have e := (cls_eq_zero_iff hl).2 h
    rw [cls_linComb hP _ _ hl, Fin.sum_univ_eight] at e
    simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul] at e
    simp only [evc, lift_comp_fst_snd]
    rw [← e]
    abel
  refine ⟨(isAdditive_iff hP).2 fun Y a a' t ↦ ?_, (BirigidLift.isAdditive_swap_iff hP).2 fun Y a t t' ↦ ?_⟩
  · have e := key Y (lift a 1) (lift a' 1) (lift 1 t)
    simp only [MonObj.mul_comp, MonObj.one_comp, lift_fst, lift_snd, _root_.mul_one, _root_.one_mul,
      evc_one_left hP h₁, evc_one_right hP h₂] at e
    rw [← sub_eq_zero, ← e]
    abel
  · have e := key Y (lift 1 t) (lift 1 t') (lift a 1)
    simp only [MonObj.mul_comp, MonObj.one_comp, lift_fst, lift_snd, _root_.mul_one, _root_.one_mul,
      evc_one_left hP h₁, evc_one_right hP h₂] at e
    rw [← sub_eq_zero, ← e]
    abel

theorem IsDual.isIso_of_cls {P : LB (A ⊗ B).left} {Q : LB (A ⊗ D).left} (hP : IsDual A B P) (hQ : IsDual A D Q)
    {x : B ⟶ D} (e : cls P hP.isLB = evc hQ.isLB (fst A B) (snd A B ≫ x)) : IsIso x := by
  obtain ⟨y, hy, -⟩ := hP.univ D Q hQ.isLB hQ.additive
  have e' : cls Q hQ.isLB = evc hP.isLB (fst A D) (snd A D ≫ y) := (cls_eq_iff hQ.isLB (pull_isLB hP.isLB _)).2 hy
  refine ⟨y, BirigidLift.dual_ext hP ?_, BirigidLift.dual_ext hQ ?_⟩
  · rw [← Category.assoc, ← BirigidLift.evc_of_cls hP.isLB hQ.isLB e', ← BirigidLift.evc_of_cls hQ.isLB hP.isLB e,
      Category.comp_id]
  · rw [← Category.assoc, ← BirigidLift.evc_of_cls hQ.isLB hP.isLB e, ← BirigidLift.evc_of_cls hP.isLB hQ.isLB e',
      Category.comp_id]

theorem principalPol_selfDual : GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.CubeTheorem →
    ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
      ∀ c : GlobalTheory.CechPic.Pic (A ⊗ A).left, GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.IsPrincipalPol A c →
        ∃ (P : LB (A ⊗ A).left) (hP : P.IsLB), GlobalTheory.CechPic.cls P hP = c ∧ GlobalTheory.AbDual.IsDual A A P := by
  intro hD hC S A _ hA c hc
  obtain ⟨P, hP, rfl⟩ := cls_surj c
  refine ⟨P, hP, rfl, ?_⟩
  obtain ⟨a₁, a₂⟩ := additive_of_cube hC hA hA hP ((triv_ev_iff hP _ _).2 hc.1) ((triv_ev_iff hP _ _).2 hc.2.1)
  obtain ⟨D, _, Q, hD', -, q, q'⟩ := hD S A hA
  obtain ⟨x, hx, e⟩ := BirigidLift.exists_hom q q'.additive hP a₁ a₂
  have ix : IsIso x := isIso_of_isIso_pullback hA hD' x fun Ω _ _ s ↦ by
    obtain ⟨L, hL, -, hK, hc'⟩ := hc.2.2 Ω s
    have f := isGrpPullback_pullback A s
    have d := isGrpPullback_pullback D s
    have hA₀ := PolPull.isAbelianScheme_of_isGrpPullback hA f
    have := hA₀.comm
    obtain ⟨g, hg⟩ := AbelianDim.exists_relDim Ω _ hA₀
    have p₀ := PerfectDual.isDual_of_isPerfect hD _ _ hA₀ hA₀ hg hg (isPerfect_lam hL hK)
    obtain ⟨m, m₁, m₂⟩ := exists_prod_pullback f d
    have hQ := pull_isLB q.isLB m
    have q₀ := q.baseChange f d m₁ m₂ hQ ((cls_eq_iff hQ hQ).1 rfl)
    refine p₀.isIso_of_cls q₀ ?_
    have l₁ : IndefiniteRowSideFullHecke.ZeroSectionBase.sqToBase A s ≫ (fst A A).left = (fst _ _ : _ ⟶ (Over.pullback s).obj A).left ≫
        pullback.fst A.hom s :=
      congrArg (fun z ↦ z.left) (lift_fst (IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (fst _ _)) (IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (snd _ _)))
    have l₂ : IndefiniteRowSideFullHecke.ZeroSectionBase.sqToBase A s ≫ (snd A A).left = (snd _ _ : _ ⟶ (Over.pullback s).obj A).left ≫
        pullback.fst A.hom s :=
      congrArg (fun z ↦ z.left) (lift_snd (IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (fst _ _)) (IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (snd _ _)))
    rw [← BirigidLift.pull_evc_eq l₁ l₂ m₁ m₂ q.isLB hQ (x := x) (pullback.lift_fst _ _ _).symm, ← e, hc']
    exact cls_cube_two hL _ _ _
  exact isDual_of_iso S A A D P Q q hP x ix hx ((cls_eq_iff hP (pull_isLB q.isLB _)).1 e)

end GlobalTheory.AbDual
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.thetaGridCharacters_archExponents_gap_gt_rank : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m), SquareStanding G t → ∀ (τf : InfinitePlace D.host.F → D.what₂.Tau)
    (hτf : ∀ w, ((starRingEnd ℂ).comp (tauE D (τf w))).comp (algebraMap D.host.F D.host.E) = w.embedding),
    ∃ mα mβ : InfinitePlace D.host.F → ℤ,
      HasExp (fun w => ⟨(starRingEnd ℂ).comp (tauE D (τf w)), hτf w⟩) (alpha G t i j) mα ∧
      HasExp (fun w => ⟨(starRingEnd ℂ).comp (tauE D (τf w)), hτf w⟩) (beta G i j) mβ ∧
      ∀ w, (((spW G i j).rank + (spW₁ G i j).rank : ℕ) : ℤ) < mα w - mβ w := by
  first | exact @GlobalTheory.SquareExps.exps | exact GlobalTheory.SquareExps.exps | (intros; apply GlobalTheory.SquareExps.exps <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.thetaTransform_injOn_adelicSchwartzSpace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ],
    ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ Φ' ∈ GlobalTheory.WeilM.schA D.host.F κ,
      (∀ w, GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w Φ) = GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w Φ')) →
      Φ = Φ' := by
  first | exact @GlobalTheory.Adopt.thetaTransform_injOn_adelicSchwartzSpace | exact GlobalTheory.Adopt.thetaTransform_injOn_adelicSchwartzSpace | (intros; apply GlobalTheory.Adopt.thetaTransform_injOn_adelicSchwartzSpace <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.weilRep_rationalDarboux_fixes_thetaDistribution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (ψ : AddChar (AF F) ℂ), (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ))) → ∀ (n d : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E), (∀ i j, σ (JX j i) = JX i j) → JX.det ≠ 0 → (∀ i j, σ (JW j i) = -JW i j) → JW.det ≠ 0 → ∀ (co : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JX) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW)) (Fin n × Fin d)), (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F, co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) → ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW → ∀ om : UA σ JX × UA σ JW →* Module.End ℂ ((Fin n × Fin d → AF F) → ℂ), IsUWeilPair (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JX) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW) co χX χW om → ∀ γ ∈ ratU σ JX, ∀ γ' ∈ ratU σ JW, ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (om (γ, γ') Φ) = thetaSum F Φ := by
  first | exact @GlobalTheory.WeilThetaRat.thetaSum_om_rat | exact GlobalTheory.WeilThetaRat.thetaSum_om_rat | (intros; apply GlobalTheory.WeilThetaRat.thetaSum_om_rat <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit

noncomputable section

namespace GlobalTheory.AdelicFourierSch

open Filter GlobalTheory.WeylFourier GlobalTheory.RatWeilOp GlobalTheory.WeylBij


open scoped Classical in
theorem fourier_mem_schA_std (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F))
    [μ.IsAddHaarMeasure] : ∀ Φ ∈ schA F κ, (fun y : κ → AF F => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ) ∈ schA F κ := by
  have hunr := psiUnr_eventually ψ hψ
  letI mI : MeasurableSpace (κ → mixedEmbedding.mixedSpace F) := borel _
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := ⟨rfl⟩
  letI mV : ∀ v : Pl (F := F), MeasurableSpace (κ → Fv F v) := fun _ => borel _
  haveI bV : ∀ v : Pl (F := F), BorelSpace (κ → Fv F v) := fun _ => ⟨rfl⟩
  obtain ⟨μi, hμi⟩ : ∃ μ : Measure (κ → mixedEmbedding.mixedSpace F), μ.IsAddHaarMeasure :=
    ⟨Measure.addHaar, inferInstance⟩
  obtain ⟨μv, hμv, hμv1⟩ : ∃ μv : ∀ v : Pl (F := F), Measure (κ → Fv F v), (∀ v, (μv v).IsAddHaarMeasure) ∧
      ∀ v, μv v {x | ∀ i, x i ∈ v.adicCompletionIntegers F} = 1 := by
    let K : ∀ v : Pl (F := F), TopologicalSpace.PositiveCompacts (κ → Fv F v) := fun v =>
      ⟨⟨Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)),
        isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v⟩, by
          show (interior (Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)))).Nonempty
          rw [(isOpen_set_pi Set.finite_univ fun _ _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers v).interior_eq]
          exact ⟨0, fun i _ => (v.adicCompletionIntegers F).zero_mem⟩⟩
    refine ⟨fun v => Measure.addHaarMeasure (K v), fun v => inferInstance, fun v => ?_⟩
    have e : {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} = (K v : Set (κ → Fv F v)) := by
      ext x; simp [K]
    rw [e]
    exact Measure.addHaarMeasure_self
  haveI := hμv
  obtain ⟨c₀, hc₀, hpure⟩ := GlobalTheory.T.integral_adelic_pureTensor_eq_product_local F κ μ μi μv hμv1
  obtain ⟨ei', hei'bij, hei'⟩ := GlobalTheory.T.exists_archimedeanSchwartz_traceFourier_bijective F κ μi
  have hψc : ∀ v, Continuous (GlobalTheory.LatVac.psiAt ψ v) := fun v => GlobalTheory.SchrSB.continuous_psiAt ψ hψ.1 v
  have hsub : ∀ v, ∀ φ ∈ SB (κ → Fv F v), φ ∈ intSub (GlobalTheory.LatVac.psiAt ψ v) (μv v) := fun v φ hφ y =>
    (hφ.1.continuous.mul ((hψc v).comp (continuous_id.dotProduct continuous_const))).integrable_of_hasCompactSupport
      hφ.2.mul_right
  let ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ := fun v => ftE (GlobalTheory.LatVac.psiAt ψ v) (μv v)
  have hev : ∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ = ft (GlobalTheory.LatVac.psiAt ψ v) (μv v) φ :=
    fun v φ hφ => ftE_eq _ _ (hsub v φ hφ)
  have hbij : ∀ v, Set.BijOn (ev v) (SB (κ → Fv F v) : Set _) (SB (κ → Fv F v) : Set _) := fun v =>
    (GlobalTheory.T.fourier_bijOn_schwartzBruhat_finitePlace F v (GlobalTheory.LatVac.psiAt ψ v) (hψc v) (fun t => GlobalTheory.StdCharFromIsStd.norm_psi hψ _)
      (GlobalTheory.PsiNontriv.psiAt_ne_one ψ hψ v) κ (μv v)).congr fun φ hφ => (hev v φ hφ).symm
  have hind : ∀ᶠ v in cofinite, ev v (ind κ v) = ind κ v := by
    filter_upwards [hunr] with v hv
    rw [hev v (ind κ v) (GlobalTheory.StdVacuum.indicator_mem_SB v)]
    exact GlobalTheory.T.integralPointsIndicator_fourier_self_unramified F v (GlobalTheory.LatVac.psiAt ψ v) (fun x => hv x) κ (μv v) (hμv1 v)
  have hpureE : ∀ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), IsFam φ →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ intSub ψ μ ∧
      ft ψ μ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c₀ • ei' f) (fun v => ev v (φ v)) := by
    intro f φ hφ
    have hφ' : ∀ y, IsFam (finT ψ φ y) := finT_isFam ψ hψ φ hφ
    have hfun : ∀ y, (fun x => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ x * ψ (x ⬝ᵥ y)) = fun x =>
        archT f (fun i => evI F (y i)) (fun i => evI F (x i)) * ∏ᶠ v, finT ψ φ y v (fun i => evFin F v (x i)) :=
      fun y => funext fun x => pure_mul_psi ψ hψ f φ hφ x y
    refine ⟨fun y => ?_, funext fun y => ?_⟩
    · rw [hfun y]
      exact (hpure _ _ (archT_continuous f _) (archT_integrable μi f _) (hφ' y)).1
    · show ∫ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ x * ψ (x ⬝ᵥ y) ∂μ = _
      rw [hfun y, (hpure _ _ (archT_continuous f _) (archT_integrable μi f _) (hφ' y)).2]
      have h2 : ∀ v, ev v (φ v) (fun i => evFin F v (y i)) = ∫ x, finT ψ φ y v x ∂(μv v) := fun v => by
        rw [hev v _ (hφ.1 v)]; rfl
      have h3 : (c₀ • ei' f) (fun i => evI F (y i)) = c₀ * ∫ x, archT f (fun i => evI F (y i)) x ∂μi := by
        have h4 := hei' f (fun i => evI F (y i))
        simp only [archT]
        rw [← h4]
        rfl
      show _ = (c₀ • ei' f) (fun i => evI F (y i)) * ∏ᶠ v, ev v (φ v) (fun i => evFin F v (y i))
      rw [h3, finprod_congr h2]
  let T : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ := ftE ψ μ
  have hfam : ∀ φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ, IsFam φ → IsFam fun v => ev v (φ v) := fun φ hφ =>
    ⟨fun v => (hbij v).mapsTo (hφ.1 v), by filter_upwards [hφ.2, hind] with v h1 h2; rw [h1, h2]⟩
  have hTpure : ∀ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), IsFam φ →
      T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c₀ • ei' f) (fun v => ev v (φ v)) := fun f φ hφ =>
    (ftE_eq ψ μ (hpureE f φ hφ).1).trans (hpureE f φ hφ).2
  have hgen := schA_le_span_pure F κ
  have hT_schA : ∀ Φ ∈ schA F κ, T Φ ∈ schA F κ := by
    intro Φ hΦ
    refine (Submodule.span_le.2 ?_ : _ ≤ (schA F κ).comap T) (hgen Φ hΦ)
    rintro _ ⟨f, φ, hφ, rfl⟩
    show T _ ∈ schA F κ
    rw [hTpure f φ hφ]
    exact pure_mem_schA _ _ (hfam φ hφ)
  have hint : ∀ Φ ∈ schA F κ, Φ ∈ intSub ψ μ := fun Φ hΦ => by
    refine (Submodule.span_le.2 ?_ : _ ≤ intSub ψ μ) (hgen Φ hΦ)
    rintro _ ⟨f, φ, hφ, rfl⟩
    exact (hpureE f φ hφ).1
  intro Φ hΦ
  have h := hT_schA Φ hΦ
  rw [show T Φ = ft ψ μ Φ from ftE_eq ψ μ (hint Φ hΦ)] at h
  exact h

theorem dilate_mem_schA {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {a : F} (ha : a ≠ 0)
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : (fun y => Φ (algebraMap F (AF F) a • y)) ∈ schA F κ := by
  classical
  have hdet : IsUnit (Matrix.diagonal fun _ : κ => a⁻¹).det := by
    rw [Matrix.det_diagonal]
    exact (Finset.prod_ne_zero_iff.2 fun _ _ => inv_ne_zero ha).isUnit
  have hinv : (Matrix.diagonal fun _ : κ => a⁻¹)⁻¹ = Matrix.diagonal fun _ : κ => a := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.diagonal_mul_diagonal]
    simp [mul_inv_cancel₀ ha]
  have h := GlobalTheory.SympChangeBij.levi_mapsTo _ hdet Φ hΦ
  rw [hinv, Matrix.diagonal_map (map_zero _)] at h
  convert h using 2 with y
  rw [LinearMap.funLeft_apply]
  congr 1
  funext i
  rw [Matrix.mulVec_diagonal]
  rfl

theorem fourier_mem_schA : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), μ.IsAddHaarMeasure → ∀ Φ ∈ schA F κ, (fun y : κ → AF F => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ) ∈ schA F κ := by
  intro F _ _ hF ψ hψ κ _ _ _ μ hμ Φ hΦ
  have h0 := GlobalTheory.SubstIntertw.isStd_stdChar F
  obtain ⟨a, ha, hψa⟩ := GlobalTheory.AdeleCharTwist.exists_mul_eq F _ ψ (GlobalTheory.StdCharFromIsStd.isCharAF h0) hψ
  have h := dilate_mem_schA ha (fourier_mem_schA_std F _ h0 κ μ Φ hΦ)
  convert h using 4 with y x
  rw [hψa, dotProduct_smul, smul_eq_mul]

end GlobalTheory.AdelicFourierSch
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

theorem _root_.GlobalTheory.T.h0_lower_bound_of_isAmple_cartierDiv : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (A : CartierDiv X) (z : X) (k : ℕ) (q : ℚ),
  IsAmpleLB (toLB A) → letI := algebraΓOfHom p; topologicalKrullDim (closure ({z} : Set X)) = k →
  q < (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin k => toLB A : ℤ) →
  ∃ l₁ : ℕ, ∀ l, l₁ ≤ l → q * (l : ℚ) ^ k / k.factorial ≤
    (letI := algebraΓOfHom (redι (Closeds.closure ({z} : Set X)) ≫ p);
      lbH0 ℂ ((toLB (l • A)).pull (redι (Closeds.closure ({z} : Set X)))) : ℚ) := by
  first | exact @GlobalTheory.ClosureRR.h0_ge_of_lt_interNumRed | exact GlobalTheory.ClosureRR.h0_ge_of_lt_interNumRed | (intros; apply GlobalTheory.ClosureRR.h0_ge_of_lt_interNumRed <;> assumption)
end
