module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2702
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2703
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.InterNumConsEqCokernel
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2937
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1746
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1619
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1776
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2913
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2914
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarSmul
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2916
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproxOrbitSumsOfGaloisClassSums
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2683
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.SymCmp

theorem grpPullback_id {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem spMap_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem sec_eq_of_f {X : Scheme.{0}} {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  cases s; cases s'
  simp only [LB.Sec.mk.injEq]
  exact funext h

theorem pullS_pullS {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB) (a : ℤ) {T T' T'' : Over S}
    (h : T' ⟶ T) (h' : T'' ⟶ T') (s : LB.Sec (LPow G L a T)) :
    VVRank.pullS G a h' (VVRank.pullS G a h s) = VVRank.pullS G a (h' ≫ h) s := by
  refine sec_eq_of_f (sec_ext_val hL (fun y J hJ => ?_))
  refine (VVRank.sv_pullS G a h' _ (𝟙 _) y hJ).trans ((VVRank.sv_pullS G a h s _ y hJ).trans ?_)
  refine Eq.trans ?_ (VVRank.sv_pullS G a (h' ≫ h) s (𝟙 _) y hJ).symm
  rw [MonoidalCategory.comp_whiskerRight, Over.comp_left, Category.assoc]

theorem thList_ext_perm : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S) (θ : SecAt G L x), Odd m → IsUnit (m : R) → PolFib G L g x → ∀ (K F : Type) [Field K] [Field F] (i : R →+* K) (i' : R →+* F) (φ : K →+* F), φ.comp i = i' → ∀ (N : ℕ) (pt : Fin N → (Over.mk (spMap i ≫ x) ⟶ G)) (c : Fin N → K) (pt' : Fin N → (Over.mk (spMap i' ≫ x) ⟶ G)) (c' : Fin N → F), ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt c → ThList G L ρ m (spMap i' ≫ x) (SecAt.pull G L θ i') pt' c' → ∃ σ : Equiv.Perm (Fin N), ∀ b, c' b = φ (c (σ b)) := by
  intro S G _ _ L ρ hL hρ g m R _ x θ hm hu hP K F _ _ i i' φ hi N pt c pt' c' H H'
  subst hi
  obtain ⟨p₁, -, h₁⟩ := GlobalTheory.T.isThetaConstantListOfFibre_pullback_field_extension S G L ρ hL hρ m N K F φ (spMap i ≫ x) (SecAt.pull G L θ i) pt c H
  simp only [SecAt.pull] at h₁
  rw [pullS_pullS G hL] at h₁
  have ey : spMap φ ≫ spMap i ≫ x = spMap (φ.comp i) ≫ x := by
    rw [← Category.assoc, spMap_comp_ringHom]
  have key : ∀ {y y' : Sp F ⟶ S} (e : y = y') (u : Over.mk y ⟶ Over.mk x) (u' : Over.mk y' ⟶ Over.mk x),
      u.left = u'.left → ∀ {p : Fin N → (Over.mk y ⟶ G)} {d : Fin N → F},
      ThList G L ρ m y (VVRank.pullS G _ u θ) p d →
      ∃ p' : Fin N → (Over.mk y' ⟶ G), ThList G L ρ m y' (VVRank.pullS G _ u' θ) p' d := by
    intro y y' e u u' hu p d h
    subst e
    obtain rfl : u = u' := Over.OverMorphism.ext hu
    exact ⟨p, h⟩
  obtain ⟨q₁, H₁⟩ := key ey _ (Over.homMk (spMap (φ.comp i)) rfl : Over.mk (spMap (φ.comp i) ≫ x) ⟶ Over.mk x)
    (by simp only [Over.comp_left, Over.homMk_left]; rw [spMap_comp_ringHom]) h₁
  have hPy : PolFib G L g (spMap (φ.comp i) ≫ x) :=
    (GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback S S G L G L (𝟙 S) (𝟙 G.left) hL hL (grpPullback_id G)
      (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hL) g R x).2 F (φ.comp i) hP
  have hmF : (m : F) ≠ 0 := by
    rw [← map_natCast (φ.comp i) m]
    exact (hu.map (φ.comp i)).ne_zero
  exact (GlobalTheory.T.thetaConstantLists_unique_up_to_perm_scalar S G L ρ hL hρ g m m N N F (spMap (φ.comp i) ≫ x) hm hmF hm hmF hPy).1 _ q₁ pt' _ c' H₁ H'

end GlobalTheory.UMin.SymCmp
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PrincDegZero

theorem log_card_eq (κ : Type) [Field κ] [Finite κ] (V : Type) [AddCommGroup V] [Module κ V] :
    Real.log (Nat.card V) = Module.finrank κ V * Real.log (Nat.card κ) := by
  by_cases h : Module.Finite κ V
  · have : Finite V := Module.finite_of_finite κ
    rw [Module.natCard_eq_pow_finrank (K := κ)]
    push_cast
    rw [Real.log_pow]
  · rw [Module.finrank_of_not_finite h]
    have : Infinite V := by
      by_contra h'
      have := not_infinite_iff_finite.1 h'
      exact h (Module.Finite.of_finite)
    simp [Nat.card_eq_zero_of_infinite]

theorem log_card_residueField {κ : Type} [Field κ] [Finite κ] {Y : Scheme.{0}} [IsIntegral Y] [Algebra κ Γ(Y, ⊤)]
    [LocallyOfFiniteType (strHom κ (X := Y))] (hd : topologicalKrullDim Y = (0 + 1 : ℕ)) {z : Y}
    (hz : Order.coheight z = 1) :
    Real.log (Nat.card (Y.residueField z)) =
      (interNumRed κ (⟨closure {z}, isClosed_closure⟩ : Closeds Y) (Fin.elim0 : Fin 0 → LB Y) : ℝ) *
        Real.log (Nat.card κ) := by
  have hdim := VdmRec.CutSec.dim_closure_of_coheight_field (strHom κ Y) hd hz
  obtain ⟨W, j, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
  have hrange : Set.range j = closure {j (genericPoint W)} := by
    rw [← Set.image_singleton, j.isClosedEmbedding.closure_image_eq, (genericPoint_spec _).def, Set.image_univ]
  letI := algebraΓAlong κ j
  have hW : topologicalKrullDim W = (0 : ℕ) :=
    (topologicalKrullDim_eq_of_isEmbedding j.isClosedEmbedding.isEmbedding hrange).symm.trans hdim
  rw [InterModel.interNumRed_eq_interNumOn _ j _ hrange,
    interNumOn_eq_interNum_pull (appTop_algebraMap_along κ j) (fun i => i.elim0), interNum_of_isEmpty]
  have hu (w : W) : w = genericPoint W := by
    have := Order.krullDim_nonpos_iff_forall_isMax.1 (show Order.krullDim (IrreducibleCloseds W) ≤ 0
      from hW.le) ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩
    exact IsGenericPoint.eq (Set.eq_univ_of_univ_subset (@this
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ W, isClosed_univ⟩ (Set.subset_univ _))) (genericPoint_spec W)
  have hZ : ({genericPoint W} : Set W) = Set.univ := Set.eq_univ_of_forall hu
  have hc : IsClosed ({genericPoint W} : Set W) := hZ ▸ isClosed_univ
  have := isClosed_singleton_iff_isClosedImmersion.1 hc
  have : Surjective (W.fromSpecResidueField (genericPoint W)) :=
    ⟨fun w => ⟨IsLocalRing.closedPoint _, (hu _).trans (hu w).symm⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective (W.fromSpecResidueField (genericPoint W))
  have : IsAffine W := .of_isIso (inv (W.fromSpecResidueField (genericPoint W)))
  have : IsIso (W.fromSpecResidueField (genericPoint W)).appTop := inferInstanceAs (IsIso (Scheme.Hom.app _ ⊤))
  have b₁ : Function.Bijective (j.residueFieldMap (genericPoint W)) := by
    refine ⟨RingHom.injective _, fun a => ?_⟩
    obtain ⟨a, rfl⟩ := W.residue_surjective _ a
    obtain ⟨b, rfl⟩ := j.stalkMap_surjective _ a
    exact ⟨Y.residue _ b, by rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]⟩
  have b₂ : Function.Bijective ((W.fromSpecResidueField (genericPoint W)).appTop ≫
      (Scheme.ΓSpecIso (W.residueField (genericPoint W))).hom) := ConcreteCategory.bijective_of_isIso _
  have e : Γ(W, ⊤) ≃ Y.residueField (j (genericPoint W)) :=
    (Equiv.ofBijective _ b₂).trans (Equiv.ofBijective _ b₁).symm
  rw [← Nat.card_congr e, chi_structureModule_of_isAffine, log_card_eq κ]
  push_cast
  ring

end GlobalTheory.PrincDegZero

namespace GlobalTheory.PrincDegZero

theorem finsum_ord_mul_log_card_eq_zero : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → topologicalKrullDim Y = (1 : ℕ) → ∀ (l : ℕ) [Fact l.Prime] [Algebra (ZMod l) Γ(Y, ⊤)] (f : Y.functionField), f ≠ 0 → ∑ᶠ z, (Scheme.ord f z : ℝ) * Real.log (Nat.card (Y.residueField z)) = 0 := by
  intro k _ Y _ _ q hA hd l _ _ f hf
  have : Module.Finite ℤ k := hA.finite
  have : AlgebraicGeometry.IsNoetherian Y := hA.isNoetherian
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨hpr, H, hH⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hA.isProjOver
  have hp : IsProjOver (strHom (ZMod l) (X := Y)) := by
    have : IsFinite (spMap (Int.castRingHom k)) := by
      rw [spMap, IsFinite.SpecMap_iff]
      exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
    have e : strHom (ZMod l) Y ≫ spMap (Int.castRingHom (ZMod l)) = q ≫ spMap (Int.castRingHom k) :=
      specZIsTerminal.hom_ext _ _
    have : IsProper (strHom (ZMod l) Y ≫ spMap (Int.castRingHom (ZMod l))) := by rw [e]; infer_instance
    have : IsProper (strHom (ZMod l) (X := Y)) := IsProper.of_comp _ (spMap (Int.castRingHom (ZMod l)))
    exact (isProjOver_iff_isProper_and_exists_isAmpleLB _).2 ⟨this, H, hH⟩
  have : IsProper (strHom (ZMod l) (X := Y)) := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  have hd' : topologicalKrullDim Y = (0 + 1 : ℕ) := hd
  let r : (LB.triv Y).ι → Y.functionFieldˣ := fun _ => Units.mk0 f hf
  have hr : IsRatSec (LB.triv Y) r := fun _ _ h => by simp [r]
  have hM := LB.isLB_triv Y
  have key := GlobalTheory.ratSec_cycle_formula (ZMod l) Y hp 0 hd.le (LB.triv Y) hM Fin.elim0 (fun i => i.elim0) r hr
  rw [interNum_eq_zero_of_cls_eq_zero (ZMod l) _ (isLB_cons hM fun i => i.elim0) 0 (cls_triv _)] at key
  have hm (z : Y) : (divOfRatSec hM hr).mult z = Scheme.ord f z :=
    ((presents_divOfRatSec hM hr).isEqn PUnit.unit z trivial).mult_eq
  have hfin : Function.HasFiniteSupport fun w => (divOfRatSec hM hr).mult w *
      interNumRed (ZMod l) (⟨closure {w}, isClosed_closure⟩ : Closeds _) (Fin.elim0 : Fin 0 → LB Y) :=
    (CartierDiv.finite_support_mult _).subset (Function.support_mul_subset_left _ _)
  have em := (AddMonoidHom.mulRight (Real.log (Nat.card (ZMod l)))).comp (Int.castAddHom ℝ) |>.map_finsum hfin
  rw [← key] at em
  simp only [map_zero] at em
  refine (finsum_congr fun z => ?_).trans em.symm
  change (Scheme.ord f z : ℝ) * _ = (((divOfRatSec hM hr).mult z * _ : ℤ) : ℝ) * _
  rw [hm]
  by_cases hz : Scheme.ord f z = 0
  · simp [hz]
  have hc : Order.coheight z = 1 := by
    by_contra h
    exact hz (Scheme.ord_eq_zero_of_coheight_neq_one h f)
  rw [Int.cast_mul, mul_assoc, log_card_residueField (κ := ZMod l) hd' hc]

end GlobalTheory.PrincDegZero
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

set_option autoImplicit false

theorem mixRecVal_cons_eq_resCyc_sub_resArch {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} (hA : IsAmb q) {e : ℕ} (hdim : topologicalKrullDim Y = (e + 1 + 1 : ℕ))
    {T : ∀ d : ℕ, (Fin d → HermLB q) → Y → ℝ} (hT : IsMix q (e + 1) T) (N : HermLB q) (L : Fin e → HermLB q)
    (t : N.B.Sec) {z : Y} (hz : Order.coheight z = 1) (hzt : z ∈ nonzeroLocus t) :
    T (e + 1) (Fin.cons N L) z = resCyc N.isLB t (T e L) z - resArch L N t z := by
  have hg : genericPoint (clo z) ∈ nonzeroLocus (secPull t (cloι z)) := by
    rw [GlobalTheory.nonzeroLocus_secPull]
    show cloι z (genericPoint (clo z)) ∈ nonzeroLocus t
    rw [cloι_genericPoint]
    exact hzt
  have hd : topologicalKrullDim (clo z) = ((e + 1 : ℕ) : WithBot ℕ∞) :=
    ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Y q hA (e + 1) hdim).2 z (genericPoint (clo z)) hz).1
  have h := hT.recur (clo z) (cloι z ≫ q) (cloι z) rfl e le_rfl hd N L (N.restr (cloι z))
    (fun a => (L a).restr (cloι z)) (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) _
    (isRatSec_ratOfSec _ hg)
  rw [cloι_genericPoint] at h
  rw [h, resCyc, resArch, dite_eq_left hg, dite_eq_left hg]
  rfl

end GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem finite_support_mult_mul {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [CompactSpace Y]
    (D : CartierDiv Y) (g : Y → ℝ) : (Function.support fun z => (D.mult z : ℝ) * g z).Finite :=
  D.finite_support_mult.subset fun z hz => by
    simp only [Function.mem_support] at hz ⊢
    intro h
    simp [h] at hz

theorem recVal_cons_recip : ArchRecip → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ T, IsMix q (e + 1) T → ∀ (M N : HermLB q) (L : Fin e → HermLB q) (s : M.B.Sec) (t : N.B.Sec) (hs : genericPoint Y ∈ nonzeroLocus s) (ht : genericPoint Y ∈ nonzeroLocus t), (∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M (isRatSec_ratOfSec s hs) = recVal (T (e + 1) (Fin.cons M L)) (Fin.cons M L : Fin (e + 1) → HermLB q) N (isRatSec_ratOfSec t ht) := by
  intro hAR k _ Y _ _ q hA e hdim T hT M N L s t hs ht hcov
  have : IsNoetherian Y := hA.isNoetherian
  have key (A B : HermLB q) (a : A.B.Sec) (b : B.B.Sec) (ha : genericPoint Y ∈ nonzeroLocus a)
      (hab : ∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus a ∨ z ∈ nonzeroLocus b) (z : Y) :
      ((divOfSec A.isLB a ha).mult z : ℝ) * T (e + 1) (Fin.cons B L) z =
        ((divOfSec A.isLB a ha).mult z : ℝ) * resCyc B.isLB b (T e L) z -
          ((divOfSec A.isLB a ha).mult z : ℝ) * resArch L B b z := by
    by_cases h0 : (divOfSec A.isLB a ha).mult z = 0
    · simp [h0]
    · have hz := CartierDiv.coheight_eq_one_of_mult_ne_zero h0
      have hza : z ∉ nonzeroLocus a := fun h =>
        (notMem_supp_divOfSec.2 h) (CartierDiv.mem_supp_of_mult_ne_zero h0)
      rw [mixRecVal_cons_eq_resCyc_sub_resArch hA hdim hT B L b hz ((hab z hz).resolve_left hza), mul_sub]
  have hL : recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M (isRatSec_ratOfSec s hs) =
      (∑ᶠ z, ((divOfSec M.isLB s hs).mult z : ℝ) * resCyc N.isLB t (T e L) z -
        ∑ᶠ z, ((divOfSec M.isLB s hs).mult z : ℝ) * resArch L N t z) -
        mixArch (Fin.cons N L : Fin (e + 1) → HermLB q) M (isRatSec_ratOfSec s hs) := by
    rw [recVal, finsum_congr (key M N s t hs hcov), finsum_sub_distrib (finite_support_mult_mul _ _)
      (finite_support_mult_mul _ _)]
  have hR : recVal (T (e + 1) (Fin.cons M L)) (Fin.cons M L : Fin (e + 1) → HermLB q) N (isRatSec_ratOfSec t ht) =
      (∑ᶠ z, ((divOfSec N.isLB t ht).mult z : ℝ) * resCyc M.isLB s (T e L) z -
        ∑ᶠ z, ((divOfSec N.isLB t ht).mult z : ℝ) * resArch L M s z) -
        mixArch (Fin.cons M L : Fin (e + 1) → HermLB q) N (isRatSec_ratOfSec t ht) := by
    rw [recVal, finsum_congr (key N M t s ht fun z hz => (hcov z hz).symm),
      finsum_sub_distrib (finite_support_mult_mul _ _) (finite_support_mult_mul _ _)]
  have hC := GlobalTheory.T.iteratedWeilDivisorSum_symm_no_common_divisor k Y q hA M.B N.B M.isLB N.isLB s t hs ht hcov (T e L)
  rw [hL, hR, hC]
  rcases GlobalTheory.T.projArithAmbient_vertical_or_arithmeticVariety k Y q hA (e + 1 + 1) hdim with ⟨l, _, _, hno⟩ | ⟨e', he', hav⟩
  · have z₀ := GlobalTheory.T.mixedArch_restricted_eq_zero_of_no_complexPoints k Y q hno
    rw [(z₀ (e + 1) (Fin.cons N L) M).1, (z₀ (e + 1) (Fin.cons M L) N).1]
    simp only [(z₀ e L N).2, (z₀ e L M).2, mul_zero, finsum_zero]
  · obtain rfl : e' = e + 1 := by omega
    have hA' := hAR k Y q e hav M N L s t hs ht hcov
    linarith

end GlobalTheory.MixHt
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

theorem _root_.GlobalTheory.T.flagRefinementBundle_dim_eq_base_add_card_aboveDiagonal : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → Y.dim = X.dim + Fintype.card (Cell m) := by
  first | exact @GlobalTheory.FlagCell2.Dim.main | exact GlobalTheory.FlagCell2.Dim.main | (intros; apply GlobalTheory.FlagCell2.Dim.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ThetaRegularizationComparison


open GlobalTheory.RegCompare in
theorem thetaInt_wop_intg {D : D7} {M X : HSp D} {ω : GlobalTheory.Grid.WRep M X} {ν : Measure (GA D M)} {𝓕 : Set (GA D M)}
    (hν : IsHaarFD M ν 𝓕) {Φ : WO M X → ℂ} (hL : ∀ γ ∈ GQ M, ∀ g h, thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ)
    (hΦ : Intg ω ν 𝓕 Φ) (z : GA D M →₀ ℂ) : thetaInt ω ν 𝓕 (wop ω z Φ) = zdeg z • thetaInt ω ν 𝓕 Φ := by
  haveI := hν.1
  have key := fun h k => setIntegral_mul_right' M ν 𝓕 hν.2 (fun g => thetaKO ω g h Φ)
    (fun γ hγ u => hL γ hγ u h) (hΦ h) k
  have hi : ∀ k, Intg ω ν 𝓕 (ω (k, 1) Φ) := fun k h => by simpa only [thetaKO_right] using (key h k).1
  have he : ∀ k, thetaInt ω ν 𝓕 (ω (k, 1) Φ) = thetaInt ω ν 𝓕 Φ := fun k => by
    funext h
    simp only [thetaInt, thetaKO_right]
    exact (key h k).2
  rw [wop_apply, thetaInt_sum _ fun k _ => (hi k).smul _]
  simp only [thetaInt_smul, he, zdeg, Finsupp.sum, Finset.sum_smul]


theorem tmul_cancel_left {P Q : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] {x : P} (hx : x ≠ 0) {u u' : Q}
    (h : x ⊗ₜ[ℂ] u = x ⊗ₜ[ℂ] u') : u = u' := by
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hx
  have := congrArg (TensorProduct.lid ℂ Q ∘ LinearMap.rTensor Q l) h
  simpa [hl] using this

theorem tmul_cancel_right {P Q : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] {y : Q} (hy : y ≠ 0) {u u' : P}
    (h : u ⊗ₜ[ℂ] y = u' ⊗ₜ[ℂ] y) : u = u' :=
  tmul_cancel_left hy (by simpa using congrArg (TensorProduct.comm ℂ P Q) h)

theorem eq_of_regConst (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}
    {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) {W : G.Weil} {B : Frames G} {ρ : RealMatch W} {t : T} {i j : Fin D.R.m}
    (hst : SquareStanding G t) {M : Vol G} (hM : M.Is t) {Θ Θ'} (hΘ : IsMatched B t ρ i j Θ Θ') {g g₁}
    (hne : ∫ u in M.fd _, kerBig W Θ g g₁ u ∂M.ν _ ≠ 0) {z} (hz : zdeg z ≠ 0)
    (hi : IntegrableOn (translates z (kerSmall W Θ' g g₁)) (M.fd _) (M.ν _)) {c c₀ : ℂ}
    (hc : zdeg z * ∫ u in M.fd _, kerBig W Θ g g₁ u ∂M.ν _ = c * ∫ u in M.fd _, translates z (kerSmall W Θ' g g₁) u ∂M.ν _)
    (h₀ : RegConst W B ρ t i j c₀) : c₀ = c := by
  obtain ⟨J, hJ⟩ := reg_const hK hL W B ρ t i j hst M hM Θ Θ' hΘ g g₁
  obtain ⟨z₀, hz₀, ⟨-, hi₀⟩, e₀⟩ := h₀ M hM Θ Θ' hΘ g g₁
  rw [hJ z hi] at hc
  rw [hJ z₀ hi₀] at e₀
  have e1 : ∫ u in M.fd _, kerBig W Θ g g₁ u ∂M.ν _ = c * J := mul_left_cancel₀ hz (by linear_combination hc)
  have e2 : ∫ u in M.fd _, kerBig W Θ g g₁ u ∂M.ν _ = c₀ * J := mul_left_cancel₀ hz₀ (by linear_combination e₀)
  have hJ0 : J ≠ 0 := fun h => hne (by rw [e1, h, mul_zero])
  exact mul_right_cancel₀ hJ0 (e2.symm.trans e1)


end GlobalTheory.ThetaRegularizationComparison

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.keyValue_unit_uniformised_of_absValueOne : ∀ κ : Rule, MBLow.KapF κ → KeyTraitU κ := by
  first | exact @GlobalTheory.KeyEven.keyTraitU_of_kapF | exact GlobalTheory.KeyEven.keyTraitU_of_kapF | (intros; apply GlobalTheory.KeyEven.keyTraitU_of_kapF <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.approx_orbitSums_of_galois_classSums : ∀ (O : Type) [CommRing O] (bar : O → O) (q p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] (Φ : FPre bar q p A) (s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (N₁ N : ℕ) (y₀ : Φ.Y) (k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) (Q : Type) (t : ∀ y, (Fin s → Φ.X y) → Q → PadicAlgCl p) (B : Type) [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B] [Finite (B ≃ₐ[A] B)], Function.Injective (algebraMap A B) → (∀ b : B, (∀ σ : B ≃ₐ[A] B, σ b = b) → b ∈ Set.range (algebraMap A B)) → ∀ 𝔷 : Ideal B, 𝔷.IsMaximal → 1 ≤ N → PosW W → (∀ y, IsUnimodMod O N (k y)) → Φ.ClassSums N₁ N y₀ k t B 𝔷 → Φ.OrbitSums W N₁ N y₀ k t := by
  first | exact @GlobalTheory.Poinc.OrbTrace.orbitSums_of_classSums | exact GlobalTheory.Poinc.OrbTrace.orbitSums_of_classSums | (intros; apply GlobalTheory.Poinc.OrbTrace.orbitSums_of_classSums <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem Trait.dim_add_rank : ∀ {g n : ℕ}, 2 ≤ n → ∀ (F : SFam g n (zetaAway n)) (T : GlobalTheory.Poinc.Trait F),
    T.D.toPre.P.g + Module.finrank ℤ T.D.toPre.X = g := by
  intro g n hn F T
  have hn0 : n ≠ 0 := by omega
  have hζ : IsUnit (zetaAway n) := by rw [← cycBase_ζ hn0]; exact Units.isUnit _
  have hd : SmoothOfRelativeDimension g F.univ.A.hom :=
    GlobalTheory.SiegSharpCover.smoothDim F.univ hn hζ (isUnit_natCast hn0)
  have hA : SmoothOfRelativeDimension g T.A.A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback T.cart.1 hd
  have e : T.A.g = g :=
    H1.dim_unique _ T.A.smoothDim hA ((η[T.A.A]).left (IsLocalRing.closedPoint _))
  have hR : AdmBase T.V (maximalIdeal T.V) := ⟨inferInstance, inferInstance, inferInstance, T.complete⟩
  have h := GlobalTheory.TateUnif.rank_add_dim hR T.semi T.U
  omega

end GlobalTheory.Poinc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.sharpOver_of_polarized_pullback : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (T T' : Scheme.{0}) (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (f : T' ⟶ T) (φ : P'.A.left ⟶ P.A.left), SharpOver F W P u → IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → SharpOver F W P' (f ≫ u) := by
  first | exact @GlobalTheory.Poinc.sharpOver_baseChange | exact GlobalTheory.Poinc.sharpOver_baseChange | (intros; apply GlobalTheory.Poinc.sharpOver_baseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.keyValue_unit_traits_of_uniformised_traits : ∀ κ : Rule, KeyTraitU κ → KeyTrait κ := by
  first | exact @GlobalTheory.KeyEven.keyTrait_of_keyTraitU | exact GlobalTheory.KeyEven.keyTrait_of_keyTraitU | (intros; apply GlobalTheory.KeyEven.keyTrait_of_keyTraitU <;> assumption)
end
