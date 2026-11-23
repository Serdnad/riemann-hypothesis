module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PrimitiveCocycle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPointsOpenIntegralCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle154
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle013
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNonvanishing
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueDescendOfTorsionInvariant
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle093
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle097
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle155
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.EmbLocal

open ReciprocityTheory.ChartRestriction.G.Out

variable {S : Scheme.{0}}

theorem exists_isGenSec_near (hS : SecBaseChangeAnySt) (P : PolAV S) (x : S) :
    ∃ V : S.Opens, x ∈ V ∧ ∀ (R : Type) [CommRing R] (q : Sp R ⟶ S), Set.range q ⊆ V →
      ∃ th, IsGenSec P.A P.L 1 (T := Over.mk q) th := by
  obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl x
  have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  let T : Over S := overRes (T := baseOver S) V
  have hT : T.hom = V.ι := Category.comp_id _
  haveI : IsOpenImmersion T.hom := by rw [hT]; exact inferInstanceAs (IsOpenImmersion V.ι)
  refine ⟨V, hV, fun R _ q hqV => ?_⟩
  obtain ⟨t, rfl⟩ : ∃ t : Spec (CommRingCat.of R) ⟶ T.left, t ≫ T.hom = q :=
    ⟨IsOpenImmersion.lift T.hom q (by rw [hT]; exact hqV.trans (Scheme.Opens.range_ι V).ge),
      IsOpenImmersion.lift_fac _ _ _⟩
  choose b' hb' using fun i =>
    PushInv.exists_pull P.A P.L (1 : ℕ) (homAt t ▷ P.A) (whiskerRight_snd (homAt t) P.A) (b i)
  obtain ⟨-, hsp⟩ := hb R t b' hb'
  refine ⟨b' hq.default, fun s => ?_⟩
  rw [Set.range_unique] at hsp
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 (hsp.ge (Submodule.mem_top (x := SecM.ofSec P.A s)))
  exact ⟨r, fun j => (congrArg (fun q => q.1 j) hr).symm⟩

theorem exists_mulPull (hG : GlobalFnsSt) (P : PolAV S) (k : ℕ) (T : Over S) :
    ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ k).left] ![(k : ℤ) ^ 2, -1]),
      α.IsGen := by
  obtain ⟨α₀, hα₀⟩ := (MulPull.mulPull_of_cube_of_symm AbLaw.CubeAssembly.cube_gen (exists_gen_negLB hG)).1 S P k
  have e₁ : (snd T P.A).left ≫ (mulA P.A k).left = (snd T P.A ^ k).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨α, hα, -⟩ := exists_gen P.isLB (φ' := ![(snd T P.A).left, (snd T P.A ^ k).left])
    (ε' := ![(k : ℤ) ^ 2, -1])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ ((k : ℤ) ^ 2)) (Category.comp_id _)
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen P.L ![𝟙 P.A.left, (mulA P.A k).left] ![(k : ℤ) ^ 2, -1] α₀ (snd T P.A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  exact ⟨α, hα⟩

theorem exists_symLift_near (hG : GlobalFnsSt) (P : PolAV S) {k : ℕ} (hk : Odd k) {T : Over S} (y : T ⟶ P.A)
    (hy : y ^ k = 1) (p : T.left) :
    ∃ V : T.left.Opens, p ∈ V ∧ ∀ (T' : Over S) (h : T' ⟶ T), Set.range h.left ⊆ V →
      ∃ θ : ThetaGrp P.A P.L k T', SymLift P.A P.L k k (h ≫ y) θ := by
  obtain ⟨V, hV, θ, hθ⟩ := ((symLift_odd hG
    (kerPow_of_square (AbSquare.square_of_cube AbLaw.CubeAssembly.cube_gen).1).2.2 (exists_gen_negLB hG)).1
      S P k hk T y hy).1 p
  refine ⟨V, hV, fun T' h hh => ?_⟩
  have hr : Set.range h.left ⊆ Set.range V.ι := hh.trans (Scheme.Opens.range_ι V).ge
  let l : T' ⟶ overRes V := Over.homMk (IsOpenImmersion.lift V.ι h.left hr) (by
    show IsOpenImmersion.lift V.ι h.left hr ≫ V.ι ≫ T.hom = T'.hom
    rw [IsOpenImmersion.lift_fac_assoc, Over.w h])
  have e : l ≫ overResι V = h := Over.OverMorphism.ext (IsOpenImmersion.lift_fac V.ι h.left hr)
  obtain ⟨θ', hθ'⟩ := GlobalLift.exists_symLift_pull P.isLB l hθ
  exact ⟨θ', by rw [← e, Category.assoc]; exact hθ'⟩

theorem exists_affine_nhds {R : Type} [CommRing R] (W : (Sp R).Opens) (p : Sp R) (hp : p ∈ W) :
    ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R'), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧
      Set.range (spMap φ) ⊆ W := by
  obtain ⟨_, ⟨r, rfl⟩, hr, hW⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (u := W.1) hp W.isOpen
  have e : Set.range (spMap (algebraMap R (Localization.Away r))) = (PrimeSpectrum.basicOpen r).1 :=
    PrimeSpectrum.localization_away_comap_range (R := R) (Localization.Away r) r
  refine ⟨Localization.Away r, inferInstance, algebraMap _ _, ?_, e.ge hr, e.le.trans hW⟩
  exact inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))))

theorem lab_pow {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o} (t : TObj g k J b s)
    (a : Ix g k) : t.lab a ^ k = 1 := by
  have := t.ab.comm
  rw [TObj.lab, linComb, List.prod_ofFn, ← Finset.prod_pow]
  exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul, t.torsion, one_pow]

end GlobalTheory.EmbLocal

namespace GlobalTheory

open EmbLocal

theorem exists_emb_locally : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S), Odd N' → m ∣ N' → ∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R') (σ : _), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ t.Emb m (Over.mk (spMap φ ≫ x)) σ := by
  intro hL hL2 o _ g N' J b S s t m R _ x hN hm p
  have hmo : Odd m := hN.of_dvd_nat hm
  haveI : NeZero (N' ^ 2) := ⟨pow_ne_zero 2 hN.pos.ne'⟩
  let u : Over.mk x ⟶ Out.baseOver S := Over.homMk x (by simp)
  have hy : ∀ a, ((u ≫ t.lab a) ^ ((N' / m) ^ 2)) ^ (m ^ 2) = 1 := fun a => by
    rw [← pow_mul, ← mul_pow, Nat.div_mul_cancel hm, ← MonObj.comp_pow, lab_pow, MonObj.comp_one]
  obtain ⟨V, hV, hth⟩ := exists_isGenSec_near hL2.secBaseChangeAny t.pol (x p)
  choose W hW hU using fun a => exists_symLift_near hL.globalFns t.pol (k := m ^ 2) hmo.pow
    (T := Over.mk x) _ (hy a) p
  obtain ⟨R', _, φ, hφ, hp, hsub⟩ := exists_affine_nhds
    (x ⁻¹ᵁ V ⊓ ⟨⋂ a, (W a).1, isOpen_iInter_of_finite fun a => (W a).isOpen⟩) p
    ⟨hV, Set.mem_iInter.2 hW⟩
  let T : Over S := Over.mk (spMap φ ≫ x)
  let h : T ⟶ Over.mk x := Over.homMk (spMap φ) rfl
  obtain ⟨th, hth⟩ := hth R' (spMap φ ≫ x) (by
    rintro _ ⟨z, rfl⟩
    exact (hsub ⟨z, rfl⟩).1)
  obtain ⟨α, hα⟩ := exists_mulPull hL.globalFns t.pol m T
  obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull t.isLB (Out.mulT t.A T m) (snd T t.A ^ m) (lift_snd _ _)
    ((m : ℤ) ^ 2) 1 α hα th
  have hU' : ∀ a, ∃ θ : Out.ThetaGrp t.A t.L ((m : ℤ) ^ 2) T, Out.SymLift t.A t.L ((m : ℤ) ^ 2) (m ^ 2)
      (((Over.homMk T.hom (by simp) : T ⟶ Out.baseOver S) ≫ t.lab a) ^ ((N' / m) ^ 2)) θ := fun a => by
    obtain ⟨θ, hθ⟩ := hU a T h fun z hz => Set.mem_iInter.1 (hsub hz).2 a
    rw [← Nat.cast_pow]
    refine ⟨θ, ?_⟩
    have e : h ≫ (u ≫ t.lab a) ^ ((N' / m) ^ 2) =
        ((Over.homMk T.hom (by simp) : T ⟶ Out.baseOver S) ≫ t.lab a) ^ ((N' / m) ^ 2) := by
      rw [MonObj.comp_pow, ← Category.assoc]; rfl
    rw [← e]
    exact hθ
  choose U hU' using hU'
  choose σ hσ using fun a => ThetaPtExist.exists_isTwistPull t.isLB (Out.translT t.A (U a).pt)
    (Out.translPt t.A (U a).pt) (lift_snd _ _) ((m : ℤ) ^ 2) ((m : ℤ) ^ 2) (U a).φ (U a).isGen s₁
  exact ⟨R', inferInstance, φ, σ, hφ, hp, th, s₁, α, U, hth, hα, hs₁, hU', hσ⟩

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem _root_.GlobalTheory.T.generic_points_open_integral_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (O : Type) [CommRing O] [IsNoetherianRing O] (MM : Scheme.{0}) (sM : MM ⟶ Sp O) (tM : SAB H MM) (m : ℕ), IsReduced MM → LocallyOfFiniteType sM → QuasiCompact sM → (∀ ξ ∈ genericPoints MM, ∃ (V : Scheme.{0}) (i : V ⟶ MM) (tV : SAB H V) (_ : SABMap tV tM i) (C : ZOn (i ≫ sM) tV m), IsOpenImmersion i ∧ ξ ∈ Set.range i ∧ IsIntegral V ∧ IsIntegral C.Z ∧ C.amp.s = 1 ∧ ∀ r : ℤ, C.amp.r ≤ r → ∃ A : GlobalTheory.LN.AmpFrames C.t.G C.t.PP.L (m ^ 2), A.r = r ∧ A.s = 1) → (∃ g, SmoothOfRelativeDimension g tM.G.hom) → Out.Laws → Out.Laws2 → IsProper tM.G.hom → Out.RelAmple tM.G tM.PP.L → Out.KTriv tM.G tM.PP.L → Nonempty (ZOn sM tM m) := by
  first | exact @GlobalTheory.Models.nonempty_zOn_of_components | exact GlobalTheory.Models.nonempty_zOn_of_components | (intros; apply GlobalTheory.Models.nonempty_zOn_of_components <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.relAmple_specialFibre_extended_principalPolarisation : Laws → Laws2 → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → IsAdicComplete (IsLocalRing.maximalIdeal V) V → RelAmple ((Over.pullback (spMap (IsLocalRing.residue V))).obj B) (M.L.L.pull (pullback.fst B.hom (spMap (IsLocalRing.residue V)))) := by
  first | exact @GlobalTheory.SpecialAmple.relAmple_special_fibre | exact GlobalTheory.SpecialAmple.relAmple_special_fibre | (intros; apply GlobalTheory.SpecialAmple.relAmple_special_fibre <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.TorsionTranslation

open Out CommutatorPairing PrimCocycle CechPic

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem transl_mulA (k : ℕ) (y : 𝟙_ (Over S) ⟶ A) (hy : y ^ k = 1) :
    ((toUnit A ≫ y) * 𝟙 A).left ≫ (mulA A k).left = (mulA A k).left := by
  rw [← Over.comp_left, mulA, MonObj.comp_pow, Category.comp_id, mul_pow, ← MonObj.comp_pow, hy,
    MonObj.comp_one, _root_.one_mul]

theorem exists_character (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {X : Scheme.{0}} {M : LB X} (hM : M.IsLB)
    {I : Type} [Fintype I] (φ : I → (A.left ⟶ X)) (ε : I → ℤ) (k : ℕ)
    (u : LB.Gen (LB.LinComb M (fun i => (mulA A k).left ≫ φ i) ε)) (hu : u.IsGen) :
    ∃ χ : {y : 𝟙_ (Over S) ⟶ A // y ^ k = 1} → Γ((𝟙_ (Over S)).left, ⊤)ˣ,
      (∀ x y, χ ⟨x.1 * y.1, by rw [mul_pow, x.2, y.2, _root_.one_mul]⟩ = χ x * χ y) ∧
      ∀ y (z : A.left) J, Good M z J →
        val u ((toUnit A ≫ y.1) * 𝟙 A).left z J = val u (𝟙 _) z J * gm (toUnit A).left z ⊤ (χ y) := by
  have he : (1 : 𝟙_ (Over S) ⟶ A).left ≫ (toUnit A).left = 𝟙 _ := by
    rw [← Over.comp_left, comp_toUnit, toUnit_unit]; rfl
  have hp : Function.Surjective (toUnit A).left.appTop.hom := by
    have e : (toUnit A).left = A.hom := (Category.comp_id _).symm.trans (Over.w (toUnit A))
    rw [e]
    exact (hG _ _ hA).2
  have H : ∀ y : {y : 𝟙_ (Over S) ⟶ A // y ^ k = 1}, ∃ c : Γ((𝟙_ (Over S)).left, ⊤)ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ A.left) (z : Z) (J), Good M z J →
        val u (r ≫ ((toUnit A ≫ y.1) * 𝟙 A).left) z J = val u r z J * gm (r ≫ (toUnit A).left) z ⊤ c := by
    intro y
    obtain ⟨c, hc⟩ := exists_ratio hM (fun U _ h => Finset.prod_congr rfl fun i _ => by
        rw [← Category.assoc, transl_mulA k y.1 y.2]) (toUnit A).left _ he hp
      (DVR.pullGen_isGen _ _ _ u hu ((toUnit A ≫ y.1) * 𝟙 A).left) hu
    exact ⟨c, fun Z r z J hJ => (val_pull hJ _ _ _).symm.trans (hc Z r z J hJ)⟩
  choose χ hχ using H
  refine ⟨χ, fun x y => unit_ext fun z _ => ?_, fun y z J hJ => ?_⟩
  · choose J hJ using fun ψ : (𝟙_ (Over S)).left ⟶ X => exists_chart hM (ψ z)
    have a := hχ ⟨x.1 * y.1, by rw [mul_pow, x.2, y.2, _root_.one_mul]⟩ _ (1 : 𝟙_ (Over S) ⟶ A).left z J hJ
    have b := hχ x _ (1 : 𝟙_ (Over S) ⟶ A).left z J hJ
    have c := hχ y _ ((1 : 𝟙_ (Over S) ⟶ A).left ≫ ((toUnit A ≫ x.1) * 𝟙 A).left) z J hJ
    have e₁ : ((toUnit A ≫ x.1) * 𝟙 A).left ≫ ((toUnit A ≫ y.1) * 𝟙 A).left =
        ((toUnit A ≫ (x.1 * y.1)) * 𝟙 A).left := by
      rw [← Over.comp_left, MonObj.comp_mul, MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id,
        ← _root_.mul_assoc, mul_comm (toUnit A ≫ y.1)]
    have e₂ : ((toUnit A ≫ x.1) * 𝟙 A).left ≫ (toUnit A).left = (toUnit A).left := by
      rw [← Over.comp_left, comp_toUnit]
    rw [b, Category.assoc, Category.assoc, e₁, e₂, a, he, _root_.mul_assoc, ← map_mul] at c
    exact mul_left_cancel c
  · have := hχ y _ (𝟙 _) z J hJ
    rwa [Category.id_comp, Category.id_comp] at this

theorem exists_gen_mulA {M : LB A.left} (hM : M.IsLB) (hΘ : ∃ t : LB.Gen (Theta A M), t.IsGen) (k : ℕ)
    (x : 𝟙_ (Over S) ⟶ A) (hx : x ^ k = 1) :
    ∃ u : LB.Gen (LB.LinComb M (fun I : ULift.{0} (Finset (Fin 2)) =>
      (mulA A k).left ≫ (psum A ![toUnit A ≫ x, 𝟙 A] I.down).left) lamε), u.IsGen := by
  refine (cls_eq_zero_iff (LB.isLB_linComb hM _ _)).1 ?_
  have h₁ : (cubeLB A ![toUnit A ≫ x, 𝟙 A] M).IsLB := LB.isLB_linComb hM _ _
  have e := congrArg (CechPic.pull (mulA A k).left) ((cls_linComb hM _ _ h₁).symm.trans (cls_cube_two hM _ _ h₁))

  rw [pull_lam, comp_toUnit_assoc, Category.comp_id, map_sum] at e
  have e' : lam (cls M hM) (toUnit A ≫ x) (mulA A k) = 0 := by
    rw [mulA, lam_pow_right hM hΘ, ← lam_pow_left hM hΘ, ← MonObj.comp_pow, hx, MonObj.comp_one, lam_one_left]
  rw [cls_linComb hM]
  refine Eq.trans (Finset.sum_congr rfl fun I _ => ?_) (e.trans e')
  rw [map_zsmul, pull_comp]

end GlobalTheory.TorsionTranslation

namespace GlobalTheory

open TorsionTranslation PairingDetermines IsoDescent PrimCocycle

theorem exists_torsion_lbIso_cubeLB : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (k : ℕ) (x : 𝟙_ (Over (Sp K)) ⟶ P.A), M.IsLB → (k : K) ≠ 0 → x ^ k = 1 → ∃ y : 𝟙_ (Over (Sp K)) ⟶ P.A, y ^ k = 1 ∧ LBIso (cubeLB P.A ![toUnit P.A ≫ x, 𝟙 P.A] M) (cubeLB P.A ![toUnit P.A ≫ y, 𝟙 P.A] P.L) := by
  intro hL hL' K _ _ P M k x hM hk hx
  haveI : IsCommMonObj P.A := P.isAb.comm
  obtain ⟨u, hu⟩ := exists_gen_mulA hM (AbLaw.CubeAssembly.cube_gen _ P M hM) k x hx
  obtain ⟨χ, hχ, vχ⟩ := exists_character hL.globalFns P.isAb hM _ _ k u hu
  obtain ⟨y, ⟨hy, hw⟩, -⟩ := hL'.charPair K P k hk (fun δ => (χ δ)⁻¹) (fun a b =>
    (congrArg (·⁻¹) (hχ a b)).trans (mul_inv _ _))
  refine ⟨y, hy, ?_⟩
  obtain ⟨u₀, hu₀, v₀⟩ := exists_gen_lam hL.globalFns hL.cube P (𝟙 P.A) 1 k y hy
  obtain ⟨u', hu', v'⟩ := exists_gen P.isLB (φ' := fun I : ULift.{0} (Finset (Fin 2)) =>
      (Out.mulA P.A k).left ≫ (psum P.A ![toUnit P.A ≫ y, 𝟙 P.A] I.down).left) (ε' := lamε)
    (fun U _ h => Finset.prod_congr rfl fun I _ => by
      have e : (lift (toUnit P.A ≫ y) (𝟙 P.A)).left ≫ lamφ P.A I =
          (psum P.A ![toUnit P.A ≫ y, 𝟙 P.A] I.down).left :=
        congrArg (fun q => q.left) ((psum_hom (preHom (lift (toUnit P.A ≫ y) (𝟙 P.A))) (x2 P.A) I.down).trans
          (congrArg (fun q => psum P.A q I.down) (funext fun i => by fin_cases i <;> simp [preHom, x2])))
      rw [Over.id_left, Category.comp_id, e, Nat.cast_one, _root_.mul_one]) u₀ hu₀
  refine lbIso_of_invariant hM P.isLB _ _ _ _ (Out.mulA P.A k).left
    (I := {y : 𝟙_ (Over (Sp K)) ⟶ P.A // y ^ k = 1}) (fun y => ((toUnit P.A ≫ y.1) * 𝟙 P.A).left)
    (fun δ => transl_mulA k δ.1 δ.2)
    (fun U f hf => torsion_invariant_descends (fun S _ P n hn => by
      obtain ⟨a, b, c, e, -⟩ := hL.mulN S P n hn
      exact ⟨a, b, c, e⟩) K P k hk U f fun y hy => hf ⟨y, hy⟩) u hu u' hu'
    (fun δ z J J' hJ hJ' => ?_)
  have w := CommPairing.weilIs_symm P.isLB (hw δ)
  rw [inv_inv] at w
  have h₁ := vχ δ z J hJ
  have h₂ := v₀ δ.1 (χ δ) δ.2 (by rw [Category.comp_id, Category.comp_id]; exact w) z J' hJ'
  rw [pow_one, ← v' _ _ z J' hJ', ← v' _ _ z J' hJ'] at h₂
  refine (congrArg₂ (fun a b => a * b⁻¹) h₂ h₁).trans ?_
  exact mul_div_mul_right_eq_div _ _ _ |> fun h => by simpa only [div_eq_mul_inv] using h

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open CechPic

theorem CechPic.lam_pull_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} {G' T' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (c : Pic G.left) (x y : T' ⟶ G') :
    lam (pull φ c) x y = lam c (pushHom h T' x) (pushHom h T' y) := by
  rw [lam, lam, ← map_mul, ← map_one (pushHom h T')]
  simp only [← pull_comp]
  rfl

theorem adjoint_cubeLB_of_dense_fibres : Out.GlobalFnsSt → ∀ (S : Scheme.{0}) [IsReduced S] (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (u v : A ⟶ A), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → IsMonHom u → IsMonHom v → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (G : Over (Sp K)) (_ : GrpObj G) (_ : IsCommMonObj G) (φ : G.left ⟶ A.left) (L' : LB G.left) (u' v' : G ⟶ G), p ∈ Set.range x ∧ IsGrpPullback G A x φ ∧ L'.IsLB ∧ LBIso L' (L.pull φ) ∧ u'.left ≫ φ = φ ≫ u.left ∧ v'.left ≫ φ = φ ≫ v.left ∧ LBIso (cubeLB G ![fst G G ≫ u', snd G G] L') (cubeLB G ![fst G G, snd G G ≫ v'] L')} → LBIso (cubeLB A ![fst A A ≫ u, snd A A] L) (cubeLB A ![fst A A, snd A A ≫ v] L) := by
  intro hG S _ A _ _ L u v hA hL hamp hu hv hd
  have := hA.smooth
  have : IsReduced A.left := GlobalTheory.isReduced_of_smooth_of_isReduced A.hom
  have hp : IsPullback (snd A A).left (fst A A).left A.hom A.hom :=
    (IsPullback.of_hasPullback A.hom A.hom).flip
  have h₁ : (cubeLB A ![fst A A ≫ u, snd A A] L).IsLB := LB.isLB_linComb hL _ _
  have h₂ : (cubeLB A ![fst A A, snd A A ≫ v] L).IsLB := LB.isLB_linComb hL _ _
  have hN := LB.isLB_div h₂ h₁
  refine GlobalTheory.T.seesaw_reduced_base_abelianScheme_of_dense_fibres hG S A L hA hL hamp A.left (A ⊗ A).left A.hom (snd A A).left (fst A A).left _ hp hN
    ((hd.preimage A.hom.isOpenMap).mono ?_) (lift (𝟙 A) (1 : A ⟶ A)).left ?_ ?_
  · rintro a ⟨K, _, x, G, _, _, φ, L', u', v', ⟨q, hq⟩, h, hL', hiso, hu', hv', H⟩
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback h.1 a q hq.symm
    let U : Over.mk ((G ⊗ G).hom ≫ x) ⟶ A ⊗ A := lift (pushHom h _ (fst G G)) (pushHom h _ (snd G G))
    have e₁ : U.left ≫ (fst A A).left = (fst G G).left ≫ φ :=
      congrArg (fun q => q.left) (lift_fst (pushHom h _ (fst G G)) (pushHom h _ (snd G G)))
    have e₂ : U.left ≫ (snd A A).left = (snd G G).left ≫ φ :=
      congrArg (fun q => q.left) (lift_snd (pushHom h _ (fst G G)) (pushHom h _ (snd G G)))
    have P : IsPullback U.left (fst G G).left (fst A A).left φ := by
      have B := (IsPullback.of_hasPullback G.hom G.hom).flip.paste_horiz h.1
      refine IsPullback.of_right ?_ e₁ hp
      rw [e₂, h.1.w]
      exact B
    have push : ∀ {w' : G ⟶ G} {w : A ⟶ A}, w'.left ≫ φ = φ ≫ w.left → ∀ y : G ⊗ G ⟶ G,
        pushHom h _ (y ≫ w') = pushHom h _ y ≫ w := fun hw y => Over.OverMorphism.ext (by
      show (y.left ≫ _) ≫ _ = (y.left ≫ _) ≫ _
      rw [Category.assoc, hw, Category.assoc])
    refine ⟨G.left.residueField z, inferInstance, G.left.fromSpecResidueField z ≫ φ,
      pullback (fst G G).left (G.left.fromSpecResidueField z), pullback.fst _ _ ≫ U.left,
      pullback.snd _ _, ⟨IsLocalRing.closedPoint (G.left.residueField z), ?_⟩,
      (IsPullback.of_hasPullback _ _).paste_horiz P, ?_⟩
    · rw [← hz]
      exact congrArg φ (Scheme.fromSpecResidueField_apply z _)
    · have h₁' : (cubeLB G ![fst G G ≫ u', snd G G] L').IsLB := LB.isLB_linComb hL' _ _
      have h₂' : (cubeLB G ![fst G G, snd G G ≫ v'] L').IsLB := LB.isLB_linComb hL' _ _
      have H' := (cls_eq_iff h₁' h₂').2 H
      rw [cls_cube_two hL', cls_cube_two hL', (cls_eq_iff hL' (pull_isLB hL φ)).2 hiso, cls_pull hL,
        lam_pull_of_isGrpPullback h, lam_pull_of_isGrpPullback h, push hu', push hv'] at H'
      have j : pull U.left (cls _ h₂ - cls _ h₁) = 0 := by
        rw [cls_cube_two hL, cls_cube_two hL, map_sub, pull_lam, pull_lam, lift_fst,
          lift_snd, lift_fst_assoc, lift_snd_assoc]
        exact sub_eq_zero.2 H'.symm
      refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
      rw [cls_pull hN, cls_div h₂ h₁]
      exact (pull_comp _ _ _).trans ((congrArg _ j).trans (map_zero _))
  · rw [← Over.comp_left, lift_fst, Over.id_left]
  · refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
    rw [cls_pull hN, cls_div h₂ h₁, cls_cube_two hL, cls_cube_two hL, map_sub, pull_lam, pull_lam, lift_fst,
      lift_snd, lift_fst_assoc, lift_snd_assoc, MonObj.one_comp, lam_one_right, lam_one_right, sub_self]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem isPullback_lift_toUnit_fst_left {S : Scheme.{0}} (A B : Over S) (x : 𝟙_ (Over S) ⟶ A) :
    IsPullback (lift (toUnit B ≫ x) (𝟙 B)).left B.hom (fst A B).left (x.left : S ⟶ A.left) := by
  have h1 : (lift (toUnit B ≫ x) (𝟙 B)).left ≫ (fst A B).left = B.hom ≫ (x.left : S ⟶ A.left) := by
    rw [← Over.comp_left, lift_fst, Over.comp_left]
    rfl
  have h2 : (lift (toUnit B ≫ x) (𝟙 B)).left ≫ (snd A B).left = 𝟙 B.left := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have h3 : (x.left : S ⟶ A.left) ≫ A.hom = 𝟙 S := Over.w x
  have hp : IsPullback (snd A B).left (fst A B).left B.hom A.hom :=
    (IsPullback.of_hasPullback A.hom B.hom).flip
  refine IsPullback.of_right ?_ h1 hp
  rw [h2, h3]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

theorem triv_of_triv_on_dense_fibres_prod_abelian : Out.GlobalFnsSt → ∀ (k : Type) [Field k] [IsAlgClosed k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B] (N : LB (A ⊗ B).left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → M.IsLB → Out.RelAmple B M → N.IsLB → (∃ t : (N.pull (lift (1 : B ⟶ A) (𝟙 B)).left).Gen, t.IsGen) → Dense (⋃ x ∈ {x : 𝟙_ (Over (Sp k)) ⟶ A | ∃ t : (N.pull (lift (toUnit B ≫ x) (𝟙 B)).left).Gen, t.IsGen}, Set.range x.left) → (∃ t : (N.pull (lift (𝟙 A) (1 : A ⟶ B)).left).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  intro hG k _ _ A B _ _ N M hA hB hM hamp hN _ hd h0
  have : IsReduced A.left :=
    (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field k A.left A.hom hA.smooth).1
  have hp : IsPullback (snd A B).left (fst A B).left B.hom A.hom :=
    (IsPullback.of_hasPullback A.hom B.hom).flip
  refine GlobalTheory.T.seesaw_reduced_base_abelianScheme_of_dense_fibres hG (Sp k) B M hB hM hamp A.left (A ⊗ B).left A.hom (snd A B).left (fst A B).left N hp hN
    (hd.mono ?_) (lift (𝟙 A) (1 : A ⟶ B)).left ?_ h0
  · intro p hp
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hp
    obtain ⟨x, hx, hpx⟩ := hp
    exact ⟨k, inferInstance, x.left, B.left, _, B.hom, hpx, isPullback_lift_toUnit_fst_left A B x, hx⟩
  · rw [← Over.comp_left, lift_fst, Over.id_left]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.card_torsion_eq_pow_two_mul_dim : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g N : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (N : k) ≠ 0 → Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ B // x ^ N = 1} = N ^ (2 * g) := by
  first | exact @GlobalTheory.card_torsion_abelianVariety | exact GlobalTheory.card_torsion_abelianVariety | (intros; apply GlobalTheory.card_torsion_abelianVariety <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.Moduli

theorem cube_of_isLB :
    ∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB →
      ∃ t : LB.Gen (Theta P.A M), t.IsGen :=
  GlobalTheory.AbLaw.CubeAssembly.cube_gen

end GlobalTheory.Moduli
end
