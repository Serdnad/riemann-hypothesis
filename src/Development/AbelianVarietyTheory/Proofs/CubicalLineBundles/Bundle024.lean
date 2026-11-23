module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.DedekindDomain.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentation
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimTrivialOfMult
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModNOfDvdModulus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Nilpotent
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
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory

namespace IsogenyModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct in
private theorem over_pullback_map_left_fst {S S' : Scheme} (φ : S' ⟶ S) (Ga X : Over S) (io : Ga ⟶ X) :
    ((Over.pullback φ).map io).left ≫ pullback.fst X.hom φ = pullback.fst _ _ ≫ io.left :=
  pullback.lift_fst _ _ _

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct in
private theorem over_pullback_map_left_snd {S S' : Scheme} (φ : S' ⟶ S) (Ga X : Over S) (io : Ga ⟶ X) :
    ((Over.pullback φ).map io).left ≫ pullback.snd X.hom φ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct in
theorem _root_.GlobalTheory.IsogenyModel.exists_flat_closure (T K : Type) [CommRing T] [IsDedekindDomain T] [Field K] [Algebra T K]
    [IsFractionRing T K] (X : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp T)) (Z : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K))
    (i : Z ⟶ (Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K))).obj X) (hi : IsClosedImmersion i.left) :
    ∃ (Ga : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp T)) (io : Ga ⟶ X)
      (e : (Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K))).obj Ga ≅ Z), IsClosedImmersion io.left ∧
      Flat Ga.hom ∧ e.hom ≫ i = (Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K))).map io := by
  haveI := hi
  haveI : Flat (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K)) := _root_.GlobalTheory.flat_specMap_localization (nonZeroDivisors T) K
  haveI : Mono (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K)) := _root_.GlobalTheory.mono_specMap_localization (nonZeroDivisors T) K
  set u := pullback.fst X.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K)) with hu
  set j := i.left ≫ u with hj
  have hjs : Z.hom ≫ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K)) = j ≫ X.hom := by
    rw [hj, Category.assoc, hu, pullback.condition, ← Category.assoc]
    congr 1
    exact (Over.w i).symm
  haveI : QuasiCompact (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K)) := by dsimp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap]; infer_instance
  haveI : QuasiCompact j := by rw [hj, hu]; infer_instance
  have hflat : Flat (j.imageι ≫ X.hom) :=
    _root_.GlobalTheory.flat_image_of_over_fractionField j X.hom Z.hom hjs
  have hA : IsPullback i.left j.toImage u j.imageι :=
    _root_.GlobalTheory.isPullback_toImage_of_isClosedImmersion j i.left u rfl
  have hB : IsPullback u (pullback.snd X.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K))) X.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K)) := IsPullback.of_hasPullback X.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K))
  have hC : IsPullback j.toImage (i.left ≫ pullback.snd X.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K))) (j.imageι ≫ X.hom) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K)) :=
    IsPullback.paste_vert hA.flip hB
  have hZ : i.left ≫ pullback.snd X.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K)) = Z.hom := Over.w i
  rw [hZ] at hC
  refine ⟨Over.mk (j.imageι ≫ X.hom), Over.homMk j.imageι rfl,
    Over.isoMk hC.isoPullback.symm (by simp), (show IsClosedImmersion j.imageι from inferInstance), hflat, ?_⟩
  ext1
  simp only [Over.comp_left, Over.isoMk_hom_left, Iso.symm_hom]
  rw [Iso.inv_comp_eq]
  apply pullback.hom_ext
  · rw [Category.assoc, over_pullback_map_left_fst]
    erw [hC.isoPullback_hom_fst_assoc]
    simp [hj, hu]
  · rw [Category.assoc, over_pullback_map_left_snd]
    erw [hC.isoPullback_hom_snd]
    exact hZ

variable {S : Scheme.{0}}


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct in
variable {S : Scheme.{0}} in
theorem _root_.GlobalTheory.IsogenyModel.exists_kernel {G B : Over S} [GrpObj G] [GrpObj B] [IsSeparated B.hom] (f : G ⟶ B)
    [IsMonHom f] [IsFinite f.left] :
    ∃ (Z : Over S) (_ : GrpObj Z) (i : Z ⟶ G), IsMonHom i ∧ IsClosedImmersion i.left ∧
      IsFinite Z.hom ∧ IsPullback i (toUnit Z) f η[B] := by
  have hP := IsPullback.of_hasPullback f η[B]
  have hL := IsPullback.map (Over.forget S) hP
  haveI : IsClosedImmersion η[B].left :=
    _root_.GlobalTheory.Retract.isClosedImmersion_section (f := 𝟙 S) (r := B.hom) (Over.w η[B])
      (Category.comp_id _)
  haveI : Mono η[B] := ⟨fun a b _ => toUnit_unique a b⟩
  set i := pullback.fst f η[B] with hi
  have key : ∀ {X : Over S} (a : X ⟶ pullback f η[B]), (a ≫ i) ≫ f = 1 := fun a => by
    rw [Category.assoc, hi, pullback.condition, ← Category.assoc,
      toUnit_unique (a ≫ pullback.snd f η[B]) (toUnit _), ← Hom.one_def]
  have key1 : i ≫ f = 1 := by simpa using key (𝟙 _)
  have hinv : ∀ {X : Over S} (a : X ⟶ G), a⁻¹ ≫ f = (a ≫ f)⁻¹ := by
    intro X a
    exact GrpObj.inv_comp a f
  obtain ⟨inst, hmon⟩ := _root_.GlobalTheory.exists_grpObj_of_mono i
    (pullback.lift η[G] (𝟙 _) (by simp))
    (pullback.lift ((fst _ _ ≫ i) * (snd _ _ ≫ i)) (toUnit _)
      (by rw [mul_comp, key, key, _root_.mul_one, Hom.one_def]))
    (pullback.lift i⁻¹ (toUnit _) (by rw [hinv, key1, _root_.inv_one, Hom.one_def]))
    (pullback.lift_fst _ _ _)
    (by rw [pullback.lift_fst, Hom.mul_def, lift_fst_comp_snd_comp])
    (by rw [pullback.lift_fst, Hom.inv_def])
  refine ⟨pullback f η[B], inst, i, hmon, ?_, ?_, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) hL.flip (show IsClosedImmersion η[B].left from inferInstance)
  · have hw := Over.w (pullback.snd f η[B])
    have : IsFinite (pullback.snd f η[B]).left :=
      MorphismProperty.of_isPullback (P := @IsFinite) hL (show IsFinite f.left from inferInstance)
    rw [← hw]
    simpa using this
  · simpa [toUnit_unique (pullback.snd f η[B]) (toUnit _)] using hP


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct in
variable {S : Scheme.{0}} in
theorem _root_.GlobalTheory.IsogenyModel.exists_iso_of_same_kernel {G A B Z : Over S} [GrpObj G] [GrpObj A] [GrpObj B]
    (q : G ⟶ A) (f : G ⟶ B) (i : Z ⟶ G) [IsMonHom q] [IsMonHom f] [Flat q.left]
    [Surjective q.left] [QuasiCompact q.left] [Surjective f.left] [IsProper A.hom]
    [IsSeparated B.hom] [IsReduced B.left] (hq : IsPullback i (toUnit Z) q η[A])
    (hf : IsPullback i (toUnit Z) f η[B]) :
    ∃ e : A ≅ B, IsMonHom e.hom ∧ q ≫ e.hom = f := by
  obtain ⟨β, hβ, hqβ⟩ := _root_.GlobalTheory.FlatQuotient.exists_desc q i f hq hf.w
  have htriv : ∀ {X : Over S} (x : X ⟶ A), x ≫ β = 1 → x = 1 := by
    intro X x hx
    have hP := IsPullback.of_hasPullback x q
    have hL := IsPullback.map (Over.forget S) hP
    haveI : Flat (pullback.fst x q).left :=
      MorphismProperty.of_isPullback (P := @Flat) hL.flip (show Flat q.left from inferInstance)
    haveI : Surjective (pullback.fst x q).left :=
      MorphismProperty.of_isPullback (P := @Surjective) hL.flip
        (show Surjective q.left from inferInstance)
    haveI : Epi (pullback.fst x q) := _root_.GlobalTheory.FlatQuotient.epi_of_flat_surjective _
    have hg : pullback.snd x q ≫ f = toUnit _ ≫ η[B] := by
      rw [← hqβ, ← Category.assoc, ← pullback.condition, Category.assoc, hx, Hom.one_def,
        ← Category.assoc, toUnit_unique (pullback.fst x q ≫ toUnit X) (toUnit _)]
    have hgq : pullback.snd x q ≫ q = toUnit _ ≫ η[A] := by
      rw [← hf.lift_fst _ _ hg, Category.assoc, hq.w, ← Category.assoc,
        toUnit_unique (hf.lift _ _ hg ≫ toUnit Z) (toUnit _)]
    rw [← cancel_epi (pullback.fst x q), pullback.condition, hgq, Hom.one_def, ← Category.assoc,
      toUnit_unique (pullback.fst x q ≫ toUnit X) (toUnit _)]
  haveI : Mono β := ⟨fun a b hab => by
    have h1 : (a * b⁻¹) ≫ β = 1 := by
      rw [mul_comp, GrpObj.inv_comp, hab, _root_.mul_inv_cancel]
    have h2 := htriv _ h1
    exact (mul_inv_eq_one.mp h2)⟩
  haveI : Surjective (q.left ≫ β.left) := by
    rw [← Over.comp_left, hqβ]; infer_instance
  haveI : Surjective β.left := Surjective.of_comp q.left β.left
  haveI : IsProper (β.left ≫ B.hom) := by rw [Over.w β]; infer_instance
  haveI : IsProper β.left := IsProper.of_comp β.left B.hom
  haveI : IsClosedImmersion β.left :=
    (IsClosedImmersion.iff_isProper_and_mono (f := β.left)).mpr ⟨inferInstance, inferInstance⟩
  haveI : IsIso β.left := isIso_of_isClosedImmersion_of_surjective β.left
  refine ⟨Over.isoMk (asIso β.left) (Over.w β), ?_, ?_⟩
  · have : (Over.isoMk (asIso β.left) (Over.w β)).hom = β := by ext1; rfl
    rw [this]; exact hβ
  · have : (Over.isoMk (asIso β.left) (Over.w β)).hom = β := by ext1; rfl
    rw [this]; exact hqβ

end IsogenyModel

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.TateRoot

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
open scoped CategoryTheory.Obj in
private lemma isCoprime_add_sub_mul_pow_factorial {j N : ℤ} (hj : IsCoprime j N) {n : ℕ} (hn : 0 < n) :
    IsCoprime (j + (1 - j) * N ^ n.factorial) n := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs, Int.natAbs_natCast]
  apply Nat.coprime_of_dvd
  intro p hp hpν hpn
  haveI := Fact.mk hp
  have hν : ((j + (1 - j) * N ^ n.factorial : ℤ) : ZMod p) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.natCast_dvd.mpr hpν
  have hpn' : p ≤ n := Nat.le_of_dvd hn hpn
  by_cases hN : (N : ZMod p) = 0
  · have hfac : n.factorial ≠ 0 := Nat.factorial_ne_zero n
    push_cast at hν
    rw [hN, zero_pow hfac, mul_zero, add_zero, ZMod.intCast_zmod_eq_zero_iff_dvd] at hν
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hN
    have hu := hj.isUnit_of_dvd' hν hN
    rw [Int.isUnit_iff] at hu
    have := hp.two_le
    omega
  · have hdvd : p - 1 ∣ n.factorial :=
      Nat.dvd_factorial (by have := hp.two_le; omega) (by omega)
    obtain ⟨s, hs⟩ := hdvd
    push_cast at hν
    rw [hs, pow_mul, ZMod.pow_card_sub_one_eq_one hN, one_pow] at hν
    simp at hν

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
open scoped CategoryTheory.Obj in
private lemma zmod_pow_eq_pow_factorial_of_dvd {n : ℕ} (hn : 0 < n) (x : ZMod n) {c : ℕ}
    (hc : n.factorial ∣ c) (hc0 : 0 < c) : x ^ c = x ^ n.factorial := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have key : ∀ a t : ℕ, a ≤ n → 0 < t → t ≤ n → x ^ (a + t) = x ^ a → x ^ c = x ^ n.factorial := by
    intro a t ha ht htn h
    have hstep : ∀ k, a ≤ k → x ^ (k + t) = x ^ k := by
      intro k hk
      have e1 : k + t = (k - a) + (a + t) := by omega
      have e2 : k = (k - a) + a := by omega
      rw [e1, pow_add, h, ← pow_add, ← e2]
    have hper : ∀ k s, a ≤ k → x ^ (k + t * s) = x ^ k := by
      intro k s hk
      induction s with
      | zero => simp
      | succ s ih =>
        rw [show k + t * (s + 1) = (k + t * s) + t by ring, hstep _ (by omega), ih]
    have hfac : n.factorial ≤ c := Nat.le_of_dvd hc0 hc
    have htd : t ∣ c - n.factorial :=
      Nat.dvd_sub ((Nat.dvd_factorial ht htn).trans hc) (Nat.dvd_factorial ht htn)
    obtain ⟨s, hs⟩ := htd
    have : c = n.factorial + t * s := by omega
    rw [this, hper _ _ (le_trans ha (Nat.self_le_factorial n))]
  obtain ⟨a, b, hab, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (n + 1) => x ^ (i : ℕ))
    (by simp [ZMod.card])
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
  · exact key a (b - a) (by omega) (by omega) (by omega)
      (by rw [show (a : ℕ) + (b - a) = b by omega]; exact heq.symm)
  · exact key b (a - b) (by omega) (by omega) (by omega)
      (by rw [show (b : ℕ) + (a - b) = a by omega]; exact heq)


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.TateRoot.exists_tateIso_zeta_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (k : Type) [Field k] (Q : Type) [Group Q]
    (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop) (_ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso D k Q act e) (N : ℕ) (z : k),
    0 < N → IsPrimitiveRoot z N → ∃ I' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso D k Q act e, (I'.ζ N : k) = z := by
  intro E _ _ _ H D l k _ Q _ act e I N z hN hz
  have hζ : IsPrimitiveRoot ((I.ζ N : kˣ) : k) N := IsPrimitiveRoot.coe_units_iff.mpr (I.ζ_prim N hN)
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hz.pow_eq_one
  have hcop : IsCoprime (i : ℤ) N := by
    rw [Nat.isCoprime_iff_coprime]
    rw [← hζ.pow_iff_coprime hN, hi]
    exact hz
  suffices h : ∃ g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sim D, ∃ hν : (∀ (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧
      IsCoprime (g.ν n) n), (N : ℤ) ∣ g.ν N - i by
    obtain ⟨g, hν, hg⟩ := h
    refine ⟨_root_.GlobalTheory.LevelTwist.twist I g hν, ?_⟩
    rw [_root_.GlobalTheory.LevelTwist.twist_ζ, _root_.GlobalTheory.LevelTwist.zeta_zpow_congr I hN hg, zpow_natCast, Units.val_pow_eq_pow_val, hi]
  rcases Nat.eq_zero_or_pos (D.p + D.q) with hpq | hpq
  · haveI := D.proj
    haveI := D.fin
    have hsub : Subsingleton D.La := Module.finrank_zero_iff.mp (by rw [D.rank]; exact hpq)
    let g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sim D :=
      { f := fun _ => LinearMap.id
        ν := fun n => i + (1 - i) * (N : ℤ) ^ n.factorial
        tower := fun n m _ _ a => ⟨0, by simp⟩
        inv := fun n _ => ⟨LinearMap.id, fun a => ⟨⟨0, Subsingleton.elim _ _⟩, ⟨0, Subsingleton.elim _ _⟩⟩⟩
        mult := fun n _ a b => by rw [Subsingleton.elim a 0]; simp }
    refine ⟨g, fun n m hn hm => ⟨?_, isCoprime_add_sub_mul_pow_factorial hcop hn⟩, ?_⟩
    · have h := zmod_pow_eq_pow_factorial_of_dvd hn (N : ZMod n)
        (Nat.factorial_dvd_factorial (Nat.le_mul_of_pos_right n hm)) (Nat.factorial_pos _)
      have h' : (((N : ℤ) ^ n.factorial : ℤ) : ZMod n) =
          (((N : ℤ) ^ (n * m).factorial : ℤ) : ZMod n) := by
        push_cast
        exact h.symm
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h'
      show (n : ℤ) ∣ (i + (1 - i) * (N : ℤ) ^ (n * m).factorial) - (i + (1 - i) * (N : ℤ) ^ n.factorial)
      rw [show (i + (1 - i) * (N : ℤ) ^ (n * m).factorial) - (i + (1 - i) * (N : ℤ) ^ n.factorial) =
        (1 - i) * ((N : ℤ) ^ (n * m).factorial - (N : ℤ) ^ n.factorial) by ring]
      exact Dvd.dvd.mul_left h' _
    · show (N : ℤ) ∣ (i + (1 - i) * (N : ℤ) ^ N.factorial) - i
      rw [add_sub_cancel_left]
      exact Dvd.dvd.mul_left (dvd_pow_self _ (Nat.factorial_ne_zero N)) _
  · have hgrp := _root_.GlobalTheory.SimAlg.sim_group
    obtain ⟨g, hg, -⟩ := _root_.GlobalTheory.SimMult.exists_sim_trivial_of_mult hgrp _root_.GlobalTheory.exists_sim_lift
      E H D { l with A := 1, A_pos := Nat.one_pos } N i hN hcop (by simp)
    exact ⟨g, (hgrp E H D hpq).1 g, hg⟩

end GlobalTheory.TateRoot
end
