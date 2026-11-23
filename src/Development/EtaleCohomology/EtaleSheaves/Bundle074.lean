module

public import Development.EtaleCohomology.EtaleSheaves.AugBijPf
public import Development.EtaleCohomology.EtaleSheaves.BoundaryKernel.Formal
public import Development.EtaleCohomology.EtaleSheaves.Bundle069
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Development.EtaleCohomology.EtaleSheaves.Bundle001
public import Development.EtaleCohomology.EtaleSheaves.Bundle066
public import Development.EtaleCohomology.EtaleSheaves.Bundle056
public import Development.EtaleCohomology.EtaleSheaves.Bundle004
public import Development.EtaleCohomology.TateTwists.Bundle007
public import Development.EtaleCohomology.TateTwists.Bundle010
public import Development.EtaleCohomology.TateTwists.Bundle027
public import Development.EtaleCohomology.TateTwists.Bundle004
public import Development.EtaleCohomology.TateTwists.Bundle005
public import Development.EtaleCohomology.TateTwists.Bundle003
public import Development.EtaleCohomology.CohomologicalPurity.Bundle032
public import Development.EtaleCohomology.TateTwists.Bundle030
public import Development.EtaleCohomology.TateTwists.Bundle035
import Development.EtaleCohomology.TateTwists.Bundle012
public import Development.EtaleCohomology.TateTwists.EtaleComplexAcyclicIffLocalExactness
public import Development.EtaleCohomology.TateTwists.Bundle019
public import Development.EtaleCohomology.TateTwists.Bundle011
public import Development.EtaleCohomology.TateTwists.Bundle032
public import Development.EtaleCohomology.TateTwists.Bundle029
public import Development.EtaleCohomology.TateTwists.Bundle034
public import Development.EtaleCohomology.TateTwists.Bundle021
import Development.EtaleCohomology.TateTwists.EtaleTensorTripleProductFamilyOfGluing
import Development.EtaleCohomology.TateTwists.Bundle020
import Development.EtaleCohomology.TateTwists.Bundle028
import Development.EtaleCohomology.TateTwists.Bundle015
import Development.EtaleCohomology.TateTwists.Bundle017
public import Development.EtaleCohomology.TateTwists.Bundle022
public import Development.EtaleCohomology.TateTwists.Bundle025
public import Development.EtaleCohomology.TateTwists.Bundle026
public import Development.EtaleCohomology.TateTwists.Bundle014
import Development.EtaleCohomology.TateTwists.Bundle033
public import Development.EtaleCohomology.TateTwists.Bundle016
public import Development.EtaleCohomology.EtaleSheaves.Bundle058
public import Development.EtaleCohomology.EtaleSheaves.Bundle067
public import Development.EtaleCohomology.EtaleSheaves.Bundle068
import Aesop.Main
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Sites.EpiMono
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Development.EtaleCohomology.EtaleSheaves.Bundle003
public import Development.EtaleCohomology.TateTwists.Bundle008
import Development.EtaleCohomology.EtaleSheaves.Bundle046
import Development.EtaleCohomology.EtaleSheaves.PropertyDescent.BaseChange

@[expose] public section

section

noncomputable section
open Polynomial IsLocalRing

namespace LateralTheory.E.LocPowPf

theorem pow_eq_one_of_aeval {q : ℕ} {A : Type} [CommRing A] (ξ : A) (h : aeval ξ (cyclotomic q ℤ) = 0) : ξ ^ q = 1 := by
  obtain ⟨p, hp⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have := congrArg (aeval ξ) hp
  rw [map_mul, h, zero_mul, map_sub, map_pow, aeval_X, map_one] at this
  exact sub_eq_zero.1 this

theorem prim_res {q : ℕ} {A : Type} [CommRing A] [IsLocalRing A] (ξ : GlobalTheory.EtC.Prim q A) :
    IsPrimitiveRoot (residue A ξ.1) q := by
  have hu : IsUnit ((q : ResidueField A)) := by simpa using ξ.2.1.map (residue A)
  have : NeZero (q : ResidueField A) := ⟨hu.ne_zero⟩
  obtain ⟨x, -, hx⟩ := ξ
  change IsPrimitiveRoot (residue A x) q
  rw [← isRoot_cyclotomic_iff, IsRoot, ← map_cyclotomic_int, eval_map]
  change aeval ((residue A).toIntAlgHom x) (cyclotomic q ℤ) = 0
  rw [aeval_algHom_apply, hx, map_zero]

theorem LocPow_of : LateralTheory.E.AugBijPf.LocPow := by
  intro q A _ _ ξ ζ
  have hq : IsUnit (q : A) := ξ.2.1
  have hz := prim_res ζ
  have hx := prim_res ξ
  have : NeZero q := ⟨by rintro rfl; simp at hq⟩
  obtain ⟨i, hi, he⟩ := hz.eq_pow_of_pow_eq_one hx.pow_eq_one
  have hcop : i.Coprime q := (hz.pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) i).1 (he ▸ hx)
  refine ⟨ZMod.unitOfCoprime i hcop, ?_⟩
  have hval : ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val = i := by
    simp [ZMod.unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  rw [hval]
  set η := ζ.1 ^ i with hη
  have h1 : ξ.1 ^ q = 1 := pow_eq_one_of_aeval ξ.1 ξ.2.2
  have h2 : η ^ q = 1 := by rw [hη, ← pow_mul, mul_comm, pow_mul, pow_eq_one_of_aeval ζ.1 ζ.2.2, one_pow]
  have hres : residue A ξ.1 = residue A η := by rw [hη, map_pow]; exact he.symm
  have hηu : residue A η ≠ 0 := hres ▸ hx.ne_zero (NeZero.ne q)
  have hS : IsUnit (∑ j ∈ Finset.range q, ξ.1 ^ j * η ^ (q - 1 - j)) := by

    rw [← residue_ne_zero_iff_isUnit, map_sum]
    simp only [map_mul, map_pow, hres]
    rw [geom_sum₂_self]
    exact mul_ne_zero (by simpa using (hq.map (residue A)).ne_zero) (pow_ne_zero _ hηu)
  have key := (Commute.all ξ.1 η).geom_sum₂_mul q
  rw [h1, h2, sub_self] at key
  exact sub_eq_zero.1 ((hS.mul_right_eq_zero).1 key)

end LateralTheory.E.LocPowPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite
namespace LateralTheory.E.H0Kernel
open LateralTheory.E.LeafDegCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafShIsoPf

theorem locSurj (B : Scheme.{0}) (q : ℕ) {F G : SShv B q} (e : F ⟶ G) [Epi e] : Sheaf.IsLocallySurjective e := by
  have : EssentiallySmall.{1} B.Etale := inferInstance
  have hSC : (EtTop B).HasSheafCompose (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) :=
    hasSheafComposeEssentiallySmallSite (J := EtTop B) (A := ModuleCat.{1} (ULift.{1} (ZMod q))) (F := forget _)
  exact (Sheaf.isLocallySurjective_iff_epi' _ e).2 inferInstance

theorem etale_sheaf_zeroth_cohomology_kernel_exact : EtaleDerivedDegreeZeroHomologyKernelLocallyVanishes := by
  intro B q M U x hx
  obtain ⟨T, e, he, H⟩ := exists_epi (C := SShv B q)
    (P := (presheafToSheaf (EtTop B) _).obj ((FP (ULift.{1} (ZMod q))).obj U)) x hx
  have := locSurj B q e
  obtain ⟨Z, hZ, hc⟩ := locally_factors (EtTop B) (ULift.{1} (ZMod q)) e
  refine ⟨Z, hZ, fun U' a ha => ?_⟩
  obtain ⟨c, hc⟩ := hc U' a ha
  have h := H _ c
  rw [← hc] at h
  exact h

end LateralTheory.E.H0Kernel
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
  LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.FiltrationLevelBase

def Step0 : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {Z' Z : PSh} {X' X : Spc} (g : X' ⟶ X)
  (h : Z' ⟶ Z) (a : disc.obj Z ⟶ X) (b : disc.obj Z' ⟶ X') (comm : disc.map h ≫ a = b ≫ g),
  IsIso (a.app (op ⦋0⦌)) → IsIso (b.app (op ⦋0⦌)) →
  ∀ z : Cocycle (mappingCone ((chains R).map g)) (res R F) n,
    rpull R g (disc.map h) b a comm F n (CohomologyClass.mk z) = 0 →
    ∃ c : Cochain (mappingCone ((chains R).map g)) (res R F) (n - 1),
      LateralTheory.E.FiltGenPf.V ((chains R).map g) (-1) n ((z : Cochain _ _ n) - δ (n - 1) n c)

theorem Filt_of (h0 : Step0) : LateralTheory.E.FiltrationLevelInjectivity.Filt := by
  intro _ R _ F n Z' Z X' X g h a b comm ha hb hlev
  have hk : ∀ p : ℕ, 1 ≤ p → Subsingleton (CohomologyClass (mappingCone
      ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map (((chains R).map g).f (-(p : ℤ)))))
      (res R F) n) := by
    intro p hp
    refine LateralTheory.E.CechFiltPf.Piece_of LateralTheory.E.DiscLvlPf.DiscLvl_of LateralTheory.E.ShiftLvlPf.ShiftLvl_of R F g p n ?_
    obtain ⟨hi, hs⟩ := hlev p hp (n - p) (by omega)
    refine LateralTheory.E.RelativeTruncationSingleDegree.sub_of R F _ _ ⟨fun m hm => ?_, hi⟩ (LateralTheory.E.RelativeTruncationSingleDegree.pull_fgt R F _ _)
    obtain rfl : m = n - p - 1 := by omega
    exact hs
  have hk' : ∀ k : ℤ, k ≤ -1 → Subsingleton (CohomologyClass (mappingCone
      ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) k).map (((chains R).map g).f k))) (res R F) n) := by
    intro k hk1
    obtain ⟨p, rfl⟩ : ∃ p : ℕ, k = -(p : ℤ) := ⟨(-k).toNat, by omega⟩
    exact hk p (by omega)
  have claim : ∀ m : ℕ, ∀ z : Cocycle (mappingCone ((chains R).map g)) (res R F) n,
      rpull R g (disc.map h) b a comm F n (CohomologyClass.mk z) = 0 →
      ∃ c : Cochain (mappingCone ((chains R).map g)) (res R F) (n - 1),
        LateralTheory.E.FiltGenPf.V ((chains R).map g) (-((m : ℤ) + 1)) n ((z : Cochain _ _ n) - δ (n - 1) n c) := by
    intro m
    induction m with
    | zero =>
      intro z hz
      have e : (-(((0 : ℕ) : ℤ) + 1)) = -1 := by norm_num
      rw [e]
      exact h0 R F n g h a b comm ha hb z hz
    | succ m ih =>
      intro z hz
      obtain ⟨c, hc⟩ := ih z hz
      have hkm := hk' (-((m : ℤ) + 1)) (by omega)
      have hs1 := LateralTheory.E.FiltGenPf.step ((chains R).map g) (-((m : ℤ) + 1)) n hkm
      have hzz : δ n (n + 1) ((z : Cochain (mappingCone ((chains R).map g)) (res R F) n) - δ (n - 1) n c) = 0 := by
        rw [δ_sub, δ_δ, sub_zero]; exact Cocycle.δ_eq_zero z (n + 1)
      have hs2 := hs1 _ hzz
      obtain ⟨c', hc'⟩ := hs2 hc
      refine ⟨c + c', ?_⟩
      have e : (-((((m + 1 : ℕ) : ℤ)) + 1)) = -((m : ℤ) + 1) - 1 := by push_cast; ring
      rw [e, δ_add, ← sub_sub]
      exact hc'
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨c, hc1, hc2⟩ := claim (n.toNat + 1) z hx
  change CohomologyClass.mk z = 0
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨c, ?_⟩
  have hz0 : (z : Cochain (mappingCone ((chains R).map g)) (res R F) n) - δ (n - 1) n c = 0 := by
    rw [mappingCone.ext_cochain_from_iff _ (n - 1) n (by omega)]
    constructor
    · simp only [Cochain.comp_zero]
      refine Cochain.ext _ _ (fun p q hpq => ?_)
      rw [Cochain.zero_v]
      rcases lt_or_ge (-((((n.toNat + 1 : ℕ) : ℤ)) + 1)) p with hp | hp
      · exact hc1 p q hpq hp
      · exact (LateralTheory.E.CechFiltPf.res_isZero R F q (by omega)).eq_of_tgt _ _
    · simp only [Cochain.comp_zero]
      refine Cochain.ext _ _ (fun p q hpq => ?_)
      rw [Cochain.zero_v]
      rcases lt_or_ge (-((((n.toNat + 1 : ℕ) : ℤ)) + 1)) p with hp | hp
      · exact hc2 p q hpq hp
      · exact (LateralTheory.E.CechFiltPf.res_isZero R F q (by omega)).eq_of_tgt _ _
  rw [sub_eq_zero] at hz0
  exact hz0.symm

end LateralTheory.E.FiltrationLevelBase
end
end

section

namespace LateralTheory.Fix.CupProductTensor
open LateralTheory.EtaleFoundations

theorem cup_spec0 : t_cup_spec0 := LateralTheory.Fin.EtaleCupProductNaturalInCoefficients.etale_cup_product_compatibility_specification_of_components
theorem cup_assoc0 : EtaleCochainCupAssociativeOfPairing :=
  etale_cochain_cup_assoc_of_cup_spec_and_alexander_whitney_assoc cup_spec0 (t_aw_assoc0_of etale_chain_cochain_eval_basic_properties_hold simplicial_subinterval_of_subinterval_along_etale)
theorem secSep : EtaleTensorTripleProductLeibnizSeparated.SecSep := etale_sheaf_sections_separated_holds
theorem tens_tri : EtaleTensorPairProductAssociative :=
  etale_tensor_triple_product_of_family_and_leibniz (etale_tensor_triple_product_family_of_gluing LateralTheory.Fin.EtaleSheafSectionsSeparatedAndGlue.intersectionNumber_baseChange)
    (etale_tensor_triple_product_leibniz_of_separated secSep)
theorem tens_ex : tt_tens_ex := tt_tens_ex_of tt_tens_pre_of etale_presheaf_tensor_data_sheafification_is_tensor_complex
theorem univ_exdeg : twpair_tens_univ_exdeg := twpair_tens_univ_exdeg_of
theorem tens_univ : twpair_tens_univ := twpair_tens_univ_of univ_exdeg
theorem tens_ge : tt_tens_ge := tt_tens_ge_of (by intro R _ I J K τ hτ; exact (tens_univ R τ hτ).2.1)
theorem res_side : tt_res_side := tt_res_side_of tens_univ LateralTheory.Fin.EtaleTensorPairQuasiIsoOfFlatQuasiIso.intersectionNumber_baseChange
theorem twres_ext : EtaleTwistResolutionUniversalExtension := LateralTheory.Fin.EtaleTwistResolutionUniversalExtension.intersectionNumber_baseChange
theorem cup_compat : EtaleCupProductNaturalInCoefficients := LateralTheory.Fin.EtaleCupProductNaturalInCoefficients.intersectionNumber_baseChange

theorem holds_of (hts : EtaleTateTwistSectionsLocallyGenerated) :
    EtaleTwistedCupProductAssociative ∧ EtaleTwistResolutionPairingCupUnique := by
  have hsec : TwMulGenMap.twSec := hts
  have hloc : EtaleTateTwistSectionsLocallyMultiplesOfGenerator := fun q _ i => (hts q i).1
  have hinj : EtaleTateTwistGeneratorMapSectionsInjective := etale_tate_twist_generator_map_injective_of_sections_glue hts LateralTheory.Fin.EtaleLocalPropertyBasicClosure.intersectionNumber_baseChange
    LateralTheory.Fin.EtaleSheafSectionsSeparatedAndGlue.intersectionNumber_baseChange
  have tw_mul : EtaleTateTwistSingletonTensorGenMul := etale_tate_twist_tensor_iso_of_generator_map_iso (etale_tate_twist_multiplication_tensor_exists_of_complex_tensor_exists tens_ex) (etale_tate_twist_multiplication_generator_map_of_section_description hsec)
    (etale_tate_twist_generator_map_isIso_of_inj_surj etale_sheaf_mono_epi_iff_sections_of_separation (etale_tate_twist_generator_map_surjective_of_local_and_root hloc
      etale_tate_twist_generator_restriction_and_root_change_holds) hinj)
  have twist : tt_twist_side := tt_twist_side_of tw_mul LateralTheory.Fin.EtaleTateTwistSheafFlat.intersectionNumber_baseChange LateralTheory.Fin.EtaleComplexPairingFlipExists.intersectionNumber_baseChange
    LateralTheory.Fin.EtaleTensorPairQuasiIsoOfFlatQuasiIso.intersectionNumber_baseChange
  have twres : EtaleTensorPairTwistResolutionMul := etale_tensor_twisted_resolution_of_existence_bound_and_sides tens_ex tens_ge twist res_side
  have pa : t_pair_assoc := t_pair_assoc_of twres tens_tri twres_ext cup_compat cup_assoc0 t_pa_tens_ex_of
    t_pa_tens_univ_of t_pa_precomp_of t_pa_cpush_id_of t_pa_cpush_htpy_of
  have tp : EtaleTwistResolutionPairingCupUnique := etale_tate_twist_cup_pairing_of_tensor_and_resolution_properties tens_ex tens_univ twres twres_ext cup_compat twpair_zc_fun_of
  exact ⟨etale_twisted_cup_assoc_of_twisted_pairing_exists_assoc (t_twpair_ex_of tp) pa, tp⟩

theorem ringAssoc : LateralTheory.E.CupProductRingLaws.LeafRingAssoc := (holds_of LateralTheory.CohomologicalPurity.LeafAWCutTw.twSec).1
theorem cupSpec : LateralTheory.E.CupProductRingLaws.LeafCupSpec := fun R _ _ _ _ μ E _ _ _ hk => cup_spec0 R μ (E := E) hk
theorem ringComm (hf : cc_cup_flip) : LateralTheory.E.CupProductRingLaws.LeafRingComm :=
  etale_twisted_cup_graded_comm_of_flip_and_unique_pairing hf (fun R _ _ _ _ μ => (LateralTheory.Fin.EtaleComplexPairingFlipExists.intersectionNumber_baseChange R μ).imp fun _ h => h.1) (holds_of LateralTheory.CohomologicalPurity.LeafAWCutTw.twSec).2
theorem awFlip : cc_aw_flip := cc_aw_flip_of LateralTheory.Fin.PrismAlexanderWhitneySwapChainHomotopy.intersectionNumber_baseChange cupflip_eta_delta_of

theorem cupFlip : cc_cup_flip := by
  intro R _ I J K μ ν hf E n m k h h' a b
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := (cupSpec R μ E h).1 α β
  obtain ⟨γ', hγ'⟩ := (cupSpec R ν E h').1 β α
  rw [(cupSpec R μ E h).2 _ _ _ hγ, (cupSpec R ν E h').2 _ _ _ hγ']
  exact awFlip R μ ν hf E h h' α β γ γ' hγ hγ'
theorem ringComm' : LateralTheory.E.CupProductRingLaws.LeafRingComm := ringComm cupFlip
theorem twPairExists : LateralTheory.E.CupProductRingLaws.LeafTwPairExists := fun q _ i j => ⟨_, ((holds_of LateralTheory.CohomologicalPurity.LeafAWCutTw.twSec).2 q i j).1⟩
end LateralTheory.Fix.CupProductTensor
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LocSecPfB

def HomSec : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}),
  ∃ e : ∀ G : Shv R, ((free R).obj (yoneda.obj X) ⟶ G) ≃+ Sec G X,
    ∀ {G G' : Shv R} (φ : G ⟶ G') (f : (free R).obj (yoneda.obj X) ⟶ G), e G' (f ≫ φ) = Sec.map φ (e G f)

def ClassSec : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0})
  (e : ∀ G : Shv R, ((free R).obj (yoneda.obj X) ⟶ G) ≃+ Sec G X),
  (∀ {G G' : Shv R} (φ : G ⟶ G') (f : (free R).obj (yoneda.obj X) ⟶ G), e G' (f ≫ φ) = Sec.map φ (e G f)) →
  ∀ (F : Shv R) (n : ℤ),
  Nonempty (CohomologyClass (LateralTheory.E.LocSecPf.pt R X) (res R F) n ≃+ (LateralTheory.E.LeafLocPf.secCx F X).homology n)

theorem locSecB_of (h1 : HomSec) (h2 : ClassSec) : LateralTheory.E.LocSecPf.LocSecB := by
  intro R _ X F n
  obtain ⟨e, he⟩ := h1 R X
  exact h2 R X e he F n

theorem LocSec_of (h1 : HomSec) (h2 : ClassSec) : LateralTheory.E.LeafLocPf.LocSec :=
  LateralTheory.E.LocSecPf.LocSec_of LateralTheory.E.LocSecPfA.locSecA (locSecB_of h1 h2)

end LateralTheory.E.LocSecPfB
end
end

section

namespace LateralTheory.E.LeafConsPfC

theorem LeafCons_of (hL : LateralTheory.E.LeafConsPf.LeafLoc) : LateralTheory.E.EtaleTopologySheaves.LeafCons :=
  LateralTheory.E.LeafConsPf.LeafCons_of hL LateralTheory.E.LeafConsPfB.LeafGlob_pf

end LateralTheory.E.LeafConsPfC
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafPropsDescendPf

namespace LateralTheory.E.LeafSpreadSeparatedPf

theorem incl_comp {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R S R' : Subalgebra k Ω} (h : R ≤ S)
    (h' : S ≤ R') : incl h' ≫ incl h = incl (h.trans h') := by
  rw [← Spec.map_comp]; rfl

theorem sep_of_stage {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R S R' : Subalgebra k Ω} (h : R ≤ S)
    (hS : S ≤ R') (hR : R ≤ R') {D E : Scheme.{0}} (q : D ⟶ Sp R) [IsSeparated (pullback.snd q (incl h))]
    (q' : E ⟶ Sp R') (r : E ⟶ D) (hE : IsPullback r q' q (incl hR)) : IsSeparated q' := by
  have hc : r ≫ q = (q' ≫ incl hS) ≫ incl h := by
    rw [Category.assoc, incl_comp]; exact hE.w
  have outer : IsPullback (pullback.lift r (q' ≫ incl hS) hc ≫ pullback.fst q (incl h)) q' q
      (incl hS ≫ incl h) := by
    rw [pullback.lift_fst, incl_comp]; exact hE
  have sq := IsPullback.of_right outer (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback q (incl h))
  exact MorphismProperty.of_isPullback (P := @IsSeparated) sq inferInstance

def BC {X Y Z T : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (p : X ⟶ Z) (w : f ≫ g = p) (t : T ⟶ Z) :
    pullback p t ⟶ pullback g t :=
  pullback.map _ _ _ _ f (𝟙 _) (𝟙 _) (by simp [w]) (by simp)

def LeafClosedImmSpread : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Sp R),
    (LocallyOfFinitePresentation g ∧ QuasiCompact g ∧ QuasiSeparated g) →
    (LocallyOfFinitePresentation (f ≫ g) ∧ QuasiCompact (f ≫ g) ∧ QuasiSeparated (f ≫ g)) →
    IsClosedImmersion (BC f g (f ≫ g) rfl (toR R)) →
    ∃ (S : Subalgebra k Ω) (h : R ≤ S), S.FG ∧ IsClosedImmersion (BC f g (f ≫ g) rfl (incl h))

def LeafDiagBC : Prop := ∀ {D Z T : Scheme.{0}} (q : D ⟶ Z) (t : T ⟶ Z),
    IsSeparated (pullback.snd q t) ↔ IsClosedImmersion (BC (pullback.diagonal q) (pullback.snd q q ≫ q) q (by simp) t)

theorem ci_congr {X Y Z T : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (p : X ⟶ Z) (w : f ≫ g = p) (t : T ⟶ Z) :
    IsClosedImmersion (BC f g p w t) ↔ IsClosedImmersion (BC f g (f ≫ g) rfl t) := by
  subst w; rfl

theorem separated_base_change_iff_diagonal_closed_immersion_holds : LeafDiagBC := by
  intro D Z T q t
  have e1 : pullback.snd q t = (pullbackSymmetry q t).hom ≫ pullback.fst t q := by simp
  have e2 : IsSeparated (pullback.snd q t) ↔ IsSeparated (pullback.fst t q) := by
    rw [e1]; exact MorphismProperty.cancel_left_of_respectsIso (P := @IsSeparated) _ _
  rw [e2]
  have e3 : IsSeparated (pullback.fst t q) ↔ IsClosedImmersion (pullback.diagonal (pullback.fst t q)) :=
    ⟨fun h => h.isClosedImmersion_diagonal, fun h => ⟨h⟩⟩
  rw [e3, diagonal_pullback_fst, MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion),
    MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion)]
  have : ((Over.pullback t).map (Over.homMk (pullback.diagonal q) : Over.mk q ⟶ Over.mk (pullback.snd q q ≫ q))).left
      = BC (pullback.diagonal q) (pullback.snd q q ≫ q) q (by simp) t := by
    apply pullback.hom_ext <;> simp only [BC, pullback.map, Category.comp_id] <;> rfl
  rw [this]

theorem of_two (hC : LeafClosedImmSpread) (hD : LeafDiagBC) :
    LateralTheory.E.LeafSpreadProperPf.LeafSpreadSeparated := by
  intro k _ Ω _ _ R hR C D c q v hf hc hv
  obtain ⟨h1, h2, h3⟩ := hf
  have s0 : IsSeparated (pullback.snd q (toR R)) := by
    rw [← hv.isoPullback_inv_snd]; infer_instance
  have ci := (ci_congr _ _ _ _ _).1 ((hD q (toR R)).1 s0)
  have hfg : pullback.diagonal q ≫ pullback.snd q q ≫ q = q := by simp
  obtain ⟨S, h, hS, ci'⟩ := hC k Ω R hR (pullback.diagonal q) (pullback.snd q q ≫ q)
    ⟨inferInstance, inferInstance, inferInstance⟩ (by rw [hfg]; exact ⟨h1, h2, h3⟩) ci
  have := (hD q (incl h)).2 ((ci_congr _ _ _ (by simp) _).2 ci')
  exact ⟨S, h, hS, fun R' hS' hRR E q' r hE => sep_of_stage h hS' hRR q q' r hE⟩

end LateralTheory.E.LeafSpreadSeparatedPf

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct
open LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf LateralTheory.E.LeafObjFPPf

namespace LateralTheory.E.LeafObjAffPf

theorem desc_spec (k : Type) [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] (A : Type) [CommRing A]
    [Algebra Ω A] [Algebra.FinitePresentation Ω A] :
    Desc k (Spec.map (CommRingCat.ofHom (algebraMap Ω A))) := by
  let P := Algebra.Presentation.ofFinitePresentation Ω A
  let R : Subalgebra k Ω := Algebra.adjoin k P.coeffs
  have : P.HasCoeffs R := ⟨fun x hx => ⟨⟨x, Algebra.subset_adjoin hx⟩, rfl⟩⟩
  let B := P.ModelOfHasCoeffs R
  let e : Ω ⊗[R] B ≃ₐ[Ω] A := P.tensorModelOfHasCoeffsEquiv R
  have hR : R.FG := ⟨P.finite_coeffs.toFinset, by simp [R]⟩
  let gB : CommRingCat.of B ⟶ CommRingCat.of A :=
    CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫ e.toRingEquiv.toCommRingCatIso.hom
  have hpo : IsPushout (CommRingCat.ofHom (algebraMap R Ω)) (CommRingCat.ofHom (algebraMap R B))
      (CommRingCat.ofHom (algebraMap Ω A)) gB := by
    refine (CommRingCat.isPushout_tensorProduct R Ω B).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      e.toRingEquiv.toCommRingCatIso ?_ ?_ ?_ ?_
    · simp
    · simp
    · ext x
      change e (x ⊗ₜ 1) = algebraMap Ω A x
      simpa [Algebra.TensorProduct.algebraMap_apply] using e.commutes x
    · simp [gB]
  refine ⟨R, hR, Spec (CommRingCat.of B), Spec.map (CommRingCat.ofHom (algebraMap R B)), _, ?_,
    (isPullback_SpecMap_of_isPushout _ _ _ _ hpo).flip⟩
  refine ⟨?_, inferInstance, inferInstance⟩
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

theorem desc_of_iso (k : Type) [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {X Y : Scheme.{0}}
    (i : X ≅ Y) (g : Y ⟶ Sp Ω) (h : Desc k g) : Desc k (i.hom ≫ g) := by
  obtain ⟨R, hR, D, q, v, hq, hpb⟩ := h
  exact ⟨R, hR, D, q, i.hom ≫ v, hq,
    hpb.of_iso i.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)⟩

theorem LeafObjAff_of : LeafObjAff := by
  intro k _ Ω _ _ X f hX hf
  obtain ⟨h1, h2, h3⟩ := hf
  let g : Spec Γ(X, ⊤) ⟶ Spec (CommRingCat.of Ω) := X.isoSpec.inv ≫ f
  let φ := Spec.preimage g
  letI : Algebra Ω Γ(X, ⊤) := φ.hom.toAlgebra
  have hg : LocallyOfFinitePresentation g := inferInstance
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap Ω Γ(X, ⊤))) = g := Spec.map_preimage g
  have hfp : Algebra.FinitePresentation Ω Γ(X, ⊤) := by
    rw [← Spec.map_preimage g, HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)] at hg
    exact hg
  have := desc_spec k (Ω := Ω) Γ(X, ⊤)
  rw [hφ] at this
  have hf' : f = X.isoSpec.hom ≫ g := by simp [g]
  rw [hf']
  exact desc_of_iso k X.isoSpec g this

end LateralTheory.E.LeafObjAffPf
end
end
