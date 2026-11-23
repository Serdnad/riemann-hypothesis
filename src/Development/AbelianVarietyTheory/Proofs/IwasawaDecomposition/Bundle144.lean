module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle086
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle140
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle134
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle106
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle091
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle110
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle397
public import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle141
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle116
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle015
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle142
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

section

noncomputable section
namespace GlobalTheory.MemLoc.TAct
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

set_option allowUnsafeReducibility true in
attribute [local irreducible] _root_.Formalism.Per.Acris _root_.Formalism.Per.Bcris

variable {l : ℕ} [Fact l.Prime]

theorem logA_mul {j : _root_.Formalism.Per.Acris l →+* _root_.Formalism.Per.BdRp l} (hj : IsCrisP j) {e e' : _root_.Formalism.Per.Fl l} {y y' : _root_.Formalism.Per.Acris l}
    (he : e.untilt = 1) (he' : e'.untilt = 1) (hy : IsLogA e y) (hy' : IsLogA e' y') :
    IsLogA (e * e') (y + y') := by
  have hee : (e * e').untilt = 1 := by rw [map_mul, he, he', one_mul]
  obtain ⟨z, _, hz, -, -⟩ := GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit l (e * e') hee
  have h := GlobalTheory.MemLoc.LogAdd.log_add l e e' (j y) (j y') (j z) he he'
    ((GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l e y he hy).2.2.2 j hj) ((GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l e' y' he' hy').2.2.2 j hj)
    ((GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l _ z hee hz).2.2.2 j hj)
  rw [← map_add (f := _)] at h
  rw [← GlobalTheory.T.acrisToBdRPlus_injective l j hj h]
  exact hz

theorem logA_pow {j : _root_.Formalism.Per.Acris l →+* _root_.Formalism.Per.BdRp l} (hj : IsCrisP j) {e : _root_.Formalism.Per.Fl l} {y : _root_.Formalism.Per.Acris l}
    (he : e.untilt = 1) (hy : IsLogA e y) (n : ℕ) : IsLogA (e ^ n) ((n : _root_.Formalism.Per.Acris l) * y) := by
  induction n with
  | zero =>
    have h1 : (1 : _root_.Formalism.Per.Fl l).untilt = 1 := map_one _
    obtain ⟨z, _, hz, -, -⟩ := GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit l 1 h1
    have h2 := logA_mul hj h1 h1 hz hz
    rw [one_mul] at h2
    have h3 := (GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l 1 z h1 hz).1 _ h2
    have h4 : z = 0 := by simpa using h3
    rw [pow_zero, Nat.cast_zero, zero_mul, ← h4]
    exact hz
  | succ n ih =>
    have := logA_mul hj (by rw [map_pow, he, one_pow]) he ih hy
    rw [pow_succ, Nat.cast_succ, add_mul, one_mul]
    exact this

theorem iter_pow (e : _root_.Formalism.Per.Fl l) (m : ℕ) :
    (((frobeniusEquiv (_root_.Formalism.Per.Fl l) l).symm)^[m] e) ^ (l ^ m) = e := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', pow_succ', pow_mul]
    have : ∀ x : _root_.Formalism.Per.Fl l, ((frobeniusEquiv (_root_.Formalism.Per.Fl l) l).symm x) ^ l = x := fun x => by
      rw [← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]
    rw [this, ih]

theorem eps_untilt (C : Core l) : C.ε.untilt = 1 := by
  have h := C.ε_root 0
  rw [C.ζ_zero, map_one] at h
  exact Subtype.ext h

theorem zeta_pow (C : Core l) (m : ℕ) : C.ζ m ^ (l ^ m) = 1 := by
  induction m with
  | zero => simp [C.ζ_zero]
  | succ m ih => rw [pow_succ', pow_mul, C.ζ_succ, ih]

theorem cong (C : Core l) (g : GQ l) (m : ℕ) : ∃ w : _root_.Formalism.Per.Acris l,
    sigA g C.t - ((PadicInt.toZModPow m (C.χ g : ℤ_[l])).val : _root_.Formalism.Per.Acris l) * C.t = (l : _root_.Formalism.Per.Acris l) ^ m * w := by
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  set a := (PadicInt.toZModPow m (C.χ g : ℤ_[l])).val with ha
  obtain ⟨b, hb⟩ : ∃ b, a + b = l ^ m := Nat.exists_eq_add_of_le (ZMod.val_lt _).le |>.imp fun _ h => h.symm
  set em := ((frobeniusEquiv (_root_.Formalism.Per.Fl l) l).symm)^[m] C.ε with hem
  have hε := eps_untilt C
  have hr : ((em.untilt : _root_.Formalism.Per.OC l) : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (C.ζ m) := C.ε_root m
  have he : (_root_.Formalism.Per.σF g em * em ^ b).untilt = 1 := by
    rw [map_mul, map_pow, GlobalTheory.RingBasics.untilt_σF]
    apply Subtype.ext
    have h1 : ((_root_.Formalism.Per.σO g em.untilt : _root_.Formalism.Per.OC l) : ℂ_[l]) = _root_.Formalism.Per.σC g (em.untilt : ℂ_[l]) :=
      GlobalTheory.RingIface.sigO_coe l g _
    have h2 : _root_.Formalism.Per.σC g (algebraMap (Om l) ℂ_[l] (C.ζ m)) = algebraMap (Om l) ℂ_[l] (g (C.ζ m)) :=
      GlobalTheory.RingBasics.σC_coe g _
    push_cast
    rw [h1, hr, h2, C.χ_cyc g m _ (zeta_pow C m), ← ha, ← map_pow, ← map_mul, ← pow_add, hb, zeta_pow, map_one]
  obtain ⟨z, _, hz, -, -⟩ := GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit l _ he
  have h1 := logA_pow C.j_cris he hz (l ^ m)
  have hgε : (_root_.Formalism.Per.σF g C.ε).untilt = 1 := by rw [GlobalTheory.RingBasics.untilt_σF, hε, map_one]
  have h2 := logA_mul C.j_cris hgε (by rw [map_pow, hε, one_pow])
    ((GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l _ _ hε C.t_log).2.1 g) (logA_pow C.j_cris hε C.t_log b)
  have h3 : (_root_.Formalism.Per.σF g em * em ^ b) ^ (l ^ m) = _root_.Formalism.Per.σF g C.ε * C.ε ^ b := by
    rw [mul_pow, ← map_pow, ← pow_mul, mul_comm b, pow_mul, hem, iter_pow]
  rw [h3] at h1
  have h4 := (GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l _ _ (by rw [map_mul, hgε, map_pow, hε, one_pow, one_mul]) h1).1 _ h2
  refine ⟨z - C.t, ?_⟩
  have h5 : (a : _root_.Formalism.Per.Acris l) + b = (l : _root_.Formalism.Per.Acris l) ^ m := by exact_mod_cast congrArg (Nat.cast : ℕ → _root_.Formalism.Per.Acris l) hb
  push_cast at h4
  linear_combination h4 - C.t * h5

theorem t_act : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (g : GQ l),
    sigA g C.t = algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.Acris l) (_root_.Formalism.Per.zA l (C.χ g : ℤ_[l])) * C.t := by
  intro l _ C g
  haveI := (acris_basic l).1
  rw [IsHausdorff.eq_iff_smodEq (I := Ideal.span {(l : _root_.Formalism.Per.Acris l)})]
  intro m
  obtain ⟨w, hw⟩ := cong C g m
  set x : ℤ_[l] := (C.χ g : ℤ_[l])
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hk : x - ((PadicInt.toZModPow m x).val : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow m : ℤ_[l] →+* ZMod (l ^ m)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at hk
  obtain ⟨c, hc⟩ := hk
  have hc' := congrArg ((algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.Acris l)).comp (_root_.Formalism.Per.zA l)) hc
  rw [map_mul, map_sub, map_pow, map_natCast, map_natCast, RingHom.comp_apply, RingHom.comp_apply] at hc'
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  refine ⟨w - algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.Acris l) (_root_.Formalism.Per.zA l c) * C.t, ?_⟩
  linear_combination - hw - C.t * hc'

end GlobalTheory.MemLoc.TAct
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ProjSpace GlobalTheory.Cartier

namespace GlobalTheory.ProjBlowup

variable {X W : Scheme.{0}} {L : LB X} {m : ℕ}

theorem exists_unit_appLE_sec (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (k l : L.ι) {T : W.Opens}
    (hk : T ≤ g ⁻¹ᵁ L.U k) (hl : T ≤ g ⁻¹ᵁ L.U l) : ∃ u : Γ(W, T)ˣ, ∀ j,
      (g.appLE (L.U k) T hk).hom ((σ j).f k) = u * (g.appLE (L.U l) T hl).hom ((σ j).f l) := by
  have hT : T ≤ g ⁻¹ᵁ (L.U k ⊓ L.U l) := le_inf hk hl
  refine ⟨Units.map (g.appLE (L.U k ⊓ L.U l) T hT).hom.toMonoidHom (L.g k l), fun j => ?_⟩
  have := congrArg (g.appLE (L.U k ⊓ L.U l) T hT).hom
    (sec_compat (σ j) k l (inf_le_left : L.U k ⊓ L.U l ≤ _) inf_le_right)
  rw [map_mul, appLE_resG, appLE_resG, appLE_resG] at this
  exact this

theorem exists_quot_of_span_eq {B : Type} [CommRing B] {ι : Type} [Fintype ι] {f : B} (hf : f ∈ nonZeroDivisors B)
    {s : ι → B} (h : Ideal.span {f} = Ideal.span (Set.range s)) :
    ∃ a c : ι → B, (∀ j, s j = a j * f) ∧ ∑ j, c j * a j = 1 := by
  have h1 : ∀ j, ∃ a, a * f = s j := fun j =>
    Ideal.mem_span_singleton'.1 (h ▸ Ideal.subset_span ⟨j, rfl⟩)
  choose a ha using h1
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 (h ▸ Ideal.mem_span_singleton_self f)
  refine ⟨a, c, fun j => (ha j).symm, (mul_cancel_right_mem_nonZeroDivisors hf).1 ?_⟩
  rw [one_mul, Finset.sum_mul]
  refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) hc
  rw [mul_assoc, ha]

theorem exists_mem_basicOpen_of_sum {A : W.Opens} {a c : Fin (m + 1) → Γ(W, A)} (h : ∑ j, c j * a j = 1)
    {y : W} (hy : y ∈ A) : ∃ j, y ∈ W.basicOpen (a j) := by
  by_contra hne
  have h1 : (W.presheaf.germ A y hy).hom (∑ j, c j * a j) ∈ IsLocalRing.maximalIdeal (W.presheaf.stalk y) := by

    rw [map_sum]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ fun hu => hne ⟨j, (W.mem_basicOpen _ y hy).2 hu⟩
  rw [h, map_one] at h1
  exact h1 isUnit_one

theorem exists_proportional (R : Type) [CommRing R] (X W : Scheme.{0}) (I : W.IdealSheafData) (L : LB X) (m : ℕ)
    (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (q : W ⟶ Sp R) (hσ : GeneratesAlong I σ g) (hI : FinalTheorems.EffCartier I) :
    ∃ ψ : W ⟶ PSpace R m, ψ ≫ PSpace.str R m = q ∧ Proportional σ g ψ := by
  obtain ⟨D, rfl⟩ := EffCartierData.exists_idealSheaf_eq hI
  have loc : ∀ y : W, ∃ (A : W.Opens) (k : L.ι) (hk : A ≤ g ⁻¹ᵁ L.U k) (i : D.ι) (hi : A ≤ D.U i)
      (a c : Fin (m + 1) → Γ(W, A)), y ∈ A ∧
      (∀ j, (g.appLE (L.U k) A hk).hom ((σ j).f k) = a j * resG W hi (D.f i)) ∧ ∑ j, c j * a j = 1 := by
    intro y
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (hσ.1.ge (Set.mem_univ y))
    obtain ⟨i, hi⟩ := D.exists_mem y
    obtain ⟨A, hy, hA⟩ := EffCartierData.exists_affine_le (V := g ⁻¹ᵁ L.U k ⊓ D.U i) (x := y) ⟨hk, hi⟩
    obtain ⟨a, c, h⟩ := exists_quot_of_span_eq (D.regular i _ (hA.trans inf_le_right))
      ((D.ideal_idealSheaf A i (hA.trans inf_le_right)).symm.trans (hσ.2 k A (hA.trans inf_le_left)))
    exact ⟨A.1, k, _, i, _, a, c, hy, h⟩
  choose A k hk i hi a c hy ha hc using loc
  have ha' : ∀ y {T : W.Opens} (hT : T ≤ A y) j, (g.appLE (L.U (k y)) T (hT.trans (hk y))).hom ((σ j).f (k y)) =
      resG W hT (a y j) * resG W (hT.trans (hi y)) (D.f (i y)) := fun y T hT j => by
    have := congrArg (resG W hT) (ha y j)
    rwa [map_mul, resG_appLE, resG_resG] at this
  have tr : ∀ y z, ∃ u : Γ(W, A y ⊓ A z)ˣ, ∀ j,
      resG W (inf_le_left : A y ⊓ A z ≤ A y) (a y j) =
        (u : Γ(W, A y ⊓ A z)) * resG W (inf_le_right : A y ⊓ A z ≤ A z) (a z j) := fun y z => by
    obtain ⟨u, hu⟩ := exists_unit_appLE_sec σ g (k y) (k z) (T := A y ⊓ A z)
      (inf_le_left.trans (hk y)) (inf_le_right.trans (hk z))
    have hy' : A y ⊓ A z ≤ D.U (i y) := inf_le_left.trans (hi y)
    have hz' : A y ⊓ A z ≤ D.U (i z) := inf_le_right.trans (hi z)
    refine ⟨u * Units.map (resG W (le_inf hz' hy')).toMonoidHom (D.trans (i z) (i y)), fun j => ?_⟩
    refine ((D.regular (i y)).resG hy').mul_right_cancel ?_
    have e := hu j
    rw [ha' y inf_le_left, ha' z inf_le_right, D.trans_spec_on (i z) (i y) hz' hy'] at e
    rw [e]
    change _ = (u : Γ(W, A y ⊓ A z)) * resG W (le_inf hz' hy') (D.trans (i z) (i y)) * _ * _
    ring
  choose u hu using tr
  let B : LB W := { ι := W, U := A, g := u }
  let t : Fin (m + 1) → B.Sec := fun j => { f := fun y => a y j, compat := fun y z => hu y z j }
  have ht : ⨆ j, Out.nonzeroLocus (t j) = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨j, hj⟩ := exists_mem_basicOpen_of_sum (hc y) (hy y)
    exact Opens.mem_iSup.2 ⟨j, (mem_nonzeroLocus_iff (t j) y (hy y)).2 hj⟩
  refine ⟨toProj q t ht, toProj_str q t ht, fun V l hl p hp j => ext_germ fun y hyV => ?_⟩
  have hm : y ∈ V ⊓ A y := ⟨hyV, hy y⟩
  have key : resG W (inf_le_left : V ⊓ A y ≤ V) ((g.appLE (L.U l) V hl).hom ((σ j).f l)) =
      resG W inf_le_left (pullRatio (toProj q t ht) V p hp j * (g.appLE (L.U l) V hl).hom ((σ p).f l)) := by
    obtain ⟨v, hv⟩ := exists_unit_appLE_sec σ g l (k y) (T := V ⊓ A y)
      (inf_le_left.trans hl) (inf_le_right.trans (hk y))
    have e : resG W inf_le_right (a y j) = _ * resG W inf_le_right (a y p) :=
      sec_eq_pullRatio_toProj_mul q t ht p j y (W := V ⊓ A y) (inf_le_left.trans hp) inf_le_right
    rw [map_mul, resG_appLE, resG_appLE, resG_pullRatio, hv, hv, ha' y inf_le_right, ha' y inf_le_right, e]
    ring
  have := congrArg (W.presheaf.germ _ y hm).hom key
  rwa [germ_resG, germ_resG] at this

end GlobalTheory.ProjBlowup
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HeckeFrob

theorem rt_mul_apply {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (a b : GAf L n) (f : GAf L n → W) :
    NG.rt L n (a * b) f = NG.rt L n a (NG.rt L n b f) := by
  funext g; simp [NG.rt, mul_assoc]

theorem exists_ne_zero_of_irrRep {G : Type} [Group G] [TopologicalSpace G] (σ : GlobalTheory.SmGL.IrrRep G) :
    ∃ a : σ.V, a ≠ 0 := by
  by_contra hne
  push Not at hne
  have h := σ.irr
  have : Subsingleton σ.V := ⟨fun a b => by rw [hne a, hne b]⟩
  exact (bot_ne_top : (⊥ : Subrepresentation σ.ρ) ≠ ⊤)
    (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem mem_iSup_range_locMap : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (s : SplitPlace L)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T : σ.V →ₗ[ℂ] (GAf L n → π.W)),
    Function.Injective T → (∀ a, T a ∈ π.S) → GlobalTheory.HeckeFrob.IsLocMap s σ i T →
    ∀ g ∈ π.S, g ∈ ⨆ (T' : {T' : σ.V →ₗ[ℂ] (GAf L n → π.W) // (∀ a, T' a ∈ π.S) ∧ GlobalTheory.HeckeFrob.IsLocMap s σ i T'}),
      LinearMap.range T'.1 := by
  intro L _ _ _ n π s σ i T hTi hTS hT g hg
  set I : Submodule ℂ (GAf L n → π.W) :=
    ⨆ (T' : {T' : σ.V →ₗ[ℂ] (GAf L n → π.W) // (∀ a, T' a ∈ π.S) ∧ GlobalTheory.HeckeFrob.IsLocMap s σ i T'}),
      LinearMap.range T'.1 with hIdef
  have hIS : I ≤ π.S := iSup_le fun T' => by
    rintro _ ⟨a, rfl⟩
    exact T'.2.1 a
  have hsub : NG.IsSubrep π.ρ I := by
    refine ⟨hIS.trans π.irrS.1.le, ?_⟩
    intro h f hf
    obtain ⟨x, y, hx, hy, rfl⟩ := (GlobalTheory.SplitAdelic.main L n s).1 h
    have hcomm := (GlobalTheory.SplitAdelic.main L n s).2.1
    refine Submodule.iSup_induction (motive := fun f => NG.rt L n (x * y) f ∈ I) _ hf ?_ ?_ ?_
    · rintro T' _ ⟨a, rfl⟩
      let T'' : σ.V →ₗ[ℂ] (GAf L n → π.W) := (NG.rt L n y).comp T'.1
      have hT'' : (∀ a, T'' a ∈ π.S) ∧ GlobalTheory.HeckeFrob.IsLocMap s σ i T'' := by
        refine ⟨fun a => π.irrS.1.stable y _ (T'.2.1 a), fun z hz a => ?_⟩
        change NG.rt L n y (T'.1 _) = NG.rt L n z (NG.rt L n y (T'.1 a))
        rw [T'.2.2 z hz a, ← rt_mul_apply, ← rt_mul_apply, (hcomm z y hz hy).eq]
      have key : NG.rt L n (x * y) (T'.1 a) =
          T'' (σ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) a) := by
        rw [hT''.2 x hx a, rt_mul_apply]
        rfl
      rw [key]
      exact Submodule.mem_iSup_of_mem ⟨T'', hT''⟩ ⟨_, rfl⟩
    · rw [map_zero]; exact zero_mem _
    · intro f₁ f₂ h₁ h₂
      rw [map_add]; exact add_mem h₁ h₂
  rcases π.irrS.2.2 I hsub hIS with hbot | htop
  · exfalso
    obtain ⟨a, ha⟩ := exists_ne_zero_of_irrRep σ
    have hmem : T a ∈ I := Submodule.mem_iSup_of_mem ⟨T, hTS, hT⟩ ⟨a, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact ha (hTi (hmem.trans (map_zero T).symm))
  · rw [htop]; exact hg

end GlobalTheory.HeckeFrob
end

section

open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.posDef_map_embedding_of_positiveAtPlace : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K), Formalism.L2.Rows.PosAt H v → (H.map v.embedding).PosDef := by
  first | exact @GlobalTheory.AmbTiePosDef.posDef_map_of_posAt | exact GlobalTheory.AmbTiePosDef.posDef_map_of_posAt | (intros; apply GlobalTheory.AmbTiePosDef.posDef_map_of_posAt <;> assumption)
end

section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.exists_finExt_conj_entries_mem_intOf : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] (a : ℕ) (ρ : Γ →* GL (Fin a) (PadicAlgCl l)), Continuous (fun g => ((ρ g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) → ∃ (L : Loc.FinExt l) (P : GL (Fin a) (PadicAlgCl l)), ∀ g i k, ((P⁻¹ * ρ g * P : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i k ∈ Formalism.L2.TwC.intOf l L.1 := by
  first | exact @GlobalTheory.IntegralConjFinExt.exists_finExt_conj_intOf | exact GlobalTheory.IntegralConjFinExt.exists_finExt_conj_intOf | (intros; apply GlobalTheory.IntegralConjFinExt.exists_finExt_conj_intOf <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_trait_nonlocal_torusExtension' : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G →
    ∀ (W : Type) [CommRing W] [IsLocalRing W] (g : R →+* W), ¬ IsLocalHom g →
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (ψ : R →+* V)
      (Ω : Type) (_ : Field Ω) (α : FractionRing V →+* Ω) (β : W →+* Ω),
      IsLocalHom ψ ∧ (∀ x ∈ maximalIdeal W, β x = 0) ∧
      (α.comp (algebraMap V (FractionRing V))).comp ψ = β.comp g ∧
      Nonempty (TorusExtension ((Over.pullback (spMap ((algebraMap V (FractionRing V)).comp ψ))).obj G)) := by
  first | exact @GlobalTheory.exists_trait_nonlocal_torusExtension | exact GlobalTheory.exists_trait_nonlocal_torusExtension | (intros; apply GlobalTheory.exists_trait_nonlocal_torusExtension <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.InertiaFix

open GlobalTheory.TorusExt GlobalTheory.UnramTorsion ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] gtGroup

theorem sigma_fixes_abelianPart : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult →
    ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (O : ValuationSubring F) (φ : R →+* O),
    (∀ r, (φ r : F) = algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r)) →
    ∀ (k : ℕ), IsUnit (k : O) → ∀ (σ : F →ₐ[FractionRing R] F), (∀ x ∈ O, O.valuation (σ x - x) < 1) →
    ∀ p : QkPt D F k, spMap σ.toRingHom ≫ p.g.b.left = p.g.b.left := by
  intro R _ _ D hB F _ _ O φ hφ k hk σ hσ p
  have memO : ∀ x : O, σ (x : F) ∈ O := fun x => by
    have h1 : σ (x : F) - x ∈ O := (O.valuation_le_one_iff _).1 (hσ x x.2).le
    have := O.add_mem _ _ h1 x.2
    simpa using this
  let σO : O →+* O := (σ.toRingHom.comp O.subtype).codRestrict O.toSubring memO
  have hσO : ∀ x : O, ((σO x : O) : F) = σ x := fun _ => rfl
  have hσφ : σO.comp φ = φ := RingHom.ext fun r => Subtype.ext (by
    show σ ((φ r : O) : F) = (φ r : F)
    rw [hφ]; exact σ.commutes _)
  have hres : (IsLocalRing.residue O).comp σO = IsLocalRing.residue O := RingHom.ext fun x => by
    show IsLocalRing.residue O (σO x) = IsLocalRing.residue O x
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    apply (ValuationSubring.valuation_lt_one_iff O _).2
    have : ((σO x - x : O) : F) = σ (x : F) - x := by push_cast; rfl
    rw [this]; exact hσ x x.2
  have hsub : σ.toRingHom.comp O.subtype = O.subtype.comp σO := rfl
  let ρ : TF (R := R) F ⟶ Over.mk (spMap φ) := Over.homMk (spMap O.subtype) (by
    show spMap O.subtype ≫ spMap φ = jFK (R := R) F ≫ jK R
    rw [jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hφ)
  obtain ⟨b', hb'⟩ := exists_extend O φ ρ rfl p.g.b
  let σ' : Over.mk (spMap φ) ⟶ Over.mk (spMap φ) := Over.homMk (spMap σO) (by
    show spMap σO ≫ spMap φ = spMap φ
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hσφ])
  have := D.P.isAb.proper
  have : D.P.A.left.IsSeparated := ⟨by rw [← terminal.comp_from D.P.A.hom]; infer_instance⟩
  haveI := D.P.isAb.comm
  have hd : IsDominant (spMap O.subtype) := by
    constructor
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical O.subtype).2
      (by rw [(RingHom.injective_iff_ker_eq_bot O.subtype).1 Subtype.val_injective]; exact bot_le)
  have hpk : p.g.b ^ k = cP D _ p.y := by
    rw [← nsmul_b, qk_nsmul hB, iota_b]
  have hpow : b' ^ k = cP D _ p.y := by
    have e : ρ ≫ b' ^ k = ρ ≫ cP D _ p.y := by
      rw [comp_cP, ← hpk, ← hb']; exact map_pow (preHom ρ) _ _
    apply Over.OverMorphism.ext
    haveI : IsReduced (Over.mk (spMap φ)).left := (inferInstance : IsReduced (Sp O))
    exact ext_of_isDominant (spMap O.subtype) (congrArg CommaMorphism.left e)
  have hpow' : b' ^ k = (σ' ≫ b') ^ k := by
    have e2 : σ' ≫ b' ^ k = (σ' ≫ b') ^ k := map_pow (preHom σ') b' k
    rw [← e2, hpow, comp_cP]
  have hcl : spMap (IsLocalRing.residue O) ≫ b'.left = spMap (IsLocalRing.residue O) ≫ (σ' ≫ b').left := by
    rw [Over.comp_left, ← Category.assoc]
    congr 1
    show _ = spMap (IsLocalRing.residue O) ≫ spMap σO
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hres]
  have heq : b' = σ' ≫ b' := GlobalTheory.T.smoothCommGroupScheme_eq_of_pow_eq_of_closedPoint (Sp R) D.P.A D.P.isAb.smooth O (spMap φ) k hk b' (σ' ≫ b') hpow'
    (IsLocalRing.ResidueField O) (IsLocalRing.residue O) inferInstance hcl
  rw [← hb', Over.comp_left]
  show spMap σ.toRingHom ≫ spMap O.subtype ≫ b'.left = spMap O.subtype ≫ b'.left
  conv_rhs => rw [heq]
  rw [← Category.assoc, Over.comp_left, ← Category.assoc]
  congr 1
  show spMap σ.toRingHom ≫ spMap O.subtype = spMap O.subtype ≫ spMap σO
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

end GlobalTheory.InertiaFix
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.inertia_two_places_over_same_prime_trivial_meet : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A A' : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A P → IsPlaceOver (F := E) A' P → ∀ σ ∈ Ine (F := E) A, σ ∈ Ine (F := E) A' → σ ≠ 1 → A' = A := by
  first | exact @GlobalTheory.InertiaTwoPlaces.eq_of_mem_Ine_of_mem_Ine | exact GlobalTheory.InertiaTwoPlaces.eq_of_mem_Ine_of_mem_Ine | (intros; apply GlobalTheory.InertiaTwoPlaces.eq_of_mem_Ine_of_mem_Ine <;> assumption)
end
