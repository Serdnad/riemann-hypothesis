module

import Development.EtaleCohomology.EtaleSheaves.KummerSequence.TwLocGenPfSec
public import Development.EtaleCohomology.TateTwists.Bundle004
public import Development.EtaleCohomology.TateTwists.Bundle005
public import Development.EtaleCohomology.TateTwists.Bundle010
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Development.EtaleCohomology.TateTwists.Bundle012
public import Development.EtaleCohomology.TateTwists.Bundle006
public import Development.EtaleCohomology.TateTwists.Bundle013
public import Development.EtaleCohomology.TateTwists.Bundle011
public import Development.EtaleCohomology.TateTwists.Bundle015
public import Development.EtaleCohomology.TateTwists.Bundle014
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct GlobalTheory.EtC GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec

namespace LateralTheory.EtaleFoundations.TwSecLocPf

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem loc_true (U : Scheme.{0}) : Loc U fun _ _ => True :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun _ _ _ => trivial⟩

theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hS'⟩ := hP
  obtain ⟨T, hT, hT'⟩ := hQ
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ⟨hS' V g hg.1, hT' V g hg.2⟩⟩

theorem loc_bind {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} {Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (hP : Loc U P) (hQ : ∀ V (g : V ⟶ U), P V g → Loc V fun W h => Q W (h ≫ g)) : Loc U Q := by
  obtain ⟨S, hS, hS'⟩ := hP
  choose T hT hT' using fun V (g : V ⟶ U) (hg : S.arrows g) => hQ V g (hS' V g hg)
  refine ⟨Sieve.bind S.arrows T, Scheme.etaleTopology.bind_covering hS hT, ?_⟩
  rintro W _ ⟨V, h, g, hg, hh, rfl⟩
  exact hT' V g hg W h hh

theorem loc_surj {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0})
    (y : Sec (ofRings R M) U) :
    Loc U fun V g => ∃ x : M.obj Γ(V, ⊤), Sec.res g y = ofRings.sec M V x := by
  have h := Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) y
  refine ⟨_, h, fun V g hg => ?_⟩
  obtain ⟨x, hx⟩ := hg
  exact ⟨x, hx.symm⟩

end LateralTheory.EtaleFoundations.TwSecLocPf

namespace LateralTheory.EtaleFoundations.TwSecLocPf

def ZarPow : Prop := ∀ (q : ℕ) [NeZero q] (V : Scheme.{0}) (ζ ξ : Prim q Γ(V, ⊤)),
  Loc V fun W h => ∃ a : (ZMod q)ˣ, (ξ.map h.appTop.hom).1 = (ζ.map h.appTop.hom).1 ^ (a : ZMod q).val

theorem ulift_smul_eq_nsmul {q : ℕ} [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    (r : ULift.{1} (ZMod q)) (m : M) : r • m = r.down.val • m := by
  have : r = ((r.down.val : ℕ) : ULift.{1} (ZMod q)) := by
    cases r with
    | up a =>
      change ULift.up a = ULift.up ((a.val : ℕ) : ZMod q)
      rw [ZMod.natCast_zmod_val]
  conv_lhs => rw [this]
  exact Nat.cast_smul_eq_nsmul _ _ _

theorem twF_map_mk (q : ℕ) (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) (x : Prim q A →₀ ULift.{1} (ZMod q)) :
    ((twF q i).map f).hom (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.hom) x) : (twF q i).obj B) := rfl

theorem twF_single_pow (q : ℕ) [NeZero q] (i : ℤ) (A : CommRingCat.{0}) (ζ ξ : Prim q A) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) (b : ULift.{1} (ZMod q)) :
    (Submodule.Quotient.mk (Finsupp.single ξ b) : (twF q i).obj A) =
      (b.down * ((a ^ i : (ZMod q)ˣ) : ZMod q)).val • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj A) := by
  apply LateralTheory.E.H2CurveOrder.TwLocGenPfSec.twF_single_pow <;> assumption

theorem twF_loc (hZ : ZarPow) (q : ℕ) [NeZero q] (i : ℤ) (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤))
    (x : (twF q i).obj Γ(V, ⊤)) :
    Loc V fun W h => ∃ c : ℕ, ((twF q i).map h.appTop).hom x =
      c • (Submodule.Quotient.mk (Finsupp.single (ζ.map h.appTop.hom) 1) : (twF q i).obj Γ(W, ⊤)) := by
  apply LateralTheory.E.H2CurveOrder.TwLocGenPfSec.twF_loc <;> assumption

theorem TwSecLoc_of (hZ : ZarPow) : LateralTheory.EtaleFoundations.TwLocPf.TwSecLoc := by
  intro q _ i U ζ y
  refine loc_bind (loc_surj (twF q i) U y) fun V g ⟨x, hx⟩ => ?_
  refine loc_mono (twF_loc hZ q i V (ζ.map g.appTop.hom) x) fun W h ⟨c, hc⟩ => ⟨c, ?_⟩
  have e : Sec.res (h ≫ g) y = Sec.res h (Sec.res g y) := by
    simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  have hp : (ζ.map g.appTop.hom).map h.appTop.hom = ζ.map (h ≫ g).appTop.hom := by
    apply Subtype.ext
    simp [Prim.map]
    rfl
  rw [e]
  refine (congrArg (fun z => ((tw q i).obj.map h.op).hom z) hx).trans ?_
  have hres : Sec.res h (ofRings.sec (twF q i) V x) =
      ofRings.sec (twF q i) W (((twF q i).map h.appTop).hom x) := by
    have hn := congrArg (fun f => f.hom x)
      ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality h.op)
    simp only [ModuleCat.hom_comp] at hn
    exact hn.symm
  refine hres.trans ?_
  rw [hc, ← hp]
  unfold twGen ofRings.sec
  exact map_nsmul _ _ _

end LateralTheory.EtaleFoundations.TwSecLocPf
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.PrimLocPf

theorem ring_core {R K : Type} [CommRing R] [Field K] (φ : R →+* K) (q : ℕ) [NeZero q]
    (hq : IsUnit (q : R)) (ζ x : R) (hζ : Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0)
    (hx : x ^ q = 1) :
    ∃ n < q, ∃ s : R, φ s ≠ 0 ∧ s * (x - ζ ^ n) = 0 ∧ IsPrimitiveRoot (φ ζ) q := by
  have hqK : (q : K) ≠ 0 := by
    have := hq.map φ; simpa using this.ne_zero
  have : NeZero (q : K) := ⟨hqK⟩
  have hζK : IsPrimitiveRoot (φ ζ) q := by
    rw [← Polynomial.isRoot_cyclotomic_iff]
    have h := Polynomial.aeval_algHom_apply φ.toIntAlgHom ζ (Polynomial.cyclotomic q ℤ)
    rw [hζ, map_zero] at h
    simpa [Polynomial.IsRoot, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
      Polynomial.map_cyclotomic] using h
  have hζq : ζ ^ q = 1 := by
    obtain ⟨c, hc⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
    have h := congrArg (Polynomial.aeval ζ) hc
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, hζ, zero_mul] at h
    exact sub_eq_zero.mp h
  have hxK : (φ x) ^ q = 1 := by rw [← map_pow, hx, map_one]
  obtain ⟨n, hn, hnx⟩ := hζK.eq_pow_of_pow_eq_one hxK
  set t := x * ζ ^ (q - n) with ht
  refine ⟨n, hn, ∑ i ∈ Finset.range q, t ^ i, ?_, ?_, hζK⟩
  · have h1 : φ t = 1 := by
      rw [ht, map_mul, map_pow, ← hnx, ← pow_add, Nat.add_sub_cancel' hn.le, hζK.pow_eq_one]

    simp [map_sum, map_pow, h1, hqK]
  · have hg : (∑ i ∈ Finset.range q, t ^ i) * (t - 1) = 0 := by
      rw [geom_sum_mul, ht, mul_pow, hx, ← pow_mul, mul_comm (q - n) q, pow_mul, hζq, one_pow,
        one_mul, sub_self]
    have : x - ζ ^ n = (t - 1) * ζ ^ n := by
      rw [ht, sub_mul, mul_assoc, ← pow_add, Nat.sub_add_cancel hn.le, hζq, mul_one, one_mul]
    rw [this, ← mul_assoc, hg, zero_mul]

theorem isUnit_of_basicOpen_top (X : Scheme.{0}) (f : Γ(X, ⊤)) (h : X.basicOpen f = ⊤) :
    IsUnit f := by
  have key : ∀ (O : X.Opens) (_ : O = ⊤) (hle : O ≤ ⊤),
      IsUnit (X.presheaf.map (homOfLE hle).op f) → IsUnit f := by
    intro O hO; subst hO; intro hle hu; simpa using hu
  exact key _ h (X.basicOpen_le f) (X.toRingedSpace.isUnit_res_basicOpen f)

theorem affine_nbhd (U : Scheme.{0}) (s : Γ(U, ⊤)) (y : U) (hy : y ∈ U.basicOpen s) :
    ∃ (V : Scheme.{0}) (g : V ⟶ U), IsAffine V ∧ Etale g ∧ y ∈ Set.range g ∧
      IsUnit (g.appTop.hom s) := by
  obtain ⟨W, hWa, hyW, hW⟩ : ∃ W : U.Opens, IsAffineOpen W ∧ y ∈ W ∧ W ≤ U.basicOpen s :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp U.isBasis_affineOpens) hy
  refine ⟨W, Scheme.Opens.ι W, hWa, inferInstance, by simpa using hyW, ?_⟩
  apply isUnit_of_basicOpen_top
  rw [← Scheme.preimage_basicOpen_top]
  ext z
  simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
  exact hW (by have h := Set.mem_range_self (f := W.ι) z; simpa using h)

theorem cyc_pow_eq_one {R : Type} [CommRing R] (q : ℕ) (ζ : R)
    (hζ : Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) : ζ ^ q = 1 := by
  obtain ⟨c, hc⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ) hc
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, hζ, zero_mul] at h
  exact sub_eq_zero.mp h

theorem mono_pow {U : Scheme.{0}} (x ζ : Γ(U, ⊤)) : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V),
    (∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ ^ a) →
    ∃ a : ℕ, (k ≫ g).appTop.hom x = (k ≫ g).appTop.hom ζ ^ a := by
  rintro V W g k ⟨a, ha⟩
  refine ⟨a, ?_⟩
  show k.appTop.hom (g.appTop.hom x) = (k.appTop.hom (g.appTop.hom ζ)) ^ a
  rw [ha, map_pow]

theorem part3 (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤))
    (hx : x ^ q = 1) : Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a := by
  rw [etale_sheaf_section_locally_iff_of_presheaf_facts U _ (mono_pow x ζ.1)]
  intro y
  obtain ⟨n, -, s, hs, hsx, -⟩ := ring_core (U.Γevaluation y).hom q ζ.2.1 ζ.1 x ζ.2.2 hx
  have hy : y ∈ U.basicOpen s := (U.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) y trivial s).mp hs
  obtain ⟨V, g, hV, hg, hyr, hu⟩ := affine_nbhd U s y hy
  refine ⟨V, g, hV, hg, hyr, n, ?_⟩
  have h := congrArg g.appTop.hom hsx
  rw [map_mul, map_sub, map_pow, map_zero] at h
  exact sub_eq_zero.mp (hu.mul_right_eq_zero.mp h)

theorem mono_unit {q : ℕ} {U : Scheme.{0}} (x ζ : Γ(U, ⊤)) :
    ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V),
    (∃ a : (ZMod q)ˣ, g.appTop.hom x = g.appTop.hom ζ ^ (a : ZMod q).val) →
    ∃ a : (ZMod q)ˣ, (k ≫ g).appTop.hom x = (k ≫ g).appTop.hom ζ ^ (a : ZMod q).val := by
  rintro V W g k ⟨a, ha⟩
  refine ⟨a, ?_⟩
  show k.appTop.hom (g.appTop.hom x) = (k.appTop.hom (g.appTop.hom ζ)) ^ (a : ZMod q).val
  rw [ha, map_pow]

theorem part2 (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) :
    Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val := by
  rw [etale_sheaf_section_locally_iff_of_presheaf_facts U _ (mono_unit ξ.1 ζ.1)]
  intro y
  obtain ⟨n, hn, s, hs, hsx, hζK⟩ := ring_core (U.Γevaluation y).hom q ζ.2.1 ζ.1 ξ.1 ζ.2.2
    (cyc_pow_eq_one q ξ.1 ξ.2.2)
  obtain ⟨-, -, -, -, -, hξK⟩ := ring_core (U.Γevaluation y).hom q ξ.2.1 ξ.1 ξ.1 ξ.2.2
    (cyc_pow_eq_one q ξ.1 ξ.2.2)
  have hφ : (U.Γevaluation y).hom ξ.1 = (U.Γevaluation y).hom ζ.1 ^ n := by
    have h := congrArg (U.Γevaluation y).hom hsx
    rw [map_mul, map_sub, map_pow, map_zero] at h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hs)
  have hcop : n.Coprime q := (hζK.pow_iff_coprime (Nat.pos_of_neZero q) n).mp (hφ ▸ hξK)
  have hy : y ∈ U.basicOpen s :=
    (U.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) y trivial s).mp hs
  obtain ⟨V, g, hV, hg, hyr, hu⟩ := affine_nbhd U s y hy
  refine ⟨V, g, hV, hg, hyr, ZMod.unitOfCoprime n hcop, ?_⟩
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hn]
  have h := congrArg g.appTop.hom hsx
  rw [map_mul, map_sub, map_pow, map_zero] at h
  exact sub_eq_zero.mp (hu.mul_right_eq_zero.mp h)

end LateralTheory.EtaleFoundations.PrimLocPf

namespace LateralTheory.EtaleFoundations

def EtaleLocallyExistsPrimitiveRootOfUnityOfInvertibleOrder : Prop :=
  ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) →
    Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))

def EtaleLocallyKummerRootsOfUnits : Prop :=
  ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ,
    Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u

theorem etale_locally_roots_of_unity_structure_of_exists_and_kummer (h1 : EtaleLocallyExistsPrimitiveRootOfUnityOfInvertibleOrder) (h4 : EtaleLocallyKummerRootsOfUnits) :
    EtalePrimitiveRootsExistLocally := by
  intro q _ U
  exact ⟨h1 q U, PrimLocPf.part2 q U, fun ζ x hx => PrimLocPf.part3 q U ζ x hx,
    fun hq u => h4 q U hq u⟩

end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

def LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapLocallySurjective : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ) (T : Shv (ZMod q)) (μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl T)),
    μ.IsTensor → i + j = k → ∀ φ : tw q k ⟶ T, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map (sglι T) (Sec.map φ (twGen k ζ)) =
        μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) →
    ∀ (U : Scheme.{0}) (b : Sec T U), Loc U fun V g => ∃ a : Sec (tw q k) V, Sec.map φ a = Sec.res g b

def LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapSectionsInjective : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ) (T : Shv (ZMod q)) (μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl T)),
    μ.IsTensor → i + j = k → ∀ φ : tw q k ⟶ T, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map (sglι T) (Sec.map φ (twGen k ζ)) =
        μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) →
    ∀ (U : Scheme.{0}) (a : Sec (tw q k) U), Sec.map φ a = 0 → Loc U fun _ g => Sec.res g a = 0

theorem LateralTheory.EtaleFoundations.etale_tate_twist_generator_map_isIso_of_inj_surj (hme : LateralTheory.EtaleFoundations.EtaleSheafMonoEpiSectionCriteria)
    (hs : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapLocallySurjective) (hi : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapSectionsInjective) :
    LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapIsIso := by
  intro q _ i j k T μ hμ hk φ hφ
  have h := hme (ZMod q) φ
  have hm : Mono φ := h.2.1.2 (hi q i j k T μ hμ hk φ hφ)
  have he : Epi φ := h.2.2.1.2 (hs q i j k T μ hμ hk φ hφ)
  exact isIso_of_mono_of_epi φ
end
end

section

namespace LateralTheory.Fin.EtaleComplexPairingFlipExists
theorem etale_cup_product_flip_exists_of_components : LateralTheory.EtaleFoundations.EtaleComplexPairingFlipExists := by
  apply LateralTheory.EtaleFoundations.etale_complex_pairing_flip_exists
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleComplexPairingFlipExists := etale_cup_product_flip_exists_of_components
end LateralTheory.Fin.EtaleComplexPairingFlipExists
end

section

namespace LateralTheory.Fin.EtaleCochainExistsOfNaturalEvaluation
theorem etale_evaluation_map_construction_of_components : LateralTheory.EtaleFoundations.EtaleCochainExistsOfNaturalEvaluation := by
  apply LateralTheory.EtaleFoundations.etale_chain_cochain_exists_of_eval_data
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleCochainExistsOfNaturalEvaluation := etale_evaluation_map_construction_of_components
end LateralTheory.Fin.EtaleCochainExistsOfNaturalEvaluation
end

section

namespace LateralTheory.Fin.EtaleSheafSectionsSeparatedAndGlue
theorem etale_sections_glue_over_cover_of_components : LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue := by
  apply LateralTheory.EtaleFoundations.etale_sheaf_sections_glue_of_forget_isSheaf
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue := etale_sections_glue_over_cover_of_components
end LateralTheory.Fin.EtaleSheafSectionsSeparatedAndGlue
end

section

namespace LateralTheory.Fix.EtaleSchemeGlobalSectionCohomologyClass

theorem delta : LateralTheory.EtaleFoundations.EtaleSimplicialCochainEvaluationDifferentialFormula := LateralTheory.EtaleFoundations.etale_chain_cochain_eval_differential_formula_holds

theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleSchemeGlobalSectionCohomologyClass :=
  LateralTheory.EtaleFoundations.etaleSimplicialCochain_scheme_class_of_evaluation_properties LateralTheory.EtaleFoundations.etale_simplicial_chains_cochain_mk_of_compatible_sections delta
    LateralTheory.EtaleFoundations.etaleSimplicialCochain_evaluation_properties_of_components
    (LateralTheory.EtaleFoundations.etaleSimplicialScheme_cocycle_vanishing_at_id_isCoboundary_of_evaluati LateralTheory.EtaleFoundations.etale_simplicial_chains_cochain_mk_of_compatible_sections delta
      LateralTheory.EtaleFoundations.etaleSimplicialCochain_evaluation_properties_of_components)

end LateralTheory.Fix.EtaleSchemeGlobalSectionCohomologyClass
end

section

namespace LateralTheory.Fin.EtaleSheafificationSectionsLocallyFromPresheaf
theorem etale_sheaf_localization_properties_of_components : LateralTheory.EtaleFoundations.EtaleSheafificationSectionsLocallyFromPresheaf := by
  apply LateralTheory.EtaleFoundations.ShfLocPf.etale_sheaf_sections_eq_of_locally_eq
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleSheafificationSectionsLocallyFromPresheaf := etale_sheaf_localization_properties_of_components
end LateralTheory.Fin.EtaleSheafificationSectionsLocallyFromPresheaf
end

section

namespace LateralTheory.Fin.EtaleTateTwistSheafFlat
theorem etale_roots_of_unity_twist_flat_of_local_free : LateralTheory.EtaleFoundations.EtaleTateTwistSheafFlat := by
  apply LateralTheory.EtaleFoundations.etale_tate_twist_sections_flat_of_quotient_iso
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleTateTwistSheafFlat := etale_roots_of_unity_twist_flat_of_local_free
end LateralTheory.Fin.EtaleTateTwistSheafFlat
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace LateralTheory.EtaleFoundations.TwMulGenMap

def twSec : Prop :=
  ∀ (q : ℕ) [NeZero q] (i : ℤ), (∀ (U : Scheme.{0}) (y : Sec (tw q i) U), Loc U fun V g => Sec.res g y = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g y = c • twGen i ζ) ∧ (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U), Loc U fun V g => ∃ c : ℕ, Sec.res g y = c • twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c : ℕ), c • twGen i ζ = 0 → q ∣ c) ∧ (∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)), Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → twGen i ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • twGen i ζ) ∧ ∀ (M : Shv (ZMod q)) (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom)) → (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → e U ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • e U ζ) → ∃! φ : tw q i ⟶ M, ∀ U ζ, Sec.map φ (twGen i ζ) = e U ζ

theorem nsmul_congr {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (n m : ℕ)
    (h : (n : ZMod q) = m) (x : M) : n • x = m • x := by
  have hn : (n : ULift.{1} (ZMod q)) = ULift.up (n : ZMod q) := by ext; simp
  have hm : (m : ULift.{1} (ZMod q)) = ULift.up (m : ZMod q) := by ext; simp
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), ← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), hn, hm, h]

theorem val_mul {q : ℕ} [NeZero q] (a : (ZMod q)ˣ) (i j k : ℤ) (hk : i + j = k) :
    ((((a ^ i : (ZMod q)ˣ) : ZMod q).val * ((a ^ j : (ZMod q)ˣ) : ZMod q).val : ℕ) : ZMod q) =
      ((((a ^ k : (ZMod q)ˣ) : ZMod q).val : ℕ) : ZMod q) := by
  rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ← Units.val_mul,
    ← zpow_add, hk]

theorem sec_map_nsmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (n : ℕ)
    (x : Sec F U) : Sec.map φ (n • x) = n • Sec.map φ x := map_nsmul _ _ _

open LateralTheory.EtaleFoundations.TwMulPf in
theorem genMap_of (h : twSec) : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapExists := by
  intro q _ i j k T μ _ hk
  let π : (sgl T).X 0 ⟶ T := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 T).hom
  have hπ : π ≫ sglι T = 𝟙 _ := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 T).hom_inv_id
  let e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec T U := fun U ζ =>
    Sec.map π (μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ)))
  have hnat : ∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom) := by
    intro V U g ζ
    simp only [e]
    rw [sec_res_map, μ.nat, sec_res_map, sec_res_map, (h q i).2.2.2.1, (h q j).2.2.2.1]
  have hrel : ∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val →
      e U ξ = ((a ^ k : (ZMod q)ˣ) : ZMod q).val • e U ζ := by
    intro U ζ ξ a hξ
    simp only [e]
    rw [(h q i).2.2.2.2.1 U ζ ξ a hξ, (h q j).2.2.2.2.1 U ζ ξ a hξ]
    rw [sec_map_nsmul, sec_map_nsmul, map_nsmul, map_nsmul, LinearMap.smul_apply, smul_smul,
      sec_map_nsmul, mul_comm, nsmul_congr _ _ (val_mul a i j k hk)]
  obtain ⟨φ, hφ, -⟩ := (h q k).2.2.2.2.2 T e hnat hrel
  refine ⟨φ, fun U ζ => ?_⟩
  rw [hφ U ζ]
  simp only [e]
  rw [sec_map_comp, hπ, sec_map_id]

end LateralTheory.EtaleFoundations.TwMulGenMap

theorem LateralTheory.EtaleFoundations.etale_tate_twist_multiplication_generator_map_of_section_description (h : LateralTheory.EtaleFoundations.TwMulGenMap.twSec) :
    LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapExists :=
  LateralTheory.EtaleFoundations.TwMulGenMap.genMap_of h
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.EtaleFoundations

structure TensPre {R : Type} [CommRing R] (I J : Cx R) where
  P : CochainComplex (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) ℤ
  e : ∀ (U : Scheme.{0}) (w : ℤ), Tens I J U w ≃ₗ[ULift.{1} R] (P.X w).obj (op U)
  nat : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w),
    e V w (Tens.res g w x) = ((P.X w).map g.op).hom (e U w x)
  leibniz : ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    ((P.d w (w + 1)).app (op U)).hom (e U w (DirectSum.of _ ⟨(s, t), h⟩ (a ⊗ₜ b))) =
      e U (w + 1) (DirectSum.of _ ⟨(s + 1, t), by omega⟩ (Sec.map (I.d s (s + 1)) a ⊗ₜ b)) +
      s.negOnePow • e U (w + 1) (DirectSum.of _ ⟨(s, t + 1), by omega⟩ (a ⊗ₜ Sec.map (J.d t (t + 1)) b))

def tt_tens_pre : Prop :=
  ∀ (R : Type) [CommRing R] (I J : Cx R), Nonempty (TensPre I J)

def tt_tens_sheafify : Prop :=
  ∀ (R : Type) [CommRing R] (I J : Cx R), TensPre I J → ∃ (K : Cx R) (μ : Pair I J K), μ.IsTensor

theorem tt_tens_ex_of (hpre : tt_tens_pre) (hsh : tt_tens_sheafify) : tt_tens_ex := by
  intro R _ I J
  obtain ⟨T⟩ := hpre R I J
  exact hsh R I J T

end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def tens_univ_ge : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor →
    (I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → K.IsStrictlyGE 0)

theorem tt_tens_ge_of (h : tens_univ_ge) : tt_tens_ge := by
  intro R _ I J K μ hI hJ hμ
  exact h R μ hμ hI hJ

end LateralTheory.EtaleFoundations
end
