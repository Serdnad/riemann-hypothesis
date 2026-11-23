module

import Development.EtaleCohomology.KummerTheory.Bundle012
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Development.EtaleCohomology.EtaleSheaves.Bundle005
public import Development.EtaleCohomology.EtaleSheaves.Bundle020
public import Development.EtaleCohomology.EtaleSheaves.Bundle010
public import Development.EtaleCohomology.EtaleSheaves.Bundle019
public import Development.EtaleCohomology.TateTwists.Bundle010
public import Development.EtaleCohomology.EtaleSheaves.Bundle015
public import Development.EtaleCohomology.EtaleSheaves.Bundle016
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.EtaleCohomology.EtaleSheaves.Bundle003
public import Development.EtaleCohomology.EtaleSheaves.Bundle017
public import Development.EtaleCohomology.EtaleSheaves.Bundle018
public import Mathlib.RingTheory.Etale.StandardEtale
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafTw0LocGenPfA

theorem pow_q_eq_one {q : ℕ} {B : Type} [CommRing B] (x : B)
    (hx : Polynomial.aeval x (Polynomial.cyclotomic q ℤ) = 0) : x ^ q = 1 := by
  obtain ⟨p, hp⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have := congrArg (Polynomial.aeval x) hp
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, hx, zero_mul] at this
  exact sub_eq_zero.1 this

theorem local_eq {q : ℕ} [NeZero q] {B : Type} [CommRing B] [IsLocalRing B] (hq : IsUnit (q : B)) {x y : B}
    (hx : x ^ q = 1) (hy : y ^ q = 1) (hr : IsLocalRing.residue B x = IsLocalRing.residue B y) : x = y := by
  apply (config := { allowSynthFailures := true }) LateralTheory.KummerTheory.PrimitiveRootTorsion.uniq <;> assumption

theorem res_root {q : ℕ} {B : Type} [CommRing B] [IsLocalRing B] (z : B)
    (hz : Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0) :
    Polynomial.IsRoot (Polynomial.cyclotomic q (IsLocalRing.ResidueField B)) (IsLocalRing.residue B z) := by
  have h := Polynomial.aeval_algHom_apply (IsLocalRing.residue B).toIntAlgHom z (Polynomial.cyclotomic q ℤ)
  rw [hz, map_zero] at h
  rw [← Polynomial.map_cyclotomic_int, Polynomial.IsRoot.def, Polynomial.eval_map]
  rw [Polynomial.aeval_def, algebraMap_int_eq] at h
  exact h

theorem local_pow {q : ℕ} [NeZero q] {B : Type} [CommRing B] [IsLocalRing B] (hq : IsUnit (q : B)) {ζ ξ : B}
    (hζ : Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) (hξ : Polynomial.aeval ξ (Polynomial.cyclotomic q ℤ) = 0) :
    ∃ a : (ZMod q)ˣ, ξ = ζ ^ (a : ZMod q).val := by
  have : NeZero ((q : ℕ) : IsLocalRing.ResidueField B) :=
    ⟨by simpa [map_natCast] using (hq.map (IsLocalRing.residue B)).ne_zero⟩
  have root : ∀ z : B, Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0 →
      IsPrimitiveRoot (IsLocalRing.residue B z) q := fun z hz =>
    Polynomial.isRoot_cyclotomic_iff.1 (res_root z hz)
  obtain ⟨i, hi, hpow⟩ := (root ζ hζ).eq_pow_of_pow_eq_one ((root ξ hξ).pow_eq_one)
  have hc : i.Coprime q :=
    ((root ζ hζ).pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) i).1 (hpow ▸ root ξ hξ)
  refine ⟨ZMod.unitOfCoprime i hc, ?_⟩
  have hval : ((ZMod.unitOfCoprime i hc : (ZMod q)ˣ) : ZMod q).val = i := by
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  rw [hval]
  refine local_eq hq (pow_q_eq_one ξ hξ) ?_ ?_
  · rw [← pow_mul, mul_comm, pow_mul, pow_q_eq_one ζ hζ, one_pow]
  · rw [map_pow]; exact hpow.symm

end LateralTheory.E.LeafTw0LocGenPfA
end
end

section

namespace LateralTheory.Fin.EtaleChapterDThree
theorem etale_cohomology_third_statement_holds_alt : LateralTheory.E.EtaleChapterDThree := by
  apply LateralTheory.E.t_D3Cut.goal
theorem intersectionNumber_baseChange : LateralTheory.E.EtaleChapterDThree := etale_cohomology_third_statement_holds_alt
end LateralTheory.Fin.EtaleChapterDThree
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafMVVanishPf

theorem mvSpc : LateralTheory.E.MVPf.MVSpc :=
  LateralTheory.E.MVPf.MVSpc_of (fun R _ _ _ _ f g h => LateralTheory.Fin.EtaleMayerVietorisChainsShortExact.intersectionNumber_baseChange R f g h)

end LateralTheory.E.LeafMVVanishPf

namespace LateralTheory.E.E8
open LateralTheory.E.LeafMVVanishPf

end LateralTheory.E.E8
end
end

section

noncomputable section
open CategoryTheory Limits GlobalTheory.EtC CochainComplex.HomComplex CochainComplex

namespace LateralTheory.E.GlueRelPfCone

theorem pre_pull_zero (R : Type) [CommRing R] {K L : Cx R} (φ : K ⟶ L) (F : Shv R) (m : ℤ) (b : HK R L F m) :
    HK.pre R (mappingCone.fst φ) F m (m + 1) (add_comm 1 m) (HK.pull R φ F m b) = 0 := by
  obtain ⟨b, rfl⟩ := b.mk_surjective
  change CohomologyClass.mk (zcomp (mappingCone.fst φ) (zcomp (Cocycle.ofHom φ) b (zero_add m)) (add_comm 1 m)) = 0
  rw [CohomologyClass.mk_eq_zero_iff]
  refine ⟨m, rfl, -(m.negOnePow • (mappingCone.snd φ).comp b.1 (zero_add m)), ?_⟩
  ext1
  simp only [zcomp, Cocycle.ofHom_coe]
  rw [δ_neg, δ_units_smul, δ_comp _ _ (zero_add m) 1 (m + 1) (m + 1) rfl (zero_add 1) rfl, mappingCone.δ_snd]
  simp [Cocycle.δ_eq_zero, Cochain.comp_assoc_of_second_is_zero_cochain, smul_smul, Int.units_mul_self]

theorem range_of_pre_zero (R : Type) [CommRing R] {K L : Cx R} (φ : K ⟶ L) (F : Shv R) (m : ℤ) (x : HK R K F m)
    (hx : HK.pre R (mappingCone.fst φ) F m (m + 1) (add_comm 1 m) x = 0) : x ∈ Set.range (HK.pull R φ F m) := by
  obtain ⟨a, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk (zcomp (mappingCone.fst φ) a (add_comm 1 m)) = 0 at hx
  rw [CohomologyClass.mk_eq_zero_iff] at hx
  obtain ⟨m', hm', γ, hγ⟩ := hx
  obtain rfl : m' = m := by omega
  have hγ' : δ m' (m' + 1) γ = (mappingCone.fst φ).1.comp a.1 (add_comm 1 m') := by
    rw [hγ]; rfl
  have hb : δ m' (m' + 1) ((Cochain.ofHom (mappingCone.inr φ)).comp γ (zero_add m')) = 0 := by
    rw [δ_comp _ _ (zero_add m') 1 (m' + 1) (m' + 1) rfl (zero_add 1) rfl, hγ', δ_ofHom]
    rw [← Cochain.comp_assoc_of_first_is_zero_cochain, mappingCone.inr_fst]
    simp
  let b : Cocycle L (res R F) m' := Cocycle.mk (-(m'.negOnePow • (Cochain.ofHom (mappingCone.inr φ)).comp γ (zero_add m')))
    (m' + 1) rfl (by rw [δ_neg, δ_units_smul, hb]; simp)
  refine ⟨CohomologyClass.mk b, ?_⟩
  change CohomologyClass.mk (zcomp (Cocycle.ofHom φ) b (zero_add m')) = CohomologyClass.mk a
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  refine ⟨m' - 1, by omega, -((mappingCone.inl φ).comp γ (by omega)), ?_⟩
  ext1
  rw [δ_neg, δ_comp _ _ (show -1 + m' = m' - 1 by omega) 0 (m' + 1) m' (by omega) (by omega) rfl, hγ',
    mappingCone.δ_inl]
  rw [← Cochain.comp_assoc _ _ _ (neg_add_cancel 1) (add_comm 1 m') (by omega), mappingCone.inl_fst]
  simp [zcomp, b, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain, sub_eq_add_neg]

theorem coneExact : LateralTheory.E.GlueRelPf.ConeExact := by
  intro R _ K L φ F m x
  exact ⟨range_of_pre_zero R φ F m x, by rintro ⟨b, rfl⟩; exact pre_pull_zero R φ F m b⟩

end LateralTheory.E.GlueRelPfCone
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.LocallyConstantH0

namespace LateralTheory.E.TwGenNZACPf

section Field
variable {q : ℕ} [NeZero q] {L : Type} [Field L]

theorem prim_isPrimitiveRoot (z : Prim q L) : IsPrimitiveRoot z.1 q := by
  have : NeZero (q : L) := ⟨z.2.1.ne_zero⟩
  have h := z.2.2
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic] at h
  exact Polynomial.isRoot_cyclotomic_iff.1 h


open Classical in
def lg (q : ℕ) (z x : L) : ZMod q := if h : ∃ n : ℕ, z ^ n = x then (h.choose : ZMod q) else 0

theorem lg_pow {z : L} (hz : IsPrimitiveRoot z q) (n : ℕ) : lg q z (z ^ n) = n := by
  have h : ∃ m : ℕ, z ^ m = z ^ n := ⟨n, rfl⟩
  unfold lg
  rw [dite_eq_left h, ZMod.natCast_eq_natCast_iff]
  have h2 := h.choose_spec
  have h3 := ((hz.isOfFinOrder (NeZero.ne q)).pow_eq_pow_iff_modEq).1 h2
  rwa [← hz.eq_orderOf] at h3


open Classical in
def fv (q : ℕ) (i : ℤ) (z x : L) : ZMod q :=
  if h : IsUnit (lg q z x) then ((h.unit ^ i : (ZMod q)ˣ) : ZMod q) else 0

theorem fv_rel (i : ℤ) (z : Prim q L) (ζ ξ : Prim q L) (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    fv q i z.1 ξ.1 = ((a ^ i : (ZMod q)ˣ) : ZMod q) * fv q i z.1 ζ.1 := by
  have hz := prim_isPrimitiveRoot z
  obtain ⟨m, -, hm⟩ := hz.eq_pow_of_pow_eq_one (prim_isPrimitiveRoot ζ).pow_eq_one
  have hl : lg q z.1 ξ.1 = lg q z.1 ζ.1 * a := by
    rw [h, ← hm, ← pow_mul, lg_pow hz, lg_pow hz]
    push_cast
    rw [ZMod.natCast_zmod_val]
  unfold fv
  by_cases hu : IsUnit (lg q z.1 ζ.1)
  · have hu' : IsUnit (lg q z.1 ξ.1) := hl ▸ hu.mul a.isUnit
    rw [dite_eq_left hu, dite_eq_left hu']
    have : hu'.unit = hu.unit * a := Units.ext (by simp [hl])
    rw [this, mul_zpow, Units.val_mul, mul_comm]
  · have hu' : ¬ IsUnit (lg q z.1 ξ.1) := by
      rw [hl]; exact fun h' => hu ((Units.isUnit_mul_units _ a).1 h')
    rw [dite_eq_right hu, dite_eq_right hu', mul_zero]

theorem fv_self (i : ℤ) (z : Prim q L) : fv q i z.1 z.1 = 1 := by
  have hl : lg q z.1 z.1 = 1 := by
    have := lg_pow (prim_isPrimitiveRoot z) 1
    rw [pow_one] at this
    rw [this, Nat.cast_one]
  unfold fv
  have hu : IsUnit (lg q z.1 z.1) := hl ▸ isUnit_one
  rw [dite_eq_left hu]
  have : hu.unit = 1 := Units.ext (by simp [hl])
  rw [this, one_zpow, Units.val_one]

def lin (i : ℤ) (z : L) : (Prim q L →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  Finsupp.linearCombination _ (fun ξ : Prim q L => ULift.up (fv q i z ξ.1))

theorem lin_rel (i : ℤ) (z : Prim q L) : twRel q i L ≤ LinearMap.ker (lin i z.1) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ, ξ, a, h, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, lin, Finsupp.linearCombination_single]
  rw [sub_eq_zero]
  apply ULift.ext
  simp [fv_rel i z ζ ξ a h]

theorem field_nz (i : ℤ) (z : Prim q L) (c : ZMod q)
    (h : c.val • (Submodule.Quotient.mk (Finsupp.single z 1) : (Prim q L →₀ ULift.{1} (ZMod q)) ⧸ twRel q i L) = 0) :
    c = 0 := by
  have h2 := congrArg ((twRel q i L).liftQ (lin i z.1) (lin_rel i z)) h
  rw [map_nsmul, Submodule.liftQ_apply, map_zero, lin, Finsupp.linearCombination_single, fv_self] at h2
  rw [one_smul] at h2
  have h3 := congrArg AddEquiv.ulift h2
  rw [map_nsmul, map_zero] at h3
  change c.val • (1 : ZMod q) = 0 at h3
  rwa [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val] at h3

end Field

theorem ring_nz {q : ℕ} [NeZero q] (i : ℤ) {A : Type} [CommRing A] [Nontrivial A] (ζ : Prim q A) (c : ZMod q)
    (h : c.val • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) = 0) :
    c = 0 := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  let _ := Ideal.Quotient.field M
  apply field_nz i (ζ.map (Ideal.Quotient.mk M)) c
  have h2 := congrArg (Submodule.mapQ _ _ (Finsupp.lmapDomain (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q))
    (Prim.map (Ideal.Quotient.mk M))) (twRel_le q i (Ideal.Quotient.mk M))) h
  rw [map_nsmul, map_zero, Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single] at h2
  exact h2

theorem gamma_nontrivial (V : Scheme.{0}) [Nonempty V] : Nontrivial Γ(V, ⊤) := by
  obtain ⟨y⟩ := ‹Nonempty V›
  exact RingHom.domain_nontrivial (V.presheaf.germ ⊤ y trivial).hom

theorem TwGenNZAC_of : LateralTheory.E.LCBijPf.TwGenNZAC := by
  intro q _ i K _ _ ζ c h
  let P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) := Scheme.Γ ⋙ twF q i
  let U : Scheme.{0} := Spec (CommRingCat.of K)
  let m : P.obj (op U) := Submodule.Quotient.mk (Finsupp.single (gam ζ) 1)
  have h1 : ((toSheafify Scheme.etaleTopology P).app (op U)).hom (c.val • m) =
      ((toSheafify Scheme.etaleTopology P).app (op U)).hom 0 := by
    rw [map_nsmul, map_zero]
    exact h
  have hS := Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) (c.val • m) 0 h1
  obtain ⟨𝒰, hle⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hS
  obtain ⟨p⟩ : Nonempty U := inferInstance
  obtain ⟨j, y, -⟩ := ((Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀).1 p
  have hj := hle _ _ (Presieve.ofArrows.mk j)
  have : Nonempty (𝒰.X j) := ⟨y⟩
  have : Nontrivial (Scheme.Γ.obj (op (𝒰.X j))) := gamma_nontrivial (𝒰.X j)
  apply ring_nz i ((gam ζ).map (Scheme.Γ.map (𝒰.f j).op).hom) c
  change (P.map (𝒰.f j).op).hom (c.val • m) = (P.map (𝒰.f j).op).hom 0 at hj
  rw [map_nsmul, map_zero] at hj
  change c.val • Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map (Scheme.Γ.map (𝒰.f j).op).hom)
    (Finsupp.single (gam ζ) 1)) = _ at hj
  erw [Finsupp.mapDomain_single] at hj
  exact hj

end LateralTheory.E.TwGenNZACPf
end
end

section

noncomputable section
open CategoryTheory AlgebraicGeometry LateralTheory.E.E4

namespace LateralTheory.E.LeafCloseBCut

def LeafProjModel : Prop := ∀ (k : Type) [Field k] (A : Type) [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A], ∃ (B : Scheme.{0}) (b : B ⟶ Sp k) (ι : Sp A ⟶ B), IsIntegral B ∧ IsProper b ∧
    IsOpenImmersion ι ∧ ι ≫ b = Spec.map (CommRingCat.ofHom (algebraMap k A))

def LeafDimOpen : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (b : X ⟶ Sp k) [LocallyOfFiniteType b],
    IsIntegral X → ∀ U : Set X, IsOpen U → U.Nonempty → topologicalKrullDim X ≤ topologicalKrullDim U

theorem goal_of (h1 : LeafProjModel) (h2 : LeafDimOpen) : LateralTheory.E.LeafSpreadVCut.LeafCloseB := by
  intro k _ A _ _ _ _
  obtain ⟨B, b, ι, hB, hb, hι, hc⟩ := h1 k A
  refine ⟨B, b, ι, hB, hb, hι, hc, ?_⟩
  obtain ⟨x⟩ : Nonempty (PrimeSpectrum A) := inferInstance
  have hemb := ι.isOpenEmbedding
  calc topologicalKrullDim B ≤ topologicalKrullDim (Set.range ι) :=
        h2 k b hB _ hemb.isOpen_range ⟨ι x, x, rfl⟩
    _ = topologicalKrullDim (Sp A) :=
        (IsHomeomorph.topologicalKrullDim_eq _ (hemb.isEmbedding.toHomeomorph).isHomeomorph).symm
    _ = ringKrullDim A := PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A

end LateralTheory.E.LeafCloseBCut

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafDescendVCut

abbrev toR {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) : Sp Ω ⟶ Sp R :=
  Spec.map (CommRingCat.ofHom (algebraMap R Ω))

abbrev incl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (h : R ≤ R') : Sp R' ⟶ Sp R :=
  Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom)

def Chain {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) {C0 C1 C2 : Scheme.{0}}
    (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) {D0 D1 D2 : Scheme.{0}} (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0)
    (d2 : D2 ⟶ D1) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2) : Prop :=
  IsProper q ∧ SmoothOfRelativeDimension 1 q ∧ IsProper (d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d1 ≫ q) ∧
  IsProper (d2 ≫ d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d2 ≫ d1 ≫ q) ∧
  IsPullback v0 c0 q (toR R) ∧ IsPullback v1 (γ1 ≫ c0) (d1 ≫ q) (toR R) ∧
  IsPullback v2 (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) (toR R) ∧ γ1 ≫ v0 = v1 ≫ d1 ∧ γ2 ≫ v1 = v2 ≫ d2

def LeafDescendChain : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {C0 : Scheme.{0}}
    (c0 : C0 ⟶ Sp Ω), IsCurve c0 → ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1),
    IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
    ∃ (R : Subalgebra k Ω), R.FG ∧ ∃ (D0 D1 D2 : Scheme.{0}) (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1)
      (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2), Chain R c0 γ1 γ2 q d1 d2 v0 v1 v2

def LeafDescendMap : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] (Ω : Type)
    [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG → ∀ {C0 D0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (q : D0 ⟶ Sp R)
    (v0 : C0 ⟶ D0), IsProper q → IsPullback v0 c0 q (toR R) → ∀ (e : C0 ⟶ X),
    e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) →
    ∃ (R' : Subalgebra k Ω) (hR : R ≤ R'), R'.FG ∧ ∀ (E0 : Scheme.{0}) (q' : E0 ⟶ Sp R') (r : E0 ⟶ D0)
      (w0 : C0 ⟶ E0), IsPullback r q' q (incl hR) → IsPullback w0 c0 q' (toR R') → w0 ≫ r = v0 →
      ∃ f : E0 ⟶ X, w0 ≫ f = e ∧ f ≫ p = q' ≫ Spec.map (CommRingCat.ofHom (algebraMap k R'))

def LeafBaseChange : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R R' : Subalgebra k Ω)
    (hR : R ≤ R') {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) {D0 D1 D2 : Scheme.{0}}
    (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2),
    Chain R c0 γ1 γ2 q d1 d2 v0 v1 v2 →
    ∃ (E0 E1 E2 : Scheme.{0}) (q' : E0 ⟶ Sp R') (e1 : E1 ⟶ E0) (e2 : E2 ⟶ E1) (w0 : C0 ⟶ E0) (w1 : C1 ⟶ E1)
      (w2 : C2 ⟶ E2) (r : E0 ⟶ D0), Chain R' c0 γ1 γ2 q' e1 e2 w0 w1 w2 ∧ IsPullback r q' q (incl hR) ∧
      w0 ≫ r = v0

def LeafIrred : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {C0 D0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (q : D0 ⟶ Sp R) (v0 : C0 ⟶ D0), IsCurve c0 →
    SmoothOfRelativeDimension 1 q → IsPullback v0 c0 q (toR R) → IrreducibleSpace D0

def LeafDimBound : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {D0 : Scheme.{0}} (q : D0 ⟶ Sp R), SmoothOfRelativeDimension 1 q →
    topologicalKrullDim D0 ≤ ringKrullDim R + 1

theorem goal_of (hA : LeafDescendChain) (hB : LeafDescendMap) (hC : LeafBaseChange) (hI : LeafIrred)
    (hD : LeafDimBound) : LateralTheory.E.LeafSpreadVCut.LeafDescendV := by
  intro k _ X p _ Ω _ _ C0 c0 e hc0 he C1 C2 γ1 γ2 h1 h2
  obtain ⟨R, hR, D0, D1, D2, q, d1, d2, v0, v1, v2, hch⟩ := hA k Ω c0 hc0 C1 C2 γ1 γ2 h1 h2
  obtain ⟨R', hRR', hR', hM⟩ := hB k p Ω R hR c0 q v0 hch.1 hch.2.2.2.2.2.2.1 e he
  obtain ⟨E0, E1, E2, q', e1, e2, w0, w1, w2, r, hch', hr, hw⟩ :=
    hC k Ω R R' hRR' c0 γ1 γ2 q d1 d2 v0 v1 v2 hch
  obtain ⟨f, hf1, hf2⟩ := hM E0 q' r w0 hr hch'.2.2.2.2.2.2.1 hw
  obtain ⟨pq, sq, pq1, sq1, pq2, sq2, P0, P1, P2, c1, c2⟩ := hch'
  exact ⟨R', hR', E0, E1, E2, q', e1, e2, f, w0, w1, w2, pq, sq, pq1, sq1, pq2, sq2, hf2,
    hI k Ω R' hR' c0 q' w0 hc0 sq P0, hD k Ω R' hR' q' sq, P0, P1, P2, c1, c2, hf1⟩

end LateralTheory.E.LeafDescendVCut

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.LocallyConstantH0

namespace LateralTheory.E.LCSurjPf

def LocForm : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) (B : Type) [CommRing B] (ζ : Prim q B) (y : Sec (tw q i) (Spec (CommRingCat.of B))),
  Loc (Spec (CommRingCat.of B)) fun _ g => ∃ c : ZMod q, Sec.res g y = c.val • twGen i ((gam ζ).map g.appTop.hom)

def Descent : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) m, IsLCMap q i m →
  ∀ (B : Type) [CommRing B] (ζ : Prim q B) (y : Sec (tw q i) (Spec (CommRingCat.of B))),
    (Loc (Spec (CommRingCat.of B)) fun _ g => ∃ c : ZMod q, Sec.res g y = c.val • twGen i ((gam ζ).map g.appTop.hom)) →
    ∃ ψ : LocallyConstant (PrimeSpectrum B) (ZMod q),
      Loc (Spec (CommRingCat.of B)) fun _ g => Sec.res g y = Sec.res g (m B ζ ψ)

theorem sec_sep {R : Type} [CommRing R] (F : Shv R) (U : Scheme.{0}) (a b : Sec F U)
    (h : Loc U fun _ g => Sec.res g a = Sec.res g b) : a = b := by
  obtain ⟨S, hS, hab⟩ := h
  exact (LateralTheory.E.L_sec_gluePf.typeSheaf F S hS).isSeparatedFor.ext fun V g hg => hab V g hg

theorem LCSurj_of (hL : LocForm) (hD : Descent) : LateralTheory.E.LCBijPf.LCSurj := by
  intro q _ i m hm B _ ζ y
  obtain ⟨ψ, hψ⟩ := hD q i m hm B ζ y (hL q i B ζ y)
  exact ⟨ψ, (sec_sep _ _ _ _ hψ).symm⟩

end LateralTheory.E.LCSurjPf
end
end

section

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.E.LeafClosedPf

theorem LeafClosed_of : LateralTheory.E.LeafGeoCut.LeafClosed := by
  intro B V
  let Z : TopologicalSpace.Closeds B := ⟨(V : Set B)ᶜ, V.isOpen.isClosed_compl⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  refine ⟨I.subscheme, I.subschemeι, inferInstance, ?_⟩
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  simp [Z]

end LateralTheory.E.LeafClosedPf

end
end

section

noncomputable section

namespace LateralTheory.E.LEtaleLiftPf

def LChart : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (A' : Type) [CommRing A']
  [Algebra A A'] [Algebra.Etale A A'] (φ : A' →ₐ[A] A ⧸ I),
  ∃ g : A', IsUnit (φ g) ∧ Algebra.IsStandardEtale A (Localization.Away g)

theorem LEtaleLift_of (hC : LChart) : LateralTheory.E.LFactorPf.LEtaleLift := by
  intro A _ I _ A' _ _ _ φ
  obtain ⟨g, hg, hS⟩ := hC A I A' φ
  let φ' : Localization.Away g →ₐ[A] A ⧸ I := IsLocalization.Away.liftAlgHom g hg
  obtain ⟨ψ, hψ⟩ := GlobalTheory.exists_algHom_lift_of_isStandardEtale I (Ideal.Quotient.mkₐ A I)
    (Ideal.Quotient.mkₐ_surjective A I) (fun b => (Ideal.Quotient.eq_zero_iff_mem).symm) φ'
  refine ⟨ψ.comp (IsScalarTower.toAlgHom A A' _), AlgHom.ext fun a => ?_⟩
  exact congr($hψ (algebraMap A' _ a)).trans (show φ' (algebraMap A' _ a) = φ a by simp [φ'])

end LateralTheory.E.LEtaleLiftPf
end
end
