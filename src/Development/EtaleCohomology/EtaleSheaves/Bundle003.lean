module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar
public import Development.EtaleCohomology.EtaleSheaves.Bundle002
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite
open GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.E.LeafKunEmptyPf

variable {R : Type} [CommRing R]

theorem sec_sub (F : Shv R) (U : Scheme.{0}) [IsEmpty U] : Subsingleton (Sec F U) :=
  ModuleCat.isZero_iff_subsingleton.mp (Sheaf.isTerminalOfBotCover F U (Scheme.bot_mem_grothendieckTopology U)).isZero

theorem subsingleton_freePresheaf_hom_of_isEmpty (Z : Scheme.{0}) [IsEmpty Z] (M : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R))
    (hM : ∀ U : Scheme.{0}, IsEmpty U → Subsingleton (M.obj (op U))) :
    Subsingleton ((freeP R).obj (yoneda.obj Z) ⟶ M) := by
  constructor; intro α β
  apply NatTrans.ext; funext U
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
  by_cases h : IsEmpty ((Opposite.unop U : Scheme.{0}) : Type)
  · haveI := hM _ h; exact Subsingleton.elim _ _
  · haveI : IsEmpty (Opposite.unop U ⟶ Z) := ⟨fun f => h ⟨fun y => isEmptyElim (f.base y)⟩⟩
    have hs : Subsingleton (((freeP R).obj (yoneda.obj Z)).obj U) := by
      change Subsingleton (ULift.{1} (Opposite.unop U ⟶ Z) →₀ ULift.{1} R); infer_instance
    rw [Subsingleton.elim x 0, map_zero, map_zero]

theorem free_zero (Z : Scheme.{0}) [IsEmpty Z] : IsZero ((free R).obj (yoneda.obj Z)) := by
  rw [IsZero.iff_id_eq_zero]
  have h1 := subsingleton_freePresheaf_hom_of_isEmpty (R := R) Z ((sheafToPresheaf Scheme.etaleTopology _).obj ((free R).obj (yoneda.obj Z)))
    (fun U hU => by haveI := hU; exact sec_sub _ U)
  apply ((sheafificationAdjunction Scheme.etaleTopology _).homEquiv ((freeP R).obj (yoneda.obj Z))
    ((free R).obj (yoneda.obj Z))).injective
  exact h1.elim _ _

theorem chains_zero (Z : Scheme.{0}) [IsEmpty Z] (p : ℤ) : IsZero (((chains R).obj (sch.obj Z)).X p) := by
  by_cases h : ∃ j : ℕ, ComplexShape.embeddingDownNat.f j = p
  · obtain ⟨j, hj⟩ := h
    have hz : IsZero (((chainsN R).obj (sch.obj Z)).X j) := free_zero (R := R) Z
    exact hz.of_iso (HomologicalComplex.extendXIso ((chainsN R).obj (sch.obj Z)) ComplexShape.embeddingDownNat hj)
  · push Not at h
    exact HomologicalComplex.isZero_extend_X ((chainsN R).obj (sch.obj Z)) ComplexShape.embeddingDownNat p h

theorem H_sub (Z : Scheme.{0}) [IsEmpty Z] (F : Shv R) (n : ℤ) : Subsingleton (H R (sch.obj Z) F n) := by
  constructor; intro x y
  obtain ⟨a, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective y
  congr 1
  apply Cocycle.ext
  apply Cochain.ext
  intro p q hpq
  exact (chains_zero (R := R) Z p).eq_of_src _ _

end LateralTheory.E.LeafKunEmptyPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.CechFiltPf

def Piece : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {E₀ E : Spc} (g : E₀ ⟶ E) (p : ℕ) (n : ℤ),
  Subsingleton (Hrel R (disc.map (g.app (op (SimplexCategory.mk p)))) F (n - p)) →
  Subsingleton (HK R (mappingCone ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map
    (((chains R).map g).f (-(p : ℤ))))) F n)

universe u v

theorem chains_isZero (R : Type) [CommRing R] (E : Spc) (j : ℤ) (hj : 0 < j) : IsZero (((chains R).obj E).X j) := by
  unfold chains
  exact HomologicalComplex.isZero_extend_X _ _ _ (fun i => by
    show -(i : ℤ) ≠ j
    omega)

theorem res_isZero (R : Type) [CommRing R] (F : Shv R) (j : ℤ) (hj : j < 0) : IsZero ((res R F).X j) := by
  unfold res InjectiveResolution.cochainComplex
  exact HomologicalComplex.isZero_extend_X _ _ _ (fun i => by
    show (i : ℤ) ≠ j
    omega)

def DiscLvl : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {P Q : PSh} (h : P ⟶ Q) (m : ℤ),
  Subsingleton (Hrel R (disc.map h) F m) →
  Subsingleton (HK R (mappingCone ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map h))) F m)

def ShiftLvl : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {E₀ E : Spc} (g : E₀ ⟶ E) (p : ℕ) (n : ℤ),
  Subsingleton (HK R (mappingCone ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map
    ((free R).map (g.app (op (SimplexCategory.mk p)))))) F (n - p)) →
  Subsingleton (HK R (mappingCone ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map
    (((chains R).map g).f (-(p : ℤ))))) F n)

theorem Piece_of (hD : DiscLvl) (hS : ShiftLvl) : Piece := by
  intro R _ F E₀ E g p n h
  exact hS R F g p n (hD R F _ _ h)

end LateralTheory.E.CechFiltPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.L_sec_gluePf

theorem typeSheaf {R : Type} [CommRing R] (F : Shv R) :
    Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
  (isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose Scheme.etaleTopology (forget (ModuleCat.{1} (ULift.{1} R)))).obj F).property

end LateralTheory.E.L_sec_gluePf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.t_E6Cut

def ConnK (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {K L : Cx R} (f : K ⟶ L) : Prop :=
  ∀ n : ℤ, (n < c - 1 → Function.Bijective (HK.pull R f F n)) ∧ (n < c → Function.Injective (HK.pull R f F n))

def Conn (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {E E' : Spc} (f : E ⟶ E') : Prop := ConnK R F c ((chains R).map f)

def EtLoc (T : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ T) → Prop) : Prop :=
  ∃ S ∈ Scheme.etaleTopology.{0} T, ∀ (V : Scheme.{0}) (k : V ⟶ T), S k → P V k

def sxMap {E E' : Spc} (f : E ⟶ E') {p : ℕ} {T : Scheme.{0}} (x : Sx E p T) : Sx E' p T :=
  (f.app (op (SimplexCategory.mk p))).app (op T) x

def sxRes {E : Spc} {p : ℕ} {V T : Scheme.{0}} (k : V ⟶ T) (x : Sx E p T) : Sx E p V :=
  (E.obj (op (SimplexCategory.mk p))).map k.op x

end LateralTheory.E.t_E6Cut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.E8

def LeafEmptyVanish : Prop := ∀ (R : Type) [CommRing R] {X : Scheme.{0}} (F : Shv R) (n : ℤ),
  Subsingleton (H R (sch.obj (⊥ : X.Opens)) F n)

end LateralTheory.E.E8

end
end

section

noncomputable section
open CategoryTheory Limits CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafConeExactPf

section General
variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
  {K L M : CochainComplex C ℤ} (φ : K ⟶ L) (n : ℤ)

theorem pre_inr_eq_zero (c : Cocycle (mappingCone φ) M n) :
    CohomologyClass.mk (zcomp (Cocycle.ofHom φ) (zcomp (Cocycle.ofHom (mappingCone.inr φ)) c (zero_add n))
      (zero_add n)) = 0 := by
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨n.negOnePow • (mappingCone.inl φ).comp c.1 (by omega), ?_⟩
  rw [δ_units_smul, δ_comp _ _ (show -1 + n = n - 1 by omega) 0 (n + 1) n (by omega) (by omega) (by omega)]
  simp only [Cocycle.δ_eq_zero, Cochain.comp_zero, zero_add, mappingCone.δ_inl, smul_smul,
    Int.units_mul_self, one_smul]
  apply Cochain.ext
  intro p q hpq
  simp [zcomp, Cochain.comp_v _ _ (zero_add n) p p q (add_zero p) hpq]

end General

end LateralTheory.E.LeafConeExactPf
end
end

section

namespace LateralTheory.E.E4

open Polynomial

theorem finInf_comm {k B L : Type} [Field k] [CommRing B] [Field L] [Algebra k B] [Algebra k L]
    [Algebra B L] [IsScalarTower k B L] (g : Polynomial k →ₐ[k] B) (p : Polynomial k) :
    aeval (algebraMap B L (g X)) p = algebraMap B L (g p) := by
  have h : (aeval (algebraMap B L (g X)) : Polynomial k →ₐ[k] L) =
      (IsScalarTower.toAlgHom k B L).comp g := by
    apply Polynomial.algHom_ext
    simp
  rw [h]; rfl

theorem finInf_integral {k B L : Type} [Field k] [CommRing B] [Field L] [Algebra k B] [Algebra k L]
    [Algebra B L] [IsScalarTower k B L] (g : Polynomial k →ₐ[k] B) (hf : g.Finite)
    (K : IntermediateField k L) (hT : algebraMap B L (g X) ∈ K) (b : B) :
    IsIntegral K (algebraMap B L b) := by
  have hi : g.toRingHom.IsIntegral := RingHom.IsIntegral.of_finite hf
  obtain ⟨p, hp, hpb⟩ := hi b
  let φ : Polynomial k →ₐ[k] K := aeval (⟨_, hT⟩ : K)
  have hc : (algebraMap K L).comp φ.toRingHom = (algebraMap B L).comp g.toRingHom := by
    refine RingHom.ext fun q => ?_
    have h1 := finInf_comm (L := L) g q
    have h2 := Polynomial.aeval_algebraMap_apply L (⟨_, hT⟩ : K) q
    exact h2.symm.trans h1
  refine ⟨p.map φ.toRingHom, hp.map _, ?_⟩
  rw [eval₂_map, hc, ← Polynomial.hom_eval₂, hpb, map_zero]

theorem LeafFinInf_of : LeafFinInf := by
  intro k B _ _ _ _ _ hft g hg hf
  have hinj : Function.Injective (algebraMap B (FractionRing B)) := IsFractionRing.injective B _
  have htr : Transcendental k (algebraMap B (FractionRing B) (g X)) := by
    rw [transcendental_iff]
    intro p hp
    rw [finInf_comm] at hp
    apply hg
    apply hinj
    simpa using hp
  refine ⟨fun h => htr (IsAlgebraic.inv_iff.mp h), ?_⟩
  set K := IntermediateField.adjoin k {(algebraMap B (FractionRing B) (g X))⁻¹} with hK
  have hT : algebraMap B (FractionRing B) (g X) ∈ K := by
    have : (algebraMap B (FractionRing B) (g X))⁻¹ ∈ K :=
      IntermediateField.subset_adjoin k _ (Set.mem_singleton _)
    simpa using K.inv_mem this
  obtain ⟨S, hS⟩ := hft.out
  let S' : Set (FractionRing B) := algebraMap B (FractionRing B) '' (S : Set B)
  have : Finite S' := (S.finite_toSet.image _).to_subtype
  have hfd : FiniteDimensional K (IntermediateField.adjoin K S') :=
    IntermediateField.finiteDimensional_adjoin (by
      rintro _ ⟨b, -, rfl⟩
      exact finInf_integral g hf K hT b)
  have hB : ∀ b : B, algebraMap B (FractionRing B) b ∈ IntermediateField.adjoin K S' := by
    intro b
    have hb : b ∈ Algebra.adjoin k (S : Set B) := hS ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin K S' ⟨x, hx, rfl⟩
    | algebraMap r =>
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply k K (FractionRing B)]
      exact IntermediateField.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have htop : IntermediateField.adjoin K S' = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    exact div_mem (hB a) (hB b)
  rw [htop] at hfd
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

end LateralTheory.E.E4
end

section

namespace LateralTheory.E.E4

open Polynomial IsDedekindDomain

theorem finVal_dedekind (D L : Type) [CommRing D] [IsDedekindDomain D] [Field L] [Algebra D L]
    [IsFractionRing D L] [Finite (HeightOneSpectrum D)] :
    ∃ (n : ℕ) (φ : Lˣ →* Multiplicative (Fin n → ℤ)), ∀ x : Lˣ, φ x = 1 →
      (x : L) ∈ (algebraMap D L).range := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (HeightOneSpectrum D)
  refine ⟨n, MonoidHom.mk' (fun x => Multiplicative.ofAdd
    (fun i => WithZero.log ((e.symm i).valuation L (x : L)))) ?_, ?_⟩
  · intro x y
    rw [← ofAdd_add]
    congr 1
    funext i
    simp only [Units.val_mul, Pi.add_apply, map_mul]
    exact WithZero.log_mul ((Valuation.ne_zero_iff _).mpr x.ne_zero)
      ((Valuation.ne_zero_iff _).mpr y.ne_zero)
  · intro x hx
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro v
    have h : WithZero.log ((e.symm (e v)).valuation L (x : L)) = 0 :=
      congrFun (congrArg Multiplicative.toAdd hx) (e v)
    rw [e.symm_apply_apply] at h
    exact WithZero.le_exp_of_log_le h.le

theorem finVal_finite (A D : Type) [CommRing A] [IsLocalRing A] [CommRing D] [IsDedekindDomain D]
    [Algebra A D] [Algebra.IsIntegral A D] [IsDomain A] [Module.IsTorsionFree A D] :
    Finite (HeightOneSpectrum D) := by
  have hf := IsDedekindDomain.primesOver_finite (IsLocalRing.maximalIdeal A) D
  have := hf.to_subtype
  refine Finite.of_injective (β := (IsLocalRing.maximalIdeal A).primesOver D)
    (fun v => ⟨v.asIdeal, v.isPrime, ⟨?_⟩⟩) ?_
  · have := v.isMaximal
    exact (IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) v.asIdeal)).symm
  · intro v w h
    exact HeightOneSpectrum.ext (congrArg Subtype.val h)

theorem finVal_sep (A K L : Type) [CommRing A] [IsLocalRing A] [IsDedekindDomain A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    ∃ (n : ℕ) (φ : Lˣ →* Multiplicative (Fin n → ℤ)), ∀ x : Lˣ, φ x = 1 → IsIntegral A (x : L) := by
  have := integralClosure.isDedekindDomain A K L
  have := integralClosure.isFractionRing_of_finite_extension (A := A) K L
  have hinj : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have : FaithfulSMul A (integralClosure A L) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    exact hinj (congrArg Subtype.val h)
  have := finVal_finite A (integralClosure A L)
  obtain ⟨n, φ, h⟩ := finVal_dedekind (integralClosure A L) L
  refine ⟨n, φ, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := h x hx
  rw [← hy]
  exact y.2

theorem finVal_gen (A K L : Type) [CommRing A] [IsLocalRing A] [IsDedekindDomain A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] :
    ∃ (n : ℕ) (φ : Lˣ →* Multiplicative (Fin n → ℤ)), ∀ x : Lˣ, φ x = 1 → IsIntegral A (x : L) := by
  obtain ⟨n, φ, h⟩ := finVal_sep A K (separableClosure K L)
  refine ⟨n, φ.comp (Units.map (Algebra.norm (separableClosure K L))), fun x hx => ?_⟩
  have h1 : IsIntegral A (Algebra.norm (separableClosure K L) (x : L)) := h _ hx
  obtain ⟨m, y, hy⟩ := IsPurelyInseparable.pow_mem (separableClosure K L)
    (ringExpChar (separableClosure K L)) (x : L)
  have hq : 0 < ringExpChar (separableClosure K L) ^ m := expChar_pow_pos (separableClosure K L) _ m
  have h2 : IsIntegral A (y ^ Module.finrank (separableClosure K L) L) := by
    rw [← Algebra.norm_algebraMap, hy, map_pow]
    exact h1.pow _
  have h3 : IsIntegral A y := h2.of_pow Module.finrank_pos
  have : IsScalarTower A (separableClosure K L) L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have h4 : IsIntegral A (algebraMap (separableClosure K L) L y) := h3.algebraMap
  rw [hy] at h4
  exact h4.of_pow hq

theorem LeafFinVal_of : LeafFinVal := by
  intro k L _ _ _ _ s hs hfd
  have hne : ∀ p : Polynomial k, p ≠ 0 → aeval s p ≠ 0 := fun p hp h0 => hp ((transcendental_iff.mp hs) p h0)
  let P : Ideal k[X] := RingHom.ker (evalRingHom (0 : k))
  have hP : P.IsPrime := RingHom.ker_isPrime _
  let A := Localization.AtPrime P
  let K := IntermediateField.adjoin k {s}
  let t : K := ⟨s, IntermediateField.mem_adjoin_simple_self k s⟩
  have hval : ∀ p : k[X], ((aeval t p : K) : L) = aeval s p := fun p =>
    (aeval_algHom_apply K.val t p).symm
  have hne' : ∀ p : k[X], p ≠ 0 → aeval t p ≠ 0 := fun p hp h0 => hne p hp (by rw [← hval, h0]; rfl)
  have hu : ∀ y : P.primeCompl, IsUnit ((aeval t : k[X] →ₐ[k] K).toRingHom y) := by
    intro y
    refine (hne' y ?_).isUnit
    intro h0
    exact y.2 (by rw [h0]; exact P.zero_mem)
  let f : A →+* K := IsLocalization.lift (M := P.primeCompl) hu
  have hf : ∀ p : k[X], f (algebraMap k[X] A p) = aeval t p := fun p => IsLocalization.lift_eq hu p
  have hfrac : ∀ c : A, ∃ a b : k[X], b.eval 0 ≠ 0 ∧ f c = aeval t a / aeval t b := by
    intro c
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj P.primeCompl c
    refine ⟨a, b, b.2, ?_⟩
    have := congrArg f hab
    rw [map_mul, hf, hf] at this
    exact (eq_div_iff (hu b).ne_zero).mpr this
  have hinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj P.primeCompl c
    have h1 := congrArg f hab
    rw [map_mul, hc, zero_mul, hf] at h1
    have ha : a = 0 := by
      by_contra ha
      exact hne' a ha h1.symm
    simp only [ha, map_zero] at hab
    exact (IsLocalization.map_units A b).mul_left_eq_zero.mp hab
  let _ : Algebra A K := f.toAlgebra
  let _ : Algebra A L := ((algebraMap K L).comp f).toAlgebra
  have : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective A K).mpr hinj
  have : IsFractionRing A K := by
    refine IsFractionRing.of_field A K (fun z => ?_)
    obtain ⟨r, q, hz⟩ := (IntermediateField.mem_adjoin_simple_iff k (z : L)).mp z.2
    refine ⟨algebraMap k[X] A r, algebraMap k[X] A q, ?_⟩
    change z = f _ / f _
    rw [hf, hf]
    apply Subtype.ext
    rw [hz, ← hval, ← hval]
    rfl
  obtain ⟨n, φ, h⟩ := finVal_gen A K L
  refine ⟨n, φ, fun x hx => ?_⟩
  obtain ⟨p, hp, hpx⟩ := h x hx
  choose a b hb hab using hfrac
  refine ⟨p.natDegree, fun i => a (p.coeff i), fun i => b (p.coeff i), fun i => hb _, ?_⟩
  rw [hp.as_sum, eval₂_add, eval₂_X_pow, eval₂_finsetSum] at hpx
  rw [← hpx]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [eval₂_mul, eval₂_C, eval₂_X_pow]
  congr 1
  change _ = ((f (p.coeff i) : K) : L)
  rw [hab, ← hval, ← hval]
  rfl

end LateralTheory.E.E4
end
