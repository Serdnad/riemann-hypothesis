module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdProperties
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle405
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle401

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.TwFree

variable (q : ℕ) [NeZero q] (A : Type) [CommRing A]

theorem pow_val_mul (ζ : Prim q A) (a b : (ZMod q)ˣ) :
    (ζ.1 ^ (a : ZMod q).val) ^ (b : ZMod q).val = ζ.1 ^ ((a * b : (ZMod q)ˣ) : ZMod q).val := by
  rw [← pow_mul, Units.val_mul, ZMod.val_mul, ← pow_eq_pow_mod _ ((GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q A).1 ζ)]

theorem pow_val_one (ζ : Prim q A) : ζ.1 ^ ((1 : (ZMod q)ˣ) : ZMod q).val = ζ.1 := by
  rw [Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ ((GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q A).1 ζ), pow_one]

def orbRel : Setoid (Prim q A) where
  r ζ ξ := ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val
  iseqv :=
    { refl := fun ζ => ⟨1, (pow_val_one q A ζ).symm⟩
      symm := fun {ζ ξ} ⟨a, h⟩ => ⟨a⁻¹, by rw [h, pow_val_mul, mul_inv_cancel, pow_val_one]⟩
      trans := fun {ζ ξ η} ⟨a, h⟩ ⟨b, h'⟩ => ⟨a * b, by rw [h', h, pow_val_mul]⟩ }

abbrev Orb := Quotient (orbRel q A)

abbrev orb (ζ : Prim q A) : Orb q A := Quotient.mk (orbRel q A) ζ

def rep (O : Orb q A) : Prim q A := Quotient.out O

theorem exists_coef (ζ : Prim q A) : ∃ a : (ZMod q)ˣ, ζ.1 = (rep q A (orb q A ζ)).1 ^ (a : ZMod q).val :=
  Quotient.exact (Quotient.out_eq (orb q A ζ))

def coef (ζ : Prim q A) : (ZMod q)ˣ := (exists_coef q A ζ).choose

theorem coef_spec (ζ : Prim q A) : ζ.1 = (rep q A (orb q A ζ)).1 ^ (coef q A ζ : ZMod q).val :=
  (exists_coef q A ζ).choose_spec

variable [Nontrivial A]

theorem units_eq_of_pow (r : Prim q A) (a b : (ZMod q)ˣ)
    (h : r.1 ^ (a : ZMod q).val = r.1 ^ (b : ZMod q).val) : a = b := by
  by_contra hne
  have hm : ¬ (a : ZMod q).val ≡ (b : ZMod q).val [MOD q] := by
    intro hm
    apply hne
    apply Units.ext
    apply ZMod.val_injective
    rw [Nat.ModEq, Nat.mod_eq_of_lt (ZMod.val_lt _), Nat.mod_eq_of_lt (ZMod.val_lt _)] at hm
    exact hm
  have hu := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q A).2.2.1 r _ _ hm
  rw [h, sub_self] at hu
  exact not_isUnit_zero hu

theorem orb_coef_of_pow (ζ ξ : Prim q A) (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    orb q A ξ = orb q A ζ ∧ coef q A ξ = coef q A ζ * a := by
  have ho : orb q A ξ = orb q A ζ := (Quotient.sound (s := orbRel q A) (a := ζ) (b := ξ) ⟨a, h⟩).symm
  refine ⟨ho, units_eq_of_pow q A (rep q A (orb q A ξ)) _ _ ?_⟩
  rw [← coef_spec, h, coef_spec q A ζ, pow_val_mul, ho]

theorem orb_coef_rep (O : Orb q A) : orb q A (rep q A O) = O ∧ coef q A (rep q A O) = 1 := by
  have ho : orb q A (rep q A O) = O := Quotient.out_eq O
  refine ⟨ho, units_eq_of_pow q A (rep q A O) _ _ ?_⟩
  have h := coef_spec q A (rep q A O)
  rw [ho] at h
  rw [← h, pow_val_one]

variable (i : ℤ)

def coordMap : (Prim q A →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] (Orb q A →₀ ULift.{1} (ZMod q)) :=
  Finsupp.linearCombination _ (fun ζ => Finsupp.single (orb q A ζ) (ULift.up ((coef q A ζ ^ i : (ZMod q)ˣ) : ZMod q)))

theorem twRel_le_ker : twRel q i A ≤ LinearMap.ker (coordMap q A i) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ, ξ, a, h, rfl⟩
  obtain ⟨ho, hc⟩ := orb_coef_of_pow q A ζ ξ a h
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, coordMap, Finsupp.linearCombination_single,
    Finsupp.smul_single, smul_eq_mul, one_mul, ho, hc, sub_eq_zero]
  congr 1
  apply ULift.ext
  simp [mul_zpow, mul_comm]

def coordQ : ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) →ₗ[ULift.{1} (ZMod q)] (Orb q A →₀ ULift.{1} (ZMod q)) :=
  (twRel q i A).liftQ (coordMap q A i) (twRel_le_ker q A i)

def basisMap : (Orb q A →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) :=
  Finsupp.linearCombination _ (fun O => Submodule.Quotient.mk (Finsupp.single (rep q A O) 1))

theorem coordQ_mk_single (ζ : Prim q A) :
    coordQ q A i (Submodule.Quotient.mk (Finsupp.single ζ 1)) =
      Finsupp.single (orb q A ζ) (ULift.up ((coef q A ζ ^ i : (ZMod q)ˣ) : ZMod q)) := by
  simp [coordQ, coordMap, Finsupp.linearCombination_single]

def twEquiv : ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) ≃ₗ[ULift.{1} (ZMod q)] (Orb q A →₀ ULift.{1} (ZMod q)) :=
  LinearEquiv.ofLinear (coordQ q A i) (basisMap q A i)
    (by
      refine Finsupp.lhom_ext' fun O => LinearMap.ext_ring ?_
      obtain ⟨ho, hc⟩ := orb_coef_rep q A O
      simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, basisMap,
        Finsupp.linearCombination_single, one_smul, coordQ_mk_single, ho, hc, one_zpow, LinearMap.id_coe, id_eq]
      rfl)
    (by
      refine Submodule.linearMap_qext _ (Finsupp.lhom_ext' fun ζ => LinearMap.ext_ring ?_)
      simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, Submodule.mkQ_apply,
        coordQ_mk_single, basisMap, Finsupp.linearCombination_single, LinearMap.id_coe, id_eq]
      rw [← Submodule.Quotient.mk_smul, Finsupp.smul_single, smul_eq_mul, mul_one, eq_comm,
        Submodule.Quotient.eq]
      exact Submodule.subset_span ⟨rep q A (orb q A ζ), ζ, coef q A ζ, coef_spec q A ζ, rfl⟩)

theorem twist_free : ∀ (q : ℕ) [NeZero q] (i : ℤ) (A : Type) [CommRing A] [Nontrivial A],
    Module.Free (ULift.{1} (ZMod q)) ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) ∧
    ∀ ζ : Prim q A, ∃ f : ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q),
      f (Submodule.Quotient.mk (Finsupp.single ζ 1)) = 1 := by
  intro q _ i A _ _
  refine ⟨Module.Free.of_equiv (twEquiv q A i).symm, fun ζ => ?_⟩
  refine ⟨ULift.up (((coef q A ζ ^ i)⁻¹ : (ZMod q)ˣ) : ZMod q) •
    (Finsupp.lapply (orb q A ζ) ∘ₗ coordQ q A i), ?_⟩
  rw [LinearMap.smul_apply, LinearMap.comp_apply, coordQ_mk_single, Finsupp.lapply_apply,
    Finsupp.single_eq_same, smul_eq_mul]
  apply ULift.ext
  simp

end GlobalTheory.TwFree
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.SecProd

variable (A B : Type) [CommRing A] [CommRing B]

theorem pt_fst (y : Spec (CommRingCat.of A)) :
    (Spec.map (CommRingCat.ofHom (RingHom.fst A B))) y =
      (PrimeSpectrum.primeSpectrumProd A B).symm (.inl (show PrimeSpectrum A from y)) := by
  apply PrimeSpectrum.ext
  rw [PrimeSpectrum.primeSpectrumProd_symm_inl_asIdeal]
  change Ideal.comap _ _ = _
  ext; simp [Ideal.prod, CommRingCat.ofHom]

theorem pt_snd (y : Spec (CommRingCat.of B)) :
    (Spec.map (CommRingCat.ofHom (RingHom.snd A B))) y =
      (PrimeSpectrum.primeSpectrumProd A B).symm (.inr (show PrimeSpectrum B from y)) := by
  apply PrimeSpectrum.ext
  rw [PrimeSpectrum.primeSpectrumProd_symm_inr_asIdeal]
  change Ideal.comap _ _ = _
  ext; simp [Ideal.prod, CommRingCat.ofHom]

theorem pt_cover (x : Spec (CommRingCat.of (A × B))) :
    x ∈ Set.range (Spec.map (CommRingCat.ofHom (RingHom.fst A B))) ∨
      x ∈ Set.range (Spec.map (CommRingCat.ofHom (RingHom.snd A B))) := by
  have hx := (PrimeSpectrum.primeSpectrumProd A B).symm_apply_apply (show PrimeSpectrum (A × B) from x)
  rcases h : PrimeSpectrum.primeSpectrumProd A B x with y | y
  · left; refine ⟨y, (pt_fst A B y).trans ?_⟩; dsimp only at hx ⊢; rw [h] at hx; exact hx
  · right; refine ⟨y, (pt_snd A B y).trans ?_⟩; dsimp only at hx ⊢; rw [h] at hx; exact hx

theorem pt_disj (y : Spec (CommRingCat.of A)) (z : Spec (CommRingCat.of B)) :
    (Spec.map (CommRingCat.ofHom (RingHom.fst A B))) y ≠ (Spec.map (CommRingCat.ofHom (RingHom.snd A B))) z := by
  rw [pt_fst, pt_snd]
  intro h
  exact Sum.inl_ne_inr ((PrimeSpectrum.primeSpectrumProd A B).symm.injective h)

instance : IsOpenImmersion (Spec.map (CommRingCat.ofHom (RingHom.fst A B))) := by
  let := (RingHom.fst A B).toAlgebra
  exact IsOpenImmersion.of_isLocalization (1, 0)

instance : IsOpenImmersion (Spec.map (CommRingCat.ofHom (RingHom.snd A B))) := by
  let := (RingHom.snd A B).toAlgebra
  exact IsOpenImmersion.of_isLocalization (0, 1)

theorem res_comp {R : Type} [CommRing R] (F : Shv R) {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res (k ≫ g) a = Sec.res k (Sec.res g a) := by
  simp [Sec.res]

theorem res_id {R : Type} [CommRing R] (F : Shv R) {U : Scheme.{0}} (a : Sec F U) :
    Sec.res (𝟙 U) a = a := by
  simp [Sec.res]

end GlobalTheory.EtC.SecProd

namespace GlobalTheory.EtC.SecProd

variable (A B : Type) [CommRing A] [CommRing B]

theorem sec_empty {R : Type} [CommRing R] (F : Shv R) (W : Scheme.{0}) [IsEmpty W] (a b : Sec F W) : a = b := by
  apply (sec_ext_glue R F W).1 a b
  rw [loc_iff_etale_affine_points]
  · intro x; exact isEmptyElim x
  · intro V W' g k h; rw [res_comp, res_comp, h]

theorem empty_of_fac {W : Scheme.{0}} (w₁ : W ⟶ Spec (CommRingCat.of A)) (w₂ : W ⟶ Spec (CommRingCat.of B))
    (h : w₁ ≫ Spec.map (CommRingCat.ofHom (RingHom.fst A B)) = w₂ ≫ Spec.map (CommRingCat.ofHom (RingHom.snd A B))) :
    IsEmpty W :=
  ⟨fun x => pt_disj A B (w₁ x) (w₂ x) (by rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply])⟩

def facSieve : Sieve (Spec (CommRingCat.of (A × B))) where
  arrows := fun _ g => (∃ w, g = w ≫ Spec.map (CommRingCat.ofHom (RingHom.fst A B))) ∨
    (∃ w, g = w ≫ Spec.map (CommRingCat.ofHom (RingHom.snd A B)))
  downward_closed := by
    rintro W V g (⟨w, rfl⟩ | ⟨w, rfl⟩) k
    · exact Or.inl ⟨k ≫ w, by simp⟩
    · exact Or.inr ⟨k ≫ w, by simp⟩

theorem facSieve_mem : facSieve A B ∈ Scheme.etaleTopology (Spec (CommRingCat.of (A × B))) := by
  have hL : Loc _ fun _ g => (facSieve A B).arrows g := by
    rw [loc_iff_etale_affine_points]
    · intro x
      rcases pt_cover A B x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact ⟨_, _, inferInstance, inferInstance, ⟨y, hy⟩, Or.inl ⟨𝟙 _, by simp⟩⟩
      · exact ⟨_, _, inferInstance, inferInstance, ⟨y, hy⟩, Or.inr ⟨𝟙 _, by simp⟩⟩
    · intro V W g k h; exact (facSieve A B).downward_closed h k
  obtain ⟨S, hS, hSP⟩ := hL
  exact Scheme.etaleTopology.superset_covering (fun W g hg => hSP W g hg) hS

end GlobalTheory.EtC.SecProd

namespace GlobalTheory.EtC


open SecProd in
theorem sec_prod : ∀ (R : Type) [CommRing R] (A B : Type) [CommRing A] [CommRing B] (F : Shv R),
    Function.Bijective fun s : Sec F (Spec (CommRingCat.of (A × B))) =>
      (Sec.res (Spec.map (CommRingCat.ofHom (RingHom.fst A B))) s,
        Sec.res (Spec.map (CommRingCat.ofHom (RingHom.snd A B))) s) := by
  intro R _ A B _ _ F
  constructor
  · intro a b hab
    simp only [Prod.mk.injEq] at hab
    apply (sec_ext_glue R F _).1 a b
    refine ⟨facSieve A B, facSieve_mem A B, ?_⟩
    rintro W g (⟨w, rfl⟩ | ⟨w, rfl⟩)
    · rw [res_comp, res_comp, hab.1]
    · rw [res_comp, res_comp, hab.2]
  · rintro ⟨s1, s2⟩
    classical
    let i1 := Spec.map (CommRingCat.ofHom (RingHom.fst A B))
    let i2 := Spec.map (CommRingCat.ofHom (RingHom.snd A B))
    let s : ∀ (V : Scheme.{0}) (g : V ⟶ Spec (CommRingCat.of (A × B))), (facSieve A B).arrows g → Sec F V :=
      fun V g hg => if h : ∃ w, g = w ≫ i1 then Sec.res h.choose s1 else Sec.res (hg.resolve_left h).choose s2
    have key1 : ∀ V g (w : V ⟶ Spec (CommRingCat.of A)) (e : g = w ≫ i1) hg, s V g hg = Sec.res w s1 := by
      intro V g w e hg
      have h : ∃ w', g = w' ≫ i1 := ⟨w, e⟩
      simp only [s, dif_pos h]
      congr 1
      exact (cancel_mono i1).1 (h.choose_spec.symm.trans e)
    have key2 : ∀ V g (w : V ⟶ Spec (CommRingCat.of B)) (e : g = w ≫ i2) hg, s V g hg = Sec.res w s2 := by
      intro V g w e hg
      by_cases h : ∃ w', g = w' ≫ i1
      · haveI := empty_of_fac A B h.choose w (h.choose_spec.symm.trans e)
        exact sec_empty F V _ _
      · simp only [s, dif_neg h]
        congr 1
        exact (cancel_mono i2).1 ((hg.resolve_left h).choose_spec.symm.trans e)
    have hs : ∀ (V W : Scheme.{0}) (g : V ⟶ _) (k : W ⟶ V) (hg : (facSieve A B).arrows g),
        Sec.res k (s V g hg) = s W (k ≫ g) ((facSieve A B).downward_closed hg k) := by
      intro V W g k hg
      have hg' := hg
      rcases hg' with ⟨w, e⟩ | ⟨w, e⟩
      · rw [key1 V g w e hg, key1 W _ (k ≫ w) (by rw [e, Category.assoc]) ((facSieve A B).downward_closed hg k), res_comp]
      · rw [key2 V g w e hg, key2 W _ (k ≫ w) (by rw [e, Category.assoc]) ((facSieve A B).downward_closed hg k), res_comp]
    obtain ⟨a, ha⟩ := (sec_ext_glue R F _).2 _ (facSieve_mem A B) s hs
    refine ⟨a, Prod.ext ?_ ?_⟩
    · change Sec.res i1 a = s1
      have h1 : (facSieve A B).arrows i1 := Or.inl ⟨𝟙 _, (Category.id_comp _).symm⟩
      rw [ha _ i1 h1, key1 _ i1 (𝟙 _) (Category.id_comp _).symm h1, res_id]
    · change Sec.res i2 a = s2
      have h2 : (facSieve A B).arrows i2 := Or.inr ⟨𝟙 _, (Category.id_comp _).symm⟩
      rw [ha _ i2 h2, key2 _ i2 (𝟙 _) (Category.id_comp _).symm h2, res_id]

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KummerSplit

noncomputable section

namespace GlobalTheory.EtC.FreeActSum

def rootUnit {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) : Aˣ :=
  Units.ofPowEqOne ζ.1 q ((GlobalTheory.EtC.PrimBasic.prim_basic q A).1 ζ) (NeZero.ne q)

lemma rootUnit_val {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) :
    ((rootUnit ζ : Aˣ) : A) = ζ.1 := rfl

lemma orderOf_rootUnit {q : ℕ} [NeZero q] {A : Type} [CommRing A] [Nontrivial A] (ζ : Prim q A) :
    orderOf (rootUnit ζ) = q := by
  rw [orderOf_eq_iff (NeZero.pos q)]
  refine ⟨?_, ?_⟩
  · ext; simp [rootUnit_val, (GlobalTheory.EtC.PrimBasic.prim_basic q A).1 ζ]
  · intro m hmq hm0 h1
    have hne : ¬ m ≡ 0 [MOD q] := by
      intro h
      have := (Nat.modEq_zero_iff_dvd).1 h
      exact absurd (Nat.le_of_dvd hm0 this) (not_le.2 hmq)
    have hu := (GlobalTheory.EtC.PrimBasic.prim_basic q A).2.2.1 ζ m 0 hne
    have h1' : ζ.1 ^ m = 1 := by
      have := congrArg (fun u : Aˣ => (u : A)) h1
      simpa [rootUnit_val] using this
    rw [h1', pow_zero, sub_self] at hu
    exact not_isUnit_zero hu

abbrev H {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) : Subgroup Aˣ :=
  Subgroup.zpowers (rootUnit ζ)

lemma mem_H {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (u : Aˣ) :
    ((QuotientGroup.mk u : Aˣ ⧸ H ζ).out)⁻¹ * u ∈ H ζ := by
  rw [← QuotientGroup.eq]
  simp

def expo {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (u : Aˣ) : ℤ :=
  Classical.choose (Subgroup.mem_zpowers_iff.1 (mem_H ζ u))

lemma expo_spec {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (u : Aˣ) :
    rootUnit ζ ^ expo ζ u = ((QuotientGroup.mk u : Aˣ ⧸ H ζ).out)⁻¹ * u :=
  Classical.choose_spec (Subgroup.mem_zpowers_iff.1 (mem_H ζ u))

def tau {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (u : Aˣ) : ZMod q :=
  (expo ζ u : ZMod q)

lemma tau_mul {q : ℕ} [NeZero q] {A : Type} [CommRing A] [Nontrivial A] (ζ : Prim q A) (u : Aˣ) (n : ℕ) :
    tau ζ (rootUnit ζ ^ n * u) = tau ζ u + n := by
  have hcls : (QuotientGroup.mk (rootUnit ζ ^ n * u) : Aˣ ⧸ H ζ) = QuotientGroup.mk u := by
    rw [QuotientGroup.eq]
    have : (rootUnit ζ ^ n * u)⁻¹ * u = (rootUnit ζ ^ n)⁻¹ := by
      rw [mul_inv_rev, mul_comm u⁻¹, mul_assoc, inv_mul_cancel, mul_one]
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
  have h1 := expo_spec ζ (rootUnit ζ ^ n * u)
  have h2 := expo_spec ζ u
  rw [hcls] at h1
  set r := ((QuotientGroup.mk u : Aˣ ⧸ H ζ).out)
  have key : rootUnit ζ ^ (expo ζ (rootUnit ζ ^ n * u) - (n : ℤ) - expo ζ u) = 1 := by
    rw [zpow_sub, zpow_sub, h1, h2, zpow_natCast]
    simp [mul_comm, mul_left_comm, mul_assoc]
  rw [← orderOf_dvd_iff_zpow_eq_one, orderOf_rootUnit] at key
  unfold tau
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).2 key
  push_cast at this
  linear_combination this

end GlobalTheory.EtC.FreeActSum

namespace GlobalTheory.EtC.FreeActSum

theorem free_act_sum : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] [Nontrivial A] (ζ : Prim q A) (ι : Type) (s : Finset ι) (c : ι → ULift.{1} (ZMod q)) (a : ι → ℕ) (v w : ι → Aˣ), (∀ i ∈ s, (w i : A) = ζ.1 ^ a i * v i) → (∑ i ∈ s, (Finsupp.single (w i) (c i) - Finsupp.single (v i) (c i))) = 0 → ∑ i ∈ s, (c i).down * (a i : ZMod q) = 0 := by
  intro q _ A _ _ ζ ι s c a v w hw hsum
  let T : (Aˣ →₀ ULift.{1} (ZMod q)) →+ ZMod q :=
    Finsupp.liftAddHom (fun u => (AddMonoidHom.mulRight (tau ζ u)).comp (AddEquiv.ulift.toAddMonoidHom))
  have hT := congrArg T hsum

  rw [map_sum, map_zero] at hT
  rw [← hT]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hwu : w i = rootUnit ζ ^ a i * v i := by
    ext; simp [rootUnit_val, hw i hi]
  simp only [T, map_sub, Finsupp.liftAddHom_apply_single, AddMonoidHom.coe_comp, Function.comp_apply,
    AddMonoidHom.coe_mulRight]
  rw [hwu, tau_mul]
  show (c i).down * (a i : ZMod q) = (c i).down * (tau ζ (v i) + a i) - (c i).down * tau ζ (v i)
  ring

end GlobalTheory.EtC.FreeActSum
end
end

section

noncomputable section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil

namespace GlobalTheory.RankFibreKer

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def tw (ν : kˣ →* ℂˣ) (d : ℕ) {a : ℕ} (g : GL (Fin a) k) : ℂ :=
  (ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2)

def minor {a d : ℕ} (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d) : k := (Y.submatrix id J).det

def idx {a d : ℕ} : (Fin a ↪ Fin d) ≃ Fin (Fintype.card (Fin a ↪ Fin d)) := Fintype.equivFin _


variable (k) in
def slice (a d : ℕ) : Set (Matrix (Fin a) (Fin d) k) :=
  {Z | ∃ J : Fin a ↪ Fin d, Z.submatrix id J = 1 ∧ ∀ J' : Fin a ↪ Fin d,
    valuation k (minor Z J') ≤ 1 ∧ (idx J' < idx J → valuation k (minor Z J') < 1)}

def IsFirstMax {a d : ℕ} (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d) : Prop :=
  minor Y J ≠ 0 ∧ ∀ J' : Fin a ↪ Fin d, valuation k (minor Y J') ≤ valuation k (minor Y J) ∧
    (idx J' < idx J → valuation k (minor Y J') < valuation k (minor Y J))


open Classical in
def sec {a d : ℕ} (Y : Matrix (Fin a) (Fin d) k) : GL (Fin a) k := by
  classical
  exact if h : ∃ J, IsFirstMax Y J then
    GeneralLinearGroup.mkOfDetNeZero (Y.submatrix id h.choose) h.choose_spec.1
  else 1

theorem tw_mul (ν : kˣ →* ℂˣ) (d : ℕ) {a : ℕ} (g x : GL (Fin a) k) : tw ν d (g * x) = tw ν d g * tw ν d x := by
  simp only [tw, gdet_mul, map_mul, Units.val_mul, apow_mul]; ring

theorem tw_ne_zero (ν : kˣ →* ℂˣ) (d : ℕ) {a : ℕ} (g : GL (Fin a) k) : tw ν d g ≠ 0 :=
  mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)

theorem omA_one_apply (ν β : kˣ →* ℂˣ) {a b : ℕ} (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin (a + b)) k → ℂ)
    (Y : Matrix (Fin a) (Fin (a + b)) k) : omA ν β g 1 Ψ Y = (tw ν (a + b) g)⁻¹ * Ψ ((g⁻¹).val * Y) := by
  have e : apow (gdet g) (-(((a + b : ℕ)) : ℂ) / 2) = (apow (gdet g) (((a + b : ℕ) : ℂ) / 2))⁻¹ := by
    rw [neg_div, apow_neg]
  simp only [omA, tw, Fintype.card_fin, e, map_one, Units.val_one, apow_one, mul_one, invT_val, inv_one,
    transpose_one, Units.val_inv_eq_inv_val, mul_inv, Matrix.mul_one]

theorem minor_mul {a d : ℕ} (g : Matrix (Fin a) (Fin a) k) (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d) :
    minor (g * Y) J = g.det * minor Y J := by
  rw [minor, minor, ← det_mul]
  congr 1

end GlobalTheory.RankFibreKer
end
end
