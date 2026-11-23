module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3363
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3035
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3365
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2755
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3221
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3348
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2327
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2308
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3111
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
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.AVCount

section
attribute [local instance] Over.cartesianMonoidalCategory

theorem deg_eq_card_ker_of_unram : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsIsogeny f → FormallyUnramified (pullback.snd (Hom.hom f).left η[B.X].left) → deg f = Nat.card (ptMap f).ker := by
  intro K _ A B f hiso hpfu
  have hfl : Flat f.hom.left := (GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K A B f hiso).2.1
  have hfin : IsFinite f.hom.left := hiso.1
  let e : Sp K ⟶ B.X.left := η[B.X].left
  let p := pullback.snd f.hom.left e
  let i := pullback.fst f.hom.left e
  have he1 : e ≫ B.X.hom = 𝟙 _ := Over.w η[B.X]
  have hpi : i ≫ A.X.hom = p := by
    calc i ≫ A.X.hom = i ≫ f.hom.left ≫ B.X.hom := by rw [Over.w f.hom]
      _ = p ≫ e ≫ B.X.hom := by rw [← Category.assoc, pullback.condition, Category.assoc]
      _ = p := by rw [he1, Category.comp_id]
  have hpet : Etale p := Etale.of_formallyUnramified_of_flat p
  let t : Sp (AlgebraicClosure K) ⟶ Sp K := (ptOver K (AlgebraicClosure K)).hom
  obtain ⟨-, hcard⟩ := GlobalTheory.FinEt.card_points_eq_finrank p t (IsLocalRing.closedPoint _)
  rw [Scheme.Hom.finrank_pullback_snd] at hcard
  have horig : e (t (IsLocalRing.closedPoint _)) = B.origin := by
    rw [origin, GlobalTheory.AV.DegSep.one_left']
    change e _ = (𝟙 (Sp K) ≫ e) _
    rw [Category.id_comp]
    congr 1
    exact Subsingleton.elim _ _
  rw [horig] at hcard
  rw [deg, if_pos hiso, ← hcard]
  symm
  refine Nat.card_congr ?_
  exact
    { toFun := fun y => ⟨pullback.lift y.1.left t (by
          have h := y.2
          rw [MonoidHom.mem_ker, ptMap_apply] at h
          have h2 : (y.1 ≫ f.hom).left = (1 : ptOver K (AlgebraicClosure K) ⟶ B.X).left := by rw [h]
          rw [Over.comp_left, GlobalTheory.AV.DegSep.one_left'] at h2
          exact h2), pullback.lift_snd _ _ _⟩
      invFun := fun y => ⟨Over.homMk (y.1 ≫ i) (by
          change (y.1 ≫ i) ≫ A.X.hom = t
          rw [Category.assoc, hpi, y.2]), by
          rw [MonoidHom.mem_ker, ptMap_apply]
          ext1
          rw [Over.comp_left, GlobalTheory.AV.DegSep.one_left']
          change (y.1 ≫ i) ≫ f.hom.left = t ≫ e
          rw [Category.assoc, pullback.condition, ← Category.assoc, y.2]⟩
      left_inv := fun y => by
        apply Subtype.ext
        ext1
        exact pullback.lift_fst _ _ _
      right_inv := fun y => by
        apply Subtype.ext
        apply pullback.hom_ext
        · exact pullback.lift_fst _ _ _
        · rw [pullback.lift_snd]; exact y.2.symm }

end

theorem map_zero_eq_one_of_additive_to_group {M G : Type} [AddCommGroup M] [Group G] (f : M → G) (hadd : ∀ a a', f (a + a') = f a * f a') : f 0 = 1 := by
  have := hadd 0 0
  rw [add_zero] at this
  exact mul_left_cancel (this.symm.trans (mul_one (f 0)).symm)

theorem map_nsmul_eq_pow_of_additive_to_mulGroup {M G : Type} [AddCommGroup M] [Group G] (f : M → G) (hadd : ∀ a a', f (a + a') = f a * f a') (n : ℕ) (a : M) : f (n • a) = f a ^ n := by
  induction n with
  | zero => rw [zero_smul, map_zero_eq_one_of_additive_to_group f hadd, pow_zero]
  | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]

theorem deg_eq_card_ker_of_tangent : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : AbVar K) (f : B ⟶ B), IsIsogeny f → (∀ v : epsPtR (𝟙 (Sp K)) ⟶ B.X, spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ v.left = (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left → v ≫ Hom.hom f = 1 → v = 1) → deg f = Nat.card (ptMap f).ker :=
  fun K _ _ B f hf hv => deg_eq_card_ker_of_unram K B B f hf (GlobalTheory.T.formallyUnramified_kernel_isogeny_tangent_injective K B f hf hv)

theorem card_ker_eq_norm_pow : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F] (act : OAct (𝓞 F) A) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (h ℓ : ℕ), ℓ.Prime → (ℓ : k) ≠ 0 → (∀ j : ℕ, ∃ f : (Fin h → 𝓞 F ⧸ Ideal.span {((ℓ ^ j : ℕ) : 𝓞 F)}) → (Over.mk x ⟶ A), (∀ a a', f (a + a') = f a * f a') ∧ (∀ (c : 𝓞 F) a, f (Ideal.Quotient.mk (Ideal.span {((ℓ ^ j : ℕ) : 𝓞 F)}) c • a) = f a ≫ act.act c) ∧ Function.Injective f ∧ ∀ g : Over.mk x ⟶ A, g ^ (ℓ ^ j) = 1 → ∃ a, f a = g) → ∀ c : 𝓞 F, c ≠ 0 → (∀ v : epsPtR x ⟶ A, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ A).left → v ≫ act.act c = 1 → v = 1) → Nat.card {g : Over.mk x ⟶ A // g ≫ act.act c = 1} = (Algebra.norm ℤ c).natAbs ^ h := by
  intro S A _ _ hA F _ _ act k _ _ x h ℓ hℓ hℓk hyp c hc hv
  obtain ⟨B, e, ψ, he, htan⟩ := GlobalTheory.T.geometric_point_abelian_variety_action S A hA F act k x
  have hiso := (GlobalTheory.AV.AbVar.DegNorm.isIsogeny_and_deg_ne_zero B ψ c hc).1
  have hE := deg_eq_card_ker_of_tangent k B (ψ c).asHom hiso (htan c hv)
  have hD := GlobalTheory.T.degree_pow_finrank_eq_natAbs_norm_pow k B F ψ c hc
  have hker : Nat.card {g : Over.mk x ⟶ A // g ≫ act.act c = 1} = Nat.card (ptMap (ψ c).asHom).ker := by
    apply Nat.card_congr
    refine Equiv.subtypeEquiv e.toEquiv (fun g => ?_)
    change _ ↔ e g ≫ Hom.hom (ψ c).asHom = 1
    rw [← he, MulEquiv.map_eq_one_iff]

  have htors : Nat.card {g : Over.mk x ⟶ A // g ^ ℓ = 1} = ℓ ^ (2 * B.dim) := by
    rw [← card_torsion_pt k B ℓ hℓk]
    apply Nat.card_congr
    refine Equiv.subtypeEquiv e.toEquiv (fun g => ?_)
    change _ ↔ e g ^ ℓ = 1
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  have hL2 : Nat.card {g : Over.mk x ⟶ A // g ^ ℓ = 1} = ℓ ^ (h * Module.finrank ℚ F) := by
    obtain ⟨f, hadd, -, hinj, hsurj⟩ := hyp 1
    have h0 := map_zero_eq_one_of_additive_to_group f hadd
    have hns := map_nsmul_eq_pow_of_additive_to_mulGroup f hadd
    have hq : ((ℓ : ℕ) : 𝓞 F ⧸ Ideal.span {((ℓ ^ 1 : ℕ) : 𝓞 F)}) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {((ℓ ^ 1 : ℕ) : 𝓞 F)})), Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (by simp)
    have hkill : ∀ a : Fin h → 𝓞 F ⧸ Ideal.span {((ℓ ^ 1 : ℕ) : 𝓞 F)}, ℓ • a = 0 := by
      intro a
      funext i
      simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, hq, zero_mul]
    have hcardQ : Nat.card (𝓞 F ⧸ Ideal.span {((ℓ ^ 1 : ℕ) : 𝓞 F)}) = ℓ ^ Module.finrank ℚ F := by
      have h1 := Ideal.absNorm_span_singleton ((ℓ ^ 1 : ℕ) : 𝓞 F)
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h1
      rw [h1]
      have : ((ℓ ^ 1 : ℕ) : 𝓞 F) = algebraMap ℤ (𝓞 F) (ℓ : ℤ) := by simp
      rw [this, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
      simp
    let eq : (Fin h → 𝓞 F ⧸ Ideal.span {((ℓ ^ 1 : ℕ) : 𝓞 F)}) ≃ {g : Over.mk x ⟶ A // g ^ ℓ = 1} :=
      Equiv.ofBijective (fun a => ⟨f a, by rw [← hns, hkill, h0]⟩)
        ⟨fun a b hab => hinj (congrArg Subtype.val hab),
         fun g => by obtain ⟨a, ha⟩ := hsurj g.1 (by rw [pow_one]; exact g.2); exact ⟨a, Subtype.ext ha⟩⟩
    rw [← Nat.card_congr eq, Nat.card_fun, hcardQ, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul, mul_comm]
  have hℓ1 : 1 < ℓ := hℓ.one_lt
  have hdim : 2 * B.dim = h * Module.finrank ℚ F := by
    have := htors.symm.trans hL2
    exact Nat.pow_right_injective hℓ.two_le this
  have hd0 : Module.finrank ℚ F ≠ 0 := Module.finrank_pos.ne'
  rw [hker, ← hE]
  apply Nat.pow_left_injective hd0
  change deg (A := B) (B := B) (ψ c).asHom ^ Module.finrank ℚ F = ((Algebra.norm ℤ c).natAbs ^ h) ^ Module.finrank ℚ F
  rw [hD, hdim, pow_mul]

end GlobalTheory.AVCount
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UPoinc.UCTraitEx

theorem injective_of_charZero {o K : Type} [CommRing o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [Field K] [CharZero K]
    (ψ : o →+* K) : Function.Injective ψ := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  by_contra hne
  push_neg at hne
  obtain ⟨a, ha, ha0⟩ := hne
  have hP : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  have hbot : RingHom.ker ψ ≠ ⊥ := fun h => ha0 (by
    have h' : a ∈ RingHom.ker ψ := ha
    rwa [h, Ideal.mem_bot] at h')
  haveI hmax : (RingHom.ker ψ).IsMaximal := hP.isMaximal hbot
  haveI := GlobalTheory.finite_quotient_of_finiteType_int (RingHom.ker ψ)
  haveI : CharZero (o ⧸ RingHom.ker ψ) := (RingHom.charZero_iff (RingHom.kerLift_injective ψ)).2 inferInstance
  exact not_finite (o ⧸ RingHom.ker ψ)

theorem exists_lift_genericFibre {o F K : Type} [CommRing o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [Field F]
    (b : o →+* F) (hb : letI := b.toAlgebra; IsFractionRing o F) [Field K] [CharZero K] {Z : Scheme.{0}} (z : Z ⟶ Sp o)
    (x : Sp K ⟶ Z) : ∃ x' : Sp K ⟶ pullback z (spMap b), x' ≫ pullback.fst _ _ = x := by
  letI := b.toAlgebra
  haveI := hb
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (x ≫ z)
  have hinj := injective_of_charZero ψ.hom
  let ψ' : F →+* K := IsFractionRing.lift hinj
  have hc : ψ'.comp b = ψ.hom := RingHom.ext fun a => IsFractionRing.lift_algebraMap hinj a
  have e : x ≫ z = spMap ψ' ≫ spMap b := by
    rw [GlobalTheory.Poinc.GCTrait.spMap_comp'', hc, ← hψ]; rfl
  exact ⟨pullback.lift x (spMap ψ') e, pullback.lift_fst _ _ _⟩

theorem exists_finite_point_rat {X : Scheme.{0}} (s : X ⟶ Sp ℚ) [LocallyOfFiniteType s] (p : ℕ) [Fact p.Prime]
    (y : Sp (PadicAlgCl p) ⟶ X) :
    ∃ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] K) (x : Sp K ⟶ X),
      spMap (algebraMap K (PadicAlgCl p)) ≫ x = y := by
  obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
    (x := y (default : PrimeSpectrum (PadicAlgCl p))) trivial
  have hr : Set.range y ⊆ Set.range hU.fromSpec := by
    rintro _ ⟨q, rfl⟩
    rw [hU.range_fromSpec, Subsingleton.elim (α := PrimeSpectrum (PadicAlgCl p)) q default]
    exact hy
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hU.fromSpec y hr)
  obtain ⟨a, ha⟩ := Spec.map_surjective (hU.fromSpec ≫ s)
  have hft : a.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), ha]
    infer_instance
  letI := a.hom.toAlgebra
  obtain ⟨T, hT⟩ := Algebra.FiniteType.out (R := ℚ) (A := Γ(X, U)) (self := hft)
  let S : Set (PadicAlgCl p) := φ.hom '' (T : Set Γ(X, U))
  have hSfin : S.Finite := T.finite_toSet.image _
  haveI : Finite S := hSfin.to_subtype
  let K := IntermediateField.adjoin ℚ_[p] S
  have hK : FiniteDimensional ℚ_[p] K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hS : S ⊆ K := IntermediateField.subset_adjoin ℚ_[p] S
  have hc : ∀ c : ℚ, φ.hom (a.hom c) ∈ K := fun c => by
    rw [show φ.hom (a.hom c) = (φ.hom.comp a.hom) c from rfl, eq_ratCast]
    exact SubfieldClass.ratCast_mem K c
  have hmem : ∀ b, φ.hom b ∈ K := fun b => by
    have hb : b ∈ Algebra.adjoin ℚ (T : Set Γ(X, U)) := hT ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact hS ⟨x, hx, rfl⟩
    | algebraMap c => exact hc c
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact K.add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact K.mul_mem ha hb
  let φK : Γ(X, U) →+* K := φ.hom.codRestrict K hmem
  refine ⟨K, hK, spMap φK ≫ hU.fromSpec, ?_⟩
  rw [← Category.assoc, GlobalTheory.Poinc.GCTrait.spMap_comp'', ← IsOpenImmersion.lift_fac hU.fromSpec y hr, ← hφ]
  rfl

theorem exists_uCTrait_of_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X : USetup C) (p : ℕ) [Fact p.Prime], ∃ U : X.M.Z.Opens, (U : Set X.M.Z).Nonempty ∧ ∀ y : Sp (OO p) ⟶ X.M.Z, Set.range (gPt p ≫ y) ⊆ U → ∃ ct : UCTrait X p (y (cPt p)), ct.y = y := by
  intro E _ _ _ H Dw _ l Xo cf C X p _
  haveI := C.iF_open
  haveI := C.ded
  haveI := C.ft
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  have hemb : Topology.IsEmbedding (pullback.fst C.z (spMap C.b)) := Scheme.Hom.isEmbedding _
  let S : Set C.Z := pullback.fst C.z (spMap C.b) '' (Set.range C.iF)ᶜ
  have hS : pullback.fst C.z (spMap C.b) ⁻¹' closure S = (Set.range C.iF)ᶜ := by
    rw [← hemb.isInducing.closure_eq_preimage_closure_image]
    exact C.iF.isOpenEmbedding.isOpen_range.isClosed_compl.closure_eq
  let V : C.Z.Opens := ⟨(closure S)ᶜ, isClosed_closure.isOpen_compl⟩
  refine ⟨X.π ⁻¹ᵁ V, ?_, ?_⟩
  · let w : Sp X.Ω₁ := IsLocalRing.closedPoint X.Ω₁
    refine ⟨X.M.pt w, ?_⟩
    have e : X.π (X.M.pt w) =
        pullback.fst C.z (spMap C.b) (C.iF ((spMap (ratHull X.S.R).val.toRingHom ≫ X.u) w)) := by
      rw [← Scheme.Hom.comp_apply, X.comp]
      simp only [UCompact.i, Scheme.Hom.comp_apply]
    show X.π (X.M.pt w) ∈ (closure S)ᶜ
    rw [e]
    intro hc
    have h' : C.iF ((spMap (ratHull X.S.R).val.toRingHom ≫ X.u) w) ∈ (Set.range C.iF)ᶜ := hS ▸ hc
    exact h' ⟨_, rfl⟩
  · intro y hr
    obtain ⟨x', hx'⟩ := exists_lift_genericFibre C.b C.isFractionRing C.z (gPt p ≫ y ≫ X.π)
    have hr' : Set.range x' ⊆ Set.range C.iF := by
      rintro _ ⟨w, rfl⟩
      by_contra hn
      have h1 : pullback.fst C.z (spMap C.b) (x' w) ∈ closure S := subset_closure ⟨_, hn, rfl⟩
      have h2 : (gPt p ≫ y) w ∈ X.π ⁻¹ᵁ V := hr ⟨w, rfl⟩
      have h3 : pullback.fst C.z (spMap C.b) (x' w) = X.π ((gPt p ≫ y) w) := by
        rw [← Scheme.Hom.comp_apply, hx']
        simp only [Scheme.Hom.comp_apply]
      exact h2 (h3 ▸ h1)
    let y₁ : Sp (PadicAlgCl p) ⟶ Xo.XF cf := IsOpenImmersion.lift C.iF x' hr'
    have hy₁ : y₁ ≫ C.i = gPt p ≫ y ≫ X.π := by
      show y₁ ≫ C.iF ≫ pullback.fst _ _ = _
      rw [← Category.assoc, IsOpenImmersion.lift_fac, hx']
    haveI := cf.fin
    haveI := Xo.smooth
    haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim _
    haveI : LocallyOfFiniteType (spMap (algebraMap ℚ cf.F)) :=
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 inferInstance)
    obtain ⟨K, hK, x, hx⟩ := exists_finite_point_rat (pullback.snd _ _ ≫ spMap (algebraMap ℚ cf.F)) p y₁
    obtain ⟨hdvr, hcomp, hunit⟩ := GlobalTheory.intRing_complete_dvr p K hK
    haveI := hdvr
    haveI : CharZero (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) := inferInstance
    let e : FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) ≃ₐ[GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K] K := FractionRing.algEquiv _ K
    let es : K →+* FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) := e.symm.toRingEquiv.toRingHom
    have hbase : GlobalTheory.Mum.Base (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) :=
      ⟨⟨inferInstance, inferInstance, inferInstance, hcomp⟩, inferInstance⟩
    obtain ⟨T, f, fK, hinj, hloc, hfin, hc, hTy⟩ :=
      GlobalTheory.UTraitExt.uTraitExtSt E H Dw l Xo cf _ hbase hdvr (spMap es ≫ x)
    haveI : IsDiscreteValuationRing T.V := T.cdvr.1
    obtain ⟨ι, hι, hint⟩ := GlobalTheory.Poinc.GCTrait.exists_ext_emb p _ T.V f fK hinj hloc hfin hc _ hunit
    have h2 : algebraMap (FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (PadicAlgCl p) =
        (algebraMap K (PadicAlgCl p)).comp e.toRingEquiv.toRingHom := by
      refine IsLocalization.ringHom_ext (nonZeroDivisors (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (RingHom.ext fun v => ?_)
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply]
      refine (IsFractionRing.lift_algebraMap (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing_injective K) v).trans ?_
      show _ = algebraMap K (PadicAlgCl p) (e (algebraMap _ _ v))
      rw [AlgEquiv.commutes]
      rfl
    have hκ : (algebraMap (FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (PadicAlgCl p)).comp es =
        algebraMap K (PadicAlgCl p) := by
      ext k
      rw [h2]
      show algebraMap K (PadicAlgCl p) (e (e.symm k)) = _
      rw [AlgEquiv.apply_symm_apply]
    have key : spMap ι ≫ spMap fK ≫ spMap es = spMap (algebraMap K (PadicAlgCl p)) := by
      rw [GlobalTheory.Poinc.GCTrait.spMap_comp'', GlobalTheory.Poinc.GCTrait.spMap_comp'', ← RingHom.comp_assoc, hι, hκ]
    refine ⟨⟨y, rfl, T, ι, hint, ?_⟩, rfl⟩
    calc gPt p ≫ y ≫ X.π = y₁ ≫ C.i := hy₁.symm
      _ = (spMap (algebraMap K (PadicAlgCl p)) ≫ x) ≫ C.i := by rw [hx]
      _ = ((spMap ι ≫ spMap fK ≫ spMap es) ≫ x) ≫ C.i := by rw [key]
      _ = spMap ι ≫ T.y ≫ C.i := by rw [hTy]; simp only [Category.assoc]

end GlobalTheory.UPoinc.UCTraitEx
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UTraitCen

theorem exists_uTrait_cen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C)
    (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ →
    ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∃ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z),
      (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) ∧
        ξ (IsLocalRing.closedPoint T.V) = x := by
  intro E _ _ _ H Dw l Xo c C X₁ M U₀ EE out hA x _
  have hU : (U₀ : Set M.Z).Nonempty := hA.1.ne
  obtain ⟨W, _, _, _, _, hc, a, ha, hg⟩ := GlobalTheory.Poinc.TraitCen.exists_cdvr M U₀ hU x
  have hr : Set.range (jK W ≫ a) ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    exact hg t
  let ξ₀' : Sp (FractionRing W) ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι (jK W ≫ a) hr
  have hξ₀' : ξ₀' ≫ U₀.ι = jK W ≫ a := IsOpenImmersion.lift_fac _ _ _
  have hB : GlobalTheory.Mum.Base W := ⟨⟨inferInstance, inferInstance, inferInstance, hc⟩, inferInstance⟩
  obtain ⟨y, ⟨x', hx', hy'⟩, -⟩ := X₁.existsUnique_lies (ξ₀' ≫ out.u₀)
  obtain ⟨T, f, fK, -, hloc, -, hcomp, hy⟩ := GlobalTheory.UTraitExt.uTraitExtSt E H Dw l Xo c W hB inferInstance y
  refine ⟨T, spMap f ≫ a, ⟨spMap fK ≫ ξ₀', ?_, spMap fK ≫ x', ?_, ?_⟩, ?_⟩
  · rw [Category.assoc, hξ₀', ← Category.assoc, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    exact hcomp r
  · rw [Category.assoc, hx', Category.assoc]
  · rw [hy, Category.assoc, hy']
  · have h : (spMap f) (closedPoint T.V) = closedPoint W := IsLocalRing.comap_closedPoint f
    show a ((spMap f) (closedPoint T.V)) = x
    rw [h, ha]

end GlobalTheory.UTraitCen
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem GlobalTheory.UPoinc.exists_uTrait_through_open_of_stalk_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (πY : Y.Z ⟶ X₁.M.Z), X₁.S.admitted Y U₀ → X₁.S.IsEE Y U₀ EE → X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → ∀ (x : Y.Z) (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A], IsAdicComplete (maximalIdeal A) A → ∀ θ : Y.Z.presheaf.stalk x →+* A, Function.Injective θ → IsLocalHom θ → ∃ (T : UTrait Xo c) (f : A →+* T.V), Function.Injective f ∧ IsLocalHom f ∧ (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ (spMap (f.comp θ) ≫ Y.Z.fromSpecStalk x) ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) ∧ T.y ≫ C.i = jK T.V ≫ (spMap (f.comp θ) ≫ Y.Z.fromSpecStalk x) ≫ πY ≫ X₁.π := by
  intro E _ _ _ H Dw _ l Xo c C X₁ Y U₀ EE out πY hAdm _ hHom x A _ _ _ _ hcomp θ hθ _
  haveI : CharZero X₁.Ω₁ := X₁.ar.char
  obtain ⟨T, f, γ, hfi, hfl, -, hpt, hy⟩ :=
    GlobalTheory.UPoinc.exists_uTrait_of_stalk_dvr E H Dw l Xo c X₁.o₁ X₁.Ω₁ Y X₁.uΩ x A hcomp θ hθ
  have hsub : Set.range Y.pt ⊆ Set.range U₀.ι := by
    rw [Y.gen, Scheme.Opens.range_ι, Set.singleton_subset_iff]
    exact (genericPoint_spec Y.Z).mem_open_set_iff U₀.isOpen |>.2 (by simpa using hAdm.1.ne)
  let ξg : Sp X₁.Ω₁ ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι Y.pt hsub
  have hξg : ξg ≫ U₀.ι = Y.pt := IsOpenImmersion.lift_fac _ _ _
  have hu : ξg ≫ out.u₀ = spMap X₁.S.R.val.toRingHom := out.u₀_gen ξg hξg
  have hHom' : Y.pt ≫ πY = X₁.M.pt := by
    rw [hHom]
    show Spec.map (CommRingCat.ofHom (RingHom.id X₁.Ω₁)) ≫ _ = _
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  refine ⟨T, f, hfi, hfl, ⟨spMap γ ≫ ξg, ?_, ?_⟩, ?_⟩
  · rw [hpt, Category.assoc, hξg]
  · refine ⟨spMap γ ≫ spMap (ratHull X₁.S.R).val.toRingHom, ?_, ?_⟩
    · rw [Category.assoc, spMap_val_toRat, Category.assoc, hu]
    · rw [hy, Category.assoc]
  · rw [hy]
    simp only [Category.assoc] at hpt ⊢
    rw [reassoc_of% hpt, reassoc_of% hHom', X₁.comp]
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.heat_commuting_periods_exists : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Dd.toPre.X), IsMonomial Dd.toPre t gam → (∀ i, t i ≠ 0) → ∀ D : Derivation ℤ R R, (∀ i, D (t i) ∈ Ideal.span {t i}) → ∃ h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D, IsBasic Y h ∧ HasDefect Y h (fun _ _ _ => 0) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hv m t gam hmon ht D hD
  obtain ⟨h, w, π, π', hb, hdef⟩ := GlobalTheory.T.exists_torusInvariant_heatOperator_polynomial_defect R Dd O oa Y n v dd hv m t gam hmon ht D hD
  have hcoc := GlobalTheory.T.heatOperator_period_defect_isCocycle R Dd O oa Y n v dd hv D h _ hb hdef
  haveI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.cocycle_polynomialDefect_bilinear_additive_parts R Dd.toPre.X w π π' hcoc
  exact GlobalTheory.T.exists_heatOperator_period_defect_zero R Dd O oa Y n v dd hv D h w π π' hb hdef h1 h2 h3 h4
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.fibre_points_joined_by_specialisation_chain : ∀ (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), GlobalTheory.GSep.ZHAbove X₁ Y πY → ∀ y y' : Y.Z, πY y = z₁ → πY y' = z₁ → Relation.EqvGen (fun a b : Y.Z => πY a = z₁ ∧ πY b = z₁ ∧ a ⤳ b) y y' := by
  first | exact @GlobalTheory.GSep.fibre_chain | exact GlobalTheory.GSep.fibre_chain | (intros; apply GlobalTheory.GSep.fibre_chain <;> assumption)
end
