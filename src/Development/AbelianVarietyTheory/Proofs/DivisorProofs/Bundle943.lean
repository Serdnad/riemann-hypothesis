module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle909
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle913
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianLocalRingAcyclicEverySheafStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle714
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCPullbackBijectiveFiniteStrictlyHenselian
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle609
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle690
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle613
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle511
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle864
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle691
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle730
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle612
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle922
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle422
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.tateTwistCohomology_zero_laurent_surjective : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T], IsUnit (q : T) → ∀ (i : ℤ) (y : Ht q (sp (LaurentPolynomial T)) 0 i), ∃ z : Ht q (sp T) 0 i, pull _ (spMap (LaurentPolynomial.C : T →+* LaurentPolynomial T)) _ 0 z = y := by
  first | (exact @GlobalTheory.EtC.MultiplicativeGroupGlobalSections.exists_ht_zero_pull_laurent_eq) | (exact GlobalTheory.EtC.MultiplicativeGroupGlobalSections.exists_ht_zero_pull_laurent_eq) | (intros; apply GlobalTheory.EtC.MultiplicativeGroupGlobalSections.exists_ht_zero_pull_laurent_eq  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem sh_eqv_tw : ∀ (q : ℕ) (i : ℤ) (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B), SH A → SH B → IsUnit (q : A) → Eqv _ (spMap φ) (tw q i) := by
  intro q i A B _ _ φ hA hB hq
  obtain ⟨hAl, _⟩ := hA
  obtain ⟨hBl, _⟩ := hB
  obtain ⟨ζ⟩ := GlobalTheory.T.nonempty_cyclotomicPrimitiveRoots_of_strictlyHenselian q A ⟨hAl, ‹_›⟩ hq
  let S : Scheme.{0} := Spec (CommRingCat.of A)
  let ζS : Prim q Γ(S, ⊤) := Prim.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ζ
  have hgen := GlobalTheory.T.tateTwist_isFreeRankOne_on_generatorSection q i S ζS
  have hac : ∀ (C : Type) [CommRing C], SH C → AcycF (ZMod q) (sch.obj (Spec (CommRingCat.of C))) (tw q i) :=
    fun C _ hC n hn => GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) C hC (tw q i) n hn
  refine GlobalTheory.T.etaleCohomologyEquiv_of_locallyConstant_bijective (ZMod q) (tw q i) S (twGen i ζS) hgen S (Spec (CommRingCat.of B)) (𝟙 S)
    (Spec.map (CommRingCat.ofHom φ)) (hac A ⟨hAl, ‹_›⟩) (hac B ⟨hBl, ‹_›⟩) ?_
  have cA := GlobalTheory.T.locallyConstant_spec_localRing_const_bijective (ZMod q) A
  have cB := GlobalTheory.T.locallyConstant_spec_localRing_const_bijective (ZMod q) B
  have hcomp : (fun φ' : LocallyConstant S (ZMod q) => φ'.comap (Spec.map (CommRingCat.ofHom φ)).base.hom) ∘
      (fun c : ZMod q => LocallyConstant.const S c) = fun c => LocallyConstant.const _ c := by
    funext c; ext x; rfl
  refine (Function.Bijective.of_comp_iff _ cA).1 ?_
  rw [hcomp]
  exact cB
end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.nonempty_ht_zero_addEquiv_zmod_of_sh : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ j : ℤ, Nonempty (Ht q (sp A) 0 j ≃+ ZMod q) := by
  first | (exact @GlobalTheory.EtC.tateTwistCohomology_zero_strictlyHenselian_equiv) | (exact GlobalTheory.EtC.tateTwistCohomology_zero_strictlyHenselian_equiv) | (intros; apply GlobalTheory.EtC.tateTwistCohomology_zero_strictlyHenselian_equiv  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

theorem _root_.GlobalTheory.T.finite_strictlyHenselian_tateTwist_acyclic : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (T : Type) [CommRing T] [Algebra A T],
  Module.Finite A T → ∀ s i : ℤ, 0 < s → Subsingleton (Ht q (sp T) s i) := by
  first | (exact @GlobalTheory.EtC.GmStep.finite_sh_acyclic_twists) | (exact GlobalTheory.EtC.GmStep.finite_sh_acyclic_twists) | (intros; apply GlobalTheory.EtC.GmStep.finite_sh_acyclic_twists  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

theorem _root_.GlobalTheory.T.laurentC_pullback_bijective_finite_strictlyHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (T : Type) [CommRing T] [Algebra A T],
  Module.Finite A T → ∀ i : ℤ, Function.Bijective (pull _ (spMap (LaurentPolynomial.C : T →+* LaurentPolynomial T)) (tw q i) 0) := by
  first | (exact @GlobalTheory.EtC.SpecMapPullbackFunctoriality.laurent_C_pull_bijective) | (exact GlobalTheory.EtC.SpecMapPullbackFunctoriality.laurent_C_pull_bijective) | (intros; apply GlobalTheory.EtC.SpecMapPullbackFunctoriality.laurent_C_pull_bijective <;> assumption)
end

section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

theorem _root_.GlobalTheory.T.dividedPowerFiltrationIdeal_le_map_of_isDPMorphism : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (C : Type) [CommRing C] (J' : Ideal C) (δ' : DividedPowers J') (f : B →+* C), IsDPMorphism δ δ' f → J' = J.map f → ∀ N, fil δ' N ≤ (fil δ N).map f := by
  first | exact @GlobalTheory.PDA.fil_le_map_fil | exact GlobalTheory.PDA.fil_le_map_fil | (intros; apply GlobalTheory.PDA.fil_le_map_fil <;> assumption)
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedCup

theorem sec_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  simp only [Sec.res, Sec.map]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]

theorem sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem cpush_id {R : Type} [CommRing R] (K I : Cx R) (n : ℤ) (a : CohomologyClass K I n) : cpush K (𝟙 I) n a = a := by
  obtain ⟨a, rfl⟩ := a.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

def semiPre {S R : Type} [CommRing S] [CommRing R] {T K : Cx S} {K' : Cx R} (u : T ⟶ K) (ρ : SemiMap K K') :
    SemiMap T K' where
  app U s := (ρ.app U s).comp ((u.f s).hom.app (op U)).hom.toAddMonoidHom
  nat g s a := by
    change Sec.res g (ρ.app _ s (Sec.map (u.f s) a)) = ρ.app _ s (Sec.map (u.f s) (Sec.res g a))
    rw [ρ.nat, sec_map_res]
  comm U s t a := by
    change Sec.map (_ : _ ⟶ _) (ρ.app U s (Sec.map (u.f s) a)) = ρ.app U t (Sec.map (u.f t) (Sec.map (T.d s t) a))
    rw [ρ.comm, ← sec_map_comp, ← sec_map_comp, u.comm]

theorem ev_comp_ofHom {R : Type} [CommRing R] {E : Spc} {I K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (u : I ⟶ K)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (R := R) (α.comp (Cochain.ofHom u) (add_zero n)) p s h U x =
      Sec.map (u.f s) (ev (R := R) α p s h U x) := by
  simp only [ev, Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rfl

theorem semiPre_op {S R : Type} [CommRing S] [CommRing R] {T K : Cx S} {K' : Cx R} (u : T ⟶ K) (ρ : SemiMap K K')
    (E : Spc) (n : ℤ) (x : CohomologyClass ((chains S).obj E) T n) :
    (semiPre u ρ).op.app E n x = ρ.op.app E n (cpush _ u n x) := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  obtain ⟨β, hβ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ).1 E n (zcomp α (Cocycle.ofHom u) (add_zero n))
  change _ = ρ.op.app E n (CohomologyClass.mk (zcomp α (Cocycle.ofHom u) (add_zero n)))
  rw [(GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ).2 E n _ β hβ]
  refine (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R (semiPre u ρ)).2 E n α β (fun p s h U y => ?_)
  rw [hβ p s h U y]
  change ρ.app U s (ev (R := S) (α.1.comp (Cochain.ofHom u) (add_zero n)) p s h U y) = _
  rw [ev_comp_ofHom]
  rfl

theorem semiMap_cup : ∀ (S R : Type) [CommRing S] [CommRing R] {I J T : Cx S} {I' J' K' : Cx R} (τ : Pair I J T) (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J') (σ : SemiMap T K'), (∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U), σ.app U w (τ.mul U s t w h a b) = ν.mul U s t w h (ρ₁.app U s a) (ρ₂.app U t b)) → ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) (a : CohomologyClass ((chains S).obj E) I n) (b : CohomologyClass ((chains S).obj E) J m), σ.op.app E k (τ.cup E hk a b) = ν.cup E hk (ρ₁.op.app E n a) (ρ₂.op.app E m b) := by
  intro S R _ _ I J T I' J' K' τ ν ρ₁ ρ₂ σ hσ E n m k hk a b
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW S τ hk).1 α β
  obtain ⟨α', hα'⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ₁).1 E n α
  obtain ⟨β', hβ'⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ₂).1 E m β
  obtain ⟨γ', hγ'⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R σ).1 E k γ
  rw [(GlobalTheory.T.cup_eq_class_of_isAW S τ hk).2 α β γ hγ, (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R σ).2 E k γ γ' hγ',
    (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ₁).2 E n α α' hα', (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ₂).2 E m β β' hβ']
  refine ((GlobalTheory.T.cup_eq_class_of_isAW R ν hk).2 α' β' γ' ?_).symm
  intro N w h U x

  rw [hγ' N w h U x, hγ N w h U x, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Units.smul_def, map_zsmul, hσ, ← hα', ← hβ', Units.smul_def]

theorem reduction_cup : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (E : Spc) {n m i j : ℤ} (a : Ht Q E n i) (b : Ht Q E m j),
    red Q q E _ _ (cup Q a b) = cup q (red Q q E _ _ a) (red Q q E _ _ b) := by
  intro Q q _ hqQ E n m i j a b
  haveI : NeZero q := ⟨by rintro rfl; exact NeZero.ne Q (zero_dvd_iff.mp hqQ)⟩
  obtain ⟨T, τ, hτ⟩ := GlobalTheory.T.exists_isTensor_etaleSheafComplexPairing (ZMod Q) (res _ (tw Q i)) (res _ (tw Q j))
  obtain ⟨u, hu, -⟩ := (GlobalTheory.T.isTensor_universal_property (ZMod Q) τ hτ).1 (twPair Q i j) (𝟙 _) (𝟙 _)
  have hcup : cup Q a b = cpush _ u _ (τ.cup E rfl a b) := by
    rw [GlobalTheory.T.cupProduct_natural_in_sheafComplexPairing (ZMod Q) τ (twPair Q i j) (𝟙 _) (𝟙 _) u hu E rfl a b, cpush_id, cpush_id]
    rfl
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_semiMap_of_tensorPairing Q (ZMod q) τ hτ (twPair q i j) (redMap Q q i) (redMap Q q j)
  have h1 := semiMap_cup (ZMod Q) (ZMod q) τ (twPair q i j) (redMap Q q i) (redMap Q q j) σ hσ E rfl a b
  rw [hcup]
  change (redMap Q q (i + j)).op.app E (n + m) (cpush _ u _ _) = (twPair q i j).cup E rfl _ _
  rw [← semiPre_op]
  change _ = (twPair q i j).cup E rfl ((redMap Q q i).op.app E n a) ((redMap Q q j).op.app E m b)
  rw [← h1]
  have hres := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy Q i
  have hresj := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy Q j
  have htw := GlobalTheory.T.isTateTwistResolution_tensor_flat Q i j (i + j) rfl (fun _ ζ => resGen i ζ) (fun _ ζ => resGen j ζ) hres.1 hresj.1 hresj.2.1 τ hτ
  have hflat := GlobalTheory.T.flat_tensor_of_flat_complexes (ZMod Q) τ hτ hres.2.1 hresj.2.1
  refine GlobalTheory.T.semiMap_eq_of_flat_tateTwist_resolution Q q hqQ (i + j) _ htw hflat _ _ ?_ E (n + m) _
  intro U ζ
  obtain ⟨ξ, hξ⟩ := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties Q Γ(U, ⊤)).2.2.2.2.2 q hqQ ζ
  rw [hσ, GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ i U ζ ξ hξ, GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ j U ζ ξ hξ, (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q i j).1 U ξ]
  change (redMap Q q (i + j)).app U 0 (Sec.map (u.f 0) _) = _
  rw [hu]
  change (redMap Q q (i + j)).app U 0 ((twPair Q i j).mul U 0 0 0 _ (resGen i ζ) (resGen j ζ)) = _
  rw [(GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique Q i j).1 U ζ, GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ (i + j) U ζ ξ hξ]

end GlobalTheory.EtC.RedCup

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC

theorem unitSec_mul_kd {U : Scheme.{0}} (u v : (Γ(U, ⊤))ˣ) : unitSec (u * v) = unitSec u + unitSec v :=
  map_add ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom
    (ULift.up (Additive.ofMul u) : (Scheme.Γ ⋙ unitsF).obj (op U)) (ULift.up (Additive.ofMul v))

theorem unitSec_res_kd {V U : Scheme.{0}} (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Sec.res g (unitSec u) = unitSec (Units.map g.appTop.hom.toMonoidHom u) := by
  unfold unitSec ofRings.sec
  have := congrArg (fun f => f.hom (ULift.up (Additive.ofMul u) : (Scheme.Γ ⋙ unitsF).obj (op U)))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).naturality g.op)
  exact this.symm

theorem Sec.res_map_kd {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have := congrArg (fun f => f.hom x) (φ.hom.naturality g.op)
  exact this.symm

theorem Sec.map_add_kd {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x + y) = Sec.map φ x + Sec.map φ y := map_add _ x y

theorem Sec.res_sub_kd {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x - y) = Sec.res g x - Sec.res g y := map_sub _ x y

theorem Prim.pow_eq_one_kd {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨g, hg⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hg
  rw [map_mul, ζ.2.2, zero_mul] at h
  simpa [sub_eq_zero] using h

def kumDiff (q : ℕ) (φ : Gm ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 0) (U : Scheme.{0})
    (v : (Γ(U, ⊤))ˣ) : Sec ((res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 0) U :=
  Sec.map φ (unitSec v) - (restrMap (Int.castRingHom (ZMod q)) (tw q 1)).app U 0 (kumT q U v)

theorem kumDiff_res (q : ℕ) (φ : Gm ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 0)
    {V U : Scheme.{0}} (g : V ⟶ U) (hq : IsUnit (q : Γ(U, ⊤))) (v : (Γ(U, ⊤))ˣ) :
    Sec.res g (kumDiff q φ U v) = kumDiff q φ V (Units.map g.appTop.hom.toMonoidHom v) := by
  unfold kumDiff
  rw [Sec.res_sub_kd, Sec.res_map_kd, unitSec_res_kd, (restrMap (Int.castRingHom (ZMod q)) (tw q 1)).nat g 0,
    (kumT_spec q).1 V U g v hq]

theorem kumDiff_mul_root (q : ℕ) (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm)
    (hκ : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 →
      Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u)
    (φ : Gm ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 0)
    (hφ : κ ≫ φ = resι ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)))
    {V : Scheme.{0}} (ζ : Prim q Γ(V, ⊤)) (z w : (Γ(V, ⊤))ˣ) (hz : (z : Γ(V, ⊤)) = ζ.1) :
    kumDiff q φ V (z * w) = kumDiff q φ V w := by
  unfold kumDiff
  have h1 : Sec.map φ (unitSec z) =
      Sec.map (resι ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)))
        (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) V from twGen 1 ζ) := by
    rw [← hκ V ζ z hz, ← hφ]; rfl
  have h2 := (kumT_spec q).2 V ζ w (z * w) (by rw [Units.val_mul, hz])
  have h3 := restrMap_spec (Int.castRingHom (ZMod q)) (tw q 1) V (twGen 1 ζ)
  rw [unitSec_mul_kd, Sec.map_add_kd, h2, map_add (f := _), h1]
  unfold resGen
  rw [h3]
  abel

end GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem kumDiff_pow_root (q : ℕ) (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm)
    (hκ : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 →
      Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u)
    (φ : Gm ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 0)
    (hφ : κ ≫ φ = resι ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)))
    {V : Scheme.{0}} (ζ : Prim q Γ(V, ⊤)) (z : (Γ(V, ⊤))ˣ) (hz : (z : Γ(V, ⊤)) = ζ.1) (a : ℕ) (w : (Γ(V, ⊤))ˣ) :
    kumDiff q φ V (z ^ a * w) = kumDiff q φ V w := by
  induction a with
  | zero => rw [pow_zero, one_mul]
  | succ a ih => rw [pow_succ', mul_assoc, kumDiff_mul_root q κ hκ φ hφ ζ z _ hz, ih]

theorem kumDiff_mul_rootOfUnity : ∀ (q : ℕ) [NeZero q] (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm),
    (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 →
      Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u) →
    ∀ φ : Gm ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 0,
      κ ≫ φ = resι ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) →
    ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ (v ω : (Γ(U, ⊤))ˣ), ω ^ q = 1 →
      Sec.map φ (unitSec (ω * v)) - (restrMap (Int.castRingHom (ZMod q)) (tw q 1)).app U 0 (kumT q U (ω * v)) =
        Sec.map φ (unitSec v) - (restrMap (Int.castRingHom (ZMod q)) (tw q 1)).app U 0 (kumT q U v) := by
  intro q _ κ hκ φ hφ U hq v ω hω
  change kumDiff q φ U (ω * v) = kumDiff q φ U v
  obtain ⟨S, hS, hP⟩ := GlobalTheory.T.rootOfUnity_etaleLocally_pow_primitiveRoot q U hq ω hω
  refine Sheaf.isSeparated _ U S hS _ _ ?_
  intro V g hg
  obtain ⟨ζ, a, ha⟩ := hP V g hg
  change Sec.res g _ = Sec.res g _
  rw [kumDiff_res q φ g hq, kumDiff_res q φ g hq, map_mul]
  have hz := Units.val_ofPowEqOne ζ.1 q ζ.pow_eq_one_kd (NeZero.ne q)
  have e : Units.map g.appTop.hom.toMonoidHom ω = Units.ofPowEqOne ζ.1 q ζ.pow_eq_one_kd (NeZero.ne q) ^ a :=
    Units.ext (by rw [ha, Units.val_pow_eq_pow_val, hz])
  rw [e]
  exact kumDiff_pow_root q κ hκ φ hφ ζ _ hz a _

end GlobalTheory.EtC

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem cup_eq_cast_of_isTwPair (q : ℕ) [NeZero q] (E : Spc) {n m i j k w : ℤ} (hk : i + j = k) (hw : n + m = w)
    (ν : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k))) (hν : IsTwPair ν) (a : Ht q E n i) (b : Ht q E m j) :
    ν.cup E hw a b = (cup q a b).cast hw hk := by
  subst hk
  subst hw
  have h := (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q i j).2 (i + j) rfl ν (twPair q i j) hν (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q i j).1 E (n := n) (m := m) rfl
  rw [h]
  rfl

theorem isTwPair_of_isFlip (q : ℕ) {i j k : ℤ} (μ : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k)))
    (ν : Pair (res _ (tw q j)) (res _ (tw q i)) (res _ (tw q k))) (hμ : IsTwPair μ) (h : μ.IsFlip ν) : IsTwPair ν := by
  intro U ζ
  rw [h U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ), hμ U ζ]
  simp

theorem cup_comm (q : ℕ) [NeZero q] (E : Spc) {n m i j : ℤ} (a : Ht q E n i) (b : Ht q E m j) :
    cup q a b = (n * m).negOnePow • (cup q b a).cast (by ring) (by ring) := by
  obtain ⟨ν, hf, -, -⟩ := GlobalTheory.T.exists_isFlip_sheafComplexPairing (ZMod q) (twPair q i j)
  have hν : IsTwPair ν := isTwPair_of_isFlip q _ ν (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q i j).1 hf
  have h1 := GlobalTheory.T.cup_graded_comm_of_isFlip (ZMod q) (twPair q i j) ν hf E (n := n) (m := m) (k := n + m) rfl (by ring) a b
  have h2 := cup_eq_cast_of_isTwPair q E (n := m) (m := n) (i := j) (j := i) (k := i + j) (w := n + m) (by ring) (by ring) ν hν b a
  change (twPair q i j).cup E rfl a b = _
  rw [h1, h2]

end GlobalTheory.EtC
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

open TensorProduct

namespace GlobalTheory.LiftSys

theorem algHom_mem_map {R B B' : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
    (I : Ideal R) (α : B →ₐ[R] B') {b : B} (hb : b ∈ I.map (algebraMap R B)) :
    α b ∈ I.map (algebraMap R B') := by
  have h := Ideal.mem_map_of_mem (α : B →+* B') hb
  rwa [Ideal.map_map, AlgHom.comp_algebraMap] at h

theorem mul_eq_zero_of_mem_map {R B' : Type} [CommRing R] [CommRing B'] [Algebra R B'] {I : Ideal R}
    (hI : I ^ 2 = 0) {x y : B'} (hx : x ∈ I.map (algebraMap R B')) (hy : y ∈ I.map (algebraMap R B')) :
    x * y = 0 := by
  have h := Ideal.mul_mem_mul hx hy
  rw [← pow_two, map_sq hI B'] at h
  simpa using h

theorem exists_unique_formExt : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → ∀ (U : AffOp X₀) (B B' : Type) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B'] (p : B →+* Sec s₀ U.unop.1), SemiHom π p → Function.Surjective p → (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) → ∀ (α : B →ₐ[R] B') (E : GlobForm s₀ →+ B'), (∀ (r : R) w, E (π r • w) = r • E w) → (∀ w, E w ∈ I.map (algebraMap R B')) → ∃! θ : Ω[Sec s₀ U.unop.1⁄R₀] →+ B', (∀ b w, θ (p b • w) = α b * θ w) ∧ (∀ w, θ w ∈ I.map (algebraMap R B')) ∧ ∀ w : GlobForm s₀, θ (w.1 U) = E w := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hpar U B B' _ _ _ _ p hsemi hsurj hker α E hE hEmem
  have hb : IsBaseChange (Sec s₀ U.unop.1) (evForm s₀ U) := hpar U
  let l : Sec s₀ U.unop.1 → B := Function.surjInv hsurj
  have hl : ∀ s, p (l s) = s := Function.surjInv_eq hsurj
  have key : ∀ b b' : B, p b = p b' → ∀ x ∈ I.map (algebraMap R B'), α b * x = α b' * x := by
    intro b b' h x hx
    have h1 : b - b' ∈ I.map (algebraMap R B) := (hker _).1 (by rw [map_sub, h, sub_self])
    have h2 := mul_eq_zero_of_mem_map hI (algHom_mem_map I α h1) hx
    rw [map_sub, sub_mul] at h2
    exact sub_eq_zero.1 h2
  let g : Sec s₀ U.unop.1 → GlobForm s₀ →+ B' := fun s =>
    AddMonoidHom.mk' (fun w => α (l s) * E w) (fun w w' => by simp [mul_add])
  let f : Sec s₀ U.unop.1 →+ GlobForm s₀ →+ B' :=
    AddMonoidHom.mk' g (fun s t => by
      ext w
      show α (l (s + t)) * E w = α (l s) * E w + α (l t) * E w
      rw [key (l (s + t)) (l s + l t) (by rw [map_add (f := _), hl, hl, hl]) _ (hEmem w), map_add (f := _), add_mul])
  have hf : ∀ (r : R₀) (s : Sec s₀ U.unop.1) (w : GlobForm s₀), f (r • s) w = f s (r • w) := by
    intro r s w
    obtain ⟨r', rfl⟩ := hπ r
    show α (l (π r' • s)) * E w = α (l s) * E (π r' • w)
    rw [key (l (π r' • s)) (r' • l s) (by rw [hl, hsemi, hl]) _ (hEmem w), hE, map_smul,
      smul_mul_assoc, mul_smul_comm]
  let T := TensorProduct.liftAddHom f hf
  let θ : Ω[Sec s₀ U.unop.1⁄R₀] →+ B' := T.comp (hb.equiv.symm.toLinearMap.toAddMonoidHom)
  have hθ : ∀ x, θ x = T (hb.equiv.symm x) := fun _ => rfl
  have hsm : ∀ (b : B) (t : Sec s₀ U.unop.1 ⊗[R₀] GlobForm s₀), T (p b • t) = α b * T t := by
    intro b t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s w =>
      rw [TensorProduct.smul_tmul', TensorProduct.liftAddHom_tmul, TensorProduct.liftAddHom_tmul]
      show α (l (p b • s)) * E w = α b * (α (l s) * E w)
      rw [key (l (p b • s)) (b * l s) (by rw [hl, map_mul, hl, smul_eq_mul]) _ (hEmem w), map_mul, mul_assoc]
    | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, mul_add]
  have hmem : ∀ t : Sec s₀ U.unop.1 ⊗[R₀] GlobForm s₀, T t ∈ I.map (algebraMap R B') := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s w => exact Ideal.mul_mem_left _ _ (hEmem w)
    | add x y hx hy => rw [map_add (f := _)]; exact Ideal.add_mem _ hx hy
  have hev : ∀ w : GlobForm s₀, θ (w.1 U) = E w := by
    intro w
    have h1 : hb.equiv.symm (w.1 U) = 1 ⊗ₜ w := by
      rw [LinearEquiv.symm_apply_eq, IsBaseChange.equiv_tmul, one_smul]; rfl
    rw [hθ, h1, TensorProduct.liftAddHom_tmul]
    show α (l 1) * E w = E w
    rw [key (l 1) 1 (by rw [hl, map_one]) _ (hEmem w), map_one, one_mul]
  refine ⟨θ, ⟨fun b w => ?_, fun w => hmem _, hev⟩, fun y ⟨hy1, _, hy3⟩ => ?_⟩
  · rw [hθ, hθ, LinearEquiv.map_smul, hsm]
  · ext x
    refine hb.inductionOn x ?_ ?_ ?_
    · intro w
      exact (hy3 w).trans (hev w).symm
    · intro s n hn
      rw [← hl s, hy1, hn, hθ, hθ, LinearEquiv.map_smul, hsm]
    · intro n₁ n₂ h₁ h₂
      rw [map_add (f := _), map_add (f := _), h₁, h₂]

end GlobalTheory.LiftSys
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem LiftSys.cobound_I : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Const s₀ → ∀ (S : Sys I π s₀) (z : Z1 S.F), S.IsIdealValuedLiftSystemCocycle z → H1.mk _ z = 0 → ∃ g : C0 S.F, S.IsIdealValuedLiftSystemCochain g ∧ d0 _ g = z.1 := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hc S z hz h0
  obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 h0
  obtain ⟨r₀, hr₀⟩ := hc (fun U ↦ S.p U (g U)) (by
    funext U V a
    have e := congrFun (congrFun (congrFun hg U) V) a
    rw [amitsur_d0_apply] at e
    rw [amitsur_d0_apply, ← S.nat a, ← map_sub, e]
    exact (S.ker V _).2 (hz U V a))
  obtain ⟨r, rfl⟩ := hπ r₀
  refine ⟨fun U ↦ g U - algebraMap R (S.F.obj U) r, fun U ↦ (S.ker U _).1 ?_, ?_⟩
  · rw [map_sub, hr₀ U, (S.semi U).map_algebraMap, sub_self]
  · rw [← hg]
    funext U V a
    simp only [amitsur_d0_apply, map_sub, AlgHom.commutes]
    ring

end GlobalTheory
end
