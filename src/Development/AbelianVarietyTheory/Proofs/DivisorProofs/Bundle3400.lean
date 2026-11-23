module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle344
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1858
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1136
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle422
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsLocalRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1144
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle262
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle377
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle396
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle342
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistFinitaryStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle943
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle031
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle752
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3391
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.HInvAic

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap]
  rw [← Functor.map_comp, ← Spec.map_comp]
  rfl

theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap]
  rw [show CommRingCat.ofHom (RingHom.id A) = 𝟙 (CommRingCat.of A) from rfl, Spec.map_id, CategoryTheory.Functor.map_id]

theorem eqv_comp {R : Type} [CommRing R] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (F : Shv R)
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n
  have : (pull R (f ≫ g) F n : _ → _) = pull R f F n ∘ pull R g F n := funext fun x => pull_comp R f g F n x
  rw [this]
  exact (hf n).comp (hg n)

theorem eqv_spMap_equiv {R : Type} [CommRing R] {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (F : Shv R) :
    Eqv R (spMap (e : A →+* B)) F := by
  intro n
  have h1 : spMap (e : A →+* B) ≫ spMap (e.symm : B →+* A) = 𝟙 _ := by
    rw [← spMap_comp]; convert spMap_id B; ext x; simp
  have h2 : spMap (e.symm : B →+* A) ≫ spMap (e : A →+* B) = 𝟙 _ := by
    rw [← spMap_comp]; convert spMap_id A; ext x; simp
  refine Function.bijective_iff_has_inverse.mpr ⟨pull R (spMap (e.symm : B →+* A)) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, h2, pull_id]
  · rw [← pull_comp, h1, pull_id]

end GlobalTheory.HInvAic

namespace GlobalTheory.HInvAic

theorem alg (T O : Type) [CommRing T] [IsDomain T] [CommRing O] [Algebra T O] :
    AIC T → SH O → IndEt T O → IsDomain O ∧ AIC O := by
  intro hT hSH hInd
  obtain ⟨hH, -⟩ := hSH
  obtain ⟨-, hac⟩ := (GlobalTheory.T.monicPolynomialsHaveRoots_iff_integrallyClosed_algClosed T).1 hT
  haveI : IsIntegrallyClosed T := ((GlobalTheory.T.monicPolynomialsHaveRoots_iff_integrallyClosed_algClosed T).1 hT).1
  refine GlobalTheory.T.isDomain_monicRoots_of_isIndEtale_local T O hInd ?_
  intro E _ _ _ P _
  obtain ⟨hd, hc⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale T P (Localization.AtPrime P)
  exact ⟨hd, (GlobalTheory.T.monicPolynomialsHaveRoots_iff_integrallyClosed_algClosed _).2 ⟨hc, GlobalTheory.T.isAlgClosed_fractionRing_atPrime_of_etale' T E P hac⟩⟩
end GlobalTheory.HInvAic

namespace GlobalTheory.HInvAic

theorem tensor_map_eq (T O : Type) [CommRing T] [CommRing O] [Algebra T O] :
    (Algebra.TensorProduct.map (AlgHom.id T O) (Algebra.ofId T (Polynomial T))).toRingHom =
      (((polyEquivTensor T O).toRingEquiv : Polynomial O →+* O ⊗[T] Polynomial T).comp Polynomial.C).comp
        ((Algebra.TensorProduct.rid T T O).toRingEquiv : O ⊗[T] T →+* O) := by
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul o t =>
    simp only [RingHom.comp_apply, AlgEquiv.coe_toRingEquiv, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv,
      Algebra.TensorProduct.rid_tmul, polyEquivTensor_apply, Polynomial.eval₂_C]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.includeLeft_apply, Algebra.ofId_apply, Polynomial.algebraMap_eq]
    rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_one, Polynomial.algebraMap_eq]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem main : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T], AIC T → IsUnit (q : T) → HInv q T := by
  intro q _ T _ _ hT hq i
  have hφ : ((Algebra.ofId T (Polynomial T)).toRingHom : T →+* Polynomial T) = Polynomial.C := by
    ext x <;> simp [Algebra.ofId_apply]
  rw [← hφ]
  apply GlobalTheory.T.etaleCohomology_local_to_global_ringMap_indEtale (ZMod q) (tw q i) (GlobalTheory.T.tateTwist_finitary q i) T T (Polynomial T) (Algebra.ofId T (Polynomial T))

  intro O _ _ hSH hInd
  obtain ⟨hdom, haic⟩ := alg T O hT hSH hInd
  obtain ⟨hH, -⟩ := hSH
  have hqO : IsUnit (q : O) := by simpa using hq.map (algebraMap T O)
  have hC := GlobalTheory.T.etaleHomotopyInvariance_absIntClosedLocalDomain q O haic hqO i
  rw [tensor_map_eq, spMap_comp, spMap_comp]
  exact eqv_comp _ _ _ (eqv_comp _ _ _ (eqv_spMap_equiv _ _) hC) (eqv_spMap_equiv _ _)

end GlobalTheory.HInvAic
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.EtC.GmAicDeg1

theorem cast_eq_zero_iff {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E n i) :
    x.cast hn hi = 0 ↔ x = 0 := by
  subst hn; subst hi; exact Iff.rfl

theorem cast_nsmul {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (k : ℕ) (x : Ht q E n i) :
    (k • x).cast hn hi = k • x.cast hn hi := by
  subst hn; subst hi; rfl

theorem inv_sp (q : ℕ) (A : Type) [CommRing A] (hq : IsUnit (q : A)) : Inv q (sp A) := fun U ⟨x⟩ => by
  have h := (hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).map
    (show U ⟶ Spec (CommRingCat.of A) from x).appTop.hom
  simpa only [map_natCast] using h

theorem dvd_of_T_eq_pow {T : Type} [CommRing T] [IsDomain T] (q n : ℕ) (w : LaurentPolynomial T)
    (hw : (LaurentPolynomial.T (n : ℤ) : LaurentPolynomial T) = w ^ q) : q ∣ n := by
  obtain ⟨k, f, hf⟩ := LaurentPolynomial.exists_T_pow w
  have h : Polynomial.toLaurent (f ^ q) = Polynomial.toLaurent (Polynomial.X ^ (n + k * q) : Polynomial T) := by
    rw [map_pow, hf, mul_pow, ← hw, Polynomial.toLaurent_X_pow, LaurentPolynomial.T_pow, ← LaurentPolynomial.T_add]
    congr 1
    push_cast
    ring
  have h2 := congrArg Polynomial.natDegree (Polynomial.toLaurent_injective h)
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_pow] at h2
  have h3 : q ∣ n + k * q := ⟨f.natDegree, h2.symm⟩
  exact (Nat.dvd_add_left (dvd_mul_left q k)).mp h3

theorem kum_pow (q : ℕ) [NeZero q] {X : Scheme.{0}} (hX : IsUnit (q : Γ(X, ⊤))) (u : (Γ(X, ⊤))ˣ) (m : ℕ) :
    kum q (u ^ m) = m • kum q u := by
  have hadd : ∀ u v : (Γ(X, ⊤))ˣ, IsUnit (q : Γ(X, ⊤)) → kum q (u * v) = kum q u + kum q v ∧ kum q (u ^ q) = 0 :=
    fun u v h => (GlobalTheory.T.chernClass_kummerClass_additive q).2 u v h
  have h1 : kum q (1 : (Γ(X, ⊤))ˣ) = 0 := by
    have h := (hadd 1 1 hX).1
    rw [mul_one] at h
    simpa using h
  induction m with
  | zero => rw [pow_zero, zero_smul, h1]
  | succ m ih => rw [pow_succ, (hadd _ _ hX).1, ih, succ_nsmul]

theorem laurentVar_val (T : Type) [CommRing T] :
    (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial T))).hom.hom ((laurentVar T : Γ(Spec (CommRingCat.of (LaurentPolynomial T)), ⊤))) =
      LaurentPolynomial.T 1 := by
  simp [laurentVar, laurentVarUnit]

end GlobalTheory.EtC.GmAicDeg1

namespace GlobalTheory.EtC.GmAicDeg1

theorem eq_zero_of_cup_kum (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] (hT : AIC T)
    (hq : IsUnit (q : T)) (b : Ht q (sp T) 0 0)
    (hb : cup q (pull _ (spMap (LaurentPolynomial.C : T →+* LaurentPolynomial T)) (tw q 0) 0 b) (kum q (laurentVar T)) = 0) :
    b = 0 := by
  obtain ⟨e⟩ := GlobalTheory.T.nonempty_ht_zero_addEquiv_zmod_of_sh q T (GlobalTheory.GenusTwoPureComparison.Cmp.sh_of_aic hT) hq 0
  have hrep : ∀ x : Ht q (sp T) 0 0, x = (e x).val • e.symm 1 := fun x => by
    apply e.injective
    rw [map_nsmul, AddEquiv.apply_symm_apply, nsmul_one, ZMod.natCast_zmod_val]
  have hqL : IsUnit (q : LaurentPolynomial T) := by simpa using hq.map (LaurentPolynomial.C : T →+* LaurentPolynomial T)
  have hqΓ := GmPhiNat.isUnit_gamma q T hq
  have hκ : ∀ (m : ℕ) (x : Ht q (sp T) 0 0),
      cup q (pull _ (spMap (LaurentPolynomial.C : T →+* LaurentPolynomial T)) (tw q 0) 0 (m • x)) (kum q (laurentVar T)) =
        m • cup q (pull _ (spMap (LaurentPolynomial.C : T →+* LaurentPolynomial T)) (tw q 0) 0 x) (kum q (laurentVar T)) := by
    intro m x
    rw [map_nsmul, map_nsmul, AddMonoidHom.nsmul_apply]
  have hone : pull _ (spMap (LaurentPolynomial.C : T →+* LaurentPolynomial T)) (tw q 0) 0 (one q (sp T)) =
      one q (sp (LaurentPolynomial T)) := (GlobalTheory.T.cup_chern_kummer_pullback_naturality q).2.1 _ (inv_sp q T hq)
  have hunit := (GlobalTheory.T.cupProduct_gradedCommRingAxioms_hold q (sp (LaurentPolynomial T))).1 (inv_sp q _ hqL) (kum q (laurentVar T))
  have h1 := hκ (e (one q (sp T))).val (e.symm 1)
  rw [← hrep, hone, hunit] at h1
  have h2 := hκ (e b).val (e.symm 1)
  rw [← hrep, hb] at h2
  have h3 : (e b).val • (kum q (laurentVar T)).cast (by ring) (by ring) = (0 : Ht q (sp (LaurentPolynomial T)) (0 + 1) (0 + 1)) := by
    rw [h1, smul_smul, mul_comm, ← smul_smul, ← h2, smul_zero]
  rw [← cast_nsmul, cast_eq_zero_iff] at h3
  have h5 : kum q (laurentVar T ^ (e b).val) = 0 := by rw [kum_pow q hqΓ, h3]
  obtain ⟨v, hv⟩ := GlobalTheory.T.eq_pow_of_kummerClassOfUnit_eq_zero q (LaurentPolynomial T) hqL _ h5
  have h6 := congrArg (fun u : (Γ(Spec (CommRingCat.of (LaurentPolynomial T)), ⊤))ˣ =>
    (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial T))).hom.hom (u : Γ(Spec (CommRingCat.of (LaurentPolynomial T)), ⊤))) hv
  simp only [Units.val_pow_eq_pow_val, map_pow] at h6
  rw [laurentVar_val, LaurentPolynomial.T_pow, mul_one] at h6
  have h7 := dvd_of_T_eq_pow q (e b).val _ h6
  have h8 : (e b).val = 0 := Nat.eq_zero_of_dvd_of_lt h7 (ZMod.val_lt _)
  rw [ZMod.val_eq_zero] at h8
  exact e.map_eq_zero_iff.1 h8

theorem main : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) →
    ∀ i : ℤ, Function.Bijective (gmPhi q T i) := by
  intro q _ T _ _ _ hT hq i
  have hinj : Function.Injective (gmPhi q T i) := by
    refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    simp only [gmPhi, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at ha
    rw [cast_eq_zero_iff] at ha
    obtain ⟨z, hz⟩ : ∃ z : T, Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0 := by
      obtain ⟨a, ha⟩ := hT (Polynomial.cyclotomic q T) (Polynomial.cyclotomic.monic q T)
        (by rw [Polynomial.natDegree_cyclotomic]; exact Nat.totient_pos.2 (NeZero.pos q))
      exact ⟨a, by rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]; exact ha⟩
    let ζ : Prim q Γ(Spec (CommRingCat.of T), ⊤) := Prim.map (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom ⟨z, hq, hz⟩
    let τ := Untwist.twistEquiv ζ (inv_sp q T hq) 0 (i - 1) 0
    have hτ : τ a = 0 := by
      apply eq_zero_of_cup_kum q T hT hq
      show cup q (pull _ _ _ 0 ((cup q (rootClass (0 - (i - 1)) ζ) a).cast (zero_add 0) (by ring))) (kum q (laurentVar T)) = 0
      rw [GmPhiNat.pull_cast, Untwist.cup_cast_left, cast_eq_zero_iff, (GlobalTheory.T.cup_chern_kummer_pullback_naturality q).1,
        (GlobalTheory.T.cupProduct_gradedCommRingAxioms_hold q _).2.1, cast_eq_zero_iff, ha, map_zero]
    exact τ.map_eq_zero_iff.1 hτ
  obtain ⟨e0⟩ := GlobalTheory.T.nonempty_ht_zero_addEquiv_zmod_of_sh q T (GlobalTheory.GenusTwoPureComparison.Cmp.sh_of_aic hT) hq (i - 1)
  obtain ⟨e1⟩ := (GlobalTheory.T.tateTwistCohomology_laurent_absIntClosedLocalDomain q T hT hq 1 i).2
  haveI : Finite (Ht q (sp (LaurentPolynomial T)) 1 i) := Finite.of_equiv _ e1.symm.toEquiv
  exact hinj.bijective_of_nat_card_le (by rw [Nat.card_congr e0.toEquiv, Nat.card_congr e1.toEquiv])

end GlobalTheory.EtC.GmAicDeg1

theorem GlobalTheory.EtC.gmPhi_bijective_of_aic : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T],
    AIC T → IsUnit (q : T) → ∀ i : ℤ, Function.Bijective (gmPhi q T i) :=
  GlobalTheory.EtC.GmAicDeg1.main
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

noncomputable section
namespace GlobalTheory.EtC.GmKill

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Functor.map_comp, ← Spec.map_comp]; rfl

theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (sp A) := by
  change sch.map (Spec.map (𝟙 _)) = _
  rw [Spec.map_id, CategoryTheory.Functor.map_id]

theorem subsingleton_of_ringEquiv (q : ℕ) (d i : ℤ) {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B)
    [Subsingleton (Ht q (sp A) d i)] : Subsingleton (Ht q (sp B) d i) := by
  constructor
  intro x y
  have h : ∀ z : Ht q (sp B) d i,
      pull _ (spMap (e : A →+* B)) _ _ (pull _ (spMap (e.symm : B →+* A)) _ _ z) = z := by
    intro z
    rw [← pull_comp, spMap_comp]
    have : (e : A →+* B).comp (e.symm : B →+* A) = RingHom.id B := by ext; simp
    rw [this, spMap_id, pull_id]
  rw [← h x, ← h y, Subsingleton.elim (pull _ (spMap (e.symm : B →+* A)) _ _ x) (pull _ _ _ _ y)]

theorem subsingleton_prod (q : ℕ) (d i : ℤ) (A B : Type) [CommRing A] [CommRing B]
    [Subsingleton (Ht q (sp A) d i)] [Subsingleton (Ht q (sp B) d i)] :
    Subsingleton (Ht q (sp (A × B)) d i) := by
  constructor
  intro x y
  exact (GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q A B d i).1 (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))

theorem subsingleton_of_subsingleton_ring (q : ℕ) (d i : ℤ) (A : Type) [CommRing A] [Subsingleton A] :
    Subsingleton (Ht q (sp A) d i) := by
  constructor
  intro a b
  obtain ⟨x, hx⟩ := (GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q A A d i).2 (a, b)
  have hfs : RingHom.fst A A = RingHom.snd A A := RingHom.ext fun _ => Subsingleton.elim _ _
  have h1 := congrArg Prod.fst hx
  have h2 := congrArg Prod.snd hx
  simp only at h1 h2
  rw [← h1, ← h2, hfs]

def piFinSuccRingEquiv (n : ℕ) (B : Fin (n + 1) → Type) [∀ j, CommRing (B j)] :
    (∀ j, B j) ≃+* B 0 × ∀ j : Fin n, B j.succ where
  toFun f := (f 0, fun j => f j.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by simp
  map_mul' f g := rfl
  map_add' f g := rfl

theorem subsingleton_pi (q : ℕ) (d i : ℤ) : ∀ (n : ℕ) (B : Fin n → Type) [∀ j, CommRing (B j)],
    (∀ j, Subsingleton (Ht q (sp (B j)) d i)) → Subsingleton (Ht q (sp (∀ j, B j)) d i) := by
  intro n
  induction n with
  | zero =>
    intro B _ _
    exact subsingleton_of_subsingleton_ring q d i _
  | succ n ih =>
    intro B _ hB
    have := ih (fun j => B j.succ) (fun j => hB j.succ)
    have := hB 0
    have := subsingleton_prod q d i (B 0) (∀ j : Fin n, B j.succ)
    exact subsingleton_of_ringEquiv q d i (piFinSuccRingEquiv n B).symm

theorem isIntegral_pi {O : Type} [CommRing O] {ι : Type} [Finite ι] {R : ι → Type}
    [∀ i, CommRing (R i)] [∀ i, Algebra O (R i)] (x : ∀ i, R i) (hx : ∀ i, IsIntegral O (x i)) :
    IsIntegral O x :=
  _root_.GlobalTheory.IntegralPi.main x hx

theorem isLocalRing_closure (A : Type) [CommRing A] [HenselianLocalRing A] (P : Ideal A) [P.IsPrime] :
    IsLocalRing (integralClosure (A ⧸ P) (AlgebraicClosure (FractionRing (A ⧸ P)))) := by
  haveI : IsLocalRing (A ⧸ P) := IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  haveI : HenselianLocalRing (A ⧸ P) := GlobalTheory.henselianLocalRing_of_finite A (A ⧸ P)
  exact GlobalTheory.EtC.Psi.isLocalRing_integralClosure _ _

theorem main : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
  ∀ (n i : ℤ), 2 ≤ n → ∀ x : Ht q (sp (LaurentPolynomial A)) n i,
  ∃ (A' : Type) (_ : CommRing A') (_ : Algebra A A'), Module.Finite A A' ∧ RingHom.ker (algebraMap A A') ≤ nilradical A ∧
    pull _ (spMap (_root_.GlobalTheory.EtC.GmStep.laurentMap (algebraMap A A'))) _ _ x = 0 := by
  classical
  intro q _ A _ _ hA hq n i hn x
  obtain ⟨hHens, -⟩ := hA
  let ι := {p : Ideal A // p ∈ minimalPrimes A}
  haveI : Finite ι := (minimalPrimes.finite_of_isNoetherianRing A).to_subtype
  letI : Fintype ι := Fintype.ofFinite ι
  let σ : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let P : Fin (Fintype.card ι) → Ideal A := fun k => (σ k).1
  haveI hP : ∀ k, (P k).IsPrime := fun k => (σ k).2.1.1
  let T : Fin (Fintype.card ι) → Type := fun k =>
    integralClosure (A ⧸ P k) (AlgebraicClosure (FractionRing (A ⧸ P k)))
  letI : ∀ k, Algebra A (T k) := fun k => ((algebraMap (A ⧸ P k) (T k)).comp (Ideal.Quotient.mk (P k))).toAlgebra
  have hint : ∀ k (s : T k), IsIntegral A s := by
    intro k s
    have h : ((algebraMap (A ⧸ P k) (T k)).comp (Ideal.Quotient.mk (P k))).IsIntegral :=
      RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective)
        (fun s => Algebra.IsIntegral.isIntegral s)
    exact h s
  haveI : Algebra.IsIntegral A (∀ k, T k) := ⟨fun s => isIntegral_pi s (fun k => hint k (s k))⟩
  have hS : Subsingleton (Ht q (sp (LaurentPolynomial (∀ k, T k))) n i) := by
    have hT : ∀ k, Subsingleton (Ht q (sp (LaurentPolynomial (T k))) n i) := by
      intro k
      haveI := isLocalRing_closure A (P k)
      have hqk : IsUnit (q : T k) := by simpa using hq.map (algebraMap A (T k))
      exact (GlobalTheory.T.tateTwistCohomology_laurent_absIntClosedLocalDomain q (T k) (GlobalTheory.aic_integralClosure_algebraicClosure (A ⧸ P k)) hqk n i).1 hn
    haveI := subsingleton_pi q n i _ (fun k => LaurentPolynomial (T k)) hT
    exact subsingleton_of_ringEquiv q n i (RingEquiv.ofBijective _ (GlobalTheory.T.laurent_pi_bijective _ T)).symm
  have hx0 : pull _ (spMap (_root_.GlobalTheory.EtC.GmStep.laurentMap (algebraMap A (∀ k, T k)))) _ _ x = 0 := Subsingleton.elim _ _
  obtain ⟨t, ht⟩ := GlobalTheory.T.laurent_class_vanishes_finitely_generated_subalgebra q A (∀ k, T k) hq n i x hx0
  refine ⟨Algebra.adjoin A (t : Set (∀ k, T k)), inferInstance, inferInstance,
    GlobalTheory.EtC.IntAcyc.finite_finDiag A (∀ k, T k) t, ?_, ht⟩
  intro a ha
  rw [RingHom.mem_ker] at ha
  have ha' : algebraMap A (∀ k, T k) a = 0 := by
    have := congrArg Subtype.val ha
    exact this
  have hmem : ∀ k, a ∈ P k := by
    intro k
    have h1 : algebraMap A (T k) a = 0 := congrFun ha' k
    have h2 : algebraMap (A ⧸ P k) (AlgebraicClosure (FractionRing (A ⧸ P k))) (Ideal.Quotient.mk (P k) a) = 0 :=
      congrArg Subtype.val h1
    rw [IsScalarTower.algebraMap_eq (A ⧸ P k) (FractionRing (A ⧸ P k)) (AlgebraicClosure (FractionRing (A ⧸ P k))),
      RingHom.comp_apply] at h2
    have h3 := (IsFractionRing.injective (A ⧸ P k) (FractionRing (A ⧸ P k)))
      ((algebraMap (FractionRing (A ⧸ P k)) _).injective (h2.trans (map_zero _).symm) |>.trans (map_zero _).symm)
    exact Ideal.Quotient.eq_zero_iff_mem.1 h3
  change a ∈ (⊥ : Ideal A).radical
  rw [← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
  intro p hp
  obtain ⟨k, hk⟩ := σ.surjective ⟨p, hp⟩
  have := hmem k
  simp only [P, hk] at this
  exact this

end GlobalTheory.EtC.GmKill

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES

theorem isMonHom_id_npow {Y : Scheme.{0}} (A : Over Y) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    IsMonHom ((𝟙 A) ^ n) := by
  have h := Grp.Hom.hom_hom_zpow (G := Grp.mk A) (H := Grp.mk A) (𝟙 _) (n : ℤ)
  have h' : IsMonHom ((𝟙 (Grp.mk A) : Grp.mk A ⟶ Grp.mk A) ^ (n : ℤ)).hom.hom := inferInstance
  rw [h, zpow_natCast] at h'
  exact h'

theorem polKer_locus_clopen : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ ∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W ↔ PolKerAt o ψ' c t := by
  intro p _ D R _ b N c Y s o B _ _ ψ ψ' hp ⟨e, hc⟩ hB hq
  have hpY : IsUnit ((p : ℕ) : Γ(Y, ⊤)) := by
    have := hp.map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rwa [map_natCast] at this
  have hn : IsUnit ((c ^ 3 : ℕ) : Γ(Y, ⊤)) := by
    rw [hc, ← pow_mul, Nat.cast_pow]
    exact hpY.pow _
  obtain ⟨C, _, Q, h, hC, -, -, hh, -, hT⟩ := GlobalTheory.T.harrisTaylor_pullback_bundle_dual_hom p D R b N Y s o B ψ' hB hq.2.1
  haveI := isMonHom_id_npow B c
  have hcomp : ∀ {T : Over Y} (x : T ⟶ B), x ≫ (𝟙 B) ^ c = x ^ c := fun x => by
    rw [MonObj.comp_pow, Category.comp_id]
  obtain ⟨W₁, o₁, c₁, H₁, -⟩ := GlobalTheory.T.isClopen_torsion_kernel_locus Y B (c ^ 3) Unit (fun _ => C) (fun _ => h) B ((𝟙 B) ^ c) hB
    (fun _ => hC) hB (fun _ => hh) inferInstance hn
  obtain ⟨W₂, o₂, c₂, H₂, -⟩ := GlobalTheory.T.isClopen_torsion_kernel_locus Y B (c ^ 3) Unit (fun _ => B) (fun _ => (𝟙 B) ^ c) C h hB
    (fun _ => hB) hC (fun _ => inferInstance) hh hn
  refine ⟨W₁ ∩ W₂, o₁.inter o₂, c₁.inter c₂, fun Tb t => ?_⟩
  rw [Set.subset_inter_iff, H₁, H₂]
  constructor
  · rintro ⟨h₁, h₂⟩ T σ hσ x hx
    rw [hT]
    refine ⟨fun hx' => ?_, fun hx' => ?_⟩
    · rw [← hcomp]; exact h₁ T σ hσ x hx fun _ => hx'
    · exact h₂ T σ hσ x hx fun _ => by rw [hcomp]; exact hx'
  · intro H
    refine ⟨fun T σ hσ x hx hx' => ?_, fun T σ hσ x hx hx' => ?_⟩
    · rw [hcomp]; exact ((H T σ hσ x hx).1 ((hT T x).2 (hx' ())))
    · exact (hT T x).1 ((H T σ hσ x hx).2 (by rw [← hcomp]; exact hx' ()))

end GlobalTheory.UPel.HT.ES
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.klt_of_klt_restrict_alt : GlobalTheory.Published.Principalisation →
  ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (T : Subring L) (hT : IsLocModel cL T)
    (ψ : T →+* K) (f : T) (w : Fin n → T) (θ : T →₀ ℚ),
  IsIntegrallyClosed T → (∀ a, ψ ⟨cL a, hT.const_mem a⟩ = cK a) →
  RingHom.ker ψ = Ideal.span {f} → f ≠ 0 → IsLocModel cK ψ.range → TrBasis cK (fun i => ψ (w i)) →
  (∀ g ∈ θ.support, ψ g ≠ 0) →
  EffAt cL (n + 1) T (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L))
    (Finsupp.mapDomain (fun g : T => (g : L)) θ) →
  Klt cK n ψ.range (dForm cK (fun i => ψ (w i))) (Finsupp.mapDomain ψ θ) →
  Klt cL (n + 1) T (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L))
    (Finsupp.mapDomain (fun g : T => (g : L)) θ) := by
  first | exact @GlobalTheory.FieldPair.klt_of_klt_restrict | exact GlobalTheory.FieldPair.klt_of_klt_restrict | (intros; apply GlobalTheory.FieldPair.klt_of_klt_restrict <;> assumption)
end
