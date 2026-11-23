module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle265
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle270
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle187
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.MuTw
variable (q : ℕ) [NeZero q]

instance muModule (A : Type) [CommRing A] : Module (ZMod q) (Additive (rootsOfUnity q A)) :=
  AddCommGroup.zmodModule (fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact Subtype.ext (by
      simp only [Subgroup.coe_pow, OneMemClass.coe_one]
      exact (mem_rootsOfUnity q _).1 (Additive.toMul x).2))

theorem smul_eq (A : Type) [CommRing A] (c : ZMod q) (x : Additive (rootsOfUnity q A)) : c • x = c.val • x := by
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  rw [Nat.cast_smul_eq_nsmul]

def muMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    ULift.{1} (Additive (rootsOfUnity q A)) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (Additive (rootsOfUnity q B)) where
  toFun x := ⟨Additive.ofMul (restrictRootsOfUnity f q (Additive.toMul x.down))⟩
  map_add' x y := congrArg ULift.up (congrArg Additive.ofMul (map_mul (restrictRootsOfUnity f q) _ _))
  map_smul' c x := by
    apply ULift.ext
    change Additive.ofMul (restrictRootsOfUnity f q (Additive.toMul (c.down • x.down))) =
      c.down • Additive.ofMul (restrictRootsOfUnity f q (Additive.toMul x.down))
    rw [smul_eq, smul_eq, toMul_nsmul, map_pow, ofMul_pow]

theorem muMap_coe {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : ULift.{1} (Additive (rootsOfUnity q A))) :
    (((Additive.toMul (muMap q f x).down : rootsOfUnity q B) : Bˣ) : B) = f (((Additive.toMul x.down : rootsOfUnity q A) : Aˣ) : A) :=
  restrictRootsOfUnity_coe_apply f _

def muF : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) where
  obj A := ModuleCat.of _ (ULift.{1} (Additive (rootsOfUnity q A)))
  map f := ModuleCat.ofHom (muMap q f.hom)
  map_id A := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    apply ULift.ext; apply Additive.toMul.injective; apply Subtype.ext; apply Units.ext
    exact muMap_coe q _ x
  map_comp f g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    apply ULift.ext; apply Additive.toMul.injective; apply Subtype.ext; apply Units.ext
    exact muMap_coe q _ x

theorem prim_pow {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨g, hg⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hg
  rw [map_mul, ζ.2.2, zero_mul, map_sub, map_pow, Polynomial.aeval_X, map_one] at h
  exact sub_eq_zero.1 h

def root {A : Type} [CommRing A] (ζ : Prim q A) : rootsOfUnity q A := rootsOfUnity.mkOfPowEq ζ.1 (prim_pow q ζ)

theorem root_coe {A : Type} [CommRing A] (ζ : Prim q A) : (((root q ζ : rootsOfUnity q A) : Aˣ) : A) = ζ.1 := rfl

def etaLin (A : Type) [CommRing A] : (Prim q A →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (Additive (rootsOfUnity q A)) :=
  Finsupp.lift _ _ _ (fun ζ => ⟨Additive.ofMul (root q ζ)⟩)

theorem etaLin_single (A : Type) [CommRing A] (ζ : Prim q A) (c : ULift.{1} (ZMod q)) :
    etaLin q A (Finsupp.single ζ c) = ⟨c.down • Additive.ofMul (root q ζ)⟩ := by
  rw [etaLin, Finsupp.lift_apply, Finsupp.sum_single_index]
  · rfl
  · exact zero_smul _ _

theorem root_pow_coe {A : Type} [CommRing A] (ζ : Prim q A) (n : ℕ) :
    ((((root q ζ) ^ n : rootsOfUnity q A) : Aˣ) : A) = ζ.1 ^ n := by
  simp [root_coe]

theorem twRel_le_ker (A : Type) [CommRing A] : twRel q 1 A ≤ LinearMap.ker (etaLin q A) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ, ξ, a, h, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, etaLin_single]
  rw [sub_eq_zero]
  apply ULift.ext
  change (1 : ZMod q) • Additive.ofMul (root q ξ) = ((a ^ (1 : ℤ) : (ZMod q)ˣ) : ZMod q) • Additive.ofMul (root q ζ)
  rw [one_smul, zpow_one, smul_eq, ← ofMul_pow]
  congr 1
  apply Subtype.ext; apply Units.ext
  rw [root_pow_coe, root_coe, h]

def eta : twF q 1 ⟶ muF q where
  app A := ModuleCat.ofHom (Submodule.liftQ _ (etaLin q A) (twRel_le_ker q A))
  naturality A B f := by
    refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (Finsupp.lhom_ext fun ζ c => ?_))
    change etaLin q B (Finsupp.mapDomain (Prim.map f.hom) (Finsupp.single ζ c)) = muMap q f.hom (etaLin q A (Finsupp.single ζ c))
    rw [Finsupp.mapDomain_single, etaLin_single, etaLin_single]
    apply ULift.ext
    change c.down • Additive.ofMul (root q (Prim.map f.hom ζ)) =
      (muMap q f.hom (c • ⟨Additive.ofMul (root q ζ)⟩)).down
    rw [map_smul]
    change _ = c.down • (muMap q f.hom ⟨Additive.ofMul (root q ζ)⟩).down
    congr 1
    apply Additive.toMul.injective; apply Subtype.ext; apply Units.ext
    exact (muMap_coe q f.hom ⟨Additive.ofMul (root q ζ)⟩).symm

theorem eta_mk (A : CommRingCat.{0}) (ζ : Prim q A) (c : ULift.{1} (ZMod q)) :
    ((eta q).app A).hom (Submodule.Quotient.mk (Finsupp.single ζ c)) = ⟨c.down • Additive.ofMul (root q ζ)⟩ :=
  etaLin_single q A ζ c

abbrev rval {V : Scheme.{0}} (t : ((Scheme.Γ ⋙ muF q) ⋙ forget (ModuleCat.{1} (ULift.{1} (ZMod q)))).obj (op V)) : Γ(V, ⊤)ˣ :=
  ((Additive.toMul (ULift.down (α := Additive (rootsOfUnity q Γ(V, ⊤))) t) : rootsOfUnity q Γ(V, ⊤)) : Γ(V, ⊤)ˣ)

theorem rval_map {V W : Scheme.{0}} (g : W ⟶ V) (t : ((Scheme.Γ ⋙ muF q) ⋙ forget (ModuleCat.{1} (ULift.{1} (ZMod q)))).obj (op V)) :
    ((rval q (((Scheme.Γ ⋙ muF q) ⋙ forget (ModuleCat.{1} (ULift.{1} (ZMod q)))).map g.op t) : Γ(W, ⊤)ˣ) : Γ(W, ⊤)) =
      (Scheme.Γ ⋙ forget CommRingCat).map g.op ((rval q t : Γ(V, ⊤)ˣ) : Γ(V, ⊤)) := muMap_coe q _ _

theorem isSheaf : Presheaf.IsSheaf Scheme.etaleTopology.{0} (Scheme.Γ ⋙ muF q) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))), isSheaf_iff_isSheaf_of_type]
  intro U S hS x hx
  have hG := GmSec.isSheaf_gamma S hS
  let v : Presieve.FamilyOfElements (Scheme.Γ ⋙ forget CommRingCat) S.arrows :=
    fun V f hf => ((rval q (x f hf) : Γ(V, ⊤)ˣ) : Γ(V, ⊤))
  have hv : v.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e
    have := congrArg (fun t => ((rval q t : Γ(Z, ⊤)ˣ) : Γ(Z, ⊤))) (hx g₁ g₂ h₁ h₂ e)
    simp only [rval_map] at this
    exact this
  obtain ⟨a, ha, -⟩ := hG v hv
  have hq : a ^ q = 1 := by
    refine hG.isSeparatedFor.ext (fun V f hf => ?_)
    change (Scheme.Γ.map f.op).hom (a ^ q) = (Scheme.Γ.map f.op).hom 1
    rw [map_pow, map_one]
    have h1 := ha f hf
    change (Scheme.Γ.map f.op).hom a = _ at h1
    rw [h1]
    change ((rval q (x f hf) : Γ(V, ⊤)ˣ) : Γ(V, ⊤)) ^ q = 1
    have hr : rval q (x f hf) ^ q = 1 :=
      (mem_rootsOfUnity q _).1 (Additive.toMul (ULift.down (α := Additive (rootsOfUnity q Γ(V, ⊤))) (x f hf))).2
    rw [← Units.val_pow_eq_pow_val, hr, Units.val_one]
  refine ⟨(ULift.up (Additive.ofMul (rootsOfUnity.mkOfPowEq a hq)) :
    ((Scheme.Γ ⋙ muF q) ⋙ forget (ModuleCat.{1} (ULift.{1} (ZMod q)))).obj (op U)), ?_, ?_⟩
  · intro V f hf
    apply ULift.ext; apply Additive.toMul.injective; apply Subtype.ext; apply Units.ext
    exact (rval_map q f _).trans (ha f hf)
  · intro y hy
    apply ULift.ext; apply Additive.toMul.injective; apply Subtype.ext; apply Units.ext
    refine hG.isSeparatedFor.ext (fun V f hf => ?_)
    have e1 := congrArg (fun t => ((rval q t : Γ(V, ⊤)ˣ) : Γ(V, ⊤))) (hy f hf)
    simp only [rval_map] at e1
    exact e1.trans (ha f hf).symm

def muS : Shv (ZMod q) := ⟨Scheme.Γ ⋙ muF q, isSheaf q⟩

def etaS : tw q 1 ⟶ muS q := ⟨sheafifyLift Scheme.etaleTopology (Functor.whiskerLeft Scheme.Γ (eta q)) (isSheaf q)⟩

theorem etaS_sec (U : Scheme.{0}) (m : (twF q 1).obj Γ(U, ⊤)) :
    Sec.map (etaS q) (ofRings.sec (twF q 1) U m) = ((eta q).app Γ(U, ⊤)).hom m := by
  have h := toSheafify_sheafifyLift Scheme.etaleTopology (Functor.whiskerLeft Scheme.Γ (eta q)) (isSheaf q)
  exact congrArg (fun φ => (φ.app (op U)).hom m) h

theorem etaS_res {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec (tw q 1) U) :
    Sec.map (etaS q) (Sec.res g x) = Sec.res g (Sec.map (etaS q) x) :=
  congrArg (fun φ => φ.hom x) ((etaS q).hom.naturality g.op)

abbrev muVal {U : Scheme.{0}} (y : Sec (muS q) U) : Γ(U, ⊤) :=
  (((Additive.toMul (ULift.down (α := Additive (rootsOfUnity q Γ(U, ⊤))) y) : rootsOfUnity q Γ(U, ⊤)) : Γ(U, ⊤)ˣ) : Γ(U, ⊤))

theorem muVal_res {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec (muS q) U) : muVal q (Sec.res g y) = g.appTop.hom (muVal q y) :=
  muMap_coe q _ _

theorem muVal_injective (U : Scheme.{0}) : Function.Injective (muVal q (U := U)) := fun y y' h => by
  apply ULift.ext; apply Additive.toMul.injective; apply Subtype.ext; exact Units.ext h

end GlobalTheory.EtC.MuTw
end
end

section

open CategoryTheory GlobalTheory.CxCoh

theorem _root_.GlobalTheory.T.joinedMapsAgreeCohomologyZeroOne_instances : JoinedOne.{1,1} ∧ JoinedOne.{1,0} ∧ JoinedOne.{0,0} := by
  first | exact @GlobalTheory.CxCoh.joinedOne_inst | exact GlobalTheory.CxCoh.joinedOne_inst | (intros; apply GlobalTheory.CxCoh.joinedOne_inst <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.PDA

variable {B : Type} [CommRing B]

def PDPoly.liftAlg (Q : PDPoly B) {C : Type} [CommRing C] [Algebra B C] (c : ℕ → C) (h0 : c 0 = 1)
    (hm : ∀ m n, c m * c n = ((m + n).choose m : C) * c (m + n)) : Q.P →ₐ[B] C :=
  AlgHom.ofLinearMap (Q.e.constr B c) (by rw [← Q.e_zero, Module.Basis.constr_basis, h0]) (by
    intro x y
    have key : (LinearMap.mul B Q.P).compr₂ (Q.e.constr B c) =
        (LinearMap.mul B C).compl₁₂ (Q.e.constr B c) (Q.e.constr B c) := by
      refine Q.e.ext fun m ↦ Q.e.ext fun n ↦ ?_
      simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₁₂_apply,
        Module.Basis.constr_basis, Q.e_mul]
      rw [← nsmul_eq_mul, LinearMap.map_smul_of_tower, Module.Basis.constr_basis, nsmul_eq_mul, hm]
    exact congrArg (fun g ↦ g x y) key)

theorem PDPoly.liftAlg_e (Q : PDPoly B) {C : Type} [CommRing C] [Algebra B C] (c : ℕ → C) (h0 : c 0 = 1)
    (hm : ∀ m n, c m * c n = ((m + n).choose m : C) * c (m + n)) (n : ℕ) :
    Q.liftAlg c h0 hm (Q.e n) = c n :=
  Q.e.constr_basis B c n

theorem PDPoly.exists_lift_and_aug : ∀ (B : Type) [CommRing B] (Q : PDPoly B),
    (∀ (C : Type) [CommRing C] (f : B →+* C) (c : ℕ → C), c 0 = 1 →
      (∀ m n, c m * c n = ((m + n).choose m : C) * c (m + n)) →
      ∃ F : Q.P →+* C, (∀ b, F (algebraMap B Q.P b) = f b) ∧ ∀ n, F (Q.e n) = c n) ∧
    ∃ ε : Q.P →ₐ[B] B, ∀ p, p ∈ Q.aug ↔ ε p = 0 := by
  intro B _ Q
  refine ⟨fun C _ f c h0 hm ↦ ?_, ?_⟩
  · letI := f.toAlgebra
    exact ⟨(Q.liftAlg c h0 hm).toRingHom, fun b ↦ (Q.liftAlg c h0 hm).commutes b,
      fun n ↦ Q.liftAlg_e c h0 hm n⟩
  · let d : ℕ → B := fun n ↦ if n = 0 then 1 else 0
    have h0 : d 0 = 1 := by simp [d]
    have hm : ∀ m n, d m * d n = ((m + n).choose m : B) * d (m + n) := by
      intro m n
      by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp [d, hm, hn]
    let ε := Q.liftAlg d h0 hm
    have hε : ∀ n, ε (Q.e n) = d n := Q.liftAlg_e d h0 hm
    have hmem : ∀ p, p - algebraMap B Q.P (ε p) ∈ Q.aug := by
      intro p
      have hp : p ∈ Submodule.span B (Set.range Q.e) := by rw [Q.e.span_eq]; trivial
      induction hp using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨n, rfl⟩ := hx
        rw [hε]
        rcases n with _ | n
        · simp [d, Q.e_zero]
        · simpa [d] using Q.e_succ_mem_aug n
      | zero => simp
      | add x y _ _ hx hy =>
        have : x + y - algebraMap B Q.P (ε (x + y)) =
            (x - algebraMap B Q.P (ε x)) + (y - algebraMap B Q.P (ε y)) := by
          rw [map_add (f := _), map_add (f := _)]; abel
        rw [this]; exact add_mem hx hy
      | smul b x _ hx =>
        have : b • x - algebraMap B Q.P (ε (b • x)) = algebraMap B Q.P b * (x - algebraMap B Q.P (ε x)) := by
          rw [map_smul, smul_eq_mul, map_mul, Algebra.smul_def, mul_sub]
        rw [this]; exact Q.aug.mul_mem_left _ hx
    refine ⟨ε, fun p ↦ ⟨fun hp ↦ ?_, fun hp ↦ ?_⟩⟩
    · have hle : Q.aug ≤ RingHom.ker ε := by
        refine Ideal.span_le.2 ?_
        rintro _ ⟨n, rfl⟩
        simp [RingHom.mem_ker, hε, d]
      exact RingHom.mem_ker.1 (hle hp)
    · have := hmem p
      rwa [hp, map_zero, sub_zero] at this

end GlobalTheory.PDA
end
end

section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDA

open MvPolynomial Finset

def dpBas2 (p : ℕ × ℕ) : MvPolynomial (Fin 2) ℚ :=
  ((p.1.factorial : ℚ)⁻¹ • X 0 ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • X 1 ^ p.2)

theorem IsPreDP.eval_zero {B : Type} [CommRing B] {J : Ideal B} {γ : ℕ → B → B} (h : IsPreDP J γ)
    {n : ℕ} (hn : n ≠ 0) : γ n 0 = 0 := by
  have := h.mul n 0 0 J.zero_mem
  rwa [mul_zero, zero_pow hn, zero_mul] at this

theorem IsPreDP.comp_add {B : Type} [CommRing B] {J : Ideal B} {γ : ℕ → B → B} (h : IsPreDP J γ)
    {x y : B} (hx : x ∈ J) (hy : y ∈ J)
    (Px : ∀ m n : ℕ, n ≠ 0 → γ m (γ n x) = (m.uniformBell n : B) * γ (m * n) x)
    (Py : ∀ m n : ℕ, n ≠ 0 → γ m (γ n y) = (m.uniformBell n : B) * γ (m * n) y)
    (m n : ℕ) (hn : n ≠ 0) : γ m (γ n (x + y)) = (m.uniformBell n : B) * γ (m * n) (x + y) := by
  classical
  set D := Submodule.span ℤ (Set.range dpBas2) with hD
  obtain ⟨φ, hφb, hφ2, hφz⟩ : ∃ φ : MvPolynomial (Fin 2) ℚ → B,
      (∀ a c : ℕ, φ (dpBas2 (a, c)) = γ a x * γ c y) ∧
      (∀ d ∈ D, ∀ e ∈ D, φ (d + e) = φ d + φ e ∧ d * e ∈ D ∧ φ (d * e) = φ d * φ e) ∧
      (∀ z : ℤ, ∀ d ∈ D, φ (z • d) = z • φ d) :=
    GlobalTheory.T.exists_dividedPowerEval_twoVars_ringHom B (fun a ↦ γ a x) (fun c ↦ γ c y) (h.zero x hx) (h.zero y hy)
      (fun a b ↦ h.mul_dpow a b x hx) (fun a b ↦ h.mul_dpow a b y hy)
  let Γ : DividedPowers (⊤ : Ideal (MvPolynomial (Fin 2) ℚ)) := RatAlgebra.dividedPowers ⊤
  have top : ∀ q : MvPolynomial (Fin 2) ℚ, q ∈ (⊤ : Ideal _) := fun _ ↦ Submodule.mem_top
  have hΓ : ∀ (k : ℕ) (q : MvPolynomial (Fin 2) ℚ), Γ.dpow k q = (k.factorial : ℚ)⁻¹ • q ^ k := fun k q ↦ by
    rw [RatAlgebra.dpow_eq_inv_fact_smul _ Γ (top q), Ring.inverse_eq_inv']
  have hbasΓ : ∀ p : ℕ × ℕ, dpBas2 p = Γ.dpow p.1 (X 0) * Γ.dpow p.2 (X 1) := fun p ↦ by
    rw [dpBas2, hΓ, hΓ]
  have hX0 : ∀ a, Γ.dpow a (X 0) = dpBas2 (a, 0) := fun a ↦ by
    rw [hbasΓ, Γ.dpow_zero (top _), mul_one]
  have hX1 : ∀ c, Γ.dpow c (X 1) = dpBas2 (0, c) := fun c ↦ by
    rw [hbasΓ, Γ.dpow_zero (top _), one_mul]
  have hbasΓ' : ∀ a c, dpBas2 (a, c) = Γ.dpow a (X 0) * Γ.dpow c (X 1) := fun a c ↦ hbasΓ (a, c)
  have hDb : ∀ p, dpBas2 p ∈ D := fun p ↦ Submodule.subset_span ⟨p, rfl⟩
  have hone : dpBas2 (0, 0) = 1 := by simp [dpBas2]
  have hφ1 : φ 1 = 1 := by rw [← hone, hφb, h.zero x hx, h.zero y hy, one_mul]
  have hD1 : (1 : MvPolynomial (Fin 2) ℚ) ∈ D := hone ▸ hDb _
  have hφ0 : φ 0 = 0 := by
    have := (hφ2 0 D.zero_mem 0 D.zero_mem).1
    rw [add_zero] at this
    exact left_eq_add.mp this
  have hpow : ∀ d ∈ D, ∀ k : ℕ, d ^ k ∈ D ∧ φ (d ^ k) = φ d ^ k := by
    intro d hd k
    induction k with
    | zero => simpa using ⟨hD1, hφ1⟩
    | succ k ih =>
      obtain ⟨_, h2, h3⟩ := hφ2 _ ih.1 d hd
      rw [pow_succ, pow_succ, h3, ih.2]
      exact ⟨h2, rfl⟩
  have hsum : ∀ (t : Finset (ℕ × ℕ)) (f : ℕ × ℕ → MvPolynomial (Fin 2) ℚ), (∀ i ∈ t, f i ∈ D) →
      (∑ i ∈ t, f i) ∈ D ∧ φ (∑ i ∈ t, f i) = ∑ i ∈ t, φ (f i) := by
    intro t f hf
    induction t using Finset.induction with
    | empty => simp [hφ0]
    | insert i t hi ih =>
      have ih' := ih fun j hj ↦ hf j (mem_insert_of_mem hj)
      have hfi := hf i (mem_insert_self i t)
      rw [sum_insert hi, sum_insert hi, (hφ2 _ hfi _ ih'.1).1, ih'.2]
      exact ⟨add_mem hfi ih'.1, rfl⟩
  have hnat : ∀ (N : ℕ), ∀ d ∈ D, (N : MvPolynomial (Fin 2) ℚ) * d ∈ D ∧ φ ((N : MvPolynomial (Fin 2) ℚ) * d) = N * φ d := by
    intro N d hd
    have e1 : (N : MvPolynomial (Fin 2) ℚ) * d = (N : ℤ) • d := by rw [zsmul_eq_mul, Int.cast_natCast]
    refine ⟨by rw [e1]; exact Submodule.smul_mem _ _ hd, ?_⟩
    rw [e1, hφz _ _ hd, zsmul_eq_mul, Int.cast_natCast]
  have hsX : ∀ N : ℕ, Γ.dpow N (X 0 + X 1) ∈ D ∧ φ (Γ.dpow N (X 0 + X 1)) = γ N (x + y) := by
    intro N
    have e1 : Γ.dpow N (X 0 + X 1) = ∑ p ∈ antidiagonal N, dpBas2 p := by
      rw [Γ.dpow_add (top _) (top _)]
      exact sum_congr rfl fun p _ ↦ (hbasΓ p).symm
    rw [e1, (hsum _ _ fun p _ ↦ hDb p).2, h.add N x hx y hy]
    exact ⟨(hsum _ _ fun p _ ↦ hDb p).1, sum_congr rfl fun p _ ↦ hφb p.1 p.2⟩
  set Dp := Submodule.span ℤ (dpBas2 '' {p | p ≠ 0}) with hDp
  have T : ∀ d ∈ Dp, d ∈ D ∧ φ d ∈ J ∧ ∀ k, Γ.dpow k d ∈ D ∧ γ k (φ d) = φ (Γ.dpow k d) := by
    intro d hd
    induction hd using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨⟨a, c⟩, hac, rfl⟩ := hd
      refine ⟨hDb _, ?_, fun k ↦ ?_⟩
      · rw [hφb]
        by_cases ha : a = 0
        · have hc : c ≠ 0 := by rintro rfl; exact hac (by simp [ha])
          exact J.mul_mem_left _ (h.mem c hc y hy)
        · exact J.mul_mem_right _ (h.mem a ha x hx)
      show Γ.dpow k (dpBas2 (a, c)) ∈ D ∧ γ k (φ (dpBas2 (a, c))) = φ (Γ.dpow k (dpBas2 (a, c)))
      rw [hφb a c]
      by_cases ha : a = 0
      · subst ha
        have hc : c ≠ 0 := by rintro rfl; exact hac rfl
        have e : Γ.dpow k (dpBas2 (0, c)) = ((k.uniformBell c : ℕ) : MvPolynomial (Fin 2) ℚ) * dpBas2 (0, k * c) := by
          rw [← hX1 c, Γ.dpow_comp hc (top _), hX1 (k * c)]
        obtain ⟨h1, h2⟩ := hnat (k.uniformBell c) _ (hDb (0, k * c))
        rw [e]
        refine ⟨h1, ?_⟩
        rw [h2, hφb, h.zero x hx, one_mul, one_mul, Py k c hc]
      · have e : Γ.dpow k (dpBas2 (a, c)) =
            ((k.uniformBell a : ℕ) : MvPolynomial (Fin 2) ℚ) * dpBas2 (k * a, 0) * dpBas2 (0, c) ^ k := by
          rw [hbasΓ' a c, Γ.dpow_mul_right (top _), Γ.dpow_comp ha (top _), hX0 (k * a), hX1 c]
        obtain ⟨h1, h2⟩ := hnat (k.uniformBell a) _ (hDb (k * a, 0))
        obtain ⟨h3, h4⟩ := hpow _ (hDb (0, c)) k
        obtain ⟨_, h5, h6⟩ := hφ2 _ h1 _ h3
        rw [e]
        refine ⟨h5, ?_⟩
        rw [h6, h2, h4, hφb, hφb, h.zero x hx, h.zero y hy, mul_comm (γ a x), h.mul k _ _ (h.mem a ha x hx),
          Px k a ha]
        ring
    | zero =>
      refine ⟨D.zero_mem, hφ0 ▸ J.zero_mem, fun k ↦ ?_⟩
      by_cases hk : k = 0
      · subst hk
        rw [Γ.dpow_zero (top _), hφ0, h.zero 0 J.zero_mem, hφ1]
        exact ⟨hD1, rfl⟩
      · rw [Γ.dpow_eval_zero hk, hφ0, h.eval_zero hk]
        exact ⟨D.zero_mem, rfl⟩
    | add d e _ _ hd he =>
      obtain ⟨dD, dJ, dk⟩ := hd
      obtain ⟨eD, eJ, ek⟩ := he
      obtain ⟨hde, -, -⟩ := hφ2 d dD e eD
      refine ⟨add_mem dD eD, hde ▸ add_mem dJ eJ, fun k ↦ ?_⟩
      have hm : ∀ p ∈ antidiagonal k, Γ.dpow p.1 d * Γ.dpow p.2 e ∈ D := fun p _ ↦
        (hφ2 _ (dk p.1).1 _ (ek p.2).1).2.1
      rw [Γ.dpow_add (top _) (top _), hde, h.add k _ dJ _ eJ, (hsum _ _ hm).2]
      refine ⟨(hsum _ _ hm).1, sum_congr rfl fun p _ ↦ ?_⟩
      rw [(dk p.1).2, (ek p.2).2, (hφ2 _ (dk p.1).1 _ (ek p.2).1).2.2]
    | smul z d _ hd =>
      obtain ⟨dD, dJ, dk⟩ := hd
      refine ⟨Submodule.smul_mem _ _ dD, (hφz z d dD) ▸ zsmul_mem dJ z, fun k ↦ ?_⟩
      have e1 : Γ.dpow k (z • d) = (z ^ k) • Γ.dpow k d := by
        rw [zsmul_eq_mul, Γ.dpow_mul (top _), zsmul_eq_mul, Int.cast_pow]
      refine ⟨by rw [e1]; exact Submodule.smul_mem _ _ (dk k).1, ?_⟩
      rw [e1, hφz _ _ dD, hφz _ _ (dk k).1, zsmul_eq_mul, h.mul k _ _ dJ, (dk k).2, zsmul_eq_mul, Int.cast_pow]
  have hmem : Γ.dpow n (X 0 + X 1) ∈ Dp := by
    rw [Γ.dpow_add (top _) (top _)]
    refine Submodule.sum_mem _ fun p hp ↦ ?_
    rw [← hbasΓ]
    refine Submodule.subset_span ⟨p, fun h0 ↦ hn ?_, rfl⟩
    rw [HasAntidiagonal.mem_antidiagonal] at hp
    rw [← hp, h0]; rfl
  obtain ⟨_, _, hk⟩ := T _ hmem
  rw [← (hsX n).2, (hk m).2, Γ.dpow_comp hn (top _), (hnat _ _ (hsX _).1).2, (hsX _).2]

theorem exists_dividedPowers_of_comp_on_gens :
    ∀ (B : Type) [CommRing B] (J : Ideal B) (γ : ℕ → B → B) (s : Set B), IsPreDP J γ → J = Ideal.span s →
      (∀ x ∈ s, ∀ m n : ℕ, n ≠ 0 → γ m (γ n x) = (m.uniformBell n : B) * γ (m * n) x) →
      ∃ δ : DividedPowers J, δ.dpow = γ := by
  intro B _ J γ s h hJ hs
  have key : ∀ x ∈ J, ∀ m n : ℕ, n ≠ 0 → γ m (γ n x) = (m.uniformBell n : B) * γ (m * n) x := by
    intro x hx
    subst hJ
    induction hx using Submodule.span_induction with
    | mem x hxs => exact hs x hxs
    | zero =>
      intro m n hn
      rw [h.eval_zero hn]
      by_cases hm : m = 0
      · subst hm
        rw [Nat.uniformBell_zero_left, zero_mul, h.zero 0 (Submodule.zero_mem _), Nat.cast_one, one_mul]
      · rw [h.eval_zero hm, h.eval_zero (mul_ne_zero hm hn), mul_zero]
    | add x y hx hy Px Py => exact fun m n hn ↦ h.comp_add hx hy Px Py m n hn
    | smul a x hx Px =>
      intro m n hn
      rw [smul_eq_mul, h.mul n a x hx, h.mul m _ _ (h.mem n hn x hx), Px m n hn, h.mul (m * n) a x hx, ← pow_mul,
        mul_comm n m]
      ring
  exact ⟨{ dpow := γ
           dpow_null := fun hx ↦ h.null _ _ hx
           dpow_zero := fun hx ↦ h.zero _ hx
           dpow_one := fun hx ↦ h.one _ hx
           dpow_mem := fun hn hx ↦ h.mem _ hn _ hx
           dpow_add := fun hx hy ↦ h.add _ _ hx _ hy
           dpow_mul := fun hx ↦ h.mul _ _ _ hx
           mul_dpow := fun hx ↦ h.mul_dpow _ _ _ hx
           dpow_comp := fun hn hx ↦ key _ hx _ _ hn }, rfl⟩

end GlobalTheory.PDA
end
end
