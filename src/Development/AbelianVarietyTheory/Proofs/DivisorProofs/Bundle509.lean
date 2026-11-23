module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle459
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle457
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle343
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTensorEtaleSheafComplexPairing
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
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
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

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_cochain_map_of_fibre_cocycle_pairing : ∀ (q N : ℕ) (i₁ i₂ i : ℤ) (h : i₁ + i₂ = i) (d : ℕ) (z : Cocycle ((chains (ZMod q)).obj (fibQ q N)) (res (ZMod q) (tw q i₂)) (2 * (d : ℤ))), ∃ ψ : Cocycle (res (ZMod q) (tw q i₁)) (Jcx (ZMod q) q N (res (ZMod q) (tw q i))) (2 * (d : ℤ)), ∀ (m w : ℤ) (hw : m + 2 * (d : ℤ) = w) (U : Scheme.{0}) (a : Sec ((res (ZMod q) (tw q i₁)).X m) U), ∃ c : Cochain ((chains (ZMod q)).obj (sch.obj U ⨯ fibQ q N)) (res (ZMod q) (tw q i)) w, Sec.map (ψ.1.v m w hw) a = Jsec c ∧ ∀ (k : ℕ) (s : ℤ) (hs : -(k : ℤ) + w = s) (V : Scheme.{0}) (y : Sx (sch.obj U ⨯ fibQ q N) k V), ev c k s hs V y = twCast h ((twPair q i₁ i₂).mul V m (-(k : ℤ) + 2 * (d : ℤ)) s (by omega) (Sec.res (Sx.map (prod.fst : sch.obj U ⨯ fibQ q N ⟶ _) y : V ⟶ U) a) (ev z.1 k (-(k : ℤ) + 2 * (d : ℤ)) rfl V (Sx.map prod.snd y))) := by
  first | (exact @GlobalTheory.EtC.PsiModel.psi_exists) | (exact GlobalTheory.EtC.PsiModel.psi_exists) | (intros; apply GlobalTheory.EtC.PsiModel.psi_exists  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.flatS_tw : ∀ (q : ℕ) [NeZero q] (i : ℤ),
    _root_.GlobalTheory.EtC.FlatS (_root_.GlobalTheory.EtC.tw q i) := by
  intro q _ i
  obtain ⟨h1, h2, -⟩ := _root_.GlobalTheory.EtC.toSheafify_loc_bij_lift (ZMod q)
    (Scheme.Γ ⋙ _root_.GlobalTheory.EtC.twF q i)
  refine ⟨_, toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ _root_.GlobalTheory.EtC.twF q i), h1, h2,
    fun U hU => ?_⟩
  obtain ⟨x⟩ := hU
  haveI : Nontrivial Γ(U, ⊤) := (U.presheaf.germ ⊤ x trivial).hom.domain_nontrivial
  haveI := (_root_.GlobalTheory.TwFree.twist_free q i Γ(U, ⊤)).1
  change Module.Flat (ULift.{1} (ZMod q))
    ((_root_.GlobalTheory.EtC.Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) ⧸
      _root_.GlobalTheory.EtC.twRel q i Γ(U, ⊤))
  infer_instance

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem etaleLocally_weaken_freeSheafSections {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : Loc U P) (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem free_sec_lin_sum {S X M : Type*} [Semiring S] [AddCommMonoid M] [Module S M]
    (φ : (X →₀ S) →ₗ[S] M) (x : X →₀ S) :
    (x.sum fun a r => r • φ (Finsupp.single a 1)) = φ x := by
  calc (x.sum fun a r => r • φ (Finsupp.single a 1))
      = x.sum fun a r => φ (Finsupp.single a r) := by
        refine Finsupp.sum_congr fun a _ => ?_
        rw [← map_smul, Finsupp.smul_single_one]
    _ = φ x := by rw [← map_finsuppSum, Finsupp.sum_single]

theorem free_sec_sum_eq (R : Type) [CommRing R] (P : PSh) (V : Scheme.{0})
    (x : ULift.{1} (P.obj (op V)) →₀ ULift.{1} R) :
    ((Finsupp.mapDomain ULift.down x).sum fun a r => r • freeGen R P V a) =
      ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom x := by
  rw [Finsupp.sum_mapDomain_index_inj ULift.down_injective]
  exact free_sec_lin_sum ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom x

theorem free_sec_loc : ∀ (R : Type) [CommRing R] (P : PSh) (U : Scheme.{0}), (∀ y : Sec ((free R).obj P) U, Loc U fun V g => ∃ c : P.obj (op V) →₀ ULift.{1} R, Sec.res g y = c.sum fun x r => r • freeGen R P V x) ∧ ∀ c : P.obj (op U) →₀ ULift.{1} R, (c.sum fun x r => r • freeGen R P U x) = 0 → Loc U fun _ g => Finsupp.mapDomain (P.map g.op) c = 0 := by
  intro R _ P U
  have base := GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift R ((freeP R).obj P)
  refine ⟨fun y => ?_, fun c hc => ?_⟩
  · refine etaleLocally_weaken_freeSheafSections (base.1 U y) ?_
    rintro V g ⟨x, hx⟩
    exact ⟨_, ((free_sec_sum_eq R P V x).trans hx).symm⟩
  · have hdu : Finsupp.mapDomain ULift.down (Finsupp.mapDomain ULift.up c) = c := by
      rw [← Finsupp.mapDomain_comp]
      exact Finsupp.mapDomain_id
    have h2 : ((Finsupp.mapDomain ULift.down (Finsupp.mapDomain ULift.up c)).sum
        fun a r => r • freeGen R P U a) = 0 := by
      rw [hdu]
      exact hc
    have hx := (free_sec_sum_eq R P U _).symm.trans h2
    refine etaleLocally_weaken_freeSheafSections (base.2.1 U _ hx) ?_
    intro V g hg
    have key : Finsupp.mapDomain ULift.down ((((freeP R).obj P).map g.op).hom
        (Finsupp.mapDomain ULift.up c)) = Finsupp.mapDomain (P.map g.op) c := by
      have e1 : (((freeP R).obj P).map g.op).hom (Finsupp.mapDomain ULift.up c) =
          Finsupp.mapDomain (fun a : ULift.{1} (P.obj (op U)) =>
            (ULift.up (P.map g.op a.down) : ULift.{1} (P.obj (op V)))) (Finsupp.mapDomain ULift.up c) := rfl
      rw [e1, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
      rfl
    rw [← key]
    exact (congrArg (Finsupp.mapDomain ULift.down) hg).trans Finsupp.mapDomain_zero

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

open scoped TensorProduct

namespace GlobalTheory.EtC.TensLocBij

theorem locAll {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) :
    Loc U P := GlobalTheory.T.etaleLocal_property_calculus_rules.1 U P h

theorem locMono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 U P Q h hPQ

theorem locAnd {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (hQ : Loc U Q) : Loc U fun V g => P V g ∧ Q V g := GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.1 U P Q hP hQ

theorem locTrans {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : Loc U fun V g => Loc V fun W k => P W (k ≫ g)) : Loc U P :=
  GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.2.1 U P h

theorem locFin {U : Scheme.{0}} {ι : Type} [Finite ι] (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : ∀ i, Loc U (P i)) : Loc U fun V g => ∀ i, P i V g :=
  GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.2.2.1 U ι P h

section Alg

variable {S : Type*} [CommRing S] {A B D : Type*} [AddCommGroup A] [Module S A]
  [AddCommGroup B] [Module S B] [AddCommGroup D] [Module S D]

theorem exists_fg_lTensor (x : A ⊗[S] B) :
    ∃ (J : Submodule S B) (_ : J.FG) (y : A ⊗[S] J), x = LinearMap.lTensor A J.subtype y := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨⊥, Submodule.fg_bot, 0, by simp⟩
  | tmul a b => exact ⟨S ∙ b, Submodule.fg_span_singleton b,
      a ⊗ₜ[S] ⟨b, Submodule.mem_span_singleton_self _⟩, rfl⟩
  | add x₁ x₂ ih₁ ih₂ =>
    obtain ⟨J₁, fg₁, y₁, rfl⟩ := ih₁
    obtain ⟨J₂, fg₂, y₂, rfl⟩ := ih₂
    refine ⟨J₁ ⊔ J₂, fg₁.sup fg₂, LinearMap.lTensor A (Submodule.inclusion le_sup_left) y₁ +
      LinearMap.lTensor A (Submodule.inclusion le_sup_right) y₂, ?_⟩
    rw [map_add (f := _), ← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply]
    rfl

theorem rTensor_comm_eq {Y : Type*} [AddCommGroup Y] [Module S Y] (g : B →ₗ[S] Y) (x : A ⊗[S] B) :
    LinearMap.rTensor A g (TensorProduct.comm S A B x) =
      TensorProduct.comm S A Y (LinearMap.lTensor A g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem fg_lTensor_eq_zero {J : Submodule S D} (hJ : J.FG) {t : A ⊗[S] J}
    (h : LinearMap.lTensor A J.subtype t = 0) :
    ∃ (K : Submodule S D) (hJK : J ≤ K), K.FG ∧
      LinearMap.lTensor A (Submodule.inclusion hJK) t = 0 := by
  have h' : LinearMap.rTensor A J.subtype (TensorProduct.comm S A J t) = 0 := by
    rw [rTensor_comm_eq, h, map_zero]
  obtain ⟨K, hJK, hK, h0⟩ := TensorProduct.eq_zero_of_fg_of_subtype_eq_zero hJ h'
  refine ⟨K, hJK, hK, ?_⟩
  rw [rTensor_comm_eq] at h0
  exact (LinearEquiv.map_eq_zero_iff _).mp h0

end Alg

end GlobalTheory.EtC.TensLocBij

namespace GlobalTheory.EtC.TensLocBij

variable {R : Type} [CommRing R] (C P Q : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ Q)

theorem surj
    (hs : ∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y)
    (U : Scheme.{0}) (y : TensorProduct (ULift.{1} R) (C.obj (op U)) (Q.obj (op U))) :
    Loc U fun V g => ∃ x, LinearMap.lTensor _ (φ.app (op V)).hom x =
      TensorProduct.map (C.map g.op).hom (Q.map g.op).hom y := by
  induction y using TensorProduct.induction_on with
  | zero => exact locAll fun V g => ⟨0, by simp⟩
  | tmul c q =>
    exact locMono (hs U q) fun V g ⟨x, hx⟩ => ⟨(C.map g.op).hom c ⊗ₜ x, by simp [hx]⟩
  | add a b ha hb =>
    exact locMono (locAnd ha hb) fun V g ⟨⟨x, hx⟩, ⟨x', hx'⟩⟩ => ⟨x + x', by simp [map_add (f := _), hx, hx']⟩

theorem kerPart
    (hi : ∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0)
    (V : Scheme.{0}) (K : Submodule (ULift.{1} R) (P.obj (op V)))
    (hK : ∀ k ∈ K, (φ.app (op V)).hom k = 0) (z : C.obj (op V) ⊗[ULift.{1} R] K) :
    Loc V fun _ h => TensorProduct.map (C.map h.op).hom (P.map h.op).hom
      (LinearMap.lTensor _ K.subtype z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => exact locAll fun _ _ => by simp
  | tmul c k => exact locMono (hi V k.1 (hK k.1 k.2)) fun W h hk => by simp [hk]
  | add a b ha hb => exact locMono (locAnd ha hb) fun W h ⟨h1, h2⟩ => by simp [map_add (f := _), h1, h2]

theorem map_restr_comp {U V W : Scheme.{0}} (g : V ⟶ U) (k : W ⟶ V) :
    TensorProduct.map (C.map (k ≫ g).op).hom (P.map (k ≫ g).op).hom =
      TensorProduct.map (C.map k.op).hom (P.map k.op).hom ∘ₗ
        TensorProduct.map (C.map g.op).hom (P.map g.op).hom := by
  rw [op_comp, Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp, ModuleCat.hom_comp,
    TensorProduct.map_comp]

theorem nat_apply {U V : Scheme.{0}} (g : V ⟶ U) (p : P.obj (op U)) :
    (φ.app (op V)).hom ((P.map g.op).hom p) = (Q.map g.op).hom ((φ.app (op U)).hom p) := by
  have := congrArg (fun h => ModuleCat.Hom.hom h p) (φ.naturality g.op)
  simpa using this

end GlobalTheory.EtC.TensLocBij

namespace GlobalTheory.EtC.TensLocBij

variable {R : Type} [CommRing R] (C P Q : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ Q)

theorem inj
    (hs : ∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y)
    (hi : ∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0)
    (U : Scheme.{0}) (x : TensorProduct (ULift.{1} R) (C.obj (op U)) (P.obj (op U)))
    (hx : LinearMap.lTensor _ (φ.app (op U)).hom x = 0) :
    Loc U fun _ g => TensorProduct.map (C.map g.op).hom (P.map g.op).hom x = 0 := by
  obtain ⟨B₀, hB₀, x₀, rfl⟩ := exists_fg_lTensor x
  have hcomp : (B₀.map (φ.app (op U)).hom).subtype ∘ₗ (φ.app (op U)).hom.submoduleMap B₀ =
      (φ.app (op U)).hom ∘ₗ B₀.subtype := rfl
  have ht : LinearMap.lTensor _ (B₀.map (φ.app (op U)).hom).subtype
      (LinearMap.lTensor _ ((φ.app (op U)).hom.submoduleMap B₀) x₀) = 0 := by
    rw [← LinearMap.lTensor_comp_apply, hcomp, LinearMap.lTensor_comp_apply]
    exact hx
  obtain ⟨K, hJK, ⟨s, hs'⟩, hK0⟩ := fg_lTensor_eq_zero (hB₀.map _) ht
  have hloc := locFin (ι := Fin s.card)
    (fun i V g => ∃ p, (φ.app (op V)).hom p = (Q.map g.op).hom (s.equivFin.symm i).1)
    (fun i => hs U (s.equivFin.symm i).1)
  apply locTrans
  refine locMono hloc fun V g hV => ?_
  have hle : K ≤ (LinearMap.range (φ.app (op V)).hom).comap (Q.map g.op).hom := by
    rw [← hs', Submodule.span_le]
    intro q hq
    obtain ⟨p, hp⟩ := hV (s.equivFin ⟨q, hq⟩)
    rw [Equiv.symm_apply_apply] at hp
    exact ⟨p, hp⟩
  let ρ := ((Q.map g.op).hom ∘ₗ K.subtype).codRestrict (LinearMap.range (φ.app (op V)).hom)
    (fun k => hle k.2)
  have key : LinearMap.lTensor _ (φ.app (op V)).hom.rangeRestrict ∘ₗ
      TensorProduct.map (C.map g.op).hom (P.map g.op).hom ∘ₗ LinearMap.lTensor _ B₀.subtype =
      TensorProduct.map (C.map g.op).hom ρ ∘ₗ LinearMap.lTensor _ (Submodule.inclusion hJK) ∘ₗ
        LinearMap.lTensor _ ((φ.app (op U)).hom.submoduleMap B₀) := by
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, TensorProduct.map_tmul]
    congr 1
    apply Subtype.ext
    simp [ρ, nat_apply]
  have hy : LinearMap.lTensor _ (φ.app (op V)).hom.rangeRestrict
      (TensorProduct.map (C.map g.op).hom (P.map g.op).hom (LinearMap.lTensor _ B₀.subtype x₀)) = 0 := by
    have := congrArg (fun L => L x₀) key
    simp only [LinearMap.comp_apply] at this
    rw [this, hK0, map_zero]
  have hex := lTensor_exact (C.obj (op V))
    (LinearMap.exact_subtype_ker_map (φ.app (op V)).hom.rangeRestrict)
    (LinearMap.surjective_rangeRestrict _)
  obtain ⟨z, hz⟩ := (hex _).mp hy
  have hK : ∀ k ∈ LinearMap.ker (φ.app (op V)).hom.rangeRestrict, (φ.app (op V)).hom k = 0 := by
    intro k hk
    have := congrArg Subtype.val (LinearMap.mem_ker.mp hk)
    simpa using this
  refine locMono (kerPart C P Q φ hi V _ hK z) fun W k hk => ?_
  rw [map_restr_comp, LinearMap.comp_apply, ← hz]
  exact hk

theorem main : ∀ (R : Type) [CommRing R] (C P Q : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ Q), (∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y) → (∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) → ∀ U : Scheme.{0}, (∀ y : TensorProduct (ULift.{1} R) (C.obj (op U)) (Q.obj (op U)), Loc U fun V g => ∃ x, LinearMap.lTensor _ (φ.app (op V)).hom x = TensorProduct.map (C.map g.op).hom (Q.map g.op).hom y) ∧ ∀ x : TensorProduct (ULift.{1} R) (C.obj (op U)) (P.obj (op U)), LinearMap.lTensor _ (φ.app (op U)).hom x = 0 → Loc U fun _ g => TensorProduct.map (C.map g.op).hom (P.map g.op).hom x = 0 :=
  fun _ _ C P Q φ hs hi U => ⟨surj C P Q φ hs U, inj C P Q φ hs hi U⟩

end GlobalTheory.EtC.TensLocBij

theorem GlobalTheory.EtC.tensor_loc_bij : ∀ (R : Type) [CommRing R] (C P Q : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ Q), (∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y) → (∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) → ∀ U : Scheme.{0}, (∀ y : TensorProduct (ULift.{1} R) (C.obj (op U)) (Q.obj (op U)), Loc U fun V g => ∃ x, LinearMap.lTensor _ (φ.app (op V)).hom x = TensorProduct.map (C.map g.op).hom (Q.map g.op).hom y) ∧ ∀ x : TensorProduct (ULift.{1} R) (C.obj (op U)) (P.obj (op U)), LinearMap.lTensor _ (φ.app (op U)).hom x = 0 → Loc U fun _ g => TensorProduct.map (C.map g.op).hom (P.map g.op).hom x = 0 :=
  GlobalTheory.EtC.TensLocBij.main
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.hypercohomologyPullback_bijective_of_termwise_bijective : ∀ (R : Type) [CommRing R] (I : Cx R) [I.IsStrictlyGE 0], (∀ n, Injective (I.X n)) → ∀ {K L : Cx R} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L), (∀ p n, Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f p)) I n)) → ∀ n, Function.Bijective (cpull g I n) := by
  first | (exact @GlobalTheory.LevelCx.main) | (exact GlobalTheory.LevelCx.main) | (intros; apply GlobalTheory.LevelCx.main  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleComplex_staircase_locally_exact : ∀ (R : Type) [CommRing R] (q e : ℕ) (K : Cx R) (a : ℤ), (∀ n, n < a → ∀ (U : Scheme.{0}) (x : Sec (K.X n) U), x = 0) → (∀ (n : ℤ) (U : Scheme.{0}) (y : Sec (K.X n) U), (q * e) • y = 0) → (∀ (n : ℤ) (U : Scheme.{0}) (x : Sec (K.X n) U), e • x = 0 → Loc U fun V g => ∃ y : Sec (K.X n) V, Sec.res g x = q • y) → (∀ (n : ℤ) (U : Scheme.{0}) (x : Sec (K.X n) U), q • x = 0 → Loc U fun V g => ∃ y : Sec (K.X n) V, Sec.res g x = e • y) → (∀ (n : ℤ) (U : Scheme.{0}) (b : Sec (K.X n) U), Sec.map (K.d n (n + 1)) b = 0 → Loc U fun V g => ∃ c : Sec (K.X (n - 1)) V, Sec.map (K.d (n - 1) n) c = Sec.res g b) → ∀ (n : ℤ) (U : Scheme.{0}) (x : Sec (K.X n) U), (Loc U fun V g => ∃ y : Sec (K.X (n + 1)) V, Sec.map (K.d n (n + 1)) (Sec.res g x) = q • y) → Loc U fun V g => ∃ (u : Sec (K.X (n - 1)) V) (y : Sec (K.X n) V), Sec.res g x = Sec.map (K.d (n - 1) n) u + q • y := by
  first | (exact @GlobalTheory.EtC.staircase_loc) | (exact GlobalTheory.EtC.staircase_loc) | (intros; apply GlobalTheory.EtC.staircase_loc  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleSheaf_descend_along_locallyBijective : ∀ (S : Type) [CommRing S] (P Q : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1}) (φ : P ⟶ Q), (∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y) → (∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) → ∀ (M : Shv S) (b : ∀ U : Scheme.{0}, P.obj (op U) →+ Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V ((P.map g.op).hom x)) → ∃ c : ∀ U : Scheme.{0}, Q.obj (op U) →+ Sec M U, (∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (c U y) = c V ((Q.map g.op).hom y)) ∧ ∀ U x, c U ((φ.app (op U)).hom x) = b U x := by
  first | (exact @GlobalTheory.EtC.desc_loc) | (exact GlobalTheory.EtC.desc_loc) | (intros; apply GlobalTheory.EtC.desc_loc  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.locallyFlatEtaleSheaf_locally_divisible : ∀ (Q q e : ℕ) [NeZero Q], q * e = Q → ∀ (M : Shv (ZMod Q)), FlatS M → ∀ (U : Scheme.{0}) (x : Sec M U), e • x = 0 → Loc U fun V g => ∃ y : Sec M V, Sec.res g x = q • y := by
  first | (exact @GlobalTheory.EtC.FlatLoc.flat_loc) | (exact GlobalTheory.EtC.FlatLoc.flat_loc) | (intros; apply GlobalTheory.EtC.FlatLoc.flat_loc  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.smooth_surjective_etale_locally_has_sections : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) [Smooth f] [Surjective f] (U : Scheme.{0}) (y : U ⟶ X), Loc U fun V g => ∃ x : V ⟶ Y, x ≫ f = g ≫ y := by
  first | exact @GlobalTheory.EtC.smooth_surjective_loc_sections | exact GlobalTheory.EtC.smooth_surjective_loc_sections | (intros; apply GlobalTheory.EtC.smooth_surjective_loc_sections <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.hypercohomologyPullbackPushforward_functorial : ∀ (R : Type) [CommRing R] , (∀ (K I : Cx R) (n : ℤ) x, cpull (𝟙 K) I n x = x ∧ cpush K (𝟙 I) n x = x) ∧ (∀ {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ) x, cpull (f ≫ g) I n x = cpull f I n (cpull g I n x)) ∧ (∀ (K : Cx R) {I J M : Cx R} (f : I ⟶ J) (g : J ⟶ M) (n : ℤ) x, cpush K (f ≫ g) n x = cpush K g n (cpush K f n x)) ∧ (∀ {K L I J : Cx R} (f : K ⟶ L) (g : I ⟶ J) (n : ℤ) x, cpull f J n (cpush L g n x) = cpush K g n (cpull f I n x)) ∧ (∀ {K L : Cx R} (f g : K ⟶ L), Nonempty (Homotopy f g) → ∀ (I : Cx R) (n : ℤ), cpull f I n = cpull g I n ∧ cpush I f n = cpush I g n) := by
  first | (exact @GlobalTheory.EtC.ZcFun.main) | (exact GlobalTheory.EtC.ZcFun.main) | (intros; apply GlobalTheory.EtC.ZcFun.main  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.MayerVietoris

theorem cpull_add {R : Type} [CommRing R] {K L : Cx R} (f g : K ⟶ L) (I : Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    cpull (f + g) I n x = cpull f I n x + cpull g I n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [cpre_mk, cpre_mk, cpre_mk, ← CohomologyClass.mk_add]
  congr 1; apply Cocycle.ext; simp [zcomp, Cochain.ofHom_add, Cochain.add_comp]

theorem cpull_neg {R : Type} [CommRing R] {K L : Cx R} (f : K ⟶ L) (I : Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    cpull (-f) I n x = -cpull f I n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [cpre_mk, cpre_mk, ← CohomologyClass.mk_neg]
  congr 1; apply Cocycle.ext; simp [zcomp, Cochain.ofHom_neg, Cochain.neg_comp]

theorem cpull_comp {R : Type} [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ) (x : CohomologyClass M I n) :
    cpull (f ≫ g) I n x = cpull f I n (cpull g I n x) := (GlobalTheory.EtC.ZcFun.main R).2.1 f g I n x

theorem cpull_lift {R : Type} [CommRing R] {K L M : Cx R} (a : M ⟶ K) (b : M ⟶ L) (I : Cx R) (n : ℤ)
    (y : CohomologyClass (K ⊞ L) I n) :
    cpull (biprod.lift a b) I n y = cpull a I n (cpull biprod.inl I n y) + cpull b I n (cpull biprod.inr I n y) := by
  rw [biprod.lift_eq, cpull_add, cpull_comp, cpull_comp]

def mvS (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) : ShortComplex (Cx R) :=
  ShortComplex.mk (biprod.lift ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g)))
    (biprod.desc ((chains R).map f) ((chains R).map g)) (by
      let : HasPullback f g := HasLimitsOfShape.has_limit (cospan f g)
      rw [biprod.lift_desc, Preadditive.neg_comp, ← Functor.map_comp, ← Functor.map_comp,
        pullback.condition (C := Spc) (f := f) (g := g)]
      simp)

theorem mvS_exact (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (h : Cover2 R f g) :
    (mvS R f g).ShortExact := by
  obtain ⟨w, hw⟩ := GlobalTheory.T.etaleSpaceChains_mayerVietoris_shortExact R f g h
  exact hw

def mvMap (R : Type) [CommRing R] {U V E U' V' E' : Spc} (f : U ⟶ E) (g : V ⟶ E) (f' : U' ⟶ E') (g' : V' ⟶ E')
    (p : E ⟶ E') (u : U ⟶ U') (v : V ⟶ V') (hu : f ≫ p = u ≫ f') (hv : g ≫ p = v ≫ g') :
    mvS R f g ⟶ mvS R f' g' where
  τ₁ := (chains R).map (pullback.map f g f' g' u v p hu hv)
  τ₂ := biprod.map ((chains R).map u) ((chains R).map v)
  τ₃ := (chains R).map p
  comm₁₂ := by
    apply biprod.hom_ext <;> simp [mvS, ← Functor.map_comp]
  comm₂₃ := by
    apply biprod.hom_ext' <;> simp [mvS, ← Functor.map_comp, hu, hv]

end GlobalTheory.EtC.MayerVietoris
end

theorem GlobalTheory.EtC.mayerVietoris : ∀ (R : Type) [CommRing R] (F : Shv R), ∃ d : ∀ {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g → ∀ n : ℤ, H R (pullback f g) F n →+ H R E F (n + 1), (∀ {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (h : Cover2 R f g) (n : ℤ), (∀ a b, pull R (pullback.fst f g) F n a = pull R (pullback.snd f g) F n b ↔ ∃ x, pull R f F n x = a ∧ pull R g F n x = b) ∧ (∀ c, d f g h n c = 0 ↔ ∃ a b, c = pull R (pullback.fst f g) F n a - pull R (pullback.snd f g) F n b) ∧ ∀ x, (pull R f F (n + 1) x = 0 ∧ pull R g F (n + 1) x = 0) ↔ ∃ c, d f g h n c = x) ∧ ∀ {U V E U' V' E' : Spc} (f : U ⟶ E) (g : V ⟶ E) (f' : U' ⟶ E') (g' : V' ⟶ E') (p : E ⟶ E') (u : U ⟶ U') (v : V ⟶ V') (hu : f ≫ p = u ≫ f') (hv : g ≫ p = v ≫ g') (h : Cover2 R f g) (h' : Cover2 R f' g') (n : ℤ) c, pull R p F (n + 1) (d f' g' h' n c) = d f g h n (pull R (pullback.map f g f' g' u v p hu hv) F n c) := by
  intro R _ F
  obtain ⟨D, hex, hnat⟩ := GlobalTheory.T.hypercohomology_longExact_first_of_injective R (res R F) (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F).2.1
  refine ⟨fun f g h n => D (GlobalTheory.EtC.MayerVietoris.mvS R f g) (GlobalTheory.EtC.MayerVietoris.mvS_exact R f g h) n, ?_, ?_⟩
  · intro U V E f g h n
    obtain ⟨e1, e2, e3⟩ := hex _ (GlobalTheory.EtC.MayerVietoris.mvS_exact R f g h) n
    have bij := fun m => GlobalTheory.EtC.cpull_biprod_bijective R ((chains R).obj U) ((chains R).obj V) (res R F) m

    have hg : ∀ m (x : H R E F m), cpull biprod.inl (res R F) m (cpull (GlobalTheory.EtC.MayerVietoris.mvS R f g).g (res R F) m x) = pull R f F m x ∧
        cpull biprod.inr (res R F) m (cpull (GlobalTheory.EtC.MayerVietoris.mvS R f g).g (res R F) m x) = pull R g F m x := by
      intro m x
      constructor
      · refine (GlobalTheory.EtC.MayerVietoris.cpull_comp (K := (chains R).obj U) (L := (chains R).obj U ⊞ (chains R).obj V) biprod.inl (biprod.desc ((chains R).map f) ((chains R).map g)) _ m x).symm.trans ?_
        rw [biprod.inl_desc]; rfl
      · refine (GlobalTheory.EtC.MayerVietoris.cpull_comp (K := (chains R).obj V) (L := (chains R).obj U ⊞ (chains R).obj V) biprod.inr (biprod.desc ((chains R).map f) ((chains R).map g)) _ m x).symm.trans ?_
        rw [biprod.inr_desc]; rfl
    have hf : ∀ y, cpull (GlobalTheory.EtC.MayerVietoris.mvS R f g).f (res R F) n y =
        pull R (pullback.fst f g) F n (cpull biprod.inl (res R F) n y) - pull R (pullback.snd f g) F n (cpull biprod.inr (res R F) n y) := by
      intro y
      have := GlobalTheory.EtC.MayerVietoris.cpull_lift (K := (chains R).obj U) (L := (chains R).obj V) ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g)) (res R F) n y
      rw [GlobalTheory.EtC.MayerVietoris.cpull_neg] at this
      rw [sub_eq_add_neg]; exact this
    have k1 : ∀ y, (pull R (pullback.fst f g) F n (cpull biprod.inl (res R F) n y) - pull R (pullback.snd f g) F n (cpull biprod.inr (res R F) n y) = 0) ↔ ∃ x, cpull (GlobalTheory.EtC.MayerVietoris.mvS R f g).g (res R F) n x = y :=
      fun y => (Iff.of_eq (congrArg (· = 0) (hf y))).symm.trans (e1 y)
    refine ⟨?_, ?_, ?_⟩
    · intro a b
      obtain ⟨y, hy⟩ := (bij n).2 (a, b)
      simp only [Prod.mk.injEq] at hy
      obtain ⟨rfl, rfl⟩ := hy
      refine sub_eq_zero.symm.trans ((k1 y).trans ⟨?_, ?_⟩)
      · rintro ⟨x, rfl⟩; exact ⟨x, (hg n x).1.symm, (hg n x).2.symm⟩
      · rintro ⟨x, h1, h2⟩
        exact ⟨x, (bij n).1 (Prod.ext ((hg n x).1.trans h1) ((hg n x).2.trans h2))⟩
    · intro c
      show D (GlobalTheory.EtC.MayerVietoris.mvS R f g) (GlobalTheory.EtC.MayerVietoris.mvS_exact R f g h) n c = 0 ↔ _
      refine (e2 c).trans ⟨?_, ?_⟩
      · rintro ⟨y, rfl⟩; exact ⟨_, _, hf y⟩
      · rintro ⟨a, b, rfl⟩
        obtain ⟨y, hy⟩ := (bij n).2 (a, b)
        simp only [Prod.mk.injEq] at hy
        obtain ⟨rfl, rfl⟩ := hy
        exact ⟨y, hf y⟩
    · intro x
      show _ ↔ ∃ c, D (GlobalTheory.EtC.MayerVietoris.mvS R f g) (GlobalTheory.EtC.MayerVietoris.mvS_exact R f g h) n c = x
      refine Iff.trans ?_ (e3 x)
      constructor
      · rintro ⟨h1, h2⟩
        apply (bij (n + 1)).1
        exact Prod.ext (((hg (n + 1) x).1.trans h1).trans (map_zero _).symm) (((hg (n + 1) x).2.trans h2).trans (map_zero _).symm)
      · intro h0
        refine ⟨(hg (n + 1) x).1.symm.trans ?_, (hg (n + 1) x).2.symm.trans ?_⟩ <;> rw [h0] <;> exact map_zero _
  · intro U V E U' V' E' f g f' g' p u v hu hv h h' n c
    exact hnat _ _ _ _ (GlobalTheory.EtC.MayerVietoris.mvMap R f g f' g' p u v hu hv) n c
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_isTensor_etaleSheafComplexPairing : ∀ (R : Type) [CommRing R] (I J : Cx R), ∃ (K : Cx R) (τ : Pair I J K), τ.IsTensor := by
  first | (exact @GlobalTheory.EtC.tensor_exists) | (exact GlobalTheory.EtC.tensor_exists) | (intros; apply GlobalTheory.EtC.tensor_exists  <;> assumption)
end
