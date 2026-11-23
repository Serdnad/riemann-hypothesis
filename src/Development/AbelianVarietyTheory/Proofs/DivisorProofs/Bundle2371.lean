module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle871
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2323
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2339
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle198
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle578
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle602
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle015
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle286

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechKS.LiftDiff

private theorem thickHom_ext {R : Type} [CommRing R] {I : Ideal R}
    {powers : DividedPowers I} {X : Scheme.{0}} {s : X ⟶ Sp R}
    {T T' : Thick powers s} {f g : T ⟶ T'} (h : ∀ b, f.φ b = g.φ b) : f = g := by
  change Thick.Hom T T' at f g
  cases f with
  | mk φ φ₀ comm dp pt =>
    cases g with
    | mk ψ ψ₀ comm' dp' pt' =>
      have e : φ = ψ := AlgHom.ext h
      subst ψ
      have e₀ : φ₀ = ψ₀ := RingHom.ext fun c ↦ by
        obtain ⟨b, rfl⟩ := T.surj c
        rw [comm, comm']
      subst ψ₀
      rfl

theorem spMap_fst_surjective {B : Type} [CommRing B] (f : DualNumber B →+* B) (hf : ∀ c, f c = c.fst) :
    Function.Surjective (spMap f) := by
  intro q
  refine ⟨spMap (algebraMap B (DualNumber B)) q, ?_⟩
  refine PrimeSpectrum.ext (Ideal.ext fun c ↦ ?_)
  change algebraMap B (DualNumber B) (f c) ∈ q.asIdeal ↔ c ∈ q.asIdeal
  rw [hf]
  have hn : c - algebraMap B (DualNumber B) c.fst ∈ q.asIdeal := by
    refine q.isPrime.mem_of_pow_mem 2 ?_
    have : (c - algebraMap B (DualNumber B) c.fst) ^ 2 = 0 := by
      ext <;> simp [pow_two, TrivSqZeroExt.algebraMap_eq_inl]
    rw [this]; exact zero_mem _
  exact ⟨fun hc ↦ by simpa using add_mem hn hc, fun hc ↦ by simpa using sub_mem hc hn⟩

theorem le_preimage_of_red {B : Type} [CommRing B] {X : Scheme.{0}} (f : DualNumber B →+* B)
    (hf : ∀ c, f c = c.fst) {y : Sp (DualNumber B) ⟶ X} {x : Sp B ⟶ X} (e : spMap f ≫ y = x) {U : X.Opens}
    (h : ⊤ ≤ x ⁻¹ᵁ U) : ⊤ ≤ y ⁻¹ᵁ U := by
  intro p _
  obtain ⟨q, rfl⟩ := spMap_fst_surjective f hf p
  have := h (Set.mem_univ q)
  rw [← e] at this
  exact this

theorem ev_eq_of_triv {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (ω : Form s)
    {T₁ T₂ T : Thick (dp0 R) s} (a : T₁ ⟶ T₂) (ψ : T₂ ⟶ T) (φ : T₁ ⟶ T) (h₁ : T₁.J = ⊥) (h₂ : T₂.J = ⊥)
    (e : a ≫ ψ = φ) : ev ω.1 φ = ev ω.1 ψ := by
  rw [← e, ev_comp, show ev ω.1 a = 0 from ω.2 a h₁ h₂, map_zero, zero_add]

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A']
  {i : A.left ⟶ A'.left}

theorem ev_sec_sub_ev_tan (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i)
    (ω : Form (A'.hom ≫ 𝟙 (Sp (DualNumber K)))) (P : GPt A) {v : epsR K ⟶ A} (hv : IsTangent v) :
    ∃ (hc : (spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i) ≫ A'.hom ≫ 𝟙 _ =
        spMap (algebraMap (DualNumber K) ((fibMor h).isMor.obj P.ext).B))
      (ec : spMap ((fibMor h).isMor.obj P.ext).π ≫ spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i =
        ((fibMor h).isMor.obj P.ext).x)
      (ht : (P.trx v ≫ i) ≫ A'.hom ≫ 𝟙 _ = spMap (algebraMap (DualNumber K) ((fibMor h).isMor.obj P.ext).B))
      (et : spMap ((fibMor h).isMor.obj P.ext).π ≫ P.trx v ≫ i = ((fibMor h).isMor.obj P.ext).x),
      ev ((fibMor h).isMor.pullForm ω).1 P.sec - ev ((fibMor h).isMor.pullForm ω).1 (P.tan hv) =
        ev ω.1 (idLift _ _ hc ec) - ev ω.1 (idLift _ _ ht et) := by
  let g : DualNumber K →+* P.B := (algebraMap K P.B).comp (TrivSqZeroExt.fstHom K K K).toRingHom
  have w : (P.x ≫ i) ≫ A'.hom ≫ 𝟙 _ = spMap g := ((fibMor h).isMor.obj P.triv).w
  have hc : (spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i) ≫ A'.hom ≫ 𝟙 _ =
      spMap (algebraMap (DualNumber K) ((fibMor h).isMor.obj P.ext).B) := by
    rw [Category.assoc, w]
    exact (Cris.spMap_comp g (algebraMap P.B (DualNumber P.B))).symm.trans (congrArg spMap (RingHom.ext fun _ ↦ rfl))
  have ec : spMap ((fibMor h).isMor.obj P.ext).π ≫ spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i =
      ((fibMor h).isMor.obj P.ext).x := by
    let π' : DualNumber P.B →+* P.B := TrivSqZeroExt.fstHom K P.B P.B
    have e : π'.comp (algebraMap P.B (DualNumber P.B)) = RingHom.id _ := RingHom.ext fun _ ↦ rfl
    show spMap π' ≫ spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i = P.x ≫ i
    rw [← Category.assoc, ← Cris.spMap_comp, e, Cris.spMap_id, Category.id_comp]
  have ht : (P.trx v ≫ i) ≫ A'.hom ≫ 𝟙 _ =
      spMap (algebraMap (DualNumber K) ((fibMor h).isMor.obj P.ext).B) :=
    ((fibMor h).isMor.obj (P.tr v).triv).w
  have et : spMap ((fibMor h).isMor.obj P.ext).π ≫ P.trx v ≫ i = ((fibMor h).isMor.obj P.ext).x :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ i) ((P.isTransl_trx v).red hv))
  refine ⟨hc, ec, ht, et, ?_⟩
  refine congrArg₂ (· - ·) (ev_eq_of_triv ω ?a (idLift _ _ hc ec) ((fibMor h).isMor.functor.map P.sec) rfl rfl ?ea)
    (ev_eq_of_triv ω ?b (idLift _ _ ht et) ((fibMor h).isMor.functor.map (P.tan hv)) rfl rfl ?eb)
  case a =>
    exact { φ := { algebraMap P.B (DualNumber P.B) with commutes' := fun _ ↦ rfl }
            φ₀ := algebraMap P.B (DualNumber P.B)
            comm := fun _ ↦ rfl
            dp := isDPMorphism_of_eq_bot _ rfl _ _
            pt := rfl }
  case b =>
    exact { φ := { RingHom.id (DualNumber P.B) with commutes' := fun _ ↦ rfl }
            φ₀ := RingHom.id _
            comm := fun _ ↦ rfl
            dp := isDPMorphism_of_eq_bot _ rfl _ _
            pt := by
              show spMap (RingHom.id (DualNumber P.B)) ≫ P.trx v ≫ i = P.trx v ≫ i
              rw [Cris.spMap_id, Category.id_comp] }
  case ea => exact thickHom_ext fun _ ↦ rfl
  case eb => exact thickHom_ext fun _ ↦ rfl

theorem liftVal_sub_snd : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i), IsAbelianScheme A → ∀ (ω : Form (A'.hom ≫ 𝟙 (Sp (DualNumber K)))) (U : A'.left.Opens), IsAffineOpen U → ∀ (P : GPt A), P.In (i ⁻¹ᵁ U) → ∀ (y₁ y₂ : Sp (DualNumber P.B) ⟶ A'.left) (h₁ : IsLift i P y₁) (h₂ : IsLift i P y₂) (n : ℕ) (u : Fin n → (epsR K ⟶ A)) (c : Fin n → P.B), (∀ a, IsTangent (u a)) → (∀ f : Γ(A'.left, U), valR y₁ U f - valR y₂ U f = (TrivSqZeroExt.inr (∑ a, c a * (valR (P.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom f)).snd) : DualNumber P.B)) → (liftVal h ω.1 h₁ - liftVal h ω.1 h₂).snd = -∑ a, c a * algebraMap K P.B (tanVal (u a) ((fibMor h).isMor.pullForm ω)) := by
  intro K _ A _ A' _ i h hA ω U hU P hP y₁ y₂ h₁ h₂ n u c hu hdiff
  obtain ⟨m, r, t, H⟩ := GlobalTheory.T.exists_crystallineForm_lift_difference_eq_sum (DualNumber K) A'.left (A'.hom ≫ 𝟙 _) ω U hU
  have hPU : ⊤ ≤ (P.x ≫ i) ⁻¹ᵁ U := hP
  have red : ∀ c : DualNumber P.B, (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) c = c.fst :=
    fun _ ↦ rfl
  have hU₁ : ⊤ ≤ y₁ ⁻¹ᵁ U := le_preimage_of_red _ red h₁.2 hPU
  have hU₂ : ⊤ ≤ y₂ ⁻¹ᵁ U := le_preimage_of_red _ red h₂.2 hPU
  have k1 := H ((liftMor (epsDP K) h).isMor.obj P.eps) (SqExt.ofModule K P.B P.B).sq rfl y₁ y₂ h₁.1 h₂.1
    h₁.2 h₂.2 hU₁ hU₂
  have e1 : liftVal h ω.1 h₁ - liftVal h ω.1 h₂ =
      -∑ k, valR y₂ U (r k) * (valR y₁ U (t k) - valR y₂ U (t k)) := by
    rw [← neg_sub]; exact congrArg Neg.neg k1
  have f2 : ∀ f, (valR y₂ U f).fst = valR P.x (i ⁻¹ᵁ U) ((i.app U).hom f) := fun f ↦ by
    rw [← GlobalTheory.Points.valR_comp, ← h₂.2, GlobalTheory.Points.valR_spMap_comp _ _ _ hU₂]; exact (red _).symm
  have step2 : ∀ a, ∑ k, valR P.x (i ⁻¹ᵁ U) ((i.app U).hom (r k)) *
      (valR (P.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom (t k))).snd =
        algebraMap K P.B (tanVal (u a) ((fibMor h).isMor.pullForm ω)) := by
    intro a
    have X := ev_sec_sub_ev_tan (K := K) (A := A) (A' := A') (i := i) h ω P (hu a)
    obtain ⟨hc, ec, ht, et, E⟩ := X
    have F := GlobalTheory.T.invariantForm_abelianVariety_translate_value K A hA (u a) (hu a) ((fibMor h).isMor.pullForm ω) P
    have hUt : ⊤ ≤ (P.trx (u a) ≫ i) ⁻¹ᵁ U := fun p hp ↦ hP.tr (hu a) hp
    have hUc : ⊤ ≤ (spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i) ⁻¹ᵁ U :=
      fun _ _ ↦ hPU (Set.mem_univ _)
    have k2 := H ((fibMor h).isMor.obj P.ext) (SqExt.ofModule K P.B P.B).sq rfl _ _ ht hc et ec hUt hUc
    have F3 : (∑ k, valR (spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i) U (r k) *
        (valR (P.trx (u a) ≫ i) U (t k) - valR (spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i) U (t k))) =
        TrivSqZeroExt.inr (algebraMap K P.B (tanVal (u a) ((fibMor h).isMor.pullForm ω))) := k2.symm.trans (E.symm.trans F)
    have F' := congrArg (fun z : DualNumber P.B ↦ z.snd) F3
    simp only [TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_sum] at F'
    rw [← F']
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [GlobalTheory.Points.valR_spMap_comp _ _ _ hPU, GlobalTheory.Points.valR_spMap_comp _ _ _ hPU, GlobalTheory.Points.valR_comp,
      GlobalTheory.Points.valR_comp, GlobalTheory.Points.valR_comp]
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  have D : ∀ k, valR y₁ U (t k) - valR y₂ U (t k) = TrivSqZeroExt.inr (∑ a, c a *
      (valR (P.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom (t k))).snd) := fun k ↦ hdiff (t k)
  refine (congrArg (fun z : DualNumber P.B ↦ z.snd) e1).trans ?_
  have G := Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) ↦ congrArg (valR y₂ U (r k) * ·) (D k)
  refine (congrArg (fun z : DualNumber P.B ↦ (-z).snd) G).trans ?_
  simp only [TrivSqZeroExt.snd_neg, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inr,
    TrivSqZeroExt.snd_inr, f2, smul_eq_mul, MulOpposite.op_zero,
    zero_smul, add_zero, neg_inj]
  simp only [← step2, Finset.mul_sum]
  clear H k1 e1 hdiff D G step2 f2 red
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  ring

end GlobalTheory.CechKS.LiftDiff
end
end

section

noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.BasicNotions.TH GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.FockBridge

section Ind

variable {T P : Type} [AddCommGroup T] [Module ℂ T] [AddCommGroup P] [Module ℂ P]

def Keeps (q : T →ₗ[ℂ] P) (L : Module.End ℂ T) : Prop := ∀ t, q t = 0 → q (L t) = 0

def indOp (q : T →ₗ[ℂ] P) (L : Module.End ℂ T) : Module.End ℂ P :=
  if h : Function.Surjective q ∧ Keeps q L then
    (q.quotKerEquivOfSurjective h.1).toLinearMap ∘ₗ
      ((LinearMap.ker q).mapQ (LinearMap.ker q) L fun t ht => LinearMap.mem_ker.2 (h.2 t (LinearMap.mem_ker.1 ht))) ∘ₗ
        (q.quotKerEquivOfSurjective h.1).symm.toLinearMap
  else 0

theorem indOp_apply {q : T →ₗ[ℂ] P} {L : Module.End ℂ T} (hq : Function.Surjective q) (hL : Keeps q L) (t : T) :
    indOp q L (q t) = q (L t) := by
  have e : (q.quotKerEquivOfSurjective hq).symm (q t) = Submodule.Quotient.mk t :=
    (LinearEquiv.symm_apply_eq _).2 (by simp)
  rw [indOp, dite_eq_left ⟨hq, hL⟩, LinearMap.comp_apply, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe]
  rw [e]
  rfl

theorem indOp_eq {q : T →ₗ[ℂ] P} {L : Module.End ℂ T} (hq : Function.Surjective q) (hL : Keeps q L)
    (M : Module.End ℂ P) (h : ∀ t, M (q t) = q (L t)) : indOp q L = M := by
  ext x
  obtain ⟨t, rfl⟩ := hq x
  rw [indOp_apply hq hL, h]

theorem keeps_mul {q : T →ₗ[ℂ] P} {L L' : Module.End ℂ T} (h : Keeps q L) (h' : Keeps q L') : Keeps q (L * L') :=
  fun t ht => h _ (h' t ht)

theorem keeps_sub {q : T →ₗ[ℂ] P} {L L' : Module.End ℂ T} (h : Keeps q L) (h' : Keeps q L') : Keeps q (L - L') :=
  fun t ht => by simp [h t ht, h' t ht]

theorem indOp_mul {q : T →ₗ[ℂ] P} {L L' : Module.End ℂ T} (hq : Function.Surjective q) (h : Keeps q L)
    (h' : Keeps q L') : indOp q (L * L') = indOp q L * indOp q L' :=
  indOp_eq hq (keeps_mul h h') _ fun t => by
    rw [Module.End.mul_apply, indOp_apply hq h', indOp_apply hq h]; rfl

theorem indOp_sub {q : T →ₗ[ℂ] P} {L L' : Module.End ℂ T} (hq : Function.Surjective q) (h : Keeps q L)
    (h' : Keeps q L') : indOp q (L - L') = indOp q L - indOp q L' :=
  indOp_eq hq (keeps_sub h h') _ fun t => by
    rw [LinearMap.sub_apply, indOp_apply hq h', indOp_apply hq h, LinearMap.sub_apply, map_sub]

end Ind

section Place

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

theorem atPl_mul (w : ι) (L L' : Module.End ℂ (V w)) : atPl w (L * L') = atPl w L * atPl w L' := by
  unfold atPl
  rw [← PiTensorProduct.map_mul]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp
  · simp only [Function.update_of_ne h]; first | rfl | simp [Module.End.mul_eq_comp]

theorem atPl_comm {w w' : ι} (hw : w ≠ w') (L : Module.End ℂ (V w)) (L' : Module.End ℂ (V w')) :
    atPl w L * atPl w' L' = atPl w' L' * atPl w L := by
  unfold atPl
  rw [← PiTensorProduct.map_mul, ← PiTensorProduct.map_mul]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp only [Function.update_self, Function.update_of_ne hw]; first | rfl | simp [Module.End.mul_eq_comp]
  · by_cases h' : i = w'
    · subst h'; simp only [Function.update_self, Function.update_of_ne h]; first | rfl | simp [Module.End.mul_eq_comp]
    · simp only [Function.update_of_ne h, Function.update_of_ne h']

end Place

section Fock

variable {F : Type} [Field F] [NumberField F] {P : Type} [AddCommGroup P] [Module ℂ P] {p₁ q₁ r s : ℕ}

def fockOp (q : Tens F p₁ q₁ r s →ₗ[ℂ] P) (w : InfinitePlace F) : Mat r s →ₗ[ℂ] Module.End ℂ P :=
  if h : Function.Surjective q ∧ ∀ Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y)) then
    { toFun := fun Y => indOp q (atPl w (fockAct2 p₁ q₁ r s Y))
      map_add' := fun Y Z => by
        apply indOp_eq h.1 (h.2 _)
        intro t
        rw [LinearMap.add_apply, indOp_apply h.1 (h.2 Y), indOp_apply h.1 (h.2 Z), map_add (f := _), Main.atPl_add,
          LinearMap.add_apply, map_add]
      map_smul' := fun c Y => by
        apply indOp_eq h.1 (h.2 _)
        intro t
        rw [RingHom.id_apply, LinearMap.smul_apply, indOp_apply h.1 (h.2 Y), map_smul, Main.atPl_smul,
          LinearMap.smul_apply, map_smul] }
  else 0

theorem fockOp_eq {q : Tens F p₁ q₁ r s →ₗ[ℂ] P} {w : InfinitePlace F} (hq : Function.Surjective q)
    (hK : ∀ Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y))) (Y : Mat r s) :
    fockOp q w Y = indOp q (atPl w (fockAct2 p₁ q₁ r s Y)) := by
  rw [fockOp, dite_eq_left ⟨hq, hK⟩]
  rfl

theorem fockOp_apply {q : Tens F p₁ q₁ r s →ₗ[ℂ] P} {w : InfinitePlace F} (hq : Function.Surjective q)
    (hK : ∀ Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y))) (Y : Mat r s) (t : Tens F p₁ q₁ r s) :
    fockOp q w Y (q t) = q (atPl w (fockAct2 p₁ q₁ r s Y) t) := by
  rw [fockOp_eq hq hK, indOp_apply hq (hK Y)]


variable (r s) in
def negT : Mat r s →ₗ[ℂ] Mat r s where
  toFun Y := -Yᵀ
  map_add' Y Z := by rw [Matrix.transpose_add, neg_add]
  map_smul' c Y := by rw [Matrix.transpose_smul, RingHom.id_apply, smul_neg]

theorem negT_apply (Y : Mat r s) : negT r s Y = -Yᵀ := rfl

def twAct (ε : Bool) (q : Tens F p₁ q₁ r s →ₗ[ℂ] P) (w : InfinitePlace F) : Mat r s →ₗ[ℂ] Module.End ℂ P :=
  if ε then fockOp q w else fockOp q w ∘ₗ negT r s

end Fock

section Frames

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def IsFrames (B : Base F E) {n d : ℕ} (Y : Spc F E n) (W : Spc F E d) {p₁ q₁ r s : ℕ}
    (A : InfinitePlace F → Matrix (Fin n) (Ix p₁ q₁) ℂ) (C : InfinitePlace F → Matrix (Fin d) (Ix r s) ℂ) : Prop :=
  Framed B.emb (incM F Y.J) (incM F W.J) 1 Complex.I A C ∧ (∀ w, Y.θ w * A w = A w * Jm p₁ q₁) ∧
    ∀ w, W.θ w * C w = C w * Jm r s

def IsFockData (B : Base F E) {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) {p₁ q₁ r s : ℕ}
    (A : InfinitePlace F → Matrix (Fin n) (Ix p₁ q₁) ℂ) (C : InfinitePlace F → Matrix (Fin d) (Ix r s) ℂ)
    (Φ : Tens F p₁ q₁ r s →ₗ[ℂ] SInf F (Fin n × Fin d)) : Prop :=
  IsFrames B Y W A C ∧ IsFockMap B.ψ B.emb M.co A C Φ

def IsAdaptedFrame (B : Base F E) {d d₁ : ℕ} (H' : Plane E d d₁) {r s : ℕ}
    (C : InfinitePlace F → Matrix (Fin d) (Ix r s) ℂ) (r₀ : Fin r) (s₀ : Fin s) : Prop :=
  ∀ w, (∃ c : ℂ, c ≠ 0 ∧ ∀ i, (B.emb w).1 (H'.x i) = c * (C w i (.inl r₀) + C w i (.inr s₀))) ∧
    (∃ c₁ c₂ : ℂ, ∀ i, (B.emb w).1 (H'.y i) = c₁ * C w i (.inl r₀) + c₂ * C w i (.inr s₀)) ∧
    ∀ a, a ≠ .inl r₀ → a ≠ .inr s₀ → ∃ z : Fin d₁ → ℂ, ∀ i, C w i a = (H'.ι.map (B.emb w).1 *ᵥ z) i

end Frames

section Laws

variable {F : Type} [Field F] [NumberField F] {P : Type} [AddCommGroup P] [Module ℂ P] {p₁ q₁ r s : ℕ}

theorem atPl_sub {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (w : ι) (L L' : Module.End ℂ (V w)) : atPl w (L - L') = atPl w L - atPl w L' := by
  simp only [Main.atPl_eq, MultilinearMap.map_update_sub]

theorem fockOp_lie {q : Tens F p₁ q₁ r s →ₗ[ℂ] P} {w : InfinitePlace F} (hq : Function.Surjective q)
    (hK : ∀ Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y))) (Y Z : Mat r s) :
    fockOp q w (Y * Z - Z * Y) = fockOp q w Y * fockOp q w Z - fockOp q w Z * fockOp q w Y := by
  rw [fockOp_eq hq hK, fockOp_eq hq hK, fockOp_eq hq hK, (GlobalTheory.FockPair.pair_lie_commute p₁ q₁ r s).2.1 Y Z,
    atPl_sub, atPl_mul, atPl_mul, indOp_sub hq (keeps_mul (hK Y) (hK Z)) (keeps_mul (hK Z) (hK Y)),
    indOp_mul hq (hK Y) (hK Z), indOp_mul hq (hK Z) (hK Y)]

theorem fockOp_comm {q : Tens F p₁ q₁ r s →ₗ[ℂ] P} (hq : Function.Surjective q)
    (hK : ∀ w Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y))) {w w' : InfinitePlace F} (hw : w ≠ w') (Y Z : Mat r s) :
    fockOp q w Y * fockOp q w' Z = fockOp q w' Z * fockOp q w Y := by
  rw [fockOp_eq hq (hK w), fockOp_eq hq (hK w'), ← indOp_mul hq (hK w Y) (hK w' Z),
    ← indOp_mul hq (hK w' Z) (hK w Y), atPl_comm hw]

theorem negT_negT (Y : Mat r s) : negT r s (negT r s Y) = Y := by
  simp [negT_apply]

theorem negT_lie (Y Z : Mat r s) : negT r s (Y * Z - Z * Y) = negT r s Y * negT r s Z - negT r s Z * negT r s Y := by
  simp only [negT_apply, Matrix.transpose_sub, Matrix.transpose_mul, neg_mul_neg, neg_sub]

theorem sameBlock_symm {a b : Ix r s} (h : sameBlock a b) : sameBlock b a := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]

theorem isKC_negT {Y : Mat r s} (hY : IsKC Y) : IsKC (negT r s Y) := fun a b hab => by
  rw [negT_apply, Matrix.neg_apply, Matrix.transpose_apply, hY b a fun h => hab (sameBlock_symm h), neg_zero]

theorem negT_Eab (a b : Ix r s) : negT r s (Eab a b) = -Eab b a := by
  rw [negT_apply, Eab, Eab, Matrix.transpose_single]

theorem twAct_lie {q : Tens F p₁ q₁ r s →ₗ[ℂ] P} {w : InfinitePlace F} (hq : Function.Surjective q)
    (hK : ∀ Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y))) (ε : Bool) (Y Z : Mat r s) :
    twAct ε q w (Y * Z - Z * Y) = twAct ε q w Y * twAct ε q w Z - twAct ε q w Z * twAct ε q w Y := by
  cases ε
  · simp only [twAct, Bool.false_eq_true, if_false, LinearMap.comp_apply]
    rw [negT_lie, fockOp_lie hq hK]
  · simp only [twAct, if_true]
    exact fockOp_lie hq hK Y Z

theorem twAct_comm {q : Tens F p₁ q₁ r s →ₗ[ℂ] P} (hq : Function.Surjective q)
    (hK : ∀ w Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y))) (ε : Bool) {w w' : InfinitePlace F} (hw : w ≠ w')
    (Y Z : Mat r s) : twAct ε q w Y * twAct ε q w' Z = twAct ε q w' Z * twAct ε q w Y := by
  cases ε
  · simp only [twAct, Bool.false_eq_true, if_false, LinearMap.comp_apply]
    exact fockOp_comm hq hK hw _ _
  · simp only [twAct, if_true]
    exact fockOp_comm hq hK hw _ _

end Laws

end GlobalTheory.FockBridge
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

theorem _root_.GlobalTheory.T.exists_tensor_section_nonvanishing_of_baseChange : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → ∀ (L M : LB Y), L.IsLB → M.IsLB → ∀ x : X, (∃ s : (tens (L.pull π) (M.pull π)).Sec, x ∈ nonzeroLocus s) → ∃ s : (tens L M).Sec, π x ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.FieldDescent.exists_sec_tens_of_baseChange | exact GlobalTheory.FieldDescent.exists_sec_tens_of_baseChange | (intros; apply GlobalTheory.FieldDescent.exists_sec_tens_of_baseChange <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne

open GlobalTheory.VecInv Formalism.IndefR.Lev

theorem mu_detAt_eq_levChi {D : D7} {T0 : Type} {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) (i : Fin D.R.m) (t : T0)
    (hQ : L.Q t = ∅) {P : Finset (Pl D.host.E)} {e : AE D} (hee : e * e = e)
    (hP : ∀ PP, PP ∈ P ↔ PP ∈ L.Pg ∨ PP ∈ L.Q t) (he : IsIdemSum e P) {κ : GA D (Vc D i)}
    (hκ : IsLevelLift (Vc D i) (L.βV i) (L.datVt i t) 1 κ) :
    ((L.mu t ((i : ℕ) + 1) (detAt e hee _ κ) : Circle) : ℂ) = levChi _ (L.βV i) (flagL (L.datVt i t)) κ := by
  have sV : finE (Vc D i) κ ∈ St (L.βV i) := parLev_St hκ.2.1
  have tg : ∀ PP ∈ L.Pg, redFn (L.βV i) PP (finE (Vc D i) κ) ∈ blockTri (blkOf D.R.r D.R.t) := fun PP h =>
    parLev_g hκ.2.1 h
  have one : ∀ PP ∈ L.Pg, upperLeftBlock (r_le_V i) (redFn (L.βV i) PP (finE (Vc D i) κ)) = 1 := fun PP h =>
    congrFun hκ.2.2 ⟨PP, h⟩
  obtain ⟨aV, haV, hrV⟩ := exists_det_int sV
  have mV := (mu_val hL t i hP he (detAt e hee _ κ) _ aV _ (isDetAt_detAt e hee _ κ) haV fun PP _ => hrV PP).1
  rw [levChi_flag_V i t tg, mV, hQ, Finset.prod_empty, Finset.prod_empty, one_mul]
  refine congrArg (fun z : ℂˣ => ((z * 1 : ℂˣ) : ℂ)) (Finset.prod_congr rfl fun PP h => ?_)
  rw [(GlobalTheory.T.det_twoDiagBlocks_properties _ _ _ 0 (r_le_V i) _).1 (blockTri_blkOf_le _ _ (tg PP h)), one PP h, map_one, one_mul]

theorem smul_of_splitFac {D : D7} {X ι : Type} {u v : X → ℂ} {c : ι → ℂ} {μ η : (AE D)ˣ →* Circle} {x y : (AE D)ˣ} {z : ℂ}
    (h : (∏ i ∈ (∅ : Finset ι), c i) • u = ((splitFacO μ (μ * η⁻¹) x y : Circle) : ℂ) • v) (hy : y = 1) (hη : η x = 1)
    (hz : ((μ x : Circle) : ℂ) = z) : u = z⁻¹ • v := by
  rwa [Finset.prod_empty, one_smul, splitFacO, MonoidHom.mul_apply, MonoidHom.inv_apply, hη, inv_one, mul_one, hy, map_one,
    mul_one, Circle.coe_inv, hz] at h

end GlobalTheory.GalOne
end
