module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.TotallySplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle265
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle439
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.TraceFormDualOneTraceFormDual
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle050
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1793
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle048
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.UnitaryClasses

theorem gramOn_one_map_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (V : Submodule E (Fin n → E)) (τ : E →+* ℂ) :
    (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).map τ =
      (Matrix.of fun k i => τ ((Module.finBasis E V i).1 k) :
        Matrix (Fin n) (Fin (Module.finrank E V)) ℂ)ᴴ *
      (Matrix.of fun k i => τ ((Module.finBasis E V i).1 k)) := by
  ext i j
  simp [gramOn, hform, Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply,
    IsCMField.complexEmbedding_complexConj, mul_ite, ite_mul, Finset.sum_ite_eq]

theorem gramOn_basis_mulVec_injective {E : Type} [Field E] {n : ℕ}
    (V : Submodule E (Fin n → E)) (τ : E →+* ℂ) :
    Function.Injective (Matrix.of fun k i => τ ((Module.finBasis E V i).1 k) :
        Matrix (Fin n) (Fin (Module.finrank E V)) ℂ).mulVec := by
  first
  | exact @_root_.GlobalTheory.BasisLeftInverse.injective_mulVec_map_basis
  | exact _root_.GlobalTheory.BasisLeftInverse.injective_mulVec_map_basis
  | (apply _root_.GlobalTheory.BasisLeftInverse.injective_mulVec_map_basis <;> assumption)
  | (intros; apply _root_.GlobalTheory.BasisLeftInverse.injective_mulVec_map_basis <;> assumption)
  | (intros; apply @_root_.GlobalTheory.BasisLeftInverse.injective_mulVec_map_basis <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.BasisLeftInverse.injective_mulVec_map_basis ..)

theorem gramOn_one_det_totallyPositive : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (V : Submodule E (Fin n → E)), (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).det ≠ 0 ∧ ∀ τ : E →+* ℂ, ∃ r : ℝ, 0 < r ∧ τ (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).det = r := by
  intro E _ _ _ n V
  have key : ∀ τ : E →+* ℂ, 0 < τ (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).det := by
    intro τ
    rw [RingHom.map_det]
    have : τ.mapMatrix (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V) =
        (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).map τ := rfl
    rw [this, gramOn_one_map_eq]
    exact (Matrix.PosDef.conjTranspose_mul_self _ (gramOn_basis_mulVec_injective V τ)).det_pos
  refine ⟨fun h0 => ?_, fun τ => ?_⟩
  · have τ0 := (Classical.arbitrary (NumberField.InfinitePlace E)).embedding
    have := key τ0
    rw [h0, map_zero] at this
    exact lt_irrefl _ this
  · have h := Complex.lt_def.mp (key τ)
    refine ⟨(τ (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).det).re, h.1, ?_⟩
    apply Complex.ext
    · simp
    · simpa using h.2.symm

end GlobalTheory.UnitaryClasses
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.SchrFixNbhd

open Matrix

def fixTrans {M : Type} [AddCommGroup M] (g : M → ℂ) : AddSubgroup M where
  carrier := {u | ∀ x, g (x + u) = g x}
  zero_mem' := fun x => by rw [add_zero]
  add_mem' := fun {a b} ha hb x => by rw [← add_assoc, hb, ha]
  neg_mem' := fun {a} ha x => by
    have := ha (x + -a)
    rw [neg_add_cancel_right] at this
    exact this.symm

theorem isOpen_fixTrans {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] {g : M → ℂ}
    (h1 : IsLocallyConstant g) (h2 : HasCompactSupport g) : IsOpen (fixTrans g : Set M) := by
  have h : ∀ᶠ u in nhds (0 : M), ∀ x ∈ tsupport g, g (x + u) = g x ∧ g (x - u) = g x := by
    apply h2.isCompact.eventually_forall_of_forall_eventually
    intro x _
    have a1 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 + z.1 by fun_prop)).eventually_eq (0, x)
    have a2 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 - z.1 by fun_prop)).eventually_eq (0, x)
    have a3 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 by fun_prop)).eventually_eq (0, x)
    filter_upwards [a1, a2, a3] with z b1 b2 b3
    simp only [Function.comp, add_zero, sub_zero] at b1 b2 b3
    exact ⟨b1.trans b3.symm, b2.trans b3.symm⟩
  have key : ∀ᶠ u in nhds (0 : M), ∀ x, g (x + u) = g x := by
    filter_upwards [h] with u hu x
    by_cases hx : x ∈ tsupport g
    · exact (hu x hx).1
    · by_cases hx' : x + u ∈ tsupport g
      · have := (hu _ hx').2
        rw [add_sub_cancel_right] at this
        exact this.symm
      · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']
  exact AddSubgroup.isOpen_of_mem_nhds _ key

theorem exists_dot_ker {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    (χ : AddChar K ℂ) (hχ : IsLocallyConstant χ) (κ : Type) [Fintype κ] [NonarchimedeanAddGroup (κ → K)]
    (C : Set (κ → K)) (hC : IsCompact C) :
    ∃ H : OpenAddSubgroup (κ → K), ∀ z ∈ C, ∀ a ∈ H, ∀ b ∈ H, χ (z ⬝ᵥ b + a ⬝ᵥ b) = 1 := by
  let V : Set K := {t | χ t = 1}
  have hV : IsOpen V := hχ.isOpen_fiber 1
  have h0 : (0 : K) ∈ V := AddChar.map_zero_eq_one χ
  have hadd : ∀ s t, s ∈ V → t ∈ V → s + t ∈ V := fun s t hs ht => by
    show χ (s + t) = 1
    rw [AddChar.map_add_eq_mul, show χ s = 1 from hs, show χ t = 1 from ht, one_mul]
  have hc1 : Continuous fun p : (κ → K) × (κ → K) => p.2 ⬝ᵥ p.1 := continuous_snd.dotProduct continuous_fst
  have hc2 : Continuous fun p : (κ → K) × (κ → K) => p.1 ⬝ᵥ p.2 := continuous_fst.dotProduct continuous_snd
  have N0 : ∀ᶠ b in nhds (0 : κ → K), ∀ z ∈ C, z ⬝ᵥ b ∈ V := by
    refine hC.eventually_forall_of_forall_eventually fun z _ => ?_
    exact hc1.tendsto ((0 : κ → K), z) (hV.mem_nhds (by simpa using h0))
  have N1 : {p : (κ → K) × (κ → K) | p.1 ⬝ᵥ p.2 ∈ V} ∈ nhds ((0 : κ → K), (0 : κ → K)) :=
    hc2.tendsto ((0 : κ → K), (0 : κ → K)) (hV.mem_nhds (by simpa using h0))
  rw [nhds_prod_eq, Filter.mem_prod_iff] at N1
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := N1
  obtain ⟨H, hH⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ (Filter.inter_mem (Filter.inter_mem N0 ht₁) ht₂)
  refine ⟨H, fun z hz a ha b hb => hadd _ _ ((hH hb).1.1 z hz) ?_⟩
  exact hsub (Set.mk_mem_prod (hH ha).1.2 (hH hb).2)

variable {F : Type} [Field F] [NumberField F]

theorem adeleJoin_zero_apply {κ : Type} (y : κ → FiniteAdeleRing (𝓞 F) F) (i : κ) :
    GlobalTheory.WeilCont.adeleJoin F 0 y i = ((0 : InfiniteAdeleRing F), y i) := by
  refine Prod.ext ?_ rfl
  show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm 0 = 0
  exact map_zero _

theorem dotProduct_adeleJoin_zero {κ : Type} [Fintype κ] (v : κ → AdeleRing (𝓞 F) F)
    (y : κ → FiniteAdeleRing (𝓞 F) F) :
    v ⬝ᵥ GlobalTheory.WeilCont.adeleJoin F 0 y = ((0 : InfiniteAdeleRing F), (fun i => (v i).2) ⬝ᵥ y) := by
  let q1 : AdeleRing (𝓞 F) F →+* InfiniteAdeleRing F := RingHom.fst _ _
  let q2 : AdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd _ _
  have e1 : ∀ s : AdeleRing (𝓞 F) F, s.1 = q1 s := fun _ => rfl
  have e2 : ∀ s : AdeleRing (𝓞 F) F, s.2 = q2 s := fun _ => rfl
  refine Prod.ext ?_ ?_
  · set_option synthInstance.maxHeartbeats 100000 in
    rw [e1, dotProduct, map_sum]
    change ∑ i, q1 (v i * GlobalTheory.WeilCont.adeleJoin F 0 y i) = 0
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_mul, adeleJoin_zero_apply]
    exact mul_zero _
  · set_option synthInstance.maxHeartbeats 100000 in
    rw [e2, dotProduct, map_sum]
    change ∑ i, q2 (v i * GlobalTheory.WeilCont.adeleJoin F 0 y i) = ∑ i, (v i).2 * y i
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, adeleJoin_zero_apply]
    rfl

theorem exists_fix_pure [Invertible (2 : AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : Continuous ψ)
    (κ : Type) [Fintype κ] (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F),
      IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ x ∈ L₁, ∀ y ∈ L₂, GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilCont.adeleJoin F 0 x, GlobalTheory.WeilCont.adeleJoin F 0 y)
        (GlobalTheory.WeilM.pureA F f g) = GlobalTheory.WeilM.pureA F f g := by
  haveI := GlobalTheory.HeisSchA.nonarch_finiteAdeleRing (F := F)
  haveI : NonarchimedeanAddGroup (κ → FiniteAdeleRing (𝓞 F) F) := GlobalTheory.HeisSchA.nonarch_pi
  obtain ⟨H, hH⟩ := exists_dot_ker (GlobalTheory.HeisSchA.finChar ψ) (GlobalTheory.HeisSchA.finChar_isLocallyConstant ψ hψ) κ
    (tsupport g) hg.2.isCompact
  let c : FiniteAdeleRing (𝓞 F) F := (⅟(2 : AdeleRing (𝓞 F) F)).2
  refine ⟨fixTrans g ⊓ (H : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)).comap
    (DistribSMul.toAddMonoidHom (κ → FiniteAdeleRing (𝓞 F) F) c), H, ?_, H.isOpen, ?_⟩
  · rw [AddSubgroup.coe_inf]
    exact (isOpen_fixTrans hg.1 hg.2).inter (H.isOpen.preimage (continuous_const_smul c))
  rintro x ⟨hx1, hx2⟩ y hy
  funext z
  have hf : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((z + GlobalTheory.WeilCont.adeleJoin F 0 x) i).1) =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1 := by
    funext i
    rw [Pi.add_apply, adeleJoin_zero_apply]
    exact congrArg _ (add_zero (z i).1)
  have hgz : (fun i => ((z + GlobalTheory.WeilCont.adeleJoin F 0 x) i).2) = (fun i => (z i).2) + x := by
    funext i
    rw [Pi.add_apply, adeleJoin_zero_apply]
    rfl
  have hz : GlobalTheory.WeilM.pureA F f g (z + GlobalTheory.WeilCont.adeleJoin F 0 x) = GlobalTheory.WeilM.pureA F f g z := by
    simp only [GlobalTheory.WeilM.pureA]
    rw [hf, hgz, hx1]
  simp only [GlobalTheory.WeilM.schr]
  rw [hz]
  by_cases hg0 : g (fun i => (z i).2) = 0
  · simp only [GlobalTheory.WeilM.pureA, hg0, mul_zero]
  have hzc : (fun i => (z i).2) ∈ tsupport g := subset_tsupport _ hg0
  have harg : z ⬝ᵥ GlobalTheory.WeilCont.adeleJoin F 0 y + ⅟(2 : AdeleRing (𝓞 F) F) *
      (GlobalTheory.WeilCont.adeleJoin F 0 x ⬝ᵥ GlobalTheory.WeilCont.adeleJoin F 0 y) =
      ((0 : InfiniteAdeleRing F), (fun i => (z i).2) ⬝ᵥ y + (c • x) ⬝ᵥ y) := by
    rw [dotProduct_adeleJoin_zero, dotProduct_adeleJoin_zero, smul_dotProduct]
    refine Prod.ext ?_ ?_
    · show (0 : InfiniteAdeleRing F) + (⅟(2 : AdeleRing (𝓞 F) F)).1 * 0 = 0
      rw [mul_zero, add_zero]
    · show (fun i => (z i).2) ⬝ᵥ y + c * ((fun i => (GlobalTheory.WeilCont.adeleJoin F 0 x i).2) ⬝ᵥ y) = _
      rfl
  rw [harg]
  have h1 : ψ ((0 : InfiniteAdeleRing F), (fun i => (z i).2) ⬝ᵥ y + (c • x) ⬝ᵥ y) = 1 :=
    hH _ hzc (c • x) hx2 y hy
  rw [h1, one_mul]

theorem exists_fix (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : Continuous ψ) (κ : Type) [Fintype κ]
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) :
    ∃ L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F),
      IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ x ∈ L₁, ∀ y ∈ L₂, GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilCont.adeleJoin F 0 x, GlobalTheory.WeilCont.adeleJoin F 0 y) Φ = Φ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact exists_fix_pure ψ hψ κ f g hg
  | zero =>
    refine ⟨⊤, ⊤, isOpen_univ, isOpen_univ, fun x _ y _ => ?_⟩
    funext z
    simp [GlobalTheory.WeilM.schr]
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨L₁, L₂, o₁, o₂, h⟩ := h1
    obtain ⟨M₁, M₂, p₁, p₂, h'⟩ := h2
    refine ⟨L₁ ⊓ M₁, L₂ ⊓ M₂, by rw [AddSubgroup.coe_inf]; exact o₁.inter p₁,
      by rw [AddSubgroup.coe_inf]; exact o₂.inter p₂, fun x hx y hy => ?_⟩
    have e1 := h x hx.1 y hy.1
    have e2 := h' x hx.2 y hy.2
    funext z
    have a1 := congrFun e1 z
    have a2 := congrFun e2 z
    simp only [GlobalTheory.WeilM.schr, Pi.add_apply] at a1 a2 ⊢
    rw [mul_add, a1, a2]
  | smul a Φ _ h =>
    obtain ⟨L₁, L₂, o₁, o₂, h⟩ := h
    refine ⟨L₁, L₂, o₁, o₂, fun x hx y hy => ?_⟩
    funext z
    have a1 := congrFun (h x hx y hy) z
    simp only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul] at a1 ⊢
    rw [mul_left_comm, a1]

theorem schr_fix_nbhd : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (κ : Type) [Fintype κ], ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
      ∃ L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F),
        IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
        IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
        ∀ x ∈ L₁, ∀ y ∈ L₂, GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilCont.adeleJoin D.host.F 0 x, GlobalTheory.WeilCont.adeleJoin D.host.F 0 y) Φ = Φ := by
  intro D ψ hψ κ _ Φ hΦ
  exact exists_fix D.host.F ψ hψ.1.1 κ Φ hΦ

end GlobalTheory.SchrFixNbhd

end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped nonZeroDivisors Matrix

noncomputable section

namespace GlobalTheory.EqCovol.IsoPlane

open GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem selfD_of_isSelfDualTr {r : ℕ} (Y : Data E r) (h : IsSelfDualTr Y) : GlobalTheory.SW.SelfD Y Y.Λ := by
  refine ⟨Y.Λ_fg, fun x => (h x).trans (forall₂_congr fun y _ => ?_)⟩
  rw [GlobalTheory.ThFr.EF_def]
  rcases Y.κ0_xi with hk | hk
  · rw [hk, show (2 * Y.ξ0) / 2 = Y.ξ0 by ring]
  · have e : -(-(2 * Y.ξ0) / 2) * herm Y.Gm x y = -(-Y.ξ0 * herm Y.Gm x y) := by ring
    rw [hk, e, map_neg]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨-n, by rw [hn, Int.cast_neg]⟩
    · rintro ⟨n, hn⟩
      exact ⟨-n, by rw [Int.cast_neg, ← hn, neg_neg]⟩

def hypG : Matrix (Fin 2) (Fin 2) E := !![0, 1; 1, 0]

theorem hypG_herm (a b : Fin 2) : cc (hypG (E := E) a b) = hypG b a := by
  fin_cases a <;> fin_cases b <;> simp [hypG, cc]

theorem hypG_det : (hypG (E := E)).det ≠ 0 := by
  simp [hypG, Matrix.det_fin_two_of]

theorem herm_hypG (x y : Fin 2 → E) : herm hypG x y = x 0 * cc (y 1) + x 1 * cc (y 0) := by
  simp [herm, hypG, Fin.sum_univ_two]

def hypLat (J : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) (Fin 2 → E) :=
  ((1 : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E).comap (LinearMap.proj 0) ⊓
    (J : Submodule (𝓞 E) E).comap (LinearMap.proj 1)

theorem mem_hypLat {J : FractionalIdeal (𝓞 E)⁰ E} {x : Fin 2 → E} :
    x ∈ hypLat J ↔ x 0 ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) ∧ x 1 ∈ J := Iff.rfl

theorem isLattice_hypLat {J : FractionalIdeal (𝓞 E)⁰ E} (hJ0 : J ≠ 0) :
    ReciprocityTheory.MultiplicativeHeights.IsLattice (hypLat J) := by
  classical
  constructor
  · refine Submodule.FG.of_le ((Submodule.fg_span_singleton (Pi.single 0 1 : Fin 2 → E)).sup
      ((FractionalIdeal.fg_of_isNoetherianRing le_rfl J).map
        (LinearMap.single (𝓞 E) (fun _ : Fin 2 => E) 1))) fun x hx => ?_
    obtain ⟨h0, h1⟩ := mem_hypLat.1 hx
    let z : 𝓞 E := ⟨x 0, mem_one_fractionalIdeal_iff.1 h0⟩
    refine Submodule.mem_sup.2 ⟨z • Pi.single 0 1, Submodule.smul_mem _ z (Submodule.mem_span_singleton_self _),
      Pi.single 1 (x 1), ⟨x 1, h1, rfl⟩, ?_⟩
    funext i
    fin_cases i
    · simp [Algebra.smul_def]; rfl
    · simp
  · obtain ⟨j, hj, hj0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (mt FractionalIdeal.coeToSubmodule_eq_bot.1 hJ0)
    have e0 : (Pi.single 0 1 : Fin 2 → E) ∈ Submodule.span E (hypLat J : Set (Fin 2 → E)) :=
      Submodule.subset_span (mem_hypLat.2 ⟨by simp, by rw [Pi.single_eq_of_ne (by decide)]; exact (J : Submodule (𝓞 E) E).zero_mem⟩)
    have e1' : (Pi.single 1 j : Fin 2 → E) ∈ Submodule.span E (hypLat J : Set (Fin 2 → E)) :=
      Submodule.subset_span (mem_hypLat.2 ⟨by simp, by simpa using hj⟩)
    have e1 : (Pi.single 1 1 : Fin 2 → E) ∈ Submodule.span E (hypLat J : Set (Fin 2 → E)) := by
      have := Submodule.smul_mem _ j⁻¹ e1'
      rwa [← Pi.single_smul, smul_eq_mul, inv_mul_cancel₀ hj0] at this
    refine Submodule.eq_top_iff'.2 fun v => ?_
    have hv : v = v 0 • (Pi.single 0 1 : Fin 2 → E) + v 1 • Pi.single 1 1 := by
      funext i; fin_cases i <;> simp
    rw [hv]
    exact add_mem (Submodule.smul_mem _ _ e0) (Submodule.smul_mem _ _ e1)

theorem modular_hypLat {J : FractionalIdeal (𝓞 E)⁰ E} (hJ0 : J ≠ 0) (hJc : ∀ z ∈ J, cc z ∈ J)
    (x : Fin 2 → E) : x ∈ hypLat J ↔ ∀ y ∈ hypLat J, herm hypG x y ∈ J := by
  constructor
  · intro hx y hy
    obtain ⟨hx0, hx1⟩ := mem_hypLat.1 hx
    obtain ⟨hy0, hy1⟩ := mem_hypLat.1 hy
    rw [herm_hypG]
    refine (J : Submodule (𝓞 E) E).add_mem ?_ ?_
    · simpa using FractionalIdeal.mul_mem_mul hx0 (hJc _ hy1)
    · have : cc (y 0) ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) :=
        mem_one_fractionalIdeal_iff.2 (isIntegral_cc (mem_one_fractionalIdeal_iff.1 hy0))
      simpa using FractionalIdeal.mul_mem_mul hx1 this
  · intro h
    have h1 : x 1 ∈ J := by
      have := h (Pi.single 0 1) (mem_hypLat.2 ⟨by simp, by rw [Pi.single_eq_of_ne (by decide)]; exact (J : Submodule (𝓞 E) E).zero_mem⟩)
      simpa [herm_hypG, cc] using this
    have h0 : ∀ j ∈ J, x 0 * j ∈ J := fun j hj => by
      have := h (Pi.single 1 (cc j)) (mem_hypLat.2 ⟨by simp, by simpa using hJc j hj⟩)
      simpa [herm_hypG, cc] using this
    have hle : FractionalIdeal.spanSingleton (𝓞 E)⁰ (x 0) * J ≤ J := by
      refine FractionalIdeal.mul_le.2 fun i hi j hj => ?_
      obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
      rw [smul_mul_assoc]
      exact (J : Submodule (𝓞 E) E).smul_mem a (h0 j hj)
    have hle1 : FractionalIdeal.spanSingleton (𝓞 E)⁰ (x 0) ≤ 1 := by
      calc FractionalIdeal.spanSingleton (𝓞 E)⁰ (x 0)
          = J⁻¹ * (FractionalIdeal.spanSingleton (𝓞 E)⁰ (x 0) * J) := by
            rw [mul_left_comm, inv_mul_cancel₀ hJ0, mul_one]
        _ ≤ J⁻¹ * J := mul_le_mul_right hle _
        _ = 1 := inv_mul_cancel₀ hJ0
    exact ⟨hle1 (FractionalIdeal.mem_spanSingleton_self _ _), h1⟩

theorem hypG_signature (τ : E →+* ℂ) : ∃ Q : Matrix (Fin 2) (Fin 2) ℂ, Q.det ≠ 0 ∧
    gram τ hypG Q = Matrix.diagonal fun a : Fin 2 => ((sgn 1 (a : ℕ) : ℝ) : ℂ) := by
  refine ⟨!![1, 1; 1 / 2, -1 / 2], by simp [Matrix.det_fin_two_of]; norm_num, ?_⟩
  ext a b
  fin_cases a <;> fin_cases b <;> simp [gram, hermC, col, hypG, sgn, Fin.sum_univ_two, map_ofNat] <;> norm_num

theorem iso_rank_two (H : Host E) (Y : Data E 2) (hp : Y.p0 = 1) (hY : IsSelfDualTr Y) :
    ∃ z : Fin 2 → E, z ≠ 0 ∧ herm Y.Gm z z = 0 := by
  haveI := H.unram
  obtain ⟨J, hJ0, hJc, hJ⟩ := GlobalTheory.Ker.OntoLat.exists_valueIdeal Y
  have HN := GlobalTheory.QNorm.hasseNormSt
  have hΨ : ∀ τ : E →+* ℂ, τ ∈ (Y.Ψ : Set (E →+* ℂ)) ∨ ComplexEmbedding.conjugate τ ∈ (Y.Ψ : Set (E →+* ℂ)) := by
    intro τ
    by_cases h : ComplexEmbedding.conjugate τ ∈ Y.Ψ
    · exact Or.inr h
    · exact Or.inl ((Y.cmType τ).mpr h)
  have hs : ∀ τ ∈ (Y.Ψ : Set (E →+* ℂ)), ∃ p : ℕ,
      (∃ Q : Matrix (Fin 2) (Fin 2) ℂ, Q.det ≠ 0 ∧
        gram τ Y.Gm Q = Matrix.diagonal fun a : Fin 2 => ((sgn p (a : ℕ) : ℝ) : ℂ)) ∧
      ∃ Q : Matrix (Fin 2) (Fin 2) ℂ, Q.det ≠ 0 ∧
        gram τ hypG Q = Matrix.diagonal fun a : Fin 2 => ((sgn p (a : ℕ) : ℝ) : ℂ) := by
    intro τ hτ
    obtain ⟨Q, hQ, hg⟩ := Y.signature ⟨τ, hτ⟩
    rw [hp] at hg
    exact ⟨1, ⟨Q, hQ, hg⟩, hypG_signature τ⟩
  obtain ⟨P, hP, hPG⟩ := GlobalTheory.SelfDualGenus.congr_of_modular (G := Y.Gm) (G' := hypG) (L := Y.Λ)
    (L' := hypLat J) (GlobalTheory.LocalQuad.landherr_of_hasseNormSt HN) HN hJ0 hJc Y.Gm_herm hypG_herm Y.Gm_det
    hypG_det ⟨Y.Λ_fg, Y.Λ_span⟩ (isLattice_hypLat hJ0) (hJ Y.Λ (selfD_of_isSelfDualTr Y hY))
    (modular_hypLat hJ0 hJc) (GlobalTheory.Published.Landherr.congr_of_signature _ hΨ hs)
  refine ⟨P *ᵥ Pi.single 0 1, fun h => ?_, ?_⟩
  · have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hP h) 0
    simp at this
  · rw [GlobalTheory.SelfDualGenus.herm_mulVec, ← hPG, herm_hypG]
    simp

end GlobalTheory.EqCovol.IsoPlane

namespace GlobalTheory.EqCovol

theorem exists_isotropic_of_isSelfDualTr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (r : ℕ)
    (Y : Data E r), 1 ≤ Y.p0 → Y.p0 < r → GlobalTheory.EqCovol.IsSelfDualTr Y →
    ∃ z : Fin r → E, z ≠ 0 ∧ herm Y.Gm z z = 0 := by
  intro E _ _ _ H r Y h1 h2 hY
  by_cases hr : 3 ≤ r
  · obtain ⟨cu⟩ := GlobalTheory.CuspExist.nonempty_cuspFD GlobalTheory.QNorm.hasseNormSt E r 1 Y h1 (by omega) (by omega)
    exact ⟨cu.e 0, cu.ind.ne_zero 0, cu.iso 0 0⟩
  · obtain rfl : r = 2 := by omega
    exact IsoPlane.iso_rank_two H Y (by omega) hY

end GlobalTheory.EqCovol
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps

theorem _root_.GlobalTheory.T.heckeLocalGaussSum_norm_sq_eq_absNorm_pow : ∀ {E : Type} [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (c : Eˣ), a ≠ 0 → ExpAt χ w a → IsUnitary χ → w.valuation E (c : E) = WithZero.exp (-((a + diffExp w : ℕ) : ℤ)) → ‖gaussSumAt χ w a c‖ ^ 2 = (Ideal.absNorm w.asIdeal : ℝ) ^ a := by
  exact @GlobalTheory.GaussMod.gaussSumAt_normSq
end

section

namespace GlobalTheory

theorem bernsteinZelevinskyFiniteness_holds : GlobalTheory.Published.BernsteinZelevinskyFiniteness :=
  GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness

end GlobalTheory
end
