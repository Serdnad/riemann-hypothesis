module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle277
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle280
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle281
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DiagIdx

open GlobalTheory.InertHomIdx

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem relIndex_pi_pi' {ι G : Type} [Fintype ι] [AddCommGroup G] (A B : ι → AddSubgroup G) :
    (AddSubgroup.pi Set.univ A).relIndex (AddSubgroup.pi Set.univ B) = ∏ i, (A i).relIndex (B i) := by
  let g : (∀ i, B i) →+ (AddSubgroup.pi Set.univ B) :=
    { toFun := fun v => ⟨fun i => (v i : G), fun i _ => (v i).2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hg : Function.Surjective g := fun x => ⟨fun i => ⟨x.1 i, x.2 i (Set.mem_univ i)⟩, rfl⟩
  have hc : ((AddSubgroup.pi Set.univ A).addSubgroupOf (AddSubgroup.pi Set.univ B)).comap g =
      AddSubgroup.pi Set.univ fun i => (A i).addSubgroupOf (B i) := by
    ext v
    simp [g, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hg, hc]
  simp_rw [AddSubgroup.relIndex, AddSubgroup.index, ← Nat.card_pi]
  refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientAddGroup.leftRel_pi]

def twist₂ (ϖ : L) (d : ℤ) : AddSubgroup L :=
  (Formalism.UG.intL L).toAddSubgroup.map (AddMonoidHom.mulLeft (ϖ ^ d))

theorem relIndex_twO (ϖ : L) (Q : ℕ) (h0 : ϖ ≠ 0) (h1 : Valued.v ϖ ≤ 1)
    (hQ : ∀ e : ℕ, ((Formalism.UG.intL L).toAddSubgroup.map (AddMonoidHom.mulLeft (ϖ ^ e))).relIndex
      (Formalism.UG.intL L).toAddSubgroup = Q ^ e) (d : ℤ) :
    (Formalism.UG.intL L).toAddSubgroup.relIndex (twist₂ ϖ d) = Q ^ (max (-d) 0).toNat := by
  rcases le_or_gt 0 d with hd | hd
  · have : max (-d) 0 = 0 := max_eq_right (by omega)
    rw [this, Int.toNat_zero, pow_zero, AddSubgroup.relIndex_eq_one]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hd
    change Valued.v (ϖ ^ (k : ℤ) * x) ≤ 1
    rw [zpow_natCast, map_mul, map_pow]
    exact mul_le_one' (pow_le_one' h1 k) hx
  · obtain ⟨e, he⟩ : ∃ e : ℕ, d = -(e : ℤ) := ⟨(-d).toNat, by omega⟩
    subst he
    have hm : max (-(-(e : ℤ))) 0 = e := by omega
    rw [hm, Int.toNat_natCast, ← hQ e]
    have hinj : Function.Injective (AddMonoidHom.mulLeft (ϖ ^ e)) :=
      mul_right_injective₀ (pow_ne_zero e h0)
    rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
    congr 1
    rw [twist₂, AddSubgroup.map_map]
    convert AddSubgroup.map_id _
    ext x
    simp [_root_.zpow_neg, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero e h0)]

end GlobalTheory.DiagIdx

namespace GlobalTheory.DiagIdx

open GlobalTheory.InertHomIdx

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem intMat_eq_pi (r n : ℕ) :
    intMat L r n =
      (AddSubgroup.pi Set.univ (fun _ : Fin r => AddSubgroup.pi Set.univ
        (fun _ : Fin n => (Formalism.UG.intL L).toAddSubgroup))).map
        (Matrix.ofAddEquiv : (Fin r → Fin n → L) ≃+ Matrix (Fin r) (Fin n) L).toAddMonoidHom := by
  ext X
  rw [AddSubgroup.mem_map_equiv, AddSubgroup.mem_pi, mem_intMat]
  simp only [Set.mem_univ, true_implies, AddSubgroup.mem_pi]
  exact Iff.rfl

theorem map_diag_eq_pi (ϖ : L) (h0 : ϖ ≠ 0) (r n : ℕ) (d : Fin r → ℤ) :
    (intMat L r n).map (lmul (Matrix.diagonal (fun i => ϖ ^ d i))) =
      (AddSubgroup.pi Set.univ (fun i : Fin r => AddSubgroup.pi Set.univ
        (fun _ : Fin n => twist₂ ϖ (d i)))).map
        (Matrix.ofAddEquiv : (Fin r → Fin n → L) ≃+ Matrix (Fin r) (Fin n) L).toAddMonoidHom := by
  ext Y
  rw [AddSubgroup.mem_map_equiv, AddSubgroup.mem_pi]
  simp only [Set.mem_univ, true_implies, AddSubgroup.mem_pi, twist₂, AddSubgroup.mem_map]
  constructor
  · rintro ⟨X, hX, hXY⟩ i j
    refine ⟨X i j, hX i j, ?_⟩
    rw [← hXY]
    change ϖ ^ d i * X i j = (Matrix.diagonal (fun i => ϖ ^ d i) * X) i j
    rw [Matrix.diagonal_mul]
  · intro hY
    refine ⟨Matrix.of fun i j => (ϖ ^ d i)⁻¹ * Y i j, fun i j => ?_, ?_⟩
    · obtain ⟨x, hx, hxe⟩ := hY i j
      change ϖ ^ d i * x = Y i j at hxe
      change (ϖ ^ d i)⁻¹ * Y i j ∈ Formalism.UG.intL L
      rw [← hxe, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ h0), one_mul]
      exact hx
    · ext i j
      change (Matrix.diagonal (fun i => ϖ ^ d i) * Matrix.of fun i j => (ϖ ^ d i)⁻¹ * Y i j) i j = Y i j
      rw [Matrix.diagonal_mul, Matrix.of_apply, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ h0), one_mul]

theorem sum_toNat {r : ℕ} (d : Fin r → ℤ) :
    ∑ i, (max (-d i) 0).toNat = (∑ i, max (-d i) 0).toNat := by
  have h : ((∑ i, (max (-d i) 0).toNat : ℕ) : ℤ) = ∑ i, max (-d i) 0 := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Int.toNat_of_nonneg (le_max_right _ _)
  rw [← h, Int.toNat_natCast]

theorem relIndex_intMat_diag : ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (Q : ℕ), ϖ ≠ 0 → Valued.v ϖ ≤ 1 → (∀ e : ℕ, ((Formalism.UG.intL L).toAddSubgroup.map (AddMonoidHom.mulLeft (ϖ ^ e))).relIndex (Formalism.UG.intL L).toAddSubgroup = Q ^ e) → ∀ (r n : ℕ) (d : Fin r → ℤ), (GlobalTheory.InertHomIdx.intMat L r n).relIndex ((GlobalTheory.InertHomIdx.intMat L r n).map (GlobalTheory.InertHomIdx.lmul (Matrix.diagonal (fun i => ϖ ^ d i)))) = Q ^ (n * (∑ i, max (-d i) 0).toNat) := by
  intro L _ _ ϖ Q h0 h1 hQ r n d
  rw [map_diag_eq_pi ϖ h0, intMat_eq_pi,
    AddSubgroup.relIndex_map_map_of_injective _ _ (AddEquiv.injective _), relIndex_pi_pi']
  simp_rw [relIndex_pi_pi', relIndex_twO ϖ Q h0 h1 hQ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← pow_mul, Finset.prod_pow_eq_pow_sum, ← sum_toNat, Finset.mul_sum,
    mul_comm n]

end GlobalTheory.DiagIdx
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.InertHomIdx


open Formalism.UG in
theorem intMat_map_lmul_of_mem_range {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
    {r n : ℕ} {g : GL (Fin r) L} (hg : g ∈ (Formalism.UG.bc (n := Fin r) (intL L).subtype).range) :
    (intMat L r n).map (lmul (n := n) (g : Matrix (Fin r) (Fin r) L)) = intMat L r n := by
  obtain ⟨h, rfl⟩ := hg
  have hint : ∀ (a : GL (Fin r) (intL L)) (X : Matrix (Fin r) (Fin n) L), X ∈ intMat L r n →
      lmul (n := n) ((Formalism.UG.bc (n := Fin r) (intL L).subtype a : GL (Fin r) L) : Matrix (Fin r) (Fin r) L) X
        ∈ intMat L r n := by
    intro a X hX i j
    rw [lmul_apply, Matrix.mul_apply]
    refine Subring.sum_mem _ fun k _ => Subring.mul_mem _ ?_ (hX k j)
    exact ((a : Matrix (Fin r) (Fin r) (intL L)) i k).2
  apply le_antisymm
  · rintro _ ⟨X, hX, rfl⟩
    exact hint h X hX
  · intro X hX
    refine ⟨lmul (n := n) ((Formalism.UG.bc (n := Fin r) (intL L).subtype h⁻¹ : GL (Fin r) L) : Matrix (Fin r) (Fin r) L) X,
      hint h⁻¹ X hX, ?_⟩
    simp only [lmul_apply]
    rw [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mul]

theorem relIndex_intMat_lmul_KU {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
    (c : L →+* L) (r n : ℕ) (t k₁ k₂ : GU c r) (hk₁ : k₁ ∈ KU c r) (hk₂ : k₂ ∈ KU c r) :
    (intMat L r n).relIndex ((intMat L r n).map (lmul (k₁ * t * k₂).1.1)) =
      (intMat L r n).relIndex ((intMat L r n).map (lmul t.1.1)) := by
  have h₁ := intMat_map_lmul_of_mem_range (n := n) ((Subgroup.mem_subgroupOf.mp hk₁)).2
  have h₂ := intMat_map_lmul_of_mem_range (n := n) ((Subgroup.mem_subgroupOf.mp hk₂)).2
  have hcomp : (lmul (n := n) (k₁ * t * k₂).1.1) =
      (lmul (n := n) k₁.1.1).comp ((lmul (n := n) t.1.1).comp (lmul (n := n) k₂.1.1)) := by
    ext X : 1
    simp only [lmul_apply, AddMonoidHom.comp_apply, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
  have hinj : Function.Injective (lmul (n := n) k₁.1.1) := by
    intro X Y hXY
    have := congrArg (fun Z => ((k₁.1⁻¹ : GL (Fin r) L) : Matrix (Fin r) (Fin r) L) * Z) hXY
    simpa only [lmul_apply, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul] using this
  rw [hcomp, ← AddSubgroup.map_map, ← AddSubgroup.map_map, h₂]
  calc _ = ((intMat L r n).map (lmul (n := n) k₁.1.1)).relIndex
        (((intMat L r n).map (lmul (n := n) t.1.1)).map (lmul (n := n) k₁.1.1)) := by rw [h₁]
    _ = _ := AddSubgroup.relIndex_map_map_of_injective _ _ hinj

end GlobalTheory.InertHomIdx
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLin

variable {D : D7}

theorem cA_incA (x : D.host.E) : cA D (incA D x) = incA D (starRingEnd D.host.E x) := by
  simp [cA, incA, sigR, inclR]
  rfl

theorem toEAf_incA_bar (c : 𝓞 D.host.E) :
    toEAf D (incA D (starRingEnd D.host.E (c : D.host.E))) =
      ((Formalism.L2.DIV.oToS D.host.F D.host.E (GlobalTheory.SW.Lev.bar c) : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
  simp [toEAf, finPart, incA, inclR, Formalism.L2.DIV.oToS, Formalism.UG.inclE]
  rfl

end GlobalTheory.RowLin

namespace GlobalTheory.RowLin

variable {D : D7}

theorem tmul_smul_add (p : AF D.host.F) (c x y : D.host.E) :
    p ⊗ₜ[D.host.F] (c * x + y) = (p ⊗ₜ[D.host.F] x) * incA D c + p ⊗ₜ[D.host.F] y := by
  rw [TensorProduct.tmul_add]
  congr 1
  simp only [incA, inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [mul_comm x c]

theorem rowAdj_smul_add (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (a e : AE D)
    (u v : Fin T.rank → D.host.E) (c : D.host.E) :
    GlobalTheory.LiftDat.rowAdj T βT a e (c • u + v) =
      toEAf D (incA D (starRingEnd D.host.E c)) • GlobalTheory.LiftDat.rowAdj T βT a e u + GlobalTheory.LiftDat.rowAdj T βT a e v := by
  have hM : (Matrix.of fun (_ : Fin 1) (l : Fin T.rank) =>
      ∑ k, cA D (cA D e * (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (c • u + v) k) * incA D (T.gram k l)) =
      incA D (starRingEnd D.host.E c) • (Matrix.of fun (_ : Fin 1) (l : Fin T.rank) =>
      ∑ k, cA D (cA D e * (pairA D.host.F 0 1) ⊗ₜ[D.host.F] u k) * incA D (T.gram k l)) +
      (Matrix.of fun (_ : Fin 1) (l : Fin T.rank) =>
      ∑ k, cA D (cA D e * (pairA D.host.F 0 1) ⊗ₜ[D.host.F] v k) * incA D (T.gram k l)) := by
    ext i l
    simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Pi.add_apply, Pi.smul_apply,
      tmul_smul_add, mul_add, map_add, map_mul, cA_incA, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  unfold GlobalTheory.LiftDat.rowAdj
  rw [hM]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply,
    map_add, map_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end GlobalTheory.RowLin

namespace GlobalTheory.RowLin

theorem rowRed_smul_add : ∀ (D : D7) (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (a e : AE D) (PP : Formalism.L2.DIV.Pl D.host.E) (u v : Fin T.rank → D.host.E), IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e u) → IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e v) → ∀ c : 𝓞 D.host.E, IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e ((c : D.host.E) • u + v)) ∧ GlobalTheory.LiftDat.rowRed T βT a e PP ((c : D.host.E) • u + v) = fun j => Ideal.Quotient.mk PP.asIdeal (GlobalTheory.SW.Lev.bar c) * GlobalTheory.LiftDat.rowRed T βT a e PP u j + GlobalTheory.LiftDat.rowRed T βT a e PP v j := by
  intro D T βT a e PP u v hu hv c
  have hz := toEAf_incA_bar (D := D) c
  have hrow := rowAdj_smul_add T βT a e u v (c : D.host.E)
  have hzi : toEAf D (incA D (starRingEnd D.host.E (c : D.host.E))) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [hz]; exact Subtype.property _
  have hent : ∀ j, GlobalTheory.LiftDat.rowAdj T βT a e ((c : D.host.E) • u + v) 0 j =
      toEAf D (incA D (starRingEnd D.host.E (c : D.host.E))) * GlobalTheory.LiftDat.rowAdj T βT a e u 0 j + GlobalTheory.LiftDat.rowAdj T βT a e v 0 j := by
    intro j; rw [hrow]; simp [Matrix.add_apply, Matrix.smul_apply]
  have hint : IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e ((c : D.host.E) • u + v)) := by
    intro i j
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    rw [hent]
    exact Subring.add_mem _ (Subring.mul_mem _ hzi (hu 0 j)) (hv 0 j)
  refine ⟨hint, ?_⟩
  funext j
  simp only [GlobalTheory.LiftDat.rowRed, redM, dif_pos (hint 0 j), dif_pos (hu 0 j), dif_pos (hv 0 j)]
  have hsub : (⟨GlobalTheory.LiftDat.rowAdj T βT a e ((c : D.host.E) • u + v) 0 j, hint 0 j⟩ :
      Formalism.L2.Herm.intAf D.host.F D.host.E) =
      Formalism.L2.DIV.oToS D.host.F D.host.E (GlobalTheory.SW.Lev.bar c) * ⟨_, hu 0 j⟩ + ⟨_, hv 0 j⟩ := by
    apply Subtype.ext
    simp only [Subring.coe_add, Subring.coe_mul, ← hz, hent]
  rw [hsub, RingHom.map_add, RingHom.map_mul, Formalism.L2.DIV.resS_oToS]

end GlobalTheory.RowLin
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section
namespace GlobalTheory.SeeConjRead.DetUnit

open Classical

section Val
variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)

theorem v_sign_smul {n : ℕ} (s : Equiv.Perm (Fin n)) (x : K) : v (Equiv.Perm.sign s • x) = v x := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h
  · rw [h, one_smul]
  · rw [h, Units.neg_smul, one_smul, Valuation.map_neg]

theorem v_det_le {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (h : ∀ i j, v (M i j) ≤ 1) : v M.det ≤ 1 := by
  rw [Matrix.det_apply]
  refine Valuation.map_sum_le v fun s _ => ?_
  rw [v_sign_smul, map_prod]
  exact Finset.prod_le_one' fun i _ => h _ _

theorem v_det_eq_one {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (d : Fin n → K) (hd : ∀ a, v (d a) = 1)
    (h : ∀ a b, v (M a b - if a = b then d a else 0) < 1) : v M.det = 1 := by
  have hle : ∀ i j, v (M i j) ≤ 1 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have h1 := h i i
      rw [if_pos rfl] at h1
      have : M i i = (M i i - d i) + d i := by ring
      rw [this]
      exact (Valuation.map_add v _ _).trans (max_le h1.le (hd i).le)
    · have h1 := h i j
      rw [if_neg hij, sub_zero] at h1
      exact h1.le
  have hdiag : ∀ i, v (M i i) = 1 := by
    intro i
    have h1 := h i i
    rw [if_pos rfl] at h1
    have : M i i = (M i i - d i) + d i := by ring
    rw [this, Valuation.map_add_eq_of_lt_right v (by rw [hd i]; exact h1), hd i]
  rw [Matrix.det_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Equiv.Perm (Fin n)))]
  have hmain : v (Equiv.Perm.sign (1 : Equiv.Perm (Fin n)) • ∏ i, M ((1 : Equiv.Perm (Fin n)) i) i) = 1 := by
    rw [v_sign_smul, map_prod]
    exact Finset.prod_eq_one fun i _ => hdiag i
  have hrest : v (∑ s ∈ Finset.univ.erase (1 : Equiv.Perm (Fin n)), Equiv.Perm.sign s • ∏ i, M (s i) i) < 1 := by
    refine Valuation.map_sum_lt v one_ne_zero fun s hs => ?_
    have hs1 : s ≠ 1 := Finset.ne_of_mem_erase hs
    obtain ⟨i, hi⟩ : ∃ i, s i ≠ i := by
      by_contra hc
      push_neg at hc
      exact hs1 (Equiv.ext hc)
    rw [v_sign_smul, map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    have h1 := h (s i) i
    rw [if_neg hi, sub_zero] at h1
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (Finset.prod_le_one' fun j _ => hle _ _)) h1
  rw [Valuation.map_add_eq_of_lt_left v (by rw [hmain]; exact hrest), hmain]

end Val

end GlobalTheory.SeeConjRead.DetUnit

namespace GlobalTheory.SeeConjRead.DetUnit

theorem val_le_of_int {D : D7} (Q : Pl D.host.E) (x : EAf D) (hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    Valued.v (GlobalTheory.StdFrames.cpt Q x) ≤ 1 := by
  have := (GlobalTheory.StdFrames.mem_OA_iff x).1 hx Q
  rwa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at this

theorem val_det_le {D : D7} {n : ℕ} (Q : Pl D.host.E) (M : Matrix (Fin n) (Fin n) (EAf D))
    (hM : ∀ i j, M i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) : Valued.v (GlobalTheory.StdFrames.cpt Q M.det) ≤ 1 := by
  rw [RingHom.map_det]
  exact v_det_le _ _ fun i j => val_le_of_int Q _ (hM i j)

theorem det_unit : ∀ {D : D7} {n : ℕ} (β₀ : GL (Fin n) (EAf D)) (J U W : Matrix (Fin n) (Fin n) (EAf D)) (Q : Pl D.host.E) (d : Fin n → EAf D), (∀ i j, (Formalism.UG.cT (GlobalTheory.StdFrames.sg D) β₀.val * J * β₀.val) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → (∀ i j, ((β₀⁻¹).val * U) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → (∀ i j, ((β₀⁻¹).val * W) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → (∀ a, Valued.v (GlobalTheory.StdFrames.cpt Q (d a)) = 1) → (∀ a b, SmallAt Q ((Formalism.UG.cT (GlobalTheory.StdFrames.sg D) U * J * W) a b - if a = b then d a else 0)) → Valued.v (GlobalTheory.StdFrames.cpt Q ((β₀⁻¹).val * W).det) = 1 := by
  intro D n β₀ J U W Q d hG hA hB hd hX
  set A := (β₀⁻¹).val * U with hAdef
  set B := (β₀⁻¹).val * W with hBdef
  set G := Formalism.UG.cT (GlobalTheory.StdFrames.sg D) β₀.val * J * β₀.val with hGdef
  have hU : U = β₀.val * A := by rw [hAdef, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hW : W = β₀.val * B := by rw [hBdef, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hX' : Formalism.UG.cT (GlobalTheory.StdFrames.sg D) U * J * W = Formalism.UG.cT (GlobalTheory.StdFrames.sg D) A * G * B := by
    rw [hGdef, hU, hW, GlobalTheory.StdFrames.cT_mul']
    simp only [Matrix.mul_assoc]
  have h1 : Valued.v (GlobalTheory.StdFrames.cpt Q (Formalism.UG.cT (GlobalTheory.StdFrames.sg D) U * J * W).det) = 1 := by
    rw [RingHom.map_det]
    refine v_det_eq_one _ _ (fun a => GlobalTheory.StdFrames.cpt Q (d a)) hd fun a b => ?_
    have := hX a b
    unfold SmallAt at this
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    split_ifs at this ⊢ with hab
    · rwa [map_sub] at this
    · rwa [sub_zero] at this ⊢
  rw [hX', Matrix.det_mul, Matrix.det_mul] at h1
  simp only [map_mul] at h1
  have ha : Valued.v (GlobalTheory.StdFrames.cpt Q (Formalism.UG.cT (GlobalTheory.StdFrames.sg D) A).det) ≤ 1 :=
    val_det_le Q _ fun i j => Formalism.UG.P.csDual_sig_mem _ (hA j i)
  have hg : Valued.v (GlobalTheory.StdFrames.cpt Q G.det) ≤ 1 := val_det_le Q _ hG
  have hb : Valued.v (GlobalTheory.StdFrames.cpt Q B.det) ≤ 1 := val_det_le Q _ hB
  refine le_antisymm hb ?_
  rw [← h1]
  exact mul_le_of_le_one_left' (mul_le_one' ha hg)

end GlobalTheory.SeeConjRead.DetUnit
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

namespace GlobalTheory.SeeConjRead

theorem flagV_pair_table : ∀ {M A : Type} [Zero M] [Ring A] (p : M → M → A) (sm : A → Prop) (ρ k n : ℕ), n = 2 * ρ + k + 1 → ∀ (e f : Fin ρ → M) (b b' : Fin k → M) (z : M), PairTable p sm e f b b' z → ∀ a c : Fin n, sm (p (flagV ρ k n f e b' z a) (flagV ρ k n e f b z c) - if a = c then sgnD ρ k a else 0) := by
  intro M A _ _ p sm ρ k n hn e f b b' z hT a c
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16⟩ := hT
  subst hn
  have ha := a.isLt
  have hc := c.isLt
  have d1 : ∀ (x y : Fin ρ), x.1 = y.1 → sm (p (f x) (e y) - 1) := by
    intro x y h; have := t1 x y; rwa [if_pos (Fin.ext h)] at this
  have o1 : ∀ (x y : Fin ρ), x.1 ≠ y.1 → sm (p (f x) (e y) - 0) := by
    intro x y h; have := t1 x y; rwa [if_neg (fun hh => h (congrArg Fin.val hh))] at this
  have d6 : ∀ (x y : Fin k), x.1 = y.1 → sm (p (b' x) (b y) - 1) := by
    intro x y h; have := t6 x y; rwa [if_pos (Fin.ext h)] at this
  have o6 : ∀ (x y : Fin k), x.1 ≠ y.1 → sm (p (b' x) (b y) - 0) := by
    intro x y h; have := t6 x y; rwa [if_neg (fun hh => h (congrArg Fin.val hh))] at this
  have d16 : ∀ (x y : Fin ρ), x.1 = y.1 → sm (p (e x) (f y) - 1) := by
    intro x y h; have := t16 x y; rwa [if_pos (Fin.ext h)] at this
  have o16 : ∀ (x y : Fin ρ), x.1 ≠ y.1 → sm (p (e x) (f y) - 0) := by
    intro x y h; have := t16 x y; rwa [if_neg (fun hh => h (congrArg Fin.val hh))] at this
  have d11 : sm (p z z - -1) := by rw [sub_neg_eq_add]; exact t11
  by_cases hac : a.1 = c.1
  · rw [if_pos (Fin.ext hac)]
    unfold flagV sgnD
    split_ifs <;> first
      | omega
      | exact d11
      | exact d1 _ _ (by dsimp only; omega)
      | exact d6 _ _ (by dsimp only; omega)
      | exact d16 _ _ (by dsimp only; omega)
  · rw [if_neg (fun hh => hac (congrArg Fin.val hh))]
    unfold flagV
    split_ifs <;> first
      | omega
      | exact o1 _ _ (by dsimp only; omega)
      | exact o6 _ _ (by dsimp only; omega)
      | exact o16 _ _ (by dsimp only; omega)
      | (rw [sub_zero]; first
          | exact t2 _ _ | exact t3 _ | exact t4 _ _ | exact t5 _ _ | exact t7 _ | exact t8 _ _
          | exact t9 _ | exact t10 _ | exact t12 _ | exact t13 _ _ | exact t14 _ _ | exact t15 _)

end GlobalTheory.SeeConjRead
end
