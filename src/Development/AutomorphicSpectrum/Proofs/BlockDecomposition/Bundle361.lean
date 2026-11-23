module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipApplyCastSuccLast
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Instances.Matrix
import GroundTheory.AutomorphicForms.GLnLocal
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import GroundTheory.AutomorphicForms.SmoothRep
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle317
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle335
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep

variable {k : Type} [Field k] {n : ℕ}

def lastRowMat (r : Fin (n + 1) → k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k :=
  (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateRow (Fin.last n) r

def rowInv (r : Fin (n + 1) → k) : Fin (n + 1) → k :=
  fun j => if j = Fin.last n then (r (Fin.last n))⁻¹ else -r j * (r (Fin.last n))⁻¹

theorem lastRowMat_mul_last (r s : Fin (n + 1) → k) (j : Fin (n + 1)) :
    (lastRowMat r * lastRowMat s) (Fin.last n) j =
      (if j = Fin.last n then 0 else r j) + r (Fin.last n) * s j := by
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat, Matrix.updateRow_self,
    Matrix.updateRow_ne (Fin.castSucc_ne_last _), Matrix.one_apply]
  congr 1
  first
  | refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [Fin.castSucc_ne_last]
    · simp [Fin.castSucc_ne_last]

theorem lastRowMat_mul_rowInv {r : Fin (n + 1) → k} (hr : r (Fin.last n) ≠ 0) :
    lastRowMat r * lastRowMat (rowInv r) = 1 := by
  ext i j
  by_cases hi : i = Fin.last n
  · subst hi
    rw [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat_mul_last]
    by_cases hj : j = Fin.last n
    · subst hj
      first
      | simp [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.rowInv, hr]
    · rw [Matrix.one_apply_ne (Ne.symm hj), if_neg hj]
      simp only [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.rowInv, if_neg hj]
      linear_combination (-r j) * mul_inv_cancel₀ hr
  · first
    | (rw [Matrix.mul_apply]
       simp only [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat, Matrix.updateRow_ne hi]
       rw [← Matrix.mul_apply, Matrix.one_mul, Matrix.updateRow_ne hi])

def lastRowGL (r : Fin (n + 1) → k) (hr : r (Fin.last n) ≠ 0) : GL (Fin (n + 1)) k where
  val := lastRowMat r
  inv := lastRowMat (rowInv r)
  val_inv := lastRowMat_mul_rowInv hr
  inv_val := mul_eq_one_comm.1 (lastRowMat_mul_rowInv hr)

def invRow (x : GL (Fin (n + 1)) k) : Fin (n + 1) → k :=
  fun j => ((x⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j

theorem invRow_one : invRow (1 : GL (Fin (n + 1)) k) (Fin.last n) = 1 := by
  simp [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow]

theorem vecMul_eLast (x : GL (Fin (n + 1)) k) :
    vecMul (eLast k n) (lastRowMat (invRow x) * (x : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) = eLast k n := by
  have h : vecMul (GlobalTheory.BZMir.eLast k n) (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x)) =
      vecMul (GlobalTheory.BZMir.eLast k n)
        ((x⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
    ext j
    first
    | simp [GlobalTheory.BZMir.eLast, Matrix.single_vecMul, GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat, GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow]
  rw [← Matrix.vecMul_vecMul, h, Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one]

section Top

variable [TopologicalSpace k] [IsTopologicalDivisionRing k] [T1Space k]

theorem continuous_invRow : Continuous (invRow : GL (Fin (n + 1)) k → _) := by
  have hc : Continuous fun x : GL (Fin (n + 1)) k =>
      ((x⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
    Units.continuous_coe_inv (M := Matrix (Fin (n + 1)) (Fin (n + 1)) k)
  unfold GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow
  first
  | exact continuous_pi fun j => hc.matrix_elem (Fin.last n) j

theorem continuous_lastRowMat : Continuous (lastRowMat : (Fin (n + 1) → k) → _) := by
  unfold GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat
  exact continuous_const.matrix_updateRow (Fin.last n) continuous_id

theorem continuousAt_rowInv : ContinuousAt (fun x : GL (Fin (n + 1)) k => rowInv (invRow x)) 1 := by
  have hv : Continuous (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow : GL (Fin (n + 1)) k → _) := GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.continuous_invRow
  have hl : ContinuousAt (fun x : GL (Fin (n + 1)) k => (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x (Fin.last n))⁻¹) 1 :=
    ((continuous_apply (Fin.last n)).comp hv).continuousAt.inv₀
      (show GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow (1 : GL (Fin (n + 1)) k) (Fin.last n) ≠ 0 by
        rw [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow_one]; exact one_ne_zero)
  refine continuousAt_pi.2 fun j => ?_
  by_cases hj : j = Fin.last n
  · simp only [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.rowInv, if_pos hj]
    exact hl
  · simp only [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.rowInv, if_neg hj]
    exact (((continuous_apply j).comp hv).continuousAt.neg).mul hl

theorem exists_nhd {V : Set (GL (Fin (n + 1)) k)} (hV : V ∈ 𝓝 (1 : GL (Fin (n + 1)) k)) :
    ∃ N ∈ 𝓝 (1 : GL (Fin (n + 1)) k), ∀ x ∈ N, ∃ hr : invRow x (Fin.last n) ≠ 0,
      lastRowGL (invRow x) hr * x ∈ V := by
  have h1 : GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow (1 : GL (Fin (n + 1)) k) (Fin.last n) ≠ 0 := by
    rw [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow_one]; exact one_ne_zero
  have hv1 : GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow (1 : GL (Fin (n + 1)) k) =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) := by
    funext j; simp [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow]
  have hg1 : GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowGL (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow (1 : GL (Fin (n + 1)) k)) h1 = 1 := by
    apply Units.ext
    show GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow (1 : GL (Fin (n + 1)) k)) = 1
    rw [hv1]
    exact Matrix.updateRow_eq_self _ _
  let ψ : GL (Fin (n + 1)) k →
      Matrix (Fin (n + 1)) (Fin (n + 1)) k × (Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵐᵒᵖ :=
    fun x => (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) * (x : Matrix (Fin (n + 1)) (Fin (n + 1)) k),
      MulOpposite.op (((x⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *
        GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.rowInv (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x))))
  have hψ : ∀ x (hr : GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x (Fin.last n) ≠ 0),
      Units.embedProduct (Matrix (Fin (n + 1)) (Fin (n + 1)) k)
        (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowGL (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) hr * x) = ψ x := fun x hr => by
    first
    | rfl
  have hfst : ContinuousAt (fun x : GL (Fin (n + 1)) k =>
      GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) * (x : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) 1 := by
    first
    | exact ((GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.continuous_lastRowMat.comp GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.continuous_invRow).mul
        Units.continuous_val).continuousAt
  have hsnd : ContinuousAt (fun x : GL (Fin (n + 1)) k =>
      MulOpposite.op (((x⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *
        GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.rowInv (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x)))) 1 :=
    MulOpposite.continuous_op.continuousAt.comp
      ((Units.continuous_coe_inv (M := Matrix (Fin (n + 1)) (Fin (n + 1)) k)).continuousAt.mul
        (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.continuous_lastRowMat.continuousAt.comp
          GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.continuousAt_rowInv))
  have hψc : ContinuousAt ψ 1 := hfst.prodMk hsnd
  have hψ1 : ψ 1 = Units.embedProduct (Matrix (Fin (n + 1)) (Fin (n + 1)) k) 1 := by
    rw [← hψ 1 h1, hg1, mul_one]
  obtain ⟨U, hU, hUV⟩ : ∃ U ∈ 𝓝 (Units.embedProduct (Matrix (Fin (n + 1)) (Fin (n + 1)) k) 1),
      Units.embedProduct (Matrix (Fin (n + 1)) (Fin (n + 1)) k) ⁻¹' U ⊆ V := by
    rw [Units.isEmbedding_embedProduct.toIsInducing.nhds_eq_comap] at hV
    exact Filter.mem_comap.1 hV
  have hne : ∀ᶠ x in 𝓝 (1 : GL (Fin (n + 1)) k), GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x (Fin.last n) ≠ 0 :=
    ((continuous_apply (Fin.last n)).comp GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.continuous_invRow).continuousAt.eventually_ne h1
  refine ⟨ψ ⁻¹' U ∩ {x | GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x (Fin.last n) ≠ 0},
    Filter.inter_mem (hψc.preimage_mem_nhds (by rw [hψ1]; exact hU)) hne, ?_⟩
  rintro x ⟨hxU, hx⟩
  refine ⟨hx, hUV ?_⟩
  show Units.embedProduct (Matrix (Fin (n + 1)) (Fin (n + 1)) k)
    (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowGL (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) hx * x) ∈ U
  rw [hψ x hx]
  exact hxU

end Top

theorem row_replacement (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (S : Subgroup (GL (Fin (n + 1)) k))
    (hS : ∀ (r : Fin (n + 1) → k), r (Fin.last n) ≠ 0 → ∀ g : GL (Fin (n + 1)) k,
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateRow (Fin.last n) r → g ∈ S)
    (O : Set (Mir k n)) (hO : O ∈ 𝓝 (1 : Mir k n)) :
    ∃ N ∈ 𝓝 (1 : GL (Fin (n + 1)) k), ∀ p ∈ S, ∀ x ∈ N, ∀ m : Mir k n, (m : GL (Fin (n + 1)) k) = p * x →
      ∃ a : Mir k n, (a : GL (Fin (n + 1)) k) ∈ S ∧ ∃ x' ∈ O, m = a * x' := by
  obtain ⟨V, hV, hVO⟩ := (mem_nhds_subtype _ _ _).1 hO
  obtain ⟨N, hN, hNV⟩ := GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.exists_nhd (k := k) (n := n) hV
  refine ⟨N, hN, fun p hp x hx m hm => ?_⟩
  obtain ⟨hr, hgx⟩ := hNV x hx
  have hgS : GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowGL (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) hr ∈ S := hS _ hr _ rfl
  have hmir : GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowGL (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) hr * x ∈ GlobalTheory.BZMir.Mir k n :=
    GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.vecMul_eLast x
  refine ⟨m * ⟨GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowGL (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) hr * x, hmir⟩⁻¹, ?_,
    ⟨GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowGL (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) hr * x, hmir⟩, hVO hgx, (inv_mul_cancel_right _ _).symm⟩
  show (m : GL (Fin (n + 1)) k) * (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowGL (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) hr * x)⁻¹ ∈ S
  rw [hm, _root_.mul_inv_rev, ← mul_assoc, mul_inv_cancel_right]
  exact S.mul_mem hp (S.inv_mem hgS)

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep

end
end

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.HeckeKm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_span_unif_pow_iff (m : ℕ) (a : 𝒪[k]) :
    a ∈ Ideal.span {Zls.unif k ^ m} ↔ (((Zls.unifU k ^ m)⁻¹ : kˣ) : k) * (a : k) ∈ 𝒪[k] := by
  have hc : (((Zls.unifU k ^ m : kˣ)) : k) = ((Zls.unif k ^ m : 𝒪[k]) : k) := by
    simp [Zls.unifU]
    rfl
  have hne : ((Zls.unif k ^ m : 𝒪[k]) : k) ≠ 0 := by
    rw [← hc]; exact Units.ne_zero _
  have hinv : (((Zls.unifU k ^ m)⁻¹ : kˣ) : k) = ((Zls.unif k ^ m : 𝒪[k]) : k)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, hc]
  rw [Ideal.mem_span_singleton', hinv]
  constructor
  · rintro ⟨b, rfl⟩
    have : ((Zls.unif k ^ m : 𝒪[k]) : k)⁻¹ * ((b * Zls.unif k ^ m : 𝒪[k]) : k) = (b : k) := by
      rw [MulMemClass.coe_mul]
      field_simp
    rw [this]
    exact b.2
  · intro h
    refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
    rw [MulMemClass.coe_mul]
    change ((Zls.unif k ^ m : 𝒪[k]) : k)⁻¹ * (a : k) * _ = _
    field_simp

theorem mem_Km_iff {N m : ℕ} (g : GL (Fin N) k) :
    g ∈ Zls.Km k N m ↔ g ∈ KO k (Fin N) ∧
      ∀ i j, (((Zls.unifU k ^ m)⁻¹ : kˣ) : k) * (g.val - 1) i j ∈ 𝒪[k] := by
  have key : ∀ (u : GL (Fin N) 𝒪[k]) (i j : Fin N),
      ((Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) u).val - 1) i j =
        ((u.val i j - (1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j : 𝒪[k]) : k) := by
    intro u i j
    by_cases h : i = j
    · subst h
      simp [Matrix.GeneralLinearGroup.map_apply]
      rfl
    · simp [Matrix.GeneralLinearGroup.map_apply, Matrix.one_apply_ne h]
      rfl
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨u, rfl⟩, fun i j => ?_⟩
    rw [key, ← mem_span_unif_pow_iff, ← Ideal.Quotient.eq]
    have h := congrArg (fun x : GL (Fin N) (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) => x.val i j)
      (MonoidHom.mem_ker.1 hu)
    simpa [Matrix.GeneralLinearGroup.map_apply, Matrix.one_apply, apply_ite] using h
  · rintro ⟨⟨u, rfl⟩, h⟩
    refine ⟨u, MonoidHom.mem_ker.2 (Units.ext (Matrix.ext fun i j => ?_)), rfl⟩
    have h' := h i j
    rw [key, ← mem_span_unif_pow_iff, ← Ideal.Quotient.eq] at h'
    simpa [Matrix.GeneralLinearGroup.map_apply, Matrix.one_apply, apply_ite] using h'

theorem continuous_entry_Km (N : ℕ) (c : k) (i j : Fin N) :
    Continuous fun g : GL (Fin N) k => c * (g.val - 1) i j :=
  continuous_const.mul
    (((Units.continuous_val (M := Matrix (Fin N) (Fin N) k)).sub continuous_const).matrix_elem i j)

theorem coe_Km_eq (N m : ℕ) :
    (Zls.Km k N m : Set (GL (Fin N) k)) = (KO k (Fin N) : Set (GL (Fin N) k)) ∩
      ⋂ i, ⋂ j, (fun g : GL (Fin N) k => (((Zls.unifU k ^ m)⁻¹ : kˣ) : k) * (g.val - 1) i j) ⁻¹'
        (𝒪[k] : Set k) := by
  ext g
  simp only [SetLike.mem_coe, mem_Km_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]

theorem isOpen_Km (N m : ℕ) : IsOpen (Zls.Km k N m : Set (GL (Fin N) k)) := by
  rw [coe_Km_eq]
  exact GlobalTheory.SplitFlip.isOpen_KO.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (show IsOpen (𝒪[k] : Set k) from Valuation.isOpen_integer).preimage (continuous_entry_Km N _ i j))

theorem isCompact_Km (N m : ℕ) : IsCompact (Zls.Km k N m : Set (GL (Fin N) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  rw [coe_Km_eq]
  exact GlobalTheory.SplitFlip.isCompact_KO.inter_right (isClosed_iInter fun i => isClosed_iInter fun j =>
    (show IsCompact (𝒪[k] : Set k) from IsNonarchimedeanLocalField.isCompact_closedBall k 1).isClosed.preimage
      (continuous_entry_Km N _ i j))

theorem totallyDisconnected_GL (N : ℕ) : TotallyDisconnectedSpace (GL (Fin N) k) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  haveI : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  haveI : TotallyDisconnectedSpace k := inferInstance
  haveI : TotallyDisconnectedSpace (Matrix (Fin N) (Fin N) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin N → Fin N → k))
  exact ⟨(GlobalTheory.SplitFlip.isEmbedding_val_GL (k := k) (n := Fin N)).isTotallyDisconnected
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

theorem exists_isHeckeOp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π →
    ∀ (m : ℕ) (g : GL (Fin N) k), ∃ T : Module.End ℂ (fixed π (Zls.Km k N m)), Zls.IsHeckeOp π m g T := by
  intro k _ _ _ _ N V _ _ π hπ m g
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  haveI := totallyDisconnected_GL (k := k) N
  have hKc := isCompact_Km (k := k) N m
  have hKo := isOpen_Km (k := k) N m
  have hπ' : GroundTheory.Automorphic.IsSmooth π := fun v => hπ v
  have hfix : ∀ w : GroundTheory.Automorphic.fixedVectors π (Zls.Km k N m),
      (w : V) ∈ fixed π (Zls.Km k N m) := fun w h => by
    simpa using w.2 h h.2
  refine ⟨LinearMap.codRestrict (fixed π (Zls.Km k N m))
    ((Submodule.subtype _) ∘ₗ GroundTheory.Automorphic.fixedProj π hπ' hKc hKo ∘ₗ π g ∘ₗ
      (fixed π (Zls.Km k N m)).subtype) fun v => hfix _, ?_⟩
  intro v l hl
  have hs := GroundTheory.Automorphic.sub_fixedProj_mem hπ' hKc hKo (π g (v : V))
  have h0 := GroundTheory.Automorphic.coinvariantsKer_le_ker_of_invariant (ρ := π) (K := Zls.Km k N m) (f := l)
    (fun x hx w => LinearMap.congr_fun (hl x hx) w) hs
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h0
  exact h0

end GlobalTheory.CompanionTheory.HeckeKm

end
end

section

open Filter Topology ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.KmTop

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_Km_iff (N m : ℕ) (g : GL (Fin N) k) :
    g ∈ Zls.Km k N m ↔ g ∈ KO k (Fin N) ∧
      ∀ i j, ((Zls.unifU k : k) ^ m)⁻¹ * (g.val i j - (1 : Matrix (Fin N) (Fin N) k) i j) ∈ 𝒪[k] := by
  have ha : ((Zls.unifU k : k) ^ m) = algebraMap 𝒪[k] k (Zls.unif k ^ m) := by
    simp [Zls.unifU]
  have ha0 : ((Zls.unifU k : k) ^ m) ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨u, rfl⟩, fun i j => ?_⟩
    have h1 : Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m}) (u.val i j) =
        Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m}) ((1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j) := by
      have h2 := congrArg (fun w => w.val i j) (MonoidHom.mem_ker.1 hu)
      simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one] at h2
      rw [h2, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h1)
    have h3 : (Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) u).val i j -
        (1 : Matrix (Fin N) (Fin N) k) i j = algebraMap 𝒪[k] k (c * Zls.unif k ^ m) := by
      rw [hc, map_sub]
      simp only [Matrix.GeneralLinearGroup.map_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [h3, map_mul, ← ha, mul_comm (algebraMap 𝒪[k] k c), inv_mul_cancel_left₀ ha0]
    exact c.2
  · rintro ⟨⟨u, rfl⟩, h⟩
    refine ⟨u, MonoidHom.mem_ker.2 ?_, rfl⟩
    refine Units.ext ?_
    ext i j
    have h1 := h i j
    let c : 𝒪[k] := ⟨_, h1⟩
    have h2 : algebraMap 𝒪[k] k (u.val i j - (1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j) =
        algebraMap 𝒪[k] k (c * Zls.unif k ^ m) := by
      rw [map_mul, ← ha, map_sub]
      show _ = ((Zls.unifU k : k) ^ m)⁻¹ * _ * _
      rw [mul_comm, mul_inv_cancel_left₀ ha0]
      simp only [Matrix.GeneralLinearGroup.map_apply, Matrix.one_apply]
      split_ifs <;> simp
    have h3 := IsFractionRing.injective 𝒪[k] k h2
    have h4 : Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m}) (u.val i j) =
        Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m}) ((1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j) :=
      Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ⟨c, h3.symm⟩)
    simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one]
    rw [h4, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem continuous_entry (N m : ℕ) (i j : Fin N) :
    Continuous fun g : GL (Fin N) k =>
      ((Zls.unifU k : k) ^ m)⁻¹ * (g.val i j - (1 : Matrix (Fin N) (Fin N) k) i j) := by
  have h : Continuous fun g : GL (Fin N) k => g.val i j :=
    (continuous_id.matrix_elem i j).comp Units.continuous_val
  exact continuous_const.mul (h.sub continuous_const)

theorem coe_Km_eq (N m : ℕ) : (Zls.Km k N m : Set (GL (Fin N) k)) =
    (KO k (Fin N) : Set (GL (Fin N) k)) ∩ ⋂ i, ⋂ j, (fun g : GL (Fin N) k =>
      ((Zls.unifU k : k) ^ m)⁻¹ * (g.val i j - (1 : Matrix (Fin N) (Fin N) k) i j)) ⁻¹' (𝒪[k] : Set k) := by
  ext g
  simp only [SetLike.mem_coe, mem_Km_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]

theorem isOpen_Km (N m : ℕ) : IsOpen (Zls.Km k N m : Set (GL (Fin N) k)) := by
  rw [coe_Km_eq]
  exact GlobalTheory.SplitFlip.isOpen_KO.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    GlobalTheory.SplitWeil.Model.isOpen_int.preimage (continuous_entry N m i j))

theorem isCompact_Km (N m : ℕ) : IsCompact (Zls.Km k N m : Set (GL (Fin N) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  rw [coe_Km_eq]
  refine GlobalTheory.SplitFlip.isCompact_KO.inter_right (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
  exact (GlobalTheory.SplitWeil.Model.isCompact_int.isClosed).preimage (continuous_entry N m i j)

end GlobalTheory.CompanionTheory.KmTop
end

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.KmVol

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isCompact_integralGL (N : ℕ) :
    IsCompact {g : GL (Fin N) k | (∀ i j, (g : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k]) ∧
      ∀ i j, ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k]} := by
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  have hO : IsCompact ((𝒪[k] : Subring k) : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall k 1
  have hM : IsCompact {A : Matrix (Fin N) (Fin N) k | ∀ i j, A i j ∈ 𝒪[k]} := by
    have h := isCompact_univ_pi fun _ : Fin N => isCompact_univ_pi fun _ : Fin N => hO
    have e : {A : Matrix (Fin N) (Fin N) k | ∀ i j, A i j ∈ 𝒪[k]} =
        Set.univ.pi fun _ : Fin N => Set.univ.pi fun _ : Fin N => ((𝒪[k] : Subring k) : Set k) :=
      Set.ext fun A => ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    exact e ▸ h
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin N) (Fin N) k)).isCompact_preimage
    (hM.prod (hM.image MulOpposite.continuous_op))
  convert h using 1
  ext g
  exact ⟨fun h => ⟨h.1, _, h.2, rfl⟩, fun ⟨h1, A, hA, e⟩ => ⟨h1, fun i j => by
    have : A = ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) := MulOpposite.op_injective e
    exact this ▸ hA i j⟩⟩

theorem Km_subset_integralGL (N m : ℕ) :
    (Zls.Km k N m : Set (GL (Fin N) k)) ⊆
      {g : GL (Fin N) k | (∀ i j, (g : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k]) ∧
        ∀ i j, ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k]} := by
  have key : ∀ (h : GL (Fin N) 𝒪[k]) (i j : Fin N),
      ((Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) h : GL (Fin N) k) :
        Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k] := fun h i j =>
    ((h : Matrix (Fin N) (Fin N) 𝒪[k]) i j).2
  rintro g ⟨h, -, rfl⟩
  refine ⟨key h, fun i j => ?_⟩
  rw [← map_inv]
  exact key h⁻¹ i j

theorem measure_image_Km_lt_top : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)] (μ : MeasureTheory.Measure (AdGL k N)), μ.IsHaarMeasure → ∀ m : ℕ, μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' (Zls.Km k N m : Set (GL (Fin N) k))) < ⊤ := by
  intro k _ _ _ _ N _ _ μ hμ m
  refine lt_of_le_of_lt (measure_mono (Set.image_mono (Km_subset_integralGL N m))) ?_
  exact ((isCompact_integralGL N).image QuotientGroup.continuous_mk).measure_lt_top

end GlobalTheory.CompanionTheory.KmVol
end
