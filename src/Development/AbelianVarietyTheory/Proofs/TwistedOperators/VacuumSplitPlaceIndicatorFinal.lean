module

import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicatorDualPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilInertPlaceVacuumEigenfunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceSchwartzBruhatVacuumConditionEqSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalImageLatticeSupportedAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalSubgroupFirstProjEqAnnihilator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeLocalDarbouxCoordsBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorLatticeStabiliserRightPreservesVacuu
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.DblVacLineTransp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


omit [NumberField F] [NumberField E] in
theorem symp_transpose {R : Type} [CommRing R] {K : Type} [CommRing K] [Algebra R K] (c : K →ₐ[R] K)
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (ξ : K) (JA : Matrix α α K) (JB : Matrix β β K)
    (x y : Matrix α β K) : symp (R := R) c ξ JB JA xᵀ yᵀ = symp (R := R) c ξ JA JB x y := by
  unfold symp hTens
  congr 2
  simp only [Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

omit [NumberField E] in
theorem at_transpose {m n : Type} (v : Pl (F := F)) (z : Matrix m n (AE F E)) :
    At (evFin F v) zᵀ ↔ At (evFin F v) z := by
  constructor
  · intro h u hu
    have := h u hu
    rw [← Matrix.transpose_smul] at this
    simpa using congrArg Matrix.transpose this
  · intro h u hu
    rw [← Matrix.transpose_smul, h u hu, Matrix.transpose_zero]

theorem transpose_mem_latAtV {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl (F := F)) {z : Matrix (Fin n) (Fin d) (AE F E)}
    (hz : z ∈ latAtV X Y v) : zᵀ ∈ latAtV Y X v := by
  have hle : latAtV X Y v ≤ (latAtV Y X v).comap (Matrix.transposeAddEquiv (Fin n) (Fin d) (AE F E)).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).mpr ?_
    rintro _ ⟨a, ha, hai, x, hx, y, hy, rfl⟩
    refine AddSubgroup.subset_closure ⟨a, ha, hai, y, hy, x, hx, ?_⟩
    show (a • incM F (Matrix.vecMulVec x y))ᵀ = _
    simp only [incM, Matrix.transpose_smul, ← Matrix.transpose_map, Matrix.transpose_vecMulVec]
  exact hle hz

theorem mem_latAtV_transpose {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl (F := F)) (z : Matrix (Fin n) (Fin d) (AE F E)) :
    zᵀ ∈ latAtV Y X v ↔ z ∈ latAtV X Y v :=
  ⟨fun h => by simpa using transpose_mem_latAtV Y X v h, transpose_mem_latAtV X Y v⟩


open GlobalTheory.DblVacLine in
theorem dbl_line_co {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {Y : Spc F E d} {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    (v : Pl (F := F)) (hunr : PsiUnr ψ v) (hX : X.L.IsLattice E) (hY : Y.L.IsLattice E)
    (hsd : ∀ z : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) z → (z ∈ latAtV X Y v ↔ ∀ γ ∈ latAtV X Y v,
      ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F Y.J) z γ) = 1))
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F Y.J)) κ) (φ : (κ → Fv F v) → ℂ)
    (hφ : φ ∈ SB _ ∧ φ ≠ 0 ∧ ∃ θ : 𝓞 E, (θ : E) + σ θ = 1 ∧ ∀ γ ∈ latAtV X Y v, Acts (evFin F v) (co.rho ψ γ) φ
      (ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F Y.J) γ γ) • φ))
    (dd : Darboux (symp (cA σ) (-1) (incM F X.J) (dbl (incM F Y.J))) (κ ⊕ κ))
    (omd : UG (cA σ) (dbl (incM F Y.J)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ))
    (hdd : IsDblCoord (cA σ) (-1) (incM F X.J) (incM F Y.J) co dd)
    (hS : IsUSplitting (adeleClass F) ψ dd (actB (cA σ)) omd)
    (R : (κ → AF F) → ℂ) (hR : Rest (evFin F v) φ R)
    (g : GlobalTheory.InertDbl.UD σ Y) (hg : g ∈ GlobalTheory.InertDbl.KAtD σ Y v) :
    ∃ c : ℂ, omd g (GlobalTheory.InertDbl.dblFun (tens (evFin F v) φ R)) = c • GlobalTheory.InertDbl.dblFun (tens (evFin F v) φ R) := by
  obtain ⟨hφSB, hφ0, θ, -, hvac⟩ := hφ
  exact _root_.GlobalTheory.SplitParLeft.dbl_line_coord hψ v hunr hX hY hsd co φ hφSB hφ0 (θ : E) hvac dd omd hdd hS R hR g hg

end GlobalTheory.DblVacLineTransp

namespace GlobalTheory.DblVacLineSplitTransp

open GlobalTheory.DblVacLineTransp

end GlobalTheory.DblVacLineSplitTransp

end
