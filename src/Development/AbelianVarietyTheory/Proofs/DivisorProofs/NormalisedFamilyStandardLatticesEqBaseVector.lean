module

public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeTransportPreservesSelfDual
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.NatAtStd

theorem isSD_pi (E : Type) [Field E] [NumberField E] [StarRing E] (N : ℕ) :
    IsSDLat E N (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)) := by
  apply _root_.GlobalTheory.SeamSelfDual.isSDLat_pi <;> assumption

theorem detId_std (D : D7) (N : ℕ) : TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N) = 1 := by
  apply _root_.Formalism.L2.Ker.detId_std <;> assumption

theorem chi_one (D : D7) (χ : TaylorLogMetric.IdE D → ℂ) (h : TaylorLogMetric.IsChi D χ) : χ 1 = 1 := by
  letI := D.host.cmStar
  have h1 := h.2 1
  rw [Submodule.one_eq_span]
  simpa using h1

theorem chiFac_std (D : D7) (χ : TaylorLogMetric.IdE D → ℂ) (h : TaylorLogMetric.IsChi D χ) (a b : ℕ) :
    Base.chiFac χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) = 1 := by
  simp [Base.chiFac, detId_std, chi_one D χ h]

variable (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ}

theorem Iop_self (A : AddSubgroup (TaylorLogMetric.VC D N N')) :
    ∃ x ∈ A, ∀ G : TaylorLogMetric.VC D N N' → ℂ, TaylorLogMetric.Iop D T A A G = fun z => TaylorLogMetric.al D T x * TaylorLogMetric.U D T x G z := by
  have htop : A.addSubgroupOf A = ⊤ := AddSubgroup.addSubgroupOf_self A
  haveI hsub : Subsingleton (A ⧸ A.addSubgroupOf A) := by
    rw [htop]; exact QuotientAddGroup.subsingleton_quotient_top
  let q0 : A ⧸ A.addSubgroupOf A := QuotientAddGroup.mk 0
  refine ⟨((Quotient.out q0 : A) : TaylorLogMetric.VC D N N'), Subtype.property _, fun G => ?_⟩
  funext z
  have hi : (A.addSubgroupOf A).index = 1 := by rw [htop]; exact AddSubgroup.index_top
  unfold TaylorLogMetric.Iop
  rw [finsum_eq_single _ q0 (fun q hq => absurd (Subsingleton.elim q q0) hq), hi]
  simp

theorem Hf_neg_right (z x : TaylorLogMetric.VC D N N') : TaylorLogMetric.Hf D T z (-x) = -TaylorLogMetric.Hf D T z x := by
  simp [TaylorLogMetric.Hf, neg_div]

theorem Hf_neg_left (z x : TaylorLogMetric.VC D N N') : TaylorLogMetric.Hf D T (-z) x = -TaylorLogMetric.Hf D T z x := by
  simp [TaylorLogMetric.Hf, neg_div]

theorem Hf_add_left (z w x : TaylorLogMetric.VC D N N') : TaylorLogMetric.Hf D T (z + w) x = TaylorLogMetric.Hf D T z x + TaylorLogMetric.Hf D T w x := by
  simp [TaylorLogMetric.Hf, add_mul, Finset.sum_add_distrib, add_div]

theorem al_neg_mul (x : TaylorLogMetric.VC D N N') : TaylorLogMetric.al D T (-x) * TaylorLogMetric.al D T x = 1 := by
  unfold TaylorLogMetric.al
  rw [Hf_neg_left, Hf_neg_right, neg_neg, ← mul_zpow]
  simp

theorem inv_op (x : TaylorLogMetric.VC D N N') (G : TaylorLogMetric.VC D N N' → ℂ) (z : TaylorLogMetric.VC D N N') :
    TaylorLogMetric.al D T (-x) * TaylorLogMetric.U D T (-x) (fun w => TaylorLogMetric.al D T x * TaylorLogMetric.U D T x G w) z = G z := by
  have h := al_neg_mul D T x
  unfold TaylorLogMetric.U
  simp only [Hf_add_left, Hf_neg_left, Hf_neg_right, neg_add_cancel_right]
  have he : Complex.exp (-(Real.pi : ℂ) * (TaylorLogMetric.Hf D T z x + -TaylorLogMetric.Hf D T x x) - (Real.pi : ℂ) * TaylorLogMetric.Hf D T x x / 2) *
      Complex.exp (-(Real.pi : ℂ) * -TaylorLogMetric.Hf D T z x - (Real.pi : ℂ) * - -TaylorLogMetric.Hf D T x x / 2) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    ring
  linear_combination (G z) * he * (TaylorLogMetric.al D T (-x) * TaylorLogMetric.al D T x) + G z * h

theorem eNat_std : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (B : Base D cc dl) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → B.VecP χ → ∀ a b : ℕ, Even a → Even b → TaylorLogMetric.admitted D a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) ∧ B.eNat χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) = B.thZero a b := by
  intro D cc dl B χ hχ hV a b ha hb
  have hA : TaylorLogMetric.admitted D a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) := by
    letI := D.host.cmStar
    exact ⟨ha, hb, isSD_pi _ a, isSD_pi _ b⟩
  refine ⟨hA, ?_⟩
  obtain ⟨x, hx, hI⟩ := Iop_self D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b))
  have hTh : B.eNat χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) ∈ TaylorLogMetric.Th D B.tor (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) :=
    (hV a b _ _ hA).1
  have hfix := hTh.2 (-x) (neg_mem hx)
  have he : B.eNat χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) = fun z => TaylorLogMetric.al D B.tor x * TaylorLogMetric.U D B.tor x
      (fun w => TaylorLogMetric.al D B.tor x * TaylorLogMetric.U D B.tor x (B.thZero a b) w) z := by
    funext z
    unfold Base.eNat Base.thMoved Base.thHalf
    rw [chiFac_std D χ hχ, one_mul, hI, hI]
  have h1 : B.eNat χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) =
      fun w => TaylorLogMetric.al D B.tor x * TaylorLogMetric.U D B.tor x (B.thZero a b) w := by
    funext z
    rw [← hfix z]
    conv_lhs => rw [he]
    exact inv_op D B.tor x _ z
  funext z
  rw [← hfix z]
  conv_lhs => rw [h1]
  exact inv_op D B.tor x _ z

end GlobalTheory.NatAtStd
