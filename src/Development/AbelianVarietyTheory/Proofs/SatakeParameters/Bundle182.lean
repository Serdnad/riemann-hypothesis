module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle020
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle174
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle040
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle176
public import Formalism.LocalToGlobal.GlobalTheory.EqGlobOfHat
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle171
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualComap
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.StdOK
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle177
import Formalism.LocalRingCardinality.DataHost
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle018
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.LocalToGlobal.InertKernelTheory.Bundle009
import Formalism.LocalToGlobal.InertKernelTheory.Bundle003
import Formalism.LocalToGlobal.KernelLattices.Bundle001
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.NrmAMemAdForms
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008

@[expose] public section

section

noncomputable section
open Matrix

namespace GlobalTheory.Hk3.HoweDuality.Square

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mul_int {a b c : ℕ} {A : Matrix (Fin a) (Fin b) L} {B : Matrix (Fin b) (Fin c) L}
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (hB : ∀ i j, B i j ∈ Formalism.UG.intL L) (i : Fin a) (j : Fin c) :
    (A * B) i j ∈ Formalism.UG.intL L := by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)

theorem star_int {σ : L →+* L} (hv : ∀ x, Valued.v (σ x) = Valued.v x) {a b : ℕ} {A : Matrix (Fin a) (Fin b) L}
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (i : Fin b) (j : Fin a) :
    (Matrix.transpose (A.map σ)) i j ∈ Formalism.UG.intL L := by
  have h := hA j i
  simp only [Matrix.transpose_apply, Matrix.map_apply]
  change Valued.v (σ (A j i)) ≤ 1
  rw [hv]; exact h

theorem gen {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {σ : L →+* L} {q : ℕ} {δ : L}
    {n n' : ℕ} {A B : Matrix (Fin n) (Fin n) L} {ψ : AddChar L ℂ}
    (hU : Formalism.UG.IsUnramInv ϖ σ q) (hq : Odd q) (hA : ∀ i j, A i j ∈ Formalism.UG.intL L)
    (hB : ∀ i j, B i j ∈ Formalism.UG.intL L) (hAB : A * B = 1) (hAh : ∀ i j, σ (A i j) = A j i)
    (hδ : Valued.v δ = 1 ∧ σ δ = -δ) (hpi : ∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1)
    (hne : ∃ a ∈ Formalism.UG.intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) (x : Matrix (Fin n') (Fin n) L)
    (hx : (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
      (∀ i j, (C * x) i j ∈ Formalism.UG.intL L) →
      ψ ((δ * Matrix.trace (C * (x * A * Matrix.transpose ((x).map σ))) + σ (δ * Matrix.trace (C * (x * A * Matrix.transpose ((x).map σ))))) / 2) = 1)) :
    ∃ l ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n,
      ∀ i j, ((x - l) * A * Matrix.transpose ((x - l).map σ)) i j ∈ Formalism.UG.intL L := by
  have hσ : ∀ x, σ (σ x) = x := hU.1
  have hv : ∀ x, Valued.v (σ x) = Valued.v x := hU.2.1
  obtain ⟨P, P', Q, Q', a, hP, hP', hPP', hQ, hQ', hQQ', hE⟩ := GlobalTheory.T.smith_normal_form_integral_matrix L ϖ hU.2.2.2.1 n n' x
  have hQ'Q : Q' * Q = 1 := mul_eq_one_comm.mp hQQ'
  have hP'P : P' * P = 1 := mul_eq_one_comm.mp hPP'
  have hA'i : ∀ i j, (Q' * A * Matrix.transpose (Q'.map σ)) i j ∈ Formalism.UG.intL L :=
    mul_int (mul_int hQ' hA) (star_int hv hQ')
  have hB'i : ∀ i j, (Matrix.transpose (Q.map σ) * B * Q) i j ∈ Formalism.UG.intL L :=
    mul_int (mul_int (star_int hv hQ) hB) hQ
  have h1 : Matrix.transpose (Q'.map σ) * Matrix.transpose (Q.map σ) = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hQQ', Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]
  have hA'B' : (Q' * A * Matrix.transpose (Q'.map σ)) * (Matrix.transpose (Q.map σ) * B * Q) = 1 := by
    calc (Q' * A * Matrix.transpose (Q'.map σ)) * (Matrix.transpose (Q.map σ) * B * Q)
        = Q' * A * (Matrix.transpose (Q'.map σ) * Matrix.transpose (Q.map σ)) * B * Q := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, Matrix.mul_assoc Q' A B, hAB, Matrix.mul_one, hQ'Q]
  have hAm : A.map σ = Matrix.transpose A := by ext i j; simp [hAh]
  have hQm : (Q'.map σ).map σ = Q' := by ext i j; simp [hσ]
  have hA'h : ∀ i j, σ ((Q' * A * Matrix.transpose (Q'.map σ)) i j) = (Q' * A * Matrix.transpose (Q'.map σ)) j i := by
    have hm : (Q' * A * Matrix.transpose (Q'.map σ)).map σ = Matrix.transpose (Q' * A * Matrix.transpose (Q'.map σ)) := by
      have hQt : (Matrix.transpose (Q'.map σ)).map σ = Matrix.transpose Q' := by ext i j; simp [hσ]
      rw [Matrix.map_mul, Matrix.map_mul, hAm, hQt]
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    intro i j
    have := congrFun (congrFun hm i) j
    simpa using this
  have hy := GlobalTheory.T.phaseCondition_integral_basisChange L σ δ n n' A ψ P Q Q' hσ hv hP hQ' hQQ' x hx
  have hD := GlobalTheory.T.phaseCondition_sub_integral_matrix L ϖ σ q δ n n' _ ψ hU hq hA'i hδ.1 hδ.2 hpi (P * x * Q) _ hE hy
  rw [sub_sub_cancel] at hD
  obtain ⟨l', hl', hG⟩ := GlobalTheory.T.completeSquare_diagonalNegPowUniformizer L ϖ σ q δ n n' _ _ ψ hU hq hA'i hB'i hA'B' hA'h hδ hpi hne a hD
  refine ⟨P' * ((P * x * Q - (Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0))) + l') * Q', ?_, ?_⟩
  · intro i j
    exact mul_int (mul_int hP' (fun i j => add_mem (hE i j) (hl' i j))) hQ' i j
  · have hxe : x - P' * ((P * x * Q - (Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0))) + l') * Q' = P' * ((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) - l') * Q' := by
      have hx0 : x = P' * (P * x * Q) * Q' := by
        simp only [Matrix.mul_assoc, hQQ', Matrix.mul_one]
        rw [← Matrix.mul_assoc, hP'P, Matrix.one_mul]
      rw [show x - P' * ((P * x * Q - (Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0))) + l') * Q' = P' * (P * x * Q) * Q' - P' * ((P * x * Q - (Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0))) + l') * Q' from by rw [← hx0]]
      have hab : P * x * Q - ((P * x * Q - (Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0))) + l') = (Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) - l' := by abel
      rw [← Matrix.sub_mul, ← Matrix.mul_sub, hab]
    rw [hxe]
    have hg : (P' * ((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) - l') * Q') * A * Matrix.transpose ((P' * ((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) - l') * Q').map σ) =
        P' * (((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) - l') * (Q' * A * Matrix.transpose (Q'.map σ)) * Matrix.transpose (((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) - l').map σ)) * Matrix.transpose (P'.map σ) := by
      simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [hg]
    exact mul_int (mul_int hP' hG) (star_int hv hP')

end GlobalTheory.Hk3.HoweDuality.Square

theorem GlobalTheory.Hk3.HoweDuality.exists_int_gram_of_phases : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (ψ : AddChar L ℂ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (Valued.v δ = 1 ∧ σ δ = -δ) → (∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1) →
    (∃ a ∈ Formalism.UG.intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) → ∀ x : Matrix (Fin n') (Fin n) L,
    (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
    (∀ i j, (C * x) i j ∈ Formalism.UG.intL L) →
    ψ ((δ * Matrix.trace (C * (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ))) + σ (δ * Matrix.trace (C * (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ))))) / 2) = 1) →
    ∃ l ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n,
      ∀ i j, ((x - l) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose ((x - l).map σ)) i j ∈ Formalism.UG.intL L := by
  intro L _ _ _ ϖ σ q δ n n' JS ψ hU hq hJS hJh hδ hpi hne x hx
  have hσ : ∀ x, σ (σ x) = x := hU.1
  have glint_entry : ∀ {g : GL (Fin n) L}, g ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → ∀ i j,
      (g : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
    intro g hg i j
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hg
    exact (k.val i j).2
  have hJi : (JS⁻¹ : GL (Fin n) L) ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) := Subgroup.inv_mem _ hJS
  set P : Matrix (Fin n) (Fin n) L := ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hPdef
  have hSm : (JS : Matrix (Fin n) (Fin n) L).map σ = Matrix.transpose (JS : Matrix (Fin n) (Fin n) L) := by
    ext i j; simp [hJh]
  have hPJ : P * (JS : Matrix (Fin n) (Fin n) L) = 1 := by rw [hPdef]; exact JS.inv_mul
  have hJP : (JS : Matrix (Fin n) (Fin n) L) * P = 1 := by rw [hPdef]; exact JS.mul_inv
  have e1 : P.map σ * Matrix.transpose (JS : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [← hSm, ← Matrix.map_mul, hPJ]; exact Matrix.map_one σ (map_zero σ) (map_one σ)
  have e2 : (JS : Matrix (Fin n) (Fin n) L) * Matrix.transpose (P.map σ) = 1 := by
    have := congrArg Matrix.transpose e1
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  have e3 : Matrix.transpose (P.map σ) = P := by
    calc Matrix.transpose (P.map σ) = (P * (JS : Matrix (Fin n) (Fin n) L)) * Matrix.transpose (P.map σ) := by
          rw [hPJ, Matrix.one_mul]
      _ = P := by rw [Matrix.mul_assoc, e2, Matrix.mul_one]
  have hPh : ∀ i j, σ (P i j) = P j i := by
    intro i j
    have := congrFun (congrFun e3 j) i
    simpa using this
  exact GlobalTheory.Hk3.HoweDuality.Square.gen hU hq (glint_entry hJi) (glint_entry hJS) hPJ hPh hδ hpi hne x hx
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.parts_adjoint_intertwiner_eq_joint_eigenspaces : ∀ {X E I : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (Θ : X →ₗ[ℂ] E) (op : I → Module.End ℂ X) (h : I → Module.End ℂ E), ∀ {C : Type} (Ec : C → Submodule ℂ E) (lab : C → I → ℂ), (∀ i u, Θ (op i u) = h i (Θ u)) → (∀ i, Commute (op i) (LinearMap.adjoint (op i))) → (∀ i, Commute (h i) (LinearMap.adjoint (h i))) → Formalism.L2.Col.PairComm op → (⨆ c, Ec c) = ⊤ → (∀ c, ∀ w ∈ Ec c, ∀ i, h i w = lab c i • w) → (∀ c, Ec c ≠ ⊥ → ∃ w ∈ Ec c, LinearMap.adjoint Θ w ≠ 0) → Formalism.L2.Col.PairComm h ∧ ∀ Q : (I → ℂ) → Prop, (∀ c, Ec c ≠ ⊥ → ((Ec c).map (LinearMap.adjoint Θ) ≤ Formalism.L2.Col.eigSum op Q ↔ Q (lab c))) ∧ (⨆ (c : C) (_ : Ec c ≠ ⊥ ∧ (Ec c).map (LinearMap.adjoint Θ) ≤ Formalism.L2.Col.eigSum op Q), Ec c) = Formalism.L2.Col.eigSum h Q := by
  first | exact @GlobalTheory.Hk3.parts_of_adjoint_lift | exact GlobalTheory.Hk3.parts_of_adjoint_lift | (intros; apply GlobalTheory.Hk3.parts_of_adjoint_lift <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory

theorem smul_dualSet_latAd_mem {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E)
    (hco : ∃ co, IsOrthCo (sp.cm.sig : E →+* E) J co) (T : ℕ) (Lb : Submodule (𝓞 E) (Fin N → E)) (hT : 0 < T)
    (hLb : Formalism.L2.GlobalTheoryTheory.Comp.IsLat Lb)
    (hdual : ∀ z ∈ dualSet (sp.cm.sig : E →+* E) J Lb, (T : E) • z ∈ Lb)
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hy : y ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F))
    (z : Fin N → E) (hz : z ∈ dualSet (sp.cm.sig : E →+* E) J (latAd y Lb)) :
    (T : E) • z ∈ latAd y Lb := by
  have hlat : latAd y Lb = Formalism.UG.CS.globLat y Lb := Submodule.span_eq (Formalism.UG.CS.globLat y Lb)
  set a : 𝓞 E := (T : 𝓞 E) with ha
  have ha0 : a ≠ 0 := by
    rw [ha]; exact_mod_cast hT.ne'
  have hsm : ∀ w : Fin N → E, a • w = (T : E) • w := by
    intro w
    rw [← algebraMap_smul E a w, ha, map_natCast]

  have hdl : ∀ w ∈ Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J Lb, a • w ∈ Lb := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => rw [hsm]; exact hdual w hw
    | zero => rw [smul_zero]; exact zero_mem _
    | add u v _ _ hu hv => rw [smul_add]; exact add_mem hu hv
    | smul c w _ hw => rw [smul_comm]; exact Lb.smul_mem c hw
  have hle : Ideal.span {a} • Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J Lb ≤ Lb := by
    refine Submodule.smul_le.2 fun r hr w hw => ?_
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [mul_smul]
    exact Lb.smul_mem c (hdl w hw)

  have hz' : z ∈ Formalism.UG.CS.globLat y (Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J Lb) := by
    rw [Formalism.L2.GlobalTheoryTheory.Comp.glob_dl sp.cm.sig J (GlobalTheory.isLat_dl_of_isOrthCo sp J hco) hLb y hy]
    rw [hlat] at hz
    exact Submodule.subset_span hz
  have h1 : a • z ∈ Ideal.span {a} • Formalism.UG.CS.globLat y (Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J Lb) :=
    Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) hz'
  have h2 := Formalism.L2.GlobalTheoryTheory.Comp.glob_mono y hle
    (Formalism.L2.GlobalTheoryTheory.Comp.smul_glob_le _ a y h1)
  rw [hlat, ← hsm]
  exact h2

end GlobalTheory
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitStab

section Alg

variable {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A)

theorem hform_eq (x y : Fin n → A) :
    Formalism.UG.hform σ J x y = dotProduct (fun i => σ (x i)) (J.mulVec y) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_smul_left (a : A) (x y : Fin n → A) :
    Formalism.UG.hform σ J (fun i => a * x i) y = σ a * Formalism.UG.hform σ J x y := by
  simp only [hform_eq, dotProduct, map_mul, Finset.mul_sum, mul_assoc]

theorem hform_smul_right (a : A) (x y : Fin n → A) :
    Formalism.UG.hform σ J x (fun i => a * y i) = a * Formalism.UG.hform σ J x y := by
  have : (fun i => a * y i) = a • y := rfl
  rw [hform_eq, hform_eq, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hform_mulVec {g : Matrix (Fin n) (Fin n) A} (hg : Formalism.UG.cT σ g * J * g = J) (x y : Fin n → A) :
    Formalism.UG.hform σ J (g.mulVec x) (g.mulVec y) = Formalism.UG.hform σ J x y := by
  have e : (fun i => σ (g.mulVec x i)) = Matrix.vecMul (fun i => σ (x i)) (Formalism.UG.cT σ g) := by
    funext i

    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, map_sum, map_mul, Formalism.UG.cT, Matrix.transpose_apply,
    Matrix.map_apply, mul_comm]
  rw [hform_eq, hform_eq, e, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

theorem stab_of_half (I : AddSubgroup A) (L : AddSubgroup (Fin n → A))
    (hL : ∀ y, y ∈ L ↔ ∀ z ∈ L, Formalism.UG.hform σ J z y ∈ I) {p : A}
    (hp : ∀ y ∈ L, (fun i => p * y i) ∈ L) (hq : ∀ y ∈ L, (fun i => σ p * y i) ∈ L)
    {g : Matrix (Fin n) (Fin n) A} (hg : Formalism.UG.cT σ g * J * g = J)
    (hs : ∀ i j, (p + σ p) * (g - 1) i j = (g - 1) i j)
    (h1 : ∀ y ∈ L, (fun i => p * g.mulVec y i) ∈ L)
    (h2 : ∀ y ∈ L, ∃ z ∈ L, (fun i => p * y i) = fun i => p * g.mulVec z i) (y : Fin n → A) :
    y ∈ L ↔ g.mulVec y ∈ L := by
  have fwd : ∀ y ∈ L, g.mulVec y ∈ L := by
    intro y hy
    have hc : (fun i => σ p * g.mulVec y i) ∈ L := by
      refine (hL _).2 fun z hz => ?_
      obtain ⟨z', hz', e⟩ := h2 z hz
      rw [hform_smul_right, ← hform_smul_left, e, hform_smul_left, hform_mulVec σ J hg, ← hform_smul_right]
      exact (hL _).1 (hq y hy) z' hz'
    have hs' : (p + σ p) • (g - 1) = g - 1 := Matrix.ext hs
    have e : (p + σ p) • (g.mulVec y - y) = g.mulVec y - y := by
      have := congrArg (fun m => Matrix.mulVec m y) hs'
      simpa only [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec] using this
    have e2 : g.mulVec y = y + ((fun i => p * g.mulVec y i) + (fun i => σ p * g.mulVec y i) -
        (fun i => p * y i) - fun i => σ p * y i) := by
      funext i
      have := congrFun e i
      simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul] at this ⊢
      linear_combination -this
    rw [e2]
    exact add_mem hy (sub_mem (sub_mem (add_mem (h1 y hy) hc) (hp y hy)) (hq y hy))
  refine ⟨fwd y, fun hy => (hL _).2 fun z hz => ?_⟩
  rw [← hform_mulVec σ J hg]
  exact (hL _).1 hy _ (fwd z hz)

theorem supp_map {B : Type} [CommRing B] (φ : A →+* B) {f : A} {g : Matrix (Fin n) (Fin n) A}
    (hs : ∀ i j, f * (g - 1) i j = (g - 1) i j) (i j : Fin n) :
    φ f * (g.map φ - 1) i j = (g.map φ - 1) i j := by
  have e : (g.map φ - 1) i j = φ ((g - 1) i j) := by
    rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [e, ← map_mul, hs]

end Alg

variable {D : D7}

theorem finPart_conj (x : Formalism.L2.Theta.AE D) :
    finPart D (cA D x) = sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a e => rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]

theorem finMat_unitary (V : HSp D) (g : GA D V) :
    Formalism.UG.cT (sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig) (finMat D.sp.cm.sig V.gram g) *
      JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) V.gram * finMat D.sp.cm.sig V.gram g =
      JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) V.gram := by
  have h : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mt V g) * JR (AF D.host.F) V.gram * mt V g =
      JR (AF D.host.F) V.gram := g.2
  have h2 := congrArg (fun m => Matrix.map m (finPart D)) h
  simp only [Matrix.map_mul] at h2
  have e1 : (JR (AF D.host.F) V.gram).map (finPart D) = JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) V.gram := rfl
  have e2 : (mt V g).map (finPart D) = finMat D.sp.cm.sig V.gram g := rfl
  have e3 : (Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mt V g)).map (finPart D) =
      Formalism.UG.cT (sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig) (finMat D.sp.cm.sig V.gram g) := by
    ext i j
    exact finPart_conj _
  rwa [e1, e2, e3] at h2

theorem mem_ksph_of_split : ∀ {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D) (g : GA D V), IsSplitIdem D e → Formalism.L2.Theta.SuppAt e V g → (∀ y ∈ LamHat V, (fun a => finPart D e * (finMat D.sp.cm.sig V.gram g).mulVec y a) ∈ LamHat V) → (∀ y ∈ LamHat V, ∃ z ∈ LamHat V, (fun a => finPart D e * y a) = fun a => finPart D e * (finMat D.sp.cm.sig V.gram g).mulVec z a) → g ∈ KsphC V ∅ := by
  intro D V e g he hs h1 h2
  obtain ⟨hd, hm⟩ := GlobalTheory.LatDual.lamHat_selfDual_and_module V
  obtain ⟨i1, -, v, ε, ⟨α, rfl, -⟩, h4⟩ := he
  have hp : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, i1])
  have hq : sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig (finPart D e) ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ← RingHom.map_mul, i1])
  refine ⟨?_, ?_, fun v hv => absurd hv (Finset.notMem_empty v)⟩
  · have h5 : infPart D (e + cA D e) = 0 := by
      rw [h4]
      exact TensorProduct.zero_tmul _ _
    refine Units.ext (Matrix.ext fun i j => ?_)
    have h6 := congrArg (infPart D) (hs i j)
    rw [RingHom.map_mul, h5, zero_mul, Matrix.sub_apply, RingHom.map_sub] at h6
    have h7 : infPart D (mt V g i j) = infPart D ((1 : Matrix _ _ (Formalism.L2.Theta.AE D)) i j) :=
      sub_eq_zero.1 h6.symm
    refine h7.trans ?_
    rw [Units.val_one, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · exact RingHom.map_one _
    · exact RingHom.map_zero _
  · refine stab_of_half (sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig)
      (JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) V.gram) (intAE D) (LamHat V) hd (p := finPart D e)
      (hm _ hp) (hm _ hq) (finMat_unitary V g) (fun i j => ?_) h1 h2
    rw [← finPart_conj, ← RingHom.map_add (f := _)]
    exact supp_map (finPart D) hs i j

end GlobalTheory.SplitStab
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem thetaUp_injective_on_carried : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.PThmB → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → ∀ p c, R.Carries p c → ∀ w ∈ R.EEc c, w ≠ 0 → LinearMap.adjoint (R.Th A3.A.μ0) w ≠ 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hB hP p c hc w hw hw0 hadj
  have hwp : w ∈ R.EEp3 p := by
    unfold RealDat3.EEp3
    exact (le_iSup₂ (f := fun (c : Pl D.host.E → List ℤ → ℂ) (_ : R.Carries p c) => R.EEc c) c hc) hw
  have h := hB A3.A.μ0 p w hwp
  rw [LinearMap.comp_apply, hadj, map_zero] at h
  have hpos : 0 < R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.μ0 j p := by
    refine mul_pos hP.1 (Finset.prod_pos fun j _ => ?_)
    unfold RealDat3.lamN
    split_ifs
    · exact hP.2 _ _ _
    · exact one_pos
  have hne : (((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.μ0 j p : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast hpos.ne'
  exact hw0 ((smul_eq_zero.1 h.symm).resolve_left hne)

end GlobalTheory
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H NumberField IsDedekindDomain Classical

namespace GlobalTheory.KerFinEntire

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem differentiable_opU (H : Sesq V) {F : V → ℂ} (hF : Differentiable ℂ F) (x : V) :
    Differentiable ℂ (opU H x F) := by
  have h : Differentiable ℂ fun z => H z x := (LinearMap.toContinuousLinearMap (H.flip x)).differentiable
  unfold opU
  fun_prop

theorem differentiable_sumU (H : Sesq V) (α : V → ℂ) (S : Finset V) {F : V → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (sumU H α S F) := by
  unfold sumU
  exact Differentiable.fun_sum fun x _ => (differentiable_opU H hF x).const_mul _

theorem differentiable_xiL (H : Sesq V) (α : V → ℂ) (vol : ℝ) (SX SA SB : Finset V) (Φ : V → ℂ) {e : V → ℂ}
    (he : Differentiable ℂ e) : Differentiable ℂ (xiL H α vol SX SA SB Φ e) := by
  unfold xiL xiS
  exact Differentiable.fun_sum fun x _ => (differentiable_opU H (differentiable_sumU H _ SB he) x).const_mul _

end General

theorem differentiable_thC {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ}
    (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ) (AA0 : Submodule (𝓞 E) E) (SS : Finset (HeightOneSpectrum (𝓞 E)))
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (c : ℕ) (Ξ : HomE E a b → ℂ) {θ : VV ι a b → ℂ}
    (hθ : Differentiable ℂ θ) : Differentiable ℂ (thC emb δ d sc AA0 SS N N' c Ξ θ) := by
  unfold thC xiV
  exact differentiable_xiL _ _ _ _ _ _ _ hθ

theorem kerFin_entire : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ), s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → ∀ (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') → ∀ (SS : Finset (HeightOneSpectrum (𝓞 X.E))) (c : ℕ) (Ξ : HomE X.E a b → ℂ), Differentiable ℂ (thC (X.embC (ambOf s B χ cD : Amb X).σ₀) (ambOf s B χ cD : Amb X).δ (ambOf s B χ cD : Amb X).d (ambOf s B χ cD : Amb X).sc (ambOf s B χ cD : Amb X).AA SS N N' c Ξ ((ambOf s B χ cD : Amb X).e a b N N')) := by
  intro D X s cc δ B χ cD _ hcc hδ hχ a b N N' hA SS c Ξ
  have hE : Differentiable ℂ (B.eNat χ a b (s.lat N) (s.lat N')) :=
    (B.vec_mem_ne hcc hδ (Formalism.L2.Ker.KS.Lat.delta_ne hcc hδ) (B.stdOK hcc hδ) χ hχ a b _ _ hA).1.1
  let T : VCx X.Tau a b →L[ℂ] TaylorLogMetric.VC D a b := ContinuousLinearMap.pi fun τ => ContinuousLinearMap.proj (s.iT.symm τ)
  have he : Differentiable ℂ ((ambOf s B χ cD : Amb X).e a b N N') := hE.comp T.differentiable
  exact differentiable_thC _ _ _ _ _ _ _ _ _ _ he

end GlobalTheory.KerFinEntire
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.Host GlobalTheory.KerJ NumberField Classical

theorem _root_.GlobalTheory.T.padic_norm_det_lattice_basis_eq_det_ideal_norm : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) (N : ℕ) (L0 L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (B : Matrix (Fin N) (Fin N) ℂ_[p]), (∀ x, x ∈ L0 ↔ ∀ k, IsIntegral ℤ (x k)) → B.det ≠ 0 → (∀ x ∈ L, ∀ a, ‖(B⁻¹.mulVec fun i => tauEmb D lam τ (x i)) a‖ ≤ 1) → (∀ a, ∃ (n : ℕ) (r : Fin n → ℂ_[p]) (x : Fin n → Fin N → D.host.E), (∀ k, ‖r k‖ ≤ 1) ∧ (∀ k, x k ∈ L) ∧ ∀ i, B i a = ∑ k, r k * tauEmb D lam τ (x k i)) → ‖B.det‖ = nrmId D lam τ (detId D L0 L) := by
  first | exact @GlobalTheory.DetBasisNorm.norm_det_eq_nrmId | exact GlobalTheory.DetBasisNorm.norm_det_eq_nrmId | (intros; apply GlobalTheory.DetBasisNorm.norm_det_eq_nrmId <;> assumption)
end
