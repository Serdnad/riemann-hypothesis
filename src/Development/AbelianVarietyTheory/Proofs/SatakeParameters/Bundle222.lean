module

public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle214
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Formalism.LocalToGlobal.GlobalTheory.GL3.PIopIso
public import Formalism.LocalToGlobal.GlobalTheory.GL3.ProvisionExtensionLink
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle005
public import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle095
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle212
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle018
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.LocalToGlobal.InertKernelTheory.Bundle009
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.LtCNeZero
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.NrmAMemAdForms
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle002
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.LocalToGlobal.KernelLattices.Bundle001
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle001
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory

theorem intOff_finset_prod {S : Finset ℕ} {κ : Type} (s : Finset κ) (f : κ → ℂ) (h : ∀ k ∈ s, IntOff S (f k)) :
    IntOff S (∏ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (IntOff.one : IntOff S 1)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem xiCpl1_intOff : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → ∀ u μ, (∀ k, D.host.g k ∉ Y.Qp μ) → ∀ al p₀ p Yb x, IntOff (t.O u μ).S (t.seam.σ₀ (XiCpl1 (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 al p₀ p Yb x)) := by
  intro D L hT Gi Gl K Y cX ex t h1 h2 u μ hQ al p₀ p Yb x
  have hm : t.m2 < D.R.m := by have := (t.idx_ok μ).hm; omega
  unfold XiCpl1
  rw [map_mul, map_prod]
  refine IntOff.mul ?_ (intOff_finset_prod _ _ fun P _ => ?_)
  · unfold phiT
    split_ifs
    · rw [map_one]; exact IntOff.one
    · rw [map_zero]; exact IntOff.zero
  · unfold PsiAt
    first
    | exact GlobalTheory.T.integralAwayFrom_moved_localDatum D L hT Gi Gl K Y cX ex t h1 h2 u μ hQ t.m2 hm P _ 1
        (fun hP => ⟨(t.idx_ok μ).stabG t.m2 al P hP, one_mem _⟩) _
    | exact GlobalTheory.T.integralAwayFrom_moved_localDatum D L hT Gi Gl K Y cX ex t h1 h2 u μ t.m2 hm P _ 1
        (fun hP => ⟨(t.idx_ok μ).stabG t.m2 al P hP, one_mem _⟩) _

end GlobalTheory
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.translate_entire_algebraic : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → ∀ (a b : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), TaylorLogMetric.admitted D a b N N' → ∀ s : TaylorLogMetric.VC D a b, (∃ m : ℕ, 0 < m ∧ m • s ∈ TaylorLogMetric.La D B.tor N N') → Differentiable ℂ (TaylorLogMetric.U D B.tor s (B.eNat χ a b N N')) ∧ TaylorLogMetric.CoefIn D (TaylorLogMetric.U D B.tor s (B.eNat χ a b N N')) TaylorLogMetric.Qbar := by
  intro D cc δ B χ hc hδ hχ a b N N' hA s hs
  obtain ⟨h1, -⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.vector_bound_link D cc hc δ hδ B χ hχ a b N N' hA
  exact ⟨Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.U_diff _ s h1.1, fun α => GlobalTheory.ThLoc.algTAll D cc δ B χ hc hδ hχ a b N N' hA s hs α⟩
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.BlockWindow

theorem jointTB_iff_jointCond (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (M0 h0 cB : ℕ) :
    JointTB D HW F i r π M0 h0 cB ↔ JointConditionTameBound D HW F i r π M0 h0 cB := by
  constructor
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun w hw => ?_⟩
    obtain ⟨a, b, c⟩ := h w hw
    exact ⟨a, b, fun C hs Y hc hY => c C.LL C.le hs Y hc hY⟩
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun w hw => ?_⟩
    obtain ⟨a, b, c⟩ := h w hw
    exact ⟨a, b, fun CL hL hs Y hc hY => c ⟨CL, hL⟩ hs Y hc hY⟩

theorem jointCond_TB_at_range (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (large₂ : SizeData₂ D)
    (hJ : AdmissibleParameterJ.JumpConditions large₂) (hA : EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (cB : ℕ)
    (h2 : D.nd.l i ∉ D.host.small) (hq : D.nd.l i ≠ D.host.q) (hd : D.nd.l i ≠ D.host.d) (hG : GoodR D.nd i r)
    (hc : GlobalTheory.HubLoc.cBnum (D.nd.l i) ⌊2 * large₂.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV) ≤ cB) :
    ∃ M0 h0 : ℕ, JointConditionTameBound D HW F i r π M0 h0 cB := by
  obtain ⟨ht, hW⟩ := GlobalTheory.T.hodgeTateJumpWindow_of_jumpSets D large₂ hJ hA
  have hT := GlobalTheory.T.jumpWindowBlockExponentCondition_of_jumpWindow D HW F i r π ⌊2 * large₂.sc.b⌋₊ h2 hq hd ht (hW i r hG π)
  exact ⟨_, _, (jointTB_iff_jointCond D HW F i r π _ _ _).1 (hT.mono hc)⟩

end GlobalTheory.BlockWindow

end
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwU.MuUnr

theorem exists_pow_eq_span {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ (n : ℕ) (s : 𝓞 F), 0 < n ∧ v.asIdeal ^ n = Ideal.span {s} := by
  classical
  have hv : v.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero v.ne_bot
  set n := Fintype.card (ClassGroup (𝓞 F)) with hn
  have hvn : v.asIdeal ^ n ∈ nonZeroDivisors (Ideal (𝓞 F)) := pow_mem hv n
  have e : (⟨v.asIdeal ^ n, hvn⟩ : nonZeroDivisors (Ideal (𝓞 F))) = ⟨v.asIdeal, hv⟩ ^ n := Subtype.ext (by simp)
  have h1 : ClassGroup.mk0 ⟨v.asIdeal ^ n, hvn⟩ = 1 := by
    rw [e, map_pow]
    exact pow_card_eq_one
  obtain ⟨s, hs⟩ := ((ClassGroup.mk0_eq_one_iff hvn).1 h1).principal
  exact ⟨n, s, Fintype.card_pos, hs⟩

end GlobalTheory.TwU.MuUnr

namespace GlobalTheory.TwU.MuUnr

open GlobalTheory.Mem.Col2 (afIso afIso_tmul_one mem_rInt_iff)

end GlobalTheory.TwU.MuUnr

namespace GlobalTheory.TwU.MuUnr

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

end GlobalTheory.TwU.MuUnr

namespace GlobalTheory.TwU

open GlobalTheory.Mem.Col2 (afIso afIso_tmul_one mem_rInt_iff)
open GlobalTheory.TwU.MuUnr

end GlobalTheory.TwU
end
end
