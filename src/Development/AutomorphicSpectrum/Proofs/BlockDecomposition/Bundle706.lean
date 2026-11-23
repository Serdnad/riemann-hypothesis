module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle700
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle502
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle795
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTensorProductHasFiniteLength
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle505
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle509
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle319
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle631
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle702
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle048
import GroundTheory.LocalFields.PadicLogSeries
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle703
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.HeisSch
public import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.GramMatrixAdjoint
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle137
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle340
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertie
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZarhinDualPolarisation.FlatFiniteFibres.FlatOfFibresFinite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle432
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet

@[expose] public section

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.schwartz_lattice_sum_bounded : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (φ : Mx D m n → ℂ), φ ∈ schwartzA θ m n →
    Continuous φ ∧ ∃ B : ℝ≥0, ∀ w : Mx D m n, ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ‖φ (rat ξ + w)‖ₑ ≤ B := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.schwartzA_continuous_and_tsum_enorm_le | exact GlobalTheory.CompanionTheory.EisUnfold.schwartzA_continuous_and_tsum_enorm_le | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.schwartzA_continuous_and_tsum_enorm_le <;> assumption)
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem sh_mul_nzx {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (y : Mx D ρ p)
    (z : hermA D ρ) (x : Mx D ρ p) :
    M.sh y * M.nzx z x = M.nzx (z + GlobalTheory.CompanionTheory.FJE.jc y x) x * M.sh y := by
  apply GlobalTheory.CompanionTheory.FourierN.mat_injective
  rw [GlobalTheory.CompanionTheory.PcB.mat_mul', GlobalTheory.CompanionTheory.PcB.mat_mul',
    M.nzx_mat, M.nzx_mat, M.sh_mat]
  simp only [blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]
  simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]
  congr 2
  simp only [jc]
  congr 2
  rw [Matrix.mul_neg]
  change z.1 + y * adj x = (z.1 + (y * adj x + x * adj y)) + -(x * adj y)
  abel

end GlobalTheory.CompanionTheory.FJE
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem rat_maps_mem_GF : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn),
    (∀ ξ : Matrix (Fin ρ) (Fin p) D.host.E, M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) ∈ GF D n) ∧
    (∀ ξ : Matrix (Fin ρ) (Fin p) D.host.E, M.nzx 0 (GlobalTheory.CompanionTheory.FJE.rt ξ) ∈ GF D n) ∧
    ∀ z ∈ ratHerm D ρ, M.nzx z 0 ∈ GF D n := by
  intro D n ρ p hn M
  refine ⟨fun ξ => GlobalTheory.CompanionTheory.PcB.sh_rat M ξ, fun ξ => GlobalTheory.CompanionTheory.PcB.nzx_rat M 0 (zero_mem _) ξ, fun z hz => ?_⟩
  have h := GlobalTheory.CompanionTheory.PcB.nzx_rat M z hz 0
  rwa [GlobalTheory.CompanionTheory.PcB.rat_zero'] at h

end GlobalTheory.CompanionTheory.FJE
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integrable_theta_kernel_product : IkSch → Dom → OrbFin → Shift → IkLint → Fub4 → JnBl → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) θ, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E), x₀.det ≠ 0 → ∀ Φ ∈ schwartzA θ B.rank n, ∀ η ∈ schwartzA θ W.rank t, Integrable (core hn I x₀ Φ η) (I.νK.prod (Q0 I μ)) := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.integrable_core | exact GlobalTheory.CompanionTheory.ColumnSplitting.integrable_core | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.integrable_core <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.invariance_of_constant_fourier_coefficient : ∀ (D : D7) (p : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (nb : hermA D p → G D p) (lam : Measure (hermA D p)) (𝓖 : Set (hermA D p)), CoefData (D := D) (n := p) nb lam 𝓖 → ∀ (F : G D p → ℂ), Continuous F → LeftInv (GF D p) F → ∀ β : HermE D p, β.1 = 0 → (∀ g, fc ψ lam 𝓖 nb F β g = F g) → ∀ (b : hermA D p) (g : G D p), F (nb b * g) = F g := by
  first | exact @GlobalTheory.CompanionTheory.ConstN.nb_inv_of_const | exact GlobalTheory.CompanionTheory.ConstN.nb_inv_of_const | (intros; apply GlobalTheory.CompanionTheory.ConstN.nb_inv_of_const <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspPair

section General

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem apply_mem_twKer {σ : Representation ℂ G V} {τ : Representation ℂ G W} (q : σ.IntertwiningMap τ)
    (H : Subgroup G) (χ : H →* ℂˣ) {v : V} (hv : v ∈ twKer σ H χ) : q v ∈ twKer τ H χ := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, u, rfl⟩ := hx
    refine Submodule.subset_span ⟨n, q u, ?_⟩
    rw [map_sub, map_smul, q.isIntertwining]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem exists_subquotient_subsingleton [TopologicalSpace G] [IsTopologicalGroup G] (π : Representation ℂ G V)
    (H : Subgroup G) (χ : H →* ℂˣ) (hs : IsSmooth π) (hf : HasFiniteLength π) (hn : ¬ π.IsIrreducible)
    (h1 : Module.finrank ℂ (TwJacquet π H χ) = 1)
    (hr : ∀ (S : Subrepresentation π) (v : S.toSubmodule), (v : V) ∈ twKer π H χ → v ∈ twKer S.toRepresentation H χ) :
    ∃ τ : IrrRep G, IsSubquotient τ.ρ π ∧ Subsingleton (TwJacquet τ.ρ H χ) := by
  have hq1 : Nontrivial (TwJacquet π H χ) := Module.nontrivial_of_finrank_pos (R := ℂ) (by omega)
  have hV : Nontrivial V := (Submodule.mkQ_surjective (twKer π H χ)).nontrivial
  have hbt : (⊥ : Subrepresentation π) ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hmem : x ∈ (⊤ : Subrepresentation π).toSubmodule := Submodule.mem_top
    rw [← h] at hmem
    exact hx ((Submodule.mem_bot ℂ).1 hmem)
  obtain ⟨S, hS0, hST⟩ : ∃ S : Subrepresentation π, S ≠ ⊥ ∧ S ≠ ⊤ := by
    by_contra hc
    push Not at hc
    exact hn { exists_pair_ne := ⟨⊥, ⊤, hbt⟩
               eq_bot_or_eq_top := fun S => (eq_or_ne S ⊥).imp_right (hc S) }
  by_cases hSK : S.toSubmodule ≤ twKer π H χ
  · let i : S.toRepresentation.IntertwiningMap π := ⟨S.toSubmodule.subtype, fun g => rfl⟩
    have hi : Function.Injective i := Subtype.val_injective
    have hsq := IsSubquotient.of_injective i hi
    have hSn : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.2 fun h =>
      hS0 (by ext v; rw [h]; rfl)
    obtain ⟨Y, _, _, τ, hτs, hτi, q, hq⟩ := GlobalTheory.SmGL.IrrQuot.exists_irreducible_smooth_quotient S.toRepresentation
      (hsq.isSmooth hs) (GlobalTheory.ProdLength.hasFiniteLength_of_injective i hi hf) hSn
    refine ⟨⟨Y, τ, hτs, hτi⟩, ⟨S, q, hq⟩, ?_⟩
    refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun w _ => ?_)
    obtain ⟨v, rfl⟩ := hq w
    exact apply_mem_twKer q H χ (hr S v (hSK v.2))
  · obtain ⟨s, hsS, hsK⟩ := IsConcreteLE.not_le_iff_exists.1 hSK
    have hs0 : (Submodule.mkQ (twKer π H χ)) s ≠ 0 := fun h => hsK ((Submodule.Quotient.mk_eq_zero _).1 h)
    have hline := (finrank_eq_one_iff_of_nonzero' _ hs0).1 h1
    let U : Submodule ℂ V := S.toSubmodule
    have hU : ∀ g, U ≤ U.comap (π g) := fun g v hv => S.apply_mem_toSubmodule g hv
    let σ : Representation ℂ G (V ⧸ U) := π.quotient U hU
    let p : π.IntertwiningMap σ := ⟨U.mkQ, fun g => by ext v; rfl⟩
    have hp : Function.Surjective p := Submodule.mkQ_surjective U
    have hsq := IsSubquotient.of_surjective p hp
    have hUn : Nontrivial (V ⧸ U) := Submodule.Quotient.nontrivial_iff.2 fun h =>
      hST (by ext v; rw [show S.toSubmodule = ⊤ from h]; rfl)
    have hfq : HasFiniteLength σ := IsFiniteLength.of_surjective hf
      (f := Representation.IntertwiningMap.equivLinearMapAsModule π σ p) hp
    obtain ⟨Y, _, _, τ, hτs, hτi, q, hq⟩ := GlobalTheory.SmGL.IrrQuot.exists_irreducible_smooth_quotient σ
      (hsq.isSmooth hs) hfq hUn
    refine ⟨⟨Y, τ, hτs, hτi⟩, (IsSubquotient.of_surjective q hq).trans hsq, ?_⟩
    refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun w _ => ?_)
    obtain ⟨b, rfl⟩ := hq w
    obtain ⟨v, rfl⟩ := hp b
    obtain ⟨c, hc⟩ := hline (Submodule.mkQ _ v)
    have hk : v - c • s ∈ twKer π H χ := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
      exact sub_eq_zero.2 hc.symm
    have hpe : p v = p (v - c • s) := by
      have h0 : p (c • s) = 0 := (Submodule.Quotient.mk_eq_zero U).2 (U.smul_mem c hsS)
      have h2 : v = (v - c • s) + c • s := by abel
      conv_lhs => rw [h2, map_add (f := _), h0, add_zero]
    rw [hpe]
    exact apply_mem_twKer q H χ (apply_mem_twKer p H χ hk)

end General

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem finrank_twJacquet_of_isCusp (hW : WhitRankIrr k) {ψ : AddChar k Circle} (hc : Continuous ψ) (h1 : ψ ≠ 1)
    {x : IrrGL (k := k)} (hx : x.IsCusp) :
    Module.finrank ℂ (TwJacquet x.rep (unipB k (Fin x.1)) (whitChar ψ x.1)) = 1 := by
  obtain ⟨d, c⟩ := x
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by have := hx.1; simp at this; omega⟩
  have hV : Nontrivial c.rep.V := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    obtain ⟨a, b, hab⟩ := c.rep.irr.exists_pair_ne
    refine hab ?_
    ext v
    rw [Subsingleton.elim v 0]
    exact ⟨fun _ => b.toSubmodule.zero_mem, fun _ => a.toSubmodule.zero_mem⟩
  have hg : IsGenericFor ψ c.rep.ρ := GlobalTheory.T.cuspidal_is_generic k ψ hc h1 n _ c.rep.ρ hx.2 hV
  have hle := hW ψ hc h1 (n + 1) _ c.rep.ρ c.rep.smooth c.rep.irr
  haveI : Nontrivial (TwJacquet c.rep.ρ (unipB k (Fin (n + 1))) (whitChar ψ (n + 1))) := hg
  exact Module.finrank_eq_of_rank_eq (le_antisymm hle (Cardinal.one_le_iff_pos.2 rank_pos))

theorem exists_nongeneric_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    WhitRankIrr k → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (x y : IrrGL (k := k)) (N : ℕ) (hd : ∑ a, (![x, y] a).1 = N), x.IsCusp → y.IsCusp →
      ¬ (prodIrr ![x, y] hd).IsIrreducible →
      ∃ τ : IrrRep (GL (Fin N) k), IsSubquotient τ.ρ (prodIrr ![x, y] hd) ∧ ¬ IsGenericFor ψ τ.ρ := by
  intro k _ _ _ _ hW ψ hc h1 x y N hd hx hy hn
  have hcusp : ∀ a, (![x, y] a).IsCusp := Fin.forall_fin_two.2 ⟨hx, hy⟩
  have hP := GlobalTheory.CompanionTheory.WhitRank.whitRankProd_of_heredity k (GlobalTheory.T.whittaker_heredity k) ψ hc h1 2 N ![x, y] hd
  have hrank : Module.finrank ℂ (TwJacquet (prodIrr ![x, y] hd) (unipB k (Fin N)) (whitChar ψ N)) = 1 :=
    hP.trans (Finset.prod_eq_one fun a _ => finrank_twJacquet_of_isCusp hW hc h1 (hcusp a))
  have hf : HasFiniteLength (prodIrr ![x, y] hd) :=
    GlobalTheory.ProdFiniteLength.multiProd_hasFiniteLength GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k 2 N
      (fun a => (![x, y] a).1) (fun a => GlobalTheory.SplitRead.Irr.ofIrrRep (![x, y] a).2.rep) _
  have hs := isSmooth_prodIrr ![x, y] hd
  obtain ⟨τ, hτ, hsub⟩ := exists_subquotient_subsingleton (prodIrr ![x, y] hd) (unipB k (Fin N)) (whitChar ψ N) hs hf hn hrank
    fun S v hv => by
      let i : S.toRepresentation.IntertwiningMap (prodIrr ![x, y] hd) := ⟨S.toSubmodule.subtype, fun g => rfl⟩
      exact GlobalTheory.CompanionTheory.PRep.WhitExact.twKer_whitChar_reflect k ψ hc N S.toRepresentation (prodIrr ![x, y] hd)
        ((IsSubquotient.of_injective i Subtype.val_injective).isSmooth hs) hs S.toSubmodule.subtype
        Subtype.val_injective (fun g v => rfl) v hv
  exact ⟨τ, hτ, not_nontrivial_iff_subsingleton.2 hsub⟩

end Local

end GlobalTheory.CompanionTheory.CuspPair

end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.integrable_of_summable_fundamental_domain : ∀ (D : D7) (ρ : ℕ) (lz : Measure (hermA D ρ)) (𝓖 : Set (hermA D ρ)), IsCovolOneH lz 𝓖 →
  ∀ f : hermA D ρ → ℝ, Continuous f → (∀ z, 0 ≤ f z) → Summable (fun ζ : ratHerm D ρ => f ζ.1) →
  ∀ K : Set (hermA D ρ), (∀ x, ∃ γ ∈ ratHerm D ρ, γ + x ∈ K) → ∀ κ : ℝ, 0 ≤ κ →
    (∀ ζ ∈ ratHerm D ρ, ∀ z ∈ K, f (ζ + z) ≤ κ * f ζ) → Integrable f lz := by
  first | exact @GlobalTheory.CompanionTheory.HermFD.integrable_of_periodisation_bound | exact GlobalTheory.CompanionTheory.HermFD.integrable_of_periodisation_bound | (intros; apply GlobalTheory.CompanionTheory.HermFD.integrable_of_periodisation_bound <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.EisZero

open GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks (pairing gramQ mmul)

variable {D : D7} {m : ℕ}

theorem heis_zy (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {n : ℕ} (y : Mx D V.rank n) (Φ : Mx D V.rank n → ℂ)
    (z : Mx D V.rank n) : EC.Heisenberg₂ ψ V (zy y) Φ z = pairing V.gram ψ z y * Φ z := by
  have hx : xPart (zy y) = 0 := by
    ext i j
    simp only [xPart, zy, Matrix.of_apply, Equiv.symm_apply_apply, Sum.elim_inl, Matrix.zero_apply]
  have hy : yPart (zy y) = y := by
    ext i j
    simp only [yPart, zy, Matrix.of_apply, Equiv.symm_apply_apply, Sum.elim_inr]
  have hin : ∀ x : Mx D V.rank n, GlobalTheory.StdUnn.inner V x y = gramQ V.gram x y := fun x => by
    unfold GlobalTheory.StdUnn.inner gramQ mmul
    rw [Matrix.mul_assoc]
    rfl
  have h0 : GlobalTheory.StdUnn.inner V (0 : Mx D V.rank n) y = 0 := by
    simp [GlobalTheory.StdUnn.inner]
  unfold EC.Heisenberg₂
  have htr0 : GlobalTheory.StdUnn.trA (0 : AE D) = 0 := map_zero _
  rw [hx, hy, h0, add_zero, Matrix.trace_zero, halfTr, htr0, mul_zero, add_zero, hin]
  rfl

theorem pairing_add_right (T : Matrix (Fin m) (Fin m) D.host.E) (ψ : AddChar (AF D.host.F) ℂ) {n : ℕ}
    (x y y' : Mx D m n) : pairing T ψ x (y + y') = pairing T ψ x y * pairing T ψ x y' := by
  unfold pairing GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA gramQ mmul
  rw [Matrix.mul_add, Matrix.trace_add, map_add (f := _), AddChar.map_add_eq_mul]

theorem continuous_pairing (T : Matrix (Fin m) (Fin m) D.host.E) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsCharAF D.host.F ψ) {n : ℕ} (x : Mx D m n) : Continuous (pairing T ψ x) := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.TowerRestrict.lattice_Mx D m n
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have ht : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA (D := D)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  unfold pairing gramQ mmul
  exact hψ.1.comp (ht.comp (continuous_const.matrix_mul continuous_id).matrix_trace)

theorem pairing_zero_left (T : Matrix (Fin m) (Fin m) D.host.E) (ψ : AddChar (AF D.host.F) ℂ) {n : ℕ}
    (y : Mx D m n) : pairing T ψ 0 y = 1 := by
  have h : GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.adj (0 : Mx D m n) = 0 := by
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.adj, Formalism.UG.cT]
  simp [pairing, gramQ, mmul, h, GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA]


open Classical in
theorem char_integral {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) {n : ℕ}
    {μ : Measure (Mx D V.rank n)} {𝓕 : Set (Mx D V.rank n)} (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕)
    (ξ : Matrix (Fin V.rank) (Fin n) D.host.E) :
    ∫ y in 𝓕, pairing V.gram ψ (ξ.map (incA D)) y ∂μ = if ξ = 0 then 1 else 0 := by
  obtain ⟨h1, h2⟩ := GlobalTheory.T.rationalAdelicMatrices_self_annihilator D V.rank n V.gram (isHermND_gram V) ψ hψ
  split_ifs with hξ
  · subst hξ
    have h0 : (0 : Matrix (Fin V.rank) (Fin n) D.host.E).map (incA D) = 0 := by
      ext i j
      simp
    simp only [h0, pairing_zero_left, setIntegral_const, smul_eq_mul, mul_one]
    simp [Measure.real, hμ.2.2]
  · set ξ' : Mx D V.rank n := ξ.map (incA D) with hξ'
    have hrat : ξ' ∈ ratMx D V.rank n := ⟨ξ, rfl⟩
    have hne : ξ' ≠ 0 := by
      intro h
      apply hξ
      exact Matrix.ext fun i j => incA_injective ((congrFun (congrFun h i) j).trans (map_zero (incA D)).symm)
    obtain ⟨y₀, hy₀⟩ : ∃ y₀, pairing V.gram ψ ξ' y₀ ≠ 1 := by
      by_contra hc
      push_neg at hc
      exact hne (h2 ξ' hrat hc)
    have hper : ∀ γ ∈ ratMx D V.rank n, ∀ a, pairing V.gram ψ ξ' (γ + a) = pairing V.gram ψ ξ' a := by
      intro γ hγ a
      rw [pairing_add_right, (h1 γ).2 hγ ξ' hrat, one_mul]
    have key := GlobalTheory.TowerRestrict.setIntegral_add_right hμ (pairing V.gram ψ ξ') hper y₀
    simp only [pairing_add_right, integral_mul_const] at key
    have : (∫ y in 𝓕, pairing V.gram ψ ξ' y ∂μ) * (pairing V.gram ψ ξ' y₀ - 1) = 0 := by
      rw [mul_sub, mul_one, key, sub_self]
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hy₀)


open Classical in
theorem zero : PositivityTheory.GramSchwartzFunctions.EC.Zero := by
  intro D ψ hψ θ hθ V n μ 𝓕 hμ Φ hΦ
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.TowerRestrict.lattice_Mx D V.rank n
  haveI : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  haveI i6 : DiscreteTopology (ratMx D V.rank n) := i5
  haveI i7 : SecondCountableTopology (ratMx D V.rank n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : Countable (ratMx D V.rank n) := TopologicalSpace.separableSpace_iff_countable.1
    (TopologicalSpace.SecondCountableTopology.to_separableSpace)
  haveI : Countable (Matrix (Fin V.rank) (Fin n) D.host.E) := by
    let g : Matrix (Fin V.rank) (Fin n) D.host.E → ratMx D V.rank n := fun ξ => ⟨ξ.map (incA D), ξ, rfl⟩
    have hg : Function.Injective g := by
      intro a b h
      have h' := congrArg Subtype.val h
      exact Matrix.ext fun i j => incA_injective (congrFun (congrFun h' i) j)
    exact hg.countable
  haveI : IsFiniteMeasure (μ.restrict 𝓕) :=
    isFiniteMeasure_restrict.2 (by rw [hμ.2.2]; exact ENNReal.one_ne_top)
  simp only [heis_zy]
  set F : Matrix (Fin V.rank) (Fin n) D.host.E → Mx D V.rank n → ℂ :=
    fun ξ y => pairing V.gram ψ (ξ.map (incA D)) y * Φ (ξ.map (incA D)) with hF
  have hnorm : ∀ ξ y, ‖F ξ y‖ = ‖Φ (ξ.map (incA D))‖ := by
    intro ξ y
    simp only [hF, norm_mul, pairing, hψ.2.1, one_mul]
  have hint : ∀ ξ, Integrable (F ξ) (μ.restrict 𝓕) := fun ξ =>
    (integrable_const ‖Φ (ξ.map (incA D))‖).mono'
      ((continuous_pairing V.gram hψ _).mul continuous_const).aestronglyMeasurable
      (ae_of_all _ fun y => (hnorm ξ y).le)
  have hsum : Summable fun ξ => ∫ y, ‖F ξ y‖ ∂(μ.restrict 𝓕) := by
    simp only [hnorm, integral_const, smul_eq_mul]
    have hr : (μ.restrict 𝓕).real Set.univ = 1 := by simp [Measure.real, hμ.2.2]
    simp only [hr, one_mul]
    exact GlobalTheory.SiegelWeilLitCompare.summable_rat hθ ⟨Φ, hΦ⟩
  show Φ 0 = ∫ y in 𝓕, ∑' ξ, F ξ y ∂μ
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  simp only [hF, integral_mul_const, char_integral hψ V hμ]
  rw [tsum_eq_single 0]
  · simp
  · intro b hb
    simp [hb]

end GlobalTheory.CompanionTheory.EisZero
end
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.CompanionTheory.Dblock

theorem epiOfFF : PositivityTheory.Tls2.Zar3.Ch1.EpiOfFF := by
  intro R _ A B A' l hf hs hq g₁ g₂ h
  have : EffectiveEpi l.left := inferInstance
  have : Epi l.left := inferInstance
  apply Over.OverMorphism.ext
  rw [← cancel_epi l.left]
  simpa using congrArg (fun k => k.left) h

end GlobalTheory.CompanionTheory.Dblock
end
