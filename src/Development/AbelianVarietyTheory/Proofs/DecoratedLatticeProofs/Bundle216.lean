module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Unitary.Span
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
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle006
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

@[expose] public section

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.DefFund

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

theorem exists_measurable_fundamentalDomain_subset [SecondCountableTopology G] (Γ : Subgroup G) [DiscreteTopology Γ]
    {K : Set G} (hK : IsClosed K) (hcov : ∀ x : G, ∃ γ ∈ Γ, γ * x ∈ K) (μ : Measure G) :
    ∃ S ⊆ K, MeasurableSet S ∧ IsFundamentalDomain Γ S μ := by
  classical
  have := GlobalTheory.countable_of_discrete_subgroup Γ
  obtain ⟨D, hD, hu, -⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup Γ
  obtain ⟨c, hc⟩ := exists_injective_nat Γ
  let S : Set G := K ∩ ⋃ g : Γ, ((fun y => g • y) ⁻¹' D ∩ ⋂ h : Γ, ⋂ _ : c h < c g, ((fun y => (h⁻¹ * g) • y) ⁻¹' K)ᶜ)
  have hS : ∀ y, y ∈ S ↔ y ∈ K ∧ ∃ g : Γ, g • y ∈ D ∧ ∀ h : Γ, c h < c g → (h⁻¹ * g) • y ∉ K := fun y => by
    simp only [S, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff]
  have hSm : MeasurableSet S :=
    hK.measurableSet.inter <| MeasurableSet.iUnion fun g => (measurable_const_smul g hD).inter <|
      MeasurableSet.iInter fun h => MeasurableSet.iInter fun _ => (measurable_const_smul _ hK.measurableSet).compl
  refine ⟨S, Set.inter_subset_left, hSm, IsFundamentalDomain.mk' hSm.nullMeasurableSet fun x => ?_⟩
  obtain ⟨d, hd, hdu⟩ := hu x
  have hex : ∃ n, ∃ g : Γ, c g = n ∧ (g⁻¹ * d) • x ∈ K := by
    obtain ⟨γ, hγ, h⟩ := hcov x
    refine ⟨_, d * (⟨γ, hγ⟩ : Γ)⁻¹, rfl, ?_⟩
    rw [_root_.mul_inv_rev, inv_inv, inv_mul_cancel_right]
    exact h
  obtain ⟨g, hg, hgK⟩ := Nat.find_spec hex
  refine ⟨g⁻¹ * d, (hS _).2 ⟨hgK, g, ?_, fun h hh hK' => ?_⟩, fun k hk => ?_⟩
  · rw [smul_smul, mul_inv_cancel_left]; exact hd
  · refine Nat.find_min hex (hg ▸ hh) ⟨h, rfl, ?_⟩
    rwa [smul_smul, mul_assoc, mul_inv_cancel_left] at hK'
  · obtain ⟨hkK, g', h1, h2⟩ := (hS _).1 hk
    rw [smul_smul] at h1
    have e : g' * k = d := hdu _ h1
    have ek : k = g'⁻¹ * d := by rw [← e, inv_mul_cancel_left]
    have hle : Nat.find hex ≤ c g' := Nat.find_min' hex ⟨g', rfl, ek ▸ hkK⟩
    rcases hle.eq_or_lt with h | h
    · rw [ek, hc (hg.trans h)]
    · refine (h2 g (hg ▸ h) ?_).elim
      rw [smul_smul, mul_assoc, e]
      exact hgK

end GlobalTheory.DefFund

theorem GlobalTheory.DefFund.coCpt_and_fundamentalDomain_subset_compact :
    ∀ (D : D7) (A : HSp D), HSpace.SigOK A → HSpace.IsPosDef A → ∀ m : Measure (GA D A), m.IsHaarMeasure → GlobalTheory.Unf.CoCpt A ∧ ∃ (X K : Set (GA D A)), MeasurableSet X ∧ IsFundamentalDomain (GQ A) X m ∧ IsCompact K ∧ X ⊆ K := by
  intro D A hs hp m hm
  have hc : GlobalTheory.Unf.CoCpt A := (GlobalTheory.Unf.CoCptOf.coCpt_of_isAniso_or_posDef D A).2 fun τ => by
    have h1 := hs (tauE D τ)
    rw [hp (tauE D τ)] at h1
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature h1
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  obtain ⟨K, hK, hcov⟩ := hc
  obtain ⟨X, hXK, hXm, hX⟩ := GlobalTheory.DefFund.exists_measurable_fundamentalDomain_subset (GQ A) hK.isClosed hcov m
  exact ⟨⟨K, hK, hcov⟩, X, K, hXm, hX, hK, hXK⟩

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockFin

theorem pt_finite : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T) (k : KerDat S T), x.Is → y.Is → k.Is ψ θ x y → ∀ P, IsThetaFunO ψ S T (k.pt ψ θ x y P) ∧ ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ p : ℂ, k.om (g, h) (comb ψ S T k.c k.vac) = p • comb ψ S T k.c k.vac → k.om (g, h) (k.pt ψ θ x y P) = p • k.pt ψ θ x y P := by
  intro D ψ θ hθ S T x y k _ _ hk P
  obtain ⟨χS, χT, hW⟩ := hk.weil
  have hψ : IsStdChar D ψ (-1) := hW.std
  have hvac : IsThetaFunO ψ S T k.vac := hk.vac.2.theta
  have hc : IsThetaFunO ψ S T (comb ψ S T k.c k.vac) :=
    Finset.sum_induction _ (IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add) GlobalTheory.OrientedHeis.theta_zero
      fun u hu => GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 hvac (hk.fin u hu))
  have hop : ∀ g ∈ GfC S, ∀ h ∈ GfC T,
      IsThetaFunO ψ S T (k.pt ψ θ x y P) ∧
        k.om (g, h) (k.pt ψ θ x y P) = pureTensorO ψ θ S T x.s y.s x.B y.B (k.om (g, h) (comb ψ S T k.c k.vac)) P :=
    fun g hg h hh => GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT k.om hW hθ x.s x.s x.B x.B y.s y.s y.B y.B g h
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hg, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hh, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hg, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hh, Matrix.one_mul]) _ hc P
  refine ⟨(hop 1 (one_mem _) 1 (one_mem _)).1, fun g hg h hh p hp => ?_⟩
  rw [(hop g hg h hh).2, hp, GlobalTheory.FiniteFock.pureTensorO_smul]
  rfl

end GlobalTheory.FockFin
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.CenterScalar

theorem scalar_of_comm_unitary {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 → U * C = C * U) : ∃ ζ : ℂ, C = ζ • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  open scoped Matrix.Norms.L2Operator in
  have hall : ∀ M : Matrix (Fin n) (Fin n) ℂ, M * C = C * M := by
    intro M
    have hM : M ∈ Submodule.span ℂ (unitary (Matrix (Fin n) (Fin n) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ)) := by
      rw [CStarAlgebra.span_unitary]; trivial
    induction hM using Submodule.span_induction with
    | mem U hU => exact h U hU.1
    | zero => simp
    | add a b _ _ ha hb => rw [Matrix.add_mul, Matrix.mul_add, ha, hb]
    | smul c a _ ha => rw [Matrix.smul_mul, Matrix.mul_smul, ha]
  obtain ⟨ζ, hζ⟩ := Matrix.mem_range_scalar_of_commute_single (M := C) (fun i j _ => hall _)
  exact ⟨ζ, by rw [← hζ, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩

theorem scalar_of_comm {n : ℕ} (G s B A : Matrix (Fin n) (Fin n) ℂ) (p : ℕ) (hs : s = 1 ∨ s = -1)
    (hB : IsONBasis G s B p) (hA : Aᴴ * G * A = G)
    (h : ∀ M : Matrix (Fin n) (Fin n) ℂ, Mᴴ * G * M = G → M * A = A * M) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ A = ζ • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  obtain ⟨ε, hε, h1, h2⟩ := hB
  have hdet : (Matrix.diagonal (fun a => (ε a : ℂ))).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
    rcases hε a with h | h <;> simp [h.1]
  rw [← h1, Matrix.det_mul, Matrix.det_mul] at hdet
  have hBu : IsUnit B.det := (right_ne_zero_of_mul hdet).isUnit
  have hG : G.det ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hdet)
  have i1 : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul _ hBu
  have i2 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hBu
  obtain ⟨c, hc⟩ : ∃ c : ℂ, Bᴴ * G * B = c • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have e : B⁻¹ * (s * B) = Matrix.diagonal (fun a => (ε a : ℂ)) := by
      rw [h2, ← Matrix.mul_assoc, i1, Matrix.one_mul]
    rcases hs with rfl | rfl
    · exact ⟨1, by rw [h1, ← e, Matrix.one_mul, i1, one_smul]⟩
    · exact ⟨-1, by rw [h1, ← e, Matrix.neg_mul, Matrix.one_mul, Matrix.mul_neg, i1, neg_smul, one_smul]⟩
  have hG' : (B⁻¹)ᴴ * (Bᴴ * G * B) * B⁻¹ = G := by
    calc _ = (B * B⁻¹)ᴴ * G * (B * B⁻¹) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = G := by rw [i2]; simp
  obtain ⟨ζ, hζ⟩ := scalar_of_comm_unitary (B⁻¹ * A * B) fun U hU => by
    have k := h (B * U * B⁻¹) (by
      calc _ = (B⁻¹)ᴴ * (Uᴴ * (Bᴴ * G * B) * U) * B⁻¹ := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = (B⁻¹)ᴴ * (Bᴴ * G * B) * B⁻¹ := by
            rw [hc, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU]
        _ = G := hG')
    calc U * (B⁻¹ * A * B) = (B⁻¹ * B) * U * (B⁻¹ * A * B) := by rw [i1, Matrix.one_mul]
      _ = B⁻¹ * (B * U * B⁻¹ * A) * B := by simp only [Matrix.mul_assoc]
      _ = B⁻¹ * A * B * U * (B⁻¹ * B) := by rw [k]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [i1, Matrix.mul_one]
  have hAζ : A = ζ • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    calc A = (B * B⁻¹) * A * (B * B⁻¹) := by rw [i2, Matrix.one_mul, Matrix.mul_one]
      _ = B * (B⁻¹ * A * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hζ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, i2]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, norm_one, Subsingleton.elim _ _⟩
  · refine ⟨ζ, ?_, hAζ⟩
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hG0 : G ≠ 0 := fun e => hG (by rw [e, Matrix.det_zero])
    rw [hAζ, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one, smul_smul] at hA
    have e : ζ * star ζ = 1 := by
      by_contra hne
      apply hG0
      have : (ζ * star ζ - 1) • G = 0 := by rw [sub_smul, hA, one_smul, sub_self]
      exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
    have e2 : ‖ζ‖ * ‖ζ‖ = 1 := by simpa using congrArg norm e
    nlinarith [norm_nonneg ζ]

theorem center_scalar : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (S : HSp D) (x : DefSp S), x.Is → ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → ∀ τ : D.what₂.Tau, ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ compAt θ τ (Formalism.L2.Theta.mt S z) = ζ • (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) := by
  intro D θ hθ S x hx z _ hz τ
  obtain ⟨p, hp⟩ := hx.onb τ
  refine scalar_of_comm (gramAt D S τ) (x.s τ) (x.B τ) _ p (hx.pm τ) hp
    (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ S z τ) fun M hM => ?_
  have ha := GlobalTheory.PointAtPlaceHom.atTau_spec hθ S τ (g := M) hM
  have hc := congrArg (infMat D.sp.cm.sig S.gram (θ τ)) (Subgroup.mem_center_iff.1 hz (atTau θ S τ M))
  rw [GlobalTheory.PointAtPlaceHom.infMat_mul, GlobalTheory.PointAtPlaceHom.infMat_mul, ha.2.1] at hc
  exact hc

end GlobalTheory.CenterScalar

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.BiCombStable

variable {D : D7}

theorem comb_apply (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) (w : WO S T) :
    comb ψ S T c f w = ∑ x ∈ c.support, c x * (ψ (symplOH S T w x) * f (w + x)) := by
  simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

def combL (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun := comb ψ S T c
  map_add' f g := by
    funext w
    simp only [comb_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    funext w
    simp only [comb_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring

def biCombL (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ) :
    (WO A S → WO S A' → ℂ) →ₗ[ℂ] (WO A S → WO S A' → ℂ) where
  toFun := biComb ψ A S A' c c'
  map_add' f g := by
    funext u v
    simp only [biComb, comb_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    funext u v
    simp only [biComb, comb_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Loc

end GlobalTheory.BiCombStable
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section

namespace GlobalTheory.SeeSawFold

variable {D : D7}

theorem theta_add' {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f g : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) : IsThetaFunO ψ S T (fun w => f w + g w) := {
  quasi γ w := by rw [hf.quasi, hg.quasi]; ring
  level := by
    obtain ⟨U, hU, hUf⟩ := hf.level
    obtain ⟨V, hV, hVg⟩ := hg.level
    refine ⟨U ⊓ V, hU.inter hV, fun u hu h0 => ?_⟩
    have e1 := hUf u hu.1 h0
    have e2 := hVg u hu.2 h0
    funext w
    have a1 := congrFun e1 w
    have a2 := congrFun e2 w
    simp only [heisO] at a1 a2 ⊢
    rw [mul_add, a1, a2]
  cont := hf.cont.add hg.cont
  smooth k L hL hL' w := (hf.smooth k L hL hL' w).add (hg.smooth k L hL hL' w) }

theorem theta_const_mul' {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f : WO S T → ℂ}
    (a : ℂ) (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (fun w => a * f w) := {
  quasi γ w := by rw [hf.quasi]; ring
  level := by
    obtain ⟨U, hU, hUf⟩ := hf.level
    refine ⟨U, hU, fun u hu h0 => ?_⟩
    funext w
    have a1 := congrFun (hUf u hu h0) w
    simp only [heisO] at a1 ⊢
    rw [mul_left_comm, a1]
  cont := continuous_const.mul hf.cont
  smooth k L hL hL' w := contDiff_const.mul (hf.smooth k L hL hL' w) }

theorem theta_zero' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : IsThetaFunO ψ S T (fun _ => 0) :=
  ⟨fun _ _ => by simp, ⟨⊤, isOpen_univ, fun a _ _ => by funext w; simp [heisO]⟩, continuous_const,
    fun _ _ _ _ _ => contDiff_const⟩

theorem theta_sum' {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {ι : Type*} (s : Finset ι) (F : ι → WO S T → ℂ)
    (hF : ∀ i ∈ s, IsThetaFunO ψ S T (F i)) : IsThetaFunO ψ S T (fun w => ∑ i ∈ s, F i w) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using theta_zero' ψ S T
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact theta_add' (hF i (Finset.mem_insert_self i s)) (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

section Ops

variable (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D)

def opL (a : WO A S →₀ ℂ) (C : WO A S → WO S A' → ℂ) : WO A S → WO S A' → ℂ :=
  fun u v => comb ψ A S a (fun u' => C u' v) u

def opR (b : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) : WO A S → WO S A' → ℂ :=
  fun u v => comb ψ S A' b (C u) v

theorem biComb_eq (a : WO A S →₀ ℂ) (b : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) :
    biComb ψ A S A' a b C = opL ψ A S A' a (opR ψ A S A' b C) := rfl

theorem opL_opR (a : WO A S →₀ ℂ) (b : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) :
    opL ψ A S A' a (opR ψ A S A' b C) = opR ψ A S A' b (opL ψ A S A' a C) := by
  funext u v
  simp only [opL, opR, comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, heisO, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem foldL_opR (l : List ((WO A S →₀ ℂ) × (WO S A' →₀ ℂ))) (b : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) :
    l.foldr (fun p C => opL ψ A S A' p.1 C) (opR ψ A S A' b C) =
      opR ψ A S A' b (l.foldr (fun p C => opL ψ A S A' p.1 C) C) := by
  induction l with
  | nil => rfl
  | cons p l ih => simp only [List.foldr_cons, ih, opL_opR]

theorem foldL_foldR (l : List ((WO A S →₀ ℂ) × (WO S A' →₀ ℂ))) (Y : WO A S → WO S A' → ℂ) :
    l.foldr (fun p C => opL ψ A S A' p.1 C) (l.foldr (fun p C => opR ψ A S A' p.2 C) Y) =
      l.foldr (fun p C => biComb ψ A S A' p.1 p.2 C) Y := by
  induction l with
  | nil => rfl
  | cons p l ih => simp only [List.foldr_cons, foldL_opR, ih, biComb_eq]

theorem foldR_apply (l : List ((WO A S →₀ ℂ) × (WO S A' →₀ ℂ))) (Y : WO A S → WO S A' → ℂ) (u : WO A S) :
    l.foldr (fun p C => opR ψ A S A' p.2 C) Y u = l.foldr (fun p f => comb ψ S A' p.2 f) (Y u) := by
  induction l with
  | nil => rfl
  | cons p l ih => simp only [List.foldr_cons, ← ih]; rfl

theorem foldL_apply (l : List ((WO A S →₀ ℂ) × (WO S A' →₀ ℂ))) (C : WO A S → WO S A' → ℂ) (u : WO A S)
    (v : WO S A') :
    l.foldr (fun p C => opL ψ A S A' p.1 C) C u v = l.foldr (fun p f => comb ψ A S p.1 f) (fun u' => C u' v) u := by
  induction l generalizing u with
  | nil => rfl
  | cons p l ih =>
    simp only [List.foldr_cons]
    show comb ψ A S p.1 (fun u' => l.foldr (fun p C => opL ψ A S A' p.1 C) C u' v) u = _
    congr 1
    funext u'
    rw [ih]

theorem theta_opR (b : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) (hC : ∀ v, IsThetaFunO ψ A S (fun u => C u v))
    (v : WO S A') : IsThetaFunO ψ A S (fun u => opR ψ A S A' b C u v) := by
  simp only [opR, comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, heisO]
  refine theta_sum' _ _ fun y _ => ?_
  have h := theta_const_mul' (b y * ψ (symplOH S A' v y)) (hC (v + y))
  simpa only [mul_assoc] using h

theorem theta_foldR (l : List ((WO A S →₀ ℂ) × (WO S A' →₀ ℂ))) (Y : WO A S → WO S A' → ℂ)
    (hY : ∀ v, IsThetaFunO ψ A S (fun u => Y u v)) (v : WO S A') :
    IsThetaFunO ψ A S (fun u => l.foldr (fun p C => opR ψ A S A' p.2 C) Y u v) := by
  induction l generalizing v with
  | nil => exact hY v
  | cons p l ih => exact theta_opR ψ A S A' p.2 _ ih v

end Ops

end GlobalTheory.SeeSawFold


open GlobalTheory.SeeSawFold in
theorem GlobalTheory.SeeSaw.biComb_eq_foldr : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c : WO A S →₀ ℂ)
    (c' : WO S A' →₀ ℂ) (l : List ((WO A S →₀ ℂ) × (WO S A' →₀ ℂ))),
    (∀ f, IsThetaFunO ψ A S f → comb ψ A S c f = l.foldr (fun p f' => comb ψ A S p.1 f') f) →
    (∀ f, IsThetaFunO ψ S A' f → comb ψ S A' c' f = l.foldr (fun p f' => comb ψ S A' p.2 f') f) →
    ∀ Y : WO A S → WO S A' → ℂ, (∀ v, IsThetaFunO ψ A S (fun u => Y u v)) → (∀ u, IsThetaFunO ψ S A' (Y u)) →
      biComb ψ A S A' c c' Y = l.foldr (fun p C => biComb ψ A S A' p.1 p.2 C) Y := by
  intro D ψ A S A' c c' l hc hc' Y hYv hYu
  have hR : opR ψ A S A' c' Y = l.foldr (fun p C => opR ψ A S A' p.2 C) Y := by
    funext u v
    show comb ψ S A' c' (Y u) v = _
    rw [hc' _ (hYu u), foldR_apply]
  rw [← foldL_foldR, biComb_eq, hR]
  funext u v
  rw [foldL_apply]
  exact congrFun (hc _ (theta_foldR ψ A S A' l Y hYv v)) u

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory.SeeSaw.RealComm

variable {D : D7}

theorem map_mul_gen {A B m n : Type} [CommRing A] [CommRing B] [Fintype n] (φ : A →+* B) (u : Matrix m n A) (g : Matrix n n A) :
    (u * g).map φ = u.map φ * g.map φ := Matrix.map_mul

theorem actO_real_fin (S T : HSp D) {z : GA D S} (hz : z ∈ GinfC S) {u : WO S T} (hu : u.map (infPart D) = 0) :
    actO S T z 1 u = u := by
  have h1 : Formalism.L2.Theta.mt T 1 = 1 := rfl
  have hz' : finHom S z⁻¹ = 1 := (GinfC S).inv_mem hz
  have h2 : (Formalism.L2.Theta.mt S z⁻¹).map (finPart D) = 1 := congrArg Units.val hz'
  rw [actO, h1, Matrix.one_mul]
  have h3 := map_mul_gen (finPart D) u (Formalism.L2.Theta.mt S z⁻¹)
  have h4 := map_mul_gen (infPart D) u (Formalism.L2.Theta.mt S z⁻¹)
  rw [h2, Matrix.mul_one] at h3
  rw [hu, Matrix.zero_mul, ← hu] at h4
  exact Matrix.ext fun i j => GlobalTheory.SplitScalar.adele_ext (congrFun (congrFun h4 i) j) (congrFun (congrFun h3 i) j)

theorem om_comb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ z ∈ GinfC S, ∀ c : WO S T →₀ ℂ, IsFinComb c → ∀ g : WO S T → ℂ, IsThetaFunO ψ S T g → om (z, 1) (comb ψ S T c g) = comb ψ S T c (om (z, 1) g) := by
  intro D ψ S T χS χT om H z hz c hc g hg
  unfold comb

  rw [map_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [map_smul, H.om_heis z 1 u g hg, actO_real_fin S T hz (hc u hu)]

end GlobalTheory.SeeSaw.RealComm
end
