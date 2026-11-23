module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import GroundTheory.AutomorphicForms.SmoothRep
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle214
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.LocTied6
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankDdRFinsum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle363
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeRhamRankLubinTateLine
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.Bundle003
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle248
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle272
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle273
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle249
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle227
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle277
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle274
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.SmoothTransfer

theorem isSmooth_found : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → GroundTheory.Automorphic.IsSmooth π := by
  intro k _ _ _ _ N V _ _ π h
  exact h

end GlobalTheory.CompanionTheory.SmoothTransfer
end

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.SchurCentre

theorem scalar_acts_by_scalar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → IsAdmissible π → ∀ t : kˣ, ∃ c : ℂ, ∀ v, π (Matrix.GeneralLinearGroup.scalar (Fin N) t) v = c • v := by
  intro k _ _ _ _ N V _ _ π hs hirr hadm t
  haveI := hirr

  have hz : ∀ g : GL (Fin N) k, g * Matrix.GeneralLinearGroup.scalar (Fin N) t =
      Matrix.GeneralLinearGroup.scalar (Fin N) t * g := by
    intro g
    ext i j
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Matrix.diagonal_apply, mul_comm]
  set z := Matrix.GeneralLinearGroup.scalar (Fin N) t with hzdef
  have hcomm : ∀ (g : GL (Fin N) k) (w : V), π g (π z w) = π z (π g w) := by
    intro g w
    rw [← Module.End.mul_apply, ← map_mul, hz g, map_mul, Module.End.mul_apply]

  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := by
    by_contra h
    push Not at h
    apply (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤)
    apply Subrepresentation.toSubmodule_injective
    change (⊥ : Submodule ℂ V) = ⊤
    ext u
    simp [h u]

  let S : Subgroup (GL (Fin N) k) :=
    { carrier := {g | π g v = v}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hb, ha]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  let K : Subgroup (GL (Fin N) k) := GlobalTheory.SplitWeil.KO k (Fin N) ⊓ S
  have hKo : IsOpen (K : Set (GL (Fin N) k)) :=
    (GlobalTheory.SplitFlip.isOpen_KO (k := k) (n := Fin N)).inter (hs v)
  have hKc : IsCompact (K : Set (GL (Fin N) k)) :=
    (GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := Fin N)).of_isClosed_subset
      (Subgroup.isClosed_of_isOpen K hKo) (fun _ h => h.1)
  haveI hfd : FiniteDimensional ℂ (fixed π K) := hadm.2 K hKo hKc
  have hmem : ∀ w : V, w ∈ fixed π K ↔ ∀ h : K, π (h : GL (Fin N) k) w = w := by
    intro w
    show (∀ h : K, _ = _) ↔ _
    simp
  have hvK : v ∈ fixed π K := (hmem v).2 fun h => h.2.2
  haveI : Nontrivial (fixed π K) :=
    ⟨⟨⟨v, hvK⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  have hst : ∀ w ∈ fixed π K, π z w ∈ fixed π K := by
    intro w hw
    refine (hmem _).2 fun h => ?_
    rw [hcomm, (hmem w).1 hw h]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((π z).restrict hst)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  have hw0 : (w : V) ≠ 0 := fun h => hw.2 (Subtype.ext h)
  have hwc : π z (w : V) = c • (w : V) := by
    have := congrArg Subtype.val hw.apply_eq_smul
    simpa using this

  let f : Representation.IntertwiningMap π π :=
    { toLinearMap := π z - c • LinearMap.id
      isIntertwining' := by
        intro g
        ext u
        simp [hcomm] }
  refine ⟨c, fun u => ?_⟩
  rcases Representation.IsIrreducible.bijective_or_eq_zero f with hb | h0
  · exfalso
    apply hw0
    apply hb.1
    show π z (w : V) - c • (w : V) = f 0
    rw [hwc, sub_self, map_zero]
  · have := congrArg (fun F : Representation.IntertwiningMap π π => F u) h0
    have h1 : π z u - c • u = 0 := this
    exact sub_eq_zero.1 h1

end GlobalTheory.CompanionTheory.SchurCentre
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.SubQuotNe

theorem exists_mem_not_mem_of_subQuot_equiv :
    ∀ {M W X : Type} [Group M] [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]
      (ρ : Representation ℂ M W) (σ : Representation ℂ M X) (S T : Subrepresentation ρ),
      Nonempty ((subQuot S T).Equiv σ) → Nontrivial X →
        ∃ s ∈ S.toSubmodule, s ∉ T.toSubmodule := by
  intro M W X _ _ _ _ _ ρ σ S T hE hX
  obtain ⟨e⟩ := hE
  by_contra h
  push_neg at h
  have hle : S.toSubmodule ≤ T.toSubmodule := fun s hs => h s hs
  haveI : Subsingleton (S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) :=
    Submodule.Quotient.subsingleton_iff.mpr (Submodule.comap_subtype_eq_top.mpr hle)
  exact not_subsingleton X e.toLinearEquiv.symm.injective.subsingleton

end GlobalTheory.CompanionTheory.SubQuotNe
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.SubQuotScalar

theorem sub_smul_mem_of_equiv_subQuot :
    ∀ {M W X : Type} [Group M] [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]
      (ρ : Representation ℂ M W) (σ : Representation ℂ M X) (S T : Subrepresentation ρ),
      Nonempty ((subQuot S T).Equiv σ) → ∀ (g : M) (c : ℂ), (∀ x, σ g x = c • x) →
        ∀ s ∈ S.toSubmodule, ρ g s - c • s ∈ T.toSubmodule := by
  intro M W X _ _ _ _ _ ρ σ S T he g c hσ s hs
  obtain ⟨e⟩ := he
  have hinj : Function.Injective e.toIntertwiningMap.toLinearMap := e.left_inv.injective
  have key : e.toIntertwiningMap.toLinearMap
        (GlobalTheory.SmGL.subQuot S T g (Submodule.Quotient.mk ⟨s, hs⟩)) =
      e.toIntertwiningMap.toLinearMap (c • Submodule.Quotient.mk ⟨s, hs⟩) := by
    rw [map_smul, ← hσ]
    exact LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) _
  have h2 := hinj key
  have h3 : (Submodule.Quotient.mk ⟨ρ g s, S.2 g hs⟩ :
        ↥S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) =
      Submodule.Quotient.mk (c • (⟨s, hs⟩ : ↥S.toSubmodule)) := h2
  rw [Submodule.Quotient.eq] at h3
  exact h3

end GlobalTheory.CompanionTheory.SubQuotScalar
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical

open Module GlobalTheory.CompanionTheory.DeRhamChar GlobalTheory.CompanionTheory.LTRead in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem _root_.GlobalTheory.T.de_rham_rank_lubin_tate_line : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied6 l P AI) →
    ∀ (K LL : FinExt l), (∀ (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), μ x ∈ LL.1) →
    ∀ (χ : ↥(GK K) →* (↥K.1)ˣ), HasPeriods P K χ → ∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1,
      Module.finrank ↥LL.1 ↥(DdR (P.PD K) (lineRep ((Units.map ((τ : ↥K.1 →+* ↥LL.1) : ↥K.1 →* ↥LL.1)).comp χ))) =
        Module.finrank ℚ_[l] ↥K.1 * 1 ∧
      ∀ (τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ),
        multV (P.PD K) (lineRep ((Units.map ((τ : ↥K.1 →+* ↥LL.1) : ↥K.1 →* ↥LL.1)).comp χ)) τ' a =
          if a = (if τ' = τ then (-1 : ℤ) else 0) then 1 else 0 := by
  rintro l _ P AI ⟨T⟩ K LL hsplit χ hP τ
  have := K.2
  have := LL.2
  set ψ : ↥(GK K) →* (↥LL.1)ˣ := (Units.map ((τ : ↥K.1 →+* ↥LL.1) : ↥K.1 →* ↥LL.1)).comp χ
  have hcomponent : ∀ τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ z ∈ DdRE (P.PD K) (lineRep ψ) τ',
      (∀ w ∈ DdRE (P.PD K) (lineRep ψ) τ', ∃ c : ↥LL.1, w = c • z) ∧
      z ∈ FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) (if τ' = τ then (-1 : ℤ) else 0) ∧
      z ∉ FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) ((if τ' = τ then (-1 : ℤ) else 0) + 1) := by
    intro τ'
    obtain ⟨σ₀, h₀⟩ := exists_lift τ' K.1.val
    obtain ⟨y, hyact, h1, h2⟩ := hP (σ₀.comp τ)
    have hact : ∀ g : ↥(GK K), gc g σ₀ = σ₀ →
        P.actQdR (g : GQ l) y = algebraMap (Om l) P.R.BdR (σ₀ ((ψ g : (↥LL.1)ˣ) : ↥LL.1)) * y :=
      fun g hg => hyact g.1 g.2 fun x => DFunLike.congr_fun hg (τ x)
    by_cases hτ : τ' = τ
    · have hμ : σ₀.comp τ = K.1.val := AlgHom.ext fun x => by
        rw [AlgHom.comp_apply, ← hτ]
        exact h₀ x
      obtain ⟨m1, m2⟩ := h1 hμ
      rw [ite_eq_left hτ]
      have m2' : y ∉ (P.PD K).Fil (1 + 1) := by
        rw [show (1 + 1 : ℤ) = 2 by norm_num]
        exact m2
      exact component_line P T ψ τ' σ₀ h₀ y hact 1 m1 m2'
    · have hμ : σ₀.comp τ ≠ K.1.val := fun h => hτ (AlgHom.ext fun x =>
        σ₀.toRingHom.injective ((h₀ x).trans (DFunLike.congr_fun h x).symm))
      obtain ⟨m1, m2⟩ := h2 hμ
      rw [ite_eq_right hτ]
      have m2' : y ∉ (P.PD K).Fil (0 + 1) := by
        rw [zero_add]
        exact m2
      have h3 := component_line P T ψ τ' σ₀ h₀ y hact 0 m1 m2'
      rw [neg_zero] at h3
      exact h3
  refine ⟨?_, fun τ' a => ?_⟩
  · have hc : Fintype.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1 := by
      rw [← GlobalTheory.DeRhamSplit.card_emb K LL hsplit, Nat.card_eq_fintype_card]
    have := (GlobalTheory.Per.FontaineBound.ddR_finite_le (P.PD K)
      (PositivityTheory.LocInh.tied_field l P AI T).1 (lineRep ψ)).1
    obtain ⟨e1, -⟩ := GlobalTheory.DeRhamSplit.finrank_DdR (P.PD K) (lineRep ψ) hc 0
    have hone : ∀ τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Module.finrank ↥LL.1 ↥(DdRE (P.PD K) (lineRep ψ) τ') = 1 := by
      intro τ'
      obtain ⟨z, hz, hgen, -, h2⟩ := hcomponent τ'
      have hz0 : z ≠ 0 := fun h => h2 (h ▸ Submodule.zero_mem _)
      have hspan : DdRE (P.PD K) (lineRep ψ) τ' = ↥LL.1 ∙ z := by
        refine le_antisymm (fun w hw => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 hz)
        obtain ⟨c, rfl⟩ := hgen w hw
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z)
      rw [hspan]
      exact finrank_span_singleton hz0
    rw [e1, Finset.sum_congr rfl fun τ' _ => hone τ']
    simp [hc]
  · obtain ⟨z, hz, hgen, h1, h2⟩ := hcomponent τ'
    exact multV_of_gen (P.PD K) (lineRep ψ) τ' _ z hz hgen h1 h2 a
end
end

section

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem coe_toC0 {f : ℝ → ℂ} (h₁ : Continuous f) (h₂ : Tendsto f (cocompact ℝ) (𝓝 0)) (y : ℝ) : toC0 f y = f y := by
  have : Continuous f ∧ Tendsto f (cocompact ℝ) (𝓝 0) := ⟨h₁, h₂⟩
  simp only [toC0]
  rw [dite_eq_left this]
  rfl

theorem adj_rho {n : ℕ} (E : KMod n) [CompleteSpace E.V] (k : Matrix.unitaryGroup (Fin n) ℂ) :
    ContinuousLinearMap.adjoint (E.ρ k⁻¹) = E.ρ k := by
  have hmul : ∀ v, E.ρ k (E.ρ k⁻¹ v) = v := fun v => by
    have := congrArg (fun L : E.V →L[ℂ] E.V => L v) (E.ρ.map_mul k k⁻¹)
    simpa using this.symm
  have hmul' : ∀ v, E.ρ k⁻¹ (E.ρ k v) = v := fun v => by
    have := congrArg (fun L : E.V →L[ℂ] E.V => L v) (E.ρ.map_mul k⁻¹ k)
    simpa using this.symm
  let I : E.V →ₗᵢ[ℂ] E.V := ⟨(E.ρ k).toLinearMap, fun v => E.iso k v⟩
  ext v
  refine ext_inner_right ℂ fun w => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  have := I.inner_map_map v (E.ρ k⁻¹ w)
  have e : ∀ z, I z = E.ρ k z := fun _ => rfl
  rw [e, e, hmul] at this
  exact this.symm

theorem kerCore_of (hFR : RowExists) (hRM : RowMatrix) (hAS : AdjSmooth) (hRL : RowLeft) (hAF : ActFormula)
    (hWR : WaveRep) (hWU : WaveUniq) (hPR : PhiRes) (hWI : WaveInt) (hSR : SupportRow) : KerCore := by
  intro n _ _ μ _ E g T₀ hb hLg hUn hRC hSG hAE hWS hWC hCS hSO hPW
  haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  obtain ⟨hAbsFC, hAbsCut, hFc, hWv, hCls, hSobOps, hCptSob, hSB, hPres, hConc, hCJ, hFr, hOmF, hIbp, hDD⟩ := id hCS
  obtain ⟨hMrep, Ω, T, hDense, hSym, hEx, hLeft, hOm⟩ :=
    hConc n μ E.V hLg hUn hRC hSG hPres hFr hCls hSobOps hCptSob hOmF hIbp hDD
  obtain ⟨F⟩ := hAbsFC _ _ Ω T hDense hSym hEx hLeft
  obtain ⟨c, hc⟩ := hSB n μ E hLg hUn hRC
  have hStd : Std μ E F c :=
    ⟨hLg, hUn, hRC, hSG, hAE, hWS, hWC, hCS, hSO, hPW, hMrep, hSym, hEx, hLeft, hOm, hc⟩
  have hPW1 := (hPW c g T₀ hb).1
  have hPW2 := (hPW c g T₀ hb).2
  have hC0 : ∀ y, toC0 (hg c g) y = hg c g y := fun y => by
    have := hPW1 0
    simp only [pow_zero, one_mul] at this
    exact coe_toC0 this.1 (by simpa using this.2) y
  have hR : Rapid (toC0 (hg c g)) := fun m =>
    ⟨toC0 (fun y : ℝ => (y : ℂ) ^ m * hg c g y), fun y => by
      rw [coe_toC0 (hPW1 m).1 (hPW1 m).2, hC0]⟩
  obtain ⟨A, hA⟩ := hRM n μ E Ω T F c hStd _ (hFR n μ E Ω T F c hStd _ hR)
  have hWV : ∀ f ∈ CE E, Cpt f → ∀ u, IsWave E u → (∀ x ∈ GLs n, u 0 x = f x) → ∀ f', Sob μ f' → IsSec E f' →
      cls μ f' = F.Φ (toC0 (hg c g)) (cls μ f) → ∀ x ∈ GLs n, ∫ t, (g t : ℂ) • u t x = f' x := by
    intro f hf hcpt u hu h0 f' hs _ hcl x hx
    obtain ⟨N, b, U, hN, hT, hUw, hU0, hUt⟩ := hWR n μ E Ω T F c hStd f hf hcpt
    have huU : ∀ t, u t x = U t x := fun t =>
      hWU hWS hCS hRC n E u U hu hUw (fun y hy => by rw [h0 y hy, hU0 y hy]) t x hx
    have hcl' : cls μ f' = F.Φ (toC0 (fun y => ((((1 + y ^ 2) ^ N)⁻¹ : ℝ) : ℂ) * hg c g y)) b := by
      rw [hPR n μ E Ω T F c hStd g T₀ hb N hN, hcl, ← hT]
      rfl
    have := hWI n μ E Ω T F c hStd g T₀ hb N b U hN hUw hUt f' hs hcl' x hx
    simpa only [huU] using this
  obtain ⟨R, hRsup⟩ := hSR n μ E Ω T F c hStd g T₀ _ hb hR hWV
  have hKdef : ∀ k : Matrix.unitaryGroup (Fin n) ℂ, ∀ y ∈ GLs n, A (y * k.1) = E.ρ k⁻¹ * A y := by
    intro k y hy
    ext v
    exact (hA v).2.1 y hy k
  have hkG : ∀ k : Matrix.unitaryGroup (Fin n) ℂ, ∀ y ∈ GLs n, k.1 * y ∈ GLs n := by
    intro k y hy
    have hk : (k.1 : Mat n).det ≠ 0 :=
      (Matrix.isUnit_det_of_right_inverse (Matrix.mem_unitaryGroup_iff.1 k.2)).ne_zero
    simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at hy ⊢
    exact mul_ne_zero hk hy
  refine ⟨fun y => ContinuousLinearMap.adjoint (A y), hAS _ _ A _ fun v => (hA v).1.1, ⟨R, ?_⟩, ?_, ?_⟩
  · intro y hy hl
    have : A y = 0 := by
      ext v
      exact hRsup v _ (hA v) y hy hl
    simp [this]
  · intro y hy k₁ k₂
    have e1 : A (k₁.1 * y * k₂.1) = E.ρ k₂⁻¹ * A (k₁.1 * y) := hKdef k₂ _ (hkG k₁ y hy)
    have e2 : A (k₁.1 * y) = A y * E.ρ k₁⁻¹ := by
      ext v
      exact hRL n μ E Ω T F c hStd _ A hR hA k₁ y hy v
    show ContinuousLinearMap.adjoint (A (k₁.1 * y * k₂.1)) = _
    rw [e1, e2]
    simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.mul_def, adj_rho]
  · intro f hf hcpt u hu h0 x hx
    have hSf : Sob μ f := (hCptSob n μ E.V hLg hRC f hf.1 hcpt).1
    obtain ⟨C, hC⟩ := hSO n μ E Ω T F hLg hUn hRC hSG hAE hCS hOm (toC0 (hg c g)) hR
    obtain ⟨f', hf's, hf'e, hf'c, -⟩ := hC (cls μ f) (subset_closure ⟨f, hSf, hf.2, rfl⟩)
    rw [hAF n μ E Ω T F c hStd _ A hA f hf hcpt f' hf's hf'e hf'c x hx,
      hWV f hf hcpt u hu h0 f' hf's hf'e hf'c x hx]

theorem kerCore : KerCore :=
  have hLC := GlobalTheory.T.left_translate_commutes GlobalTheory.T.left_translate_sobolev
  kerCore_of (GlobalTheory.T.kernel_row_exists GlobalTheory.T.rapid_factorization GlobalTheory.T.eigenvalue_adjoint_facts) GlobalTheory.T.kernel_row_matrix GlobalTheory.T.kernel_adjoint_smooth
    (GlobalTheory.T.kernel_row_left_invariant GlobalTheory.T.left_translate_sobolev hLC) (GlobalTheory.T.kernel_action_formula GlobalTheory.T.left_translate_sobolev hLC) GlobalTheory.T.wave_representation GlobalTheory.T.wave_uniqueness GlobalTheory.T.phi_resolvent_identity
    GlobalTheory.T.wave_integral_identity GlobalTheory.T.kernel_row_support

end GlobalTheory.CompanionTheory.KerFc
end
end

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA

theorem mol_ae_lConv : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V],
    Unimod → ∀ φ : Mat n → ℝ, IsTest φ → ∀ x : Lp V 2 μ,
      (fun y : G n => Mol μ φ (⇑x) y.val) =ᵐ[μ] lConv μ V φ x := by
  intro n _ _ μ _ V _ _ _ hU φ hφ x
  obtain ⟨h1, h2⟩ := hU n μ
  have hφc : Continuous φ := hφ.1.continuous
  have hφv : Continuous (fun y : G n => φ y.val) := hφc.comp Units.continuous_val

  have hcont : Continuous (fun y : G n => φ y.val • lT μ V y x) :=
    hφv.smul (GlobalTheory.T.regular_representation_continuous n μ V hU x).2
  have hK : IsCompact ((Units.val : G n → Mat n) ⁻¹' tsupport φ) := by
    refine ((GlobalTheory.CompanionTheory.SobGL.HaarDom.isOpenEmbedding_valG n).isInducing.isCompact_preimage_iff
      ?_).2 hφ.2.1
    intro g hg
    have hd : g.det ≠ 0 := hφ.2.2 hg
    have hu : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).2 (isUnit_iff_ne_zero.2 hd)
    exact ⟨hu.unit, rfl⟩
  have hcs : HasCompactSupport (fun y : G n => φ y.val • lT μ V y x) := by
    refine HasCompactSupport.intro hK fun y hy => ?_
    have : φ y.val = 0 := image_eq_zero_of_notMem_tsupport hy
    simp [this]
  have hint : Integrable (fun y : G n => φ y.val • lT μ V y x) μ :=
    hcont.integrable_of_hasCompactSupport hcs

  have hmul : Measurable (fun p : G n × G n => p.1⁻¹ * p.2) :=
    (continuous_fst.inv.mul continuous_snd).measurable
  have hF : AEStronglyMeasurable
      (Function.uncurry fun (y z : G n) => φ y.val • (x : G n → V) (y⁻¹ * z)) (μ.prod μ) := by
    refine StronglyMeasurable.aestronglyMeasurable ?_
    have a1 : StronglyMeasurable (fun p : G n × G n => φ p.1.val) :=
      (hφv.comp continuous_fst).stronglyMeasurable
    have a2 : StronglyMeasurable (fun p : G n × G n => (x : G n → V) (p.1⁻¹ * p.2)) :=
      (Lp.stronglyMeasurable x).comp_measurable hmul
    exact a1.smul a2
  have hae : ∀ᵐ y ∂μ, (φ y.val • lT μ V y x : Lp V 2 μ) =ᵐ[μ]
      fun z => φ y.val • (x : G n → V) (y⁻¹ * z) := by
    refine Eventually.of_forall fun y => ?_
    filter_upwards [Lp.coeFn_smul (φ y.val) (lT μ V y x), lT_coe μ y x] with z e1 e2
    rw [e1, Pi.smul_apply, e2]
  have key := GlobalTheory.T.lp_integral_ae_pointwise (G n) (G n) V μ μ (fun y : G n => φ y.val • lT μ V y x)
    (fun y z => φ y.val • (x : G n → V) (y⁻¹ * z)) hint hF hae
  have hconv : lConv μ V φ x = ∫ y : G n, φ y.val • lT μ V y x ∂μ := rfl
  rw [hconv]
  filter_upwards [key] with z hz
  rw [hz]

  let H : G n → V := fun u => φ (z.val * (u⁻¹ : G n).val) • (x : G n → V) u
  have e2 : ∫ u, H u ∂μ = ∫ u, H (u⁻¹ * z) ∂μ := by
    rw [integral_inv_eq_self (fun u => H (u * z)) μ, integral_mul_right_eq_self H z]
  show ∫ u, H u ∂μ = _
  rw [e2]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have e3 : z.val * ((y⁻¹ * z)⁻¹ : G n).val = y.val := by
    rw [← Units.val_mul]
    congr 1
    group
  show φ (z.val * ((y⁻¹ * z)⁻¹ : G n).val) • (x : G n → V) (y⁻¹ * z) = _
  rw [e3]

end GlobalTheory.CompanionTheory.PresSobA
end
end
