module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarRightInvariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle482
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle537
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.GenericPrincipalSeries.GenericPrincipalSeries
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle382
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle326
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle286
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle553
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle324
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle397
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle555
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle293
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVecUnitaryModule
public import Formalism.PeriodIntegrals.Bundle003
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle041
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle509
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsIrrKSubOfIsKTypeOf

@[expose] public section

section

open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

theorem _root_.GlobalTheory.T.exists_open_compact_subgroup_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (S : Subgroup (GL (Fin N) (Af E))), IsOpen (S : Set (GL (Fin N) (Af E))) → ∃ L : Subgroup (GL (Fin N) (Af E)), L ≤ S ∧ IsOpen (L : Set (GL (Fin N) (Af E))) ∧ IsCompact (L : Set (GL (Fin N) (Af E))) := by
  first | exact @GlobalTheory.CompanionTheory.FinDiscOrth.exists_compact_open_level_le | exact GlobalTheory.CompanionTheory.FinDiscOrth.exists_compact_open_level_le | (intros; apply GlobalTheory.CompanionTheory.FinDiscOrth.exists_compact_open_level_le <;> assumption)
end

section

open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC

theorem _root_.GlobalTheory.T.cuspidal_convolution_compact : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA E a → ℂ), Continuous f → HasCompactSupport f → IsCompactOperator (repOp (Rcusp μ) μ f) := by
  first | exact @GlobalTheory.CompanionTheory.CuspidalCompact.isCompactOperator_repOp_Rcusp | exact GlobalTheory.CompanionTheory.CuspidalCompact.isCompactOperator_repOp_Rcusp | (intros; apply GlobalTheory.CompanionTheory.CuspidalCompact.isCompactOperator_repOp_Rcusp <;> assumption)
end

section

open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

theorem _root_.GlobalTheory.T.haar_right_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  first | exact @GlobalTheory.CompanionTheory.AdelicUnimod.isMulRightInvariant_GA_CM | exact GlobalTheory.CompanionTheory.AdelicUnimod.isMulRightInvariant_GA_CM | (intros; apply GlobalTheory.CompanionTheory.AdelicUnimod.isMulRightInvariant_GA_CM <;> assumption)
end

section

open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.ConvHecke

theorem conv_isHecke : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (K L : Subgroup H) (f₁ f₂ : H → ℂ), L ≤ K → L.relIndex K ≠ 0 → IsHecke L f₁ → IsHecke L f₂ →
    IsHecke L (fun y => hint K fun z => f₁ z * f₂ (z⁻¹ * y)) ∧
      ∀ y, (hint K fun z => f₁ z * f₂ (z⁻¹ * y)) ≠ 0 → ∃ z, f₁ z ≠ 0 ∧ f₂ (z⁻¹ * y) ≠ 0 := by
  intro H _ _ _ _ K L f₁ f₂ hLK hfin h₁ h₂
  have hu : ∀ y, L ≤ rStab (fun z => f₁ z * f₂ (z⁻¹ * y)) := by
    intro y l hl x
    show f₁ (x * l) * f₂ ((x * l)⁻¹ * y) = f₁ x * f₂ (x⁻¹ * y)
    have e : (x * l)⁻¹ * y = l⁻¹ * (x⁻¹ * y) := by group
    rw [e, (h₁.2 l hl x).2, (h₂.2 l⁻¹ (L.inv_mem hl) _).1]
  have hlev := fun y =>
    GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H K L (fun z => f₁ z * f₂ (z⁻¹ * y)) hLK (hu y) hfin
  have hnz : ∀ y, (hint K fun z => f₁ z * f₂ (z⁻¹ * y)) ≠ 0 →
      ∃ z, f₁ z ≠ 0 ∧ f₂ (z⁻¹ * y) ≠ 0 := by
    intro y hy
    by_contra hcon
    push_neg at hcon
    apply hy
    rw [hlev y]
    have hz : ∀ p : H ⧸ L, f₁ p.out * f₂ ((p.out)⁻¹ * y) = 0 := by
      intro p
      by_cases h : f₁ p.out = 0
      · simp [h]
      · simp [hcon _ h]
    simp [hz]
  refine ⟨⟨?_, ?_⟩, hnz⟩
  · refine HasCompactSupport.of_support_subset_isCompact
      (h₁.1.isCompact.mul h₂.1.isCompact) ?_
    intro y hy
    obtain ⟨z, hz1, hz2⟩ := hnz y hy
    exact Set.mem_mul.2 ⟨z, subset_tsupport _ hz1, z⁻¹ * y, subset_tsupport _ hz2, by group⟩
  · intro l hl x
    constructor
    · show (hint K fun z => f₁ z * f₂ (z⁻¹ * (l * x))) = hint K fun z => f₁ z * f₂ (z⁻¹ * x)
      rw [hlev (l * x), hlev x]
      congr 1
      refine (finsum_comp_equiv (MulAction.toPerm l : Equiv.Perm (H ⧸ L))).symm.trans
        (finsum_congr fun p => ?_)
      set w : H := ((MulAction.toPerm l : Equiv.Perm (H ⧸ L)) p).out with hw
      have hcl : ((l * p.out : H) : H ⧸ L) = (w : H ⧸ L) := by
        rw [hw, QuotientGroup.out_eq']
        show ((l * p.out : H) : H ⧸ L) = l • p
        conv_rhs => rw [← QuotientGroup.out_eq' p]
        rfl
      have hm : (l * p.out)⁻¹ * w ∈ L := QuotientGroup.eq.1 hcl
      have hinv := hu (l * x) hm (l * p.out)
      have hmul : l * p.out * ((l * p.out)⁻¹ * w) = w := by group
      simp only [hmul] at hinv
      refine hinv.trans ?_
      have e : (l * p.out)⁻¹ * (l * x) = (p.out)⁻¹ * x := by group
      rw [e, (h₁.2 l hl _).1]
    · show (hint K fun z => f₁ z * f₂ (z⁻¹ * (x * l))) = hint K fun z => f₁ z * f₂ (z⁻¹ * x)
      have e : (fun z => f₁ z * f₂ (z⁻¹ * (x * l))) = fun z => f₁ z * f₂ (z⁻¹ * x) := by
        funext z
        rw [← mul_assoc, (h₂.2 l hl _).2]
      rw [e]

end GlobalTheory.CompanionTheory.ConvHecke

end
end

section

open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

namespace GlobalTheory.CompanionTheory.HintLevelPt

theorem hint_eq_level_of_forall : ∀ (H : Type) [Group H] (K L : Subgroup H) (u : H → ℂ), L ≤ K →
    L.relIndex K ≠ 0 → (∀ l ∈ L, ∀ x, u (x * l) = u x) →
    hint K u = ((L.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ p : H ⧸ L, u p.out := by
  intro H _ K L u hLK hfin hu
  exact GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H K L u hLK (fun l hl x => hu l hl x) hfin

end GlobalTheory.CompanionTheory.HintLevelPt
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitIndex

theorem rStab_index_ne_zero_of_compact : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K K' : Subgroup G) (d : G) (f : G → ℂ),
  Continuous θ → IsCompact (K : Set G) → IsOpen (K' : Set G) → (∀ k ∈ K', ∀ x, f (k * x) = f x ∧ f (x * k) = f x) →
  ∀ y : G, (rStab fun k : K => f ((y * k)⁻¹ * d * θ (y * k))).index ≠ 0 := by
  intro G _ _ _ θ K K' d f hθ hKc ho hf y
  set W : Subgroup G := K' ⊓ K'.comap θ with hW
  have hWo : IsOpen (W : Set G) := by
    rw [hW, Subgroup.coe_inf]
    exact ho.inter (ho.preimage hθ)
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hWo' : IsOpen ((W.subgroupOf K : Subgroup K) : Set K) :=
    hWo.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ hWo'
  haveI : (W.subgroupOf K).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  have hle : W.subgroupOf K ≤ rStab fun k : K => f ((y * k)⁻¹ * d * θ (y * k)) := by
    intro k' hk' k
    have hk'W : (k' : G) ∈ W := Subgroup.mem_subgroupOf.mp hk'
    have hl : (k' : G)⁻¹ ∈ K' := K'.inv_mem hk'W.1
    have hr : θ (k' : G) ∈ K' := hk'W.2
    have e : (y * ((k * k' : K) : G))⁻¹ * d * θ (y * ((k * k' : K) : G)) =
        (k' : G)⁻¹ * (((y * (k : G))⁻¹ * d * θ (y * (k : G))) * θ (k' : G)) := by
      simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev, mul_assoc]
    show f _ = f _
    rw [e, (hf _ hl _).1, (hf _ hr _).2]
  exact (Subgroup.finiteIndex_of_le hle).index_ne_zero

end GlobalTheory.CompanionTheory.SplitIndex
end
end

section

open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

namespace GlobalTheory.CompanionTheory.CptDiag

theorem isCompact_closure_zpowers_image {G G' : Type} [Group G] [Group G'] [TopologicalSpace G] [TopologicalSpace G']
    [T2Space G'] (φ : G →* G') (hφ : Continuous φ) (t : G)
    (ht : IsCompact (closure (Subgroup.zpowers t : Set G))) :
    IsCompact (closure (Subgroup.zpowers (φ t) : Set G')) := by
  have hK : IsCompact (φ '' closure (Subgroup.zpowers t : Set G)) := ht.image hφ
  refine hK.of_isClosed_subset isClosed_closure ?_
  refine closure_minimal ?_ hK.isClosed
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact ⟨t ^ k, subset_closure (Subgroup.zpow_mem_zpowers t k), map_zpow φ t k⟩

theorem cptPart_diag : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (Z : Subgroup H), cptPart (Z.map ((MonoidHom.id H).prod (MonoidHom.id H))) = (cptPart Z).map ((MonoidHom.id H).prod (MonoidHom.id H)) := by
  intro H _ _ _ _ Z
  unfold cptPart
  rw [MonoidHom.map_closure]
  congr 1
  ext u
  constructor
  · rintro ⟨hu, hc⟩
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hu
    refine ⟨t, ⟨ht, ?_⟩, rfl⟩
    have := isCompact_closure_zpowers_image (MonoidHom.fst H H) continuous_fst _ hc
    simpa using this
  · rintro ⟨t, ⟨ht, hc⟩, rfl⟩
    have hcont : Continuous ((MonoidHom.id H).prod (MonoidHom.id H)) := by
      show Continuous fun x : H => (x, x)
      exact continuous_id.prodMk continuous_id
    exact ⟨Subgroup.mem_map_of_mem _ ht, isCompact_closure_zpowers_image _ hcont t hc⟩

end GlobalTheory.CompanionTheory.CptDiag
end

section

open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

namespace GlobalTheory.CompanionTheory.OrbitalCount

theorem exists_compact_reps_of_finite_doubleCosets :
    ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (K : Subgroup H) (N : H),
      IsCompact (K : Set H) →
      (∀ C : Set H, IsCompact C →
        {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) N : Set H) (K : Set H) |
          ∃ k ∈ K, (Quotient.out q * k)⁻¹ * N * MonoidHom.id H (Quotient.out q * k) ∈ C}.Finite) →
      ∀ C : Set H, IsCompact C →
        ∃ D : Set H, IsCompact D ∧ ∀ x : H, x⁻¹ * N * x ∈ C →
          ∃ t ∈ twCent (MonoidHom.id H) N, ∃ d ∈ D, x = t * d := by
  intro H _ _ _ K N hK hfin C hC
  refine ⟨⋃ q ∈ {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) N : Set H) (K : Set H) |
      ∃ k ∈ K, (Quotient.out q * k)⁻¹ * N * MonoidHom.id H (Quotient.out q * k) ∈ C},
      (fun k => Quotient.out q * k) '' (K : Set H), ?_, ?_⟩
  · exact (hfin C hC).isCompact_biUnion fun q _ =>
      hK.image (continuous_const.mul continuous_id)
  · intro x hx
    obtain ⟨h, hh, k, hk, hout⟩ :=
      DoubleCoset.mk_out_eq_mul (twCent (MonoidHom.id H) N) K x
    have hcomm : h * N = N * h := hh
    have hconj : (h * x)⁻¹ * N * (h * x) = x⁻¹ * N * x := by
      have : h⁻¹ * N * h = N := by
        rw [mul_assoc, ← hcomm, inv_mul_cancel_left]
      calc (h * x)⁻¹ * N * (h * x) = x⁻¹ * (h⁻¹ * N * h) * x := by group
        _ = x⁻¹ * N * x := by rw [this]
    set q := DoubleCoset.mk (twCent (MonoidHom.id H) N) K x with hq
    have hd : Quotient.out q * k⁻¹ = h * x := by
      rw [hout]; group
    refine ⟨h⁻¹, inv_mem hh, Quotient.out q * k⁻¹, ?_, ?_⟩
    · refine Set.mem_biUnion (x := q) ?_ ⟨k⁻¹, inv_mem hk, rfl⟩
      refine ⟨k⁻¹, inv_mem hk, ?_⟩
      rw [MonoidHom.id_apply, hd, hconj]
      exact hx
    · rw [hd, inv_mul_cancel_left]

end GlobalTheory.CompanionTheory.OrbitalCount
end

section

open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

namespace GlobalTheory.CompanionTheory.SwapCent

theorem twCent_swap : ∀ (H : Type) [Group H] (N : H),
    twCent ((MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom) (N, (1 : H)) =
      (twCent (MonoidHom.id H) N).map ((MonoidHom.id H).prod (MonoidHom.id H)) := by
  intro H _ N
  ext ⟨a, b⟩
  constructor
  · intro h
    have h' : (a, b) * (N, (1 : H)) = (N, (1 : H)) * (b, a) := h
    have h1 : a * N = N * b := congrArg Prod.fst h'
    have h2 : b = a := by simpa using congrArg Prod.snd h'
    subst h2
    exact ⟨b, h1, rfl⟩
  · rintro ⟨x, hx, hxe⟩
    have hx' : x * N = N * x := hx
    have e1 : x = a := congrArg Prod.fst hxe
    have e2 : x = b := congrArg Prod.snd hxe
    subst e1
    subst e2
    change (x, x) * (N, (1 : H)) = (N, (1 : H)) * (x, x)
    simp [hx']

end GlobalTheory.CompanionTheory.SwapCent
end

section

open Matrix

theorem _root_.GlobalTheory.T.exists_normal_open_subgroup_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (U : Set (GL (Fin n) k)), U ∈ nhds (1 : GL (Fin n) k) → ∃ K₁ : Subgroup (GL (Fin n) k), K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin n) ∧ IsOpen (K₁ : Set (GL (Fin n) k)) ∧ (K₁ : Set (GL (Fin n) k)) ⊆ U ∧ K₁.relIndex (GlobalTheory.SplitWeil.KO k (Fin n)) ≠ 0 ∧ ∀ κ ∈ GlobalTheory.SplitWeil.KO k (Fin n), ∀ b ∈ K₁, κ * b * κ⁻¹ ∈ K₁ := by
  first | exact @GlobalTheory.CompanionTheory.OpenCore.exists_open_normal_subgroup_KO | exact GlobalTheory.CompanionTheory.OpenCore.exists_open_normal_subgroup_KO | (intros; apply GlobalTheory.CompanionTheory.OpenCore.exists_open_normal_subgroup_KO <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.GlFrob



theorem embedding_of_exponent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (n : ℕ) (hd1 : ∑ _a : Fin n, 1 = n) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → IsAdmissible π → π.IsIrreducible → ∀ (ξ : Fin n → kˣ →* ℂˣ) (hξ : ∀ a, IsSmoothChar (ξ a)) (hd : ∑ a, (IrrGL.ofChar (ξ a) (hξ a)).1 = n), (∃ v : Jacquet π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd1)), v ≠ 0 ∧ ∀ t : Levi k (fun _ : Fin n => Fin 1), v ∈ Module.End.maxGenEigenspace (_root_.GlobalTheory.SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π t) (PositivityTheory.Lbc.torusChar ξ t)) → ∃ f : π.IntertwiningMap (prodIrr (fun a => IrrGL.ofChar (ξ a) (hξ a)) hd), Function.Injective f := by
  intro k _ _ _ _ _ n hd1 V _ _ π hs ha hirr ξ hξ hd hv
  obtain ⟨v, hv0, hv⟩ := hv
  have h0 := GlobalTheory.CompanionTheory.KmIwahori.c0 k
  have h3 := GlobalTheory.CompanionTheory.Lbc.c3 k
  have hcomm : ∀ l l' : Levi k (fun _ : Fin n => Fin 1),
      _root_.GlobalTheory.SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π l * _root_.GlobalTheory.SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π l' =
        _root_.GlobalTheory.SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π l' * _root_.GlobalTheory.SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π l := by
    intro l l'
    rw [← map_mul, ← map_mul]
    congr 1
    funext a
    exact GlobalTheory.CompanionTheory.PinLift.gl_one_comm _ _
  obtain ⟨hanti, hpow⟩ := GlobalTheory.T.deep_level_subgroups_filtration (k := k) n hd1
  have hsm : ∀ w : Jacquet π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd1)), ∃ m,
      ∀ u ∈ PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd1,
        _root_.GlobalTheory.SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π u w = w := by
    intro w
    obtain ⟨m, hm, h⟩ := GlobalTheory.T.jacquet_vector_fixed_deep_level (k := k) n hd1 π hs w
    refine ⟨m - 1, ?_⟩
    rw [Nat.sub_add_cancel hm]
    exact h
  have hfd : ∀ m, FiniteDimensional ℂ ↥(⨅ u : PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd1,
      LinearMap.ker (_root_.GlobalTheory.SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π (u : Levi k (fun _ : Fin n => Fin 1)) - 1)) := by
    intro m
    haveI := GlobalTheory.T.jacquet_module_admissible_fixed (k := k) n hd1 π ha h0 h3 (m + 1) (by omega)
    refine Submodule.finiteDimensional_of_le (S₂ := fixed (_root_.GlobalTheory.SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π)
      (PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd1)) ?_
    intro w hw u
    have h1 := (Submodule.mem_iInf _).1 hw u
    have h2 : (_root_.GlobalTheory.SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π (u : Levi k (fun _ : Fin n => Fin 1)) - 1) w = 0 := h1
    have h3' : _root_.GlobalTheory.SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π (u : Levi k (fun _ : Fin n => Fin 1)) w = w := by
      simpa [sub_eq_zero] using h2
    simpa using h3'
  obtain ⟨f, hf0, hf⟩ := GlobalTheory.T.generalized_eigenvector_exists (Levi k (fun _ : Fin n => Fin 1))
    (Jacquet π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd1)))
    (_root_.GlobalTheory.SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π) hcomm
    (fun m => PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd1) hanti hpow hsm hfd
    (GlobalTheory.CompanionTheory.PinLift.torusCharHom ξ) v hv0 hv
  obtain ⟨g, w, hg⟩ := GlobalTheory.T.jacquet_cuspidal_support_of_functional n π ξ hξ hd f hf0 hf
  obtain ⟨G, x, hx⟩ := GlobalTheory.CompanionTheory.FrobInv.exists_map_prodIrr (fun a => IrrGL.ofChar (ξ a) (hξ a)) hd π hs g ⟨w, hg⟩
  refine ⟨G, ?_⟩
  have hso : IsSimpleOrder (Subrepresentation π) := hirr
  have hk : ∀ y, y ∈ G.ker.toSubmodule ↔ G y = 0 := fun y => Iff.rfl
  rcases eq_bot_or_eq_top G.ker with h0' | h0'
  · refine (injective_iff_map_eq_zero G.toLinearMap).2 fun y hy => ?_
    have hy' : y ∈ G.ker.toSubmodule := (hk y).2 hy
    rw [h0'] at hy'
    exact (Submodule.mem_bot ℂ).1 hy'
  · refine absurd ((hk x).1 ?_) hx
    rw [h0']
    trivial

end GlobalTheory.CompanionTheory.GlFrob
end

section

open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.KFinSmoothBoth

theorem kFin_smooth_both : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam →
    Formalism.MainNotions.S.IsDS ε lam σ → ∀ v : H, Formalism.MainNotions.S.IsKFin ε σ v →
    v ∈ GlobalTheory.SmoothVecMod.smoothVec ε σ ∧ v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) σ := by
  intro n ε lam H _ _ σ _ hσ v hv
  have : CompleteSpace H := hσ.1
  have h : Formalism.QuantumDeterminants.SmoothOnH (Formalism.REAL.Jm ε) fun g => σ g v :=
    GlobalTheory.Published.KFiniteVectorsUnitary.smoothOnH
      GlobalTheory.CompanionTheory.Published.kFiniteVectors_irreducibleUnitary_unitaryGroupPQ
      hσ.2.2.1 hσ.2.2.2.1 hv
  exact ⟨h, h⟩

end GlobalTheory.CompanionTheory.KFinSmoothBoth
end
