module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle926
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1884
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1817
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1879
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1336
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsUnitaryOfOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1881
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.LeafHypothesesConst
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.WachBlock

theorem wach_inputs : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (σ : Equiv.Perm (E →+* PadicAlgCl l)), IsFrobPerm σ → ∀ (n t h : ℕ) (J : (E →+* PadicAlgCl l) → Fin n → ℤ) (bot : (E →+* PadicAlgCl l) → ℤ), (∀ i a, 0 ≤ J i a ∧ J i a ≤ h) → (∀ i (s : Fin t), 0 ≤ bot i + ((s : ℕ) : ℤ) ∧ bot i + ((s : ℕ) : ℤ) ≤ h) → BlockPair E Ω l n t J bot → ∃ (O' F L' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : Algebra ℤ_[l] O') (_ : Field F) (_ : CharP F l) (_ : Field L') (I : Ideal O') (_ : IsAdicComplete I O') (Wl : Formalism.CohomologicalDescent.FrobeniusPeriodChange.WLat (E →+* PadicAlgCl l) t n O' F) (u : ℤ_[l]ˣ) (c : ℤ_[l]) (kap : (E →+* PadicAlgCl l) → Fin t → ℤ) (ζ : O') (em : O' →+* L') (jj : ℕ → PowerSeries O' →+* PowerSeries L'), Formalism.CohomologicalDescent.FrobeniusPeriodChange.NInputs Wl σ l h u c J (fun i s => bot i + ((s : ℕ) : ℤ)) kap I ζ em jj := by
  intro hBS E Ω _ _ _ _ _ _ l _ hl2 hdisc σ hσ n t h J bot hJ hbot hBP
  obtain ⟨O', F, L', i1, i2, i3, i4, i5, i6, I, i7, red, un, N, Npsi, u, c, ζ, em, jj, hU, hR, hN, hψ, hF⟩ :=
    GlobalTheory.T.wachLattices_rankOne_models_reducedFiltration hBS E Ω l hl2 hdisc σ hσ n t h J bot hJ hbot (GlobalTheory.T.integralCrystallineBlockData_of_reductionPair E Ω l n t J bot hBP)
  obtain ⟨g, b, pos, w, kap, hpos, hP, hG, hPd, hGd⟩ :=
    GlobalTheory.T.adaptedBases_blockTriangular_of_reducedEtaleFiltration _ σ l n t F _ _ _ _ _ (Fact.out : l.Prime).pos inferInstance hF
  exact ⟨O', F, L', i1, i2, i3, i4, i5, i6, I, i7, ⟨red, un, N, Npsi, g, b, pos, w⟩, u, c, kap, ζ, em, jj,
    ⟨hU, hJ, hbot, hpos, hP, hG, hPd, hGd⟩, hR, hN, hψ⟩

end GlobalTheory.WachBlock

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.restrictsToQuadraticSignPow_of_restrictsToQuadraticCharPow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 →
    ∀ (χ : (AF F ⊗[F] E)ˣ →* Circle) (n : ℕ), GlobalTheory.LFun.ResEta F E χ n →
      GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ n := by
  first | exact @GlobalTheory.LFun.resEtaPow_of_resEta | exact GlobalTheory.LFun.resEtaPow_of_resEta | (intros; apply GlobalTheory.LFun.resEtaPow_of_resEta <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section


theorem _root_.GlobalTheory.T.chiGridVertexRank_add_lt_two_exponent_add_centre : ∀ {D : D7} (C : ℝ) (τ : D.what₂.Tau) (i j : ℕ) (hi : i < D.R.m) (hj : j < D.R.m),
    ((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℚ) < 2 * (D.hc τ).e ⟨j, hj⟩ + 2 * (cen D C τ (D.R.m - i) : ℚ) := by
  first | exact @GlobalTheory.ChiGrid.rankV_add_lt_two_e_add_two_cen | exact GlobalTheory.ChiGrid.rankV_add_lt_two_e_add_two_cen | (intros; apply GlobalTheory.ChiGrid.rankV_add_lt_two_e_add_two_cen <;> assumption)
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section
namespace GlobalTheory.LocFin

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

theorem inf_le_cptPart (T K : Subgroup G) (hK : IsCompact (K : Set G)) : T ⊓ K ≤ cptPart T := by
  intro g hg
  apply Subgroup.subset_closure
  refine ⟨hg.1, ?_⟩
  have hzp : (Subgroup.zpowers g : Set G) ⊆ K := (Subgroup.zpowers_le (G := G) (H := K)).2 hg.2
  exact hK.of_isClosed_subset isClosed_closure (closure_minimal hzp hK.isClosed)

theorem isCompact_map_conj (K : Subgroup G) (hK : IsCompact (K : Set G)) (x : G) :
    IsCompact ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.coe_map]
  have hc : Continuous fun a : G => x * a * x⁻¹ := by fun_prop
  exact hK.image hc

theorem isOpen_map_conj (K : Subgroup G) (hK : IsOpen (K : Set G)) (x : G) :
    IsOpen ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.coe_map]
  exact (Homeomorph.mulLeft x |>.trans (Homeomorph.mulRight x⁻¹)).isOpenMap _ hK

theorem relIndex_ne_zero_of_isOpen (A H : Subgroup G) (hA : IsOpen (A : Set G)) (hH : IsCompact (H : Set G)) :
    A.relIndex H ≠ 0 := by
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH
  have ho : IsOpen ((A.subgroupOf H : Subgroup H) : Set H) := hA.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.index_ne_zero_of_finite

theorem relIndex_cptPart_ne_zero (T A H : Subgroup G) (hA : IsOpen (A : Set G)) (hH : IsCompact (H : Set G))
    (hTH : cptPart T ≤ H) : (T ⊓ A).relIndex (cptPart T) ≠ 0 := by
  have hPT : cptPart T ≤ T := by
    rw [cptPart, Subgroup.closure_le]; exact fun t ht => ht.1
  have e : (T ⊓ A) ⊓ cptPart T = A ⊓ cptPart T := by
    ext g; simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hPT h.2, h.1⟩, h.2⟩⟩
  rw [← Subgroup.inf_relIndex_right, e, Subgroup.inf_relIndex_right]
  have h1 := relIndex_ne_zero_of_isOpen A H hA hH
  have : (A.subgroupOf H).FiniteIndex := ⟨h1⟩
  have : Finite (cptPart T ⧸ A.subgroupOf (cptPart T)) :=
    Finite.of_injective _ (Subgroup.quotientSubgroupOfEmbeddingOfLE A hTH).injective
  exact Subgroup.index_ne_zero_of_finite

theorem finite_of_subset_mul (T K' : Subgroup G) (hK' : IsOpen (K' : Set G)) (D : Set G) (hD : IsCompact D)
    (P : G → Prop) (hP : ∀ x, P x → ∃ t ∈ T, ∃ d ∈ D, x = t * d) :
    {q : DoubleCoset.Quotient (T : Set G) (K' : Set G) | P (Quotient.out q)}.Finite := by
  obtain ⟨s, hs⟩ := compact_covered_by_mul_left_translates hD
    (show (interior (K' : Set G)).Nonempty from ⟨1, hK'.interior_eq.symm ▸ K'.one_mem⟩)
  refine (s.finite_toSet.image fun g => DoubleCoset.mk T K' g⁻¹).subset ?_
  intro q hq
  obtain ⟨t, ht, d, hd, hx⟩ := hP _ hq
  have := hs hd
  simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe] at this
  obtain ⟨g, hg, hgd⟩ := this
  refine ⟨g, hg, ?_⟩
  rw [← DoubleCoset.out_eq' q, DoubleCoset.eq]
  exact ⟨t, ht, g * d, hgd, by simp [hx, mul_assoc]⟩

end Generic

section Main

theorem hKT : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E), Continuous (thL n w) ∧ ∀ g : GLw n w, thL n w (thL n w g) = g := GlobalTheory.T.continuous_involutive_local_transpose_inverse

theorem hKPa : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (N : GLw n w), N.val.charpoly.Separable → ∀ C : Set (GLw n w), IsCompact C → ∃ D : Set (GLw n w), IsCompact D ∧ ∀ x : GLw n w, x⁻¹ * N * x ∈ C → ∃ z : GLw n w, z * N = N * z ∧ ∃ d ∈ D, x = z * d := GlobalTheory.T.orbit_compact_mod_centralizer_separable_local

theorem hKA : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : GLw n w), (nrmL n w y).val.charpoly.Separable → ∃ H : Subgroup (GLw n w), IsCompact (H : Set (GLw n w)) ∧ cptPart (twCent (thL n w) y) ≤ H := GlobalTheory.T.exists_compact_ge_compactPart_twistedCentralizer

theorem hKPb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : GLw n w), (nrmL n w y).val.charpoly.Separable → ∀ C : Set (GLw n w), IsCompact C → ∃ D : Set (GLw n w), IsCompact D ∧ ∀ z : GLw n w, z * nrmL n w y = nrmL n w y * z → z⁻¹ * y * thL n w z ∈ C → ∃ t ∈ twCent (thL n w) y, ∃ d ∈ D, z = t * d := GlobalTheory.T.normCommuting_twistedConj_compact_mem_twistedCentralizer_mul

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem nrmL_twConj (hU : Unr E) (n : ℕ) (w : Pl E) (x y : GLw n w) :
    nrmL n w (x⁻¹ * y * thL n w x) = x⁻¹ * nrmL n w y * x := by
  by_cases hs : IsSplitAt w
  · have h1 : thL n w = MonoidHom.id _ := by rw [thL, if_pos hs]
    simp only [nrmL, if_pos hs, h1, MonoidHom.id_apply]
  · have h1 : thL n w = thetaGL n (cj w) := by rw [thL, if_neg hs]
    have h2 := (hKT E hU n w).2
    rw [h1] at h2
    simp only [nrmL, if_neg hs, h1, map_mul, map_inv, h2]
    group

theorem continuous_nrmL (hU : Unr E) (n : ℕ) (w : Pl E) : Continuous (nrmL n w) := by
  by_cases hs : IsSplitAt w
  · have e : nrmL n w = fun u => u := funext fun u => by simp [nrmL, hs]
    rw [e]; exact continuous_id
  · have h1 : thL n w = thetaGL n (cj w) := by rw [thL, if_neg hs]
    have hc := (hKT E hU n w).1
    rw [h1] at hc
    have e : nrmL n w = fun u => u * thetaGL n (cj w) u := funext fun u => by simp [nrmL, hs]
    rw [e]; exact continuous_id.mul hc

theorem proper (hU : Unr E) (n : ℕ) (w : Pl E) (y : GLw n w) (hy : (nrmL n w y).val.charpoly.Separable)
    (C : Set (GLw n w)) (hC : IsCompact C) : ∃ D : Set (GLw n w), IsCompact D ∧
      ∀ x : GLw n w, x⁻¹ * y * thL n w x ∈ C → ∃ t ∈ twCent (thL n w) y, ∃ d ∈ D, x = t * d := by
  have hθ := (hKT E hU n w).1
  obtain ⟨D₁, hD₁, h₁⟩ := hKPa E hU n w (nrmL n w y) hy _ (hC.image (continuous_nrmL hU n w))
  set C₂ := (fun p : GLw n w × GLw n w × GLw n w => p.1 * p.2.1 * (thL n w p.2.2)⁻¹) '' (D₁ ×ˢ C ×ˢ D₁)
  have hC₂ : IsCompact C₂ := (hD₁.prod (hC.prod hD₁)).image (by fun_prop)
  obtain ⟨D₂, hD₂, h₂⟩ := hKPb E hU n w y hy C₂ hC₂
  refine ⟨(fun p : GLw n w × GLw n w => p.1 * p.2) '' (D₂ ×ˢ D₁), (hD₂.prod hD₁).image (by fun_prop), ?_⟩
  intro x hx
  obtain ⟨z, hz, d, hd, rfl⟩ := h₁ x ⟨_, hx, by rw [nrmL_twConj hU]⟩
  have hz2 : z⁻¹ * y * thL n w z ∈ C₂ := ⟨(d, (z * d)⁻¹ * y * thL n w (z * d), d), ⟨hd, hx, hd⟩, by
    simp only [map_mul]; group⟩
  obtain ⟨t, ht, d₂, hd₂, rfl⟩ := h₂ z hz hz2
  exact ⟨t, ht, d₂ * d, ⟨(d₂, d), ⟨hd₂, hd⟩, rfl⟩, by group⟩

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : GLw n w), (nrmL n w y).val.charpoly.Separable → ∀ K' : Subgroup (GLw n w), IsLevel (thL n w) (GlobalTheory.LFun.KGL w (n := n)) K' → (∀ x : GLw n w, twCent (thL n w) y ⊓ (GlobalTheory.LFun.KGL w (n := n)).map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent (thL n w) y) ∧ (twCent (thL n w) y ⊓ K'.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent (thL n w) y)) ≠ 0) ∧ ∀ C : Set (GLw n w), IsCompact C → {q : DoubleCoset.Quotient (twCent (thL n w) y : Set (GLw n w)) (K' : Set (GLw n w)) | (Quotient.out q)⁻¹ * y * thL n w (Quotient.out q) ∈ C}.Finite := by
  intro E _ _ _ hU n w y hy K' hK'
  obtain ⟨hK'o, hK'K, -⟩ := hK'
  obtain ⟨hKo, hKc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n
  obtain ⟨H, hH, hPH⟩ := hKA E hU n w y hy
  refine ⟨fun x => ⟨inf_le_cptPart _ _ (isCompact_map_conj _ hKc x),
    relIndex_cptPart_ne_zero _ _ H (isOpen_map_conj _ hK'o x) hH hPH⟩, fun C hC => ?_⟩
  obtain ⟨D, hD, hP⟩ := proper hU n w y hy C hC
  exact finite_of_subset_mul _ K' hK'o D hD _ hP

end Main

end GlobalTheory.LocFin
end
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

theorem _root_.GlobalTheory.T.congruence_subgroup_indicator_weight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n a b k : ℕ), a + b = n → 1 ≤ k → Match n a b w 1 ((({γ : UL n w | γ.1 ∈ {g : GLw n w | g ∈ GlobalTheory.LFun.KGL w (n := n) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))}} : Set (UL n w))).indicator 1) (fun y : GLw a w × GLw b w => ((-((Real.sqrt (qV E w : ℝ) : ℝ) : ℂ)) ^ (k * a * b))⁻¹ * (if y.1 ∈ GlobalTheory.LFun.KGL w (n := a) ∧ nrmL a w y.1 ∈ {g : GLw a w | g ∈ GlobalTheory.LFun.KGL w (n := a) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} ∧ y.2 ∈ GlobalTheory.LFun.KGL w (n := b) ∧ nrmL b w y.2 ∈ {g : GLw b w | g ∈ GlobalTheory.LFun.KGL w (n := b) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0)) := by
  first | exact @GlobalTheory.CongMatch.match_principal_congruence_inert | exact GlobalTheory.CongMatch.match_principal_congruence_inert | (intros; apply GlobalTheory.CongMatch.match_principal_congruence_inert <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LatSplit

open GlobalTheory.AdelicU.Supp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem singleTens_tmul (v : Pl (F := F)) (a : Fv F v) (x : E) :
    singleTens E v (a ⊗ₜ[F] x) = GlobalTheory.LatVac.liftV v a ⊗ₜ[F] x := rfl

theorem tmul_smul_gen_mem {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) {a : Fv F v}
    (ha : a ∈ v.adicCompletionIntegers F) (o : 𝓞 E) {c : AF F} (hc : At (evFin F v) c)
    (hcv : evFin F v c ∈ v.adicCompletionIntegers F) {x : Fin n → E} (hx : x ∈ X.L) {y : Fin d → E} (hy : y ∈ W.L) :
    singleTens E v (a ⊗ₜ[F] (o : E)) • (c • incM F (Matrix.vecMulVec x y)) ∈ latAtV X W v := by
  refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v a * c, ?_, ?_, o • x, X.L.smul_mem o hx, y, hy, ?_⟩
  · intro u hu
    rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u c, hc u hu, mul_zero]
  · rw [map_mul, GlobalTheory.LatVac.evFin_liftV]
    exact mul_mem ha hcv
  · ext i j
    simp only [singleTens_tmul, Matrix.smul_apply, incM, Matrix.map_apply, Matrix.vecMulVec_apply, smul_eq_mul,
      Pi.smul_apply, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, inclR]
    change _ * ((c ⊗ₜ[F] (1:E)) * ((1:AF F) ⊗ₜ[F] (x i * y j))) =
      ((GlobalTheory.LatVac.liftV v a * c) ⊗ₜ[F] (1:E)) * ((1:AF F) ⊗ₜ[F] ((o:E) * x i * y j))
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_assoc]

theorem singleTens_smul_mem {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) {y : Fv F v ⊗[F] E}
    (hy : y ∈ intLoc F E v) {γ : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hγ : γ ∈ latAtV X W v) :
    singleTens E v y • γ ∈ latAtV X W v := by
  refine intLoc_induction (p := fun y => singleTens E v y • γ ∈ latAtV X W v) ?_ ?_ ?_ ?_ hy
  · intro a ha o
    induction hγ using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨c, hc, hcv, x, hx, y', hy', rfl⟩ := hz
      exact tmul_smul_gen_mem X W v ha o hc hcv hx hy'
    | zero => rw [smul_zero]; exact zero_mem _
    | add z z' _ _ h h' => rw [smul_add]; exact add_mem h h'
    | neg z _ h => rw [smul_neg]; exact neg_mem h
  · show singleTens E v 0 • γ ∈ latAtV X W v
    rw [map_zero, zero_smul]; exact zero_mem _
  · intro y z h h'
    show singleTens E v (y + z) • γ ∈ latAtV X W v
    rw [map_add (f := _), add_smul]; exact add_mem h h'
  · intro y h
    show singleTens E v (-y) • γ ∈ latAtV X W v
    rw [map_neg, neg_smul]; exact neg_mem h

theorem piW_splitIdemAd {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) :
    piW t (splitIdemAd hcm t) = 1 ∧ piW (t.comp σ) (splitIdemAd hcm t) = 0 := by
  constructor
  · change splitProj t (compFin F E v (singleTens E v (splitIdem hcm t))) = 1
    rw [compFin_singleTens_self, splitProj_splitIdem]
  · change splitProj (t.comp σ) (compFin F E v (singleTens E v (splitIdem hcm t))) = 0
    rw [compFin_singleTens_self, splitProj_comp_splitIdem]

theorem latAtV_decomp : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ},
    IsCMExt F E σ → ∀ (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v), ∀ γ ∈ latAtV X W v,
      ∃ γ₁ ∈ latAtV X W v, ∃ γ₂ ∈ latAtV X W v, γ = γ₁ + γ₂ ∧ γ₁.map (piW (t.comp σ)) = 0 ∧ γ₂.map (piW t) = 0 := by
  intro F E _ _ _ _ _ σ n d hcm X W v t γ hγ
  have h1 : splitIdemAd hcm t • γ ∈ latAtV X W v := singleTens_smul_mem X W v (splitIdem_mem hcm t) hγ
  obtain ⟨e1, e0⟩ := piW_splitIdemAd hcm t
  refine ⟨splitIdemAd hcm t • γ, h1, γ - splitIdemAd hcm t • γ, sub_mem hγ h1, (add_sub_cancel _ _).symm, ?_, ?_⟩
  · ext i j
    simp [smul_eq_mul, e0]
  · ext i j
    simp [smul_eq_mul, e1]

end GlobalTheory.LatSplit
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.HeisCoords

open Matrix

section Cplx

variable {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)

variable {J}

end Cplx

section Coords

variable {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ}

end Coords

section Transfer

open Formalism.UG (cT bc UJ)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {ν : InfinitePlace F}

theorem archMat_unitary (hcm : IsCMExt F E σ) (τ : EmbOver E ν) (g : HA ν.Completion σ J) :
    (GlobalTheory.Orb.archMat σ J τ g)ᴴ * J.map τ.1 * GlobalTheory.Orb.archMat σ J τ g = J.map τ.1 :=
  (archEquiv J hcm τ g).2

end Transfer

open Formalism.UG (cT bc UJ)

end GlobalTheory.HeisCoords

end
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

open GlobalTheory.Mem.Col2.SplitChar

namespace GlobalTheory.UnrKill

theorem exists_prime_mem {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) :
    ∃ q : ℕ, q.Prime ∧ ((q : ℕ) : 𝓞 K) ∈ P.asIdeal := by
  haveI := P.isPrime
  haveI : Finite (𝓞 K ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  refine ⟨ringChar (𝓞 K ⧸ P.asIdeal), CharP.char_is_prime (𝓞 K ⧸ P.asIdeal) _, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ringChar.spec]

theorem vl_nat_eq_one {D : D7} {q m : ℕ} (hm : Nat.Coprime m q) {v : HeightOneSpectrum (𝓞 D.host.E)}
    (hv : GlobalTheory.Mem.Chr.OverP D.host q v) : vl D v (m : AE D) = 1 := by
  refine le_antisymm (vl_le (natCast_mem _ _) v) (not_lt.1 fun hlt => ?_)
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hm
  have hab' := congrArg (Int.cast : ℤ → AE D) hab
  push_cast at hab'
  have h2 : vl D v ((a : AE D) * m) < 1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_left' (vl_le (intCast_mem _ _) v)).trans_lt hlt
  have h3 : vl D v ((b : AE D) * q) < 1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_left' (vl_le (intCast_mem _ _) v)).trans_lt (val_nat_lt hv)
  have h4 := Valuation.map_add_lt _ h2 h3
  rw [hab', map_one] at h4
  exact lt_irrefl _ h4

theorem vl_eq_zero_of_zeroAt {D : D7} {q : ℕ} {x : AE D} (h : ZeroAt D q x) {v : HeightOneSpectrum (𝓞 D.host.E)}
    (hv : GlobalTheory.Mem.Chr.OverP D.host q v) : vl D v x = 0 := by
  have hk : ∀ k : ℕ, vl D v x ≤ vl D v (q : AE D) ^ k := fun k => by
    obtain ⟨m, -, hm, s, hs, e⟩ := h k
    have h1 := vl_nat_eq_one hm hv
    rw [← one_mul (vl D v x), ← h1, ← map_mul, e, map_mul, map_pow]
    exact mul_le_of_le_one_right' (vl_le hs v)
  by_contra h0
  obtain ⟨k, hk'⟩ := exists_pow_lt₀ (val_nat_lt hv) (Units.mk0 _ h0)
  exact lt_irrefl _ ((hk k).trans_lt hk')

theorem unr_kill : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E), (∀ P : HeightOneSpectrum (𝓞 D.host.E), (∃ q : ℕ, q.Prime ∧ InertQ D q ∧ ((q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) → χ.UnrAt P) → ∀ u : (AE D)ˣ, IntU D u → (∀ q : ℕ, q.Prime → ¬ InertQ D q → ZeroAt D q ((u : AE D) - 1)) → χ.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D u) = 1 := by
  intro D χ hχ u hu hz
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local D.host.E χ.1 χ.2.1 (finIdl D u) (finIdl_unit hu)
    (fun w => by rw [finIdl_fst]; rfl) ?_
  intro P x hx
  obtain ⟨q, hq, hqP⟩ := exists_prime_mem P
  by_cases hI : InertQ D q
  · have hunr := hχ P ⟨q, hq, hI, hqP⟩
    refine hunr x ?_
    show Valued.v (x : P.adicCompletion D.host.E) = 1
    rw [hx]
    exact finIdl_unit hu P
  · have h0 := vl_eq_zero_of_zeroAt (hz q hq hI) (v := P) hqP
    rw [← vl_sub_one, map_eq_zero, sub_eq_zero, ← hx] at h0
    have hx1 : x = 1 := Units.ext h0
    rw [hx1, map_one]
    exact map_one _

end GlobalTheory.UnrKill
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

theorem _root_.GlobalTheory.T.schurConstantsExistOnChain_of_cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), SchurAll R := by
  first | exact @GlobalTheory.Hk3.schurAll_of_cuspRapidDecay | exact GlobalTheory.Hk3.schurAll_of_cuspRapidDecay | (intros; apply GlobalTheory.Hk3.schurAll_of_cuspRapidDecay <;> assumption)
end
