module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DiscreteTopologyRationalPointsHermitianSpace
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviModulusOneLinearReductiveExpMulExp
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1449
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle237
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle133
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SatakeDualWeyl.Bundle001
public import Formalism.SatakeDualWeyl.StatementG
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle008

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU

namespace GlobalTheory.SplitIdx

variable {D : D7}

def intMat (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (m n : ℕ) :
    AddSubgroup (Matrix (Fin m) (Fin n) (v.adicCompletion F)) where
  carrier := {y | ∀ i j, y i j ∈ v.adicCompletionIntegers F}
  add_mem' hx hy i j := add_mem (hx i j) (hy i j)
  zero_mem' _ _ := zero_mem _
  neg_mem' hx i j := neg_mem (hx i j)

def mulL {K : Type} [CommRing K] {m n : ℕ} (P : Matrix (Fin m) (Fin m) K) :
    Matrix (Fin m) (Fin n) K →+ Matrix (Fin m) (Fin n) K :=
  AddMonoidHom.mk' (fun y => P * y) (Matrix.mul_add P)

def halfLat (S T : HSp D) (e : AE D) : AddSubgroup (WO S T) :=
  (latO S T (frameLat S) (frameLat T) fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T e

def actL (S T : HSp D) (h : GA D T) : WO S T →+ WO S T :=
  AddMonoidHom.mk' (actO S T 1 h) fun x y => by simp only [actO, Matrix.mul_add, Matrix.add_mul]

end GlobalTheory.SplitIdx

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DetVal

open Formalism.L2.Host (IsUnitAt IsUnifAt)

theorem isUnitAt_det_of_mem_KGL {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    {k : GL (Fin n) (w.adicCompletion E)} (hk : k ∈ GlobalTheory.LFun.KGL w (n := n)) :
    IsUnitAt w (Matrix.GeneralLinearGroup.det k) := by
  unfold GlobalTheory.LFun.KGL at hk
  obtain ⟨k', rfl⟩ := hk
  set c := Matrix.GeneralLinearGroup.det k' with hc
  have hdc : ((Matrix.GeneralLinearGroup.det (Formalism.UG.bc (Formalism.UG.Ov E w).subtype k') :
      (w.adicCompletion E)ˣ) : w.adicCompletion E) = ((c : Formalism.UG.Ov E w) : w.adicCompletion E) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hc, Matrix.GeneralLinearGroup.val_det_apply]
    unfold Formalism.UG.bc
    rw [Units.coe_map]
    exact (RingHom.map_det _ _).symm
  have hle : ∀ y : Formalism.UG.Ov E w, Valued.v (y : w.adicCompletion E) ≤ 1 := fun y =>
    (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers ..).1 y.2
  have h3 : Valued.v ((c : Formalism.UG.Ov E w) : w.adicCompletion E) *
      Valued.v ((↑c⁻¹ : Formalism.UG.Ov E w) : w.adicCompletion E) = 1 := by
    rw [← map_mul, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one, map_one]
  unfold Formalism.L2.Host.IsUnitAt
  rw [hdc]
  refine le_antisymm (hle _) ?_
  rw [← h3]
  exact mul_le_of_le_one_right' (hle _)

theorem locChar_det_doubleCoset : ∀ (D : D7) (T : HSp D) (χ : (AE D)ˣ →* Circle) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), UnrAt χ w → ∀ e, IsSplitChart D.sp.cm.sig T.gram (frameLat T) h e → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w (n := T.rank), ∀ k₂ ∈ KGL w (n := T.rank), ((locChar χ w (Matrix.GeneralLinearGroup.det (locMat D.sp.cm.sig T.gram h (e.symm (k₁ * t * k₂)))) : ℂˣ) : ℂ) = ((val χ w : ℂˣ) : ℂ) ^ (∑ i, d i) := by
  intro D T χ v w h hχ e he ϖ hϖ d t ht k₁ hk₁ k₂ hk₂
  obtain ⟨⟨a, -, hea⟩, -⟩ := he
  have hloc : ∀ g, locMat D.sp.cm.sig T.gram h g = a * e g * a⁻¹ := fun g => by
    rw [hea g]
    group
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    unfold IsUnifV at hϖ
    simp at hϖ
  set u : (w.adicCompletion D.host.E)ˣ := Units.mk0 ϖ hϖ0 with hu
  have hprod : ∀ s : Finset (Fin T.rank), ∏ i ∈ s, u ^ d i = u ^ ∑ i ∈ s, d i := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro j s hj ih
      rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, _root_.zpow_add]
  have hdt : Matrix.GeneralLinearGroup.det t = u ^ ∑ i, d i := by
    rw [← hprod]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, ht, Matrix.det_diagonal, Units.coe_prod]
    simp only [Units.val_zpow_eq_zpow_val, hu, Units.val_mk0]
  have hdet : Matrix.GeneralLinearGroup.det (locMat D.sp.cm.sig T.gram h (e.symm (k₁ * t * k₂))) =
      Matrix.GeneralLinearGroup.det k₁ * u ^ (∑ i, d i) * Matrix.GeneralLinearGroup.det k₂ := by
    simp only [hloc, MulEquiv.apply_symm_apply, map_mul, map_inv, hdt]
    rw [mul_comm (Matrix.GeneralLinearGroup.det a), mul_inv_cancel_right]
  have hunif := hχ.locChar_eq_val (x := u) (by
    show Valued.v (u : w.adicCompletion D.host.E) = WithZero.exp (-1 : ℤ)
    rw [hu, Units.val_mk0, hϖ]
    rfl)
  rw [hdet, map_mul, map_mul, hχ _ (isUnitAt_det_of_mem_KGL _ hk₁), hχ _ (isUnitAt_det_of_mem_KGL _ hk₂),
    one_mul, mul_one, map_zpow, hunif, Units.val_zpow_eq_zpow_val]

end GlobalTheory.DetVal
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix Topology

noncomputable section

namespace GlobalTheory.TrFinite

theorem finite_preimage_of_nhds_zero {A G : Type} [AddCommGroup A] [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] (f : A →+ G) {U : Set G} (hU : U ∈ 𝓝 (0 : G)) (h : ∀ x, f x ∈ U → x = 0)
    {K : Set G} (hK : IsCompact K) : {x | f x ∈ K}.Finite := by
  obtain ⟨V, hV0, hV⟩ : ∃ V ∈ 𝓝 (0 : G), ∀ a ∈ V, ∀ b ∈ V, a - b ∈ U := by
    have ht : Tendsto (fun p : G × G => p.1 - p.2) (𝓝 ((0 : G), (0 : G))) (𝓝 0) := by
      simpa using (continuous_sub.tendsto ((0 : G), (0 : G)))
    have h2 := ht hU
    rw [nhds_prod_eq] at h2
    obtain ⟨V1, h1, V2, h2', hs⟩ := Filter.mem_prod_iff.1 h2
    exact ⟨V1 ∩ V2, inter_mem h1 h2', fun a ha b hb => @hs (a, b) ⟨ha.1, hb.2⟩⟩
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun k => (fun y => y - k) ⁻¹' V) (fun k _ => by
    have hc : Continuous fun y : G => y - k := continuous_id.sub continuous_const
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hV0))
  have hsub : {x | f x ∈ K} ⊆ ⋃ k ∈ t, {x | f x - k ∈ V} := fun x hx => by
    have := ht hx
    simp only [Set.mem_iUnion, Set.mem_preimage] at this ⊢
    exact this
  refine Set.Finite.subset (Set.Finite.biUnion t.finite_toSet fun k _ => ?_) hsub
  refine Set.Subsingleton.finite fun x hx y hy => ?_
  have hm : f (x - y) ∈ U := by
    have := hV _ hx _ hy
    rwa [sub_sub_sub_cancel_right, ← map_sub] at this
  exact sub_eq_zero.1 (h _ hm)

theorem continuous_coeff_charpoly {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

end GlobalTheory.TrFinite

namespace GlobalTheory.TrFinite

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

theorem charpoly_conj_ratEmb (γ : GRat σ J) (x : GAd σ J) :
    (((matHom (AF F) σ J (x⁻¹ * ratEmb σ J γ * x) : GL (Fin n) (AF F ⊗[F] E)) :
      Matrix (Fin n) (Fin n) (AF F ⊗[F] E))).charpoly = γ.1.1.charpoly.map (inclR (AF F)) := by
  rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
    Matrix.charpoly_units_conj']
  exact Matrix.charpoly_map _ _

theorem finite_ratEmb_mem {K : Set (GAd σ J)} (hK : IsCompact K) : {γ : GRat σ J | ratEmb σ J γ ∈ K}.Finite := by
  haveI : DiscreteTopology (ratPts σ J) := GlobalTheory.RationalDiscrete.discreteTopology_HFinIn σ J
  have hcl : IsClosed (ratPts σ J : Set (GAd σ J)) := Subgroup.isClosed_of_discrete
  have hfin : ((Subtype.val : ratPts σ J → GAd σ J) ⁻¹' K).Finite :=
    (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK).finite_of_discrete
  let g : GRat σ J → ratPts σ J := fun γ => ⟨ratEmb σ J γ, range_ratEmb σ J ▸ ⟨γ, rfl⟩⟩
  have hg : Function.Injective g := fun a b h => ratEmb_injective σ J (congrArg Subtype.val h)
  exact Set.Finite.preimage (f := g) hg.injOn hfin

theorem finite_charpoly_and_ratPts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (C : Set (GAd σ J)), IsCompact C →
    {Q : E[X] | ∃ γ : GRat σ J, γ.1.1.charpoly = Q ∧ ∃ x, x⁻¹ * ratEmb σ J γ * x ∈ C}.Finite ∧
      ∀ x, {γ : GRat σ J | x⁻¹ * ratEmb σ J γ * x ∈ C}.Finite := by
  intro F E _ _ _ _ _ σ _ n J C hC
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := F) (E := E)
  refine ⟨?_, fun x => ?_⟩
  ·
    let c : Fin (n + 1) → GAd σ J → AF F ⊗[F] E := fun i g =>
      (((matHom (AF F) σ J g : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))).charpoly.coeff i
    have hc : ∀ i, Continuous (c i) := fun i =>
      (continuous_coeff_charpoly n i).comp (Units.continuous_val.comp continuous_subtype_val)
    obtain ⟨U, hU, hU0⟩ := GlobalTheory.RationalDiscrete.exists_nhds_zero_inclR (F := F) (E := E)
    let T : Fin (n + 1) → Set E := fun i => {e | (inclR (AF F)).toAddMonoidHom e ∈ c i '' C}
    have hT : ∀ i, (T i).Finite := fun i =>
      finite_preimage_of_nhds_zero _ hU hU0 (hC.image (hc i))
    let S := {Q : E[X] | ∃ γ : GRat σ J, γ.1.1.charpoly = Q ∧ ∃ x, x⁻¹ * ratEmb σ J γ * x ∈ C}
    let φ : E[X] → Fin (n + 1) → E := fun Q i => Q.coeff i
    have hdeg : ∀ Q ∈ S, Q.natDegree = n := by
      rintro Q ⟨γ, rfl, -⟩
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    have hinj : Set.InjOn φ S := fun P hP Q hQ h => by
      ext i
      by_cases hi : i ≤ n
      · exact congrFun h ⟨i, Nat.lt_succ_of_le hi⟩
      · push_neg at hi
        rw [coeff_eq_zero_of_natDegree_lt (by rw [hdeg P hP]; exact hi),
          coeff_eq_zero_of_natDegree_lt (by rw [hdeg Q hQ]; exact hi)]
    have himg : φ '' S ⊆ Set.pi Set.univ T := by
      rintro _ ⟨Q, ⟨γ, rfl, x, hx⟩, rfl⟩ i -
      refine ⟨_, hx, ?_⟩
      change (((matHom (AF F) σ J (x⁻¹ * ratEmb σ J γ * x) : GL (Fin n) (AF F ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (AF F ⊗[F] E))).charpoly.coeff i = inclR (AF F) (γ.1.1.charpoly.coeff i)
      rw [charpoly_conj_ratEmb, coeff_map]
    exact Set.Finite.of_finite_image ((Set.Finite.pi hT).subset himg) hinj
  · have hK : IsCompact ((fun g => x * g * x⁻¹) '' C) :=
      hC.image ((continuous_const.mul continuous_id).mul continuous_const)
    refine (finite_ratEmb_mem σ J hK).subset fun γ hγ => ⟨_, hγ, ?_⟩
    change x * (x⁻¹ * ratEmb σ J γ * x) * x⁻¹ = ratEmb σ J γ
    group

end GlobalTheory.TrFinite
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EigSpan

theorem eig_span : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (t : T) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ R.HE.H), (∀ P, GlobalTheory.Hk3.Good R t P → ∀ c x, R.HE.e (h P c x) = postOn (R.MY 0) (GlobalTheory.Hk3.hk (Yc D 0) P c) (R.HE.e x)) → ∀ P, GlobalTheory.Hk3.Good R t P → ∀ (a : List ℤ → ℂ) (w : R.HE.H) (s : Set (List ℤ →₀ ℂ)), (∀ c ∈ s, h P c w = GlobalTheory.Hk3.evC (Yc D 0) P a c • w) → ∀ c ∈ Submodule.span ℂ s, h P c w = GlobalTheory.Hk3.evC (Yc D 0) P a c • w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC t h hh P hP a w s hs c hc
  have inj : Function.Injective R.HE.e := hC.models.HE.1
  have hkAdd : ∀ c c' : List ℤ →₀ ℂ, GlobalTheory.Hk3.hk (Yc D 0) P (c + c') = GlobalTheory.Hk3.hk (Yc D 0) P c + GlobalTheory.Hk3.hk (Yc D 0) P c' :=
    fun c c' => by
      unfold GlobalTheory.Hk3.hk
      exact Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)
  have hkSmul : ∀ (z : ℂ) (c : List ℤ →₀ ℂ), GlobalTheory.Hk3.hk (Yc D 0) P (z • c) = z • GlobalTheory.Hk3.hk (Yc D 0) P c :=
    fun z c => by
      unfold GlobalTheory.Hk3.hk
      rw [Finsupp.sum_smul_index', Finsupp.smul_sum]
      · simp only [smul_eq_mul, mul_smul]
      · intro; exact zero_smul _ _
  have hkZero : GlobalTheory.Hk3.hk (Yc D 0) P 0 = 0 := by
    unfold GlobalTheory.Hk3.hk; exact Finsupp.sum_zero_index
  have evAdd : ∀ c c' : List ℤ →₀ ℂ, GlobalTheory.Hk3.evC (Yc D 0) P a (c + c') = GlobalTheory.Hk3.evC (Yc D 0) P a c + GlobalTheory.Hk3.evC (Yc D 0) P a c' :=
    fun c c' => by
      unfold GlobalTheory.Hk3.evC
      exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by split_ifs <;> ring)
  have evSmul : ∀ (z : ℂ) (c : List ℤ →₀ ℂ), GlobalTheory.Hk3.evC (Yc D 0) P a (z • c) = z * GlobalTheory.Hk3.evC (Yc D 0) P a c :=
    fun z c => by
      unfold GlobalTheory.Hk3.evC
      rw [Finsupp.sum_smul_index', Finsupp.mul_sum]
      · exact Finsupp.sum_congr fun d _ => by split_ifs <;> simp [mul_assoc]
      · intro; simp
  have evZero : GlobalTheory.Hk3.evC (Yc D 0) P a 0 = 0 := by
    unfold GlobalTheory.Hk3.evC; exact Finsupp.sum_zero_index
  have pAdd : ∀ L L' x, postOn (R.MY 0) (L + L') x = postOn (R.MY 0) L x + postOn (R.MY 0) L' x := by
    intro L L' x; ext v; simp [postOn]
  have pSmul : ∀ (z : ℂ) L x, postOn (R.MY 0) (z • L) x = z • postOn (R.MY 0) L x := by
    intro z L x; ext v; simp [postOn]
  have pZero : ∀ x, postOn (R.MY 0) 0 x = 0 := by
    intro x; ext v; simp [postOn]
  have hAdd : ∀ c c', h P (c + c') w = h P c w + h P c' w := fun c c' =>
    inj (by rw [hh P hP, map_add (f := _), hh P hP, hh P hP, hkAdd, pAdd])
  have hSmul : ∀ (z : ℂ) c, h P (z • c) w = z • h P c w := fun z c =>
    inj (by rw [hh P hP, map_smul, hh P hP, hkSmul, pSmul])
  have hZero : h P 0 w = 0 := inj (by rw [hh P hP, hkZero, pZero, map_zero])
  induction hc using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => rw [hZero, evZero, zero_smul]
  | add x y _ _ hx hy => rw [hAdd, hx, hy, evAdd, add_smul]
  | smul z x _ hx => rw [hSmul, hx, evSmul, mul_smul]

end GlobalTheory.EigSpan
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.TwistPlaces

theorem typePlaces_disjoint_twistPlaces : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ t : T, Disjoint R.Pg (R.Q t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC t
  have hL := hC.lev
  rw [Finset.disjoint_left]
  intro PP hPg hQ
  obtain ⟨k, hk⟩ := (hL.Pg PP).1 hPg
  obtain ⟨⟨q, hq, hcard, -, hne⟩, -⟩ := hL.Q_pl t PP hQ
  have hmemK : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (PP.under (𝓞 D.host.K)).asIdeal := by
    have h := R.C.P.pb_over k
    have hk' : PP.under (𝓞 D.host.K) = R.C.P.pb k := hk
    rw [hk']; exact h
  have hmemE : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := hmemK
    simpa using h2
  haveI : Finite (kP PP) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hq.ne_zero)
  have : PP.asIdeal.IsPrime := PP.isPrime
  haveI : Nontrivial (kP PP) := inferInstance
  haveI : Fintype (kP PP) := Fintype.ofFinite _
  have h0g : ((D.host.g k : ℕ) : kP PP) = 0 := by
    have := (Ideal.Quotient.eq_zero_iff_mem (I := PP.asIdeal)).2 hmemE
    simpa using this
  have h0q : ((q : ℕ) : kP PP) = 0 := by
    rw [← hcard, Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero (kP PP)
  have hd1 : ringChar (kP PP) ∣ D.host.g k := ringChar.dvd h0g
  have hd2 : ringChar (kP PP) ∣ q := ringChar.dvd h0q
  have hcop : Nat.Coprime q (D.host.g k) := (Nat.coprime_primes hq (D.host.g_prime k)).2 (hne k)
  have h1 : ringChar (kP PP) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd2 hd1
  exact CharP.ringChar_ne_one h1

end GlobalTheory.TwistPlaces
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.realPointIdentification_leastSize_linear_growth : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ g ∈ GinfC (D.sp.Y 0), (iotaX X h g).2 = 1) ∧ (1 ≤ (D.sp.Y 0).rank → ∀ x : X.B.I.GA, ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ GinfC (D.sp.Y 0), (GlobalTheory.Count.tau1 X.B.I (x * iotaX X h g))⁻¹ ≤ C * normInf R.θ (D.sp.Y 0) g) := by
  first | exact @GlobalTheory.IotaNorm.iotaX_norm | exact GlobalTheory.IotaNorm.iotaX_norm | (intros; apply GlobalTheory.IotaNorm.iotaX_norm <;> assumption)
end

section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

theorem _root_.GlobalTheory.T.leviModulusOne_linearReductive_exp_mul_exp : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Flag n a), IsIsoFlag ε j W → (∀ i, 1 ≤ j i) → GlobalTheory.LinRed.IsLinRed (mats (leviOne ε W)) ∧ ∀ g ∈ mats (leviOne ε W), ∃ X Y : Matrix (Fin n) (Fin n) ℂ, (∀ t : ℝ, NormedSpace.exp (t • X) ∈ mats (leviOne ε W)) ∧ (∀ t : ℝ, NormedSpace.exp (t • Y) ∈ mats (leviOne ε W)) ∧ g = NormedSpace.exp X * NormedSpace.exp Y := by
  first | exact @GlobalTheory.LeviPolar.isLinRed_leviOne | exact GlobalTheory.LeviPolar.isLinRed_leviOne | (intros; apply GlobalTheory.LeviPolar.isLinRed_leviOne <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Links

theorem _root_.GlobalTheory.T.card_weightSet_grid_eq_gridRowSpaceRank : ∀ (D : D7), HostHyp D → ∀ (τ : D.what₂.Tau) (j : ℕ), 1 ≤ j → j ≤ D.R.m → ((GlobalTheory.Grid.grid D τ).weightX j).card = GlobalTheory.Grid.rkX D j := by
  first | exact @GlobalTheory.Grid.card_weightX_grid | exact GlobalTheory.Grid.card_weightX_grid | (intros; apply GlobalTheory.Grid.card_weightX_grid <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical

theorem _root_.GlobalTheory.T.realMetaplectic_family_derivative_quadratic : GlobalTheory.Published.RealMetaplecticRepresentation → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V), μ.IsAddHaarMeasure → ∀ (P : V → V → ℝ), IsPairing P →
    ∀ (A : ℝ → (V × V) →ₗ[ℝ] (V × V)) (T : ℝ → 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ)),
    (∀ v, Continuous fun t => A t v) →
    (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) →
    (∀ t v (f f₁ : 𝓢(V, ℂ)), ⇑f₁ = schrF P v ⇑f → ⇑(T t f₁) = schrF P (A t v) ⇑(T t f)) →
    (∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    (∀ f y, Continuous fun t => T t f y) →
    (∀ f φ : 𝓢(V, ℂ), Continuous fun t => ∫ x, T t f x * starRingEnd ℂ (φ x) ∂μ) →
    ∃ (m : ℕ) (a b : Fin m → V × V) (c : Fin m → ℂ) (c₀ : ℂ), ∀ (f : 𝓢(V, ℂ)) (g₁ g₂ : Fin m → 𝓢(V, ℂ)),
      (∀ i y, g₁ i y = fderiv ℝ (⇑f) y (b i).1 - 2 * Real.pi * Complex.I * (P y (b i).2 : ℂ) * f y) →
      (∀ i y, g₂ i y = fderiv ℝ (⇑(g₁ i)) y (a i).1 - 2 * Real.pi * Complex.I * (P y (a i).2 : ℂ) * g₁ i y) →
      ∀ y, HasDerivAt (fun t => T t f y) (∑ i, c i * g₂ i y + c₀ * f y) 0 := by
  first | exact @GlobalTheory.QuadFam.deriv_quad | exact GlobalTheory.QuadFam.deriv_quad | (intros; apply GlobalTheory.QuadFam.deriv_quad <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_admissible_unipotent_at_split_place : (∀ {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) O),
    IsUnit (Matrix.fromBlocks A B C D).det → ∃ X : Matrix (Fin n) (Fin n) O, IsUnit (A + X * C).det) →
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (V : Spc F E d) (r s : ℕ), B.IsGood σ → V.IsHerm σ B r s →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal → ∀ g ∈ GlobalTheory.DblVac.KD σ V v,
      ∃ Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) Y ∧
        (∀ z ∈ GlobalTheory.InertSph.latAt V v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt V v) ∧
        Yᵀ * incM F V.J + incM F V.J * Y.map (cA σ) = 0 ∧
        ∃ M : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), M * (GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂))) = 1 ∧
          ∀ z ∈ GlobalTheory.InertSph.latAt V v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt V v := by
  first | exact @GlobalTheory.SplitChooseHerm.exists_admissible_unipotent_split_place_hermitian | exact GlobalTheory.SplitChooseHerm.exists_admissible_unipotent_split_place_hermitian | (intros; apply GlobalTheory.SplitChooseHerm.exists_admissible_unipotent_split_place_hermitian <;> assumption)
end
