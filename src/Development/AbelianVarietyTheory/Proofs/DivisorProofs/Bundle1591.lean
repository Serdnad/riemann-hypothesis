module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1534
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle295
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteL2ABoundWords
public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCB
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle404
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankZetaSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle451
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormFiniteZerosOnLineCmExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1555
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish

@[expose] public section

section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.localTensorCenterInclusion_injective_central_finrank : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), Function.Injective (iotaF G v) ∧ (∀ z x, Commute (iotaF G v z) x) ∧ Module.finrank (Qv v) (Qv v ⊗[ℚ] G.C) = G.n ^ 2 * Module.finrank (Qv v) (Qv v ⊗[ℚ] G.F) := by
  first | (exact @GlobalTheory.OrbFinAf.iotaF_props) | (exact GlobalTheory.OrbFinAf.iotaF_props) | (intros; apply GlobalTheory.OrbFinAf.iotaF_props  <;> assumption)
end

section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.integralLocalCenter_finite_maximal_ideals : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1) (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)), Set.Finite {I : Ideal (intF G v h1 hm) | I.IsMaximal} := by
  first | (exact @GlobalTheory.OrbFinAf.intF_finite_maximal) | (exact GlobalTheory.OrbFinAf.intF_finite_maximal) | (intros; apply GlobalTheory.OrbFinAf.intF_finite_maximal  <;> assumption)
end

section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.powers_linearIndependent_over_localTensorCenter : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.C), (minpoly G.F γ).natDegree = G.n → ∀ (v : AwayP p) (c : Fin G.n → Qv v ⊗[ℚ] G.F), ∑ i, iotaF G v (c i) * (1 : Qv v) ⊗ₜ[ℚ] γ ^ (i : ℕ) = 0 → c = 0 := by
  first | (exact @GlobalTheory.OrbFinAf.pow_indep_tensor) | (exact GlobalTheory.OrbFinAf.pow_indep_tensor) | (intros; apply GlobalTheory.OrbFinAf.pow_indep_tensor  <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

namespace GlobalTheory.PlaneNorm

theorem exists_local_unitNorm_vector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → (∃ u : Fin M → K ⊗[F] E, u ≠ 0 ∧ hR K σ J u u = 0) → ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ w : Fin M → K ⊗[F] E, IsUnitNorm K σ (-(gram2R K σ J (fun i => inclR K (x i)) w)) ∧ IsUnitNorm K σ (-(gram2R K σ J w (fun i => inclR K (y i)))) := by
  intro F E _ _ _ _ _ σ hcm K _ _ M J hM hJ hiso x y hx hy
  have hinj : Function.Injective (inclR (F := F) K : E →+* K ⊗[F] E) := Algebra.TensorProduct.includeRight_injective (algebraMap F K).injective
  have hne : ∀ z : Fin M → E, hE σ J z z ≠ 0 → ((fun i => inclR K (z i)) : Fin M → K ⊗[F] E) ≠ 0 := by
    intro z hz h0
    apply hz
    have hz0 : z = 0 := funext fun i => hinj (by simpa using congrFun h0 i)
    subst hz0
    simp [hE, Formalism.UG.hform]
  rcases GlobalTheory.T.tensorCM_isField_or_norm_surjective F E σ hcm K with hfld | hspl
  · exact GlobalTheory.T.exists_unitNorm_gramDet_pair_fieldCase F E σ hcm K M J hJ hfld hiso _ _ (hne x hx) (hne y hy)
  · obtain ⟨w, hxw, hwy⟩ := GlobalTheory.T.exists_common_hermitianGramDetTwoVectors_ne F E σ hcm M J hM hJ x y hx hy
    have hs : ∀ e : E, sigR K σ (inclR K e) = inclR K (σ e) := fun e => rfl
    have hRE : ∀ a b : Fin M → E, hR K σ J (fun i => inclR K (a i)) (fun i => inclR K (b i)) =
        inclR K (hE σ J a b) := by
      intro a b

      simp only [hR, hE, Formalism.UG.hform, map_sum, map_mul, hs, JR, Matrix.map_apply, RingHom.coe_coe]
    have hG : ∀ a b : Fin M → E, gram2R K σ J (fun i => inclR K (a i)) (fun i => inclR K (b i)) =
        inclR K (gram2E σ J a b) := by
      intro a b
      simp only [gram2R, gram2E, hRE, map_sub, map_mul]
    have hsym : ∀ a b : Fin M → E, σ (hE σ J a b) = hE σ J b a := by
      intro a b

      simp only [hE, Formalism.UG.hform, map_sum, map_mul, RingHom.coe_coe, GlobalTheory.HermLineZeros.conj_invol hcm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hJ.1]
      ring
    have hfix : ∀ a b : Fin M → E, σ (gram2E σ J a b) = gram2E σ J a b := by
      intro a b
      simp only [gram2E, map_sub, map_mul, hsym]
      ring
    have key : ∀ a b : Fin M → E, gram2E σ J a b ≠ 0 →
        IsUnitNorm K σ (-(gram2R K σ J (fun i => inclR K (a i)) (fun i => inclR K (b i)))) := by
      intro a b hab
      obtain ⟨g, hg⟩ := GlobalTheory.HermLineZeros.exists_of_fixed hcm _ (hfix a b)
      have hg0 : g ≠ 0 := by rintro rfl; exact hab (by rw [← hg, map_zero])
      have hk : algebraMap F K (-g) ≠ 0 := by
        rw [map_neg, neg_ne_zero, ne_eq, map_eq_zero_iff _ (algebraMap F K).injective]; exact hg0
      obtain ⟨t, ht⟩ := hspl _ hk
      have hval : -(gram2R K σ J (fun i => inclR K (a i)) (fun i => inclR K (b i))) =
          algebraMap K (K ⊗[F] E) (algebraMap F K (-g)) := by
        rw [hG, ← hg, map_neg, map_neg]
        congr 1
        rw [← IsScalarTower.algebraMap_apply]
        exact (Algebra.TensorProduct.includeRight : E →ₐ[F] K ⊗[F] E).commutes g
      have hu : IsUnit (t * sigR K σ t) := by
        rw [ht]; exact (IsUnit.mk0 _ hk).map _
      exact ⟨t, isUnit_of_mul_isUnit_left hu, by rw [ht, hval]⟩
    exact ⟨fun i => inclR K (w i), key x w hxw, key w y hwy⟩

end GlobalTheory.PlaneNorm
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical


theorem _root_.GlobalTheory.T.exists_finite_l2A_bound_words : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ → ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    ∀ (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (n : ℕ) (R : ℝ), ∃ B : ENNReal, B ≠ ⊤ ∧ ∀ ws : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)), ws.length = n → (∀ h ∈ ws, ‖h‖ ≤ R) →
      GlobalTheory.WeilL2Words.l2A F μ (GlobalTheory.WeilL2Words.word F ψ ws Φ) ≤ B := by
  first | exact @GlobalTheory.WeilL2Words.l2A_word_le | exact GlobalTheory.WeilL2Words.l2A_word_le | (intros; apply GlobalTheory.WeilL2Words.l2A_word_le <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.WeilL2Words.StdTheta

def negSum (F : Type) [Field F] [NumberField F] : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ :=
  -(∑ w : {w : InfinitePlace F // w.IsReal}, (LinearMap.proj w).comp (LinearMap.fst ℝ _ _))

theorem negSum_apply (F : Type) [Field F] [NumberField F] (z : mixedEmbedding.mixedSpace F) :
    negSum F z = -∑ w, z.1 w := by
  simp [negSum]

theorem negSum_nondeg (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (z : mixedEmbedding.mixedSpace F)
    (hz : z ≠ 0) : ∃ u, negSum F (z * u) ≠ 0 := by
  have h1 : z.1 ≠ 0 := by
    intro h0
    apply hz
    refine Prod.ext h0 (funext fun w => absurd (IsTotallyReal.isReal w.1) ?_)
    exact InfinitePlace.not_isReal_iff_isComplex.2 w.2
  obtain ⟨w, hw⟩ := Function.ne_iff.1 h1
  refine ⟨(Pi.single w 1, 0), ?_⟩
  rw [negSum_apply]
  simpa [Pi.single_apply] using hw

theorem cmTypeComponents_sum_eq_realCoordinates_sum (D : D7) (x : Ainf D.host.F) :
    ∑ ρ, Formalism.L2.Fam.ThC.th0 D ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)) =
      ((∑ w, (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F x).1 w : ℝ) : ℂ) := by
  haveI := D.sp.cm.totReal
  have e1 : ∀ ρ, Formalism.L2.Fam.ThC.th0 D ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)) =
      InfinitePlace.Completion.extensionEmbedding (GlobalTheory.AdelicU.placeOf D ρ) (x (GlobalTheory.AdelicU.placeOf D ρ)) := by
    intro ρ
    show Formalism.L2.Fam.ThC.projAt (tauE D ρ) (x ⊗ₜ[D.host.F] (1 : D.host.E)) = _
    rw [Formalism.L2.Fam.ThC.projAt_tmul, map_one, mul_one]
    rfl
  rw [Finset.sum_congr rfl fun ρ _ => e1 ρ,
    (GlobalTheory.AdelicU.placeOf_bijective D).sum_comp (fun w => InfinitePlace.Completion.extensionEmbedding w (x w)),
    Complex.ofReal_sum]
  refine (Fintype.sum_equiv (Equiv.subtypeUnivEquiv fun w : InfinitePlace D.host.F => IsTotallyReal.isReal w) _ _
    fun w => ?_).symm
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply w.2 (x w.1)

theorem isStdInf_of_isStdChar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    GlobalTheory.WeilL2Words.IsStdInf D.host.F ψ := by
  intro D ψ hψ
  haveI := D.sp.cm.totReal
  have h := Formalism.L2.Fam.ThC.allSome_fam.1 hψ.2
  refine ⟨negSum D.host.F, negSum_nondeg D.host.F, fun z => ?_⟩
  have hx := h ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm z)
  rw [cmTypeComponents_sum_eq_realCoordinates_sum, RingEquiv.apply_symm_apply] at hx
  show psiInf D.host.F ψ ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm z) = _
  rw [hx, negSum_apply]
  congr 1
  push_cast
  ring

end GlobalTheory.WeilL2Words.StdTheta
end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

noncomputable section

namespace GlobalTheory.SplitInvFormF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {xi0 : E}
  {ψ : AddChar (AF F) ℂ}


variable (σ) in
def conjHalf (e : AEF F E) (nS nT : ℕ) : AddSubgroup (WOF F E nS nT) where
  carrier := {u | ∀ i j, cAF σ e * u i j = u i j}
  add_mem' := fun {a b} ha hb i j => by
    simp only [Set.mem_setOf_eq] at ha hb
    rw [Matrix.add_apply, mul_add, ha i j, hb i j]
  zero_mem' := fun i j => by simp
  neg_mem' := fun {a} ha i j => by
    simp only [Set.mem_setOf_eq] at ha
    rw [Matrix.neg_apply, mul_neg, ha i j]


variable (σ JS JT xi0 ψ) in
def heisL (w : WOF F E nS nT) : (WOF F E nS nT → ℂ) →ₗ[ℂ] (WOF F E nS nT → ℂ) where
  toFun := heisOF σ JS JT xi0 ψ w
  map_add' := GlobalTheory.WeilPartsF.heisOF_add w
  map_smul' := fun c f => GlobalTheory.WeilPartsF.heisOF_smul c w f


variable (σ JS JT xi0 ψ) in
def commF (u y : WOF F E nS nT) : ℂ :=
  ψ (symplOHF σ JS JT xi0 u y - symplOHF σ JS JT xi0 y u)

theorem heisOF_heisOF (u y : WOF F E nS nT) (f : WOF F E nS nT → ℂ) :
    heisOF σ JS JT xi0 ψ u (heisOF σ JS JT xi0 ψ y f) =
      ψ (symplOHF σ JS JT xi0 u y) • heisOF σ JS JT xi0 ψ (u + y) f := by
  funext w
  simp only [heisOF, Pi.smul_apply, smul_eq_mul]
  rw [GlobalTheory.HeisThetaF.symplOHF_add_left w u y, GlobalTheory.HeisThetaF.symplOHF_add_right w u y,
    AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, add_assoc]
  ring

theorem heisOF_comm (u y : WOF F E nS nT) (f : WOF F E nS nT → ℂ) :
    heisOF σ JS JT xi0 ψ u (heisOF σ JS JT xi0 ψ y f) =
      commF σ JS JT xi0 ψ u y • heisOF σ JS JT xi0 ψ y (heisOF σ JS JT xi0 ψ u f) := by
  rw [heisOF_heisOF, heisOF_heisOF, smul_smul, add_comm y u, commF, ← AddChar.map_add_eq_mul, sub_add_cancel]

theorem heisOF_zero (f : WOF F E nS nT → ℂ) : heisOF σ JS JT xi0 ψ 0 f = f := by
  funext w
  simp only [heisOF, add_zero, GlobalTheory.HeisThetaF.symplOHF_zero_right, AddChar.map_zero_eq_one, one_mul]

theorem cAF_cAF {e : AEF F E} (he : IsSplitIdemF σ e) : cAF σ (cAF σ e) = e := by
  obtain ⟨-, -, v, ε, -, h⟩ := he
  have h2 := congrArg (cAF σ) h
  rw [map_add (f := _), GlobalTheory.HeisThetaF.cAF_algebraMap] at h2
  linear_combination h2 - h

theorem hOF_half {e : AEF F E} (he : IsSplitIdemF σ e) {x y : WOF F E nS nT} (hx : x ∈ conjHalf σ e nS nT)
    (hy : y ∈ conjHalf σ e nS nT) : hOF σ JS JT x y = 0 := by
  have hcc := cAF_cAF he
  have h2 : e * cAF σ e = 0 := he.2.1
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
    Finset.sum_eq_zero fun d _ => ?_
  have e1 : cAF σ (y c b) = e * cAF σ (y c b) := by
    conv_lhs => rw [← hy c b]
    rw [map_mul, hcc]
  rw [e1, ← hx d a]
  linear_combination (incAF F E (JS⁻¹ a b) * cAF σ (y c b) * incAF F E (JT c d) * x d a) * h2

theorem symplOHF_half {e : AEF F E} (he : IsSplitIdemF σ e) {x y : WOF F E nS nT} (hx : x ∈ conjHalf σ e nS nT)
    (hy : y ∈ conjHalf σ e nS nT) : symplOHF σ JS JT xi0 x y = 0 := by
  simp only [symplOHF, symplOF, hOF_half he hx hy, mul_zero, map_zero]

theorem exists_nsmul_fix {e : AEF F E} (he : IsSplitIdemF σ e) {u : WOF F E nS nT} (hu : u ∈ conjHalf σ e nS nT)
    {g : WOF F E nS nT → ℂ} (hg : IsThetaFunOF σ JS JT xi0 ψ g) :
    ∃ k : ℕ, 0 < k ∧ heisOF σ JS JT xi0 ψ (k • u) g = g := by
  obtain ⟨he1, he2, v, ε, hpl, hsum⟩ := he
  obtain ⟨α, rfl, hα1, hα0⟩ := id hpl
  obtain ⟨U, hU, hUf⟩ := hg.level
  haveI : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  haveI : ContinuousSMul (AF F) (AEF F E) := IsModuleTopology.toContinuousSMul (AF F) (AEF F E)
  set ε' := algebraMap (AF F) (AEF F E) (pairA F 0 α) with hε'
  have hcc : cAF σ e * cAF σ e = cAF σ e := by rw [← map_mul, he1]
  have hce : cAF σ e * ε' = cAF σ e := by
    rw [← hsum]
    linear_combination he2 + hcc
  have hu' : ∀ i j, ε' * u i j = u i j := fun i j => by
    have := hu i j
    calc ε' * u i j = ε' * (cAF σ e * u i j) := by rw [this]
      _ = (cAF σ e * ε') * u i j := by ring
      _ = u i j := by rw [hce, this]
  let φ : Af F → WOF F E nS nT := fun t i j => algebraMap (AF F) (AEF F E) (pairA F 0 t) * u i j
  have hφ : Continuous φ := by
    have h1 : Continuous fun t : Af F => algebraMap (AF F) (AEF F E) (pairA F 0 t) := by
      have : Continuous fun t : Af F => pairA F 0 t := continuous_const.prodMk continuous_id
      have h2 : Continuous fun c : AF F => algebraMap (AF F) (AEF F E) c := by
        simp only [Algebra.algebraMap_eq_smul_one]
        exact continuous_smul.comp (continuous_id.prodMk continuous_const)
      exact h2.comp this
    exact continuous_pi fun i => continuous_pi fun j => h1.mul continuous_const
  have h0 : φ 0 = 0 := by
    funext i j
    show algebraMap (AF F) (AEF F E) (pairA F 0 0) * u i j = 0
    rw [show pairA F 0 0 = (0 : AF F) from rfl, map_zero, zero_mul]
  have hV : φ ⁻¹' (U : Set (WOF F E nS nT)) ∈ nhds (0 : Af F) :=
    (hU.preimage hφ).mem_nhds (by rw [Set.mem_preimage, h0]; exact U.zero_mem)
  obtain ⟨N, hN, hNα⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hV
  have hint : ∀ w, α w ∈ w.adicCompletionIntegers F := fun w => by
    by_cases hw : w = v
    · subst hw
      rw [show α w = 1 from hα1]
      exact one_mem _
    · rw [show α w = 0 from hα0 w hw]
      exact zero_mem _
  have hmem := hNα α hint
  have heq : φ (N • α) = N • u := by
    funext i j
    show algebraMap (AF F) (AEF F E) (pairA F 0 (N • α)) * u i j = (N • u) i j
    rw [show pairA F 0 (N • α) = N • pairA F 0 α by
      show ((0 : Ainf F), N • α) = N • ((0 : Ainf F), α)
      rw [Prod.smul_mk, smul_zero], map_nsmul, smul_mul_assoc, hu' i j, Matrix.smul_apply]
  rw [Set.mem_preimage, heq] at hmem
  refine ⟨N, hN, hUf _ hmem ?_⟩
  ext i j
  show infPartF F E ((N • u) i j) = 0
  rw [Matrix.smul_apply, map_nsmul, ← hu' i j, map_mul, GlobalTheory.WeilPartsF.infPartF_placeIdem hpl, zero_mul, smul_zero]

end GlobalTheory.SplitInvFormF

end
end

section

open MeasureTheory GlobalTheory.SplitFlip
open scoped Matrix

theorem _root_.GlobalTheory.T.full_rank_zeta_surjective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν,
    ∃ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ h : GL (Fin d) k,
      smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ (GlobalTheory.FullRankCoinv.Y0 k n d * h.val) = f h := by
  first | exact @GlobalTheory.FullRankOnto.exists_fullRk_smallF_eq | exact GlobalTheory.FullRankOnto.exists_fullRk_smallF_eq | (intros; apply GlobalTheory.FullRankOnto.exists_fullRk_smallF_eq <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.span_invariantOneForms_affineOpen_abelianScheme_eq_top : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ U : AffOp A.left, Submodule.span (Sec A.hom U.unop.1) (Set.range fun w : GlobalTheory.InvForm.InvForm A ↦ evForm A.hom U w.1) = ⊤ := by
  first | exact @GlobalTheory.InvSpan.span_invForm_eq_top | exact GlobalTheory.InvSpan.span_invForm_eq_top | (intros; apply GlobalTheory.InvSpan.span_invForm_eq_top <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.descended_birigidified_bundle_symmetric : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A') (G : Subgroup (𝟙_ (Over S) ⟶ o.A)), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ (m : ℕ) (P' : LB (G2 A').left), P'.IsLB → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso P' (P'.pull (lift (snd A' A') (fst A' A')).left) := by
  first | exact @GlobalTheory.HeckeSym.descended_symm | exact GlobalTheory.HeckeSym.descended_symm | (intros; apply GlobalTheory.HeckeSym.descended_symm <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.QCompat

theorem comp_quasiInv : ∀ (T Y : Scheme.{0}) (t : T ⟶ Y) (A B : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (k : ℕ) (ψ : A ⟶ B) (ψ' : B ⟶ A) (A₁ B₁ : Over T) [GrpObj A₁] [IsCommMonObj A₁] [GrpObj B₁] [IsCommMonObj B₁] (φ : A₁.left ⟶ A.left) (θ : B₁.left ⟶ B.left) (ψ₁ : A₁ ⟶ B₁) (ψ₁' : B₁ ⟶ A₁), IsAbelianScheme B₁ → 0 < k → IsQuasiInv k ψ ψ' → IsQuasiInv k ψ₁ ψ₁' → IsGrpPullback A₁ A t φ → φ ≫ ψ.left = ψ₁.left ≫ θ → θ ≫ ψ'.left = ψ₁'.left ≫ φ := by
  intro T Y t A B _ _ _ _ k ψ ψ' A₁ B₁ _ _ _ _ φ θ ψ₁ ψ₁' hB hk hq hq₁ hφ hsq
  obtain ⟨h1, h2, -⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow T B₁ hB k hk
  haveI : Epi ((𝟙 B₁) ^ k).left := Flat.epi_of_flat_of_surjective _
  have e₁ : ψ₁'.left ≫ ψ₁.left = ((𝟙 B₁) ^ k).left := by rw [← Over.comp_left, hq₁.2.2.2]
  haveI : Epi (ψ₁'.left ≫ ψ₁.left) := by rw [e₁]; infer_instance
  haveI : Epi ψ₁.left := epi_of_epi ψ₁'.left ψ₁.left
  rw [← cancel_epi ψ₁.left, ← Category.assoc, ← hsq, Category.assoc, ← Over.comp_left, hq.2.2.1,
    ← Category.assoc, ← Over.comp_left, hq₁.2.2.1]
  exact (GlobalTheory.LamF.IsGrpPullback.id_pow_left hφ k).symm

end GlobalTheory.UPel.HT.ES.QCompat
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem isFinite_etale_surjective_of_isQuasiInv : ∀ (Y : Scheme.{0}) (A B : Over Y) [GrpObj A] [GrpObj B] (k : ℕ) (ψ : A ⟶ B) (ψ' : B ⟶ A), IsAbelianScheme A → IsAbelianScheme B → IsUnit (k : Γ(Y, ⊤)) → IsQuasiInv k ψ ψ' → IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left := by
  intro Y A B _ _ k ψ ψ' hA hB hk hq
  obtain ⟨-, -, h1, h2⟩ := hq
  obtain ⟨⟨hAf, hAe⟩, -⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A (hG := hA) hk
  obtain ⟨⟨-, hBe⟩, -⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion B (hG := hB) hk
  rw [GlobalTheory.GrpTangent.mulN_eq_pow, ← h1, Over.comp_left] at hAf hAe
  rw [GlobalTheory.GrpTangent.mulN_eq_pow, ← h2, Over.comp_left] at hBe
  haveI := hB.proper
  haveI : IsSeparated (ψ'.left ≫ A.hom) := by rw [Over.w]; infer_instance
  haveI := IsSeparated.of_comp ψ'.left A.hom
  haveI := FormallyUnramified.of_comp ψ'.left ψ.left
  haveI := locallyOfFiniteType_of_comp ψ'.left ψ.left
  refine ⟨IsFinite.of_comp ψ.left ψ'.left, Etale.of_comp ψ.left ψ'.left, ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · refine ⟨fun b => ?_⟩
    have hu := hk.map (Y.evaluation ⊤ (B.hom.base b) trivial).hom
    rw [map_natCast, Nat.cast_zero] at hu
    exact absurd hu not_isUnit_zero
  · obtain ⟨-, hs, -⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow Y B hB k hk0
    rw [← h2, Over.comp_left] at hs
    exact Surjective.of_comp ψ'.left ψ.left

end GlobalTheory.UPel.HT.ES
end
