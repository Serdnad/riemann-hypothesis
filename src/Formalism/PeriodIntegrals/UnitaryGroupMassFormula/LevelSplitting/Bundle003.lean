module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ClosedStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.UnitaryGroupSecondCountableT2
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.RatVMemSpan

@[expose] public section

section

noncomputable section

namespace PI.LevelKSplit.W.Meas

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
  PI.LevelKSplit.W.Glob
open scoped TensorProduct

theorem countable_nf (K : Type) [Field K] [NumberField K] : Countable K :=
  (Module.finBasis ℚ K).equivFun.injective.countable

theorem places_countable : PlacesCountable := by
  intro F _ _
  haveI : Countable F := countable_nf F
  haveI : Countable (𝓞 F) := (IsFractionRing.injective (𝓞 F) F).countable
  have hs : Function.Surjective (fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F))) := by
    intro I
    obtain ⟨s, hs⟩ := IsNoetherian.noetherian I
    exact ⟨s, hs⟩
  haveI : Countable (Ideal (𝓞 F)) := hs.countable
  have hinj : Function.Injective (fun P : HeightOneSpectrum (𝓞 F) => P.asIdeal) :=
    fun P Q h => HeightOneSpectrum.ext h
  exact hinj.countable

private theorem mulVec_mem_span_of_mulVec_generators_mem {O B : Type} [CommRing O] [CommRing B] [Algebra O B] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) B) (G : Set (Fin n → B))
    (hG : ∀ y ∈ G, A.mulVec y ∈ Submodule.span O G) :
    ∀ x ∈ Submodule.span O G, A.mulVec x ∈ Submodule.span O G := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact hG y hy
  | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c ha

theorem stab_iff {O B : Type} [CommRing O] [CommRing B] [Algebra O B] {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) B) (hCA : ∀ x, C.mulVec (A.mulVec x) = x)
    (hAC : ∀ x, A.mulVec (C.mulVec x) = x) (G : Set (Fin n → B)) :
    (∀ x, x ∈ Submodule.span O G ↔ A.mulVec x ∈ Submodule.span O G) ↔
      ∀ y ∈ G, A.mulVec y ∈ Submodule.span O G ∧ C.mulVec y ∈ Submodule.span O G := by
  constructor
  · intro h y hy
    have hyS : y ∈ Submodule.span O G := Submodule.subset_span hy
    refine ⟨(h y).1 hyS, ?_⟩
    rw [h (C.mulVec y), hAC y]
    exact hyS
  · intro h x
    constructor
    · exact fun hx => mulVec_mem_span_of_mulVec_generators_mem A G (fun y hy => (h y hy).1) x hx
    · intro hx
      have hC := mulVec_mem_span_of_mulVec_generators_mem C G (fun y hy => (h y hy).2) _ hx
      rwa [hCA x] at hC

theorem compV_inv_mulVec {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (v : HeightOneSpectrum (𝓞 F))
    (g : HA (Af F) σ J) (x : Fin n → Fv F v ⊗[F] E) :
    Matrix.mulVec ((compV v (incAf σ J g⁻¹) : GL (Fin n) (Fv F v ⊗[F] E)) :
      Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
      (Matrix.mulVec ((compV v (incAf σ J g) : GL (Fin n) (Fv F v ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) x) = x := by
  rw [Matrix.mulVec_mulVec, map_inv, map_inv, Units.inv_mul, Matrix.one_mulVec]

theorem compV_mulVec_inv {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (v : HeightOneSpectrum (𝓞 F))
    (g : HA (Af F) σ J) (x : Fin n → Fv F v ⊗[F] E) :
    Matrix.mulVec ((compV v (incAf σ J g) : GL (Fin n) (Fv F v ⊗[F] E)) :
      Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
      (Matrix.mulVec ((compV v (incAf σ J g⁻¹) : GL (Fin n) (Fv F v ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) x) = x := by
  rw [Matrix.mulVec_mulVec, map_inv, map_inv, Units.mul_inv, Matrix.one_mulVec]

theorem measKf_of (h2 : ContPlace) (h3 : LatBorel) : MeasKfAll := by
  intro F E _ _ _ _ _ σ _ M J _ Λ
  haveI : Countable (HeightOneSpectrum (𝓞 F)) := places_countable F
  haveI : Countable E := countable_nf E
  unfold Kf
  rw [Subgroup.coe_iInf]
  refine MeasurableSet.iInter fun v => ?_
  let Mf : HA (Af F) σ J → Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E) := fun g =>
    ((compV v (incAf σ J g) : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E))
  let G : Set (Fin M → Fv F v ⊗[F] E) := ratV (F := F) (Fv F v) '' Λ
  have hG : G.Countable := (Set.to_countable Λ).image _
  have hset : ((Subgroup.comap ((compV v).comp (incAf σ J)) (Kloc v Λ) : Subgroup (HA (Af F) σ J)) :
      Set (HA (Af F) σ J)) = ⋂ y ∈ G, ((fun g => (Mf g).mulVec y) ⁻¹' (latLoc (E := E) v Λ : Set _) ∩
        (fun g => (Mf g⁻¹).mulVec y) ⁻¹' (latLoc (E := E) v Λ : Set _)) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]
    change (∀ x, x ∈ latLoc (E := E) v Λ ↔ (Mf g).mulVec x ∈ latLoc (E := E) v Λ) ↔ _
    exact stab_iff (Mf g) (Mf g⁻¹) (compV_inv_mulVec v g) (compV_mulVec_inv v g) G
  rw [hset]
  refine MeasurableSet.biInter hG fun y _ => ?_
  letI : MeasurableSpace (Fin M → Fv F v ⊗[F] E) := borel _
  haveI : BorelSpace (Fin M → Fv F v ⊗[F] E) := ⟨rfl⟩
  have hc : Continuous (fun g => (Mf g).mulVec y) :=
    (h2 F E σ M J v).matrix_mulVec continuous_const
  refine MeasurableSet.inter (hc.measurable (h3 F E M v Λ)) ?_
  have hc' : Continuous (fun g => (Mf g⁻¹).mulVec y) :=
    ((h2 F E σ M J v).comp continuous_inv).matrix_mulVec continuous_const
  exact hc'.measurable (h3 F E M v Λ)

end PI.LevelKSplit.W.Meas
end
end

section

noncomputable section

namespace PI.LevelKSplit.W.ExS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open PI.VolSemiDirect.W
open scoped TensorProduct

def SCAf : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], SecondCountableTopology (Af F)

section Ext

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

def SemiNHS : Prop :=
  IsHermND σ J → (∀ x, σ (σ x) = x) → ∀ (r : ℕ) (P : Frame E M r) (T : F), P.IsStd σ J T →
    Semi (Ssub (Af F) σ J P) (Nsub (Af F) σ J P) (Hsub (Af F) σ J P)

def ConjNH : Prop :=
  IsHermND σ J → (∀ x, σ (σ x) = x) → ∀ (r : ℕ) (P : Frame E M r) (T : F), P.IsStd σ J T →
    ConjInv (Nsub (Af F) σ J P) (Hsub (Af F) σ J P)

variable {F E σ M J}

theorem lcsc_HAf [FiniteDimensional F E] (hsc : SecondCountableTopology (Af F)) :
    LCSC (HA (Af F) σ J) := by
  haveI := hsc
  refine ⟨inferInstance, ?_, ?_, inferInstance⟩
  · haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
    let e := (Algebra.TensorProduct.basis (Af F) (Module.finBasis F E)).equivFun
    have hc1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    have hc2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
    let h : (Af F ⊗[F] E) ≃ₜ (Fin (Module.finrank F E) → Af F) := ⟨e.toEquiv, hc1, hc2⟩
    haveI : SecondCountableTopology (Af F ⊗[F] E) := h.secondCountableTopology
    haveI h4 : SecondCountableTopology (Matrix (Fin M) (Fin M) (Af F ⊗[F] E)) :=
      inferInstanceAs (SecondCountableTopology (Fin M → Fin M → Af F ⊗[F] E))
    haveI : SecondCountableTopology (Matrix (Fin M) (Fin M) (Af F ⊗[F] E))ᵐᵒᵖ :=
      MulOpposite.opHomeomorph.symm.secondCountableTopology
    haveI : SecondCountableTopology (GL (Fin M) (Af F ⊗[F] E)) :=
      Units.isEmbedding_embedProduct.isInducing.secondCountableTopology
    show SecondCountableTopology ↥(HR (Af F) σ J)
    exact Topology.IsInducing.subtypeVal.secondCountableTopology
  · show T2Space ↥(HR (Af F) σ J)
    infer_instance

theorem existS_of [FiniteDimensional F E] (hJ : IsHermND σ J) (hinv : ∀ x, σ (σ x) = x)
    (hPr : ProdHaarG) (hsc : SecondCountableTopology (Af F)) (hS : SemiNHS F E σ M J)
    (hCo : ConjNH F E σ M J) : ExistS F E σ M J := by
  intro r P T hP μN hN μH hH
  obtain ⟨hSc, hNc, hHc⟩ := PI.LevelKSplit.W.ExC.closed_SNH hJ hinv P T hP
  obtain ⟨hLC, hSC, hT2, hTG⟩ := lcsc_HAf (σ := σ) (J := J) hsc
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI := hTG
  have hsub : ∀ K : Subgroup (HA (Af F) σ J), IsClosed (K : Set (HA (Af F) σ J)) → LCSC K := by
    intro K hK
    refine ⟨?_, ?_, ?_, inferInstance⟩
    · first
        | exact hK.isClosedEmbedding_subtypeVal.locallyCompactSpace
        | exact hK.locallyCompactSpace
        | exact hK.closedEmbedding_subtypeVal.locallyCompactSpace
    · first
        | exact Topology.IsInducing.subtypeVal.secondCountableTopology
        | exact @Topology.IsInducing.secondCountableTopology _ _ _ _ hSC _ Topology.IsInducing.subtypeVal
    · first
        | exact inferInstance
        | exact Topology.IsEmbedding.subtypeVal.t2Space
  obtain ⟨μS, hμS, hprod⟩ := hPr (HA (Af F) σ J) _ _ _ (hS hJ hinv r P T hP) (hsub _ hSc)
    (hsub _ hNc) (hsub _ hHc) (hCo hJ hinv r P T hP) μN hN μH hH
  exact ⟨μS, hμS, hprod⟩

end Ext

def SemiNHSAll : Prop := ForAllCM fun F E _ _ _ _ σ M J => SemiNHS F E σ M J

def ConjNHAll : Prop := ForAllCM fun F E _ _ _ _ σ M J => ConjNH F E σ M J

theorem existSAll_of (hPr : ProdHaarG) (hsc : SCAf) (hS : SemiNHSAll) (hCo : ConjNHAll) :
    ExistSAll := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
    apply τ.injective
    rw [hσ.2.2.2 τ (σ x), hσ.2.2.2 τ x, star_star]
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  exact existS_of hJ hinv hPr (hsc F) (hS F E σ hσ M J hJ) (hCo F E σ hσ M J hJ)

end PI.LevelKSplit.W.ExS
end
end
