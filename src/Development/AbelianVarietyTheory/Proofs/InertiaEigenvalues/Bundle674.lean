module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import ReciprocityTheory.Automorphisms.Bundle001
public import Formalism.GaloisCohomology.StatementLoc
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.WeaklyAdmissibleFiltrations.Bundle001
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle643
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle644
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle006
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseChangeDistinctness
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle015
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle642
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle457
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle491
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle476
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Formalism.AlgebraicWeights.IsAlgWeight
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.UnitaryReadTrue

theorem host_conj_eq (D : D7) (x : D.host.E) : D.host.conj x = IsCMField.complexConj D.host.E x :=
  D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])

theorem coe_cO (D : D7) (x : 𝓞 D.host.E) :
    ((IsCMField.ringOfIntegersComplexConj D.host.E x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := by
  rw [IsCMField.coe_ringOfIntegersComplexConj, host_conj_eq]

theorem exists_splitPlace_w (D : D7) (w : PlE D.host) (hw : IsSplitPl D.host w) :
    ∃ s : SplitPlace D.host.E, s.w = w := by
  obtain ⟨s, -, hc, -⟩ := GlobalTheory.SplitConjPlace.splitEx_all D w hw
  refine ⟨GlobalTheory.SplitConjPlace.conjSP s, HeightOneSpectrum.ext (Ideal.ext fun x => ?_)⟩
  change Valued.v (s.i (IsCMField.complexConj D.host.E (x : D.host.E))) < 1 ↔ _
  change IsCMField.ringOfIntegersComplexConj D.host.E x ∈ s.w.asIdeal ↔ _
  exact (hc x _ (coe_cO D x)).symm

theorem not_isSplitAt (D : D7) (w : PlE D.host) (hw : ¬ IsSplitPl D.host w) : ¬ IsSplitAt w := by
  rintro ⟨u, hu, he⟩
  apply hw
  let cO := IsCMField.ringOfIntegersComplexConj D.host.E
  have cc (x : 𝓞 D.host.E) : cO (cO x) = x := by
    apply RingOfIntegers.ext
    simp only [cO, IsCMField.coe_ringOfIntegersComplexConj]
    exact IsCMField.complexConj_apply_apply D.host.E (x : D.host.E)
  let Q : PlE D.host := {
    asIdeal := w.asIdeal.comap (cO : 𝓞 D.host.E →+* 𝓞 D.host.E)
    isPrime := Ideal.comap_isPrime _ _
    ne_bot := by
      obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
      refine (Submodule.ne_bot_iff _).2 ⟨cO y, ?_, ?_⟩
      · change cO (cO y) ∈ w.asIdeal
        rwa [cc]
      · intro h
        apply hy0
        rw [← cc y, h, map_zero] }
  have hQ (x : 𝓞 D.host.E) : x ∈ Q.asIdeal ↔ cO x ∈ w.asIdeal := Iff.rfl
  have hne : Q ≠ w := by
    intro h
    have nle : ∀ P : PlE D.host, u ≠ P → ¬ u.asIdeal ≤ P.asIdeal := fun P hne hle =>
      hne (HeightOneSpectrum.ext (u.isMaximal.eq_of_le P.isPrime.ne_top hle))
    obtain ⟨x, hx, hxw⟩ := Set.not_subset.mp (nle w hu)
    have hxc : cO x ∉ w.asIdeal := by
      intro hxc
      have : x ∈ Q.asIdeal := (hQ x).2 hxc
      exact hxw (h ▸ this)
    have hfix : cO (x * cO x) = x * cO x := by rw [map_mul, cc, mul_comm]
    obtain ⟨y, hy⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff D.host.E _).1 hfix
    have hyu : y ∈ u.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
      rw [Ideal.mem_comap, hy]; exact u.asIdeal.mul_mem_right _ hx
    change y ∈ (u.under (𝓞 (maximalRealSubfield D.host.E))).asIdeal at hyu
    rw [he] at hyu
    change y ∈ w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) at hyu
    rw [Ideal.mem_comap, hy] at hyu
    rcases w.isPrime.mem_or_mem hyu with h1 | h1
    · exact hxw h1
    · exact hxc h1
  have hle : ¬ w.asIdeal ≤ Q.asIdeal := fun hle =>
    hne (HeightOneSpectrum.ext (w.isMaximal.eq_of_le Q.isPrime.ne_top hle)).symm
  obtain ⟨x, hx, hx'⟩ := Set.not_subset.mp hle
  refine ⟨x, hx, fun y hy hyw => hx' ?_⟩
  refine (hQ x).2 ?_
  have : y = IsCMField.ringOfIntegersComplexConj D.host.E x := RingOfIntegers.ext (by rw [hy, coe_cO])
  rwa [← this]

theorem infOf_eq_infOfWeight {n : ℕ} (lam : DomWeight n) : NG.infOf lam.w = infOfWeight lam := by
  unfold NG.infOf infOfWeight
  congr 1
  funext k
  ring

end GlobalTheory.UnitaryReadTrue
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix

namespace GlobalTheory.RatPtsBridge

theorem exists_ratGL : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (γQ : GQ L n), ∃ (γ : UA L n) (γ₀ : GL (Fin n) L), γ.1 = ratGL L n γ₀ ∧ (((γQ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom := by
  intro L _ _ _ n γQ
  obtain ⟨γ₀, hγ₀, he⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γQ.2)
  have h0 : (γ₀ : Matrix (Fin n) (Fin n) L) * conjT (IsCMField.complexConj L : L →+* L) γ₀ = 1 := hγ₀
  have h1 : conjT (IsCMField.complexConj L : L →+* L) (γ₀ : Matrix (Fin n) (Fin n) L) *
      (γ₀ : Matrix (Fin n) (Fin n) L) = 1 := mul_eq_one_comm.1 h0
  have hmem : ratGL L n γ₀ ∈ UA L n := by
    show Formalism.UG.cT (conjAd L) ((ratGL L n γ₀ : GL (Fin n) (Ad L)) : Matrix (Fin n) (Fin n) (Ad L)) * 1 *
      ((ratGL L n γ₀ : GL (Fin n) (Ad L)) : Matrix (Fin n) (Fin n) (Ad L)) = 1
    have e : Formalism.UG.cT (conjAd L) ((γ₀ : Matrix (Fin n) (Fin n) L).map (algebraMap L (Ad L))) =
        (conjT (IsCMField.complexConj L : L →+* L) (γ₀ : Matrix (Fin n) (Fin n) L)).map (algebraMap L (Ad L)) := by
      ext i j
      simp [Formalism.UG.cT, conjT, conjAd_algebraMap]
    change Formalism.UG.cT (conjAd L) ((γ₀ : Matrix (Fin n) (Fin n) L).map (algebraMap L (Ad L))) * 1 *
      (γ₀ : Matrix (Fin n) (Fin n) L).map (algebraMap L (Ad L)) = 1
    rw [mul_one, e, ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨⟨ratGL L n γ₀, hmem⟩, γ₀, rfl, ?_⟩
  rw [← he]
  rfl

end GlobalTheory.RatPtsBridge
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.DecInertia

theorem valuation_lt_one_iff_norm {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] {A : ValuationSubring Ω}
    {j : Ω →+* PadicAlgCl p} (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) (x : Ω) :
    A.valuation x < 1 ↔ ‖j x‖ < 1 := by
  rw [valuation_lt_one_iff', hj, hj, map_inv₀, norm_inv]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h0 : 0 < ‖j x‖ := norm_pos_iff.mpr ((_root_.map_ne_zero _).mpr hx)
    simp only [hx, false_or, not_le, one_lt_inv₀ h0]
    exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

theorem inertiaK_iff_mem_Ine (p : ℕ) [Fact p.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (A : ValuationSubring Ω) (j : Ω →+* PadicAlgCl p) (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (i : ↥(A.decompositionSubgroup F) ≃* (PadicAlgCl p ≃ₐ[↥K] PadicAlgCl p))
    (hi : ∀ (g : ↥(A.decompositionSubgroup F)) (x : Ω), i g (j x) = j ((g : Ω ≃ₐ[F] Ω) x))
    (g : ↥(A.decompositionSubgroup F)) :
    i g ∈ Formalism.GaloisCohomology.inertiaK p K ↔ (g : Ω ≃ₐ[F] Ω) ∈ Ine (F := F) A := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have hn : ∀ (σ : PadicAlgCl p ≃ₐ[↥K] PadicAlgCl p) (z : PadicAlgCl p), ‖σ z‖ = ‖z‖ := fun σ z =>
    GlobalTheory.PlaceBridge.norm_algEquiv (σ.restrictScalars ℚ_[p]) z
  have hadd : ∀ a b : PadicAlgCl p, ‖a + b‖ ≤ max ‖a‖ ‖b‖ := IsUltrametricDist.norm_add_le_max
  constructor
  · intro h
    let H : Subgroup (PadicAlgCl p ≃ₐ[↥K] PadicAlgCl p) :=
      ((Ine (F := F) A).subgroupOf (A.decompositionSubgroup F)).map i.toMonoidHom
    have hsub : Formalism.GaloisCohomology.inertiaSet p K ⊆ H := by
      intro σ hσ
      refine ⟨i.symm σ, ?_, by simp⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      refine ⟨(i.symm σ).2, fun x hx => ?_⟩
      rw [valuation_lt_one_iff_norm hj, map_sub, ← hi, MulEquiv.apply_symm_apply]
      exact hσ (j x) ((hj x).1 ((A.valuation_le_one_iff x).1 hx))
    have hle : Formalism.GaloisCohomology.inertiaK p K ≤ H := (Subgroup.closure_le _).2 hsub
    obtain ⟨g', hg', e⟩ := hle h
    have : g' = g := i.injective e
    subst this
    exact Subgroup.mem_subgroupOf.1 hg'
  · intro h
    apply Subgroup.subset_closure
    intro x hx
    obtain ⟨y, hy⟩ := (GlobalTheory.PlaceBridge.denseRange_embedding j).exists_dist_lt x one_pos
    rw [dist_eq_norm] at hy
    have hjy : ‖j y‖ ≤ 1 := by
      have e : j y = x + -(x - j y) := by ring
      rw [e]
      exact (hadd _ _).trans (max_le hx (by rw [norm_neg]; exact hy.le))
    have hgy : ‖(i g) (j y) - j y‖ < 1 := by
      rw [hi, ← map_sub, ← valuation_lt_one_iff_norm hj]
      exact h.2 y ((A.valuation_le_one_iff y).2 ((hj y).2 hjy))
    have e : (i g) x - x = (i g) (x - j y) + (((i g) (j y) - j y) + -(x - j y)) := by
      rw [map_sub]; ring
    rw [e]
    refine (hadd _ _).trans_lt (max_lt (by rw [hn]; exact hy) ((hadd _ _).trans_lt (max_lt hgy ?_)))
    rw [norm_neg]; exact hy

end GlobalTheory.DecInertia
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.CrisCoord

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
  {B : Type} [CommRing B] [Algebra F B] {d : ℕ}

def crd (bV : Module.Basis (Fin d) F V) (r : Fin d) : V ⊗[F] B →ₗ[F] B :=
  (TensorProduct.lid F B).toLinearMap ∘ₗ TensorProduct.map (bV.coord r) LinearMap.id

theorem crd_tmul (bV : Module.Basis (Fin d) F V) (r : Fin d) (v : V) (x : B) :
    crd bV r (v ⊗ₜ[F] x) = bV.coord r v • x := by
  simp [crd]

theorem crd_mulLeft (bV : Module.Basis (Fin d) F V) (r : Fin d) (β : B) (z : V ⊗[F] B) :
    crd bV r (AlgebraTensorModule.map (LinearMap.id : V →ₗ[F] V) (LinearMap.mulLeft F β) z) =
      β * crd bV r z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v x => simp [crd_tmul, mul_smul_comm]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, mul_add]

theorem crd_map (bV : Module.Basis (Fin d) F V) (r : Fin d) (f : V →ₗ[F] V) (σ : B →ₗ[F] B)
    (z : V ⊗[F] B) :
    crd bV r (AlgebraTensorModule.map f σ z) =
      ∑ s, LinearMap.toMatrix bV bV f r s • σ (crd bV s z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v x =>
    have h := congrFun (LinearMap.toMatrix_mulVec_repr bV bV f v) r
    simp only [Matrix.mulVec, dotProduct] at h
    simp only [AlgebraTensorModule.map_tmul, crd_tmul, Module.Basis.coord_apply, map_smul, smul_smul]
    rw [← Finset.sum_smul, ← h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add, Finset.sum_add_distrib]

theorem crd_basis (bV : Module.Basis (Fin d) F V) (r j : Fin d) :
    crd bV r ((bV j) ⊗ₜ[F] (1 : B)) = if r = j then 1 else 0 := by
  rw [crd_tmul, Module.Basis.coord_apply, Module.Basis.repr_self]
  by_cases h : r = j
  · subst h; simp
  · rw [Finsupp.single_apply, if_neg (Ne.symm h), if_neg h, zero_smul]

end GlobalTheory.CrisCoord

namespace GlobalTheory.CrisCoord

variable {l : ℕ} [Fact l.Prime] {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V]
  [IsScalarTower ℤ_[l] ℚ_[l] V] {d : ℕ}

theorem linIndep_lat (T : Submodule ℤ_[l] V) (b : Module.Basis (Fin d) ℤ_[l] T) :
    LinearIndependent ℚ_[l] (fun i => (b i : V)) := by
  rw [← LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]]
  exact b.linearIndependent.map' T.subtype (Submodule.ker_subtype T)

theorem sum_lat (T : Submodule ℤ_[l] V) (b : Module.Basis (Fin d) ℤ_[l] T) (w : T) :
    (w : V) = ∑ i, (algebraMap ℤ_[l] ℚ_[l] (b.repr w i)) • (b i : V) := by
  have h := congrArg T.subtype (b.sum_repr w)

  rw [map_sum] at h
  simp only [map_smul, Submodule.subtype_apply] at h
  simp only [algebraMap_smul]
  exact h.symm

theorem span_lat (T : Submodule ℤ_[l] V) (hT : Submodule.span ℚ_[l] (T : Set V) = ⊤)
    (b : Module.Basis (Fin d) ℤ_[l] T) : ⊤ ≤ Submodule.span ℚ_[l] (Set.range fun i => (b i : V)) := by
  rw [← hT]
  refine Submodule.span_le.mpr fun x hx => ?_
  rw [show x = ((⟨x, hx⟩ : T) : V) from rfl, sum_lat T b]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def bVL (T : Submodule ℤ_[l] V) (hT : Submodule.span ℚ_[l] (T : Set V) = ⊤)
    (b : Module.Basis (Fin d) ℤ_[l] T) : Module.Basis (Fin d) ℚ_[l] V :=
  Module.Basis.mk (linIndep_lat T b) (span_lat T hT b)

theorem bVL_apply (T : Submodule ℤ_[l] V) (hT : Submodule.span ℚ_[l] (T : Set V) = ⊤)
    (b : Module.Basis (Fin d) ℤ_[l] T) (i : Fin d) : bVL T hT b i = (b i : V) := by
  simp [bVL]

theorem repr_lat (T : Submodule ℤ_[l] V) (hT : Submodule.span ℚ_[l] (T : Set V) = ⊤)
    (b : Module.Basis (Fin d) ℤ_[l] T) (w : T) (r : Fin d) :
    (bVL T hT b).repr (w : V) r = algebraMap ℤ_[l] ℚ_[l] (b.repr w r) := by
  have h : (w : V) = ∑ i, (algebraMap ℤ_[l] ℚ_[l] (b.repr w i)) • bVL T hT b i := by
    simp only [bVL_apply]; exact sum_lat T b w
  rw [h, Module.Basis.repr_sum_self]

end GlobalTheory.CrisCoord

namespace GlobalTheory.CrisCoord

theorem toMatrix_lat {l : ℕ} [Fact l.Prime] {G : Type} [Group G] {V : Type} [AddCommGroup V]
    [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] {ρ : Representation ℚ_[l] G V}
    (L : Lattice (O := ℤ_[l]) ρ) {d : ℕ} (b : Module.Basis (Fin d) ℤ_[l] L.T) (g : G) (r s : Fin d) :
    LinearMap.toMatrix (bVL L.T L.span b) (bVL L.T L.span b) (ρ g) r s =
      algebraMap ℤ_[l] ℚ_[l] (LinearMap.toMatrix b b (actT L g) r s) := by
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, bVL_apply, ← repr_lat L.T L.span b]
  rfl

theorem lattice_basis_span_invariants : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (L : Lattice (O := ℤ_[l]) ρ), IsCrys (P.PD K) ρ → ∀ (d : ℕ) (b : Module.Basis (Fin d) ℤ_[l] ↥L.T), ∀ j : Fin d, ∃ (m : ℕ) (c : Fin m → Per.Bcris l) (v : Fin m → Fin d → Per.Bcris l), (∀ i (g : ↥(GK K)), ((LinearMap.toMatrix b b (actT L g)).map (Per.zB l)).mulVec (fun r => Per.σB (g : GQ l) (v i r)) = v i) ∧ (Pi.single j 1 : Fin d → Per.Bcris l) = ∑ i, c i • v i := by
  intro l _ K P AI T V _ _ _ _ _ ρ L hC d b j
  obtain ⟨m, β, δ, hδ, hy⟩ :=
    GlobalTheory.T.dcris_span_tensorBcris_rat l P AI T K V ρ hC ((bVL L.T L.span b j) ⊗ₜ[ℚ_[l]] (1 : P.R.B))
  refine ⟨m, fun i => T.eB (β i), fun i r => T.eB (crd (bVL L.T L.span b) r (δ i)), ?_, ?_⟩
  · intro i g
    have hinv : actVB (P.PD K) ρ g (δ i) = δ i := by
      have h := hδ i
      simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] at h
      exact h g
    funext r
    have key := congrArg (fun z => T.eB (crd (bVL L.T L.span b) r z)) hinv
    beta_reduce
    rw [← key, actVB, crd_map]

    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [toMatrix_lat, Algebra.smul_def, map_mul, PadicInt.algebraMap_apply, T.zB]
    congr 1
    simp only [LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply, AlgEquiv.coe_toAlgHom,
      AlgHom.coe_coe]
    rw [← T.actB]
    congr 1
    exact (P.PD_actB K g _).symm
  · funext r
    have key := congrArg (fun z => T.eB (crd (bVL L.T L.span b) r z)) hy

    simp only [map_sum, crd_mulLeft, crd_basis, map_mul] at key
    beta_reduce
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← key]
    by_cases h : r = j
    · subst h; simp
    · simp [h]

end GlobalTheory.CrisCoord
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicModulus

theorem map_mul_right_unitary : ∀ (D : D7) (V : HSp D) (m : ℕ) (g : GA D V) (μ : Measure (Mx D m V.rank)), μ.IsAddHaarMeasure → μ.map (fun x : Mx D m V.rank => (HMul.hMul (x : Matrix (Fin m) (Fin V.rank) (AE D)) (mt V g) : Mx D m V.rank)) = μ := by
  intro D V m g μ hμ
  exact GlobalTheory.T.map_mul_right_unitaryGram_adelicMatrix_haar_eq D V.rank m V.gram (fun a b => V.herm.eq (V.frame b) (V.frame a)) (gram_det_ne V) g μ hμ

end GlobalTheory.AdelicModulus
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.mem_completedLattice_conjugateHalf_iff_dual : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ e : AE D, e * e = e → e * cA D e = 0 → infPart D e = 0 → finPart D e ∈ intAE D → ∀ u : WO S T, IsHalf (cA D e) u → (u ∈ latO S T ΛS ΛT (fun _ => True) ↔ ∀ l ∈ latO S T ΛS ΛT (fun _ => True), IsHalf e l → ψ (symplO S T l u) = 1) := by
  first | exact @GlobalTheory.ConjHalfDual.mem_latO_iff_of_conjHalf | exact GlobalTheory.ConjHalfDual.mem_latO_iff_of_conjHalf | (intros; apply GlobalTheory.ConjHalfDual.mem_latO_iff_of_conjHalf <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.DefiniteBC

namespace GlobalTheory.DefiniteBCFrozen

attribute [local instance] GlobalTheory.CuspRep.host_isCMField

theorem isBC_of_isBaseChange {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
    {B : NBC A} {j : ℕ} {π : B.AU j} {Pa : List (Part A.CG)}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeDistinctness.IsBaseChange B j π Pa) : SphericalInertData.IsBC N A B j π Pa := by
  refine ⟨fun p hp => ⟨(h.discrete p hp).1, (h.discrete p hp).2, h.conjSelfDual p hp⟩, ?_, h.rank, h.split,
    h.inert, h.inf⟩
  refine h.distinct.map ?_
  rintro ⟨a, π, d⟩ ⟨a', π', d'⟩ hh
  simp only [Prod.mk.injEq, Sigma.mk.injEq] at hh
  obtain ⟨⟨rfl, h2⟩, rfl⟩ := hh
  cases h2
  rfl

end GlobalTheory.DefiniteBCFrozen

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem fontaine_litFont_assembled :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.InvariantsGenerators.LitFont D HW F := by
  intro D HW F
  unfold Formalism.MainNotions.InvariantsGenerators.LitFont
  intro l _ K LL hA
  unfold Formalism.MainNotions.InvariantsGenerators.FontCore
  have hff := GlobalTheory.T.wachFunctor_fullyFaithful D HW F l K 1 LL hA.2.2
  have hex := GlobalTheory.T.etaleFunctor_exact_on_lattices D HW F l K 1 LL hA.2.2
  have hpd := GlobalTheory.T.exists_psi_operator_etale_phiGamma_module D HW F l K 1 LL hA.2.2
  have hpe := GlobalTheory.T.wachFunctorRing_psiOperator_exists_of_good D HW F l K 1 LL hA.2.2
  have hfr := GlobalTheory.T.etaleRing_free_over_frobenius_image D HW F l K 1 LL hA.2.2
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  refine ⟨hff, hex, ?_, hpd⟩
  obtain ⟨ψ, h1, h2, h3⟩ := hpe
  refine ⟨ψ, h1, h2, ?_, ?_⟩
  · rw [hp]; exact h3
  · intro x
    obtain ⟨c, hc, -⟩ := hfr x
    rw [hp]
    exact ⟨c, hc⟩

end GlobalTheory
end
