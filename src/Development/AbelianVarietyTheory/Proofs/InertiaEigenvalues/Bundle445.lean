module

public import Formalism.ConjugateSelfDual.Bundle001
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle431
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionInjectiveSaturatedInter
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle015
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFixingSubgroupMaxUnramifiedOfMemLocalGalois
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle418
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle432
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import ReciprocityTheory.NeutralLocalFields.Bundle001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.absNorm_place_le_of_frobenius : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver A w → ∀ q : ℕ, 1 < q → ∀ σ : G E Ω, IsFrob A q σ → normV w ≤ q := by
  first | exact @GlobalTheory.NormLeFrob.normV_le_of_isFrob | exact GlobalTheory.NormLeFrob.normV_le_of_isFrob | (intros; apply GlobalTheory.NormLeFrob.normV_le_of_isFrob <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT

theorem _root_.GlobalTheory.T.exists_residueField_embedding_place_over : ∀ (E' Ω : Type) [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] (g : ℕ) [Fact g.Prime]
    (A : ValuationSubring Ω) (w' : HeightOneSpectrum (𝓞 E')) (h' : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w')
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g),
    ∃ ι : 𝓞 E' ⧸ w'.asIdeal →+* Formalism.CyclotomicNorms.Fbar g,
      ∀ x : 𝓞 E', ι (Ideal.Quotient.mk _ x) = redThrough A κ (algebraMap E' Ω (x : E')) := by
  first | exact @GlobalTheory.residue_ringOfIntegers_to_place | exact GlobalTheory.residue_ringOfIntegers_to_place | (intros; apply GlobalTheory.residue_ringOfIntegers_to_place <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.dense_numberField_of_continuous_completion_equiv : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [Algebra.IsAlgebraic E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')), IsPlaceOver A' w' → ∀ (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), Continuous i → (∀ x, i (algebraMap E _ x) = algebraMap E' _ (j x)) → ∀ (y : E') (δ : Ω'), δ ≠ 0 → ∃ x : E, A'.valuation (algebraMap E' Ω' y - algebraMap E' Ω' (j x)) < A'.valuation δ := by
  first | exact @GlobalTheory.approx_of_completion_equiv | exact GlobalTheory.approx_of_completion_equiv | (intros; apply GlobalTheory.approx_of_completion_equiv <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.EtaleFrob

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem linearIndependent_of_span {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {r : ℕ}
    (d : Basis (Fin r) R M) (v : Fin r → M) (hv : Submodule.span R (Set.range v) = ⊤) :
    LinearIndependent R v := by
  let f : (Fin r → R) →ₗ[R] M := Fintype.linearCombination R v
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]; exact hv
  let g : (Fin r → R) →ₗ[R] (Fin r → R) := d.equivFun.toLinearMap ∘ₗ f
  have hg : Function.Surjective g := d.equivFun.surjective.comp hf
  have hgi : Function.Injective g := OrzechProperty.injective_of_surjective_endomorphism g hg
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have h1 : g a = g 0 := by
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe, map_zero, f, Fintype.linearCombination_apply, ha]
  exact fun i => congrFun (hgi h1) i

theorem twmap_smul {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {R : Type} [CommRing R] [Algebra O R]
    (f : R →ₐ[O] R) (T : LocLat G Qp LL O) (a : R) (z : TW R T) :
    TWmap f T (a • z) = f a • TWmap f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x t => simp [TWmap, TensorProduct.smul_tmul', map_mul]
  | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, map_add (f := _), smul_add]

theorem twmap_surjective {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {R : Type} [CommRing R] [Algebra O R]
    (f : R →ₐ[O] R) (T : LocLat G Qp LL O) (hf : Function.Surjective f) :
    Function.Surjective (TWmap f T) :=
  TensorProduct.map_surjective (g := f.toLinearMap) hf (g' := LinearMap.id) (fun x => ⟨x, rfl⟩)

end GlobalTheory.EtaleFrob

namespace GlobalTheory.EtaleFrob

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}



theorem phi_basis_of_tie {W : LocWach PD LL O v n} (E : EtTie W RA RW inclR φR gR πA) [Nontrivial W.EE] [Nontrivial O]
    (hφ : Function.Surjective φR) (hunits : ∀ x : W.EE, IsUnit (E.ioE x) → IsUnit x)
    (T : LocLat G Qp LL O) (hTfree : Module.Free O ↥T.L.T) (hTfin : Module.Finite O ↥T.L.T) :
    ∃ (r : ℕ) (b b' : Module.Basis (Fin r) W.EE (W.DD T)), ∀ j, b' j = W.φD T (b j) := by
  haveI hfreeD : Module.Free W.EE (W.DD T) := (W.DD_free T).1
  have hrk : finrank W.EE (W.DD T) = finrank O ↥T.L.T := (W.DD_free T).2
  obtain ⟨d0⟩ : Nonempty (Basis (Fin (finrank O ↥T.L.T)) RW (TW RW T)) :=
    ⟨Algebra.TensorProduct.basis RW (Module.finBasis O ↥T.L.T)⟩
  haveI hfin : Module.Finite W.EE (W.DD T) := by
    rcases Nat.eq_zero_or_pos (finrank W.EE (W.DD T)) with h0 | h0
    · haveI : IsEmpty (Fin (finrank O ↥T.L.T)) := by rw [← hrk, h0]; infer_instance
      have hz : ∀ x : W.DD T, x = 0 := fun x => E.jD_inj T (by
        rw [map_zero, ← d0.sum_repr (E.jD T x)]; simp)
      haveI : Subsingleton (W.DD T) := ⟨fun x y => by rw [hz x, hz y]⟩
      infer_instance
    · exact Module.finite_of_finrank_pos h0
  obtain ⟨r, hr⟩ : ∃ r, r = finrank W.EE (W.DD T) := ⟨_, rfl⟩
  obtain ⟨b⟩ : Nonempty (Basis (Fin r) W.EE (W.DD T)) :=
    ⟨(Module.finBasis W.EE (W.DD T)).reindex (finCongr hr.symm)⟩
  obtain ⟨d⟩ : Nonempty (Basis (Fin r) RW (TW RW T)) := ⟨d0.reindex (finCongr (hr.trans hrk).symm)⟩

  obtain ⟨c, hcdef⟩ : ∃ c : Fin r → TW RW T, ∀ j, c j = E.jD T (b j) := ⟨_, fun _ => rfl⟩
  have hjD : ∀ x : W.DD T, E.jD T x = ∑ i, E.ioE (b.repr x i) • c i := by
    intro x
    conv_lhs => rw [← b.sum_repr x]

    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [E.jD_smul, hcdef]
  have hc : Submodule.span RW (Set.range c) = ⊤ := by
    rw [eq_top_iff, ← E.jD_span T, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [hjD x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  obtain ⟨cb, hcb⟩ : ∃ cb : Basis (Fin r) RW (TW RW T), ∀ i, cb i = c i :=
    ⟨Basis.mk (linearIndependent_of_span d c hc) hc.ge, fun i => Basis.mk_apply _ _ i⟩

  obtain ⟨c', hc'def⟩ : ∃ c' : Fin r → TW RW T, ∀ j, c' j = TWmap φR T (c j) := ⟨_, fun _ => rfl⟩
  have hTW : ∀ y : TW RW T, ∃ x, TWmap φR T x = y := fun y => twmap_surjective φR T hφ y
  have himg : ∀ x : TW RW T, TWmap φR T x ∈ Submodule.span RW (Set.range c') := by
    intro x
    have hx : x ∈ Submodule.span RW (Set.range c) := by rw [hc]; exact Submodule.mem_top
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun RW).1 hx

    rw [← ha, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [twmap_smul, ← hc'def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  have hc' : Submodule.span RW (Set.range c') = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, hxy⟩ := hTW y
    rw [← hxy]
    exact himg x
  have hdet : IsUnit (cb.det c') := cb.is_basis_iff_det.1 ⟨linearIndependent_of_span d c' hc', hc'⟩

  obtain ⟨M, hMdef⟩ : ∃ M : Matrix (Fin r) (Fin r) W.EE, M = b.toMatrix (fun j => W.φD T (b j)) :=
    ⟨_, rfl⟩
  have hM : cb.toMatrix c' = M.map E.ioE := by
    ext i j
    rw [Basis.toMatrix_apply, Matrix.map_apply]
    have e1 : c' j = ∑ k, E.ioE (M k j) • cb k := by
      rw [hc'def, hcdef, ← E.jD_φ, hjD]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hcb, hMdef, Basis.toMatrix_apply]
    rw [e1, ← Basis.equivFun_symm_apply, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hdetM : IsUnit (E.ioE M.det) := by
    rw [AlgHom.map_det]
    rw [Basis.det_apply, hM] at hdet
    exact hdet
  have hbas := (b.is_basis_iff_det (v := fun j => W.φD T (b j))).2
    (by rw [Basis.det_apply, ← hMdef]; exact hunits _ hdetM)
  exact ⟨r, b, Basis.mk hbas.1 hbas.2.ge, fun j => Basis.mk_apply _ _ j⟩

end Generic

theorem φRW_onto {l : ℕ} [Fact l.Prime] (LL : FinExt l) : Function.Surjective (φRW LL) := by
  haveI := (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).1
  have h : Function.Surjective (frobW l) :=
    WittVector.map_surjective (frobenius (Cb l) l) fun x =>
      IsAlgClosed.exists_pow_nat_eq x (Fact.out : l.Prime).pos
  exact LinearMap.lTensor_surjective ↥(OL LL) (g := (frobW l).toLinearMap) h



theorem phi_basis : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), ∃ (r : ℕ) (b b' : Module.Basis (Fin r) W.EE (W.DD T)), ∀ j, b' j = W.φD T (b j) := by
  intro D HW F l _ K s LL h W T
  haveI : Nontrivial W.EE := W.EE_inj.nontrivial
  exact phi_basis_of_tie ((F l).E K s LL h).tie (φRW_onto LL)
    (GlobalTheory.IoInj.ioE_injective_saturated_inter l (D.loc l) (D.locA l) K s LL h _ _ _
      (GlobalTheory.NL.ioW (HW l) (F l) h (GlobalTheory.NL.Holds.laws (HW l) (F l) h))).2.1
    T T.L.free (Module.Finite.iff_fg.mpr T.L.fg)

end GlobalTheory.EtaleFrob
end
end

section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
open TensorProduct

noncomputable section

namespace GlobalTheory.ExtDict

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]

theorem exists_ext_cocycle [IsTopologicalRing LL] {T Y Z : LocLat G Qp LL O}
    (ι : LatHom T.L Y.L) (π : LatHom Y.L Z.L) (hs : IsSESLat (Qp := Qp) ι π)
    (hZ : ∀ g z, Z.ρ g z = z) (x : ↥Y.L.T) :
    ∃ c : ↥(latticeCocycles T.L), ∀ g, ι.f ((c : G → T.V) g) = Y.ρ g (x : Y.V) - (x : Y.V) := by
  obtain ⟨h1, -, -, h4, h5⟩ := hs
  obtain ⟨r, hr⟩ := ι.f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 h1)
  have hr' : ∀ y, r (ι.f y) = y := fun y => LinearMap.congr_fun hr y
  have hval : ∀ g, ι.f (r (Y.ρ g (x : Y.V) - (x : Y.V))) = Y.ρ g (x : Y.V) - (x : Y.V) := by
    intro g
    obtain ⟨y, hy⟩ := (h4 (Y.ρ g (x : Y.V) - (x : Y.V))).1 (by rw [map_sub, π.equiv, hZ, sub_self])
    rw [← hy, hr']
  have : ContinuousSMul LL T.V := IsModuleTopology.toContinuousSMul LL T.V
  have hrc : Continuous r := IsModuleTopology.continuous_of_linearMap r
  have : IsTopologicalAddGroup Y.V := IsModuleTopology.topologicalAddGroup LL Y.V
  refine ⟨⟨fun g => r (Y.ρ g (x : Y.V) - (x : Y.V)), ⟨?_, fun g h => ?_⟩, fun g _ => ?_⟩, hval⟩
  · exact hrc.comp ((Y.cont x).sub continuous_const)
  · apply h1
    rw [map_add (f := _), ι.equiv, hval, hval, hval, map_mul, Module.End.mul_apply, map_sub]
    abel
  · apply h5
    change ι.f (r _) ∈ _
    rw [hval]
    exact Y.L.T.sub_mem (Y.actT g x).2 x.2

variable {K₀ K : Type} [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

theorem exists_unit_fixed (E : EtTie W RA RW inclR φR gR πA) (u : ↥W.one.L.T) :
    ∃ e₀ ∈ tableLineDegreeTwo.fixDD W W.one, E.jD W.one e₀ = (1 : RW) ⊗ₜ[O] u := by
  obtain ⟨e₁, f₀, hf₀, hj, -⟩ := E.one_e
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1
    (hf₀ ▸ Submodule.mem_top : u ∈ Submodule.span O {f₀})
  have hje : E.jD W.one (c • e₁) = (1 : RW) ⊗ₜ[O] u := by
    rw [map_smul, hj, ← hc, TensorProduct.tmul_smul]
  have hφ : W.φD W.one (c • e₁) = c • e₁ := by
    apply E.jD_inj
    rw [E.jD_φ, hje]
    simp [TWmap]
  have hγ : ∀ g, W.γD W.one g (c • e₁) = c • e₁ := by
    intro g
    obtain ⟨g, rfl⟩ := W.resΓ_onto g
    apply E.jD_inj
    have hact : W.one.actT g u = u := Subtype.ext (W.one_triv g u)
    rw [E.jD_act, hje]
    simp [TWact, hact]
  refine ⟨c • e₁, ⟨⟨?_, ?_⟩, ?_⟩, hje⟩
  · exact LinearMap.mem_ker.2 (sub_eq_zero.2 hφ)
  · exact LinearMap.mem_ker.2 (sub_eq_zero.2 (hγ _))
  · exact (Submodule.mem_iInf _).2 fun δ => (Submodule.mem_iInf _).2 fun _ =>
      LinearMap.mem_ker.2 (sub_eq_zero.2 (hγ δ))

end Generic

theorem herrExt_of_dense (S : LocalSituation.Sit) (E : S.Comparison₂) [IsTopologicalRing S.LL] [T2Space S.LL]
    (hR : Function.Injective (algebraMap S.O S.RW))
    (hDel : S.PD.p = 2 → S.W.DelF = {1})
    (hdens : ∀ A : Subgroup S.G, IsClosed (A : Set S.G) → (∀ g, S.W.resΓ g ∈ S.W.DelF → g ∈ A) →
      (∀ g, S.W.resΓ g = S.W.gamK → g ∈ A) → ∀ g, g ∈ A) : tableLineDegreeTwo.HerrExt S.W E := by
  refine ⟨exists_unit_fixed E, fun T Tp ι π hs x u hu e hδ he p h1 h2 => ?_⟩
  obtain ⟨c, hc⟩ := exists_ext_cocycle ι π hs S.W.one_triv x
  exact ⟨c, (dict_of_dense S E hR hDel hdens T Tp _ ι π hs x u e hu he hδ p h1 h2 c hc).symm, hc⟩

theorem extension_rule (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) :
    InvariantsGenerators.HerrExtensionEtale D HW F := by
  intro l _ K LL hA
  let S := LocalSituation.sit D.loc HW l (D.locA l) K 1 LL hA.2.2
  let E : S.Comparison₂ := ((F l).E K 1 LL hA.2.2).tie
  have : IsTopologicalRing S.LL := inferInstanceAs (IsTopologicalRing ↥LL.1.toSubring)
  have : T2Space S.LL := inferInstanceAs (T2Space ↥LL.1)
  exact herrExt_of_dense S E (algebraMap_RW_injective LL)
    (fun h2 => absurd (((D.loc l).PD_p K).symm.trans h2) hA.2.1)
    (dense_DelF_gamK (D.loc l) S.W (D.locA l) fun h2 => absurd h2 hA.2.1)

end GlobalTheory.ExtDict
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

namespace GlobalTheory.NL.FiniteRestrictionH1f

theorem coboundary_of_finiteIndex {G M k : Type} [Group G] [Field k] [CharZero k] [AddCommGroup M]
    [Module k M] (a : G → M →ₗ[k] M) (ha : ∀ g h x, a (g * h) x = a g (a h x))
    (H : Subgroup G) [H.FiniteIndex] (c : G → M) (hc : ∀ g h, c (g * h) = c g + a g (c h))
    (b : M) (hb : ∀ h ∈ H, c h = a h b - b) : ∃ x : M, ∀ g, c g = a g x - x := by
  classical
  let d : G → M := fun g => c g - (a g b - b)
  have hd : ∀ g h, d (g * h) = d g + a g (d h) := by
    intro g h
    simp only [d, hc, ha, map_sub]
    abel
  have hd0 : ∀ h ∈ H, d h = 0 := fun h hh => by simp only [d, hb h hh, sub_self]
  have hdH : ∀ g g' : G, (QuotientGroup.leftRel H) g g' → d g = d g' := by
    intro g g' hgg
    rw [QuotientGroup.leftRel_apply] at hgg
    have : g' = g * (g⁻¹ * g') := by group
    rw [this, hd, hd0 _ hgg, map_zero, add_zero]
  let D : G ⧸ H → M := fun q => Quotient.liftOn' q d hdH
  have hD : ∀ (g : G) (q : G ⧸ H), D (g • q) = d g + a g (D q) := by
    intro g q
    induction q using QuotientGroup.induction_on with
    | H x => exact hd g x
  let _inst : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hn : ((Fintype.card (G ⧸ H) : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hsum : ∀ g : G, ∑ q, D q = ((Fintype.card (G ⧸ H) : ℕ) : k) • d g + a g (∑ q, D q) := by
    intro g
    rw [← Equiv.sum_comp (MulAction.toPerm g) D]
    conv_rhs => rw [Equiv.sum_comp (MulAction.toPerm g) D]

    simp only [MulAction.toPerm_apply, hD, Finset.sum_add_distrib, map_sum, Finset.sum_const,
    Finset.card_univ, Nat.cast_smul_eq_nsmul]
  refine ⟨b - (((Fintype.card (G ⧸ H) : ℕ) : k))⁻¹ • ∑ q, D q, fun g => ?_⟩
  have h1 : d g = (((Fintype.card (G ⧸ H) : ℕ) : k))⁻¹ • (∑ q, D q - a g (∑ q, D q)) := by
    rw [← eq_sub_iff_add_eq.2 (hsum g).symm, smul_smul, inv_mul_cancel₀ hn, one_smul]
  have h2 : c g = d g + (a g b - b) := by simp only [d]; abel
  rw [h2, h1, map_sub, map_smul, smul_sub]
  abel

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem actVB_tmul (g : G) (x : V) (b : B) :
    actVB PD ρ g (x ⊗ₜ[Qp] b) = ρ g x ⊗ₜ[Qp] PD.actB g b := rfl

theorem actVB_mul (g h : G) (x : V ⊗[Qp] B) :
    actVB PD ρ (g * h) x = actVB PD ρ g (actVB PD ρ h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp only [actVB_tmul, map_mul]; rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem crisCob_of_finiteIndex [CharZero LL] (H : Subgroup G) [H.FiniteIndex] (c : G → V)
    (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) (b : V ⊗[Qp] B)
    (hb : ∀ h ∈ H, c h ⊗ₜ[Qp] (1 : B) = actVB PD ρ h b - b) :
    ∃ x : V ⊗[Qp] B, ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x :=
  coboundary_of_finiteIndex (actVB PD ρ) (actVB_mul PD ρ) H (fun g => c g ⊗ₜ[Qp] (1 : B))
    (fun g h => by simp only [hc, add_tmul, actVB_tmul, map_one]) b hb

end Generic

section Classes

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O]
    [Algebra O LL] [TopologicalSpace LL] (T : LocLat G Qp LL O)

theorem mem_H1fT_iff_res [CharZero LL] (H : Subgroup G) [H.FiniteIndex] (κ : LatticeCohomology T.L) :
    κ ∈ latticeFiniteCohomology PD T.L ↔ ∃ c : ↥(latticeCocycles (resLat T H)),
      (∃ x : T.V ⊗[Qp] B, ∀ h : ↥H,
        (c : ↥H → T.V) h ⊗ₜ[Qp] (1 : B) = actVB PD T.ρ (h : G) x - x) ∧
      Submodule.Quotient.mk c = resH1 T H κ := by
  constructor
  · rintro ⟨z, ⟨-, -, x, hx⟩, rfl⟩
    exact ⟨⟨resFun T H z, resFun_Z1T T H z z.2⟩, ⟨x, fun h => hx (h : G)⟩, rfl⟩
  · rintro ⟨c, ⟨x, hx⟩, hc⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ κ
    have hc' : (Submodule.Quotient.mk c : LatticeCohomology (resLat T H)) =
        Submodule.Quotient.mk ⟨resFun T H z, resFun_Z1T T H z z.2⟩ := hc
    obtain ⟨y, -, hy⟩ := (Submodule.Quotient.eq _).1 hc'
    refine ⟨z, ⟨z.2, z.2.1, ?_⟩, rfl⟩
    refine crisCob_of_finiteIndex PD T.ρ H z z.2.1.2 (x - y ⊗ₜ[Qp] (1 : B)) fun h hh => ?_
    have h1 : T.ρ h y - y = (c : ↥H → T.V) ⟨h, hh⟩ - (z : G → T.V) h := congrFun hy ⟨h, hh⟩
    have h2 : (z : G → T.V) h = (c : ↥H → T.V) ⟨h, hh⟩ - (T.ρ h y - y) := by rw [h1]; abel
    rw [h2, sub_tmul, sub_tmul, hx ⟨h, hh⟩, map_sub, actVB_tmul, map_one]
    abel

end Classes

theorem GKs_finiteIndex {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (n : ℕ)
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) : W.GKs.FiniteIndex := by
  have h1 : W.GKs = (GlobalTheory.Cyc.Gj K W.s).subgroupOf (GK K) := by
    ext x
    rw [GlobalTheory.Cyc.mem_GKs_iff_mem_Gj, Subgroup.mem_subgroupOf]
  have h2 : (GlobalTheory.Cyc.Gj K W.s).FiniteIndex := by
    have hlp : l.Prime := Fact.out
    constructor
    rw [GlobalTheory.Cyc.Gj, ← IntermediateField.finrank_eq_fixingSubgroup_index,
      GlobalTheory.Cyc.finrank_Ks K W.s W.s_pos]
    have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
    have : FiniteDimensional ℚ_[l] ↥(K0 K) :=
      FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
        (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
    exact (Nat.mul_pos Module.finrank_pos
      (Nat.mul_pos (Nat.sub_pos_of_lt hlp.one_lt) (pow_pos hlp.pos _))).ne'
  rw [h1]
  infer_instance

end GlobalTheory.NL.FiniteRestrictionH1f
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.rowBound_at_place_of_latticeColengthBound : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : ℝ) (y : ℚ), RowL i r ρ π w hw Cx x → x ≤ (y : ℝ) → RowAt (Br.PD D.loc D.nbr i w hw) (O := ↥(OL Cx.LL)) (fun x : D.nd.X i => ⇑(TruncatedSeriesCountingIdentities.locC Cx (rDuO D.nd i r x))) ⇑(TruncatedSeriesCountingIdentities.locC Cx (T2O D.nd i ρ π)) y := by
  first | exact @GlobalTheory.RowAtOfColLen.main | exact GlobalTheory.RowAtOfColLen.main | (intros; apply GlobalTheory.RowAtOfColLen.main <;> assumption)
end
