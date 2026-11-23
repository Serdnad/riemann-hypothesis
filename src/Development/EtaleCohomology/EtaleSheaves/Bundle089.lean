module

public import Development.EtaleCohomology.EtaleSheaves.Bundle021
public import Development.EtaleCohomology.EtaleSheaves.Bundle088
public import Development.EtaleCohomology.EtaleSheaves.EtaleSpreading.FPProof
public import Development.EtaleCohomology.EtaleSheaves.FPColimPf
public import Development.EtaleCohomology.EtaleSheaves.Bundle038
public import Development.EtaleCohomology.EtaleSheaves.Bundle031
public import Development.EtaleCohomology.EtaleSheaves.Bundle084
public import Development.EtaleCohomology.EtaleSheaves.Bundle058
public import Development.EtaleCohomology.EtaleSheaves.Bundle059
public import Development.EtaleCohomology.EtaleSheaves.Bundle082
public import Development.EtaleCohomology.EtaleSheaves.Bundle045
public import Development.EtaleCohomology.EtaleSheaves.Bundle037
public import Development.EtaleCohomology.EtaleSheaves.Bundle083
public import Development.EtaleCohomology.EtaleSheaves.Bundle075
public import Development.EtaleCohomology.EtaleSheaves.Bundle087
public import Development.EtaleCohomology.EtaleSheaves.Bundle076
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.EtaleCohomology.EtaleSheaves.Bundle086
public import Development.EtaleCohomology.EtaleSheaves.Bundle085
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
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
public import Mathlib.RingTheory.Etale.Descent
import Mathlib.Order.CompletePartialOrder
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
public import Development.EtaleCohomology.EtaleSheaves.Bundle025
public import Development.EtaleCohomology.EtaleSheaves.LocalSlices.LocSliceOf
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

@[expose] public section

section

theorem LateralTheory.E.TruncationIsoComparison.IEComp_of : LateralTheory.E.t_E3Cut.IEComp :=
  LateralTheory.E.IECompPf.IEComp_of (LateralTheory.E.UnderFAPf.UnderFA_of LateralTheory.E.FPColimPf.FPColim_of)
    (LateralTheory.E.SpreadPf.Cut.EtSpreads_of LateralTheory.E.SpreadPf.FPProof.finite_presentation_ring_maps_pre_ind_spread LateralTheory.E.EtStagePf.EtStage_of)
theorem LateralTheory.E.TruncationIsoComparison.Comp_of : LateralTheory.E.SHExistsPf.Comp := @LateralTheory.E.TruncationIsoComparison.IEComp_of
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafTwistIsoPf

theorem leafLoc : LateralTheory.E.LeafTwistPf.LeafLoc :=
  LateralTheory.E.LeafLocPf.LeafLoc_of' (LateralTheory.E.LocSecPfC.LocSec_of LateralTheory.E.ClassSecPf.ClassSec_of)
    (LateralTheory.E.LocSlicePf.LocSlice_of' LateralTheory.E.PullMonoPf.PullMono_of)

theorem leafTwSec : LateralTheory.E.LeafTwistPf.LeafTwSec :=
  LateralTheory.E.LeafTwSecPf.LeafTwSec_of' LateralTheory.E.LeafTwInjPf.LeafTwInj_of LateralTheory.E.LeafTwSecPf.LeafTwSurj_of

end LateralTheory.E.LeafTwistIsoPf

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf
open LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.KernelLocalization

theorem KerLoc_of (hC : Coprod) (hD : LateralTheory.E.TruncationKernel.RelDesc) : KerLoc := by
  intro hH q _ i n A Y φ hq P hpush het hlow _ D d hPD hpts Y' w φ' hpo
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, rfl⟩ := relExact _ _ _ n x hx
  obtain ⟨E, e, Z, u, ψ, h, he, hs, h0⟩ := relKill hH.2.2.2.2.2.2.1 hC q i n φ hq d hpts w φ' hpo z hx
  have hz : z = 0 := (injective_iff_map_eq_zero _).1
    (hD hH q i n φ hq P hpush het hlow D d hPD Y' w φ' hpo E e Z u ψ he hs (het d e hPD he) h) z h0
  rw [hz, map_zero]

end LateralTheory.E.KernelLocalization
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut TensorProduct

namespace LateralTheory.E.SpreadingOutSmoothness

theorem stepB {R K B A : Type} [CommRing R] [CommRing K] [CommRing B] [CommRing A] [Algebra R K] [Algebra R A]
    [Algebra R B] [Algebra K B] [IsScalarTower R K B] [Algebra A B] [IsScalarTower R A B] (M : Submonoid R)
    [IsLocalization M K] [IsLocalization (Algebra.algebraMapSubmonoid A M) B] [Algebra.Smooth K B]
    (Q : Ideal B) [Q.IsPrime] : Algebra.IsSmoothAt R (Q.comap (algebraMap A B)) := by
  haveI : Algebra.FormallySmooth R K := Algebra.FormallySmooth.of_isLocalization M
  haveI : Algebra.FormallySmooth K (Localization.AtPrime Q) := inferInstance
  haveI : Algebra.FormallySmooth R (Localization.AtPrime Q) := Algebra.FormallySmooth.comp R K _
  haveI := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (Algebra.algebraMapSubmonoid A M) (Localization.AtPrime Q) Q
  exact Algebra.FormallySmooth.of_equiv ((IsLocalization.algEquiv (Q.comap (algebraMap A B)).primeCompl
    (Localization.AtPrime Q) _).restrictScalars R)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem algDescend (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω)
    (A : Type) [CommRing A] [Algebra R A] (hfp : Algebra.FinitePresentation R A) (hs : Algebra.Smooth Ω (Ω ⊗[R] A))
    (P : PrimeSpectrum (Ω ⊗[R] A)) :
    PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] Ω ⊗[R] A).toRingHom P ∈ Algebra.smoothLocus R A := by
  letI : Algebra (FractionRing R) Ω := FractionRing.liftAlgebra R Ω
  haveI : IsScalarTower R (FractionRing R) Ω := FractionRing.isScalarTower_liftAlgebra R Ω
  let e := Algebra.TensorProduct.cancelBaseChange R (FractionRing R) Ω Ω A
  haveI : Algebra.Smooth Ω (Ω ⊗[FractionRing R] (FractionRing R ⊗[R] A)) := Algebra.Smooth.of_equiv e.symm
  haveI : Module.Free (FractionRing R) Ω := Module.Free.of_divisionRing _ Ω
  haveI : Algebra.Smooth (FractionRing R) (FractionRing R ⊗[R] A) :=
    Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat Ω
  letI : Algebra A (FractionRing R ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) (FractionRing R ⊗[R] A) :=
    IsLocalization.tensorRight _ _
  let φ : FractionRing R ⊗[R] A →+* Ω ⊗[R] A := e.toRingHom.comp
    (Algebra.TensorProduct.includeRight : FractionRing R ⊗[R] A →ₐ[FractionRing R] Ω ⊗[FractionRing R] _).toRingHom
  haveI : (P.asIdeal.comap φ).IsPrime := Ideal.comap_isPrime _ _
  have hφ : φ.comp (algebraMap A (FractionRing R ⊗[R] A)) =
      (Algebra.TensorProduct.includeRight : A →ₐ[R] Ω ⊗[R] A).toRingHom := by
    ext a
    show e (1 ⊗ₜ (1 ⊗ₜ a)) = 1 ⊗ₜ a
    rw [Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
  have hc : PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] Ω ⊗[R] A).toRingHom P =
      ⟨(P.asIdeal.comap φ).comap (algebraMap A (FractionRing R ⊗[R] A)), inferInstance⟩ := by
    ext1; simp only [PrimeSpectrum.comap_asIdeal, Ideal.comap_comap, hφ]
  rw [hc]
  exact stepB (K := FractionRing R) (nonZeroDivisors R) (P.asIdeal.comap φ)

def LeafAlgDescend : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω)
    (A : Type) [CommRing A] [Algebra R A], Algebra.FinitePresentation R A → Algebra.Smooth Ω (Ω ⊗[R] A) →
    ∀ P : PrimeSpectrum (Ω ⊗[R] A),
      PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] Ω ⊗[R] A).toRingHom P ∈ Algebra.smoothLocus R A

def LeafStalkOfAlg : Prop := LeafAlgDescend → LateralTheory.E.LeafSpreadSmoothAffSmPf.LeafStalkDescend

theorem leafAlgDescend : LeafAlgDescend := fun k _ Ω _ _ R A _ _ hfp hs P => algDescend k Ω R A hfp hs P

theorem LeafSpreadSmooth1_of (hB : LateralTheory.E.LeafSpreadSmoothPf.LeafSpreadRelDim) (hT : LeafStalkOfAlg) :
    LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadSmooth1 :=
  LateralTheory.E.LeafSpreadSmoothPf.LeafSpreadSmooth_of
    (LateralTheory.E.LeafSpreadSmoothAffSmPf.LeafSpreadSmoothAffSm_of (hT leafAlgDescend)) hB

end LateralTheory.E.SpreadingOutSmoothness

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.BuildCut LateralTheory.E.SysFMPf Topology

namespace LateralTheory.E.FMrangePf

def RRsub : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ q : PrimeSpectrum W,
    RR w q ⊆ closure (w.toNormalization.base '' {p : Spec (CommRingCat.of W) | p.asIdeal ≤ q.asIdeal})

theorem range_spec_atPrime {W : Type} [CommRing W] (q : PrimeSpectrum W) :
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal)))).base =
      {p : Spec (CommRingCat.of W) | p.asIdeal ≤ q.asIdeal} := by
  have h := PrimeSpectrum.localization_comap_range (Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl
  ext p
  change p ∈ Set.range (PrimeSpectrum.comap (algebraMap W (Localization.AtPrime q.asIdeal))) ↔ _
  rw [h]
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hd x hx
    by_contra hq
    exact Set.disjoint_left.1 hd (show x ∈ (q.asIdeal.primeCompl : Set W) from hq) hx
  · intro hle
    exact Set.disjoint_left.2 fun x hx hp => hx (hle hp)

theorem mem_basicOpen_toNorm {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) (s : Γ(w.normalization, ⊤)) (p : Spec (CommRingCat.of W)) :
    w.toNormalization p ∈ w.normalization.basicOpen s ↔ phi w s ∉ p.asIdeal := by
  change p ∈ w.toNormalization ⁻¹ᵁ w.normalization.basicOpen s ↔ _
  rw [Scheme.preimage_basicOpen_top, AlgebraicGeometry.basicOpen_eq_of_affine']
  rfl

theorem phi_injective {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) : Function.Injective (phi w) := by
  have h1 : Function.Injective (w.toNormalization.appTop) := w.toNormalization.app_injective ⊤
  have h2 : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of W)).hom :=
    ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of W)).hom)).1
  exact h2.comp h1

theorem closure_sub_RR {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) (q : PrimeSpectrum W) :
    closure (w.toNormalization.base '' {p : Spec (CommRingCat.of W) | p.asIdeal ≤ q.asIdeal}) ⊆ RR w q := by
  intro y hy s hs hsq
  have hid : IsIdempotentElem s := phi_injective w (by rw [map_mul]; exact hs.eq)
  have hcl : IsClosed (w.normalization.basicOpen s : Set w.normalization) := by
    rw [← isOpen_compl_iff]
    have : (w.normalization.basicOpen s : Set w.normalization)ᶜ = w.normalization.basicOpen (1 - s) := by
      ext x
      exact LateralTheory.E.SysFMPfSys.basicOpen_one_sub hid x
    rw [this]
    exact (w.normalization.basicOpen (1 - s)).isOpen
  refine closure_minimal ?_ hcl hy
  rintro _ ⟨p, hp, rfl⟩
  exact (mem_basicOpen_toNorm w s p).2 fun h => hsq (hp h)

def IdemLift : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ e : W, IsIdempotentElem e → ∃ s, phi w s = e

def QcIdem : Prop := ∀ (W : Type) [CommRing W], ProdACF W → ∀ U : (Spec (CommRingCat.of W)).Opens,
  IsCompact (U : Set (Spec (CommRingCat.of W))) → ∃ e : W, IsIdempotentElem e ∧ ∀ p : Spec (CommRingCat.of W),
    p ∈ U ↔ e ∉ p.asIdeal

theorem RRsub_of (hI : IdemLift) (hQ : QcIdem) : RRsub := by
  intro P _ _ W _ w hW q y hy
  by_contra hc
  rw [mem_closure_iff] at hc
  push Not at hc
  obtain ⟨o, ho, hyo, hoT⟩ := hc
  obtain ⟨V, hV, hyV, hVo⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 (Scheme.isBasis_affineOpens w.normalization))
    (show y ∈ (⟨o, ho⟩ : TopologicalSpace.Opens w.normalization) from hyo)
  have hVc : IsCompact (w.toNormalization ⁻¹ᵁ V : Set (Spec (CommRingCat.of W))) :=
    QuasiCompact.isCompact_preimage _ V.isOpen (IsAffineOpen.isCompact hV)
  obtain ⟨e, he, hpe⟩ := hQ W hW _ hVc
  have heq : e ∈ q.asIdeal := by
    by_contra hnq
    have hmem : w.toNormalization q ∈ V := (hpe q).2 hnq
    have : w.toNormalization q ∈ o ∩ (w.toNormalization.base '' {p : Spec (CommRingCat.of W) | p.asIdeal ≤ q.asIdeal}) :=
      ⟨hVo hmem, q, show q.asIdeal ≤ q.asIdeal from le_refl _, rfl⟩
    rw [hoT] at this
    exact this
  have hf : IsIdempotentElem (1 - e) := he.one_sub
  have hfq : (1 - e) ∉ q.asIdeal := fun h => q.2.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using q.asIdeal.add_mem heq h))
  obtain ⟨s, hs⟩ := hI W w hW (1 - e) hf
  have hys : y ∈ w.normalization.basicOpen s := hy s (by rw [hs]; exact hf) (by rw [hs]; exact hfq)
  obtain ⟨_, ⟨hz1, hz2⟩, p, rfl⟩ := w.toNormalization.denseRange.inter_open_nonempty
    ((w.normalization.basicOpen s ⊓ V : w.normalization.Opens) : Set w.normalization)
    (w.normalization.basicOpen s ⊓ V).isOpen ⟨y, hys, hyV⟩
  have h1 : phi w s ∉ p.asIdeal := (mem_basicOpen_toNorm w s p).1 hz1
  have h2 : e ∉ p.asIdeal := (hpe p).1 hz2
  rw [hs] at h1
  have : e * (1 - e) ∈ p.asIdeal := by rw [mul_sub, mul_one, he.eq, sub_self]; exact p.asIdeal.zero_mem
  rcases p.2.mem_or_mem this with h | h
  · exact h2 h
  · exact h1 h

theorem FMrange_of (hC : RRsub) : FMrange := by
  intro P _ _ W _ w hW q m e1 e2
  set a := Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal)))
  have : IsIntegralHom (m ≫ w.fromNormalization) := by rw [e2]; infer_instance
  have : IsIntegralHom m := IsIntegralHom.of_comp m w.fromNormalization
  have hcl : IsClosedMap m.base := m.isClosedMap
  have hd : closure (Set.range (a ≫ w).toNormalization.base) = Set.univ :=
    (a ≫ w).toNormalization.denseRange.closure_range
  have himg : m.base '' Set.range (a ≫ w).toNormalization.base =
      w.toNormalization.base '' Set.range a.base := by
    rw [← Set.range_comp, ← Set.range_comp]
    congr 1
    funext x
    simpa only [Function.comp_apply, ← Scheme.Hom.comp_apply] using
      congrArg (fun f : Spec (CommRingCat.of (Localization.AtPrime q.asIdeal)) ⟶
        w.normalization => f x) e1.symm
  rw [subset_antisymm (hC W w hW q) (closure_sub_RR w q), ← range_spec_atPrime q, ← Set.image_univ, ← hd,
    ← hcl.closure_image_eq_of_continuous m.continuous, himg]

theorem FMrange_of_leaves (hI : IdemLift) (hQ : QcIdem) : FMrange :=
  FMrange_of (RRsub_of hI hQ)

end LateralTheory.E.FMrangePf
end
end

section

namespace LateralTheory.E.LeafClosedSH0PfCut
open LateralTheory.E.LeafClosedSH0Pf

theorem LeafClosedSH0_of (hS : LeafSHSieve) : LateralTheory.E.LeafVanBPf.LeafClosedSH0 :=
  LateralTheory.E.LeafClosedSH0Pf.LeafClosedSH0_of hS LateralTheory.E.LeafClosedSH0PfQuot.shQuot
    LateralTheory.E.LeafClosedSH0PfEmpty.emptySec LateralTheory.E.LeafClosedSH0PfPrim.primLift

end LateralTheory.E.LeafClosedSH0PfCut
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafDescendFPPf LateralTheory.E.LeafPairFPPf LateralTheory.E.LeafMapFPPf

namespace LateralTheory.E.LeafMapFPPf2

theorem dgMap_isPullback {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R : Subalgebra k Ω} {D1 : Scheme.{0}}
    (q1 : D1 ⟶ Sp R) {S T : Subalgebra k Ω} (hS : R ≤ S) (hT : R ≤ T) (h : S ≤ T) :
    IsPullback (dgMap q1 hS hT h) (pullback.snd q1 (incl hT)) (pullback.snd q1 (incl hS)) (incl h) := by
  have t : IsPullback (dgMap q1 hS hT h ≫ pullback.fst _ _) (pullback.snd q1 (incl hT)) q1 (incl h ≫ incl hS) := by
    rw [dgMap_fst, incl_comp]; exact IsPullback.of_hasPullback _ _
  exact IsPullback.of_right t (dgMap_snd q1 hS hT h) (IsPullback.of_hasPullback _ _)

theorem stages : LeafStagesFP := by
  intro k _ Ω _ _ R D1 q1 hq1
  obtain ⟨_, h2, h3⟩ := hq1
  refine ⟨fun S => ⟨?_, ?_⟩, fun S T h => ?_⟩
  · have : QuasiCompact (pullback.snd q1 (incl S.unop.2.2)) :=
      by
      first
        | exact MorphismProperty.of_isPullback (P := @QuasiCompact) (IsPullback.of_hasPullback q1 (incl S.unop.2.2)) h2
    exact @QuasiCompact.compactSpace_of_compactSpace _ _ (pullback.snd q1 (incl S.unop.2.2)) this _
  · have : QuasiSeparated (pullback.snd q1 (incl S.unop.2.2)) :=
      by
      first
        | exact MorphismProperty.of_isPullback (P := @QuasiSeparated) (IsPullback.of_hasPullback q1 (incl S.unop.2.2)) h3
    exact @quasiSeparatedSpace_of_quasiSeparated _ _ (pullback.snd q1 (incl S.unop.2.2)) _ this
  · first
      | exact MorphismProperty.of_isPullback (P := @IsAffineHom) (dgMap_isPullback q1 S.2.2 T.2.2 h) inferInstance
      | exact MorphismProperty.of_isPullback (P := @IsAffineHom) (dgMap_isPullback q1 S.2.2 T.2.2 h).flip inferInstance

theorem morphismDescent_of_isLimit (hL : LeafLimFP) : LeafMapFP := LateralTheory.E.LeafMapFPPf.morphismDescent_of_isLimit hL stages

end LateralTheory.E.LeafMapFPPf2

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafSHPtPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafInj0Pf LateralTheory.E.LeafInj0VPf

theorem germ (hH : Hyps) (q : ℕ) [NeZero q] (i : ℤ) {B : Scheme.{0}} (U : B.Etale) (x : U.left)
    {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (hc : IsColimit c)
    (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (y : ∀ j, (V j).left) (e : ∀ j, Sp (D.obj j) ⟶ (V j).left)
    (t : Sp c.pt ⟶ U.left) (he : ∀ j, IsIso (e j)) (hy : ∀ j, (a j).left (y j) = x)
    (hq : ∀ j, IsUnit ((q : ℕ) : D.obj j))
    (hcomp : ∀ (j k : J) (f : j ⟶ k), Spec.map (CommRingCat.ofHom (D.map f).hom) ≫ e j ≫ (a j).left = e k ≫ (a k).left)
    (ht : ∀ j, Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ (a j).left = t)
    (s : Sec (tw q i) U.left) (hs : Sec.res t s = 0) :
    ∃ (U' : B.Etale) (a' : U' ⟶ U) (y' : U'.left), a'.left y' = x ∧ Sec.res a'.left s = 0 := by
  have hA9 : A9 := hH.2.2.2.2.2.2.2.1
  have hB1 : B1 := hH.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, eq, hnat, -⟩ := hA9 (ZMod q) (tw q i)
  obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
  set z : Ht q (sp (D.obj j)) 0 i := eq _ (Sec.res (e j ≫ (a j).left) s) with hz
  have h0 : pull _ (spMap (c.ι.app j).hom) _ _ z = 0 := by
    rw [hz, spMap, hnat, ← res_comp, ht, hs, map_zero]
  obtain ⟨k, f, hk⟩ := (hB1 q D c hc 0 i).2 j z (hq j) h0
  rw [hz, spMap, hnat, ← res_comp, hcomp] at hk
  have hk' : Sec.res (e k ≫ (a k).left) s = 0 := (eq _).injective (by rw [hk, map_zero])
  refine ⟨V k, a k, y k, hy k, ?_⟩
  have := congrArg (Sec.res (inv (e k))) hk'
  rw [← res_comp, IsIso.inv_hom_id_assoc] at this
  simpa using this

def LeafSHNb : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ {B : Scheme.{0}}
  (U : B.Etale) (_ : U.left ⟶ Sp k) (x : U.left),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (_ : IsColimit c)
    (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (y : ∀ j, (V j).left) (e : ∀ j, Sp (D.obj j) ⟶ (V j).left)
    (t : Sp c.pt ⟶ U.left), (∀ j, IsIso (e j)) ∧ (∀ j, (a j).left (y j) = x) ∧ (∀ j, IsUnit ((q : ℕ) : D.obj j)) ∧
    (∀ (j k : J) (f : j ⟶ k), Spec.map (CommRingCat.ofHom (D.map f).hom) ≫ e j ≫ (a j).left = e k ≫ (a k).left) ∧
    (∀ j, Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ (a j).left = t) ∧ SH c.pt ∧
    (∀ (U' : B.Etale) (b : U' ⟶ U) (y' : U'.left), b.left y' = x →
      ∃ (j : J) (g : (V j).left ⟶ U'.left), g ≫ b.left = (a j).left)

def LeafSHTop : Prop := ∀ {B : Scheme.{0}} (U : B.Etale) (x : U.left) {J : Type} [SmallCategory J] [Nonempty J]
  (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (e : ∀ j, Sp (D.obj j) ⟶ (V j).left)
  (t : Sp c.pt ⟶ U.left), (∀ j, Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ (a j).left = t) →
  (∀ (U' : B.Etale) (b : U' ⟶ U) (y' : U'.left), b.left y' = x →
      ∃ (j : J) (g : (V j).left ⟶ U'.left), g ≫ b.left = (a j).left) →
  (∀ O : U.left.Opens, x ∈ O → Set.range t ⊆ O) ∧
  (∀ S ∈ (EtTop B) U, ∃ (U' : B.Etale) (a' : U' ⟶ U), S a' ∧ ∃ t' : Sp c.pt ⟶ U'.left, t' ≫ a'.left = t)

theorem LeafSHPt_of (hN : LeafSHNb) (hT : LeafSHTop) : LeafSHPt := by
  intro hH q _ k _ hq i B U s0 x
  obtain ⟨J, _, _, D, c, hc, V, a, y, e, t, he, hy, hqj, hcomp, ht, hSH, hcof⟩ := hN hH q k hq U s0 x
  have : Nonempty J := IsFiltered.nonempty
  obtain ⟨hO, hL⟩ := hT U x D c V a e t ht hcof
  exact ⟨c.pt, inferInstance, t, hSH, hO, hL, fun s hs => germ hH q i U x D c hc V a y e t he hy hqj hcomp ht s hs⟩

end LateralTheory.E.LeafSHPtPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafDescendFPPf LateralTheory.E.LeafPairFPPf LateralTheory.E.LeafMapFPPf

namespace LateralTheory.E.LeafLimFPPf

theorem isLimit_pullback_finitelyGenerated : LeafLimFP := by
  intro k _ Ω _ _ R hR C1 D1 c1 q1 v1 hs _
  refine ⟨IsLimit.ofExistsUnique fun s => ?_⟩
  let o : GlobalTheory.FGAbove R := ⟨R, hR, le_rfl⟩
  let a : ∀ S : GlobalTheory.FGAbove R, s.pt ⟶ pullback q1 (incl S.2.2) := fun S => s.π.app (op S)
  have ha : ∀ (S T : GlobalTheory.FGAbove R) (h : S.1 ≤ T.1), a T ≫ dgMap q1 S.2.2 T.2.2 h = a S :=
    fun S T h => s.w (homOfLE (show S ≤ T from h)).op
  have hsnd : ∀ (S T : GlobalTheory.FGAbove R) (h : S.1 ≤ T.1),
      (a T ≫ pullback.snd _ _) ≫ incl h = a S ≫ pullback.snd _ _ := fun S T h => by
    rw [← ha S T h, Category.assoc, Category.assoc, dgMap_snd]
  obtain ⟨ψ, hψ⟩ := GlobalTheory.FGAbove.exists_ringHom hR
    (fun S => ((Scheme.ΓSpecIso (.of S.1)).inv ≫ (a S ≫ pullback.snd _ _).appTop).hom) (by
      intro S T h x
      rw [← hsnd S T h]
      exact (GlobalTheory.appTop_comp_spMap (Subalgebra.inclusion h).toRingHom _ x).symm)
  obtain ⟨b, hb⟩ : ∃ b : s.pt ⟶ Sp Ω, (Scheme.ΓSpecIso (.of Ω)).inv ≫ b.appTop = CommRingCat.ofHom ψ := by
    refine ⟨s.pt.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ), ?_⟩
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      Scheme.toSpecΓ_appTop]
    simp
  have hb' : ∀ S : GlobalTheory.FGAbove R, b ≫ toR S.1 = a S ≫ pullback.snd _ _ := fun S =>
    GlobalTheory.hom_spec_ext (CommRingCat.hom_ext (RingHom.ext fun x => by
      refine (GlobalTheory.appTop_comp_spMap (algebraMap S.1 Ω) b x).trans ?_
      rw [hb]
      exact hψ S x))
  have hf : ∀ S : GlobalTheory.FGAbove R, a S ≫ pullback.fst _ _ = a o ≫ pullback.fst _ _ := fun S => by
    rw [← ha o S S.2.2, Category.assoc, dgMap_fst]
  have hw : (a o ≫ pullback.fst _ _) ≫ q1 = b ≫ toR R := by
    conv_rhs => rw [← toR_incl o.2.2]
    rw [← Category.assoc, hb' o, Category.assoc, Category.assoc, pullback.condition]
  refine ⟨hs.lift (a o ≫ pullback.fst _ _) b hw, fun S => ?_, fun m hm => ?_⟩
  · show _ ≫ pullback.lift v1 (c1 ≫ toR S.unop.1) _ = a S.unop
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hs.lift_fst, hf S.unop]
    · rw [Category.assoc, pullback.lift_snd, hs.lift_snd_assoc, hb']
  · change s.pt ⟶ C1 at m
    have hm' : ∀ S : GlobalTheory.FGAbove R, m ≫ pullback.lift v1 (c1 ≫ toR S.1)
        (by rw [Category.assoc, toR_incl, hs.w]) = a S := fun S => hm (op S)
    apply hs.hom_ext
    · rw [hs.lift_fst, ← hm' o, Category.assoc, pullback.lift_fst]
    · rw [hs.lift_snd]
      refine GlobalTheory.hom_spec_ext (CommRingCat.hom_ext (RingHom.ext fun x => ?_))
      obtain ⟨S, hx⟩ := GlobalTheory.FGAbove.exists_mem hR x
      have e : (m ≫ c1) ≫ toR S.1 = b ≫ toR S.1 := by
        rw [hb', ← hm' S, Category.assoc, Category.assoc, pullback.lift_snd]
      exact (GlobalTheory.appTop_comp_spMap (algebraMap S.1 Ω) _ ⟨x, hx⟩).symm.trans
        (e ▸ GlobalTheory.appTop_comp_spMap (algebraMap S.1 Ω) b ⟨x, hx⟩)

end LateralTheory.E.LeafLimFPPf

end
end

section

namespace LateralTheory.E.LeafSpreadLQFMap_vtuPfG


open LateralTheory.E.SpreadingOutLocallyQuasiFinite in
theorem LeafSpreadLQFMap_of (hD : LeafQFAtDescend) (hO : LeafOpenSpread) :
    LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadLQFMap :=
  LateralTheory.E.SpreadingOutLocallyQuasiFinite.LeafSpreadLQFMap_of quasi_finite_at_base_change_of_finite_type hD hO

end LateralTheory.E.LeafSpreadLQFMap_vtuPfG
end
