module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle025
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.GeoNum
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle026
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle028
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

namespace IntegralCoordGeometricNumber

variable {T T₂ : Type} [Fintype T] [DecidableEq T] [Fintype T₂] [DecidableEq T₂]

def substR (R : Type) [CommRing R] (A : Matrix T T₂ ℤ) :
    MRingOver R (dualBlocks T₂) →ₐ[R] MRingOver R (dualBlocks T) :=
  aeval fun p => ∑ t, C ((A t p.2 : ℤ) : R) * X (⟨(), t⟩ : Σ k : Unit, dualBlocks T k)


omit [Fintype T₂] [DecidableEq T] [DecidableEq T₂] in
theorem substR_int (A : Matrix T T₂ ℤ) : substR ℤ A = intCoordSubst A := by
  unfold substR intCoordSubst
  simp


omit [DecidableEq T₂] in
theorem substR_substR (R : Type) [CommRing R] {A : Matrix T T₂ ℤ} {B : Matrix T₂ T ℤ}
    (hAB : A * B = 1) (f : MRingOver R (dualBlocks T)) : substR R A (substR R B f) = f := by
  have h : (substR R A).comp (substR R B) = AlgHom.id R _ := by
    refine MvPolynomial.algHom_ext fun p => ?_
    obtain ⟨⟨⟩, t⟩ := p

    simp only [AlgHom.comp_apply, AlgHom.id_apply, substR, aeval_X, map_sum, map_mul, aeval_C,
    algebraMap_eq]
    simp_rw [Finset.mul_sum, ← mul_assoc, ← C_mul]
    rw [Finset.sum_comm]

    simp_rw [← Finset.sum_mul, ← map_sum C, ← Int.cast_mul, ← Int.cast_sum]
    have h1 : ∀ x : T, ∑ s, B s t * A x s = (A * B) x t := fun x => by
      simp [Matrix.mul_apply, mul_comm]
    simp_rw [h1, hAB, Matrix.one_apply]
    simp
  exact DFunLike.congr_fun h f


omit [DecidableEq T] in
theorem isWH_iff {R : Type} [CommRing R] (f : MRingOver R (dualBlocks T)) (m : Unit → ℕ) :
    IsWeightedHomogeneous (NumbersDVR.blockWeight (dualBlocks T)) f m ↔ f.IsHomogeneous (m ()) := by
  have hw : ∀ d : (Σ k : Unit, dualBlocks T k) →₀ ℕ,
      Finsupp.weight (1 : (Σ k : Unit, dualBlocks T k) → ℕ) d = ∑ i : T, d ⟨(), i⟩ := by
    intro d
    rw [Pi.one_def, ← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum, Fintype.sum_sigma]
    simp
  unfold IsHomogeneous IsWeightedHomogeneous
  simp only [Bridge.weight_blockWeight, hw, funext_iff]
  constructor
  · intro h d hd
    exact h hd ()
  · intro h d hd u
    cases u
    exact h hd


omit [DecidableEq T] [DecidableEq T₂] in
theorem substR_isWH (R : Type) [CommRing R] (A : Matrix T T₂ ℤ) {f : MRingOver R (dualBlocks T₂)}
    {m : Unit → ℕ} (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight (dualBlocks T₂)) f m) :
    IsWeightedHomogeneous (NumbersDVR.blockWeight (dualBlocks T)) (substR R A f) m := by
  rw [isWH_iff] at hf ⊢
  have hg : ∀ p : Σ k : Unit, dualBlocks T₂ k,
      (∑ t, C ((A t p.2 : ℤ) : R) * X (⟨(), t⟩ : Σ k : Unit, dualBlocks T k)).IsHomogeneous 1 := by
    intro p
    refine IsHomogeneous.sum _ _ _ fun t _ => ?_
    have := (isHomogeneous_C (Σ k : Unit, dualBlocks T k) ((A t p.2 : ℤ) : R)).mul
      (isHomogeneous_X R (⟨(), t⟩ : Σ k : Unit, dualBlocks T k))
    rwa [zero_add] at this
  have := hf.eval₂ (algebraMap R _) _ (fun r => by rw [algebraMap_eq]; exact isHomogeneous_C _ r) hg
  rw [one_mul] at this
  unfold substR
  rw [aeval_def]
  exact this

theorem comap_substR (R : Type) [CommRing R] {A : Matrix T T₂ ℤ} {B : Matrix T₂ T ℤ}
    (hAB : A * B = 1) (hBA : B * A = 1) (V : Ideal (MRingOver R (dualBlocks T))) :
    V.comap (substR R A) = V.map (substR R B) := by
  apply le_antisymm
  · intro f hf
    rw [← substR_substR R hBA f]
    exact Ideal.mem_map_of_mem _ hf
  · rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, Ideal.mem_comap, substR_substR R hAB]
    exact hg


omit [Fintype T₂] [DecidableEq T] [DecidableEq T₂] in
theorem red_substR (p : ℕ) (A : Matrix T T₂ ℤ) (f : MRingOver ℤ (dualBlocks T₂)) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) (substR ℤ A f) =
      substR (ZMod p) A (MvPolynomial.map (Int.castRingHom (ZMod p)) f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [substR]
  | add f g hf hg => rw [map_add (f := _), map_add (f := _), hf, hg, map_add (f := _), map_add (f := _)]
  | mul_X f q hf =>
    rw [map_mul, map_mul, hf, map_mul, map_mul, map_X]
    congr 1

    simp [substR, map_sum]

theorem hilbFn_comap (F : Type) [Field F] {A : Matrix T T₂ ℤ} {B : Matrix T₂ T ℤ}
    (hAB : A * B = 1) (hBA : B * A = 1) (Q : Ideal (MRingOver F (dualBlocks T))) :
    NumbersDVR.hilbFn (Q.comap (substR F A)) = NumbersDVR.hilbFn Q := by
  let e : MRingOver F (dualBlocks T₂) ≃ₐ[F] MRingOver F (dualBlocks T) :=
    AlgEquiv.ofAlgHom (substR F A) (substR F B) (AlgHom.ext fun f => substR_substR F hAB f)
      (AlgHom.ext fun f => substR_substR F hBA f)
  have hQ : Q = (Q.comap (substR F A)).map (e : MRingOver F (dualBlocks T₂) →+* MRingOver F (dualBlocks T)) :=
    (Ideal.map_comap_of_surjective _ e.surjective Q).symm
  let qe := Ideal.quotientEquivAlg (Q.comap (substR F A)) Q e hQ
  have hcomp : qe.toLinearEquiv.toLinearMap ∘ₗ (Ideal.Quotient.mkₐ F (Q.comap (substR F A))).toLinearMap =
      (Ideal.Quotient.mkₐ F Q).toLinearMap ∘ₗ (substR F A).toLinearMap :=
    LinearMap.ext fun x => rfl
  have hH : ∀ m : Unit → ℕ,
      (weightedHomogeneousSubmodule F (NumbersDVR.blockWeight (dualBlocks T₂)) m).map
        (substR F A).toLinearMap =
      weightedHomogeneousSubmodule F (NumbersDVR.blockWeight (dualBlocks T)) m := by
    intro m
    apply le_antisymm
    · rw [Submodule.map_le_iff_le_comap]
      intro f hf
      rw [Submodule.mem_comap, mem_weightedHomogeneousSubmodule] at *
      exact substR_isWH F A hf
    · intro g hg
      rw [mem_weightedHomogeneousSubmodule] at hg
      exact ⟨substR F B g, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr (substR_isWH F B hg),
        substR_substR F hAB g⟩
  funext m
  unfold NumbersDVR.hilbFn
  split_ifs with hm
  · have key : (NumbersDVR.gradedPiece (Q.comap (substR F A)) fun k => (m k).toNat).map
        qe.toLinearEquiv.toLinearMap = NumbersDVR.gradedPiece Q fun k => (m k).toNat := by
      unfold NumbersDVR.gradedPiece
      rw [← Submodule.map_comp, hcomp, Submodule.map_comp, hH]
    congr 1
    rw [← key]
    exact (LinearEquiv.finrank_map_eq qe.toLinearEquiv _).symm
  · rfl

end IntegralCoordGeometricNumber


open IntegralCoordGeometricNumber in
theorem IntCoordGeoNum.proof : IntCoordGeoNum.Statement := by
  intro T T₂ _ _ _ _ A B hAB hBA V n p hV hp hpV hdim a
  have : Fact p.Prime := ⟨hp⟩
  rw [← substR_int]
  have hsurj : Function.Surjective (substR ℤ A) := fun f => ⟨substR ℤ B f, substR_substR ℤ hAB f⟩
  have hV' : IsMultiProjPrime (V.comap (substR ℤ A)) := by
    have : V.IsPrime := hV.1
    refine ⟨inferInstance, ?_, ?_⟩
    · obtain ⟨S, hS, hVS⟩ := hV.2.1
      refine ⟨substR ℤ B '' S, ?_, ?_⟩
      · rintro _ ⟨f, hf, rfl⟩
        obtain ⟨b, hb⟩ := hS f hf
        exact ⟨b, (Bridge.isMultiHomog_iff _ b).mp
          (substR_isWH ℤ B ((Bridge.isMultiHomog_iff f b).mpr hb))⟩
      · rw [comap_substR ℤ hAB hBA, hVS, Ideal.map_span]
    · intro k
      obtain ⟨t, ht⟩ := hV.2.2 k
      by_contra h
      push Not at h
      apply ht
      have hmem : substR ℤ B (X ⟨k, t⟩) ∈ V.comap (substR ℤ A) := by
        simp only [substR, aeval_X]
        exact Ideal.sum_mem _ fun s _ => Ideal.mul_mem_left _ _ (h s)
      rwa [Ideal.mem_comap, substR_substR ℤ hAB] at hmem
  have hpV' : (C (p : ℤ) : MRing (dualBlocks T₂)) ∈ V.comap (substR ℤ A) := by
    rw [Ideal.mem_comap]
    simpa [substR] using hpV
  have hdim' : ringKrullDim (MRing (dualBlocks T₂) ⧸ V.comap (substR ℤ A)) =
      ((n + Fintype.card Unit : ℕ) : WithBot ℕ∞) := by
    rw [← hdim]
    exact ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq (by
        rw [← RingHom.comap_ker, Ideal.mk_ker]
        try rfl)).trans
      (RingHom.quotientKerEquivOfSurjective (f := (Ideal.Quotient.mk V).comp
        (substR ℤ A : MRing (dualBlocks T₂) →+* MRing (dualBlocks T)))
        (Ideal.Quotient.mk_surjective.comp hsurj)))
  rw [← Bridge.intNum_map_eq_geoNum p n V hV hpV hdim a,
    ← Bridge.intNum_map_eq_geoNum p n _ hV' hpV' hdim' a]
  have e1 : V.map (substR ℤ B) =
      V.map (substR ℤ B : MRingOver ℤ (dualBlocks T) →+* MRingOver ℤ (dualBlocks T₂)) := rfl
  have e2 : (V.map (MvPolynomial.map (Int.castRingHom (ZMod p)))).map (substR (ZMod p) B) =
      (V.map (MvPolynomial.map (Int.castRingHom (ZMod p)))).map
        (substR (ZMod p) B : MRingOver (ZMod p) (dualBlocks T) →+* MRingOver (ZMod p) (dualBlocks T₂)) := rfl
  have hred : (V.comap (substR ℤ A)).map (MvPolynomial.map (Int.castRingHom (ZMod p))) =
      (V.map (MvPolynomial.map (Int.castRingHom (ZMod p)))).comap (substR (ZMod p) A) := by
    rw [comap_substR ℤ hAB hBA, comap_substR (ZMod p) hAB hBA, e1, e2, Ideal.map_map, Ideal.map_map]
    congr 1
    exact RingHom.ext fun f => red_substR p B f
  unfold NumbersDVR.intNum
  rw [hred, hilbFn_comap (ZMod p) hAB hBA]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial GenericFibreModelTransport

theorem GenFibreModelTransport.proof : GenFibreModelTransport.Statement := by
  intro K _ ι _ K' _ ι' _ v P' G Ω _ z hz Φ₀ _ _ hΦ₀ τ w q
  let φ : MRing ι' →+* G.Φ' := (aeval G.x').toRingHom
  let ψ : MRing ι' →+* Ω := eval₂Hom (Int.castRingHom Ω) z
  have : P'.IsPrime := hz ▸ RingHom.ker_isPrime ψ
  have hφ : ∀ a ∈ P', φ a = 0 := fun a ha => RingHom.mem_ker.1 (G.genericFibre_ker_target.symm ▸ ha)
  have hψ : ∀ a ∈ P', ψ a = 0 := fun a ha => RingHom.mem_ker.1 (hz.symm ▸ ha)
  let α : FractionRing (MRing ι' ⧸ P') →+* G.Φ' :=
    IsFractionRing.lift (quotient_lift_injective φ P' G.genericFibre_ker_target hφ)
  let β : FractionRing (MRing ι' ⧸ P') →+* Ω := IsFractionRing.lift (quotient_lift_injective ψ P' hz hψ)
  let ξ : (Σ k', ι' k') → FractionRing (MRing ι' ⧸ P') := fun p =>
    algebraMap _ _ (Ideal.Quotient.mk P' (X p))
  have hα : α ∘ ξ = G.x' := funext fun p => by simp [α, ξ, φ]
  have hβ : β ∘ ξ = z := funext fun p => by simp [β, ξ, ψ]
  let k := Subfield.closure (Set.range (ξ ∘ v))
  have h₁ : (algebraMap G.Φ G.Φ').fieldRange = k.map α := by
    rw [RingHom.map_field_closure, ← Set.range_comp, ← Function.comp_assoc, hα]
    refine le_antisymm ?_ (Subfield.closure_le.2 ?_)
    · rintro _ ⟨c, rfl⟩
      obtain ⟨f, g, -, rfl⟩ := G.gen c
      have key : ∀ f : MRing ι, algebraMap G.Φ G.Φ' (aeval G.x f) ∈ Subfield.closure (Set.range (G.x' ∘ v)) := by
        intro f
        rw [aeval_def, eval₂_comp_left]
        convert eval₂_mem_closure _ (G.x' ∘ v) f using 2
        exact funext fun p => (G.compat p).symm
      rw [map_div₀]
      exact div_mem (key f) (key g)
    · rintro _ ⟨p, rfl⟩
      exact ⟨G.x p, (G.compat p).symm⟩
  have h₂ : (algebraMap Φ₀ Ω).fieldRange = k.map β := by
    rw [hΦ₀, RingHom.map_field_closure, ← Set.range_comp, ← Function.comp_assoc, hβ]
  obtain ⟨e₁, he₁⟩ := subfield_equiv k α (algebraMap G.Φ G.Φ') h₁
  obtain ⟨e₂, he₂⟩ := subfield_equiv k β (algebraMap Φ₀ Ω) h₂
  let s : Set (FractionRing (MRing ι' ⧸ P')) := Set.range fun t => ξ (w t) / ξ q
  have hs : ∀ (F : Type) [Field F] (γ : FractionRing (MRing ι' ⧸ P') →+* F) (y : (Σ k', ι' k') → F),
      γ ∘ ξ = y → γ '' s = Set.range fun t => y (w t) / y q := by
    rintro F _ γ y rfl
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun t => map_div₀ γ _ _)
  obtain ⟨f₁, t₁⟩ := adjoin_transport e₁ α (RingHom.ext he₁) s (ξ q)
  obtain ⟨f₂, t₂⟩ := adjoin_transport e₂ β (RingHom.ext he₂) s (ξ q)
  rw [hs _ α _ hα] at f₁ t₁
  rw [show α (ξ q) = G.x' q from congrFun hα q] at t₁
  rw [hs _ β _ hβ] at f₂ t₂
  rw [show β (ξ q) = z q from congrFun hβ q] at t₂
  refine ⟨?_, f₁.symm.trans f₂, t₁.symm.trans t₂⟩
  rw [← congrFun hα q, ← congrFun hβ q]
  exact (map_eq_zero α).trans (map_eq_zero β).symm

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField Matrix
open scoped ComplexOrder

namespace DualMetricEnergyAlt

theorem log_det_re_sub {m : Type} [Fintype m] [DecidableEq m] {H A : Matrix m m ℂ} (hH : H.PosDef)
    (hA : Function.Bijective A.mulVec) :
    Real.log (Aᴴ * H * A).det.re - Real.log (Aᴴ * A).det.re = Real.log H.det.re := by
  have hd : A.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det A).mp (Matrix.mulVec_injective_iff_isUnit.mp hA.1)).ne_zero
  obtain ⟨hre, him⟩ := Complex.lt_def.mp hH.det_pos
  simp only [Complex.zero_re, Complex.zero_im] at hre him
  have hHd : H.det = (H.det.re : ℂ) := Complex.ext (by simp) (by simp [← him])
  have hn : 0 < Complex.normSq A.det := Complex.normSq_pos.mpr hd
  have e1 : (Aᴴ * H * A).det.re = Complex.normSq A.det * H.det.re := by
    rw [det_mul, det_mul, det_conjTranspose, hHd, mul_right_comm, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.ofReal_re]
  have e2 : (Aᴴ * A).det.re = Complex.normSq A.det := by
    rw [det_mul, det_conjTranspose, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  rw [e1, e2, Real.log_mul hn.ne' hre.ne']
  ring

end DualMetricEnergyAlt

theorem DualMetricEnergy.proof (hD : DualEnergyCharts.Statement) (hC : ChartEnergy.Statement)
    (hG : GrassGeomDegChart.Statement) (hM : ChartMassInvariant.Statement) :
    DualMetricEnergy.Statement := by
  intro K _ _ i F T _ _ b hb hi
  obtain ⟨A, hA, hE⟩ := hD K i F T b hb hi
  obtain ⟨B, hB, hG'⟩ := hG (i - 1)
  have e1 : 1 * 1 * (i - 1) = i - 1 := by simp
  rw [e1, hG', hM _ _ (Matrix.PosDef.conjTranspose_mul_self B hB.1),
    Finset.sum_congr rfl fun k _ => hE k, Finset.sum_comm]
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  have hterm : ∀ σ : K →+* ℂ,
      ∑ k ∈ Finset.range (n + 1), chartMixedEnergy ((A σ)ᴴ * F.metric σ * A σ) ((A σ)ᴴ * A σ) k =
        1 / 2 * Real.log (F.metric σ).det.re *
          chartMass (1 : Matrix (Fin (n + 1 - 1 + 1)) (Fin (n + 1 - 1 + 1)) ℂ) := by
    intro σ
    have h := hC (n + 1 - 1) _ _ ((F.posDef σ).conjTranspose_mul_mul_same (hA σ).1)
      (Matrix.PosDef.conjTranspose_mul_self (A σ) (hA σ).1)
    have hl := DualMetricEnergyAlt.log_det_re_sub (m := Fin (n + 1)) (F.posDef σ) (hA σ)
    rw [hl] at h
    exact h
  rw [Finset.sum_congr rfl fun σ _ => hterm σ, ← Finset.sum_mul, ← Finset.mul_sum]

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1 NumberField MvPolynomial

namespace StandardDualFibreRatios

theorem nonempty_of_basis {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i} {T : Type} [Fintype T]
    (b : Module.Basis T ℤ (dualLattice F)) (hi : 1 ≤ i) : Nonempty T := by
  by_contra hT
  rw [not_nonempty_iff] at hT
  have h := DualArithmeticVariety.span_basis (K := K) b
  rw [Set.range_eq_empty, Submodule.span_empty] at h
  have h1 : (Pi.single (⟨0, hi⟩ : Fin i) 1 : Fin i → K) ∈ (⊥ : Submodule K (Fin i → K)) := h ▸ Submodule.mem_top
  rw [Submodule.mem_bot] at h1
  have h2 := congrFun h1 ⟨0, hi⟩
  simp at h2

end StandardDualFibreRatios


open StandardDualFibreRatios in
theorem DualStdFibreRatios.proof (hTr : GenFibreModelTransport.Statement) (hMod : DualStdGraphModel.Statement)
    (hRk : DualStdModelRank.Statement) (hTc : DualStdModelTransc.Statement) : DualStdFibreRatios.Statement := by
  intro K _ _ i T _ _ b G hi
  obtain ⟨c⟩ := nonempty_of_basis b hi
  let Φ₀ : Subfield (dualStdModelField K i) :=
    Subfield.closure (Set.range (dualStdModelPt b ∘ inrV (ι := dualBlocks T) (ι₂ := PBlk i)))
  have hΦ₀ : (algebraMap Φ₀ (dualStdModelField K i)).fieldRange = Φ₀ := Subfield.fieldRange_subtype _
  obtain ⟨h0, hrk, htr⟩ := hTr Unit (PBlk i) (Unit ⊕ Unit) (Sum.elim (dualBlocks T) (PBlk i))
    (inrV (ι := dualBlocks T) (ι₂ := PBlk i))
    (graphIdeal (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))) G (dualStdModelField K i)
    (dualStdModelPt b) (hMod K i T b) Φ₀ hΦ₀ T
    (fun t => (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k))
    (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k)
  obtain ⟨hz, hrk₀⟩ := hRk K i T b Φ₀ hΦ₀ hi c
  refine ⟨c, fun h => hz (h0.mp h), ?_, ?_⟩
  · exact hrk.trans hrk₀
  · exact htr.mpr (hTc K i T b Φ₀ hΦ₀ hi c)

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField

noncomputable section

theorem DualTopSimpleSub.proof (hBasis : DualTopBasisChange.Statement)
    (hStep : DualTopSimpleStacked.Statement) (hDeg : DualStackedDegree.Statement) :
    DualTopSimpleSub.Statement := by
  intro K _ _ i F F' T T' _ _ _ _ b hb b' hb' II hi hII hlt hcov
  have hle := hlt.le
  have hcard : Fintype.card T = Fintype.card T' := by
    rw [DualTopStackedExistence.card_eq_of_bijective b hb, DualTopStackedExistence.card_eq_of_bijective b' hb']
  obtain ⟨b₁, b₁', a, hab⟩ := DualTopStackedExistence.exists_stacked hle b b' hcard
  have hb₁ := DualEmbBijective.proof K i F T' b₁
  have hb₁' := DualEmbBijective.proof K i F' T' b₁'

  have h1 : II Unit (dualBlocks T') (dualIdeal b') i (fun _ => dualLine F'.withStdMetric b' hb') =
      II Unit (dualBlocks T') (dualIdeal b₁') i (fun _ => dualLine F'.withStdMetric b₁' hb₁') :=
    hBasis K i F'.withStdMetric T' T' b₁' hb₁' b' hb' II hi hII
  have h2 : II Unit (dualBlocks T') (dualIdeal b₁) i (fun _ => dualLine F.withStdMetric b₁ hb₁) =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) :=
    hBasis K i F.withStdMetric T T' b hb b₁ hb₁ II hi hII

  have h3 := hStep K i F F' T' b₁ hb₁ b₁' hb₁' a II hi hII hlt hcov hab
  have h4 := hDeg K i F F' T' b₁ b₁' a hle hab
  rw [h1, h3, h2, h4]

end

end GroundTheory.Heights₂.Heights
end
