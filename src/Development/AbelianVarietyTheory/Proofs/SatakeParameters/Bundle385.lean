module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle198
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle353
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle022
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle273
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle247
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle023
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionExistence.LeOneIffOfMulEqOne
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle399
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle128
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitLocPlace

open GlobalTheory.FinPl GlobalTheory.FinPl.SplitPoint GlobalTheory.IdemModTwo GlobalTheory.SplitChart GlobalTheory.LocMod.SplitCompl Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

theorem conjPl_ne {D : D7} (s : SplitPlace D.host.E) : Formalism.DivisionValues.conjPl s.w ≠ s.w := by
  intro h
  have hm : ∀ x : 𝓞 D.host.E, x ∈ (Formalism.DivisionValues.conjPl s.w).asIdeal ↔
      IsCMField.ringOfIntegersComplexConj D.host.E x ∈ s.w.asIdeal := by
    intro x
    show x ∈ Ideal.map (Formalism.DivisionValues.cO D.host.E) s.w.asIdeal ↔ _
    have e0 : (Formalism.DivisionValues.cO D.host.E).symm x = IsCMField.ringOfIntegersComplexConj D.host.E x := RingOfIntegers.ext rfl
    rw [Ideal.mem_map_of_equiv]
    refine ⟨fun ⟨y, hy, hxy⟩ => ?_, fun hx => ⟨_, hx, ?_⟩⟩
    · rw [← e0, ← hxy, RingEquiv.symm_apply_apply]; exact hy
    · rw [← e0, RingEquiv.apply_symm_apply]
  have hw : (GlobalTheory.SplitConjPlace.conjSP s).w = s.w := by
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    rw [GlobalTheory.SplitConjPlace.mem_conj_w, ← hm, h]
  have hv : ∀ x : D.host.E, Valued.v ((s.i.comp (IsCMField.complexConj D.host.E).toAlgHom).toRingHom x) =
      s.w.valuation D.host.E x := by
    intro x
    have h1 := PI.CompAtExist.muV_eq (GlobalTheory.SplitConjPlace.conjSP s) x
    rw [hw] at h1
    exact h1
  obtain ⟨φ, hφc, hφ, -⟩ := GlobalTheory.DenseCompl.exists_extension s.w s.v _ hv
  obtain ⟨c, hc, -, hci⟩ := GlobalTheory.SplitCompl.exists_ringEquiv D.host.E s
  have hg : ∀ y, φ (c y) = y := by
    intro y
    refine (HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield D.host.E) s.v).induction_on
      (p := fun y => φ (c y) = y) y (isClosed_eq (hφc.comp hc) continuous_id) fun a => ?_
    have e1 := s.i.commutes a
    rw [← e1, hci, hφ]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_algHom]
    rw [AlgEquiv.commutes]
  apply IsCMField.complexConj_ne_one D.host.E
  refine AlgEquiv.ext fun x => s.i.toRingHom.injective ?_
  have h2 := hg (s.i x)
  rw [hci, hφ] at h2
  exact h2

theorem exists_transport {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2)
    (v1 : HeightOneSpectrum (𝓞 F1)) (w : HeightOneSpectrum (𝓞 F2))
    (hv : ∀ a : F1, v1.valuation F1 a = w.valuation F2 ⟨a, h.le a.2⟩) :
    ∃ κ : v1.adicCompletion F1 →+* w.adicCompletion F2, Continuous κ ∧
      (∀ a : F1, κ (algebraMap F1 _ a) = algebraMap F2 (w.adicCompletion F2) ⟨a, h.le a.2⟩) ∧
      ∀ z : FiniteAdeleRing (𝓞 F1) F1, ∃ z' : FiniteAdeleRing (𝓞 F2) F2,
        Formalism.IndefR.principalLevelFrame.tensCastR h (z ⊗ₜ[F1] (1 : E)) = (1 : E) ⊗ₜ[F2] z' ∧ κ (z v1) = z' w := by
  subst h
  have hvw : v1 = w := by
    refine HeightOneSpectrum.ext (Ideal.ext fun a => ?_)
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F1), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F1),
      hv]
  subst hvw
  exact ⟨RingHom.id _, continuous_id, fun a => rfl, fun z => ⟨z, rfl, rfl⟩⟩

theorem tensCastR_one_tmul {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2) (x : E) :
    Formalism.IndefR.principalLevelFrame.tensCastR h ((1 : FiniteAdeleRing (𝓞 F1) F1) ⊗ₜ[F1] x) = x ⊗ₜ[F2] (1 : FiniteAdeleRing (𝓞 F2) F2) := by
  subst h
  rfl



theorem exists_place : ∀ (D : D7) (s : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E),
    ∃ (p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E))
      (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E),
      Formalism.L2.JoinChr.IsPlIdem D p.e s.w ∧ Continuous c ∧
      (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) ∧
      ∀ a : Formalism.L2.Theta.AE D, p.π a = c (s.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a))) := by
  intro D s hF
  obtain ⟨e, he⟩ := GlobalTheory.Hk3.SplitMatch.exists_isIdemAt (conjPl_ne s)
  obtain ⟨-, -, v, ε, hε, hs⟩ := he.1
  have hsa : SplitAt D v e := splitAt_of he.1 hε hs
  have hP := splitPrime_emb hsa s.w he
  have hf : ∀ x : D.host.E, Valued.v ((emb hsa).toRingHom x) = s.w.valuation D.host.E x := by
    intro x
    rw [← hP]
    exact GlobalTheory.AdelicU.valued_apply_eq_valuation (emb hsa) x
  obtain ⟨φ, hφc, hφ, -⟩ := GlobalTheory.DenseCompl.exists_extension s.w v _ hf
  let g : D.host.F →+* s.w.adicCompletion D.host.E :=
    (algebraMap D.host.E (s.w.adicCompletion D.host.E)).comp (algebraMap D.host.F D.host.E)
  have hg : ∀ a, Valued.v (g a) = v.valuation D.host.F a := by
    intro a
    simp only [g, RingHom.comp_apply]
    rw [GlobalTheory.Idele.valued_algebraMap, ← hf, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
      GlobalTheory.Idele.valued_algebraMap]
  obtain ⟨ψ, hψc, hψ, -⟩ := GlobalTheory.DenseCompl.exists_extension v s.w g hg
  have hcomp : ∀ y, φ (ψ y) = y := by
    intro y
    refine (HeightOneSpectrum.denseRange_algebraMap D.host.F v).induction_on
      (p := fun y => φ (ψ y) = y) y (isClosed_eq (hφc.comp hψc) continuous_id) fun a => ?_
    rw [hψ]
    simp only [g, RingHom.comp_apply]
    rw [hφ]
    exact (emb hsa).commutes a
  let e0 := RingEquiv.ofBijective φ ⟨φ.injective, fun y => ⟨ψ y, hcomp y⟩⟩
  have he0 : ∀ y, e0.symm y = ψ y := fun y => e0.injective (by rw [e0.apply_symm_apply]; exact (hcomp y).symm)
  have hΦc : Continuous e0.symm := hψc.congr fun y => (he0 y).symm
  have hΦc' : Continuous e0 := hφc
  have hΦ : ∀ x : D.host.E, e0.symm (emb hsa x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x := by
    intro x
    have h1 := e0.symm_apply_apply (algebraMap D.host.E (s.w.adicCompletion D.host.E) x)
    exact (congrArg e0.symm (hφ x)).symm.trans h1
  obtain ⟨c, hc, -, hci⟩ := GlobalTheory.SplitCompl.exists_ringEquiv D.host.E s
  have hvv : ∀ a : D.host.F, v.valuation D.host.F a =
      s.v.valuation (maximalRealSubfield D.host.E) ⟨a, hF.le a.2⟩ := by
    intro a
    have h1 := hf (algebraMap D.host.F D.host.E a)
    have h2 := PI.CompAtExist.muV_eq s (algebraMap (maximalRealSubfield D.host.E) D.host.E ⟨a, hF.le a.2⟩)
    rw [← GlobalTheory.Idele.valued_algebraMap, ← GlobalTheory.Idele.valued_algebraMap, ← (emb hsa).commutes, ← s.i.commutes]
    exact h1.trans h2.symm
  obtain ⟨κ, hκc, hκa, hκz⟩ := exists_transport hF v s.v hvv
  have hΦκ : ∀ y, e0.symm y = c (κ y) := by
    intro y
    refine (HeightOneSpectrum.denseRange_algebraMap D.host.F v).induction_on
      (p := fun y => e0.symm y = c (κ y)) y (isClosed_eq hΦc (hc.comp hκc)) fun a => ?_
    have h1 : algebraMap D.host.F (v.adicCompletion D.host.F) a = emb hsa (algebraMap D.host.F D.host.E a) :=
      ((emb hsa).commutes a).symm
    have h2 : algebraMap (maximalRealSubfield D.host.E) (s.v.adicCompletion (maximalRealSubfield D.host.E))
        ⟨a, hF.le a.2⟩ = s.i (algebraMap (maximalRealSubfield D.host.E) D.host.E ⟨a, hF.le a.2⟩) :=
      (s.i.commutes _).symm
    rw [hκa]
    rw [h2]
    rw [hci]
    rw [h1]
    rw [hΦ]
  let p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E) :=
    { e := e
      split := he.1
      π := e0.symm.toRingHom.comp (comp hsa)
      ι := (sec D v e).comp e0.toRingHom.toAddMonoidHom
      π_ι := fun x => by
        show e0.symm (comp hsa (sec D v e (e0 x))) = x
        rw [comp_sec, RingEquiv.symm_apply_apply]
      ι_π := fun a => by
        show sec D v e (e0 (e0.symm (comp hsa a))) = e * a
        rw [RingEquiv.apply_symm_apply, sec_comp]
      cont_π := hΦc.comp (continuous_comp hsa)
      cont_ι := continuous_sec.comp hΦc' }
  refine ⟨p, c, ⟨he.1.1, ⟨v, ε, hε, Or.inl ⟨he.1.2.1, hs⟩⟩, he.2⟩, hc, hci, fun a => ?_⟩
  show e0.symm (comp hsa a) = _
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul y x =>
    have hyx : y ⊗ₜ[D.host.F] x = algebraMap (AF D.host.F) (AE D) y * incA D x := by
      show _ = (y ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hyx, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul]
    congr 1
    · rw [comp_algebraMap, hΦκ]
      obtain ⟨z', hz1, hz2⟩ := hκz y.2
      have e1 : Formalism.L2.Theta.finPart D (algebraMap (AF D.host.F) (AE D) y) = y.2 ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
      rw [e1]
      show _ = c (s.proj (Formalism.IndefR.principalLevelFrame.tensCastR hF (y.2 ⊗ₜ[D.host.F] (1 : D.host.E))))
      rw [hz1]
      show c (κ (y.2 v)) = c (s.i 1 * z' s.v)
      rw [map_one, one_mul, hz2]
    · show e0.symm (emb hsa x) = _
      rw [hΦ]
      have e1 : Formalism.L2.Theta.finPart D (incA D x) = (1 : Af D.host.F) ⊗ₜ[D.host.F] x := rfl
      rw [e1]
      show _ = c (s.proj (Formalism.IndefR.principalLevelFrame.tensCastR hF ((1 : Af D.host.F) ⊗ₜ[D.host.F] x)))
      rw [tensCastR_one_tmul]
      show _ = c (s.i x * ReciprocityTheory.Aut.evalAt D.host.E s.v 1)
      rw [map_one, mul_one, hci]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

end GlobalTheory.SplitLocPlace
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

namespace GlobalTheory.PlaceSupp

theorem finPart_surjective (D : D7) : Function.Surjective (Formalism.L2.Theta.finPart D) := by
  intro y
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a x =>
    exact ⟨((0, a) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ⊗ₜ[D.host.F] x, rfl⟩
  | add y z hy hz =>
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨b, rfl⟩ := hz
    exact ⟨a + b, (Formalism.L2.Theta.finPart D).map_add a b⟩

theorem comp_idem : ∀ (D : D7) (sp : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E)
    (p : GlobalTheory.LocMod.Place D (sp.w.adicCompletion D.host.E))
    (c : sp.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* sp.w.adicCompletion D.host.E),
    (∀ a : Formalism.L2.Theta.AE D, p.π a = c (sp.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a)))) →
    sp.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D p.e)) = 1 ∧
      ∀ x y, sp.proj (GlobalTheory.NJoin.tensCast hF x) = sp.proj (GlobalTheory.NJoin.tensCast hF y) →
        Formalism.L2.Theta.finPart D p.e * x = Formalism.L2.Theta.finPart D p.e * y := by
  intro D sp hF p c hπ
  have hι1 : p.ι 1 = p.e := by
    have := p.ι_π 1
    rwa [map_one, mul_one] at this
  have hπe : p.π p.e = 1 := by rw [← hι1, p.π_ι]
  refine ⟨?_, ?_⟩
  · apply c.injective
    rw [← hπ, hπe, map_one]
  · intro x y hxy
    obtain ⟨a, rfl⟩ := finPart_surjective D x
    obtain ⟨b, rfl⟩ := finPart_surjective D y
    have hab : p.π a = p.π b := by rw [hπ, hπ, hxy]
    have key : p.e * a = p.e * b := by rw [← p.ι_π, ← p.ι_π, hab]
    rw [← map_mul, ← map_mul, key]

end GlobalTheory.PlaceSupp
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.PlaceSupp

theorem tensCast_tmul_one {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2)
    (v : HeightOneSpectrum (𝓞 F1)) (α : FiniteAdeleRing (𝓞 F1) F1) (h1 : α v = 1) (h0 : ∀ v', v' ≠ v → α v' = 0) :
    ∃ (w : HeightOneSpectrum (𝓞 F2)) (α' : FiniteAdeleRing (𝓞 F2) F2),
      GlobalTheory.NJoin.tensCast h (α ⊗ₜ[F1] (1 : E)) = (1 : E) ⊗ₜ[F2] α' ∧ α' w = 1 ∧ ∀ v', v' ≠ w → α' v' = 0 := by
  subst h
  exact ⟨v, α, rfl, h1, h0⟩


open Classical in
theorem equivFinsuppOfBasisRight_rTensor {K M N N' ι : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [AddCommGroup N'] [Module K N']
    (b : Module.Basis ι K M) (f : N →ₗ[K] N') (x : N ⊗[K] M) (i : ι) :
    TensorProduct.equivFinsuppOfBasisRight b (LinearMap.rTensor M f x) i =
      f (TensorProduct.equivFinsuppOfBasisRight b x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => simp [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem rTensor_eq_zero {K M N P Q ι : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [AddCommGroup P] [Module K P] [AddCommGroup Q] [Module K Q]
    (b : Module.Basis ι K M) (f : N →ₗ[K] P) (g : N →ₗ[K] Q) (hfg : ∀ n, f n = 0 → g n = 0 → n = 0)
    (x : N ⊗[K] M) (h1 : LinearMap.rTensor M f x = 0) (h2 : LinearMap.rTensor M g x = 0) : x = 0 := by
  classical
  let e := TensorProduct.equivFinsuppOfBasisRight (M := N) b
  have hc : ∀ i, e x i = 0 := by
    intro i
    apply hfg
    · have := equivFinsuppOfBasisRight_rTensor b f x i
      rw [h1, map_zero, Finsupp.zero_apply] at this
      exact this.symm
    · have := equivFinsuppOfBasisRight_rTensor b g x i
      rw [h2, map_zero, Finsupp.zero_apply] at this
      exact this.symm
  have : e x = 0 := Finsupp.ext hc
  simpa using congrArg e.symm this

theorem AE_eq_zero (D : D7) (x : Formalism.L2.Theta.AE D) (h1 : Formalism.L2.Theta.infPart D x = 0)
    (h2 : Formalism.L2.Theta.finPart D x = 0) : x = 0 := by
  classical
  let b := Module.finBasis D.host.F D.host.E
  refine rTensor_eq_zero b (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA D.host.F).toLinearMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F).toLinearMap
    (fun n hf hs => Prod.ext hf hs) x ?_ ?_
  · rw [← h1]; clear h1 h2
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => rfl
    | add x y hx hy => rw [LinearMap.map_add (f := _), RingHom.map_add (f := _), hx, hy]
  · rw [← h2]; clear h1 h2
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => rfl
    | add x y hx hy => rw [LinearMap.map_add (f := _), RingHom.map_add (f := _), hx, hy]



theorem idem_mul_eq_self : ∀ (D : D7) (s : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E) (p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E)) (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E), (∀ a : Formalism.L2.Theta.AE D, p.π a = c (s.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a)))) → ∀ a : Formalism.L2.Theta.AE D, Formalism.L2.Theta.infPart D a = 0 → (∀ v' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)), v' ≠ s.v → ReciprocityTheory.Aut.compAt D.host.E v' (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a)) = 0) → (p.e + Formalism.L2.Theta.cA D p.e) * a = a := by
  intro D s hF p c hπ a ha0 haf
  obtain ⟨he2, hec, v, ε, ⟨α, rfl, hα1, hα0⟩, hsum⟩ := p.split
  rw [hsum]
  have hι1 : p.ι 1 = p.e := by
    have := p.ι_π 1
    rwa [map_one, mul_one] at this
  have hπe : p.π p.e = 1 := by rw [← hι1, p.π_ι]
  have hee : p.e * algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) (Formalism.L2.Theta.AE D) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 α) = p.e := by
    rw [← hsum, mul_add, he2, hec, add_zero]
  have hfin : Formalism.L2.Theta.finPart D (algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) (Formalism.L2.Theta.AE D)
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 α)) = α ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  obtain ⟨w, α', hT, hw1, hw0⟩ := tensCast_tmul_one hF v α hα1 hα0
  have hws : w = s.v := by
    by_contra hne
    have h0 : α' s.v = 0 := hw0 s.v (Ne.symm hne)
    have hz : p.π (algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) (Formalism.L2.Theta.AE D) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 α)) = 0 := by
      rw [hπ, hfin, hT]
      have : s.proj ((1 : D.host.E) ⊗ₜ α') = 0 := by
        rw [SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
        exact h0
      rw [this, map_zero]
    have := congrArg p.π hee
    rw [map_mul, hz, mul_zero, hπe] at this
    exact zero_ne_one this
  subst hws
  set x := algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) (Formalism.L2.Theta.AE D) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 α) with hx
  suffices hb : x * a - a = 0 from sub_eq_zero.mp hb
  apply AE_eq_zero D
  · rw [RingHom.map_sub, RingHom.map_mul, ha0, mul_zero, sub_zero]
  · have key : GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D (x * a - a)) = 0 := by
      apply GlobalTheory.AL_eq_zero_of_compAt
      intro v''
      rw [(Formalism.L2.Theta.finPart D).map_sub, (Formalism.L2.Theta.finPart D).map_mul, (GlobalTheory.NJoin.tensCast hF).map_sub,
        (GlobalTheory.NJoin.tensCast hF).map_mul, (compAt D.host.E v'').map_sub, (compAt D.host.E v'').map_mul, hfin, hT]
      by_cases hv : v'' = s.v
      · subst hv
        have : compAt D.host.E s.v ((1 : D.host.E) ⊗ₜ α') = 1 := by
          rw [compAt, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
          change (1 : D.host.E) ⊗ₜ (α' s.v) = 1
          rw [hw1]
          rfl
        rw [this, one_mul, sub_self]
      · rw [haf v'' hv, mul_zero, sub_zero]
    exact (GlobalTheory.NJoin.tensCast hF).map_eq_zero_iff.mp key

end GlobalTheory.PlaceSupp
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

namespace GlobalTheory.SplitFrameLattice



theorem glint_mul_frame_basis : ∀ {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D}
    (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V V.rank) (sp : SplitPlace D.host.E)
    (β β' : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)),
    β * β' = 1 → β' * β = 1 →
    (∀ κ, Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (Ps.ψ κ) =
      β * ((κ.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)).map (GlobalTheory.NJoin.tensCast hF).symm) * β') →
    (∀ κ, κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank ↔ Ps.ψ κ ∈ Formalism.L2.Theta.KsphC V ∅) →
    ∀ (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)
      (sec : sp.v.adicCompletion (maximalRealSubfield D.host.E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)
      (B : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)),
    (∀ t, sp.proj (GlobalTheory.NJoin.tensCast hF (sec t)) = t) →
    (∀ t ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E), sec t ∈ Formalism.L2.Theta.intAE D) →
    (∀ x ∈ Formalism.L2.Theta.intAE D,
      sp.proj (GlobalTheory.NJoin.tensCast hF x) ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) →
    sp.proj (GlobalTheory.NJoin.tensCast hF ε) = 1 →
    (∀ z, Formalism.IndefR.Mult.IntVec z → (fun a => ε * B.mulVec z a) ∈ Formalism.L2.NTheta.LamHat V) →
    (∀ y ∈ Formalism.L2.NTheta.LamHat V, ∃ z, Formalism.IndefR.Mult.IntVec z ∧ (fun a => ε * y a) = fun a => ε * B.mulVec z a) →
    ∀ g ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v),
    ∀ z : Fin V.rank → sp.v.adicCompletion (maximalRealSubfield D.host.E),
      (∀ i, z i ∈ Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v) →
      ∃ z' : Fin V.rank → sp.v.adicCompletion (maximalRealSubfield D.host.E),
        (∀ i, z' i ∈ Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v) ∧
        (g : Matrix (Fin V.rank) (Fin V.rank) _).mulVec
            ((β'.map (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x)) *
              B.map (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x))).mulVec z) =
          (β'.map (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x)) *
              B.map (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x))).mulVec z' := by
  intro D hF V Ps sp β β' hββ' hβ'β hfr hK ε sec B hsec hsecI hint hε b1 b2 g hg z hz
  let φ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E →+*
      sp.v.adicCompletion (maximalRealSubfield D.host.E) :=
    sp.proj.comp (GlobalTheory.NJoin.tensCast hF).toRingHom
  have hfun : (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x)) = ⇑φ := rfl
  have hφε : φ ε = 1 := hε
  rw [hfun]
  obtain ⟨emb, htriv, hloc⟩ := GlobalTheory.SplitEmb.exists_hom_trivOutside_loc D.host.E V.rank sp
  have hκ : emb g ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank :=
    GlobalTheory.SplitHeckeComm.mem_Umax_of_loc sp (emb g) (htriv g) (by rw [hloc]; exact hg)
  have hKs := (hK (emb g)).1 hκ
  have hz0 : Formalism.IndefR.Mult.IntVec (sec ∘ z) := fun i => hsecI _ (hz i)
  have hy := b1 _ hz0
  have hy' := (hKs.2.1 _).1 hy
  obtain ⟨z'', hz'', e⟩ := b2 _ hy'
  refine ⟨φ ∘ z'', fun i => hint _ (hz'' i), ?_⟩
  have mv : ∀ (M : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) x,
      φ ∘ (M.mulVec x) = (M.map φ).mulVec (φ ∘ x) := fun M x => funext fun i => RingHom.map_mulVec φ M x i
  have hε' : ∀ w : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E,
      φ ∘ (fun a => ε * w a) = φ ∘ w := fun w => funext fun a => by
    simp only [Function.comp_apply, map_mul, hφε, one_mul]
  have hg' : (((emb g).1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)).map
      (GlobalTheory.NJoin.tensCast hF).symm).map φ = (g : Matrix (Fin V.rank) (Fin V.rank) _) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply]
    show sp.proj (GlobalTheory.NJoin.tensCast hF ((GlobalTheory.NJoin.tensCast hF).symm _)) = _
    rw [RingEquiv.apply_symm_apply]
    conv_rhs => rw [← hloc g]
    rfl
  have hM : (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (Ps.ψ (emb g))).map φ =
      β.map φ * (g : Matrix (Fin V.rank) (Fin V.rank) _) * β'.map φ := by
    rw [hfr (emb g), Matrix.map_mul, Matrix.map_mul, hg']
  have hzφ : φ ∘ (sec ∘ z) = z := funext fun i => hsec _
  have hβ : β'.map φ * β.map φ = 1 := by
    rw [← Matrix.map_mul, hβ'β, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have E := congrArg (fun w => φ ∘ w) e
  rw [hε', hε', mv, mv, hε', mv, hzφ, hM] at E
  have E2 := congrArg (fun w => (β'.map φ).mulVec w) E
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hβ, Matrix.one_mul] at E2
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc]
  exact E2

end GlobalTheory.SplitFrameLattice
end
