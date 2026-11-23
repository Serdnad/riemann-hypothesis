module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseChangeIsomorphicFields
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle020
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle133
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordLattice
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle194
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle198
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle197
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle200
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Filter Topology Matrix GlobalTheory.IsoPull

namespace GlobalTheory.DegOneLift

section Val

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M]

theorem tendsto_pow {v : HeightOneSpectrum (𝓞 K)} (x : v.adicCompletion K) (h : Valued.v x < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 _ hne)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [Valuation.restrict_lt_iff_lt_embedding, map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

theorem lt_one_of_continuous {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (s : v.adicCompletion K →+* w.adicCompletion M) (hs : Continuous s) {z : v.adicCompletion K}
    (hz : Valued.v z < 1) : Valued.v (s z) < 1 := by
  have h1 : Tendsto (fun n : ℕ => s z ^ n) atTop (𝓝 0) := by
    have := (hs.tendsto 0).comp (tendsto_pow z hz)
    simpa [Function.comp_def, map_pow] using this
  have hU : {y : w.adicCompletion M | Valued.v y < 1} ∈ 𝓝 (0 : w.adicCompletion M) :=
    Valued.mem_nhds_zero.2 ⟨1, fun y hy => by simpa using hy⟩
  obtain ⟨N, hN⟩ := (h1.eventually hU).exists
  by_contra hc
  rw [not_lt] at hc
  have hN' : Valued.v (s z ^ N) < 1 := hN
  rw [map_pow] at hN'
  exact absurd hN' (not_lt.2 (one_le_pow₀ hc))

theorem mem_iff_lt_one (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    x ∈ v.asIdeal ↔ Valued.v (algebraMap K (v.adicCompletion K) (x : K)) < 1 := by
  have h : Valued.v (algebraMap K (v.adicCompletion K) (x : K)) = v.valuation K (algebraMap (𝓞 K) K x) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  rw [h, HeightOneSpectrum.valuation_lt_one_iff_mem]

theorem over_of_continuous (e : K ≃+* M) {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (i : v.adicCompletion K →+* w.adicCompletion M) (hi : Continuous i)
    (he : ∀ x : K, i (algebraMap K _ x) = algebraMap M _ (e x)) : Over e v w := by
  have h1 : v.asIdeal ≤ (src e w).asIdeal := by
    intro x hx
    rw [ringEquivPlaceCorrespondence_placeUnder e w x, mem_iff_lt_one]
    rw [mem_iff_lt_one] at hx
    have := lt_one_of_continuous i hi hx
    rw [he] at this
    exact this
  have h2 : v = src e w := HeightOneSpectrum.ext (v.isMaximal.eq_of_le (src e w).isPrime.ne_top h1)
  rw [h2]
  exact ringEquivPlaceCorrespondence_placeUnder e w

theorem normV_eq_absNorm (v : HeightOneSpectrum (𝓞 K)) : normV v = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rfl

theorem two_le_normV (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ normV v := by
  rw [normV_eq_absNorm]
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  omega

end Val

end GlobalTheory.DegOneLift

namespace GlobalTheory.DegOneLift

section Rep

variable {K M : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M]
  {a : ℕ}

theorem pull_pull (e : K ≃+* M) (φ : Sm K a) : pull a e (pull a e.symm φ) = φ :=
  Subtype.ext <| funext fun g => congrArg φ.1 (mapA_symm e g)

theorem pullSub_pullSub (e : K ≃+* M) (π : CuspSub K a) : pullSub e (pullSub e.symm π) = π := by
  refine CuspSub.ext ?_
  change (π.V.map (pull a e.symm).toLinearMap).map (pull a e).toLinearMap = π.V
  rw [← Submodule.map_comp]
  convert Submodule.map_id π.V
  refine LinearMap.ext fun φ => ?_
  exact pull_pull e φ

def SmIrr.comap {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] (σ : SmIrr H)
    (f : G →* H) (hf : Continuous f) (hs : Function.Surjective f) : SmIrr G where
  V := σ.V
  ρ := σ.ρ.comp f
  smooth x := (σ.smooth x).preimage hf
  irred := by
    obtain ⟨h0, h⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 σ.irred
    refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h W fun g x hx => ?_⟩
    obtain ⟨g, rfl⟩ := hs g
    exact hW g x hx

theorem locRep_pullSub (e : K ≃+* M) {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)} (hO : Over e v w)
    (π : CuspSub K a) (g : GL (Fin a) (v.adicCompletion K)) (x : π.V) :
    (pullSub e.symm π).locRep w (GeneralLinearGroup.map (cLoc hO) g) ((pull a e.symm).submoduleMap π.V x) =
      (pull a e.symm).submoduleMap π.V (π.locRep v g x) := by
  apply Subtype.ext
  refine Eq.trans ?_ (pull_act e.symm (.fin (locGL K a v g)) x.1).symm
  change _ = act (.fin (GeneralLinearGroup.map (cFin e) (locGL K a v g))) (pull a e.symm x.1)
  rw [cFin_locGL hO]
  rfl

end Rep

theorem isLift : ∀ (K M : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Algebra K M], Module.finrank K M = 1 → ∀ (a : ℕ) (π : CuspSub K a), ∃ P : CuspSub M a, GlobalTheory.GalCut.IsLift π P := by
  intro K M _ _ _ _ _ _ _ h1 a π
  let e : K ≃+* M := RingEquiv.ofBijective (algebraMap K M) (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h1)
  have he : ∀ x, e x = algebraMap K M x := fun _ => rfl
  refine ⟨pullSub e.symm π, ?_, ?_, ?_⟩
  · intro w f B hf hB
    have hO : Over e.symm w (w.under (𝓞 K)) := fun x => by
      rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap]
      have : algebraMap (𝓞 K) (𝓞 M) (RingOfIntegers.mapRingEquiv e.symm x) = x := by
        apply RingOfIntegers.ext
        change algebraMap K M (e.symm (x : M)) = x
        rw [← he]
        exact e.apply_symm_apply _
      rw [this]
    have hq : normV w = normV (w.under (𝓞 K)) := by
      rw [normV_eq_absNorm, normV_eq_absNorm]
      exact (qV_eq hO).symm
    have h2 := two_le_normV (w.under (𝓞 K))
    have hf1 : f = 1 := Nat.pow_right_injective h2 (by
      change normV (w.under (𝓞 K)) ^ f = normV (w.under (𝓞 K)) ^ 1
      rw [pow_one, ← hf, hq])
    subst hf1
    simp only [pow_one, Multiset.map_id']
    exact hasSat_pullSub e.symm hO hB
  · intro τ
    have hτ : (τ.comp e.toRingHom).comp e.symm.toRingHom = τ := by
      ext x
      simp
    have key : ∀ m, (CG.mk π).HasInfChar (τ.comp (algebraMap K M)) m ↔
        (CG.mk (pullSub e.symm π)).HasInfChar τ m := by
      intro m
      constructor
      · intro h
        exact hasInfChar_pullSub e.symm (π := π) (σ := τ) h
      · intro h
        have h3 : (pullSub e (pullSub e.symm π)).HasInfChar (τ.comp e.toRingHom) m :=
          hasInfChar_pullSub e (σ := τ.comp e.toRingHom) (by rw [hτ]; exact h)
        rw [pullSub_pullSub] at h3
        exact h3
    by_cases h : ∃ m, (CG.mk π).HasInfChar (τ.comp (algebraMap K M)) m
    · obtain ⟨m, hm⟩ := h
      rw [((key m).1 hm).infChar_eq, hm.infChar_eq]
    · have h' : ¬ ∃ m, (CG.mk (pullSub e.symm π)).HasInfChar τ m := fun ⟨m, hm⟩ => h ⟨m, (key m).2 hm⟩
      unfold CG.infChar
      rw [dite_eq_right h, dite_eq_right h']
  · intro v w i hi hie σ σ' hσ hσ'
    have hO : Over e v w := over_of_continuous e i.toRingHom hi fun x => hie x
    have hiL : ∀ y, i y = cLoc hO y := fun y => congrFun
      ((HeightOneSpectrum.denseRange_algebraMap (K := K) v).equalizer hi (continuous_cLoc hO)
        (funext fun x => (hie x).trans (cLoc_algebraMap hO x).symm)) y
    have hsurj : Function.Surjective (GeneralLinearGroup.map (n := Fin a) (cLoc hO)) := fun g =>
      ⟨GeneralLinearGroup.map (locEquiv hO).symm.toRingHom g, Units.ext (Matrix.ext fun _ _ =>
        (locEquiv hO).apply_symm_apply _)⟩
    let σ'' := SmIrr.comap σ' (GeneralLinearGroup.map (n := Fin a) (cLoc hO))
      (continuous_mapGL _ (continuous_cLoc hO)) hsurj
    let T := (pull a e.symm).submoduleMap π.V
    have h'' : π.IsLocComp v σ'' := by
      obtain ⟨f, h0, hf⟩ := hσ'
      refine ⟨T.symm.toLinearMap ∘ₗ f, fun hz => h0 (LinearMap.ext fun x => T.symm.injective ?_), fun g x => ?_⟩
      · exact (LinearMap.congr_fun hz x).trans (map_zero T.symm).symm
      · have e1 := hf (GeneralLinearGroup.map (cLoc hO) g) x
        have e2 : (pullSub e.symm π).locRep w (GeneralLinearGroup.map (cLoc hO) g) (T (T.symm (f x))) =
            T (π.locRep v g (T.symm (f x))) := locRep_pullSub e hO π g (T.symm (f x))
        have e3 : (pullSub e.symm π).locRep w (GeneralLinearGroup.map (cLoc hO) g) (f x) =
            T (π.locRep v g (T.symm (f x))) := by
          refine Eq.trans ?_ e2
          exact congrArg _ (T.apply_symm_apply (f x)).symm
        exact (congrArg T.symm (e1.trans e3)).trans (T.symm_apply_apply _)
    obtain ⟨E⟩ := GlobalTheory.CuspRep.LocUniq.isLocComp_unique π v σ σ'' hσ h''
    refine ⟨E.toLinearEquiv, fun g x => ?_⟩
    have hg : GeneralLinearGroup.map i.toRingHom g = GeneralLinearGroup.map (cLoc hO) g :=
      Units.ext (Matrix.ext fun _ _ => hiL _)
    rw [hg]
    exact LinearMap.congr_fun (E.isIntertwining' g) x

end GlobalTheory.DegOneLift
end
end

section

open Matrix

theorem _root_.GlobalTheory.T.exists_intUnitary_of_gramClass_alt : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n n' : ℕ)
    (JS : GL (Fin n) L) (JT : GL (Fin n') L), Formalism.UG.IsUnramInv ϖ σ q → Odd q →
    JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ x y : Matrix (Fin n') (Fin n) L,
    (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.HoweG.HomA σ JS JT x y → GlobalTheory.Hk3.HoweG.GramEq σ JT x y → GlobalTheory.Hk3.HoweDuality.latIdx y = GlobalTheory.Hk3.HoweDuality.latIdx x →
    ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      ∀ i j, (y - ((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) i j ∈ Formalism.UG.intL L := by
  first | exact @GlobalTheory.Hk3.HoweG.exists_intUnitary_of_gramClass | exact GlobalTheory.Hk3.HoweG.exists_intUnitary_of_gramClass | (intros; apply GlobalTheory.Hk3.HoweG.exists_intUnitary_of_gramClass <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_place_chart_of_splitIdempotent : ∀ {D : D7} (e : AE D), IsSplitIdem D e → ∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), Chart e v π := by
  first | exact @GlobalTheory.SplitChart.exists_chart | exact GlobalTheory.SplitChart.exists_chart | (intros; apply GlobalTheory.SplitChart.exists_chart <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitFrame

open GlobalTheory.IdemModTwo (fj inF inF_finPart inF_tmul)
open GlobalTheory.SplitHeckeLabel (exists_local_lattice smul_mem_latHat mul_mem_intA intA)

theorem exists_gl_of_lattice (O : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] {K : Type} [Field K]
    [Algebra O K] [IsFractionRing O K] {n : ℕ} (Λ : Submodule O (Fin n → K)) (hfg : Λ.FG)
    (hsp : Submodule.span K (Λ : Set (Fin n → K)) = ⊤) :
    ∃ β : GL (Fin n) K, ∀ w, w ∈ Λ ↔ ∀ i, IsInt O (((β⁻¹).1 *ᵥ w) i) := by
  classical
  have : Submodule.IsFullLattice K Λ := { toIsLattice := Submodule.IsLattice.of_fg K hfg, span_eq_top := hsp }
  have := Submodule.IsLattice.finite K Λ
  have := Submodule.IsLattice.free K Λ
  have hr : Module.finrank O Λ = n := by
    rw [((Submodule.IsFullLattice.finrank_eq K Λ).trans (Module.finrank_fintype_fun_eq_card K)), Fintype.card_fin]
  let b : Module.Basis (Fin n) O Λ := Module.finBasisOfFinrankEq O Λ hr
  let c : Module.Basis (Fin n) K (Fin n → K) := b.extendOfIsFullLattice K
  let s := Pi.basisFun K (Fin n)
  refine ⟨⟨s.toMatrix c, c.toMatrix s, Module.Basis.toMatrix_mul_toMatrix_flip _ _,
    Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩, fun w => ?_⟩
  have hw : c.toMatrix s *ᵥ w = c.repr w := by
    exact Module.Basis.toMatrix_mulVec_repr s c w
  change _ ↔ ∀ i, IsInt O ((c.toMatrix s *ᵥ w) i)
  rw [hw]
  have hc : ∀ i, c i = (b i : Fin n → K) := fun i => Module.Basis.extendOfIsFullLattice_apply K b i
  constructor
  · intro h i
    refine ⟨b.repr ⟨w, h⟩ i, ?_⟩
    have h1 : w = ∑ j, algebraMap O K (b.repr ⟨w, h⟩ j) • c j := by
      have := congrArg Subtype.val (b.sum_repr ⟨w, h⟩)
      rw [Submodule.coe_sum] at this
      refine this.symm.trans (Finset.sum_congr rfl fun j _ => ?_)
      rw [hc, algebraMap_smul]
      rfl
    conv_rhs => rw [h1]
    rw [c.repr_sum_self]
  · intro h
    choose o ho using h
    rw [← c.sum_repr w]
    refine Λ.sum_mem fun j _ => ?_
    rw [← ho, algebraMap_smul, hc]
    exact Λ.smul_mem _ (b j).2

variable {D : D7}

theorem finPart_inF (z : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (inF D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [AddMonoidHom.map_zero, RingHom.map_zero]
  | tmul a x => rfl
  | add x y hx hy => rw [AddMonoidHom.map_add (f := _), RingHom.map_add (f := _), hx, hy]

theorem exists_factor {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (h : Chart e v π) : ∃ φ : Af D.host.F ⊗[D.host.F] D.host.E →+* Fv D.host.F v, ∀ z, φ (finPart D z) = π z := by
  have h1 : π (fj D 1) = 1 := (h.2.2.1 _).trans (map_one (evalV D.host.F v))
  refine ⟨(finPart D).liftOfRightInverse (inF D) finPart_inF ⟨π, fun z hz => ?_⟩, fun z =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ z⟩
  rw [RingHom.mem_ker] at hz ⊢
  have h2 := inF_finPart z
  rw [hz, AddMonoidHom.map_zero] at h2
  have h3 := congrArg π h2
  rwa [RingHom.map_zero, RingHom.map_mul, h1, one_mul, eq_comm] at h3

theorem finPart_mul_eq {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (h : Chart e v π) {φ : Af D.host.F ⊗[D.host.F] D.host.E →+* Fv D.host.F v} (hφ : ∀ z, φ (finPart D z) = π z)
    (y : AE D) (z : Af D.host.F ⊗[D.host.F] D.host.E) (hy : π y = φ z) : finPart D (e * y) = finPart D e * z := by
  have h1 : π y = π (inF D z) := by
    rw [← hφ (inF D z), finPart_inF]
    exact hy
  have h2 := (h.2.1 (y - inF D z)).1 (by rw [RingHom.map_sub, h1, sub_self])
  rw [mul_sub, sub_eq_zero] at h2
  rw [h2, RingHom.map_mul, finPart_inF]

theorem exists_frame : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ V : HSp D, ∃ β : GL (Fin V.rank) (Fv D.host.F v), Frame V e π β := by
  intro D e v π he h V
  obtain ⟨φ, hφ⟩ := exists_factor h
  have hei : finPart D e ∈ intA D.host.F D.host.E :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he.1])
  have hπe : π e = 1 := by
    have := (h.2.1 (e - 1)).2 (by rw [mul_sub, he.1, mul_one, sub_self])
    rwa [RingHom.map_sub, RingHom.map_one, sub_eq_zero] at this
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
    V.L0.map (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E))
  have hL : (L : Set (Fin V.rank → D.host.E)) = L0c D V := Set.ext fun y => by
    change _ ↔ ∑ i, y i • V.frame i ∈ V.L0
    rw [← V.frame.equivFun_symm_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      change V.frame.equivFun.symm (V.frame.equivFun x) ∈ V.L0
      rwa [LinearEquiv.symm_apply_apply]
    · exact fun h => ⟨_, h, V.frame.equivFun.apply_symm_apply y⟩
  have hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    classical
    have hs : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      obtain ⟨s, hs⟩ := V.standardTuple_isLattice.fg
      apply eq_top_iff.mpr
      intro y _
      obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s (fun x => V.hT x y)
      have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 :=
        (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
      let P : Submodule (𝓞 D.host.E) V.V := {
        carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * V.hT x y}
        zero_mem' := by refine ⟨0, ?_⟩; simp
        add_mem' := by
          rintro x z ⟨b, hb⟩ ⟨c, hc⟩
          refine ⟨b + c, ?_⟩
          change (b : D.host.E) + c = _
          rw [hb, hc, map_add, LinearMap.add_apply, mul_add]
        smul_mem' := by
          rintro c x ⟨b, hb⟩
          refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
          simp only [map_mul, RingOfIntegers.mapRingHom_apply, hb]
          rw [show c • x = (c : D.host.E) • x from (IsScalarTower.algebraMap_smul D.host.E c x).symm, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
          change star (c : D.host.E) * ((algebraMap (𝓞 D.host.E) D.host.E a) * V.hT x y) = _
          simp only [starRingEnd_apply]
          ring }
      have hsP : (s : Set V.V) ⊆ P := by
        intro x hx
        obtain ⟨b, hb⟩ := ha x hx
        exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
      have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        change (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Formalism.E.hdual V.hT V.L0
        simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap]
        intro x hx
        obtain ⟨b, hb⟩ := (hs ▸ Submodule.span_le.mpr hsP) hx
        change V.hT x ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)
        rw [map_smul, smul_eq_mul, ← hb]
        exact Submodule.algebraMap_mem _
      have hy' := (Submodule.span D.host.E (V.L0 : Set V.V)).smul_mem (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ (Submodule.subset_span hy)
      rwa [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at hy'
    change Submodule.span _ (V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V)) = ⊤
    rw [← Submodule.map_span, hs, Submodule.map_top, LinearEquiv.range]
  obtain ⟨Λ, hfg, hΛ, hmem⟩ := exists_local_lattice (F := D.host.F) L (V.standardTuple_isLattice.fg.map _) hsp v φ
    (fun a => (hφ (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 a))).trans (h.2.2.1 _))
    (fun x hx => by
      rw [← finPart_inF x, hφ, ← isInt_Ov, ← h.2.2.2, RingHom.map_mul, finPart_inF]
      exact mul_mem_intA hei hx)
  obtain ⟨β, hβ⟩ := exists_gl_of_lattice (Ov D v) Λ hfg hΛ
  refine ⟨β, fun y => ?_⟩
  rw [← hβ, hmem, LamHat, ← hL]
  constructor
  · intro hy
    refine ⟨_, hy, funext fun i => ?_⟩
    rw [Function.comp_apply, hφ, RingHom.map_mul, hπe, one_mul]
  · rintro ⟨z, hz, hy⟩
    have : (fun i => finPart D (e * y i)) = finPart D e • z := funext fun i =>
      finPart_mul_eq h hφ (y i) (z i) (congrFun hy i)
    rw [this]
    exact smul_mem_latHat L hei hz

end GlobalTheory.SplitFrame

end
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.Published GlobalTheory.IdemAdj

theorem _root_.GlobalTheory.T.cuspidal_typeClosure_preserved_by_archCompact_intertwiner : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ₀ : Representation ℂ (Kinf E a) W) (U : Submodule ℂ π.V), FiniteDimensional ℂ U → (∀ k, ∀ u ∈ U, cptOn π k u ∈ U) → ∀ f : π.V →ₗ[ℂ] π.V, (∀ k, ∀ u ∈ U, f (cptOn π k u) = cptOn π k (f u)) → ∀ u ∈ U, (∀ g, (fun k : Kinf E a => (cptRep E a k u.1).1 g) ∈ AutFin.coeffSpan ρ₀) → ∀ g, (fun k : Kinf E a => (cptRep E a k (f u).1).1 g) ∈ AutFin.coeffSpan ρ₀ := by
  first | exact @GlobalTheory.IdemAdj.typeClosure_of_intertwine | exact GlobalTheory.IdemAdj.typeClosure_of_intertwine | (intros; apply GlobalTheory.IdemAdj.typeClosure_of_intertwine <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory

theorem galoisRepOfPolarizedCuspidal_iff_pair : GlobalTheory.Published.GelfandKazhdanDual →
    (GlobalTheory.Published.CaraianiLocalGlobalDual → GlobalTheory.Published.CaraianiLocalGlobal) ∧
    (GlobalTheory.Published.GaloisRepOfPolarizedPair → GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) := by
  intro hGK
  refine ⟨fun hC => ?_, fun hP => ?_⟩
  · intro E Ω _ _ _ _ _ _ l _ ι a ha π hcsd hcoh
    have hd : DualIsConj π :=
      (dualIsConjBy_one π).1 (GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose E a π 1 (hGK E a _) ((GlobalTheory.GalOfCusp.isConjDualBy_one π).2 hcsd))
    exact hC E Ω l ι a ha π hd hcoh
  · intro E Ω _ _ _ _ _ _ l _ ι a ha π χ hr hpol
    exact hP E Ω l ι a ha π χ hr
      ⟨hpol.sign, GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose E a π (GlobalTheory.GalOfCusp.compNorm E χ) (hGK E a _) hpol.dual⟩

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_splitPrime_GL_chart_of_unitaryGroup : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P → ∀ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∃ ρ : GA D V →* GL (Fin V.rank) (P.adicCompletion D.host.E), (∀ M : GL (Fin V.rank) (P.adicCompletion D.host.E), ∃ g, Formalism.L2.Theta.SuppAt e V g ∧ ρ g = M) ∧ (∀ k ∈ KsphC V ∅, ρ k ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov D.host.E P)) ∧ ∀ (g : GA D V) (a : Fin V.rank → ℤ), ∀ k₁ ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov D.host.E P), ∀ k₂ ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov D.host.E P), ((ρ g : GL (Fin V.rank) (P.adicCompletion D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion D.host.E)) = (k₁ : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion D.host.E)) * Formalism.UG.diagPow D.host.E P (algebraMap D.host.E (P.adicCompletion D.host.E) (ϖ : D.host.E)) a * (k₂ : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion D.host.E)) → DivAt V e (ϖ : D.host.E) (List.ofFn a) g := by
  first | exact @GlobalTheory.SplitPrimeChart.exists_chart | exact GlobalTheory.SplitPrimeChart.exists_chart | (intros; apply GlobalTheory.SplitPrimeChart.exists_chart <;> assumption)
end
