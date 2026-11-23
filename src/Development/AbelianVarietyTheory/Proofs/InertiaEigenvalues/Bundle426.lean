module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import GroundTheory.LocalFields.PadicLogSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle367
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle407
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstHalfLocalCohomologyVanishingOfLocalDualityT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle374
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle319
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle380
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle346
public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle394
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle397
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStableComplActK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle396
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle395
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle408
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
public import Formalism.DoubleCosetMeasures.Statement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFundamentalDomainIUnion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle409
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.ConjugateSelfDual.Bundle001
import GroundTheory.AutomorphicForms.GL2.FiniteIdeleDecomp
public import GroundTheory.AutomorphicForms.GL2.Bundle003
import GroundTheory.GlobalFields.HerbrandQuotients.RationalForm
public import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal
public import GroundTheory.LocalFields.Bundle008
public import GroundTheory.LocalFields.Bundle010
public import GroundTheory.LocalFields.Bundle011
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
open GroundTheory.Global (HeckeCharacter localAdelicChar)
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DelEps.GaussBridge

open GroundTheory.LocalField (valBall unitFiltrationUnits addCharConductor quasiCharConductor
  IsUnramifiedChar unifUnit unitsModRep unitsModFiltration unitsModCoset gaussSum)

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem continuous_of_isSmoothChar {χ : Fˣ →* ℂˣ} (hχ : IsSmoothChar χ) : Continuous χ := by
  refine continuous_def.2 fun U _ => isOpen_iff_forall_mem_open.2 fun x hx => ?_
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (χ.ker : Set Fˣ), fun y hy => ?_,
    hχ.preimage (continuous_const_mul _), by simp⟩
  have h : χ (x⁻¹ * y) = 1 := hy
  rw [map_mul, map_inv, inv_mul_eq_one] at h
  show χ y ∈ U
  rw [← h]
  exact hx

variable {χ : Fˣ →* ℂˣ} {ψ : AddChar F Circle}

end GlobalTheory.DelEps.GaussBridge

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.DualSub

section Cup

variable {Γ A M M' : Type} [Group Γ] [TopologicalSpace Γ] [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup M']
  [Module A M'] [TopologicalSpace M] [DiscreteTopology M] [TopologicalSpace M'] [DiscreteTopology M'] {n : ℕ}
  (χ : Γ → ZMod n) (π : Representation A Γ M) (π' : Representation A Γ M') (P : M →+ M' →+ ZMod n)


omit [TopologicalSpace M] [DiscreteTopology M] in
theorem cupB_left (hP : ∀ g x y, P (π g x) (π' g y) = χ g * P x y) (x x' : Γ → M) (y : Γ → M') (w : M)
    (hy : Continuous y) (hy' : ∀ g h, y (g * h) = y g + π' g (y h)) (hx : ∀ g, x' g = x g + (π g w - w))
    (h : CupB χ (fun g m => π' g m) P x y) : CupB χ (fun g m => π' g m) P x' y := by
  obtain ⟨F, hF, h⟩ := h
  refine ⟨F + fun g => P w (y g), hF.add (((IsLocallyConstant.iff_continuous y).2 hy).comp fun m => P w m), fun g k => ?_⟩
  have h1 := h g k
  simp only [hx, map_add (f := _), map_sub, AddMonoidHom.add_apply, AddMonoidHom.sub_apply, Pi.add_apply, hy', hP] at h1 ⊢
  linear_combination h1

theorem cupB_right (hP : ∀ g x y, P (π g x) (π' g y) = χ g * P x y) (x : Γ → M) (y y' : Γ → M') (m : M')
    (hx : Continuous x) (hx' : ∀ g h, x (g * h) = x g + π g (x h)) (hm : Continuous fun g => π' g m)
    (hy : ∀ g, y' g = y g - (π' g m - m))
    (h : CupB χ (fun g m => π' g m) P x y) : CupB χ (fun g m => π' g m) P x y' := by
  obtain ⟨F, hF, h⟩ := h
  refine ⟨F + fun g => P (x g) (π' g m), hF.add (((IsLocallyConstant.iff_continuous _).2 (hx.prodMk hm)).comp
    fun p : M × M' => P p.1 p.2), fun g k => ?_⟩
  have h1 := h g k
  have h2 := hP g (x k) (π' k m)
  simp only [hy, map_add (f := _), map_sub, AddMonoidHom.add_apply, Pi.add_apply, hx', map_mul, Module.End.mul_apply] at h1 ⊢
  linear_combination h1 + h2

end Cup

theorem exists_compLeft {A Y Y' : Type} [CommRing A] [AddCommGroup Y] [Module A Y] [AddCommGroup Y'] [Module A Y'] {r : ℕ}
    (e : Y →ₗ[A] Y') (m : Fin r → Y') (h : ∀ a, m a ∈ LinearMap.range e) : ∃ m', e.compLeft (Fin r) m' = m := by
  choose m' hm' using h
  exact ⟨m', funext hm'⟩

theorem dualSel_of_smul_cob : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → NoInvDual i κ ρ → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (Y' : Type) [AddCommGroup Y'] [Module A Y'] [TopologicalSpace Y'] [DiscreteTopology Y'] (Y₂ : Type) [AddCommGroup Y₂] [Module A Y₂] [TopologicalSpace Y₂] [DiscreteTopology Y₂] (Y₂' : Type) [AddCommGroup Y₂'] [Module A Y₂'] [TopologicalSpace Y₂'] [DiscreteTopology Y₂'] (β : Y →+ Y' →+ ZMod (X.l i ^ (nu X i + 1))) (β₂ : Y₂ →+ Y₂' →+ ZMod (X.l i ^ (nu X i + 1))) (f : Y →ₗ[A] Y₂) (e : Y₂' →ₗ[A] Y') (c t : A), Bal A β → Bal A β₂ → Function.Surjective f → Function.Injective e → (∀ y', (c * t) • y' = 0 → y' ∈ LinearMap.range e) → (∀ y y', β₂ (f y) y' = β y (e y')) → (∀ v, v ∈ Spl i ∨ v ∈ Q → ∀ m, (∀ g ∈ DecV N v, repOn ρ κ⁻¹ Y' g m = m) → t • m = 0) → ∀ y : Z1 (repOn ρ κ⁻¹ Y'), DualSel bkP i s κ ρ β Q y → Cob (repOn ρ κ⁻¹ Y') (fun g => c • y.1 g) → ∃ y₂ : Z1 (repOn ρ κ⁻¹ Y₂'), DualSel bkP i s κ ρ β₂ Q y₂ ∧ Cob (repOn ρ κ⁻¹ Y') (fun g a => y.1 g a - e (y₂.1 g a)) := by
  intro D N X bkP i s A _ _ _ _ κ Q ρ hS hK hD hNI Y _ _ _ _ Y' _ _ _ _ Y₂ _ _ _ _ Y₂' _ _ _ _ β β₂ f e c t hβ hβ₂ hf he hct
    hfe ht y hy hc
  obtain ⟨hcY, hcY', hP, hU⟩ := GlobalTheory.T.pairing_equivariant_alt D N X bkP i s A κ Q ρ hS hK hD Y Y' β hβ
  obtain ⟨-, -, hP₂, -⟩ := GlobalTheory.T.pairing_equivariant_alt D N X bkP i s A κ Q ρ hS hK hD Y₂ Y₂' β₂ hβ₂
  obtain ⟨m, hm⟩ := hc
  have hE : Function.Injective (e.compLeft (Fin D.R.r)) := fun a b hab => funext fun j => he (congrFun hab j)

  have hq := hNI (Y' ⧸ LinearMap.range (c • (LinearMap.id : Y' →ₗ[A] Y')))
    ((Submodule.mkQ _).compLeft (Fin D.R.r) m) fun g => by
      rw [← repOn_map, ← sub_eq_zero, ← map_sub, ← hm g]
      funext a
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨y.1 g a, rfl⟩
  obtain ⟨m', hm'⟩ := exists_compLeft (c • (LinearMap.id : Y' →ₗ[A] Y')) m fun a =>
    (Submodule.Quotient.mk_eq_zero _).1 (congrFun hq a)
  have hm'' : m = c • m' := hm'.symm
  have hcm : Continuous fun g => repOn ρ κ⁻¹ Y' g m' := hcY'.comp (continuous_id.prodMk continuous_const)
  have hkill : ∀ g, c • (y.1 g - (repOn ρ κ⁻¹ Y' g m' - m')) = 0 := fun g => by
    have := hm g
    simp only at this
    rw [smul_sub, this, hm'', map_smul, smul_sub, sub_self]
  have hex : ∀ g, ∃ z, e.compLeft (Fin D.R.r) z = y.1 g - (repOn ρ κ⁻¹ Y' g m' - m') := fun g =>
    exists_compLeft e _ fun a => hct _ (by
      rw [mul_comm, mul_smul]
      have := congrFun (hkill g) a
      rw [Pi.smul_apply] at this
      rw [this, Pi.zero_apply, smul_zero])
  choose z hz using hex
  have hzc : Continuous z := by
    have h1 : IsLocallyConstant fun g => y.1 g - (repOn ρ κ⁻¹ Y' g m' - m') :=
      (IsLocallyConstant.iff_continuous _).2 (y.2.1.sub (hcm.sub continuous_const))
    exact (IsLocallyConstant.iff_continuous _).1 (IsLocallyConstant.desc z (e.compLeft (Fin D.R.r))
      (by rw [show (e.compLeft (Fin D.R.r)) ∘ z = _ from funext hz]; exact h1) hE)
  have hzz : ∀ g h, z (g * h) = z g + repOn ρ κ⁻¹ Y₂' g (z h) := fun g h => hE (by
    rw [map_add (f := _), repOn_map, hz, hz, hz, y.2.2, map_mul, Module.End.mul_apply, map_sub, map_sub]
    abel)
  refine ⟨⟨z, hzc, hzz⟩, ⟨fun v h1 h2 h3 τ hτ => hE ?_, fun v hv => ?_, fun v hv x₂ hx₂ => ?_⟩, m', fun g => ?_⟩
  · show e.compLeft _ (z τ) = _
    rw [hz, hy.1 v h1 h2 h3 τ hτ, (hU v h1 h2 h3 _ (N.plOm.2 v) τ hτ).2]
    simp
  · obtain ⟨m₀, hm₀⟩ := hy.2.1 v hv
    have h1 := ht v hv (c • (m₀ - m')) fun g hg => by
      have := hkill g
      rw [hm₀ g hg] at this
      rw [map_smul, map_sub, ← sub_eq_zero, ← smul_sub, ← this]
      congr 1
      abel
    obtain ⟨m₂, hm₂⟩ := exists_compLeft e (m₀ - m') fun a => hct _ (by
      rw [mul_comm, mul_smul]
      exact congrFun h1 a)
    refine ⟨m₂, fun g hg => hE ?_⟩
    show e.compLeft _ (z g) = _
    rw [hz, map_sub, repOn_map, hm₂, hm₀ g hg, map_sub]
    abel
  · obtain ⟨xc, hxc, hxe⟩ := GlobalTheory.T.bkOn_le_map_h1MapSubgroup_of_surjective D N X bkP i s A κ Q hS hK Y Y₂ f hf v hx₂
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ xc
    have h1 := hy.2.2 v hv x hxc
    have h2 := cupB_right _ ((repOn (Tgl i s) κ Y).comp (DecV N v).subtype) ((repOn ρ κ⁻¹ Y').comp (DecV N v).subtype)
      (vecPair D.R.r β) (fun g => hP g.1) x.1 _ (fun g => e.compLeft _ (z g.1)) m' x.2.1 x.2.2
      (hcm.comp continuous_subtype_val) (fun g => hz g.1) h1
    have h3 : (Submodule.Quotient.mk x₂ : H1 _) = Submodule.Quotient.mk (cocycles1MapOfEquivariant _ _ (f.compLeft (Fin D.R.r))
        continuous_of_discreteTopology (fun g m => repOn_map (Tgl i s) κ f g.1 m) x) := hxe.symm
    obtain ⟨w, hw⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.eq _).1 h3)
    refine cupB_left _ ((repOn (Tgl i s) κ Y₂).comp (DecV N v).subtype) ((repOn ρ κ⁻¹ Y₂').comp (DecV N v).subtype)
      (vecPair D.R.r β₂) (fun g => hP₂ g.1) (fun g => f.compLeft _ (x.1 g)) x₂.1 (fun g => z g.1) w
      (hzc.comp continuous_subtype_val) (fun g h => hzz g.1 h.1) (fun g => ?_) ?_
    · rw [← hw g]
      exact (add_sub_cancel _ _).symm
    · obtain ⟨F, hF, h2⟩ := h2
      refine ⟨F, hF, fun g h => ?_⟩
      rw [← h2 g h]
      show vecPair _ β₂ _ (repOn ρ κ⁻¹ Y₂' g.1 (z h.1)) = vecPair _ β _ (repOn ρ κ⁻¹ Y' g.1 (e.compLeft _ (z h.1)))
      rw [← repOn_map, vecPair_apply, vecPair_apply]
      exact Finset.sum_congr rfl fun a _ => hfe _ _
  · have : (fun a => y.1 g a - e (z g a)) = y.1 g - e.compLeft _ (z g) := rfl
    show (fun a => y.1 g a - e (z g a)) = _
    rw [this, hz, sub_sub_cancel]

end GlobalTheory.DualSub
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.StageFirst

open IsLocalRing GlobalTheory.ScalarFrob GlobalTheory.PrimeToInertia GlobalTheory.AntiRamConj
open scoped Pointwise

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (i : X.Tw) (s : X.Sig i)

theorem isLocalHom_of_kills {A : Type} [CommRing A] [Nontrivial A] [Algebra (X.O0 i) A] (h : Kills i A) :
    IsLocalHom (algebraMap (X.O0 i) A) := by
  refine ⟨fun x hx => ?_⟩
  by_contra hn
  have hm : x ∈ maximalIdeal (X.O0 i) := hn
  have : CharZero (FractionRing (X.O0 i)) := (X.emb0 i).charZero_iff (X.emb0 i).injective |>.1 inferInstance
  have : CharZero (X.O0 i) := (algebraMap (X.O0 i) (FractionRing (X.O0 i))).charZero
  have hl : ((X.l i : ℕ) : X.O0 i) ^ nu X i ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : (X.l i).Prime).ne_zero)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.O0 i)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl hϖ
  have h1 : ϖ ∣ x := by
    rwa [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  have h2 : ((X.l i : ℕ) : X.O0 i) ^ nu X i ∣ x ^ n := by
    rw [hu, Units.mul_left_dvd]
    exact pow_dvd_pow_of_dvd h1 n
  have h3 := h (x ^ n * x) (Ideal.mul_mem_mul (Ideal.mem_span_singleton.2 h2) hm)
  rw [← pow_succ, map_pow] at h3
  exact (hx.pow _).ne_zero h3

theorem frob_scalar (bkP : BKPh X) (h : GalHyp bkP i s) {z : GE N} {L : Subgroup (GE N)} (hz : IsTameInertiaElementAtTwistPrime X i z)
    (hL : Small i s L z) {P : PlE D.host}
    (hA : ∀ v, Over P v → v ∉ X.S0 i ∧ (normV v : ResidueField (X.O0 i)) = 1)
    (hS : ∀ σ : GE N, IsFrob (N.plOm.1 P) (normV P) σ → ∃ g : GE N, g * σ * g⁻¹ * z⁻¹ ∈ L)
    {v : PlE D.host} (hv : Over P v) {σ : GE N}
    (hσ : IsFrob (N.plOm.1 v) (normV v) σ) : ∃ c : ResidueField (X.O0 i), c ≠ 0 ∧ c ≠ 1 ∧ resT i s σ = c • 1 := by
  obtain ⟨e, he, -, hu, -⟩ := GlobalTheory.T.tameInertiaElement_acts_by_scalar D N X bkP i s z h.1 hz
  have c0 : residue (X.O0 i) e ≠ 0 := (residue_ne_zero_iff_isUnit _).2 e.isUnit
  have c1 : residue (X.O0 i) e ≠ 1 := by
    rw [← residue_ne_zero_iff_isUnit, map_sub, map_one, sub_ne_zero] at hu
    exact hu
  have key : ∀ τ : GE N, IsFrob (N.plOm.1 P) (normV P) τ → resT i s τ = residue (X.O0 i) e • 1 := by
    intro τ hτ
    obtain ⟨g, hg⟩ := hS τ hτ
    have e1 : resT i s (g * τ * g⁻¹ * z⁻¹ * z) = residue (X.O0 i) e • 1 := by
      rw [map_mul, resT_apply, (hL.2.2.2.2 _ hg).1, one_mul, resT_apply, he]
      ext a b
      by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    have e2 := conj_scalar _ e1 g⁻¹
    rwa [show g⁻¹ * (g * τ * g⁻¹ * z⁻¹ * z) * g⁻¹⁻¹ = τ by group] at e2
  have hp := hA v hv
  have hp0 := hA _ (over_refl P)
  rcases hv with rfl | hv
  · exact ⟨_, c0, c1, key σ hσ⟩
  · have ε := eps_frob i hp.1 hp.2 hσ
    obtain ⟨τ, g, hτ, rfl⟩ := exists_frob_of_conj X hv hσ
    have ε0 := eps_frob i hp0.1 hp0.2 hτ
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm] at ε
    refine ⟨_, inv_ne_zero c0, inv_ne_one.2 c1, conj_scalar _ (scalar_of_dual i s ε c0 ?_) g⟩
    obtain ⟨A, hA⟩ := h.2.2.1
    have e3 : ((((eps0 X i τ : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s τ).map (residue (X.O0 i)) =
        residue (X.O0 i) e • 1 := by
      rw [← key τ hτ, resT_apply]
      ext a b
      simp [ε0]
    rw [hA τ _ (cConj_apply X τ), Matrix.map_mul, Matrix.map_mul, e3, mul_smul_comm, mul_one, smul_mul_assoc,
      ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

theorem firstHalf : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → 0 < nu X i → ∀ (M R n : ℕ) (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (A₀ : Finset (PlE D.host)) (L : Subgroup (GE N)) (z : GE N) (P : Fin R ⊕ Fin n → PlE D.host), nu X i + 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A₀ L z P → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Kills i A → (∀ g, ∃ k : ℕ, κ g ^ (X.l i ^ k) = 1) → (ρ = Tgl i s ∨ IsDual i s ρ) → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (b : Fin R), (∀ v, Over (P (.inl b)) v → ∀ m, (∀ g ∈ DecV N v, repOn ρ κ Y g m = m) → m = 0) ∧ (AntiHom X.cc κ → (∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 (P (.inl b))), κ τ = 1) → ∀ f : Z1 (repOn ρ κ Y), ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 (P (.inl b))), f.1 τ = 0 ∧ f.1 (cConj X τ) = 0) := by
  intro hT D N X bkP i s h hl2 M R n d A₀ L z P hM hz hL hP A _ _ _ _ κ ρ hK hκ hρ Y _ _ _ _ b
  have := isLocalHom_of_kills i hK
  have hA : ∀ v, Over (P (.inl b)) v → v ∉ X.S0 i ∧ (normV v : ResidueField (X.O0 i)) = 1 := fun v hv =>
    ⟨(hP.1.1 _ v hv).2.2.2.1, natCast_eq_one i (show 1 ≤ M by omega) (hP.1.1 _ v hv).2.2.2.2.2⟩
  have fix0 : ∀ v, Over (P (.inl b)) v → ∀ σ : GE N, IsFrob (N.plOm.1 v) (normV v) σ →
      ∀ m, repOn ρ κ Y σ m = m → m = 0 := by
    intro v hv σ hσ m hm
    obtain ⟨c, c0, c1, hc⟩ := frob_scalar i s bkP h hz hL.1 hA (hP.2.1 b).2 hv hσ
    obtain ⟨c', c1', hc'⟩ : ∃ c' : ResidueField (X.O0 i), c' ≠ 1 ∧
        ((ρ σ : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (residue _) = c' • 1 := by
      rcases hρ with rfl | hρ
      · exact ⟨c, c1, by rw [Tgl_coe, ← resT_apply, hc]⟩
      · exact ⟨c⁻¹, inv_ne_one.2 c1, by rw [hρ, dual_of_scalar i s (eps_frob i (hA v hv).1 (hA v hv).2 hσ) c0 hc]⟩
    exact eq_zero_of_scalar Fact.out (l_mem i) ρ κ (hκ σ) c1' hc' (q := 1) Nat.cast_one m (by rw [one_smul]; exact hm)
  have fix : ∀ v, Over (P (.inl b)) v → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ σ : GE N, IsFrob B (normV v) σ →
      ∀ m, repOn ρ κ Y σ m = m → m = 0 := by
    intro v hv B hB σ hσ m hm
    obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := D.host.E) hB (N.plOm.2 v)
    have h3 := isFrob_smul hσ g
    rw [hg] at h3
    have h4 := fix0 v hv _ h3 (repOn ρ κ Y g m) (by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply, hm])
    have h5 := congrArg (repOn ρ κ Y g⁻¹) h4
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero] at h5
  have van : ∀ v, Over (P (.inl b)) v → ∀ B : ValuationSubring N.Om, IsPlaceOver B v →
      (∀ τ ∈ Ine (F := D.host.E) B, κ τ = 1) → ∀ f : Z1 (repOn ρ κ Y), ∀ τ ∈ Ine (F := D.host.E) B, f.1 τ = 0 := by
    intro v hv B hB hκB f
    obtain ⟨γ, -, hγ⟩ := GlobalTheory.TameRead.exists_gen_read hT.1 D.host.E N.Om (X.l i) B v hB
      (fun h => (hA v hv).1 (X.twistExcludedPlaces_contains_residueChar i h))
    have h1 : ∀ m : Fin D.R.r → Y, (X.l i ^ (nu X i + 1)) • m = 0 := fun m => by
      have := hK ((X.l i : X.O0 i) ^ nu X i * (X.l i : X.O0 i))
        (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (l_mem i))
      rw [map_mul, map_pow, map_natCast] at this
      rw [← Nat.cast_smul_eq_nsmul A, Nat.cast_pow, pow_succ, this, zero_smul]
    have h2 : normV v ≡ 1 [MOD X.l i ^ (nu X i + 1)] := by
      have hq := (hP.1.1 _ v hv).2.2.2.2.2
      have hd : X.l i ^ (nu X i + 1) ∣ 2 * X.l i ^ M := Dvd.dvd.mul_left (pow_dvd_pow _ hM) 2
      have h6 : normV v ≡ 1 [MOD 2 * X.l i ^ M] := by
        rw [← hq]
        exact (Nat.mod_modEq _ _).symm
      exact h6.of_dvd hd
    have h3 : ∀ σ ∈ Ine (F := D.host.E) B, ∀ m, repOn ρ κ Y σ m = m := by
      intro σ hσ m
      have hσL := (hP.2.1 b).1 v hv B hB hσ
      rcases hρ with rfl | hρ
      · rw [(GlobalTheory.T.twisted_representation_kills_small_subgroup D N X i s hl2 M L z hM hL A κ _ hK (isDual_dualRep i s) Y σ hσL).1, hκB σ hσ, Units.val_one,
          one_smul]
      · rw [(GlobalTheory.T.twisted_representation_kills_small_subgroup D N X i s hl2 M L z hM hL A κ _ hK hρ Y σ hσL).2.1, hκB σ hσ, Units.val_one, one_smul]
    obtain ⟨h4, h5⟩ := hγ A _ (repOn ρ κ Y) (nu X i + 1) h1 h2 h3 f
    obtain ⟨φ, hφ⟩ := exists_isFrob (F := D.host.E) hB
    exact h4 (fix v hv B hB φ hφ _ (h5 φ hφ))
  refine ⟨fun v hv m hm => ?_, fun hanti hκI f τ hτ => ⟨van _ (over_refl _) _ (N.plOm.2 _) hκI f τ hτ, ?_⟩⟩
  · obtain ⟨σ, hσ⟩ := exists_isFrob (N.plOm.2 v)
    exact fix0 v hv σ hσ m (hm σ hσ.1)
  · obtain ⟨v, hv⟩ := exists_isConjPl (P (.inl b))
    refine van v (Or.inr hv) _ (isPlaceOver_moveVal_cc X hv (N.plOm.2 _)) (fun σ hσ => ?_) f _ (cConj_mem_ine X hτ)
    have h1 := cConj_mem_ine X hσ
    have e : moveVal X.cc (moveVal X.cc (N.plOm.1 (P (.inl b)))) = N.plOm.1 (P (.inl b)) := by
      ext y
      rw [mem_moveVal, mem_moveVal, cc_symm, cc_symm, cc_cc]
    rw [e] at h1
    have h2 := hκI _ h1
    rwa [antiHom_cConj X hanti, inv_eq_one] at h2

end GlobalTheory.StageFirst
end
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Pass.LocDual.OneX

theorem span_stable (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)) {a : ℕ} (x : Fin a → ↥Xs) (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y) (γ : GE D.nd) :
    ∀ v ∈ Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i)),
      actK i r Xs x γ v ∈ Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i)) := by
  let f : (Fin a → Fin D.R.nV → KK D.nd i) →ₗ[KK D.nd i] (Fin a → Fin D.R.nV → KK D.nd i) :=
    LinearMap.pi fun b => Matrix.toLin' (mapM (toK D.nd i) (rTwO D.nd i r (x b)) γ) ∘ₗ LinearMap.proj b
  have hf : ∀ v, f v = actK i r Xs x γ v := fun v => rfl
  intro v hv
  rw [← hf]
  have h : Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i)) ≤
      (Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i))).comap f := by
    refine Submodule.span_le.2 fun y hy => ?_
    rw [SetLike.mem_coe, Submodule.mem_comap, hf]
    exact Submodule.subset_span (hst γ y hy)
  exact h hv

end GlobalTheory.Pass.LocDual.OneX


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem GlobalTheory.Pass.LocDual.OneX.main : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))),
    GoodR D.nd i r → ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (n : ℕ), PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
    ∀ (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hSub : SubTw i r Xs M)
      (F : Finset (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)),
      (F : Set (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)) ⊆ cutCoc i w hw r Xs M →
      ∃ X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw),
        IsSummandTw i w hw r Xs X ∧
        Submodule.span (Br.OLL D.nbr i w hw) (F : Set (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)) ≤
          BlochKatoDuality.spanPush (Br.PD D.loc D.nbr i w hw) X (locU i w hw M hSub.1) (Br.locLat D.nbr i w hw M) := by
  intro D hF i r hr Xs w hw n hP k M hSub F hFs
  obtain ⟨a, x, E, Y, hYfg, hst, hE, hc⟩ := GlobalTheory.Pass.LocDual.OneX.cutCoc_finset_common D i w hw r Xs M F hFs
  have hC := GlobalTheory.BlockSum.exists_stable_compl_actK D i r Xs hr x (Submodule.span (KK D.nd i) (Y : Set _))
    (fun γ => GlobalTheory.Pass.LocDual.OneX.span_stable D i r Xs x Y hst γ)
  refine ⟨GlobalTheory.Pass.LocDual.OneX.XG i w hw r Xs hr x Y hst,
    GlobalTheory.Pass.LocDual.OneX.isSummandTw_XG D i w hw r Xs hr x Y hst hC, ?_⟩
  obtain ⟨LY, hLY⟩ := GlobalTheory.T.localIntegerSpanOfImage_is_stable_lattice D i w hw r Xs hr x Y hst hYfg
  have hy := GlobalTheory.Pass.LocDual.OneX.yfun_Z1fT D hF i r hr Xs w hw n hP x Y hst E hE LY hLY
  apply Submodule.span_le.2
  intro c hcF
  obtain ⟨φ, hφ, rfl⟩ := hc c hcF
  obtain ⟨φ', hG, hpush⟩ := GlobalTheory.Pass.LocDual.OneX.PushEq.main D i w hw r Xs hr x Y hst E hE M LY hLY φ hφ
  unfold BlochKatoDuality.spanPush
  exact Submodule.subset_span (R := Br.OLL D.nbr i w hw) (M := Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T) ⟨LY, φ', hG, ⟨_, hy.1⟩, hy, (hpush ⟨_, hy.1⟩ rfl).symm⟩
end

section

noncomputable section

open MeasureTheory GlobalTheory.CuspRep
open scoped ENNReal Matrix

namespace GlobalTheory.ThetaUnfold

variable {E : Type} [Field E] [NumberField E] {a : ℕ}



open NumberField Matrix GlobalTheory.MirTower in
theorem mem_mirU_pred {K : Type} [Field K] {a : ℕ} (ha : 0 < a) (γ : GL (Fin a) K) :
    γ ∈ mirU K a (a - 1) ↔ ∀ j, γ.val ⟨a - 1, Nat.sub_lt ha Nat.one_pos⟩ j =
      if j = ⟨a - 1, Nat.sub_lt ha Nat.one_pos⟩ then 1 else 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, a = n + 1 := ⟨a - 1, by omega⟩
  exact mem_mirU_last


open NumberField Matrix GlobalTheory.MirTower in
theorem lintegral_theta_unfold : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ha : 0 < a) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 𝓕P : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (ratMirU E a (a - 1)) 𝓕P μ → ∀ F : GA E a → (Fin a → Ad E) → ℝ≥0∞, (∀ v : Fin a → E, Measurable fun g : GA E a => F g (Matrix.vecMul (fun i => algebraMap E (Ad E) (v i)) g.val)) → (∀ (γ : GL (Fin a) E) g y, F (ratGL E a γ * g) y = F g y) → ∫⁻ g in 𝓕, ∑' ξ : {v : Fin a → E // v ≠ 0}, F g (Matrix.vecMul (fun i => algebraMap E (Ad E) (ξ.1 i)) g.val) ∂μ = ∫⁻ g in 𝓕P, F g (g.val ⟨a - 1, Nat.sub_lt ha Nat.one_pos⟩) ∂μ := by
  intro E _ _ a ha μ _ 𝓕 𝓕P h𝓕 h𝓕P F hm hF
  set l : Fin a := ⟨a - 1, Nat.sub_lt ha Nat.one_pos⟩
  have hv : (Pi.single l 1 : Fin a → E) ≠ 0 := fun h0 => by simpa using congrFun h0 l
  have hP' : ∀ γ : GL (Fin a) E, γ ∈ mirU E a (a - 1) ↔ (Pi.single l 1 : Fin a → E) ᵥ* γ.val = Pi.single l 1 :=
    fun γ => by
      rw [mem_mirU_pred ha, Matrix.single_one_vecMul, funext_iff]
      simp only [Pi.single_apply, Matrix.row]
      rfl
  have he : algebraMap E (Ad E) ∘ (Pi.single l 1 : Fin a → E) = (Pi.single l 1 : Fin a → Ad E) := by
    funext j
    simp only [Function.comp_apply, Pi.single_apply]
    split_ifs <;> simp
  have := lintegral_tsum_vecMul μ hv hP' h𝓕 h𝓕P F hF (hm _).aemeasurable
  simp only [he, Matrix.single_one_vecMul] at this
  exact this

end GlobalTheory.ThetaUnfold
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

theorem _root_.GlobalTheory.T.exists_inv_io_pi_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∃ u ∈ FilB P 0, io AI AI.π₁ * u = 1 := by
  first | exact @GlobalTheory.ExpImage.exists_inv_io_pi | exact GlobalTheory.ExpImage.exists_inv_io_pi | (intros; apply GlobalTheory.ExpImage.exists_inv_io_pi <;> assumption)
end
