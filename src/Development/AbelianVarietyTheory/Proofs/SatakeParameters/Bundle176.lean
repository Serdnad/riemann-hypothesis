module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.GlobalTheory.EqGlobOfHat
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
public import Formalism.LocalToGlobal.GlobalTheory.Bundle002
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle170
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle109
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittEmbeddingsCompatible
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.TheoremOfAlternateForm
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle168
public import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.EqOffBound
public import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.Assemble
public import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.SplitElementExistsHolds
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle006
public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle169
public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle018
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.LocalToGlobal.InertKernelTheory.Bundle009
import Formalism.LocalToGlobal.InertKernelTheory.Bundle003
import Formalism.LocalToGlobal.KernelLattices.Bundle001
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.NrmAMemAdForms
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle001
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle017
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.IsComplRatCompl
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

@[expose] public section

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OrthSelfDual

theorem toLE_mem_mvL {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ} (co : GL (Fin N) E)
    (M : Submodule (𝓞 E) (Fin N → E)) (y : Fin N → E) :
    toLE co y ∈ mvL co M ↔ y ∈ M := by
  constructor
  · rintro ⟨x, hx, hxy⟩
    have hxy' : x = y := (toLE co).injective hxy
    rw [hxy'] at hx
    exact hx
  · intro hy
    exact Submodule.mem_map.mpr ⟨y, hy, rfl⟩

theorem isLat_and_dl_eq_of_isSDLat_mvL : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (co : GL (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E)), IsOrthCo (sp.cm.sig : E →+* E) J (toLE co) → IsSDLat E N (mvL co M) → Formalism.L2.GlobalTheoryTheory.Comp.IsLat M ∧ Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J M = M := by
  intro R F E _ _ _ _ _ _ sp N J co M hco hsd
  obtain ⟨hfg, hspan, hdual⟩ := hsd

  have hkey : ∀ x z : Fin N → E, Formalism.BasicNotions.stdH E N (toLE co x) (toLE co z) =
      ∑ a, ∑ b, (sp.cm.sig : E →+* E) (x a) * J a b * z b := fun x z => hco x z
  have hinj : Function.Injective
      (((toLE co : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)).restrictScalars (𝓞 E)) :=
    (toLE co).injective
  refine ⟨⟨?_, ?_⟩, ?_⟩
  ·
    have hfin : Module.Finite (𝓞 E)
        (M.map ((((toLE co : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E))).restrictScalars (𝓞 E))) :=
      Module.Finite.iff_fg.mpr hfg
    exact Module.Finite.equiv (Submodule.equivMapOfInjective _ hinj M).symm
  ·
    have himage : (↑(mvL co M) : Set (Fin N → E)) = (toLE co) '' (↑M : Set (Fin N → E)) := by
      ext x
      simp [mvL]
    rw [himage] at hspan
    apply top_unique
    intro x hx
    apply (Submodule.apply_mem_span_image_iff_mem_span
      (R := E) (R₂ := E)
      (f := ((toLE co : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)))
      (toLE co).injective).mp
    change toLE co x ∈ Submodule.span E ((toLE co) '' (↑M : Set (Fin N → E)))
    rw [hspan]
    trivial
  ·
    ext y
    rw [Formalism.L2.GlobalTheoryTheory.Comp.mem_dl, ← toLE_mem_mvL co M y, hdual (toLE co y)]
    constructor
    · intro h x' hx'
      obtain ⟨x, hx, hxx'⟩ := Submodule.mem_map.mp hx'
      have hx'' : x' = toLE co x := hxx'.symm
      rw [hx'', hkey]
      exact h x hx
    · intro h x hx
      have h1 := h (toLE co x) ((toLE_mem_mvL co M x).mpr hx)
      rw [hkey] at h1
      exact h1

end GlobalTheory.OrthSelfDual

end
end

section

noncomputable section

namespace GlobalTheory.SDCompan

section Gen

open Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.L2.GlobalTheoryTheory.Comp Formalism.L2.KerInert
open scoped TensorProduct

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {N : ℕ}

omit [StarRing E] in
theorem latAd_eq (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E)) :
    Formalism.L2.PairingIndexBounds.F.latAd y Lb = Formalism.UG.CS.globLat y Lb :=
  Submodule.span_eq (Formalism.UG.CS.globLat y Lb)

theorem compan_eq (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (Λ : Submodule (𝓞 E) (Fin N → E)) :
    Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a Λ = Λ ⊔ Ideal.span {a} • dl sp.cm.sig J Λ := rfl

theorem compan_zero (J : Matrix (Fin N) (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E)) :
    Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J 0 Λ = Λ := by
  rw [compan_eq, Ideal.span_singleton_eq_bot.2 rfl, Submodule.bot_smul, sup_bot_eq]

theorem mem_toStd (J : Matrix (Fin N) (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E)) (y : Fin N → E) :
    y ∈ Formalism.L2.PairingIndexBounds.F.toStd (sp.cm.sig : E →+* E) J M ↔
      (Formalism.L2.PairingIndexBounds.F.stdCo (sp.cm.sig : E →+* E) J).symm y ∈ M := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    have : (Formalism.L2.PairingIndexBounds.F.stdCo (sp.cm.sig : E →+* E) J).symm (Formalism.L2.PairingIndexBounds.F.stdCo (sp.cm.sig : E →+* E) J x) = x :=
      LinearEquiv.symm_apply_apply _ x
    simpa using (this ▸ hx)
  · intro h
    exact ⟨_, h, by simp⟩

theorem isSD_toStd (J : Matrix (Fin N) (Fin N) E)
    (hco : ∃ co, Formalism.L2.PairingIndexBounds.F.IsOrthCo (sp.cm.sig : E →+* E) J co)
    {M : Submodule (𝓞 E) (Fin N → E)} (hM : IsLat M) (hsd : dl sp.cm.sig J M = M) :
    IsSDLat E N (Formalism.L2.PairingIndexBounds.F.toStd (sp.cm.sig : E →+* E) J M) := by
  have hc : Formalism.L2.PairingIndexBounds.F.IsOrthCo (sp.cm.sig : E →+* E) J (Formalism.L2.PairingIndexBounds.F.stdCo (sp.cm.sig : E →+* E) J) :=
    Classical.epsilon_spec hco
  set co := Formalism.L2.PairingIndexBounds.F.stdCo (sp.cm.sig : E →+* E) J with hco_def
  have key : ∀ x y, stdH E N (co x) (co y) = hform (sp.cm.sig : E →+* E) J x y := fun x y => hc x y
  refine ⟨(Module.Finite.iff_fg.1 hM.1).map _, ?_, fun y => ?_⟩
  · rw [Formalism.L2.PairingIndexBounds.F.toStd, Submodule.map_coe, LinearMap.coe_restrictScalars, ← hco_def, eq_top_iff]
    rintro v -
    have hv : co.symm v ∈ Submodule.span E (M : Set (Fin N → E)) := by rw [hM.2]; trivial
    have h1 := Submodule.apply_mem_span_image_of_mem_span (co : (Fin N → E) →ₗ[E] (Fin N → E)) hv
    simpa using h1
  · rw [mem_toStd (sp := sp), ← hco_def]
    constructor
    · intro hy x hx
      rw [mem_toStd (sp := sp), ← hco_def] at hx
      have h1 := (mem_dl sp.cm.sig J M (co.symm y)).1 (hsd.symm ▸ hy) (co.symm x) hx
      rw [← key, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
      exact h1
    · intro h
      rw [← hsd, mem_dl]
      intro x hx
      have h1 := h (co x) ((mem_toStd (sp := sp) J M (co x)).2 (by rw [← hco_def, LinearEquiv.symm_apply_apply]; exact hx))
      rw [← LinearEquiv.apply_symm_apply co y, key] at h1
      exact h1

theorem isSD_core (J : Matrix (Fin N) (Fin N) E)
    (hJ : ∀ M : Submodule (𝓞 E) (Fin N → E), IsLat M → IsLat (dl sp.cm.sig J M))
    (hco : ∃ co, Formalism.L2.PairingIndexBounds.F.IsOrthCo (sp.cm.sig : E →+* E) J co)
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hy : y ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F))
    {Lb M0 : Submodule (𝓞 E) (Fin N → E)} (hLb : IsLat Lb) (a : 𝓞 E)
    (hA : Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a Lb = M0) (hM0 : IsLat M0) (hsd : dl sp.cm.sig J M0 = M0) :
    IsSDLat E N (Formalism.L2.PairingIndexBounds.F.toStd (sp.cm.sig : E →+* E) J
      (Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a (Formalism.L2.PairingIndexBounds.F.latAd y Lb))) := by
  have hG : Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a (Formalism.L2.PairingIndexBounds.F.latAd y Lb) = Formalism.UG.CS.globLat y M0 := by
    rw [latAd_eq, ← hA]
    by_cases ha : a = 0
    · subst ha
      rw [compan_zero, compan_zero]
    · rw [compan_eq, compan_eq]
      exact (glob_companion sp.cm.sig J hJ hLb ha y hy).symm
  rw [hG]
  exact isSD_toStd (sp := sp) J hco (isLat_glob hM0 y) (glob_selfdual sp.cm.sig J hJ hM0 hsd y hy)

end Gen

section Main

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isSDLat_latK : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E), (∀ M : Submodule (𝓞 E) (Fin N → E), Formalism.L2.GlobalTheoryTheory.Comp.IsLat M → Formalism.L2.GlobalTheoryTheory.Comp.IsLat (Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J M)) → (∃ co, IsOrthCo (sp.cm.sig : E →+* E) J co) → ∀ y ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F), ∀ (Lb : Submodule (𝓞 E) (Fin N → E)) (a : 𝓞 E), Formalism.L2.GlobalTheoryTheory.Comp.IsLat Lb → Formalism.L2.GlobalTheoryTheory.Comp.IsLat (compan (sp := sp) J a Lb) → Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J (compan (sp := sp) J a Lb) = compan (sp := sp) J a Lb → IsSDLat E N (latK sp J a y Lb) := by
  intro R F E _ _ _ _ _ _ sp N J hJ hco y hy Lb a hLb hM hsd
  exact isSD_core (sp := sp) J hJ hco y hy hLb a rfl hM hsd

end Main

end GlobalTheory.SDCompan
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

theorem parts_of_adjoint_lift : ∀ {X E I : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (Θ : X →ₗ[ℂ] E) (op : I → Module.End ℂ X) (h : I → Module.End ℂ E), ∀ {C : Type} (Ec : C → Submodule ℂ E) (lab : C → I → ℂ), (∀ i u, Θ (op i u) = h i (Θ u)) → (∀ i, Commute (op i) (LinearMap.adjoint (op i))) → (∀ i, Commute (h i) (LinearMap.adjoint (h i))) → Formalism.L2.Col.PairComm op → (⨆ c, Ec c) = ⊤ → (∀ c, ∀ w ∈ Ec c, ∀ i, h i w = lab c i • w) → (∀ c, Ec c ≠ ⊥ → ∃ w ∈ Ec c, LinearMap.adjoint Θ w ≠ 0) → Formalism.L2.Col.PairComm h ∧ ∀ Q : (I → ℂ) → Prop, (∀ c, Ec c ≠ ⊥ → ((Ec c).map (LinearMap.adjoint Θ) ≤ Formalism.L2.Col.eigSum op Q ↔ Q (lab c))) ∧ (⨆ (c : C) (_ : Ec c ≠ ⊥ ∧ (Ec c).map (LinearMap.adjoint Θ) ≤ Formalism.L2.Col.eigSum op Q), Ec c) = Formalism.L2.Col.eigSum h Q := by
  intro X E I _ _ _ _ _ _ Θ op h C Ec lab hint hn hn' hc htop hh hne
  have hcomm : Formalism.L2.Col.PairComm h := by
    intro i j
    refine GlobalTheory.EigTransfer.linearMap_ext_of_iSup_eq_top Ec htop (h i * h j) (h j * h i) fun c w hw => ?_
    simp only [Module.End.mul_apply, hh c w hw, map_smul, smul_smul, mul_comm]
  have hup : ∀ c, (Ec c).map (LinearMap.adjoint Θ) ≤ Formalism.L2.Col.eigAt op (lab c) := by
    rintro c _ ⟨w, hw, rfl⟩
    exact Formalism.L2.Col.mem_eigAt_of_forall_apply fun i =>
      GlobalTheory.T.eigenvector_adjoint_intertwiner_normal_operators Θ op h hint hn hn' i (lab c i) w (hh c w hw i)
  have hiff : ∀ (Q : (I → ℂ) → Prop) c, Ec c ≠ ⊥ →
      ((Ec c).map (LinearMap.adjoint Θ) ≤ Formalism.L2.Col.eigSum op Q ↔ Q (lab c)) := by
    intro Q c hcne
    constructor
    · intro hle
      by_contra hq
      obtain ⟨w, hw, hw0⟩ := hne c hcne
      have hm : LinearMap.adjoint Θ w ∈ (Ec c).map (LinearMap.adjoint Θ) := ⟨w, hw, rfl⟩
      have hd := Formalism.L2.Col.disjoint_eigSum hc (C := fun x => ¬ Q x) (C' := Q) fun x hx => hx
      exact hw0 ((Submodule.disjoint_def.1 hd) _
        (Formalism.L2.Col.eigAt_le_eigSum (C := fun x => ¬ Q x) hq (hup c hm)) (hle hm))
    · intro hq
      exact (hup c).trans (Formalism.L2.Col.eigAt_le_eigSum hq)
  refine ⟨hcomm, fun Q => ⟨fun c hcne => hiff Q c hcne, ?_⟩⟩
  have hle : ∀ P : (I → ℂ) → Prop, (⨆ (c : C) (_ : P (lab c)), Ec c) ≤ Formalism.L2.Col.eigSum h P := fun P =>
    iSup₂_le fun c hq w hw => Formalism.L2.Col.eigAt_le_eigSum hq
      (Formalism.L2.Col.mem_eigAt_of_forall_apply fun i => hh c w hw i)
  have hsup : (⨆ (c : C) (_ : Q (lab c)), Ec c) ⊔ (⨆ (c : C) (_ : ¬ Q (lab c)), Ec c) = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine iSup_le fun c => ?_
    by_cases hq : Q (lab c)
    · exact le_sup_of_le_left (le_iSup₂_of_le (f := fun c (_ : Q (lab c)) => Ec c) c hq le_rfl)
    · exact le_sup_of_le_right (le_iSup₂_of_le (f := fun c (_ : ¬ Q (lab c)) => Ec c) c hq le_rfl)
  have hd : Disjoint (⨆ (c : C) (_ : ¬ Q (lab c)), Ec c) (Formalism.L2.Col.eigSum h Q) :=
    (Formalism.L2.Col.disjoint_eigSum hcomm (C := fun x => ¬ Q x) (C' := Q) fun x hx => hx).mono_left
      (hle fun x => ¬ Q x)
  have hQ : (⨆ (c : C) (_ : Q (lab c)), Ec c) = Formalism.L2.Col.eigSum h Q := by
    have := sup_inf_assoc_of_le (⨆ (c : C) (_ : ¬ Q (lab c)), Ec c) (hle Q)
    rw [hsup, top_inf_eq, hd.eq_bot, sup_bot_eq] at this
    exact this.symm
  rw [← hQ]
  apply le_antisymm
  · refine iSup₂_le fun c hcq => ?_
    exact le_iSup₂_of_le (f := fun c (_ : Q (lab c)) => Ec c) c ((hiff Q c hcq.1).1 hcq.2) le_rfl
  · refine iSup₂_le fun c hq => ?_
    by_cases hb : Ec c = ⊥
    · rw [hb]; exact bot_le
    · exact le_iSup₂_of_le (f := fun c (_ : Ec c ≠ ⊥ ∧ (Ec c).map (LinearMap.adjoint Θ) ≤ Formalism.L2.Col.eigSum op Q) => Ec c)
        c ⟨hb, (hiff Q c hb).2 hq⟩ le_rfl

end GlobalTheory.Hk3
end

section

noncomputable section

namespace GlobalTheory.UnitK

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

theorem vEqK_zero_of_norm_one : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmb X.G)
    (x : X.G.Kf), ‖E.iK x‖ = 1 → X.vEqK x 0 := by
  intro p _ X hfr E x hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨N, hN⟩ := Formalism.MainNotions.FormalGroupSystem.Pf.exists_rep X hfr hx0

  have hint : ∀ y : X.G.Kf, ‖E.iK y‖ = 1 → y ∈ X.intK := fun y hy =>
    (E.mem_iff y).1 (by rw [mem_OcC]; exact hy.le)
  have h1 : X.vGeK x 0 := (Formalism.MainNotions.FormalGroupSystem.Pf.vGeK_zero_iff X).2 (hint x hx)
  have h2 : X.vGeK x⁻¹ 0 := (Formalism.MainNotions.FormalGroupSystem.Pf.vGeK_zero_iff X).2 (hint x⁻¹ (by rw [map_inv₀, norm_inv, hx, inv_one]))
  have hN1 := (Formalism.MainNotions.FormalGroupSystem.Pf.vGeK_iff_of_rep X hfr hN 0).1 h1
  have hN2 := (Formalism.MainNotions.FormalGroupSystem.Pf.vGeK_iff_of_rep X hfr (Formalism.MainNotions.FormalGroupSystem.Pf.Rep.inv X hN) 0).1 h2
  simp only [zero_mul] at hN1 hN2
  have hN0 : N = 0 := by
    have a : (0 : ℤ) ≤ N := by exact_mod_cast hN1
    have b : (0 : ℤ) ≤ -N := by exact_mod_cast hN2
    omega

  have he : 0 < X.eO := by
    rcases Nat.eq_zero_or_pos X.eO with h0 | h0
    · exfalso
      obtain ⟨u, hu⟩ := X.eO_spec
      rw [h0, pow_zero] at hu

      have hpu : IsUnit (p : X.G.O) := by
        exact IsUnit.of_mul_eq_one _ hu
      obtain ⟨w, hw⟩ := hpu.exists_right_inv
      have hb := E.int w
      have hmul : E.iK (algebraMap X.G.O X.G.Kf (p : X.G.O)) * E.iK (algebraMap X.G.O X.G.Kf w) = 1 := by
        rw [← map_mul, ← map_mul, hw, map_one, map_one]
      have hn : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
        have : (p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := by simp
        rw [this, norm_algebraMap', Padic.norm_p]
      rw [map_natCast, map_natCast] at hmul
      have hn2 := congrArg norm hmul
      rw [norm_mul, norm_one, hn] at hn2
      have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
      have hp0 : (0 : ℝ) < p := by linarith
      have : ‖E.iK (algebraMap X.G.O X.G.Kf w)‖ = p := by
        field_simp at hn2
        linarith
      linarith
    · exact h0
  exact (Formalism.MainNotions.FormalGroupSystem.Pf.vEqK_iff_of_rep X hfr hN 0).2 ⟨he, by simp [hN0]⟩

end GlobalTheory.UnitK
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_iSup_type_parts_of_good_base_forms : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), (R.toCx3 F).PartsW false → ∀ j (w : (R.HW j (sg0 D A3.A)).H), w ∈ R.toRealDat.WS F.lv2 false j (sg0 D A3.A) → w ∈ ⨆ p, R.Wp3 j p := by
  first | exact @GlobalTheory.TwParts.mem_iSup_Wp3_of_mem_WS | exact GlobalTheory.TwParts.mem_iSup_Wp3_of_mem_WS | (intros; apply GlobalTheory.TwParts.mem_iSup_Wp3_of_mem_WS <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.EqOffSplitOfSplit

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

theorem isSplit_conj (D : D7) {P Q : HeightOneSpectrum (𝓞 D.host.E)} (hP : GL3Theta.SplitP D P)
    (hQ : ∀ x : 𝓞 D.host.E, x ∈ Q.asIdeal ↔ Formalism.L2.PairingIndexBounds.Rec.cO D x ∈ P.asIdeal) : GL3Theta.SplitP D Q := by
  obtain ⟨a, b, hab, ha, hb⟩ := hP
  have hb' : b = Formalism.L2.PairingIndexBounds.Rec.cO D a := Subtype.ext (hab.trans rfl)
  refine ⟨b, a, ?_, ?_, ?_⟩
  · rw [hab]; exact (Formalism.L2.PairingIndexBounds.Rec.conj_conj' D (a : D.host.E)).symm
  · rw [hQ, hb', Formalism.L2.PairingIndexBounds.Rec.cO_cO]; exact ha
  · rw [hQ, ← hb']; exact hb

theorem eqOffSplit_of_eqOff : ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ)
    (L L₀ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)),
    GL3Theta.SplitP D P → GL3Theta.EqOff D P L L₀ → GL3Theta.EqOffSplit D L L₀ := by
  intro D P n L L₀ hP hoff
  obtain ⟨m, hm⟩ := hoff
  obtain ⟨x, hx0, hxP, hxM⟩ := Formalism.L2.PairingIndexBounds.Rec.genPow D P
  have hc0 : ∀ y : 𝓞 D.host.E, y ≠ 0 → Formalism.L2.PairingIndexBounds.Rec.cO D y ≠ 0 := fun y hy h => hy (by
    rw [← Formalism.L2.PairingIndexBounds.Rec.cO_cO D y, h, map_zero])
  have hg0 : x ^ m ≠ 0 := pow_ne_zero m hx0
  obtain ⟨h1, h2⟩ := hm (x ^ m) (Formalism.L2.PairingIndexBounds.Rec.cO D (x ^ m)) rfl (Ideal.pow_mem_pow hxP m)
  refine ⟨x ^ m * Formalism.L2.PairingIndexBounds.Rec.cO D (x ^ m), mul_ne_zero hg0 (hc0 _ hg0), fun Q hQ => ?_, h1, h2⟩
  rcases Q.isPrime.mem_or_mem hQ with h | h
  · have e : P.asIdeal = Q.asIdeal := hxM _ Q.isPrime (Q.isPrime.mem_of_pow_mem m h)
    have e' : P = Q := HeightOneSpectrum.ext e
    exact e' ▸ hP
  · rw [map_pow] at h
    have h3 : Formalism.L2.PairingIndexBounds.Rec.cO D x ∈ Q.asIdeal := Q.isPrime.mem_of_pow_mem m h
    have e : P.asIdeal = (Formalism.L2.PairingIndexBounds.Rec.cQ D Q).asIdeal :=
      hxM _ (Formalism.L2.PairingIndexBounds.Rec.cQ D Q).isPrime ((Formalism.L2.PairingIndexBounds.Rec.mem_cQ D Q x).2 h3)
    refine isSplit_conj D hP fun y => ?_
    rw [e, Formalism.L2.PairingIndexBounds.Rec.mem_cQ, Formalism.L2.PairingIndexBounds.Rec.cO_cO]

end GlobalTheory.EqOffSplitOfSplit
end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

theorem _root_.GlobalTheory.T.heckeCharacter_finite_idele_eq_prod_values_zpow : ∀ {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (T : Finset (HeightOneSpectrum (𝓞 L))) (b : Neutral.B1.Ideles L), Formalism.L2.Host.IsFinIdele b → (∀ P, P ∉ T → (b : AdeleRing (𝓞 L) L).2 P = 1) → (∀ P ∈ T, χ.UnrAt P) → ∃ n : HeightOneSpectrum (𝓞 L) → ℤ, χ.1 b = ∏ P ∈ T, χ.val P ^ n P := by
  first | exact @GlobalTheory.HeckeFinVal.eq_prod_val_zpow | exact GlobalTheory.HeckeFinVal.eq_prod_val_zpow | (intros; apply GlobalTheory.HeckeFinVal.eq_prod_val_zpow <;> assumption)
end

section

open IsDedekindDomain NumberField Matrix

theorem _root_.GlobalTheory.T.cartanExponents_nonneg_minusculeTop_product : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (ϖ : v.adicCompletion F), Formalism.UG.IsUnifV F v ϖ → ∀ (d : Fin n → ℤ) (k : ℕ), Antitone d → (∀ i, 0 ≤ d i) → (∀ i : Fin n, 0 < d i ↔ (i : ℕ) < k) → ∀ a₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ a₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ a₃ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ d' : Fin n → ℤ, Antitone d' → ∀ k₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ k₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), (a₁ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagPow F v ϖ (fun i => if 0 < d i then d i - 1 else d i) * (a₂ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagPow F v ϖ (fun i => if (i : ℕ) < k then 1 else 0) * (a₃ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = (k₁ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagPow F v ϖ d' * (k₂ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) → (∀ i, 0 ≤ d' i) ∧ (d' = d ∨ (∑ i, d' i = ∑ i, d i ∧ ∑ i, d' i ^ 2 < ∑ i, d i ^ 2)) := by
  first | exact @GlobalTheory.Hk3.MinuscTopLocal.cartan_top_step | exact GlobalTheory.Hk3.MinuscTopLocal.cartan_top_step | (intros; apply GlobalTheory.Hk3.MinuscTopLocal.cartan_top_step <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

namespace GlobalTheory.TwV.Xc

theorem sum_alt_sign_range (m : ℕ) :
    ∑ i ∈ Finset.range (2 * m), (if i % 2 = 1 then (-1 : ℤ) else 1) = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have h1 : (2 * m) % 2 = 0 := by omega
    have h2 : (2 * m + 1) % 2 = 1 := by omega
    simp [h1, h2]

theorem sum_alt_sign_pos (n' : ℕ) (hn : Even n') :
    ∑ s : Fin n', (if IsOddPos s then (-1 : ℤ) else 1) = 0 := by
  obtain ⟨m, rfl⟩ := hn
  calc (∑ s : Fin (m + m), (if IsOddPos s then (-1 : ℤ) else 1))
        = ∑ i ∈ Finset.range (m + m), (if i % 2 = 1 then (-1 : ℤ) else 1) := by
          rw [← Fin.sum_univ_eq_sum_range]; rfl
    _ = 0 := by simpa [two_mul] using sum_alt_sign_range m

theorem vm_eq_of_shift (p : ℕ) [Fact p.Prime] (X : Sys p) (v : X.Pl) (l : ℕ) (e : Fin (X.G.P.n' v) → ℤ) (k : ℤ)
    (hk : ∀ s, X.w v l s = e s - k) :
    X.vm v l = ∑ s : Fin (X.G.P.n' v), (if IsOddPos s then -1 else 1) * e s := by
  have hw : ∑ s : Fin (X.G.P.n' v), (if IsOddPos s then -1 else 1) * X.w v l s = X.vm v l := by
    unfold Sys.vm
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases h : IsOddPos s <;> simp [h]
  rw [← hw]
  have e1 : ∀ s, (if IsOddPos s then (-1 : ℤ) else 1) * X.w v l s =
      (if IsOddPos s then -1 else 1) * e s - (if IsOddPos s then (-1 : ℤ) else 1) * k := by
    intro s; rw [hk s]; ring
  rw [Finset.sum_congr rfl (fun s _ => e1 s), Finset.sum_sub_distrib, ← Finset.sum_mul,
    sum_alt_sign_pos _ (X.G.P.setting v).even, zero_mul, sub_zero]

theorem vm_shift_cancels : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (v : X.Pl) (l : ℕ) (e : Fin (X.G.P.n' v) → ℤ) (k : ℤ),
    (∀ s, X.w v l s = e s - k) → X.vm v l = ∑ s : Fin (X.G.P.n' v), (if IsOddPos s then -1 else 1) * e s :=
  fun p _ X v l e k hk => vm_eq_of_shift p X v l e k hk

end GlobalTheory.TwV.Xc
end
