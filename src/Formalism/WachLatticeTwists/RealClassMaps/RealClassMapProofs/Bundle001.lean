module

public import Formalism.WachLatticeTwists.RealClassMaps.StatClassMapReal
public import Formalism.WachLatticeTwists.RealClassMaps.Statement
public import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.ClsRowVOfMem
public import Formalism.WachLatticeTwists.CupProductVanishing.CupProductProofs.Clause4GK
public import Formalism.WachLatticeTwists.ShapeRowIsomorphisms.ShapeRowProofs.BkInRow
public import Formalism.WachLatticeTwists.ShapeRowIsomorphisms.ShapeRowProofs.Clause5Row
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsCycOn IsFGTop cupFG)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN

theorem ko_tors (O : Type) [CommRing O] [IsDomain O] (z : KO O) : ∃ c : O, c ≠ 0 ∧ c • z = 0 := by
  obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨⟨a, ⟨b, hb⟩⟩, hq⟩ := IsLocalization.surj (nonZeroDivisors O) q
  refine ⟨b, nonZeroDivisors.ne_zero hb, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  refine Submodule.mem_one.2 ⟨a, ?_⟩
  rw [Algebra.smul_def, mul_comm]
  exact hq.symm

theorem psiCont (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    (A : Type) [Ring A] [Algebra O A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [ContinuousConstSMul O A] (Y : Submodule A A) (hO : PadicCoeff p O) (hA : IsFGTop O A)
    (ψ : Y →ₗ[O] KO O) : Continuous ψ := by
  have hfg : IsFGTop O Y := by
    have := hA.fg
    have := hA.t2
    have := hA.csmul
    refine ⟨?_, inferInstance, ?_⟩
    · exact Module.Finite.of_injective (Y.subtype.restrictScalars O) Subtype.val_injective
    · exact ⟨Continuous.subtype_mk (f := fun q : O × Y => q.1 • (q.2 : A))
        (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)) _⟩
  obtain ⟨a, ha, hka⟩ : ∃ a : O, a ≠ 0 ∧ ∀ y : Y, a • ψ y = 0 := by
    obtain ⟨s, hs⟩ := hfg.fg.fg_top
    choose f hf0 hf using fun y : Y => ko_tors O (ψ y)
    refine ⟨∏ y ∈ s, f y, Finset.prod_ne_zero_iff.2 (fun y _ => hf0 y), fun y => ?_⟩
    have hy : y ∈ Submodule.span O (s : Set Y) := hs ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem f hx
      rw [hc, mul_comm, mul_smul, hf, smul_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), smul_add, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, smul_comm, hx, smul_zero]
  have hopen := hfg.isOpen_mulSub hO ha
  refine continuous_of_continuousAt_zero ψ.toAddMonoidHom ?_
  intro U hU
  have hU0 : (0 : KO O) ∈ U := by
    have := mem_of_mem_nhds hU
    simpa using this
  rw [Filter.mem_map]
  refine Filter.mem_of_superset (hopen.mem_nhds (zero_mem _)) ?_
  rintro _ ⟨z, rfl⟩
  show ψ (a • z) ∈ U
  rw [map_smul, hka]
  exact hU0

theorem inRowReal_of (p : ℕ) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {A T' G : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [ContinuousConstSMul O A] [ContinuousMul A]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (Dw : Subgroup G) [TopologicalSpace Dw]
    {T₁ T₂ : Type} [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
    [TopologicalSpace T₁] [IsTopologicalAddGroup T₁] [ContinuousConstSMul O T₁]
    (ρ₁ : Representation O G T₁) (inc : T₁ →ₗ[O] A) (π : T₁ →ₗ[O] T₂)
    (D : LatData O Dw VT VT') (v : T₂ ≃ₗ[O] D.T') (hc : Continuous fun t => v (π t))
    (he : ∀ g t, v (π (resRep ρ₁ Dw g t)) = D.ρTl' g (v (π t)))
    (Fs : Submodule O (H1 D.ρTl')) (Hf₁ : Submodule O (H1 (resRep ρ₁ Dw)))
    (hO : PadicCoeff p O) (hA : IsFGTop O A) (hinc : Continuous inc)
    (hur : Continuous fun g : Dw => uElt r χ (g : G)) (hIm : Hf₁.map (gRow D _ π v hc he) ≤ Fs) :
    InRowReal r χ E Dw ρ₁ inc π D v Fs (Hf₁.map (gRow D _ π v hc he)) := by
  refine ⟨fun a => Continuous a, fun a ha => ?_, fun a ha => ?_, fun ψ f hf => ?_, fun a ha => hc.comp ha, ?_, hIm⟩
  · refine Continuous.subtype_mk (f := fun q : Dw × Dw =>
      inc (a q.1) * (uElt r χ (q.1 : G) * ((uElt r χ (q.2 : G) - 1) * E))) ?_ _
    exact (hinc.comp (ha.comp continuous_fst)).mul ((hur.comp continuous_fst).mul
      (((hur.comp continuous_snd).sub continuous_const).mul continuous_const))
  · exact ((hinc.comp ha).mul (hur.mul continuous_const)).neg
  · exact (psiCont p O A (Ymod r χ E) hO hA ψ).comp hf
  · rintro _ ⟨y, _, rfl⟩
    induction y using Submodule.Quotient.induction_on with
    | _ c =>
      have h : (fun g => v (π (c.1 g))) ∈ Z1 D.ρTl' :=
        (cocycles1MapOfEquivariant (resRep ρ₁ Dw) D.ρTl' (v.toLinearMap ∘ₗ π) hc he c).2
      refine ⟨c.1, c.2.2, c.2.1, ?_⟩
      rw [clsRow_of_mem D v _ h]
      rfl

end Formalism.RepresentationBoundsCohomology.FIN
end
end

section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.T2
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsCycOn IsFGTop cupFG RealLatG fracBilinear)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN


theorem rowRhoReal : StatRowRhoReal := by
  intro p _ O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ek Ω _ _ _ _ _ Aw hp A T' _ _ _ _ _ _ _
    M _ _ _ _ r χ E ε T₁ T₂ _ _ _ _ ρ₁ ρ₂ inc π γ D u hu v familyMassRatio iS1 familyMassSecondLine iS2 HfV HfV' Fs Im hO hF hA hcyc hε hD hπ
    hv hγ hBK hFs hRow hk
  obtain ⟨K, hK, i, h1, -, -⟩ := ReciprocityTheory.ChartRestriction.T2.exists_dec_equiv (F := Ek) Aw hp
  have hεD : D.ε = ε.comp (Aw.decompositionSubgroup Ek).subtype := by
    ext g; simp [hε g]
  have hcD : IsCyc p K (ReciprocityTheory.ChartRestriction.T2.carry i D.ε) := h1 O D.ε (hεD ▸ hcyc)
  obtain ⟨inv, invF, hc⟩ := ReciprocityTheory.ChartRestriction.T2.exists_invariants_iso hK hO hF i hcD
  have hD' : RealLatG i (withInv D inv.toLinearMap invF.toLinearMap) :=
    ⟨hcD, hD.lat, hD.perf, hD.contT, hD.openT, hD.t2, hD.t2', hD.cs, hD.cs'⟩
  let j1 : Module (FractionRing O) (H1 (withInv D inv.toLinearMap invF.toLinearMap).ρT) := familyMassRatio
  have j2 : IsScalarTower O (FractionRing O) (H1 (withInv D inv.toLinearMap invF.toLinearMap).ρT) := iS1
  let j3 : Module (FractionRing O) (H1 (withInv D inv.toLinearMap invF.toLinearMap).ρT') := familyMassSecondLine
  have j4 : IsScalarTower O (FractionRing O) (H1 (withInv D inv.toLinearMap invF.toLinearMap).ρT') := iS2
  have hBK' : ∀ a, a ∈ HfV ↔ ∀ b ∈ HfV',
      fracBilinear (pairF (withInv D inv.toLinearMap invF.toLinearMap)) a b = 0 := by
    intro a
    rw [hBK a]
    refine forall₂_congr fun b _ => ?_
    show _ ↔ invF (cupFG D a b) = 0
    rw [LinearEquiv.map_eq_zero_iff]
  obtain ⟨_, hbk⟩ := bkInRow p K O VT VT' A T' _ M r χ (Aw.decompositionSubgroup Ek)
    (withInv D inv.toLinearMap invF.toLinearMap) i u hu HfV HfV' hK hO hF hD' inv.injective invF.injective hc hBK'
  obtain ⟨C₁, c1, c2, c3, c3', c6, c7⟩ := hRow
  let pairD := fracBilinear (pairF (withInv D inv.toLinearMap invF.toLinearMap))
  refine ⟨prK (withInv D inv.toLinearMap invF.toLinearMap) _ hk, pairD, ?_, ?_⟩
  · rw [hFs]; exact hbk
  · refine ⟨C₁, fun z => Continuous fun q : _ × _ => z q.1 q.2, fun f => Continuous f, fun f => Continuous f,
      fun f => Continuous f, c1, c2, c3, ?_, ?_, c6, c7⟩
    · exact clause4GK p K O A T' _ r χ E (Aw.decompositionSubgroup Ek) ε hK hO i (hεD ▸ hcD) hA
    · exact clause5Row O VT VT' A T' _ M r χ (Aw.decompositionSubgroup Ek) ε T₁ T₂ ρ₁ ρ₂ π γ
        (withInv D inv.toLinearMap invF.toLinearMap) u hu v hε hD.contT hπ hv hγ hk C₁ c3'


end Formalism.RepresentationBoundsCohomology.FIN
end
end
