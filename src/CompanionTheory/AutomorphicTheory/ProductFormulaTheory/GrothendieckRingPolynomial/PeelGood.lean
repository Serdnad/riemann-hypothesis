module

public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ProdList
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.CuspEmbP
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyExhaustion.PeelDefs
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.ExhaustionOfSteps
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.IrreducibleAdmissibleGL
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.JuxtPOfFineUniq
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.NotAboveTransGenSelf
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.SquareIntegrableSegments.SegmentReordering.CsOrderfree
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.BernsteinZelevinsky.TopAdm
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Mathlib.Topology.Algebra.Group.Units
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosocleOfContragredientSocle
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSegmentRepresentation
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubSegmentProduct
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOrderedFormSnoc
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsFactorsDualReverseOrdered
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSegmentDual
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFree
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLanglandsOfIrreducibleAdmissible
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReverseOrderedProductHasSocle
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetAll
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentProductWordInShuffle
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducible
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.IsLAddSegmentOfInjectiveOfNotPrecedes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsListPairwiseNotRel
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExhUnipRadOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLength

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos CompanionTheory.Exh GlobalTheory.CompanionTheory.ExhGood



namespace CompanionTheory.Groth.ClsOfF

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem comm_of (hI : Zc.Cos.LUnlinkedIrr k) : Zc.Cos.LUnlinkedComm k :=
  _root_.GlobalTheory.CompanionTheory.BZSegComm.lUnlinkedComm k CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top hI

theorem stdCos (hZ : GlobalTheory.Published.SegmentRepresentation) (hI : Zc.Cos.LUnlinkedIrr k) :
    ∀ (𝔪 : Multiset (Segment k)) (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), LFactors 𝔪 x →
      ∃ π : IrrRep (GL (Fin N) k), IsCosocle π.ρ (prodIrr x hd) := by
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  intro 𝔪 h N x hd hx
  obtain ⟨Γ, hΓ, hL⟩ := _root_.GlobalTheory.CompanionTheory.DualForms.exists_revOrdered_dual hA (_root_.GlobalTheory.CompanionTheory.SegLDual.lSegDual hA hZ) 𝔪 x hx
  obtain ⟨hd', ⟨e⟩⟩ := _root_.GlobalTheory.CompanionTheory.ContraProd.contra_prodIrr hA x hd
  obtain ⟨τ, hτ⟩ := _root_.GlobalTheory.CompanionTheory.SocleRev.exists_isSocle_prodIrr_of_isRevOrdered hA (_root_.GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet hA hZ) hI (comm_of hI) Γ (fun a => dualCl (x a)) hd' hΓ hL
  exact _root_.GlobalTheory.CompanionTheory.CosocleContra.isCosocle_of_isSocle_contra hA (prodIrr x hd) (isSmooth_prodIrr x hd) (_root_.GlobalTheory.CompanionTheory.ProdFL.main hA x hd) τ
    (hτ.of_equiv (Representation.Equiv.refl _) e.symm)

theorem segCl (Δ : Segment k) : ∃ x : IrrGL (k := k), IsLSeg Δ x.rep := by
  obtain ⟨π, hπ⟩ := _root_.GlobalTheory.CompanionTheory.SegExists.exists_isLSeg CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top Δ
  exact ⟨IrrGL.of π.ρ π.smooth π.irr, hπ.of_equiv (IrrGL.equivOf π.ρ π.smooth π.irr)⟩

theorem ex_of (HS : ∀ (𝔪 : Multiset (Segment k)) (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), LFactors 𝔪 x →
      ∃ π : IrrRep (GL (Fin N) k), IsCosocle π.ρ (prodIrr x hd)) (𝔪 : Multiset (Segment k)) :
    ∃ x : IrrGL (k := k), IsL 𝔪 x.rep := by
  obtain ⟨Δ, hΔ⟩ := GlobalTheory.LocGL.exists_isOrderedForm 𝔪
  choose y hy using (segCl (k := k))
  let x : Fin 𝔪.card → IrrGL (k := k) := fun i => y (Δ i)
  have hx : LFactors 𝔪 x := ⟨Δ, hΔ, fun i => hy (Δ i)⟩
  obtain ⟨π, hπ⟩ := HS 𝔪 𝔪.card _ x rfl hx
  refine ⟨IrrGL.of π.ρ π.smooth π.irr, 𝔪.card, x, rfl, hx, ?_⟩
  exact hπ.of_equiv (IrrGL.equivOf π.ρ π.smooth π.irr) (.refl _)

theorem peelGood (HS : ∀ (𝔪 : Multiset (Segment k)) (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), LFactors 𝔪 x →
      ∃ π : IrrRep (GL (Fin N) k), IsCosocle π.ρ (prodIrr x hd)) (HL : LSocleGL k) : Zc.PeelGoodP k := by
  intro x y hd s 𝔫 hs hn hf hp
  exact isL_add_segment_of_injective_of_not_precedes_of_cosocle HS HL x y hd s 𝔫 hs hn hf hp

theorem exh_at (hM : MidP k) (hR : RefineP k) (hS : SwapP k) (hC : CuspEmbP k) (hP : SuppP k) (hJ : JuxtP k)
    (hL : LinkP k) (hm : MinP k) (hG : Zc.PeelGoodP k) (x : IrrGL (k := k)) : ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep :=
  exhaustion_at hM hR hS hC hP hJ hL hm hG x

end CompanionTheory.Groth.ClsOfF

namespace CompanionTheory.Groth


open ClsOfF in
theorem cls_of (hZ : GlobalTheory.Published.SegmentRepresentation) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hI : Zc.Cos.LUnlinkedIrr k)
    (H : CompanionTheory.Exh.MidP k ∧ CompanionTheory.Exh.RefineP k ∧ CompanionTheory.Exh.SwapP k) : Cls k := by
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  obtain ⟨hM, hR, hS⟩ := H
  have hCm : Zc.Cos.LUnlinkedComm k := comm_of hI
  have hF : Zc.LOrderFree k := CompanionTheory.PfEss.Zc2.cs_orderfree hA hCm
  have hSoc : Zc.LSocleGL k := _root_.GlobalTheory.CompanionTheory.LSocle.lSocleGL hA (_root_.GlobalTheory.CompanionTheory.GKLocalProof.gkLocal hA) hF
  have HS := stdCos hZ hI
  have hC : CuspEmbP k := cuspEmbP k hA hR
  exact
    { ex := ex_of HS
      exh := exh_at hM hR hS hC (suppP k)
        (juxtP_of_fineUniq hA hM hR hS hC (_root_.GlobalTheory.CompanionTheory.CuspShuffle.inShW_of_wd hA (_root_.GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet hA hZ)) (_root_.GlobalTheory.CompanionTheory.SegUniq.isLSeg_of_dec hA hZ))
        linkP minP (peelGood HS hSoc)
      free := hF
      soc := hSoc
      jac := _root_.GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet hA hZ
      seg := fun Δ => _root_.GlobalTheory.CompanionTheory.SegExists.exists_isLSeg hA Δ
      unl := hI
      com := hCm }

end CompanionTheory.Groth

end
