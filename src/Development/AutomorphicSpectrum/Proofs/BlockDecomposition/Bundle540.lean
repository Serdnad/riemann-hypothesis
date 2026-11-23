module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle509
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle464
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepMetricSmooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1332
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle487
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle521
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle472
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle524
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle480
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle490
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle515
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle493
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CliffordHighestWeightVector
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle514
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle517
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle518
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle492
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle459
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle039

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.DimClosure

private theorem exists_ringKrullDim_le_add_of_finiteType {R A : Type*} [CommRing R] [CommRing A]
    [IsNoetherianRing R] (f : R →+* A) (hf : f.FiniteType) :
    ∃ N : ℕ, ringKrullDim A ≤ ringKrullDim R + N := by
  letI := f.toAlgebra
  obtain ⟨k, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hf
  refine ⟨k, ?_⟩
  calc ringKrullDim A ≤ ringKrullDim (MvPolynomial (Fin k) R) :=
        ringKrullDim_le_of_surjective g.toRingHom hg
    _ = ringKrullDim R + k := by
        rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem exists_open_nhd_topologicalKrullDim_MP_le {m : ℕ} {n : Fin (m + 1) → ℕ} (y : MP ℤ m n) :
    ∃ U : (MP ℤ m n).Opens, y ∈ U ∧ ∃ N : ℕ, topologicalKrullDim (U : Set (MP ℤ m n)) ≤ N := by
  haveI : AlgebraicGeometry.IsProper (mpStr ℤ m n) := isProper_mpStr ℤ m n
  obtain ⟨U, hU, hyU, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (U := (⊤ : (MP ℤ m n).Opens)) (x := y) (by simp)
  refine ⟨U, hyU, ?_⟩
  have hZ := AlgebraicGeometry.isAffineOpen_top (Spec (CommRingCat.of ℤ))
  have hft := AlgebraicGeometry.Scheme.Hom.finiteType_appLE (mpStr ℤ m n) hZ hU
    (by simp)
  haveI : IsNoetherianRing ((Spec (CommRingCat.of ℤ)).presheaf.obj (Opposite.op ⊤)) :=
    isNoetherianRing_of_ringEquiv ℤ (Scheme.ΓSpecIso (CommRingCat.of ℤ)).symm.commRingCatIsoToRingEquiv
  obtain ⟨N, hN⟩ := exists_ringKrullDim_le_add_of_finiteType _ hft
  have hZdim : ringKrullDim ((Spec (CommRingCat.of ℤ)).presheaf.obj (Opposite.op ⊤)) ≤ 1 := by
    rw [ringKrullDim_eq_of_ringEquiv (Scheme.ΓSpecIso (CommRingCat.of ℤ)).commRingCatIsoToRingEquiv]
    have h1 := Ring.krullDimLE_iff.mp (IsPrincipalIdealRing.krullDimLE_one ℤ)
    exact_mod_cast h1
  haveI := hU.isOpenImmersion_fromSpec
  have htop : topologicalKrullDim (U : Set (MP ℤ m n)) =
      ringKrullDim ((MP ℤ m n).presheaf.obj (Opposite.op U)) := by
    rw [GlobalTheory.topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
  refine ⟨N + 1, ?_⟩
  rw [htop]
  calc ringKrullDim ((MP ℤ m n).presheaf.obj (Opposite.op U))
        ≤ ringKrullDim ((Spec (CommRingCat.of ℤ)).presheaf.obj (Opposite.op ⊤)) + N := hN
    _ ≤ 1 + N := by gcongr
    _ = ((N + 1 : ℕ) : WithBot ℕ∞) := by push_cast; exact add_comm _ _

private theorem exists_topologicalKrullDim_MP_le {m : ℕ} {n : Fin (m + 1) → ℕ} :
    ∃ d : ℕ, topologicalKrullDim (MP ℤ m n) ≤ d := by
  haveI : AlgebraicGeometry.IsProper (mpStr ℤ m n) := isProper_mpStr ℤ m n
  haveI : CompactSpace (MP ℤ m n) :=
    AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace (mpStr ℤ m n)
  choose U hyU N hN using fun y : MP ℤ m n => exists_open_nhd_topologicalKrullDim_MP_le y
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (U y : Set (MP ℤ m n)))
    (fun y => (U y).isOpen) (fun y _ => Set.mem_iUnion.mpr ⟨y, hyU y⟩)
  refine ⟨t.sup N, GlobalTheory.topologicalKrullDim_le_of_forall_exists_isOpen fun z => ?_⟩
  obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ z))
  refine ⟨U y, (U y).isOpen, hzy, (hN y).trans ?_⟩
  exact_mod_cast Finset.le_sup (f := N) hy

theorem exists_dim_closure_eq {m : ℕ} {n : Fin (m + 1) → ℕ} (x : MP ℤ m n) :
    ∃ e : ℕ, topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = (e : ℕ) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_MP_le (m := m) (n := n)
  have hle : topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) ≤ d :=
    (topologicalKrullDim_subspace_le _ _).trans hd
  have hnn : 0 ≤ topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) := by
    haveI : Nonempty (IrreducibleCloseds (closure ({x} : Set (MP ℤ m n)))) :=
      ⟨⟨closure {(⟨x, subset_closure (Set.mem_singleton x)⟩ : closure ({x} : Set (MP ℤ m n)))},
        isIrreducible_singleton.closure, isClosed_closure⟩⟩
    unfold topologicalKrullDim
    exact Order.krullDim_nonneg
  generalize topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = D at hle hnn ⊢
  induction D using WithBot.recBotCoe with
  | bot => exact absurd hnn (not_le.mpr (WithBot.bot_lt_coe _))
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have h5 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((d : ℕ∞) : WithBot ℕ∞) := hle
      exact ENat.natCast_ne_top d (top_le_iff.mp (WithBot.coe_le_coe.mp h5))
    | coe e => exact ⟨e, rfl⟩

theorem dim_closure_iff_isArithVar : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) (d : ℕ),
    CharZero ((MP ℤ m n).residueField x) →
      (topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = (d : ℕ) ↔ Geo.IsArithVar (ptIdeal x) d) := by
  intro m n x d hc
  refine ⟨GlobalTheory.T.arithmetic_variety_point_dimension m n x d hc, fun h => ?_⟩
  obtain ⟨e, he⟩ := exists_dim_closure_eq x
  have h' := GlobalTheory.T.arithmetic_variety_point_dimension m n x e hc he
  have h1 := h.2.2.2
  have h2 := h'.2.2.2
  have hde : d = e := by
    have h3 := h1.symm.trans h2
    have h4 : d + Fintype.card (Fin (m + 1)) = e + Fintype.card (Fin (m + 1)) := by exact_mod_cast h3
    omega
  rw [he, hde]

end GlobalTheory.CompanionTheory.MPDict.DimClosure
end
end

section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

open GlobalTheory.CompanionTheory.MPDict.SmoothRep (rt mem_mchart ev_rt)

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {D : ℕ}

def ratioVec {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) (p : ∀ k, Bk n k) (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) :
    (Σ k, Bk n k) → ℂ :=
  fun q => ev (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart p) ((i.appLE (mchart p) (i ⁻¹ᵁ mchart p) le_rfl).hom (rt p q)) y

theorem mem_ptsIn_of_over {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) {p : ∀ k, Bk n k}
    {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (H : Over i y z) (hp : ∀ k, z ⟨k, p k⟩ ≠ 0) :
    y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart p) :=
  (mem_ptsIn_preimage (f := i) (m := PtsOver.map i rfl _) fun _ => rfl).2 (mem_mchart H hp)

theorem ratioVec_apply {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) {p : ∀ k, Bk n k}
    {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (H : Over i y z) (hp : ∀ k, z ⟨k, p k⟩ ≠ 0)
    (q : Σ k, Bk n k) : ratioVec i p y q = z q / z ⟨q.1, p q.1⟩ :=
  (CxPts.ev_appLE_of_comp (r := i) (m := PtsOver.map i rfl _) (fun _ => rfl) le_rfl _
    (mem_ptsIn_of_over i H hp)).trans (ev_rt H hp q)

theorem sameOrbit_ratioVec {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) {p : ∀ k, Bk n k}
    {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (H : Over i y z) (hp : ∀ k, z ⟨k, p k⟩ ≠ 0) :
    SameOrbit z (ratioVec i p y) := by
  refine ⟨fun k => z ⟨k, p k⟩, hp, funext fun q => ?_⟩
  rw [ratioVec_apply i H hp q, mul_div_cancel₀ _ (hp q.1)]

theorem over_liftOf {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) : Over i y (liftOf i y) := by
  obtain ⟨z, -, hz⟩ := GlobalTheory.T.complex_point_lifts_to_multicone m n X i y
  have h : ∃ z, Over i y z := ⟨z, hz⟩
  rw [liftOf, dite_eq_left h]
  exact h.choose_spec

theorem differentiableAt_projCoord {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (Ψ : LinProj n D) (c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D) {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀}
    (hy : y ∈ c.e.source) {z : (Σ k, Bk n k) → ℂ} (H : Over i y z) (h0 : Ψ (segre z) 0 ≠ 0) :
    DifferentiableAt ℂ (projCoord i Ψ ∘ c.finChart.symm) (c.finChart y) := by
  choose p hp using fun k => exists_block_ne_zero_of_isUnder H k
  have hyW := mem_ptsIn_of_over i H hp
  have hOo : IsOpen (c.finChart.target ∩ c.finChart.symm ⁻¹' ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart p)) :=
    c.finChart.isOpen_inter_preimage_symm (isOpen_ptsIn _)
  have hv : c.finChart y ∈ c.finChart.target ∩ c.finChart.symm ⁻¹' ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart p) :=
    ⟨c.finChart.map_source hy, by rwa [Set.mem_preimage, c.finChart.left_inv hy]⟩
  have hl : DifferentiableAt ℂ (fun v => ratioVec i p (c.finChart.symm v)) (c.finChart y) :=
    differentiableAt_pi.2 fun q =>
      (((c.analyticOnNhd_finChart_iff (isOpen_ptsIn _) _).2 (c.holo _ _)) _ hv).differentiableAt
  have hs := ReciprocityTheory.ChartRestriction.G.Geo.segre_differentiableAt hl
  let L := LinearMap.toContinuousLinearMap Ψ
  have hL : DifferentiableAt ℂ (fun v => L (segre (ratioVec i p (c.finChart.symm v)))) (c.finChart y) :=
    L.differentiableAt.comp _ hs
  have hc (a : Fin (D + 1)) := differentiableAt_pi.1 hL a
  have hne : Ψ (segre (ratioVec i p y)) 0 ≠ 0 := by
    obtain ⟨l, hl0, e⟩ := sameOrbit_ratioVec i H hp
    intro h
    apply h0
    rw [segre_orbit e, map_smul, Pi.smul_apply, h, smul_zero]
  have hne' : L (segre (ratioVec i p (c.finChart.symm (c.finChart y)))) 0 ≠ 0 := by
    rw [c.finChart.left_inv hy]
    exact hne
  have hev : (projCoord i Ψ ∘ c.finChart.symm) =ᶠ[nhds (c.finChart y)]
      fun v => ratios Ψ (ratioVec i p (c.finChart.symm v)) := by
    filter_upwards [hOo.mem_nhds hv, (hc 0).continuousAt.eventually_ne hne'] with v hvO hv0
    have H' := over_liftOf i (c.finChart.symm v)
    have hp' : ∀ k, liftOf i (c.finChart.symm v) ⟨k, p k⟩ ≠ 0 := fun k =>
      (H' k (p k)).1.1 (ptsIn_mono (mchart_le p k)
        ((mem_ptsIn_preimage (f := i) (m := PtsOver.map i rfl _) fun _ => rfl).1 hvO.2))
    exact ratios_eq_of_sameOrbit Ψ (sameOrbit_ratioVec i H' hp') hv0
  refine DifferentiableAt.congr_of_eventuallyEq (differentiableAt_pi.2 fun a => ?_) hev
  simp only [ratios, div_eq_mul_inv]
  exact (hc a.succ).mul ((hc 0).inv hne')

theorem volume_image_crit : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ)
    (Ψ : GlobalTheory.CompanionTheory.MixZ.ArchEq.LinProj n D) (c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D),
    volume (GlobalTheory.CompanionTheory.MixZ.ArchEq.projCoord i Ψ '' {y | y ∈ c.e.source ∧
      (∃ z, GlobalTheory.CompanionTheory.MixZ.ArchEq.Over i y z ∧ Ψ (segre z) 0 ≠ 0) ∧ ¬ GlobalTheory.CompanionTheory.MixZ.ArchEq.IsRegAt i Ψ c y}) = 0 := by
  intro m n X _ i _ D Ψ c
  set A := {y | y ∈ c.e.source ∧ (∃ z, Over i y z ∧ Ψ (segre z) 0 ≠ 0) ∧ ¬ IsRegAt i Ψ c y} with hA
  have e : projCoord i Ψ '' A = (projCoord i Ψ ∘ c.finChart.symm) '' (c.finChart '' A) := by
    rw [Set.image_image]
    exact Set.image_congr fun y hy => by
      simp only [Function.comp_apply, c.finChart.left_inv (show y ∈ c.finChart.source from hy.1)]
  rw [e]
  refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
    (f' := fun v => (fderiv ℂ (projCoord i Ψ ∘ c.finChart.symm) v).restrictScalars ℝ) ?_ ?_
  · rintro _ ⟨y, ⟨hy, ⟨z, hz, h0⟩, -⟩, rfl⟩
    exact ((differentiableAt_projCoord i Ψ c hy hz h0).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  · rintro _ ⟨y, ⟨-, -, hc⟩, rfl⟩
    have h0 := not_not.1 hc
    have hdet : ((fderiv ℂ (projCoord i Ψ ∘ c.finChart.symm) (c.finChart y)).restrictScalars ℝ).det =
        Algebra.norm ℝ (LinearMap.det (fderiv ℂ (projCoord i Ψ ∘ c.finChart.symm) (c.finChart y) :
          (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))) :=
      LinearMap.det_restrictScalars (f := (fderiv ℂ (projCoord i Ψ ∘ c.finChart.symm) (c.finChart y) :
        (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)))
    rw [hdet, h0, Algebra.norm_complex_apply, map_zero]

end GlobalTheory.CompanionTheory.MixZ.ArchEq
end
end

section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

theorem _root_.GlobalTheory.T.clifford_highest_weight_vector : ∀ {n : ℕ} (lam : Fin n → ℤ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (A : V →ₗ[ℂ] V),
    IsCoreMod (infOf lam) E1 E2 σ A → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ),
      IsCliff c → ∀ (τ : Fin n → ℝ) (x : ι → V), x ≠ 0 → Formalism.REAL.KHighest (fun _ => true) (yF (kF E1 E2) c) τ x →
        ∑ a, (m0 lam a) ^ 2 ≤ ∑ a, (τ a + rhoV n a) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.DiracK.dirac_ineq | exact GlobalTheory.CompanionTheory.DiracK.dirac_ineq | (intros; apply GlobalTheory.CompanionTheory.DiracK.dirac_ineq <;> assumption)
end

section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

theorem _root_.GlobalTheory.T.highest_weight_of_unitary_derivative : ∀ {n : ℕ} (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (ρ : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H)) (G : Fin n → Fin n → Module.End ℂ H), (∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X → (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) → ∀ w : H, HasDerivAt (fun t : ℝ => ρ (γ t) w) (∑ a, ∑ b, X a b • G a b w) 0) → ∀ (μ : Fin n → ℝ) (v : H), v ≠ 0 → Formalism.REAL.IsWeight G μ v → ∃ ν : Fin n → ℤ, μ = wtR ν := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.WtInt.weight_integral | exact GlobalTheory.CompanionTheory.RealCountG.WtInt.weight_integral | (intros; apply GlobalTheory.CompanionTheory.RealCountG.WtInt.weight_integral <;> assumption)
end

section

open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory


theorem _root_.GlobalTheory.T.local_fibre_measure_unramified_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J → ∀ (n : ℕ) (mv : (HermR (Fv F v) σ n) → Measure (Fin n → Fin M → (Fv F v ⊗[F] E))), IsGramFibFree (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) mv → ∀ Tt : Set (Fin n → Fin M → (Fv F v ⊗[F] E)), IsCompact Tt → IsOpen Tt → Tt ⊆ {X : (Fin n → Fin M → (Fv F v ⊗[F] E)) | LinearIndependent (Fv F v ⊗[F] E) X} → (∀ Y : Set (HermR (Fv F v) σ n), MeasurableSet Y → (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (Tt ∩ gramIn (Fv F v) σ J Y) = ∫⁻ y in Y, mv y Tt ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n)) ∧ Continuous (fun y => (mv y Tt).toReal) ∧ (∀ y, mv y Tt ≠ ⊤) ∧ ∃ C : ℝ≥0, ∀ y, mv y Tt ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.AvgFree.free_fibre_masses | exact GlobalTheory.CompanionTheory.AvgFree.free_fibre_masses | (intros; apply GlobalTheory.CompanionTheory.AvgFree.free_fibre_masses <;> assumption)
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis


theorem _root_.GlobalTheory.T.parabolic_factorization_rows : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n ρ p : ℕ} (hn : ρ + p = n) (a b c d a₂ b₂ c₂ d₂ A B Dd : Matrix (Fin p) (Fin p) K),
    IsUnitary σ (blk4 0 1 (-1) 0) (blk4 A B 0 Dd) → blk4 a b c d = blk4 A B 0 Dd * blk4 a₂ b₂ c₂ d₂ →
    ∀ (ζ : Matrix (Fin ρ) (Fin ρ) K) (η : Matrix (Fin ρ) (Fin p) K), cT σ ζ = ζ →
    ∃ (ζ₂ : Matrix (Fin ρ) (Fin ρ) K) (η₂ : Matrix (Fin ρ) (Fin p) K) (T : Matrix (Fin n) (Fin n) K),
      cT σ ζ₂ = ζ₂ ∧ rowC hn η a c = T * rowC hn η₂ a₂ c₂ ∧ rowD hn σ ζ η b d = T * rowD hn σ ζ₂ η₂ b₂ d₂ := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.ClassRep.exists_change_rep | exact GlobalTheory.CompanionTheory.ZUnf.ClassRep.exists_change_rep | (intros; apply GlobalTheory.CompanionTheory.ZUnf.ClassRep.exists_change_rep <;> assumption)
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis


theorem _root_.GlobalTheory.T.rows_proportional_of_transform : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n ρ p : ℕ} (hn : ρ + p = n) (a b c d a₂ b₂ c₂ d₂ : Matrix (Fin p) (Fin p) K) (ζ ζ₂ : Matrix (Fin ρ) (Fin ρ) K)
      (η η₂ : Matrix (Fin ρ) (Fin p) K) (T : Matrix (Fin n) (Fin n) K),
    rowC hn η₂ a₂ c₂ = T * rowC hn η a c → rowD hn σ ζ₂ η₂ b₂ d₂ = T * rowD hn σ ζ η b d →
    (∃ T' : Matrix (Fin p) (Fin p) K, c₂ = T' * c ∧ d₂ = T' * d) ∧
    (IsUnit (blk4 a b c d).det → a₂ = a → b₂ = b → c₂ = c → d₂ = d → ζ₂ = ζ ∧ η₂ = η) := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.lowerRows_determine | exact GlobalTheory.CompanionTheory.ZUnf.lowerRows_determine | (intros; apply GlobalTheory.CompanionTheory.ZUnf.lowerRows_determine <;> assumption)
end
end

section

theorem GlobalTheory.T.inducedFunction_at_one :
    ∀ (n : ℕ) (lam : Fin n → ℤ) (lev : Fin n → ℕ),
      GlobalTheory.CompanionTheory.ModelS.fRaw lam lev 1 = 1 :=
  GlobalTheory.CompanionTheory.ModelS.fRaw_one
end

section

open GlobalTheory.CompanionTheory.ModelS (SmF Kf)

theorem GlobalTheory.T.eq_zero_on_unitary_of_vanish_at_one :
    ∀ (n : ℕ) (S : Submodule ℂ (SmF n)), FiniteDimensional ℂ S →
      (∀ a b : Fin n, ∀ w ∈ S, Kf a b w ∈ S) → (∀ w ∈ S, w.1 1 = 0) →
      ∀ w ∈ S, ∀ k : Matrix.unitaryGroup (Fin n) ℂ, w.1 k.1 = 0 :=
  GlobalTheory.CompanionTheory.ModelS.Sep.main
end

section

open PositivityTheory.RgBcC (infOf)
open PositivityTheory.RgBcC.RealD (IsLev)

theorem _root_.GlobalTheory.T.exists_perm_shifted_weight_eq_inf_char :
    ∀ (n : ℕ) (lam : Fin n → ℤ) (lev : Fin n → ℕ), IsLev lam lev →
      ∃ σ : Equiv.Perm (Fin n), ∀ a : Fin n,
        (GlobalTheory.CompanionTheory.ModelS.yZ lam lev a : ℂ) + ((n : ℂ) - 1) / 2 -
          ((a : ℕ) : ℂ) = infOf lam false (σ a) :=
  GlobalTheory.CompanionTheory.ModelS.ReversedBlocks.exists_perm_yZ
end

section

open PositivityTheory.RgBcC (GLs)
open PositivityTheory.RgBcC.RealD (IsLev)
open GlobalTheory.CompanionTheory.ModelS (Pb fRaw)

theorem _root_.GlobalTheory.T.inducedFunction_parabolic_equivariant :
    ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev →
      ∀ p ∈ Pb lev, ∀ g ∈ GLs n, fRaw lam lev (p * g) = fRaw lam lev p * fRaw lam lev g :=
  GlobalTheory.CompanionTheory.ModelS.FMul.fRaw_mul
end

section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.inducedFunction_smooth : ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev → GlobalTheory.CompanionTheory.ModelS.fRaw lam lev ∈ GlobalTheory.CompanionTheory.ModelS.SmF n := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.fRaw_mem_SmF | exact GlobalTheory.CompanionTheory.ModelS.fRaw_mem_SmF | (intros; apply GlobalTheory.CompanionTheory.ModelS.fRaw_mem_SmF <;> assumption)
end
