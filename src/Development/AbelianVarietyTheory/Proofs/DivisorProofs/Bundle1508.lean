module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1418
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1417
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle233
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1382
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1428
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle324
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1427
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1326

@[expose] public section

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open scoped TensorProduct

namespace GlobalTheory.GenericEtale

theorem trdeg_eq (k K A B : Type) [CommRing k] [IsDomain k] [Field K] [Algebra k K]
    [IsFractionRing k K] [CommRing A] [Algebra k A] [FaithfulSMul k A] [CommRing B] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] [Algebra.IsAlgebraic A B] [Algebra K B] [Algebra k B]
    [IsScalarTower k K B] [IsScalarTower k A B] : Algebra.trdeg K B = Algebra.trdeg k A := by
  have : Nontrivial A := (algebraMap A B).domain_nontrivial
  have : Algebra.IsAlgebraic k K := IsLocalization.isAlgebraic K (nonZeroDivisors k)
  have h₁ := trdeg_add_eq k K (A := B)
  have h₂ := trdeg_add_eq k A (A := B)
  rw [trdeg_eq_zero, zero_add] at h₁
  rw [trdeg_eq_zero (R := A), add_zero] at h₂
  rw [h₁, h₂]

theorem formallySmooth_fractionField (k A L : Type) [CommRing k] [IsDomain k] [CharZero k]
    [CommRing A] [IsDomain A] [Algebra k A] [FaithfulSMul k A] [Algebra.FiniteType k A] [Field L]
    [Algebra A L] [IsFractionRing A L] [Algebra k L] [IsScalarTower k A L] :
    Algebra.FormallySmooth k L ∧ Module.rank L Ω[L⁄k] = Algebra.trdeg k A := by
  let K := FractionRing k
  have hinj : Function.Injective (algebraMap k L) := by
    rw [IsScalarTower.algebraMap_eq k A L]
    exact (IsFractionRing.injective A L).comp (FaithfulSMul.algebraMap_injective k A)
  let : Algebra K L := (IsFractionRing.lift (K := K) hinj).toAlgebra
  have : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq fun a =>
    (IsFractionRing.lift_algebraMap (K := K) hinj a).symm
  have : Algebra.EssFiniteType A L := .of_isLocalization L (nonZeroDivisors A)
  have : Algebra.EssFiniteType k L := .comp k A L
  have : Algebra.EssFiniteType K L := .of_comp k K L
  have : Algebra.FormallySmooth K L := Algebra.FormallySmooth.of_perfectField
  have : Algebra.FormallyEtale k K := .of_isLocalization (nonZeroDivisors k)
  have : Algebra.IsAlgebraic A L := IsLocalization.isAlgebraic L (nonZeroDivisors A)
  refine ⟨.comp k K L, ?_⟩
  have hb : Function.Bijective (KaehlerDifferential.map k K L L) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, KaehlerDifferential.map_surjective k K L⟩
    obtain ⟨y, rfl⟩ := (KaehlerDifferential.exact_mapBaseChange_map k K L x).1 hx
    rw [Subsingleton.elim y 0, map_zero]
  rw [(LinearEquiv.ofBijective _ hb).rank_eq, rank_kaehler_eq_trdeg, trdeg_eq k K A L]

theorem exists_away (k A : Type) [CommRing k] [IsDomain k] [CharZero k] [IsNoetherianRing k]
    [CommRing A] [IsDomain A] [Algebra k A] [FaithfulSMul k A] [Algebra.FiniteType k A] {D : ℕ}
    (hd : Algebra.trdeg k A = D) :
    ∃ f : A, f ≠ 0 ∧ Algebra.IsStandardSmoothOfRelativeDimension D k (Localization.Away f) := by
  have : Algebra.FinitePresentation k A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  let L := Localization.AtPrime (⊥ : Ideal A)
  have : IsFractionRing A L :=
    (congrArg (fun M : Submonoid A => IsLocalization M L) (Ideal.primeCompl_bot (α := A))).mp
      inferInstance
  have hL : IsField L :=
    (FractionRing.algEquiv A L).symm.toMulEquiv.isField (Field.toIsField (FractionRing A))
  let : Field L := hL.toField
  obtain ⟨h₁, h₂⟩ := formallySmooth_fractionField k A L
  have : Algebra.IsSmoothAt k (⊥ : Ideal A) := h₁
  obtain ⟨f, hf, h⟩ := exists_isStandardSmoothOfRelativeDimension_of_isSmoothAt k (⊥ : Ideal A)
    (d := D) (Module.finrank_eq_of_rank_eq (h₂.trans hd))
  exact ⟨f, hf, h⟩

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}


attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem trdeg_chart (h : IsArithVar p D) {A : Type} [CommRing A] [Algebra k A]
    (i : Sp A ⟶ X) [IsOpenImmersion i] (hi : i ≫ p = spMap (algebraMap k A)) [Nontrivial A] :
    Algebra.trdeg k A = D := by
  have := h.isDomain
  let K := FractionRing k
  obtain ⟨_, _, _⟩ := RegGenSmooth.chart_props h i hi
  obtain ⟨_, hd⟩ := RegGenSmooth.ringKrullDim_chart h
    (IsPullback.of_hasPullback p (spMap (algebraMap k K))) i hi
  have := IsLocalization.tensorRight (S := A) K (nonZeroDivisors k)
  have hle : Algebra.algebraMapSubmonoid A (nonZeroDivisors k) ≤ nonZeroDivisors A :=
    Submonoid.map_le_iff_le_comap.mpr fun x hx ↦ mem_nonZeroDivisors_of_ne_zero
      (by simpa using nonZeroDivisors.ne_zero hx)
  have : FaithfulSMul A (K ⊗[k] A) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsLocalization.injective _ hle)
  have : Algebra.IsAlgebraic A (K ⊗[k] A) :=
    IsLocalization.isAlgebraic _ (Algebra.algebraMapSubmonoid A (nonZeroDivisors k))
  obtain ⟨d, hd₁, hd₂⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq K (K ⊗[k] A)
  have e : d = D := by exact_mod_cast hd₁.symm.trans hd
  rw [← trdeg_eq k K A (K ⊗[k] A), hd₂, e]

theorem exists_etale_coords [IsIntegral X] (h : IsArithVar p D) :
    ∃ (U : X.Opens) (x : Fin D → Γ(X, U)), IsAffineOpen U ∧ genericPoint X ∈ U ∧
      (MvPolynomial.eval₂Hom (algX p U) x).Etale := by
  have := h.isDomain
  have := h.charZero_base
  have := h.isNoetherianRing
  obtain ⟨A, _, _, i, _, a, -, hi⟩ := exists_affine_chart_over p (genericPoint X)
  have : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨a⟩
  obtain ⟨_, _, _⟩ := RegGenSmooth.chart_props h i hi
  obtain ⟨f, hf, hs⟩ := exists_away k A (trdeg_chart h i hi)
  let B := Localization.Away f
  have : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers f) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  have : IsOpenImmersion (spMap (algebraMap A B)) := IsOpenImmersion.of_isLocalization f
  let j : Sp B ⟶ X := spMap (algebraMap A B) ≫ i
  have hj : j ≫ p = spMap (algebraMap k B) := by
    rw [Category.assoc, hi, IsScalarTower.algebraMap_eq k A B, ← Spec.map_comp]
    rfl
  have h₁ : SmoothOfRelativeDimension D (j ≫ p) := by
    rw [hj]
    refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension D)).mpr ?_
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
      ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap D).mpr hs)
  have h₂ : SmoothOfRelativeDimension D (j.opensRange.ι ≫ p) := by
    rw [← j.isoOpensRange_inv_comp, Category.assoc]
    have : SmoothOfRelativeDimension (0 + D) (j.isoOpensRange.inv ≫ j ≫ p) := inferInstance
    rwa [zero_add] at this
  refine ModelCharts.exists_etale_coords_of_opens p D j.opensRange ?_
  exact ⟨genericPoint _, genericPoint_eq_of_isOpenImmersion j⟩

end GlobalTheory.GenericEtale
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.HSAmp

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.KrullZero

theorem coheight_le_one {Y : Scheme.{0}} [IsLocallyNoetherian Y] {N : LB Y} (hN : N.IsLB) (t : N.Sec) (w : Y)
    (hw : w ∉ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t)
    (hgen : ∀ y : Y, w < y → y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t) : Order.coheight w ≤ 1 := by
  obtain ⟨k, hk⟩ := exists_chart hN w
  obtain ⟨V, hV, hwV, hle⟩ := exists_isAffineOpen_mem_and_subset hk
  have hle' : V ≤ N.U k := hle
  set g : Γ(Y, V) := Y.presheaf.map (homOfLE hle').op (t.f k) with hg
  have hbo : Y.basicOpen g = V ⊓ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t := by
    rw [hg, Scheme.basicOpen_res, ← GlobalTheory.nonzeroLocus_inf_chart, inf_comm _ (N.U k), ← inf_assoc,
      inf_eq_left.2 hle']
  obtain ⟨P, hP⟩ : ∃ P : PrimeSpectrum Γ(Y, V), hV.fromSpec P = w := by
    have : w ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hwV
    exact this
  haveI : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hmemb : ∀ Q : PrimeSpectrum Γ(Y, V), g ∈ Q.asIdeal ↔ hV.fromSpec Q ∉ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t := by
    intro Q
    have h1 : Q ∈ PrimeSpectrum.basicOpen g ↔ hV.fromSpec Q ∈ Y.basicOpen g := by
      rw [← hV.fromSpec_preimage_basicOpen]; rfl
    have h2 : hV.fromSpec Q ∈ V := by
      have := Set.mem_range_self (f := hV.fromSpec) Q
      rwa [hV.range_fromSpec] at this
    rw [hbo] at h1
    constructor
    · intro hgQ hQ
      exact (PrimeSpectrum.mem_basicOpen _ _).1 (h1.2 ⟨h2, hQ⟩) hgQ
    · intro hQ
      by_contra hgQ
      exact hQ (h1.1 ((PrimeSpectrum.mem_basicOpen _ _).2 hgQ)).2
  have hgP : g ∈ P.asIdeal := (hmemb P).2 (hP ▸ hw)
  have hmin : P.asIdeal ∈ (Ideal.span {g}).minimalPrimes := by
    refine ⟨⟨P.isPrime, (Ideal.span_singleton_le_iff_mem _).mpr hgP⟩, fun Q hQ hQP => ?_⟩
    have hgQ : g ∈ Q := (Ideal.span_singleton_le_iff_mem _).mp hQ.2
    by_contra hne
    let Q' : PrimeSpectrum Γ(Y, V) := ⟨Q, hQ.1⟩
    have hsp : Q' ⤳ P := (PrimeSpectrum.le_iff_specializes Q' P).1 hQP
    have hsp' : hV.fromSpec Q' ⤳ w := hP ▸ hsp.map hV.fromSpec.continuous
    have hneq : hV.fromSpec Q' ≠ w := by
      rw [← hP]
      intro h
      have := hV.fromSpec.isOpenEmbedding.injective h
      exact hne (by rw [← this])
    have hlt : w < hV.fromSpec Q' := lt_of_le_not_ge (show w ≤ hV.fromSpec Q' from hsp') fun h => hneq (hsp'.antisymm h).eq
    exact (hmemb Q').1 hgQ (hgen _ hlt)
  have hh : P.asIdeal.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  let x : Spec Γ(Y, V) := P
  have eS := (asIso (hV.fromSpec.stalkMap x) ≪≫ Spec.stalkIso Γ(Y, V) x).commRingCatIsoToRingEquiv
  have hPh : (P.asIdeal.height : WithBot ℕ∞) = Order.coheight w := by
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height P.asIdeal (Localization.AtPrime P.asIdeal),
      ← ringKrullDim_eq_of_ringEquiv eS, ← ringKrullDim_stalk_eq_coheight, hP]
  have : ((Order.coheight w : ℕ∞) : WithBot ℕ∞) ≤ ((1 : ℕ∞) : WithBot ℕ∞) := by
    rw [← hPh]; exact_mod_cast hh
  exact_mod_cast this

end GlobalTheory.KrullZero

namespace GlobalTheory.KrullZero


open GlobalTheory.MixHt in
theorem exists_irreducible_zero : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (M : LB X) (s : M.Sec) (C : Set X), M.IsLB → IsIrreducible C → IsClosed C →
    (C ∩ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s : Set X)).Nonempty → ¬ C ⊆ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s : Set X) →
    ∃ C' : Set X, IsIrreducible C' ∧ IsClosed C' ∧ C' ⊆ C \ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s : Set X) ∧
      topologicalKrullDim C ≤ topologicalKrullDim C' + 1 := by
  intro k _ X _ p D hX M s C hM hC hCc hmeet hnot
  set Z := ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s with hZ
  have hamb : IsAmb p := isAmb_of_isArithVar hX
  haveI : IsNoetherian X := hamb.isNoetherian
  obtain ⟨η, hη⟩ := QuasiSober.sober hC hCc
  have hηC : closure ({η} : Set X) = C := hη
  let i := cloι η
  have hambY : IsAmb (i ≫ p) := hamb.sub i
  haveI : IsNoetherian (clo η) := hambY.isNoetherian
  have hgi : i (genericPoint (clo η)) = η := cloι_genericPoint η
  have hWm : ∀ y : clo η, y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (GlobalTheory.secPull s i) ↔ i y ∈ Z := fun y => by
    rw [GlobalTheory.nonzeroLocus_secPull]; rfl
  have basic := hasDim_basic k X p hamb
  have basicY := hasDim_basic k (clo η) (i ≫ p) hambY
  obtain ⟨m, hm⟩ := basicY.1
  obtain ⟨d, -, hd⟩ := hm (genericPoint (clo η))
  have hdY : topologicalKrullDim (clo η) = d := (basicY.2.2.2.2.2 (clo η) d).1 hd
  have hdC : topologicalKrullDim C = d := by
    have h := (basic.2.2.2.2.1 (clo η) i (genericPoint (clo η)) d).2 hd
    rw [hgi] at h
    rw [← hηC]; exact h

  have hrange : C ⊆ Set.range i := by
    rw [← hηC]
    refine closure_minimal ?_ i.isClosedEmbedding.isClosed_range
    rintro _ rfl
    exact ⟨_, hgi⟩

  obtain ⟨x, hxC, hxZ⟩ := Set.not_subset.1 hnot
  obtain ⟨y₀, rfl⟩ := hrange hxC
  have hηZ : η ∈ Z := by
    obtain ⟨x', hx'C, hx'Z⟩ := hmeet
    rw [← hηC] at hx'C
    exact (specializes_iff_mem_closure.2 hx'C).mem_open Z.isOpen hx'Z

  obtain ⟨w, hw, hwmin⟩ := (InvImage.wf (Order.coheight : clo η → ℕ∞) wellFounded_lt).has_min
    {y | y ∉ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (GlobalTheory.secPull s i)} ⟨y₀, fun h => hxZ ((hWm y₀).1 h)⟩
  obtain ⟨e, -, he⟩ := hm w
  have hce : Order.coheight w + (e : ℕ∞) = d := GlobalTheory.DimCoheight.coheight_add_eq k (clo η) (i ≫ p) hambY d hdY w e he
  have hfin : Order.coheight w < ⊤ := by
    refine lt_of_le_of_lt (le_self_add) (hce ▸ ENat.natCast_lt_top d)
  have hgen : ∀ y : clo η, w < y → y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (GlobalTheory.secPull s i) := by
    intro y hlt
    by_contra hy
    exact hwmin y hy (Order.coheight_strictAnti hlt ((Order.coheight_anti hlt.le).trans_lt hfin))
  have h1 : Order.coheight w ≤ 1 := coheight_le_one (LB.isLB_pull hM i) (GlobalTheory.secPull s i) w hw hgen
  have h0 : Order.coheight w ≠ 0 := by
    intro h0
    have hmax : IsMax w := Order.coheight_eq_zero.1 h0
    have hsp : genericPoint (clo η) ⤳ w := genericPoint_specializes w
    have hle : genericPoint (clo η) ≤ w := hmax (show w ≤ genericPoint (clo η) from hsp)
    have heq : w = genericPoint (clo η) := (hsp.antisymm hle).eq.symm
    have hgW := (hWm (genericPoint (clo η))).2 (by rw [hgi]; exact hηZ)
    rw [← heq] at hgW
    exact hw hgW
  have hc1 : Order.coheight w = 1 := le_antisymm h1 (Order.one_le_iff_ne_zero.2 h0)
  rw [hc1] at hce
  have hde : d = e + 1 := by
    have : ((e + 1 : ℕ) : ℕ∞) = d := by push_cast; rw [← hce, add_comm]
    exact_mod_cast this.symm
  refine ⟨closure {i w}, isIrreducible_singleton.closure, isClosed_closure, ?_, ?_⟩
  · refine closure_minimal ?_ (hCc.sdiff Z.isOpen)
    rintro _ rfl
    refine ⟨?_, fun h => hw ((hWm w).2 h)⟩
    have hs := (genericPoint_specializes w).map i.continuous
    rw [hgi] at hs
    rw [← hηC]
    exact specializes_iff_mem_closure.1 hs
  · have hC' : topologicalKrullDim (closure ({i w} : Set X)) = e := (basic.2.2.2.2.1 (clo η) i w e).2 he
    rw [hdC, hC', hde]
    push_cast
    exact le_rfl

end GlobalTheory.KrullZero
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocModelProj


open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw in
theorem exists_projective_openImmersion (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.FiniteType ℂ S] :
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (p : Y ⟶ Sp ℂ) (j : Sp S ⟶ Y),
      IsProjOver p ∧ IsOpenImmersion j ∧ LocallyOfFiniteType p ∧ j ≫ p = spMap (algebraMap ℂ S) := by
  have : LocallyOfFiniteType (spMap (algebraMap ℂ S)) :=
    HasRingHomProperty.Spec_iff.2 (RingHom.finiteType_algebraMap.2 inferInstance)
  obtain ⟨N, i, _, _, e⟩ := (isAmpleLB_of_isAffine (LB.isLB_triv (Sp S))).isQProjOver (spMap (algebraMap ℂ S))
  have := isProper_str ℂ N
  exact ⟨i.image, isIntegral_image i, i.imageι ≫ PSpace.str ℂ N, i.toImage, ⟨N, i.imageι, inferInstance, rfl⟩,
    inferInstance, inferInstance, by rw [i.toImage_imageι_assoc, e]⟩

theorem topologicalKrullDim_eq_of_openImmersion (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.FiniteType ℂ S] (Y : Scheme.{0}) [IsIntegral Y]
    (p : Y ⟶ Sp ℂ) [LocallyOfFiniteType p] (j : Sp S ⟶ Y) [IsOpenImmersion j] (n : ℕ) (h : Algebra.trdeg ℂ S = n) :
    topologicalKrullDim Y = n := by
  have : Nonempty (Sp S) := inferInstance
  rw [← GlobalTheory.OpenImmDim.topologicalKrullDim_eq_of_isOpenImmersion ℂ Y (Sp S) p j]
  change topologicalKrullDim (PrimeSpectrum S) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, GlobalTheory.ringKrullDim_eq_of_trdeg_eq ℂ S h]

theorem exists_projective_of_isLocModel : ∀ (L : Type) [Field L] (c : ℂ →+* L) (R : Subring L) (n : ℕ) (x : Fin n → L), IsLocModel c R → TrBasis c x →
  ∃ (Y : AlgebraicGeometry.Scheme.{0}) (_ : AlgebraicGeometry.IsIntegral Y) (p : Y ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) (e : Y.functionField ≃+* L) (y : Y),
    IsProjOver p ∧ topologicalKrullDim Y = n ∧ (∀ a, e (GlobalTheory.Cartier.constFn p a) = c a) ∧ (locRing y).map e.toRingHom = R := by
  intro L _ c R n x hR hx
  obtain ⟨S, hS, q, hq, hft, hfrac, hmem⟩ := GlobalTheory.T.exists_finiteType_localization_same_fractionField L c R hR
  letI : Algebra ℂ S := (c.codRestrict S hS).toAlgebra
  letI : Algebra S L := S.subtype.toAlgebra
  letI : Algebra ℂ L := c.toAlgebra
  haveI : IsScalarTower ℂ S L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.FiniteType ℂ S := hft
  haveI : FaithfulSMul S L := (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  haveI : IsFractionRing S L := by
    refine IsFractionRing.of_field S L fun f => ?_
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hfrac f
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    change f = a / b
    rw [← e, mul_div_cancel_right₀ _ hb0]
  have htr : Algebra.trdeg ℂ S = n := by
    have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hx
    have : Algebra.IsAlgebraic S L := IsLocalization.isAlgebraic L (nonZeroDivisors S)
    rw [← trdeg_add_eq ℂ S (A := L), trdeg_eq_zero (R := S) (A := L), add_zero] at h2
    rw [← h2, Cardinal.mk_fin]
  obtain ⟨Y, hY, p, j, hproj, hj, hlft, hjp⟩ := exists_projective_openImmersion S
  obtain ⟨e, hc, hloc⟩ := GlobalTheory.T.exists_functionFieldEquiv_openImmersionSpec S Y p j hjp
  let e2 : FractionRing S ≃ₐ[S] L := IsLocalization.algEquiv (nonZeroDivisors S) (FractionRing S) L
  refine ⟨Y, hY, p, e.trans e2.toRingEquiv, j.base ⟨q, hq⟩, hproj, topologicalKrullDim_eq_of_openImmersion S Y p j n htr, fun a => ?_, ?_⟩
  · change e2 (e (GlobalTheory.Cartier.constFn p a)) = c a
    rw [hc, IsScalarTower.algebraMap_apply ℂ S (FractionRing S), AlgEquiv.commutes]
    rfl
  · ext g
    have h1 : g ∈ (locRing (j.base ⟨q, hq⟩)).map (e.trans e2.toRingEquiv).toRingHom ↔
        e2.symm g ∈ (locRing (j.base ⟨q, hq⟩)).map e.toRingHom := by
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u, hu, by simp⟩
      · rintro ⟨u, hu, hu'⟩
        refine ⟨u, hu, ?_⟩
        change e2 (e u) = g
        rw [show e u = e2.symm g from hu', AlgEquiv.apply_symm_apply]
    rw [h1, hloc ⟨q, hq⟩, hmem g]
    refine exists₂_congr fun a b => and_congr_right fun _ => ?_
    constructor
    · intro h
      have := congrArg e2 h
      rwa [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.commutes, AlgEquiv.commutes] at this
    · intro h
      apply e2.injective
      rw [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.commutes, AlgEquiv.commutes]
      exact h

end GlobalTheory.LocModelProj
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.graphLocalRing_regular_params_and_dim : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K]
  [Algebra ℂ κ'] [Algebra ℂ L] [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L]
  [IsFractionRing (K ⊗[ℂ] κ') L] (σ : K →ₐ[ℂ] κ') (n : ℕ) (x : Fin n → K),
  Algebra.EssFiniteType ℂ K → Algebra.EssFiniteType ℂ κ' → TrBasis (algebraMap ℂ K) x →
  IsLocalRing.maximalIdeal (GlobalTheory.DiagLoc.loc L σ) =
      Ideal.span (Set.range fun i => GlobalTheory.DiagLoc.toLoc L σ (x i ⊗ₜ[ℂ] 1 - 1 ⊗ₜ[ℂ] σ (x i))) ∧
    ringKrullDim (GlobalTheory.DiagLoc.loc L σ) = n := by
  first | exact @GlobalTheory.DiagLoc.maximalIdeal_eq_span_and_ringKrullDim | exact GlobalTheory.DiagLoc.maximalIdeal_eq_span_and_ringKrullDim | (intros; apply GlobalTheory.DiagLoc.maximalIdeal_eq_span_and_ringKrullDim <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isLocalRingOfVarietyPoint_tensorGraphLocalization : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ']
  [Algebra ℂ L] [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L]
  [IsFractionRing (K ⊗[ℂ] κ') L] (σ : K →ₐ[ℂ] κ'),
  Algebra.EssFiniteType ℂ K → Algebra.EssFiniteType ℂ κ' →
  IsLocModel (algebraMap ℂ L) (GlobalTheory.DiagLoc.loc L σ) := by
  first | exact @GlobalTheory.DiagLoc.isLocModel_loc | exact GlobalTheory.DiagLoc.isLocModel_loc | (intros; apply GlobalTheory.DiagLoc.isLocModel_loc <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

theorem _root_.GlobalTheory.T.transcendenceBasis_uniformiser_cons_residual_lifts : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (S : Place cL) (ψ : S.ring →+* K) (f : S.ring) (w : Fin n → S.ring), Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) → Irreducible f → TrBasis cK (fun i => ψ (w i)) → TrBasis cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) ∧ (fun ω => @dite ℤ (∃ a, S.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L)) = 0 ∧ S.ord (f : L) = 1 ∧ ∀ g : S.ring, ψ g ≠ 0 → S.ord (g : L) = 0 := by
  first | exact @GlobalTheory.FieldPair.trBasis_uniformiser_cons | exact GlobalTheory.FieldPair.trBasis_uniformiser_cons | (intros; apply GlobalTheory.FieldPair.trBasis_uniformiser_cons <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_trBasis_in_image_of_fractionField : ∀ {K κ : Type} [Field K] [Field κ] [Algebra ℂ κ] (k : ℕ) (R : Subring K) (π : R →+* κ),
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  ∃ zR : Fin k → R, TrBasis (algebraMap ℂ κ) (fun i => π (zR i)) := by
  first | exact @GlobalTheory.GraphLocal.exists_trBasis_lift | exact GlobalTheory.GraphLocal.exists_trBasis_lift | (intros; apply GlobalTheory.GraphLocal.exists_trBasis_lift <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.eq_unit_mul_zpow_regularLocalModel_dimTwo : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel cL Q) (t u : Q),
  Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
  ∀ E : Place cL, E.IsPrimeOf Q → E.ord (u : L) = 1 →
  ∀ G : L, G ≠ 0 → (∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ E.ring → P.ord G = 0) →
  ∃ q : Q, IsUnit q ∧ G = (q : L) * (u : L) ^ E.ord G := by
  first | exact @GlobalTheory.FieldPair.AdjUnit.eq_unit_mul_zpow | exact GlobalTheory.FieldPair.AdjUnit.eq_unit_mul_zpow | (intros; apply GlobalTheory.FieldPair.AdjUnit.eq_unit_mul_zpow <;> assumption)
end
