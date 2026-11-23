module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle003
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle274
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle275
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle327
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle392
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle002
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Formalism.RealPlaceAnalysis.Bundle001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.IsPhysSet
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle394
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle002
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle393
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperplaneFixerSumVanishesHarishChandraInduction
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle395
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.DualLattices.Bundle007

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.AlgConn

theorem connectedSpace_specialFibre_of_morphisms : GlobalTheory.Published.FormalAlgebraisation.Morphisms →
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (Y : Scheme.{0}) (f : Y ⟶ Spec (.of O)),
      IsProper f → ConnectedSpace ↑Y → ConnectedSpace ↑(GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialFibre f) := by
  intro H O _ _ _ hI Y f hP hY
  open GlobalTheory.SpecialConn GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits in
  have hT : Set.range (specialι f) = f ⁻¹' {IsLocalRing.closedPoint O} := by
    have h := Scheme.Pullback.range_fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))
    rw [range_residue] at h
    exact h
  open GlobalTheory.SpecialConn GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits in
  have hTn : ∀ n, Set.range (thickι f n) = f ⁻¹' {IsLocalRing.closedPoint O} := fun n => by
    have h := Scheme.Pullback.range_fst f (Spec.map (CommRingCat.ofHom (thickQ O n)))
    rw [range_thickQ] at h
    exact h
  open GlobalTheory.SpecialConn GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits in
  have hne : ∃ y : Y, f y = IsLocalRing.closedPoint O := by
    obtain ⟨y⟩ := (inferInstance : Nonempty Y)
    have hc : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
    have hsp : f y ⤳ IsLocalRing.closedPoint O :=
      (PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal (f y).2.ne_top)
    exact hsp.mem_closed hc ⟨y, rfl⟩
  open GlobalTheory.SpecialConn GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits in
  obtain ⟨y₀, hy₀⟩ := hne
  open GlobalTheory.SpecialConn GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits in
  have hy₀' : y₀ ∈ Set.range (specialι f) := by rw [hT]; exact hy₀
  obtain ⟨z₀, -⟩ := hy₀'
  haveI : Nonempty (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialFibre f) := ⟨z₀⟩
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  haveI : IsClosedImmersion (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι f) :=
    inferInstanceAs (IsClosedImmersion (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))))
  have hcl : Topology.IsClosedEmbedding (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι f) :=
    (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι f).isClosedEmbedding
  refine { toPreconnectedSpace := preconnectedSpace_iff_clopen.2 fun U hU => ?_, toNonempty := ‹_› }
  by_contra hcon
  push_neg at hcon
  obtain ⟨hU0, hU1⟩ := hcon
  obtain ⟨u, hu⟩ := hU0
  obtain ⟨u', hu'⟩ : ∃ u', u' ∉ U := by
    by_contra h
    push_neg at h
    exact hU1 (Set.eq_univ_of_forall h)
  let A := GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι f '' U
  let B := GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι f '' Uᶜ
  have hA : IsClosed A := hcl.isClosedMap _ hU.1
  have hB : IsClosed B := hcl.isClosedMap _ hU.2.isClosed_compl
  have hpt : ∀ n (z : GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialFibre f), ∃ x, GlobalTheory.SpecialConn.thickι f n x =
      GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι f z := fun n z => by
    have : GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι f z ∈ Set.range (GlobalTheory.SpecialConn.thickι f n) := by
      rw [hTn, ← hT]; exact ⟨z, rfl⟩
    exact this
  have hAB : ∀ n, (GlobalTheory.SpecialConn.thickι f n ⁻¹' A)ᶜ = GlobalTheory.SpecialConn.thickι f n ⁻¹' B := by
    intro n
    ext x
    obtain ⟨z, hz⟩ : GlobalTheory.SpecialConn.thickι f n x ∈ Set.range (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι f) := by
      rw [hT, ← hTn n]; exact ⟨x, rfl⟩
    simp only [Set.mem_compl_iff, Set.mem_preimage, A, B, Set.mem_image]
    constructor
    · intro h
      exact ⟨z, fun hzU => h ⟨z, hzU, hz⟩, hz⟩
    · rintro ⟨w, hw, hw'⟩ ⟨w', hw'U, hw''⟩
      exact hw (hcl.injective (hw''.trans hw'.symm) ▸ hw'U)
  have hclo : ∀ n, IsClopen (GlobalTheory.SpecialConn.thickι f n ⁻¹' A) := fun n =>
    ⟨hA.preimage (GlobalTheory.SpecialConn.thickι f n).continuous,
      by rw [← isClosed_compl_iff, hAB n]; exact hB.preimage (GlobalTheory.SpecialConn.thickι f n).continuous⟩
  choose h hhp hhU using fun n => GlobalTheory.T.exists_hom_specProdSelf_preimage_eq_clopen O (GlobalTheory.SpecialConn.thickFib f n)
    (GlobalTheory.SpecialConn.thickι f n ≫ f) _ (hclo n)
  haveI : IsProper (Over.mk f).hom := hP
  haveI : IsProper (Over.mk (twoπ O)).hom := isProper_twoπ O
  have hc : ∀ n, GlobalTheory.SpecialConn.thickTr f n ≫ h (n + 1) = h n := by
    intro n
    refine GlobalTheory.T.hom_ext_specProdSelf_of_basicOpen_preimage_eq O _ _ _ ?_ ?_
    · rw [Category.assoc, hhp, hhp, ← Category.assoc, GlobalTheory.SpecialConn.thickTr_ι]
    · refine TopologicalSpace.Opens.ext ?_
      rw [hhU n, Scheme.Hom.comp_preimage]
      change GlobalTheory.SpecialConn.thickTr f n ⁻¹' ((h (n + 1) ⁻¹ᵁ _ : (GlobalTheory.SpecialConn.thickFib f (n+1)).Opens) : Set _) = _
      rw [hhU (n + 1), ← Set.preimage_comp, ← GlobalTheory.SpecialConn.thickTr_ι f n]
      rfl
  obtain ⟨g, hg, -⟩ := GlobalTheory.Published.FormalAlgebraisation.Morphisms.existsUnique_thick H hI (Over.mk f)
    (Over.mk (twoπ O)) h (fun n => hhp n) hc
  have hW : IsClopen ((g.left ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : Y.Opens) : Set Y) :=
    (isClopen_basicOpen_specProdSelfFirstIdempotent O).preimage g.left.continuous
  have h0 : GlobalTheory.SpecialConn.thickι f 0 ⁻¹' ((g.left ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : Y.Opens) : Set Y) =
      GlobalTheory.SpecialConn.thickι f 0 ⁻¹' A := by
    rw [← hhU 0, ← hg 0]
    rfl
  obtain ⟨x, hx⟩ := hpt 0 u
  obtain ⟨x', hx'⟩ := hpt 0 u'
  rcases isClopen_iff.1 hW with hW0 | hW1
  · have hxA : x ∈ GlobalTheory.SpecialConn.thickι f 0 ⁻¹' A := ⟨u, hu, hx.symm⟩
    rw [← h0, hW0] at hxA
    simp at hxA
  · have hxA : x' ∈ GlobalTheory.SpecialConn.thickι f 0 ⁻¹'
        ((g.left ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : Y.Opens) : Set Y) := by
      rw [hW1]; trivial
    rw [h0] at hxA
    obtain ⟨w, hw, hw'⟩ := hxA
    exact hu' (hcl.injective (hw'.trans hx') ▸ hw)

end GlobalTheory.AlgConn
end
end

section

open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

theorem GlobalTheory.HeckeTwo.summable_eisClass_two : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F,
    Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 2 σ z) := by
  intro F _ _ _ 𝔞 𝔟 σ hσ z hz
  obtain ⟨C, hC⟩ := GlobalTheory.T.hilbertEisensteinLatticeSummand_weightTwo_bound F σ hσ z hz
  have hS := (GlobalTheory.T.summable_gaussianExtension_norm_rpow F 𝔞 𝔟 (1 + σ.re) (by linarith) (GlobalTheory.T.finite_gaussianExtension_units_quot_units F)).mul_left C
  refine Summable.of_norm_bounded hS fun c => ?_
  have hp : c.out.1 ≠ 0 := c.out.2.2.2
  have e : |((Algebra.norm ℚ (GlobalTheory.GaussExt.gEmb F c.out.1) : ℚ) : ℝ)| =
      ∏ τ : F →+* ℝ, ((τ c.out.1.1) ^ 2 + (τ c.out.1.2) ^ 2) := by
    rw [GlobalTheory.T.algebraNorm_rat_gaussianExtensionOfPair F c.out.1.1 c.out.1.2]
    exact abs_of_nonneg (Finset.prod_nonneg fun τ _ => by positivity)
  rw [e]
  exact hC _ hp
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix

theorem _root_.GlobalTheory.T.detOneSubOffDiagonalBlockGram_le_one_ball : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (X.p0 = 1 ∨ X.p0 + 1 = r) → ∀ z : V (nd X), z ∈ Om X → ∀ τ : X.Ψ, zDet X z τ ≤ 1 := by
  first | exact @GlobalTheory.IntBall.zDet_le_one | exact GlobalTheory.IntBall.zDet_le_one | (intros; apply GlobalTheory.IntBall.zDet_le_one <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.AffineOpenAgree

theorem app_restrict_eq (X W : Scheme.{0}) (N : X.Opens) (c : W ⟶ N.toScheme) (hc : ⊤ ≤ (c ≫ N.ι) ⁻¹ᵁ N) :
    (c ≫ N.ι).app N ≫ W.presheaf.map (homOfLE hc).op = N.topIso.inv ≫ c.appTop := by
  have h0 : (⊤ : N.toScheme.Opens) ≤ N.ι ⁻¹ᵁ N := by simp
  have e1 : N.topIso.inv = N.ι.app N ≫ N.toScheme.presheaf.map (homOfLE h0).op := by
    rw [Scheme.Opens.topIso_inv, Scheme.Opens.ι_app]
    change _ = X.presheaf.map _ ≫ X.presheaf.map _
    exact (congrArg X.presheaf.map (Subsingleton.elim _ _)).trans (X.presheaf.map_comp _ _)
  have e2 := c.naturality (homOfLE h0).op
  rw [e1, Scheme.Hom.comp_app]
  refine (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans ?_).symm |>.symm
  refine congrArg (N.ι.app N ≫ ·) ?_
  refine Eq.trans ?_ e2.symm
  rfl

theorem cst_pull {R : Type} [CommRing R] {X W : Scheme.{0}} (sm : X ⟶ Spec (CommRingCat.of R)) (N : X.Opens)
    (c : W ⟶ X) (hc : ⊤ ≤ c ⁻¹ᵁ N) (x : R) :
    (W.presheaf.map (homOfLE hc).op).hom ((c.app N).hom (GlobalTheory.AbLaw.cst sm N x)) =
      (c ≫ sm).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) := by
  have e := c.naturality (homOfLE (le_top : N ≤ ⊤)).op
  have e' := congrArg (fun f => (f ≫ W.presheaf.map (homOfLE hc).op).hom (sm.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x))) e
  simp only [Category.assoc, ← Functor.map_comp] at e'
  simp only [GlobalTheory.AbLaw.cst, GlobalTheory.AbLaw.rs, RingHom.comp_apply]
  refine (e'.trans ?_)
  rw [Scheme.Hom.comp_appTop]
  have : ((TopologicalSpace.Opens.map c.base).map (homOfLE (le_top : N ≤ ⊤)).op.unop).op ≫ (homOfLE hc).op = 𝟙 _ := Subsingleton.elim _ _
  rw [this]
  erw [W.presheaf.map_id, Category.comp_id]
  rfl

end GlobalTheory.AffineOpenAgree

namespace GlobalTheory
open AffineOpenAgree

theorem eq_of_agree_on_generators (R : Type) [CommRing R] (X W : Scheme.{0}) (sm : X ⟶ Spec (CommRingCat.of R))
    (N : X.Opens) (hN : IsAffineOpen N) (m : ℕ) (r : Fin m → Γ(X, N))
    (hgen : ∀ g : Γ(X, N), ∃ P Q : MvPolynomial (Fin m) R,
      IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r Q) ∧
        g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r P)
    (a b : W ⟶ X) (hab : a ≫ sm = b ≫ sm) (ha : ⊤ ≤ a ⁻¹ᵁ N) (hb : ⊤ ≤ b ⁻¹ᵁ N)
    (hr : ∀ l, (W.presheaf.map (homOfLE ha).op).hom ((a.app N).hom (r l)) =
      (W.presheaf.map (homOfLE hb).op).hom ((b.app N).hom (r l))) : a = b := by

  have hφ : ∀ g : Γ(X, N), (W.presheaf.map (homOfLE ha).op).hom ((a.app N).hom g) =
      (W.presheaf.map (homOfLE hb).op).hom ((b.app N).hom g) := by
    let φa : Γ(X, N) →+* Γ(W, ⊤) := (W.presheaf.map (homOfLE ha).op).hom.comp (a.app N).hom
    let φb : Γ(X, N) →+* Γ(W, ⊤) := (W.presheaf.map (homOfLE hb).op).hom.comp (b.app N).hom
    have hc : φa.comp (GlobalTheory.AbLaw.cst sm N) = φb.comp (GlobalTheory.AbLaw.cst sm N) := by
      ext x
      simp only [RingHom.comp_apply, φa, φb]
      rw [cst_pull sm N a ha, cst_pull sm N b hb, hab]
    have hrr : (⇑φa ∘ r) = (⇑φb ∘ r) := funext hr
    have hev : ∀ P : MvPolynomial (Fin m) R, φa (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r P) =
        φb (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r P) := by
      intro P
      rw [MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left, hc, hrr]
    intro g
    obtain ⟨P, Q, hQ, hg⟩ := hgen g
    have h1 := congrArg φa hg
    have h2 := congrArg φb hg
    rw [map_mul] at h1 h2
    have hu : IsUnit (φa (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r Q)) := hQ.map φa
    change φa g = φb g
    refine hu.mul_left_injective ?_
    simp only
    rw [h1, hev P, ← h2, ← hev Q]
  haveI : IsAffine N := hN
  have hra : Set.range a ⊆ Set.range N.ι := by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨w, rfl⟩; exact ha trivial
  have hrb : Set.range b ⊆ Set.range N.ι := by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨w, rfl⟩; exact hb trivial
  obtain ⟨a', rfl⟩ : ∃ a', a' ≫ N.ι = a := ⟨_, IsOpenImmersion.lift_fac N.ι a hra⟩
  obtain ⟨b', rfl⟩ : ∃ b', b' ≫ N.ι = b := ⟨_, IsOpenImmersion.lift_fac N.ι b hrb⟩
  refine congrArg (· ≫ N.ι) (ext_of_isAffine ?_)
  ext x
  have ea := congrArg (fun f => f.hom (N.topIso.hom.hom x)) (app_restrict_eq X W N a' ha)
  have eb := congrArg (fun f => f.hom (N.topIso.hom.hom x)) (app_restrict_eq X W N b' hb)
  have key := ea.symm.trans ((hφ _).trans eb)
  simp only [CommRingCat.comp_apply, Iso.hom_inv_id_apply] at key
  exact key

end GlobalTheory
end

section

noncomputable section

open Matrix
open GlobalTheory.PsCo.Pc1 (Mat Poly ev OmP Mode dM dZ barM sg)
open ReciprocityTheory.ChartRestriction.DS.TRGap (physDet IsPhys)

namespace GlobalTheory.PsCo.PcEF.OmegaDeterminant

variable {n : ℕ}

lemma ev_X_inl (k : Mat n) (p : Fin n × Fin n) : ev k (MvPolynomial.X (Sum.inl p)) = k p.1 p.2 := by
  simp [ev]

lemma ev_X_inr (k : Mat n) (p : Fin n × Fin n) : ev k (MvPolynomial.X (Sum.inr p)) = star (k p.1 p.2) := by
  simp [ev]

lemma OmP_apply (ε : Fin n → Bool) (x y : Mode ε) :
    OmP ε x y = (if x.1.2 = y.1.2 then MvPolynomial.X (Sum.inr (y.1.1, x.1.1)) else 0) -
      (if x.1.1 = y.1.1 then MvPolynomial.X (Sum.inr (x.1.2, y.1.2)) else 0) := by
  obtain ⟨⟨i, a⟩, hi, ha⟩ := x
  obtain ⟨⟨j, b⟩, hj, hb⟩ := y
  simp only [OmP, dM, dZ, MvPolynomial.mkDerivation_X, Sum.elim_inr, barM, Matrix.single_apply]
  simp [ite_and, mul_ite, sg]
  simp only at hi ha hj hb
  rcases eq_or_ne a b with rfl | hab <;> rcases eq_or_ne i j with rfl | hij <;>
    simp [apply_ite MvPolynomial.C, mul_ite, ite_mul, Finset.sum_add_distrib, sub_eq_add_neg, *]

lemma ev_OmP (ε : Fin n → Bool) (k : Mat n) (x y : Mode ε) :
    ev k (OmP ε x y) = (if x.1.2 = y.1.2 then star (k y.1.1 x.1.1) else 0) -
      (if x.1.1 = y.1.1 then star (k x.1.2 y.1.2) else 0) := by
  rw [OmP_apply, map_sub, apply_ite (ev k), apply_ite (ev k), ev_X_inr, ev_X_inr, map_zero]

lemma K_block {ε : Fin n → Bool} {k : Mat n} (hk : k ∈ Formalism.REAL.Kset ε) {i j : Fin n} (h : ε i ≠ ε j) :
    k i j = 0 := by
  have := congrFun (congrFun hk.2 i) j
  simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at this
  cases hi : ε i <;> cases hj : ε j <;> simp only [hi, hj, ↓reduceIte, Bool.false_eq_true] at this h
  · exact absurd rfl h
  · linear_combination (1 / 2 : ℂ) * this
  · linear_combination (-1 / 2 : ℂ) * this
  · exact absurd rfl h

lemma K_unit {ε : Fin n → Bool} {k : Mat n} (hk : k ∈ Formalism.REAL.Kset ε) (i l : Fin n) :
    ∑ j, k i j * star (k l j) = if i = l then 1 else 0 := by
  have := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hk.1) i) l
  simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using this

lemma sum_mode (ε : Fin n → Bool) (f : Fin n × Fin n → ℂ) :
    ∑ y : Mode ε, f y.1 = ∑ j, ∑ b, if ε j = true ∧ ε b = false then f (j, b) else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun p : Fin n × Fin n => ε p.1 = true ∧ ε p.2 = false)
    (by simp) f, Finset.sum_filter, Fintype.sum_prod_type]

lemma entry {ε : Fin n → Bool} {k : Mat n} (hk : k ∈ Formalism.REAL.Kset ε) (x z : Mode ε) :
    ∑ y : Mode ε, (if x.1.2 = y.1.2 then k x.1.1 y.1.1 else 0) *
      ((if y.1.2 = z.1.2 then star (k z.1.1 y.1.1) else 0) -
        (if y.1.1 = z.1.1 then star (k y.1.2 z.1.2) else 0)) =
    (if x = z then 1 else 0) - k x.1.1 z.1.1 * star (k x.1.2 z.1.2) := by
  obtain ⟨⟨i, a⟩, hi, ha⟩ := x
  obtain ⟨⟨l, d⟩, hl, hd⟩ := z
  have hs := sum_mode ε (fun p => (if a = p.2 then k i p.1 else 0) *
      ((if p.2 = d then star (k l p.1) else 0) - (if p.1 = l then star (k p.2 d) else 0)))
  simp only at hs ⊢
  rw [hs]
  have h1 : ∀ j, (∑ b, if ε j = true ∧ ε b = false then (if a = b then k i j else 0) *
      ((if b = d then star (k l j) else 0) - (if j = l then star (k b d) else 0)) else 0) =
      k i j * ((if a = d then star (k l j) else 0) - (if j = l then star (k a d) else 0)) := by
    intro j
    rw [Finset.sum_eq_single a]
    · by_cases hj : ε j = true
      · simp [hj, ha]
      · have : k i j = 0 := K_block hk (by rw [hi]; exact fun h => hj h.symm)
        simp [hj, this]
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  rw [Finset.sum_congr rfl (fun j _ => h1 j)]
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  by_cases had : a = d
  · subst had
    simp only [if_true, K_unit hk]
    by_cases hil : i = l
    · subst hil; simp
    · simp [hil]
  · simp [had]

def AP (ε : Fin n → Bool) : Matrix (Mode ε) (Mode ε) (Poly n) :=
  fun x y => if x.1.2 = y.1.2 then MvPolynomial.X (Sum.inl (x.1.1, y.1.1)) else 0

end OmegaDeterminant

open OmegaDeterminant in
theorem modeMatrixDet_eq_adjointDet :
    ∀ (n : ℕ) (ε : Fin n → Bool), ∃ Q : Poly n, ∀ k ∈ Formalism.REAL.Kset ε,
      ev k Q * ev k (OmP ε).det = physDet ε k := by
  intro n ε
  refine ⟨(AP ε).det, fun k hk => ?_⟩
  let e : Mode ε ≃ {x : Fin n × Fin n // IsPhys ε x} :=
    Equiv.subtypeEquivRight (p := fun x : Fin n × Fin n => ε x.1 = true ∧ ε x.2 = false) (fun _ => Iff.rfl)
  have key : (ev k).mapMatrix (AP ε) * (ev k).mapMatrix (OmP ε) =
      (Matrix.of fun x y : {x : Fin n × Fin n // IsPhys ε x} =>
        (if x = y then (1 : ℂ) else 0) - k x.1.1 y.1.1 * star (k x.1.2 y.1.2)).submatrix e e := by
    ext x z
    rw [Matrix.mul_apply]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, AP, ev_OmP, Matrix.submatrix_apply, Matrix.of_apply,
      apply_ite (ev k), ev_X_inl, map_zero, e, EmbeddingLike.apply_eq_iff_eq]
    exact entry hk x z
  rw [RingHom.map_det, RingHom.map_det, ← Matrix.det_mul, key, Matrix.det_submatrix_equiv_self]
  rfl

end GlobalTheory.PsCo.PcEF
end
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_conj_eisensteinPolynomial_levelOne : ∀ (g : ℂ ≃+* ℂ) (w N : ℕ) (F F' : ℍ → ℂ), 0 < N → (∀ γ : SL(2, ℤ), F ∣[(w : ℤ)] γ = F) → QConj g N F F' → ∃ (s : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ), (∀ p ∈ s, 4 * p.1 + 6 * p.2 = w) ∧ (∀ τ, F τ = ∑ p ∈ s, c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2)) ∧ ∀ τ, F' τ = ∑ p ∈ s, g (c p) * (E₄ τ ^ p.1 * E₆ τ ^ p.2) := by
  first | exact @GlobalTheory.QFam.levelPoly_conj | exact GlobalTheory.QFam.levelPoly_conj | (intros; apply GlobalTheory.QFam.levelPoly_conj <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_eq_discriminant_pow_mul_eval_jInvariant : ∀ (R : Subring ℂ) (N w : ℕ) (f : ℍ → ℂ), 0 < N → (∀ γ : SL(2, ℤ), f ∣[(12 * w : ℤ)] γ = f) → QAll (· ∈ R) N f → ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ R) ∧ ∀ τ, f τ = DD τ ^ w * P.eval (jT τ) := by
  first | exact @GlobalTheory.QFam.exists_eq_DD_pow_mul_eval_jT | exact GlobalTheory.QFam.exists_eq_DD_pow_mul_eval_jT | (intros; apply GlobalTheory.QFam.exists_eq_DD_pow_mul_eval_jT <;> assumption)
end

section

open ReciprocityTheory.PGsh.Up GlobalTheory.Sandwich Matrix

theorem _root_.GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ ε : PreTilt O p, IsPrimitiveRoot (root ε).untilt p → IsDomain (Ainf p O) ∧ IsLocalRing (Ainf p O) ∧ RingHom.ker (WittVector.fontaineTheta O p) = Ideal.span {xi ε} ∧ Function.Surjective (WittVector.fontaineTheta O p) ∧ WittVector.fontaineTheta O p (nu ε) ≠ 0 ∧ xi ε ≠ 0 ∧ (∀ x : Ainf p O, x ≠ 0 → ∃ (N : ℕ) (y : Ainf p O), x = xi ε ^ N * y ∧ WittVector.fontaineTheta O p y ≠ 0) := by
  first | exact @GlobalTheory.AinfXi.ainf_local_xi_order | exact GlobalTheory.AinfXi.ainf_local_xi_order | (intros; apply GlobalTheory.AinfXi.ainf_local_xi_order <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.hyperplaneFixerSumVanishes_harishChandraInduction : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ), n = a + b → ∀ (A : GL (Fin a) F → ℂ) (B : GL (Fin b) F → ℂ), IsChar ℂ ℂ A → IsChar ℂ ℂ B → HFree A → HFree B → HFree (hc a b A B n) := by
  first | (exact @GlobalTheory.Shin.FreeHc.hfree_hc) | (exact GlobalTheory.Shin.FreeHc.hfree_hc) | (intros; apply GlobalTheory.Shin.FreeHc.hfree_hc  <;> assumption)
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.functionFieldPlace_sum_order_eq_finrank : ∀ (k F E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k F →
  ∀ ρ : Place k E → Place k F, IsRes ρ → ∀ (v : Place k F) (π : F), π ≠ 0 → ord v π = 1 → {p | ρ p = v}.Finite ∧ ∑ᶠ p ∈ {p | ρ p = v}, ord p (algebraMap F E π) = Module.finrank F E := by
  first | exact @GlobalTheory.Nef.FundId.sum_ord_eq_finrank | exact GlobalTheory.Nef.FundId.sum_ord_eq_finrank | (intros; apply GlobalTheory.Nef.FundId.sum_ord_eq_finrank <;> assumption)
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.functionFieldPlace_isDVR_and_residue_eq_ground : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ v : Place k F, IsDiscreteValuationRing v.O ∧ ∀ x : F, v.1 x ≤ 1 → ∃ c : k, v.1 (x - algebraMap k F c) < 1 := by
  first | exact @GlobalTheory.Nef.place_isDVR_residue | exact GlobalTheory.Nef.place_isDVR_residue | (intros; apply GlobalTheory.Nef.place_isDVR_residue <;> assumption)
end
