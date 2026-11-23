module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.PosIndexMapEqCardOfCongrDiagonal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle074
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2612
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2532
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2600
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalModificationKsIsoSec
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle028
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2613
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.LandherrStIffLandherr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2614
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
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2596
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle628

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IsoNegIdx

open ReciprocityTheory.ChartRestriction.G GlobalTheory.Inertia

theorem posIndex_of_hasSignature {n : Type} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ} {p q : ℕ}
    (h : Formalism.UG.HasSignature M p q) : posIndex M = p ∧ posIndex (-M) = q := by
  obtain ⟨e, P, hP⟩ := h
  set A : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := (P : Matrix _ _ ℂ).map (starRingEnd ℂ) with hA
  have hAc : A.map (starRingEnd ℂ) = (P : Matrix _ _ ℂ) := by
    ext i j; simp [hA]
  have hdet : A.det ≠ 0 := by
    have hu := Matrix.isUnits_det_units P
    have h2 := RingHom.map_det (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    rw [RingHom.mapMatrix_apply] at h2
    rw [hA, ← h2]
    exact (map_ne_zero _).2 hu.ne_zero
  have hc : A.transpose * M.reindex e e * A.map (starRingEnd ℂ) = Formalism.UG.Jpq p q := by
    rw [hAc, ← hP]; rfl
  have hcn : A.transpose * (-M).reindex e e * A.map (starRingEnd ℂ) = -Formalism.UG.Jpq p q := by
    rw [← hc]
    have : (-M).reindex e e = -(M.reindex e e) := by ext; simp
    rw [this, Matrix.mul_neg, Matrix.neg_mul]
  have hJ : Formalism.UG.Jpq p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Formalism.UG.Jpq, Matrix.one_apply, Matrix.diagonal_apply] <;> split_ifs <;> simp
  have hJn : -Formalism.UG.Jpq p q = Matrix.diagonal (Sum.elim (fun _ => (-1 : ℂ)) (fun _ => 1)) := by
    rw [hJ, Matrix.diagonal_neg]
    congr 1
    ext i; rcases i with i | i <;> simp
  have hre : ∀ N : Matrix n n ℂ, posIndex N = posIndex (N.reindex e e) := fun N =>
    (posIndex_submatrix_equiv N e.symm).symm
  constructor
  · rw [hre, ← posIndex_congr _ hdet, hc, hJ, posIndex_diagonal, Finset.card_filter, Fintype.sum_sum_type]
    simp
  · rw [hre, ← posIndex_congr _ hdet, hcn, hJn, posIndex_diagonal, Finset.card_filter, Fintype.sum_sum_type]
    simp

theorem hT_coords {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (u : Fin S.rank → E) :
    S.hT (S.frame.equivFun.symm u) (S.frame.equivFun.symm u) = ∑ b, ∑ a, star (u a) * S.gram a b * u b := by
  rw [Module.Basis.equivFun_symm_apply]

  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
  Finset.mul_sum, Formalism.BasicNotions.HSpace.gram]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [starRingEnd_apply]
  ring

end GlobalTheory.IsoNegIdx

namespace GlobalTheory.IsoNegIdx

open ReciprocityTheory.ChartRestriction.G GlobalTheory.Inertia

theorem exists_isotropic_of_negIdx : ∀ (D : D7) (S : HSp D) (k : ℕ), NegIdx S k → 1 ≤ k → k + 1 ≤ S.rank → 3 ≤ S.rank →
    ∃ x : S.V, x ≠ 0 ∧ S.hT x x = 0 := by
  intro D S k hS hk1 hk2 hn
  letI : IsCMField D.host.E := D.host.isCMField_hostE
  have hst : ∀ x : D.host.E, star x = FD.cc x := fun _ => rfl

  have hsig : ∀ φ : D.host.E →+* ℂ, Formalism.UG.HasSignature (S.gram.map φ) (S.rank - k) k := by
    intro φ
    obtain ⟨ρ, h | h⟩ := GlobalTheory.MassLink.tauE_or' D φ
    · subst h
      simpa [gramAt] using hS ρ
    · have h1 := GlobalTheory.BottomIsom.hasSignature_map_star (by simpa [gramAt] using hS ρ)
      rw [Matrix.map_map] at h1
      have e : (⇑(starRingEnd ℂ) ∘ ⇑(tauE D ρ)) = ⇑φ := by
        funext x
        rw [Function.comp_apply, h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
      rwa [e] at h1

  set G : Matrix (Fin S.rank) (Fin S.rank) D.host.E := S.gram.transpose with hGdef
  have hG : ∀ a b, FD.cc (G a b) = G b a := fun a b => by
    simp only [hGdef, Matrix.transpose_apply, ← hst]
    exact S.herm.eq _ _
  have hform : ∀ u, S.hT (S.frame.equivFun.symm u) (S.frame.equivFun.symm u) = FD.herm G u u := fun u => by
    rw [hT_coords, FD.herm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    simp only [hGdef, Matrix.transpose_apply, hst]
    ring
  have hGφ : ∀ φ : D.host.E →+* ℂ, G.map φ = S.gram.map (ComplexEmbedding.conjugate φ) := fun φ => by
    ext a b
    simp only [Matrix.map_apply, ComplexEmbedding.conjugate_coe_eq]
    rw [← hG b a, GlobalTheory.Published.embedding_cc]
    rfl
  obtain ⟨P, d, hP, hPd, hd, -⟩ := GlobalTheory.HermDiag.exists_congr_diagonal_herm hG
  have key : ∀ u, FD.herm G (P.mulVec u) (P.mulVec u) = FD.herm (Matrix.diagonal d) u u := fun u => by
    rw [GlobalTheory.Published.LandherrSt.herm_mulVec, hPd]
  have hne : ∀ u, u ≠ 0 → S.frame.equivFun.symm (P.mulVec u) ≠ 0 := fun u hu h => by
    apply hu
    apply Matrix.eq_zero_of_mulVec_eq_zero hP
    have h3 := congrArg S.frame.equivFun h
    rwa [LinearEquiv.apply_symm_apply, map_zero] at h3
  by_cases hz : ∃ i, d i = 0
  · obtain ⟨i, hi⟩ := hz
    refine ⟨_, hne (Pi.single i 1) (by simp), ?_⟩
    rw [hform, key, GlobalTheory.UTrans.herm_diagonal_self]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j = i
    · subst hj; simp [hi]
    · simp [Pi.single_apply, hj]
  push_neg at hz

  have hs : ∀ φ : D.host.E →+* ℂ, (∃ i, 0 < (φ (d i)).re) ∧ ∃ j, (φ (d j)).re < 0 := by
    intro φ
    have hc : (P.map φ).transpose * G.map φ * (P.map φ).map (starRingEnd ℂ) = Matrix.diagonal fun i => φ (d i) := by
      have h1 : (P.map φ).map (starRingEnd ℂ) = (P.map FD.cc).map φ := by
        ext a b
        simp [GlobalTheory.Published.embedding_cc]
      rw [h1, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hPd, Matrix.diagonal_map (map_zero φ)]
    have hdet : (P.map φ).det ≠ 0 := by
      have h2 := RingHom.map_det φ P
      rw [RingHom.mapMatrix_apply] at h2
      rw [← h2]
      exact (map_ne_zero φ).2 hP
    obtain ⟨hp, hq⟩ := posIndex_of_hasSignature (hGφ φ ▸ hsig (ComplexEmbedding.conjugate φ))
    have hcn : (P.map φ).transpose * (-G.map φ) * (P.map φ).map (starRingEnd ℂ) =
        Matrix.diagonal fun i => -φ (d i) := by
      rw [Matrix.mul_neg, Matrix.neg_mul, hc, Matrix.diagonal_neg]
    rw [← posIndex_congr _ hdet, hc, posIndex_diagonal] at hp
    rw [← posIndex_congr _ hdet, hcn, posIndex_diagonal] at hq
    constructor
    · obtain ⟨i, hi⟩ := Finset.card_pos.1 (show 0 < _ by rw [hp]; omega)
      exact ⟨i, (Finset.mem_filter.1 hi).2⟩
    · obtain ⟨i, hi⟩ := Finset.card_pos.1 (show 0 < _ by rw [hq]; omega)
      refine ⟨i, ?_⟩
      have := (Finset.mem_filter.1 hi).2
      simp only [Complex.neg_re] at this
      linarith
  obtain ⟨z, hz0, hzz⟩ := GlobalTheory.UTrans.exists_isotropic_diagonal hn hd hz hs
  exact ⟨_, hne z hz0, by rw [hform, key, hzz]⟩

end GlobalTheory.IsoNegIdx
end
end

section

set_option autoImplicit false

namespace GlobalTheory

theorem abelianDeRham_free_hodge_baseChange : GlobalTheory.Published.AbelianHodgeDeRham →
    GlobalTheory.Published.AbelianDeRham.Free ∧ GlobalTheory.Published.AbelianDeRham.Hodge ∧
      GlobalTheory.Published.AbelianDeRham.BaseChange := by
  intro hH
  obtain ⟨hF, hBC, -⟩ := GlobalTheory.abelianDeRham_free_baseChange_rigid hH
  exact ⟨hF, GlobalTheory.AbelianHodge.abelianDeRham_hodge
    GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations hH, hBC⟩

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DeRham

open GlobalTheory.Published GlobalTheory.Published.AbelianDeRham



theorem IsKSValue.exists_of_isAbelianScheme_ring (P : AbelianDeRham) {K : Type} [CommRing K] {A : Over (Sp K)} [GrpObj A]
    {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left}
    (h : IsGrpPullback A A' (epsRed K) i) {g : ℕ} (hA : Semi.IsAbelianScheme A')
    (hg : SmoothOfRelativeDimension g A'.hom) {f : HdR A} (hf : f ∈ Fil A) : ∃ v, IsKSValue h f v := by
  have a₀ : Semi.IsAbelianScheme A := by
    have := hA.comm
    open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj in
    have hc : IsCommMonObj A := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl,
        ← h.2 T y x (pushPt h.1.w y) (pushPt h.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) h.1 hA.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) h.1 hA.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hA.geomConnected⟩
  have g₀ := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h.1 hg
  have hL := (P.2.1 K A g a₀ g₀).1
  letI : Algebra (DualNumber K) K := (TrivSqZeroExt.fstHom K K K).toRingHom.toAlgebra
  obtain ⟨-, hF⟩ := P.2.2.1 (DualNumber K) A' g hA hg K A i h
  obtain ⟨-, ⟨N, hN⟩, -⟩ := P.2.1 (DualNumber K) A' g hA hg
  obtain ⟨-, hproj, -⟩ := P.1.prim hA hg
  have su : Function.Surjective (TrivSqZeroExt.fstHom K K K).toRingHom :=
    fun r => ⟨TrivSqZeroExt.inl r, rfl⟩
  have rA := P.2.2.2.1 _ A' g hA hg _ (epsDP K) (isDPNilpotent_squareZero _) K _ su rfl A i h
  have rB := P.2.2.2.1.crysToDR_bijective hA hg (κ := epsDP K) (isDPNilpotent_squareZero _) su rfl h
  let φL : primDR A' →ₗ[DualNumber K] K :=
    { toFun := fun c => f ((bcMor h).pull c)
      map_add' := fun x y => by simp only [map_add (f := _)]
      map_smul' := fun r c => by
        rw [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, Algebra.smul_def] }
  obtain ⟨u, hu⟩ := Module.projective_lifting_property (Algebra.linearMap (DualNumber K) K) φL
    (fun r => ⟨TrivSqZeroExt.inl r, rfl⟩)
  let d' : HdR A' := u ∘ₗ N.projection (PrimitiveSubmodule A') hN.symm
  have hd' : d' ∈ Fil A' := by
    rw [Fil, Submodule.mem_dualAnnihilator]
    intro x hx
    change u (N.projection (PrimitiveSubmodule A') hN.symm x) = 0
    rw [Submodule.projection_apply_of_mem_right hN.symm hx, map_zero]
  have fd' : ∀ x, (d' x).fst = f ((bcMor h).pull x) := fun x => by
    have e1 : ∀ y, (u y).fst = f ((bcMor h).pull y) := fun y => LinearMap.congr_fun hu y
    have e2 := Submodule.projection_add_projection_eq_self hN.symm x
    have e3 : f ((bcMor h).pull ((PrimitiveSubmodule A').projection N hN.symm.symm x)) = 0 := by
      rw [Fil, hF] at hf
      exact (Submodule.mem_dualAnnihilator _).1 hf _
        (Submodule.subset_span ⟨_, Submodule.projection_apply_mem _ _, rfl⟩)
    change (u _).fst = _
    rw [e1, ← add_zero (f ((bcMor h).pull _)), ← e3, ← map_add (f := _), ← map_add (f := _), e2]
  obtain ⟨d, hd⟩ := rB.2 d'
  let k : HdR A :=
    { toFun := fun c => (d ((constMor A).pull c)).snd
      map_add' := fun x y => by simp only [map_add (f := _), TrivSqZeroExt.snd_add]
      map_smul' := fun r c => by
        rw [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, smul_eq_mul,
          TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_mul]
        simp }
  obtain ⟨v, hv, -⟩ := hL.1 k
  refine ⟨v, k, ⟨d, by rw [liftFil, Submodule.mem_comap, hd]; exact hd', fun c => ?_⟩, hv⟩
  obtain ⟨x, hx⟩ := rA.2 ((constMor A).pull c)
  have red : (bcMor h).pull x = c := by
    rw [← GrpMor.pull_pull (liftMor (epsDP K) h) (redMor A) (bcMor h) (fun _ => rfl) (by simp) x, hx,
      redMor_constMor]
  apply TrivSqZeroExt.ext
  · have e := fd' x
    rw [← hd, crysToDR_apply, hx, red] at e
    rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
    exact e
  · rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
    rfl

theorem ksRegular_of_isAbelianScheme_ring : GlobalTheory.Published.AbelianDeRham → ∀ {K : Type} [CommRing K] {A : Over (Sp K)}
    [GrpObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left}
    (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) {g : ℕ}, Semi.IsAbelianScheme A' →
    SmoothOfRelativeDimension g A'.hom → KSRegular h := by
  intro P K _ A _ A' _ i h g hA hg f hf
  obtain ⟨v, hv⟩ := IsKSValue.exists_of_isAbelianScheme_ring P h hA hg hf
  exact ⟨v, hv, fun w hw => IsKSValue.unique P hA hg hw hv⟩

end GlobalTheory.DeRham
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DeRham

open GlobalTheory.Published GlobalTheory.Published.AbelianDeRham



theorem IsKSValue.exists_of_isAbelianScheme (P : AbelianDeRham) {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]
    {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left}
    (h : IsGrpPullback A A' (epsRed K) i) {g : ℕ} (hA : Semi.IsAbelianScheme A')
    (hg : SmoothOfRelativeDimension g A'.hom) {f : HdR A} (hf : f ∈ Fil A) : ∃ v, IsKSValue h f v := by
  have a₀ : Semi.IsAbelianScheme A := by
    have := hA.comm
    have hc : IsCommMonObj A := by
      open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj in
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl,
        ← h.2 T y x (pushPt h.1.w y) (pushPt h.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) h.1 hA.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) h.1 hA.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hA.geomConnected⟩
  have g₀ := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h.1 hg
  have hL := (P.2.1 K A g a₀ g₀).1
  letI : Algebra (DualNumber K) K := (TrivSqZeroExt.fstHom K K K).toRingHom.toAlgebra
  obtain ⟨-, hF⟩ := P.2.2.1 (DualNumber K) A' g hA hg K A i h
  obtain ⟨-, ⟨N, hN⟩, -⟩ := P.2.1 (DualNumber K) A' g hA hg
  obtain ⟨-, hproj, -⟩ := P.1.prim hA hg
  have su : Function.Surjective (TrivSqZeroExt.fstHom K K K).toRingHom :=
    fun r => ⟨TrivSqZeroExt.inl r, rfl⟩
  have rA := P.2.2.2.1 _ A' g hA hg _ (epsDP K) (isDPNilpotent_squareZero _) K _ su rfl A i h
  have rB := P.2.2.2.1.crysToDR_bijective hA hg (κ := epsDP K) (isDPNilpotent_squareZero _) su rfl h
  let φL : primDR A' →ₗ[DualNumber K] K :=
    { toFun := fun c => f ((bcMor h).pull c)
      map_add' := fun x y => by simp only [map_add (f := _)]
      map_smul' := fun r c => by
        rw [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, Algebra.smul_def] }
  obtain ⟨u, hu⟩ := Module.projective_lifting_property (Algebra.linearMap (DualNumber K) K) φL
    (fun r => ⟨TrivSqZeroExt.inl r, rfl⟩)
  let d' : HdR A' := u ∘ₗ N.projection (PrimitiveSubmodule A') hN.symm
  have hd' : d' ∈ Fil A' := by
    rw [Fil, Submodule.mem_dualAnnihilator]
    intro x hx
    change u (N.projection (PrimitiveSubmodule A') hN.symm x) = 0
    rw [Submodule.projection_apply_of_mem_right hN.symm hx, map_zero]
  have fd' : ∀ x, (d' x).fst = f ((bcMor h).pull x) := fun x => by
    have e1 : ∀ y, (u y).fst = f ((bcMor h).pull y) := fun y => LinearMap.congr_fun hu y
    have e2 := Submodule.projection_add_projection_eq_self hN.symm x
    have e3 : f ((bcMor h).pull ((PrimitiveSubmodule A').projection N hN.symm.symm x)) = 0 := by
      rw [Fil, hF] at hf
      exact (Submodule.mem_dualAnnihilator _).1 hf _
        (Submodule.subset_span ⟨_, Submodule.projection_apply_mem _ _, rfl⟩)
    change (u _).fst = _
    rw [e1, ← add_zero (f ((bcMor h).pull _)), ← e3, ← map_add (f := _), ← map_add (f := _), e2]
  obtain ⟨d, hd⟩ := rB.2 d'
  let k : HdR A :=
    { toFun := fun c => (d ((constMor A).pull c)).snd
      map_add' := fun x y => by simp only [map_add (f := _), TrivSqZeroExt.snd_add]
      map_smul' := fun r c => by
        rw [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, smul_eq_mul,
          TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_mul]
        simp }
  obtain ⟨v, hv, -⟩ := hL.1 k
  refine ⟨v, k, ⟨d, by rw [liftFil, Submodule.mem_comap, hd]; exact hd', fun c => ?_⟩, hv⟩
  obtain ⟨x, hx⟩ := rA.2 ((constMor A).pull c)
  have red : (bcMor h).pull x = c := by
    rw [← GrpMor.pull_pull (liftMor (epsDP K) h) (redMor A) (bcMor h) (fun _ => rfl) (by simp) x, hx,
      redMor_constMor]
  apply TrivSqZeroExt.ext
  · have e := fd' x
    rw [← hd, crysToDR_apply, hx, red] at e
    rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
    exact e
  · rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
    rfl

theorem ksRegular_of_isAbelianScheme : GlobalTheory.Published.AbelianDeRham → ∀ {K : Type} [Field K] {A : Over (Sp K)}
    [GrpObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left}
    (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) {g : ℕ}, Semi.IsAbelianScheme A' →
    SmoothOfRelativeDimension g A'.hom → KSRegular h := by
  intro P K _ A _ A' _ i h g hA hg f hf
  obtain ⟨v, hv⟩ := IsKSValue.exists_of_isAbelianScheme P h hA hg hf
  exact ⟨v, hv, fun w hw => IsKSValue.unique P hA hg hw hv⟩

end GlobalTheory.DeRham
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

theorem _root_.GlobalTheory.T.canonical_modification_ks_iso_sec : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (hV : IsVariety₀ TF.X Z) (ω₀ : CanId (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z))) (M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw)) (ω : CanId M) (b s : AllWt.Weight Dw) (hs : FlagTan.kap Dw + b = s) (m : H0 (str₀ TF.X Z) (L₀ TF.X Z s) (U₀ TF.X Z)), (∃ g : H0 (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).str (tens (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle ((L₀ TF.X Z b).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ)) ⊤, H0.restr le_top g = (((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).canChart (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.isLB hs).mul ω₀.ω ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).pullOff m)) ↔ ∃ g : H0 M.str (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)) ⊤, H0.restr le_top g = (((common₀ TF.X Z).pull M.σ).canChart M.K.isLB hs).mul ω.ω (M.pullOff m) := by
  first | exact @GlobalTheory.CanonBirat.extends_iff_modif | exact GlobalTheory.CanonBirat.extends_iff_modif | (intros; apply GlobalTheory.CanonBirat.extends_iff_modif <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TiedUnif

theorem uniformisation_every_embedding_thirdKind : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (fw : FWTie T R.toRealDat κ v₀), ∀ (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)), R.WeakCharacterisation F → BarTie fw → (∀ i, OMPins T R.toRealDat κ v₀ O i) → RhoGeo fw O → EquivAll T R.toRealDat κ O → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → R.toRealDat.LUnif := by
  intro h1 h2 D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ fw O hC hb hO hr ha hn
  exact lUnif_of_pins h1 h2 T R.toRealDat κ v₀ O F.lv2 fw hC.base.lev hC.base.grp hC.base.models hb hO hr ha hn

end GlobalTheory.TiedUnif
end

section

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

theorem _root_.GlobalTheory.T.flat_to_spec_field' : ∀ (K : Type) [Field K] (Z : Scheme.{0}) (f : Z ⟶ Sp K), Flat f := by
  first | exact @GlobalTheory.flat_to_spec_field | exact GlobalTheory.flat_to_spec_field | (intros; apply GlobalTheory.flat_to_spec_field <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_basicOpen_nbhd_point_mem_open : ∀ (S : Type) [CommRing S] (X : Scheme.{0}) (x : Sp S ⟶ X) (V : X.Opens) (q : PrimeSpectrum S), x q ∈ V → ∃ f₀ : S, f₀ ∉ q.asIdeal ∧ ⊤ ≤ (spMap (algebraMap S (Localization.Away f₀)) ≫ x) ⁻¹ᵁ V := by
  first | exact @GlobalTheory.nbhd_basicOpen_of_mem | exact GlobalTheory.nbhd_basicOpen_of_mem | (intros; apply GlobalTheory.nbhd_basicOpen_of_mem <;> assumption)
end
