module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1170
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039
import Development.AbelianVarietyTheory.Definitions.Divisors.LeTwoMulOfForallScale
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

namespace GlobalTheory.FibreDim

theorem charZero_residueField_genericPoint' (X : Scheme.{0}) [IsIntegral X] (hc : CharZero Γ(X, ⊤)) :
    CharZero (X.residueField (genericPoint X)) := by
  have hg : Function.Injective (X.presheaf.germ ⊤ (genericPoint X) trivial) :=
    germ_injective_of_isIntegral X _ _
  have hr : Function.Injective (X.residue (genericPoint X)) := (X.residue (genericPoint X)).hom.injective
  exact charZero_of_injective_ringHom (f := (X.presheaf.germ ⊤ (genericPoint X) trivial ≫ X.residue _).hom)
    (by simpa using hr.comp hg)

theorem not_charZero_residueField {Z : Scheme.{0}} (p : ℕ) [Fact p.Prime] (s : Z ⟶ Sp (ZMod p)) (z : Z) :
    ¬ CharZero (Z.residueField z) := by
  intro hc
  let φ : ZMod p →+* Z.residueField z :=
    ((Scheme.ΓSpecIso (CommRingCat.of (ZMod p))).inv ≫ s.appTop ≫ Z.Γevaluation z).hom
  have h0 : ((p : ZMod p) : ZMod p) = 0 := ZMod.natCast_self p
  have : (p : Z.residueField z) = 0 := by rw [← map_natCast φ p, h0, map_zero]
  exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) this

end GlobalTheory.FibreDim

namespace GlobalTheory.FibreDim

theorem fibre_isProjOver_and_dim_le : ∀ (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k), IsArithVar q 1 → ∀ (p : ℕ) [Fact p.Prime], (letI := GlobalTheory.algebraΓOfHom (pullback.snd (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))); IsProjOver (strHom (ZMod p) (X := (pullback (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))))))) ∧ topologicalKrullDim ↥(pullback (C := Scheme.{0}) (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))) ≤ 1 := by
  intro k _ W q hq p _
  haveI hgc : IsClosedImmersion (spMap (Int.castRingHom (ZMod p))) :=
    IsClosedImmersion.spec_of_surjective _ (ZMod.ringHom_surjective _)
  refine ⟨?_, ?_⟩
  · letI := GlobalTheory.algebraΓOfHom (pullback.snd (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))))
    exact VertProj.isProjOver_strHom_zmod k W q 1 hq _
      (pullback.fst (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))) p
  · set f := q ≫ spMap (Int.castRingHom k)
    set g := spMap (Int.castRingHom (ZMod p))
    have := hq.isIntegral
    have hemb := (pullback.fst f g).isClosedEmbedding
    have hs : IsClosed (Set.range (pullback.fst f g)) := hemb.isClosed_range
    have hne : ∀ z, (pullback.fst f g) z ≠ genericPoint W := by
      intro z hz
      have h1 := charZero_residueField_genericPoint' W hq.charZero
      rw [← hz] at h1
      exact not_charZero_residueField p (pullback.snd f g) z
        (charZero_of_injective_ringHom ((pullback.fst f g).residueFieldMap z).hom.injective)
    have key := topologicalKrullDim_add_one_le hs isClosed_univ (T := W) fun x hx =>
      ⟨genericPoint W, trivial, fun ⟨z, hz⟩ => hne z hz, genericPoint_specializes x⟩
    have hW : topologicalKrullDim (Set.univ : Set W) ≤ 2 := by
      have := topologicalKrullDim_subspace_le W Set.univ
      rw [hq.dim_eq] at this
      exact this
    have heq : topologicalKrullDim (Set.range (pullback.fst f g)) =
        topologicalKrullDim ↥(pullback (C := Scheme.{0}) f g) :=
      GlobalTheory.topologicalKrullDim_eq_of_isEmbedding hemb.isEmbedding rfl
    rw [← heq]
    have h2 := key.trans hW
    generalize topologicalKrullDim (Set.range (pullback.fst f g)) = d at h2 ⊢
    induction d with
    | bot => exact bot_le
    | coe n =>
      norm_cast at h2 ⊢
      induction n with
      | top => exact absurd h2 (by decide)
      | coe m =>
        norm_cast at h2 ⊢
        have h3 : m + 1 ≤ 2 := by exact_mod_cast h2
        omega

end GlobalTheory.FibreDim
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.exists_section_ampleTwist_nonvanishing_finiteSet : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M A : HermLB p), IsAmpleLB A.B → ∀ S : Set X, S.Finite → ∃ b : ℕ, 0 < b ∧ ∃ u : (M.tens (A.pow b)).B.Sec, S ⊆ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u := by
  first | exact @GlobalTheory.VolBr.exists_sec_finite_subset_nonzeroLocus | exact GlobalTheory.VolBr.exists_sec_finite_subset_nonzeroLocus | (intros; apply GlobalTheory.VolBr.exists_sec_finite_subset_nonzeroLocus <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

noncomputable section

namespace GlobalTheory.NefShift

theorem isNef_shift_nonneg : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (M : HermLB p) (t : ℝ), 0 ≤ t → M.IsNef D →
      (M.shift (fun _ => t) fun _ => rfl).IsNef D := by
  intro k _ X _ p D hX M t ht hM
  refine ⟨hM.semiPos.shift _ _, fun Z i _ _ κ _ _ _ hd => hM.vertical Z i κ hd, ?_⟩
  intro Z i _ _ _ hc hd
  obtain ⟨r, hr, h0⟩ := hM.horizontal Z i hc hd
  refine ⟨r, hr, ?_⟩
  rw [GlobalTheory.HtSelfInter.curveDeg_shift hX M t i hc hd hr]
  have : (0 : ℝ) ≤ t * Nat.card (X.residueField (i (genericPoint Z)) →+* ℂ) := by positivity
  linarith

end GlobalTheory.NefShift
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.exists_semiPos_fubiniStudy_power_add_smooth_fn : ∀ (k : Type) [CommRing k] (σ : k →+* ℂ) (N : ℕ) (v : CxPts (PSpace.str k N) σ → ℝ), (∀ y, CInfAt v y) → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ((((ProjSpace.hermitianTwistingSheaf k N).φ σ).pow m).addFn v).SemiPosReg N := by
  first | exact @GlobalTheory.WeightShift.exists_semiPosReg_fubiniStudy | exact GlobalTheory.WeightShift.exists_semiPosReg_fubiniStudy | (intros; apply GlobalTheory.WeightShift.exists_semiPosReg_fubiniStudy <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.exists_smooth_semipositive_weight_of_generated : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (B : LB X), B.IsLB → (∃ (n : ℕ) (u : Fin n → B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) → ∃ (φ : Weight p σ B), φ.IsCInf ∧ ∀ D : ℕ, φ.SemiPosReg D := by
  first | exact @GlobalTheory.weight_cInf_semiPos_of_generated | exact GlobalTheory.weight_cInf_semiPos_of_generated | (intros; apply GlobalTheory.weight_cInf_semiPos_of_generated <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.smooth_weights_differ_by_smooth_function : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (B : LB X) (φ ψ : Weight p σ B), φ.IsCInf → ψ.IsCInf → ∃ u : CxPts p σ → ℝ, (∀ y, CInfAt u y) ∧ ∀ i, ∀ y ∈ ptsIn p σ (B.U i), ψ.φ i y = φ.φ i y + u y := by
  first | exact @GlobalTheory.Mix.weight_sub_cInf | exact GlobalTheory.Mix.weight_sub_cInf | (intros; apply GlobalTheory.Mix.weight_sub_cInf <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.exists_continuous_read_on_affineOpen_ringHoms : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (U : X.Opens) (hU : IsAffineOpen U) (u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ), (∀ σ, ContinuousOn (u σ) (ptsIn p σ U)) → (letI : TopologicalSpace (Γ(X, U) →+* ℂ) := TopologicalSpace.induced (fun x : Γ(X, U) →+* ℂ => (x : Γ(X, U) → ℂ)) inferInstance; ∃ ψ : (Γ(X, U) →+* ℂ) → ℝ, Continuous ψ ∧ (∀ (σ : k →+* ℂ) (y : CxPts p σ) (hy : y ∈ ptsIn p σ U), ψ (evHom hy) = u σ y) ∧ (∀ x : Γ(X, U) →+* ℂ, ∃ (σ : k →+* ℂ) (y : CxPts p σ) (hy : y ∈ ptsIn p σ U), evHom hy = x) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ) (hy : y ∈ ptsIn p σ U) (W : Set (Γ(X, U) →+* ℂ)), W ∈ 𝓝 (evHom hy) → {z : CxPts p σ | ∃ hz : z ∈ ptsIn p σ U, evHom hz ∈ W} ∈ 𝓝 y) := by
  first | exact @GlobalTheory.ContRead.exists_continuous_read | exact GlobalTheory.ContRead.exists_continuous_read | (intros; apply GlobalTheory.ContRead.exists_continuous_read <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

theorem _root_.GlobalTheory.T.exists_smooth_bump_complexPoints_projective : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (σ : k →+* ℂ) (y : CxPts p σ) (O : Set (CxPts p σ)), IsOpen O → y ∈ O → ∃ χ : CxPts p σ → ℝ, (∀ z, CInfAt χ z) ∧ (∀ z, 0 ≤ χ z) ∧ 0 < χ y ∧ tsupport χ ⊆ O := by
  first | exact @GlobalTheory.BumpPts.exists_cInf_bump | exact GlobalTheory.BumpPts.exists_cInf_bump | (intros; apply GlobalTheory.BumpPts.exists_cInf_bump <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.exists_section_extending_rationalGenericFibre_mul_int : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (B : LB X), B.IsLB → ∀ t : (B.pull (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)))).Sec, ∃ s : B.Sec, ∀ y : ↥(Limits.pullback (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))), (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))) y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ↔ y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t := by
  first | exact @GlobalTheory.GenSecInt.main | exact GlobalTheory.GenSecInt.main | (intros; apply GlobalTheory.GenSecInt.main <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

namespace GlobalTheory.GoodTop

theorem frame_eventually {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ}
    (E : Fr (ratOf X) (fun _ : Unit => m) 0) {y : CxPts X.str σ} {A : Mat (fun _ : Unit => m) X.Fn}
    (hA : A ∈ E.S (under y)) : ∀ᶠ z in 𝓝 y, A ∈ E.S (under z) := by
  obtain ⟨U, B, hU, hB, hS⟩ := E.loc (under y)
  have hP := (hS _ hU A).1 hA
  have hreg : ∀ g : X.Fn, RegAt (under y) g → ∀ᶠ z in 𝓝 y, RegAt (under z) g := by
    intro g hg
    obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
    filter_upwards [(isOpen_ptsIn W).mem_nhds (mem_ptsIn.2 hW)] with z hz
    exact regAt_fnOf (mem_ptsIn.1 hz) _ a
  have hU' : ∀ᶠ z in 𝓝 y, under z ∈ U := by
    filter_upwards [(isOpen_ptsIn U).mem_nhds (mem_ptsIn.2 hU)] with z hz
    exact mem_ptsIn.1 hz
  have h1 : ∀ᶠ z in 𝓝 y, ∀ τ, (∀ i j, RegAt (under z) ((A * B⁻¹) τ i j)) ∧ RegAt (under z) ((A * B⁻¹) τ).det⁻¹ :=
    Filter.eventually_all.2 fun τ => (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      hreg _ (mem_O_ratOf.1 ((hP τ).1 i j))).and (hreg _ (mem_O_ratOf.1 (hP τ).2.2.1))
  filter_upwards [hU', h1] with z hz hz1
  exact (hS _ hz A).2 fun τ => ⟨fun i j => mem_O_ratOf.2 ((hz1 τ).1 i j), (hP τ).2.1, mem_O_ratOf.2 (hz1 τ).2,
    fun i j hi => absurd hi (by simp)⟩

end GlobalTheory.GoodTop
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

open IsLocalRing KaehlerDifferential Module

theorem mem_maximalIdeal_of_mul_add_mul_mem_sq {R : Type} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {t u : R} (h : Ideal.span {t, u} = maximalIdeal R)
    (hd : ringKrullDim R = 2) {a b : R} (hab : a * t + b * u ∈ maximalIdeal R ^ 2) :
    a ∈ maximalIdeal R := by
  by_contra ha
  have hau : IsUnit a := by simpa [mem_maximalIdeal, mem_nonunits_iff] using ha
  have hu : u ∈ maximalIdeal R := h ▸ Ideal.subset_span (by simp)
  have hle : maximalIdeal R ≤ Ideal.span {u} ⊔ maximalIdeal R ^ 2 := by
    conv_lhs => rw [← h]
    rw [Ideal.span_le]
    rintro x (rfl | rfl)
    · obtain ⟨c, hc⟩ := hau.exists_left_inv
      have e : x = c * (a * x + b * u) + (-(c * b)) * u := by
        linear_combination (-x) * hc
      rw [e]
      exact add_mem (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ hab))
        (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self u)))
    · exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  have h1 := spanFinrank_maximalIdeal_le_ncard_of_le_sup_sq (Set.finite_singleton u)
    ((Ideal.span_singleton_le_iff_mem _).2 hu) hle
  rw [Set.ncard_singleton] at h1
  have h2 := ringKrullDim_le_spanFinrank_maximalIdeal R
  rw [hd] at h2
  have h3 : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤ 1 := by exact_mod_cast h1
  have := h2.trans h3
  norm_num at this

theorem isFreeGen_dForm_regularPair_cons : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L)
    (hQ : IsLocModel cL Q) (t u : Q),
    Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) →
    ringKrullDim Q = 2 →
    ∃ (m : ℕ) (z : Fin m → Q),
      (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 →
        IsUnit (MvPolynomial.eval₂ (cL.codRestrict Q hQ.const_mem) z P)) ∧
      IsFreeGen Q (dForm (cL.codRestrict Q hQ.const_mem)
        (Fin.cons t (Fin.cons u z : Fin (m + 1) → Q) : Fin (m + 2) → Q)) := by
  intro L _ cL Q hQ t u hspan hdim
  letI := hQ.isLocalRing
  letI : Algebra ℂ Q := (cL.codRestrict Q hQ.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ Q := hQ.essFiniteType
  haveI : IsNoetherianRing Q := Algebra.EssFiniteType.isNoetherianRing ℂ Q
  haveI : IsRegularLocalRing Q := by
    refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le Q ?_
    rw [hdim, ← hspan]
    have h1 := Submodule.spanFinrank_span_le_ncard_of_finite (R := Q) (Set.toFinite ({t, u} : Set Q))
    have h2 : ({t, u} : Set Q).ncard ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)
    exact_mod_cast h1.trans h2
  haveI : Algebra.FormallySmooth ℂ Q := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ Q
  have hs : Function.Surjective (algebraMap Q (ResidueField Q)) := residue_surjective
  haveI : Algebra.EssFiniteType ℂ (ResidueField Q) := .comp ℂ Q _
  have hinj := (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff (R := ℂ) hs).mpr
    inferInstance
  have hker : RingHom.ker (algebraMap Q (ResidueField Q)) = maximalIdeal Q := ker_residue
  have htm : t ∈ maximalIdeal Q := hspan ▸ Ideal.subset_span (by simp)
  have hum : u ∈ maximalIdeal Q := hspan ▸ Ideal.subset_span (by simp)
  have ht0 : algebraMap Q (ResidueField Q) t = 0 := (residue_eq_zero_iff t).mpr htm
  have hu0 : algebraMap Q (ResidueField Q) u = 0 := (residue_eq_zero_iff u).mpr hum

  obtain ⟨s, hsb⟩ := exists_isTranscendenceBasis ℂ (ResidueField Q)
  haveI := hsb.isAlgebraic_field
  haveI : Algebra.IsSeparable
      (IntermediateField.adjoin ℂ (Set.range ((↑) : s → ResidueField Q))) (ResidueField Q) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨bκ, hbκ⟩ := exists_basis_kaehler_of_algebraicIndependent hsb.1
  haveI : Finite s := Module.Finite.finite_basis bκ
  let e : Fin (Nat.card s) ≃ s := (Finite.equivFin s).symm
  let b' := bκ.reindex e.symm
  have hb' : ∀ i, b' i = D ℂ (ResidueField Q) (e i) := fun i => by
    rw [Basis.reindex_apply, Equiv.symm_symm, hbκ]
  let z : Fin (Nat.card s) → Q := fun i => Function.surjInv hs (e i : ResidueField Q)
  have hz : ∀ i, algebraMap Q (ResidueField Q) (z i) = e i := fun i => Function.surjInv_eq hs _
  refine ⟨Nat.card s, z, fun P hP => ?_, ?_⟩
  · have e1 : algebraMap Q (ResidueField Q) (MvPolynomial.eval₂ (cL.codRestrict Q hQ.const_mem) z P)
        = MvPolynomial.aeval (fun i => (e i : ResidueField Q)) P := by
      rw [show (fun i => (e i : ResidueField Q)) = algebraMap Q (ResidueField Q) ∘ z from
        funext fun i => (hz i).symm, MvPolynomial.aeval_algebraMap_apply]
      rfl
    refine (residue_ne_zero_iff_isUnit _).mp ?_
    change algebraMap Q (ResidueField Q) _ ≠ 0
    rw [e1]
    exact fun h0 => hP ((algebraicIndependent_iff.1 (hsb.1.comp e e.injective)) P h0)
  · let v : Fin (Nat.card s + 2) → Q := Fin.cons t (Fin.cons u z : Fin (Nat.card s + 1) → Q)
    let w : Fin (Nat.card s + 2) → (ResidueField Q) ⊗[Q] Ω[Q⁄ℂ] := TensorProduct.mk Q (ResidueField Q) Ω[Q⁄ℂ] 1 ∘ fun i => D ℂ Q (v i)
    have hw0 : w 0 = (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q t := rfl
    have hw1 : w (Fin.succ 0) = (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q u := rfl
    have hwz : ∀ i : Fin (Nat.card s), w i.succ.succ = (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q (z i) := fun i => rfl
    have hmb : ∀ x : Q, mapBaseChange ℂ Q (ResidueField Q) ((1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q x) = D ℂ (ResidueField Q) (algebraMap Q (ResidueField Q) x) :=
      fun x => by rw [mapBaseChange_tmul, one_smul, map_D]
    have hpair : ∀ a b : Q, (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q (a * t + b * u) =
        algebraMap Q (ResidueField Q) a • w 0 + algebraMap Q (ResidueField Q) b • w (Fin.succ 0) := fun a b => by
      rw [hw0, hw1]
      simp only [map_add (f := _), Derivation.leibniz, TensorProduct.tmul_add, TensorProduct.tmul_smul]
      rw [← algebraMap_smul (ResidueField Q) t, ← algebraMap_smul (ResidueField Q) u, ht0, hu0]
      simp only [zero_smul, add_zero, algebraMap_smul]
    have hkc : ∀ x (hx : x ∈ RingHom.ker (algebraMap Q (ResidueField Q))),
        kerCotangentToTensor ℂ Q (ResidueField Q) ((RingHom.ker (algebraMap Q (ResidueField Q))).toCotangent ⟨x, hx⟩) =
          (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q x := fun x hx => kerCotangentToTensor_toCotangent _ _ _ _

    have hsp : Submodule.span (ResidueField Q) (Set.range w) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      let c := b'.repr (mapBaseChange ℂ Q (ResidueField Q) y)
      have hy0 : mapBaseChange ℂ Q (ResidueField Q) (y - ∑ i, c i • w i.succ.succ) = 0 := by

        rw [map_sub, map_sum, sub_eq_zero]
        conv_lhs => rw [← b'.sum_repr (mapBaseChange ℂ Q (ResidueField Q) y)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, hwz, hmb, hz, hb']
      obtain ⟨c', hc'⟩ := (exact_kerCotangentToTensor_mapBaseChange ℂ Q (ResidueField Q) hs _).mp hy0
      obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ c'
      have hx' := hx
      rw [hker, ← hspan, Ideal.mem_span_pair] at hx'
      obtain ⟨a, b, rfl⟩ := hx'
      rw [hkc, hpair] at hc'
      have hy : y = (algebraMap Q (ResidueField Q) a • w 0 + algebraMap Q (ResidueField Q) b • w (Fin.succ 0)) + ∑ i, c i • w i.succ.succ := by
        rw [hc', sub_add_cancel]
      rw [hy]
      refine add_mem (add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.succ 0, rfl⟩)))
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))

    have hli : LinearIndependent (ResidueField Q) w := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hg
      have hφ := congrArg (mapBaseChange ℂ Q (ResidueField Q)) hg

      simp only [map_add (f := _), map_sum, map_smul, map_zero] at hφ
      rw [hw0, hmb, ht0, Derivation.map_zero, smul_zero, zero_add] at hφ
      rw [hw1, hmb, hu0, Derivation.map_zero, smul_zero, zero_add] at hφ
      simp only [hwz, hmb, hz, ← hb'] at hφ
      have hrest : ∀ i : Fin (Nat.card s), g i.succ.succ = 0 :=
        Fintype.linearIndependent_iff.mp b'.linearIndependent (fun i => g i.succ.succ) hφ
      simp only [hrest, zero_smul, Finset.sum_const_zero, add_zero] at hg
      obtain ⟨a, ha⟩ := hs (g 0)
      obtain ⟨b, hb⟩ := hs (g (Fin.succ 0))
      have hg' : (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q (a * t + b * u) = 0 := by
        rw [hpair, ha, hb]
        exact hg
      have hmem : a * t + b * u ∈ RingHom.ker (algebraMap Q (ResidueField Q)) := by
        rw [hker]
        exact add_mem (Ideal.mul_mem_left _ _ htm) (Ideal.mul_mem_left _ _ hum)
      have hsq : a * t + b * u ∈ maximalIdeal Q ^ 2 := by
        have h1 : (RingHom.ker (algebraMap Q (ResidueField Q))).toCotangent ⟨_, hmem⟩ = 0 :=
          hinj (by rw [hkc, map_zero]; exact hg')
        have h2 : a * t + b * u ∈ RingHom.ker (algebraMap Q (ResidueField Q)) ^ 2 :=
          (Ideal.toCotangent_eq_zero _ _).mp h1
        rwa [hker] at h2
      have ham : a ∈ maximalIdeal Q := mem_maximalIdeal_of_mul_add_mul_mem_sq hspan hdim hsq
      have hbm : b ∈ maximalIdeal Q := by
        refine mem_maximalIdeal_of_mul_add_mul_mem_sq (t := u) (u := t) (a := b) (b := a)
          (by rw [Set.pair_comm]; exact hspan) hdim ?_
        rw [add_comm]; exact hsq
      have h0 : g 0 = 0 := by rw [← ha]; exact (residue_eq_zero_iff a).mpr ham
      have h1 : g (Fin.succ 0) = 0 := by rw [← hb]; exact (residue_eq_zero_iff b).mpr hbm
      intro i
      refine Fin.cases h0 (fun j => Fin.cases h1 (fun k => hrest k) j) i
    haveI : Module.FinitePresentation Q Ω[Q⁄ℂ] := Module.finitePresentation_of_finite Q _
    obtain ⟨b, hb⟩ := Module.exists_basis_of_basis_baseChange (R := Q) (fun i => D ℂ Q (v i)) hli hsp
      (Module.Flat.rTensor_preserves_injective_linearMap (maximalIdeal Q).subtype
        Subtype.val_injective)
    exact isFreeGen_dForm v b hb

end GlobalTheory.FieldPair
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory

theorem essFiniteType_of_isLocModel : ∀ {K : Type} [Field K] [Algebra ℂ K] (R : Subring K),
    IsLocModel (algebraMap ℂ K) R → Algebra.EssFiniteType ℂ K := by
  intro K _ _ R h
  letI : Algebra ℂ R := ((algebraMap ℂ K).codRestrict R h.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ R := h.essFiniteType
  haveI : IsScalarTower ℂ R K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsFractionRing R K := IsFractionRing.of_field R K fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := h.frac z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, by
      show z = a / b
      rw [eq_div_iff hb0, e]⟩
  haveI : Algebra.EssFiniteType R K :=
    Algebra.EssFiniteType.of_isLocalization K (nonZeroDivisors R)
  exact Algebra.EssFiniteType.comp ℂ R K

end GlobalTheory
end
