module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentPullChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1606
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1404
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1700
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1114
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle377
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1118
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1223
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1701
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.PosDef
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
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.GaloisValuations.GlobalB
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.squareZeroLifting_of_noetherian_case : AbelianDeRham → (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (hI : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → LiftObj (divided₂ hI) π ∧ LiftHom (divided₂ hI) π) → SqLifting := by
  first | exact @GlobalTheory.SqLift.sqLifting_of_noetherian | exact GlobalTheory.SqLift.sqLifting_of_noetherian | (intros; apply GlobalTheory.SqLift.sqLifting_of_noetherian <;> assumption)
end

section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon

theorem local_of_opens_pullback (Q : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget Q] {X Y : Scheme.{0}}
    (f : X ⟶ Y) {Ix : Type} (V : Ix → Y.Opens) (hV : ∀ y : Y, ∃ i, y ∈ V i)
    (h : ∀ i, Q (pullback.snd f (V i).ι)) : Q f := by
  have hV' : iSup V = ⊤ := by
    rw [eq_top_iff]
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.2 (hV y)
  exact IsZariskiLocalAtTarget.of_openCover (P := Q) (Y.openCoverOfIsOpenCover V hV') h

theorem Good.of_opens {g : ℕ} {X Y : Scheme.{0}} (f : X ⟶ Y) {Ix : Type} (V : Ix → Y.Opens)
    (hV : ∀ y : Y, ∃ i, y ∈ V i) (h : ∀ i, Good g (pullback.snd f (V i).ι)) : Good g f := by
  have h1 : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension.{0} g) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  have h2 : IsZariskiLocalAtTarget (@GeometricallyConnected.{0}) := by
    rw [GeometricallyConnected.eq_geometrically]; infer_instance
  exact ⟨local_of_opens_pullback @IsProper f V hV fun i ↦ (h i).proper,
    local_of_opens_pullback (@SmoothOfRelativeDimension g) f V hV fun i ↦ (h i).smooth,
    local_of_opens_pullback @GeometricallyConnected f V hV fun i ↦ (h i).conn⟩

theorem hasRep_of_local : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (g : ℕ), IsAbelianScheme A → (∀ s : S, ∃ V : S.Opens, s ∈ V ∧ HasRep A g (Over.mk V.ι)) → HasRep A g (𝟙_ _) := by
  intro S A _ g hA h
  choose V hV hR using h
  obtain ⟨B, P, hP, hG⟩ := GlobalTheory.T.exists_additiveFamily_representative_zariski_glue S A hA S V (fun _ ↦ g) (fun s ↦ ⟨s, hV s⟩) hR
  exact ⟨B, toUnit B, P, hP, Good.of_opens (Y := S) B.hom V (fun s ↦ ⟨s, hV s⟩) hG⟩

end GlobalTheory.DualCon
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelic_unitary_character_trivial_at_nonsplit_place : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ → ∀ v ε, NonSplitAt D v ε → ∀ ν : GA D V →* Circle, (∀ k, SuppPl ε V k → (∀ y, y ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) ↔ (finMat D.sp.cm.sig V.gram k).mulVec y ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E))) → ν k = 1) → ∀ g, SuppPl ε V g → ν g = 1 := by
  first | exact @GlobalTheory.InertChar.char_eq_one_of_nonSplit | exact GlobalTheory.InertChar.char_eq_one_of_nonSplit | (intros; apply GlobalTheory.InertChar.char_eq_one_of_nonSplit <;> assumption)
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HSShort.DetIdeal

theorem detSpan_relIndex_le : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (d : ℕ) (β : Module.Basis (Fin d) F V) (N₀ N : Submodule (𝓞 F) V), N₀ ≤ N → N₀.toAddSubgroup.relIndex N.toAddSubgroup ≠ 0 → Submodule.span (𝓞 F) {y | ∃ w : Fin d → V, (∀ i, w i ∈ N₀) ∧ y = β.det w} ≠ ⊥ → (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ y ∈ Submodule.span (𝓞 F) {y | ∃ w : Fin d → V, (∀ i, w i ∈ N) ∧ y = β.det w}, c • y ∈ (1 : Submodule (𝓞 F) F)) → (Submodule.span (𝓞 F) {y | ∃ w : Fin d → V, (∀ i, w i ∈ N₀) ∧ y = β.det w}).toAddSubgroup.relIndex (Submodule.span (𝓞 F) {y | ∃ w : Fin d → V, (∀ i, w i ∈ N) ∧ y = β.det w}).toAddSubgroup ≤ N₀.toAddSubgroup.relIndex N.toAddSubgroup := by
  intro F V _ _ _ _ _ _ d β N₀ N hle hidx hne hbdd
  classical
  set A : Submodule (𝓞 F) V → Submodule (𝓞 F) F :=
    fun P => Submodule.span (𝓞 F) {y | ∃ w : Fin d → V, (∀ i, w i ∈ P) ∧ y = β.det w} with hA
  have hmono : ∀ P P' : Submodule (𝓞 F) V, P ≤ P' → A P ≤ A P' := fun P P' h =>
    Submodule.span_mono fun y ⟨w, hw, hy⟩ => ⟨w, fun i => h (hw i), hy⟩
  show (A N₀).toAddSubgroup.relIndex (A N).toAddSubgroup ≤ N₀.toAddSubgroup.relIndex N.toAddSubgroup
  obtain ⟨c, hc0, hc⟩ := hbdd
  induction hn : N₀.toAddSubgroup.relIndex N.toAddSubgroup using Nat.strong_induction_on generalizing N₀ with
  | _ n ih =>
  rcases eq_or_lt_of_le hle with rfl | hlt
  · rw [AddSubgroup.relIndex_self]
    omega
  obtain ⟨u, p, hp, huN, hu0, hpu⟩ := GlobalTheory.T.exists_maximalIdeal_smul_mem_of_lt_of_relIndex_ne_zero F V N₀ N hlt hidx
  set N₁ := N₀ ⊔ Submodule.span (𝓞 F) {u} with hN₁
  have h01 : N₀ ≤ N₁ := le_sup_left
  have h1N : N₁ ≤ N := sup_le hle ((Submodule.span_singleton_le_iff_mem _ _).mpr huN)
  have hidx01 := GlobalTheory.T.relIndex_sup_span_singleton_eq_absNorm_of_isMaximal F V N₀ u p hp hu0 hpu
  have hmul := AddSubgroup.relIndex_mul_relIndex N₀.toAddSubgroup N₁.toAddSubgroup N.toAddSubgroup
    (Submodule.toAddSubgroup_mono h01) (Submodule.toAddSubgroup_mono h1N)
  rw [hidx01] at hmul
  have hpN : Ideal.absNorm p ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hmul; exact hidx hmul.symm
  have hp1 : 1 < Ideal.absNorm p := by
    rcases Nat.lt_or_ge 1 (Ideal.absNorm p) with h | h
    · exact h
    · exfalso
      have : Ideal.absNorm p = 1 := by omega
      exact hp.ne_top (Ideal.absNorm_eq_one_iff.mp this)
  have hidx1 : N₁.toAddSubgroup.relIndex N.toAddSubgroup ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hmul; exact hidx hmul.symm
  have hlt' : N₁.toAddSubgroup.relIndex N.toAddSubgroup < n := by
    rw [← hn, ← hmul]
    exact lt_mul_left (Nat.pos_of_ne_zero hidx1) hp1
  have hne1 : A N₁ ≠ ⊥ := fun h => hne (le_bot_iff.mp (h ▸ hmono _ _ h01))
  have ih' := ih _ hlt' N₁ h1N hidx1 hne1 rfl

  have hpA : p • A N₁ ≤ A N₀ := by
    rw [Submodule.smul_le]
    intro π hπ y hy
    exact GlobalTheory.T.smul_detSpan_sup_le_detSpan_lattice F V d β N₀ u π (hpu π hπ) y hy
  have hp0 : p ≠ ⊥ := by
    rintro rfl; exact hpN (by simp)
  have hfr := GlobalTheory.T.relIndex_ideal_smul_fractionalIdeal_eq_absNorm_numberField F (A N₁) p hp0 hne1 ⟨c, hc0, fun y hy => hc y (hmono _ _ h1N hy)⟩
  have hstep : (A N₀).toAddSubgroup.relIndex (A N₁).toAddSubgroup ≤ Ideal.absNorm p := by
    rw [← hfr]
    exact AddSubgroup.relIndex_le_of_le_left (Submodule.toAddSubgroup_mono hpA) (by rw [hfr]; exact hpN)
  have hmulA := AddSubgroup.relIndex_mul_relIndex (A N₀).toAddSubgroup (A N₁).toAddSubgroup (A N).toAddSubgroup
    (Submodule.toAddSubgroup_mono (hmono _ _ h01)) (Submodule.toAddSubgroup_mono (hmono _ _ h1N))
  rw [← hmulA, ← hn, ← hmul]
  exact Nat.mul_le_mul hstep ih'

theorem finPart_sub_mean_le_deg : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (nm : HermFam F V) (M : Submodule (𝓞 F) V) (d : ℕ) (b : Module.Basis (Fin d) F V), IsFull M → ∀ (τ : Type) (g : MvPolynomial τ F), g ≠ 0 → (∀ m, AddMonoidAlgebra.coeff g m ∈ Submodule.span (𝓞 F) {y | ∃ v : Fin d → V, (∀ i, v i ∈ M) ∧ y = b.det v}) → finPart g - mean F (fun σ => Real.log (nm.gram σ b).det.re) / 2 ≤ deg nm M := by
  intro F V _ _ _ _ _ _ nm M d b hM τ g hg hcoef
  classical
  have hfg := hM.fg
  have hsp := hM.span
  obtain ⟨r, v, hv⟩ : ∃ (r : ℕ) (v : Fin r → V), IsFrame F M v := ⟨_, exists_isFrame M hfg⟩
  have hspan : ⊤ ≤ Submodule.span F (Set.range v) := by
    rw [← hsp]
    exact Submodule.span_le.mpr hv.2.2
  let β : Module.Basis (Fin r) F V := Module.Basis.mk hv.2.1 hspan
  have hβ : ⇑β = v := Module.Basis.coe_mk _ _
  obtain rfl : r = d := by simpa using Fintype.card_congr (β.indexEquiv b)
  set δ := b.det v with hδ
  have hδ0 : δ ≠ 0 := by
    have := (b.isUnit_det β).ne_zero
    rwa [hβ] at this
  set L := Submodule.span (𝓞 F) (Set.range v) with hL
  set B := Submodule.span (𝓞 F) {y | ∃ w : Fin r → V, (∀ i, w i ∈ M) ∧ y = β.det w} with hB

  have hdet : ∀ w : Fin r → V, b.det w = δ * β.det w := fun w => by
    rw [hδ, ← hβ, Module.Basis.det_apply, Module.Basis.det_apply, Module.Basis.det_apply, ← Matrix.det_mul,
      Module.Basis.toMatrix_mul_toMatrix]
  have hcoef' : ∀ m, AddMonoidAlgebra.coeff g m / δ ∈ B := fun m => by
    let φ : F →ₗ[𝓞 F] F := (LinearMap.mulLeft F δ⁻¹).restrictScalars (𝓞 F)
    have hmap : (Submodule.span (𝓞 F) {y | ∃ v : Fin r → V, (∀ i, v i ∈ M) ∧ y = b.det v}).map φ ≤ B := by
      rw [Submodule.map_span_le]
      rintro _ ⟨w, hw, rfl⟩
      have : φ (b.det w) = β.det w := by
        simp only [φ, LinearMap.restrictScalars_apply, LinearMap.mulLeft_apply, hdet]
        field_simp
      rw [this]
      exact Submodule.subset_span ⟨w, hw, rfl⟩
    have := hmap (Submodule.mem_map_of_mem (f := φ) (hcoef m))
    simpa [φ, div_eq_inv_mul] using this
  have hLM : L ≤ M := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hv.1 i)
  have hidx : L.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0 := hv.relIndex_ne_zero hfg
  have hbase := GlobalTheory.T.span_basis_det_integral_eq_one F V r β
  rw [hβ] at hbase
  have hbdd := GlobalTheory.T.exists_common_denominator_span_det F V r β M hfg
  have hind := detSpan_relIndex_le F V r β L M hLM hidx (by rw [hbase]; intro h; have h1 : (1 : F) ∈ (1 : Submodule (𝓞 F) F) := Submodule.one_le.mp le_rfl; rw [h] at h1; simp at h1) hbdd
  rw [hbase] at hind
  have h1B : (1 : Submodule (𝓞 F) F) ≤ B := by
    rw [← hbase]
    exact Submodule.span_mono fun y ⟨w, hw, hy⟩ => ⟨w, fun i => hLM (hw i), hy⟩
  have hgauss := GlobalTheory.T.finsum_log_gaussAbs_le_fractionalIdeal_index F τ g hg B δ hδ0 h1B hbdd hcoef'
  have hprod := GlobalTheory.T.finsum_log_finitePlace_eq_neg_log_abs_norm' F δ hδ0
  have hn : (0 : ℝ) < Module.finrank ℚ F := by exact_mod_cast Module.finrank_pos

  have hG : ∀ σ : F →+* ℂ, Real.log (nm.gram σ v).det.re = Real.log (Complex.normSq (σ δ)) + Real.log (nm.gram σ b).det.re := by
    intro σ
    rw [GlobalTheory.T.hermFam_gram_det_eq_normSq_basis_det_mul F V nm σ r b v, ← hδ]
    have hpos : 0 < (nm.gram σ ⇑b).det.re := by
      open scoped ComplexOrder in
      have hp := nm.posDef σ r b b.linearIndependent
      unfold HermFam.gram
      rw [hp.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
      change 0 < ∏ i, hp.isHermitian.eigenvalues i
      exact Finset.prod_pos fun i _ => hp.eigenvalues_pos i
    have hn0 : 0 < Complex.normSq (σ δ) := Complex.normSq_pos.mpr ((map_ne_zero σ).mpr hδ0)
    rw [Complex.re_ofReal_mul, Real.log_mul hn0.ne' hpos.ne']
  have hsum := ds_sum_log_normSq_embeddings δ hδ0
  rw [arakelovDegree_eq_degreeOfFamily nm hfg hv, degreeOfFamily, finPart, mean]
  simp only [hG, Finset.sum_add_distrib, hsum]
  have hlog : Real.log ((1 : Submodule (𝓞 F) F).toAddSubgroup.relIndex B.toAddSubgroup : ℝ) ≤ Real.log (L.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) := by
    rcases Nat.eq_zero_or_pos ((1 : Submodule (𝓞 F) F).toAddSubgroup.relIndex B.toAddSubgroup) with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hidx)
    · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hind)
  have hkey : ∑ᶠ q : FinitePlace F, Real.log (gaussAbs q g) ≤
      Real.log (L.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) - Real.log |((Algebra.norm ℚ δ : ℚ) : ℝ)| := by
    linarith
  calc _ = ((∑ᶠ q : FinitePlace F, Real.log (gaussAbs q g)) - (∑ σ : F →+* ℂ, Real.log (nm.gram σ ⇑b).det.re) / 2) /
        (Module.finrank ℚ F : ℝ) := by ring
    _ ≤ (Real.log (L.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) - 1 / 2 * (2 * Real.log |((Algebra.norm ℚ δ : ℚ) : ℝ)| +
        ∑ σ : F →+* ℂ, Real.log (nm.gram σ ⇑b).det.re)) / (Module.finrank ℚ F : ℝ) := by
      apply div_le_div_of_nonneg_right _ hn.le
      linarith
    _ = _ := by ring

end GlobalTheory.HSShort.DetIdeal
end
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem sqrtNegNat_im_ne_zero {p : ℕ} (hp : 0 < p) : (sqrtNegNat p).im ≠ 0 := by
  have : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.2 (by exact_mod_cast hp)
  simpa [sqrtNegNat] using this.ne'

theorem modelAt_one_of_sqProd_mem : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ),
    p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → sqProd p L t ∈ F →
    ∀ V : ValuationSubring ℂ, V.valuation (p : ℂ) = 1 → ModelAt V F (latticeCurve L) 1 := by
  intro p F L t hp hp4 hp3 hD hQ V hVp
  have hβ : (sqrtNegNat p).im ≠ 0 := sqrtNegNat_im_ne_zero hp.pos
  have hΔF : (latticeCurve L).Δ ∈ F := by
    rw [latticeCurve_Δ]
    exact sub_mem (pow_mem hD.g₂_mem 3) (mul_mem (by simpa using (algebraMap_mem F (27 : ℚ))) (pow_mem hD.g₃_mem 2))
  obtain ⟨A, hAF, hA0, hAv⟩ := GlobalTheory.T.exists_cube_valuation_eq_discriminant p F L t hp hp4 hp3 hD V
  obtain ⟨u, huF, hu0, huv⟩ := GlobalTheory.T.exists_valuation_pow_twelve_mul_eq p V F (latticeCurve L).Δ A (sqProd p L t) hp4 hΔF hAF hQ
    (latticeCurve_Δ_ne_zero L) hA0 hAv (GlobalTheory.T.prodDerivWeierstrassPOverSquares_pow_eight_mul p F L t hp hp4 hp3 hD)
  rw [hVp, one_pow, mul_one] at huv
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  by_cases h2 : V.valuation (2 : ℂ) = 1
  · by_cases h3 : V.valuation (3 : ℂ) = 1
    ·
      have h6 : V.valuation (6 : ℂ) = 1 := by
        rw [show (6 : ℂ) = 2 * 3 by norm_num, map_mul, h2, h3, one_mul]
      have hj : (latticeCurve L).j ∈ V :=
        ReciprocityTheory.Gal.mem_of_isIntegral_int V (GlobalTheory.T.isIntegral_j_of_nonreal_multiplier L (sqrtNegNat p) hD.mul hβ)
      exact GlobalTheory.T.modelAt_short_of_valuation_six_eq_one V F (-L.g₂ / 4) (-L.g₃ / 4) (latticeCurve L).j u 1 hj
        (GlobalTheory.j_mul_Δ (latticeCurve L)) h6 huF hu0 (one_mem V) (by rw [map_one, mul_one]; exact huv)
    ·
      obtain ⟨N, ι, hι, T, hNodd, hN3, hNv, hcard, hT, hTor⟩ := GlobalTheory.T.exists_galoisStable_torsion_family_ker p F L t hp hp4 hp3 hD V
      have hcop : Nat.Coprime (Fintype.card ι) 3 := by
        rw [hcard]
        exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega))
      have hc : V.valuation (Fintype.card ι : ℂ) = 1 := by
        rcases GlobalTheory.T.valuation_natCast_eq_one_or_of_coprime V _ _ hcop with h | h
        · exact h
        · exact absurd (by simpa using h) h3
      exact GlobalTheory.T.exists_integralModel_of_galoisStable_torsion L (sqrtNegNat p) u V N hD.mul hβ huv hNv hNodd F ι T hD.g₂_mem hD.g₃_mem huF
        hT hTor hc
  ·
    obtain ⟨-, hodd'⟩ := GlobalTheory.T.two_mul_card_sq_add_one_eq_and_odd_of_mod_four_eq_three p hp hp4
    have hcop : Nat.Coprime (Fintype.card (Sq p)) 2 :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by rcases hodd' with ⟨k, hk⟩; omega))
    have hc : V.valuation (Fintype.card (Sq p) : ℂ) = 1 := by
      rcases GlobalTheory.T.valuation_natCast_eq_one_or_of_coprime V _ _ hcop with h | h
      · exact h
      · exact absurd (by simpa using h) h2
    exact GlobalTheory.T.exists_integralModel_of_galoisStable_torsion L (sqrtNegNat p) u V p hD.mul hβ huv hVp hodd F (Sq p) (sqPt p t)
      hD.g₂_mem hD.g₃_mem huF ((GlobalTheory.T.prodDerivWeierstrassPOverSquares_sq_mem_stable p F L t hp hp4 hp3 hD).2 hQ)
      (GlobalTheory.T.prodDerivWeierstrassPOverSquares_ne_zero p F L t hp hp4 hp3 hD).1 hc

end GlobalTheory.CMModel
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.chowForm_zeroSet_extensionField_iff_common_cone_zero : ∀ (F : Type) [Field F] [CharZero F] (D N d : ℕ) (I : Ideal (MvPolynomial (Fin N) F)) (f : MvPolynomial (Fin (D + 1) × Fin N) F), IsChowForm I D d f → (∀ (Ω : Type) [Field Ω] [Algebra F Ω] (s : Fin D → Fin N → Ω) (ξ y : Fin N → Ω), y ≠ 0 → (∀ g ∈ I, aeval y g = 0) → (∀ i, ∑ j, s i j * y j = 0) → ∑ j, ξ j * y j = 0 → aeval (join s ξ) f = 0) ∧ (∀ (Ω : Type) [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] (s : Fin D → Fin N → Ω) (ξ : Fin N → Ω), aeval (join s ξ) f = 0 → ∃ y : Fin N → Ω, y ≠ 0 ∧ (∀ g ∈ I, aeval y g = 0) ∧ (∀ i, ∑ j, s i j * y j = 0) ∧ ∑ j, ξ j * y j = 0) := by
  first | exact @GlobalTheory.ChowZeroExt.zero_set_ext | exact GlobalTheory.ChowZeroExt.zero_set_ext | (intros; apply GlobalTheory.ChowZeroExt.zero_set_ext <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.rationalSquaringPathsRigid_of_proper_charZero : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (H : Over (Sp Ω)) [GrpObj H], IsProper H.hom → RatRigid H (𝟙 (Sp Ω)) := by
  first | exact @GlobalTheory.Nef.ratRigid_of_isProper_of_charZero | exact GlobalTheory.Nef.ratRigid_of_isProper_of_charZero | (intros; apply GlobalTheory.Nef.ratRigid_of_isProper_of_charZero <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.smooth_snc_component_closure_charZero : ∀ (F : Type) [Field F] [CharZero F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (e : ℕ), IsProjOver p → SmoothOfRelativeDimension (e + 1) p → ∀ (r : ℕ) (z : Fin r → X), (∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x) → ∀ a, SmoothOfRelativeDimension e (closι (z a) ≫ p) := by
  first | exact @GlobalTheory.SncComp.smooth_component | exact GlobalTheory.SncComp.smooth_component | (intros; apply GlobalTheory.SncComp.smooth_component <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.HSNef.Den

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem one_mem_H (P : Pair p) : (1 : X.functionField) ∈ P.H 0 0 := by
  intro x i j _ _
  exact ⟨1, by simp [Pair.loc]⟩

theorem mul_mem_H {P : Pair p} {a b a' b' : ℤ} {f g : X.functionField} (hf : f ∈ P.H a b) (hg : g ∈ P.H a' b') :
    f * g ∈ P.H (a + a') (b + b') :=
  (NuMul.mul_mem_H_and_nu_mul k X p P a b a' b' f g hf hg).1

theorem prod_mem_H {P : Pair p} {J : Type} (s : Finset J) (c : J → ℕ) (g : J → X.functionField)
    (hg : ∀ j ∈ s, g j ∈ P.H 0 (c j)) : (∏ j ∈ s, g j) ∈ P.H 0 ((∑ j ∈ s, c j : ℕ) : ℤ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one_mem_H P
  | insert l s hl ih =>
    rw [Finset.prod_insert hl, Finset.sum_insert hl]
    have := mul_mem_H (hg l (Finset.mem_insert_self l s)) (ih fun j hj => hg j (Finset.mem_insert_of_mem hj))
    simpa using this

theorem exists_clear_denominators : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.A.B → ∀ (a : ℤ) (J : Type) [Finite J] (f : J → X.functionField), ∃ (c : ℕ) (g : X.functionField), 0 < c ∧ g ≠ 0 ∧ g ∈ P.H a c ∧ ∀ j, g * f j ∈ P.H a c := by
  intro k _ X _ p D hX P hA a J _ f
  classical
  have := Fintype.ofFinite J
  choose c g hc hg0 hg hgf using fun j => GlobalTheory.T.exists_ampleSection_clearing_rationalFunction_denominator k X p D hX P hA (f j)
  obtain ⟨c', h, hc', h0, hh⟩ := GlobalTheory.T.exists_pos_nonzero_pairSection_of_ample k X p D hX P hA a
  refine ⟨c' + ∑ j, c j, h * ∏ j, g j, by omega, mul_ne_zero h0 (Finset.prod_ne_zero_iff.2 fun j _ => hg0 j), ?_, fun j => ?_⟩
  · have := mul_mem_H hh (prod_mem_H Finset.univ c g fun j _ => hg j)
    simpa using this
  · have e : h * (∏ l, g l) * f j = h * ((g j * f j) * ∏ l ∈ Finset.univ.erase j, g l) := by
      rw [← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ j)]; ring
    have es : ∑ l, c l = c j + ∑ l ∈ Finset.univ.erase j, c l := (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
    rw [e, es]
    have := mul_mem_H hh (mul_mem_H (hgf j) (prod_mem_H (Finset.univ.erase j) c g fun l _ => hg l))
    simpa using this

end GlobalTheory.HSNef.Den
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.extremalVector_matrixCoeff_holomorphicType : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → HolFn (gramAt D V) (fun τ => nNeg (M.ε τ)) (x0Mat M) w (fun u => ∏ τ, ⟪(v τ : M.H τ), M.rep τ (u τ) (v τ : M.H τ)⟫_ℂ) ∧ ∀ s τ, M.rep τ (torEl (x0Mat M) s τ) (v τ : M.H τ) = (∏ a, Complex.exp ((s τ a : ℂ) * Complex.I) ^ w τ a) • (v τ : M.H τ) := by
  first | exact @GlobalTheory.HolDict.holFn_coef_extVec | exact GlobalTheory.HolDict.holFn_coef_extVec | (intros; apply GlobalTheory.HolDict.holFn_coef_extVec <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.log_card_smallSections_ge_of_shift_nef : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ (a c : ℤ) (M : HermLB p) (α t₀ : ℝ), P.Rep a c M → M.IsSelfInter α → (M.shift (fun _ => t₀) fun _ => rfl).IsNef D → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, (α / (D + 1).factorial - ε) * (m : ℝ) ^ (D + 1) ≤ P.lc (m * a) (m * c) 1 := by
  first | exact @GlobalTheory.VolBr.log_ncard_ball_one_ge_of_shift_nef | exact GlobalTheory.VolBr.log_ncard_ball_one_ge_of_shift_nef | (intros; apply GlobalTheory.VolBr.log_ncard_ball_one_ge_of_shift_nef <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.smallSectionCount_nearPowers_le : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ m : ℕ in atTop, P.lc 0 (b * (n * m : ℕ) + m) 2 ≤ P.lc 0 (b * (n * m : ℕ)) 1 + ε * ((n : ℝ) * m) ^ (D + 1) := by
  first | exact @GlobalTheory.VolBr.lc_two_le_lc_one_add | exact GlobalTheory.VolBr.lc_two_le_lc_one_add | (intros; apply GlobalTheory.VolBr.lc_two_le_lc_one_add <;> assumption)
end
