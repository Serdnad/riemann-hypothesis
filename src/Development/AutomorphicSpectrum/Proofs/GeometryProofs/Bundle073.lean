module

import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.WeilBound.CoreStatements.HodgeTatePoints.MlLift
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle002
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderFlatBaseChange
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle004
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle011
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle063
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle015
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle024
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle037
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle025
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.WeilBound.CoreStatements.IdealCycleValues.IsModelOverRamifiedBaseChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesHodgeTate
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Mathlib.Topology.Sheaves.Presheaf
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open PositivityTheory.HtPt.Ml (generic_max mem_of_dense_of_max)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.Ar.M0

theorem genericPoints_subset_range_j :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
      (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O]
      (β : O →+* c.F) (Y : Model Xo c β),
      IsDomain O → (letI := β.toAlgebra; IsFractionRing O c.F) →
        genericPoints Y.X ⊆ Set.range Y.j := by
  apply PositivityTheory.HtPt.Ml.generic_points_range <;> assumption

end GlobalTheory.CompanionTheory.Ar.M0
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem exists_modelPoint_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (j : K →+* ℂ_[p]) (βK : c.F →+* K) (y : Sp K ⟶ Xo.XF c),
    (∀ x : c.F, ‖κ x‖ ≤ 1 ↔ x ∈ β.range) → (∀ a : K, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V K).range) → j.comp βK = κ →
    y ≫ pullback.snd _ _ = spMap βK → ∃ z : Sp V ⟶ Y.X, spMap (algebraMap V K) ≫ z = y ≫ Y.j := by
  intro E _ _ _ H D l Xo c O _ _ _ β Y p κ V K _ _ _ _ _ _ j βK y hκ hj hjκ hy
  have hpr : IsProper Y.s := GlobalTheory.SchemeWords.isProper_of_isProjOver Y.proj
  have hmem : ∀ o : O, (βK.comp β) o ∈ (algebraMap V K).range := by
    intro o
    refine (hj _).1 ?_
    have h1 : j (βK (β o)) = κ (β o) := by rw [← hjκ]; rfl
    simp only [RingHom.comp_apply]
    rw [h1]
    exact (hκ _).2 ⟨o, rfl⟩
  let e : V ≃+* (algebraMap V K).range :=
    RingEquiv.ofBijective (algebraMap V K).rangeRestrict
      ⟨fun a b h => IsFractionRing.injective V K (congrArg Subtype.val h),
        (algebraMap V K).rangeRestrict_surjective⟩
  let b : O →+* V := e.symm.toRingHom.comp ((βK.comp β).codRestrict _ hmem)
  have hb : (algebraMap V K).comp b = βK.comp β := by
    ext o
    have h2 : e (b o) = (βK.comp β).codRestrict _ hmem o := e.apply_symm_apply _
    exact congrArg Subtype.val h2
  have hsq : (y ≫ Y.j) ≫ Y.s = Spec.map (CommRingCat.ofHom ((algebraMap V K).comp b)) := by
    rw [hb]
    have h3 : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
      simp only [Model.j, Category.assoc]
      rw [pullback.condition, ← Category.assoc, Y.jQ_over]
    rw [Category.assoc, h3, ← Category.assoc, hy]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨z, ⟨hz, _⟩, _⟩ := existsUnique_valuationRing_lift O V K b Y.X Y.s (y ≫ Y.j) hsq
  exact ⟨z, hz⟩

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.btOrder_flat_base_change : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → Module.Flat R R' → Γ'.btOrder ⊤ = extOrder (algebraMap R R') (Γ.btOrder ⊤) := by
  exact @GlobalTheory.CompanionTheory.Ar.BT.FlatBC.btOrder_flat_baseChange
end

section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

theorem _root_.GlobalTheory.T.triv_flag_mod_of_dvd : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ϖ ϖ' : o) (N : ℕ) (b : Fin N → K → ℤ), ϖ' ∣ ϖ → Num.TrivFlagMod o ϖ y N b → Num.TrivFlagMod o ϖ' y N b := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.trivFlagMod_of_dvd | exact GlobalTheory.CompanionTheory.Ar.HT.trivFlagMod_of_dvd | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.trivFlagMod_of_dvd <;> assumption)
end

section

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

namespace GlobalTheory.CompanionTheory.Ar.Cmp.IsoLines

theorem isoLineOn_comb_trans_symm_pull : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (Xo : Set ((Σ k, ι k) → ℂ)), IsMultiProjPrime P → Xo ⊆ mcPts P → (∀ (J : Type) [Fintype J] (ℓ ℓ' : J → HermLine ι) (n : J → ℤ), (∀ j, IsoLineOn P Xo (ℓ j) (ℓ' j)) → IsoLineOn P Xo (Top.combLine ℓ n) (Top.combLine ℓ' n)) ∧ (∀ A B C : HermLine ι, IsoLineOn P Xo A B → IsoLineOn P Xo B C → IsoLineOn P Xo A C) ∧ (∀ A B : HermLine ι, IsoLineOn P Xo A B → IsoLineOn P Xo B A) ∧ ∀ (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (κ : K₁ → K) (v : (Σ k, ι₁ k) → Σ k, ι k) (J : Type) [Fintype J] (ℓ : J → HermLine ι₁) (ℓ' : J → HermLine ι) (n : J → ℤ), IsBlockMap κ v → (∀ j, IsPullHerm κ v (ℓ j) (ℓ' j)) → IsPullHerm κ v (Top.combLine ℓ n) (Top.combLine ℓ' n) :=
  @PositivityTheory.UnitarySelfGeneration.i_comb

end GlobalTheory.CompanionTheory.Ar.Cmp.IsoLines
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem exists_pow_mul_mem_chart {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {κ : Type} {x : κ → Ω} (T : CoordTie ℤ ξ x) {c : κ} (hc : x c ≠ 0) (m : ℕ) (τ : Ω)
    (hτ : ∀ q : Cpt ξ, InChart ξ x c q → unitAt ξ q (m : Ω) → τ ∈ regAt ξ q) :
    ∃ n : ℕ, (m : Ω) ^ n * τ ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) := by
  let B := Algebra.adjoin ℤ (Set.range fun j => x j / x c)
  let I : Ideal B :=
    { carrier := {r | (r : Ω) * τ ∈ B}
      add_mem' := by
        intro a b ha hb
        have ha' : (a : Ω) * τ ∈ B := ha
        have hb' : (b : Ω) * τ ∈ B := hb
        have h := add_mem ha' hb'
        rw [← add_mul] at h
        exact h
      zero_mem' := by
        show ((0 : B) : Ω) * τ ∈ B
        simp
      smul_mem' := by
        intro r a ha
        have ha' : (a : Ω) * τ ∈ B := ha
        have h := mul_mem r.2 ha'
        rw [← _root_.mul_assoc] at h
        exact h }
  have hmem : (m : B) ∈ I.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro Q ⟨hIQ, hQ⟩
    by_contra hmQ
    obtain ⟨q, ⟨hqc, hq⟩, -⟩ := chart_point_of_prime X Ω ξ ℤ κ x T c hc Q hQ
    have hu : unitAt ξ q (((m : B) : B) : Ω) := (hq (m : B)).1 hmQ
    have hu' : unitAt ξ q (m : Ω) := by simpa using hu
    obtain ⟨s, hsB, hsu, hsτ⟩ :=
      (regAt_iff_exists_chart_fraction X Ω ξ ℤ κ x T c q hqc τ).1 (hτ q hqc hu')
    have hsQ : (⟨s, hsB⟩ : B) ∈ Q := hIQ hsτ
    exact (hq ⟨s, hsB⟩).2 hsu hsQ
  obtain ⟨n, hn⟩ := hmem
  refine ⟨n, ?_⟩
  have h : (((m : B) ^ n : B) : Ω) * τ ∈ B := hn
  simpa using h

theorem unitAt_natCast_of_dvd {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (q : Cpt ξ) {p m : ℕ} (hd : p ∣ m) (hm : unitAt ξ q (m : Ω)) : unitAt ξ q (p : Ω) := by
  obtain ⟨w, rfl⟩ := hd
  obtain ⟨h0, -, hinv⟩ := hm
  have hc : (((p * w : ℕ) : Ω)) = (p : Ω) * (w : Ω) := by push_cast; ring
  rw [hc] at h0 hinv
  have hp : (p : Ω) ≠ 0 := left_ne_zero_of_mul h0
  have hw : (w : Ω) ≠ 0 := right_ne_zero_of_mul h0
  refine ⟨hp, natCast_mem _ p, ?_⟩
  have he : (p : Ω)⁻¹ = (w : Ω) * ((p : Ω) * (w : Ω))⁻¹ := by field_simp
  rw [he]
  exact mul_mem (natCast_mem _ w) hinv


variable {Ω' : Type} [Field Ω'] in
theorem div_mem_of_mem_span {R : Subring Ω'} {v w : Ω'} (hw : w ≠ 0) (h : v ∈ Submodule.span R {w}) :
    v / w ∈ R := by
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 h
  have hr' : (r : Ω') * w = v := hr
  rw [← hr', mul_div_cancel_right₀ _ hw]
  exact r.2

theorem exists_pow_chart_quotients {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}
    (T : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩))
    {L L' : Lat ξ Ω} {a a' : K → ℤ} {e e' : Ω} (hL : L.IsDegOn Set.univ y a e)
    (hL' : L'.IsDegOn Set.univ y a' e') (S : Finset Nat.Primes)
    (hS : ∀ q : Cpt ξ, (∀ p ∈ S, ¬ InFibre ξ p q) → L q = L' q)
    (c : (k : K) → J k) (hc : ∏ k, y ⟨k, c k⟩ ≠ 0) :
    (∃ n : ℕ, ((∏ p ∈ S, (p : ℕ) : ℕ) : Ω) ^ n *
        (((∏ k, y ⟨k, c k⟩ ^ a' k) * e') / ((∏ k, y ⟨k, c k⟩ ^ a k) * e)) ∈
        Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩)) ∧
      ∃ n : ℕ, ((∏ p ∈ S, (p : ℕ) : ℕ) : Ω) ^ n *
        (((∏ k, y ⟨k, c k⟩ ^ a k) * e) / ((∏ k, y ⟨k, c k⟩ ^ a' k) * e')) ∈
        Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) := by
  have key : ∀ q : Cpt ξ, InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c q →
      unitAt ξ q ((∏ p ∈ S, (p : ℕ) : ℕ) : Ω) →
      Submodule.span (regAt ξ q) {(∏ k, y ⟨k, c k⟩ ^ a k) * e} =
        Submodule.span (regAt ξ q) {(∏ k, y ⟨k, c k⟩ ^ a' k) * e'} := by
    intro q hq hm
    have h1 := hL.2 q (Set.mem_univ q) c hq
    have h2 := hL'.2 q (Set.mem_univ q) c hq
    rw [smul_eq_mul] at h1 h2
    rw [← h1, ← h2]
    refine hS q fun p hp hf => hf ?_
    exact unitAt_natCast_of_dvd q (Finset.dvd_prod_of_mem (fun p : Nat.Primes => (p : ℕ)) hp) hm
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc k (Finset.mem_univ k)
  have hu : (∏ k, y ⟨k, c k⟩ ^ a k) * e ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)) hL.1
  have hu' : (∏ k, y ⟨k, c k⟩ ^ a' k) * e' ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)) hL'.1
  constructor
  · refine exists_pow_mul_mem_chart T hc _ _ fun q hq hm => div_mem_of_mem_span hu ?_
    rw [key q hq hm]
    exact Submodule.mem_span_singleton_self _
  · refine exists_pow_mul_mem_chart T hc _ _ fun q hq hm => div_mem_of_mem_span hu' ?_
    rw [← key q hq hm]
    exact Submodule.mem_span_singleton_self _

theorem lat_vertOff : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ d : ℕ, IsArithVar (mCoordIdeal y) (d + 1) → ∀ (L L' : Lat ξ Ω) (a a' : K → ℤ) (e e' : Ω), L.IsDegOn Set.univ y a e → L'.IsDegOn Set.univ y a' e' → ∀ S : Finset Nat.Primes, (∀ q : Cpt ξ, (∀ p ∈ S, ¬ InFibre ξ p q) → L q = L' q) → ∃ f g : MvPolynomial (Σ k, J k) ℤ, (⟨fun _ => a, fun _ => a', fun _ => f, fun _ => g⟩ : LocPair J ℤ Unit).IsVertOff (mCoordIdeal y) S ∧ aeval y f = e' / e * aeval y g := by
  intro X Ω _ ξ K _ _ J _ y T d hA L L' a a' e e' hL hL' S hS
  have hrel : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hA.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    rw [mCoordIdeal, RingHom.mem_ker]
    simp [mConeMap, h0]
  have hproj : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiProjPrime (pointIdeal ℤ y) :=
    GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDim.isMultiProjPrime_pointIdeal y hrel
  have he : e ≠ 0 := hL.1
  have he' : e' ≠ 0 := hL'.1
  refine GlobalTheory.T.degree_lattice_prime_scaling K J Ω y hproj S a a' (e' / e) (div_ne_zero he' he) ?_ hA.2.2.1
  intro c hc
  have hc' : ∏ k, y ⟨k, c k⟩ ≠ 0 := hc
  obtain ⟨⟨n, hn⟩, ⟨n', hn'⟩⟩ := exists_pow_chart_quotients T hL hL' S hS c hc'
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc' k (Finset.mem_univ k)
  have hY : (∏ k, y ⟨k, c k⟩ ^ a k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)
  have hY' : (∏ k, y ⟨k, c k⟩ ^ a' k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)
  constructor
  · rintro t ⟨A, hAm, rfl⟩
    have hAm' : A ∈ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k =>
        (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) := hAm
    refine ⟨n', _, ⟨_, mul_mem hn' hAm', rfl⟩, ?_⟩
    generalize (∏ k, y ⟨k, c k⟩ ^ a k) = Y at hY
    generalize (∏ k, y ⟨k, c k⟩ ^ a' k) = Y' at hY'
    field_simp
  · rintro t ⟨A, hAm, rfl⟩
    have hAm' : A ∈ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k =>
        (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) := hAm
    refine ⟨n, _, ⟨_, mul_mem hn hAm', rfl⟩, ?_⟩
    generalize (∏ k, y ⟨k, c k⟩ ^ a k) = Y at hY
    generalize (∏ k, y ⟨k, c k⟩ ^ a' k) = Y' at hY'
    field_simp

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver)

theorem _root_.GlobalTheory.T.exists_isometric_herm_line : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (S : Finset Nat.Primes) (T : LocPair ι ℤ Unit), T.IsVertOff P S → ∀ A : HermLine ι, A.a = T.x () → IsSmoothHerm A → IsConjInvariantH A → ∃ A' : HermLine ι, IsSmoothHerm A' ∧ IsConjInvariantH A' ∧ T.IsIsometric P (fun _ => A) (fun _ => A') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.twist_line | exact GlobalTheory.CompanionTheory.Ar.Num.twist_line | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.twist_line <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem numbers_divCycle_baseChange_dvr : ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] (ϖ : O) (ϖ' : O') (u : O'ˣ) (e : ℕ), Irreducible ϖ → Irreducible ϖ' → 0 < e → algebraMap O O' ϖ = u * ϖ' ^ e → ∀ (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MvPolynomial (Σ k, J k) O)) (d : ℕ), IsModelOver P d → IsModelOver (P.map (MvPolynomial.map (algebraMap O O'))) d → ∀ (a : K → ℕ) (f : MvPolynomial (Σ k, J k) O), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f a → f ∉ P → ∀ l : List (K → ℤ), l.length = d → cycList (divCycle (P.map (MvPolynomial.map (algebraMap O O'))) (MvPolynomial.map (algebraMap O O') f)) l = e * cycList (divCycle P f) l :=
  BaseChangeColon.isModelOver_ramified_base_change

end GlobalTheory.CompanionTheory.Ar.Num
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

def lieModelOfEquiv {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} {F F' : Type} [AddCommGroup F] [Module R F] [AddCommGroup F'] [Module R F']
    (M : LieModel G x F) (e : F' ≃ₗ[R] F) : LieModel G x F' where
  pt v := M.pt (e v)
  tan v := M.tan _
  inj := M.inj.comp e.injective
  onto v hv := by
    obtain ⟨w, h⟩ := M.onto v hv
    exact ⟨e.symm w, by simpa using h⟩
  add v w := by rw [map_add (f := _), M.add]
  smul c v := by rw [map_smul, M.smul]

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.embedding_base_change_compat : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → ∀ (A : Subalgebra R (T → R)) (A' : Subalgebra R' (T → R')) (ψ : A →+* A'), (∀ (a : A) t, (ψ a).1 t = algebraMap R R' (a.1 t)) → ∀ (j : Γ.G.left ⟶ Spec (CommRingCat.of A)) (j' : Γ'.G.left ⟶ Spec (CommRingCat.of A')), Γ.IsEmb A j → Γ'.IsEmb A' j' → F ≫ j = j' ≫ Spec.map (CommRingCat.ofHom ψ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.isEmb_baseChange_square | exact GlobalTheory.CompanionTheory.Ar.BT.isEmb_baseChange_square | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.isEmb_baseChange_square <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.existsUnique_btOrder_embedding : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T), ∃! j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤)), Γ.IsEmb (Γ.btOrder ⊤) j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.exists_unique_emb_btOrder_top | exact GlobalTheory.CompanionTheory.Ar.BT.exists_unique_emb_btOrder_top | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.exists_unique_emb_btOrder_top <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem _root_.GlobalTheory.T.regAt_local_order_fraction : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), (∀ p : Cpt ξ, IsLocalRing (regAt ξ p)) ∧ (∀ p q : Cpt ξ, q.1 ⤳ p.1 → regAt ξ p ≤ regAt ξ q) ∧ (IsCptGen ξ → ∀ (p : Cpt ξ) (a : Ω), ∃ u ∈ regAt ξ p, ∃ v ∈ regAt ξ p, v ≠ 0 ∧ a = u / v) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.regAt_local_mono_frac | exact GlobalTheory.CompanionTheory.Ar.regAt_local_mono_frac | (intros; apply GlobalTheory.CompanionTheory.Ar.regAt_local_mono_frac <;> assumption)
end
