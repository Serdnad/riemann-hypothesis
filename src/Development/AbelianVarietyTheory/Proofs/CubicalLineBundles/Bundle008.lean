module

public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.LinearAlgebra.Span.Defs
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DiagZEqNegAddY
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle002
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve
open scoped CategoryTheory.Obj UpperHalfPlane

noncomputable section

namespace GlobalTheory.WeierstrassCurve.OriginTangent

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) {A : Type} [CommRing A]

theorem ptHom_origin_inj {ρ ρ' : R →+* A} {z w z' w' : A}
    (h : IsUnimodularSol (W.map ρ) ![z, -1, w]) (h' : IsUnimodularSol (W.map ρ') ![z', -1, w'])
    (e : ptHom W ρ ![z, -1, w] h = ptHom W ρ' ![z', -1, w'] h') : z = z' ∧ w = w' := by
  have e₁ := (SpecMap_originEval_chartY W ρ z w h.equation).trans
    (e.trans (SpecMap_originEval_chartY W ρ' z' w' h'.equation).symm)
  rw [cancel_mono] at e₁
  have e' : originEval W ρ z w h.equation = originEval W ρ' z' w' h'.equation :=
    congrArg (·.hom) (Spec.map_injective e₁)
  exact ⟨(originEval_originZ ..).symm.trans
      ((RingHom.congr_fun e' (originZ W)).trans (originEval_originZ ..)),
    (originEval_originW ..).symm.trans
      ((RingHom.congr_fun e' (originW W)).trans (originEval_originW ..))⟩

theorem exists_eq_ptHom_origin (ρ : R →+* A) (g : Spec (.of A) ⟶ scheme W)
    (hY : ∀ p, g p ∈ coordOpen W 1) (hg : g ≫ toSpec W = Spec.map (CommRingCat.ofHom ρ)) :
    ∃ (z w : A) (h : IsUnimodularSol (W.map ρ) ![z, -1, w]), g = ptHom W ρ ![z, -1, w] h := by
  have hr : Set.range g ⊆ Set.range (chartY W) := by
    rintro _ ⟨p, rfl⟩
    rw [← Scheme.Hom.coe_opensRange, opensRange_chartY]
    exact hY p
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (IsOpenImmersion.lift _ _ hr)
  have hl : Spec.map ψ ≫ chartY W = g := hψ ▸ IsOpenImmersion.lift_fac _ _ hr
  have hc : ψ.hom.comp (algebraMap R (OriginRing W)) = ρ := by
    rw [← hl, Category.assoc, chartY_toSpec, ← Spec.map_comp] at hg
    exact congrArg (·.hom) (Spec.map_injective hg)
  have hP : (ψ.hom ∘ ![originZ W, -1, originW W]) =
      ![ψ.hom (originZ W), -1, ψ.hom (originW W)] := by
    ext1 j; fin_cases j <;> simp
  have h₀ : IsUnimodularSol (W.map (algebraMap R (OriginRing W))) ![originZ W, -1, originW W] :=
    isUnimodularSol_origin (equation_originZ_originW W)
  have h₁ := h₀.map_comp ψ.hom
  have h₂ : IsUnimodularSol (W.map ρ) ![ψ.hom (originZ W), -1, ψ.hom (originW W)] := by
    rw [← hc, ← hP]; exact h₁
  refine ⟨_, _, h₂, ?_⟩
  rw [← hl]
  exact (SpecMap_ptHom W _ _ h₀ ψ.hom).trans (ptHom_congr W _ _ _ hc hP _)

theorem SpecMap_zero_origin (ρ : R →+* A) (h : IsUnimodularSol (W.map ρ) ![0, -1, 0]) :
    Spec.map (CommRingCat.ofHom ρ) ≫ zero W = ptHom W ρ ![0, -1, 0] h := by
  rw [SpecMap_zero, ← ptHom_smul W ρ _ _ isUnit_one.neg]
  exact ptHom_congr W _ _ _ rfl (by ext1 j; fin_cases j <;> simp) _

theorem isUnimodularSol_zero_neg (V : WeierstrassCurve A) : IsUnimodularSol V ![0, -1, 0] :=
  isUnimodularSol_origin (by rw [equation_origin_iff]; simp)

theorem exists_eq_ptHom_eps (f : R →+* A) (g : Spec (.of (DualNumber A)) ⟶ scheme W)
    (hg : g ≫ toSpec W =
      Spec.map (CommRingCat.ofHom ((algebraMap A (DualNumber A)).comp f)))
    (h0 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) ≫ g =
      Spec.map (CommRingCat.ofHom f) ≫ zero W) :
    ∃ (c : A) (h : IsUnimodularSol (W.map ((algebraMap A (DualNumber A)).comp f))
      ![TrivSqZeroExt.inr c, -1, 0]),
      g = ptHom W ((algebraMap A (DualNumber A)).comp f) ![TrivSqZeroExt.inr c, -1, 0] h := by
  have hY : ∀ p, g p ∈ coordOpen W 1 := by
    intro p
    have hs : Function.Surjective (PrimeSpectrum.comap (TrivSqZeroExt.fstHom A A A).toRingHom) := by
      rw [← Set.range_eq_univ, range_comap_of_surjective _ _ TrivSqZeroExt.fst_surjective,
        PrimeSpectrum.zeroLocus_eq_univ_iff]
      intro x hx
      have hx' : x.fst = 0 := hx
      refine ⟨2, ?_⟩
      ext <;> simp [pow_two, hx']
    obtain ⟨q, rfl⟩ := hs p
    have e : g (PrimeSpectrum.comap (TrivSqZeroExt.fstHom A A A).toRingHom q) =
        zero W (Spec.map (CommRingCat.ofHom f) q) := by
      exact (Scheme.Hom.comp_apply
        (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom)) g q).symm.trans
        ((congrArg (fun t => t q) h0).trans
          (Scheme.Hom.comp_apply (Spec.map (CommRingCat.ofHom f)) (zero W) q))
    rw [e]
    exact (zero_preimage_coordOpen_one W).ge (Set.mem_univ _)
  obtain ⟨z, w, h, rfl⟩ := exists_eq_ptHom_origin W _ g hY hg
  have hP : ((TrivSqZeroExt.fstHom A A A).toRingHom ∘ ![z, -1, w]) = ![z.fst, -1, w.fst] := by
    ext1 j; fin_cases j <;> simp
  have h₁ := h.map_comp (TrivSqZeroExt.fstHom A A A).toRingHom
  have h₂ := h₁
  rw [hP] at h₂
  rw [SpecMap_ptHom, SpecMap_zero_origin W f (isUnimodularSol_zero_neg _),
    ptHom_congr W _ _ h₁ rfl hP h₂] at h0
  obtain ⟨hz, hw⟩ := ptHom_origin_inj W _ _ h0
  have he := (equation_origin_iff _ _ _).mp h.equation
  have hzz : z * z = 0 := by ext <;> simp [hz]
  have hzw : z * w = 0 := by ext <;> simp [hz, hw]
  have hww : w * w = 0 := by ext <;> simp [hw]
  have hw0 : w = 0 := by
    set V := W.map ((algebraMap A (DualNumber A)).comp f)
    linear_combination he + z * hzz + (V.a₁ + V.a₂ * z + V.a₄ * w) * hzw + (V.a₃ + V.a₆ * w) * hww
  have hz0 : z = TrivSqZeroExt.inr z.snd := by ext <;> simp [hz]
  have hQ : ![z, -1, w] = ![TrivSqZeroExt.inr z.snd, -1, 0] := by rw [hw0, ← hz0]
  exact ⟨z.snd, hQ ▸ h, ptHom_congr W _ _ _ rfl hQ _⟩

theorem epsScale_ptHom (f : R →+* A) (c : A)
    (h : IsUnimodularSol (W.map ((algebraMap A (DualNumber A)).comp f)) ![DualNumber.eps, -1, 0]) :
    ∃ h', spMap (epsScaleR c) ≫
        ptHom W ((algebraMap A (DualNumber A)).comp f) ![DualNumber.eps, -1, 0] h =
      ptHom W ((algebraMap A (DualNumber A)).comp f) ![TrivSqZeroExt.inr c, -1, 0] h' := by
  have hρ : (epsScaleR c).comp ((algebraMap A (DualNumber A)).comp f) =
      (algebraMap A (DualNumber A)).comp f := by
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have hP : (epsScaleR c ∘ ![DualNumber.eps, -1, 0]) = ![TrivSqZeroExt.inr c, -1, 0] := by
    ext1 j; fin_cases j
    · ext <;> simp [epsScaleR]
    · simp
    · simp
  have h₁ := h.map_comp (epsScaleR c)
  rw [hρ, hP] at h₁
  exact ⟨h₁, (SpecMap_ptHom W _ _ h _).trans (ptHom_congr W _ _ _ hρ hP _)⟩

theorem isLieComb_one_iff {G : Over (Sp A)} [GrpObj G] (c : Fin 1 → A) (v w : epsR A ⟶ G) :
    IsLieComb c ![v] w ↔ w.left = spMap (epsScaleR (c 0)) ≫ v.left := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu 0
  · intro hw
    refine ⟨![w], fun i => ?_, by simp⟩
    fin_cases i
    exact hw

theorem isLieBasis_eps : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R) (R' : Type) [CommRing R'] (f : R →+* R') (A : Over (Sp R')) [GrpObj A] (φ : A.left ⟶ scheme W) (v : epsR R' ⟶ A) (h : IsUnimodularSol (W.map ((algebraMap R' (DualNumber R')).comp f)) ![DualNumber.eps, -1, 0]), IsPullback φ A.hom (toSpec W) (spMap f) → eSec A ≫ φ = spMap f ≫ zero W → v.left ≫ φ = ptHom W ((algebraMap R' (DualNumber R')).comp f) ![DualNumber.eps, -1, 0] h → IsLieBasis ![v] := by
  intro R _ W R' _ f A _ φ v h hpb he hv
  have hover : ∀ w : epsR R' ⟶ A, w.left ≫ A.hom = spMap (algebraMap R' (DualNumber R')) :=
    fun w => Over.w w
  have hη : η[A].left ≫ A.hom = 𝟙 (Sp R') := Over.w η[A]
  have he' : η[A].left ≫ φ = spMap f ≫ zero W := he
  constructor
  · intro i
    fin_cases i
    change spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left = η[A].left
    refine hpb.hom_ext ?_ ?_
    · rw [Category.assoc, hv, he', SpecMap_zero_origin W f (isUnimodularSol_zero_neg _)]
      refine (SpecMap_ptHom W _ _ h _).trans (ptHom_congr W _ _ _ ?_ ?_ _)
      · ext a; simp [TrivSqZeroExt.algebraMap_eq_inl]
      · ext1 j; fin_cases j <;> simp
    · rw [Category.assoc, hover, hη, ← Spec.map_comp, ← Spec.map_id]
      congr 1
  · intro w hw
    have hw' : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ w.left = η[A].left := hw
    obtain ⟨c, hc, hwc⟩ := exists_eq_ptHom_eps W f (w.left ≫ φ)
      (by rw [Category.assoc, hpb.w, ← Category.assoc, hover, ← Spec.map_comp]; rfl)
      (by rw [← Category.assoc, hw', he'])
    have key : ∀ a : R', w.left = spMap (epsScaleR a) ≫ v.left ↔ a = c := by
      intro a
      obtain ⟨ha, hea⟩ := epsScale_ptHom W f a h
      constructor
      · intro e
        rw [e, Category.assoc, hv, hea] at hwc
        exact TrivSqZeroExt.inr_injective (ptHom_origin_inj W _ _ hwc).1
      · rintro rfl
        refine hpb.hom_ext ?_ ?_
        · rw [Category.assoc, hv, hea, hwc]
        · rw [Category.assoc, hover, hover, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
          congr 2
          ext b <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
    refine ⟨fun _ => c, (isLieComb_one_iff _ _ _).mpr ((key c).mpr rfl), fun c' hc' => ?_⟩
    funext i
    fin_cases i
    exact (key _).mp ((isLieComb_one_iff _ _ _).mp hc')

end GlobalTheory.WeierstrassCurve.OriginTangent
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

noncomputable section

namespace GlobalTheory.WeierstrassLie

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

theorem equation_inr (c : R) : (W.map (algebraMap R (DualNumber R))).toProjective.Equation
    ![TrivSqZeroExt.inr c, -1, 0] := by
  rw [equation_origin_iff]
  simp [pow_succ, TrivSqZeroExt.inr_mul_inr]

def vec (c : R) : Spec (.of (DualNumber R)) ⟶ scheme W :=
  ptHom W (algebraMap R (DualNumber R)) ![TrivSqZeroExt.inr c, -1, 0]
    (isUnimodularSol_origin (equation_inr W c))

theorem scale_vec (c : R) : spMap (epsScaleR c) ≫ vec W 1 = vec W c := by
  refine (SpecMap_ptHom W _ _ _ (epsScaleR c)).trans (ptHom_congr W _ _ _ ?_ ?_ _)
  · ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext1 j
    fin_cases j
    · ext <;> simp [epsScaleR]
    · simp
    · simp

theorem vec_inj {c d : R} (e : vec W c = vec W d) : c = d := by
  rw [vec, vec, ← SpecMap_originEval_chartY W _ _ _ (equation_inr W c),
    ← SpecMap_originEval_chartY W _ _ _ (equation_inr W d), cancel_mono] at e
  have e' : originEval W _ _ _ (equation_inr W c) = originEval W _ _ _ (equation_inr W d) :=
    congrArg (·.hom) (Spec.map_injective e)
  have := RingHom.congr_fun e' (originZ W)
  rw [originEval_originZ, originEval_originZ] at this
  simpa using congrArg TrivSqZeroExt.snd this

theorem fst_vec (c : R) :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ vec W c = zero W := by
  refine (SpecMap_ptHom W _ _ _ (TrivSqZeroExt.fstHom R R R).toRingHom).trans ?_
  rw [zero, ← pt_smul W (A := R) _ _ isUnit_one.neg]
  refine ptHom_congr W _ _ _ ?_ ?_ _
  · ext a; simp [TrivSqZeroExt.algebraMap_eq_inl]
  · ext1 j
    fin_cases j <;> simp

theorem surjective_fst :
    Function.Surjective (PrimeSpectrum.comap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
  intro p
  refine ⟨PrimeSpectrum.comap (algebraMap R (DualNumber R)) p, PrimeSpectrum.ext (Ideal.ext fun a => ?_)⟩
  change algebraMap R (DualNumber R) a.fst ∈ p.asIdeal ↔ a ∈ p.asIdeal
  have h : (TrivSqZeroExt.inr a.snd : DualNumber R) ∈ p.asIdeal :=
    p.isPrime.mem_of_pow_mem 2 (by rw [pow_two, TrivSqZeroExt.inr_mul_inr]; exact zero_mem _)
  conv_rhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq a]
  exact (Ideal.add_mem_iff_left _ h).symm

theorem exists_eq_vec (g : Spec (.of (DualNumber R)) ⟶ scheme W)
    (hg : g ≫ toSpec W = spMap (algebraMap R (DualNumber R)))
    (h0 : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ g = zero W) : ∃ c, g = vec W c := by
  have hr : Set.range g ⊆ Set.range (chartY W) := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨q, rfl⟩ := surjective_fst p
    rw [← Scheme.Hom.coe_opensRange, opensRange_chartY]
    have : q ∈ zero W ⁻¹ᵁ coordOpen W 1 := by
      rw [zero_preimage_coordOpen_one]; trivial
    rw [← h0] at this
    exact this
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift _ _ hr)
  have hl : Spec.map φ ≫ chartY W = g := hφ ▸ IsOpenImmersion.lift_fac _ _ hr
  have hc : φ.hom.comp (algebraMap R (OriginRing W)) = algebraMap R (DualNumber R) := by
    rw [← hl, Category.assoc, chartY_toSpec, ← Spec.map_comp] at hg
    exact congrArg (·.hom) (Spec.map_injective hg)
  have ha : (TrivSqZeroExt.fstHom R R R).toRingHom.comp φ.hom =
      (originAug W : OriginRing W →+* R) := by
    rw [← hl, ← SpecMap_originAug_chartY, ← Category.assoc, cancel_mono] at h0
    exact congrArg (·.hom) (Spec.map_injective ((Spec.map_comp _ _).trans h0))
  have hz : (φ.hom (originZ W)).fst = 0 := (RingHom.congr_fun ha _).trans (originAug_originZ W)
  have hw : (φ.hom (originW W)).fst = 0 := (RingHom.congr_fun ha _).trans (originAug_originW W)
  have hw0 : φ.hom (originW W) = 0 := by
    have e := congrArg φ.hom ((equation_origin_iff _ _ _).mp (equation_originZ_originW W))
    simp only [map_add (f := _), map_mul, map_pow] at e
    ext
    · exact hw
    · rw [e]
      simp [pow_succ, hz, hw]
  have hz0 : φ.hom (originZ W) = TrivSqZeroExt.inr (φ.hom (originZ W)).snd := by
    ext <;> simp [hz]
  refine ⟨(φ.hom (originZ W)).snd, ?_⟩
  rw [← hl, vec, ← SpecMap_originEval_chartY W _ _ _ (equation_inr W _)]
  congr 2
  ext1
  refine origin_hom_ext W (fun r => ?_) ?_ ?_
  · exact (RingHom.congr_fun hc r).trans (originEval_algebraMap W _ _ _ (equation_inr W _) r).symm
  · exact hz0.trans (originEval_originZ W _ _ _ (equation_inr W _)).symm
  · exact hw0.trans (originEval_originW W _ _ _ (equation_inr W _)).symm

theorem isLieBasis_eps : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R)
    [GrpObj (schemeOver W)], η[schemeOver W].left = zero W → ∃ v : epsR R ⟶ schemeOver W,
      (∃ h : IsUnimodularSol (W.map (algebraMap R (DualNumber R))) ![DualNumber.eps, -1, 0],
        v.left = ptHom W (algebraMap R (DualNumber R)) ![DualNumber.eps, -1, 0] h) ∧
      IsLieBasis ![v] := by
  intro R _ W _ hη
  let v : epsR R ⟶ schemeOver W := Over.homMk (vec W 1) (ptHom_toSpec ..)
  have key : ∀ (c : Fin 1 → R) (w : epsR R ⟶ schemeOver W),
      IsLieComb c ![v] w ↔ w.left = vec W (c 0) := by
    intro c w
    constructor
    · rintro ⟨u, hu, rfl⟩
      have : (List.ofFn u).prod = u 0 := by simp
      rw [this]
      exact (hu 0).trans (scale_vec W _)
    · intro h
      refine ⟨fun _ => w, fun i => ?_, by simp⟩
      obtain rfl : i = 0 := Subsingleton.elim _ _
      exact h.trans (scale_vec W _).symm
  refine ⟨v, ⟨isUnimodularSol_origin (equation_inr W 1), rfl⟩, fun i => ?_, fun w hw => ?_⟩
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    exact (fst_vec W 1).trans hη.symm
  · obtain ⟨c, hc⟩ := exists_eq_vec W w.left (Over.w w) (hw.trans hη)
    refine ⟨fun _ => c, (key _ _).mpr hc, fun d hd => ?_⟩
    funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact vec_inj W (((key _ _).mp hd).symm.trans hc)

end GlobalTheory.WeierstrassLie
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem single_mem_span_iff_of_selfDual : ∀ (O R K La I : Type) [CommRing O] [CommRing R] [Field K] [Algebra R K] [AddCommGroup La] [Module O La] [Fintype I] [DecidableEq I] (τ₀ : O →+* R) (h : La → La → O) (ev dv : La → I → K) (n : ℕ) (x y : Fin n → La), (∀ a b, algebraMap R K (τ₀ (h a b)) = ∑ i, ev a i * dv b i) → (∀ a, ev a = ∑ m, algebraMap R K (τ₀ (h a (y m))) • ev (x m)) → Submodule.span K (Set.range ev) = ⊤ → ∀ (i : I) (t : K), Pi.single i t ∈ Submodule.span R (Set.range ev) ↔ ∀ b, t * dv b i ∈ (algebraMap R K).range := by
  intro O R K La I _ _ _ _ _ _ _ _ τ₀ h ev dv n x y hh hev hspan i t
  have hsum : ∀ b, ∑ j, (Pi.single i t : I → K) j * dv b j = t * dv b i := by
    intro b
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  constructor
  · intro hm b
    rw [← hsum b]
    generalize (Pi.single i t : I → K) = v at hm
    induction hm using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, rfl⟩ := hv
      exact ⟨_, hh a b⟩
    | zero => simp
    | add u w _ _ hu hw =>
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      exact add_mem hu hw
    | smul r u _ hu =>
      have : ∑ j, (r • u) j * dv b j = algebraMap R K r * ∑ j, u j * dv b j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Pi.smul_apply, Algebra.smul_def, _root_.mul_assoc]
      rw [this]
      exact mul_mem ⟨r, rfl⟩ hu
  · intro hb
    have key : ∀ v : I → K, v = ∑ m, (∑ j, v j * dv (y m) j) • ev (x m) := by
      intro v
      have hv : v ∈ Submodule.span K (Set.range ev) := hspan ▸ Submodule.mem_top
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨a, rfl⟩ := hv
        simp only [← hh]
        exact hev a
      | zero => simp
      | add u w _ _ hu hw =>
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, add_smul]
        rw [← hu, ← hw]
      | smul r u _ hu =>
        simp only [Pi.smul_apply, smul_eq_mul, _root_.mul_assoc, ← Finset.mul_sum, mul_smul,
          ← Finset.smul_sum]
        rw [← hu]
    rw [key (Pi.single i t)]
    refine Submodule.sum_mem _ fun m _ => ?_
    rw [hsum]
    obtain ⟨r, hr⟩ := hb (y m)
    rw [← hr, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

end GlobalTheory.CM
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.CMNormIdentity

theorem primeSpectrum_dualNumber_eq (x y : PrimeSpectrum (DualNumber ℂ)) : x = y := by
  have h : ∀ z : PrimeSpectrum (DualNumber ℂ), ∀ a, a ∈ z.asIdeal ↔ a.fst = 0 := fun z a => by
    constructor
    · intro ha
      by_contra h0
      exact z.2.ne_top (z.asIdeal.eq_top_of_isUnit_mem ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)))
    · intro ha
      refine z.2.mem_of_pow_mem 2 ?_
      rw [show a ^ 2 = 0 by ext <;> simp [pow_two, ha]]
      exact z.asIdeal.zero_mem
  ext a
  rw [h, h]

section Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem isDiff_of_isLieComb {w : Fin g → ℂ} {v v' : epsR ℂ ⟶ A} (h : u.IsDiff w v) (c : ℂ)
    (hc : IsLieComb ![c] ![v] v') : u.IsDiff (c • w) v' := by
  obtain ⟨y, hy, hv'⟩ := hc
  have hl : v'.left = spMap (epsScaleR c) ≫ v.left := by
    have := hy 0
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, _root_.mul_one] at hv'
    rw [hv']
    simpa using this
  intro U
  rw [hl]
  intro hU f
  have hU' : ⊤ ≤ v.left ⁻¹ᵁ U := fun x _ => by
    have := hU (Set.mem_univ x)
    have hx : (spMap (epsScaleR c)) x = x := primeSpectrum_dualNumber_eq _ _
    change v.left ((spMap (epsScaleR c)) x) ∈ U at this
    rwa [hx] at this
  rw [map_smul, ← h U hU' f]
  have e : (spMap (epsScaleR c) ≫ v.left).appLE U ⊤ hU = v.left.appLE U ⊤ hU' ≫ (spMap (epsScaleR c)).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE (spMap (epsScaleR c)) v.left U ⊤ ⊤ hU' le_rfl).symm
  have e2 := congrArg (fun k => k.hom ((v.left.appLE U ⊤ hU').hom f))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (epsScaleR c)))
  rw [e]
  refine (congrArg TrivSqZeroExt.snd e2).trans ?_
  simp [epsScaleR]

end Unif

end GlobalTheory.CMNormIdentity
end
