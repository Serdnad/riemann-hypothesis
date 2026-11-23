module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle096
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle109
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle054
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle105
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle056
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle087
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle128
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle093
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.TestInOpen

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem proj_bot {T : AddSubgroup S.Gam} (h : T = ⊥) : S.proj T 0 = 1 := by
  subst h
  unfold ThetaSys.proj
  rw [finsum_unique, S.ρ_one _ (by rw [AddSubgroup.mem_bot.1 (Subtype.prop _), smul_zero])]
  simp

variable {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J}

theorem exists_crd_ne_zero (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) {K : Type} [Field K]
    (x : Sp K ⟶ Q.P.left) {z : M.Z} (hz : Set.range (x ≫ Q.P.hom) = {z}) (hc : z ∈ U₀) :
    ∃ v, Crd Q.O1 Q.st x v ∧ v ≠ 0 := by
  have hxz : ∀ s, Q.P.hom (x s) = z := fun s => by
    have : (x ≫ Q.P.hom) s ∈ Set.range (x ≫ Q.P.hom) := ⟨_, rfl⟩
    rw [hz] at this
    exact this
  obtain ⟨l, hl⟩ : ∃ l, z ∈ Q.W l := TopologicalSpace.Opens.mem_iSup.1 (by rw [Q.cover]; trivial)
  have hr : Set.range x ⊆ Set.range (Q.P.hom ⁻¹ᵁ Q.W l).ι := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι]
    change Q.P.hom (x s) ∈ Q.W l
    rwa [hxz]
  obtain ⟨x', rfl⟩ : ∃ x', x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι = x :=
    ⟨_, IsOpenImmersion.lift_fac _ x hr⟩
  have hcov := (Q.imm l).1
  have hm : x' (IsLocalRing.closedPoint K) ∈ ⨆ i ∈ (Set.univ : Set S.J), nonzeroLocus (Q.σ l i) := by
    rw [hcov]; trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at hm
  obtain ⟨i, -, hi⟩ := hm
  obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
  obtain ⟨w, hw⟩ : ∃ w, Crd _ (Q.σ l) x' w :=
    ⟨_, m, 1, (CrdCalc.top_le_iff x' _).2 (Scheme.basicOpen_le _ _ hm), fun _ => rfl⟩
  have hwi := ((CrdCalc.crd_isUnit_iff i hw).2 ((CrdCalc.top_le_iff x' _).2 hi)).ne_zero
  refine ⟨_, Q.rel l K x' _ hw, fun h0 => hwi ?_⟩
  have hBm : ∀ a b, Q.B l a b ∈ M.O z := fun a => (RatModel.Lat.mem_const_iff M).1 (by
    rw [RatModel.Lat.const_E, ← hB.ee.1 z hc, Q.basis l z hl]
    exact Submodule.subset_span ⟨a, rfl⟩)
  let B' : Matrix S.J S.J (M.O z) := fun a b => ⟨_, hBm a b⟩
  let C' : Matrix S.J S.J (M.O z) := fun a b => ⟨_, RatModel.valF_mem_O hl (Q.c l a b)⟩
  have h1 : C' * B' = 1 := by
    apply Matrix.map_injective (f := (M.O z).val.toRingHom) Subtype.val_injective
    beta_reduce
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Q.c_inv l
  have h2 := congrArg (fun A => A.map (RatModel.valHom _ z hz)) (mul_eq_one_comm.1 h1)
  beta_reduce at h2
  rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
  have h3 : C'.map (RatModel.valHom _ z hz) =
      (Q.c l).map (valR (x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) (Q.W l)) := by
    ext a b
    rw [← Category.assoc]
    exact RatModel.val_valF (by rw [hz]; exact Set.singleton_subset_iff.2 hl) _
  have h4 : w = 0 := by
    rw [← Matrix.one_mulVec w, ← h2, ← Matrix.mulVec_mulVec, h3, h0, Matrix.mulVec_zero]
  rw [h4]; rfl

theorem mem_G_of_mem [ArithBase o Ω] (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) (w : Q.P.left)
    (hc : Q.P.hom w ∈ U₀) : w ∈ Q.G := by
  let x : Sp (Q.P.left.residueField w) ⟶ Q.P.left := Q.P.left.fromSpecResidueField w
  have hx : ∀ s, x s = w := fun s => Scheme.fromSpecResidueField_apply w s
  have hz : Set.range (x ≫ Q.P.hom) = {Q.P.hom w} := by
    rw [RatModel.range_eq_singleton _ (IsLocalRing.closedPoint _)]
    exact congrArg (fun a => {Q.P.hom a}) (hx _)
  obtain ⟨v, hv, hv0⟩ := exists_crd_ne_zero hB Q x hz hc
  have h := (OpenPart.le_preimage_G_iff o Ω S ρ M U₀ EE hB Q _ x _
    (Spec.preimage (x ≫ Q.P.hom ≫ M.s)).hom v hz (Or.inr hc) (Spec.map_preimage _).symm hv).2 (by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hv0
      refine ⟨i, ?_⟩
      rw [proj_bot (hB.gen _ hc), Finset.sum_eq_single i]
      · simpa using hi
      · intro j _ hj
        simp [hj]
      · simp)
  rw [← hx (IsLocalRing.closedPoint _)]
  exact (CrdCalc.top_le_iff x _).1 h

theorem big_of_big (ρ : S.Real) (h : S.Big) : Big S.g S.N (S.r * S.N) := by
  refine ⟨?_, h.1, h.2.1⟩
  have h1 : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
  rw [ρ.N_eq]
  nlinarith

variable {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p}

theorem isLocalHom_j (u : ρ.UTest p y₀) : IsLocalHom u.j := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨b, hb⟩ := ha.exists_right_inv
  have hb' : algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ a) * b = 1 := congrArg Subtype.val hb
  have h0 : algebraMap u.V (FractionRing u.V) a ≠ 0 := fun h => by simp [h] at hb'
  obtain ⟨c, hc⟩ := (u.norm_le (algebraMap u.V _ a)⁻¹).1 (by
    rw [map_inv₀, ← eq_inv_of_mul_eq_one_right hb']
    exact (mem_OO_iff _).1 b.2)
  refine IsUnit.of_mul_eq_one c (IsFractionRing.injective u.V (FractionRing u.V) ?_)
  rw [map_mul, hc, mul_inv_cancel₀ h0, map_one]

theorem mem_range_or (u : ρ.UTest p y₀) (s : Sp u.V) :
    s ∈ Set.range (jK u.V) ∨ s ∈ Set.range (rPt p ≫ spMap u.j) := by
  by_cases h : s.asIdeal = ⊥
  · refine Or.inl ⟨(⊥ : PrimeSpectrum (FractionRing u.V)), PrimeSpectrum.ext ?_⟩
    rw [h]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective u.V (FractionRing u.V))
  · have := isLocalHom_j u
    refine Or.inr ⟨IsLocalRing.closedPoint (kb p), ?_⟩
    have e₁ : rPt p (IsLocalRing.closedPoint (kb p)) = cPt p :=
      IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p))
    have e₂ : spMap u.j (cPt p) = IsLocalRing.closedPoint u.V := IsLocalRing.comap_closedPoint u.j
    refine ((congrArg (spMap u.j) e₁).trans e₂).trans ?_
    exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime h s.isPrime)).symm

theorem top_le_preimage_G : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ⊤ ≤ (tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) ⁻¹ᵁ Q.G := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q p _ y y₀ t c tm hS x _
  rcases mem_range_or t.u (t.u.G.hom x) with ⟨s, hs⟩ | ⟨s, hs⟩
  · refine mem_G_of_mem hB Q _ ?_
    have e₁ : Q.P.hom ((tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) x) = c.yV (t.u.G.hom x) := by
      rw [← Scheme.Hom.comp_apply, Category.assoc, tm.f_over, Scheme.Hom.comp_apply]
    have e₂ : c.yV (jK t.u.V s) = U₀.ι (c.yK s) := by
      rw [← Scheme.Hom.comp_apply, ← c.yK_fac, Scheme.Hom.comp_apply]
    show Q.P.hom ((tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) x) ∈ U₀
    rw [e₁, ← hs, e₂]
    exact (c.yK s).2
  · haveI : IsAlgClosed (kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
    have pb : IsPullback t.mod.r t.mod.Φ.G.hom t.u.G.hom (rPt p ≫ spMap t.u.j) := t.mod.cart.1
    obtain ⟨x', rfl, -⟩ := Scheme.exists_preimage_of_isPullback pb x s hs.symm
    have hsm : SmoothOfRelativeDimension S.g t.mod.Φ.G.hom :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback pb t.mod.smooth
    have : Smooth t.mod.Φ.G.hom := SmoothOfRelativeDimension.smooth S.g _
    have : JacobsonSpace t.mod.Φ.G.left := LocallyOfFiniteType.jacobsonSpace t.mod.Φ.G.hom
    have hcov := (GlobalTheory.T.immBy_weight_zero' hL.1 hL.2.1 (kb p) t.mod.Φ S.g S.N _ _ S.J _ t.mod.F t.mod.pol (big_of_big ρ hS)
      t.mod.good t.mod.dim).1
    let U : t.mod.Φ.G.left.Opens := t.mod.r ⁻¹ᵁ ((tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) ⁻¹ᵁ Q.G)
    by_contra hx
    obtain ⟨a, haU, ha⟩ := nonempty_inter_closedPoints (Z := (U : Set t.mod.Φ.G.left)ᶜ) ⟨x', hx⟩
      U.isOpen.isClosed_compl.isLocallyClosed
    let x₀ := pointOfClosedPoint (K := kb p) t.mod.Φ.G.hom a ha
    have h₂ : x₀ ≫ t.mod.Φ.G.hom = 𝟙 _ := pointOfClosedPoint_comp _ a ha
    have h₃ : x₀ (IsLocalRing.closedPoint (kb p)) = a := pointOfClosedPoint_apply _ a ha _
    obtain ⟨v, hv⟩ := CrdCalc.crd_exists (R := kb p) (t.mod.Φ.H_isLB 1) t.mod.F x₀
    have hmem : x₀ (IsLocalRing.closedPoint (kb p)) ∈
        ⨆ i ∈ {i | t.mod.xe.symm (t.cls i) = 0}, Out.nonzeroLocus (t.mod.F i) := by
      rw [hcov]; trivial
    simp only [TopologicalSpace.Opens.mem_iSup] at hmem
    obtain ⟨i, hi, hm⟩ := hmem
    have h₄ := ((CrdCalc.crd_isUnit_iff i hv).2 ((CrdCalc.top_le_iff _ _).2 hm)).ne_zero
    have h₁ : (x₀ ≫ t.mod.r) ≫ t.u.G.hom = rPt p ≫ spMap t.u.j := by
      rw [Category.assoc, pb.w, ← Category.assoc, h₂]
      exact Category.id_comp _
    have hcr := tm.crd (kb p) ((IsLocalRing.residue (OO p)).comp t.u.j) _ v
      (h₁.trans (Spec.map_comp _ _).symm) (t.mod.red (Over.homMk x₀ h₂) v hv)
    have hov : ((x₀ ≫ t.mod.r) ≫ tm.f) ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι ≫ Q.P.hom = rPt p ≫ y := by
      rw [Category.assoc, tm.f_over, ← Category.assoc, h₁, Category.assoc, c.fac]
    have key := (GlobalTheory.T.le_preimage_openPart_iff_testCoordinates o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hS _ v hov hcr).2
      ⟨i, t.mod.xe.symm.map_eq_zero_iff.1 hi, h₄⟩
    refine haU ?_
    rw [← h₃]
    exact key (x := IsLocalRing.closedPoint (kb p)) trivial

end GlobalTheory.ZH.TestInOpen
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PolCountableDescent

theorem countable_closure {K : Type} [Field K] (s : Finset K) :
    Countable (Subfield.closure (s : Set K)) := by
  rw [← Cardinal.mk_le_aleph0_iff]
  refine (Subfield.cardinalMk_closure_le_max _).trans ?_
  exact max_le (Cardinal.mk_le_aleph0_iff.2 s.countable_toSet.to_subtype) le_rfl

theorem subset_closure_of_subset {K : Type} [Field K] {s s' : Finset K} (h : s ⊆ s') :
    (s : Set K) ⊆ Subfield.closure (s' : Set K) :=
  fun _ hx => Subfield.subset_closure (h hx)

theorem spMap_subtype_comp {K : Type} [Field K] {K₀ K₁ : Subfield K} (h : K₀ ≤ K₁) :
    spMap K₁.subtype ≫ spMap (Subfield.inclusion h) = spMap K₀.subtype := by
  rw [← Spec.map_comp]; rfl

theorem polAV_descends_to_countable_subfield :
    ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (J I : Type) [Finite J] [Finite I] (a : J → (P.A ⟶ P.A)) (x : I → (𝟙_ (Over (Sp K)) ⟶ P.A)), ∃ (K₀ : Subfield K) (P₀ : PolAV (Sp K₀)) (Φ : P.A.left ⟶ P₀.A.left) (a₀ : J → (P₀.A ⟶ P₀.A)) (x₀ : I → (𝟙_ (Over (Sp K₀)) ⟶ P₀.A)), Countable K₀ ∧ IsGrpPullback P.A P₀.A (spMap K₀.subtype) Φ ∧ LBIso P.L (P₀.L.pull Φ) ∧ (∀ j, (a j).left ≫ Φ = Φ ≫ (a₀ j).left) ∧ ∀ i, (x i).left ≫ Φ = spMap K₀.subtype ≫ (x₀ i).left := by
  intro K _ P J I _ _ a x
  classical
  obtain ⟨s₀, H₀⟩ := GlobalTheory.exists_finset_isProjOver_descends K ⊥ P.A.left P.A.hom
    (GlobalTheory.ProjSpace.isProjOver_of_relAmple P.ample)
  let K₀ : Subfield K := Subfield.closure (s₀ : Set K)
  obtain ⟨X₀, p₀, φ, hp₀, sq⟩ := H₀ K₀ bot_le Subfield.subset_closure
  have : IsProper p₀ := by
    obtain ⟨N, i, hi, rfl⟩ := hp₀
    have := isProper_str K₀ N
    infer_instance
  have : LocallyOfFinitePresentation p₀ := inferInstance
  have : QuasiCompact (Over.mk p₀).hom := inferInstanceAs (QuasiCompact p₀)
  have : QuasiSeparated (Over.mk p₀).hom := inferInstanceAs (QuasiSeparated p₀)
  have : LocallyOfFinitePresentation (Over.mk p₀).hom := inferInstanceAs (LocallyOfFinitePresentation p₀)
  obtain ⟨s₁, H₁⟩ := GlobalTheory.grpObj_descends_to_large_subfield K K₀ (Over.mk p₀) P.A φ sq
  obtain ⟨s₂, H₂⟩ := GlobalTheory.LBDescent.exists_lb_subfield K K₀ X₀ P.A.left p₀ P.A.hom φ P.L P.isLB sq
  obtain ⟨s₃, H₃⟩ := GlobalTheory.morphisms_descend_to_large_subfield K K₀ X₀ P.A.left p₀ P.A.hom φ X₀ p₀ J
    (fun j => (a j).left ≫ φ) sq
    (fun j => by rw [Category.assoc, sq.w, ← Category.assoc, Over.w])
  obtain ⟨s₄, H₄⟩ := GlobalTheory.morphisms_descend_to_large_subfield K K₀ (Sp K₀) (Sp K) (𝟙 _) (𝟙 _)
    (spMap K₀.subtype) X₀ p₀ I (fun i => (x i).left ≫ φ) (IsPullback.of_vert_isIso ⟨by simp⟩)
    (fun i => by
      have e : (x i).left ≫ P.A.hom = 𝟙 _ := Over.w (x i)
      rw [Category.assoc, sq.w, ← Category.assoc, e]; simp)
  let s : Finset K := s₀ ∪ s₁ ∪ s₂ ∪ s₃ ∪ s₄
  let K₁ : Subfield K := Subfield.closure (s : Set K)
  have h : K₀ ≤ K₁ := Subfield.closure_mono (Finset.coe_subset.2 (fun y hy => by simp [s, hy]))
  let inc := spMap (Subfield.inclusion h)
  let A₁ : Over (Sp K₁) := Over.mk (pullback.snd p₀ inc)
  let φ₁ : A₁.left ⟶ X₀ := pullback.fst p₀ inc
  have sq₁ : IsPullback φ₁ A₁.hom p₀ inc := IsPullback.of_hasPullback p₀ inc
  let ψ : P.A.left ⟶ A₁.left := sq₁.lift φ (P.A.hom ≫ spMap K₁.subtype)
    (by rw [Category.assoc, spMap_subtype_comp h, sq.w])
  have hψ₁ : ψ ≫ φ₁ = φ := sq₁.lift_fst _ _ _
  have hψ₂ : ψ ≫ A₁.hom = P.A.hom ≫ spMap K₁.subtype := sq₁.lift_snd _ _ _
  obtain ⟨gr₁, hG⟩ := H₁ K₁ h (subset_closure_of_subset (fun y hy => by simp [s, hy])) A₁ φ₁ ψ sq₁ hψ₁ hψ₂
  obtain ⟨L₁, hL₁, hL⟩ := H₂ K₁ h (subset_closure_of_subset (fun y hy => by simp [s, hy])) A₁.left A₁.hom φ₁ ψ
    sq₁ hψ₁ hψ₂
  obtain ⟨f₁, hf₁⟩ := H₃ K₁ h (subset_closure_of_subset (fun y hy => by simp [s, hy])) A₁.left A₁.hom φ₁ ψ
    sq₁ hψ₁ hψ₂
  obtain ⟨x₁, hx₁⟩ := H₄ K₁ h (subset_closure_of_subset (fun y hy => by simp [s, hy])) (Sp K₁) (𝟙 _) inc
    (spMap K₁.subtype) (IsPullback.of_vert_isIso ⟨by simp [inc]⟩) (spMap_subtype_comp h) (by simp)
  let act₁ : J → (A₁ ⟶ A₁) := fun j =>
    Over.homMk (sq₁.lift (f₁ j) A₁.hom (by rw [(hf₁ j).2, sq₁.w])) (sq₁.lift_snd _ _ _)
  let pt₁ : I → (𝟙_ (Over (Sp K₁)) ⟶ A₁) := fun i =>
    Over.homMk (sq₁.lift (x₁ i) (𝟙 _) (by rw [(hx₁ i).2]; simp)) (sq₁.lift_snd _ _ _)
  obtain ⟨hab, hdim⟩ := GlobalTheory.FieldDescentAb.isAbelianScheme_and_relDim_descend K₁ K K₁.subtype A₁ P.A ψ hG P.isAb
  obtain ⟨hrig, hsym, hkt⟩ := GlobalTheory.PolDescent.rigidified_sym_kTriv_descend K₁ K K₁.subtype A₁ P.A ψ L₁ P.L
    hab hG hL₁ P.isLB hL
  have hamp := GlobalTheory.AmpleDescent.relAmple_of_fieldExtension K₁ K K₁.subtype A₁ P.A ψ L₁ P.L
    hab hG hL₁ P.isLB hL P.ample
  let P₁ : PolAV (Sp K₁) :=
    { A := A₁, grp := gr₁, isAb := hab, g := P.g, smoothDim := hdim P.g P.smoothDim, L := L₁,
      isLB := hL₁, rigid := hrig P.rigid, sym := hsym P.sym, ample := hamp, ktriv := hkt P.ktriv }
  refine ⟨K₁, P₁, ψ, act₁, pt₁, countable_closure s, hG, hL, fun j => ?_, fun i => ?_⟩
  · change (a j).left ≫ ψ = ψ ≫ (act₁ j).left
    have e₁ : (act₁ j).left ≫ φ₁ = f₁ j := sq₁.lift_fst _ _ _
    apply sq₁.hom_ext
    · rw [Category.assoc, hψ₁, Category.assoc, e₁, (hf₁ j).1]
    · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w, Category.assoc, Over.w, hψ₂]
  · change (x i).left ≫ ψ = spMap K₁.subtype ≫ (pt₁ i).left
    have e : (x i).left ≫ P.A.hom = 𝟙 _ := Over.w (x i)
    have e₁ : (pt₁ i).left ≫ φ₁ = x₁ i := sq₁.lift_fst _ _ _
    have e₂ : (pt₁ i).left ≫ A₁.hom = 𝟙 _ := sq₁.lift_snd _ _ _
    apply sq₁.hom_ext
    · rw [Category.assoc, hψ₁]
      exact ((hx₁ i).1.symm.trans (congrArg _ e₁.symm)).trans (Category.assoc _ _ _).symm
    · rw [Category.assoc, hψ₂, ← Category.assoc, e]
      refine (Category.id_comp _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
      exact ((congrArg _ e₂).trans (Category.comp_id _)).symm

end GlobalTheory.PolCountableDescent
end
end
