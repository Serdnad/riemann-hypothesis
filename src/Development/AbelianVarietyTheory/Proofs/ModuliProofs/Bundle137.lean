module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAlgebraicSectionOfHolomorphicTheta
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle132
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfComplexPoints
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle060
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle102
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle110
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle087
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle080
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle133
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle048
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.LocalFramePowerSections
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.cubicalBundlePairing_compatible_pullback : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (m : CubeMap G' G) (hw : m.F ≫ G.hom = G'.hom ≫ f), (∀ (T : Over S') (x y : T ⟶ G'), Out.toBase hw (x * y) = Out.toBase hw x * Out.toBase hw y) → ∀ (L : RigLB G) (L' : RigLB G') (c : CubicalStr G L) (c' : CubicalStr G' L'), m.IsPullCubical c' c → ∀ (N : ℕ) (T : Over S') (x y : T ⟶ G') (ζ : Γ(T.left, ⊤)ˣ), CubWeil c' N x y ζ → CubWeil c N (Out.toBase hw x) (Out.toBase hw y) ζ := by
  first | exact @GlobalTheory.UU.cubWeil_of_isPullCubical | exact GlobalTheory.UU.cubWeil_of_isPullCubical | (intros; apply GlobalTheory.UU.cubWeil_of_isPullCubical <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

namespace SameFactor

variable {A : Over (Sp ℂ)} [GrpObj A] {M M' : LB A.left} {g : ℕ}

theorem valAt'_div_g {X : Scheme.{0}} (M M' : LB X) (x : Sp ℂ ⟶ X) (p q : (LB.div M' M).ι)
    (h : ⊤ ≤ x ⁻¹ᵁ ((LB.div M' M).U p ⊓ (LB.div M' M).U q)) :
    valAt' x ((LB.div M' M).U p ⊓ (LB.div M' M).U q) ((LB.div M' M).g p q).val =
      valAt' x (M'.U p.1 ⊓ M'.U q.1) (M'.g p.1 q.1).val * (valAt' x (M.U p.2 ⊓ M.U q.2) (M.g p.2 q.2).val)⁻¹ := by
  dsimp only [LB.div] at h ⊢
  rw [Units.val_mul, valAt'_mul, valAt'_units_inv x h, GlobalTheory.HolSecAlg.val_res_unit x _ _ h,
    GlobalTheory.HolSecAlg.val_res_unit x _ _ h]

def divUnif (u : HolUnif A M g) (u' : HolUnif A M' g) (hex : u'.ex = u.ex) : HolUnif A (LB.div M' M) g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr := fun p z => u'.fr p.1 z * (u.fr p.2 z)⁻¹
  fr_hol := fun p => by
    have h1 := u'.fr_hol p.1
    rw [hex] at h1
    refine DifferentiableOn.mul (h1.mono fun z hz => ?_)
      (DifferentiableOn.inv ((u.fr_hol p.2).mono fun z hz => ?_) fun z hz => u.fr_ne _ _ ?_)
    · exact ((top_le_preimage_inf _ _ _).1 hz).1
    · exact ((top_le_preimage_inf _ _ _).1 hz).2
    · exact ((top_le_preimage_inf _ _ _).1 hz).2
  fr_ne := fun p z hz => by
    obtain ⟨h1, h2⟩ := (top_le_preimage_inf _ _ _).1 hz
    exact mul_ne_zero (u'.fr_ne _ _ (by rw [hex]; exact h1)) (inv_ne_zero (u.fr_ne _ _ h2))
  fr_compat := fun p q z hz => by
    obtain ⟨hp, hq⟩ := (top_le_preimage_inf _ _ _).1 hz
    obtain ⟨hp1, hp2⟩ := (top_le_preimage_inf _ _ _).1 hp
    obtain ⟨hq1, hq2⟩ := (top_le_preimage_inf _ _ _).1 hq
    have e1 := u'.fr_compat p.1 q.1 z (by rw [hex]; exact (top_le_preimage_inf _ _ _).2 ⟨hp1, hq1⟩)
    rw [hex] at e1
    have e2 := u.fr_compat p.2 q.2 z ((top_le_preimage_inf _ _ _).2 ⟨hp2, hq2⟩)
    rw [valAt'_div_g M M' _ p q hz, e1, e2, mul_inv]
    ring

theorem exists_gen_of_isFn [LocallyOfFiniteType A.hom] (u : HolUnif A M g) (s : M.Sec) (θ : (Fin g → ℂ) → ℂ)
    (hs : u.IsFn s θ) (hθ : ∀ z, θ z ≠ 0) : ∃ t : LB.Gen M, t.IsGen := by

  have hunit : ∀ i, IsUnit (s.f i) := fun i =>
    GlobalTheory.ThetaBundleSym.isUnit_of_complex_points u.ex_onto (s.f i) fun z hz => by
      rw [hs i z hz]
      exact mul_ne_zero (hθ z) (u.fr_ne i z hz)
  refine ⟨⟨fun i => (hunit i).unit⟩, fun i j => Units.ext ?_⟩
  rw [Units.val_mul]
  exact s.compat i j

end SameFactor

theorem lbIso_of_same_factor : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (M M' : LB P.A.left) (u : HolUnif P.A M P.g) (u' : HolUnif P.A M' P.g), M.IsLB → M'.IsLB → u'.ex = u.ex → (∀ (l : u.Λ) i j z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U i → ⊤ ≤ (u.ex z).left ⁻¹ᵁ M'.U j → u.fr i z * u'.fr j (z + l) = u.fr i (z + l) * u'.fr j z) → LBIso M M' := by
  intro hL hL2 hTh hU P M M' u u' hM hM' hex hfac
  have : LocallyOfFiniteType P.A.hom := by
    have := P.isAb.proper
    infer_instance

  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_algebraic_section_of_holomorphic_theta hL hL2 hTh hU P (LB.div M' M) (SameFactor.divUnif u u' hex) (fun _ => 1)
    (LB.isLB_div hM' hM) (differentiable_const 1) (by
      intro l p z hz
      obtain ⟨h1, h2⟩ := (top_le_preimage_inf _ _ _).1 hz
      have hl : u.ex (z + l) = u.ex z := GlobalTheory.HolSecAlg.ex_add_lattice u z l.2
      have n0 : u.fr p.2 z ≠ 0 := u.fr_ne _ _ h2
      have n1 : u.fr p.2 (z + l) ≠ 0 := u.fr_ne _ _ (by rw [hl]; exact h2)
      have key := hfac l p.2 p.1 z h2 h1
      show (1 : ℂ) * (u'.fr p.1 (z + l) * (u.fr p.2 (z + l))⁻¹) = 1 * (u'.fr p.1 z * (u.fr p.2 z)⁻¹)
      rw [_root_.one_mul, _root_.one_mul, ← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff n1 n0]
      linear_combination key)
  obtain ⟨t, ht⟩ := SameFactor.exists_gen_of_isFn _ s (fun _ => 1) hs fun _ => one_ne_zero
  exact ⟨t, ht⟩

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SiegDesc

theorem exists_isSquare {S' S : Scheme.{0}} {A' : Over S'} {A : Over S} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (w : φ ≫ A.hom = A'.hom ≫ f) :
    ∃ φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left, Geo.Tor.IsSquare φ φ₂ := by
  have v₁ : (fst A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  have v₂ : (snd A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  exact ⟨pullback.lift ((fst A' A').left ≫ φ) ((snd A' A').left ≫ φ)
    (by rw [Category.assoc, Category.assoc, w, reassoc_of% v₁, reassoc_of% v₂]),
    pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem isSquare_w {S' S : Scheme.{0}} {A' : Over S'} {A : Over S} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (w : φ ≫ A.hom = A'.hom ≫ f) {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} (h : Geo.Tor.IsSquare φ φ₂) :
    φ₂ ≫ (A ⊗ A).hom = (A' ⊗ A').hom ≫ f := by
  have w₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have v₁ : (fst A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  have h₁ := h.1
  rw [← w₁, reassoc_of% h₁, w, reassoc_of% v₁]

theorem isSquare_comp {S'' S' S : Scheme.{0}} {A'' : Over S''} {A' : Over S'} {A : Over S}
    {ψ : A''.left ⟶ A'.left} {φ : A'.left ⟶ A.left} {χ : A''.left ⟶ A.left} (e : ψ ≫ φ = χ)
    {ψ₂ : (A'' ⊗ A'').left ⟶ (A' ⊗ A').left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}
    {χ₂ : (A'' ⊗ A'').left ⟶ (A ⊗ A).left} (hψ : Geo.Tor.IsSquare ψ ψ₂) (hφ : Geo.Tor.IsSquare φ φ₂)
    (hχ : Geo.Tor.IsSquare χ χ₂) : ψ₂ ≫ φ₂ = χ₂ := by
  have a₁ := hψ.1
  have a₂ := hψ.2
  apply pullback.hom_ext
  · change _ ≫ (fst A A).left = _ ≫ (fst A A).left
    rw [Category.assoc, hφ.1, reassoc_of% a₁, hχ.1, e]
  · change _ ≫ (snd A A).left = _ ≫ (snd A A).left
    rw [Category.assoc, hφ.2, reassoc_of% a₂, hχ.2, e]

theorem isPullback_of_isSquare {S' S : Scheme.{0}} {A' : Over S'} {A : Over S} {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (hA : IsPullback φ A'.hom A.hom f) {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}
    (h : Geo.Tor.IsSquare φ φ₂) : IsPullback φ₂ (A' ⊗ A').hom (A ⊗ A).hom f := by
  have w₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have w₂ : (snd A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have v₁ : (fst A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  have v₂ : (snd A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  have h₁ := h.1
  have h₂ := h.2
  refine ⟨⟨isSquare_w hA.w h⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => pullback.lift
      (hA.lift (s.fst ≫ (fst A A).left) s.snd (by rw [Category.assoc, w₁, s.condition]))
      (hA.lift (s.fst ≫ (snd A A).left) s.snd (by rw [Category.assoc, w₂, s.condition]))
      (by rw [IsPullback.lift_snd, IsPullback.lift_snd])) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · apply pullback.hom_ext
    · change _ ≫ (fst A A).left = _ ≫ (fst A A).left
      rw [Category.assoc, h₁, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
    · change _ ≫ (snd A A).left = _ ≫ (snd A A).left
      rw [Category.assoc, h₂, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_snd _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
  · rw [← v₁, ← Category.assoc]
    exact (congrArg (· ≫ A'.hom) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_snd _ _ _ _)
  · apply pullback.hom_ext
    · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      change _ ≫ (fst A' A').left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₁]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₁]
    · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      change _ ≫ (snd A' A').left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₂]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₂]

theorem spMap_subtype_inclusion {K : Type} [Field K] {K₀ K₁ : Subfield K} (h : K₀ ≤ K₁) :
    spMap K₁.subtype ≫ spMap (Subfield.inclusion h) = spMap K₀.subtype := by
  rw [← Spec.map_comp]
  rfl

theorem siegPre_descends : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (K : Type) [Field K] (K₀ : Subfield K) (s₀ : Sp K₀ ⟶ Sp o) (s : Sp K ⟶ Sp o) (c : SiegPre h M ζ s), s = spMap K₀.subtype ≫ s₀ → c.Principal → ∃ F : Finset K, ∀ (K₁ : Subfield K) (hK : K₀ ≤ K₁), (F : Set K) ⊆ K₁ → ∃ c₁ : SiegPre h M ζ (spMap (Subfield.inclusion hK) ≫ s₀), c₁.Principal ∧ SiegPB c c₁ (spMap K₁.subtype) := by
  intro h M o _ ζ K _ K₀ s₀ s c hs hc
  classical
  obtain ⟨sA, hA⟩ := GlobalTheory.T.exists_finset_isProjOver_descends_to_subfield K K₀ c.A.left c.A.hom (GlobalTheory.ProjSpace.isProjOver_of_relAmple hc.1)
  let K' : Subfield K := K₀ ⊔ Subfield.closure (sA : Set K)
  obtain ⟨X', p', φ', hproj, hpb⟩ := hA K' le_sup_left
    (Subfield.subset_closure.trans (SetLike.coe_subset_coe.2 le_sup_right))
  have : IsProper p' := by
    obtain ⟨N, i, _, rfl⟩ := hproj
    have := isProper_str K' N
    infer_instance
  have : LocallyOfFinitePresentation p' :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  let A' : Over (Sp K') := Over.mk p'
  have : IsProper A'.hom := ‹IsProper p'›
  have : LocallyOfFinitePresentation A'.hom := ‹LocallyOfFinitePresentation p'›
  have hpb' : IsPullback (φ' : c.A.left ⟶ A'.left) c.A.hom A'.hom (spMap K'.subtype) := hpb
  obtain ⟨sG, hG⟩ := GlobalTheory.grpObj_descends_to_large_subfield K K' A' c.A φ' hpb'
  obtain ⟨φ₂', hsq'⟩ := exists_isSquare hpb'.w
  have : IsProper (A' ⊗ A').hom := by
    change IsProper (pullback.fst A'.hom A'.hom ≫ A'.hom)
    infer_instance
  obtain ⟨sL, hL⟩ := GlobalTheory.T.exists_lineBundle_descent_to_subfield K K' (A' ⊗ A').left (c.A ⊗ c.A).left (A' ⊗ A').hom (c.A ⊗ c.A).hom φ₂'
    c.P c.isLB (isPullback_of_isSquare hpb' hsq')
  obtain ⟨lv, hlv⟩ : ∃ lv : Fin h ⊕ Fin h → (Sp K ⟶ c.A.left), ∀ u, lv u = (c.lev (Pi.single u 1)).left :=
    ⟨_, fun _ => rfl⟩
  have hlev : ∀ u, lv u ≫ c.A.hom = 𝟙 (Sp K) := fun u =>
    (congrArg (· ≫ c.A.hom) (hlv u)).trans (Over.w (c.lev (Pi.single u 1)))
  obtain ⟨sP, hP⟩ := GlobalTheory.T.exists_descent_of_morphisms_to_subfield K K' (Sp K') (Sp K) (𝟙 _) (𝟙 _) (spMap K'.subtype) X' p' (Fin h ⊕ Fin h)
    (fun u => lv u ≫ φ') IsPullback.of_id_snd
    (fun u => by
      have e := hlev u
      rw [Category.comp_id, Category.assoc, hpb.w, reassoc_of% e])
  refine ⟨sA ∪ sG ∪ sL ∪ sP, fun K₁ hK hF => ?_⟩
  simp only [Finset.coe_union, Set.union_subset_iff] at hF
  obtain ⟨⟨⟨hsA, hsG⟩, hsL⟩, hsP⟩ := hF
  have h' : K' ≤ K₁ := sup_le hK (Subfield.closure_le.2 hsA)
  let j := spMap (Subfield.inclusion h')
  have hj : spMap K₁.subtype ≫ j = spMap K'.subtype := spMap_subtype_inclusion h'
  let A₁ : Over (Sp K₁) := Over.mk (pullback.snd p' j)
  let φ₁ : A₁.left ⟶ A'.left := pullback.fst p' j
  have hpb₁ : IsPullback φ₁ A₁.hom A'.hom j := IsPullback.of_hasPullback p' j
  let ψ : c.A.left ⟶ A₁.left := hpb₁.lift φ' (c.A.hom ≫ spMap K₁.subtype)
    (by rw [Category.assoc, hj]; exact hpb.w)
  have hψ₁ : ψ ≫ φ₁ = φ' := hpb₁.lift_fst _ _ _
  have hψ₂ : ψ ≫ A₁.hom = c.A.hom ≫ spMap K₁.subtype := hpb₁.lift_snd _ _ _
  obtain ⟨grp, hgrp⟩ := hG K₁ h' hsG A₁ φ₁ ψ hpb₁ hψ₁ hψ₂
  obtain ⟨φ₂, hsq₁⟩ := exists_isSquare hpb₁.w
  obtain ⟨ψ₂, hsqψ⟩ := exists_isSquare hψ₂
  obtain ⟨P₁, hP₁, hiso⟩ := hL K₁ h' hsL (A₁ ⊗ A₁).left (A₁ ⊗ A₁).hom φ₂ ψ₂
    (isPullback_of_isSquare hpb₁ hsq₁) (isSquare_comp hψ₁ hsqψ hsq₁ hsq') (isSquare_w hψ₂ hsqψ)
  obtain ⟨f₁, hf₁⟩ := hP K₁ h' hsP (Sp K₁) (𝟙 _) j (spMap K₁.subtype) IsPullback.of_id_snd hj (by simp)
  let l : Fin h ⊕ Fin h → (Sp K₁ ⟶ A₁.left) := fun u => hpb₁.lift (f₁ u) (𝟙 _)
    (by rw [Category.id_comp]; exact (hf₁ u).2.trans (Category.comp_id _))
  have hl₁ : ∀ u, l u ≫ φ₁ = f₁ u := fun u => hpb₁.lift_fst _ _ _
  have hl₂ : ∀ u, l u ≫ A₁.hom = 𝟙 _ := fun u => hpb₁.lift_snd _ _ _
  let lev₁ : Fin h ⊕ Fin h → (𝟙_ (Over (Sp K₁)) ⟶ A₁) := fun u => Over.homMk (l u) (hl₂ u)
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.exists_siegelObject_of_descended_data h M o ζ K₁ K K₁.subtype (spMap (Subfield.inclusion hK) ≫ s₀) s c A₁ ψ ψ₂ P₁
    lev₁ (by rw [hs, ← Category.assoc, spMap_subtype_inclusion]) hgrp hsqψ hP₁ hiso (fun u => by
      have e := hlev u
      have key : lv u ≫ ψ = spMap K₁.subtype ≫ l u := by
        apply hpb₁.hom_ext
        · rw [Category.assoc, Category.assoc, hψ₁, hl₁]
          exact (hf₁ u).1.symm
        · rw [Category.assoc, Category.assoc, hψ₂, hl₂, reassoc_of% e, Category.comp_id]
      exact (congrArg (· ≫ ψ) (hlv u)).symm.trans key)
  exact ⟨c₁, GlobalTheory.SiegelDescent.principal_of_fieldExtension h M o ζ K₁ K K₁.subtype _ s c₁ c hc₁ hc, hc₁⟩

end GlobalTheory.SiegDesc
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.FrameCompare
open GlobalTheory.IndefiniteRowSideFullHecke.LocalFramePowerSections (PowSec)

variable {S : Scheme.{0}} (G : Over S)

variable [GrpObj G] [IsCommMonObj G] (L : RigLB G) (N : ℕ)


omit [GrpObj G] [IsCommMonObj G] in
theorem relAmple_iff {O : Type} [CommRing O] (b : S ⟶ Sp O) {A : LB S} (hA : A.IsLB) :
    (Out.RelAmple (Over.mk b) A →
      ∀ z : S, ∃ (d : ℕ) (s : Out.H0 A d), 1 ≤ d ∧ z ∈ Out.nonzeroLocus s ∧ IsAffineOpen (Out.nonzeroLocus s)) ∧
    (IsProper b → (∀ z : S, ∃ (d : ℕ) (s : Out.H0 A d), 1 ≤ d ∧ z ∈ Out.nonzeroLocus s ∧
      IsAffineOpen (Out.nonzeroLocus s)) → Out.RelAmple (Over.mk b) A) := by
  constructor
  · intro h z
    obtain ⟨n, hn, s, hs⟩ := (isAmpleLB_of_relAmple_of_isAffine (Over.mk b) hA h).exists_affine z
    obtain ⟨s', e, -⟩ := exists_sec_oneTerm A (K' := Fin 1) (e' := (n : ℤ)) rfl s
    exact ⟨n, s', hn, by rw [← e] at hs; exact hs⟩
  · intro hb h
    have : IsProper (Over.mk b).hom := hb
    have hc : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace b
    have ha : IsAmpleLB A := ⟨hA, hc, fun z => by
      obtain ⟨n, s, hn, hs⟩ := h z
      obtain ⟨s', e, -⟩ := exists_sec_oneTerm A (K' := PUnit) (e' := (n : ℤ)) rfl s
      exact ⟨n, hn, s', by rw [← e] at hs; exact hs⟩⟩
    refine relAmple_of_isAmpleLB (Over.mk b) hA fun U hU => ?_
    have : CompactSpace (b ⁻¹ᵁ U).toScheme :=
      isCompact_iff_compactSpace.1 (QuasiCompact.isCompact_preimage (f := b) _ U.isOpen hU.isCompact)
    exact ha.pull_of_isOpenImmersion (b ⁻¹ᵁ U).ι

end GlobalTheory.FrameCompare
end
end
