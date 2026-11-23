module

public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PerfectPairingCount

variable {F : Type} [Field F]

theorem linearIndependent_unitsChar (G : Type) [Group G] :
    LinearIndependent F (fun (f : G →* Fˣ) => (fun g => ((f g : Fˣ) : F) : G → F)) := by
  have h := linearIndependent_monoidHom G F
  have hinj : Function.Injective (fun f : G →* Fˣ => (Units.coeHom F).comp f) := by
    intro f g hfg
    ext x
    exact DFunLike.congr_fun hfg x
  exact h.comp _ hinj

theorem finite_unitsChar (G : Type) [Group G] [Finite G] : Finite (G →* Fˣ) :=
  (linearIndependent_unitsChar (F := F) G).finite

theorem card_unitsChar_le (G : Type) [Group G] [Finite G] :
    Nat.card (G →* Fˣ) ≤ Nat.card G := by
  classical
  haveI := finite_unitsChar (F := F) G
  haveI := Fintype.ofFinite (G →* Fˣ)
  haveI := Fintype.ofFinite G
  have h := (linearIndependent_unitsChar (F := F) G).fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card] at h
  simpa [Nat.card_eq_fintype_card] using h

variable {A : Type} [CommGroup A] [Finite A]

theorem card_ker_mul_le (E : A →* (A →* Fˣ)) (hE : ∀ a, (∀ b, E a b = 1) → a = 1)
    (H K : Subgroup A) (hK : ∀ k ∈ K, ∀ h ∈ H, E k h = 1) :
    Nat.card K * Nat.card H ≤ Nat.card A := by
  haveI := finite_unitsChar (F := F) (A ⧸ H)
  let φ : K → (A ⧸ H →* Fˣ) := fun k =>
    QuotientGroup.lift H (E k) (fun h hh => hK k k.2 h hh)
  have hφ : Function.Injective φ := by
    intro k k' hkk
    have h1 : E k = E k' := by
      apply MonoidHom.ext
      intro b
      have := DFunLike.congr_fun hkk (QuotientGroup.mk b)
      exact this
    have h2 : (k : A) * (k' : A)⁻¹ = 1 := by
      apply hE
      intro b
      rw [map_mul, map_inv, h1, mul_inv_cancel]
      rfl
    exact Subtype.ext (mul_inv_eq_one.mp h2)
  have h3 : Nat.card K ≤ Nat.card (A ⧸ H) :=
    (Nat.card_le_card_of_injective φ hφ).trans (card_unitsChar_le _)
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup H]
  exact Nat.mul_le_mul_right _ h3

theorem right_nondegenerate (E : A →* (A →* Fˣ)) (hE : ∀ a, (∀ b, E a b = 1) → a = 1)
    (b : A) (hb : ∀ a, E a b = 1) : b = 1 := by
  have h := card_ker_mul_le E hE E.flip.ker ⊤ (fun k _ h hh => by
    have := DFunLike.congr_fun (MonoidHom.mem_ker.mp hh) k
    simpa using this)
  rw [Subgroup.card_top] at h
  have hpos : 0 < Nat.card A := Nat.card_pos
  have h1 : Nat.card E.flip.ker ≤ 1 := by
    have : Nat.card A * Nat.card E.flip.ker ≤ Nat.card A * 1 := by simpa using h
    exact Nat.le_of_mul_le_mul_left this hpos
  have h2 : E.flip.ker = ⊥ := Subgroup.card_le_one_iff_eq_bot _ |>.mp h1
  have h3 : b ∈ E.flip.ker := by
    rw [MonoidHom.mem_ker]
    apply MonoidHom.ext
    intro a
    simpa using hb a
  rw [h2] at h3
  exact Subgroup.mem_bot.mp h3

theorem one_side (E : A →* (A →* Fˣ)) (hE : ∀ a, (∀ b, E a b = 1) → a = 1)
    (T H : Subgroup A) (hTH : ∀ t ∈ T, ∀ h ∈ H, E t h = 1)
    (hc : Nat.card T * Nat.card H = Nat.card A) :
    (∀ x, (∀ h ∈ H, E x h = 1) ↔ x ∈ T) ∧ (∀ χ : H →* Fˣ, ∃ x, ∀ h : H, E x h = χ h) := by
  let R : A →* (H →* Fˣ) :=
    { toFun := fun a => (E a).comp H.subtype
      map_one' := by apply MonoidHom.ext; intro h; simp
      map_mul' := by intro a a'; apply MonoidHom.ext; intro h; simp }
  have hR : ∀ x, x ∈ R.ker ↔ ∀ h ∈ H, E x h = 1 := by
    intro x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx h hh
      exact DFunLike.congr_fun hx ⟨h, hh⟩
    · intro hx
      apply MonoidHom.ext
      intro h
      exact hx h h.2
  have hle : T ≤ R.ker := fun t ht => (hR t).mpr (hTH t ht)
  have hHpos : 0 < Nat.card H := Nat.card_pos
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have hcard : Nat.card R.ker ≤ Nat.card T := by
    have := card_ker_mul_le E hE H R.ker (fun k hk => (hR k).mp hk)
    rw [← hc] at this
    exact Nat.le_of_mul_le_mul_right this hHpos
  have heq : T = R.ker := Subgroup.eq_of_le_of_card_ge hle hcard
  refine ⟨fun x => by rw [← hR, heq], ?_⟩
  haveI := finite_unitsChar (F := F) H
  have hrange : Nat.card R.range = Nat.card H := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup R.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange R).toEquiv, ← heq, ← hc,
      mul_comm] at h1
    exact (Nat.eq_of_mul_eq_mul_right hTpos h1).symm
  have htop : R.range = ⊤ := by
    apply Subgroup.eq_of_le_of_card_ge le_top
    rw [Subgroup.card_top, hrange]
    exact card_unitsChar_le _
  intro χ
  have : χ ∈ R.range := by rw [htop]; trivial
  obtain ⟨x, hx⟩ := this
  exact ⟨x, fun h => DFunLike.congr_fun hx h⟩

end GlobalTheory.PerfectPairingCount

namespace GlobalTheory

theorem perfectPairing_orthogonal_of_card :
    ∀ (F : Type) [Field F] (A : Type) [CommGroup A] [Finite A] (e : A → A → Fˣ), (∀ a a' b, e (a * a') b = e a b * e a' b) → (∀ a b b', e a (b * b') = e a b * e a b') → (∀ a, (∀ b, e a b = 1) → a = 1) → ∀ T H : Subgroup A, (∀ t ∈ T, ∀ h ∈ H, e t h = 1) → Nat.card T * Nat.card H = Nat.card A → (∀ x, (∀ h ∈ H, e x h = 1) ↔ x ∈ T) ∧ (∀ x, (∀ t ∈ T, e t x = 1) ↔ x ∈ H) ∧ (∀ χ : H →* Fˣ, ∃ x, ∀ h : H, e x h = χ h) ∧ (∀ χ : T →* Fˣ, ∃ x, ∀ t : T, e t x = χ t) := by
  intro F _ A _ _ e h1 h2 h3 T H hTH hc
  let E : A →* (A →* Fˣ) :=
    MonoidHom.mk' (fun a => MonoidHom.mk' (e a) (h2 a)) (fun a a' => by
      apply MonoidHom.ext
      intro b
      exact h1 a a' b)
  have hE : ∀ a, (∀ b, E a b = 1) → a = 1 := h3
  have hE' : ∀ b, (∀ a, E.flip b a = 1) → b = 1 :=
    fun b hb => PerfectPairingCount.right_nondegenerate E hE b hb
  obtain ⟨a1, a2⟩ := PerfectPairingCount.one_side E hE T H hTH hc
  obtain ⟨b1, b2⟩ := PerfectPairingCount.one_side E.flip hE' H T
    (fun h hh t ht => hTH t ht h hh) (by rw [mul_comm, hc])
  exact ⟨a1, b1, a2, b2⟩

end GlobalTheory
end

section

namespace GlobalTheory.PowGrp

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}}

theorem prop_powObj (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    (G : Over S) (hG : P G.hom) : ∀ n : ℕ, P (powObj G n).hom
  | 0 => P.id_mem S
  | n + 1 =>
    P.comp_mem (pullback.fst G.hom (powObj G n).hom) G.hom
      (P.pullback_fst _ _ (prop_powObj P G hG n)) hG

theorem smooth_isMultiplicative : MorphismProperty.IsMultiplicative (C := Scheme.{0}) @Smooth where
  id_mem _ := inferInstance
  comp_mem f g (_ : Smooth f) (_ : Smooth g) := inferInstance

attribute [local instance] smooth_isMultiplicative

theorem exists_iso_powObj {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ} (p : IsPowGrp G' G j) :
    ∃ e : G'.left ⟶ (powObj G j).left, IsIso e ∧ G'.hom = e ≫ (powObj G j).hom := by
  let e : G' ≅ powObj G j := p.lim.conePointUniqueUpToIso (powIsLimit G j)
  exact ⟨e.hom.left, inferInstanceAs (IsIso ((Over.forget _).map e.hom)), (Over.w e.hom).symm⟩

theorem prop_of_isPowGrp (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ} (p : IsPowGrp G' G j) (hG : P G.hom) : P G'.hom := by
  obtain ⟨e, he, hw⟩ := exists_iso_powObj p
  rw [hw]
  exact (P.cancel_left_of_respectsIso e _).2 (prop_powObj P G hG j)

theorem relDim_powObj (G : Over S) (g : ℕ) (hG : SmoothOfRelativeDimension g G.hom) :
    ∀ n : ℕ, SmoothOfRelativeDimension (n * g) (powObj G n).hom
  | 0 => by
    have h : SmoothOfRelativeDimension 0 (𝟙 S) := inferInstance
    rw [Nat.zero_mul]
    exact h
  | n + 1 => by
    have ih := relDim_powObj G g hG n
    have h1 : SmoothOfRelativeDimension (n * g) (pullback.fst G.hom (powObj G n).hom) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
        (IsPullback.of_hasPullback _ _).flip ih
    have h2 : SmoothOfRelativeDimension (n * g + g) (pullback.fst G.hom (powObj G n).hom ≫ G.hom) :=
      inferInstance
    rw [Nat.succ_mul]
    exact h2

theorem geomConnected_of_isIso {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] : GeometricallyConnected f := by
  refine ⟨fun K _ y Z fst snd h ↦ ?_⟩
  have : IsIso snd := h.isIso_snd_of_isIso
  exact snd.homeomorph.symm.surjective.connectedSpace snd.homeomorph.symm.continuous

theorem geomConnected_powObj (G : Over S) [Smooth G.hom] [GeometricallyConnected G.hom] :
    ∀ n : ℕ, GeometricallyConnected (powObj G n).hom
  | 0 => geomConnected_of_isIso (𝟙 S)
  | n + 1 => by
    have := geomConnected_powObj G n
    have : Smooth (powObj G n).hom := prop_powObj @Smooth G ‹_› n
    show GeometricallyConnected (pullback.fst G.hom (powObj G n).hom ≫ G.hom)
    exact GeometricallyConnected.comp _ _

theorem comm_of_isPowGrp {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ} (p : IsPowGrp G' G j)
    (hG : IsCommMonObj G) : IsCommMonObj G' := by
  refine ⟨p.lim.hom_ext fun ⟨i⟩ => ?_⟩
  have := p.hom i
  show ((β_ G' G').hom ≫ μ) ≫ p.pr i = μ ≫ p.pr i
  rw [Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm]

theorem powers : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [GrpObj G] (j : ℕ) (p : IsPowGrp G' G j), (Smooth G.hom → Smooth G'.hom) ∧ (IsSeparated G.hom → IsSeparated G'.hom) ∧ (∀ g : ℕ, SmoothOfRelativeDimension g G.hom → SmoothOfRelativeDimension (j * g) G'.hom) ∧ (IsAbelianScheme G → IsAbelianScheme G') ∧ (IsSemiAbelian G → IsCommMonObj G') := by
  intro S G' G _ _ j p
  refine ⟨prop_of_isPowGrp @Smooth p, prop_of_isPowGrp @IsSeparated p, fun g hg => ?_, fun hG => ?_,
    fun hG => comm_of_isPowGrp p hG.comm⟩
  · obtain ⟨e, he, hw⟩ := exists_iso_powObj p
    have h1 := relDim_powObj G g hg j
    have h2 : SmoothOfRelativeDimension (0 + j * g) G'.hom := by
      rw [hw]; infer_instance
    rwa [Nat.zero_add] at h2
  · refine ⟨comm_of_isPowGrp p hG.comm, prop_of_isPowGrp @Smooth p hG.smooth,
      prop_of_isPowGrp @IsProper p hG.proper, ?_⟩
    obtain ⟨e, he, hw⟩ := exists_iso_powObj p
    have := hG.smooth
    have := hG.geomConnected
    have := geomConnected_powObj G j
    have : Smooth (powObj G j).hom := prop_powObj @Smooth G ‹_› j
    have := geomConnected_of_isIso e
    rw [hw]
    exact GeometricallyConnected.comp _ _

end GlobalTheory.PowGrp
end
