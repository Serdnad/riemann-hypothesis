module

import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle733
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle677
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle542
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle712
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle744
public import Formalism.LocalRingCardinality.DataTheta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle199
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechTripleRestrictCompositeInjectiveSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle256
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle258
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle450
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle292
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle452
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleCoboundaryCommaLocalBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle157
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle290
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle622
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle713
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle715
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false

namespace GlobalTheory.CechPoset.CechPosetH1Surjective

open GlobalTheory.CechPoset

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

theorem hom_eq {a b : (NE κ)ᵒᵖ} (φ ψ : a ⟶ b) : φ = ψ :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

noncomputable def V (f : Z1 F) (b : (NE κ)ᵒᵖ) (x : κ) : F.obj b :=
  if hx : x ∈ sub b then
    f.1 (ne {x} (Finset.singleton_nonempty x)) b
      (homOf (show ({x} : Finset κ) ⊆ sub b from Finset.singleton_subset_iff.2 hx))
  else 0

variable {F}

theorem V_res (f : Z1 F) {a b : (NE κ)ᵒᵖ} (φ : a ⟶ b) {x : κ} (hx : x ∈ sub a) :
    mp F φ (V F f a x) = V F f b x - f.1 a b φ := by
  unfold V
  rw [dite_eq_left hx, dite_eq_left (sub_subset φ hx)]
  have e := Z1.comp f (homOf (a := ne {x} (Finset.singleton_nonempty x)) (b := a)
    (Finset.singleton_subset_iff.2 hx)) φ
  rw [hom_eq (_ ≫ φ) (homOf (a := ne {x} (Finset.singleton_nonempty x)) (b := b)
    (Finset.singleton_subset_iff.2 (sub_subset φ hx)))] at e
  rw [e]
  ring

noncomputable def zc (f : Z1 F) : CC F 1 := fun t =>
  V F f (ne t.1 (card_nonempty t)) (t.1.min' (card_nonempty t)) -
    V F f (ne t.1 (card_nonempty t)) (t.1.max' (card_nonempty t))

theorem zc_res (f : Z1 F) (s : {s : Finset κ // s.card = 1 + 1}) (b : (NE κ)ᵒᵖ)
    (h : sub (ne s.1 (card_nonempty s)) ⊆ sub b) :
    mp F (homOf h) (zc f s) = V F f b (s.1.min' (card_nonempty s)) - V F f b (s.1.max' (card_nonempty s)) := by
  unfold zc
  rw [map_sub, V_res f (homOf h) (x := s.1.min' (card_nonempty s)) (Finset.min'_mem _ _),
    V_res f (homOf h) (x := s.1.max' (card_nonempty s)) (Finset.max'_mem _ _)]
  ring

theorem pair_min_max {s : Finset κ} {x y : κ} (hs : s = {x, y}) (h : x < y) (hne : s.Nonempty) :
    s.min' hne = x ∧ s.max' hne = y := by
  subst hs
  constructor
  · exact le_antisymm (Finset.min'_le _ _ (by simp)) (Finset.le_min' _ _ _ (by
      intro z hz; simp at hz; rcases hz with rfl | rfl
      · exact le_rfl
      · exact h.le))
  · exact le_antisymm (Finset.max'_le _ _ _ (by
      intro z hz; simp at hz; rcases hz with rfl | rfl
      · exact h.le
      · exact le_rfl)) (Finset.le_max' _ _ (by simp))

theorem exists_triple {s : Finset κ} (h : s.card = 3) : ∃ a b c, a < b ∧ b < c ∧ s = {a, b, c} := by
  apply GlobalTheory.AbLaw.CechOne.exists_triple <;> assumption

end GlobalTheory.CechPoset.CechPosetH1Surjective

namespace GlobalTheory.CechPoset.CechPosetH1Surjective
open GlobalTheory.CechPoset
variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] {F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R}

theorem erase3 {a b c : κ} (hab : a < b) (hbc : b < c) :
    ({a, b, c} : Finset κ).erase a = {b, c} ∧ ({a, b, c} : Finset κ).erase b = {a, c} ∧
      ({a, b, c} : Finset κ).erase c = {a, b} := by
  have hac := hab.trans hbc
  refine ⟨?_, ?_, ?_⟩ <;> ext w <;> simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] <;>
    constructor
  all_goals first
    | (rintro ⟨hw, h | h | h⟩ <;> first | exact absurd h hw | (subst h; simp))
    | (rintro (h | h) <;> subst h <;> simp [hab.ne, hab.ne', hbc.ne, hbc.ne', hac.ne, hac.ne'])

theorem sign3 {a b c : κ} (hab : a < b) (hbc : b < c) :
    GlobalTheory.cubeSign ({a, b, c} : Finset κ) a = 1 ∧ GlobalTheory.cubeSign ({a, b, c} : Finset κ) b = -1 ∧
      GlobalTheory.cubeSign ({a, b, c} : Finset κ) c = 1 := by
  have hac := hab.trans hbc
  refine ⟨?_, ?_, ?_⟩ <;> simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, hab, hbc, hac,
    not_lt.2 hab.le, not_lt.2 hbc.le, not_lt.2 hac.le, Finset.card_pair hab.ne]

theorem part2 (f : Z1 F) : f.1 - e1 F (zc f) = d0 F (fun a => V F f a (mn a)) := by
  funext a b φ
  simp only [Pi.sub_apply, amitsur_d0_apply]
  rw [V_res f φ (mn_mem a)]
  by_cases h : mn b < mn a
  · have e : e1 F (zc f) a b φ = -(mp F (homOf (a := ne {mn b, mn a} (Finset.insert_nonempty _ _)) (b := b)
        (pair_subset φ)) (zc f ⟨{mn b, mn a}, Finset.card_pair h.ne⟩)) := by
      simp [e1, h]
    have z := zc_res f ⟨{mn b, mn a}, Finset.card_pair h.ne⟩ b (pair_subset φ)
    obtain ⟨h1, h2⟩ := pair_min_max (s := ({mn b, mn a} : Finset κ)) rfl h (Finset.insert_nonempty _ _)
    rw [h1, h2] at z
    rw [e]
    linear_combination z
  · have e : e1 F (zc f) a b φ = 0 := by simp [e1, h]
    have e' : mn b = mn a := le_antisymm (mn_le_of_hom φ) (not_lt.1 h)
    rw [e, e']
    ring

end GlobalTheory.CechPoset.CechPosetH1Surjective

namespace GlobalTheory.CechPoset.CechPosetH1Surjective
open GlobalTheory.CechPoset
variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] {F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R}

def term3 {M : Type} [AddCommGroup M] (W : κ → M) (a b c x : κ) : M :=
  GlobalTheory.cubeSign ({a, b, c} : Finset κ) x • (if x = a then W b - W c else if x = b then W a - W c else W a - W b)

theorem sum3 {M : Type} [AddCommGroup M] (W : κ → M) {a b c : κ} (hab : a < b) (hbc : b < c) :
    ∑ x ∈ ({a, b, c} : Finset κ), term3 W a b c x = 0 := by
  have hac := hab.trans hbc
  rw [Finset.sum_insert (by simp [hab.ne, hac.ne]), Finset.sum_insert (by simp [hbc.ne]),
    Finset.sum_singleton]
  obtain ⟨s1, s2, s3⟩ := sign3 hab hbc
  simp only [term3, if_pos rfl, if_neg hab.ne', if_neg hac.ne', if_neg hbc.ne', s1, s2, s3, one_smul, neg_smul]
  norm_num

theorem part1 (f : Z1 F) : δ F 1 (zc f) = 0 := by
  funext t
  rw [δ_apply]
  obtain ⟨s, hs⟩ := t
  obtain ⟨a, b, c, hab, hbc, rfl⟩ := exists_triple (s := s) (by rw [hs])
  have hac := hab.trans hbc
  obtain ⟨e1', e2', e3'⟩ := erase3 hab hbc
  refine (Finset.sum_congr rfl
    (g := fun i : ({a, b, c} : Finset κ) => term3 (V F f (ne {a, b, c} (card_nonempty ⟨_, hs⟩))) a b c i.1)
    fun i _ => ?_).trans ?_
  · have z := zc_res f (GlobalTheory.Cube.eraseIdx ⟨{a, b, c}, hs⟩ i) (ne _ (card_nonempty ⟨_, hs⟩))
      (Finset.erase_subset i.1 _)
    rw [z]
    obtain ⟨x, hx⟩ := i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · obtain ⟨h1, h2⟩ := pair_min_max (s := (GlobalTheory.Cube.eraseIdx ⟨{x, b, c}, hs⟩ ⟨x, by simp⟩).1) e1' hbc
        (card_nonempty _)
      rw [h1, h2, term3, if_pos rfl]
    · obtain ⟨h1, h2⟩ := pair_min_max (s := (GlobalTheory.Cube.eraseIdx ⟨{a, x, c}, hs⟩ ⟨x, by simp⟩).1) e2' hac
        (card_nonempty _)
      rw [h1, h2, term3, if_neg hab.ne', if_pos rfl]
    · obtain ⟨h1, h2⟩ := pair_min_max (s := (GlobalTheory.Cube.eraseIdx ⟨{a, b, x}, hs⟩ ⟨x, by simp⟩).1) e3' hab
        (card_nonempty _)
      rw [h1, h2, term3, if_neg hac.ne', if_neg hbc.ne']
  · refine (Finset.sum_coe_sort ({a, b, c} : Finset κ)
      (term3 (V F f (ne {a, b, c} (card_nonempty ⟨_, hs⟩))) a b c)).trans ?_
    exact sum3 _ hab hbc

end GlobalTheory.CechPoset.CechPosetH1Surjective


open GlobalTheory.CechPoset.CechPosetH1Surjective in
theorem GlobalTheory.CechPoset.exists_cech_cocycle_cohomologous : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R]
    (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (f : Z1 F),
    ∃ z : CC F 1, δ F 1 z = 0 ∧ ∃ g : C0 F, f.1 - e1 F z = d0 F g :=
  fun F f => ⟨zc f, part1 f, fun a => V F f a (mn a), part2 f⟩
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem stdForm_incl_map_eq {F F' : Type} [Field F] [Field F'] [Algebra F F'] (n : ℕ) (t : F' ≃ₐ[F] F')
    (γ : GL (Fin n) F) :
    ((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F').map t =
      ((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') := by
  ext i j
  show t (algebraMap F F' ((γ : Matrix (Fin n) (Fin n) F) i j)) = algebraMap F F' ((γ : Matrix (Fin n) (Fin n) F) i j)
  exact t.commutes _

theorem stdForm_adjoin_map_mem {F F' : Type} [Field F] [Field F'] [Algebra F F'] (n : ℕ) (t : F' ≃ₐ[F] F')
    (γ : GL (Fin n) F) {M : Matrix (Fin n) (Fin n) F'}
    (hM : M ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')}) :
    M.map t ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} := by
  apply GlobalTheory.Shin.NormSurj.adjoin_stable <;> assumption

theorem stdForm_commute_iff {F' : Type} [Field F'] {n : ℕ} (x y : GL (Fin n) F') :
    Commute x y ↔ Commute (x : Matrix (Fin n) (Fin n) F') (y : Matrix (Fin n) (Fin n) F') := by
  simp only [Commute, SemiconjBy, Units.ext_iff, Units.val_mul]

theorem isNorm_exists_twistedConj_adjoin :
    ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
      (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (δ : GL (Fin n) F') (γ : GL (Fin n) F),
      IsNorm s δ γ → ∃ y : GL (Fin n) F', ((y⁻¹ * δ * galAct F F' n s y : GL (Fin n) F') :
        Matrix (Fin n) (Fin n) F') ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} ∧
        nrm s (y⁻¹ * δ * galAct F F' n s y) = incl F F' n γ := by
  intro F F' _ _ _ _ s hs n δ γ hN
  obtain ⟨_, -, h3, h4, h5⟩ := GlobalTheory.T.galoisTwistedNormGL_basic_properties F F' s hs n

  have hgfix : ∀ t : F' ≃ₐ[F] F', galAct F F' n t (incl F F' n γ) = incl F F' n γ := fun t =>
    Units.ext (stdForm_incl_map_eq n t γ)

  have hC : ∀ z w : GL (Fin n) F',
      (z : Matrix (Fin n) (Fin n) F') ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} →
      Commute w (incl F F' n γ) → Commute z w := by
    intro z w hz hw
    rw [stdForm_commute_iff] at hw ⊢
    exact (Algebra.commute_of_mem_adjoin_singleton_of_commute hz hw).symm
  have hCt : ∀ (t : F' ≃ₐ[F] F') (w : GL (Fin n) F'), Commute w (incl F F' n γ) →
      Commute (galAct F F' n t w) (incl F F' n γ) := by
    intro t w hw
    have := hw.map (galAct F F' n t)
    rwa [hgfix t] at this

  obtain ⟨c, hc⟩ := isConj_iff.1 hN
  have hn1 : nrm s (c⁻¹ * δ * galAct F F' n s c) = incl F F' n γ := by
    rw [h3, ← hc]; group
  have hcomm1 : Commute (c⁻¹ * δ * galAct F F' n s c) (incl F F' n γ) := by
    have := h4 (c⁻¹ * δ * galAct F F' n s c)
    rw [hn1, hgfix s] at this
    exact this

  obtain ⟨δ₀, hδ₀A, hn0⟩ := GlobalTheory.T.norm_map_surjective_finite_field F F' s hs n γ
  have hδ₀g : Commute δ₀ (incl F F' n γ) := hC δ₀ _ hδ₀A (Commute.refl _)
  have hεg : Commute (δ₀⁻¹ * (c⁻¹ * δ * galAct F F' n s c)) (incl F F' n γ) :=
    (hδ₀g.inv_left).mul_left hcomm1
  have hεn : nrm s (δ₀⁻¹ * (c⁻¹ * δ * galAct F F' n s c)) = 1 := by
    have hp := h5 δ₀ (δ₀⁻¹ * (c⁻¹ * δ * galAct F F' n s c)) (fun t u =>
      hC _ _ (by rw [show ((galAct F F' n t δ₀ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') =
        (δ₀ : Matrix (Fin n) (Fin n) F').map t from rfl]; exact stdForm_adjoin_map_mem n t γ hδ₀A) (hCt u _ hεg))
    rw [mul_inv_cancel_left, hn1, hn0] at hp
    exact (mul_eq_left.1 hp.symm)

  have hBst : ∀ M ∈ Subalgebra.centralizer F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')},
      M.map s ∈ Subalgebra.centralizer F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} := by
    intro M hM
    rw [Subalgebra.mem_centralizer_iff] at hM ⊢
    intro g' hg'
    rw [Set.mem_singleton_iff] at hg'
    subst hg'
    have e := congrArg (fun N => ((s : F' ≃+* F') : F' →+* F').mapMatrix N) (hM _ rfl)
    simp only [map_mul] at e
    rw [← stdForm_incl_map_eq n s γ]
    exact e
  have hεB : ((δ₀⁻¹ * (c⁻¹ * δ * galAct F F' n s c) : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈
      Subalgebra.centralizer F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g' hg'
    rw [Set.mem_singleton_iff] at hg'
    subst hg'
    exact ((stdForm_commute_iff _ _).1 hεg).eq.symm
  obtain ⟨x, hxB, hεx⟩ := GlobalTheory.T.exists_coboundary_of_norm_one_in_subalgebra F F' s hs n _ hBst _ hεB hεn
  have hxg : Commute x (incl F F' n γ) := by
    rw [stdForm_commute_iff]
    exact ((Subalgebra.mem_centralizer_iff F').1 hxB _ rfl).symm
  have hxδ₀ : Commute δ₀ x := hC δ₀ x hδ₀A hxg
  have e1 : c⁻¹ * δ * galAct F F' n s c = δ₀ * (x⁻¹ * galAct F F' n s x) := by
    rw [← hεx, mul_inv_cancel_left]
  have key : (c * x⁻¹)⁻¹ * δ * galAct F F' n s (c * x⁻¹) = δ₀ := by
    rw [map_mul, map_inv]
    calc (c * x⁻¹)⁻¹ * δ * (galAct F F' n s c * (galAct F F' n s x)⁻¹)
        = x * (c⁻¹ * δ * galAct F F' n s c) * (galAct F F' n s x)⁻¹ := by group
      _ = x * δ₀ * x⁻¹ := by rw [e1]; group
      _ = δ₀ := by rw [← hxδ₀.eq]; group
  exact ⟨c * x⁻¹, by rw [key]; exact hδ₀A, by rw [key]; exact hn0⟩

end GlobalTheory.Shin
end

section

open Formalism.BasicNotions.TH MvPolynomial

namespace GlobalTheory

theorem pderiv_pderiv_comm_fock {σ : Type} (i j : σ) (P : MvPolynomial σ ℂ) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  apply GlobalTheory.FockCasimir.pderiv_pderiv_comm <;> assumption

theorem fock_letters_ccr (p q r s : ℕ) (l m : Ln p q r s) :
    (lowB l * raiB m - raiB m * lowB l = if l = m then (1 : Module.End ℂ (Pol p q r s)) else 0) ∧
      lowB l * lowB m = lowB m * lowB l ∧ raiB l * raiB m = raiB m * raiB l := by
  classical
  have hcomm : ∀ (i j : Ln p q r s) (P : Pol p q r s), pderiv i (pderiv j P) = pderiv j (pderiv i P) :=
    fun i j P => pderiv_pderiv_comm_fock i j P
  have hX : ∀ (i j : Ln p q r s), pderiv i (X j : Pol p q r s) = if j = i then 1 else 0 := by
    intro i j
    rw [pderiv_X, Pi.single_apply]
  have hne : ∀ l m : Ln p q r s, linePos l ≠ linePos m → l ≠ m := by
    rintro l m h rfl
    exact h rfl
  refine ⟨?_, ?_, ?_⟩
  · by_cases hlm : l = m
    · subst hlm
      rw [if_pos rfl]
      cases hl : linePos l <;> simp only [lowB, raiB, hl, Bool.false_eq_true, ↓reduceIte] <;>
        refine LinearMap.ext fun f => ?_ <;>
        simp [Module.End.mul_apply, hX]
    · rw [if_neg hlm]
      cases hl : linePos l <;> cases hm : linePos m <;>
        simp only [lowB, raiB, hl, hm, Bool.false_eq_true, ↓reduceIte] <;>
        refine LinearMap.ext fun f => ?_ <;>
        simp [Module.End.mul_apply, hX, hcomm, Ne.symm hlm, hlm] <;> ring
  · cases hl : linePos l <;> cases hm : linePos m <;>
      simp only [lowB, hl, hm, Bool.false_eq_true, ↓reduceIte] <;>
      refine LinearMap.ext fun f => ?_ <;>
      simp [Module.End.mul_apply, hX, hcomm] <;> (try ring_nf) <;> (try (intro h; subst h; exact absurd (hl.symm.trans hm) (by decide)))
  · cases hl : linePos l <;> cases hm : linePos m <;>
      simp only [raiB, hl, hm, Bool.false_eq_true, ↓reduceIte] <;>
      refine LinearMap.ext fun f => ?_ <;>
      simp [Module.End.mul_apply, hX, hcomm] <;> (try ring_nf) <;> (try (intro h; subst h; exact absurd (hl.symm.trans hm) (by decide)))

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem restrictO_bijective_of_basis {R' : Type} [CommRing R'] {X' : Scheme.{0}} (s' : X' ⟶ Sp R')
    {C' : Type} [Category.{0} C'] [Quiver.IsThin C'] (G : C' ⥤ AffOp X')
    (hcov : ∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (OAff s').obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S),
        IsUnit (mp (OAff s') u (b i)) →
          ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u)
    (hdir : ∀ (t₁ t₂ : C') (S : AffOp X'), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) →
      ∃ (n : ℕ) (b : Fin n → (OAff s').obj S), Ideal.span (Set.range b) = ⊤ ∧
        ∀ (i : Fin n) (S' : AffOp X') (u : S ⟶ S'), IsUnit (mp (OAff s') u (b i)) →
          ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) :
    Function.Bijective (CoefMap.restrict (OAff s') G).pull1 ∧
      Function.Bijective (CoefMap.restrict (OAff s') G).pull2 := by
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s'
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s') G H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s') G H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s') G H hcov hdir
  have hv2 := GlobalTheory.T.twoCocycle_coboundary_of_basisFunctor (OAff s') G H hcov hdir
  exact ⟨⟨_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg,
      _root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hs hg hv⟩,
    GlobalTheory.T.comma_descent_injective _ _ hs hg hv, GlobalTheory.T.comma_descent_restriction_equiv _ _ hs hg hv hv2⟩

section

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}

theorem pairResO_bijective (φ : X' ⟶ X) (s' : X' ⟶ Sp R') :
    Function.Bijective (pairRes φ s').pull1 ∧ Function.Bijective (pairRes φ s').pull2 :=
  restrictO_bijective_of_basis s' (pairFst φ) (pair_cover_affine φ s') (exists_pair_below_two φ s')

theorem triResO_injective (ψ : X'' ⟶ X') (φ : X' ⟶ X) (s'' : X'' ⟶ Sp R'') :
    Function.Injective (cechTripleRestrictComposite ψ φ s'').pull1 := by
  have key : ∀ c : HO1 s'', (cechTripleRestrictComposite ψ φ s'').pull1 ((pairRes (ψ ≫ φ) s'').pull1 c) =
      (CoefMap.restrict (OAff s'') (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ))).pull1 c := fun c ↦ by
    rw [← CoefMap.pullCohomologyOne_comp]
    exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s'') _ b) c
  intro x y e
  obtain ⟨x0, rfl⟩ := (pairResO_bijective (ψ ≫ φ) s'').1.2 x
  obtain ⟨y0, rfl⟩ := (pairResO_bijective (ψ ≫ φ) s'').1.2 y
  rw [key, key] at e
  rw [(restrictO_bijective_of_basis s'' _ (triple_cover_affine ψ φ s'')
    (exists_triple_below_two ψ φ s'')).1.1 e]

variable {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {τ : R' →+* R''}
  {φ : X' ⟶ X} {ψ : X'' ⟶ X'}

theorem isPullO_comp (h : φ ≫ s = s' ≫ spMap σ) (h' : ψ ≫ s' = s'' ≫ spMap τ)
    (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (τ.comp σ)) (a : HO1 s) (a' : HO1 s') (a'' : HO1 s'')
    (p : IsPullO h a a') (p' : IsPullO h' a' a'') : IsPullO h'' a a'' := by
  apply GlobalTheory.CompanionTheory.Axis.PullO.isPullO_comp <;> assumption

theorem isPullO2_cup (h : φ ≫ s = s' ≫ spMap σ) (a b : HO1 s) (a' b' : HO1 s')
    (p : IsPullO h a a') (q : IsPullO h b b') :
    IsPullbackH2Structure h (GlobalTheory.CatCoh.cup _ a b) (GlobalTheory.CatCoh.cup _ a' b') := by
  have p0 : (pairPull h).pull1 a = (pairRes φ s').pull1 a' := p
  have q0 : (pairPull h).pull1 b = (pairRes φ s').pull1 b' := q
  unfold IsPullbackH2Structure
  rw [CoefMap.pullCohomologyTwo_cup, CoefMap.pullCohomologyTwo_cup, p0, q0]

end

theorem pullO_basic : ∀ (R : Type) [CommRing R] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R) (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap (RingHom.id R)), Function.Bijective (pairRes φ s').pull2 ∧ (∀ a b a' b', IsPullO h a a' → IsPullO h b b' → IsPullbackH2Structure h (GlobalTheory.CatCoh.cup _ a b) (GlobalTheory.CatCoh.cup _ a' b')) ∧ ∀ (X'' : Scheme.{0}) (s'' : X'' ⟶ Sp R) (ψ : X'' ⟶ X') (h' : ψ ≫ s' = s'' ≫ spMap (RingHom.id R)) (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (RingHom.id R)) a a' a'', IsPullO h a a' → IsPullO h' a' a'' → IsPullO h'' a a'' :=
  fun _ _ _ _ _ s' φ h ↦ ⟨(pairResO_bijective φ s').2, fun a b a' b' p q ↦ isPullO2_cup h a b a' b' p q,
    fun _ _ _ h' h'' a a' a'' p p' ↦ isPullO_comp h h' h'' a a' a'' p p'⟩

end GlobalTheory.Obs
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.modF_finiteIdeleUpToExtension : ∀ {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (t : (Af K)ˣ), modF (upIdele K E t) = modF t ^ Module.finrank K E := by
  first | exact @GlobalTheory.UpIdeleMod.modF_upIdele | exact GlobalTheory.UpIdeleMod.modF_upIdele | (intros; apply GlobalTheory.UpIdeleMod.modF_upIdele <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds

theorem _root_.GlobalTheory.T.cuspForm_pullback_isBoundedSection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ), F ∈ M.SS la → ∀ (h : U) (c : C), (M.comp c).IsBddSec (castWt (M.comp_Ψ c) la) (fun x => M.pull h F c (castFrame (M.comp_Ψ c) x)) := by
  first | exact @GlobalTheory.PullBdd.pull_isBddSec | exact GlobalTheory.PullBdd.pull_isBddSec | (intros; apply GlobalTheory.PullBdd.pull_isBddSec <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.harishChandraProductCuspidalGL_frobenius_pow : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (t : F ≃+* F) (j : ℕ), (∀ x, t x = x ^ (ringChar F ^ j)) → ∀ (L : List (ℕ × ℕ)) (n : ℕ) (x : GL (Fin n) F), J θ L n (gal (t : F →+* F) n x) = J θ (L.map fun p => (p.1, p.2 * ringChar F ^ j)) n x := by
  first | (exact @GlobalTheory.Shin.J_gal) | (exact GlobalTheory.Shin.J_gal) | (intros; apply GlobalTheory.Shin.J_gal <;> assumption)
end
