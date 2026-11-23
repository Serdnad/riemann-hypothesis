module

public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOrthSucc
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle745
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle747
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle748
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle749
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle006
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport

@[expose] public section

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.LowGen

variable {p q : ℕ}

theorem mem_hwSub {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (μ : Ix p q → ℚ) (x : V) : x ∈ hwSub act μ ↔
      (∀ a, act (Eab a a) x = ((μ a : ℚ) : ℂ) • x) ∧ ∀ a b, posC a b → act (Eab a b) x = 0 := by
  simp [hwSub, wtSub, Submodule.mem_iInf, sub_eq_zero]

theorem genSub_stable {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (S : Set V) (Z : Mat p q) : ∀ y ∈ genSub act S, act Z y ∈ genSub act S := by
  intro y hy
  rw [genSub, Submodule.mem_sInf] at hy ⊢
  exact fun N hN => hN.2 Z y (hy N hN)

theorem mem_genSub_self {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (u : V) : u ∈ genSub act {u} := by
  rw [genSub, Submodule.mem_sInf]
  exact fun N hN => hN.1 rfl

theorem genSub_le {V : Type} [AddCommGroup V] [Module ℂ V] {act : Mat p q →ₗ[ℂ] Module.End ℂ V}
    {u : V} {N : Submodule ℂ V} (hu : u ∈ N) (hN : ∀ Z, ∀ y ∈ N, act Z y ∈ N) : genSub act {u} ≤ N :=
  sInf_le ⟨Set.singleton_subset_iff.2 hu, hN⟩

theorem gen_irred_adm {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (hlie : IsLieAct act) (ip : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (herm : ∀ x y, star (ip x y) = ip y x) (pos : ∀ x, x ≠ 0 → 0 < (ip x x).re)
    (hadj : ∀ Z x y, ip (act Z x) y = ip x (act (adjZ Z) y))
    {lam : Ix p q → ℚ} (hl : IsParam lam) (hg1 : GapGt lam (((p + q : ℕ) : ℝ) ^ 3 / 24 + 1))
    (hg2 : GapGt lam (((p + q : ℕ) : ℝ) - 1)) (u : V)
    (hfin : ∃ W : Submodule ℂ V, FiniteDimensional ℂ W ∧ u ∈ W ∧ KStable act W)
    (hu : u ∈ hwSub act (blattner lam))
    (hc : casimir act u = ((normSq lam - rhoSq (p + q) : ℚ) : ℂ) • u) :
    (∀ Q : Submodule ℂ V, Q ≤ genSub act {u} → (∀ Z, ∀ y ∈ Q, act Z y ∈ Q) → u ∉ Q → Q = ⊥) ∧
    ∀ μ, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ ∀ x ∈ genSub act {u}, x ∈ hwSub act μ → x ∈ S := by
  first
  | exact @_root_.GlobalTheory.FiltrationEquivalenceRelation.main
  | exact _root_.GlobalTheory.FiltrationEquivalenceRelation.main
  | (apply _root_.GlobalTheory.FiltrationEquivalenceRelation.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiltrationEquivalenceRelation.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiltrationEquivalenceRelation.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiltrationEquivalenceRelation.main ..)

def prodAct {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (a : Mat p q →ₗ[ℂ] Module.End ℂ V) (a' : Mat p q →ₗ[ℂ] Module.End ℂ V') :
    Mat p q →ₗ[ℂ] Module.End ℂ (V × V') where
  toFun Z := (a Z).prodMap (a' Z)
  map_add' Y Z := by ext <;> simp
  map_smul' c Z := by ext <;> simp

@[simp] theorem prodAct_apply {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (a : Mat p q →ₗ[ℂ] Module.End ℂ V) (a' : Mat p q →ₗ[ℂ] Module.End ℂ V') (Z : Mat p q) (x : V × V') :
    prodAct a a' Z x = (a Z x.1, a' Z x.2) := rfl

def prodForm {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (b' : V' →ₗ⋆[ℂ] V' →ₗ[ℂ] ℂ) : (V × V') →ₗ⋆[ℂ] (V × V') →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => b x.1 y.1 + b' x.2 y.2)
    (fun x y z => by simp; ring) (fun c x y => by simp; ring) (fun x y z => by simp; ring)
    (fun c x y => by simp; ring)

theorem prodForm_apply {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (b' : V' →ₗ⋆[ℂ] V' →ₗ[ℂ] ℂ) (x y : V × V') :
    prodForm b b' x y = b x.1 y.1 + b' x.2 y.2 := rfl

theorem ip_nonneg (M : UGKMod p q) (x : M.M.V) : 0 ≤ (M.ip x x).re := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (M.pos x hx).le

theorem diag_irred {lam : Ix p q → ℚ} (hl : IsParam lam) (hg1 : GapGt lam (((p + q : ℕ) : ℝ) ^ 3 / 24 + 1))
    (hg2 : GapGt lam (((p + q : ℕ) : ℝ) - 1)) (M M' : UGKMod p q) (u : M.M.V) (u' : M'.M.V)
    (hu : u ∈ hwSub M.M.act (blattner lam)) (hu' : u' ∈ hwSub M'.M.act (blattner lam))
    (hc : casimir M.M.act u = ((normSq lam - rhoSq (p + q) : ℚ) : ℂ) • u)
    (hc' : casimir M'.M.act u' = ((normSq lam - rhoSq (p + q) : ℚ) : ℂ) • u') :
    ∀ Q : Submodule ℂ (M.M.V × M'.M.V), Q ≤ genSub (prodAct M.M.act M'.M.act) {(u, u')} →
      (∀ Z, ∀ y ∈ Q, prodAct M.M.act M'.M.act Z y ∈ Q) → (u, u') ∉ Q → Q = ⊥ := by
  refine (gen_irred_adm (prodAct M.M.act M'.M.act) ?_ (prodForm M.ip M'.ip) ?_ ?_ ?_ hl hg1 hg2 (u, u')
    ?_ ?_ ?_).1
  · intro X Y
    refine LinearMap.ext fun x => ?_
    simp only [prodAct_apply, M.M.lie X Y, M'.M.lie X Y, LinearMap.sub_apply, Module.End.mul_apply]
    rfl
  · intro x y
    rw [prodForm_apply, prodForm_apply, star_add, M.herm, M'.herm]
  · intro x hx
    rw [prodForm_apply, Complex.add_re]
    have h1 := ip_nonneg M x.1
    have h2 := ip_nonneg M' x.2
    by_cases h : x.1 = 0
    · have := M'.pos x.2 fun h' => hx (Prod.ext h h')
      linarith
    · have := M.pos x.1 h
      linarith
  · intro Z x y
    simp only [prodForm_apply, prodAct_apply, M.adj, M'.adj]
  · obtain ⟨W, hW, huW, hst⟩ := M.M.kfin u
    obtain ⟨W', hW', huW', hst'⟩ := M'.M.kfin u'
    exact ⟨W.prod W', Module.Finite.of_fg (Submodule.FG.prod (Submodule.FG.of_finite) (Submodule.FG.of_finite)), ⟨huW, huW'⟩,
      fun X hX w hw => ⟨hst X hX _ hw.1, hst' X hX _ hw.2⟩⟩
  · rw [mem_hwSub] at hu hu' ⊢
    exact ⟨fun a => Prod.ext (hu.1 a) (hu'.1 a), fun a b h => Prod.ext (hu.2 a b h) (hu'.2 a b h)⟩
  · refine Prod.ext ?_ ?_
    · rw [Prod.smul_fst, ← hc]
      simp [casimir, Prod.fst_sum]
    · rw [Prod.smul_snd, ← hc']
      simp [casimir, Prod.snd_sum]

theorem gen_iso_of_lowest_type : admQ7 → admQ8 → ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → GapGt lam (((p + q : ℕ) : ℝ) ^ 3 / 24 + 1) → GapGt lam (((p + q : ℕ) : ℝ) - 1) → ∀ (M M' : UGKMod p q) (u : M.M.V) (u' : M'.M.V), IsHW M.M.act (blattner lam) u → IsHW M'.M.act (blattner lam) u' → casimir M.M.act u = ((normSq lam - rhoSq (p + q) : ℚ) : ℂ) • u → casimir M'.M.act u' = ((normSq lam - rhoSq (p + q) : ℚ) : ℂ) • u' → IrrGK M'.M → (∃ e : M'.M.V →ₗ[ℂ] M.M.V, Function.Injective e ∧ (∀ Z x, e (M'.M.act Z x) = M.M.act Z (e x)) ∧ e u' = u ∧ LinearMap.range e = genSub M.M.act {u}) ∧ AdmGK M'.M := by
  intro _ _ p q lam hl hg1 hg2 M M' u u' hu hu' hc hc' hirr
  constructor
  · set N := genSub (prodAct M.M.act M'.M.act) {(u, u')} with hN
    have hNs := genSub_stable (prodAct M.M.act M'.M.act) {(u, u')}
    have hw : (u, u') ∈ N := mem_genSub_self _ _
    let π : N →ₗ[ℂ] M'.M.V := LinearMap.snd ℂ _ _ ∘ₗ N.subtype
    have hinj : Function.Injective π := by
      have h := diag_irred hl hg1 hg2 M M' u u' hu.2 hu'.2 hc hc' (N ⊓ LinearMap.ker (LinearMap.snd ℂ _ _))
        inf_le_left (fun Z y hy => ⟨hNs Z y hy.1, by
          have h2 : y.2 = 0 := hy.2
          change M'.M.act Z y.2 = 0
          rw [h2, map_zero]⟩) (fun h => hu'.1 h.2)
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro x hx
      have : (x : M.M.V × M'.M.V) ∈ N ⊓ LinearMap.ker (LinearMap.snd ℂ _ _) := ⟨x.2, hx⟩
      rw [h] at this
      exact Subtype.ext this
    have hsurj : Function.Surjective π := by
      rcases hirr.2 (LinearMap.range π) (by
        rintro Z _ ⟨x, rfl⟩
        exact ⟨⟨_, hNs Z x x.2⟩, rfl⟩) with h | h
      · have : u' ∈ LinearMap.range π := ⟨⟨_, hw⟩, rfl⟩
        rw [h] at this
        exact absurd this hu'.1
      · exact LinearMap.range_eq_top.1 h
    let φ := LinearEquiv.ofBijective π ⟨hinj, hsurj⟩
    let e : M'.M.V →ₗ[ℂ] M.M.V := (LinearMap.fst ℂ _ _ ∘ₗ N.subtype) ∘ₗ φ.symm.toLinearMap
    have he : ∀ x : N, e (x : M.M.V × M'.M.V).2 = (x : M.M.V × M'.M.V).1 := fun x =>
      congrArg (fun y : N => (y : M.M.V × M'.M.V).1) (φ.symm_apply_apply x)
    have heZ : ∀ Z x, e (M'.M.act Z x) = M.M.act Z (e x) := by
      intro Z x
      obtain ⟨y, rfl⟩ := hsurj x
      have h1 := he ⟨_, hNs Z y y.2⟩
      have h2 := he y
      exact h1.trans (congrArg (M.M.act Z) h2.symm)
    have heu : e u' = u := he ⟨_, hw⟩
    refine ⟨e, ?_, heZ, heu, le_antisymm ?_ (genSub_le ⟨u', heu⟩ ?_)⟩
    · rcases hirr.2 (LinearMap.ker e) (fun Z y hy => by
        rw [LinearMap.mem_ker] at hy ⊢
        rw [heZ, hy, map_zero]) with h | h
      · exact LinearMap.ker_eq_bot.1 h
      · have : u' ∈ LinearMap.ker e := h ▸ Submodule.mem_top
        rw [LinearMap.mem_ker, heu] at this
        exact absurd this hu.1
    · rintro _ ⟨x, rfl⟩
      obtain ⟨y, rfl⟩ := hsurj x
      have h1 : N ≤ (genSub M.M.act {u}).comap (LinearMap.fst ℂ _ _) :=
        genSub_le (mem_genSub_self _ u) fun Z z hz => genSub_stable _ _ Z _ hz
      exact (he y).symm ▸ h1 y.2
    · rintro Z _ ⟨x, rfl⟩
      exact ⟨_, heZ Z x⟩
  · intro μ
    obtain ⟨S, hS, hS'⟩ := (gen_irred_adm M'.M.act M'.M.lie M'.ip M'.herm M'.pos M'.adj hl hg1 hg2 u'
      (M'.M.kfin u') hu'.2 hc').2 μ
    have htop : genSub M'.M.act {u'} = ⊤ := by
      rcases hirr.2 _ (genSub_stable M'.M.act {u'}) with h | h
      · have := mem_genSub_self M'.M.act u'
        rw [h] at this
        exact absurd this hu'.1
      · exact h
    exact Submodule.finiteDimensional_of_le (S₂ := S) fun x hx => hS' x (htop ▸ Submodule.mem_top) hx

end GlobalTheory.LowGen
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory

theorem submodule_eq_top_of_sup_maximal_smul_eq_top :
    ∀ (R : Type) [CommRing R] (N : Type) [AddCommGroup N] [Module R N] [Module.Finite R N]
      (M : Submodule R N), (∀ m : Ideal R, m.IsMaximal → M ⊔ m • ⊤ = ⊤) → M = ⊤ := by
  intro R _ N _ _ _ M h

  have hQ : ∀ m : Ideal R, m.IsMaximal → (⊤ : Submodule R (N ⧸ M)) ≤ m • ⊤ := by
    intro m hm
    have h1 := congrArg (Submodule.map M.mkQ) (h m hm)
    rw [Submodule.map_sup, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at h1
    have h2 : Submodule.map M.mkQ M = ⊥ := Submodule.mkQ_map_self M
    rw [h2, bot_sup_eq] at h1
    rw [h1]
  have hfg : (⊤ : Submodule R (N ⧸ M)).FG := Module.Finite.fg_top
  have hann : Module.annihilator R (N ⧸ M) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr1, hr⟩ :=
      Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m ⊤ hfg (hQ m hm)
    have hrm : r ∈ m := hle (Module.mem_annihilator.mpr fun q => hr q Submodule.mem_top)
    have : (1 : R) ∈ m := by
      have := m.sub_mem hrm hr1
      simpa using this
    exact hm.ne_top ((Ideal.eq_top_iff_one m).mpr this)
  rw [eq_top_iff]
  intro n _
  have h1 : (1 : R) ∈ Module.annihilator R (N ⧸ M) := hann ▸ Submodule.mem_top
  have h0 : (Submodule.Quotient.mk n : N ⧸ M) = 0 := by
    simpa using Module.mem_annihilator.mp h1 (Submodule.Quotient.mk n)
  exact (Submodule.Quotient.mk_eq_zero M).mp h0

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

theorem _root_.GlobalTheory.T.finrank_range_mulLeft_idempotent_groupAlgebra : ∀ (K H : Type) [Field K] [CharZero K] [Group H] [Finite H] (a : MonoidAlgebra K H), a * a = a → ((finrank K (LinearMap.range (LinearMap.mulLeft K a)) : ℕ) : K) = (Nat.card H : K) * a.coeff 1 := by
  first | exact @GlobalTheory.BadCount.finrank_range_mulLeft_idem | exact GlobalTheory.BadCount.finrank_range_mulLeft_idem | (intros; apply GlobalTheory.BadCount.finrank_range_mulLeft_idem <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.closed_subfunctor_stalk_ideal_criterion : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (H : Over (Sp K)) [GrpObj H] (j : H ⟶ A), IsMonHom j → IsClosedImmersion j.left → IsFinite H.hom → ∀ x₀ : A.left, x₀ ∈ Set.range (η[A]).left.base → ∀ J : Ideal (A.left.presheaf.stalk x₀), (∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'), (∃ y : Sp R' ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) ↔ J ≤ RingHom.ker ψ) → J ≠ ⊤ ∧ IsArtinianRing (A.left.presheaf.stalk x₀ ⧸ J) := by
  first | exact @GlobalTheory.FinStalk.stalk_quotient_ne_top_and_isArtinianRing | exact GlobalTheory.FinStalk.stalk_quotient_ne_top_and_isArtinianRing | (intros; apply GlobalTheory.FinStalk.stalk_quotient_ne_top_and_isArtinianRing <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem _root_.GlobalTheory.T.hilbert_scheme_finite_free_algebra_affine_exists : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B] (r : ℕ), ∃ (H : Scheme.{0}) (h : H ⟶ Spec (CommRingCat.of A)) (U : Scheme.{0}) (u : U ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) h), IsProper h ∧ IsClosedImmersion u ∧ IsFinite (u ≫ pullback.snd _ h) ∧ Flat (u ≫ pullback.snd _ h) ∧ (∀ y, (u ≫ pullback.snd _ h).finrank y = r) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Spec (CommRingCat.of A)) (V : Scheme.{0}) (v : V ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) g), IsClosedImmersion v → IsFinite (v ≫ pullback.snd _ g) → Flat (v ≫ pullback.snd _ g) → (∀ y, (v ≫ pullback.snd _ g).finrank y = r) → ∃! f : T ⟶ H, ∃ hf : f ≫ h = g, ∃ w : V ⟶ U, IsPullback v w (pullback.map _ g _ h (𝟙 _) f (𝟙 _) (by simp) (by rw [Category.comp_id, hf])) u := by
  first | (exact @GlobalTheory.HilbAff.hilbertScheme_exists) | (exact GlobalTheory.HilbAff.hilbertScheme_exists) | (intros; apply GlobalTheory.HilbAff.hilbertScheme_exists <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory

theorem exists_desc_of_flat_of_schemeTheoreticallyDominant :
    ∀ {S S' U U' X Y Y' YU Y'' : Scheme.{0}} (f : S' ⟶ S) (j : U ⟶ S) (f' : U' ⟶ U) (j' : U' ⟶ S')
      [Flat f] [Surjective f] [QuasiCompact f] [QuasiCompact j] [IsSchemeTheoreticallyDominant j],
      IsPullback j' f' f j → ∀ (x : X ⟶ S) [IsSeparated x] (y : Y ⟶ S) [Flat y] (y' : Y' ⟶ S')
      (π : Y' ⟶ Y), IsPullback π y' y f → ∀ (yU : YU ⟶ U) (ιY : YU ⟶ Y), IsPullback ιY yU y j →
      ∀ (y'' : Y'' ⟶ U') (c : Y'' ⟶ Y') (cU : Y'' ⟶ YU), IsPullback c y'' y' j' →
      IsPullback cU y'' yU f' → cU ≫ ιY = c ≫ π → ∀ (h' : Y' ⟶ X) (hU : YU ⟶ X),
      h' ≫ x = y' ≫ f → c ≫ h' = cU ≫ hU → ∃ h : Y ⟶ X, π ≫ h = h' ∧ ιY ≫ h = hU ∧ h ≫ x = y := by
  intro S S' U U' X Y Y' YU Y'' f j f' j' _ _ _ _ _ hUsq x _ y _ y' π hπ yU ιY hι y'' c cU hc hcU
    hcomm h' hU hx hagree
  have : Flat π := MorphismProperty.of_isPullback (P := @Flat) hπ.flip ‹_›
  have : Surjective π := MorphismProperty.of_isPullback (P := @Surjective) hπ.flip ‹_›
  have : QuasiCompact π := MorphismProperty.of_isPullback (P := @QuasiCompact) hπ.flip ‹_›
  have : Flat f' := MorphismProperty.of_isPullback (P := @Flat) hUsq ‹_›
  have : Surjective f' := MorphismProperty.of_isPullback (P := @Surjective) hUsq ‹_›
  have : Flat cU := MorphismProperty.of_isPullback (P := @Flat) hcU.flip ‹_›
  have : Surjective cU := MorphismProperty.of_isPullback (P := @Surjective) hcU.flip ‹_›
  have : Epi cU := Flat.epi_of_flat_of_surjective cU

  have key : ∀ {T : Scheme.{0}} (a : T ⟶ Y') (ψ : T ⟶ U) (w : (a ≫ π) ≫ y = ψ ≫ j),
      a ≫ h' = hι.lift (a ≫ π) ψ w ≫ hU := by
    intro T a ψ w
    have w1 : (a ≫ y') ≫ f = ψ ≫ j := by
      rw [Category.assoc, ← hπ.w, ← Category.assoc, w]
    let u : T ⟶ U' := hUsq.lift (a ≫ y') ψ w1
    have w2 : a ≫ y' = u ≫ j' := (hUsq.lift_fst _ _ _).symm
    let q : T ⟶ Y'' := hc.lift a u w2
    have hq : q ≫ cU = hι.lift (a ≫ π) ψ w := by
      apply hι.hom_ext
      · rw [Category.assoc, hcomm, ← Category.assoc, hc.lift_fst, hι.lift_fst]
      · rw [Category.assoc, hcU.w, ← Category.assoc, hc.lift_snd, hι.lift_snd, hUsq.lift_snd]
    calc a ≫ h' = q ≫ c ≫ h' := by rw [← Category.assoc, hc.lift_fst]
      _ = q ≫ cU ≫ hU := by rw [hagree]
      _ = _ := by rw [← Category.assoc, hq]

  have hP : pullback.fst π π ≫ h' = pullback.snd π π ≫ h' := by
    let g : pullback π π ⟶ S := pullback.fst π π ≫ π ≫ y
    have : Flat g := by dsimp [g]; infer_instance
    let φ : pullback g j ⟶ pullback π π := pullback.fst g j
    have : IsSchemeTheoreticallyDominant φ := IsSchemeTheoreticallyDominant.pullbackFst g j
    refine ExtUnique.hom_ext_of_dominant x ?_ φ ?_
    · simp only [Category.assoc, hx]
      rw [← hπ.w, pullback.condition_assoc]
    · have e1 : ((φ ≫ pullback.fst π π) ≫ π) ≫ y = pullback.snd g j ≫ j := by
        simpa [g, Category.assoc] using pullback.condition (f := g) (g := j)
      have e2 : ((φ ≫ pullback.snd π π) ≫ π) ≫ y = pullback.snd g j ≫ j := by
        rw [Category.assoc φ, ← pullback.condition]; exact e1
      have l : hι.lift ((φ ≫ pullback.fst π π) ≫ π) (pullback.snd g j) e1 =
          hι.lift ((φ ≫ pullback.snd π π) ≫ π) (pullback.snd g j) e2 := by
        congr 1; rw [Category.assoc, Category.assoc, pullback.condition]
      rw [← Category.assoc, ← Category.assoc, key _ _ e1, key _ _ e2, l]
  have H : ∀ {Z : Scheme.{0}} (a b : Z ⟶ Y'), a ≫ π = b ≫ π → a ≫ h' = b ≫ h' := by
    intro Z a b hab
    calc a ≫ h' = pullback.lift a b hab ≫ pullback.fst π π ≫ h' := by rw [pullback.lift_fst_assoc]
      _ = pullback.lift a b hab ≫ pullback.snd π π ≫ h' := by rw [hP]
      _ = b ≫ h' := by rw [pullback.lift_snd_assoc]
  let h : Y ⟶ X := EffectiveEpi.desc π h' H
  have h1 : π ≫ h = h' := EffectiveEpi.fac π h' H
  refine ⟨h, h1, ?_, ?_⟩
  · apply (cancel_epi cU).1
    rw [← Category.assoc, hcomm, Category.assoc, h1, hagree]
  · apply (cancel_epi π).1
    rw [← Category.assoc, h1, hx, hπ.w]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem sectionComponents_preimage_of_isPullback :
    ∀ (X S X' S' : Scheme.{0}) (f : X ⟶ S) (f' : X' ⟶ S') (p : S' ⟶ S) (q : X' ⟶ X)
      (e : S ⟶ X) (e' : S' ⟶ X'), Smooth f → IsPullback q f' f p → e ≫ f = 𝟙 _ →
      e' ≫ f' = 𝟙 _ → e' ≫ q = p ≫ e →
      q ⁻¹' {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} =
        {x : X' | x ∈ connectedComponentIn (f' ⁻¹' {f' x}) (e' (f' x))} := by
  intro X S X' S' f f' p q e e' hf hq he he' hee
  ext x'
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  have hfq : f (q x') = p (f' x') := by
    rw [← Scheme.Hom.comp_apply, hq.w, Scheme.Hom.comp_apply]
  rw [hfq]

  have hY := IsPullback.of_hasPullback f (S.fromSpecResidueField (p (f' x')))
  have hY' := IsPullback.of_hasPullback f' (S'.fromSpecResidueField (f' x'))
  have hsq : S'.fromSpecResidueField (f' x') ≫ p =
      Spec.map (p.residueFieldMap (f' x')) ≫ S.fromSpecResidueField (p (f' x')) :=
    (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField p (f' x')).symm

  let eY : Spec (S.residueField (p (f' x'))) ⟶ pullback f (S.fromSpecResidueField (p (f' x'))) :=
    pullback.lift (S.fromSpecResidueField (p (f' x')) ≫ e) (𝟙 _) (by simp [he])
  let eY' : Spec (S'.residueField (f' x')) ⟶ pullback f' (S'.fromSpecResidueField (f' x')) :=
    pullback.lift (S'.fromSpecResidueField (f' x') ≫ e') (𝟙 _) (by simp [he'])

  let r : pullback f' (S'.fromSpecResidueField (f' x')) ⟶
      pullback f (S.fromSpecResidueField (p (f' x'))) :=
    pullback.lift (pullback.fst _ _ ≫ q) (pullback.snd _ _ ≫ Spec.map (p.residueFieldMap (f' x')))
      (by simp only [Category.assoc]; rw [hq.w, ← Category.assoc, pullback.condition, Category.assoc, hsq])
  have hbig := hY'.paste_horiz hq
  have hr : IsPullback r (pullback.snd _ _) (pullback.snd _ _)
      (Spec.map (p.residueFieldMap (f' x'))) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) hY
    have h1 : r ≫ pullback.fst _ _ = pullback.fst _ _ ≫ q := pullback.lift_fst _ _ _
    rw [h1, ← hsq]
    exact hbig
  have hsec : eY ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
  have hsec' : eY' ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
  have hcomm : eY' ≫ r = Spec.map (p.residueFieldMap (f' x')) ≫ eY := by
    apply pullback.hom_ext
    · simp only [r, eY, eY', Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      rw [hee, reassoc_of% hsq]
    · simp only [r, eY, eY', Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.id_comp, Category.comp_id]
  have hsm : Smooth (pullback.snd f (S.fromSpecResidueField (p (f' x')))) := inferInstance
  have key := GlobalTheory.T.preimage_connectedComponent_rationalPoint_fieldExt (S.residueField (p (f' x'))) (S'.residueField (f' x')) _ _
    (pullback.snd _ _) (pullback.snd _ _) (Spec.map (p.residueFieldMap (f' x'))) r eY eY'
    hsm hr hsec hsec' hcomm

  obtain ⟨y', hy'1, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f') (g := S'.fromSpecResidueField (f' x')) x' (IsLocalRing.closedPoint _)
    (Scheme.fromSpecResidueField_apply _ _).symm
  have hy₀ : pullback.fst f (S.fromSpecResidueField (p (f' x'))) (eY (IsLocalRing.closedPoint _)) =
      e (p (f' x')) := by
    have h1 : eY ≫ pullback.fst _ _ = S.fromSpecResidueField (p (f' x')) ≫ e := pullback.lift_fst _ _ _
    refine (Scheme.Hom.comp_apply eY (pullback.fst _ _) _).symm.trans ?_
    rw [h1]
    exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg e (Scheme.fromSpecResidueField_apply _ _))
  have hy₀' : pullback.fst f' (S'.fromSpecResidueField (f' x')) (eY' (IsLocalRing.closedPoint _)) =
      e' (f' x') := by
    have h1 : eY' ≫ pullback.fst _ _ = S'.fromSpecResidueField (f' x') ≫ e' := pullback.lift_fst _ _ _
    refine (Scheme.Hom.comp_apply eY' (pullback.fst _ _) _).symm.trans ?_
    rw [h1]
    exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg e' (Scheme.fromSpecResidueField_apply _ _))
  have hqx : pullback.fst f (S.fromSpecResidueField (p (f' x'))) (r y') = q x' := by
    have h1 : r ≫ pullback.fst _ _ = pullback.fst _ _ ≫ q := pullback.lift_fst _ _ _
    refine (Scheme.Hom.comp_apply r (pullback.fst _ _) _).symm.trans ?_
    rw [h1, Scheme.Hom.comp_apply, hy'1]
  have A := GlobalTheory.T.mem_connectedComponentIn_fibre_iff_of_isPullback X S f e (p (f' x')) _ (pullback.snd _ _) (pullback.fst _ _) _ hY hy₀ (r y')
  have B := GlobalTheory.T.mem_connectedComponentIn_fibre_iff_of_isPullback X' S' f' e' (f' x') _ (pullback.snd _ _) (pullback.fst _ _) _ hY' hy₀' y'
  rw [hqx] at A
  rw [hy'1] at B
  rw [A, B, ← key]
  rfl

end GlobalTheory
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.quadraticField_exists_sqrt_neg_discr : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (h2 : Module.finrank ℚ K = 2) (hd : discr K = -(d : ℤ)), ∃ δ : K, δ ^ 2 = -(d : K) := by
  first | exact @GlobalTheory.exists_sq_eq_neg_of_discr_eq_neg | exact GlobalTheory.exists_sq_eq_neg_of_discr_eq_neg | (intros; apply GlobalTheory.exists_sq_eq_neg_of_discr_eq_neg <;> assumption)
end
