module

public import Development.EtaleCohomology.TateTwists.Bundle012
public import Development.EtaleCohomology.TateTwists.Bundle013
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Development.EtaleCohomology.KummerTheory.CupAWCutEv
public import Development.EtaleCohomology.TateTwists.Bundle017
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleAlexanderWhitneyCupCochainExistsForPairing : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m),
    ∃ γ : Cochain ((chains R).obj E) K k, μ.IsAW hk α β γ

def EtaleAlexanderWhitneyCupUniqueBiadditive : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k),
    (∀ (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ γ' : Cochain ((chains R).obj E) K k),
      μ.IsAW hk α β γ → μ.IsAW hk α β γ' → γ = γ') ∧
    (∀ (α α' : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ γ' : Cochain ((chains R).obj E) K k),
      μ.IsAW hk α β γ → μ.IsAW hk α' β γ' → μ.IsAW hk (α + α') β (γ + γ')) ∧
    (∀ (α : Cochain ((chains R).obj E) I n) (β β' : Cochain ((chains R).obj E) J m) (γ γ' : Cochain ((chains R).obj E) K k),
      μ.IsAW hk α β γ → μ.IsAW hk α β' γ' → μ.IsAW hk α (β + β') (γ + γ')) ∧
    (∀ (β : Cochain ((chains R).obj E) J m), μ.IsAW hk 0 β 0) ∧
    (∀ (α : Cochain ((chains R).obj E) I n), μ.IsAW hk α 0 0)

def EtaleAlexanderWhitneyCupLeibnizRule : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k n₁ m₁ k₁ : ℤ} (hk : n + m = k)
    (hn : n + 1 = n₁) (hm : m + 1 = m₁) (hk₁ : n₁ + m = k₁) (hk₂ : n + m₁ = k₁)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K k) (γ₁ γ₂ : Cochain ((chains R).obj E) K k₁),
    μ.IsAW hk α β γ → μ.IsAW hk₁ (δ n n₁ α) β γ₁ → μ.IsAW hk₂ α (δ m m₁ β) γ₂ → δ k k₁ γ = γ₁ + n.negOnePow • γ₂

theorem ev_add' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x := by
  unfold ev
  rw [Cochain.add_v, Preadditive.comp_add]
  rfl

theorem ev_zero' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by
  unfold ev
  rw [Cochain.zero_v, Limits.comp_zero]
  rfl

def EtaleAlexanderWhitneyCupCochainUnique : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ γ' : Cochain ((chains R).obj E) K k),
      μ.IsAW hk α β γ → μ.IsAW hk α β γ' → γ = γ'

theorem awalg_of (hu : EtaleAlexanderWhitneyCupCochainUnique) : EtaleAlexanderWhitneyCupUniqueBiadditive := by
  intro R _ I J K μ E n m k hk
  refine ⟨hu R μ hk, ?_, ?_, ?_, ?_⟩
  · intro α α' β γ γ' h h' N w hw U x
    rw [ev_add', h, h', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [ev_add', map_add (f := _), LinearMap.add_apply, smul_add]
  · intro α β β' γ γ' h h' N w hw U x
    rw [ev_add', h, h', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [ev_add', map_add (f := _), smul_add]
  · intro β N w hw U x
    rw [ev_zero']
    symm
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [ev_zero', map_zero, LinearMap.zero_apply, smul_zero]
  · intro α N w hw U x
    rw [ev_zero']
    symm
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [ev_zero', map_zero, smul_zero]

theorem cup_spec_part1 (h1 : EtaleAlexanderWhitneyCupCochainExistsForPairing) (h2 : EtaleAlexanderWhitneyCupUniqueBiadditive) (h3 : EtaleAlexanderWhitneyCupLeibnizRule)
    (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) :
    ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1 := by
  obtain ⟨γ, hγ⟩ := h1 R μ hk α.1 β.1
  obtain ⟨γ₁, hγ₁⟩ := h1 R μ (show (n + 1) + m = k + 1 by omega) (δ n (n + 1) α.1) β.1
  obtain ⟨γ₂, hγ₂⟩ := h1 R μ (show n + (m + 1) = k + 1 by omega) α.1 (δ m (m + 1) β.1)
  have hd := h3 R μ hk rfl rfl _ _ α.1 β.1 γ γ₁ γ₂ hγ hγ₁ hγ₂
  rw [Cocycle.δ_eq_zero] at hγ₁
  rw [Cocycle.δ_eq_zero] at hγ₂
  have e1 : γ₁ = 0 := (h2 R μ _).1 _ _ _ _ hγ₁ ((h2 R μ _).2.2.2.1 _)
  have e2 : γ₂ = 0 := (h2 R μ _).1 _ _ _ _ hγ₂ ((h2 R μ _).2.2.2.2 _)
  rw [e1, e2, smul_zero, add_zero] at hd
  exact ⟨Cocycle.mk γ (k + 1) rfl hd, hγ⟩

def EtaleAlexanderWhitneyCupDescendsToCohomology : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k),
    ∃ c : CohomologyClass ((chains R).obj E) I n →+ CohomologyClass ((chains R).obj E) J m →+
        CohomologyClass ((chains R).obj E) K k,
      ∀ (α : Cocycle _ I n) (β : Cocycle _ J m) (γ : Cocycle _ K k), μ.IsAW hk α.1 β.1 γ.1 →
        c (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ

section Desc
variable (h1 : EtaleAlexanderWhitneyCupCochainExistsForPairing) (h2 : EtaleAlexanderWhitneyCupUniqueBiadditive) (h3 : EtaleAlexanderWhitneyCupLeibnizRule)
  {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)

noncomputable def chZ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) :
    Cocycle ((chains R).obj E) K k :=
  Classical.choose (cup_spec_part1 h1 h2 h3 R μ hk α β)

theorem chZ_spec (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) :
    μ.IsAW hk α.1 β.1 (chZ h1 h2 h3 μ E hk α β).1 :=
  Classical.choose_spec (cup_spec_part1 h1 h2 h3 R μ hk α β)

theorem chZ_eq (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (γ : Cocycle ((chains R).obj E) K k) (h : μ.IsAW hk α.1 β.1 γ.1) : chZ h1 h2 h3 μ E hk α β = γ :=
  Cocycle.ext ((h2 R μ hk).1 _ _ _ _ (chZ_spec h1 h2 h3 μ E hk α β) h)

theorem chZ_add_left (α α' : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) :
    chZ h1 h2 h3 μ E hk (α + α') β = chZ h1 h2 h3 μ E hk α β + chZ h1 h2 h3 μ E hk α' β :=
  chZ_eq h1 h2 h3 μ E hk _ _ _ ((h2 R μ hk).2.1 _ _ _ _ _ (chZ_spec h1 h2 h3 μ E hk α β) (chZ_spec h1 h2 h3 μ E hk α' β))

theorem chZ_add_right (α : Cocycle ((chains R).obj E) I n) (β β' : Cocycle ((chains R).obj E) J m) :
    chZ h1 h2 h3 μ E hk α (β + β') = chZ h1 h2 h3 μ E hk α β + chZ h1 h2 h3 μ E hk α β' :=
  chZ_eq h1 h2 h3 μ E hk _ _ _ ((h2 R μ hk).2.2.1 _ _ _ _ _ (chZ_spec h1 h2 h3 μ E hk α β) (chZ_spec h1 h2 h3 μ E hk α β'))

theorem chZ_cob_left (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (hα : α ∈ coboundaries _ _ n) : chZ h1 h2 h3 μ E hk α β ∈ coboundaries _ _ k := by
  obtain ⟨m', hm', η, hη⟩ := hα
  obtain ⟨γ, hγ⟩ := h1 R μ (show m' + m = m' + m from rfl) η β.1
  obtain ⟨γ₂, hγ₂⟩ := h1 R μ (show m' + (m + 1) = k by omega) η (δ m (m + 1) β.1)
  have hd := h3 R μ rfl hm' rfl (show n + m = k from hk) (show m' + (m + 1) = k by omega) η β.1 γ
    (chZ h1 h2 h3 μ E hk α β).1 γ₂ hγ (by rw [hη]; exact chZ_spec h1 h2 h3 μ E hk α β) hγ₂
  rw [Cocycle.δ_eq_zero] at hγ₂
  have e2 : γ₂ = 0 := (h2 R μ _).1 _ _ _ _ hγ₂ ((h2 R μ _).2.2.2.2 _)
  rw [e2, smul_zero, add_zero] at hd
  exact ⟨m' + m, by omega, γ, hd⟩

theorem chZ_cob_right (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (hβ : β ∈ coboundaries _ _ m) : chZ h1 h2 h3 μ E hk α β ∈ coboundaries _ _ k := by
  obtain ⟨m', hm', θ, hθ⟩ := hβ
  obtain ⟨γ, hγ⟩ := h1 R μ (show n + m' = n + m' from rfl) α.1 θ
  obtain ⟨γ₁, hγ₁⟩ := h1 R μ (show (n + 1) + m' = k by omega) (δ n (n + 1) α.1) θ
  have hd := h3 R μ rfl rfl hm' (show (n + 1) + m' = k by omega) (show n + m = k from hk) α.1 θ γ
    γ₁ (chZ h1 h2 h3 μ E hk α β).1 hγ hγ₁ (by rw [hθ]; exact chZ_spec h1 h2 h3 μ E hk α β)
  rw [Cocycle.δ_eq_zero] at hγ₁
  have e1 : γ₁ = 0 := (h2 R μ _).1 _ _ _ _ hγ₁ ((h2 R μ _).2.2.2.1 _)
  rw [e1, zero_add] at hd
  refine ⟨n + m', by omega, n.negOnePow • γ, ?_⟩
  rw [δ_units_smul, hd, smul_smul, Int.units_mul_self, one_smul]

end Desc

theorem desc_of (h1 : EtaleAlexanderWhitneyCupCochainExistsForPairing) (h2 : EtaleAlexanderWhitneyCupUniqueBiadditive) (h3 : EtaleAlexanderWhitneyCupLeibnizRule) :
    EtaleAlexanderWhitneyCupDescendsToCohomology := by
  intro R _ I J K μ E n m k hk
  let G : Cocycle ((chains R).obj E) I n → (CohomologyClass ((chains R).obj E) J m →+ CohomologyClass ((chains R).obj E) K k) :=
    fun α => QuotientAddGroup.lift _
      (AddMonoidHom.mk' (fun β => CohomologyClass.mk (chZ h1 h2 h3 μ E hk α β))
        (fun β β' => by rw [chZ_add_right, CohomologyClass.mk_add]))
      (fun β hβ => by
        simp only [AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply]
        exact (QuotientAddGroup.eq_zero_iff _).2 (chZ_cob_right h1 h2 h3 μ E hk α β hβ))
  let F : Cocycle ((chains R).obj E) I n →+ (CohomologyClass ((chains R).obj E) J m →+ CohomologyClass ((chains R).obj E) K k) :=
    AddMonoidHom.mk' G (fun α α' => by
      refine QuotientAddGroup.addMonoidHom_ext _ (AddMonoidHom.ext fun β => ?_)
      show CohomologyClass.mk _ = CohomologyClass.mk _ + CohomologyClass.mk _
      rw [chZ_add_left, CohomologyClass.mk_add])
  refine ⟨QuotientAddGroup.lift _ F (fun α hα => ?_), ?_⟩
  · rw [AddMonoidHom.mem_ker]
    refine QuotientAddGroup.addMonoidHom_ext _ (AddMonoidHom.ext fun β => ?_)
    show CohomologyClass.mk _ = 0
    exact (QuotientAddGroup.eq_zero_iff _).2 (chZ_cob_left h1 h2 h3 μ E hk α β hα)
  · intro α β γ hγ
    show CohomologyClass.mk _ = _
    rw [chZ_eq h1 h2 h3 μ E hk α β γ hγ]

theorem etale_cup_compat_spec_of_alexander_whitney_exists_unique_leibniz (h1 : EtaleAlexanderWhitneyCupCochainExistsForPairing) (hu : EtaleAlexanderWhitneyCupCochainUnique)
    (h3 : EtaleAlexanderWhitneyCupLeibnizRule) : EtaleCupCompatAlexanderWhitneyCocycleSpec := by
  have h2 := awalg_of hu
  have h4 := desc_of h1 h2 h3
  intro R _ I J K μ E n m k hk
  refine ⟨fun α β => cup_spec_part1 h1 h2 h3 R μ hk α β, ?_⟩
  intro α β γ hγ
  exact pick_spec (h4 R μ E hk) α β γ hγ
end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct DirectSum

noncomputable section

namespace LateralTheory.EtaleFoundations

section
variable {R : Type} [CommRing R]

lemma sec_map_res {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.map f (Sec.res g a) = Sec.res g (Sec.map f a) := by
  change ((F.obj.map g.op ≫ f.hom.app (op V)).hom a) = ((f.hom.app (op U) ≫ G.obj.map g.op).hom a)
  rw [f.hom.naturality]

lemma sec_map_dd (I : Cx R) (i j k : ℤ) {U : Scheme.{0}} (a : Sec (I.X i) U) :
    Sec.map (I.d j k) (Sec.map (I.d i j) a) = 0 := by
  change ((I.d i j ≫ I.d j k).hom.app (op U)).hom a = 0
  rw [HomologicalComplex.d_comp_d]; rfl

def etaleTensorPresheafOfComplexes (I J : Cx R) (w : ℤ) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of _ (Tens I J U.unop w)
  map g := ModuleCat.ofHom (Tens.res g.unop w)
  map_id U := by
    ext1; apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
    simp [Tens.res]
  map_comp f g := by
    ext1; apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
    simp [Tens.res]

def dB (I J : Cx R) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w}) :
    Sec (I.X p.1.1) U →ₗ[ULift.{1} R] Sec (J.X p.1.2) U →ₗ[ULift.{1} R] Tens I J U (w + 1) :=
  ((TensorProduct.mk (ULift.{1} R) _ _).compr₂ (DirectSum.lof (ULift.{1} R) {p : ℤ × ℤ // p.1 + p.2 = w + 1}
      (fun p => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(p.1.1 + 1, p.1.2), by have := p.2; omega⟩)).compl₁₂
      ((I.d p.1.1 (p.1.1 + 1)).hom.app (op U)).hom LinearMap.id +
  ((p.1.1.negOnePow : ℤ) • ((TensorProduct.mk (ULift.{1} R) _ _).compr₂ (DirectSum.lof (ULift.{1} R) {p : ℤ × ℤ // p.1 + p.2 = w + 1}
      (fun p => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(p.1.1, p.1.2 + 1), by have := p.2; omega⟩)).compl₁₂
      LinearMap.id ((J.d p.1.2 (p.1.2 + 1)).hom.app (op U)).hom)

def dT (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens I J U (w + 1) :=
  DirectSum.toModule _ _ _ fun p => TensorProduct.lift (dB I J U w p)

lemma dT_pure (I J : Cx R) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    dT I J U w (tensPure s t w h a b) =
      tensPure (s + 1) t (w + 1) (by omega) (Sec.map (I.d s (s + 1)) a) b +
      s.negOnePow • tensPure s (t + 1) (w + 1) (by omega) a (Sec.map (J.d t (t + 1)) b) := by
  simp [dT, tensPure, dB, DirectSum.toModule_lof, Units.smul_def, Sec.map]

lemma tensPure_res (I J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (s t w : ℤ) (h : s + t = w)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    Tens.res g w (tensPure s t w h a b) = tensPure s t w h (Sec.res g a) (Sec.res g b) := by
  simp [Tens.res, tensPure, Sec.res]

lemma tens_ext {I J : Cx R} {U : Scheme.{0}} {w : ℤ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} R) M]
    {f g : Tens I J U w →ₗ[ULift.{1} R] M}
    (H : ∀ s t (h : s + t = w) a b, f (tensPure s t w h a b) = g (tensPure s t w h a b)) : f = g := by
  apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
  exact H p.1.1 p.1.2 p.2 a b

def dP (I J : Cx R) (w : ℤ) : etaleTensorPresheafOfComplexes I J w ⟶ etaleTensorPresheafOfComplexes I J (w + 1) where
  app U := ModuleCat.ofHom (dT I J U.unop w)
  naturality V U g := by
    ext1
    refine tens_ext fun s t h a b => ?_
    change dT I J U.unop w (Tens.res g.unop w (tensPure s t w h a b)) =
      Tens.res g.unop (w + 1) (dT I J V.unop w (tensPure s t w h a b))
    simp only [tensPure_res, dT_pure, map_add (f := _), Units.smul_def, map_zsmul, sec_map_res]

lemma tensPure_zero_left (I J : Cx R) {U : Scheme.{0}} (s t w : ℤ) (h : s + t = w) (b : Sec (J.X t) U) :
    tensPure (I := I) s t w h 0 b = 0 := by simp [tensPure]

lemma tensPure_zero_right (I J : Cx R) {U : Scheme.{0}} (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) :
    tensPure (J := J) s t w h a 0 = 0 := by simp [tensPure]

lemma tensorDifferential_comp_tensorDifferential (I J : Cx R) (w : ℤ) : dP I J w ≫ dP I J (w + 1) = 0 := by
  apply NatTrans.ext; funext U; apply ModuleCat.hom_ext
  refine tens_ext (M := Tens I J U.unop (w + 1 + 1)) fun s t h a b => ?_
  change dT I J U.unop (w + 1) (dT I J U.unop w (tensPure s t w h a b)) = 0
  simp only [dT_pure, map_add (f := _), Units.smul_def, map_zsmul, sec_map_dd, tensPure_zero_left, tensPure_zero_right,
    smul_zero, zero_add, add_zero, Int.negOnePow_succ, Units.val_neg, neg_smul]
  abel

end

theorem etale_sheaf_tensor_complex_exists : EtaleSheafTensorComplexExists := by
  intro R _ I J
  let K : Cx R := CochainComplex.of (fun w => (presheafToSheaf Scheme.etaleTopology _).obj (etaleTensorPresheafOfComplexes I J w))
    (fun w => (presheafToSheaf Scheme.etaleTopology _).map (dP I J w))
    (fun w => by rw [← Functor.map_comp, tensorDifferential_comp_tensorDifferential, Functor.map_zero])
  refine ⟨K, fun U w => ((toSheafify Scheme.etaleTopology (etaleTensorPresheafOfComplexes I J w)).app (op U)).hom, ?_, ?_, ?_, ?_⟩
  · intro V U g w x
    change ((toSheafify Scheme.etaleTopology (etaleTensorPresheafOfComplexes I J w)).app (op U) ≫ (sheafify Scheme.etaleTopology (etaleTensorPresheafOfComplexes I J w)).map g.op).hom x = _
    rw [← (toSheafify Scheme.etaleTopology (etaleTensorPresheafOfComplexes I J w)).naturality]; rfl
  · intro U s t w h a b
    have hd : K.d w (w + 1) = (presheafToSheaf Scheme.etaleTopology _).map (dP I J w) := by
      simp [K, CochainComplex.of_d]
    rw [hd]
    change ((toSheafify Scheme.etaleTopology (etaleTensorPresheafOfComplexes I J w) ≫ sheafifyMap Scheme.etaleTopology (dP I J w)).app (op U)).hom (tensPure s t w h a b) = _
    rw [← toSheafify_naturality]
    change ((toSheafify Scheme.etaleTopology (etaleTensorPresheafOfComplexes I J (w + 1))).app (op U)).hom (dT I J U w (tensPure s t w h a b)) = _
    simp only [dT_pure, Units.smul_def]
    exact (LinearMap.map_add _ _ _).trans (congrArg _ (map_zsmul _ _ _))
  · intro U w y
    obtain h := Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (etaleTensorPresheafOfComplexes I J w)) (U := op U) y
    exact ⟨_, h, fun V g hg => hg⟩
  · intro U w x hx
    have h := Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (etaleTensorPresheafOfComplexes I J w)) (X := op U) x 0
      (by rw [map_zero]; exact hx)
    exact ⟨_, h, fun V g hg => (show Tens.res g w x = Tens.res g w 0 from hg).trans (map_zero _)⟩

end LateralTheory.EtaleFoundations
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.EvMkPf

variable {R : Type} [CommRing R] {E : Spc} {I : Cx R}

theorem sq {X Y : Type 1} (h : X ⟶ Y) {M N : ModuleCat.{1} (ULift.{1} R)} (a : Y ⟶ M) (b : X ⟶ N) (φ : N ⟶ M)
    (H : ∀ x, a (h x) = φ (b x)) :
    (ModuleCat.free (ULift.{1} R)).map h ≫ ModuleCat.freeDesc a = ModuleCat.freeDesc b ≫ φ := by
  apply ModuleCat.free_hom_ext
  intro x
  simp [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, H]

noncomputable def eta (k : ℕ) (s : ℤ) (F : ∀ U : Scheme.{0}, Sx E k U → Sec (I.X s) U)
    (hF : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E k U), Sec.res g (F U x) = F V (x.res g)) :
    (freeP R).obj (E.obj (op (SimplexCategory.mk k))) ⟶ (I.X s).obj where
  app U := ModuleCat.freeDesc (X := ULift.{1} (Sx E k U.unop)) (↾fun x => F U.unop (ULift.down x))
  naturality U V g := sq _ _ _ _ (fun x => (hF V.unop U.unop g.unop x.down).symm)

noncomputable def phi (k : ℕ) (s : ℤ) (F : ∀ U : Scheme.{0}, Sx E k U → Sec (I.X s) U)
    (hF : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E k U), Sec.res g (F U x) = F V (x.res g)) :
    (free R).obj (E.obj (op (SimplexCategory.mk k))) ⟶ I.X s :=
  ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv
    ((freeP R).obj (E.obj (op (SimplexCategory.mk k)))) (I.X s)).symm (eta k s F hF)

theorem phi_unit (k : ℕ) (s : ℤ) (F : ∀ U : Scheme.{0}, Sx E k U → Sec (I.X s) U)
    (hF : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E k U), Sec.res g (F U x) = F V (x.res g)) :
    toSheafify Scheme.etaleTopology.{0} ((freeP R).obj (E.obj (op (SimplexCategory.mk k)))) ≫ (phi k s F hF).hom =
      eta k s F hF := by
  have := ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv
    ((freeP R).obj (E.obj (op (SimplexCategory.mk k)))) (I.X s)).apply_symm_apply (eta k s F hF)
  rw [Adjunction.homEquiv_unit] at this
  exact this

theorem phi_freeGen (k : ℕ) (s : ℤ) (F : ∀ U : Scheme.{0}, Sx E k U → Sec (I.X s) U)
    (hF : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E k U), Sec.res g (F U x) = F V (x.res g))
    (U : Scheme.{0}) (x : Sx E k U) :
    ((phi k s F hF).hom.app (op U)).hom (freeGen R _ U x) = F U x := by
  have h2 := congrArg (fun f => (f.app (op U)).hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x))) (phi_unit k s F hF)
  exact h2.trans (ModuleCat.freeDesc_apply _ _)

variable {n : ℤ} (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
  (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))

noncomputable def comp (p q : ℤ) (hpq : p + n = q) : ((chains R).obj E).X p ⟶ I.X q :=
  if hp : p ≤ 0 then
    (HomologicalComplex.XIsoOfEq _ (by omega : p = -((p.natAbs : ℕ) : ℤ))).hom ≫ (chainsXIso R E p.natAbs).hom ≫
      phi p.natAbs q (fun U x => a p.natAbs q (by omega) U x) (fun V U g x => ha _ _ _ V U g x)
  else 0

theorem aux {s : ℤ} (j k : ℕ) (e : j = k) (hjk : -(k : ℤ) = -(j : ℤ)) (hj : -(j : ℤ) + n = s) (hk : -(k : ℤ) + n = s) :
    (HomologicalComplex.XIsoOfEq ((chains R).obj E) hjk).hom ≫ (chainsXIso R E j).hom ≫
      phi j s (fun U x => a j s hj U x) (fun V U g x => ha _ _ _ V U g x) =
    (chainsXIso R E k).hom ≫ phi k s (fun U x => a k s hk U x) (fun V U g x => ha _ _ _ V U g x) := by
  subst e
  simp

theorem comp_neg (k : ℕ) (s : ℤ) (h : -(k : ℤ) + n = s) :
    comp a ha (-(k : ℤ)) s h = (chainsXIso R E k).hom ≫ phi k s (fun U x => a k s h U x) (fun V U g x => ha _ _ _ V U g x) := by
  unfold comp
  rw [dite_eq_left (by omega)]
  exact aux a ha _ _ (by omega) _ _ _

end LateralTheory.EtaleFoundations.EvMkPf

open LateralTheory.EtaleFoundations.EvMkPf in
theorem LateralTheory.EtaleFoundations.pp_ev_mk_of : LateralTheory.EtaleFoundations.pp_ev_mk := by
  intro R _ E I n a ha
  refine ⟨Cochain.mk (comp a ha), fun p s h U x => ?_⟩
  unfold ev
  rw [Cochain.mk_v, comp_neg a ha p s h, Iso.inv_hom_id_assoc]
  exact phi_freeGen _ _ _ _ U x
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.EvBasicPf
variable {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
open LateralTheory.KummerTheory.AW

theorem ev_sub (α β : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x := by
  rw [ev_eq, Cochain.sub_v, Preadditive.comp_sub]
  exact map_sub (AddMonoidHom.mk' (fun φ : _ ⟶ I.X s => Sec.map φ (freeGen R _ U x)) (fun _ _ => rfl)) _ _

theorem ev_zero (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by
  rw [ev_eq, Cochain.zero_v, comp_zero]
  exact map_zero (AddMonoidHom.mk' (fun φ : _ ⟶ I.X s => Sec.map φ (freeGen R _ U x)) (fun _ _ => rfl))

theorem ev_zsmul (c : ℤ) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) : ev (c • α) p s h U x = c • ev α p s h U x := by
  exact map_zsmul (AddMonoidHom.mk' (fun β : Cochain ((chains R).obj E) I n => ev β p s h U x)
    (fun a b => ev_add a b p s h U x)) c α

theorem ev_post {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s)
    (U : Scheme.{0}) (x : Sx E p U) :
    ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  rw [ev_eq, Cochain.comp_zero_cochain_v, Cochain.ofHom_v, ev_eq]; rfl

theorem chainsXIso_nat {E' : Spc} (f : E' ⟶ E) (p : ℕ) :
    (chainsXIso R E' p).inv ≫ ((chains R).map f).f (-(p : ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E p).inv := by
  rw [Iso.inv_comp_eq]
  unfold chains chainsXIso
  change (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat).f (-(p : ℤ)) = _
  exact HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := p) (i' := -(p : ℤ)) rfl

theorem ev_pre {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s)
    (U : Scheme.{0}) (x : Sx E' p U) :
    ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f) := by
  rw [ev_eq, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, reassoc_of% (chainsXIso_nat (R := R) f p), ev_eq]
  change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h) (Sec.map ((free R).map (f.app (op (SimplexCategory.mk p))))
    (freeGen R _ U x)) = _
  rw [map_freeGen]; rfl

end LateralTheory.EtaleFoundations.EvBasicPf

open LateralTheory.EtaleFoundations.EvBasicPf LateralTheory.KummerTheory.AW in
theorem LateralTheory.EtaleFoundations.pp_ev_basic_of : LateralTheory.EtaleFoundations.pp_ev_basic := fun _ _ =>
  ⟨fun α β p s h U x => ⟨ev_add α β p s h U x, ev_sub α β p s h U x, ev_zero p s h U x, fun c => ev_zsmul c α p s h U x⟩,
   fun α p s h _ _ g x => ev_res α p s h g x,
   fun α β hh => ev_ext α β hh,
   fun f α p s h U x => ev_pre f α p s h U x,
   fun m α p s h U x => ev_post m α p s h U x⟩
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem t_pa_cpush_htpy_of : t_pa_cpush_htpy := by
  intro R _ E I J u u' H n x
  obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
  show CohomologyClass.mk (zcomp α (Cocycle.ofHom u) (add_zero n)) =
    CohomologyClass.mk (zcomp α (Cocycle.ofHom u') (add_zero n))
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨α.1.comp (Cochain.ofHomotopy H) (show n + -1 = n - 1 by omega), ?_⟩
  rw [δ_comp _ _ _ (n + 1) 0 n (by omega) rfl (by omega), δ_ofHomotopy, Cocycle.δ_eq_zero]
  simp [zcomp, Cochain.comp_sub]

end LateralTheory.EtaleFoundations
end
