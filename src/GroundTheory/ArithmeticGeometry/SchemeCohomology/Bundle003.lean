module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ConsCompSuccAboveZero
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import GroundTheory.FunctionField.PlaceDefs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Kaehler.Basic
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
public import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Algebra.Category.Grp.EpiMono
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Unramified.Field

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory Opposite TopologicalSpace Limits

universe w u

variable {X : TopCat.{u}}

section

variable {ι : Type w} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)

lemma res_congr {n : ℕ} (σ : Cochain P U n) {j₁ j₂ : Fin (n + 1) → ι} (h : j₁ = j₂)
    {V : Opens X} (h₁ : V ≤ inter U j₁) (h₂ : V ≤ inter U j₂) :
    res P h₁ (σ j₁) = res P h₂ (σ j₂) := by
  subst h
  rfl

lemma le_inter_const {n : ℕ} (a : ι) : U a ≤ inter U (fun _ : Fin n => a) := by
  intro x hx
  rw [mem_inter_iff]
  exact fun _ => hx

lemma inter_succ {n : ℕ} (i : Fin (n + 2) → ι) :
    inter U i = U (i 0) ⊓ inter U (i ∘ Fin.succ) := by
  ext x
  simp only [SetLike.mem_coe, Opens.mem_inf, mem_inter_iff, Fin.forall_fin_succ, Function.comp]

lemma d_zero_apply (σ : Cochain P U 0) (i : Fin 2 → ι) :
    d P U 0 σ i = res P (inter_le_comp U i (0 : Fin 2).succAbove) (σ (i ∘ (0 : Fin 2).succAbove)) -
      res P (inter_le_comp U i (1 : Fin 2).succAbove) (σ (i ∘ (1 : Fin 2).succAbove)) := by
  rw [d_apply, Fin.sum_univ_two]
  simp [sub_eq_add_neg]

def constCochain {V : Opens X} (hUV : ∀ a, U a ≤ V) (s : P.obj (op V)) : Cochain P U 0 :=
  fun i => res P ((inter_le U i 0).trans (hUV (i 0))) s

lemma d_constCochain {V : Opens X} (hUV : ∀ a, U a ≤ V) (s : P.obj (op V)) :
    d P U 0 (constCochain P U hUV s) = 0 := by
  funext i
  rw [d_zero_apply]
  simp only [constCochain, res_res, sub_self]
  rfl

end

variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
  (hP : Presheaf.IsSheaf (Opens.grothendieckTopology X) P)


include hP in
lemma exists_glue {ι : Type w} (U : ι → Opens X) (V : Opens X) (hUV : ∀ a, U a ≤ V)
    (hV : V ≤ iSup U) (τ : Cochain P U 0) (hτ : d P U 0 τ = 0) :
    ∃ t : P.obj (op V), ∀ i : Fin 1 → ι,
      res P ((inter_le U i 0).trans (hUV (i 0))) t = τ i := by
  let sf : ∀ j, P.obj (op (U j)) := fun j => res P (le_inter_const U j) (τ (fun _ => j))
  have compat : TopCat.Presheaf.IsCompatible P U sf := by
    intro i j
    have h := congrFun hτ ![i, j]
    rw [d_zero_apply] at h
    have hle : U i ⊓ U j ≤ inter U ![i, j] := by
      intro x hx
      rw [mem_inter_iff]
      intro a
      fin_cases a
      · exact hx.1
      · exact hx.2
    rw [Pi.zero_apply] at h
    have h' := congrArg (res P hle) h
    rw [map_sub, res_res, res_res, map_zero, sub_eq_zero] at h'
    have e0 : (![i, j] ∘ (0 : Fin 2).succAbove) = fun _ : Fin 1 => j := by
      funext a; fin_cases a; rfl
    have e1 : (![i, j] ∘ (1 : Fin 2).succAbove) = fun _ : Fin 1 => i := by
      funext a; fin_cases a; rfl
    rw [res_congr P U τ e0 _ ((inf_le_right).trans (le_inter_const U j)),
      res_congr P U τ e1 _ ((inf_le_left).trans (le_inter_const U i))] at h'
    change res P inf_le_left (sf i) = res P inf_le_right (sf j)
    simp only [sf, res_res]
    exact h'.symm
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' (⟨P, hP⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)
    U V (fun a => homOfLE (hUV a)) hV sf compat
  refine ⟨t, fun i => ?_⟩
  have hi : (fun _ : Fin 1 => i 0) = i := funext fun a => by rw [Subsingleton.elim a 0]
  have ht' : res P (hUV (i 0)) t = sf (i 0) := ht (i 0)
  rw [← res_res P (inter_le U i 0) (hUV (i 0)), ht']
  simp only [sf, res_res]
  exact (res_congr P U τ hi _ le_rfl).trans (res_refl _ _ _)


variable {P} in
lemma CechAcyclic.of_shortExact' {ι : Type w} (U : ι → Opens X)
    {F I Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (f : F ⟶ I) (g : I ⟶ Q) (hfg : f ≫ g = 0)
    (hinj : ∀ {n : ℕ} (i : Fin (n + 1) → ι), Function.Injective (f.app (op (inter U i))))
    (hex : ∀ {n : ℕ} (i : Fin (n + 1) → ι) (y : I.obj (op (inter U i))),
      g.app _ y = 0 → ∃ x, f.app _ x = y)
    (hsurj : ∀ {n : ℕ} (i : Fin (n + 1) → ι), Function.Surjective (g.app (op (inter U i))))
    (hF : CechAcyclic F U) (hI : CechAcyclic I U) : CechAcyclic Q U := by
  intro n σ hσ
  choose τ hτ using fun i => hsurj i (σ i)
  have hτ' : push U g (n + 1) τ = σ := funext hτ
  have h0 : push U g (n + 2) (d I U (n + 1) τ) = 0 := by rw [push_d, hτ', hσ]
  choose ρ hρ using fun j => hex j _ (congrFun h0 j)
  have hρ' : push U f (n + 2) ρ = d I U (n + 1) τ := funext hρ
  have hρc : d F U (n + 2) ρ = 0 := by
    apply push_injective U f (n + 3) (fun j => hinj j)
    rw [map_zero, push_d, hρ', d_d]
  obtain ⟨α, hα⟩ := hF (n + 1) ρ hρc
  have hc : d I U (n + 1) (τ - push U f (n + 1) α) = 0 := by
    rw [map_sub, ← push_d, hα, hρ', sub_self]
  obtain ⟨β, hβ⟩ := hI n _ hc
  refine ⟨push U g n β, ?_⟩
  rw [← push_d, hβ, map_sub, hτ', push_comp, hfg, push_zero', sub_zero]

section

variable {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)

include hS in
lemma app_injective_of_shortExact (W : (Opens X)ᵒᵖ) : Function.Injective (S.f.hom.app W) := by
  have : Mono S.f := hS.mono_f
  have : Mono S.f.hom := (TopCat.Sheaf.forget AddCommGrpCat.{u} X).map_mono S.f
  exact (AddCommGrpCat.mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 this W)

include hS in
lemma app_exact_of_shortExact (W : Opens X) (y : S.X₂.obj.obj (op W))
    (hy : S.g.hom.app (op W) y = 0) : ∃ x, S.f.hom.app (op W) x = y :=
  TopCat.Sheaf.sections_exact_of_left_exact hS.1 hS.2 y hy

set_option backward.isDefEq.respectTransparency false in
lemma comp_hom_eq_zero : S.f.hom ≫ S.g.hom = 0 := by
  rw [← ObjectProperty.FullSubcategory.comp_hom, S.zero]
  rfl

lemma app_comp_apply_eq_zero (W : (Opens X)ᵒᵖ) (x : S.X₁.obj.obj W) :
    S.g.hom.app W (S.f.hom.app W x) = 0 := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, comp_hom_eq_zero]
  rfl

end

variable (B : Opens X → Prop)

def CechCondition (F : TopCat.Sheaf AddCommGrpCat.{u} X) : Prop :=
  ∀ V, B V → ∀ (ι : Type u) [Finite ι] (U : ι → Opens X), (∀ a, B (U a)) → iSup U = V →
    CechAcyclic F.obj U

variable {B}

lemma inter_mem (hinf : ∀ V W, B V → B W → B (V ⊓ W)) {ι : Type w} (U : ι → Opens X)
    (hU : ∀ a, B (U a)) {n : ℕ} (i : Fin (n + 1) → ι) : B (inter U i) := by
  induction n with
  | zero =>
    have : inter U i = U (i 0) := le_antisymm (inter_le U i 0) (by
      intro x hx
      rw [mem_inter_iff]
      intro a
      rwa [Fin.fin_one_eq_zero a])
    rw [this]
    exact hU _
  | succ n ih =>
    rw [inter_succ]
    exact hinf _ _ (hU _) (ih _)

variable {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)

end GroundTheory.Arith.SchemeCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjSpace

variable (A : Type u) [CommRing A] (n : ℕ)

abbrev grading : ℕ → Submodule A (MvPolynomial (Fin (n + 1)) A) :=
  homogeneousSubmodule (Fin (n + 1)) A

end ProjSpace

open ProjSpace

abbrev projectiveSpace (A : Type u) [CommRing A] (n : ℕ) : Scheme.{u} := Proj (grading A n)

namespace ProjSpace

variable {A : Type u} [CommRing A] {n : ℕ}

def stdOpen (A : Type u) [CommRing A] (n : ℕ) (j : Fin (n + 1)) : (projectiveSpace A n).Opens :=
  Proj.basicOpen (grading A n) (X j)

def xprod {p : ℕ} (i : Fin p → Fin (n + 1)) : MvPolynomial (Fin (n + 1)) A := ∏ a, X (i a)

lemma xprod_mem {p : ℕ} (i : Fin p → Fin (n + 1)) : xprod (A := A) i ∈ grading A n p := by
  have := IsHomogeneous.prod (Finset.univ : Finset (Fin p)) (fun a => (X (i a) : MvPolynomial _ A))
    (fun _ => 1) (fun a _ => isHomogeneous_X A (i a))
  simpa [xprod] using this

lemma X_mem (j : Fin (n + 1)) : (X j : MvPolynomial (Fin (n + 1)) A) ∈ grading A n 1 :=
  isHomogeneous_X A j

lemma xprod_succ {p : ℕ} (i : Fin (p + 1) → Fin (n + 1)) :
    xprod (A := A) i = X (i 0) * xprod (A := A) (i ∘ Fin.succ) := by
  simp [xprod, Fin.prod_univ_succ]

lemma inter_stdOpen {p : ℕ} (i : Fin (p + 1) → Fin (n + 1)) :
    inter (X := (projectiveSpace A n).toTopCat) (stdOpen A n) i =
      Proj.basicOpen (grading A n) (xprod i) := by
  ext x
  change x ∈ inter (X := (projectiveSpace A n).toTopCat) (stdOpen A n) i ↔ _
  rw [mem_inter_iff]
  change (∀ a, x ∈ stdOpen A n (i a)) ↔ x ∈ Proj.basicOpen (grading A n) (xprod i)
  change (∀ a, X (i a) ∉ x.asHomogeneousIdeal.toIdeal) ↔
    (∏ a, X (i a)) ∉ x.asHomogeneousIdeal.toIdeal
  have := x.isPrime
  rw [Ideal.IsPrime.prod_mem_iff]
  simp

lemma isAffineOpen_inter {p : ℕ} (i : Fin (p + 1) → Fin (n + 1)) :
    IsAffineOpen (inter (X := (projectiveSpace A n).toTopCat) (stdOpen A n) i) := by
  rw [inter_stdOpen]
  exact Proj.isAffineOpen_basicOpen (grading A n) (xprod i) (xprod_mem i) (Nat.succ_pos p)

lemma isAffineOpen_stdOpen (j : Fin (n + 1)) : IsAffineOpen (stdOpen A n j) :=
  Proj.isAffineOpen_basicOpen (grading A n) (X j) (X_mem j) Nat.one_pos

lemma iSup_stdOpen : ⨆ j, stdOpen A n j = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  intro p hp
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  by_contra! h
  have hm0 : m = 0 := Finsupp.ext fun i => h i (Set.mem_univ i)
  subst hm0
  have h0 : GradedRing.proj (grading A n) 0 p = 0 := hp
  rw [GradedRing.proj_apply] at h0
  change ((MvPolynomial.decomposition.decompose' p 0 : homogeneousSubmodule (Fin (n + 1)) A 0) :
    MvPolynomial (Fin (n + 1)) A) = 0 at h0
  rw [MvPolynomial.decomposition.decompose'_apply, homogeneousComponent_zero, C_eq_zero] at h0
  exact (MvPolynomial.mem_support_iff.mp hm) h0

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
end

section

namespace GroundTheory.Arith.SchemeCoh

open GroundTheory.FunctionField KaehlerDifferential IntermediateField

variable {k K : Type*} [Field k] [Field K] [Algebra k K]


variable (k) in
def spanDField (x : K) : IntermediateField k K where
  carrier := {y | D k K y ∈ Submodule.span K {D k K x}}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Derivation.leibniz] at *
    exact add_mem (Submodule.smul_mem _ _ hb) (Submodule.smul_mem _ _ ha)
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, map_add (f := _)] at *
    exact add_mem ha hb
  algebraMap_mem' c := by
    simp only [Set.mem_ofPred_eq, Derivation.map_algebraMap]
    exact zero_mem _
  inv_mem' a ha := by
    simp only [Set.mem_ofPred_eq, Derivation.leibniz_inv] at *
    exact Submodule.smul_mem _ _ ha

theorem D_mem_span_of_mem_adjoin (x : K) {y : K} (hy : y ∈ k⟮x⟯) :
    D k K y ∈ Submodule.span K {D k K x} := by
  have : k⟮x⟯ ≤ spanDField k x := by
    rw [adjoin_le_iff, Set.singleton_subset_iff]
    exact Submodule.subset_span rfl
  exact this hy

theorem span_D_eq_top (x : K) [Algebra.IsSeparable k⟮x⟯ K] :
    Submodule.span K {D k K x} = ⊤ := by
  have : Algebra.FormallyUnramified k⟮x⟯ K := .of_isSeparable _ _
  refine eq_top_iff.mpr fun ω hω ↦ ?_
  clear hω
  obtain ⟨z, rfl⟩ := (exact_mapBaseChange_map k k⟮x⟯ K ω).mp (Subsingleton.elim _ _)
  induction z with
  | add a b ha hb => simpa only [map_add] using add_mem ha hb
  | tmul a b =>
    rw [mapBaseChange_tmul]
    refine Submodule.smul_mem _ _ ?_
    have hb : b ∈ Submodule.span k⟮x⟯ (Set.range (D k k⟮x⟯)) := by
      rw [span_range_derivation]; trivial
    induction hb using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨e, rfl⟩ := h
      rw [map_D]
      exact D_mem_span_of_mem_adjoin x e.2
    | zero => simp
    | add _ _ _ _ h₁ h₂ => simpa only [map_add] using add_mem h₁ h₂
    | smul c _ _ h =>
      rw [map_smul, algebra_compatible_smul K c]
      exact Submodule.smul_mem _ _ h

variable [IsFunctionField k K]

theorem kaehlerDifferential_nontrivial : Nontrivial Ω[K⁄k] := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have : Algebra.FormallyUnramified k K := ⟨h⟩
  have : Algebra.EssFiniteType k K := essFiniteType
  have : Module.Finite k K := Algebra.FormallyUnramified.finite_of_free k K
  have h1 := trdeg_eq_one (k := k) (K := K)
  have : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.of_finite k K
  rw [_root_.trdeg_eq_zero] at h1
  exact zero_ne_one h1

theorem D_ne_zero_of_isSeparable (x : K) [Algebra.IsSeparable k⟮x⟯ K] : D k K x ≠ 0 := by
  intro h
  have htop := span_D_eq_top (k := k) x
  rw [h, Submodule.span_singleton_eq_bot.mpr rfl] at htop
  have := kaehlerDifferential_nontrivial (k := k) (K := K)
  exact bot_ne_top htop

section Perfect

variable [PerfectField k]


variable (k K) in
theorem exists_isSeparable_adjoin : ∃ x : K, Algebra.IsSeparable k⟮x⟯ K := by
  have : Algebra.EssFiniteType k K := essFiniteType
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
  have hcard : s.card = 1 := by
    have h := hs.cardinalMk_eq_trdeg
    rw [trdeg_eq_one, Cardinal.mk_coe_finset] at h
    exact_mod_cast h
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hcard
  refine ⟨x, ?_⟩
  convert hsep <;> simp


variable (k K) in
theorem finrank_kaehlerDifferential : Module.finrank K Ω[K⁄k] = 1 := by
  obtain ⟨x, hx⟩ := exists_isSeparable_adjoin k K
  rw [← finrank_top, ← span_D_eq_top (k := k) x, finrank_span_singleton (D_ne_zero_of_isSeparable x)]

theorem span_D_eq_top_of_ne_zero {z : K} (hz : D k K z ≠ 0) :
    Submodule.span K {D k K z} = ⊤ :=
  have : FiniteDimensional K Ω[K⁄k] :=
    Module.finite_of_finrank_pos (by rw [finrank_kaehlerDifferential]; norm_num)
  Submodule.eq_top_of_finrank_eq (by
    rw [finrank_span_singleton hz, finrank_kaehlerDifferential])

theorem isSeparable_of_D_ne_zero {z : K} (hz : D k K z ≠ 0) : Algebra.IsSeparable k⟮z⟯ K := by
  have hsub : Subsingleton Ω[K⁄k⟮z⟯] := by
    refine subsingleton_of_forall_eq 0 fun ω' ↦ ?_
    obtain ⟨ω, rfl⟩ := map_surjective k k⟮z⟯ K ω'
    have hω : ω ∈ Submodule.span K {D k K z} := by rw [span_D_eq_top_of_ne_zero hz]; trivial
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hω
    have h0 : D k⟮z⟯ K z = 0 := (D k⟮z⟯ K).map_algebraMap ⟨z, mem_adjoin_simple_self k z⟩
    simp only [map_smul, map_D, Algebra.algebraMap_self, RingHom.id_apply]
    rw [h0, smul_zero]
  have : Algebra.FormallyUnramified k⟮z⟯ K := ⟨hsub⟩
  have : Algebra.EssFiniteType k K := essFiniteType
  have : Algebra.EssFiniteType k⟮z⟯ K := .of_comp k k⟮z⟯ K
  exact Algebra.FormallyUnramified.isSeparable k⟮z⟯ K

end Perfect

section Order

variable [PerfectField k]

end Order

end GroundTheory.Arith.SchemeCoh
end
