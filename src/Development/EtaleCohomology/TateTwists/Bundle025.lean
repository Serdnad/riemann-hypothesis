module

public import Development.EtaleCohomology.TateTwists.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Development.EtaleCohomology.TateTwists.Bundle017
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Sites.Adjunction
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
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.EtaleFoundations.TensUnivDeg

variable {R : Type} [CommRing R]

theorem tens_ind {I J : Cx R} (V : Scheme.{0}) (w : ℤ) (P : Tens I J V w → Prop) (h0 : P 0)
    (hadd : ∀ a b, P a → P b → P (a + b))
    (hm : ∀ (p : {p : ℤ × ℤ // p.1 + p.2 = w}) (a : Sec (I.X p.1.1) V) (b : Sec (J.X p.1.2) V),
      P (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        (Sec (I.X p.1.1) V ⊗[ULift.{1} R] Sec (J.X p.1.2) V)) p (a ⊗ₜ b)))
    (x : Tens I J V w) : P x := by
  classical
  induction x using DirectSum.induction_on with
  | zero => exact h0
  | of p t =>
    rw [← DirectSum.lof_eq_of (ULift.{1} R)]
    induction t using TensorProduct.induction_on with
    | zero => simpa using h0
    | tmul a b => exact hm p a b
    | add a b ha hb => rw [map_add (f := _)]; exact hadd _ _ ha hb
  | add a b ha hb => exact hadd _ _ ha hb

theorem res_lof {I J : Cx R} {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    Tens.res g w (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        (Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U)) p (a ⊗ₜ b)) =
      DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        (Sec (I.X p.1.1) V ⊗[ULift.{1} R] Sec (J.X p.1.2) V)) p (Sec.res g a ⊗ₜ Sec.res g b) := by
  classical
  simp [Tens.res, Sec.res]

theorem lift_lof {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    μ.lift U w (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        (Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U)) p (a ⊗ₜ b)) = μ.mul U p.1.1 p.1.2 w p.2 a b := by
  classical
  simp [Pair.lift]

def Tmap {I J I' J' : Cx R} (f : I ⟶ I') (g : J ⟶ J') (U : Scheme.{0}) (w : ℤ) :
    Tens I J U w →ₗ[ULift.{1} R] Tens I' J' U w :=
  DirectSum.lmap fun p => TensorProduct.map ((f.f p.1.1).hom.app (op U)).hom ((g.f p.1.2).hom.app (op U)).hom

theorem tmap_lof {I J I' J' : Cx R} (f : I ⟶ I') (g : J ⟶ J') (U : Scheme.{0}) (w : ℤ)
    (p : {p : ℤ × ℤ // p.1 + p.2 = w}) (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    Tmap f g U w (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        (Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U)) p (a ⊗ₜ b)) =
      DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        (Sec (I'.X p.1.1) U ⊗[ULift.{1} R] Sec (J'.X p.1.2) U)) p (Sec.map (f.f p.1.1) a ⊗ₜ Sec.map (g.f p.1.2) b) := by
  classical
  simp [Tmap, Sec.map]

def TP (I J : Cx R) (w : ℤ) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of _ (Tens I J U.unop w)
  map g := ModuleCat.ofHom (Tens.res g.unop w)
  map_id U := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    refine tens_ind U.unop w (fun x => Tens.res (𝟙 U.unop) w x = x) (by simp) (fun a b ha hb => ?_) (fun p a b => ?_) x
    · rw [map_add (f := _), ha, hb]
    · rw [res_lof]; simp [Sec.res]
  map_comp g h := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    refine tens_ind _ w (fun x => Tens.res (g ≫ h).unop w x = Tens.res h.unop w (Tens.res g.unop w x))
      (by simp) (fun a b ha hb => ?_) (fun p a b => ?_) x
    · rw [map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]
    · rw [res_lof, res_lof, res_lof]; simp [Sec.res]

def alpha {I J K : Cx R} (τ : Pair I J K) (w : ℤ) : TP I J w ⟶ (K.X w).obj where
  app U := ModuleCat.ofHom (τ.lift U.unop w)
  naturality U V g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    refine tens_ind U.unop w (fun x => τ.lift V.unop w (Tens.res g.unop w x) = Sec.res g.unop (τ.lift U.unop w x))
      (by simp) (fun a b ha hb => ?_) (fun p a b => ?_) x
    · simp only [map_add (f := _), ha, hb]
    · rw [res_lof, lift_lof, lift_lof, τ.nat]

def beta {I J I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (w : ℤ) : TP I J w ⟶ (K'.X w).obj where
  app U := ModuleCat.ofHom (ν.lift U.unop w ∘ₗ Tmap f g U.unop w)
  naturality U V e := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    refine tens_ind U.unop w (fun x => ν.lift V.unop w (Tmap f g V.unop w (Tens.res e.unop w x)) =
        Sec.res e.unop (ν.lift U.unop w (Tmap f g U.unop w x)))
      (by simp) (fun a b ha hb => ?_) (fun p a b => ?_) x
    · simp only [map_add (f := _), ha, hb]
    · rw [res_lof, tmap_lof, tmap_lof, lift_lof, lift_lof, ν.nat, TensUnivPf.nat_sec, TensUnivPf.nat_sec]

theorem alpha_locSurj {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (w : ℤ) :
    Presheaf.IsLocallySurjective Scheme.etaleTopology (alpha τ w) where
  imageSieve_mem {U} y := by
    obtain ⟨S, hS, hh⟩ := hτ.1 U w y
    refine Scheme.etaleTopology.superset_covering (fun V g hg => ?_) hS
    obtain ⟨x, hx⟩ := hh V g hg
    exact ⟨x, hx⟩

theorem etale_tensor_pairing_lift_eq_locally_res_eq {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (w : ℤ) {U : Scheme.{0}}
    (x y : Tens I J U w) (h : τ.lift U w x = τ.lift U w y) :
    Loc U fun _ g => Tens.res g w x = Tens.res g w y := by
  obtain ⟨S, hS, hh⟩ := hτ.2 U w (x - y) (by rw [map_sub, h, sub_self])
  exact ⟨S, hS, fun V g hg => sub_eq_zero.1 (by rw [← map_sub]; exact hh V g hg)⟩

theorem alpha_locInj {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (w : ℤ) :
    Presheaf.IsLocallyInjective Scheme.etaleTopology (alpha τ w) where
  equalizerSieve_mem {U} x y h := by
    obtain ⟨S, hS, hh⟩ := etale_tensor_pairing_lift_eq_locally_res_eq τ hτ w x y h
    exact Scheme.etaleTopology.superset_covering (fun V g hg => hh V g hg) hS

end LateralTheory.EtaleFoundations.TensUnivDeg

open LateralTheory.EtaleFoundations.TensUnivDeg in
theorem LateralTheory.EtaleFoundations.etale_tensor_pairing_degreewise_universal_of_sheafification : LateralTheory.EtaleFoundations.EtaleTensorDegreewiseMapExists := by
  intro R _ I J K τ hτ I' J' K' ν f g w
  have := alpha_locSurj τ hτ w
  have := alpha_locInj τ hτ w
  have hW : Scheme.etaleTopology.W (alpha τ w) := GrothendieckTopology.W_of_isLocallyBijective _ _
  obtain ⟨m, hm⟩ := (hW (K'.X w).obj (K'.X w).property).2 (beta ν f g w)
  refine ⟨⟨m⟩, fun U s t h a b => ?_⟩
  have e := congrArg (fun φ : TP I J w ⟶ (K'.X w).obj => (φ.app (op U)).hom
    (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        (Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U)) ⟨(s, t), h⟩ (a ⊗ₜ b))) hm
  simp only [NatTrans.comp_app, ModuleCat.hom_comp] at e
  change Sec.map ⟨m⟩ (τ.lift U w _) = (ν.lift U w ∘ₗ Tmap f g U w) _ at e
  rw [lift_lof, LinearMap.comp_apply, tmap_lof, lift_lof] at e
  exact e
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.EtaleFoundations

noncomputable def muK (q : ℕ) (A : CommRingCat.{0}) : Submodule (ULift.{1} (ZMod q)) ((twF q 1).obj A) :=
  Submodule.span _ {x | ∃ l : List (Prim q A), (l.map fun ζ => ζ.1).prod = 1 ∧
    x = (l.map fun ζ => twGenR A ζ).sum}

theorem muK_gen_map (q : ℕ) {A B : CommRingCat.{0}} (f : A ⟶ B) (ζ : Prim q A) :
    ((twF q 1).map f).hom (twGenR A ζ) = twGenR B (ζ.map f.hom) := by
  change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.hom) (Finsupp.single ζ 1)) = _
  rw [Finsupp.mapDomain_single]
  rfl

theorem muK_le (q : ℕ) {A B : CommRingCat.{0}} (f : A ⟶ B) :
    muK q A ≤ (muK q B).comap ((twF q 1).map f).hom := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨l, hl, rfl⟩
  refine Submodule.subset_span ⟨l.map (Prim.map f.hom), ?_, ?_⟩
  · have : ((l.map fun ζ => ζ.1).map f.hom).prod = f.hom 1 := by rw [← map_list_prod, hl]
    rw [map_one] at this
    rw [← this, List.map_map, List.map_map]
    rfl
  · rw [map_list_sum, List.map_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro ζ _
    exact muK_gen_map q f ζ

noncomputable def muT (q : ℕ) : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) where
  obj A := ModuleCat.of _ ((twF q 1).obj A ⧸ muK q A)
  map f := ModuleCat.ofHom (Submodule.mapQ _ _ ((twF q 1).map f).hom (muK_le q f))
  map_id A := by
    refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_))
    change Submodule.Quotient.mk (((twF q 1).map (𝟙 A)).hom x) = Submodule.Quotient.mk x
    rw [(twF q 1).map_id]; rfl
  map_comp f g := by
    refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_))
    change Submodule.Quotient.mk (((twF q 1).map (f ≫ g)).hom x) =
      Submodule.Quotient.mk (((twF q 1).map g).hom (((twF q 1).map f).hom x))
    rw [(twF q 1).map_comp]; rfl

noncomputable def muτ (q : ℕ) : twF q 1 ⟶ muT q where
  app A := ModuleCat.ofHom (muK q A).mkQ
  naturality A B f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    rfl

theorem muτ_list (q : ℕ) (A : CommRingCat.{0}) (l : List (Prim q A)) (hl : (l.map fun ζ => ζ.1).prod = 1) :
    (l.map fun ζ => ((muτ q).app A).hom (twGenR A ζ)).sum = 0 := by
  have h : (l.map fun ζ => twGenR A ζ).sum ∈ muK q A := Submodule.subset_span ⟨l, hl, rfl⟩
  have := (Submodule.Quotient.mk_eq_zero (muK q A)).2 h
  refine Eq.trans ?_ this
  change _ = ((muτ q).app A).hom (List.map (fun ζ => twGenR A ζ) l).sum
  rw [map_list_sum, List.map_map]
  rfl

def EtaleSheafifyMonoOfKernelLocallyZeroCriterion : Prop :=
  ∀ (q : ℕ) (P Q : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (τ : P ⟶ Q),
    (∀ (U : Scheme.{0}) (x : P.obj Γ(U, ⊤)), (τ.app _).hom x = 0 → Loc U fun _ g => (P.map g.appTop).hom x = 0) →
    Mono ((presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ τ))

def MuRootRelationSubmoduleEtaleLocallyZero : Prop :=
  ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (x : (twF q 1).obj Γ(U, ⊤)), x ∈ muK q Γ(U, ⊤) →
    Loc U fun _ g => ((twF q 1).map g.appTop).hom x = 0

theorem etale_sheafify_mono_of_kernel_locally_zero : EtaleSheafifyMonoOfKernelLocallyZeroCriterion := by
  intro q P Q τ h
  have hli : Presheaf.IsLocallyInjective Scheme.etaleTopology (Functor.whiskerLeft Scheme.Γ τ) := by
    refine ⟨fun {X} x y hxy => ?_⟩
    let x' : P.obj Γ(X.unop, ⊤) := x
    let y' : P.obj Γ(X.unop, ⊤) := y
    have hxy' : (τ.app _).hom x' = (τ.app _).hom y' := hxy
    obtain ⟨S, hS, hSP⟩ := h X.unop (x' - y') (by rw [map_sub, hxy', sub_self])
    refine Scheme.etaleTopology.superset_covering ?_ hS
    intro V g hg
    have h2 : (P.map g.appTop).hom (x' - y') = 0 := hSP V g hg
    rw [map_sub, sub_eq_zero] at h2
    exact h2
  have : Sheaf.IsLocallyInjective ((presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ τ)) :=
    (Presheaf.isLocallyInjective_presheafToSheaf_map_iff _ _).2 hli
  exact Sheaf.mono_of_isLocallyInjective _

theorem exists_etale_mono_muTwist_quotient_of_locally_zero (h1 : EtaleSheafifyMonoOfKernelLocallyZeroCriterion) (h2 : MuRootRelationSubmoduleEtaleLocallyZero) :
    ExistsEtaleMonoMuTwistKillingRootRelations := by
  intro q _
  refine ⟨muT q, muτ q, h1 q _ _ (muτ q) fun U x hx => h2 q U x ?_, muτ_list q⟩
  exact (Submodule.Quotient.mk_eq_zero (muK q _)).1 hx

end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

abbrev LkumTex : Prop := ∀ (q : ℕ) [NeZero q], IsKum q (kumT q)

abbrev LevMk : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
  (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U),
  (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) →
  ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x

abbrev LevDelta : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m)
  (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}),
  (∀ (x : Sx E 0 U), ev (δ n m α) 0 m (by simp) U x = Sec.map (I.d n m) (ev α 0 n (by simp) U x)) ∧
  ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U),
    ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) +
      m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U (x.face i)

lemma units_map_appTop_comp {V U X : Scheme.{0}} (g : V ⟶ U) (x : U ⟶ X) (u : (Γ(X, ⊤))ˣ) :
    Units.map g.appTop.hom.toMonoidHom (Units.map x.appTop.hom.toMonoidHom u) =
      Units.map (g ≫ x).appTop.hom.toMonoidHom u := by
  ext; simp; rfl

lemma isUnit_q_pull {U X : Scheme.{0}} (q : ℕ) (x : U ⟶ X) (hq : IsUnit (q : Γ(X, ⊤))) :
    IsUnit (q : Γ(U, ⊤)) := by
  simpa using hq.map x.appTop.hom

theorem kum_pow_coc_of (hk : LkumTex) (hmk : LevMk) (hd : LevDelta) (he : kum_exists) : kum_pow_coc := by
  intro q _ X u hq
  let I := res _ (tw q 1)
  let a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 0 = s → ∀ U : Scheme.{0}, Sx (sch.obj X) p U → Sec (I.X s) U :=
    fun p s _ U x => if hs : s = 0 then (by subst hs; exact kumT q U (Units.map (x : U ⟶ X).appTop.hom.toMonoidHom u))
      else 0
  have ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx (sch.obj X) p U),
      Sec.res g (a p s h U x) = a p s h V (x.res g) := by
    intro p s h V U g x
    by_cases hs : s = 0
    · subst hs
      simp only [a, dif_pos]
      rw [(hk q).1 V U g _ (isUnit_q_pull q x hq)]
      exact congrArg (kumT q V) (units_map_appTop_comp g x u)
    · simp only [a, dif_neg hs, map_zero]
  obtain ⟨α, hα⟩ := hmk (ZMod q) a ha
  refine ⟨Cocycle.mk (δ 0 1 α) 2 (by norm_num) (δ_δ 0 1 2 α), ⟨?_, ?_⟩, ?_⟩
  · have key : ∀ (U : Scheme.{0}) (x : Sx (sch.obj X) (0 + 1) U), ev (δ 0 1 α) (0 + 1) 0 (by simp) U x = 0 := by
      intro U x
      rw [(hd (ZMod q) (n := 0) (m := 1) (by norm_num) α U).2 0 (-1) 0 (by simp) (by simp) x, hα]
      have z : a (0 + 1) (-1) (by simp) U x = 0 := dif_neg (by norm_num)
      have f0 : x.face 0 = x.face 1 := rfl
      rw [z, Fin.sum_univ_two, f0]
      simp [Sec.map]
    exact fun U x => key U x
  · intro U x v hv
    obtain ⟨γ0, _, hγ0⟩ := he q X (u ^ q) hq
    have e1 := hγ0 U x v hv
    have e2 := hγ0 U x (Units.map x.appTop.hom.toMonoidHom u) (by rw [map_pow])
    have h1 := (hd (ZMod q) (n := 0) (m := 1) (by norm_num) α U).1 x
    refine h1.trans ?_
    erw [hα]
    simp only [a, dif_pos]
    exact e2.symm.trans e1
  · rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨0, by norm_num, α, rfl⟩

end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def uniq_prim_loc : Prop :=
  ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), (IsUnit (q : Γ(U, ⊤)) → Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))) ∧ (∀ ζ ξ : Prim q Γ(U, ⊤), Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) ∧ (∀ (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)), x ^ q = 1 → Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a) ∧ (IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ, Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u)

def sections_unique_of_local_agreement : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg

def uniq_ev_basic : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x, ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧ ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧ ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧ ∀ c : ℤ, ev (c • α) p s h U x = c • ev α p s h U x) ∧ (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)) ∧ (∀ α β : Cochain ((chains R).obj E) I n, (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β) ∧ (∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U), ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f)) ∧ ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x, ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x)

theorem sec_neg_eq (q : ℕ) [NeZero q] (s : ℤ) (hs : s < 0) (U : Scheme.{0})
    (a b : Sec ((res _ (tw q 1)).X s) U) : a = b := by
  have h0 : IsZero ((res _ (tw q 1)).X s) := by
    unfold res
    exact CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by omega)
  have h1 : IsZero (((res _ (tw q 1)).X s).obj.obj (op U)) :=
    ((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U)).map_isZero h0)
  have : Subsingleton (((res _ (tw q 1)).X s).obj.obj (op U)) :=
    (ModuleCat.isZero_iff_subsingleton).mp h1
  exact Subsingleton.elim a b

theorem root_res (q : ℕ) (X U V : Scheme.{0}) (u : (Γ(X, ⊤))ˣ) (x : U ⟶ X) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ)
    (hv : v ^ q = Units.map g.appTop.hom.toMonoidHom (Units.map x.appTop.hom.toMonoidHom u)) :
    v ^ q = Units.map (Sx.res (E := sch.obj X) (p := 0) g x : V ⟶ X).appTop.hom.toMonoidHom u := by
  have e : (Sx.res (E := sch.obj X) (p := 0) g x : V ⟶ X) = g ≫ x := rfl
  rw [hv, e]; ext; simp
  rfl

theorem kum_uniq_of (hl : uniq_prim_loc) (hg : sections_unique_of_local_agreement) (hb : uniq_ev_basic) : kum_uniq := by
  intro q _ X u hq γ γ' h h'
  have key : γ = γ' := by
    apply Subtype.ext
    apply (hb (ZMod q)).2.2.1
    intro p s hs U x
    rcases p with _ | _ | p
    · have hs' : s = 1 := by omega
      subst hs'
      have hqU : IsUnit ((q : ℕ) : Γ(U, ⊤)) := by
        have := hq.map x.appTop.hom
        simpa using this
      obtain ⟨S, hS, hP⟩ := (hl q U).2.2.2 hqU (Units.map x.appTop.hom.toMonoidHom u)
      apply (hg (ZMod q) _ U).1
      refine ⟨S, hS, fun V g hgS => ?_⟩
      obtain ⟨v, hv⟩ := hP V g hgS
      rw [(hb (ZMod q)).2.1, (hb (ZMod q)).2.1]
      have hv' := root_res q X U V u x g v hv
      rw [h.2 V _ v hv', h'.2 V _ v hv']
    · have hs' : s = 0 := by omega
      subst hs'
      rw [h.1 U x, h'.1 U x]
    · exact sec_neg_eq q s (by omega) U _ _
  rw [key]

end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem t_pa_cpush_id_of : t_pa_cpush_id := by
  intro R _ E I n x
  obtain ⟨a, rfl⟩ := CohomologyClass.mk_surjective x
  show CohomologyClass.mk (zcomp a (Cocycle.ofHom (𝟙 I)) (add_zero n)) = CohomologyClass.mk a
  congr 1
  apply Cocycle.ext
  simp [zcomp]

end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem pa_sec_res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have := congrArg (fun f => (ModuleCat.Hom.hom f) x) (φ.hom.naturality g.op)
  simpa using this.symm

theorem pa_sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}}
    (x : Sec F U) : Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem t_pa_precomp_of : t_pa_precomp := by
  intro R _ I I' J K u μ
  refine ⟨⟨fun U s t w h => (μ.mul U s t w h).comp ((u.f s).hom.app (op U)).hom, ?_, ?_⟩, ?_⟩
  · intro V U g s t w h a b
    simp only [LinearMap.comp_apply]
    exact (μ.nat g s t w h _ b).trans (by rw [pa_sec_res_map])
  · intro U s t w h a b
    simp only [LinearMap.comp_apply]
    rw [μ.leibniz]
    congr 2
    rw [← pa_sec_map_comp, u.comm]; rfl
  · intro U s t w h a b
    rfl

end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

lemma restr_isRightAdjoint (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) :
    (restr φ).IsRightAdjoint := by
  unfold restr
  exact (Sheaf.adjunction Scheme.etaleTopology.{0} (ModuleCat.extendRestrictScalarsAdj.{1, 1, 1}
    ((ULift.ringEquiv.symm : S ≃+* ULift.{1} S).toRingHom.comp (φ.comp (ULift.ringEquiv : ULift.{1} R ≃+* R).toRingHom)))).isRightAdjoint

lemma restr_isLeftAdjoint (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) :
    (restr φ).IsLeftAdjoint := by
  unfold restr
  set f := ((ULift.ringEquiv.symm : S ≃+* ULift.{1} S).toRingHom.comp (φ.comp (ULift.ringEquiv : ULift.{1} R ≃+* R).toRingHom))
  have hpl : PreservesLimitsOfSize.{0, 1} (ModuleCat.coextendScalars.{1, 1, 1} f) :=
    (ModuleCat.restrictCoextendScalarsAdj.{1, 1, 1} f).rightAdjoint_preservesLimits
  have : Scheme.etaleTopology.{0}.HasSheafCompose (ModuleCat.coextendScalars.{1, 1, 1} f) :=
    hasSheafCompose_of_preservesLimitsOfSize _
  have adj := Sheaf.adjunction Scheme.etaleTopology.{0} (ModuleCat.restrictCoextendScalarsAdj.{1, 1, 1} f)
  have := (sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).counit_isIso_of_R_fully_faithful
  have e : Sheaf.composeAndSheafify Scheme.etaleTopology.{0} (ModuleCat.restrictScalars.{1} f) ≅
      sheafCompose Scheme.etaleTopology.{0} (ModuleCat.restrictScalars.{1} f) :=
    NatIso.ofComponents (fun X => (asIso (sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).counit).app
      ((sheafCompose Scheme.etaleTopology.{0} (ModuleCat.restrictScalars.{1} f)).obj X)) (by
        intro X Y g
        exact (sheafificationAdjunction _ _).counit.naturality
          ((sheafCompose Scheme.etaleTopology.{0} (ModuleCat.restrictScalars.{1} f)).map g))
  exact ⟨_, ⟨adj.ofNatIsoLeft e⟩⟩

theorem etaleSheaf_restrictScalars_functor_exact_of_adjoints : EtaleSheafRestrictScalarsFunctorExact := by
  intro R S _ _ φ
  have := restr_isRightAdjoint R S φ
  have := restr_isLeftAdjoint R S φ
  exact ⟨inferInstance, inferInstance⟩

end LateralTheory.EtaleFoundations
end
