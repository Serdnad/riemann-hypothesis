module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle065
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2791
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2917
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2919
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2792
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2920
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2957
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle155
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2990
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle188
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SurjectiveCubeOfGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2947
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2948
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2994
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle097
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8

theorem equivMap_of_torMatch : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left), Function.Injective g → ∀ ρ, TorMatch U U' g β ρ → EquivMap U U' β ρ := by
  intro R _ _ _ hR G _ _ hG D A U V _ _ _ hV G' _ _ hG' D' A' U' g β hg ρ h
  intro f f' hf hf' hc m m' hm hm' y
  have hkV : ∀ k : ℕ, IsUnit (k : R) → IsUnit (k : V) := fun k hk => by
    simpa using hk.map g
  have hkR : ∀ k : ℕ, IsUnit (k : R) → IsUnit (k : R) := fun _ hk => hk
  have t := GlobalTheory.Poinc.TorEnd.torMatch_of_endChar R hR G hG D A U f hf m hm
  have t' := GlobalTheory.Poinc.TorEnd.torMatch_of_endChar V hV G' hG' D' A' U' f' hf' m' hm'
  have c₁ := torMatch_comp R hR G hG D A U R hR G hG D A U (RingHom.id R) f.left V hV G' hG' D' A' U' g β hg hkR m ρ t h
  have c₂ := torMatch_comp R hR G hG D A U V hV G' hG' D' A' U' g β V hV G' hG' D' A' U' (RingHom.id V) f'.left
    Function.injective_id hkV ρ m' h t'
  rw [RingHom.comp_id] at c₁
  rw [RingHom.id_comp, hc] at c₂
  have e := torMatch_unique R hR G hG D A U V hV G' hG' D' A' U' g (β ≫ f.left) hg _ _ c₁ c₂
  exact DFunLike.congr_fun e y

end GlobalTheory.Poinc.Eq8
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8.PowChar

theorem isMonHom_of_coords {S : Scheme.{0}} {B C X : Over S} [GrpObj B] [GrpObj C] [GrpObj X]
    (pr : Fin 8 → (B ⟶ C)) (hpr : ∀ a, IsMonHom (pr a))
    (huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ C)), ∃! x : T ⟶ B, ∀ a, x ≫ pr a = y a)
    (z : X ⟶ B) (h : ∀ a, IsMonHom (z ≫ pr a)) : IsMonHom z := by
  have hm : ∀ (T : Over S) (x y : T ⟶ X), (x * y) ≫ z = (x ≫ z) * (y ≫ z) := by
    intro T x y
    refine (huniv T (fun a => (x * y) ≫ z ≫ pr a)).unique (fun a => Category.assoc _ _ _) (fun a => ?_)
    haveI := hpr a
    haveI := h a
    rw [MonObj.mul_comp, Category.assoc, Category.assoc, ← MonObj.mul_comp]
  exact { one_hom := by
            rw [MonObj.one_eq_one, MonObj.one_eq_one]
            exact map_one (MonoidHom.mk' (fun x : 𝟙_ (Over S) ⟶ X ↦ x ≫ z) (hm _))
          mul_hom := by
            rw [MonObj.mul_eq_mul, hm, MonObj.mul_eq_mul, MonObj.comp_mul]
            simp }

theorem isMonHom_one {S : Scheme.{0}} {B C : Over S} [GrpObj B] [GrpObj C] : IsMonHom (1 : B ⟶ C) :=
  inferInstanceAs (IsMonHom (toUnit B ≫ η[C]))

theorem exists_incl {S : Scheme.{0}} {B C : Over S} [GrpObj B] [GrpObj C]
    (pr : Fin 8 → (B ⟶ C)) (hpr : ∀ a, IsMonHom (pr a))
    (huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ C)), ∃! x : T ⟶ B, ∀ a, x ≫ pr a = y a) :
    ∃ z : Fin 8 → (C ⟶ B), (∀ u, IsMonHom (z u)) ∧ ∀ u v, z u ≫ pr v = if v = u then 𝟙 C else 1 := by
  choose z hz _ using fun u : Fin 8 => huniv C (fun v => if v = u then 𝟙 C else 1)
  refine ⟨z, fun u => isMonHom_of_coords pr hpr huniv (z u) fun a => ?_, hz⟩
  rw [hz u a]
  split_ifs
  · infer_instance
  · exact isMonHom_one

end GlobalTheory.Poinc.Eq8.PowChar

namespace GlobalTheory.Poinc.Eq8.PowChar

theorem isMonHom_prod {S : Scheme.{0}} {X M : Over S} [GrpObj X] [GrpObj M] [IsCommMonObj M] {J : Type}
    (f : J → (X ⟶ M)) (hf : ∀ i, IsMonHom (f i)) (s : Finset J) : IsMonHom (∏ i ∈ s, f i) := by
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty]; exact isMonHom_one
  · intro a s ha ih
    rw [Finset.prod_insert ha]
    haveI := hf a
    exact inferInstanceAs (IsMonHom (lift (f a) (∏ i ∈ s, f i) ≫ μ[M]))

theorem prod_comp {S : Scheme.{0}} {X M N : Over S} [GrpObj M] [GrpObj N] [IsCommMonObj M] [IsCommMonObj N] {J : Type}
    (f : J → (X ⟶ M)) (s : Finset J) (g : M ⟶ N) [IsMonHom g] : (∏ i ∈ s, f i) ≫ g = ∏ i ∈ s, f i ≫ g := by
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.prod_empty, MonObj.one_comp]
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.mul_comp, ih]

end GlobalTheory.Poinc.Eq8.PowChar

namespace GlobalTheory.Poinc.Eq8


open PowChar in
theorem characters_eighthPower_elementaryMatrices : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → (Function.Bijective fun y : Fin 8 → D.toPre.X => ∑ v, c v (y v)) ∧ ∀ (a b : Fin 8) (f : G' ⟶ G') (f₁ : A'.A ⟶ A'.A) (m : D'.toPre.X →+ D'.toPre.X), IsMonHom f → MatEnd pr a b f₁ → (Over.pullback (jK R)).map f ≫ U'.gen.hom = U'.gen.hom ≫ f₁ → EndChar U' f m → ∀ w x, m (c w x) = if w = a then c b x else 0 := by
  intro R _ _ _ hR hdvr G _ _ hG D A U G' _ _ hG' D' A' U' W _ pr hpr huniv _ pG hpG hgen c hc
  haveI := hdvr
  haveI := U.gen_hom
  haveI := U'.gen_hom
  letI : (Over.pullback (jK R)).Monoidal := (Over.instBraidedPullback (f := jK R)).toMonoidal
  have ext : ∀ {H H' : Over (Sp R)} [GrpObj H] [GrpObj H'], IsSemiAbelian H → IsSemiAbelian H' →
      ∀ (F₁ F₂ : H ⟶ H'), IsMonHom F₁ → IsMonHom F₂ →
        (Over.pullback (jK R)).map F₁ = (Over.pullback (jK R)).map F₂ → F₁ = F₂ := by
    intro H H' _ _ h h' F₁ F₂ h₁ h₂ e
    exact (GlobalTheory.semiAbelian_hom_extends_uniquely_dvr R (FractionRing R) H H' h h' _ inferInstance).unique
      ⟨h₁, e⟩ ⟨h₂, rfl⟩
  obtain ⟨z, hzm, hz⟩ := exists_incl pr hpr huniv
  have hic : ∀ u, ∃ ic : G ⟶ G', IsMonHom ic ∧ (Over.pullback (jK R)).map ic = U.gen.hom ≫ z u ≫ U'.gen.inv := by
    intro u
    haveI := hzm u
    obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.semiAbelian_hom_extends_uniquely_dvr R (FractionRing R) G G' hG hG'
      (U.gen.hom ≫ z u ≫ U'.gen.inv) inferInstance
    exact ⟨F, hF, hF'⟩
  choose ic hicm hicg using hic
  have hicp : ∀ u v, ic u ≫ pG v = if v = u then 𝟙 G else 1 := by
    intro u v
    haveI := hicm u
    haveI := hpG v
    have key : (Over.pullback (jK R)).map (ic u ≫ pG v) ≫ U.gen.hom = U.gen.hom ≫ (if v = u then 𝟙 A.A else 1) := by
      rw [Functor.map_comp, Category.assoc, hgen v, ← Category.assoc, hicg u]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, hz u v]
    by_cases h : v = u
    · rw [if_pos h] at key ⊢
      refine ext hG hG _ _ inferInstance inferInstance ?_
      rw [← cancel_mono U.gen.hom, key, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    · rw [if_neg h] at key ⊢
      refine ext hG hG _ _ inferInstance isMonHom_one ?_
      rw [← cancel_mono U.gen.hom, key, Functor.map_one, MonObj.comp_one, MonObj.one_comp]
  have hpw : ∀ w, (∏ v, pG v ≫ ic v) ≫ pG w = pG w := by
    intro w
    haveI := hpG w
    rw [PowChar.prod_comp, Finset.prod_eq_single w]
    · rw [Category.assoc, hicp w w, if_pos rfl, Category.comp_id]
    · intro v _ hv
      rw [Category.assoc, hicp v w, if_neg (Ne.symm hv), MonObj.comp_one]
    · intro h
      exact absurd (Finset.mem_univ w) h
  have hprod : (∏ v, pG v ≫ ic v) = 𝟙 G' := by
    have hm : IsMonHom (∏ v, pG v ≫ ic v) :=
      isMonHom_prod _ (fun v => by haveI := hpG v; haveI := hicm v; infer_instance) _
    refine ext hG' hG' _ _ hm inferInstance ?_
    rw [CategoryTheory.Functor.map_id, ← cancel_mono U'.gen.hom, Category.id_comp]
    refine (huniv _ (fun w => U'.gen.hom ≫ pr w)).unique (fun w => ?_) (fun w => rfl)
    rw [Category.assoc, ← hgen w, ← Category.assoc, ← Functor.map_comp, hpw w]
  have hinj : Function.Injective (RingHom.id R) := Function.injective_id
  have hk : ∀ k : ℕ, IsUnit (k : R) → IsUnit (k : R) := fun _ h => h
  choose d hd using fun u => GlobalTheory.Poinc.HomTor.exists_torMatch R hR G' hG' D' A' U' G hG D A U (ic u) (hicm u)
  obtain ⟨hid, hone, -⟩ := torMatch_id_one_mul R hR G hG D A U G hG D A U
  obtain ⟨hid', hone', hmul'⟩ := torMatch_id_one_mul R hR G' hG' D' A' U' G' hG' D' A' U'
  obtain ⟨-, hone'', -⟩ := torMatch_id_one_mul R hR G hG D A U G' hG' D' A' U'
  have hdc : ∀ u v, (d u).comp (c v) = if v = u then AddMonoidHom.id _ else 0 := by
    intro u v
    have h1 := torMatch_comp R hR G hG D A U R hR G' hG' D' A' U' (RingHom.id R) (pG v).left R hR G hG D A U
      (RingHom.id R) (ic u).left hinj hk (c v) (d u) (hc v) (hd u)
    rw [← Over.comp_left, hicp u v, RingHom.id_comp] at h1
    by_cases h : v = u
    · rw [if_pos h] at h1 ⊢
      rw [Over.id_left] at h1
      exact torMatch_unique R hR G hG D A U R hR G hG D A U _ _ hinj _ _ h1 hid
    · rw [if_neg h] at h1 ⊢
      exact torMatch_unique R hR G hG D A U R hR G hG D A U _ _ hinj _ _ h1 hone
  have hcd : ∑ v, (c v).comp (d v) = AddMonoidHom.id _ := by
    have hs : ∀ s : Finset (Fin 8), TorMatch U' U' (RingHom.id R) (∏ v ∈ s, pG v ≫ ic v).left
        (∑ v ∈ s, (c v).comp (d v)) := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · rw [Finset.prod_empty, Finset.sum_empty]
        exact hone'
      · intro a s ha ih
        rw [Finset.prod_insert ha, Finset.sum_insert ha]
        have h1 := torMatch_comp R hR G' hG' D' A' U' R hR G hG D A U (RingHom.id R) (ic a).left R hR G' hG' D' A' U'
          (RingHom.id R) (pG a).left hinj hk (d a) (c a) (hd a) (hc a)
        rw [← Over.comp_left, RingHom.id_comp] at h1
        exact hmul' _ _ _ _ h1 ih
    have h2 := hs Finset.univ
    rw [hprod, Over.id_left] at h2
    exact torMatch_unique R hR G' hG' D' A' U' R hR G' hG' D' A' U' _ _ hinj _ _ h2 hid'
  refine ⟨?_, ?_⟩
  · rw [Function.bijective_iff_has_inverse]
    refine ⟨fun x u => d u x, fun y => ?_, fun x => ?_⟩
    · funext u
      have e : ∀ v, d u (c v (y v)) = if v = u then y v else 0 := fun v => by
        have := DFunLike.congr_fun (hdc u v) (y v)
        rw [AddMonoidHom.comp_apply] at this
        rw [this]
        split_ifs <;> rfl

      simp only [map_sum, e, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · have := DFunLike.congr_fun hcd x
      simpa using this
  · intro a b f f₁ m hf hf₁ hff₁ hm w x
    haveI := hf
    haveI := hpG w
    have hfp : f ≫ pG w = if w = a then pG b else 1 := by
      have key : (Over.pullback (jK R)).map (f ≫ pG w) ≫ U.gen.hom = U'.gen.hom ≫ (if w = a then pr b else 1) := by
        rw [Functor.map_comp, Category.assoc, hgen w, ← Category.assoc, hff₁, Category.assoc, hf₁.2 w]
      by_cases h : w = a
      · rw [if_pos h] at key ⊢
        refine ext hG' hG _ _ inferInstance (hpG b) ?_
        rw [← cancel_mono U.gen.hom, key, hgen b]
      · rw [if_neg h] at key ⊢
        refine ext hG' hG _ _ inferInstance isMonHom_one ?_
        rw [← cancel_mono U.gen.hom, key, Functor.map_one, MonObj.comp_one, MonObj.one_comp]
    have h1 := torMatch_comp R hR G hG D A U R hR G' hG' D' A' U' (RingHom.id R) (pG w).left R hR G' hG' D' A' U'
      (RingHom.id R) f.left hinj hk (c w) m (hc w) (GlobalTheory.Poinc.TorEnd.torMatch_of_endChar R hR G' hG' D' A' U' f hf m hm)
    rw [← Over.comp_left, hfp, RingHom.id_comp] at h1
    have e : m.comp (c w) = if w = a then c b else 0 := by
      by_cases h : w = a
      · rw [if_pos h] at h1 ⊢
        exact torMatch_unique R hR G hG D A U R hR G' hG' D' A' U' _ _ hinj _ _ h1 (hc b)
      · rw [if_neg h] at h1 ⊢
        exact torMatch_unique R hR G hG D A U R hR G' hG' D' A' U' _ _ hinj _ _ h1 hone''
    have := DFunLike.congr_fun e x
    rw [AddMonoidHom.comp_apply] at this
    rw [this]
    split_ifs <;> rfl

end GlobalTheory.Poinc.Eq8
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_monomial_trivialisation_sqrt_refinedPolarisedData : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) [IsLocalRing R'] (m : ℕ) (t : Fin m → R) (r : Fin m → R') (δ : Fin m → LinearMap.BilinForm ℤ Q.X), IsCN R' → Function.Injective ρ → Half Q ρ D e (fun _ _ => 1) → D.PsiEven → D.TauBimult → Q.IsMonomialTau t δ → (∀ i y, 0 ≤ δ i y y) → (∀ i, t i ≠ 0) → (∀ i, r i ^ 2 = ρ (t i)) → IsMonomial D r fun i => (2 : ℤ) • pull e.toIntLinearEquiv.toLinearMap (δ i) := by
  first | exact @GlobalTheory.MonoTriv.main | exact GlobalTheory.MonoTriv.main | (intros; apply GlobalTheory.MonoTriv.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_symmetric_data_compare_polarised_up_to_function : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [IsNoetherianRing R'] (Q : Data R) (ρ : R →+* R') (P : PolAV (Sp R')) (β : P.A.left ⟶ Q.B.left) (β₂ : (G2 P.A).left ⟶ (G2 Q.B).left), Function.Injective ρ → IsGrpPullback P.A Q.B (spMap ρ) β → IsSquare β β₂ → (letI := P.isAb.comm; LBIso (abelian₂ P.A P.L) ((abelian₂ Q.B Q.M.L).pull β₂)) → ∃ (D : DegPre R') (e : D.X ≃+ Q.X) (f : D.X → D.X → (FractionRing R')ˣ), Half Q ρ D e f := by
  first | exact @GlobalTheory.HalfEx.half_exists | exact GlobalTheory.HalfEx.half_exists | (intros; apply GlobalTheory.HalfEx.half_exists <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isMonomialTau_first_coords_of_unit_last_coords : ∀ (V : Type) [CommRing V] [IsDomain V] (Q : Data V) (τ₀ : GlobalTheory.Poinc.Sep.Gens Q) (m N : ℕ) (s : Fin m ⊕ Fin N → V) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ Q.X), (∀ k, IsUnit (s (.inr k))) → GlobalTheory.Poinc.Sep.TauIn Q τ₀ (fun k => s (finSumFinEquiv.symm k)) (fun k => ε (finSumFinEquiv.symm k)) → Q.IsMonomialTau (fun k => s (.inl k)) (fun k => ε (.inl k)) := by
  first | exact @GlobalTheory.Poinc.Sep.isMonomialTau_inl_of_tauIn | exact GlobalTheory.Poinc.Sep.isMonomialTau_inl_of_tauIn | (intros; apply GlobalTheory.Poinc.Sep.isMonomialTau_inl_of_tauIn <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_trait_period_form_valuation_sum_refined_chart : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) (S : Scheme.{0}) (j : F.X ⟶ S)
    (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (ξ : Sp V ⟶ S), UnifOver F j ξ Q →
    ∀ (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X) (R' : Type) [CommRing R'] [IsDomain R']
      [IsLocalRing R'] (ρ : V →+* R') (r : Fin m → R') (D : DegData R' (maximalIdeal R')) (e : D.toPre.X ≃+ Q.X),
      IsCN R' → Function.Injective ρ → ρ.Finite → IsLocalHom ρ → (∀ k, r k ^ 2 = ρ (t k)) → (∀ k, t k ≠ 0) →
      (∀ k a b, δ k a b = δ k b a) → Refines Q ρ D.toPre e →
      IsMonomial D.toPre r (fun k => (2 : ℤ) • pull e.toIntLinearEquiv.toLinearMap (δ k)) →
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W], IsAdicComplete (maximalIdeal W) W →
    ∀ κ : R' →+* W, Function.Injective κ → IsLocalHom κ →
      ∃ (T : Trait F) (σ : W →+* T.V) (c : Fin m → ℕ) (e' : T.D.toPre.X ≃+ Q.X), Function.Bijective σ ∧
        jK T.V ≫ spMap σ ≫ spMap κ ≫ spMap ρ ≫ ξ = T.y ≫ j ∧ (∀ k, Associated (σ (κ (ρ (t k)))) (T.ϖ ^ c k)) ∧
        ∀ a b, T.β a b = ∑ k, (c k : ℤ) * δ k (e' a) (e' b) := by
  first | exact @GlobalTheory.Poinc.ChartTraitForm.exists_trait | exact GlobalTheory.Poinc.ChartTraitForm.exists_trait | (intros; apply GlobalTheory.Poinc.ChartTraitForm.exists_trait <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.tauBimult_of_refines_polarised_data : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X), Function.Injective ρ → Half Q ρ D e (fun _ _ => 1) → D.TauBimult := by
  first | exact @GlobalTheory.PolDeg.tauBimult_of_half | exact GlobalTheory.PolDeg.tauBimult_of_half | (intros; apply GlobalTheory.PolDeg.tauBimult_of_half <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_isPullDeg_rescale_both_sides : ∀ {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {θ : R →+* V} {Q : DegPre R} {Q' : DegPre V} (hD : IsPullDeg θ Q Q') (g : Q.X → (FractionRing R)ˣ) (g' : Q'.X → (FractionRing V)ˣ), Nonempty (PsiOn (GlobalTheory.PolDeg.rescale Q g) ⊤) → (∀ y, ∃ a b : R, θ b ≠ 0 ∧ (g (hD.xe y) : FractionRing R) * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a ∧ (g' y : FractionRing V) * algebraMap V (FractionRing V) (θ b) = algebraMap V (FractionRing V) (θ a)) → ∃ h : IsPullDeg θ (GlobalTheory.PolDeg.rescale Q g) (GlobalTheory.PolDeg.rescale Q' g'), h.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ) = hD.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ) ∧ ∀ y, h.xe y = hD.xe y := by
  first | exact @GlobalTheory.RescaleBoth.exists_isPullDeg_rescale | exact GlobalTheory.RescaleBoth.exists_isPullDeg_rescale | (intros; apply GlobalTheory.RescaleBoth.exists_isPullDeg_rescale <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TraitTate

open GlobalTheory.TorusExt GlobalTheory.ArcExt

theorem exists_tate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F), Function.Injective β → ∀ (T : Formalism.L2.Pj.CDVR) (b : O →+* T.V), Function.Injective b → ∀ (D : DegData T.V (maximalIdeal T.V)) [Module (𝓞 E) D.toPre.X] (o : letI := H.starRing; D.toPre.OAct (𝓞 E)), PelOK Dm D.toPre o → (∀ k : ℕ, k ∣ l.M' → ∀ q : QkPt D.toPre (AlgebraicClosure (FractionRing T.V)) k, ∃ p : QkPt D.toPre (FractionRing T.V) k, QkExt (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))) p q) → ∃ (pA : Dm.La → QkPt D.toPre (FractionRing T.V) l.A) (pM : Dm.La → QkPt D.toPre (FractionRing T.V) l.M), ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing T.V) F] (z : O), ((β z : c.F) : ℂ) = zeta l.A → ∃ I : (letI := H.starRing; TateIsoQ Dm D.toPre o F), (I.ζ l.A : F) = algebraMap (FractionRing T.V) F (algebraMap T.V _ (b z)) ∧ (∀ a q, QkExt (algebraMap _ F) (pA a) q → QkPt.Equiv D.toPre F q (I.ev l.A a)) ∧ ∀ a q, QkExt (algebraMap _ F) (pM a) q → QkPt.Equiv D.toPre F q (I.ev l.M a) := by
  intro E _ _ _ H Dm l c O _ β hβ T b hb D _ o hP hrat
  letI := H.starRing
  haveI : CharZero (FractionRing T.V) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective T.V (FractionRing T.V))
  haveI : CharZero (AlgebraicClosure (FractionRing T.V)) :=
    charZero_of_injective_algebraMap (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))).injective
  have hB : D.toPre.TauBimult := D.tau_bimult

  set g : O →+* AlgebraicClosure (FractionRing T.V) :=
    (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))).comp ((algebraMap T.V _).comp b) with hg
  have hginj : Function.Injective g :=
    (algebraMap (FractionRing T.V) _).injective.comp ((IsFractionRing.injective T.V (FractionRing T.V)).comp hb)

  obtain ⟨ζ₀, hζp, hζc, hζA⟩ : ∃ ζ₀ : ℕ → (AlgebraicClosure (FractionRing T.V))ˣ,
      (∀ n, 0 < n → IsPrimitiveRoot (ζ₀ n) n) ∧ (∀ n m, 0 < n → 0 < m → ζ₀ (n * m) ^ m = ζ₀ n) ∧
      ∀ z : O, ((β z : c.F) : ℂ) = zeta l.A → (ζ₀ l.A : AlgebraicClosure (FractionRing T.V)) = g z := by
    by_cases hz : ∃ z : O, ((β z : c.F) : ℂ) = zeta l.A
    · obtain ⟨z, hz⟩ := hz
      have h₀ : IsPrimitiveRoot (((β z : c.F) : ℂ)) l.A := by
        rw [hz]; exact Complex.isPrimitiveRoot_exp l.A l.A_pos.ne'
      have h₁ : IsPrimitiveRoot (β z) l.A :=
        IsPrimitiveRoot.of_map_of_injective (f := c.F.val.toRingHom) h₀ Subtype.val_injective
      have h₂ : IsPrimitiveRoot z l.A := IsPrimitiveRoot.of_map_of_injective (f := β) h₁ hβ
      have h₃ : IsPrimitiveRoot (g z) l.A := h₂.map_of_injective hginj
      obtain ⟨ζ, e₁, e₂, e₃⟩ := GlobalTheory.T.exists_compatible_primitiveRoots_through (AlgebraicClosure (FractionRing T.V)) l.A (g z) l.A_pos h₃
      refine ⟨ζ, e₁, e₂, fun z' hz' => ?_⟩
      have : z' = z := hβ (Subtype.val_injective (hz'.trans hz.symm))
      rw [this]; exact e₃
    · obtain ⟨ζ, e₁, e₂, -⟩ := GlobalTheory.T.exists_compatible_primitiveRoots_through (AlgebraicClosure (FractionRing T.V)) 1 1 one_pos IsPrimitiveRoot.one
      exact ⟨ζ, e₁, e₂, fun z hz' => (hz ⟨z, hz'⟩).elim⟩

  obtain ⟨-, -, -, hF⟩ := hP
  obtain ⟨-, hT⟩ := hF (AlgebraicClosure (FractionRing T.V))
  obtain ⟨I₀, hI₀⟩ := hT ζ₀ hζp hζc

  have hA : l.A ∣ l.M' := Nat.dvd_lcm_right l.M l.A
  have hM : l.M ∣ l.M' := Nat.dvd_lcm_left l.M l.A
  choose pA hpA using fun a => hrat l.A hA (I₀.ev l.A a)
  choose pM hpM using fun a => hrat l.M hM (I₀.ev l.M a)
  refine ⟨pA, pM, fun F _ _ _ z hz => ?_⟩

  let e : AlgebraicClosure (FractionRing T.V) →ₐ[FractionRing T.V] F :=
    IsAlgClosed.lift (M := F) (R := FractionRing T.V) (S := AlgebraicClosure (FractionRing T.V))
  have he : (e : AlgebraicClosure (FractionRing T.V) →+* F).comp
      (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))) = algebraMap (FractionRing T.V) F :=
    RingHom.ext fun x => e.commutes x
  have hK : (algebraMap (AlgebraicClosure (FractionRing T.V)) (AlgebraicClosure (FractionRing T.V))).comp
      (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))) =
      algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V)) := RingHom.ext fun _ => rfl

  have base : ∀ {k : ℕ} (p₀ : QkPt D.toPre (FractionRing T.V) k) (r : QkPt D.toPre (AlgebraicClosure (FractionRing T.V)) k),
      QkExt (algebraMap _ (AlgebraicClosure (FractionRing T.V))) p₀ r →
      ∀ p, QkExt (algebraMap _ (AlgebraicClosure (FractionRing T.V))) p₀ p →
        QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing T.V)) p r := by
    intro k p₀ r hr p hp
    have u := (existsUnique_qkExt hB (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))) hK p₀).unique hp hr
    rw [u]; exact qk_equiv_refl hB r
  refine ⟨tateExt (e : AlgebraicClosure (FractionRing T.V) →+* F) he hB abelianSchemeLaws_all.1 I₀
    (ArcInputCompare.weil_ext hB (e : AlgebraicClosure (FractionRing T.V) →+* F) he), ?_, ?_, ?_⟩
  ·
    show ((Units.map (e : AlgebraicClosure (FractionRing T.V) →+* F).toMonoidHom (I₀.ζ l.A) : Fˣ) : F) = _
    rw [hI₀, Units.coe_map, hζA z hz, hg]
    exact e.commutes _
  · intro a q hq
    exact GlobalTheory.LiftExt.equiv_of_base hB _ he (base (pA a) _ (hpA a)) q hq
  · intro a q hq
    exact GlobalTheory.LiftExt.equiv_of_base hB _ he (base (pM a) _ (hpM a)) q hq

end GlobalTheory.TraitTate
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum



theorem evenOn_of_local : ∀ (R W : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W), IsLocalHom φ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (β : G'.left ⟶ G.left), IsGrpPullback G' G (spMap φ) β → IsProper (pullback.snd G'.hom (jK W)) → ∀ (P : GlobalTheory.UU.CP G) (P' : GlobalTheory.UU.CP G'), LBIso P'.L.L (P.L.L.pull β) → EvenOn P' → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X], Nonempty (GlobalTheory.UU.TQ (thickObj R (maximalIdeal R) 0 G) X) → EvenOn P := by
  intro R W _ _ _ _ _ _ φ hφ G _ _ hG G' _ _ β hβ hp P P' hL hE X _ _ _ ⟨Q₀⟩
  have hG' := GlobalTheory.T.isSemiAbelian_of_isGrpPullback_divisor _ _ _ G G' β hβ hG
  have h3 := GlobalTheory.EvenTriv.surjective_cube_of_generic G' hG' hp
  obtain ⟨w, hw⟩ := GlobalTheory.T.exists_cubicalStructureMap_of_lineBundleIso_rescaled _ _ _ G G' β hβ.1.w (GlobalTheory.UU.TowerEx.toBase_mul hβ hβ.1.w) h3 P P' hL
  obtain ⟨X', _, _, _, Q'₀, P'₀, hlev', σ', hσ'⟩ := hE
  obtain ⟨P₀, hlev⟩ := GlobalTheory.UU.exists_isLevelCP (maximalIdeal R) 0 P
  obtain ⟨ρ, β₀, hβ₀, w₀, hw₀⟩ := GlobalTheory.T.exists_cubicalStructureMap_closedFibre_localHom R W φ hφ G G' β hβ P P' w hw P₀ P'₀ hlev hlev'
  have hk : IsField (R ⧸ maximalIdeal R ^ (0 + 1)) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp (by rw [zero_add, pow_one]; exact IsLocalRing.maximalIdeal.isMaximal R)
  have hk' : IsField (W ⧸ maximalIdeal W ^ (0 + 1)) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp (by rw [zero_add, pow_one]; exact IsLocalRing.maximalIdeal.isMaximal W)
  obtain ⟨i₁, e, he, rfl, hc⟩ := GlobalTheory.T.exists_torus_factor_baseChange_field _ _ hk' ρ _ _ β₀ hβ₀ X X' Q₀ Q'₀
  obtain ⟨σ₁, hσ₁⟩ := GlobalTheory.T.exists_even_cubicalTrivialisation_comp_monHom _ _ _ _ P'₀ Q'₀.i e he σ' hσ'
  have := Q₀.i_hom
  have hi₁ : IsMonHom (e ≫ Q'₀.i) := GlobalTheory.UU.TorusCompat.isMonHom hβ₀ hc
  obtain ⟨σ⟩ := @GlobalTheory.T.exists_cubicalTrivialisation_splitTorus_field _ _ hk _ _ _ X _ _ _ P₀ Q₀.i Q₀.i_hom
  obtain ⟨χ, hχ⟩ := @GlobalTheory.T.exists_character_symmetricDefect_twice_fieldExt _ _ _ _ hk hk' ρ _ _ _ _ _ _ β₀ hβ₀ P₀ P'₀ w₀ hw₀ X _ _ _ Q₀.i (e ≫ Q'₀.i) Q₀.i_hom hi₁ hc σ σ₁ hσ₁
  exact ⟨X, inferInstance, inferInstance, inferInstance, Q₀, P₀, hlev, _, hχ⟩

end GlobalTheory.Mum
end
