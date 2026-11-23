module

public import Development.EtaleCohomology.EtaleSheaves.Bundle053
public import Development.EtaleCohomology.EtaleSheaves.Bundle054
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open CategoryTheory AlgebraicGeometry Polynomial LateralTheory.E.t_E2Cut LateralTheory.E.FibStalkPf

namespace LateralTheory.E.StalkSHSPf

theorem germs (S : Scheme.{0}) (x : S) (c : ℕ → S.presheaf.stalk x) (s : Finset ℕ) :
    ∃ (U : S.Opens) (_ : IsAffineOpen U) (hx : x ∈ U) (f : ℕ → Γ(S, U)),
      ∀ i ∈ s, (S.presheaf.germ U x hx).hom (f i) = c i := by
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨U, hU, hx, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
      (show x ∈ (⊤ : S.Opens) from trivial)
    exact ⟨U, hU, hx, fun _ => 0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨U, hU, hx, f, hf⟩ := ih
    obtain ⟨V, hxV, g, hg⟩ := S.presheaf.exists_germ_eq (c a)
    obtain ⟨W, hW, hxW, hWUV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
      (show x ∈ U ⊓ V from ⟨hx, hxV⟩)
    refine ⟨W, hW, hxW, fun i => if i = a then (S.presheaf.map (homOfLE (hWUV.trans inf_le_right)).op).hom g
       else (S.presheaf.map (homOfLE (hWUV.trans inf_le_left)).op).hom (f i), ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · simp only [if_true]
      rw [← hg, ← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]
    · have : i ≠ a := fun h => ha (h ▸ hi)
      simp only [this, if_false]
      rw [← hf i hi, ← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]

theorem stalkAIC : StalkAIC := by
  intro S hS x p hm hd
  obtain ⟨U, hU, hx, f, hf⟩ := germs S x (fun i => p.coeff i) (Finset.range (p.natDegree + 1))
  have hl : p ∈ Polynomial.lifts (S.presheaf.germ U x hx).hom := by
    refine (lifts_iff_coeff_lifts p).2 fun i => ?_
    by_cases hi : i < p.natDegree + 1
    · exact ⟨f i, hf i (Finset.mem_range.2 hi)⟩
    · exact ⟨0, by rw [map_zero, coeff_eq_zero_of_natDegree_lt (by omega)]⟩
  obtain ⟨P, hP, hdeg, hPm⟩ := lifts_and_natDegree_eq_and_monic hl hm
  obtain ⟨r, hr⟩ := hS.2 U hU ⟨x, hx⟩ P hPm (by omega)
  exact ⟨(S.presheaf.germ U x hx).hom r, by rw [← hP, Polynomial.eval_map, eval₂_at_apply, hr, map_zero]⟩

end LateralTheory.E.StalkSHSPf
end
end

section

namespace LateralTheory.E.PartDirectedPf

variable {A : Type} [CommRing A]

theorem prod_eq_zero_of_ne {a b c d : A} (P Q : PartDiagCut.Part A)
    (ha : a ∈ P.blocks) (hb : b ∈ Q.blocks) (hc : c ∈ P.blocks) (hd : d ∈ Q.blocks)
    (hne : (a, b) ≠ (c, d)) : (a * b) * (c * d) = 0 := by
  by_cases hac : a = c
  · have hbd : b ≠ d := by
      intro h; exact hne (by rw [hac, h])
    have := Q.orth b hb d hd hbd
    calc a * b * (c * d) = a * c * (b * d) := by ring
      _ = 0 := by rw [this, mul_zero]
  · have := P.orth a ha c hc hac
    calc a * b * (c * d) = a * c * (b * d) := by ring
      _ = 0 := by rw [this, zero_mul]

open Classical in
noncomputable def meet (P Q : PartDiagCut.Part A) : PartDiagCut.Part A where
  blocks := ((P.blocks ×ˢ Q.blocks).filter (fun x => x.1 * x.2 ≠ 0)).image (fun x => x.1 * x.2)
  idem := by
    intro e he
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product] at he
    obtain ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, hne⟩, rfl⟩ := he
    exact ⟨(P.idem a ha).1.mul (Q.idem b hb).1, hne⟩
  orth := by
    intro e he e' he' hee
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product] at he he'
    obtain ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, _⟩, rfl⟩ := he
    obtain ⟨⟨c, d⟩, ⟨⟨hc, hd⟩, _⟩, rfl⟩ := he'
    refine prod_eq_zero_of_ne P Q ha hb hc hd ?_
    intro h; apply hee; simp only [Prod.mk.injEq] at h; rw [h.1, h.2]
  sum_eq := by
    rw [Finset.sum_image]
    · rw [Finset.sum_filter_ne_zero, Finset.sum_product, ← Finset.sum_mul_sum,
        P.sum_eq, Q.sum_eq, mul_one]
    · intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hx hy
      by_contra hne
      have h0 := prod_eq_zero_of_ne P Q hx.1.1 hx.1.2 hy.1.1 hy.1.2 hne
      change x.1 * x.2 = y.1 * y.2 at hxy
      rw [← hxy] at h0
      have hid : IsIdempotentElem (x.1 * x.2) := (P.idem _ hx.1.1).1.mul (Q.idem _ hx.1.2).1
      exact hx.2 (by rw [← hid.eq]; exact h0)

theorem le_meet_left (P Q : PartDiagCut.Part A) : P ≤ meet P Q := by
  intro e he
  simp only [meet, Finset.mem_image, Finset.mem_filter, Finset.mem_product] at he
  obtain ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, _⟩, rfl⟩ := he
  refine ⟨a, ha, ?_⟩
  calc a * b * a = a * a * b := by ring
    _ = a * b := by rw [(P.idem a ha).1.eq]

theorem le_meet_right (P Q : PartDiagCut.Part A) : Q ≤ meet P Q := by
  intro e he
  simp only [meet, Finset.mem_image, Finset.mem_filter, Finset.mem_product] at he
  obtain ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, _⟩, rfl⟩ := he
  refine ⟨b, hb, ?_⟩
  calc a * b * b = a * (b * b) := by ring
    _ = a * b := by rw [(Q.idem b hb).1.eq]

theorem part_nonempty (A : Type) [CommRing A] : Nonempty (PartDiagCut.Part A) := by
  by_cases h : Nontrivial A
  · exact ⟨{ blocks := {1}
             idem := by intro e he; rw [Finset.mem_singleton] at he; subst he; exact ⟨IsIdempotentElem.one, one_ne_zero⟩
             orth := by intro e he e' he' hne; rw [Finset.mem_singleton] at he he'; exact absurd (he.trans he'.symm) hne
             sum_eq := by simp }⟩
  · rw [not_nontrivial_iff_subsingleton] at h
    exact ⟨{ blocks := ∅
             idem := by simp
             orth := by simp
             sum_eq := Subsingleton.elim _ _ }⟩

theorem PartDirected_of : LateralTheory.E.PartDiagCut.PartDirected := by
  intro A _
  exact ⟨⟨fun P Q => ⟨meet P Q, le_meet_left P Q, le_meet_right P Q⟩⟩, part_nonempty A⟩

end LateralTheory.E.PartDirectedPf
end

section

noncomputable section
open LateralTheory.E.PartDiagCut

namespace LateralTheory.E.DiagCompPf

theorem block_unique {A : Type} [CommRing A] (P R : PartDiagCut.Part A) (e : A) (he : e ∈ R.1) (a b : P.1)
    (ha : e * a.1 = e) (hb : e * b.1 = e) : a = b := by
  by_contra hne
  have hne' : a.1 ≠ b.1 := fun h => hne (Subtype.ext h)
  have h0 : a.1 * b.1 = 0 := P.orth a.1 a.2 b.1 b.2 hne'
  have : e = 0 := by
    calc e = e * a.1 * b.1 := by rw [ha, hb]
      _ = e * (a.1 * b.1) := by ring
      _ = 0 := by rw [h0, mul_zero]
  exact (R.idem e he).2 this

theorem par_trans {B : Type} [CommRing B] (I : Ideal B) {P Q R : PartDiagCut.Part (B ⧸ I)} (h1 : P ≤ Q) (h2 : Q ≤ R) (e : R.1) :
    par (h1.trans h2) e = par h1 (par h2 e) := by
  apply block_unique P R e.1 e.2
  · exact par_spec _ e
  · calc e.1 * (par h1 (par h2 e)).1 = e.1 * (par h2 e).1 * (par h1 (par h2 e)).1 := by rw [par_spec h2 e]
      _ = e.1 * ((par h2 e).1 * (par h1 (par h2 e)).1) := by ring
      _ = e.1 := by rw [par_spec h1 (par h2 e), par_spec h2 e]

theorem DiagComp_of : DiagComp := by
  intro B _ I P Q R h1 h2
  ext x e
  have key : ∀ (g g' : B →+* B), g = g' → ∀ (a b : P.1), a = b →
      ∀ (hA : S I a.1 ≤ (S I e.1).comap g) (hD : S I b.1 ≤ (S I e.1).comap g'),
      IsLocalization.map (M := S I a.1) (T := S I e.1) (Localization (S I e.1)) g hA (x a)
      = IsLocalization.map (M := S I b.1) (T := S I e.1) (Localization (S I e.1)) g' hD (x b) := by
    rintro g _ rfl a _ rfl hA hD; rfl
  simp only [stageMap, RingHom.comp_apply, RingHom.pi_apply, Pi.evalRingHom_apply]
  erw [IsLocalization.map_map]
  exact key _ _ (RingHom.id_comp _).symm _ _ (par_trans I h1 h2 e) _ _

end LateralTheory.E.DiagCompPf
end
end

section

noncomputable section
open LateralTheory.E.PartDiagCut

namespace LateralTheory.E.DiagIdPf

theorem par_self {A : Type} [CommRing A] {P : LateralTheory.E.PartDiagCut.Part A} (h : P ≤ P) (e : P.1) : par h e = e := by
  apply Subtype.ext
  by_contra hne
  have h1 := par_spec h e
  have h2 := P.orth e.1 e.2 (par h e).1 (par h e).2 (fun h' => hne h'.symm)
  exact (P.idem e.1 e.2).2 (h1.symm.trans h2)

theorem aux {B : Type} [CommRing B] (I : Ideal B) (P : LateralTheory.E.PartDiagCut.Part (B ⧸ I)) (x : PiLocalization₂ I P) (e0 e : P.1) (hee : e0 = e)
    (hle : S I e0.1 ≤ (S I e.1).comap (RingHom.id B)) :
    IsLocalization.map (M := S I e0.1) (T := S I e.1) (Localization (S I e.1)) (RingHom.id B) hle (x e0) = x e := by
  subst hee
  exact IsLocalization.map_id _ _

theorem DiagId_of : LateralTheory.E.PartDiagCut.DiagId := by
  intro B _ I P h
  refine RingHom.ext fun x => funext fun e => ?_
  simp only [stageMap, RingHom.pi_apply, RingHom.comp_apply, Pi.evalRingHom_apply, RingHom.id_apply]
  exact aux I P x (par h e) e (par_self h e) _

end LateralTheory.E.DiagIdPf
end
end

section

namespace LateralTheory.E.DiagNatPf
open LateralTheory.E.PartDiagCut

theorem DiagNat_of : LateralTheory.E.PartDiagCut.DiagNat := by
  intro B _ I P Q h
  apply RingHom.ext
  intro b
  funext e
  simp only [stageMap, βP, RingHom.comp_apply, RingHom.pi_apply, Pi.evalRingHom_apply]
  exact (IsLocalization.map_eq (S := Localization (S I (par h e).1)) _ b).trans (by rfl)

end LateralTheory.E.DiagNatPf
end

section

noncomputable section
open LateralTheory.E.PartDiagCut

namespace LateralTheory.E.PartAPf

variable {B : Type} [CommRing B]

theorem one_mem_S (I : Ideal B) {e : B ⧸ I} {u : B} (hu : Ideal.Quotient.mk I u = e) (he : IsIdempotentElem e) :
    u ∈ S I e := ⟨1, by rw [hu, mul_one, he.eq]⟩

theorem mem_map_of_comp (I : Ideal B) (P : PartDiagCut.Part (B ⧸ I)) (z : PiLocalization₂ I P)
    (hz : ∀ e : P.1, z e ∈ I.map (algebraMap B (Localization (S I e.1)))) : z ∈ I.map (βP I P) := by
  classical
  choose a ha using fun e : P.1 =>
    (IsLocalization.mem_map_algebraMap_iff (S I e.1) (Localization (S I e.1))).1 (hz e)
  have key : z = ∑ e : P.1, βP I P ((a e).1 : B) *
      Pi.single e (IsLocalization.mk' (Localization (S I e.1)) (1 : B) (a e).2) := by
    funext e'
    rw [Finset.sum_apply, Finset.sum_eq_single e']
    · simp only [Pi.mul_apply, Pi.single_eq_same, βP, RingHom.pi_apply]
      rw [← IsLocalization.mk'_eq_mul_mk'_one, IsLocalization.eq_mk'_iff_mul_eq]
      exact ha e'
    · intro e _ hne
      simp [Pi.single_eq_of_ne' hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [key]
  exact Ideal.sum_mem _ fun e _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (a e).1.2)

theorem comp_mem (I : Ideal B) (P : PartDiagCut.Part (B ⧸ I)) (z : PiLocalization₂ I P) (hz : z ∈ I.map (βP I P)) (e : P.1) :
    z e ∈ I.map (algebraMap B (Localization (S I e.1))) := by
  have h := Ideal.mem_map_of_mem (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e) hz
  rw [Ideal.map_map] at h
  exact h

theorem sum_mul_single (I : Ideal B) (P : PartDiagCut.Part (B ⧸ I)) (c : P.1 → B ⧸ I) (e' : P.1) :
    (∑ e : P.1, c e * e.1) * e'.1 = c e' * e'.1 := by
  classical
  rw [Finset.sum_mul, Finset.sum_eq_single e']
  · rw [mul_assoc, (P.idem e'.1 e'.2).1.eq]
  · intro e _ hne
    rw [mul_assoc, P.orth e.1 e.2 e'.1 e'.2 (fun h => hne (Subtype.ext h)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem PartA_of : PartA := by
  intro B _ I P
  classical
  constructor
  · apply Ideal.quotientMap_injective'
    intro x hx
    rw [Ideal.mem_comap] at hx
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hcomp : ∀ e : P.1, Ideal.Quotient.mk I x * e.1 = 0 := by
      intro e
      have h := comp_mem I P _ hx e
      obtain ⟨⟨i, s⟩, hs⟩ := (IsLocalization.mem_map_algebraMap_iff (S I e.1) (Localization (S I e.1))).1 h
      simp only [βP, RingHom.pi_apply] at hs
      rw [← map_mul] at hs
      obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (S I e.1) (Localization (S I e.1))).1 hs
      have hq := congrArg (Ideal.Quotient.mk I) hc
      rw [map_mul, map_mul, map_mul, Ideal.Quotient.eq_zero_iff_mem.2 i.2, mul_zero] at hq
      obtain ⟨t, ht⟩ := c.2
      obtain ⟨t', ht'⟩ := s.2
      calc Ideal.Quotient.mk I x * e.1
          = Ideal.Quotient.mk I x * ((Ideal.Quotient.mk I c * t * e.1) * (Ideal.Quotient.mk I s * t' * e.1)) := by
            rw [ht, ht', (P.idem e.1 e.2).1.eq]
        _ = (Ideal.Quotient.mk I c * (Ideal.Quotient.mk I x * Ideal.Quotient.mk I s)) * (t * t' * e.1 * e.1) := by ring
        _ = 0 := by rw [hq, zero_mul]
    calc Ideal.Quotient.mk I x = Ideal.Quotient.mk I x * ∑ e ∈ P.1, e := by rw [P.sum_eq, mul_one]
      _ = ∑ e : P.1, Ideal.Quotient.mk I x * e.1 := by
          rw [Finset.mul_sum, ← Finset.sum_coe_sort P.1]
      _ = 0 := Finset.sum_eq_zero fun e _ => hcomp e
  · intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hB : ∀ e : P.1, ∃ (b : B) (s : S I e.1), IsLocalization.mk' (Localization (S I e.1)) b s = y e :=
      fun e => by
        obtain ⟨⟨b, s⟩, h⟩ := IsLocalization.mk'_surjective (S I e.1) (y e)
        exact ⟨b, s, h⟩
    choose b s hbs using hB
    have hS : ∀ e : P.1, ∃ t, Ideal.Quotient.mk I (s e : B) * t * e.1 = e.1 := fun e => (s e).2
    choose t ht using hS
    choose τ hτ using fun e : P.1 => Ideal.Quotient.mk_surjective (t e)
    choose ε hε using fun e : P.1 => Ideal.Quotient.mk_surjective e.1
    refine ⟨Ideal.Quotient.mk _ (∑ e : P.1, b e * τ e * ε e), ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
    apply mem_map_of_comp
    intro e'
    set x := ∑ e : P.1, b e * τ e * ε e
    have hεS : ε e' ∈ S I e'.1 := one_mem_S I (hε e') (P.idem e'.1 e'.2).1
    rw [IsLocalization.mem_map_algebraMap_iff (S I e'.1) (Localization (S I e'.1))]
    refine ⟨⟨⟨(x * s e' - b e') * ε e', ?_⟩, s e' * ⟨ε e', hεS⟩⟩, ?_⟩
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_sub, map_mul, hε]
      have hx : Ideal.Quotient.mk I x = ∑ e : P.1, (Ideal.Quotient.mk I (b e) * t e) * e.1 := by

        simp only [x, map_sum, map_mul, hτ, hε]
      rw [sub_mul, mul_right_comm, hx, sum_mul_single]
      calc Ideal.Quotient.mk I (b e') * t e' * e'.1 * Ideal.Quotient.mk I (s e') - Ideal.Quotient.mk I (b e') * e'.1
          = Ideal.Quotient.mk I (b e') * (Ideal.Quotient.mk I (s e') * t e' * e'.1) - Ideal.Quotient.mk I (b e') * e'.1 := by ring
        _ = 0 := by rw [ht e', sub_self]
    · simp only [Pi.sub_apply, βP, RingHom.pi_apply, Submonoid.coe_mul, map_mul, map_sub, ← hbs e']
      rw [sub_mul, sub_mul, ← mul_assoc (IsLocalization.mk' _ _ _), IsLocalization.mk'_spec]
      ring

end LateralTheory.E.PartAPf
end
end

section

noncomputable section
open LateralTheory.E.PartDiagCut

namespace LateralTheory.E.PartBPf

theorem comp_mem {B : Type} [CommRing B] (I : Ideal B) (P : PartDiagCut.Part (B ⧸ I)) (x : PiLocalization₂ I P)
    (hx : x ∈ I.map (βP I P)) (e : P.1) :
    x e ∈ I.map (algebraMap B (Localization (S I e.1))) := by
  have h1 : (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e) x ∈
      (I.map (βP I P)).map (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e) :=
    Ideal.mem_map_of_mem _ hx
  rw [Ideal.map_map] at h1
  have h2 : (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e).comp (βP I P) =
      algebraMap B (Localization (S I e.1)) := by
    ext b; rfl
  rw [h2] at h1
  exact h1

theorem comp_unit {B : Type} [CommRing B] (I : Ideal B) (e : B ⧸ I) (y : Localization (S I e))
    (hy : y ∈ I.map (algebraMap B (Localization (S I e)))) : IsUnit (1 + y) := by
  obtain ⟨⟨⟨i, hi⟩, ⟨s, hs⟩⟩, h⟩ := (IsLocalization.mem_map_algebraMap_iff (S I e) _).1 hy
  simp only at h
  have hsi : s + i ∈ S I e := by
    obtain ⟨t, ht⟩ := hs
    refine ⟨t, ?_⟩
    have : Ideal.Quotient.mk I i = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hi
    rw [map_add (f := _), this, add_zero]; exact ht
  have hu : IsUnit ((1 + y) * algebraMap B _ s) := by
    rw [add_mul, one_mul, h, ← map_add (f := _)]
    exact IsLocalization.map_units (Localization (S I e)) ⟨s + i, hsi⟩
  exact isUnit_of_mul_isUnit_left hu

theorem PartB_of : LateralTheory.E.PartDiagCut.PartB := by
  intro B _ I P x hx
  rw [Pi.isUnit_iff]
  intro e
  exact comp_unit I e.1 (x e) (comp_mem I P x hx e)

end LateralTheory.E.PartBPf
end
end

section

noncomputable section
open GlobalTheory.EtC

namespace LateralTheory.E.StageProdPf
open LateralTheory.E.PartDiagCut

theorem zero_not_mem_S {B : Type} [CommRing B] (I : Ideal B) (P : LateralTheory.E.PartDiagCut.Part (B ⧸ I)) (e : P.1) :
    (0 : B) ∉ S I e.1 := by
  rintro ⟨t, ht⟩
  simp only [map_zero, zero_mul] at ht
  exact (P.idem e.1 e.2).2 ht.symm

theorem StageProd_of (hloc : LateralTheory.E.HensCut.LocAIC) : LateralTheory.E.PartDiagCut.StageProd := by
  intro q B _ _ I hB hq P
  let R : Fin P.1.card → Type := fun k => Localization (S I (P.1.equivFin.symm k).1)
  refine ⟨P.1.card, R, fun k => inferInstance, fun k => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hloc B (S I (P.1.equivFin.symm k).1) (zero_not_mem_S I P _) hB
    refine ⟨h1, h2, ?_⟩
    have := hq.map (algebraMap B (R k))
    rwa [map_natCast] at this
  · exact ⟨(RingEquiv.piCongrLeft (fun e : P.1 => Localization (S I e.1)) P.1.equivFin.symm).symm⟩

end LateralTheory.E.StageProdPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.TateTwistZeroAugmentationBijective

def Aug : Prop := ∀ q : ℕ, ∃ φ : ∀ T : Scheme.{0}, Sec (tw q 0) T →+ LocallyConstant T (ZMod q),
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec (tw q 0) U), φ V (Sec.res g x) = (φ U x).comap g.base.hom) ∧
  ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), φ U (twGen 0 ζ) = 1

def AugBij : Prop := ∀ (q : ℕ) (φ : ∀ T : Scheme.{0}, Sec (tw q 0) T →+ LocallyConstant T (ZMod q)),
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec (tw q 0) U), φ V (Sec.res g x) = (φ U x).comap g.base.hom) →
  (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), φ U (twGen 0 ζ) = 1) →
  ∀ T : Scheme.{0}, IsUnit (q : Γ(T, ⊤)) → Function.Bijective (φ T)

theorem Tw0_of (hA : Aug) (hB : AugBij) : LateralTheory.E.LCIsoPf.Tw0 := by
  intro q
  obtain ⟨φ, hnat, hgen⟩ := hA q
  have hb := hB q φ hnat hgen
  refine ⟨fun T hT => (AddEquiv.ofBijective (φ T) (hb T hT)).symm, ?_⟩
  intro V U g hV hU a
  apply (hb V hV).1
  have h1 : ∀ (T : Scheme.{0}) (hT : IsUnit (q : Γ(T, ⊤))) (b : LocallyConstant T (ZMod q)),
      φ T ((AddEquiv.ofBijective (φ T) (hb T hT)).symm b) = b := fun T hT b =>
    (AddEquiv.ofBijective (φ T) (hb T hT)).apply_symm_apply b
  rw [hnat, h1 U hU, h1 V hV]

end LateralTheory.E.TateTwistZeroAugmentationBijective
end
end
