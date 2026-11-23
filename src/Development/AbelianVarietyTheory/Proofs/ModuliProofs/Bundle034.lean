module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Mathlib.Algebra.AffineMonoid.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle023
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
theorem _root_.GlobalTheory.Models.sup_mul_sup_eq_of_coprime {R : Type} [CommRing R] {I J N : Ideal R}
    (h : I ⊔ J = ⊤) (hN : I * J ≤ N) : (I ⊔ N) * (J ⊔ N) = N := by
  apply le_antisymm
  · rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
    exact sup_le (sup_le hN (Ideal.mul_le_inf.trans inf_le_right))
      (sup_le (Ideal.mul_le_inf.trans inf_le_left) (Ideal.mul_le_inf.trans inf_le_left))
  · calc N = N * (I ⊔ J) := by rw [h, Ideal.mul_top]
      _ = N * I ⊔ N * J := Ideal.mul_sup _ _ _
      _ ≤ (I ⊔ N) * (J ⊔ N) := sup_le
          (by rw [mul_comm]; exact Ideal.mul_mono le_sup_left le_sup_right)
          (Ideal.mul_mono le_sup_right le_sup_left)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def divisorLevel (l : Level H) (m : ℕ) (hm : m ∣ l.M) (h3 : 3 ≤ m) : Level H where
  M := m
  three_le := h3
  odd := l.odd.of_dvd_nat hm
  Mb := l.Mb ⊔ Ideal.span {(m : 𝓞 E)}
  fromK := by
    apply le_antisymm
    · apply sup_le
      · refine l.fromK.le.trans (Ideal.span_mono ?_)
        rintro a ⟨ha, ha'⟩
        exact ⟨Ideal.mem_sup_left ha, ha'⟩
      · apply Ideal.span_mono
        rintro a rfl
        exact ⟨Ideal.mem_sup_right (Ideal.mem_span_singleton_self _), natCast_mem _ m⟩
    · exact Ideal.span_le.mpr fun a ha => ha.1
  prod := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast]
    refine sup_mul_sup_eq_of_coprime l.coprime ?_
    rw [l.prod]
    exact Ideal.span_singleton_le_span_singleton.mpr (Nat.cast_dvd_cast hm)
  coprime := by
    rw [eq_top_iff, ← l.coprime]
    exact sup_le_sup le_sup_left (Ideal.map_mono le_sup_left)
  A := 1
  A_pos := one_pos

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in
private theorem level_ext' {a b : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (hM : a.M = b.M) (hMb : a.Mb = b.Mb)
    (hA : a.A = b.A) : a = b := by
  cases a
  cases b
  simp only at hM hMb hA
  subst hM hMb hA
  rfl


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in
theorem _root_.GlobalTheory.Models.primeToPart_spec : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p : ℕ), p.Prime →
    (∀ l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H, l.GoodAt p → ∃ l₀ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H, _root_.GlobalTheory.Models.IsPrimeToPart l₀ l p) ∧
    (∀ l l₀ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H, _root_.GlobalTheory.Models.IsPrimeToPart l₀ l p → l₀.Dvd l ∧ l₀.M.Coprime p ∧
      ∀ l₀' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H, _root_.GlobalTheory.Models.IsPrimeToPart l₀' l p → l₀' = l₀) ∧
    ∀ l l' l₀ l₀' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H, _root_.GlobalTheory.Models.IsPrimeToPart l₀ l p → _root_.GlobalTheory.Models.IsPrimeToPart l₀' l' p → l.Dvd l' →
      l₀.Dvd l₀' := by
  intro E _ _ _ H p hp
  refine ⟨fun l hl => ?_, fun l l₀ h₀ => ?_, fun l l' l₀ l₀' h₀ h₀' hd => ?_⟩
  · unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level.GoodAt at hl
    exact ⟨_root_.GlobalTheory.Models.divisorLevel l _ (Nat.ordCompl_dvd _ _) hl, rfl, rfl, rfl⟩
  · unfold _root_.GlobalTheory.Models.IsPrimeToPart at h₀ ⊢
    obtain ⟨hA, hM, hMb⟩ := h₀
    have hl : l.M ≠ 0 := by have := l.three_le; omega
    refine ⟨?_, ?_, fun l₀' ⟨hA', hM', hMb'⟩ => ?_⟩
    · unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level.Dvd
      refine ⟨hM ▸ Nat.ordCompl_dvd _ _, hMb ▸ le_sup_left, hA ▸ one_dvd _⟩
    · rw [hM]
      exact (Nat.coprime_ordCompl hp hl).symm
    · have e : l₀'.M = l₀.M := hM'.trans hM.symm
      exact level_ext' e (by rw [hMb', hMb, e]) (hA'.trans hA.symm)
  · unfold _root_.GlobalTheory.Models.IsPrimeToPart at h₀ h₀'
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level.Dvd at hd ⊢
    obtain ⟨hA, hM, hMb⟩ := h₀
    obtain ⟨hA', hM', hMb'⟩ := h₀'
    obtain ⟨hdM, hdMb, -⟩ := hd
    have hmd : l₀.M ∣ l₀'.M := by
      rw [hM, hM']
      exact Nat.ordCompl_dvd_ordCompl_of_dvd hdM p
    refine ⟨hmd, ?_, by rw [hA]; exact one_dvd _⟩
    rw [hMb, hMb']
    exact sup_le (hdMb.trans le_sup_left)
      (le_sup_of_le_right (Ideal.span_singleton_le_span_singleton.mpr (Nat.cast_dvd_cast hmd)))

end GlobalTheory.Models
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

theorem isFinite_lift_comp {X X' X'' S S' S'' : Scheme.{0}} {s : X ⟶ S} {s' : X' ⟶ S'} {s'' : X'' ⟶ S''}
    {g : S' ⟶ S} {g' : S'' ⟶ S'} {g'' : S'' ⟶ S} (hg : g'' = g' ≫ g) {p : X' ⟶ X} {p' : X'' ⟶ X'}
    (w : p ≫ s = s' ≫ g) (w' : p' ≫ s' = s'' ≫ g') (w'' : (p' ≫ p) ≫ s = s'' ≫ g'')
    (h : IsFinite (pullback.lift p s' w)) (h' : IsFinite (pullback.lift p' s'' w')) :
    IsFinite (pullback.lift (p' ≫ p) s'' w'') := by
  subst hg
  obtain ⟨θ, hθ1, hθ2⟩ : ∃ θ : pullback s' g' ⟶ pullback s (g' ≫ g),
      θ ≫ pullback.fst s (g' ≫ g) = pullback.fst s' g' ≫ p ∧ θ ≫ pullback.snd s (g' ≫ g) = pullback.snd s' g' :=
    ⟨pullback.lift (pullback.fst s' g' ≫ p) (pullback.snd s' g')
      (by rw [Category.assoc, w, pullback.condition_assoc]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨κ, hκ1, hκ2⟩ : ∃ κ : pullback s (g' ≫ g) ⟶ pullback s g,
      κ ≫ pullback.fst s g = pullback.fst s (g' ≫ g) ∧ κ ≫ pullback.snd s g = pullback.snd s (g' ≫ g) ≫ g' :=
    ⟨pullback.lift (pullback.fst s (g' ≫ g)) (pullback.snd s (g' ≫ g) ≫ g')
      (by rw [Category.assoc]; exact pullback.condition), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

  have hfac : pullback.lift (p' ≫ p) s'' w'' = pullback.lift p' s'' w' ≫ θ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hθ1, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [Category.assoc, hθ2, pullback.lift_snd]

  have hright : IsPullback (pullback.snd s (g' ≫ g)) κ g' (pullback.snd s g) := by
    refine IsPullback.of_bot ?_ hκ2.symm (IsPullback.of_hasPullback s g).flip
    rw [hκ1]
    exact (IsPullback.of_hasPullback s (g' ≫ g)).flip

  have hsq : IsPullback θ (pullback.fst s' g') κ (pullback.lift p s' w) := by
    refine IsPullback.of_right ?_ ?_ hright
    · rw [hθ2, pullback.lift_snd]
      exact (IsPullback.of_hasPullback s' g').flip
    · apply pullback.hom_ext
      · simp only [Category.assoc, hκ1, hθ1, pullback.lift_fst]
      · simp only [Category.assoc, hκ2, reassoc_of% hθ2, pullback.lift_snd, pullback.condition]
  have hfin : IsFinite θ := MorphismProperty.of_isPullback (P := @IsFinite) hsq.flip h
  rw [hfac]
  infer_instance

theorem above_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (U'' : Scheme.{0}) (F'' O'' : Type) [Field F''] [CommRing O''] (c'' : U'' ⟶ Sp F'') (t'' : SAB H U'') (β'' : O'' →+* F'') (C : Cpt c t β) (C' : Cpt c' t' β') (C'' : Cpt c'' t'' β'') (b : O →+* O') (b' : O' →+* O'') (r : U' ⟶ U) (ν : SABMap t' t r) (r' : U'' ⟶ U') (ν' : SABMap t'' t' r') (ν'' : SABMap t'' t (r' ≫ r)) (a : C'.Above C b r ν) (a' : C''.Above C' b' r' ν'), ν''.φ = ν'.φ ≫ ν.φ → ∃ a'' : C''.Above C (b'.comp b) (r' ≫ r) ν'', a''.π = a'.π ≫ a.π ∧ a''.mu.φ = a'.mu.φ ≫ a.mu.φ := by
  intro E _ _ _ H U F O _ _ c t β U' F' O' _ _ c' t' β' U'' F'' O'' _ _ c'' t'' β'' C C' C'' b b' r ν r' ν' ν'' a a' hν
  obtain ⟨mu, hmu⟩ := sabComp pullCubComp E H _ _ _ C.t C'.t C''.t a.π a'.π a.mu a'.mu
  have hsp : spMap (b'.comp b) = spMap b' ≫ spMap b := by
    unfold spMap
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hover : (a'.π ≫ a.π) ≫ C.s = C''.s ≫ spMap (b'.comp b) := by
    rw [hsp, Category.assoc, a.π_over, ← Category.assoc, a'.π_over, Category.assoc]
  refine ⟨⟨a'.π ≫ a.π, hover, isFinite_lift_comp hsp a.π_over a'.π_over hover a.fin a'.fin, mu, ?_, ?_⟩, rfl, hmu⟩
  · rw [← Category.assoc, a'.j_comm, Category.assoc, a.j_comm, Category.assoc]
  · rw [hmu, hν, ← Category.assoc, a'.φ_comm, Category.assoc, a.φ_comm, Category.assoc]

end GlobalTheory.Models
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem finrank_int_eq_mul (O M : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Free ℤ O] [Module.Finite ℤ O]
    [AddCommGroup M] [Module O M] [Module.Finite O M] :
    Module.finrank ℤ M = Module.finrank ℤ O * Module.finrank O M := by
  have : Module.Finite ℤ M := Module.Finite.trans O M
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := O) (M := M) le_rfl
  let F : Submodule O M := Submodule.span O (Set.range f)
  let bF : Module.Basis (Fin (Module.finrank O M)) O F := Module.Basis.span hf
  have : Module.Free O F := Module.Free.of_basis bF
  have h1 : Module.finrank O F = Module.finrank O M := by
    rw [Module.finrank_eq_card_basis bF, Fintype.card_fin]
  have h2 : Module.finrank O (M ⧸ F) = 0 := by
    have := Submodule.finrank_quotient_add_finrank F
    omega
  have h3 : Module.finrank ℤ (M ⧸ F.restrictScalars ℤ) = 0 := by
    rw [Module.finrank_eq_zero_iff] at h2 ⊢
    intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨a, ha, hax⟩ := h2 (Submodule.Quotient.mk x)
    obtain ⟨r, hr, c, hc⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) a).exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero ha)
    refine ⟨r, hr, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hax ⊢
    rw [Submodule.restrictScalars_mem, ← algebraMap_smul O r x, hc, mul_comm, mul_smul]
    exact F.smul_mem c hax
  have h4 := Submodule.finrank_quotient_add_finrank (F.restrictScalars ℤ)
  have h5 : Module.finrank ℤ (F.restrictScalars ℤ) = Module.finrank ℤ O * Module.finrank O F :=
    (Module.finrank_mul_finrank ℤ O F).symm
  rw [← h4, h3, zero_add, h5, h1]

theorem finrank_int_lattice {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) :
    Module.finrank ℤ D.La = 2 * (Module.finrank ℚ E / 2 * (D.p + D.q)) := by
  have := D.fin
  rw [finrank_int_eq_mul (𝓞 E) D.La, D.rank, RingOfIntegers.rank, IsTotallyComplex.finrank E,
    Nat.mul_div_cancel_left _ two_pos, Nat.mul_assoc]

theorem exists_equiv_stdSymp {M : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    {B : LinearMap.BilinForm ℤ M} (hB : B.IsAlt) (hp : Function.Bijective B) {g : ℕ}
    (hg : Module.finrank ℤ M = 2 * g) :
    ∃ bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] M,
      ∀ i j, B (bas (Pi.single i 1)) (bas (Pi.single j 1)) = Out.stdSymp g i j := by
  obtain ⟨b, hb⟩ := exists_isSymplecticBasis_of_finrank hB hp hg
  let e : Fin g ⊕ Fin g ≃ Fin (2 * g) := finSumFinEquiv.trans (finCongr (two_mul g).symm)
  have hl : ∀ i, ((e (Sum.inl i) : Fin (2 * g)) : ℕ) = i := fun i => by simp [e]
  have hr : ∀ i, ((e (Sum.inr i) : Fin (2 * g)) : ℕ) = g + i := fun i => by simp [e]; omega
  refine ⟨(b.reindex e).equivFun.symm, fun i j => ?_⟩
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  have hs : ∀ k, (b.reindex e).equivFun.symm (Pi.single (e k) 1) = b k := fun k => by
    rw [Module.Basis.equivFun_symm_apply]; simp [Pi.single_apply]
  rw [hs, hs, Out.stdSymp]
  rcases i with i | i <;> rcases j with j | j <;> have := i.2 <;> have := j.2
  · rw [hb.left_left, hl, hl, if_neg (by omega), if_neg (by omega)]
  · rw [hb.left_right, hl, hr]
    by_cases h : i = j
    · subst h; rw [if_pos rfl, if_pos (by omega)]
    · have : (i : ℕ) ≠ j := fun a => h (Fin.ext a)
      rw [if_neg h, if_neg (by omega), if_neg (by omega)]
  · rw [hb.right_left hB, hl, hr]
    by_cases h : i = j
    · subst h; rw [if_pos rfl, if_neg (by omega), if_pos (by omega)]
    · have : (i : ℕ) ≠ j := fun a => h (Fin.ext a)
      rw [if_neg h, if_neg (by omega), if_neg (by omega)]
  · rw [hb.right_right, hr, hr, if_neg (by omega), if_neg (by omega)]

theorem exists_isSympBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H),
    ∃ bas : (Fin (2 * (Module.finrank ℚ E / 2 * (D.p + D.q))) → ℤ) ≃ₗ[ℤ] D.La, IsSympBasis D bas := by
  intro E _ _ _ H D
  have := D.fin
  have := D.proj
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 E) D.La
  have : Module.Free ℤ D.La := inferInstance
  exact exists_equiv_stdSymp D.alt D.unimod (finrank_int_lattice D)

end GlobalTheory.ZM
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

theorem Cpt.openImmersion_comp_structure_eq_generic {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {U : Scheme.{0}} {F O : Type}
    [Field F] [CommRing O] {c : U ⟶ Sp F} {t : SAB H U} {β : O →+* F} (C : Cpt c t β) :
    C.j ≫ C.s = c ≫ spMap β := by
  rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]

private theorem spMap_comp_moduli_spaces {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (g : A →+* B) (g' : B →+* D) :
    spMap (g'.comp g) = spMap g' ≫ spMap g := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem Cpt.Above.exists_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (U'' : Scheme.{0}) (F'' O'' : Type) [Field F''] [CommRing O''] (c'' : U'' ⟶ Sp F'') (t'' : SAB H U'') (β'' : O'' →+* F'') (C : Cpt c t β) (C' : Cpt c' t' β') (C'' : Cpt c'' t'' β'') (b : O →+* O') (b' : O' →+* O'') (k' : F' →+* F'') (r : U' ⟶ U) (ν : SABMap t' t r) (a : C'.Above C b r ν) (r' : U'' ⟶ U') (ν' : SABMap t'' t' r') (f : C''.X ⟶ C.X) (mu : SABMap C''.t C.t f) (hf : f ≫ C.s = C''.s ≫ spMap (b'.comp b)), IsDedFrac β'' → β''.comp b' = k'.comp β' → r' ≫ c' = c'' ≫ spMap k' → C''.j ≫ f = r' ≫ r ≫ C.j → C''.m.φ ≫ mu.φ = ν'.φ ≫ ν.φ ≫ C.m.φ → ∃ (h : C''.X ⟶ C'.X) (mu' : SABMap C''.t C'.t h) (hh : h ≫ C'.s = C''.s ≫ spMap b'), h ≫ a.π = f ∧ mu'.φ ≫ a.mu.φ = mu.φ ∧ C''.j ≫ h = r' ≫ C'.j ∧ C''.m.φ ≫ mu'.φ = ν'.φ ≫ C'.m.φ ∧ (IsFinite (pullback.lift f C''.s hf) → IsFinite (pullback.lift h C''.s hh)) := by
  intro E _ _ _ H U F O _ _ c t β U' F' O' _ _ c' t' β' U'' F'' O'' _ _ c'' t'' β'' C C' C'' b b' k' r ν a r' ν' f mu hf
    hD hβ hc hj hφ
  obtain ⟨⟨hdom, hDed⟩, -, hFrac⟩ := hD
  let _ : Algebra O'' F'' := β''.toAlgebra
  have := hdom
  have : IsDedekindDomain O'' := hDed
  have : IsFractionRing O'' F'' := hFrac
  obtain ⟨hN, -, -, hPre, hFl, hDom, hQC⟩ := GlobalTheory.genericPart_dense_proOpen O'' F'' C''.X U'' C''.s C''.jQ C''.flat
    C''.proj C''.jQ_open C''.jQ_dense
  have : IsLocallyNoetherian C''.X := hN

  have hbase : f ≫ C.s = (C''.s ≫ spMap b') ≫ spMap b := by
    rw [hf, Category.assoc, spMap_comp_moduli_spaces]
  have hq : IsIntegralHom (pullback.lift a.π C'.s a.π_over) := by
    have := a.fin
    infer_instance
  have hsq : (r' ≫ C'.j) ≫ pullback.lift a.π C'.s a.π_over = C''.j ≫ pullback.lift f (C''.s ≫ spMap b') hbase := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, a.j_comm, hj]
    · simp only [Category.assoc, pullback.lift_snd]
      rw [Cpt.openImmersion_comp_structure_eq_generic C', ← Category.assoc r', hc, Category.assoc, ← spMap_comp_moduli_spaces, ← hβ,
        spMap_comp_moduli_spaces, ← Category.assoc C''.j, Cpt.openImmersion_comp_structure_eq_generic C'', Category.assoc]
  obtain ⟨h, ⟨h1, h2⟩, -⟩ := GlobalTheory.existsUnique_lift_of_densePart C''.X U'' (pullback C.s (spMap b)) C'.X C''.j C''.normal
    hPre hFl hDom hQC _ _ _ hq hsq
  have hπ : h ≫ a.π = f := by
    simpa only [Category.assoc, pullback.lift_fst] using congrArg (· ≫ pullback.fst _ _) h2
  have hh : h ≫ C'.s = C''.s ≫ spMap b' := by
    simpa only [Category.assoc, pullback.lift_snd] using congrArg (· ≫ pullback.snd _ _) h2
  clear h2 hsq hbase
  subst hπ
  obtain ⟨mu', hmu'⟩ := sabCancel pullCubCancel E H C.X C'.X C''.X C.t C'.t C''.t a.π h a.mu mu
  refine ⟨h, mu', hh, rfl, hmu'.symm, h1, ?_, ?_⟩
  · apply a.mu.2.1.hom_ext
    · rw [Category.assoc, Category.assoc]
      erw [← hmu', hφ, a.φ_comm]
    · have w1 := mu'.2.1.w
      have w2 := C''.m.2.1.w
      have w3 := ν'.2.1.w
      have w4 := C'.m.2.1.w
      have h1' : C''.jQ ≫ pullback.fst _ _ ≫ h = r' ≫ C'.jQ ≫ pullback.fst _ _ := by
        simpa only [Cpt.j, Category.assoc] using h1
      simp only [Category.assoc] at w1 w2 w3 w4 ⊢
      erw [w1, reassoc_of% w2, h1', w4, reassoc_of% w3]
  · intro hfin
    have : IsProper C'.s := projProper O' C'.X C'.s C'.proj
    let p : pullback C'.s (spMap b') ⟶ pullback C.s (spMap (b'.comp b)) :=
      pullback.lift (pullback.fst _ _ ≫ a.π) (pullback.snd _ _) (by
        rw [Category.assoc, a.π_over, ← Category.assoc, pullback.condition, Category.assoc, spMap_comp_moduli_spaces])
    have hp : pullback.lift h C''.s hh ≫ p = pullback.lift (h ≫ a.π) C''.s hf := by
      apply pullback.hom_ext
      · simp only [p, Category.assoc]
        rw [pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst]
      · simp only [p, Category.assoc]
        rw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
    have : IsSeparated p := by
      have e : p ≫ pullback.snd C.s (spMap (b'.comp b)) = pullback.snd C'.s (spMap b') := pullback.lift_snd _ _ _
      have : IsSeparated (p ≫ pullback.snd C.s (spMap (b'.comp b))) := by
        rw [e]
        infer_instance
      exact IsSeparated.of_comp p (pullback.snd C.s (spMap (b'.comp b)))
    rw [← hp] at hfin
    exact IsFinite.of_comp _ p

end GlobalTheory.Models
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem exists_section_of_pow_eq_one {T V : Scheme.{0}} [IsLocallyNoetherian T] (hT : Geo.Tor.IsNormalScheme T)
    (j : V ⟶ T) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j]
    (G : Over T) [GrpObj G] [IsCommMonObj G] [IsProper G.hom] (n : ℕ) (hn : IsUnit (n : Γ(T, ⊤)))
    (P : Over T) (x : P ⟶ G) (hx : x ^ n = 1) (k : V ⟶ P.left) (hk : k ≫ P.hom = j) :
    ∃ σ : T ⟶ G.left, σ ≫ G.hom = 𝟙 T ∧ j ≫ σ = k ≫ x.left := by
  have hw : (Out.mulA G n).left ≫ G.hom = G.hom := Over.w _
  have h₁ : FormallyUnramified (Out.mulA G n).left := formallyUnramified_mulA T G n hn
  have h₂ : IsProper ((Out.mulA G n).left ≫ G.hom) := by rw [hw]; infer_instance
  have h₃ : IsProper (Out.mulA G n).left := IsProper.of_comp _ G.hom
  have h₄ : LocallyQuasiFinite (Out.mulA G n).left := by
    refine ⟨fun {U} hU {W} hW e => ?_⟩
    have a₁ := (Out.mulA G n).left.formallyUnramified_appLE hU hW e
    have a₂ := (Out.mulA G n).left.finiteType_appLE hU hW e
    algebraize [((Out.mulA G n).left.appLE U W e).hom]
    exact inferInstanceAs (Algebra.QuasiFinite _ _)
  have h₅ : IsFinite (Out.mulA G n).left := .of_isProper_of_locallyQuasiFinite _
  have e₁ : x ≫ Out.mulA G n = toUnit P ≫ η[G] := by
    rw [Out.mulA, MonObj.comp_pow, Category.comp_id, hx, Hom.one_def]
  have e₂ : x.left ≫ (Out.mulA G n).left = P.hom ≫ (η[G]).left := by
    rw [← Over.comp_left, e₁]; simp
  obtain ⟨σ, ⟨a, b⟩, -⟩ := existsUnique_lift_of_densePart T V G.left G.left j hT ‹_› ‹_› ‹_› ‹_›
    (Out.mulA G n).left (η[G]).left (k ≫ x.left) inferInstance
    (by rw [Category.assoc, e₂, ← hk, Category.assoc])
  refine ⟨σ, ?_, a⟩
  rw [← hw, reassoc_of% b]
  exact Over.w η[G]

theorem torsion_section_extends_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), IsDedFrac β → AbOpen Y.t.G → ∃ U : Y.X.Opens, (U : Set Y.X) = abLocus Y.t.G ∧ ∀ (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (n : ℕ), IsUnit (n : O) → σ ^ n = 1 → Y.Extends U σ := by
  intro E _ _ _ H D l Xo c O _ β Y ⟨⟨_, hD⟩, _, hF⟩ ⟨U, hU, hP⟩
  refine ⟨U, hU, fun σ n hn hσ => ?_⟩
  letI : Algebra O c.F := β.toAlgebra
  obtain ⟨hN, -, -, j₁, j₂, j₃, j₄⟩ := genericPart_dense_proOpen O c.F Y.X (Xo.XF c) Y.s Y.jQ Y.flat Y.proj
    Y.jQ_open Y.jQ_dense
  replace j₁ : IsPreimmersion Y.j := j₁
  replace j₂ : Flat Y.j := j₂
  replace j₃ : IsDominant Y.j := j₃
  replace j₄ : QuasiCompact Y.j := j₄
  have hr : Set.range Y.j ⊆ Set.range U.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι, hU]
    have : Y.jQ x ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]; exact ⟨_, rfl⟩
    exact this
  let j : Xo.XF c ⟶ U.toScheme := IsOpenImmersion.lift U.ι Y.j hr
  have hj : j ≫ U.ι = Y.j := IsOpenImmersion.lift_fac _ _ _
  have sq : IsPullback (𝟙 _) j Y.j U.ι := IsPullback.of_horiz_isIso_mono ⟨by simp [hj]⟩
  have k₁ : IsPreimmersion j := MorphismProperty.of_isPullback (P := @IsPreimmersion) sq j₁
  have k₂ : Flat j := MorphismProperty.of_isPullback (P := @Flat) sq j₂
  have k₄ : QuasiCompact j := MorphismProperty.of_isPullback (P := @QuasiCompact) sq j₄
  have k₃ : IsDominant j := by
    constructor
    have hd := Dense.preimage j₃.denseRange U.ι.isOpenEmbedding.isOpenMap
    refine hd.mono ?_
    rintro y ⟨x, hx⟩
    refine ⟨x, U.ι.isOpenEmbedding.injective ?_⟩
    rw [← hx, ← hj]; rfl
  have hT : Geo.Tor.IsNormalScheme U.toScheme := fun x => by
    obtain ⟨_, _⟩ := Y.normal (U.ι x)
    let e := (asIso (U.ι.stalkMap x)).commRingCatIsoToRingEquiv
    exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩
  have hn' : IsUnit (n : Γ(U.toScheme, ⊤)) := by
    simpa using hn.map ((U.ι ≫ Y.s).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom)
  let G : Over U.toScheme := (Over.pullback U.ι).obj Y.t.G
  have hG : IsProper G.hom := by
    have : IsProper ((pullbackRestrictIsoRestrict Y.t.G.hom U).inv ≫ pullback.snd Y.t.G.hom U.ι) := hP
    exact (MorphismProperty.cancel_left_of_respectsIso @IsProper _ _).mp this
  have gp := isGrpPullback_pullback Y.t.G U.ι
  have hc := Y.m.cart
  let ψ : Y.oF.t.G.left ⟶ G.left := gp.1.lift Y.m.φ (Y.oF.t.G.hom ≫ j)
    (by rw [Category.assoc, hj]; exact hc.1.w)
  have hψ : ψ ≫ pullback.fst Y.t.G.hom U.ι = Y.m.φ := gp.1.lift_fst _ _ _
  have gq : IsGrpPullback Y.oF.t.G G j ψ :=
    gp.cancel (by rw [hψ, hj]; exact hc) (gp.1.lift_snd _ _ _)
  obtain ⟨s, hs₁, hs₂⟩ := exists_section_of_pow_eq_one hT j G n hn' _ (pushHom gq _ σ)
    (by rw [← map_pow, hσ, map_one]) (𝟙 _) ((Category.id_comp _).trans (Category.id_comp _))
  refine ⟨s ≫ pullback.fst Y.t.G.hom U.ι, ?_, fun j' hj' => ?_⟩
  · rw [Category.assoc, gp.1.w, reassoc_of% hs₁]
  · obtain rfl : j' = j := by rw [← cancel_mono U.ι, hj, hj']
    rw [reassoc_of% hs₂, ← hψ]
    exact Category.assoc _ _ _

end GlobalTheory
end
