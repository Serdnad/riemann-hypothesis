module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle192
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
public import Mathlib.Dynamics.Newton
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Lagrange
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory

theorem prod_X_sub_C_dvd_pow_of_isRoot (g : ℂ[X]) :
    ∀ s : Multiset ℂ, (∀ a ∈ s, g.IsRoot a) →
      (s.map fun a => X - C a).prod ∣ g ^ Multiset.card s := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons a s ih =>
    intro h
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ']
    exact mul_dvd_mul (dvd_iff_isRoot.mpr (h a (Multiset.mem_cons_self a s)))
      (ih fun b hb => h b (Multiset.mem_cons_of_mem hb))

theorem dvd_pow_natDegree_of_forall_isRoot (f g : ℂ[X]) (hf : f.Monic)
    (h : ∀ a ∈ f.roots, g.IsRoot a) : f ∣ g ^ f.natDegree := by
  have hc : Multiset.card f.roots = f.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have key := prod_X_sub_C_dvd_pow_of_isRoot g f.roots h
  rw [hc] at key
  have hf' := C_leadingCoeff_mul_prod_multiset_X_sub_C hc
  rw [hf.leadingCoeff, C_1, one_mul] at hf'
  rwa [hf'] at key

theorem exists_poly_pow_mul_eq_one : ∀ (n l : ℕ) (B : Matrix (Fin n) (Fin n) ℂ), 0 < l → IsUnit B →
    ∃ p : ℂ[X], (aeval B p) ^ l * B = 1 := by
  intro n l B hl hB
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  set f := B.charpoly with hf
  have hfm : f.Monic := Matrix.charpoly_monic B
  have hB0 : aeval B f = 0 := Matrix.aeval_self_charpoly B
  have hdet : B.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det B).mp hB).ne_zero
  have hroot0 : ∀ a ∈ f.roots, a ≠ 0 := by
    intro a ha h0
    subst h0
    have h1 : f.eval 0 = 0 := (mem_roots hfm.ne_zero).mp ha
    apply hdet
    rw [Matrix.det_eq_sign_charpoly_coeff, coeff_zero_eq_eval_zero, ← hf, h1, mul_zero]
  have hc : ∀ a : ℂ, ∃ c : ℂ, a ≠ 0 → c ^ (k + 1) * a = 1 := by
    intro a
    by_cases ha : a = 0
    · exact ⟨0, fun h => (h ha).elim⟩
    · obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq a⁻¹ (Nat.succ_pos k)
      exact ⟨c, fun _ => by rw [hc, inv_mul_cancel₀ ha]⟩
  choose c hc using hc
  let q : ℂ[X] := Lagrange.interpolate f.roots.toFinset id c
  have hq : ∀ a ∈ f.roots, q.eval a = c a := by
    intro a ha
    exact Lagrange.eval_interpolate_at_node (s := f.roots.toFinset) (v := id) c
      (Set.injOn_id _) (Multiset.mem_toFinset.mpr ha)
  let g : ℂ[X] := X * q ^ (k + 1) - 1
  have hg : ∀ a ∈ f.roots, g.IsRoot a := by
    intro a ha
    have := hc a (hroot0 a ha)
    simp only [g, IsRoot, eval_sub, eval_mul, eval_X, eval_pow, eval_one, hq a ha]
    rw [mul_comm, this, sub_self]
  have hdvd : f ∣ g ^ f.natDegree := dvd_pow_natDegree_of_forall_isRoot f g hfm hg
  let r : AdjoinRoot f := AdjoinRoot.root f
  let x : AdjoinRoot f := AdjoinRoot.mk f q
  let P : (AdjoinRoot f)[X] := C r * X ^ (k + 1) - 1
  have hPx : ∀ z, aeval z P = r * z ^ (k + 1) - 1 := by intro z; simp [P]
  have hmk : r * x ^ (k + 1) - 1 = AdjoinRoot.mk f g := by
    simp [r, x, g, map_sub, map_mul, map_pow, AdjoinRoot.mk_X]
  have hnil : IsNilpotent (aeval x P) := by
    refine ⟨f.natDegree, ?_⟩
    rw [hPx, hmk, ← map_pow, AdjoinRoot.mk_eq_zero]
    exact hdvd
  have hunit : IsUnit (r * x ^ (k + 1)) := by
    have := hnil.isUnit_add_one
    rwa [hPx, sub_add_cancel] at this
  have hunit' : IsUnit (r * x ^ k) := by
    rw [pow_succ, ← mul_assoc] at hunit
    exact isUnit_of_mul_isUnit_left hunit
  have hl : IsUnit ((k + 1 : ℕ) : AdjoinRoot f) := by
    have : IsUnit ((k + 1 : ℕ) : ℂ) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))
    simpa using this.map (algebraMap ℂ (AdjoinRoot f))
  have hder : IsUnit (aeval x (derivative P)) := by
    have h1 : aeval x (derivative P) = ((k + 1 : ℕ) : AdjoinRoot f) * (r * x ^ k) := by
      simp [P]
      ring
    rw [h1]
    exact hl.mul hunit'
  obtain ⟨y, ⟨_, hy⟩, _⟩ := existsUnique_nilpotent_sub_and_aeval_eq_zero hnil hder
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
  refine ⟨p, ?_⟩
  have e : (AdjoinRoot.mk f p) ^ (k + 1) * r = 1 := by
    rw [mul_comm]
    rw [hPx] at hy
    exact sub_eq_zero.mp hy
  have e2 : AdjoinRoot.mk f (p ^ (k + 1) * X - 1) = 0 := by
    rw [map_sub, map_mul, map_pow, AdjoinRoot.mk_X, map_one]
    exact sub_eq_zero.mpr e
  obtain ⟨b, hb⟩ := AdjoinRoot.mk_eq_zero.mp e2
  have h2 := congrArg (aeval B) hb
  rw [map_mul, hB0, zero_mul, map_sub, map_mul, map_pow, aeval_X, map_one] at h2
  exact sub_eq_zero.mp h2

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option autoImplicit false

namespace GlobalTheory.NilThicken

theorem ker_inl_le_map_ker_of_isPushout {A B C D : CommRingCat.{0}} {a : A ⟶ B} {c : A ⟶ C}
    {b : B ⟶ D} {d : C ⟶ D} (h : IsPushout a c b d) (hc : Function.Surjective c.hom) :
    RingHom.ker b.hom ≤ Ideal.map a.hom (RingHom.ker c.hom) := by
  set J : Ideal B := Ideal.map a.hom (RingHom.ker c.hom)
  let π : B ⟶ CommRingCat.of (B ⧸ J) := CommRingCat.ofHom (Ideal.Quotient.mk J)
  let e := RingHom.quotientKerEquivOfSurjective hc
  let σ : C ⟶ CommRingCat.of (B ⧸ J) := CommRingCat.ofHom
    ((Ideal.quotientMap J a.hom (Ideal.le_comap_map)).comp e.symm.toRingHom)
  have w : a ≫ π = c ≫ σ := by
    ext x
    have hx : e.symm (c.hom x) = Ideal.Quotient.mk _ x := by
      rw [RingEquiv.symm_apply_eq]; rfl
    simp [π, σ, hx]
  intro x hx
  have h1 : (b ≫ h.desc π σ w).hom x = π.hom x := by rw [h.inl_desc]
  rw [CommRingCat.comp_apply, (RingHom.mem_ker).mp hx, map_zero] at h1
  exact Ideal.Quotient.eq_zero_iff_mem.mp h1.symm

theorem isNilpotent_ker_app :
    ∀ (R₁ R₀ : CommRingCat.{0}) (g : R₁ ⟶ R₀) (Y₁ Y₀ : Scheme.{0}) (p₁ : Y₁ ⟶ Spec R₁)
      (p₀ : Y₀ ⟶ Spec R₀) (i : Y₀ ⟶ Y₁), IsPullback i p₀ p₁ (Spec.map g) →
      Function.Surjective g → IsNilpotent (RingHom.ker g.hom) → ∀ U : Y₁.Opens, IsAffineOpen U →
      IsNilpotent (RingHom.ker (i.app U).hom) := by
  intro R₁ R₀ g Y₁ Y₀ p₁ p₀ i hpb hg hnil U hU
  have P := GlobalTheory.AffBaseChange.isPushout_appLE_of_isPullback_of_isAffine Y₁ Y₀ (Spec R₁) (Spec R₀)
    i p₀ p₁ (Spec.map g) hpb inferInstance inferInstance U hU
  have hnat := Scheme.ΓSpecIso_naturality g
  set c := (Spec.map g).appTop
  have hcker : RingHom.ker c.hom = Ideal.comap (Scheme.ΓSpecIso R₁).hom.hom (RingHom.ker g.hom) := by
    ext x
    simp only [RingHom.mem_ker, Ideal.mem_comap]
    have := congrArg (fun φ => φ.hom x) hnat
    simp only [CommRingCat.comp_apply] at this
    rw [← this]
    constructor
    · intro h0; rw [h0, map_zero]
    · intro h0
      have hinj := ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R₀).hom)).1
      exact hinj (by rw [h0, map_zero])
  have hcs : Function.Surjective c.hom := by
    intro y
    obtain ⟨r, hr⟩ := hg ((Scheme.ΓSpecIso R₀).hom y)
    obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R₁).hom).2 r
    refine ⟨x, ?_⟩
    have := congrArg (fun φ => φ.hom x) hnat
    simp only [CommRingCat.comp_apply] at this
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R₀).hom).1
    rw [this, hx, hr]
  obtain ⟨n, hn⟩ := hnil
  refine ⟨n, ?_⟩
  have hle := ker_inl_le_map_ker_of_isPushout P hcs
  have hJ : (Ideal.map (p₁.appLE ⊤ U (fun _ _ => trivial)).hom (RingHom.ker c.hom)) ^ n = ⊥ := by
    rw [← Ideal.map_pow, hcker]
    have h2 : (Ideal.comap (Scheme.ΓSpecIso R₁).hom.hom (RingHom.ker g.hom)) ^ n = ⊥ := by
      apply le_bot_iff.mp
      refine (Ideal.le_comap_pow _ n).trans ?_
      rw [show RingHom.ker g.hom ^ n = ⊥ from hn]
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot] at hx
      rw [Ideal.mem_bot]
      exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R₁).hom).1 (by rw [hx, map_zero])
    rw [h2, Ideal.map_bot]
  exact le_bot_iff.mp ((Ideal.pow_right_mono hle n).trans hJ.le)

end GlobalTheory.NilThicken
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory

theorem specAdj_symm_comp_specMap (T : Scheme.{0}) {R S : CommRingCat.{0}}
    (f : T ⟶ Spec S) (φ : R ⟶ S) :
    ((ΓSpec.adjunction.homEquiv T (op R)).symm (f ≫ Spec.map φ)).unop =
      φ ≫ ((ΓSpec.adjunction.homEquiv T (op S)).symm f).unop := by
  have h := ΓSpec.adjunction.homEquiv_naturality_right_symm (X := T) (Y := op S) (Y' := op R)
    f φ.op
  exact congrArg Quiver.Hom.unop h

theorem spec_widePushout_isLimit : ∀ (n : ℕ) (C D A : Type) [CommRing C] [CommRing D] [CommRing A] (a : C →+* D) (b : C →+* A) (l : Fin n → (D →+* A)) (hl : ∀ i, (l i).comp a = b), (∀ (B : Type) [CommRing B] (g : Fin n → (D →+* B)) (c : C →+* B), (∀ i, (g i).comp a = c) → ∃! u : A →+* B, u.comp b = c ∧ ∀ i, u.comp (l i) = g i) → Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin n => Spec.map (CommRingCat.ofHom a)) (Spec.map (CommRingCat.ofHom b)) (fun i => Spec.map (CommRingCat.ofHom (l i))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hl i]))) := by
  intro n C D A _ _ _ a b l hl H
  classical
  let adj := ΓSpec.adjunction
  let e : ∀ (T : Scheme.{0}) (R : CommRingCat.{0}), (op Γ(T, ⊤) ⟶ op R) ≃ (T ⟶ Spec R) :=
    fun T R => adj.homEquiv T (op R)
  have hcomp : ∀ (T : Scheme.{0}) {R S : CommRingCat.{0}} (f : T ⟶ Spec S) (φ : R ⟶ S),
      ((e T R).symm (f ≫ Spec.map φ)).unop = φ ≫ ((e T S).symm f).unop :=
    fun T R S f φ => specAdj_symm_comp_specMap T f φ
  have hse : ∀ (T : Scheme.{0}) (R : CommRingCat.{0}) (ψ : R ⟶ Γ(T, ⊤)),
      ((e T R).symm (e T R ψ.op)).unop = ψ := fun T R ψ => by
    rw [Equiv.symm_apply_apply]; rfl
  have hinj : ∀ (T : Scheme.{0}) (R : CommRingCat.{0}) (f g : T ⟶ Spec R),
      ((e T R).symm f).unop = ((e T R).symm g).unop → f = g :=
    fun T R f g h => (e T R).symm.injective (Quiver.Hom.unop_inj h)

  let gOf : ∀ (t : WidePullbackCone (fun _ : Fin n => Spec.map (CommRingCat.ofHom a))),
      Fin n → (D →+* Γ(t.pt, ⊤)) :=
    fun t i => ((e t.pt (CommRingCat.of D)).symm (t.π i)).unop.hom
  let cOf : ∀ (t : WidePullbackCone (fun _ : Fin n => Spec.map (CommRingCat.ofHom a))),
      C →+* Γ(t.pt, ⊤) :=
    fun t => ((e t.pt (CommRingCat.of C)).symm t.base).unop.hom
  have hgc : ∀ t i, (gOf t i).comp a = cOf t := by
    intro t i
    have h1 := hcomp t.pt (t.π i) (CommRingCat.ofHom a)
    rw [t.condition i] at h1
    have h2 := congrArg CommRingCat.Hom.hom h1
    simpa [gOf, cOf] using h2.symm
  let uOf : ∀ t : WidePullbackCone (fun _ : Fin n => Spec.map (CommRingCat.ofHom a)), A →+* Γ(t.pt, ⊤) := fun t => (H Γ(t.pt, ⊤) (gOf t) (cOf t) (hgc t)).choose
  have huOf : ∀ t : WidePullbackCone (fun _ : Fin n => Spec.map (CommRingCat.ofHom a)), (uOf t).comp b = cOf t ∧ ∀ i, (uOf t).comp (l i) = gOf t i :=
    fun t => (H Γ(t.pt, ⊤) (gOf t) (cOf t) (hgc t)).choose_spec.1
  have huniq : ∀ (t : WidePullbackCone (fun _ : Fin n => Spec.map (CommRingCat.ofHom a))) (u : A →+* Γ(t.pt, ⊤)), u.comp b = cOf t → (∀ i, u.comp (l i) = gOf t i) →
      u = uOf t :=
    fun t u h1 h2 => (H Γ(t.pt, ⊤) (gOf t) (cOf t) (hgc t)).choose_spec.2 u ⟨h1, h2⟩
  refine ⟨WidePullbackCone.IsLimit.mk _
    (fun t => e t.pt (CommRingCat.of A) (CommRingCat.ofHom (uOf t)).op) ?_ ?_ ?_⟩
  · intro t
    rw [WidePullbackCone.mk_base]
    apply hinj
    erw [hcomp, hse]
    apply CommRingCat.hom_ext
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom]
    exact (huOf t).1
  · intro t i
    rw [WidePullbackCone.mk_π]
    apply hinj
    erw [hcomp, hse]
    apply CommRingCat.hom_ext
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom]
    exact (huOf t).2 i
  · intro t m hb hπ
    rw [WidePullbackCone.mk_base] at hb
    simp only [WidePullbackCone.mk_π] at hπ
    have hu : ((e t.pt (CommRingCat.of A)).symm m).unop.hom = uOf t := by
      apply huniq
      · have hb' : m ≫ Spec.map (CommRingCat.ofHom b) = t.base := hb
        have h1 : ((e t.pt (CommRingCat.of C)).symm t.base).unop =
            CommRingCat.ofHom b ≫ ((e t.pt (CommRingCat.of A)).symm m).unop := by
          rw [← hb']; exact hcomp t.pt m (CommRingCat.ofHom b)
        have h2 := congrArg CommRingCat.Hom.hom h1
        rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at h2
        exact h2.symm
      · intro i
        have hπ' : m ≫ Spec.map (CommRingCat.ofHom (l i)) = t.π i := hπ i
        have h1 : ((e t.pt (CommRingCat.of D)).symm (t.π i)).unop =
            CommRingCat.ofHom (l i) ≫ ((e t.pt (CommRingCat.of A)).symm m).unop := by
          rw [← hπ']; exact hcomp t.pt m (CommRingCat.ofHom (l i))
        have h2 := congrArg CommRingCat.Hom.hom h1
        rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at h2
        exact h2.symm
    apply hinj
    rw [hse, ← hu]
    rfl

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.ClopenIdealSheaf

theorem map_comap_localization {R A S T : Type*} [CommRing R] [CommRing A] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra A T] (f : R) [IsLocalization.Away f S] (ρ : R →+* A)
    [IsLocalization.Away (ρ f) T] (τ : S →+* T)
    (hcomm : ∀ a, τ (algebraMap R S a) = algebraMap A T (ρ a)) (I : Ideal A) :
    (I.comap ρ).map (algebraMap R S) = (I.map (algebraMap A T)).comap τ := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    refine Ideal.mem_comap.mpr (Ideal.mem_comap.mpr ?_)
    rw [hcomm]
    exact Ideal.mem_map_of_mem _ ha
  · intro s hs
    obtain ⟨⟨⟨x, hx⟩, ⟨_, n, rfl⟩⟩, hxs⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (.powers (ρ f)) T).mp (Ideal.mem_comap.mp hs)
    obtain ⟨⟨b, ⟨_, k, rfl⟩⟩, hb⟩ := IsLocalization.surj (.powers f) s
    simp only at hxs hb
    have h1 : algebraMap A T (ρ b * ρ f ^ n) = algebraMap A T (x * ρ f ^ k) := by
      calc algebraMap A T (ρ b * ρ f ^ n)
          = τ (algebraMap R S b) * algebraMap A T (ρ f ^ n) := by rw [map_mul, hcomm]
        _ = τ s * τ (algebraMap R S (f ^ k)) * algebraMap A T (ρ f ^ n) := by
          rw [← hb, map_mul]
        _ = τ s * algebraMap A T (ρ f ^ n) * algebraMap A T (ρ f ^ k) := by
          rw [hcomm, map_pow]; ring
        _ = algebraMap A T (x * ρ f ^ k) := by rw [hxs, map_mul]
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.eq_iff_exists (.powers (ρ f)) T).mp h1
    simp only at hm
    rw [IsLocalization.mem_map_algebraMap_iff (.powers f)]
    refine ⟨⟨⟨f ^ (m + n) * b, ?_⟩, ⟨f ^ (m + n + k), m + n + k, rfl⟩⟩, ?_⟩
    · have e : ρ (f ^ (m + n) * b) = ρ f ^ m * (ρ b * ρ f ^ n) := by
        rw [map_mul, map_pow, pow_add]; ring
      rw [Ideal.mem_comap, e, hm]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hx)
    · simp only
      rw [map_mul, pow_add, map_mul, ← hb]
      ring

theorem map_comap_eq {Z : Scheme.{0}} (F : ∀ U : Z.affineOpens, Ideal Γ(Z, U))
    {U V B : Z.affineOpens} (hVU : (V : Z.Opens) ≤ U) (f : Γ(Z, U))
    (hB : Z.affineBasicOpen ((Z.presheaf.map (homOfLE hVU).op).hom f) = B)
    (hBD : (B : Z.Opens) ≤ Z.basicOpen f)
    (hI : (F V).map (Z.presheaf.map (homOfLE (Z.basicOpen_le
        ((Z.presheaf.map (homOfLE hVU).op).hom f))).op).hom =
      F (Z.affineBasicOpen ((Z.presheaf.map (homOfLE hVU).op).hom f))) :
    ((F V).comap (Z.presheaf.map (homOfLE hVU).op).hom).map
        (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom =
      (F B).comap (Z.presheaf.map (homOfLE hBD).op).hom := by
  subst hB
  rw [← hI]
  haveI := U.2.isLocalization_basicOpen f
  haveI := V.2.isLocalization_basicOpen ((Z.presheaf.map (homOfLE hVU).op).hom f)
  refine map_comap_localization (S := Γ(Z, Z.basicOpen f)) f _
    (T := Γ(Z, Z.basicOpen ((Z.presheaf.map (homOfLE hVU).op).hom f))) _ ?_ _
  intro a
  change (Z.presheaf.map (homOfLE hBD).op).hom
      ((Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom a) =
    (Z.presheaf.map (homOfLE (Z.basicOpen_le _)).op).hom
      ((Z.presheaf.map (homOfLE hVU).op).hom a)
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp]
  rfl

end GlobalTheory.ClopenIdealSheaf

namespace GlobalTheory.ClopenIdealSheaf

theorem exists_idealSheafData_of_isClopen : ∀ (Z : Scheme.{0}) (W : Set Z), IsClopen W →
    ∀ (F : ∀ U : Z.affineOpens, Ideal Γ(Z, U)),
    (∀ (U : Z.affineOpens) (f : Γ(Z, U)), (U : Set Z) ⊆ W →
      (F U).map (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom = F (Z.affineBasicOpen f)) →
    ∃ J : Z.IdealSheafData, (∀ U : Z.affineOpens, (U : Set Z) ⊆ W → J.ideal U = F U) ∧
      (J.support : Set Z) ⊆ W := by
  intro Z W hW F hF
  let W' : Z.Opens := ⟨W, hW.isOpen⟩
  let Wc : Z.Opens := ⟨Wᶜ, hW.isClosed.isOpen_compl⟩
  have hAff : ∀ U : Z.affineOpens, IsAffineOpen ((U : Z.Opens) ⊓ W') := by
    intro U
    obtain ⟨e, -, he, -⟩ := GlobalTheory.IsNormalScheme.exists_isIdempotentElem_basicOpen_eq (X := Z)
      (U := (U : Z.Opens)) (V := (U : Z.Opens) ⊓ W') (W := (U : Z.Opens) ⊓ Wc)
      (by
        rw [← inf_sup_left]
        have : W' ⊔ Wc = ⊤ := by
          ext x; simp [W', Wc, em]
        rw [this, inf_top_eq])
      (by
        refine Disjoint.mono inf_le_right inf_le_right ?_
        rw [disjoint_iff]; ext x; simp [W', Wc])
    rw [← he]; exact U.2.basicOpen e
  let V : Z.affineOpens → Z.affineOpens := fun U => ⟨(U : Z.Opens) ⊓ W', hAff U⟩
  have hVU : ∀ U, (V U : Z.Opens) ≤ U := fun U => inf_le_left
  have hVW : ∀ U, ((V U : Z.Opens) : Set Z) ⊆ W := fun U => Set.inter_subset_right
  let I : ∀ U : Z.affineOpens, Ideal Γ(Z, U) := fun U =>
    (F (V U)).comap (Z.presheaf.map (homOfLE (hVU U)).op).hom
  refine ⟨{ ideal := I, map_ideal_basicOpen := ?_ }, ?_, ?_⟩
  · intro U f
    have hB : Z.affineBasicOpen ((Z.presheaf.map (homOfLE (hVU U)).op).hom f) =
        V (Z.affineBasicOpen f) := by
      apply Subtype.ext
      change Z.basicOpen ((Z.presheaf.map (homOfLE (hVU U)).op).hom f) = Z.basicOpen f ⊓ W'
      rw [Scheme.basicOpen_res]
      have := Z.basicOpen_le f
      apply le_antisymm
      · exact le_inf inf_le_right (inf_le_left.trans inf_le_right)
      · exact le_inf (le_inf (inf_le_left.trans this) inf_le_right) inf_le_left
    exact map_comap_eq F (hVU U) f hB (hVU _) (hF (V U) _ (hVW U))
  · intro U hU
    have key : ∀ (A B : Z.affineOpens), A = B → ∀ hle : (B : Z.Opens) ≤ A,
        (F B).comap (Z.presheaf.map (homOfLE hle).op).hom = F A := by
      rintro A B rfl hle
      have : homOfLE hle = 𝟙 _ := rfl
      rw [this, op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id]
      exact Ideal.comap_id _
    exact key U (V U) (Subtype.ext (inf_eq_left.mpr (show (U : Z.Opens) ≤ W' from hU)).symm) (hVU U)
  · intro x hx
    by_contra hxW
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open hxW hW.isClosed.isOpen_compl
    replace hx := (Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hxU).mp hx
    have hbot : ((V ⟨U, hU⟩ : Z.affineOpens) : Z.Opens) = ⊥ := by
      ext y
      simp only [V, W', TopologicalSpace.Opens.coe_inf, TopologicalSpace.Opens.coe_mk,
        Set.mem_inter_iff, TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun h => hUW h.1 h.2
    haveI : Subsingleton Γ(Z, (V ⟨U, hU⟩ : Z.Opens)) :=
      CommRingCat.subsingleton_of_isTerminal (Z.sheaf.isTerminalOfEqEmpty hbot)
    have htop : F (V ⟨U, hU⟩) = ⊤ := by
      rw [Ideal.eq_top_iff_one, Subsingleton.elim (1 : Γ(Z, (V ⟨U, hU⟩ : Z.Opens))) 0]
      exact zero_mem _
    have hI : I ⟨U, hU⟩ = ⊤ := by
      simp only [I, htop, Ideal.comap_top]
    change x ∈ Z.zeroLocus (U := U) (I ⟨U, hU⟩ : Set Γ(Z, U)) at hx
    rw [hI, Scheme.mem_zeroLocus_iff] at hx
    exact hx 1 (Submodule.mem_top) (by rw [Scheme.basicOpen_one]; exact hxU)

end GlobalTheory.ClopenIdealSheaf
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

theorem _root_.GlobalTheory.T.exists_nonempty_isIso_restrict_of_generic_mem : ∀ {W W' Y Y₁ : Scheme.{0}} [IsIntegral W] [IsIntegral W'] (i : W ⟶ Y) [IsClosedImmersion i] (h : W' ⟶ W) (c : W' ⟶ Y₁) [IsClosedImmersion c] (s₁ : Y₁ ⟶ Y) (U : Y.Opens), IsIso (s₁ ∣_ U) → h ≫ i = c ≫ s₁ → i (genericPoint W) ∈ U → (∃ w', h w' = genericPoint W) → ∃ U' : W.Opens, (U' : Set W).Nonempty ∧ IsIso (h ∣_ U') := by
  first | exact @GlobalTheory.isIso_restrict_of_closedImmersion_near_generic | exact GlobalTheory.isIso_restrict_of_closedImmersion_near_generic | (intros; apply GlobalTheory.isIso_restrict_of_closedImmersion_near_generic <;> assumption)
end
