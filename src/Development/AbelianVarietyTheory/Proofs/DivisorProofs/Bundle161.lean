module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle018
public import Mathlib.RingTheory.Localization.Away.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle032
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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
public import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NormSheaf

theorem normForm_coeff_smul (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] {m : ℕ}
    (y : Fin m → L) (c : K) (s : Fin m →₀ ℕ) :
    (normForm K L (fun i => algebraMap K L c * y i)).coeff s =
      c ^ Module.finrank K L * (normForm K L y).coeff s := by
  have hM : ∀ i, (Algebra.leftMulMatrix (Module.finBasis K L) (algebraMap K L c * y i)).map
      (MvPolynomial.C : K →+* MvPolynomial (Fin m) K) =
      (MvPolynomial.C c : MvPolynomial (Fin m) K) • (Algebra.leftMulMatrix (Module.finBasis K L) (y i)).map
        (MvPolynomial.C : K →+* MvPolynomial (Fin m) K) := by
    intro i
    rw [← Algebra.smul_def, map_smul]
    ext a b
    simp [Matrix.map_apply, Matrix.smul_apply, MvPolynomial.C_mul]
  have : normForm K L (fun i => algebraMap K L c * y i) =
      MvPolynomial.C (c ^ Module.finrank K L) * normForm K L y := by
    unfold normForm
    simp_rw [hM, smul_comm (MvPolynomial.X _ : MvPolynomial (Fin m) K) (MvPolynomial.C c), ← Finset.smul_sum,
      Matrix.det_smul, Fintype.card_fin, map_pow]
  rw [this, MvPolynomial.coeff_C_mul]

end GlobalTheory.NormSheaf

namespace GlobalTheory.NormSheaf

theorem normIdeal_map_away : ∀ (A K L B A' B' : Type) [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [Algebra A K] [Algebra B L] [Algebra A' K] [Algebra B' L]
    [Algebra A A'] [Algebra B B'] [Algebra A B] (f : A) [IsLocalization.Away f A']
    [IsLocalization.Away (algebraMap A B f) B'],
    (algebraMap A' K).comp (algebraMap A A') = algebraMap A K →
    (algebraMap B' L).comp (algebraMap B B') = algebraMap B L →
    (algebraMap K L).comp (algebraMap A K) = (algebraMap B L).comp (algebraMap A B) →
    Function.Injective (algebraMap A' K) →
    (∀ {m : ℕ} (g : Fin m → B) s,
      (GlobalTheory.NormSheaf.normForm K L (fun i => algebraMap B L (g i))).coeff s ∈ (algebraMap A K).range) →
    ∀ J : Ideal B, (GlobalTheory.NormSheaf.normIdeal A K L B J).map (algebraMap A A') =
      GlobalTheory.NormSheaf.normIdeal A' K L B' (J.map (algebraMap B B')) := by
  intro A K L B A' B' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f _ _ h1 h2 h3 hinj hcoef J
  have e1 : ∀ x : A, algebraMap A' K (algebraMap A A' x) = algebraMap A K x := fun x => by
    simpa using RingHom.congr_fun h1 x
  have e2 : ∀ x : B, algebraMap B' L (algebraMap B B' x) = algebraMap B L x := fun x => by
    simpa using RingHom.congr_fun h2 x
  have e3 : ∀ x : A, algebraMap K L (algebraMap A K x) = algebraMap B L (algebraMap A B x) := fun x => by
    simpa using RingHom.congr_fun h3 x
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    unfold normIdeal
    rw [Ideal.span_le]
    rintro a ⟨m, g, hg, s, hs⟩
    rw [SetLike.mem_coe, Ideal.mem_comap]
    apply Ideal.subset_span
    refine ⟨m, fun i => algebraMap B B' (g i), fun i => Ideal.mem_map_of_mem _ (hg i), s, ?_⟩
    rw [e1, hs]
    simp only [e2]
  · unfold normIdeal
    rw [Ideal.span_le]
    rintro a' ⟨m, g', hg', s, hs⟩
    set b := algebraMap A B f with hb
    have hloc : ∀ i, ∃ (j : B) (n : ℕ), j ∈ J ∧ g' i * algebraMap B B' (b ^ n) = algebraMap B B' j := by
      intro i
      obtain ⟨⟨⟨j, hj⟩, ⟨_, n, rfl⟩⟩, h⟩ :=
        (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers b) B').1 (hg' i)
      exact ⟨j, n, hj, h⟩
    choose j n hj hn using hloc
    set N := ∑ i, n i
    have hN : ∀ i, g' i * algebraMap B B' (b ^ N) = algebraMap B B' (j i * b ^ (N - n i)) := by
      intro i
      have hle : n i ≤ N := Finset.single_le_sum (fun k _ => Nat.zero_le (n k)) (Finset.mem_univ i)
      rw [← Nat.add_sub_cancel' hle, pow_add, map_mul, ← mul_assoc, hn i, Nat.add_sub_cancel_left, map_mul]
    have hjJ : ∀ i, j i * b ^ (N - n i) ∈ J := fun i => J.mul_mem_right _ (hj i)
    set c := algebraMap A K f
    have himg : ∀ i, algebraMap B L (j i * b ^ (N - n i)) =
        algebraMap K L (c ^ N) * algebraMap B' L (g' i) := by
      intro i
      rw [← e2, ← hN i, map_mul, e2, map_pow, map_pow, hb, ← e3, mul_comm]
    obtain ⟨a, ha⟩ := hcoef (fun i => j i * b ^ (N - n i)) s
    have hcoef' : algebraMap A K a = (c ^ N) ^ Module.finrank K L * algebraMap A' K a' := by
      rw [ha, hs]
      simp only [himg]
      exact normForm_coeff_smul K L _ _ s
    have hmem : a ∈ normIdeal A K L B J := Ideal.subset_span ⟨m, _, hjJ, s, ha⟩
    have key : algebraMap A A' a = algebraMap A A' (f ^ (N * Module.finrank K L)) * a' := by
      apply hinj
      rw [map_mul, e1, e1, hcoef', map_pow, pow_mul]
    have hu : IsUnit (algebraMap A A' (f ^ (N * Module.finrank K L))) := by
      rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit f).pow _
    rw [SetLike.mem_coe, ← Ideal.unit_mul_mem_iff_mem _ hu, ← key]
    exact Ideal.mem_map_of_mem _ hmem

end GlobalTheory.NormSheaf
end

section

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

def secAlg {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.Opens) : A →+* Γ(T, U) :=
  (g.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] in
theorem _root_.GlobalTheory.HilbAff.appLE_eq_of_eq {X Y : Scheme.{0}} {f₁ f₂ : X ⟶ Y} (h : f₁ = f₂)
    (U : Y.Opens) (V : X.Opens)
    (e₁ : V ≤ f₁ ⁻¹ᵁ U) (e₂ : V ≤ f₂ ⁻¹ᵁ U) : f₁.appLE U V e₁ = f₂.appLE U V e₂ := by
  subst h
  rfl

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] in
theorem _root_.GlobalTheory.HilbAff.kappa_comm {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (_root_.GlobalTheory.HilbAff.str A B) g).IdealSheafData) (U : T.Opens) (a : A) :
    ((I.subschemeι ≫ pullback.fst _ g).appLE ⊤ ((I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U)
      (by simp)).hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B a)) =
    ((I.subschemeι ≫ pullback.snd _ g).app U).hom (_root_.GlobalTheory.HilbAff.secAlg A g U a) := by
  have key : (I.subschemeι ≫ pullback.fst _ g) ≫ _root_.GlobalTheory.HilbAff.str A B =
      (I.subschemeι ≫ pullback.snd _ g) ≫ g := by
    simp [pullback.condition]
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B a) =
      (_root_.GlobalTheory.HilbAff.str A B).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) := by
    have := congrArg (fun φ => φ.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B)))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    exact this
  have hm : (_root_.GlobalTheory.HilbAff.str A B).appTop ≫
      (I.subschemeι ≫ pullback.fst _ g).appLE ⊤ ((I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U)
        (by simp) = g.appLE ⊤ U (by simp) ≫ (I.subschemeι ≫ pullback.snd _ g).app U := by
    calc _ = ((I.subschemeι ≫ pullback.fst _ g) ≫ _root_.GlobalTheory.HilbAff.str A B).appLE ⊤
          ((I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U) (by simp) :=
          (Scheme.Hom.comp_appLE _ _ _ _ _).symm
      _ = ((I.subschemeι ≫ pullback.snd _ g) ≫ g).appLE ⊤
          ((I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U) (by simp) :=
          _root_.GlobalTheory.HilbAff.appLE_eq_of_eq key _ _ _ _
      _ = _ := by
        rw [Scheme.Hom.app_eq_appLE]
        exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [h1]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) hm

def kappa {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) g).IdealSheafData) (U : T.Opens) :
    letI := (secAlg A g U).toAlgebra;
    Γ(T, U) ⊗[A] B →+* Γ(I.subscheme, (I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U) :=
  letI := (secAlg A g U).toAlgebra
  letI : Algebra A Γ(I.subscheme, (I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U) :=
    (((I.subschemeι ≫ pullback.snd _ g).app U).hom.comp (secAlg A g U)).toAlgebra
  (Algebra.TensorProduct.lift
    { toRingHom := ((I.subschemeι ≫ pullback.snd _ g).app U).hom, commutes' := fun (_ : A) => rfl }
    { toRingHom := (((I.subschemeι ≫ pullback.fst _ g).appLE ⊤ _ (by simp)).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom),
      commutes' := fun a => kappa_comm A B g I U a }
    (fun _ _ => Commute.all _ _)).toRingHom

theorem kappa_tmul {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) g).IdealSheafData) (U : T.Opens) (c : Γ(T, U)) (b : B) :
    letI := (secAlg A g U).toAlgebra
    kappa A B g I U (c ⊗ₜ[A] b) = ((I.subschemeι ≫ pullback.snd _ g).app U).hom c *
      ((I.subschemeι ≫ pullback.fst _ g).appLE ⊤ ((I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U)
        (by simp)).hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) := by
  letI := (secAlg A g U).toAlgebra
  letI : Algebra A Γ(I.subscheme, (I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U) :=
    (((I.subschemeι ≫ pullback.snd _ g).app U).hom.comp (secAlg A g U)).toAlgebra
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

def xI (C : Type) [CommRing C] [Algebra A C] (J : Ideal (C ⊗[A] B)) :
    (pullback (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C)))).IdealSheafData :=
  (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp
    (Algebra.TensorProduct.comm A B C).toRingHom)) ≫ (pullbackSpecIso A B C).inv).ker

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] in
theorem _root_.GlobalTheory.HilbAff.basic_iff_kappa {r N : ℕ} (e : Module.Basis (Fin N) A B)
    (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (_root_.GlobalTheory.HilbAff.str A B) g).IdealSheafData)
    (hI : _root_.GlobalTheory.HilbAff.Good A B r g I) :
    _root_.GlobalTheory.HilbAff.Basic A B e σ (T := T) ⟨g, ⟨I, hI⟩⟩ ↔ ∀ U : T.affineOpens,
      letI := (_root_.GlobalTheory.HilbAff.secAlg A g U).toAlgebra;
      Function.Bijective fun c : Fin r → Γ(T, U) =>
        _root_.GlobalTheory.HilbAff.kappa A B g I U (∑ k, c k ⊗ₜ[A] e (σ k)) := by
  unfold _root_.GlobalTheory.HilbAff.Basic
  refine forall_congr' fun U => ?_

  simp only [map_sum, _root_.GlobalTheory.HilbAff.kappa_tmul]

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] in
theorem _root_.GlobalTheory.HilbAff.secAlg_res {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) {U V : T.Opens}
    (h : U ≤ V) : (T.presheaf.map (homOfLE h).op).hom.comp (_root_.GlobalTheory.HilbAff.secAlg A g V) =
      _root_.GlobalTheory.HilbAff.secAlg A g U := by
  ext a
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))
    (Scheme.Hom.appLE_map g (U := ⊤) (by simp) (homOfLE h).op)

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] in
theorem _root_.GlobalTheory.HilbAff.secAlg_comp {C : Type} [CommRing C] {T : Scheme.{0}}
    (h : T ⟶ Spec (CommRingCat.of C)) (f : A →+* C) (U : T.Opens) :
    _root_.GlobalTheory.HilbAff.secAlg A (h ≫ Spec.map (CommRingCat.ofHom f)) U =
      (_root_.GlobalTheory.HilbAff.secAlg C h U).comp f := by
  have hm : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (h ≫ Spec.map (CommRingCat.ofHom f)).appLE ⊤ U (by simp) =
      CommRingCat.ofHom f ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫ h.appLE ⊤ U (by simp) :=
    calc _ = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
          (Spec.map (CommRingCat.ofHom f)).appTop ≫ h.appLE ⊤ U (by simp) :=
          congrArg (_ ≫ ·) (Scheme.Hom.comp_appLE h _ ⊤ U _)
      _ = ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
          (Spec.map (CommRingCat.ofHom f)).appTop) ≫ h.appLE ⊤ U (by simp) :=
          (Category.assoc _ _ _).symm
      _ = (CommRingCat.ofHom f ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).inv) ≫
          h.appLE ⊤ U (by simp) := by rw [← Scheme.ΓSpecIso_inv_naturality]
      _ = _ := Category.assoc _ _ _
  ext a
  exact congrArg (fun φ => φ.hom a) hm

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] in
theorem _root_.GlobalTheory.HilbAff.eq_of_secAlg_top {T : Scheme.{0}}
    {g₁ g₂ : T ⟶ Spec (CommRingCat.of A)}
    (h : _root_.GlobalTheory.HilbAff.secAlg A g₁ ⊤ = _root_.GlobalTheory.HilbAff.secAlg A g₂ ⊤) :
    g₁ = g₂ := by
  apply ext_of_isAffine
  have e₁ : g₁.appLE ⊤ ⊤ le_top = g₁.appTop := g₁.appLE_eq_app
  have e₂ : g₂.appLE ⊤ ⊤ le_top = g₂.appTop := g₂.appLE_eq_app
  have h' : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ g₁.appLE ⊤ ⊤ le_top =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ g₂.appLE ⊤ ⊤ le_top := CommRingCat.hom_ext h
  rw [e₁, e₂] at h'
  exact (cancel_epi _).1 h'

end GlobalTheory.HilbAff
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ}

abbrev proj {T : Scheme.{0}} (y : (functor A B r).obj (op T)) : y.2.1.subscheme ⟶ T :=
  y.2.1.subschemeι ≫ pullback.snd _ y.1

def gens {N : ℕ} (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) (U : T.Opens) : Fin r → Γ(y.2.1.subscheme, proj y ⁻¹ᵁ U) :=
  fun k => ((y.2.1.subschemeι ≫ pullback.fst _ y.1).appLE ⊤ (proj y ⁻¹ᵁ U) (by simp)).hom
    ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (e (σ k)))

def bad {N : ℕ} (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) (U : T.Opens) : Set (PrimeSpectrum Γ(T, U)) :=
  letI := ((proj y).app U).hom.toAlgebra
  Module.support Γ(T, U)
    (Γ(y.2.1.subscheme, proj y ⁻¹ᵁ U) ⧸ Submodule.span Γ(T, U) (Set.range (gens e σ y U)))

def goodSet {N : ℕ} (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) : Set T :=
  ⋃ U : T.affineOpens, U.2.fromSpec '' (bad e σ y U)ᶜ

def pbMap {T T' : Scheme.{0}} (a : T' ⟶ T) (y : (functor A B r).obj (op T)) :
    ((functor A B r).map a.op y).2.1.subscheme ⟶ y.2.1.subscheme :=
  (y.2.1.comapIso (bc A B y.1 a)).hom ≫ pullback.snd _ _

theorem isPullback_pbMap {T T' : Scheme.{0}} (a : T' ⟶ T) (y : (functor A B r).obj (op T)) :
    IsPullback (pbMap a y) (proj ((functor A B r).map a.op y)) (proj y) a := by
  have H : IsPullback (pullback.snd (bc A B y.1 a) y.2.1.subschemeι)
      (pullback.fst (bc A B y.1 a) y.2.1.subschemeι ≫ pullback.snd _ (a ≫ y.1))
      (y.2.1.subschemeι ≫ pullback.snd _ y.1) a :=
    (IsPullback.of_hasPullback (bc A B y.1 a) y.2.1.subschemeι).flip.paste_vert
      (isPullback_bc A B y.1 a)
  refine IsPullback.of_iso H (y.2.1.comapIso (bc A B y.1 a)).symm (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [pbMap, Iso.symm_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact (Iso.inv_hom_id_assoc _ _).symm
  · change _ = (y.2.1.comapIso (bc A B y.1 a)).inv ≫
      (y.2.1.comap (bc A B y.1 a)).subschemeι ≫ pullback.snd _ (a ≫ y.1)
    rw [Scheme.IdealSheafData.comapIso_inv_subschemeι_assoc]
    simp
  · simp
  · simp

theorem pbMap_fst {T T' : Scheme.{0}} (a : T' ⟶ T) (y : (functor A B r).obj (op T)) :
    pbMap a y ≫ y.2.1.subschemeι ≫ pullback.fst _ y.1 =
      ((functor A B r).map a.op y).2.1.subschemeι ≫ pullback.fst _ ((functor A B r).map a.op y).1 := by
  change (y.2.1.comapIso (bc A B y.1 a)).hom ≫ pullback.snd _ _ ≫
      y.2.1.subschemeι ≫ pullback.fst _ y.1 =
    (y.2.1.comap (bc A B y.1 a)).subschemeι ≫ pullback.fst _ (a ≫ y.1)
  rw [← pullback.condition_assoc, Scheme.IdealSheafData.comapIso_hom_fst_assoc]
  congr 1
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

end GlobalTheory.HilbAff
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace GlobalTheory.HilbAff

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

theorem sigma_inv (r : ℕ) {T : Scheme.{0}} {g₀ g : T ⟶ Spec (CommRingCat.of A)}
    {I₀ : (pullback (str A B) g₀).IdealSheafData} {I : (pullback (str A B) g).IdealSheafData}
    {h₀ : Good A B r g₀ I₀} {h₁ : Good A B r g I}
    (e : (⟨g₀, ⟨I₀, h₀⟩⟩ : Σ g : T ⟶ Spec (CommRingCat.of A),
      {I : (pullback (str A B) g).IdealSheafData // Good A B r g I}) = ⟨g, ⟨I, h₁⟩⟩) :
    ∃ h : g₀ = g, I = I₀.comap
      (pullback.map (str A B) g (str A B) g₀ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [h])) := by
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp e
  refine ⟨rfl, ?_⟩
  have : pullback.map (str A B) g₀ (str A B) g₀ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp) = 𝟙 _ := by
    ext <;> simp
  rw [this, Scheme.IdealSheafData.comap_id]
  exact (congrArg Subtype.val (eq_of_heq h2)).symm

theorem good_ker (r : ℕ) {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) {V : Scheme.{0}}
    (v : V ⟶ pullback (str A B) g) [IsClosedImmersion v] (h1 : IsFinite (v ≫ pullback.snd _ g))
    (h2 : Flat (v ≫ pullback.snd _ g)) (h3 : ∀ y, (v ≫ pullback.snd _ g).finrank y = r) :
    Good A B r g v.ker := by
  let φ := IsClosedImmersion.lift v v.ker.subschemeι (by rw [Scheme.IdealSheafData.ker_subschemeι])
  have hφ : φ ≫ v = v.ker.subschemeι := IsClosedImmersion.lift_fac _ _ _
  haveI : IsIso φ := IsClosedImmersion.isIso_of_ker_eq v.ker.subschemeι v φ hφ
    (Scheme.IdealSheafData.ker_subschemeι _)
  have e : v.ker.subschemeι ≫ pullback.snd _ g = φ ≫ (v ≫ pullback.snd _ g) := by
    rw [← Category.assoc, hφ]
  refine ⟨?_, ?_, fun y => ?_⟩
  · rw [e]; infer_instance
  · rw [e]; infer_instance
  · rw [e, Scheme.Hom.finrank_comp_left_of_isIso, h3]

end GlobalTheory.HilbAff

theorem GlobalTheory.HilbAff.universal : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ) (H : Scheme.{0}) (R : (GlobalTheory.HilbAff.functor A B r).RepresentableBy H), ∃ (U : Scheme.{0}) (u : U ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) (R.homEquiv (𝟙 H)).1), IsClosedImmersion u ∧ IsFinite (u ≫ pullback.snd _ (R.homEquiv (𝟙 H)).1) ∧ Flat (u ≫ pullback.snd _ (R.homEquiv (𝟙 H)).1) ∧ (∀ y, (u ≫ pullback.snd _ (R.homEquiv (𝟙 H)).1).finrank y = r) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Spec (CommRingCat.of A)) (V : Scheme.{0}) (v : V ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) g), IsClosedImmersion v → IsFinite (v ≫ pullback.snd _ g) → Flat (v ≫ pullback.snd _ g) → (∀ y, (v ≫ pullback.snd _ g).finrank y = r) → ∃! f : T ⟶ H, ∃ hf : f ≫ (R.homEquiv (𝟙 H)).1 = g, ∃ w : V ⟶ U, IsPullback v w (pullback.map _ g _ (R.homEquiv (𝟙 H)).1 (𝟙 _) f (𝟙 _) (by simp) (by rw [Category.comp_id, hf])) u := by
  intro A B _ _ _ r H R
  have key : ∀ {T : Scheme.{0}} (f : T ⟶ H), R.homEquiv f =
      ⟨f ≫ (R.homEquiv (𝟙 H)).1, ⟨(R.homEquiv (𝟙 H)).2.1.comap
        (GlobalTheory.HilbAff.bc A B (R.homEquiv (𝟙 H)).1 f), GlobalTheory.HilbAff.good_comap A B r _ f _
          (R.homEquiv (𝟙 H)).2.2⟩⟩ := fun f => by
    have := R.homEquiv_comp f (𝟙 H)
    rw [Category.comp_id] at this
    rw [this]; rfl
  refine ⟨(R.homEquiv (𝟙 H)).2.1.subscheme, (R.homEquiv (𝟙 H)).2.1.subschemeι, inferInstance,
    (R.homEquiv (𝟙 H)).2.2.1, (R.homEquiv (𝟙 H)).2.2.2.1, (R.homEquiv (𝟙 H)).2.2.2.2, ?_⟩
  intro T g V v hv h1 h2 h3
  have hG := GlobalTheory.HilbAff.good_ker A B r g v h1 h2 h3
  let y : (GlobalTheory.HilbAff.functor A B r).obj (op T) := ⟨g, ⟨v.ker, hG⟩⟩

  have cmp : ∀ (f : T ⟶ H) (hf : f ≫ (R.homEquiv (𝟙 H)).1 = g),
      pullback.map (GlobalTheory.HilbAff.str A B) g (GlobalTheory.HilbAff.str A B) (f ≫ (R.homEquiv (𝟙 H)).1)
          (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [hf]) ≫
        GlobalTheory.HilbAff.bc A B (R.homEquiv (𝟙 H)).1 f =
      pullback.map _ g _ (R.homEquiv (𝟙 H)).1 (𝟙 _) f (𝟙 _) (by simp)
        (by rw [Category.comp_id, hf]) := by
    intro f hf
    apply pullback.hom_ext <;>
      simp only [GlobalTheory.HilbAff.bc, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]
  have cmp' : ∀ (f : T ⟶ H) (hf : f ≫ (R.homEquiv (𝟙 H)).1 = g),
      pullback.map (GlobalTheory.HilbAff.str A B) (f ≫ (R.homEquiv (𝟙 H)).1) (GlobalTheory.HilbAff.str A B) g
          (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [hf]) ≫
        pullback.map _ g _ (R.homEquiv (𝟙 H)).1 (𝟙 _) f (𝟙 _) (by simp)
          (by rw [Category.comp_id, hf]) =
      GlobalTheory.HilbAff.bc A B (R.homEquiv (𝟙 H)).1 f := by
    intro f hf
    apply pullback.hom_ext <;>
      simp only [GlobalTheory.HilbAff.bc, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]
  let f := R.homEquiv.symm y
  have hfy : R.homEquiv f = y := Equiv.apply_symm_apply _ _
  rw [key] at hfy
  obtain ⟨hf, hI⟩ := GlobalTheory.HilbAff.sigma_inv A B r hfy
  have hcomap : (R.homEquiv (𝟙 H)).2.1.comap (pullback.map _ g _ (R.homEquiv (𝟙 H)).1 (𝟙 _) f
      (𝟙 _) (by simp) (by rw [Category.comp_id, hf])) = v.ker := by
    rw [hI, ← Scheme.IdealSheafData.comap_comp, cmp f hf]
  refine ⟨f, ⟨hf, ?_⟩, ?_⟩
  · have hle : ((R.homEquiv (𝟙 H)).2.1.subschemeι).ker ≤ (v ≫ pullback.map _ g _
        (R.homEquiv (𝟙 H)).1 (𝟙 _) f (𝟙 _) (by simp) (by rw [Category.comp_id, hf])).ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_comp,
        Scheme.IdealSheafData.le_map_iff_comap_le, hcomap]
    refine ⟨IsClosedImmersion.lift _ _ hle, ?_⟩
    exact isPullback_of_isClosedImmersion _ _ _ _ (IsClosedImmersion.lift_fac _ _ hle).symm
      (by rw [Scheme.IdealSheafData.ker_subschemeι, hcomap])
  · rintro f' ⟨hf', w', hpb⟩
    have hv : v.ker = (R.homEquiv (𝟙 H)).2.1.comap (pullback.map _ g _ (R.homEquiv (𝟙 H)).1 (𝟙 _)
        f' (𝟙 _) (by simp) (by rw [Category.comp_id, hf'])) := by
      rw [← hpb.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
        Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, Scheme.IdealSheafData.ker_subschemeι]
    have h' : R.homEquiv f' = y := by
      rw [key]
      refine GlobalTheory.HilbAff.sigma_eq A B r hf' ?_ _ _
      rw [hv, ← Scheme.IdealSheafData.comap_comp, cmp' f' hf']
    apply R.homEquiv.injective
    rw [h']
    exact (Equiv.apply_symm_apply R.homEquiv y).symm
end
end
