module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Mathlib.Algebra.Category.Ring.FinitePresentation
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem etFF_eq_toMorphismProperty :
    EtFF = RingHom.toMorphismProperty (fun f => RingHom.Etale f ∧ RingHom.FaithfullyFlat f) := by
  ext A B g; rfl

theorem etFF_iff_spec {A B : CommRingCat.{0}} (g : A ⟶ B) :
    EtFF g ↔ Etale (Spec.map g) ∧ Surjective (Spec.map g) := by
  have he : Etale (Spec.map g) ↔ g.hom.Etale := HasRingHomProperty.Spec_iff
  have hs : Surjective (Spec.map g) ↔ Function.Surjective (PrimeSpectrum.comap g.hom) := by
    rw [surjective_iff]; rfl
  rw [he, hs]
  change g.hom.Etale ∧ g.hom.FaithfullyFlat ↔ _
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  constructor
  · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, (RingHom.Etale.iff_flat_and_formallyUnramified.1 h1).1, h2⟩

theorem etFF_isMultiplicative : EtFF.IsMultiplicative := by
  refine { id_mem := ?_, comp_mem := ?_ }
  · intro A
    change (RingHom.id A).Etale ∧ (RingHom.id A).FaithfullyFlat
    exact ⟨RingHom.Etale.of_bijective Function.bijective_id,
      RingHom.FaithfullyFlat.of_bijective Function.bijective_id⟩
  · intro A B C f g hf hg
    change (f ≫ g).hom.Etale ∧ (f ≫ g).hom.FaithfullyFlat
    rw [CommRingCat.hom_comp]
    exact ⟨RingHom.Etale.stableUnderComposition _ _ hf.1 hg.1,
      RingHom.FaithfullyFlat.stableUnderComposition _ _ hf.2 hg.2⟩

theorem etFF_isStableUnderCobaseChange : EtFF.IsStableUnderCobaseChange := by
  rw [etFF_eq_toMorphismProperty]
  exact RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2
    (RingHom.Etale.isStableUnderBaseChange.and RingHom.FaithfullyFlat.isStableUnderBaseChange)

theorem etFF_respectsIso : EtFF.RespectsIso := by
  rw [etFF_eq_toMorphismProperty]
  exact RingHom.toMorphismProperty_respectsIso_iff.1
    (RingHom.Etale.respectsIso.and RingHom.FaithfullyFlat.respectsIso)

theorem finiteType_of_etFF {A B : CommRingCat.{0}} (g : A ⟶ B) (hg : EtFF g)
    (hA : Algebra.FiniteType ℤ A) : Algebra.FiniteType ℤ B := by
  letI := g.hom.toAlgebra
  haveI : Algebra.Etale A B := RingHom.Etale.toAlgebra hg.1
  exact Algebra.FiniteType.trans hA inferInstance

theorem etFF_basic :
    (EtFF.IsMultiplicative ∧ EtFF.IsStableUnderCobaseChange ∧ EtFF.RespectsIso) ∧
    (∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ↔ Etale (Spec.map g) ∧ Surjective (Spec.map g)) ∧
    ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → Algebra.FiniteType ℤ A → Algebra.FiniteType ℤ B :=
  ⟨⟨etFF_isMultiplicative, etFF_isStableUnderCobaseChange, etFF_respectsIso⟩,
    fun _ _ g => etFF_iff_spec g, fun _ _ g hg hA => finiteType_of_etFF g hg hA⟩

end GlobalTheory.EtC
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.WExactCongr

variable {T : Type 1} [Category.{0} T]

theorem exactAt_iff {N M : T ⥤ AddCommGrpCat.{1}} (ε : N ⟶ M) {X : CosimplicialObject T}
    (hX : ∀ k, IsIso (ε.app (X.obj k))) (n : ℕ) :
    ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj (X ⋙ N)).ExactAt (n + 1) ↔
    ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj (X ⋙ M)).ExactAt (n + 1) := by
  haveI : ∀ k, IsIso ((Functor.whiskerLeft X ε).app k) := fun k => hX k
  have hw : IsIso (Functor.whiskerLeft X ε) := NatIso.isIso_of_isIso_app _
  let e := (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).mapIso (@asIso _ _ _ _ (Functor.whiskerLeft X ε) hw)
  exact ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩

theorem wExact_iff (U : T) (X : CosimplicialObject T) (a : (CosimplicialObject.const T).obj U ⟶ X)
    (N M : T ⥤ AddCommGrpCat.{1}) (ε : N ⟶ M) (hU : IsIso (ε.app U)) (hX : ∀ k, IsIso (ε.app (X.obj k))) :
    WExact N a ↔ WExact M a := by
  have nat : ∀ {P Q : T} (f : P ⟶ Q) (x : N.obj P), M.map f (ε.app P x) = ε.app Q (N.map f x) := by
    intro P Q f x
    exact (ConcreteCategory.congr_hom (ε.naturality f) x).symm
  have surj : ∀ (P : T), IsIso (ε.app P) → ∀ (x : M.obj P), ∃ x', ε.app P x' = x := by
    intro P hP x
    refine ⟨inv (ε.app P) x, ?_⟩
    have := ConcreteCategory.congr_hom (IsIso.inv_hom_id (ε.app P)) x
    simpa using this
  have inj : ∀ (P : T), IsIso (ε.app P) → ∀ (x y : N.obj P), ε.app P x = ε.app P y → x = y := by
    intro P hP x y hxy
    have h := congrArg (inv (ε.app P)) hxy
    have hx := ConcreteCategory.congr_hom (IsIso.hom_inv_id (ε.app P)) x
    have hy := ConcreteCategory.congr_hom (IsIso.hom_inv_id (ε.app P)) y
    simp only [ConcreteCategory.comp_apply] at hx hy
    rw [hx, hy] at h
    simpa using h
  have h0 := hX (SimplexCategory.mk 0)
  have h1 := hX (SimplexCategory.mk 1)
  constructor
  · rintro ⟨i1, i2, i3⟩
    refine ⟨?_, ?_, fun n => (exactAt_iff ε hX n).1 (i3 n)⟩
    · intro x y hxy
      obtain ⟨x, rfl⟩ := surj _ hU x
      obtain ⟨y, rfl⟩ := surj _ hU y
      erw [nat, nat] at hxy
      rw [i1 (inj _ h0 _ _ hxy)]
    · intro y hy
      obtain ⟨y, rfl⟩ := surj _ h0 y
      erw [nat, nat] at hy
      obtain ⟨x, hx⟩ := i2 y (inj _ h1 _ _ hy)
      exact ⟨ε.app U x, (nat _ x).trans (congrArg _ hx)⟩
  · rintro ⟨i1, i2, i3⟩
    refine ⟨?_, ?_, fun n => (exactAt_iff ε hX n).2 (i3 n)⟩
    · intro x y hxy
      have h := congrArg (ε.app _) hxy
      erw [← nat, ← nat] at h
      exact inj _ hU _ _ (i1 h)
    · intro y hy
      have h := congrArg (ε.app _) hy
      erw [← nat, ← nat] at h
      obtain ⟨x, hx⟩ := i2 _ h
      obtain ⟨x, rfl⟩ := surj _ hU x
      erw [nat] at hx
      exact ⟨x, inj _ h0 _ _ hx⟩

end GlobalTheory.EtC.WExactCongr

theorem GlobalTheory.EtC.wExact_congr : ∀ (T : Type 1) [Category.{0} T] (U : T) (X : CosimplicialObject T)
    (a : (CosimplicialObject.const T).obj U ⟶ X) (N M : T ⥤ AddCommGrpCat.{1}) (ε : N ⟶ M),
    IsIso (ε.app U) → (∀ k, IsIso (ε.app (X.obj k))) → (WExact N a ↔ WExact M a) :=
  fun _ _ U X a N M ε hU hX => GlobalTheory.EtC.WExactCongr.wExact_iff U X a N M ε hU hX
end
end

section

open TensorProduct GlobalTheory.EtC

namespace GlobalTheory.PicCech

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]

theorem exists_sum_of_mem_mul {M N : Submodule A B} {z : B} (hz : z ∈ M * N) :
    ∃ (ι : Type) (_ : Fintype ι) (x y : ι → B), (∀ i, x i ∈ M) ∧ (∀ i, y i ∈ N) ∧ ∑ i, x i * y i = z := by
  induction hz using Submodule.mul_induction_on' with
  | mem_mul_mem m hm n hn => exact ⟨Unit, inferInstance, fun _ => m, fun _ => n, fun _ => hm, fun _ => hn, by simp⟩
  | add a _ b _ ha hb =>
    obtain ⟨ι, _, x, y, hx, hy, hs⟩ := ha
    obtain ⟨κ, _, x', y', hx', hy', hs'⟩ := hb
    refine ⟨ι ⊕ κ, inferInstance, Sum.elim x x', Sum.elim y y', ?_, ?_, ?_⟩
    · rintro (i | i) <;> simp [hx, hx']
    · rintro (i | i) <;> simp [hy, hy']
    · rw [Fintype.sum_sum_type]; simp [hs, hs']

theorem tmul_eq_one_tmul {c : B} (hc : c ∈ (1 : Submodule A B)) (q : B) :
    c ⊗ₜ[A] q = (1 : B) ⊗ₜ[A] (c * q) := by
  obtain ⟨a, rfl⟩ := Submodule.mem_one.1 hc
  rw [← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]

theorem tmul_eq_tmul_one {c : B} (hc : c ∈ (1 : Submodule A B)) (p : B) :
    p ⊗ₜ[A] c = (p * c) ⊗ₜ[A] (1 : B) := by
  obtain ⟨a, rfl⟩ := Submodule.mem_one.1 hc
  rw [mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.smul_def, mul_one]

theorem sum_tmul_mul_one_tmul {ι : Type} [Fintype ι] (x y : ι → B) (hs : ∑ i, x i * y i = 1) {b : B}
    (hb : ∀ i, y i * b ∈ (1 : Submodule A B)) :
    (∑ i, x i ⊗ₜ[A] y i) * ((1 : B) ⊗ₜ[A] b) = b ⊗ₜ[A] (1 : B) := by
  rw [Finset.sum_mul]
  simp_rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [Finset.sum_congr rfl (fun i _ => tmul_eq_tmul_one (hb i) (x i)), ← TensorProduct.sum_tmul]
  congr 1
  simp_rw [← mul_assoc]; rw [← Finset.sum_mul, hs, one_mul]

theorem sum_tmul_mul_sum_tmul {ι : Type} [Fintype ι] (x y : ι → B) (hs : ∑ i, x i * y i = 1)
    (hxy : ∀ i j, x i * y j ∈ (1 : Submodule A B)) :
    (∑ i, x i ⊗ₜ[A] y i) * (∑ j, y j ⊗ₜ[A] x j) = 1 := by
  rw [Finset.sum_mul_sum]
  simp_rw [Algebra.TensorProduct.tmul_mul_tmul]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => tmul_eq_one_tmul (hxy i j) (y i * x j)))]
  simp_rw [← TensorProduct.tmul_sum]
  rw [Algebra.TensorProduct.one_def]
  congr 1
  calc ∑ i, ∑ j, x i * y j * (y i * x j) = (∑ i, x i * y i) * (∑ j, x j * y j) := by
        rw [Finset.sum_mul_sum]; exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ = 1 := by rw [hs, one_mul]

theorem cocycle_sum {ι : Type} [Fintype ι] (x y : ι → B) (hs : ∑ i, x i * y i = 1)
    (hyx : ∀ i j, y i * x j ∈ (1 : Submodule A B)) :
    Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) (∑ i, x i ⊗ₜ[A] y i) =
    Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) (∑ i, x i ⊗ₜ[A] y i) *
      (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)) (∑ i, x i ⊗ₜ[A] y i) := by

  simp only [map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.includeRight_apply,
  Algebra.TensorProduct.includeLeft_apply]
  rw [Finset.sum_mul_sum]
  simp_rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
    congrArg (fun t => x i ⊗ₜ[A] t) (tmul_eq_one_tmul (hyx i j) (y j))))]
  simp_rw [← TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [mul_assoc, ← Finset.mul_sum, hs, mul_one]

theorem exists_unitCocycle_descMod_eq : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], descMod A B 1 ≤ 1 →
    ∀ I : (Submodule A B)ˣ, ∃ u : (B ⊗[A] B)ˣ, UCoc A B u ∧ descMod A B u = (I : Submodule A B) := by
  intro A B _ _ _ h1 I
  have hone : (1 : B) ∈ (I : Submodule A B) * ↑I⁻¹ := by
    rw [I.mul_inv]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
  obtain ⟨ι, _, x, y, hx, hy, hs⟩ := exists_sum_of_mem_mul hone
  have hxy : ∀ i j, x i * y j ∈ (1 : Submodule A B) := fun i j => by
    rw [← I.mul_inv]; exact Submodule.mul_mem_mul (hx i) (hy j)
  have hyx : ∀ i j, y i * x j ∈ (1 : Submodule A B) := fun i j => by
    rw [← I.inv_mul]; exact Submodule.mul_mem_mul (hy i) (hx j)
  have hs' : ∑ i, y i * x i = 1 := by simp_rw [mul_comm (y _)]; exact hs
  have huv := sum_tmul_mul_sum_tmul x y hs hxy
  let u : (B ⊗[A] B)ˣ := ⟨∑ i, x i ⊗ₜ[A] y i, ∑ j, y j ⊗ₜ[A] x j, huv, by rw [mul_comm]; exact huv⟩
  refine ⟨u, cocycle_sum x y hs hyx, le_antisymm ?_ ?_⟩
  · intro b hb
    have hb' : (∑ i, x i ⊗ₜ[A] y i) * ((1 : B) ⊗ₜ[A] b) = b ⊗ₜ[A] (1 : B) := hb
    have key : ∀ i, b * y i ∈ (1 : Submodule A B) := by
      intro i
      apply h1
      show ((1 : (B ⊗[A] B)ˣ) : B ⊗[A] B) * ((1 : B) ⊗ₜ[A] (b * y i)) = (b * y i) ⊗ₜ[A] (1 : B)
      have hv := sum_tmul_mul_one_tmul y x hs' (b := y i) (fun j => hxy j i)
      calc ((1 : (B ⊗[A] B)ˣ) : B ⊗[A] B) * ((1 : B) ⊗ₜ[A] (b * y i))
          = ((∑ i, x i ⊗ₜ[A] y i) * ((1 : B) ⊗ₜ[A] b)) * ((∑ j, y j ⊗ₜ[A] x j) * ((1 : B) ⊗ₜ[A] y i)) := by
            rw [mul_mul_mul_comm, huv, Algebra.TensorProduct.tmul_mul_tmul, Units.val_one, one_mul, one_mul, one_mul]
        _ = (b * y i) ⊗ₜ[A] (1 : B) := by rw [hb', hv, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have hb2 : b = ∑ i, (b * y i) * x i := by
      simp_rw [mul_assoc, ← Finset.mul_sum, hs', mul_one]
    rw [hb2]
    exact Submodule.sum_mem _ fun i _ => by simpa using Submodule.mul_mem_mul (key i) (hx i)
  · intro b hb
    exact sum_tmul_mul_one_tmul x y hs (fun i => by rw [← I.inv_mul]; exact Submodule.mul_mem_mul (hy i) hb)

end GlobalTheory.PicCech
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem refines_of_coAug : ∀ (T : Type 1) [Category.{0} T] [HasFiniteWidePushouts T] (Cov : MorphismProperty T) (Q : ∀ (U : T) (X : CosimplicialObject T), ((CosimplicialObject.const T).obj U ⟶ X) → Prop), (∀ (U V : T) (g : U ⟶ V), Cov g → Q U _ (coAug g)) → Refines Cov Q := by
  intro T _ _ Cov Q hQ U V g hg
  refine ⟨_, coAug g, WidePushout.ι (fun _ : Fin 1 => g) 0, ?_, hQ U V g hg⟩
  exact WidePushout.arrow_ι (fun _ : Fin 1 => g) 0

end GlobalTheory
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.CechBC

universe v u

theorem widePullback_isPullback {C : Type u} [Category.{v} C] {Y X Y' X' : C}
    {a : Y' ⟶ Y} {f' : Y' ⟶ X'} {f : Y ⟶ X} {b : X' ⟶ X} (hP : IsPullback a f' f b) (n : ℕ)
    [HasWidePullback X' (fun _ : Fin (n + 1) => Y') (fun _ => f')]
    [HasWidePullback X (fun _ : Fin (n + 1) => Y) (fun _ => f)] :
    IsPullback
      (WidePullback.lift (WidePullback.base (fun _ : Fin (n + 1) => f') ≫ b)
        (fun i => WidePullback.π (fun _ : Fin (n + 1) => f') i ≫ a)
        (fun i => by rw [Category.assoc, hP.w, ← Category.assoc, WidePullback.π_arrow]))
      (WidePullback.base (fun _ : Fin (n + 1) => f')) (WidePullback.base (fun _ : Fin (n + 1) => f)) b := by
  refine IsPullback.of_isLimit' ⟨WidePullback.lift_base _ _ _ _⟩ (PullbackCone.IsLimit.mk _
    (fun s => WidePullback.lift s.snd
      (fun i => hP.lift (s.fst ≫ WidePullback.π _ i) s.snd
        (by rw [Category.assoc, WidePullback.π_arrow, s.condition]))
      (fun i => hP.lift_snd _ _ _)) ?_ ?_ ?_)
  · intro s
    apply WidePullback.hom_ext
    · intro j
      rw [Category.assoc, WidePullback.lift_π, ← Category.assoc, WidePullback.lift_π, IsPullback.lift_fst]
    · rw [Category.assoc, WidePullback.lift_base, ← Category.assoc, WidePullback.lift_base, s.condition]
  · intro s
    exact WidePullback.lift_base _ _ _ _
  · intro s m h1 h2
    apply WidePullback.hom_ext
    · intro j
      apply hP.hom_ext
      · rw [WidePullback.lift_π, IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, WidePullback.lift_π]
      · rw [WidePullback.lift_π, IsPullback.lift_snd, Category.assoc, WidePullback.π_arrow, h2]
    · rw [WidePullback.lift_base, h2]

theorem lift_comp_lift {C : Type u} [Category.{v} C] {Y X Y' X' : C}
    {a : Y' ⟶ Y} {f' : Y' ⟶ X'} {f : Y ⟶ X} {b : X' ⟶ X} (w : a ≫ f = f' ≫ b) (n : ℕ)
    [HasWidePullback X' (fun _ : Fin (n + 1) => Y') (fun _ => f')]
    [HasWidePullback X (fun _ : Fin (n + 1) => Y) (fun _ => f)] {T : C}
    (g : T ⟶ X') (e : Fin (n + 1) → (T ⟶ Y')) (he : ∀ i, e i ≫ f' = g)
    (g₂ : T ⟶ X) (e₂ : Fin (n + 1) → (T ⟶ Y)) (he₂ : ∀ i, e₂ i ≫ f = g₂)
    (hg : g ≫ b = g₂) (hh : ∀ i, e i ≫ a = e₂ i) :
    WidePullback.lift g e he ≫
      WidePullback.lift (WidePullback.base (fun _ : Fin (n + 1) => f') ≫ b)
        (fun i => WidePullback.π (fun _ : Fin (n + 1) => f') i ≫ a)
        (fun i => by rw [Category.assoc, w, ← Category.assoc, WidePullback.π_arrow]) =
      WidePullback.lift g₂ e₂ he₂ := by
  apply WidePullback.hom_ext
  · intro j
    rw [Category.assoc, WidePullback.lift_π, ← Category.assoc, WidePullback.lift_π, WidePullback.lift_π, hh]
  · rw [Category.assoc, WidePullback.lift_base, ← Category.assoc, WidePullback.lift_base, WidePullback.lift_base, hg]

end GlobalTheory.CechBC


open GlobalTheory.CechBC in
theorem GlobalTheory.cech_baseChange : ∀ (Y X Y' X' : Scheme.{0}) (a : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (b : X' ⟶ X), IsPullback a f' f b → ∃ m : cech f' ⟶ cech f, IsPullback m (cechAug f') (cechAug f) (sch.map b) ∧ ∀ (k : ℕ) (U : Scheme.{0}) (x : U ⟶ X') (y : Fin (k + 1) → (U ⟶ Y')) (h : ∀ i, y i ≫ f' = x), ∃ h', (m.app (op (SimplexCategory.mk (k)))).app (op U) (cechPt f' k x y h) = cechPt f k (x ≫ b) (fun i => y i ≫ a) h' := by
  intro Y X Y' X' a f' f b hP
  have hw : yoneda.map a ≫ yoneda.map f = yoneda.map f' ≫ yoneda.map b := by
    rw [← yoneda.map_comp, ← yoneda.map_comp, hP.w]
  have hY : IsPullback (yoneda.map a) (yoneda.map f') (yoneda.map f) (yoneda.map b) := hP.map yoneda
  refine ⟨Arrow.mapCechNerve (Arrow.homMk' (f := yoneda.map f') (g := yoneda.map f) (yoneda.map a) (yoneda.map b) hw), ?_, ?_⟩
  · refine IsPullback.of_forall_isPullback_app (fun n => ?_)
    exact widePullback_isPullback hY n.unop.len
  · intro k U x y h
    have h' : ∀ i, (y i ≫ a) ≫ f = x ≫ b := fun i => by rw [Category.assoc, hP.w, ← Category.assoc, h i]
    refine ⟨h', ?_⟩
    have key : WidePullback.lift (arrows := fun _ : Fin (k + 1) => yoneda.map f') (yoneda.map x) (fun i => yoneda.map (y i))
        (fun i => by rw [← yoneda.map_comp, h i]) ≫
        (Arrow.mapCechNerve (Arrow.homMk' (f := yoneda.map f') (g := yoneda.map f) (yoneda.map a) (yoneda.map b) hw)).app (op (SimplexCategory.mk k)) =
        WidePullback.lift (arrows := fun _ : Fin (k + 1) => yoneda.map f) (yoneda.map (x ≫ b)) (fun i => yoneda.map (y i ≫ a))
        (fun i => by rw [← yoneda.map_comp, h' i]) := by
      exact lift_comp_lift hw k _ _ _ _ _ _ (yoneda.map_comp x b).symm (fun i => (yoneda.map_comp (y i) a).symm)
    unfold cechPt
    erw [← NatTrans.comp_app_apply]
    exact congrArg (fun φ : yoneda.obj U ⟶ (cech f).obj (op (SimplexCategory.mk k)) => φ.app (op U) (𝟙 U)) key
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem hom_d_apply {C D : AbCx} (φ : C ⟶ D) (i j : ℤ) (x : C.X i) :
    φ.f j (C.d i j x) = D.d i j (φ.f i x) := by
  rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, HomologicalComplex.Hom.comm]

theorem nat_f_apply {N M : CommRingCat.{0} ⥤ AbCx} (ε : N ⟶ M) {A B : CommRingCat.{0}} (g : A ⟶ B) (n : ℤ)
    (x : (N.obj A).X n) : (ε.app B).f n ((N.map g).f n x) = (M.map g).f n ((ε.app A).f n x) := by
  rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, ← HomologicalComplex.comp_f,
    ← HomologicalComplex.comp_f, ε.naturality]

end GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem contH_transport_quasiIso : ∀ (N M : CommRingCat.{0} ⥤ AbCx) (ε : N ⟶ M), (∀ A, SurjH (ε.app A) ∧ InjH (ε.app A)) → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((N).obj c.pt).X n, ((N).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((N).obj (D.obj j)).X n) (y : ((N).obj c.pt).X (n - 1)), ((N).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((N).map (c.ι.app j)).f n w = z + ((N).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((N).obj (D.obj j)).X n), ((N).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((N).obj c.pt).X (n - 1), ((N).map (c.ι.app j)).f n w = ((N).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((N).obj (D.obj k)).X (n - 1)), ((N).map (D.map f)).f n w = ((N).obj (D.obj k)).d (n - 1) n y) → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((M).obj c.pt).X n, ((M).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((M).obj (D.obj j)).X n) (y : ((M).obj c.pt).X (n - 1)), ((M).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((M).map (c.ι.app j)).f n w = z + ((M).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((M).obj (D.obj j)).X n), ((M).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((M).obj c.pt).X (n - 1), ((M).map (c.ι.app j)).f n w = ((M).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((M).obj (D.obj k)).X (n - 1)), ((M).map (D.map f)).f n w = ((M).obj (D.obj k)).d (n - 1) n y) := by
  intro N M ε hε hN J _ _ D c hc n
  obtain ⟨hN1, hN2⟩ := hN J D c hc n
  have nat : ∀ (j : J) (m : ℤ) (x : ((N).obj (D.obj j)).X m),
      (ε.app c.pt).f m ((N.map (c.ι.app j)).f m x) = (M.map (c.ι.app j)).f m ((ε.app (D.obj j)).f m x) :=
    fun j m x => nat_f_apply ε (B := c.pt) (c.ι.app j) m x
  have dN : ∀ (j : J) (m m' : ℤ) (x : ((N).obj (D.obj j)).X m),
      (N.map (c.ι.app j)).f m' (((N).obj (D.obj j)).d m m' x) = ((N).obj c.pt).d m m' ((N.map (c.ι.app j)).f m x) :=
    fun j m m' x => hom_d_apply (D := (N).obj c.pt) (N.map (c.ι.app j)) m m' x
  have dM : ∀ (j : J) (m m' : ℤ) (x : ((M).obj (D.obj j)).X m),
      (M.map (c.ι.app j)).f m' (((M).obj (D.obj j)).d m m' x) = ((M).obj c.pt).d m m' ((M.map (c.ι.app j)).f m x) :=
    fun j m m' x => hom_d_apply (D := (M).obj c.pt) (M.map (c.ι.app j)) m m' x
  refine ⟨fun z hz => ?_, fun j w hw ⟨y, hy⟩ => ?_⟩
  · obtain ⟨c', y1, hc', h1⟩ := (hε c.pt).1 n z hz
    obtain ⟨j, w, y2, hw, h2⟩ := hN1 c' hc'
    refine ⟨j, (ε.app (D.obj j)).f n w, y1 + (ε.app c.pt).f (n - 1) y2, ?_, ?_⟩
    · rw [← hom_d_apply, hw, map_zero]
    · rw [← nat, h2, map_add (f := _), h1, map_add (f := _), hom_d_apply]
      abel
  · obtain ⟨c1, y1, hc1, h1⟩ := (hε (D.obj j)).1 n w hw
    have hcz : ((N).obj c.pt).d n (n + 1) ((N.map (c.ι.app j)).f n c1) = 0 := by
      rw [← dN, hc1, map_zero]
    obtain ⟨b, hb⟩ := (hε c.pt).2 n _ hcz ⟨y + (show ((M).obj c.pt).X (n - 1) from (M.map (c.ι.app j)).f (n - 1) y1), by
      rw [nat, h1, map_add (f := _), hy, map_add (f := _), dM]⟩
    obtain ⟨k, f, y2, h2⟩ := hN2 j c1 hc1 ⟨b, hb.symm⟩
    refine ⟨k, f, (ε.app (D.obj k)).f (n - 1) y2 - (M.map (D.map f)).f (n - 1) y1, ?_⟩
    have e1 : w = (ε.app (D.obj j)).f n c1 - ((M).obj (D.obj j)).d (n - 1) n y1 := by
      rw [h1]; abel
    rw [e1, map_sub, map_sub, ← nat_f_apply, h2, hom_d_apply, hom_d_apply]

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC

instance : PreservesLimitsOfShape WalkingCospan sch := by unfold sch; infer_instance

theorem isPullback_sch_bc {S W : Scheme.{0}} (r : W ⟶ S) (U : Over S) :
    IsPullback (sch.map (pullback.snd U.hom r)) (sch.map (pullback.fst U.hom r)) (sch.map r) (sch.map U.hom) :=
  (IsPullback.of_hasPullback U.hom r).flip.map sch

theorem bc_sch_iso : ∀ (S W : Scheme.{0}) (r : W ⟶ S), ∃ e : (Over.pullback r ⋙ Over.forget W ⋙ sch) ≅ bc (sch.map r), ∀ U : Over S, e.hom.app U ≫ pullback.fst (sch.map r) (sch.map U.hom) = sch.map (pullback.snd U.hom r) ∧ e.hom.app U ≫ pullback.snd (sch.map r) (sch.map U.hom) = sch.map (pullback.fst U.hom r) := by
  intro S W r
  refine ⟨NatIso.ofComponents (fun U => (isPullback_sch_bc r U).isoPullback) ?_, fun U => ?_⟩
  · intro U V g
    have fV := (isPullback_sch_bc r V).isoPullback_hom_fst
    have sV := (isPullback_sch_bc r V).isoPullback_hom_snd
    have fU := (isPullback_sch_bc r U).isoPullback_hom_fst
    have sU := (isPullback_sch_bc r U).isoPullback_hom_snd
    apply pullback.hom_ext
    · simp only [bc, pullback.map, Functor.comp_map, Over.forget_map, Over.pullback_map_left, Category.assoc,
        pullback.lift_fst, Category.comp_id]
      erw [fV, fU, ← Functor.map_comp, pullback.lift_snd]
    · simp only [bc, pullback.map, Functor.comp_map, Over.forget_map, Over.pullback_map_left, Category.assoc,
        pullback.lift_snd]
      erw [sV, reassoc_of% sU, ← Functor.map_comp, ← Functor.map_comp, pullback.lift_fst]
  · exact ⟨IsPullback.isoPullback_hom_fst _, IsPullback.isoPullback_hom_snd _⟩

end GlobalTheory.EtC
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem exists_etale_factor_of_indEt : ∀ (A O : Type) [CommRing A] [CommRing O] [Algebra A O], IndEt A O → ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B] (φ : B →ₐ[A] O), ∃ (C : Type) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra.Etale A C) (ψ : B →ₐ[A] C) (χ : C →ₐ[A] O), χ.comp ψ = φ := by
  intro A O _ _ _ hO B _ _ _ φ
  obtain ⟨J, _, _, D, t, s, hs, hst⟩ := hO
  have hp : MorphismProperty.isFinitelyPresentable.{0} CommRingCat.{0}
      (CommRingCat.ofHom (algebraMap A B)) :=
    CommRingCat.isFinitelyPresentable_hom _ (RingHom.finitePresentation_algebraMap.2 inferInstance)
  obtain ⟨j, q, hq1, hq2⟩ := MorphismProperty.exists_hom_of_isFinitelyPresentable hs hp t
    (CommRingCat.ofHom φ.toRingHom) (fun j => by
      rw [(hst j).2]; ext a; simp)
  letI : Algebra A (D.obj j) := (t.app j).hom.toAlgebra
  haveI : Algebra.Etale A (D.obj j) := (hst j).1
  have h1 : ∀ a : A, q.hom (algebraMap A B a) = algebraMap A (D.obj j) a := fun a =>
    congrArg (fun f => f.hom a) hq1
  have h2 : ∀ a : A, (s.app j).hom (algebraMap A (D.obj j) a) = algebraMap A O a := fun a =>
    congrArg (fun f => f.hom a) (hst j).2
  have h3 : ∀ b : B, (s.app j).hom (q.hom b) = φ b := fun b =>
    congrArg (fun f => f.hom b) hq2
  refine ⟨D.obj j, inferInstance, inferInstance, inferInstance, ⟨q.hom, h1⟩, ⟨(s.app j).hom, h2⟩, ?_⟩
  ext b
  exact h3 b

end GlobalTheory.EtC
end
