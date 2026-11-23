module

public import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle157
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Mon
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open scoped TensorProduct

namespace GlobalTheory

namespace PDiv

theorem cotMap_injective_of_sq : ∀ (R C A : Type) [CommRing R] [CommRing C] [CommRing A]
    [Bialgebra R C] [Bialgebra R A] (f : C →ₐc[R] A),
    (∀ b : C, f b ∈ RingHom.ker (Bialgebra.counitAlgHom R A) ^ 2 →
      b ∈ RingHom.ker (Bialgebra.counitAlgHom R C) ^ 2) →
    Function.Injective (GlobalTheory.PDiv.cotMap f) := by
  intro R C A _ _ _ _ _ f h
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro w hw
  obtain ⟨c, rfl⟩ := AugCot.d_surjective _ w
  have hw' : dUnit (R := R) (f c) = 0 := (cotMap_d f c).symm.trans hw
  rw [dUnit, AugCot.d_eq_zero_iff] at hw'
  change AugCot.d _ c = 0
  rw [AugCot.d_eq_zero_iff]
  apply h
  have e : Bialgebra.counitAlgHom R A (f c) = Bialgebra.counitAlgHom R C c :=
    AlgHom.congr_fun (BialgHomClass.counitAlgHom_comp f) c
  have e2 : f (c - algebraMap R C (Bialgebra.counitAlgHom R C c)) =
      f c - algebraMap R A (Bialgebra.counitAlgHom R A (f c)) := by
    rw [map_sub, e]
    congr 1
    exact AlgHom.commutes (f : C →ₐ[R] A) _
  rw [e2]
  exact hw'

end PDiv

end GlobalTheory
end

section

open CategoryTheory GlobalTheory.CxCoh

set_option autoImplicit false
namespace GlobalTheory.CxCoh.VertSurjTwo
universe a b
variable {C' : Type b} [Category.{0} C']

theorem core {L L' : Cx C'} (a0 : ∀ T, L.M0.obj T →+ L'.M0.obj T) (a1 : ∀ T, L.M1.obj T →+ L'.M1.obj T)
    (a2 : ∀ T, L.M2.obj T →+ L'.M2.obj T)
    (a0m : ∀ {T T' : C'} (φ : T ⟶ T') x, a0 T' (L.M0.map φ x) = L'.M0.map φ (a0 T x))
    (a1m : ∀ {T T' : C'} (φ : T ⟶ T') x, a1 T' (L.M1.map φ x) = L'.M1.map φ (a1 T x))
    (a2m : ∀ {T T' : C'} (φ : T ⟶ T') x, a2 T' (L.M2.map φ x) = L'.M2.map φ (a2 T x))
    (ad0 : ∀ T x, a1 T (L.d0 T x) = L'.d0 T (a0 T x)) (ad1 : ∀ T x, a2 T (L.d1 T x) = L'.d1 T (a1 T x))
    (hq : ∀ T, IsQ (L.d0 T) (L.d1 T) (L.d2 T) (L'.d0 T) (L'.d1 T) (L'.d2 T) (a0 T) (a1 T) (a2 T))
    (c' : L'.T2) (hc' : c' ∈ L'.Z2) :
    ∃ c ∈ L.Z2, ∃ g : L'.T1, c' = ((fun T T' T'' φ ψ ↦ a0 T'' (c.1 T T' T'' φ ψ)),
      (fun T T' φ ↦ a1 T' (c.2.1 T T' φ)), fun T ↦ a2 T (c.2.2 T)) + L'.D1 g := by
  obtain ⟨z', α', η'⟩ := c'
  obtain ⟨hz, hα, hη, hd⟩ := hc'
  simp only at hz hα hη hd
  choose η w hη0 hηw using fun T ↦ (hq T).surj2 (η' T) (hd T)
  have key2 : ∀ (T T' : C') (φ : T ⟶ T'), a2 T' (η T' - L.M2.map φ (η T)) =
      L'.d1 T' (α' T T' φ + L'.M1.map φ (w T) - w T') := by
    intro T T' φ
    have h := hη T T' φ
    rw [hηw T', hηw T] at h
    simp only [map_sub, map_add (f := _), a2m, ← L'.diffOne_natural] at h ⊢
    linear_combination (norm := abel1) h
  have cl2 : ∀ (T T' : C') (φ : T ⟶ T'), L.d2 T' (η T' - L.M2.map φ (η T)) = 0 := by
    intro T T' φ
    rw [map_sub, L.diffTwo_natural, hη0, hη0, map_zero, sub_zero]
  choose α₁ hα₁ using fun T T' φ ↦ (hq T').inj2 _ _ (cl2 T T' φ) (key2 T T' φ)

  have cl1 : ∀ (T T' : C') (φ : T ⟶ T'),
      L'.d1 T' (α' T T' φ + L'.M1.map φ (w T) - w T' - a1 T' (α₁ T T' φ)) = 0 := by
    intro T T' φ
    rw [map_sub (L'.d1 T'), ← key2, ← ad1, hα₁, sub_self]
  choose α₂ f hα₂0 hα₂ using fun T T' φ ↦ (hq T').surj1 _ (cl1 T T' φ)
  obtain ⟨α, hA, hB⟩ : ∃ α : L.M1.c1, (∀ (T T' : C') (φ : T ⟶ T'), L.d1 T' (α T T' φ) = η T' - L.M2.map φ (η T)) ∧
      ∀ (T T' : C') (φ : T ⟶ T'), α' T T' φ + L'.M1.map φ (w T) - w T' = a1 T' (α T T' φ) + L'.d0 T' (f T T' φ) := by
    refine ⟨fun T T' φ ↦ α₁ T T' φ + α₂ T T' φ, fun T T' φ ↦ ?_, fun T T' φ ↦ ?_⟩
    · simp only [map_add (f := _), hα₁, hα₂0, add_zero]
    · have h := hα₂ T T' φ
      simp only [map_add (f := _)]
      linear_combination (norm := abel1) h
  have clβ : ∀ (T T' T'' : C') (φ : T ⟶ T') (ψ : T' ⟶ T''),
      L.d1 T'' (α T T'' (φ ≫ ψ) - L.M1.map ψ (α T T' φ) - α T' T'' ψ) = 0 := by
    intro T T' T'' φ ψ
    simp only [map_sub, hA, L.diffOne_natural, L.M2.map_comp]
    abel
  have keyβ : ∀ (T T' T'' : C') (φ : T ⟶ T') (ψ : T' ⟶ T''),
      a1 T'' (α T T'' (φ ≫ ψ) - L.M1.map ψ (α T T' φ) - α T' T'' ψ) =
        L'.d0 T'' (z' T T' T'' φ ψ + (L'.M0.map ψ (f T T' φ) - f T T'' (φ ≫ ψ) + f T' T'' ψ)) := by
    intro T T' T'' φ ψ
    have e1 := hB T T'' (φ ≫ ψ)
    have e2 := congrArg (L'.M1.map ψ) (hB T T' φ)
    have e3 := hB T' T'' ψ
    have h := hα T T' T'' φ ψ
    simp only [map_add (f := _), map_sub, ← L'.M1.map_comp, ← L'.diffZero_natural] at e2
    simp only [map_add (f := _), map_sub, a1m]
    linear_combination (norm := abel1) e2 + e3 + h - e1
  choose z₁ hz₁ using fun T T' T'' φ ψ ↦ (hq T'').inj1 _ _ (clβ T T' T'' φ ψ) (keyβ T T' T'' φ ψ)
  have cl0 : ∀ (T T' T'' : C') (φ : T ⟶ T') (ψ : T' ⟶ T''),
      L'.d0 T'' (z' T T' T'' φ ψ + (L'.M0.map ψ (f T T' φ) - f T T'' (φ ≫ ψ) + f T' T'' ψ) -
        a0 T'' (z₁ T T' T'' φ ψ)) = 0 := by
    intro T T' T'' φ ψ
    rw [map_sub (L'.d0 T''), ← keyβ, ← ad0, hz₁, sub_self]
  choose z₂ hz₂0 hz₂ using fun T T' T'' φ ψ ↦ (hq T'').surj0 _ (cl0 T T' T'' φ ψ)
  obtain ⟨z, hzd, hza⟩ : ∃ z : L.M0.c2, (∀ (T T' T'' : C') (φ : T ⟶ T') (ψ : T' ⟶ T''),
      L.d0 T'' (z T T' T'' φ ψ) = α T T'' (φ ≫ ψ) - L.M1.map ψ (α T T' φ) - α T' T'' ψ) ∧
      ∀ (T T' T'' : C') (φ : T ⟶ T') (ψ : T' ⟶ T''),
      a0 T'' (z T T' T'' φ ψ) = z' T T' T'' φ ψ + (L'.M0.map ψ (f T T' φ) - f T T'' (φ ≫ ψ) + f T' T'' ψ) := by
    refine ⟨fun T T' T'' φ ψ ↦ z₁ T T' T'' φ ψ + z₂ T T' T'' φ ψ, fun T T' T'' φ ψ ↦ ?_, fun T T' T'' φ ψ ↦ ?_⟩
    · simp only [map_add (f := _), hz₁, hz₂0, add_zero]
    · simp only [map_add (f := _), hz₂]
      abel
  have hzc : ∀ (T T' T'' T''' : C') (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T'''),
      L.M0.map χ (z T T' T'' φ ψ) + z T T'' T''' (φ ≫ ψ) χ = z T T' T''' φ (ψ ≫ χ) + z T' T'' T''' ψ χ := by
    intro T T' T'' T''' φ ψ χ
    refine sub_eq_zero.mp ((hq T''').inj0 _ ?_ ?_)
    · simp only [map_sub, map_add (f := _), L.diffZero_natural, hzd, L.M1.map_comp, Category.assoc]
      abel
    · have h := hz T T' T'' T''' φ ψ χ
      simp only [map_sub, map_add (f := _), a0m, hza, ← L'.M0.map_comp, Category.assoc]
      linear_combination (norm := abel1) h
  refine ⟨(z, α, η), ⟨hzc, fun T T' T'' φ ψ ↦ ?_, fun T T' φ ↦ ?_, hη0⟩, (-f, w), ?_⟩
  · show α T T'' (φ ≫ ψ) = L.M1.map ψ (α T T' φ) + α T' T'' ψ + L.d0 T'' (z T T' T'' φ ψ)
    rw [hzd]; abel
  · show η T' = L.M2.map φ (η T) + L.d1 T' (α T T' φ)
    rw [hA]; abel
  · refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext T T' T'' φ ψ
      simp [Cx.D1, hza]
      abel
    · funext T T' φ
      have h := hB T T' φ
      simp [Cx.D1]
      linear_combination (norm := abel1) h
    · funext T
      simp [Cx.D1, hηw T]

theorem vertical_h2_surjective {C : Type a} [Category.{0} C] {K : Cx C} {K' : Cx C'} (m : CxMap K K')
    (hq : m.QAll) : Function.Surjective m.vert.h2 := by
  intro y
  obtain ⟨⟨c', hc'⟩, rfl⟩ := QuotientAddGroup.mk_surjective y
  obtain ⟨c, hc, g, hg⟩ := core (L := K.res m.G) m.a0 m.a1 m.a2 m.compDegreeZero_natural m.compDegreeOne_natural m.compDegreeTwo_natural m.comp_commutes_diffZero m.comp_commutes_diffOne hq c' hc'
  refine ⟨QuotientAddGroup.mk ⟨c, hc⟩, ?_⟩
  rw [CxMap.h2, QuotientAddGroup.map_mk, QuotientAddGroup.eq]
  refine ⟨g, ?_⟩
  show K'.D1 g = -(m.vert.p2 c) + c'
  rw [hg]
  show K'.D1 g = -(m.vert.p2 c) + (m.vert.p2 c + K'.D1 g)
  abel

theorem main.{a', b'} : VertHas.{a', b'} (fun m ↦ Function.Surjective m.h2) :=
  fun m hq ↦ vertical_h2_surjective m hq

theorem inst : VertHas.{1,1} (fun m ↦ Function.Surjective m.h2) ∧
    VertHas.{1,0} (fun m ↦ Function.Surjective m.h2) ∧ VertHas.{0,0} (fun m ↦ Function.Surjective m.h2) :=
  ⟨main, main, main⟩

end GlobalTheory.CxCoh.VertSurjTwo
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace GlobalTheory.CxCoh

universe a b

theorem cocycle_two_isCoboundary_of_objectwiseQuasiIso {C : Type b} [Category.{0} C] {L K : Cx C}
    (a0 : ∀ T, L.M0.obj T →+ K.M0.obj T) (a1 : ∀ T, L.M1.obj T →+ K.M1.obj T)
    (a2 : ∀ T, L.M2.obj T →+ K.M2.obj T)
    (compDegreeZero_natural : ∀ {T T' : C} (φ : T ⟶ T') x, a0 T' (L.M0.map φ x) = K.M0.map φ (a0 T x))
    (compDegreeOne_natural : ∀ {T T' : C} (φ : T ⟶ T') x, a1 T' (L.M1.map φ x) = K.M1.map φ (a1 T x))
    (comp_commutes_diffZero : ∀ T x, a1 T (L.d0 T x) = K.d0 T (a0 T x))
    (comp_commutes_diffOne : ∀ T x, a2 T (L.d1 T x) = K.d1 T (a1 T x))
    (hq : ∀ T, IsQ (L.d0 T) (L.d1 T) (L.d2 T) (K.d0 T) (K.d1 T) (K.d2 T) (a0 T) (a1 T) (a2 T))
    (z : L.T2) (hz : z ∈ L.Z2) (c' : K.T1)
    (E0 : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''),
      K.M0.map ψ (c'.1 T T' φ) - c'.1 T T'' (φ ≫ ψ) + c'.1 T' T'' ψ = a0 T'' (z.1 T T' T'' φ ψ))
    (E1 : ∀ T T' (φ : T ⟶ T'),
      c'.2 T' - K.M1.map φ (c'.2 T) - K.d0 T' (c'.1 T T' φ) = a1 T' (z.2.1 T T' φ))
    (E2 : ∀ T, K.d1 T (c'.2 T) = a2 T (z.2.2 T)) :
    ∃ c, L.D1 c = z := by
  obtain ⟨Za, Zb, Zc, Zd⟩ := hz
  choose ω₁ hω₁ using fun T ↦ (hq T).inj2 (z.2.2 T) (c'.2 T) (Zd T) (E2 T).symm
  have h1 : ∀ T, K.d1 T (c'.2 T - a1 T (ω₁ T)) = 0 := fun T ↦ by
    rw [map_sub, E2, ← comp_commutes_diffOne, hω₁, sub_self]
  choose ω₂ w hω₂ hw using fun T ↦ (hq T).surj1 _ (h1 T)
  have hw' : ∀ T, a1 T (ω₂ T) = c'.2 T - a1 T (ω₁ T) - K.d0 T (w T) := fun T ↦ by
    rw [hw T]; abel
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : ∀ T, L.M1.obj T, ∀ T, Ω T = ω₁ T + ω₂ T := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : L.M1.c1, ∀ T T' (φ : T ⟶ T'),
      α T T' φ = z.2.1 T T' φ - (Ω T' - L.M1.map φ (Ω T)) := ⟨_, fun _ _ _ ↦ rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : K.M0.c1, ∀ T T' (φ : T ⟶ T'),
      f T T' φ = c'.1 T T' φ - (w T' - K.M0.map φ (w T)) := ⟨_, fun _ _ _ ↦ rfl⟩
  have hα1 : ∀ T T' (φ : T ⟶ T'), L.d1 T' (α T T' φ) = 0 := fun T T' φ ↦ by
    have hc := Zc T T' φ
    simp only [hα, hΩ, map_sub, map_add (f := _), L.diffOne_natural, hω₁, hω₂, add_zero, map_zero]
    rw [hc]; abel
  have hα2 : ∀ T T' (φ : T ⟶ T'), a1 T' (α T T' φ) = K.d0 T' (-f T T' φ) := fun T T' φ ↦ by
    simp only [hα, hΩ, hf, map_sub, map_add (f := _), map_neg, compDegreeOne_natural, hw', ← E1, K.diffZero_natural]
    abel
  choose g hg using fun T T' (φ : T ⟶ T') ↦
    (hq T').inj1 (α T T' φ) (-f T T' φ) (hα1 T T' φ) (hα2 T T' φ)
  have h3 : ∀ T T' (φ : T ⟶ T'), K.d0 T' (f T T' φ + a0 T' (g T T' φ)) = 0 := fun T T' φ ↦ by
    rw [map_add (f := _), ← comp_commutes_diffZero, hg, hα2, map_neg, add_neg_cancel]
  choose f₂ hf₂ hf₂' using fun T T' (φ : T ⟶ T') ↦ (hq T').surj0 _ (h3 T T' φ)
  refine ⟨(fun T T' φ ↦ f₂ T T' φ - g T T' φ, Ω), Prod.ext (funext fun T ↦ funext fun T' ↦
    funext fun T'' ↦ funext fun φ ↦ funext fun ψ ↦ ?_) (Prod.ext (funext fun T ↦ funext fun T' ↦
    funext fun φ ↦ ?_) (funext fun T ↦ ?_))⟩
  · change L.M0.map ψ (f₂ T T' φ - g T T' φ) - (f₂ T T'' (φ ≫ ψ) - g T T'' (φ ≫ ψ))
      + (f₂ T' T'' ψ - g T' T'' ψ) = z.1 T T' T'' φ ψ
    have hZb : L.d0 T'' (z.1 T T' T'' φ ψ) =
        z.2.1 T T'' (φ ≫ ψ) - L.M1.map ψ (z.2.1 T T' φ) - z.2.1 T' T'' ψ := by
      rw [Zb T T' T'' φ ψ]; abel
    have hd : L.d0 T'' (z.1 T T' T'' φ ψ - (L.M0.map ψ (f₂ T T' φ - g T T' φ) -
        (f₂ T T'' (φ ≫ ψ) - g T T'' (φ ≫ ψ)) + (f₂ T' T'' ψ - g T' T'' ψ))) = 0 := by
      simp only [map_sub, map_add (f := _), L.diffZero_natural, hf₂, hg, hα, hZb, L.M1.map_comp, map_zero]
      abel
    have ha : a0 T'' (z.1 T T' T'' φ ψ - (L.M0.map ψ (f₂ T T' φ - g T T' φ) -
        (f₂ T T'' (φ ≫ ψ) - g T T'' (φ ≫ ψ)) + (f₂ T' T'' ψ - g T' T'' ψ))) = 0 := by
      simp only [map_sub, map_add (f := _), compDegreeZero_natural, hf₂', ← E0, hf, K.M0.map_comp]
      abel
    exact (sub_eq_zero.mp ((hq T'').inj0 _ hd ha)).symm
  · change Ω T' - L.M1.map φ (Ω T) - L.d0 T' (f₂ T T' φ - g T T' φ) = z.2.1 T T' φ
    rw [map_sub, hf₂, hg, hα]; abel
  · change L.d1 T (Ω T) = z.2.2 T
    rw [hΩ, map_add (f := _), hω₁, hω₂, add_zero]

theorem vertical_h2_injective : VertHas.{a, b} (fun m ↦ Function.Injective m.h2) := by
  intro C _ C' _ K K' m hq
  refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hx' : (QuotientAddGroup.mk (m.vert.z2 z) : K'.H2) = 0 := hx
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at hx' ⊢
  obtain ⟨c', hc'⟩ := hx'
  exact cocycle_two_isCoboundary_of_objectwiseQuasiIso (L := K.res m.G) (K := K') m.a0 m.a1 m.a2 m.compDegreeZero_natural m.compDegreeOne_natural
    m.comp_commutes_diffZero m.comp_commutes_diffOne hq z.1 z.2 c'
    (fun T T' T'' φ ψ ↦ congrArg (fun c ↦ c.1 T T' T'' φ ψ) hc')
    (fun T T' φ ↦ congrArg (fun c ↦ c.2.1 T T' φ) hc')
    (fun T ↦ congrArg (fun c ↦ c.2.2 T) hc')

theorem vertical_h2_injective_universes :
    VertHas.{1,1} (fun m ↦ Function.Injective m.h2) ∧ VertHas.{1,0} (fun m ↦ Function.Injective m.h2) ∧
      VertHas.{0,0} (fun m ↦ Function.Injective m.h2) :=
  ⟨vertical_h2_injective, vertical_h2_injective, vertical_h2_injective⟩

end GlobalTheory.CxCoh
end
end

section

open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory.CxCoh.Cx

theorem fnMap_h1_bijective (C : Type 1) [Category.{0} C] (K : Cx C) (hA0 : K.M1.Ac0)
    (hA1 : K.M1.Ac1) (hB0 : K.M2.Ac0) : Function.Bijective K.fnMap.h1 := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨c, rfl⟩ := QuotientAddGroup.mk_surjective x
    have hc : K.D1 c.1 = 0 := c.2
    rw [CxMap.h1, QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff,
      AddSubgroup.mem_addSubgroupOf] at hx
    obtain ⟨g, hg⟩ := hx
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    refine ⟨g, ?_⟩
    have hf : ∀ T T' (φ : T ⟶ T'), c.1.1 T T' φ = g T' - K.M0.map φ (g T) := by
      intro T T' φ
      have := congrArg (fun p => p.1 T T' φ) hg
      exact this.symm
    have h2c : ∀ T T' (φ : T ⟶ T'),
        c.1.2 T' - K.M1.map φ (c.1.2 T) - K.d0 T' (c.1.1 T T' φ) = 0 := by
      intro T T' φ
      have := congrArg (fun p => p.2.1 T T' φ) hc
      simpa [Cx.D1] using this
    have hw := hA0 (fun T => c.1.2 T - K.d0 T (g T)) (by
      intro T T' φ
      have := h2c T T' φ
      rw [hf, map_sub, K.diffZero_natural] at this
      simp only [map_sub]
      rw [← sub_eq_zero, ← this]; abel)
    refine Prod.ext (funext fun T => funext fun T' => funext fun φ => ?_) (funext fun T => ?_)
    · simp [Cx.D0, hf]
    · have := congrFun hw T
      simp only [Pi.zero_apply, sub_eq_zero] at this
      simp [Cx.D0, this]
  · intro y
    obtain ⟨c, rfl⟩ := QuotientAddGroup.mk_surjective y
    have hc : (Cx.single K.M0).D1 c.1 = 0 := c.2
    have hδ : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''),
        K.M0.map ψ (c.1.1 T T' φ) - c.1.1 T T'' (φ ≫ ψ) + c.1.1 T' T'' ψ = 0 := by
      intro T T' T'' φ ψ
      have := congrArg (fun p => p.1 T T' T'' φ ψ) hc
      simpa [Cx.D1] using this
    obtain ⟨w, hw⟩ := hA1 (fun T T' φ => K.d0 T' (c.1.1 T T' φ)) (by
      intro T T' T'' φ ψ
      have h := congrArg (K.d0 T'') (hδ T T' T'' φ ψ)
      simp only [map_add (f := _), map_sub, map_zero, K.diffZero_natural] at h ⊢
      rw [← sub_eq_zero, ← neg_eq_zero, ← h]; abel)
    have hdw := hB0 (fun T => K.d1 T (w T)) (by
      intro T T' φ
      have h := congrArg (K.d1 T') (hw T T' φ)
      rw [K.diffOne_diffZero, map_sub, K.diffOne_natural] at h
      exact (sub_eq_zero.mp h.symm))
    let z : K.Z1 := ⟨(c.1.1, w), by
      show K.D1 _ = 0
      refine Prod.ext (funext fun T => funext fun T' => funext fun T'' => funext fun φ =>
        funext fun ψ => ?_) (Prod.ext (funext fun T => funext fun T' => funext fun φ => ?_)
        (funext fun T => ?_))
      · simpa [Cx.D1] using hδ T T' T'' φ ψ
      · simp [Cx.D1, hw T T' φ]
      · simpa [Cx.D1] using congrFun hdw T⟩
    refine ⟨QuotientAddGroup.mk z, ?_⟩
    rw [CxMap.h1, QuotientAddGroup.map_mk]
    congr 1
end GlobalTheory.CxCoh.Cx
end

section

open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory.CxCoh.VertQ

universe a b

theorem D0_eq_iff {C' : Type b} [Category.{0} C'] (L : Cx C') (g : L.M0.c0) (c : L.T1) :
    L.D0 g = c ↔ (∀ T T' (φ : T ⟶ T'), g T' - L.M0.map φ (g T) = c.1 T T' φ) ∧
      ∀ T, L.d0 T (g T) = c.2 T := by
  constructor
  · rintro rfl; exact ⟨fun _ _ _ => rfl, fun _ => rfl⟩
  · rintro ⟨h1, h2⟩
    refine Prod.ext ?_ ?_
    · funext T T' φ; exact h1 T T' φ
    · funext T; exact h2 T

theorem components_of_D0_eq_zero {C' : Type b} [Category.{0} C'] (L : Cx C') (g : L.M0.c0) (h : L.D0 g = 0) :
    (∀ T T' (φ : T ⟶ T'), g T' - L.M0.map φ (g T) = 0) ∧ ∀ T, L.d0 T (g T) = 0 :=
  (D0_eq_iff L g 0).1 h

theorem D0_eq_zero_of_compat_of_d0_eq_zero {C' : Type b} [Category.{0} C'] (L : Cx C') (g : L.M0.c0)
    (h1 : ∀ T T' (φ : T ⟶ T'), g T' - L.M0.map φ (g T) = 0) (h2 : ∀ T, L.d0 T (g T) = 0) :
    L.D0 g = 0 :=
  (D0_eq_iff L g 0).2 ⟨h1, h2⟩

theorem components_of_D1_eq_zero {C' : Type b} [Category.{0} C'] (L : Cx C') (c : L.T1) (h : L.D1 c = 0) :
    (∀ T T' (φ : T ⟶ T'), c.2 T' - L.M1.map φ (c.2 T) - L.d0 T' (c.1 T T' φ) = 0) ∧
      ∀ T, L.d1 T (c.2 T) = 0 := by
  refine ⟨fun T T' φ => ?_, fun T => ?_⟩
  · have := congrFun (congrFun (congrFun (congrArg (fun x => x.2.1) h) T) T') φ
    exact this
  · have := congrFun (congrArg (fun x => x.2.2) h) T
    exact this

variable {C : Type a} [Category.{0} C] {C' : Type b} [Category.{0} C']

theorem vertical_h0_injective {K : Cx C} {K' : Cx C'} (m : CxMap K K') (hq : m.QAll) :
    Function.Injective m.vert.h0 := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  rintro ⟨g, hg⟩ h
  have hg' := components_of_D0_eq_zero _ g (AddMonoidHom.mem_ker.1 hg)
  apply Subtype.ext
  funext T
  have hT : m.a0 T (g T) = 0 := congrFun (congrArg Subtype.val h) T
  exact (hq T).inj0 _ (hg'.2 T) hT

theorem vertical_h0_surjective {K : Cx C} {K' : Cx C'} (m : CxMap K K') (hq : m.QAll) :
    Function.Surjective m.vert.h0 := by
  rintro ⟨y, hy⟩
  have hy' := components_of_D0_eq_zero K' y (AddMonoidHom.mem_ker.1 hy)
  choose x hx0 hxa using fun T => (hq T).surj0 (y T) (hy'.2 T)
  refine ⟨⟨x, AddMonoidHom.mem_ker.2 (D0_eq_zero_of_compat_of_d0_eq_zero (K.res m.G) x (fun T T' φ => ?_) hx0)⟩, Subtype.ext (funext hxa)⟩
  show x T' - K.M0.map (m.G.map φ) (x T) = 0
  apply (hq T').inj0
  · rw [map_sub, hx0 T', K.diffZero_natural, hx0 T, map_zero, sub_zero]
  · rw [map_sub, hxa T', m.compDegreeZero_natural, hxa T]
    exact hy'.1 T T' φ

theorem vertical_h1_injective {K : Cx C} {K' : Cx C'} (m : CxMap K K') (hq : m.QAll) :
    Function.Injective m.vert.h1 := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨⟨⟨f, ω⟩, hfω⟩, rfl⟩ := QuotientAddGroup.mk_surjective c
  rw [CxMap.h1, QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff,
    AddSubgroup.mem_addSubgroupOf] at hc
  obtain ⟨g', hg'⟩ := hc
  have hg'' := (D0_eq_iff K' g' _).1 hg'
  have hc1 := components_of_D1_eq_zero _ _ (AddMonoidHom.mem_ker.1 hfω)
  have e0 : ∀ T, K'.d0 T (g' T) = m.a1 T (ω T) := fun T => hg''.2 T
  have e3 : ∀ T T' (φ : T ⟶ T'), m.a0 T' (f T T' φ) = g' T' - K'.M0.map φ (g' T) :=
    fun T T' φ => (hg''.1 T T' φ).symm
  have hc1a : ∀ T T' (φ : T ⟶ T'), ω T' - K.M1.map (m.G.map φ) (ω T) - K.d0 _ (f T T' φ) = 0 :=
    hc1.1
  choose w hw using fun T => (hq T).inj1 (ω T) (g' T) (hc1.2 T) (e0 T).symm
  choose u hu0 hua using fun T => (hq T).surj0 (g' T - m.a0 T (w T))
    (by rw [map_sub, e0 T, ← m.comp_commutes_diffZero, hw T, sub_self])
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  refine ⟨fun T => w T + u T, (D0_eq_iff _ _ _).2 ⟨fun T T' φ => ?_, fun T => ?_⟩⟩
  · show w T' + u T' - K.M0.map (m.G.map φ) (w T + u T) = f T T' φ
    rw [← sub_eq_zero]
    apply (hq T').inj0
    · rw [map_sub, map_sub, K.diffZero_natural, map_add (f := _), map_add (f := _), hw, hw, hu0, hu0, add_zero, add_zero]
      exact hc1a T T' φ
    · have e1 : m.a0 T' (w T' + u T') = g' T' := by rw [map_add (f := _), hua]; abel
      have e2 : m.a0 T' (K.M0.map (m.G.map φ) (w T + u T)) = K'.M0.map φ (g' T) := by
        rw [m.compDegreeZero_natural, map_add (f := _), hua, add_sub_cancel]
      rw [map_sub, map_sub, e1, e2, e3]
      abel
  · show K.d0 _ (w T + u T) = ω T
    rw [map_add (f := _), hw, hu0, add_zero]

theorem main : VertHas.{a,b} (fun m ↦ Function.Bijective m.h0 ∧ Function.Injective m.h1) :=
  fun m hq => ⟨⟨vertical_h0_injective m hq, vertical_h0_surjective m hq⟩, vertical_h1_injective m hq⟩

end GlobalTheory.CxCoh.VertQ

theorem GlobalTheory.CxCoh.vertical_bijective_h0_injective_h1 :
    VertHas.{1,1} (fun m ↦ Function.Bijective m.h0 ∧ Function.Injective m.h1) ∧
    VertHas.{1,0} (fun m ↦ Function.Bijective m.h0 ∧ Function.Injective m.h1) ∧
    VertHas.{0,0} (fun m ↦ Function.Bijective m.h0 ∧ Function.Injective m.h1) :=
  ⟨VertQ.main.{1,1}, VertQ.main.{1,0}, VertQ.main.{0,0}⟩
end

section

open Polynomial

theorem _root_.GlobalTheory.T.exists_selfReciprocalInvAlg_with_poly : ∀ (K : GlobalTheory.UnitLemma.UQ) (P : K.E[X]), P.Monic → C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse → ∃ B : GlobalTheory.UnitLemma.InvAlg K, B.g * B.σ B.g = 1 ∧ B.P = P := by
  first | exact @GlobalTheory.UnitLemma.exists_invAlg_root | exact GlobalTheory.UnitLemma.exists_invAlg_root | (intros; apply GlobalTheory.UnitLemma.exists_invAlg_root <;> assumption)
end
