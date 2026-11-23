module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CechDeRhamCoefMapOneFormsRestrictAlongFunctor
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle262
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
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

theorem pullHyp2_restrict_injective {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type}
    [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C)
    (h2 : Function.Injective (CoefMap.restrict F G).pull2)
    (h1 : Function.Surjective (CoefMap.restrict F G).pull1)
    (hc : ∀ κ : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
        κ T T'' (φ ≫ ψ) = p1 F ψ (κ T T' φ) + κ T' T'' ψ) →
      ∀ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R],
        (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), κ _ _ (G.map a) = θ' t' - p1 F (G.map a) (θ' t)) →
        ∃ θ : A0 F, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - p1 F φ (θ T))
    (hf : Function.Surjective (pullGlob1 (CoefMap.restrict F G)))
    (hs : ∀ (T : C) (x : Om R (F.obj T) 2), (∀ t (u : T ⟶ G.obj t), pOm F 2 u x = 0) → x = 0) :
    Function.Injective (pullHyp2 (CoefMap.restrict F G)) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨c, rfl⟩ := Hyp2.mk_surjective F x
  rw [pullHyp2_mk, Hyp2.mk_eq_zero] at hx
  obtain ⟨⟨f₀, θ₀⟩, hfe⟩ := hx
  obtain ⟨f', rfl⟩ : ∃ f' : ∀ (t t' : C') (_ : t ⟶ t'), F.obj (G.obj t'), (f' : C1 (G ⋙ F)) = f₀ :=
    ⟨f₀, rfl⟩
  obtain ⟨θ', rfl⟩ : ∃ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], (θ' : A0 (G ⋙ F)) = θ₀ := ⟨θ₀, rfl⟩
  have hz : ∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''),
      mp F (G.map b) (f' t t' a) - f' t t'' (a ≫ b) + f' t' t'' b =
        c.1.1 _ _ _ (G.map a) (G.map b) :=
    fun t t' t'' a b ↦ congrArg (fun y : Tot2 (G ⋙ F) ↦ y.1 t t' t'' a b) hfe
  have ha : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'),
      θ' t' - p1 F (G.map a) (θ' t) - D R _ (f' t t' a) = c.1.2.1 _ _ (G.map a) :=
    fun t t' a ↦ (congrArg (fun y : Tot2 (G ⋙ F) ↦ y.2.1 t t' a) hfe).trans (cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t' _)
  have hη : ∀ t, dOne R _ (θ' t) = c.1.2.2 (G.obj t) :=
    fun t ↦ (congrArg (fun y : Tot2 (G ⋙ F) ↦ y.2.2 t) hfe).trans (qOm_restrict F G t _)

  have hz0 : H2.mk F ⟨c.1.1, (mem_cechDeRhamTotalCocyclesTwo_iff.1 c.2).1⟩ = 0 := h2 (by
    rw [CoefMap.pullCohomologyTwo_class, map_zero]
    exact H2.mk_eq_zero.2 ⟨f', by funext t t' t'' a b; exact hz a b⟩)
  obtain ⟨f, hfz⟩ := H2.mk_eq_zero.1 hz0
  have hf1 : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
      mp F ψ (f T T' φ) - f T T'' (φ ≫ ψ) + f T' T'' ψ = c.1.1 T T' T'' φ ψ :=
    fun T T' T'' φ ψ ↦ congrFun (congrFun (congrFun (congrFun (congrFun hfz T) T') T'') φ) ψ

  let u : Z1 (G ⋙ F) := ⟨fun t t' a ↦ f' t t' a - f _ _ (G.map a), fun t t' t'' a b ↦ by
    have e1 := hz a b
    have e2 := hf1 (G.map a) (G.map b)
    rw [← G.map_comp] at e2
    show f' t t'' (a ≫ b) - f _ _ (G.map (a ≫ b)) =
      mp F (G.map b) (f' t t' a - f _ _ (G.map a)) + (f' t' t'' b - f _ _ (G.map b))
    rw [map_sub]
    linear_combination e2 - e1⟩
  obtain ⟨g₀, hg₀⟩ := h1 (H1.mk _ u)
  obtain ⟨g, rfl⟩ := H1.mk_surjective F g₀
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_mk] at hg₀
  obtain ⟨h₀, hh'⟩ := hg₀
  obtain ⟨h', rfl⟩ : ∃ h' : ∀ t, F.obj (G.obj t), (h' : C0 (G ⋙ F)) = h₀ := ⟨h₀, rfl⟩
  have hfu : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), f' t t' a =
      f _ _ (G.map a) + g.1 _ _ (G.map a) - (h' t' - mp F (G.map a) (h' t)) := fun t t' a ↦ by
    have e : h' t' - mp F (G.map a) (h' t) = g.1 _ _ (G.map a) - (f' t t' a - f _ _ (G.map a)) :=
      congrFun (congrFun (congrFun hh' t) t') a
    linear_combination e
  obtain ⟨f₁, hf₁⟩ : ∃ f₁ : C1 F, ∀ T T' φ, f₁ T T' φ = f T T' φ + g.1 T T' φ := ⟨_, fun _ _ _ ↦ rfl⟩
  have hf1' : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
      mp F ψ (f₁ T T' φ) - f₁ T T'' (φ ≫ ψ) + f₁ T' T'' ψ = c.1.1 T T' T'' φ ψ := fun T T' T'' φ ψ ↦ by
    rw [hf₁, hf₁, hf₁, map_add (f := _)]
    linear_combination hf1 φ ψ - Z1.comp g φ ψ

  obtain ⟨a₁, ha₁⟩ : ∃ a₁ : A1 F, ∀ T T' φ, a₁ T T' φ = c.1.2.1 T T' φ + D R _ (f₁ T T' φ) :=
    ⟨_, fun _ _ _ ↦ rfl⟩
  have hac : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
      a₁ T T'' (φ ≫ ψ) = p1 F ψ (a₁ T T' φ) + a₁ T' T'' ψ := fun T T' T'' φ ψ ↦ by
    have e := cechDeRhamTotalCocyclesTwo.one c φ ψ
    rw [← hf1' φ ψ, map_add (f := _), map_sub] at e
    rw [ha₁, ha₁, ha₁, map_add (f := _), p1_D, e]
    abel
  obtain ⟨θ'', hθ''⟩ : ∃ θ'' : ∀ t, Ω[F.obj (G.obj t)⁄R], ∀ t, θ'' t = θ' t + D R _ (h' t) :=
    ⟨_, fun _ ↦ rfl⟩
  have hres : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), a₁ _ _ (G.map a) = θ'' t' - p1 F (G.map a) (θ'' t) :=
    fun t t' a ↦ by
      have e := ha a
      rw [hfu a] at e
      simp only [map_add (f := _), map_sub] at e
      rw [ha₁, hθ'', hθ'', hf₁]
      simp only [map_add (f := _), p1_D]
      linear_combination (norm := abel1) -e
  obtain ⟨θ, hθ⟩ := hc a₁ hac θ'' hres

  let ω' : Glob1 (G ⋙ F) := ⟨fun t ↦ θ (G.obj t) - θ'' t, fun t t' a ↦ by
    have e1 := hθ (G.map a)
    have e2 := hres a
    show θ (G.obj t') - θ'' t' = p1 F (G.map a) (θ (G.obj t) - θ'' t)
    rw [map_sub]
    linear_combination (norm := abel1) e2 - e1⟩
  obtain ⟨ω, hω⟩ := hf ω'
  have hωG : ∀ t, ω.1 (G.obj t) = θ (G.obj t) - θ'' t := fun t ↦
    (cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t _).symm.trans (congrArg (fun y : Glob1 (G ⋙ F) ↦ y.1 t) hω)
  obtain ⟨θ₁, hθ₁⟩ : ∃ θ₁ : A0 F, ∀ T, θ₁ T = θ T - ω.1 T := ⟨_, fun _ ↦ rfl⟩
  have hθ1 : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), a₁ T T' φ = θ₁ T' - p1 F φ (θ₁ T) := fun T T' φ ↦ by
    rw [hθ₁, hθ₁, map_sub, ← ω.2 φ, hθ φ]; abel
  have hθ1G : ∀ t, θ₁ (G.obj t) = θ'' t := fun t ↦ by rw [hθ₁, hωG]; abel

  obtain ⟨η₂, hη₂⟩ : ∃ η₂ : W0 F 2, ∀ T, η₂ T = c.1.2.2 T - dOne R _ (θ₁ T) := ⟨_, fun _ ↦ rfl⟩
  have hη2 : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), η₂ T' = pOm F 2 φ (η₂ T) := fun T T' φ ↦ by
    have e1 := cechDeRhamTotalCocyclesTwo.two c φ
    have e2 := congrArg (dOne R _) (hθ1 φ)
    rw [ha₁] at e2
    simp only [map_add (f := _), map_sub, dOne_D, add_zero] at e2
    rw [hη₂, hη₂, map_sub, pOm_dOne]
    linear_combination (norm := abel1) e1 + e2
  have hη2G : ∀ t, η₂ (G.obj t) = 0 := fun t ↦ by
    rw [hη₂, hθ1G, hθ'', map_add (f := _), dOne_D, add_zero, ← hη t, sub_self]
  have hη0 : ∀ T, η₂ T = 0 := fun T ↦ hs T _ fun t u ↦ by rw [← hη2 u, hη2G]
  refine Hyp2.mk_eq_zero.2 ⟨(f₁, θ₁), Tot2.ext (fun T T' T'' φ ψ ↦ ?_) (fun T T' φ ↦ ?_) fun T ↦ ?_⟩
  · exact hf1' φ ψ
  · have e := hθ1 φ
    rw [ha₁] at e
    show θ₁ T' - p1 F φ (θ₁ T) - D R _ (f₁ T T' φ) = c.1.2.1 T T' φ
    linear_combination (norm := abel1) -e
  · have e := hη0 T
    rw [hη₂] at e
    exact (sub_eq_zero.1 e).symm

end GlobalTheory.CechDR
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

theorem pullHyp1_restrict_surjective {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type}
    [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C)
    (hO : Function.Surjective (CoefMap.restrict F G).pull1)
    (hc : ∀ κ : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
        κ T T'' (φ ≫ ψ) = p1 F ψ (κ T T' φ) + κ T' T'' ψ) →
      ∀ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], (∀ ⦃t t' : C'⦄ (a : t ⟶ t'),
        κ _ _ (G.map a) = θ' t' - p1 F (G.map a) (θ' t)) →
      ∃ θ : A0 F, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - p1 F φ (θ T))
    (hf : Function.Surjective (pullGlob1 (CoefMap.restrict F G)))
    (hs : ∀ (T : C) (η : Om R (F.obj T) 2), (∀ t (u : T ⟶ G.obj t), pOm F 2 u η = 0) → η = 0) :
    Function.Surjective (pullHyp1 (CoefMap.restrict F G)) := by
  intro c'
  obtain ⟨c', rfl⟩ := Hyp1.mk_surjective _ c'
  obtain ⟨h0, hh⟩ := hO (toO _ (Hyp1.mk _ c'))
  obtain ⟨f, rfl⟩ := H1.mk_surjective F h0
  rw [toO_mk, CoefMap.pullCohomologyOne_class, H1.mk_eq_mk] at hh
  obtain ⟨g', hg'⟩ := hh
  let g : ∀ t, F.obj (G.obj t) := g'
  let f' : ∀ (t t' : C') (_ : t ⟶ t'), F.obj (G.obj t') := c'.1.1
  let ω' : ∀ t, Ω[F.obj (G.obj t)⁄R] := c'.1.2
  have hga : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'),
      g t' - mp F (G.map a) (g t) = f.1 _ _ (G.map a) - f' t t' a := fun t t' a ↦
    congrFun (congrFun (congrFun hg' t) t') a
  have hκ : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
      D R _ (f.1 T T'' (φ ≫ ψ)) = p1 F ψ (D R _ (f.1 T T' φ)) + D R _ (f.1 T' T'' ψ) := by
    intro T T' T'' φ ψ
    rw [Z1.comp f φ ψ, map_add (f := _), p1_D]
  let θ' : ∀ t, Ω[F.obj (G.obj t)⁄R] := fun t ↦ ω' t + D R _ (g t)
  have hθ' : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'),
      D R _ (f.1 _ _ (G.map a)) = θ' t' - p1 F (G.map a) (θ' t) := by
    intro t t' a
    have e1 : ω' t' = p1 F (G.map a) (ω' t) + D R _ (f' t t' a) := cechDeRhamTotalCocyclesOne.conn c' a
    have e2 : f.1 _ _ (G.map a) = g t' - mp F (G.map a) (g t) + f' t t' a :=
      (sub_eq_iff_eq_add.1 (hga a).symm)
    simp only [θ']
    rw [e1, e2]
    simp only [map_add (f := _), map_sub, p1_D]
    abel
  obtain ⟨θ, hθ⟩ := hc (fun T T' φ ↦ D R _ (f.1 T T' φ)) hκ θ' hθ'
  have hθ2 : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), D R _ (f.1 T T' φ) = θ T' - p1 F φ (θ T) := hθ
  let ψ0 : Glob1 (G ⋙ F) := ⟨fun t ↦ θ' t - θ (G.obj t), fun t t' a ↦ by
    change θ' t' - θ (G.obj t') = p1 F (G.map a) (θ' t - θ (G.obj t))
    have e := (hθ2 (G.map a)).symm.trans (hθ' a)
    rw [map_sub]
    rw [← sub_eq_zero] at e ⊢
    rw [← neg_eq_zero, ← e]
    abel⟩
  obtain ⟨ψ, hψ⟩ := hf ψ0
  have hψG : ∀ t, ψ.1 (G.obj t) = θ' t - θ (G.obj t) := fun t ↦
    (cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t _).symm.trans (congrArg (fun z : Glob1 (G ⋙ F) ↦ z.1 t) hψ)
  let ω : A0 F := fun T ↦ θ T + ψ.1 T
  have hωG : ∀ t, ω (G.obj t) = θ' t := fun t ↦ by
    change θ (G.obj t) + ψ.1 (G.obj t) = _
    rw [hψG]; abel
  have hconn : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), ω T' = p1 F φ (ω T) + D R _ (f.1 T T' φ) := by
    intro T T' φ
    change θ T' + ψ.1 T' = p1 F φ (θ T + ψ.1 T) + D R _ (f.1 T T' φ)
    rw [map_add (f := _), ← ψ.2 φ, hθ2 φ]; abel
  have hclosed : ∀ T, dOne R _ (ω T) = 0 := by
    intro T
    refine hs T _ fun t u ↦ ?_
    have e : p1 F u (ω T) = ω' t + D R _ (g t) - D R _ (f.1 _ _ u) := by
      rw [eq_sub_iff_add_eq, ← hconn u, hωG]
    rw [pOm_dOne, e, map_sub, map_add (f := _), dOne_D, dOne_D]
    have e3 : dOne R _ (ω' t) = 0 := cechDeRhamTotalCocyclesOne.closed c' t
    rw [e3]; simp
  let c : cechDeRhamTotalCocyclesOne F := ⟨(f.1, ω), mem_cechDeRhamTotalCocyclesOne_iff.2 ⟨f.2, hconn, hclosed⟩⟩
  refine ⟨Hyp1.mk F c, ?_⟩
  rw [pullHyp1_mk, Hyp1.mk_eq_mk]
  refine ⟨g', Tot1.ext (fun t t' a ↦ hga a) fun t ↦ ?_⟩
  have e4 : q1 (CoefMap.restrict F G) t (ω (G.obj t)) = θ' t := (cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t _).trans (hωG t)
  change D R _ (g t) = q1 (CoefMap.restrict F G) t (ω (G.obj t)) - c'.1.2 t
  rw [e4]
  change _ = ω' t + D R _ (g t) - ω' t
  abel

end GlobalTheory.CechDR
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

theorem pullHyp2_restrict_surjective : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Function.Surjective (CoefMap.restrict F G).pull2 → (∀ κ : A2 F, (∀ ⦃T T' T'' T''' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T'''), p1 F χ (κ T T' T'' φ ψ) + κ T T'' T''' (φ ≫ ψ) χ = κ T T' T''' φ (ψ ≫ χ) + κ T' T'' T''' ψ χ) → ∀ β' : ∀ t t', (t ⟶ t') → Ω[F.obj (G.obj t')⁄R], (∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), κ _ _ _ (G.map a) (G.map b) = p1 F (G.map b) (β' t t' a) - β' t t'' (a ≫ b) + β' t' t'' b) → ∃ β : A1 F, ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T' T'' φ ψ = p1 F ψ (β T T' φ) - β T T'' (φ ≫ ψ) + β T' T'' ψ) → (∀ β' : ∀ t t', (t ⟶ t') → Ω[F.obj (G.obj t')⁄R], (∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), β' t t'' (a ≫ b) = p1 F (G.map b) (β' t t' a) + β' t' t'' b) → ∃ β : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), β T T'' (φ ≫ ψ) = p1 F ψ (β T T' φ) + β T' T'' ψ) ∧ ∃ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), β _ _ (G.map a) - β' t t' a = θ' t' - p1 F (G.map a) (θ' t)) → (∀ κ : W1 F 2, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T'' (φ ≫ ψ) = pOm F 2 ψ (κ T T' φ) + κ T' T'' ψ) → ∀ θ' : ∀ t, Om R (F.obj (G.obj t)) 2, (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), κ _ _ (G.map a) = θ' t' - pOm F 2 (G.map a) (θ' t)) → ∃ θ : W0 F 2, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - pOm F 2 φ (θ T)) → (∀ η' : ∀ t, Om R (F.obj (G.obj t)) 2, (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), η' t' = pOm F 2 (G.map a) (η' t)) → ∃ η : W0 F 2, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), η T' = pOm F 2 φ (η T)) ∧ ∀ t, η (G.obj t) = η' t) → (∀ (T : C) (x : Om R (F.obj T) 3), (∀ t (u : T ⟶ G.obj t), pOm F 3 u x = 0) → x = 0) → Function.Surjective (pullHyp2 (CoefMap.restrict F G)) := by
  intro R _ C _ C' _ F G hO hκ hl h2 he hs c'
  obtain ⟨c', rfl⟩ := Hyp2.mk_surjective _ c'
  obtain ⟨h0, hh⟩ := hO (H2.mk _ ⟨c'.1.1, (mem_cechDeRhamTotalCocyclesTwo_iff.1 c'.2).1⟩)
  obtain ⟨z, rfl⟩ := H2.mk_surjective F h0
  rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk] at hh
  obtain ⟨y', hy'⟩ := hh
  let z' : ∀ (t t' t'' : C') (_ : t ⟶ t') (_ : t' ⟶ t''), F.obj (G.obj t'') := c'.1.1
  let a' : ∀ (t t' : C') (_ : t ⟶ t'), Ω[F.obj (G.obj t')⁄R] := c'.1.2.1
  let η' : ∀ t : C', Om R (F.obj (G.obj t)) 2 := c'.1.2.2
  let y : ∀ (t t' : C') (_ : t ⟶ t'), F.obj (G.obj t') := y'
  have hz : ∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), z.1 _ _ _ (G.map a) (G.map b) =
      z' t t' t'' a b + (mp F (G.map b) (y t t' a) - y t t'' (a ≫ b) + y t' t'' b) := by
    intro t t' t'' a b
    have e := congrFun (congrFun (congrFun (congrFun (congrFun hy' t) t') t'') a) b
    change mp F (G.map b) (y t t' a) - y t t'' (a ≫ b) + y t' t'' b =
      z.1 _ _ _ (G.map a) (G.map b) - z' t t' t'' a b at e
    rw [e]; ring
  let a2 : ∀ (t t' : C') (_ : t ⟶ t'), Ω[F.obj (G.obj t')⁄R] := fun t t' a ↦ a' t t' a - D R _ (y t t' a)
  have ha2 : ∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), a2 t t'' (a ≫ b) =
      p1 F (G.map b) (a2 t t' a) + a2 t' t'' b + D R _ (z.1 _ _ _ (G.map a) (G.map b)) := by
    intro t t' t'' a b
    have e : a' t t'' (a ≫ b) = p1 F (G.map b) (a' t t' a) + a' t' t'' b +
      D R _ (z' t t' t'' a b) := cechDeRhamTotalCocyclesTwo.one c' a b
    simp only [a2]
    rw [e, hz, map_sub, p1_D]
    simp only [map_add (f := _), map_sub]
    abel

  obtain ⟨a₀, ha₀⟩ := hκ (fun T T' T'' φ ψ ↦ -D R _ (z.1 T T' T'' φ ψ)) (by
      intro T T' T'' T''' φ ψ χ
      have e := z.2 φ ψ χ
      simp only [p1_D, map_neg]
      rw [← neg_add, ← neg_add, ← map_add (f := _), ← map_add (f := _), e]) a2 (by
      intro t t' t'' a b
      beta_reduce
      rw [ha2]; abel)
  have ha₀' : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
      a₀ T T'' (φ ≫ ψ) = p1 F ψ (a₀ T T' φ) + a₀ T' T'' ψ + D R _ (z.1 T T' T'' φ ψ) := by
    intro T T' T'' φ ψ
    have e := ha₀ φ ψ
    beta_reduce at e
    linear_combination (norm := abel1) e
  obtain ⟨β, hβ, θ', hθ'⟩ := hl (fun t t' a ↦ a₀ _ _ (G.map a) - a2 t t' a) (by
      intro t t' t'' a b
      beta_reduce
      rw [G.map_comp, ha2, ha₀']
      simp only [a2, map_sub]
      abel)
  let a : A1 F := fun T T' φ ↦ a₀ T T' φ - β T T' φ
  have ha : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
      a T T'' (φ ≫ ψ) = p1 F ψ (a T T' φ) + a T' T'' ψ + D R _ (z.1 T T' T'' φ ψ) := by
    intro T T' T'' φ ψ
    simp only [a]
    rw [ha₀', hβ, map_sub]
    abel
  have haG : ∀ ⦃t t' : C'⦄ (b : t ⟶ t'), a _ _ (G.map b) =
      a2 t t' b - (θ' t' - p1 F (G.map b) (θ' t)) := by
    intro t t' b
    have e := hθ' b
    beta_reduce at e
    simp only [a]
    linear_combination (norm := abel1) -e
  let η3 : ∀ t : C', Om R (F.obj (G.obj t)) 2 := fun t ↦ η' t - dOne R _ (θ' t)
  have hη3 : ∀ ⦃t t' : C'⦄ (b : t ⟶ t'), dOne R _ (a _ _ (G.map b)) =
      η3 t' - pOm F 2 (G.map b) (η3 t) := by
    intro t t' b
    have e : η' t' = pOm F 2 (G.map b) (η' t) + dOne R _ (a' t t' b) := cechDeRhamTotalCocyclesTwo.two c' b
    simp only [η3]
    rw [haG, e]
    simp only [a2, map_sub, dOne_D, pOm_dOne]
    abel
  obtain ⟨η₀, hη₀⟩ := h2 (fun T T' φ ↦ dOne R _ (a T T' φ)) (by
      intro T T' T'' φ ψ
      beta_reduce
      rw [ha, map_add (f := _), map_add (f := _), dOne_D, pOm_dOne, add_zero]) η3 hη3
  obtain ⟨ε, hε, hεG⟩ := he (fun t ↦ η3 t - η₀ (G.obj t)) (by
      intro t t' b
      beta_reduce
      have e1 := hη3 b
      have e2 := hη₀ (G.map b)
      beta_reduce at e2
      rw [map_sub]
      linear_combination (norm := abel1) e2 - e1)
  let η : W0 F 2 := fun T ↦ η₀ T + ε T
  have hη : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), η T' = pOm F 2 φ (η T) + dOne R _ (a T T' φ) := by
    intro T T' φ
    have e := hη₀ φ
    beta_reduce at e
    simp only [η]
    rw [hε φ, e, map_add (f := _)]
    abel
  have hηG : ∀ t, η (G.obj t) = η3 t := by
    intro t
    simp only [η]
    rw [hεG t]
    abel
  have hclosed : ∀ T, dTwo R _ (η T) = 0 := by
    intro T
    refine hs T _ fun t u ↦ ?_
    have e : pOm F 2 u (η T) = η3 t - dOne R _ (a _ _ u) := by
      rw [← hηG, hη u]; abel
    have e3 : dTwo R _ (η' t) = 0 := cechDeRhamTotalCocyclesTwo.closed c' t
    rw [pOm_dTwo, e]
    simp only [η3, map_sub, dTwo_dOne, e3, sub_zero]
  let c : cechDeRhamTotalCocyclesTwo F := ⟨(z.1, a, η), mem_cechDeRhamTotalCocyclesTwo_iff.2 ⟨z.2, ha, hη, hclosed⟩⟩
  refine ⟨Hyp2.mk F c, ?_⟩
  rw [pullHyp2_mk, Hyp2.mk_eq_mk]
  refine ⟨(y, fun t ↦ -θ' t), Tot2.ext (fun t t' t'' b b' ↦ ?_) (fun t t' b ↦ ?_) fun t ↦ ?_⟩
  · change mp F (G.map b') (y t t' b) - y t t'' (b ≫ b') + y t' t'' b' =
      z.1 _ _ _ (G.map b) (G.map b') - z' t t' t'' b b'
    rw [hz]; ring
  · change -θ' t' - p1 F (G.map b) (-θ' t) - D R _ (y t t' b) =
      q1 (CoefMap.restrict F G) t' (a _ _ (G.map b)) - c'.1.2.1 t t' b
    have e4 : q1 (CoefMap.restrict F G) t' (a _ _ (G.map b)) =
        a2 t t' b - (θ' t' - p1 F (G.map b) (θ' t)) := (cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t' _).trans (haG b)
    rw [e4]
    change -θ' t' - p1 F (G.map b) (-θ' t) - D R _ (y t t' b) =
      a2 t t' b - (θ' t' - p1 F (G.map b) (θ' t)) - a' t t' b
    simp only [a2, map_neg]
    abel
  · change dOne R _ (-θ' t) = qOm (CoefMap.restrict F G) 2 t (η (G.obj t)) - c'.1.2.2 t
    have e5 : qOm (CoefMap.restrict F G) 2 t (η (G.obj t)) = η3 t :=
      (qOm_restrict F G t _).trans (hηG t)
    rw [e5]
    change dOne R _ (-θ' t) = η3 t - η' t
    simp only [η3, map_neg]
    abel

end GlobalTheory.CechDR
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem restrict_glob1_bijective : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (ω : Ω[F.obj T⁄R]), (∀ t (u : T ⟶ G.obj t), p1 F u ω = 0) → ω = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → Ω[F.obj (G.obj t)⁄R]), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = p1 F (G.map a) (s t u)) → ∃ ω : Ω[F.obj T⁄R], ∀ t u, p1 F u ω = s t u) → Function.Bijective (pullGlob1 (CoefMap.restrict F G)) := by
  intro R _ C _ C' _ F G hsep hglue
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro ω hω
    apply Subtype.ext
    funext T
    refine hsep T (ω.1 T) fun t u ↦ ?_
    have h1 := congrArg (fun x : Glob1 (G ⋙ F) ↦ x.1 t) hω
    have h2 : (pullGlob1 (CoefMap.restrict F G) ω).1 t = ω.1 (G.obj t) := cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t _
    rw [← ω.2 u, ← h2, h1]
    rfl
  · intro ω'
    have hc : ∀ (T : C), ∃ ω : Ω[F.obj T⁄R], ∀ t (u : T ⟶ G.obj t), p1 F u ω = ω'.1 t :=
      fun T ↦ hglue T (fun t _ ↦ ω'.1 t) fun t t' u a ↦ ω'.2 a
    choose ω hω using hc
    have hglob : ω ∈ Glob1 F := by
      intro T T' φ
      rw [← sub_eq_zero]
      refine hsep T' _ fun t u ↦ ?_
      rw [map_sub, ← oneFormsMapOfFunctorMorphism_comp, hω, hω, sub_self]
    refine ⟨⟨ω, hglob⟩, Subtype.ext (funext fun t ↦ ?_)⟩
    change q1 (CoefMap.restrict F G) t (ω (G.obj t)) = ω'.1 t
    rw [cechDeRhamCoefMapOneForms_restrictAlongFunctor, ← hω (G.obj t) t (𝟙 _), oneFormsMapOfFunctorMorphism_id]

end GlobalTheory
end
end

section

open GlobalTheory GlobalTheory.TopForm
open scoped TensorProduct

theorem _root_.GlobalTheory.T.kaehlerWedgeForm_map_eq_smul_of_basis : ∀ {k K L : Type} [CommRing k] [CommRing K] [CommRing L] (cK : k →+* K) (cL : k →+* L)
    (j : K →+* L), j.comp cK = cL → ∀ {n r : ℕ} (x w : Fin n → K) (bK : Module.Basis (Fin n) K (Omega cK)),
    (∀ i, bK i = dFun cK (w i)) → ∀ f : K, dForm cK x = f • dForm cK w → ∀ t : Fin r → L,
    dForm cL (Fin.append t (fun i => j (x i))) = j f • dForm cL (Fin.append t (fun i => j (w i))) := by
  first | exact @GlobalTheory.TopFormAppend.dForm_append_eq_smul | exact GlobalTheory.TopFormAppend.dForm_append_eq_smul | (intros; apply GlobalTheory.TopFormAppend.dForm_append_eq_smul <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.isStrictlyHenselian_of_isField_monicRoots : ∀ (T : Type) [CommRing T], IsField T → AIC T → SH T := by
  first | (exact @GlobalTheory.EtC.isField_aic_sh) | (exact GlobalTheory.EtC.isField_aic_sh) | (intros; apply GlobalTheory.EtC.isField_aic_sh  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.cechNerve_level_preserves_cofiltered_limit : ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (A : I ⥤ Arrow PSh) (cA : Cone A), IsLimit (Arrow.leftFunc.mapCone cA) → (∀ ⦃i j : I⦄ (f : i ⟶ j), IsIso (A.map f).right) → (∀ i, IsIso (cA.π.app i).right) → ∀ k : SimplexCategoryᵒᵖ, Nonempty (IsLimit (((evaluation _ PSh).obj k).mapCone (SimplicialObject.cechNerve.mapCone cA))) := by
  first | exact @GlobalTheory.cech_level_limit | exact GlobalTheory.cech_level_limit | (intros; apply GlobalTheory.cech_level_limit <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties : ∀ (R : Type) [CommRing R] (F : Shv R), (∀ n : ℤ, Injective ((res R F).X n)) ∧ (∀ n : ℤ, n < 0 → IsZero ((res R F).X n)) ∧ Mono (resι R F) ∧ (∃ w : resι R F ≫ (res R F).d 0 1 = 0, (ShortComplex.mk _ _ w).Exact) ∧ (∀ n : ℤ, n ≠ 0 → (res R F).ExactAt n) ∧ ∀ (E : Spc) (n : ℤ), 0 < n → IsZero (((chains R).obj E).X n) := by
  first | exact @GlobalTheory.EtC.res_basic | exact GlobalTheory.EtC.res_basic | (intros; apply GlobalTheory.EtC.res_basic <;> assumption)
end
