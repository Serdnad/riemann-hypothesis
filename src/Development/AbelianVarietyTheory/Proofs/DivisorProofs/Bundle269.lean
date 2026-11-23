module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle004
public import Mathlib.RingTheory.Unramified.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle158
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory.CxCoh.VertSurj

universe a b

theorem surj_of_id {C' : Type b} [Category.{0} C'] {K K' : Cx C'} (m : CxMap K K')
    (hG : m.G = 𝟭 C') (hQ : m.QAll) : Function.Surjective m.h1 := by
  obtain ⟨G, a0, a1, a2, a3, compDegreeZero_natural, compDegreeOne_natural, compDegreeTwo_natural, comp_commutes_diffZero, comp_commutes_diffOne, comp_commutes_diffTwo⟩ := m
  dsimp only at hG
  subst hG
  simp only [Functor.id_obj, Functor.id_map] at compDegreeZero_natural compDegreeOne_natural comp_commutes_diffZero comp_commutes_diffOne
  dsimp only [CxMap.QAll, Functor.id_obj] at hQ
  intro c
  obtain ⟨⟨⟨f', ω'⟩, hc⟩, rfl⟩ := QuotientAddGroup.mk_surjective c
  have hc' : K'.D1 (f', ω') = 0 := hc
  have hA : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''),
      K'.M0.map ψ (f' T T' φ) - f' T T'' (φ ≫ ψ) + f' T' T'' ψ = 0 :=
    fun T T' T'' φ ψ ↦ congrFun (congrFun (congrFun (congrFun (congrFun (congrArg Prod.fst hc') T) T') T'') φ) ψ
  have hB : ∀ T T' (φ : T ⟶ T'), ω' T' - K'.M1.map φ (ω' T) - K'.d0 T' (f' T T' φ) = 0 :=
    fun T T' φ ↦ congrFun (congrFun (congrFun (congrArg (fun x ↦ x.2.1) hc') T) T') φ
  have hC : ∀ T, K'.d1 T (ω' T) = 0 := fun T ↦ congrFun (congrArg (fun x ↦ x.2.2) hc') T
  choose ω w hω hωw using fun T ↦ (hQ T).surj1 (ω' T) (hC T)

  have hE : ∀ T T' (φ : T ⟶ T'), a1 T' (ω T' - K.M1.map φ (ω T)) =
      K'.d0 T' (f' T T' φ - (w T' - K'.M0.map φ (w T))) := by
    intro T T' φ
    have h1 := hωw T'
    have h2 := hωw T
    have h3 := hB T T' φ
    rw [map_sub, compDegreeOne_natural]
    have e1 : a1 T' (ω T') = ω' T' - K'.d0 T' (w T') := by rw [h1]; abel
    have e2 : a1 T (ω T) = ω' T - K'.d0 T (w T) := by rw [h2]; abel
    rw [e1, e2]; simp only [map_sub]; rw [← K'.diffZero_natural]
    have e3 : ω' T' = K'.M1.map φ (ω' T) + K'.d0 T' (f' T T' φ) := by rw [← sub_eq_zero, ← h3]; abel
    rw [e3]; abel
  choose f₁ hf₁ using fun T T' (φ : T ⟶ T') ↦ (hQ T').inj1 (ω T' - K.M1.map φ (ω T))
    (f' T T' φ - (w T' - K'.M0.map φ (w T)))
    (by rw [map_sub, K.diffOne_natural, hω, hω, map_zero, sub_zero]) (hE T T' φ)
  choose f₂ hf₂0 hf₂ using fun T T' (φ : T ⟶ T') ↦ (hQ T').surj0
    (f' T T' φ - (w T' - K'.M0.map φ (w T)) - a0 T' (f₁ T T' φ))
    (by rw [map_sub, ← comp_commutes_diffZero, hf₁, hE, sub_self])
  have hfa : ∀ T T' (φ : T ⟶ T'), a0 T' (f₁ T T' φ + f₂ T T' φ) =
      f' T T' φ - (w T' - K'.M0.map φ (w T)) := by
    intro T T' φ; rw [map_add (f := _), hf₂]; abel
  have hfd : ∀ T T' (φ : T ⟶ T'), K.d0 T' (f₁ T T' φ + f₂ T T' φ) = ω T' - K.M1.map φ (ω T) := by
    intro T T' φ; rw [map_add (f := _), hf₁, hf₂0, add_zero]
  let f : K.M0.c1 := fun T T' φ ↦ f₁ T T' φ + f₂ T T' φ
  have hfa' : ∀ T T' (φ : T ⟶ T'), a0 T' (f T T' φ) = f' T T' φ - (w T' - K'.M0.map φ (w T)) := hfa
  have hfd' : ∀ T T' (φ : T ⟶ T'), K.d0 T' (f T T' φ) = ω T' - K.M1.map φ (ω T) := hfd
  clear_value f
  have hZ : ((f, ω) : K.T1) ∈ K.Z1 := by
    show K.D1 (f, ω) = 0
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext T T' T'' φ ψ
      show K.M0.map ψ (f T T' φ) - f T T'' (φ ≫ ψ) + f T' T'' ψ = 0
      apply (hQ T'').inj0
      · simp only [map_add (f := _), map_sub, K.diffZero_natural, hfd', K.M1.map_comp]; abel
      · rw [map_add (f := _), map_sub, compDegreeZero_natural, hfa', hfa', hfa']
        simp only [map_sub, K'.M0.map_comp]
        linear_combination (norm := abel1) hA T T' T'' φ ψ
    · funext T T' φ
      show ω T' - K.M1.map φ (ω T) - K.d0 T' (f T T' φ) = 0
      rw [hfd', sub_self]
    · funext T
      exact hω T
  refine ⟨QuotientAddGroup.mk ⟨(f, ω), hZ⟩, ?_⟩
  show QuotientAddGroup.mk (CxMap.z1 _ ⟨(f, ω), hZ⟩) = QuotientAddGroup.mk _
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  refine ⟨w, Prod.ext ?_ ?_⟩
  · funext T T' φ
    show w T' - K'.M0.map φ (w T) = -(a0 T' (f T T' φ)) + f' T T' φ
    rw [hfa']; abel
  · funext T
    show K'.d0 T (w T) = -(a1 T (ω T)) + ω' T
    rw [hωw T]; abel

theorem main : VertHas.{a, b} (fun m ↦ Function.Surjective m.h1) := by
  intro C _ C' _ K K' m hQ
  exact surj_of_id m.vert rfl hQ

theorem instances : VertHas.{1,1} (fun m ↦ Function.Surjective m.h1) ∧
    VertHas.{1,0} (fun m ↦ Function.Surjective m.h1) ∧ VertHas.{0,0} (fun m ↦ Function.Surjective m.h1) :=
  ⟨main, main, main⟩

end GlobalTheory.CxCoh.VertSurj
end

section

open CategoryTheory GlobalTheory.CxCoh GlobalTheory.CatCoh

set_option autoImplicit false

namespace GlobalTheory.CxCoh.AlgDict

universe u

variable {R : Type} [CommRing R] {C : Type u} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem singleComplex_mem_cocyclesOne_iff_algebraFunctor (c : (Cx.single (Coef.ofAlg F)).T1) :
    c ∈ (Cx.single (Coef.ofAlg F)).Z1 ↔ c.1 ∈ Z1 F := by
  change (Cx.single (Coef.ofAlg F)).D1 c = 0 ↔ _
  constructor
  · intro h T T' T'' φ ψ
    have := congrFun (congrFun (congrFun (congrFun (congrFun (congrArg Prod.fst h) T) T') T'') φ) ψ
    change mp F ψ (c.1 T T' φ) - c.1 T T'' (φ ≫ ψ) + c.1 T' T'' ψ = 0 at this
    linear_combination -this
  · intro h
    refine Prod.ext ?_ (Subsingleton.elim _ _)
    funext T T' T'' φ ψ
    change mp F ψ (c.1 T T' φ) - c.1 T T'' (φ ≫ ψ) + c.1 T' T'' ψ = 0
    rw [h φ ψ]; ring

theorem singleComplex_mem_cocyclesTwo_iff_algebraFunctor (c : (Cx.single (Coef.ofAlg F)).T2) :
    c ∈ (Cx.single (Coef.ofAlg F)).Z2 ↔ c.1 ∈ Z2 F :=
  ⟨fun h _ _ _ _ φ ψ χ ↦ h.1 _ _ _ _ φ ψ χ,
    fun h ↦ ⟨fun _ _ _ _ φ ψ χ ↦ h φ ψ χ, fun _ _ _ _ _ ↦ Subsingleton.elim _ _,
      fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ Subsingleton.elim _ _⟩⟩

variable {C' : Type u} [Category.{0} C'] (G : C' ⥤ C)

theorem h1_injective (hi : Function.Injective (CoefMap.restrict F G).pull1) :
    Function.Injective ((Cx.single (Coef.ofAlg F)).resMap G).h1 := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective c
  have hz : z.1.1 ∈ Z1 F := (singleComplex_mem_cocyclesOne_iff_algebraFunctor F z.1).1 z.2
  change (QuotientAddGroup.mk (((Cx.single (Coef.ofAlg F)).resMap G).z1 z) :
    ((Cx.single (Coef.ofAlg F)).res G).H1) = 0 at hc
  rw [QuotientAddGroup.eq_zero_iff] at hc
  obtain ⟨g, hg⟩ := hc
  have h0 : (CoefMap.restrict F G).pull1 (H1.mk F ⟨z.1.1, hz⟩) = (CoefMap.restrict F G).pull1 0 := by
    rw [map_zero, CoefMap.pullCohomologyOne_class, H1.mk_eq_zero]
    exact ⟨g, congrArg Prod.fst hg⟩
  obtain ⟨g', hg'⟩ := H1.mk_eq_zero.1 (hi h0)
  rw [QuotientAddGroup.eq_zero_iff]
  exact ⟨g', Prod.ext hg' (Subsingleton.elim _ _)⟩

theorem h1_surjective (hs : Function.Surjective (CoefMap.restrict F G).pull1) :
    Function.Surjective ((Cx.single (Coef.ofAlg F)).resMap G).h1 := by
  intro c'
  obtain ⟨z', rfl⟩ := QuotientAddGroup.mk_surjective c'
  have hz' : z'.1.1 ∈ Z1 (G ⋙ F) := (singleComplex_mem_cocyclesOne_iff_algebraFunctor (G ⋙ F) z'.1).1 z'.2
  obtain ⟨c, hc⟩ := hs (H1.mk _ ⟨z'.1.1, hz'⟩)
  obtain ⟨f, rfl⟩ := H1.mk_surjective F c
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_mk] at hc
  obtain ⟨g, hg⟩ := hc
  refine ⟨QuotientAddGroup.mk ⟨(f.1, fun _ ↦ 0), (singleComplex_mem_cocyclesOne_iff_algebraFunctor F _).2 f.2⟩, ?_⟩
  change (QuotientAddGroup.mk (((Cx.single (Coef.ofAlg F)).resMap G).z1 _) :
    ((Cx.single (Coef.ofAlg F)).res G).H1) = QuotientAddGroup.mk z'
  rw [QuotientAddGroup.eq]
  refine ⟨-g, Prod.ext ?_ (Subsingleton.elim _ _)⟩
  rw [map_neg]
  funext T T' φ
  have := congrFun (congrFun (congrFun hg T) T') φ
  change -(d0 (G ⋙ F) g T T' φ) = -(f.1 _ _ (G.map φ)) + z'.1.1 T T' φ
  rw [this]
  change -((f.1 _ _ (G.map φ)) - z'.1.1 T T' φ) = _
  abel

theorem h2_injective (hi : Function.Injective (CoefMap.restrict F G).pull2) :
    Function.Injective ((Cx.single (Coef.ofAlg F)).resMap G).h2 := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective c
  have hz : z.1.1 ∈ Z2 F := (singleComplex_mem_cocyclesTwo_iff_algebraFunctor F z.1).1 z.2
  change (QuotientAddGroup.mk (((Cx.single (Coef.ofAlg F)).resMap G).z2 z) :
    ((Cx.single (Coef.ofAlg F)).res G).H2) = 0 at hc
  rw [QuotientAddGroup.eq_zero_iff] at hc
  obtain ⟨g, hg⟩ := hc
  have h0 : (CoefMap.restrict F G).pull2 (H2.mk F ⟨z.1.1, hz⟩) = (CoefMap.restrict F G).pull2 0 := by
    rw [map_zero, CoefMap.pullCohomologyTwo_class, H2.mk_eq_zero]
    exact ⟨g.1, congrArg Prod.fst hg⟩
  obtain ⟨g', hg'⟩ := H2.mk_eq_zero.1 (hi h0)
  rw [QuotientAddGroup.eq_zero_iff]
  exact ⟨(g', fun _ ↦ 0), Prod.ext hg' (Subsingleton.elim _ _)⟩

theorem h2_surjective (hs : Function.Surjective (CoefMap.restrict F G).pull2) :
    Function.Surjective ((Cx.single (Coef.ofAlg F)).resMap G).h2 := by
  intro c'
  obtain ⟨z', rfl⟩ := QuotientAddGroup.mk_surjective c'
  have hz' : z'.1.1 ∈ Z2 (G ⋙ F) := (singleComplex_mem_cocyclesTwo_iff_algebraFunctor (G ⋙ F) z'.1).1 z'.2
  obtain ⟨c, hc⟩ := hs (H2.mk _ ⟨z'.1.1, hz'⟩)
  obtain ⟨f, rfl⟩ := H2.mk_surjective F c
  rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk] at hc
  obtain ⟨g, hg⟩ := hc
  refine ⟨QuotientAddGroup.mk ⟨(f.1, fun _ _ _ ↦ 0, fun _ ↦ 0), (singleComplex_mem_cocyclesTwo_iff_algebraFunctor F _).2 f.2⟩, ?_⟩
  change (QuotientAddGroup.mk (((Cx.single (Coef.ofAlg F)).resMap G).z2 _) :
    ((Cx.single (Coef.ofAlg F)).res G).H2) = QuotientAddGroup.mk z'
  rw [QuotientAddGroup.eq]
  refine ⟨(-g, fun _ ↦ 0), Prod.ext ?_ (Subsingleton.elim _ _)⟩
  funext T T' T'' φ ψ
  have := congrFun (congrFun (congrFun (congrFun (congrFun hg T) T') T'') φ) ψ
  change d1 (G ⋙ F) (-g) T T' T'' φ ψ = -(f.1 _ _ _ (G.map φ) (G.map ψ)) + z'.1.1 T T' T'' φ ψ
  rw [map_neg, Pi.neg_apply, Pi.neg_apply, Pi.neg_apply, Pi.neg_apply, Pi.neg_apply, this]
  change -((f.1 _ _ _ (G.map φ) (G.map ψ)) - z'.1.1 T T' T'' φ ψ) = _
  abel

end GlobalTheory.CxCoh.AlgDict

theorem GlobalTheory.CxCoh.single_algebra_restriction_bijective : ∀ (R : Type) [CommRing R] (C C' : Type 1) [Category.{0} C]
    [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C),
    Function.Bijective (CoefMap.restrict F G).pull1 → Function.Bijective (CoefMap.restrict F G).pull2 →
    ((Cx.single (Coef.ofAlg F)).resMap G).PullbackBijectiveDegreesOneTwo :=
  fun _ _ _ _ _ _ F G h1 h2 ↦
    ⟨⟨AlgDict.h1_injective F G h1.1, AlgDict.h1_surjective F G h1.2⟩,
      AlgDict.h2_injective F G h2.1, AlgDict.h2_surjective F G h2.2⟩
end

section

set_option autoImplicit false

open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory

theorem coef_acyclic_of_two_sections (C : Type 1) [Category.{0} C] (M : Coef C) (S : C ⥤ C) (u v : 𝟭 C ⟶ S)
    (r : ∀ T, M.obj (S.obj T) →+ M.obj T)
    (hr : ∀ (T T' : C) (φ : T ⟶ T') x, r T' (M.map (S.map φ) x) = M.map φ (r T x))
    (hu : ∀ T x, r T (M.map (u.app T) x) = 0) (hv : ∀ T x, r T (M.map (v.app T) x) = x) :
    M.Ac0 ∧ M.Ac1 ∧ M.Ac2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    funext T
    have h1 : g (S.obj T) = M.map (u.app T) (g T) := hg T (S.obj T) (u.app T)
    have h2 : g (S.obj T) = M.map (v.app T) (g T) := hg T (S.obj T) (v.app T)
    have e := hv T (g T)
    rw [← h2, h1, hu] at e
    exact e.symm
  · intro f hf
    refine ⟨fun T ↦ r T (f T (S.obj T) (u.app T) - f T (S.obj T) (v.app T)), ?_⟩
    intro T T' φ
    have key : ∀ θ : 𝟭 C ⟶ S, r T' (M.map (θ.app T') (f T T' φ)) + r T' (f T' (S.obj T') (θ.app T')) =
        M.map φ (r T (f T (S.obj T) (θ.app T))) + r T' (f (S.obj T) (S.obj T') (S.map φ)) := by
      intro θ
      have nat : φ ≫ θ.app T' = θ.app T ≫ S.map φ := θ.naturality φ
      have e1 := hf T T' (S.obj T') φ (θ.app T')
      have e2 := hf T (S.obj T) (S.obj T') (θ.app T) (S.map φ)
      rw [nat, e2] at e1
      have e3 := congrArg (r T') e1
      simp only [map_add (f := _), hr] at e3
      exact e3.symm
    have ku := key u
    have kv := key v
    rw [hu] at ku
    rw [hv] at kv
    simp only [map_sub]
    linear_combination (norm := abel1) kv - ku
  · intro z hz
    let A : (𝟭 C ⟶ S) → ∀ (T T' : C) (_ : T ⟶ T'), M.obj (S.obj T') := fun θ T T' φ ↦
      z T T' (S.obj T') φ (θ.app T') - z T (S.obj T) (S.obj T') (θ.app T) (S.map φ)
    refine ⟨fun T T' φ ↦ r T' (A v T T' φ - A u T T' φ), ?_⟩
    intro T T' T'' φ ψ
    have key : ∀ θ : 𝟭 C ⟶ S, M.map ψ (r T' (A θ T T' φ)) =
        r T'' (M.map (θ.app T'') (z T T' T'' φ ψ)) + r T'' (A θ T T'' (φ ≫ ψ)) - r T'' (A θ T' T'' ψ)
          - r T'' (z (S.obj T) (S.obj T') (S.obj T'') (S.map φ) (S.map ψ)) := by
      intro θ
      have nat1 : φ ≫ θ.app T' = θ.app T ≫ S.map φ := θ.naturality φ
      have nat2 : ψ ≫ θ.app T'' = θ.app T' ≫ S.map ψ := θ.naturality ψ
      have h1 := hz T T' T'' (S.obj T'') φ ψ (θ.app T'')
      have h2 := hz T T' (S.obj T') (S.obj T'') φ (θ.app T') (S.map ψ)
      have h3 := hz T (S.obj T) (S.obj T') (S.obj T'') (θ.app T) (S.map φ) (S.map ψ)
      rw [nat1, ← nat2] at h2
      rw [← S.map_comp] at h3
      have inner : M.map (S.map ψ) (A θ T T' φ) =
          M.map (θ.app T'') (z T T' T'' φ ψ) + A θ T T'' (φ ≫ ψ) - A θ T' T'' ψ
            - z (S.obj T) (S.obj T') (S.obj T'') (S.map φ) (S.map ψ) := by
        simp only [A, map_sub]
        first
          | linear_combination (norm := abel1) h2 - h3 - h1
          | linear_combination (norm := abel1) h2 - h3 + h1
          | linear_combination (norm := abel1) h1 + h2 - h3
          | linear_combination (norm := abel1) -h1 - h2 + h3
      rw [← hr, inner]
      simp only [map_sub, map_add (f := _)]
    have ku := key u
    have kv := key v
    rw [hu] at ku
    rw [hv] at kv
    simp only [map_sub]
    linear_combination (norm := abel1) ku - kv

end GlobalTheory
end

section

open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory.CxCoh

theorem fnMap_h2_bijective (C : Type 1) [Category.{0} C] (K : Cx C) (h11 : K.M1.Ac1) (h12 : K.M1.Ac2)
    (h20 : K.M2.Ac0) (h21 : K.M2.Ac1) (h30 : K.M3.Ac0) : Function.Bijective K.fnMap.h2 := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
    change (QuotientAddGroup.mk (K.fnMap.z2 a) : (Cx.single K.M0).H2) = 0 at hc
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range] at hc
    obtain ⟨⟨f, ω0⟩, hf⟩ := hc
    have hz : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''),
        K.M0.map ψ (f T T' φ) - f T T'' (φ ≫ ψ) + f T' T'' ψ = a.1.1 T T' T'' φ ψ := by
      intro T T' T'' φ ψ
      have := congrArg (fun x => x.1 T T' T'' φ ψ) hf
      simp [Cx.D1, Cx.fnMap, CxMap.z2, CxMap.p2] at this
      exact this
    have ha := a.2
    obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
    obtain ⟨ω, hω⟩ := h11 (fun T T' φ => a.1.2.1 T T' φ + K.d0 T' (f T T' φ)) (by
      intro T T' T'' φ ψ
      rw [ha2 T T' T'' φ ψ, ← hz T T' T'' φ ψ]
      simp only [map_add (f := _), map_sub, K.diffZero_natural]
      abel)
    have hη : (fun T => a.1.2.2 T - K.d1 T (ω T)) = 0 := by
      apply h20
      intro T T' φ
      have e := hω T T' φ
      have e2 : a.1.2.1 T T' φ = ω T' - K.M1.map φ (ω T) - K.d0 T' (f T T' φ) := by
        rw [← e]; abel
      rw [ha3 T T' φ, e2]
      simp only [map_sub, K.diffOne_diffZero, K.diffOne_natural]
      abel
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]
    refine ⟨(f, ω), ?_⟩
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext T T' T'' φ ψ
      exact hz T T' T'' φ ψ
    · funext T T' φ
      have e := hω T T' φ
      change ω T' - K.M1.map φ (ω T) - K.d0 T' (f T T' φ) = _
      rw [← e]; abel
    · funext T
      have e := congrFun hη T
      change K.d1 T (ω T) = _
      simp only [Pi.zero_apply, sub_eq_zero] at e
      exact e.symm
  · intro c
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨hb1, -, -, -⟩ := b.2
    obtain ⟨f, hf⟩ := h12 (fun T T' T'' φ ψ => K.d0 T'' (b.1.1 T T' T'' φ ψ)) (by
      intro T T' T'' T''' φ ψ χ
      rw [← K.diffZero_natural, ← map_add (f := _), hb1, map_add (f := _)])
    obtain ⟨g, hg⟩ := h21 (fun T T' φ => K.d1 T' (-f T T' φ)) (by
      intro T T' T'' φ ψ
      have e := hf T T' T'' φ ψ
      have e2 : f T T'' (φ ≫ ψ) = K.M1.map ψ (f T T' φ) + f T' T'' ψ - K.d0 T'' (b.1.1 T T' T'' φ ψ) := by
        rw [e]; abel
      rw [e2]
      simp only [map_neg, map_add (f := _), map_sub, K.diffOne_diffZero, K.diffOne_natural]
      abel)
    have h3 : (fun T => K.d2 T (g T)) = 0 := by
      apply h30
      intro T T' φ
      have e := hg T T' φ
      have e2 : g T' = K.M2.map φ (g T) + K.d1 T' (-f T T' φ) := by rw [e]; abel
      rw [e2, map_add (f := _), K.diffTwo_comp_diffOne, add_zero, K.diffTwo_natural]
    let a : K.Z2 := ⟨(b.1.1, fun T T' φ => -f T T' φ, g), by
      refine ⟨hb1, fun T T' T'' φ ψ => ?_, fun T T' φ => ?_, fun T => ?_⟩
      · rw [hf T T' T'' φ ψ]; simp only [map_neg, map_sub, map_add (f := _)]; abel
      · have e := hg T T' φ
        change g T' = K.M2.map φ (g T) + K.d1 T' (-f T T' φ)
        rw [e]; abel
      · exact congrFun h3 T⟩
    refine ⟨QuotientAddGroup.mk a, ?_⟩
    change (QuotientAddGroup.mk (K.fnMap.z2 a) : (Cx.single K.M0).H2) = QuotientAddGroup.mk b
    congr 1
end CxCoh
end GlobalTheory
end

section

set_option autoImplicit false

open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory.CxCoh.JoinedTwoProof

universe a b

theorem main : JoinedTwo.{a, b} := by
  intro C _ C' _ K K' m m' θ j c
  obtain ⟨⟨⟨z, w, η⟩, hc⟩, rfl⟩ := QuotientAddGroup.mk_surjective c
  obtain ⟨h1, h2, h3, -⟩ := hc
  dsimp only at h1 h2 h3
  refine QuotientAddGroup.eq.2 ⟨(fun T T' φ ↦ m'.a0 T' (z _ _ _ (θ.app T) (m'.G.map φ) - z _ _ _ (m.G.map φ) (θ.app T')),
    fun T ↦ m'.a1 T (w _ _ (θ.app T))), ?_⟩
  refine Prod.ext (funext fun T ↦ funext fun T' ↦ funext fun T'' ↦ funext fun φ ↦ funext fun ψ ↦ ?_)
    (Prod.ext (funext fun T ↦ funext fun T' ↦ funext fun φ ↦ ?_) (funext fun T ↦ ?_))
  · change K'.M0.map ψ (m'.a0 T' (z _ _ _ (θ.app T) (m'.G.map φ) - z _ _ _ (m.G.map φ) (θ.app T'))) -
        m'.a0 T'' (z _ _ _ (θ.app T) (m'.G.map (φ ≫ ψ)) - z _ _ _ (m.G.map (φ ≫ ψ)) (θ.app T'')) +
        m'.a0 T'' (z _ _ _ (θ.app T') (m'.G.map ψ) - z _ _ _ (m.G.map ψ) (θ.app T'')) =
      -m.a0 T'' (z _ _ _ (m.G.map φ) (m.G.map ψ)) + m'.a0 T'' (z _ _ _ (m'.G.map φ) (m'.G.map ψ))
    have e1 := congrArg (m'.a0 T'') (h1 _ _ _ _ (m.G.map φ) (m.G.map ψ) (θ.app T''))
    have e2 := congrArg (m'.a0 T'') (h1 _ _ _ _ (m.G.map φ) (θ.app T') (m'.G.map ψ))
    have e3 := congrArg (m'.a0 T'') (h1 _ _ _ _ (θ.app T) (m'.G.map φ) (m'.G.map ψ))
    rw [θ.naturality ψ] at e1
    rw [θ.naturality φ] at e2
    rw [← m.G.map_comp] at e1
    rw [← m'.G.map_comp] at e3
    simp only [map_add (f := _), j.e0, m'.compDegreeZero_natural] at e1 e2 e3
    simp only [map_sub, m'.compDegreeZero_natural]
    linear_combination (norm := abel1) e1 - e2 + e3
  · change m'.a1 T' (w _ _ (θ.app T')) - K'.M1.map φ (m'.a1 T (w _ _ (θ.app T))) -
        K'.d0 T' (m'.a0 T' (z _ _ _ (θ.app T) (m'.G.map φ) - z _ _ _ (m.G.map φ) (θ.app T'))) =
      -m.a1 T' (w _ _ (m.G.map φ)) + m'.a1 T' (w _ _ (m'.G.map φ))
    have e := congrArg (m'.a1 T') ((h2 _ _ _ (m.G.map φ) (θ.app T')).symm.trans
      ((congrArg (w _ _) (θ.naturality φ)).trans (h2 _ _ _ (θ.app T) (m'.G.map φ))))
    simp only [map_add (f := _), j.e1, m'.compDegreeOne_natural, m'.comp_commutes_diffZero] at e
    simp only [map_sub]
    linear_combination (norm := abel1) e
  · change K'.d1 T (m'.a1 T (w _ _ (θ.app T))) = -m.a2 T (η _) + m'.a2 T (η _)
    rw [h3 _ _ (θ.app T), map_add (f := _), j.e2, m'.comp_commutes_diffOne]; abel

theorem joinedTwo_inst : JoinedTwo.{1,1} ∧ JoinedTwo.{1,0} ∧ JoinedTwo.{0,0} := ⟨main, main, main⟩

end GlobalTheory.CxCoh.JoinedTwoProof
end

section

open GlobalTheory

theorem _root_.GlobalTheory.T.coeff_mem_span_of_weightedHomogeneous_relation_quasiRegular : ∀ {R : Type} [CommRing R] {n : ℕ} (z : Fin n → R) (w : Fin n → ℕ), (∀ i, 1 ≤ w i) →
    IsQuasiRegularSeq R z → ∀ (D : ℕ) (F : MvPolynomial (Fin n) R),
    F.IsWeightedHomogeneous w D → MvPolynomial.eval z F = 0 →
    ∀ α : Fin n →₀ ℕ, F.coeff α ∈ Ideal.span (Set.range z) := by
  first | exact @GlobalTheory.weightedRelation_coeff_mem_span | exact GlobalTheory.weightedRelation_coeff_mem_span | (intros; apply GlobalTheory.weightedRelation_coeff_mem_span <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.galoisElement_dvd_of_formallyUnramified : ∀ (R C O : Type) [CommRing R] [CommRing C] [Algebra R C] [CommRing O] [Algebra R O]
    [Algebra.FormallyUnramified O (O ⊗[R] C)] [Algebra.EssFiniteType O (O ⊗[R] C)]
    (G : Type) [Group G] [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (b : R) (n : ℕ) (x y : Fin n → C),
      (∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C b else 0) →
    ∀ σ : C →ₐ[R] O, Function.Injective (GlobalTheory.GoodEtale.galMap act σ) →
    ∀ h : G, ∃ m' : O ⊗[R] C, GlobalTheory.GoodEtale.galElt act σ x y h = algebraMap R O b • m' := by
  first | (exact @GlobalTheory.GoodEtale.galElt_dvd_of_unramified) | (exact GlobalTheory.GoodEtale.galElt_dvd_of_unramified) | (intros; apply GlobalTheory.GoodEtale.galElt_dvd_of_unramified  <;> assumption)
end
