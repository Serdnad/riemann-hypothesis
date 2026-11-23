module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.LBPush

theorem gm_eq_one {X Z : Scheme.{0}} (κ : Z ⟶ X) [IsOpenImmersion κ] (z : Z) {U : X.Opens} (h : κ z ∈ U)
    {a : Γ(X, U)ˣ} (e : gm κ z U a = 1) : gm (𝟙 X) (κ z) U a = 1 := by
  have hU : (𝟙 X) (κ z) ∈ U := h
  unfold gm pullU at e ⊢
  rw [dite_eq_left h] at e
  rw [dite_eq_left hU]
  have e' := congrArg Units.val e
  apply Units.ext
  apply (ConcreteCategory.bijective_of_isIso (κ.stalkMap z)).1
  refine ((Scheme.Hom.germ_stalkMap_apply κ U z h (a : Γ(X, U))).trans ?_).trans (map_one _).symm
  exact e'

theorem exists_unit_image {X Y : Scheme.{0}} (κ : Y ⟶ X) [IsOpenImmersion κ] (V : Y.Opens) (a : Γ(Y, V)ˣ) :
    ∃ b : Γ(X, κ ''ᵁ V)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ V →
      gm (r ≫ κ) z (κ ''ᵁ V) b = gm r z V a := by
  refine ⟨Units.map (κ.appIso V).inv.hom a, fun Z r z hz => ?_⟩
  have h1 : (r ≫ κ) z ∈ κ ''ᵁ V := ⟨r z, hz, rfl⟩
  unfold gm pullU
  rw [dite_eq_left hz, dite_eq_left h1]
  apply Units.ext
  refine (Scheme.Hom.germ_stalkMap_apply (r ≫ κ) (κ ''ᵁ V) z h1 _).symm.trans ?_
  refine Eq.trans ?_ (Scheme.Hom.germ_stalkMap_apply r V z hz (a : Γ(Y, V)))
  rw [Scheme.Hom.stalkMap_comp]
  refine congrArg (r.stalkMap z) ?_
  refine (Scheme.Hom.germ_stalkMap_apply κ (κ ''ᵁ V) (r z) h1 _).trans ?_
  refine (congrArg (ConcreteCategory.hom (Y.presheaf.germ (κ ⁻¹ᵁ κ ''ᵁ V) (r z) h1))
    (Scheme.Hom.appIso_inv_app_apply κ V (a : Γ(Y, V)))).trans ?_
  exact TopCat.Presheaf.germ_res_apply' Y.presheaf _ (r z) _ _

private theorem gm_res_eq_gm {S T : Scheme.{0}} (f : T ⟶ S) (t : T) {U V : S.Opens} (hVU : V ≤ U) (a : Γ(S, U)ˣ)
    (ht : f t ∈ V) : gm f t V (res hVU a) = gm f t U a := by
  unfold gm pullU res
  rw [dite_eq_left ht, dite_eq_left (hVU ht)]
  apply Units.ext
  refine (Scheme.Hom.germ_stalkMap_apply f V t ht _).symm.trans ?_
  refine Eq.trans ?_ (Scheme.Hom.germ_stalkMap_apply f U t (hVU ht) (a : Γ(S, U)))
  congr 1
  exact TopCat.Presheaf.germ_res_apply S.presheaf (homOfLE hVU) (f t) ht _

private theorem units_eq_of_gm_eq {S : Scheme.{0}} {W : S.Opens} {a b : Γ(S, W)ˣ}
    (h : ∀ x, x ∈ W → gm (𝟙 S) x W a = gm (𝟙 S) x W b) : a = b := by
  apply Units.ext
  apply TopCat.Presheaf.section_ext S.sheaf W
  intro x hx
  have := congrArg Units.val (h x hx)
  unfold gm pullU at this
  rw [dite_eq_left (show (𝟙 S) x ∈ W from hx)] at this
  exact this

private theorem gm_id_pullU' {S T : Scheme.{0}} (f : T ⟶ S) (t : T) (W : S.Opens) (c : Γ(S, W)ˣ) (ht : f t ∈ W) :
    gm (𝟙 T) t (f ⁻¹ᵁ W) (pullU f W c) = gm f t W c := by
  unfold gm
  rw [dite_eq_left (show (𝟙 T) t ∈ f ⁻¹ᵁ W from ht), dite_eq_left ht]
  rfl

private theorem gm_inv_moduli {S T : Scheme.{0}} (f : T ⟶ S) (t : T) (U : S.Opens) (a : Γ(S, U)ˣ) :
    gm f t U a⁻¹ = (gm f t U a)⁻¹ :=
  map_inv _ _

private theorem res_eq_mul_inv_mul_of_gm {S : Scheme.{0}} {W A B C D : S.Opens} (hA : W ≤ A) (hB : W ≤ B) (hC : W ≤ C)
    (hD : W ≤ D) (a : Γ(S, A)ˣ) (b : Γ(S, B)ˣ) (c : Γ(S, C)ˣ) (d : Γ(S, D)ˣ)
    (h : ∀ x, x ∈ W → gm (𝟙 S) x A a = gm (𝟙 S) x B b * (gm (𝟙 S) x C c)⁻¹ * gm (𝟙 S) x D d) :
    res hA a = res hB b * (res hC c)⁻¹ * res hD d := by
  apply units_eq_of_gm_eq
  intro x hx
  rw [map_mul, map_mul, gm_inv_moduli, gm_res_eq_gm (𝟙 S) x hA a hx, gm_res_eq_gm (𝟙 S) x hB b hx,
    gm_res_eq_gm (𝟙 S) x hC c hx, gm_res_eq_gm (𝟙 S) x hD d hx]
  exact h x hx

theorem exists_push : ∀ (X Y : Scheme.{0}) (ψ : Y ⟶ X) [IsOpenImmersion ψ] (L : LB Y), L.IsLB →
    ∃ M : LB X, ⨆ a, M.U a = ψ.opensRange ∧
      (∀ (a : M.ι) (x : X), x ∈ M.U a → gm (𝟙 X) x (M.U a ⊓ M.U a) (M.g a a) = 1) ∧
      (M.pull ψ).IsLB ∧ LBIso L (M.pull ψ) := by
  intro X Y ψ _ L hL
  have himg : ∀ i j, ψ ''ᵁ L.U i ⊓ ψ ''ᵁ L.U j ≤ ψ ''ᵁ (L.U i ⊓ L.U j) := by
    rintro i j x ⟨⟨y, hy, rfl⟩, ⟨y', hy', e⟩⟩
    have e' : y' = y := ψ.isOpenEmbedding.injective e
    rw [e'] at hy'
    exact ⟨y, ⟨hy, hy'⟩, rfl⟩
  choose b hb using fun i j => exists_unit_image ψ (L.U i ⊓ L.U j) (L.g i j)
  let M : LB X := ⟨L.ι, fun i => ψ ''ᵁ L.U i, fun i j => res (himg i j) (b i j)⟩
  have hcov : ∀ y : Y, ∃ i, y ∈ L.U i := by
    intro y
    have hy : y ∈ ⨆ i, L.U i := by rw [hL.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hy
  have hmem : ∀ (j : PUnit → L.ι) (y : Y), y ∈ (M.pull ψ).U j ↔ y ∈ L.U (j PUnit.unit) := by
    intro j y
    constructor
    · intro hy
      obtain ⟨y', hy', e⟩ := Set.mem_iInter.1 hy PUnit.unit
      rwa [ψ.isOpenEmbedding.injective e] at hy'
    · intro hy
      exact Set.mem_iInter.2 fun k => ⟨y, hy, rfl⟩
  have Gself : ∀ i y, y ∈ L.U i → gm (𝟙 Y) y (L.U i ⊓ L.U i) (L.g i i) = 1 := by
    intro i y hy
    have := congrArg (gm (𝟙 Y) y _) (hL.g_self i)
    rw [gm_res_eq_gm (𝟙 Y) y, map_one] at this
    · exact this
    · exact hy
  have Gcoc : ∀ i j k y, y ∈ L.U i → y ∈ L.U j → y ∈ L.U k →
      gm (𝟙 Y) y (L.U i ⊓ L.U j) (L.g i j) * gm (𝟙 Y) y (L.U j ⊓ L.U k) (L.g j k) =
        gm (𝟙 Y) y (L.U i ⊓ L.U k) (L.g i k) := by
    intro i j k y hi hj hk
    have := congrArg (gm (𝟙 Y) y _) (hL.cocycle i j k)
    rw [map_mul, gm_res_eq_gm (𝟙 Y) y, gm_res_eq_gm (𝟙 Y) y, gm_res_eq_gm (𝟙 Y) y] at this
    · exact this
    all_goals exact ⟨⟨hi, hj⟩, hk⟩
  have key : ∀ i j y, y ∈ L.U i → y ∈ L.U j →
      gm ψ y (M.U i ⊓ M.U j) (M.g i j) = gm (𝟙 Y) y (L.U i ⊓ L.U j) (L.g i j) := by
    intro i j y hi hj
    have := hb i j Y (𝟙 Y) y ⟨hi, hj⟩
    rw [Category.id_comp] at this
    exact (gm_res_eq_gm ψ y (himg i j) (b i j) ⟨⟨y, hi, rfl⟩, ⟨y, hj, rfl⟩⟩).trans this
  have hN : ∀ (j j' : PUnit → L.ι) y, y ∈ L.U (j PUnit.unit) → y ∈ L.U (j' PUnit.unit) →
      gm (𝟙 Y) y ((M.pull ψ).U j ⊓ (M.pull ψ).U j') ((M.pull ψ).g j j') =
        gm (𝟙 Y) y (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) (L.g (j PUnit.unit) (j' PUnit.unit)) := by
    intro j j' y h1 h2
    rw [← key _ _ y h1 h2]
    unfold LB.pull LB.LinComb
    dsimp only
    rw [map_prod, Fintype.prod_unique, map_zpow, zpow_one]
    refine (gm_res_eq_gm (𝟙 Y) y _ _ ?_).trans (gm_id_pullU' ψ y (M.U (j default) ⊓ M.U (j' default)) _ ?_)
    all_goals first
      | exact ⟨(hmem j y).2 h1, (hmem j' y).2 h2⟩
      | exact ⟨⟨y, h1, rfl⟩, ⟨y, h2, rfl⟩⟩
  refine ⟨M, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · apply le_antisymm
    · intro x hx
      obtain ⟨i, y, hy, rfl⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      exact ⟨y, rfl⟩
    · rintro x ⟨y, rfl⟩
      obtain ⟨i, hi⟩ := hcov y
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, y, hi, rfl⟩
  · rintro a x ⟨y, hy, rfl⟩
    exact gm_eq_one ψ y (U := M.U a ⊓ M.U a) ⟨⟨y, hy, rfl⟩, ⟨y, hy, rfl⟩⟩ ((key a a y hy hy).trans (Gself a y hy))
  · apply eq_top_iff.2
    intro y _
    obtain ⟨i, hi⟩ := hcov y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, (hmem _ y).2 hi⟩
  · intro j
    apply units_eq_of_gm_eq
    intro y hy
    have h1 := (hmem j y).1 hy
    rw [gm_res_eq_gm (𝟙 Y) y, map_one, hN j j y h1 h1, Gself _ y h1]
    exact hy
  · intro j j' j''
    apply units_eq_of_gm_eq
    intro y hy
    have h1 := (hmem j y).1 hy.1.1
    have h2 := (hmem j' y).1 hy.1.2
    have h3 := (hmem j'' y).1 hy.2
    rw [map_mul, gm_res_eq_gm (𝟙 Y) y, gm_res_eq_gm (𝟙 Y) y, gm_res_eq_gm (𝟙 Y) y, hN j j' y h1 h2, hN j' j'' y h2 h3,
      hN j j'' y h1 h3]
    · exact Gcoc _ _ _ y h1 h2 h3
    all_goals exact hy
  · unfold LBIso LB.Iso LB.div LB.Gen.IsGen
    have hle : ∀ p : (PUnit → L.ι) × L.ι, (M.pull ψ).U p.1 ⊓ L.U p.2 ≤ L.U (p.1 PUnit.unit) ⊓ L.U p.2 :=
      fun p y hy => ⟨(hmem p.1 y).1 hy.1, hy.2⟩
    refine ⟨⟨fun p => res (hle p) (L.g (p.1 PUnit.unit) p.2)⟩, ?_⟩
    intro p q
    refine res_eq_mul_inv_mul_of_gm _ _ _ _ _ _ _ _ (fun y hy => ?_)
    have ha := (hmem p.1 y).1 hy.1.1
    have hi := hy.1.2
    have ha' := (hmem q.1 y).1 hy.2.1
    have hi' := hy.2.2
    have eA := gm_res_eq_gm (𝟙 Y) y (hle p) (L.g (p.1 PUnit.unit) p.2) hy.1
    have eD := gm_res_eq_gm (𝟙 Y) y (hle q) (L.g (q.1 PUnit.unit) q.2) hy.2
    have eB := hN p.1 q.1 y ha ha'
    have hG : gm (𝟙 Y) y (L.U (p.1 PUnit.unit) ⊓ L.U p.2) (L.g (p.1 PUnit.unit) p.2) =
        gm (𝟙 Y) y (L.U (p.1 PUnit.unit) ⊓ L.U (q.1 PUnit.unit)) (L.g (p.1 PUnit.unit) (q.1 PUnit.unit)) *
          (gm (𝟙 Y) y (L.U p.2 ⊓ L.U q.2) (L.g p.2 q.2))⁻¹ *
            gm (𝟙 Y) y (L.U (q.1 PUnit.unit) ⊓ L.U q.2) (L.g (q.1 PUnit.unit) q.2) := by
      rw [mul_right_comm, Gcoc _ _ _ y ha ha' hi', ← Gcoc _ _ _ y ha hi hi', mul_inv_cancel_right]
    refine eA.trans (hG.trans ?_)
    exact congrArg₂ (· * ·) (congrArg₂ (· * ·) eB.symm rfl) eD.symm

end GlobalTheory.LBPush
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.ObjLower

section Identity

variable {X : Scheme.{0}}

def idIso (L : LB X) : LB.Iso L (L.pull (𝟙 X)) where
  s := fun p => res (fun _ hx => ⟨mem_pull.1 hx.1, hx.2⟩ :
    (L.pull (𝟙 X)).U p.1 ⊓ L.U p.2 ≤ L.U (p.1 PUnit.unit) ⊓ L.U p.2) (L.g (p.1 PUnit.unit) p.2)

theorem gw_idIso (L : LB X) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (j k : L.ι) (hj : f y ∈ L.U j) (hk : f y ∈ L.U k) :
    gw (idIso L) f y j k = gm f y _ (L.g j k) :=
  gm_res f y _ (show f y ∈ (L.pull (𝟙 X)).U (fun _ => j) ⊓ L.U k from ⟨mem_pull.2 hj, hk⟩) _

theorem pgen_idIso {L : LB X} (hL : L.IsLB) : PGen (idIso L) := by
  intro Y f y j j' k k' hj hj' hk hk'
  rw [gw_idIso L f y j k hj hk, gw_idIso L f y j' k' hj' hk', Category.comp_id,
    ← gm_cocycle hL f y hj' hk hk', ← gm_cocycle hL f y hj hj' hk]
  generalize gm f y _ (L.g j j') = A
  generalize gm f y _ (L.g j' k) = B
  generalize gm f y _ (L.g k k') = C
  rw [_root_.mul_assoc, mul_comm B C, inv_mul_cancel_left]

theorem pmaps_idIso (L : LB X) {K : Type} [Fintype K] {Y : Scheme.{0}} (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) : PMaps (idIso L) φ φ ε t t (𝟙 Y) := by
  intro Z r z p q hp hq
  have hm : r z ∈ LB.wchart L φ p ⊓ LB.wchart L φ q := ⟨Set.mem_iInter.2 hp, Set.mem_iInter.2 hq⟩
  have e := congrArg (gm r z (LB.wchart L φ p ⊓ LB.wchart L φ q)) (ht p q)
  rw [Category.comp_id]
  refine (gm_res r z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans ?_))
  refine congrArg₂ (· * ·) ?_ (gm_res r z _ hm _)
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  rw [gw_idIso L (r ≫ φ k) z (p k) (q k) (hp k) (hq k)]
  exact (gm_res r z _ hm _).trans (gm_pull r (φ k) z (L.U (p k) ⊓ L.U (q k)) ⟨hp k, hq k⟩ _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}}

def cubeId (G : Over S) [GrpObj G] [IsCommMonObj G] : CubeMap G G where
  F := 𝟙 _
  F3 := 𝟙 _
  e := 𝟙 _
  e_comm := by rw [Category.comp_id, Category.id_comp]
  psum_comm := fun _ => by rw [Category.comp_id, Category.id_comp]

def sabId (t : SAB H S) : SABMap t t (𝟙 S) where
  cm := cubeId t.G
  cart := by
    refine ⟨(IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback (𝟙 t.G.left) t.G.hom t.G.hom (𝟙 S)),
      fun T x y x₀ y₀ hx hy => ?_⟩
    refine Eq.trans ?_ (Category.comp_id _).symm
    exact mul_left_congr (b := T.hom) (Category.comp_id _) x₀ y₀ x y (hx.trans (Category.comp_id _))
      (hy.trans (Category.comp_id _))
  base := rfl
  act := fun a => by
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    rw [Category.comp_id, Category.id_comp]
  lin := (isPullCubical_iff _ _ _).2 ⟨idIso t.PP.L, pgen_idIso t.PP.isLB,
    pmaps_idIso _ _ _ _ t.PP.rigGen, pmaps_idIso _ _ _ _ t.cub.isGen⟩

end Identity

section Ideals

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem quot_mul_mem {l l₂ : Level H} (h : l.Dvd l₂) {x : 𝓞 E} (hx : x ∈ l.Mb) :
    ((l₂.M / l.M : ℕ) : 𝓞 E) * x ∈ l₂.Mb := by
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 h.2.1
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have h0 : Ideal.span {(l.M : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact_mod_cast hM
  have e : Ideal.span {(l.M : 𝓞 E)} * (J * J.map (H.bar : 𝓞 E →+* 𝓞 E)) =
      Ideal.span {(l.M : 𝓞 E)} * Ideal.span {((l₂.M / l.M : ℕ) : 𝓞 E)} := by
    rw [Ideal.span_singleton_mul_span_singleton, ← Nat.cast_mul, Nat.mul_div_cancel' h.1, ← l₂.prod, ← l.prod, hJ,
      Ideal.map_mul]
    ring
  have hk : ((l₂.M / l.M : ℕ) : 𝓞 E) ∈ J := by
    apply (Ideal.mul_le_left : J * J.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ J)
    rw [mul_left_cancel₀ h0 e]
    exact Ideal.mem_span_singleton_self _
  rw [hJ, mul_comm _ x]
  exact Ideal.mul_mem_mul hx hk

theorem quot_mul_mem_map {l l₂ : Level H} (h : l.Dvd l₂) {x : 𝓞 E}
    (hx : x ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) :
    ((l₂.M / l.M : ℕ) : 𝓞 E) * x ∈ l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
  obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective).1 hx
  have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) (quot_mul_mem h hy)
  rwa [map_mul, map_natCast] at this

theorem nsmul_mem_smul_top {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {I J : Ideal R} {n : ℕ}
    (h : ∀ x ∈ I, (n : R) * x ∈ J) {a : M} (ha : a ∈ I • (⊤ : Submodule R M)) :
    n • a ∈ J • (⊤ : Submodule R M) := by
  refine Submodule.smul_induction_on ha (fun r hr m _ => ?_) (fun x y hx hy => ?_)
  · rw [← Nat.cast_smul_eq_nsmul R, smul_smul]
    exact Submodule.smul_mem_smul (h r hr) trivial
  · rw [smul_add]; exact add_mem hx hy

end Ideals

theorem map_nsmul_of_add {A Q : Type*} [AddCommGroup A] [Group Q] (f : A → Q) (hf : ∀ a c, f (a + c) = f a * f c)
    (n : ℕ) (a : A) : f (n • a) = f a ^ n := by
  induction n with
  | zero =>
    have := hf 0 0
    rw [add_zero] at this
    rw [zero_nsmul, pow_zero]
    exact left_eq_mul.1 this
  | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l l₂ : Level H}
  {B : Type} [CommRing B] {b : Base l B} {b₂ : Base l₂ B} {S : Scheme.{0}} {s : S ⟶ Sp B}

def lower (o₂ : Obj D l₂ b₂ s) (h : l.Dvd l₂) (hρ : b.ρ = b₂.ρ) (hζ : b.ζ = b₂.ζ ^ (l₂.A / l.A)) : Obj D l b s where
  t := o₂.t
  proper := o₂.proper
  ample := o₂.ample
  ktriv := o₂.ktriv
  eta a := o₂.eta a ^ (l₂.M / l.M)
  eta_add a c := by rw [o₂.eta_add, mul_pow]
  eta_ker a ha := by
    rw [← map_nsmul_of_add _ o₂.eta_add]
    exact o₂.eta_ker _ (nsmul_mem_smul_top (fun _ hx => quot_mul_mem h hx) ha)
  etaA a := o₂.etaA a ^ (l₂.A / l.A)
  etaA_add a c := by rw [o₂.etaA_add, mul_pow]
  etaA_ker a := by
    rw [← map_nsmul_of_add _ o₂.etaA_add, smul_smul, Nat.div_mul_cancel h.2.2, o₂.etaA_ker]
  geom k _ _ x β hx := by
    obtain ⟨hd, I, h₁, h₂, h₃⟩ := o₂.geom k x β hx
    have hA : 0 < l₂.A / l.A := Nat.div_pos (Nat.le_of_dvd l₂.A_pos h.2.2) l.A_pos
    have hM₁ : 0 < l.M := by have := l.three_le; omega
    have hM₂ : 0 < l₂.M := by have := l₂.three_le; omega
    have hM : 0 < l₂.M / l.M := Nat.div_pos (Nat.le_of_dvd hM₂ h.1) hM₁
    refine ⟨hρ ▸ hd, I, ?_, fun a => ?_, fun a ha => ?_⟩
    · rw [hζ, map_pow, ← h₁, ← I.ζ_pow l.A _ l.A_pos hA, Nat.mul_div_cancel' h.2.2, Units.val_pow_eq_pow_val]
    · rw [MonObj.comp_pow, h₂, ← I.tower l.A _ l.A_pos hA, Nat.mul_div_cancel' h.2.2]
    · rw [← map_nsmul_of_add _ o₂.eta_add,
        h₃ _ (nsmul_mem_smul_top (fun _ hx => quot_mul_mem_map h hx) ha),
        map_nsmul_of_add _ (I.add _), ← I.tower l.M _ hM₁ hM, Nat.mul_div_cancel' h.1]

end GlobalTheory.ObjLower

namespace GlobalTheory

theorem obj_lower_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l l₂ : Level H) (B : Type) [CommRing B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B)
    (o₂ : Obj D l₂ b₂ s), l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) →
    ∃ (o : Obj D l b s) (m : SABMap o₂.t o.t (𝟙 S)),
      (∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = 𝟙 S ≫ (o.eta a).left) ∧
      (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = 𝟙 S ≫ (o.etaA a).left) := by
  intro E _ _ _ H D l l₂ B _ b b₂ S s o₂ h hρ hζ
  exact ⟨ObjLower.lower o₂ h hρ hζ, ObjLower.sabId o₂.t,
    fun _ => (Category.comp_id _).trans (Category.id_comp _).symm,
    fun _ => (Category.comp_id _).trans (Category.id_comp _).symm⟩

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LatticeTorsion

variable {S : Scheme.{0}}

theorem prop_powObj (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative]
    [P.IsStableUnderBaseChange] (X : Over S) (hX : P X.hom) : ∀ k, P (Out.powObj X k).hom
  | 0 => P.id_mem S
  | k + 1 => by
    change P (pullback.fst X.hom (Out.powObj X k).hom ≫ X.hom)
    exact P.comp_mem _ _ (P.pullback_fst _ _ (prop_powObj P X hX k)) hX

theorem existsUnique_torsion (G : Over S) [GrpObj G] (n : ℕ) {T : Over S} (x : T ⟶ G)
    (hx : x ^ n = 1) : ∃! y : T ⟶ torsion G n, y ≫ torsion.ι G n = x := by
  refine ⟨pullback.lift x (toUnit T) ((GrpTangent.comp_mulN x n).trans hx),
    pullback.lift_fst _ _ _, fun y hy => ?_⟩
  exact pullback.hom_ext (hy.trans (pullback.lift_fst _ _ _).symm) (toUnit_unique _ _)

theorem torsionι_pow_eq_one (G : Over S) [GrpObj G] (n : ℕ) : torsion.ι G n ^ n = 1 := by
  rw [← GrpTangent.comp_mulN]
  refine pullback.condition.trans ?_
  rw [toUnit_unique (pullback.snd _ _) (toUnit _)]
  rfl

theorem eq_prod_zpow {La I A : Type} [AddCommGroup La] [Fintype I] [CommGroup A]
    (b : Module.Basis I ℤ La) (f : La → A) (hf : ∀ a c, f (a + c) = f a * f c) (a : La) :
    f a = ∏ i, f (b i) ^ (b.repr a i) := by
  let φ : Multiplicative La →* A := MonoidHom.mk' (fun x => f x.toAdd) fun x y => hf _ _
  have h : ∀ x, f x = φ (Multiplicative.ofAdd x) := fun _ => rfl
  conv_lhs => rw [← b.sum_repr a]
  simp only [h, ofAdd_sum, ofAdd_zsmul, map_prod, map_zpow]

end GlobalTheory.LatticeTorsion

namespace GlobalTheory


open LatticeTorsion in
theorem exists_finiteEtale_latticeTorsionHom :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La], IsAbelianScheme G → IsUnit (n : Γ(S, ⊤)) → ∃ (Z : Over S) (et : La → (Z ⟶ G)), IsFinite Z.hom ∧ Etale Z.hom ∧ (∀ a c, et (a + c) = et a * et c) ∧ (∀ a, et a ^ n = 1) ∧ ∀ (T : Over S) (et' : La → (T ⟶ G)), (∀ a c, et' (a + c) = et' a * et' c) → (∀ a, et' a ^ n = 1) → ∃! h : T ⟶ Z, ∀ a, h ≫ et a = et' a := by
  intro S G _ _ n La _ _ _ hG hn
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion G hn
  let b := Module.finBasis ℤ La
  let r := Module.finrank ℤ La
  let Z := Out.powObj (torsion G n) r
  let x : Fin r → (Z ⟶ G) := fun i => Out.powPr (torsion G n) i ≫ torsion.ι G n
  have hx : ∀ i, x i ^ n = 1 := fun i => by
    rw [← MonObj.comp_pow, torsionι_pow_eq_one, MonObj.comp_one]
  let et : La → (Z ⟶ G) := fun a => ∏ i, x i ^ (b.repr a i)
  have hadd : ∀ a c, et (a + c) = et a * et c := fun a c => by
    simp only [et, map_add (f := _), Finsupp.add_apply, zpow_add, Finset.prod_mul_distrib]
  have hb : ∀ i, et (b i) = x i := fun i => by
    simp only [et, Module.Basis.repr_self]
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [Finsupp.single_eq_of_ne hj]) (by simp)]
    simp
  refine ⟨Z, et, prop_powObj @IsFinite _ hfin r, prop_powObj @Etale _ het r, hadd, fun a => ?_,
    fun T et' hadd' hpow' => ?_⟩
  · simp only [et, ← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  · choose y hy hyu using fun i : Fin r => existsUnique_torsion G n (et' (b i)) (hpow' _)
    let h : T ⟶ Z := (Out.powIsLimit (torsion G n) r).lift (Fan.mk T y)
    have hh : ∀ i, h ≫ Out.powPr (torsion G n) i = y i := fun i =>
      (Out.powIsLimit (torsion G n) r).fac (Fan.mk T y) ⟨i⟩
    refine ⟨h, fun a => ?_, fun h' hh' => ?_⟩
    · rw [eq_prod_zpow b (fun a => h ≫ et a) (fun a c => by rw [hadd, MonObj.comp_mul]) a,
        eq_prod_zpow b et' hadd' a]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hb, ← hy i, ← hh i, Category.assoc]
    · refine (Out.powIsLimit (torsion G n) r).hom_ext fun ⟨i⟩ => ?_
      refine (hyu i _ ?_).trans (hh i).symm
      have := hh' (b i)
      rw [hb] at this
      exact (Category.assoc _ _ _).trans this

end GlobalTheory
end
