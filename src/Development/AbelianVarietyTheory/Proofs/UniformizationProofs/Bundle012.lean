module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoOfIsClosedImmersionOfThickenings
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
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
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.RingGlue

noncomputable def loc {Y B : Scheme.{0}} {W : Y.Opens} {V : B.Opens} (hV : IsAffineOpen V)
    (ψ : Γ(B, V) ⟶ Γ(Y, W)) : W.toScheme ⟶ B :=
  W.toSpecΓ ≫ Spec.map ψ ≫ hV.fromSpec

theorem homOfLE_loc {Y B : Scheme.{0}} {W W' : Y.Opens} {V V' : B.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen V') (ψ : Γ(B, V) ⟶ Γ(Y, W)) (ψ' : Γ(B, V') ⟶ Γ(Y, W'))
    (h : W' ≤ W) (e : V' ≤ V)
    (H : B.presheaf.map (homOfLE e).op ≫ ψ' = ψ ≫ Y.presheaf.map (homOfLE h).op) :
    Y.homOfLE h ≫ loc hV ψ = loc hV' ψ' := by
  unfold loc
  rw [← IsAffineOpen.map_fromSpec hV hV' (homOfLE e).op, ← Spec.map_comp_assoc, H,
    Spec.map_comp_assoc, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc]

theorem appLE_of_loc {Y B : Scheme.{0}} {W : Y.Opens} {V : B.Opens} (hV : IsAffineOpen V)
    (ψ : Γ(B, V) ⟶ Γ(Y, W)) (q : Y ⟶ B) (hq : W.ι ≫ q = loc hV ψ) :
    ∃ h : W ≤ q ⁻¹ᵁ V, q.appLE V W h = ψ := by
  have h : W ≤ q ⁻¹ᵁ V := by
    intro y hy
    have h1 : q y = hV.fromSpec ((W.toSpecΓ ≫ Spec.map ψ) ⟨y, hy⟩) := by
      have := congr($(hq) ⟨y, hy⟩)
      exact this
    change q y ∈ (V : Set B)
    rw [h1, ← hV.range_fromSpec]
    exact ⟨_, rfl⟩
  refine ⟨h, ?_⟩
  have h2 : W.toSpecΓ ≫ Spec.map (q.appLE V W h) ≫ hV.fromSpec = W.ι ≫ q := by
    rw [Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, IsAffineOpen.toSpecΓ_fromSpec,
      Scheme.Hom.resLE_comp_ι]
  rw [hq, loc, ← Category.assoc, ← Category.assoc, cancel_mono] at h2
  have h3 := congr(($h2).appTop)
  simp only [Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop,
    Scheme.ΓSpecIso_naturality_assoc] at h3
  simpa only [cancel_epi, cancel_mono] using h3


set_option backward.isDefEq.respectTransparency false in
theorem exists_hom_of_ring_maps : (∀ (Y B : Scheme.{0}) (κ : Type) (W : κ → Y.Opens) (V : κ → B.Opens), (∀ k, IsAffineOpen (V k)) → ∀ (ψ : ∀ k, Γ(B, V k) ⟶ Γ(Y, W k)), (∀ y : Y, ∃ k, y ∈ W k) → (∀ (k l : κ) (y : Y), y ∈ W k → y ∈ W l → ∃ (m : κ) (h : W m ≤ W k) (h' : W m ≤ W l) (e : V m ≤ V k) (e' : V m ≤ V l), y ∈ W m ∧ B.presheaf.map (homOfLE e).op ≫ ψ m = ψ k ≫ Y.presheaf.map (homOfLE h).op ∧ B.presheaf.map (homOfLE e').op ≫ ψ m = ψ l ≫ Y.presheaf.map (homOfLE h').op) → ∃ q : Y ⟶ B, ∀ k, ∃ h : W k ≤ q ⁻¹ᵁ V k, q.appLE (V k) (W k) h = ψ k) := by
  intro Y B κ W V hV ψ hc hbas
  let 𝒱 : Y.OpenCover := Y.openCoverOfIsOpenCover W (by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro y _
    obtain ⟨k, hk⟩ := hc y
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨k, hk⟩)
  let q : Y ⟶ B := 𝒱.glueMorphisms (fun k ↦ loc (hV k) (ψ k)) (by
    intro k l
    apply Scheme.hom_ext_of_forall
    intro x
    have hx : (pullback.fst (𝒱.f k) (𝒱.f l) x).1 = (pullback.snd (𝒱.f k) (𝒱.f l) x).1 :=
      congr($(pullback.condition (f := 𝒱.f k) (g := 𝒱.f l)) x)
    obtain ⟨m, h1, h2, e1, e2, hxW, H1, H2⟩ := hbas k l _ (pullback.fst (𝒱.f k) (𝒱.f l) x).2
      (hx ▸ (pullback.snd (𝒱.f k) (𝒱.f l) x).2)
    let α : (W m).toScheme ⟶ pullback (𝒱.f k) (𝒱.f l) :=
      pullback.lift (Y.homOfLE h1) (Y.homOfLE h2) ((Y.homOfLE_ι h1).trans (Y.homOfLE_ι h2).symm)
    have hα1 : α ≫ pullback.fst _ _ = Y.homOfLE h1 := pullback.lift_fst _ _ _
    have hα2 : α ≫ pullback.snd _ _ = Y.homOfLE h2 := pullback.lift_snd _ _ _
    have : IsOpenImmersion (α ≫ pullback.fst _ _) := by rw [hα1]; infer_instance
    have : IsOpenImmersion α := .of_comp _ (pullback.fst _ _)
    refine ⟨α.opensRange, ⟨⟨_, hxW⟩, ?_⟩, ?_⟩
    · apply (pullback.fst (𝒱.f k) (𝒱.f l)).isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hα1]
      exact Subtype.ext (Scheme.homOfLE_apply _ _)
    · rw [← cancel_epi α.isoOpensRange.hom]
      simp only [Scheme.Hom.isoOpensRange_hom_ι_assoc]
      rw [reassoc_of% hα1, reassoc_of% hα2]
      exact (homOfLE_loc (hV k) (hV m) _ _ h1 e1 H1).trans
        (homOfLE_loc (hV l) (hV m) _ _ h2 e2 H2).symm)
  exact ⟨q, fun k ↦ appLE_of_loc (hV k) (ψ k) q (𝒱.ι_glueMorphisms _ _ k)⟩

end GlobalTheory.RingGlue
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.FourthSide

theorem gm_pull_g {X X' Y : Scheme.{0}} (L : LB X) (F : X' ⟶ X) (f : Y ⟶ X') (y : Y) (j j' : L.ι)
    (hj : F (f y) ∈ L.U j) (hj' : F (f y) ∈ L.U j') :
    gm f y ((L.pull F).U (fun _ => j) ⊓ (L.pull F).U (fun _ => j')) ((L.pull F).g (fun _ => j) (fun _ => j')) =
      gm (f ≫ F) y _ (L.g j j') := by
  have hp : f y ∈ (L.pull F).U (fun _ => j) ⊓ (L.pull F).U (fun _ => j') := ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  show gm f y _ (∏ _k : PUnit, (res _ (pullU F _ (L.g j j'))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res f y _ hp _).trans (gm_pull f F y (L.U j ⊓ L.U j') ⟨hj, hj'⟩ _)

variable {B B' G G' Ge Ge' : Scheme.{0}} {M : LB B} {M' : LB B'} {L : LB G} {L' : LB G'}
  {Φ : B' ⟶ B} {Ψ : G' ⟶ G} {pG : Ge ⟶ B} {pG' : Ge' ⟶ B'} {fG : Ge ⟶ G} {fG' : Ge' ⟶ G'} {h : Ge' ⟶ Ge}

def germ (pG' : Ge' ⟶ B') (fG' : Ge' ⟶ G') (h : Ge' ⟶ Ge) (w : LB.Iso M' (M.pull Φ)) (wL : LB.Iso L' (L.pull Ψ))
    (we : LB.Iso (L.pull fG) (M.pull pG)) {Z : Scheme.{0}} (r : Z ⟶ Ge') (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι)
    (jL' : L'.ι) : (Z.presheaf.stalk z)ˣ :=
  (gw w (r ≫ pG') z jM jM')⁻¹ * (gw we (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ fG') z jL jL')

theorem germ_change (e₁ : pG' ≫ Φ = h ≫ pG) (e₂ : h ≫ fG = fG' ≫ Ψ) {w : LB.Iso M' (M.pull Φ)}
    {wL : LB.Iso L' (L.pull Ψ)} {we : LB.Iso (L.pull fG) (M.pull pG)} (hw : PGen w) (hwL : PGen wL) (hwe : PGen we)
    {Z : Scheme.{0}} (r : Z ⟶ Ge') (z : Z) (jM kM : M.ι) (jM' kM' : M'.ι) (jL kL : L.ι) (jL' kL' : L'.ι)
    (a₁ : Φ (pG' (r z)) ∈ M.U jM) (a₂ : pG' (r z) ∈ M'.U jM') (a₃ : Ψ (fG' (r z)) ∈ L.U jL)
    (a₄ : fG' (r z) ∈ L'.U jL') (b₁ : Φ (pG' (r z)) ∈ M.U kM) (b₂ : pG' (r z) ∈ M'.U kM')
    (b₃ : Ψ (fG' (r z)) ∈ L.U kL) (b₄ : fG' (r z) ∈ L'.U kL') :
    germ pG' fG' h w wL we r z jM jM' jL jL' =
      gm (r ≫ pG') z _ (M'.g jM' kM') * (gm (r ≫ fG') z _ (L'.g jL' kL'))⁻¹ *
        germ pG' fG' h w wL we r z kM kM' kL kL' := by
  have p₁ : pG (h (r z)) = Φ (pG' (r z)) := congrArg (fun g => g (r z)) e₁.symm
  have p₂ : fG (h (r z)) = Ψ (fG' (r z)) := congrArg (fun g => g (r z)) e₂
  have c₃ : fG (h (r z)) ∈ L.U jL := p₂ ▸ a₃
  have d₃ : fG (h (r z)) ∈ L.U kL := p₂ ▸ b₃
  have c₁ : pG (h (r z)) ∈ M.U jM := p₁ ▸ a₁
  have d₁ : pG (h (r z)) ∈ M.U kM := p₁ ▸ b₁
  have a := hw Z (r ≫ pG') z jM kM jM' kM' a₁ b₁ a₂ b₂
  have b := hwL Z (r ≫ fG') z jL kL jL' kL' a₃ b₃ a₄ b₄
  have c := hwe Z (r ≫ h) z jM kM (fun _ => jL) (fun _ => kL) c₁ d₁ (mem_pull.2 c₃) (mem_pull.2 d₃)
  rw [gm_pull_g L fG (r ≫ h) z jL kL c₃ d₃, Category.assoc, Category.assoc, ← e₁, e₂] at c
  rw [Category.assoc] at a b
  unfold germ
  rw [a, b, c]
  generalize gm (r ≫ pG' ≫ Φ) z _ (M.g jM kM) = A
  generalize gm (r ≫ fG' ≫ Ψ) z _ (L.g jL kL) = C
  generalize gm (r ≫ pG') z _ (M'.g jM' kM') = A'
  generalize gm (r ≫ fG') z _ (L'.g jL' kL') = C'
  generalize gw w (r ≫ pG') z kM kM' = P
  generalize gw wL (r ≫ fG') z kL kL' = Q
  generalize gw we (r ≫ h) z kM (fun _ => kL) = R
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_unit (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB) (hL' : L'.IsLB)
    (e₁ : pG' ≫ Φ = h ≫ pG) (e₂ : h ≫ fG = fG' ≫ Ψ) {w : LB.Iso M' (M.pull Φ)}
    {wL : LB.Iso L' (L.pull Ψ)} {we : LB.Iso (L.pull fG) (M.pull pG)} (hw : PGen w) (hwL : PGen wL) (hwe : PGen we)
    (jM' : M'.ι) (jL' : L'.ι) :
    ∃ s : Γ(Ge', (M'.pull pG').U (fun _ => jM') ⊓ (L'.pull fG').U (fun _ => jL'))ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (jM : M.ι) (jL : L.ι), Φ (pG' (r z)) ∈ M.U jM →
        pG' (r z) ∈ M'.U jM' → Ψ (fG' (r z)) ∈ L.U jL → fG' (r z) ∈ L'.U jL' →
        gm r z _ s = germ pG' fG' h w wL we r z jM jM' jL jL' := by
  have p₁ : ∀ x, pG (h x) = Φ (pG' x) := fun x => congrArg (fun g => g x) e₁.symm
  have p₂ : ∀ x, fG (h x) = Ψ (fG' x) := fun x => congrArg (fun g => g x) e₂
  obtain ⟨W, hW⟩ : ∃ W : M.ι × L.ι → Ge'.Opens, ∀ i x, x ∈ W i ↔
      Φ (pG' x) ∈ M.U i.1 ∧ pG' x ∈ M'.U jM' ∧ Ψ (fG' x) ∈ L.U i.2 ∧ fG' x ∈ L'.U jL' :=
    ⟨fun i => pG' ⁻¹ᵁ (Φ ⁻¹ᵁ M.U i.1) ⊓ (pG' ⁻¹ᵁ M'.U jM' ⊓ (fG' ⁻¹ᵁ (Ψ ⁻¹ᵁ L.U i.2) ⊓ fG' ⁻¹ᵁ L'.U jL')),
      fun _ _ => Iff.rfl⟩
  have l₀ : ∀ i, W i ≤ (M'.pull pG').U (fun _ => jM') ⊓ (L'.pull fG').U (fun _ => jL') := fun i x hx =>
    ⟨mem_pull.2 ((hW i x).1 hx).2.1, mem_pull.2 ((hW i x).1 hx).2.2.2⟩
  have l₁ : ∀ i, W i ≤ pG' ⁻¹ᵁ ((M.pull Φ).U (fun _ => i.1) ⊓ M'.U jM') := fun i x hx =>
    ⟨mem_pull.2 ((hW i x).1 hx).1, ((hW i x).1 hx).2.1⟩
  have l₂ : ∀ i, W i ≤ h ⁻¹ᵁ ((M.pull pG).U (fun _ => i.1) ⊓ (L.pull fG).U (fun _ => i.2)) := fun i x hx =>
    ⟨mem_pull.2 ((p₁ x).symm ▸ ((hW i x).1 hx).1), mem_pull.2 ((p₂ x).symm ▸ ((hW i x).1 hx).2.2.1)⟩
  have l₃ : ∀ i, W i ≤ fG' ⁻¹ᵁ ((L.pull Ψ).U (fun _ => i.2) ⊓ L'.U jL') := fun i x hx =>
    ⟨mem_pull.2 ((hW i x).1 hx).2.2.1, ((hW i x).1 hx).2.2.2⟩
  obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(Ge', W i)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (i : M.ι × L.ι), r z ∈ W i →
      gm r z (W i) (u i) = germ pG' fG' h w wL we r z i.1 jM' i.2 jL' :=
    ⟨fun i => (res (l₁ i) (pullU pG' _ (w.s (fun _ => i.1, jM'))))⁻¹ *
        (res (l₂ i) (pullU h _ (we.s (fun _ => i.1, fun _ => i.2))) *
          res (l₃ i) (pullU fG' _ (wL.s (fun _ => i.2, jL')))),
      fun Z r z i hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans (congrArg (·⁻¹)
        ((gm_res r z (l₁ i) hz _).trans (gm_pull r pG' z _ (l₁ i hz) _)))) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((gm_res r z (l₂ i) hz _).trans (gm_pull r h z _ (l₂ i hz) _))
          ((gm_res r z (l₃ i) hz _).trans (gm_pull r fG' z _ (l₃ i hz) _)))))⟩
  obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
      obtain ⟨i, hi⟩ := exists_chart hM (Φ (pG' x))
      obtain ⟨j, hj⟩ := exists_chart hL (Ψ (fG' x))
      exact Opens.mem_iSup.2 ⟨(i, j), (hW (i, j) x).2 ⟨hi, mem_pull.1 hx.1, hj, mem_pull.1 hx.2⟩⟩) u
    (fun i i' x hx => by
      have h₁ := (hW i x).1 hx.1
      have h₂ := (hW i' x).1 hx.2
      have k := germ_change e₁ e₂ hw hwL hwe (𝟙 Ge') x i.1 i'.1 jM' jM' i.2 i'.2 jL' jL' h₁.1 h₁.2.1 h₁.2.2.1
        h₁.2.2.2 h₂.1 h₂.2.1 h₂.2.2.1 h₂.2.2.2
      rw [gm_self hM' (𝟙 Ge' ≫ pG') x h₁.2.1, gm_self hL' (𝟙 Ge' ≫ fG') x h₁.2.2.2, inv_one, one_mul, one_mul] at k
      exact (hu _ (𝟙 Ge') x i hx.1).trans (k.trans (hu _ (𝟙 Ge') x i' hx.2).symm))
  refine ⟨s, fun Z r z jM jL a₁ a₂ a₃ a₄ => ?_⟩
  have hz := (hW (jM, jL) (r z)).2 ⟨a₁, a₂, a₃, a₄⟩
  exact (gm_res r z (l₀ (jM, jL)) hz s).symm.trans
    ((congrArg (gm r z (W (jM, jL))) (hs (jM, jL))).trans (hu Z r z (jM, jL) hz))

theorem exists_fourth_side (B B' G G' Ge Ge' : Scheme.{0}) (M : LB B) (M' : LB B') (L : LB G) (L' : LB G')
    (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB) (hL' : L'.IsLB) (Φ : B' ⟶ B) (Ψ : G' ⟶ G) (pG : Ge ⟶ B)
    (pG' : Ge' ⟶ B') (fG : Ge ⟶ G) (fG' : Ge' ⟶ G') (h : Ge' ⟶ Ge) (e₁ : pG' ≫ Φ = h ≫ pG)
    (e₂ : h ≫ fG = fG' ≫ Ψ) (w : LB.Iso M' (M.pull Φ)) (wL : LB.Iso L' (L.pull Ψ))
    (we : LB.Iso (L.pull fG) (M.pull pG)) (hw : w.IsGen) (hwL : wL.IsGen) (hwe : we.IsGen) :
    ∃ we' : LB.Iso (L'.pull fG') (M'.pull pG'), we'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι) (jL' : L'.ι),
        Φ (pG' (r z)) ∈ M.U jM → pG' (r z) ∈ M'.U jM' → Ψ (fG' (r z)) ∈ L.U jL → fG' (r z) ∈ L'.U jL' →
        gw w (r ≫ pG') z jM jM' * gw we' r z jM' (fun _ => jL') =
          gw we (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ fG') z jL jL' := by
  rw [isGen_iff] at hw hwL hwe
  choose s hs using exists_unit hM hM' hL hL' e₁ e₂ hw hwL hwe
  refine ⟨⟨fun p => s (p.1 PUnit.unit) (p.2 PUnit.unit)⟩, (isGen_iff _).2 ?_, fun Z r z jM jM' jL jL' a₁ a₂ a₃ a₄ => ?_⟩
  · intro Z r z j j' k k' a₂ b₂ a₄ b₄
    obtain ⟨i, hi⟩ := exists_chart hM (Φ (pG' (r z)))
    obtain ⟨l, hl⟩ := exists_chart hL (Ψ (fG' (r z)))
    have a₄' := mem_pull.1 a₄
    have b₄' := mem_pull.1 b₄
    have c := germ_change e₁ e₂ hw hwL hwe r z i i j j' l l _ _ hi a₂ hl a₄' hi b₂ hl b₄'
    rw [← hs j _ Z r z i l hi a₂ hl a₄', ← hs j' _ Z r z i l hi b₂ hl b₄',
      ← gm_pull_g L' fG' r z _ _ a₄' b₄'] at c
    exact c
  · exact (congrArg (gw w (r ≫ pG') z jM jM' * ·) (hs jM' jL' Z r z jM jL a₁ a₂ a₃ a₄)).trans
      (mul_inv_cancel_left _ _)

end GlobalTheory.FourthSide
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open ThickeningClosed in
theorem isIso_of_isClosedImmersion_of_thickenings_of_isProper {R : Type} [CommRing R]
    [IsNoetherianRing R] (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥)
    (Y : Over (Spec (CommRingCat.of R))) [IsProper Y.hom] {Z : Scheme.{0}} (j : Z ⟶ Y.left)
    [IsClosedImmersion j]
    (h : ∀ n : ℕ, ∃ l : (thickObj R I n Y).left ⟶ Z, l ≫ j = (fstG I n Y).left) : IsIso j := by
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have h' : ∀ n : ℕ, ∃ l : pullback Y.hom (thick R I n) ⟶ Z, l ≫ j = pullback.fst Y.hom (thick R I n) :=
    fun n => h n
  have hnear : ∀ x : Y.left, x ∈ zeroLocusOpen j.ker := by
    by_contra hne
    simp only [not_forall] at hne
    obtain ⟨x₀, hx₀⟩ := hne
    have hSc : IsClosed (zeroLocusOpen j.ker)ᶜ := (isOpen_zeroLocusOpen j.ker).isClosed_compl
    have hT : IsClosed (Y.hom '' (zeroLocusOpen j.ker)ᶜ) := Y.hom.isClosedMap _ hSc
    obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal (Y.hom x₀).asIdeal (Y.hom x₀).isPrime.ne_top
    have hcl : (⟨m, hm.isPrime⟩ : PrimeSpectrum (CommRingCat.of R)) ∈ closure {Y.hom x₀} :=
      (PrimeSpectrum.le_iff_mem_closure _ _).mp hpm
    obtain ⟨x, hxS, hx⟩ :=
      closure_minimal (Set.singleton_subset_iff.mpr
        (Set.mem_image_of_mem _ hx₀ : Y.hom x₀ ∈ Y.hom '' (zeroLocusOpen j.ker)ᶜ)) hT hcl
    apply hxS
    refine ThickeningClosed.mem_of_thickenings I Y.hom j h' x ?_
    rw [hx]
    exact hI.trans (sInf_le ⟨bot_le, hm⟩)
  have hker : j.ker = ⊥ := by
    ext U a
    simp only [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, Submodule.mem_bot]
    constructor
    · intro ha
      have hJ : LinearMap.ker (LinearMap.toSpanSingleton Γ(Y.left, U) Γ(Y.left, U) a) = ⊤ := by
        by_contra hJ
        obtain ⟨q, hq, hJq⟩ := Ideal.exists_le_maximal _ hJ
        obtain ⟨s, hs, hsa⟩ :=
          ThickeningClosed.exists_mul_eq_zero_of_mem j.ker U ⟨q, hq.isPrime⟩ (hnear _) ha
        exact hs (hJq (by simp [LinearMap.mem_ker, hsa]))
      have h1 : (1 : Γ(Y.left, U)) ∈ LinearMap.ker (LinearMap.toSpanSingleton Γ(Y.left, U) Γ(Y.left, U) a) :=
        hJ ▸ Submodule.mem_top
      simpa using h1
    · rintro rfl
      exact zero_mem _
  exact IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker

theorem hom_eq_of_thickenings_of_isProper : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (Y Z : Over (Spec (CommRingCat.of R))) [IsProper Y.hom] [IsSeparated Z.hom] (f g : Y ⟶ Z), (∀ e, (fstG I e Y).left ≫ f.left = (fstG I e Y).left ≫ g.left) → f = g := by
  intro R _ _ _ I hI Y Z _ _ f g hfg
  have hf : f.left ≫ Z.hom = Y.hom := Over.w f
  have hg : g.left ≫ Z.hom = Y.hom := Over.w g
  obtain ⟨φ, hφ⟩ : ∃ φ : Y.left ⟶ pullback Z.hom Z.hom,
      φ = pullback.lift f.left g.left (hf.trans hg.symm) := ⟨_, rfl⟩
  have hφ1 : φ ≫ pullback.fst Z.hom Z.hom = f.left := by rw [hφ, pullback.lift_fst]
  have hφ2 : φ ≫ pullback.snd Z.hom Z.hom = g.left := by rw [hφ, pullback.lift_snd]
  have hι : IsIso (pullback.fst φ (pullback.diagonal Z.hom)) := by
    refine isIso_of_isClosedImmersion_of_thickenings_of_isProper I hI Y _ fun n => ?_
    refine ⟨pullback.lift (fstG I n Y).left ((fstG I n Y).left ≫ f.left) ?_, pullback.lift_fst _ _ _⟩
    apply pullback.hom_ext
    · simp [hφ1]
    · simp [hφ2, hfg n]
  have key : φ = inv (pullback.fst φ (pullback.diagonal Z.hom)) ≫
      pullback.snd φ (pullback.diagonal Z.hom) ≫ pullback.diagonal Z.hom := by
    rw [← pullback.condition, IsIso.inv_hom_id_assoc]
  apply Over.OverMorphism.ext
  rw [← hφ1, ← hφ2, key]
  simp

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.open_eq_top_of_contains_special_part_universallyClosed : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (Y : Over (Spec (CommRingCat.of R))) [UniversallyClosed Y.hom] (U : Y.left.Opens), (∀ z : (thickObj R I 0 Y).left, pullback.fst Y.hom (thick R I 0) z ∈ U) → U = ⊤ := by
  first | exact @GlobalTheory.Unif.eq_top_of_special_part | exact GlobalTheory.Unif.eq_top_of_special_part | (intros; apply GlobalTheory.Unif.eq_top_of_special_part <;> assumption)
end
