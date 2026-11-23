module

import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle126
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle060
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle019
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle002

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU

variable {S S' : Scheme.{0}} {f : S' ⟶ S}

private theorem comp_mul_of_isGrpPullback_lift {G H : Over S} {G' H' : Over S'} [GrpObj G] [GrpObj H]
    [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hφ : IsGrpPullback G' G f φ)
    (hψ : IsGrpPullback H' H f ψ) (a : G ⟶ H) [IsMonHom a] (a' : G' ⟶ H') (h : a'.left ≫ ψ = φ ≫ a.left)
    {T : Over S'} (x y : T ⟶ G') : (x * y) ≫ a' = (x ≫ a') * (y ≫ a') := by
  apply Over.OverMorphism.ext
  apply hψ.1.hom_ext
  · let x₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk (x.left ≫ φ) (by
      show (x.left ≫ φ) ≫ G.hom = T.hom ≫ f
      rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w])
    let y₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk (y.left ≫ φ) (by
      show (y.left ≫ φ) ≫ G.hom = T.hom ≫ f
      rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w])
    let x₁ : Over.mk (T.hom ≫ f) ⟶ H := Over.homMk ((x ≫ a').left ≫ ψ) (by
      show ((x ≫ a').left ≫ ψ) ≫ H.hom = T.hom ≫ f
      rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w])
    let y₁ : Over.mk (T.hom ≫ f) ⟶ H := Over.homMk ((y ≫ a').left ≫ ψ) (by
      show ((y ≫ a').left ≫ ψ) ≫ H.hom = T.hom ≫ f
      rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w])
    have e1 := hφ.2 T x y x₀ y₀ rfl rfl
    have e2 := hψ.2 T (x ≫ a') (y ≫ a') x₁ y₁ rfl rfl
    have e3 : x₁ = x₀ ≫ a := by
      apply Over.OverMorphism.ext
      simp only [x₁, x₀, Over.comp_left, Over.homMk_left, Category.assoc, h]
    have e4 : y₁ = y₀ ≫ a := by
      apply Over.OverMorphism.ext
      simp only [y₁, y₀, Over.comp_left, Over.homMk_left, Category.assoc, h]
    calc ((x * y) ≫ a').left ≫ ψ = (x * y).left ≫ φ ≫ a.left := by
          rw [Over.comp_left, Category.assoc, h]
      _ = ((x₀ * y₀) ≫ a).left := by rw [← Category.assoc, ← e1, Over.comp_left]
      _ = (x₁ * y₁).left := by rw [MonObj.mul_comp, e3, e4]
      _ = ((x ≫ a') * (y ≫ a')).left ≫ ψ := e2
  · rw [Over.w, Over.w]

theorem isMonHom_of_over_isMonHom {G H : Over S} {G' H' : Over S'} [GrpObj G] [GrpObj H] [GrpObj G'] [GrpObj H']
    {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hφ : IsGrpPullback G' G f φ) (hψ : IsGrpPullback H' H f ψ)
    (a : G ⟶ H) [IsMonHom a] (a' : G' ⟶ H') (h : a'.left ≫ ψ = φ ≫ a.left) : IsMonHom a' := by
  apply (config := { allowSynthFailures := true }) GlobalTheory.SharpPull.isMonHom_lift <;> assumption

theorem eSec_comp_of_isGrpPullback {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}
    (hφ : IsGrpPullback G' G f φ) : (η[G']).left ≫ φ = f ≫ (η[G]).left := by
  have h1 : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  let P : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G := Over.homMk ((η[G']).left ≫ φ) (by
    show ((η[G']).left ≫ φ) ≫ G.hom = (𝟙_ (Over S')).hom ≫ f
    rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w])
  have e := hφ.2 (𝟙_ (Over S')) η[G'] η[G'] P P rfl rfl
  have hP : P * P = P := by
    apply Over.OverMorphism.ext
    rw [e, ← h1, _root_.mul_one, h1]
    rfl
  have hP1 : P = 1 := mul_eq_left.mp hP
  have hl := congrArg Over.Hom.left hP1
  rw [Hom.one_def, Over.comp_left] at hl
  change (η[G']).left ≫ φ = _ at hl
  rw [hl]
  congr 1

theorem IsWt.pull {X : Type} [AddCommGroup X] {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) {i : splitTorus S X ⟶ G} {i' : splitTorus S' X ⟶ G'}
    (hi : TorusCompat f F i' i) {V : G.left.Opens} {V' : G'.left.Opens} (hV : V' ≤ F ⁻¹ᵁ V) {u : Γ(G.left, V)}
    {χ : X} (hu : IsWt i V u χ) : IsWt i' V' ((F.appLE V V' hV).hom u) χ := by
  obtain ⟨τ, hτ, hχ, hτi⟩ := hi
  intro Z' t' g' h₁ h₂
  let Z : Over S := Over.mk (Z'.hom ≫ f)
  let t : Z ⟶ splitTorus S X := Over.homMk (t'.left ≫ τ) (by
    show (t'.left ≫ τ) ≫ (splitTorus S X).hom = Z'.hom ≫ f
    rw [Category.assoc, hτ, ← Category.assoc, Over.w])
  let g : Z ⟶ G := Over.homMk (g'.left ≫ F) (by
    show (g'.left ≫ F) ≫ G.hom = Z'.hom ≫ f
    rw [Category.assoc, hF.1.w, ← Category.assoc, Over.w])
  let x₀ : Z ⟶ G := Over.homMk ((t' ≫ i').left ≫ F) (by
    show ((t' ≫ i').left ≫ F) ≫ G.hom = Z'.hom ≫ f
    rw [Category.assoc, hF.1.w, ← Category.assoc, Over.w])
  have hx₀ : t ≫ i = x₀ := by
    apply Over.OverMorphism.ext
    simp only [t, x₀, Over.comp_left, Over.homMk_left, Category.assoc, hτi]
  have hmul : (t ≫ i * g).left = (t' ≫ i' * g').left ≫ F := by
    rw [hx₀]
    exact hF.2 Z' (t' ≫ i') g' x₀ g rfl rfl
  have h₁' : ⊤ ≤ (t ≫ i * g).left ⁻¹ᵁ V := by
    rw [hmul]
    intro x _
    exact hV (h₁ trivial)
  have h₂' : ⊤ ≤ g.left ⁻¹ᵁ V := by
    intro x _
    exact hV (h₂ trivial)
  have key := hu Z t g h₁' h₂'
  have hcong : ∀ (a b : Z'.left ⟶ G.left) (hab : a = b) (ha : ⊤ ≤ a ⁻¹ᵁ V) (hb : ⊤ ≤ b ⁻¹ᵁ V),
      (a.appLE V ⊤ ha).hom u = (b.appLE V ⊤ hb).hom u := by
    intro a b hab ha hb
    subst hab
    rfl
  have e1 : ((t' ≫ i' * g').left.appLE V' ⊤ h₁).hom ((F.appLE V V' hV).hom u) =
      (((t' ≫ i' * g').left ≫ F).appLE V ⊤ (by intro x _; exact hV (h₁ trivial))).hom u := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have e2 : (g'.left.appLE V' ⊤ h₂).hom ((F.appLE V V' hV).hom u) =
      ((g'.left ≫ F).appLE V ⊤ (by intro x _; exact hV (h₂ trivial))).hom u := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have hc : (t.left.appTop).hom (charUnit S X χ).val = (t'.left.appTop).hom (charUnit S' X χ).val := by
    show ((t'.left ≫ τ).appTop).hom _ = _
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hχ]
  rw [e1, e2]
  exact (hcong _ _ hmul.symm _ h₁').trans (key.trans (congrArg₂ (· * ·) hc (hcong _ _ rfl h₂' _)))

theorem exists_tq_baseChange : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (X : Type) [AddCommGroup X] (G : Over S) [GrpObj G]
    (G' : Over S') [GrpObj G'] (F : G'.left ⟶ G.left), IsGrpPullback G' G f F →
    ∀ Q : TQ G X, ∃ Q' : TQ G' X, TorusCompat f F Q'.i Q.i := by
  intro S S' f X _ G _ G' _ F hF Q
  letI := Q.grp
  letI := Q.comm
  haveI := Q.q_hom
  haveI := Q.i_hom
  obtain ⟨i', hi', -⟩ := existsUnique_torusCompat hF.1 Q.i
  haveI : IsMonHom i' := TorusCompat.isMonHom hF hi'
  have hB := isGrpPullback_pullback Q.B f
  let q' : G' ⟶ (Over.pullback f).obj Q.B :=
    Over.homMk (pullback.lift (F ≫ Q.q.left) G'.hom (by rw [Category.assoc, Over.w Q.q, hF.1.w]))
      (by exact pullback.lift_snd _ _ _)
  have hq'fst : q'.left ≫ pullback.fst Q.B.hom f = F ≫ Q.q.left := pullback.lift_fst _ _ _
  haveI : IsMonHom q' := isMonHom_of_over_isMonHom hF hB Q.q q' hq'fst
  have hBsq : IsPullback F q'.left Q.q.left (pullback.fst Q.B.hom f) := by
    refine IsPullback.of_bot ?_ hq'fst.symm (IsPullback.of_hasPullback Q.B.hom f)
    have e1 : q'.left ≫ pullback.snd Q.B.hom f = G'.hom := pullback.lift_snd _ _ _
    rw [e1, Over.w Q.q]
    exact hF.1
  have hAb : IsAbelianScheme ((Over.pullback f).obj Q.B) := by
    haveI := Q.isAb.smooth
    haveI := Q.isAb.proper
    haveI := Q.isAb.geomConnected
    exact ⟨inferInstance, by simp only [Over.pullback_obj_hom]; infer_instance,
      by simp only [Over.pullback_obj_hom]; infer_instance, by simp only [Over.pullback_obj_hom]; infer_instance⟩
  have hη : (η[(Over.pullback f).obj Q.B]).left ≫ pullback.fst Q.B.hom f = f ≫ (η[Q.B]).left :=
    eSec_comp_of_isGrpPullback hB
  have hT' : (toUnit (splitTorus S' X)).left = (splitTorus S' X).hom := by
    have := Over.w (toUnit (splitTorus S' X))
    simpa using this
  have hT : (toUnit (splitTorus S X)).left = (splitTorus S X).hom := by
    have := Over.w (toUnit (splitTorus S X))
    simpa using this
  have hker0 : IsPullback Q.i.left (splitTorus S X).hom Q.q.left (η[Q.B]).left := by
    have h0 : IsPullback Q.i.left (toUnit (splitTorus S X)).left Q.q.left (η[Q.B]).left :=
      Q.isKernel.map (Over.forget S)
    rw [hT] at h0
    exact h0
  have hcomp : IsPullback (i'.left ≫ F) (splitTorus S' X).hom Q.q.left
      ((η[(Over.pullback f).obj Q.B]).left ≫ pullback.fst Q.B.hom f) := by
    rw [← torusCompat_iff.mp hi', hη]
    exact (SplitTorus.isGrpPullback_bcMap f X).1.paste_horiz hker0
  have hcommA : i'.left ≫ q'.left = (splitTorus S' X).hom ≫ (η[(Over.pullback f).obj Q.B]).left := by
    apply hB.1.hom_ext
    · simpa only [Category.assoc, hq'fst] using hcomp.w
    · rw [Category.assoc, Over.w q', Over.w i', Category.assoc, Over.w η[(Over.pullback f).obj Q.B]]
      simp
  have hA : IsPullback i'.left (splitTorus S' X).hom q'.left (η[(Over.pullback f).obj Q.B]).left :=
    IsPullback.of_right hcomp hcommA hBsq
  have hker : IsPullback i' (toUnit (splitTorus S' X)) q' η := by
    apply IsPullback.of_map (Over.forget S')
    · apply Over.OverMorphism.ext
      show i'.left ≫ q'.left = (toUnit (splitTorus S' X)).left ≫ (η[(Over.pullback f).obj Q.B]).left
      rw [hT']
      exact hcommA
    · show IsPullback i'.left (toUnit (splitTorus S' X)).left q'.left (η[(Over.pullback f).obj Q.B]).left
      rw [hT']
      exact hA
  have hloc : ∀ (b : ((Over.pullback f).obj Q.B).left) (χ : X),
      ∃ V, b ∈ V ∧ ∃ u : (Γ(G'.left, q'.left ⁻¹ᵁ V))ˣ, IsWt i' (q'.left ⁻¹ᵁ V) (↑u) χ := by
    intro b χ
    obtain ⟨V, hbV, u, hu⟩ := Q.loc ((pullback.fst Q.B.hom f).base b) χ
    have hle : q'.left ⁻¹ᵁ (pullback.fst Q.B.hom f ⁻¹ᵁ V) ≤ F ⁻¹ᵁ (Q.q.left ⁻¹ᵁ V) := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hq'fst]
    refine ⟨pullback.fst Q.B.hom f ⁻¹ᵁ V, hbV, Units.map (F.appLE _ _ hle).hom.toMonoidHom u, ?_⟩
    exact IsWt.pull hF hi' hle hu
  exact ⟨TQ.mk _ hAb q' i' inferInstance inferInstance
    (MorphismProperty.of_isPullback (P := @Flat) hBsq Q.q_flat)
    (MorphismProperty.of_isPullback (P := @Surjective) hBsq Q.q_surj)
    (MorphismProperty.of_isPullback (P := @IsAffineHom) hBsq Q.q_affine) hker hloc, hi'⟩

end GlobalTheory.UU
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.lbIso_pw_sq_pull_pow_of_isLocalRing : ∀ (A : Type) [CommRing A] [IsLocalRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsCommMonObj B] (M : CP B) (n : ℕ), LBIso (pw M.L.L ((n : ℤ) ^ 2)) (M.L.L.pull (𝟙 B ^ n).left) := by
  first | exact @GlobalTheory.UU.lbIso_pw_pull_pow_local | exact GlobalTheory.UU.lbIso_pw_pull_pow_local | (intros; apply GlobalTheory.UU.lbIso_pw_pull_pow_local <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.ExpLin

def secComb {X : Scheme.{0}} {L : LB X} {n : ℕ} (b : Fin n → Γ(X, ⊤)) (t : Fin n → LB.Sec L) : LB.Sec L where
  f := fun j => ∑ i, resTop _ (b i) * (t i).f j
  compat := fun i j => by

    simp only [map_sum, map_mul, (t _).compat, DVR.SecOps.resTop_res, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => mul_left_comm _ _ _

theorem sval_secComb {X Y T Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {n : ℕ} (p : Y ⟶ T) (c : Fin n → Γ(T, ⊤)) (t : Fin n → LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (secComb (fun i => p.appTop.hom (c i)) t) r z J = ∑ i, gs (r ≫ p) z ⊤ (c i) * sval (t i) r z J := by
  rw [DVR.SectionScalarValuation.sval_lin (s := secComb (fun i => p.appTop.hom (c i)) t) (fun i => p.appTop.hom (c i)) t
    (fun _ => rfl) r z hJ]
  exact Finset.sum_congr rfl fun i _ => congrArg (· * _) (gs_pull r p z ⊤ trivial (c i))

theorem sum_comb {S X : Type} [CommRing S] [DecidableEq X] {n : ℕ} (w : S) (c a : Fin n → S) (s : Fin n → Finset X)
    (b : Fin n → X → S) (t : X → S) (h₀ : ∀ i, ∀ α ∉ s i, b i α = 0) (h : ∀ i, w * a i = ∑ α ∈ s i, b i α * t α) :
    w * ∑ i, c i * a i = ∑ α ∈ Finset.univ.biUnion s, (∑ i, c i * b i α) * t α := by
  simp only [Finset.sum_mul]
  rw [Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm, h i, Finset.mul_sum]
  simp only [_root_.mul_assoc]
  refine Finset.sum_subset (Finset.subset_biUnion_of_mem s (Finset.mem_univ i)) fun α _ hα => ?_
  rw [h₀ i α hα, zero_mul, mul_zero]

theorem expT_linear : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (T : Over (Spec (CommRingCat.of R))) (k n : ℕ) (c : Fin n → Γ(T.left, ⊤)) (σ : Fin n → U.SecGT T k) (f : Fin n → ∀ α, SecBT D T k α), (∀ i, U.ExpT T k (σ i) (f i)) → ∃ (σ' : U.SecGT T k) (f' : ∀ α, SecBT D T k α), U.ExpT T k σ' f' ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ G).left) (z : Z) (J), Good U.P.L.L z J → sval σ' r z J = ∑ i, gs (r ≫ (fst T G).left) z ⊤ (c i) * sval (σ i) r z J) ∧ ∀ α (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ D.P.A).left) (z : Z) (J), Good D.P.L z J → sval (f' α) r z J = ∑ i, gs (r ≫ (fst T D.P.A).left) z ⊤ (c i) * sval (f i α) r z J := by
  classical
  intro R _ _ I D A G _ _ U T k n c σ f h
  refine ⟨secComb (fun i => (fst T G).left.appTop.hom (c i)) σ,
    fun α => secComb (fun i => (fst T D.P.A).left.appTop.hom (c i)) (fun i => f i α), fun e => ?_,
    fun Z r z J hJ => sval_secComb _ c σ r z hJ, fun α Z r z J hJ => sval_secComb _ c (fun i => f i α) r z hJ⟩
  choose s hs using fun i => h i e
  refine ⟨Finset.univ.biUnion s, fun Z x rG rB h₁ h₂ h₃ z JG J hG hJ => ⟨fun α hα => ?_, ?_⟩⟩
  · rw [sval_secComb _ c (fun i => f i α) rB z hJ]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [(hs i Z x rG rB h₁ h₂ h₃ z JG J hG hJ).1 α
      (fun hi => hα (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hi⟩)), mul_zero]
  · rw [sval_secComb _ c σ rG z hG]
    refine Eq.trans ?_ (Finset.sum_congr rfl fun α _ =>
      (congrArg (· * _) (sval_secComb (fst T D.P.A).left c (fun i => f i α) rB z hJ)).symm)
    rw [h₃]
    exact sum_comb _ _ _ s (fun i α => sval (f i α) rB z J) _
      (fun i => (hs i Z x rG rB h₁ h₂ h₃ z JG J hG hJ).1) (fun i => (hs i Z x rG rB h₁ h₂ h₃ z JG J hG hJ).2)

end GlobalTheory.UU.ExpLin
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem line_zero_const {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F (DegPre.zeroF D F)) (DegPre.lineε k))) (hw : w.IsGen) :
    ∃ c : Fˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) (J), Good D.P.L z J →
      (val w r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c.val) := by
  have hI : IsIso (Scheme.Hom.appTop (𝟙 (TF (R := R) F).left)) :=
    inferInstanceAs (IsIso (Scheme.Hom.app (𝟙 (TF (R := R) F).left) ⊤))
  obtain ⟨a, ha⟩ := H1.exists_const D.P.L D.P.isLB (𝟙 _) (ConcreteCategory.bijective_of_isIso _).2 w hw
    (fun U _ h => by
      rw [Fin.prod_univ_two]
      show h (DegPre.zeroF D F).left ^ (k : ℤ) * h (DegPre.zeroF D F).left ^ (-(k : ℤ)) = 1
      rw [zpow_neg, mul_inv_cancel])
  obtain ⟨c, rfl⟩ : ∃ c : F, (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c = a :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 a
  have hc : c ≠ 0 := by
    rintro rfl
    let z : (TF (R := R) F).left := (⊥ : PrimeSpectrum F)
    choose I hI using fun χ : (TF (R := R) F).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
    have e := ha _ (𝟙 _) z I hI
    rw [gs_eq _ z ⊤ trivial, map_zero] at e
    exact (val w (𝟙 _) z I).ne_zero (e.trans ((congrArg _ (map_zero _)).trans (map_zero _)))
  refine ⟨Units.mk0 c hc, fun Z r z J hJ => ?_⟩
  have e := ha Z r z J hJ
  rw [Category.comp_id] at e
  exact e

theorem trPt_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] : DegPre.trPt D F (DegPre.zeroF D F) = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [DVR.tr_fst, Category.id_comp]
  · refine (DVR.tr_pr D F _).trans ?_
    have : fst (TF (R := R) F) D.P.A ≫ DegPre.zeroF D F = 1 := MonObj.comp_one (M := D.P.A) _
    rw [this, _root_.mul_one, Category.id_comp]

theorem phiRaw_torus : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (g : GtPtF D F) (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))), g.b = DegPre.zeroF D F → w.IsGen → ∃ c : Fˣ, ∀ s s' : Raw D F k, PhiRaw D F k 0 g w s s' → (∀ α, (∃ j, (s α).f j ≠ 0) → ∀ z J, Good D.P.L z J → val (g.s α) (𝟙 _) z J = 1) → ∀ α j, (s' α).f j = DegPre.constBF D F c.val _ * (s α).f j := by
  intro R _ _ D F _ _ k g w hb hw
  obtain ⟨b, gs', hg, h0, hm⟩ := g
  dsimp only at hb w
  subst hb
  obtain ⟨c, hc⟩ := line_zero_const D F k w hw
  refine ⟨c, fun s s' H hs α j => ?_⟩
  obtain ⟨u, hu, vu⟩ := exists_gen D.P.isLB (φ' := DegPre.phiφ D F 0 α (DegPre.zeroF D F)) (ε' := DegPre.deltaε k)
    (fun U _ h => by
      have e₁ : padd D.P.A (DegPre.cF D F α) (DegPre.zeroF D F) = DegPre.cF D F α :=
        _root_.mul_one (DegPre.cF D F α)
      rw [DegPre.phiφ, trPt_zero, add_zero]
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 2) (U := U) _ (c := 1) (c' := 1) ?_ ?_)
        (Eq.trans ?_ (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
          (c := ∏ i, h (DegPre.famφ D F α i) ^ DegPre.famε k i) rfl
          (DVR.prod_neg _ _ (c := ∏ i, h (DegPre.famφ D F α i) ^ DegPre.famε k i) ?_)).symm)
      · simp [Fin.prod_univ_four, DegPre.gtφ, DegPre.gtε, e₁]
      · simp [Fin.prod_univ_two, DegPre.lineφ, DegPre.lineε]
      · simp
      · simp)
    (LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (gs' α) w) (fst (TF (R := R) F) D.P.A).left)
    (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (hg α) hw) _)
  have z₁ : (DegPre.zF D F).left ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _ :=
    congrArg (fun q => q.left) (lift_fst (𝟙 (TF (R := R) F)) (toUnit _ ≫ η[D.P.A]))
  have rel := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (H α u hu (corr_of_val D.P.isLB fun y J hJ => by
    rw [val_pull hJ, vu _ _ y J hJ, val_pull hJ, Category.id_comp, z₁]))
  have key : ∀ y J, Good D.P.L y J → sval (s' α) (𝟙 _) y J = sval (s α) (𝟙 _) y J *
      ((val (gs' α) (fst (TF (R := R) F) D.P.A).left y J).val *
        gs (fst (TF (R := R) F) D.P.A).left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c.val)) := by
    intro y J hJ
    have e := rel _ (𝟙 _) y J hJ
    rw [vu _ _ y J hJ, val_pull hJ, val_mul hJ, Category.id_comp, Category.id_comp, Units.val_mul, hc _ _ y J hJ] at e
    dsimp only at e
    rw [trPt_zero, add_zero] at e
    exact e
  refine fn_ext fun y hy => ?_
  choose I hI using fun χ : (DegPre.BF D F).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
  have hI' : Good D.P.L y I := hI
  have e₁ := sec_trans (s' α) (𝟙 _) y hy (hI'.mem _ (𝟙 _))
  have e₂ := sec_trans (s α) (𝟙 _) y hy (hI'.mem _ (𝟙 _))
  have e₃ : gs (𝟙 _) y _ (DegPre.constBF D F c.val _ * (s α).f j) =
      gs (𝟙 _ ≫ (fst (TF (R := R) F) D.P.A).left) y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c.val) *
        gs (𝟙 _) y (LB.wchart D.P.L (DegPre.famφ D F α) j) ((s α).f j) :=
    (gs_mul (𝟙 _) y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_res (𝟙 _) y le_top hy _).trans
      (gs_pull (𝟙 _) (fst (TF (R := R) F) D.P.A).left y ⊤ trivial _)) rfl)
  rw [Category.id_comp] at e₃
  have e₄ : sval (s α) (𝟙 _) y I * (val (gs' α) (fst (TF (R := R) F) D.P.A).left y I).val = sval (s α) (𝟙 _) y I := by
    by_cases hz : ∃ j, (s α).f j ≠ 0
    · have hcorr : LB.Gen.Corr D.P.L _ _ _ _ (gs' α) (LB.oneGen D.P.L) :=
        corr_of_val D.P.isLB fun z J hJ => (hs α hz z J hJ).trans (val_one _).symm
      rw [val_corr hI' hcorr, val_one, Units.val_one, _root_.mul_one]
    · push_neg at hz
      have : sval (s α) (𝟙 _) y I = 0 :=
        (congrArg (gs (𝟙 _) y _) (hz _)).trans ((gs_eq _ y _ (hI'.mem _ (𝟙 _)) _).trans
          ((congrArg _ (map_zero _)).trans (map_zero _)))
      rw [this, MulZeroClass.zero_mul]
  have e₅ := key y I hI'
  rw [← _root_.mul_assoc, e₄] at e₅
  refine e₁.trans (Eq.trans ?_ (e₃.trans (congrArg _ e₂)).symm)
  refine (congrArg _ e₅).trans ?_
  rw [sval]; ring

end GlobalTheory.UU
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.ConvTermFE
open ReciprocityTheory.ChartRestriction.G.DVR

theorem famFE_val (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (s : Raw D F k) (hs : DegPre.FamFE D F k s) (mu β : D.X)
    (Z : Over (Spec (CommRingCat.of R))) (r : Z ⟶ DegPre.BF D F) (z : Z.left) (J) (hJ : Good D.P.L z J) :
    sval (s (β + k • mu)) r.left z J = sval (s β) (r ≫ DegPre.trF D F mu).left z J *
      (uVal D F k β (cP D _ mu) r z J * val (DegPre.famMult D F k mu β) (r ≫ fst _ _).left z J).val := by
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D) (F := F) hG k mu β
  rw [← hv u hu hc Z r z J hJ]
  exact (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (hs mu β u hu hc) _ r.left z J hJ

theorem val_powGen {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    val (GeneratorPullback.powGen L φ ε t n) r z J = val t r z J ^ n := map_pow _ _ _

theorem units_mul {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {F : Type} [Field F]
    [Algebra (FractionRing R) F] (k l : ℕ) (mu β ga : D.X)
    (Z : Over (Spec (CommRingCat.of R))) (r : Z ⟶ DegPre.BF D F) (z : Z.left) (J) (hJ : Good D.P.L z J) :
    (uVal D F k β (cP D _ mu) r z J * val (DegPre.famMult D F k mu β) (r ≫ fst _ _).left z J) *
      (uVal D F l ga (cP D _ mu) r z J * val (DegPre.famMult D F l mu ga) (r ≫ fst _ _).left z J) *
      th D z J (cP D Z (β + k • mu)) (cP D Z (ga + l • mu)) (r ≫ DegPre.prB D F) =
    th D z J (cP D Z β) (cP D Z ga) ((r ≫ DegPre.trF D F mu) ≫ DegPre.prB D F) *
      (uVal D F (k + l) (β + ga) (cP D _ mu) r z J *
        val (DegPre.famMult D F (k + l) mu (β + ga)) (r ≫ fst _ _).left z J) := by
  have C : IsCub (th D (T := Z) z J) := isCub_cubV D.cub hJ
  have hm : r ≫ fst (TF (R := R) F) D.P.A ≫ cP D _ mu = cP D Z mu := by rw [comp_cP, comp_cP]
  have hy : (r ≫ DegPre.trF D F mu) ≫ DegPre.prB D F = (r ≫ DegPre.prB D F) * cP D Z mu := by
    rw [trF_eq, Category.assoc, tr_pr, MonObj.comp_mul, hm]
  have t := tau_mul (r ≫ fst (TF (R := R) F) D.P.A) hJ hB β ga mu
  rw [tau_symm _ hJ (β + ga), tau_symm _ hJ β, tau_symm _ hJ ga] at t
  have key := GlobalTheory.translationUnit_mul _ _ _ C k l (cP D Z β) (cP D Z ga) (cP D Z mu) (r ≫ DegPre.prB D F)
  rw [hy, uVal, uVal, uVal, hm, val_famMult _ hJ, val_famMult _ hJ, val_famMult _ hJ, cPoint_add, cPoint_add, cPoint_add,
    cPoint_nsmul, cPoint_nsmul]
  simp only [val_powGen, pow_add]
  apply Additive.ofMul.injective
  have key' := congrArg Additive.ofMul key
  have t' := congrArg Additive.ofMul t
  simp only [ofMul_mul, ofMul_inv] at key' t' ⊢
  linear_combination (norm := abel) key' - t'

theorem conv_term_fe : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k l : ℕ) (s : Raw D F k) (s' : Raw D F l), DegPre.FamFE D F k s → DegPre.FamFE D F l s' → ∀ (mu α β ga β' ga' : D.X), β + ga = α → β' = β + k • mu → ga' = ga + l • mu → ∀ u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F (k + l) α mu) (DegPre.deltaε (k + l))), u.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (DegPre.famMult D F (k + l) mu α) → ∀ (Z : Over (Spec (CommRingCat.of R))) (r : Z ⟶ DegPre.BF D F) (z : Z.left) (J), Good D.P.L z J → sval (s β') r.left z J * sval (s' ga') r.left z J * (cubV D.cub z J (toUnit Z ≫ D.c β') (toUnit Z ≫ D.c ga') (r ≫ snd _ _)).val = sval (s β) (r ≫ DegPre.trF D F mu).left z J * sval (s' ga) (r ≫ DegPre.trF D F mu).left z J * (cubV D.cub z J (toUnit Z ≫ D.c β) (toUnit Z ≫ D.c ga) ((r ≫ DegPre.trF D F mu) ≫ snd _ _)).val * (val u r.left z J).val := by
  rintro hG R _ _ D hB F _ _ k l s s' hs hs' mu _ β ga _ _ rfl rfl rfl u hu hc Z r z J hJ
  have e := congrArg Units.val (units_mul hB k l mu β ga Z r z J hJ)
  rw [famFE_val hG k s hs mu β Z r z J hJ, famFE_val hG l s' hs' mu ga Z r z J hJ,
    (gen_fe hG (k + l) mu (β + ga)).2 u hu hc Z r z J hJ]
  rw [Units.val_mul, Units.val_mul, Units.val_mul (th D z J _ _ _)] at e
  refine Eq.trans ?_ ((congrArg (sval (s β) (r ≫ DegPre.trF D F mu).left z J *
    sval (s' ga) (r ≫ DegPre.trF D F mu).left z J * ·) e).trans (_root_.mul_assoc _ _ _).symm)
  rw [_root_.mul_mul_mul_comm, _root_.mul_assoc]
  rfl

end GlobalTheory.ConvTermFE
end
