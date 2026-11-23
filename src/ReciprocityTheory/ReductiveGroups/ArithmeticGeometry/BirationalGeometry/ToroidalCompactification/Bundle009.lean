module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

theorem ext_of_schDom {W X Y Z : Scheme.{0}} {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (ι : W ⟶ X) [IsSchemeTheoreticallyDominant ι] (hU : ι ≫ f = ι ≫ g) : f = g := by
  have hΔ : IsClosedImmersion (pullback.diagonal s) := inferInstance
  have hi : IsClosedImmersion (pullback.snd (pullback.diagonal s) (pullback.lift f g h)) :=
    inferInstance
  have hj : (ι ≫ f) ≫ pullback.diagonal s = ι ≫ pullback.lift f g h := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
      pullback.lift_fst, pullback.lift_snd, hU]
  have hji : pullback.lift (ι ≫ f) ι hj ≫ pullback.snd (pullback.diagonal s) (pullback.lift f g h) = ι :=
    pullback.lift_snd _ _ _
  have hker : (pullback.snd (pullback.diagonal s) (pullback.lift f g h)).ker = ⊥ := by
    apply le_bot_iff.mp
    have h0 := Scheme.Hom.le_ker_comp (pullback.lift (ι ≫ f) ι hj)
      (pullback.snd (pullback.diagonal s) (pullback.lift f g h))
    rw [hji, (inferInstance : IsSchemeTheoreticallyDominant ι).1] at h0
    exact h0
  have hiso : IsIso (pullback.snd (pullback.diagonal s) (pullback.lift f g h)) :=
    IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  have hc := pullback.condition (f := pullback.diagonal s) (g := pullback.lift f g h)
  have h1 : pullback.fst (pullback.diagonal s) (pullback.lift f g h) =
      pullback.snd (pullback.diagonal s) (pullback.lift f g h) ≫ f := by
    simpa only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
      pullback.lift_fst, pullback.lift_snd] using congrArg (· ≫ pullback.fst s s) hc
  have h2 : pullback.fst (pullback.diagonal s) (pullback.lift f g h) =
      pullback.snd (pullback.diagonal s) (pullback.lift f g h) ≫ g := by
    simpa only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
      pullback.lift_fst, pullback.lift_snd] using congrArg (· ≫ pullback.snd s s) hc
  exact (cancel_epi _).mp (h1.symm.trans h2)

theorem schDom_spec_map {A B : Type} [CommRing A] [CommRing B] [IsReduced A] (φ : A →+* B)
    (hφ : Function.Injective φ) : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom φ)) := by
  haveI : IsDominant (Spec.map (CommRingCat.ofHom φ)) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (f := φ)).mpr (by
      rw [(RingHom.injective_iff_ker_eq_bot φ).mp hφ]; exact bot_le)⟩
  exact IsSchemeTheoreticallyDominant.of_isDominant _



theorem over_ext_of_points {F : Type} [Field F] [IsAlgClosed F] {K Y : Over (Spec (CommRingCat.of F))}
    [LocallyOfFiniteType K.hom] [FormallyUnramified Y.hom] [LocallyOfFiniteType Y.hom] (u v : K ⟶ Y)
    (h : ∀ p : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ K, p ≫ u = p ≫ v) : u = v := by
  have hop : IsOpenImmersion (equalizer.ι u v).left := by
    refine MorphismProperty.of_isPullback ((Limits.isPullback_equalizer_prod u v).map (Over.forget _)).flip ?_
    show IsOpenImmersion (prod.lift (𝟙 Y) (𝟙 Y)).left
    rw [← MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion _ (Over.prodLeftIsoPullback Y Y).hom]
    convert! (inferInstance : IsOpenImmersion (pullback.diagonal Y.hom))
    ext1 <;> simp [← Over.comp_left] <;> first | rw [prod.lift_fst, Over.id_left] | rw [prod.lift_snd, Over.id_left]
  have : JacobsonSpace K.left := LocallyOfFiniteType.jacobsonSpace K.hom
  have hcl : closedPoints K.left ⊆ Set.range (equalizer.ι u v).left := by
    intro x hx
    let p : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ K :=
      Over.homMk (pointOfClosedPoint K.hom x hx) (pointOfClosedPoint_comp K.hom x hx)
    let q := equalizer.lift p (h p)
    let pt : (𝟙_ (Over (Spec (CommRingCat.of F)))).left := IsLocalRing.closedPoint F
    refine ⟨q.left pt, ?_⟩
    have e : q.left ≫ (equalizer.ι u v).left = p.left := by rw [← Over.comp_left, equalizer.lift_ι]
    have e' : (q.left ≫ (equalizer.ι u v).left) pt = p.left pt := by rw [e]
    exact e'.trans (pointOfClosedPoint_apply K.hom x hx pt)
  have hsurj : Function.Surjective (equalizer.ι u v).left := by
    by_contra hns
    obtain ⟨x, hx⟩ := not_forall.1 hns
    have hC : IsClosed (Set.range (equalizer.ι u v).left)ᶜ :=
      (equalizer.ι u v).left.isOpenEmbedding.isOpen_range.isClosed_compl
    obtain ⟨y, hy1, hy2⟩ := nonempty_inter_closedPoints ⟨x, hx⟩ hC.isLocallyClosed
    exact hy1 (hcl hy2)
  have : Surjective (equalizer.ι u v).left := ⟨hsurj⟩
  have : IsIso (equalizer.ι u v).left := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨hop, this⟩
  have h0 : IsIso ((Over.forget _).map (equalizer.ι u v)) := (inferInstance : IsIso (equalizer.ι u v).left)
  have : IsIso (equalizer.ι u v) := isIso_of_reflects_iso _ (Over.forget _)
  exact (cancel_epi (equalizer.ι u v)).1 (equalizer.condition u v)


open MonObj in

theorem fix_torsion (hMul : Out.MulNSt) {F : Type} [Field F] [IsAlgClosed F] (P : Out.PolAV (Spec (CommRingCat.of F)))
    (M : ℕ) (hM1 : 1 ≤ M) (hM : (M : F) ≠ 0) (σ : P.A ⟶ P.A) [IsMonHom σ]
    (hσ : ∀ x : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ P.A, x ^ M = 1 → x ≫ σ = x)
    (T : Over (Spec (CommRingCat.of F))) (x : T ⟶ P.A) (hx : x ^ M = 1) : x ≫ σ = x := by
  obtain ⟨-, -, -, het, -⟩ := hMul _ P M hM1
  have hunit : IsUnit ((M : ℕ) : Γ(Spec (CommRingCat.of F), ⊤)) := by
    have e := (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv
    have : IsUnit (e.symm (M : F)) := (isUnit_iff_ne_zero.2 hM).map e.symm
    rwa [map_natCast] at this
  have : Etale (Out.mulA P.A M).left := het hunit
  have hpow : ∀ {Z : Over (Spec (CommRingCat.of F))} (z : Z ⟶ P.A), z ^ M = z ≫ Out.mulA P.A M := fun z =>
    (congrArg (· ^ M) (Category.comp_id z).symm).trans (MonObj.comp_pow (𝟙 P.A) M z).symm
  have hcomm : σ ≫ Out.mulA P.A M = Out.mulA P.A M ≫ σ := by
    rw [← hpow, Out.mulA, MonObj.pow_comp, Category.id_comp]
  let m := (Out.mulA P.A M).left
  let e := (η[P.A]).left
  let K : Over (Spec (CommRingCat.of F)) := Over.mk (show pullback m e ⟶ Spec (CommRingCat.of F) from pullback.snd m e)
  have hw : pullback.fst m e ≫ P.A.hom = pullback.snd m e := by
    rw [← Over.w (Out.mulA P.A M), ← Category.assoc, pullback.condition, Category.assoc, Over.w η[P.A]]
    exact Category.comp_id _
  have hσm : (pullback.fst m e ≫ σ.left) ≫ m = pullback.snd m e ≫ e := by
    have h1 : σ.left ≫ m = m ≫ σ.left := congrArg CommaMorphism.left hcomm
    have h2 : e ≫ σ.left = e := congrArg CommaMorphism.left (IsMonHom.one_hom σ)
    rw [Category.assoc, h1, ← Category.assoc, pullback.condition, Category.assoc, h2]
  let τ : K ⟶ K := Over.homMk (pullback.lift _ _ hσm) (pullback.lift_snd _ _ _)
  have hKe : Etale K.hom := by show Etale (pullback.snd m e); infer_instance
  have : LocallyOfFinitePresentation K.hom := inferInstance
  have : LocallyOfFiniteType K.hom := inferInstance
  have : FormallyUnramified K.hom := inferInstance
  have hτ : τ = 𝟙 K := by
    refine over_ext_of_points τ (𝟙 K) fun p => ?_
    rw [Category.comp_id]
    ext1
    apply pullback.hom_ext
    · show p.left ≫ pullback.lift _ _ hσm ≫ pullback.fst m e = p.left ≫ pullback.fst m e
      rw [pullback.lift_fst]
      have hp1 : p.left ≫ pullback.snd m e = 𝟙 _ := Over.w p
      let q : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ P.A := Over.homMk (p.left ≫ pullback.fst m e) (by
        rw [Category.assoc, hw, hp1]; rfl)
      have hq : q ^ M = 1 := by
        rw [hpow]
        ext1
        show (p.left ≫ pullback.fst m e) ≫ m = (toUnit _ ≫ η[P.A]).left
        rw [Category.assoc, pullback.condition, ← Category.assoc, hp1, Category.id_comp, Over.comp_left]
        have : toUnit (𝟙_ (Over (Spec (CommRingCat.of F)))) = 𝟙 _ := Subsingleton.elim _ _
        rw [this, Over.id_left, Category.id_comp]
      have := congrArg CommaMorphism.left (hσ q hq)
      rw [← Category.assoc]
      exact this
    · show p.left ≫ pullback.lift _ _ hσm ≫ pullback.snd m e = p.left ≫ pullback.snd m e
      rw [pullback.lift_snd]
  have hxm : x.left ≫ m = T.hom ≫ e := by
    have := congrArg CommaMorphism.left ((hpow x).symm.trans hx)
    exact this
  let κ : T ⟶ K := Over.homMk (pullback.lift x.left T.hom hxm) (pullback.lift_snd _ _ _)
  have hτl : pullback.lift _ _ hσm = 𝟙 _ := congrArg CommaMorphism.left hτ
  ext1
  show x.left ≫ σ.left = x.left
  have k1 : x.left = κ.left ≫ pullback.fst m e := (pullback.lift_fst _ _ _).symm
  rw [k1, Category.assoc, ← pullback.lift_fst (pullback.fst m e ≫ σ.left) (pullback.snd m e) hσm, hτl,
    Category.id_comp]

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def IsTypeFn (H : Host E) (p q : ℕ) {g : ℕ} (ty : Fin g → (E →+* ℂ)) : Prop :=
  ∀ τ : E →+* ℂ, (τ (H.rt : E) = H.rt0 → Nat.card {i // ty i = τ} = p) ∧ (τ (H.rt : E) ≠ H.rt0 → Nat.card {i // ty i = τ} = q)

def IsPeriod (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) : Prop :=
  (∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i) ∧ Function.Injective P ∧ DiscreteTopology P.range ∧
    Submodule.span ℝ (Set.range P) = ⊤ ∧
    ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
      ∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y

def IsHolTo {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}} (B : Set V) (y : V → (Sp ℂ ⟶ X)) : Prop :=
  ∀ (U : X.Opens) (f : Γ(X, U)), IsOpen {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} ∧
    DifferentiableOn ℂ (fun b => valAt' (y b) U f) {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U}

def IsHolPeriods (D : Datum H) {g m : ℕ} (ty : Fin g → (E →+* ℂ)) (B : Set (Fin m → ℂ))
    (P : (Fin m → ℂ) → (D.La →+ (Fin g → ℂ))) : Prop :=
  (∀ b ∈ B, IsPeriod D ty (P b)) ∧ ∀ x, DifferentiableOn ℂ (fun b => P b x) B

def IsDerivAt0 {g : ℕ} {X : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ X) : Prop :=
  spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 ∧
    ∀ (U : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)),
      TrivSqZeroExt.snd (show DualNumber ℂ from
        (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.appLE U ⊤ h).hom f)) =
        fderiv ℂ (fun z => valAt' (e z) U f) 0 w

def IsThetaFrame {g m : ℕ} {S : Scheme.{0}} {G : Over S} [GrpObj G] (L : RigLB G) (B : Set (Fin m → ℂ))
    (y : (Fin m → ℂ) → (Sp ℂ ⟶ S)) (e : (Fin m → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ G.left))
    (θ : (Fin m → ℂ) → (Fin g → ℂ) → ℂ) : Prop :=
  ∃ fr : L.L.ι → (Fin m → ℂ) × (Fin g → ℂ) → ℂ,
    (∀ j, DifferentiableOn ℂ (fr j) {bz | bz.1 ∈ B ∧ ⊤ ≤ e bz.1 bz.2 ⁻¹ᵁ L.L.U j}) ∧
    (∀ j b z, b ∈ B → ⊤ ≤ e b z ⁻¹ᵁ L.L.U j → fr j (b, z) ≠ 0) ∧
    (∀ j j' b z, b ∈ B → ⊤ ≤ e b z ⁻¹ᵁ (L.L.U j ⊓ L.L.U j') →
      fr j (b, z) = valAt' (e b z) (L.L.U j ⊓ L.L.U j') (L.L.g j j').val * fr j' (b, z)) ∧
    (∀ j b, b ∈ B → ⊤ ≤ e b 0 ⁻¹ᵁ L.L.U j →
      fr j (b, 0) = valAt' (y b) ((L.L.pull (eSec G)).U (fun _ => j)) (L.rig.s (fun _ => j)).val) ∧
    ∀ b ∈ B, ∃ s : (L.L.pull (pullback.fst G.hom (y b))).Sec, ∀ j z (x : Sp ℂ ⟶ pullback G.hom (y b)),
      x ≫ pullback.fst _ _ = e b z → x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ e b z ⁻¹ᵁ L.L.U j →
      valAt' x ((L.L.pull (pullback.fst G.hom (y b))).U (fun _ => j)) (s.f (fun _ => j)) = θ b z * fr j (b, z)

structure FamilyUnif {D : Datum H} {l : Level H} (Xo : Moduli D l) (σ : KA l →+* ℂ) {g : ℕ}
    (ty : Fin g → (E →+* ℂ)) where
  n : ℕ
  n_pos : 0 < n
  Di : Fin n → Datum H
  sig : ∀ i, (Di i).p = D.p ∧ (Di i).q = D.q

  t : ∀ i, D.La →ₗ[𝓞 E] (Di i).La
  t_inj : ∀ i a, (∃ b, t i a = l.M' • b) ↔ ∃ b, a = l.M' • b
  t_surj : ∀ i b, ∃ a e, b = t i a + l.M' • e
  u : ∀ i, ((Di i).La →+ (Fin g → ℂ)) → (Sp ℂ ⟶ Xo.X)
  ex : ∀ i P, (Fin g → ℂ) → (Over.mk (u i P) ⟶ Xo.univ.t.G)
  over_σ : ∀ i P, IsPeriod (Di i) ty P → u i P ≫ Xo.s = spMap σ
  ex_add : ∀ i P, IsPeriod (Di i) ty P → ∀ z w, ex i P (z + w) = ex i P z * ex i P w
  ex_onto : ∀ i P, IsPeriod (Di i) ty P → Function.Surjective (ex i P)
  ex_ker : ∀ i P, IsPeriod (Di i) ty P → ∀ z, ex i P z = 1 ↔ z ∈ P.range
  ex_lin : ∀ i P, IsPeriod (Di i) ty P → ∀ (a : 𝓞 E) z,
    ex i P (fun k => ty k (a : E) * z k) = ex i P z ≫ Xo.univ.t.act.act a
  ex_weil : ∀ i P, IsPeriod (Di i) ty P → ∀ (k : ℕ) (a b : (Di i).La) (c : ℂˣ), 0 < k →
    (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((Di i).EF a b : ℂ) / k) →
    Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (ex i P ((k : ℂ)⁻¹ • P a)) (ex i P ((k : ℂ)⁻¹ • P b)) (unitOn c)
  ex_eta : ∀ i P, IsPeriod (Di i) ty P →
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      toUnit _ ≫ Xo.univ.eta a = ex i P ((l.M : ℂ)⁻¹ • P (t i a))
  ex_etaA : ∀ i P, IsPeriod (Di i) ty P → ∀ a, toUnit _ ≫ Xo.univ.etaA a = ex i P ((l.A : ℂ)⁻¹ • P (t i a))
  onto : ∀ y : Sp ℂ ⟶ Xo.X, y ≫ Xo.s = spMap σ → ∃ i P, IsPeriod (Di i) ty P ∧ u i P = y
  disj : ∀ i j P P', IsPeriod (Di i) ty P → IsPeriod (Di j) ty P' → u i P = u j P' → i = j
  fibre : ∀ i P P', IsPeriod (Di i) ty P → IsPeriod (Di i) ty P' → (u i P = u i P' ↔
    ∃ (gam : (Di i).La ≃ₗ[𝓞 E] (Di i).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ a b, (Di i).EF (gam a) (gam b) = (Di i).EF a b) ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (Di i).La), ∃ e, gam a = a + l.M • e) ∧
      (∀ a, ∃ e, gam a = a + l.A • e) ∧ ∀ a, P' (gam a) = h (P a))

  hol : ∀ i (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((Di i).La →+ (Fin g → ℂ))), IsOpen B →
    IsHolPeriods (Di i) ty B P →
    IsHolTo B (fun b => u i (P b)) ∧
      IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (ex i (P bz.1) bz.2).left)

  ex_diff : ∀ i P, IsPeriod (Di i) ty P →
    (∀ w, ∃! v : epsPt (u i P) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (ex i P z).left) w v.left) ∧
    ∀ v : epsPt (u i P) ⟶ Xo.univ.t.G,
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (ex i P 0).left →
      ∃! w, IsDerivAt0 (fun z => (ex i P z).left) w v.left

  theta : ∀ i (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((Di i).La →+ (Fin g → ℂ)))
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (Di i).La) (sgn : ℤˣ) (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ),
    IsOpen B → IsPreconnected B → IsHolPeriods (Di i) ty B P →
    (∀ a b, (Di i).EF (bas a) (bas b) = sgn * omegaStd a b) →
    (∀ b ∈ B, ((τ b).map Complex.im).PosDef ∧ ∀ k,
      (h b).mulVec (P b (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧
      (h b).mulVec (P b (bas (Pi.single (.inr k) 1))) = (τ b).mulVec (Pi.single k 1)) →
    ∃ c₁ c₂ : Fin g → ℂ, (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) ∧ (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) ∧
      IsThetaFrame Xo.univ.t.PP B (fun b => u i (P b)) (fun b z => (ex i (P b) z).left)
        (fun b z => thetaChar (τ b) c₁ c₂ ((h b).mulVec z))

  lift : ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)), IsOpen B →
    (∀ b ∈ B, y b ≫ Xo.s = spMap σ) → IsHolTo B y → ∀ b₀ ∈ B,
    ∃ (B' : Set (Fin m → ℂ)) (i : Fin n) (P : (Fin m → ℂ) → ((Di i).La →+ (Fin g → ℂ))),
      IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ IsHolPeriods (Di i) ty B' P ∧ ∀ b ∈ B', u i (P b) = y b

def N1c : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 →
    IsTypeFn H D.p D.q ty → Nonempty (FamilyUnif Xo σ ty)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi

variable {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}
variable {K : Type} [Fintype K] {Y Y' : Scheme.{0}} {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X')} {ε : K → ℤ}

theorem gm_gen_change {Z : Scheme.{0}} (hL : L.IsLB) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (r : Z ⟶ Y) (z : Z)
    (p p' : K → L.ι) (hp : ∀ k, φ k (r z) ∈ L.U (p k)) (hp' : ∀ k, φ k (r z) ∈ L.U (p' k)) :
    gm r z (LB.wchart L φ p) (t.s p) =
      (∏ k, gm (r ≫ φ k) z (L.U (p k) ⊓ L.U (p' k)) (L.g (p k) (p' k)) ^ ε k) * gm r z (LB.wchart L φ p') (t.s p') := by
  have m : r z ∈ (LB.LinComb L φ ε).U p ⊓ (LB.LinComb L φ ε).U p' :=
    ⟨Set.mem_iInter.2 fun k => hp k, Set.mem_iInter.2 fun k => hp' k⟩
  have e := congrArg (gm r z _) (ht p p')
  rw [gm_res r z _ m, map_mul, gm_res r z _ m] at e
  refine e.trans ?_
  congr 1
  show gm r z _ (∏ k, (res _ (pullU (φ k) _ (L.g (p k) (p' k)))) ^ ε k) = _
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow]
  exact congrArg (· ^ ε k) ((gm_res r z _ m _).trans (gm_pull r (φ k) z (L.U (p k) ⊓ L.U (p' k)) ⟨hp k, hp' k⟩ _))

theorem exists_defect (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (hw : PGen w)
    (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (h : Y' ⟶ Y)
    (hc : ∀ k, φ' k ≫ F = h ≫ φ k) :
    ∃ u : Γ(Y', ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
      (∀ k, F (φ' k (r z)) ∈ L.U (p k)) → (∀ k, φ' k (r z) ∈ L'.U (q k)) →
      gm (r ≫ h) z (LB.wchart L φ p) (t.s p) =
        gm r z ⊤ u * ((∏ k, gw w (r ≫ φ' k) z (p k) (q k) ^ ε k) * gm r z (LB.wchart L' φ' q) (a.s q)) := by
  classical
  have pt : ∀ k y, F (φ' k y) = φ k (h y) := fun k y => congrArg (fun g => g y) (hc k)
  let O : (K → L.ι) × (K → L'.ι) → Y'.Opens := fun pq => h ⁻¹ᵁ (LB.wchart L φ pq.1) ⊓ LB.wchart L' φ' pq.2
  have memO : ∀ pq x, x ∈ O pq ↔ (∀ k, φ k (h x) ∈ L.U (pq.1 k)) ∧ (∀ k, φ' k x ∈ L'.U (pq.2 k)) := fun pq x =>
    ⟨fun hx => ⟨fun k => Set.mem_iInter.1 hx.1 k, fun k => Set.mem_iInter.1 hx.2 k⟩,
      fun hx => ⟨Set.mem_iInter.2 hx.1, Set.mem_iInter.2 hx.2⟩⟩
  have l1 : ∀ pq k, O pq ≤ φ' k ⁻¹ᵁ ((L.pull F).U (fun _ => pq.1 k) ⊓ L'.U (pq.2 k)) := fun pq k x hx =>
    ⟨Set.mem_iInter.2 fun _ => show F (φ' k x) ∈ L.U (pq.1 k) by rw [pt k x]; exact ((memO pq x).1 hx).1 k,
      ((memO pq x).1 hx).2 k⟩
  have l2 : ∀ pq, O pq ≤ h ⁻¹ᵁ (LB.wchart L φ pq.1) := fun _ => inf_le_left
  have l3 : ∀ pq, O pq ≤ LB.wchart L' φ' pq.2 := fun _ => inf_le_right
  let v : ∀ pq, Γ(Y', O pq)ˣ := fun pq =>
    res (l2 pq) (pullU h _ (t.s pq.1)) *
      ((∏ k, (res (l1 pq k) (pullU (φ' k) _ (w.s (fun _ => pq.1 k, pq.2 k)))) ^ ε k) * res (l3 pq) (a.s pq.2))⁻¹
  have gv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (pq : (K → L.ι) × (K → L'.ι)), r z ∈ O pq →
      gm r z (O pq) (v pq) = gm (r ≫ h) z (LB.wchart L φ pq.1) (t.s pq.1) *
        ((∏ k, gw w (r ≫ φ' k) z (pq.1 k) (pq.2 k) ^ ε k) * gm r z (LB.wchart L' φ' pq.2) (a.s pq.2))⁻¹ := by
    intro Z r z pq hz
    show gm r z (O pq) (res _ _ * ((∏ k, (res _ _) ^ ε k) * res _ _)⁻¹) = _
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res r z _ hz _).trans (gm_pull r h z _ (l2 pq hz) _)) ?_)
    refine (map_inv _ _).trans (congrArg (·⁻¹) ?_)
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (gm_res r z _ hz _))
    refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => ?_)
    exact (map_zpow _ _ _).trans (congrArg (· ^ ε k) ((gm_res r z _ hz _).trans (gm_pull r (φ' k) z _ (l1 pq k hz) _)))
  obtain ⟨s, hs⟩ := glue_unit ⊤ O (fun _ => le_top) (fun x _ => by
      choose p hp using fun k => exists_chart hL (φ k (h x))
      choose q hq using fun k => exists_chart hL' (φ' k x)
      exact Opens.mem_iSup.2 ⟨(p, q), (memO (p, q) x).2 ⟨hp, hq⟩⟩) v (fun pq pq' x hx => by
      rw [gv Y' (𝟙 Y') x pq hx.1, gv Y' (𝟙 Y') x pq' hx.2]
      have m := (memO pq x).1 hx.1
      have m' := (memO pq' x).1 hx.2
      rw [gm_gen_change hL t ht (𝟙 Y' ≫ h) x pq.1 pq'.1 m.1 m'.1,
        gm_gen_change hL' a ha (𝟙 Y') x pq.2 pq'.2 m.2 m'.2]
      have hW : ∀ k, gw w (𝟙 Y' ≫ φ' k) x (pq.1 k) (pq.2 k) =
          gm ((𝟙 Y' ≫ h) ≫ φ k) x _ (L.g (pq.1 k) (pq'.1 k)) *
            (gm (𝟙 Y' ≫ φ' k) x _ (L'.g (pq.2 k) (pq'.2 k)))⁻¹ * gw w (𝟙 Y' ≫ φ' k) x (pq'.1 k) (pq'.2 k) := by
        intro k
        have e := hw Y' (𝟙 Y' ≫ φ' k) x (pq.1 k) (pq'.1 k) (pq.2 k) (pq'.2 k)
          (by show F (φ' k x) ∈ _; rw [pt]; exact m.1 k) (by show F (φ' k x) ∈ _; rw [pt]; exact m'.1 k)
          (m.2 k) (m'.2 k)
        rw [e, Category.assoc, Category.assoc, hc k]
      simp only [hW]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_prod, ofMul_zpow, inv_zpow', Finset.sum_add_distrib,
        smul_add, smul_neg, Finset.sum_neg_distrib, smul_eq_mul, neg_one_mul, neg_smul]
      abel)
  refine ⟨s, fun Z r z p q hp hq => ?_⟩
  have hz : r z ∈ O (p, q) := (memO (p, q) (r z)).2 ⟨fun k => by rw [← pt]; exact hp k, hq⟩
  have e := gv Z r z (p, q) hz
  rw [← hs (p, q), gm_res r z _ hz] at e
  rw [e, inv_mul_cancel_right]

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj

section Transport

variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

def scaleGen {M : LB X} (t : LB.Gen M) (c : Γ(X, ⊤)ˣ) : LB.Gen M := ⟨fun i => res le_top c * t.s i⟩

theorem gm_scaleGen {M : LB X} (t : LB.Gen M) (c : Γ(X, ⊤)ˣ) (r : Z ⟶ X) (z : Z) (i : M.ι) (h : r z ∈ M.U i) :
    gm r z (M.U i) ((scaleGen t c).s i) = gm r z ⊤ c * gm r z (M.U i) (t.s i) := by
  have hT : r z ∈ (⊤ : X.Opens) := trivial
  have e : X.presheaf.map (homOfLE (le_top : M.U i ≤ ⊤)).op ≫ r.app (M.U i) ≫
      Z.presheaf.germ (r ⁻¹ᵁ M.U i) z h = r.app ⊤ ≫ Z.presheaf.germ (r ⁻¹ᵁ ⊤) z hT := by
    first
      | (rw [Scheme.Hom.naturality_assoc]; congr 1; exact TopCat.Presheaf.germ_res _ _ _ _)
      | (simp only [Scheme.Hom.naturality_assoc]; congr 1; exact TopCat.Presheaf.germ_res _ _ _ _)
      | (simp [Scheme.Hom.naturality_assoc]; congr 1; exact TopCat.Presheaf.germ_res _ _ _ _)
      | (simp [Scheme.Hom.naturality_assoc]; erw [TopCat.Presheaf.germ_res]; rfl)
  have key : gm r z (M.U i) (res le_top c) = gm r z ⊤ c := by
    unfold gm
    rw [dite_eq_left h, dite_eq_left hT]
    ext
    exact congrArg (fun f => f.hom (c : Γ(X, ⊤))) e
  show gm r z (M.U i) (res le_top c * t.s i) = _
  rw [map_mul, key]

theorem scaleGen_isGen {M : LB X} (hM : M.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb M φ ε))
    (ht : t.IsGen) (c : Γ(Y, ⊤)ˣ) : (scaleGen t c).IsGen := by
  have rr : ∀ {U V W : Y.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(Y, U)ˣ),
      res h2 (res h1 x) = res (h2.trans h1) x := by
    intro U V W h1 h2 x
    ext
    show (Y.presheaf.map (homOfLE h2).op).hom ((Y.presheaf.map (homOfLE h1).op).hom (x : Γ(Y, U))) =
      (Y.presheaf.map (homOfLE (h2.trans h1)).op).hom (x : Γ(Y, U))
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
    rfl
  unfold LB.Gen.IsGen
  intro i j
  show res _ (res le_top c * t.s i) = _ * res _ (res le_top c * t.s j)
  rw [map_mul, map_mul, rr, rr, ht i j]
  exact mul_left_comm _ _ _

end Transport

section Pull

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'}

end Pull

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end
