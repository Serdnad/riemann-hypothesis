module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle043
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ConstantThetaDeformationZero
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.AutUniq

theorem hom_eq_of_sval {X X' Y B : Scheme.{0}} {L : LB Y} {K : Type} [Fintype K] {φ : K → (X ⟶ Y)} {ε : K → ℤ}
    {M : ℕ} (s : Fin (M + 1) → LB.Sec (LB.LinComb L φ ε)) (f : X ⟶ B) (p q : X' ⟶ X) (hf : p ≫ f = q ≫ f)
    (hcov : ⨆ i, nonzeroLocus (s i) = ⊤) (haff : ∀ i, IsAffineOpen (nonzeroLocus (s i)))
    (r : ∀ i, Fin (M + 1) → Γ(X, nonzeroLocus (s i))) (hr : ∀ i j, AmpleSpan.IsRatio (s j) (s i) (r i j))
    (hsurj : ∀ i, Function.Surjective (MvPolynomial.eval₂Hom (f.appLE ⊤ (nonzeroLocus (s i)) le_top).hom (r i)))
    (h : ∀ z : X', ∃ J, Good L z J ∧ ∃ u : (X'.presheaf.stalk z)ˣ, ∀ j, sval (s j) q z J = u.val * sval (s j) p z J) :
    p = q := by
  have mem : ∀ (χ : X' ⟶ X) i z J, Good L z J → (χ z ∈ nonzeroLocus (s i) ↔ IsUnit (sval (s i) χ z J)) :=
    fun χ i z J hJ => AmpleSpan.mem_nonzeroLocus_iff_gs (s i) χ z (hJ.mem φ χ)
  have rat : ∀ (χ : X' ⟶ X) i j z J, Good L z J → χ z ∈ nonzeroLocus (s i) →
      sval (s j) χ z J = gs χ z _ (r i j) * sval (s i) χ z J :=
    fun χ i j z J hJ hz => (hr i j).gs χ z hz (hJ.mem φ χ)
  have hm : ∀ i z, p z ∈ nonzeroLocus (s i) → q z ∈ nonzeroLocus (s i) := fun i z hz => by
    obtain ⟨J, hJ, u, hu⟩ := h z
    rw [mem q i z J hJ, hu]
    exact u.isUnit.mul ((mem p i z J hJ).1 hz)
  refine MapUniq.hom_ext_of_gs (fun i => nonzeroLocus (s i)) haff hcov p q hm fun i z hz a => ?_
  have hz' := hm i z hz
  obtain ⟨J, hJ, u, hu⟩ := h z
  have hrr : ∀ j, gs p z _ (r i j) = gs q z _ (r i j) := fun j => by
    have e := rat q i j z J hJ hz'
    rw [hu, hu, rat p i j z J hJ hz, mul_left_comm] at e
    have e' := (Units.mul_right_inj _).1 ((mul_left_comm _ _ _).trans e |>.trans (mul_left_comm _ _ _))
    exact ((mem p i z J hJ).1 hz).mul_right_cancel e'
  have cst : ∀ (χ : X' ⟶ X), χ z ∈ nonzeroLocus (s i) → ∀ c : Γ(B, ⊤),
      gs χ z _ ((f.appLE ⊤ (nonzeroLocus (s i)) le_top).hom c) = gs (χ ≫ f) z ⊤ c := fun χ hχ c =>
    (gs_res χ z le_top hχ _).trans (gs_pull χ f z ⊤ trivial _)
  obtain ⟨P, rfl⟩ := hsurj i a
  induction P using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.eval₂Hom_C, cst p hz, cst q hz', hf]
  | add P Q hP hQ => rw [map_add (f := _), gs_add p z _ hz, gs_add q z _ hz', hP, hQ]
  | mul_X P j hP => rw [map_mul, MvPolynomial.eval₂Hom_X', gs_mul p z _ hz, gs_mul q z _ hz', hP, hrr]

theorem eq_of_twistPull {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    (hS : IsAffineOpen (⊤ : S.Opens)) {n : ℕ} (hV : VeryAmpleAt A L n) {T : Over S} (ψ ψ' : T ⊗ A ⟶ T ⊗ A)
    (h₁ : ψ ≫ fst _ _ = fst _ _) (h₂ : ψ' ≫ fst _ _ = fst _ _)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (ψ ≫ snd _ _).left] ![(n : ℤ), -(n : ℤ)]))
    (α' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (ψ' ≫ snd _ _).left] ![(n : ℤ), -(n : ℤ)]))
    (hα : α.IsGen) (hα' : α'.IsGen) (c : Γ(T.left, ⊤)ˣ)
    (H : ∀ t t₁ t₂ : LB.Sec (LPow A L n T), IsTwistPull A L ψ (ψ ≫ snd _ _) rfl n n α t t₁ →
      IsTwistPull A L ψ' (ψ' ≫ snd _ _) rfl n n α' t t₂ → ∀ j, t₂.f j = liftFun A _ c.val * t₁.f j) : ψ = ψ' := by
  obtain ⟨M, s, hcov, haff⟩ := hV ⊤ hS
  choose r hr hsurj using fun i => (haff i).2
  obtain ⟨i', hi⟩ : ∃ i' : A.left ⟶ (A.hom ⁻¹ᵁ ⊤).toScheme, i' ≫ (A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨A.left.topIso.inv, A.left.topIso.inv_hom_id⟩
  have sec : ∀ j, ∃ v : LB.Sec (LPow A L n T), ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J),
      Good L z J → VVRank.sv A v r z J =
        sval (L := L) (φ := fun _ : Fin n => (A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) (s j)
          (r ≫ (snd T A).left ≫ i') z J := fun j => by
    obtain ⟨s', hs'⟩ := exists_sec hL (φ := fun _ : Fin n => (snd T A).left) (ε := fun _ => 1)
      (φ' := fun _ : Fin 1 => (snd T A).left) (ε' := fun _ => (n : ℤ))
      (fun U _ f => by
        simp only [zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one, zpow_natCast])
      (VVRank.pullTo (L := L) (φ := fun _ : Fin n => (A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) (s j)
        ((snd T A).left ≫ i') (fun _ => by rw [Category.assoc, hi, Category.comp_id]))
    exact ⟨s', fun Z r z J hJ => (hs' Z r z J hJ).trans (VVRank.sval_pullTo _ _ _ r z hJ)⟩
  choose v hv using sec
  have key : ψ.left ≫ (snd T A).left ≫ i' = ψ'.left ≫ (snd T A).left ≫ i' := by
    refine hom_eq_of_sval (L := L) (φ := fun _ : Fin n => (A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) s (A.hom ∣_ ⊤) _ _ ?_
      hcov (fun i => (haff i).1) r hr hsurj fun y => ?_
    · rw [← cancel_mono (⊤ : S.Opens).ι]
      simp only [Category.assoc, morphismRestrict_ι, reassoc_of% hi, Over.w]
    · choose J hJ using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hL (χ y)
      refine ⟨J, hJ, (val α' (𝟙 _) y J)⁻¹ * gm (𝟙 _ ≫ (fst T A).left) y ⊤ c * val α (𝟙 _) y J, fun j => ?_⟩
      obtain ⟨t₁, ht₁⟩ := VVRank.exists_isTwistPull A (hm := rfl) hL hα (v j)
      obtain ⟨t₂, ht₂⟩ := VVRank.exists_isTwistPull A (hm := rfl) hL hα' (v j)
      have e₁ := VVRank.sv_of_isTwistPull A ht₁ (𝟙 _) y hJ
      have e₂ := VVRank.sv_of_isTwistPull A ht₂ (𝟙 _) y hJ
      have hy := Good.mem hJ (fun _ : Fin 1 => (snd T A).left) (𝟙 (T ⊗ A).left)
      have e₃ : VVRank.sv A t₂ (𝟙 _) y J =
          (gm (𝟙 _ ≫ (fst T A).left) y ⊤ c).val * VVRank.sv A t₁ (𝟙 _) y J :=
        (congrArg (gs (𝟙 _) y _) (H _ _ _ ht₁ ht₂ _)).trans ((gs_mul _ y _ hy _ _).trans
          (congrArg (· * _) ((gs_res _ y le_top hy _).trans ((gs_pull _ _ y ⊤ trivial _).trans
            (gs_unit _ y ⊤ trivial c)))))
      rw [hv _ _ _ _ _ hJ, Category.id_comp] at e₁ e₂
      rw [Units.val_mul, Units.val_mul, _root_.mul_assoc, _root_.mul_assoc, ← e₁, ← e₃, e₂, Units.inv_mul_cancel_left]
  refine CartesianMonoidalCategory.hom_ext _ _ (h₁.trans h₂.symm) (Over.OverMorphism.ext ?_)
  have := congrArg (fun q => q ≫ (A.hom ⁻¹ᵁ ⊤).ι) key
  simpa only [Category.assoc, hi, Category.comp_id, Over.comp_left] using this

theorem endo_eq_of_sections : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ), 4 ≤ N → ∀ (ψ ψ' : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)), ψ ≫ fst _ _ = fst _ _ → ψ' ≫ fst _ _ = fst _ _ → ∀ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, (ψ ≫ snd _ _).left] ![(N : ℤ), -(N : ℤ)])) (α' : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, (ψ' ≫ snd _ _).left] ![(N : ℤ), -(N : ℤ)])), α.IsGen → α'.IsGen → ∀ c : Γ((TFK (R := R) F).left, ⊤)ˣ, (∀ t t₁ t₂ : SecA A F N, IsTwistPull A.A A.L ψ (ψ ≫ snd _ _) rfl N N α t t₁ → IsTwistPull A.A A.L ψ' (ψ' ≫ snd _ _) rfl N N α' t t₂ → ∀ j, t₂.f j = liftFun A.A _ c.val * t₁.f j) → ψ = ψ' := by
  intro hL R _ _ A F _ _ N hN ψ ψ' h₁ h₂ α α' hα hα' c H
  exact eq_of_twistPull A.isLB (isAffineOpen_top _) (hL.1.ample _ A N hN).2 ψ ψ' h₁ h₂ α α' hα hα' c H

end GlobalTheory.AutUniq
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ProjBaseChange

open MvPolynomial

variable {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

theorem appLE_cst (φ : X' ⟶ X) (f : X ⟶ Spec (CommRingCat.of R)) {U : X.Opens} {V : X'.Opens} (h : V ≤ φ ⁻¹ᵁ U) :
    (φ.appLE U V h).hom.comp (cst f U) = cst (φ ≫ f) V := by
  have e : X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ φ.appLE U V h =
      φ.appTop ≫ X'.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op := by
    rw [Scheme.Hom.map_appLE]
    rfl
  ext a
  exact congrArg (fun q => q.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))) e

theorem cst_comp (f' : X' ⟶ Spec (CommRingCat.of R')) (g : R →+* R') (V : X'.Opens) :
    cst (f' ≫ Spec.map (CommRingCat.ofHom g)) V = (cst f' V).comp g := by
  ext a
  have e := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  exact congrArg (fun q => rs X' (le_top : V ≤ ⊤) (f'.appTop.hom q)) e.symm

theorem gs_appLE (φ : X' ⟶ X) {U : X.Opens} {V : X'.Opens} (h : V ≤ φ ⁻¹ᵁ U) (z : X') (hz : z ∈ V) (a : Γ(X, U)) :
    gs (𝟙 X') z V ((φ.appLE U V h).hom a) = gs φ z U a :=
  (gs_res (𝟙 X') z h hz ((φ.app U).hom a)).trans ((gs_pull (𝟙 X') φ z U (h hz) a).trans (by rw [Category.id_comp]))

theorem isClosedImmersion_of_charts (φ : X' ⟶ X) {J : Type} (U : J → X.Opens) (hc : ⨆ i, U i = ⊤)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ i, IsAffineOpen (φ ⁻¹ᵁ U i))
    (hs : ∀ i, Function.Surjective (φ.app (U i)).hom) : IsClosedImmersion φ := by
  refine @HasAffineProperty.of_iSup_eq_top _ _ IsClosedImmersion.hasAffineProperty _ _ _ _
    (fun i => ⟨U i, hU i⟩) hc fun i => ⟨hV i, ?_⟩
  have key : ∀ (A : X.Opens) (B : X'.Opens) (h : B ≤ φ ⁻¹ᵁ A), A = U i → B = φ ⁻¹ᵁ U i →
      Function.Surjective (φ.appLE A B h).hom := by
    rintro _ _ h rfl rfl
    rw [Scheme.Hom.appLE_eq_app]
    exact hs i
  show Function.Surjective ((φ ∣_ U i).app ⊤).hom
  rw [morphismRestrict_app']
  exact key _ _ _ (by simp) (by simp)

theorem isPullback_of_charts (g : R →+* R') (hg : Function.Surjective g) (φ : X' ⟶ X)
    (f : X ⟶ Spec (CommRingCat.of R)) (f' : X' ⟶ Spec (CommRingCat.of R'))
    (hw : φ ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g)) {J : Type} (U : J → X.Opens) (V : J → X'.Opens)
    (hUV : ∀ i, V i = φ ⁻¹ᵁ U i) (hc : ⨆ i, U i = ⊤) (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ i, IsAffineOpen (V i))
    (hs : ∀ i, Function.Surjective (φ.appLE (U i) (V i) (hUV i).le).hom)
    (hk : ∀ i a, (φ.appLE (U i) (V i) (hUV i).le).hom a = 0 → ∀ (B : Type) [CommRing B] (θ : Γ(X, U i) →+* B)
      (c : R' →+* B), θ.comp (cst f (U i)) = c.comp g → θ a = 0) :
    IsPullback φ f' f (Spec.map (CommRingCat.ofHom g)) := by
  obtain rfl : V = fun i => φ ⁻¹ᵁ U i := funext hUV
  simp only [Scheme.Hom.appLE_eq_app] at hs hk
  have := isClosedImmersion_of_charts φ U hc hU hV hs
  have := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom g) hg
  have hle : φ.ker ≤ (pullback.fst f (Spec.map (CommRingCat.ofHom g))).ker := by
    refine Scheme.IdealSheafData.le_of_iSup_eq_top (fun i => ⟨U i, hU i⟩) hc fun i a ha => ?_
    rw [Scheme.Hom.ker_apply] at ha ⊢
    refine hk i a ha _ _ (cst (pullback.snd f (Spec.map (CommRingCat.ofHom g))) _) ?_
    rw [← cst_comp, ← pullback.condition, ← appLE_cst _ f le_rfl, Scheme.Hom.appLE_eq_app]
  have hl := IsClosedImmersion.lift_fac φ _ hle
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk _
    (fun t => pullback.lift t.fst t.snd t.condition ≫ IsClosedImmersion.lift φ _ hle) (fun t => ?_) (fun t => ?_)
    (fun t m h₁ _ => ?_)⟩⟩
  · rw [Category.assoc, hl, pullback.lift_fst]
  · rw [← cancel_mono (Spec.map (CommRingCat.ofHom g)), Category.assoc, ← hw, ← Category.assoc, Category.assoc _ _ φ,
      hl, pullback.lift_fst, t.condition]
  · rw [← cancel_mono φ, Category.assoc, hl, pullback.lift_fst, h₁]

theorem eventually_exists_form (f : X ⟶ Spec (CommRingCat.of R)) {H : LB X} {m : ℕ} {s : Fin (m + 1) → H.Sec}
    (hc : ⨆ i, nonzeroLocus (s i) = ⊤) (ha : ∀ i, IsAffineOpen (nonzeroLocus (s i)))
    (r : ∀ i, Fin (m + 1) → Γ(X, nonzeroLocus (s i))) (hr' : ∀ i, IsRatioFamily s i (r i)) (i : Fin (m + 1))
    (p : MvPolynomial (Fin (m + 1)) R) (hp : eval₂Hom (cst f _) (r i) p = 0) :
    ∀ᶠ d in Filter.atTop, ∃ F ∈ vanishingForms f s d, MvPolynomial.X i - 1 ∣ F - p := by
  obtain ⟨e, F, hF, hFp⟩ := (ThetaDeform.exists_homogeneous i p).exists
  have hFi : eval₂Hom (cst f _) (r i) F = 0 := by
    obtain ⟨G, hG⟩ := hFp
    rw [eq_add_of_sub_eq hG, map_add (f := _), hp, map_mul, map_sub, map_one, eval₂Hom_X', (hr' i).self_eq_one]
    simp
  have hn : ∀ j, ∃ n, r j i ^ n * eval₂Hom (cst f _) (r j) F = 0 := fun j => by
    refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X (ha j) _ _ (fn_ext fun y hy => ?_)
    have hj : y ∈ nonzeroLocus (s j) := X.basicOpen_le _ hy
    obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus hj
    have uj := (mem_nonzeroLocus_iff_isUnit _ hk).1 hj
    have hi : y ∈ nonzeroLocus (s i) := by
      rw [mem_nonzeroLocus_iff_isUnit _ hk, (hr' j).gs_eq hj hk i]
      exact ((LBGerm.isUnit_gs_iff (𝟙 X) y _ hj _).2 hy).mul uj
    have e₁ := ((hr' j).gs_form f hj hk hF).symm.trans ((hr' i).gs_form f hi hk hF)
    rw [hFi, LBGerm.gs_zero _ y _ hi, mul_zero] at e₁
    rw [LBGerm.gs_zero _ y _ hy]
    exact (gs_res _ y (X.basicOpen_le _) hy _).trans ((uj.pow e).mul_right_eq_zero.1 e₁)
  choose n hn using hn
  filter_upwards [Filter.eventually_ge_atTop (Finset.univ.sup n + e)] with d hd
  obtain ⟨c, rfl⟩ : ∃ c, d = c + e := ⟨d - e, by omega⟩
  refine ⟨MvPolynomial.X i ^ c * F, ?_, ?_⟩
  · refine mem_vanishingForms_of_ratios f hc r hr' ((isHomogeneous_X_pow i c).mul hF) fun j => ?_
    have hle : n j ≤ c := (Finset.le_sup (Finset.mem_univ j)).trans (by omega)
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le' hle
    rw [map_mul, map_pow, eval₂Hom_X', pow_add, _root_.mul_assoc, hn j, mul_zero]
  · have : MvPolynomial.X i ^ c * F - p = (MvPolynomial.X i ^ c - 1) * F + (F - p) := by ring
    rw [this]
    exact ((sub_one_dvd_pow_sub_one _ c).mul_right _).add hFp

theorem isPullback_of_equations_lift : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (R' : Type) [CommRing R'] (g : R →+* R'), Function.Surjective g → ∀ (X' : Scheme.{0}) (f' : X' ⟶ Spec (CommRingCat.of R')) (H' : LB X') (s' : Fin (n + 1) → LB.Sec H') (φ : X' ⟶ X) (w : LB.Iso H' (H.pull φ)), H'.IsLB → VeryAmpleBy f' H' s' → φ ≫ f = f' ≫ (Spec.map (CommRingCat.ofHom g)) → w.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) → ∀ t₀ : ℕ, (∀ t, t₀ ≤ t → ∀ F : MvPolynomial (Fin (n + 1)) R, F.IsHomogeneous t → (∀ k : (H').ι, MvPolynomial.eval₂Hom (cst (f' ≫ (Spec.map (CommRingCat.ofHom g))) ((H').U k)) (fun j => (s' j).f k) (F) = 0) → ∃ F₁ : MvPolynomial (Fin (n + 1)) R, F₁.IsHomogeneous t ∧ (∀ k : (H).ι, MvPolynomial.eval₂Hom (cst (f) ((H).U k)) (fun j => (s j).f k) (F₁) = 0) ∧ MvPolynomial.map g F₁ = MvPolynomial.map g F) → IsPullback φ f' f (Spec.map (CommRingCat.ofHom g)) := by
  intro R _ X f H n s hH ⟨hc, hs⟩ R' _ g hg X' f' H' s' φ w hH' ⟨hc', hs'⟩ hw _ hrel t₀ hlift
  choose ha r hr hsur using hs
  choose ha' r' hr' hsur' using hs'
  have hR : ∀ i, IsRatioFamily s i (r i) := hr
  have hR' : ∀ i, IsRatioFamily s' i (r' i) := hr'
  have unit : ∀ i z k, φ z ∈ H.U k → (φ z ∈ nonzeroLocus (s i) ↔ IsUnit (gs φ z _ ((s i).f k))) := fun i z k hk =>
    ((mem_nonzeroLocus_iff_isUnit _ hk).trans (LBGerm.isUnit_gs_iff (𝟙 X) _ _ hk _)).trans
      (LBGerm.isUnit_gs_iff φ z _ hk _).symm
  have hUV : ∀ i, nonzeroLocus (s' i) = φ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by
    ext z
    obtain ⟨k, hk⟩ := exists_chart hH (φ z)
    obtain ⟨k', hk'⟩ := exists_chart hH' z
    refine (mem_nonzeroLocus_iff_isUnit _ hk').trans (Iff.trans ?_ (unit i z k hk).symm)
    rw [hrel i z k k' hk hk', Units.isUnit_units_mul]
  have hrr : ∀ i j, (φ.appLE _ _ (hUV i).le).hom (r i j) = r' i j := fun i j => fn_ext fun z hz => by
    obtain ⟨k, hk⟩ := exists_chart hH (φ z)
    obtain ⟨k', hk'⟩ := exists_chart hH' z
    have hz₁ : φ z ∈ nonzeroLocus (s i) := (hUV i).le hz
    have h : φ z ∈ nonzeroLocus (s i) ⊓ H.U k := ⟨hz₁, hk⟩
    have e := congrArg (gs φ z _) (hr i j k)
    rw [gs_res _ z _ h, gs_mul _ z _ h, gs_res _ z _ h, gs_res _ z _ h] at e
    rw [gs_appLE φ _ z hz]
    refine ((unit i z k hk).1 hz₁).mul_right_cancel (e.symm.trans ?_)
    rw [hrel j z k k' hk hk', hrel i z k k' hk hk', (hR' i).gs_eq hz hk' j]
    ring
  have hev : ∀ i p, (φ.appLE _ _ (hUV i).le).hom (eval₂Hom (cst f _) (r i) p) =
      eval₂Hom (cst (f' ≫ Spec.map (CommRingCat.ofHom g)) _) (r' i) p := fun i p => by
    rw [map_eval₂Hom, appLE_cst, hw]
    simp only [hrr]
  refine isPullback_of_charts g hg φ f f' hw _ _ hUV hc ha ha' (fun i b => ?_) fun i a h0 B _ θ c hθ => ?_
  · obtain ⟨q, rfl⟩ := hsur' i b
    obtain ⟨p, rfl⟩ := MvPolynomial.map_surjective g hg q
    exact ⟨_, (hev i p).trans (by rw [cst_comp, eval₂Hom_map_hom])⟩
  · obtain ⟨p, rfl⟩ := hsur i a
    rw [hev] at h0
    obtain ⟨t, ht, F, hF, G, hG⟩ := ((Filter.eventually_ge_atTop t₀).and
      (eventually_exists_form _ hc' ha' r' hR' i p h0)).exists
    obtain ⟨F₁, h₁, h₂, h₃⟩ := hlift t ht F hF.1 hF.2
    have e₁ : eval₂Hom (cst f _) (r i) F₁ = 0 := (hR i).eval_eq_zero f ⟨h₁, h₂⟩
    have e₂ : eval₂Hom (cst f _) (r i) p = eval₂Hom (cst f _) (r i) F := by
      rw [eq_add_of_sub_eq hG, map_add (f := _), map_mul, map_sub, map_one, eval₂Hom_X', (hR i).self_eq_one]
      simp
    have e₃ : ∀ P, θ (eval₂Hom (cst f _) (r i) P) = eval₂Hom c (fun j => θ (r i j)) (MvPolynomial.map g P) :=
      fun P => by rw [map_eval₂Hom, hθ, eval₂Hom_map_hom]
    rw [e₂, e₃, ← h₃, ← e₃, e₁, map_zero]

end GlobalTheory.ProjBaseChange
end
