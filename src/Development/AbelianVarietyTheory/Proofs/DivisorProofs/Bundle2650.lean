module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.InvWt

theorem top_le_preimage_of_fst {S : Type} [CommRing S] {X : Scheme.{0}} (w : Sp (DualNumber S) ⟶ X) (a : Sp S ⟶ X) (U : X.Opens)
    (h : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = a) (ha : ⊤ ≤ a ⁻¹ᵁ U) : ⊤ ≤ w ⁻¹ᵁ U := by
  intro p _
  let p0 : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S (DualNumber S)) p
  have hp : (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) p0 = p := by
    apply PrimeSpectrum.ext
    ext z
    show algebraMap S (DualNumber S) (TrivSqZeroExt.fst z) ∈ p.asIdeal ↔ z ∈ p.asIdeal
    have hz : TrivSqZeroExt.inr (TrivSqZeroExt.snd z) ∈ p.asIdeal := by
      apply p.isPrime.mem_of_pow_mem 2
      rw [pow_two, TrivSqZeroExt.inr_mul_inr]
      exact p.asIdeal.zero_mem
    rw [TrivSqZeroExt.algebraMap_eq_inl]
    constructor
    · intro h1
      rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq z]
      exact p.asIdeal.add_mem h1 hz
    · intro h1
      have e : TrivSqZeroExt.inl (TrivSqZeroExt.fst z) = z - TrivSqZeroExt.inr (TrivSqZeroExt.snd z) := by
        rw [eq_sub_iff_add_eq, TrivSqZeroExt.inl_fst_add_inr_snd_eq]
      rw [e]
      exact p.asIdeal.sub_mem h1 hz
  have hm : p0 ∈ a ⁻¹ᵁ U := ha (Set.mem_univ _)
  rw [← h] at hm
  show w p ∈ U
  rw [← hp]
  exact hm

theorem map_unitOn {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Aˣ) :
    Units.map (spMap f).appTop.hom.toMonoidHom (unitOn u) = unitOn (Units.map f.toMonoidHom u) := by
  ext
  have e := congrArg (fun g => g.hom (u : A)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  exact e.symm

theorem exists_tan_over {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v : TanM (𝟙 (Sp R)) G)
    {S : Type} [CommRing S] (φ : R →+* S) :
    ∃ v' : Over.mk (spMap ((algebraMap S (DualNumber S)).comp φ)) ⟶ G,
      v'.left = spMap (dualMap φ) ≫ (tv v).left ∧
      spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v'.left = (1 : Over.mk (spMap φ) ⟶ G).left := by
  refine ⟨Over.homMk (spMap (dualMap φ) ≫ (tv v).left) ?_, rfl, ?_⟩
  · rw [Category.assoc, Over.w (tv v)]
    simp only [overAt, Over.mk_hom, Category.comp_id, spMap, ← Spec.map_comp]
    congr 1
    ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl, CommRingCat.hom_comp]
  · let ψ : Over.mk (spMap φ) ⟶ overAt (𝟙 (Sp R)) (DualNumber R) :=
      Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (dualMap φ)) (by
        simp only [overAt, Over.mk_hom, Category.comp_id, spMap, ← Spec.map_comp]
        congr 1
        ext r
        simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
    have hψ : ψ ≫ Formalism.L2.Pj.homAt (𝟙 (Sp R)) (tm ((0 : R) • LinearMap.id)) = ψ := by
      apply Over.OverMorphism.ext
      show (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (dualMap φ)) ≫ spMap _ =
        spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (dualMap φ)
      simp only [spMap, ← Spec.map_comp, Category.assoc]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro z
      simp [dualMap, CommRingCat.hom_comp, tm]
    have e := congrArg (·.left) (Formalism.L2.Pj.tan_pull (𝟙 (Sp R)) ψ hψ (tv v) (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem v))
    simpa [ψ] using e

theorem cv_pull_of_unit {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
    {oa : Q.OAct O} (Y : Ray oa) {T T' : Over (Sp R)} (k : T' ⟶ T) (x x' : T ⟶ Y.H) (u : Q.X → (Γ(T.left, ⊤))ˣ)
    (h : ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ x').s χ) (𝟙 _) y J = gm (𝟙 T.left) y ⊤ (u χ) * val ((Y.Φ _ x).s χ) (𝟙 _) y J) :
    ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ (k ≫ x')).s χ) (𝟙 _) y J =
        gm (𝟙 T'.left) y ⊤ (Units.map k.left.appTop.hom.toMonoidHom (u χ)) * val ((Y.Φ _ (k ≫ x)).s χ) (𝟙 _) y J := by
  intro χ y J hJ
  have p' := ((GlobalTheory.TorusModel.isPull_iff k _ _).1 (Y.rep.1 _ _ k x')).2 χ y J hJ
  have p := ((GlobalTheory.TorusModel.isPull_iff k _ _).1 (Y.rep.1 _ _ k x)).2 χ y J hJ
  let g : LB.Gen (LB.LinComb Q.P.L (Y := T.left) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim) :=
    ⟨fun _ => res le_top (u χ)⟩
  have hg : ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) z J', Good Q.P.L z J' → val g r z J' = gm r z ⊤ (u χ) :=
    fun Z r z J' hJ' => gm_res r z le_top (hJ'.mem PEmpty.elim r) (u χ)
  have hC := corr_of_val Q.P.isLB (t := (Y.Φ _ x').s χ) (t' := LB.mulGen Q.P.L _ _ _ _ g ((Y.Φ _ x).s χ))
    (fun y' J' hJ' => by rw [val_mul hJ', hg _ _ _ _ hJ']; exact h χ y' J' hJ')
  have e := val_corr hJ hC k.left
  rw [val_mul hJ, hg _ _ _ _ hJ] at e
  show GlobalTheory.TorusModel.cv _ χ y J = _ * GlobalTheory.TorusModel.cv _ χ y J
  rw [p', p, e]
  congr 1
  have e2 := gm_pull (𝟙 _) k.left y ⊤ trivial (u χ)
  rw [Category.id_comp] at e2
  rw [← e2]
  rfl

theorem cv_mul_of_unit {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
    {oa : Q.OAct O} (Y : Ray oa) {T : Over (Sp R)} (X X' v : T ⟶ Y.H) (hq : X' ≫ Y.q = X ≫ Y.q)
    (u : Q.X → (Γ(T.left, ⊤))ˣ)
    (h : ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ X').s χ) (𝟙 _) y J = gm (𝟙 T.left) y ⊤ (u χ) * val ((Y.Φ _ X).s χ) (𝟙 _) y J) :
    ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ (X' * v)).s χ) (𝟙 _) y J = gm (𝟙 T.left) y ⊤ (u χ) * val ((Y.Φ _ (X * v)).s χ) (𝟙 _) y J := by
  intro χ y J hJ
  have h1 := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ X v)).2 χ y J hJ
  have h2 := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ X' v)).2 χ y J hJ
  rw [Y.Φ_b, Y.Φ_b] at h1 h2
  rw [hq] at h2
  have h3 := h χ y J hJ
  apply mul_right_cancel (b := DVR.th Q y J (DVR.cP Q _ χ) (X ≫ Y.q) (v ≫ Y.q))
  show GlobalTheory.TorusModel.cv _ χ y J * _ = _ * GlobalTheory.TorusModel.cv _ χ y J * _
  rw [h2, _root_.mul_assoc, h1, ← _root_.mul_assoc]
  congr 1

theorem _root_.GlobalTheory.Heat.IsInv.isWt : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (v : TanM (𝟙 (Sp R)) Y.H) (dd : Fld Y.H.left), IsInv Y.H v dd → ∀ (α : Q.X) (V : Y.H.left.Opens) (f : Γ(Y.H.left, V)), IsWt Y α V f → IsWt Y α V (dd V f) := by
  intro R _ _ Q O _ _ _ oa Y v dd hinv α V f hf
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  let φε : R →+* DualNumber S := (algebraMap S (DualNumber S)).comp φ
  let π : Over.mk (spMap φε) ⟶ Over.mk (spMap φ) :=
    Over.homMk (spMap (algebraMap S (DualNumber S))) (by
      show spMap (algebraMap S (DualNumber S)) ≫ spMap φ = spMap φε
      simp only [spMap, φε, ← Spec.map_comp]; rfl)
  let ie : Over.mk (spMap φ) ⟶ Over.mk (spMap φε) :=
    Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by
      show spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap φε = spMap φ
      simp only [spMap, φε, ← Spec.map_comp]
      congr 1)
  obtain ⟨v'', hv₁, hv₂⟩ := exists_tan_over Y.H v φ
  have hιπ : ie ≫ π = 𝟙 _ := by
    ext1
    show spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _
    simp only [spMap, ← Spec.map_comp]
    rw [← Spec.map_id]; congr 1
  have hiev : ie ≫ v'' = 1 := by
    ext1
    exact hv₂
  have hqm : IsMonHom Y.q := Y.q_linear.isMonHom
  have hW : ∀ z : Over.mk (spMap φ) ⟶ Y.H, ie ≫ (π ≫ z * v'') = z := by
    intro z
    rw [MonObj.comp_mul, ← Category.assoc, hιπ, Category.id_comp, hiev, _root_.mul_one]
  have hWa : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (π ≫ x * v'').left = a := by
    rw [ha]; exact congrArg (·.left) (hW x)
  have hWa' : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (π ≫ x' * v'').left = a' := by
    rw [ha']; exact congrArg (·.left) (hW x')
  have htr : ∀ z : Over.mk (spMap φ) ⟶ Y.H, IsTr Y.H φ z.left v (π ≫ z * v'').left := by
    intro z
    let e : tEpsG (z.left ≫ Y.H.hom) ⟶ Over.mk (spMap φε) := Over.homMk (𝟙 _) (by
      show 𝟙 _ ≫ spMap φε = spMap (algebraMap S (DualNumber S)) ≫ z.left ≫ Y.H.hom
      rw [Over.w z]
      simp only [Over.mk_hom, Category.id_comp, spMap, φε]
      rw [← Spec.map_comp]; rfl)
    refine ⟨e ≫ π ≫ z, e ≫ v'', ?_, ?_, ?_⟩
    · show 𝟙 _ ≫ spMap (algebraMap S (DualNumber S)) ≫ z.left = _
      rw [Category.id_comp]
    · show 𝟙 _ ≫ v''.left = _
      rw [Category.id_comp, hv₁]
    · rw [← MonObj.comp_mul]
      show 𝟙 _ ≫ _ = _
      rw [Category.id_comp]
  let c' : Q.X → (DualNumber S)ˣ := fun χ => Units.map (algebraMap S (DualNumber S)).toMonoidHom (c χ)
  have hqW : (π ≫ x' * v'') ≫ Y.q = (π ≫ x * v'') ≫ Y.q := by
    rw [MonObj.mul_comp, MonObj.mul_comp, Category.assoc, Category.assoc, hq]
  have hcW := cv_mul_of_unit Y (π ≫ x) (π ≫ x') v'' (by rw [Category.assoc, Category.assoc, hq])
    (fun χ => Units.map π.left.appTop.hom.toMonoidHom (unitOn (c χ))) (cv_pull_of_unit Y π x x' (fun χ => unitOn (c χ)) hc)
  have key := hf (DualNumber S) φε (π ≫ x * v'') (π ≫ x' * v'') c' _ _ rfl rfl
    (top_le_preimage_of_fst _ a V hWa hV) (top_le_preimage_of_fst _ a' V hWa' hV') hqW (fun χ y J hJ => by
      rw [hcW χ y J hJ]
      congr 2
      exact map_unitOn _ _)
  have e₁ := hinv.2 S φ a (π ≫ x * v'').left V f (by rw [ha]; exact Over.w x) hV (ha ▸ htr x)
  have e₂ := hinv.2 S φ a' (π ≫ x' * v'').left V f (by rw [ha']; exact Over.w x') hV' (ha' ▸ htr x')
  rw [← e₁, ← e₂, key]
  show ((c' α : DualNumber S) * _).snd = _
  rw [TrivSqZeroExt.snd_mul]
  simp [c', TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.Heat.InvWt
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.WtAlg

theorem valR_eq' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : valR x U f = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((x.appLE U ⊤ h).hom f) := dif_pos h

theorem valR_add' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f g : Γ(X, U)) : valR x U (f + g) = valR x U f + valR x U g := by
  simp only [valR_eq' x U h, map_add (f := _)]

theorem valR_sub' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f g : Γ(X, U)) : valR x U (f - g) = valR x U f - valR x U g := by
  simp only [valR_eq' x U h, map_sub]

theorem valR_mul'' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f g : Γ(X, U)) : valR x U (f * g) = valR x U f * valR x U g := by
  simp only [valR_eq' x U h, map_mul]

theorem valR_zero' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) :
    valR x U (0 : Γ(X, U)) = 0 := by
  unfold valR; split_ifs <;> simp

theorem valR_natCast' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (m : ℕ) : valR x U (m : Γ(X, U)) = m := by
  simp only [valR_eq' x U h, map_natCast]

theorem appLE_congr_top {P P' : Scheme.{0}} (b b' : P ⟶ P') (e : b = b') (h h') :
    b.appLE ⊤ ⊤ h = b'.appLE ⊤ ⊤ h' := by
  subst e; rfl

theorem valR_constFn_congr {A B : Type} [CommRing A] [CommRing B] {X : Scheme.{0}} (x x' : Sp A ⟶ X) (p : X ⟶ Sp B)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ x' ⁻¹ᵁ U) (e : x ≫ p = x' ≫ p) (r : B) :
    valR x U (constFn p U r) = valR x' U (constFn p U r) := by
  have key : ∀ (b : Sp A ⟶ X) (hb : ⊤ ≤ b ⁻¹ᵁ U) (y : Γ(Sp B, ⊤)),
      (b.appLE U ⊤ hb).hom ((p.appLE ⊤ U (fun _ _ => trivial)).hom y) = ((b ≫ p).appLE ⊤ ⊤ (fun _ _ => trivial)).hom y := by
    intro b hb y
    rw [← Scheme.Hom.appLE_comp_appLE]; rfl
  rw [valR_eq' x U h, valR_eq' x' U h', constFn, key, key]
  have hh := appLE_congr_top (x ≫ p) (x' ≫ p) e (fun _ _ => trivial) (fun _ _ => trivial)
  rw [hh]

theorem rsT_self {X : Scheme.{0}} {O : X.Opens} (s : Γ(X, O)) : rsT s O = s := by
  simp [rsT, resG]

end GlobalTheory.Heat.WtAlg

namespace GlobalTheory.Heat.WtAlg

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} {Y : Ray oa}

theorem c_zero {S : Type} [CommRing S] {φ : R →+* S} (x x' : Over.mk (spMap φ) ⟶ Y.H) (c : Q.X → Sˣ)
    (hc : ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ x').s χ) (𝟙 _) y J = gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (c χ)) * val ((Y.Φ _ x).s χ) (𝟙 _) y J) :
    c 0 = 1 := by
  have hu : unitOn (c 0) = 1 := unit_ext fun y _ => by
    obtain ⟨J, hJ, -⟩ := exists_good Q.P.L Q.P.isLB y (K := PEmpty.{1}) PEmpty.elim PEmpty.elim
      (fun a => a.elim) (fun a => a.elim)
    have e := hc 0 y J hJ
    rw [(val_corr hJ (Y.Φ _ x').s_zero _).trans (val_one _), (val_corr hJ (Y.Φ _ x).s_zero _).trans (val_one _),
      _root_.mul_one] at e
    rw [map_one]; exact e.symm
  have := congrArg (fun u : (Γ(Sp S, ⊤))ˣ => (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom u.val) hu
  simp only [unitOn, Units.coe_map, Units.val_one, map_one] at this
  exact Units.ext ((Iso.inv_hom_id_apply _ _).symm.trans this)

theorem isWt_add {α : Q.X} {V : Y.H.left.Opens} {f g : Γ(Y.H.left, V)} (hf : IsWt Y α V f) (hg : IsWt Y α V g) :
    IsWt Y α V (f + g) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [valR_add' _ _ hV', valR_add' _ _ hV, hf S φ x x' c a a' ha ha' hV hV' hq hc,
    hg S φ x x' c a a' ha ha' hV hV' hq hc, mul_add]

theorem isWt_sub {α : Q.X} {V : Y.H.left.Opens} {f g : Γ(Y.H.left, V)} (hf : IsWt Y α V f) (hg : IsWt Y α V g) :
    IsWt Y α V (f - g) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [valR_sub' _ _ hV', valR_sub' _ _ hV, hf S φ x x' c a a' ha ha' hV hV' hq hc,
    hg S φ x x' c a a' ha ha' hV hV' hq hc, mul_sub]

theorem isWt_zero (α : Q.X) (V : Y.H.left.Opens) : IsWt Y α V 0 := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [valR_zero', valR_zero', mul_zero]

theorem isWt_sum {α : Q.X} {V : Y.H.left.Opens} {I : Type} (s : Finset I) (f : I → Γ(Y.H.left, V))
    (hf : ∀ i ∈ s, IsWt Y α V (f i)) : IsWt Y α V (∑ i ∈ s, f i) :=
  Finset.sum_induction f (IsWt Y α V) (fun _ _ => isWt_add) (isWt_zero α V) hf

theorem isRaynaudTorusWeightFunction_weightZero_mul {α : Q.X} {V : Y.H.left.Opens} {g f : Γ(Y.H.left, V)} (hg : IsWt Y 0 V g) (hf : IsWt Y α V f) :
    IsWt Y α V (g * f) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [valR_mul'' _ _ hV', valR_mul'' _ _ hV, hg S φ x x' c a a' ha ha' hV hV' hq hc,
    hf S φ x x' c a a' ha ha' hV hV' hq hc, c_zero x x' c hc, Units.val_one, _root_.one_mul]
  ring

theorem isWt_natCast (V : Y.H.left.Opens) (m : ℕ) : IsWt Y 0 V (m : Γ(Y.H.left, V)) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [valR_natCast' _ _ hV', valR_natCast' _ _ hV, c_zero x x' c hc, Units.val_one, _root_.one_mul]

theorem isWt_constFn (V : Y.H.left.Opens) (r : R) : IsWt Y 0 V (constFn Y.H.hom V r) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  subst ha ha'
  rw [valR_constFn_congr x'.left x.left Y.H.hom V hV' hV ((Over.w x').trans (Over.w x).symm) r,
    c_zero x x' c hc, Units.val_one, _root_.one_mul]

end GlobalTheory.Heat.WtAlg

namespace GlobalTheory.Heat.WtAlg

theorem op_isWt : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} (dd : Fin n → Fld Y.H.left) (D : R → R) (h : Heat Y.H Y.q.left Q.P.L dd D), (∀ a (α : Q.X) (V : Y.H.left.Opens) f, IsWt Y α V f → IsWt Y α V (dd a V f)) → IsBasic Y h → ∀ (i : h.J) (k : ℕ) (α : Q.X) (f : Γ(Y.H.left, h.W i)), IsWt Y α (h.W i) f → IsWt Y α (h.W i) (op Y.H dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) f) := by
  intro R _ _ Q O _ _ _ oa Y n dd D h hdd hB i k α f hf
  obtain ⟨⟨V, hV⟩, hp, hp', hd⟩ := hB i
  have key : ∀ g : Γ(Y.H.left, h.W i), IsWt Y α (h.W i) g → IsWt Y α (h.W i) (h.d i (h.W i) g) := by
    have := hd α V hV.ge
    rw [← hV] at this
    exact this
  have h2 : IsWt Y 0 (h.W i) (2 : Γ(Y.H.left, h.W i)) := by simpa using isWt_natCast (Y := Y) (h.W i) 2
  have hk : IsWt Y 0 (h.W i) (k : Γ(Y.H.left, h.W i)) := isWt_natCast (h.W i) k
  have hk2 : IsWt Y 0 (h.W i) ((k : Γ(Y.H.left, h.W i)) ^ 2) := by rw [sq]; exact isRaynaudTorusWeightFunction_weightZero_mul hk hk
  have hrp : IsWt Y 0 (h.W i) (rsT (h.p i) (h.W i)) := by rw [rsT_self]; exact hp
  have hrp' : IsWt Y 0 (h.W i) (rsT (h.p' i) (h.W i)) := by rw [rsT_self]; exact hp'
  unfold op
  refine isWt_add (isWt_add (isWt_sub ?_ ?_) ?_) ?_
  · exact isRaynaudTorusWeightFunction_weightZero_mul (isRaynaudTorusWeightFunction_weightZero_mul h2 hk) (key f hf)
  · exact isWt_sum _ _ fun a _ => isWt_sum _ _ fun b _ =>
      isRaynaudTorusWeightFunction_weightZero_mul (isWt_constFn _ _) (hdd _ _ _ _ (hdd _ _ _ _ hf))
  · exact isRaynaudTorusWeightFunction_weightZero_mul h2 (isWt_sum _ _ fun a _ => isRaynaudTorusWeightFunction_weightZero_mul (isWt_constFn _ _) (hdd _ _ _ _ hf))
  · exact isRaynaudTorusWeightFunction_weightZero_mul (isWt_add (isRaynaudTorusWeightFunction_weightZero_mul (isRaynaudTorusWeightFunction_weightZero_mul h2 hk2) hrp) (isRaynaudTorusWeightFunction_weightZero_mul (isRaynaudTorusWeightFunction_weightZero_mul h2 hk) hrp')) hf

end GlobalTheory.Heat.WtAlg
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatConj

section Ring

variable {A : Type} [CommRing A] (δ : A → A)
  (hadd : ∀ x y, δ (x + y) = δ x + δ y) (hmul : ∀ x y, δ (x * y) = x * δ y + y * δ x)
include hadd hmul

theorem der_natCast (k : ℕ) : δ (k : A) = 0 := by
  have h0 : δ 0 = 0 := by
    have := hadd 0 0
    simp only [add_zero] at this
    linear_combination -this
  have h1 : δ 1 = 0 := by
    have := hmul 1 1
    rw [_root_.one_mul] at this
    linear_combination -this
  induction k with
  | zero => simpa using h0
  | succ k ih => rw [Nat.cast_succ, hadd, ih, h1, add_zero]

theorem der_pow (g g' : A) (hg : g * g' = 1) (k : ℕ) : δ (g ^ k) = (k : A) * g ^ k * (δ g * g') := by
  induction k with
  | zero =>
    have := hmul 1 1
    rw [_root_.one_mul] at this
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    linear_combination -this
  | succ k ih =>
    rw [pow_succ, hmul, ih]
    push_cast
    linear_combination -(δ g * g ^ k) * hg

theorem der_pow_mul (g g' : A) (hg : g * g' = 1) (k : ℕ) (f : A) :
    δ (g ^ k * f) = g ^ k * (δ f + (k : A) * (δ g * g') * f) := by
  rw [hmul, der_pow δ hadd hmul g g' hg]
  ring

theorem der_natCast_mul (k : ℕ) (x : A) : δ ((k : A) * x) = (k : A) * δ x := by
  rw [hmul, der_natCast δ hadd hmul]
  ring

end Ring

end GlobalTheory.HeatConj

namespace GlobalTheory.HeatConj

theorem op_pow_mul : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (dd : Fin n → Fld G.left) (Θ : Matrix (Fin n) (Fin n) R), Θᵀ = Θ → ∀ (u : Fin n → R) (d : Fld G.left) (W₀ Wp Wo : G.left.Opens) (p p' : Γ(G.left, Wp)) (k : ℕ) (g g' : Γ(G.left, Wo)), g * g' = 1 → Wo ≤ W₀ → IsField W₀ d → (∀ a, IsField W₀ (dd a)) → ∀ f, op G dd Θ u d p p' k Wo (g ^ k * f) = g ^ k * (op G dd Θ u d p p' k Wo f - 2 * (k : Γ(G.left, Wo)) * ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd b Wo g * g') * dd a Wo f + ((k : Γ(G.left, Wo)) ^ 2 * (2 * (d Wo g * g') - ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd a Wo g * g') * (dd b Wo g * g')) + (k : Γ(G.left, Wo)) * (2 * ∑ a, constFn G.hom Wo (u a) * (dd a Wo g * g') - ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * dd a Wo (dd b Wo g * g'))) * f) := by
  intro R _ G _ _ n dd Θ hΘ u d W₀ Wp Wo p p' k g g' hg hWo hd hdd f
  have E3 := der_pow_mul (d Wo) (hd.1 Wo hWo) (hd.2.1 Wo hWo) g g' hg k f
  have E2 : ∀ a, dd a Wo (g ^ k * f) = g ^ k * (dd a Wo f + (k : Γ(G.left, Wo)) * (dd a Wo g * g') * f) :=
    fun a => der_pow_mul (dd a Wo) ((hdd a).1 Wo hWo) ((hdd a).2.1 Wo hWo) g g' hg k f
  have E1 : ∀ a b, dd a Wo (dd b Wo (g ^ k * f)) = g ^ k * (dd a Wo (dd b Wo f) +
      (k : Γ(G.left, Wo)) * (dd b Wo g * g') * dd a Wo f + (k : Γ(G.left, Wo)) * (dd a Wo g * g') * dd b Wo f +
      (k : Γ(G.left, Wo)) * dd a Wo (dd b Wo g * g') * f +
      (k : Γ(G.left, Wo)) ^ 2 * (dd a Wo g * g') * (dd b Wo g * g') * f) := by
    intro a b
    have ha := (hdd a).1 Wo hWo
    have hm := (hdd a).2.1 Wo hWo
    rw [E2 b, der_pow_mul (dd a Wo) ha hm g g' hg k, ha, mul_assoc (k : Γ(G.left, Wo)),
      der_natCast_mul (dd a Wo) ha hm, hm]
    ring
  have hsym : ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd a Wo g * g') * dd b Wo f =
      ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd b Wo g * g') * dd a Wo f := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have : Θ b a = Θ a b := by
      have := congrFun (congrFun hΘ a) b
      simpa [Matrix.transpose_apply] using this
    rw [this]
  have hS : ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * dd a Wo (dd b Wo (g ^ k * f)) =
      g ^ k * ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * dd a Wo (dd b Wo f) +
      ((k : Γ(G.left, Wo)) * g ^ k) * ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd b Wo g * g') * dd a Wo f +
      ((k : Γ(G.left, Wo)) * g ^ k) * ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd a Wo g * g') * dd b Wo f +
      ((k : Γ(G.left, Wo)) * g ^ k) * (∑ a, ∑ b, constFn G.hom Wo (Θ a b) * dd a Wo (dd b Wo g * g')) * f +
      ((k : Γ(G.left, Wo)) ^ 2 * g ^ k) *
        (∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd a Wo g * g') * (dd b Wo g * g')) * f := by
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [E1]
    ring
  have hU : ∑ a, constFn G.hom Wo (u a) * dd a Wo (g ^ k * f) =
      g ^ k * ∑ a, constFn G.hom Wo (u a) * dd a Wo f +
      ((k : Γ(G.left, Wo)) * g ^ k) * (∑ a, constFn G.hom Wo (u a) * (dd a Wo g * g')) * f := by
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [E2]
    ring
  unfold op
  rw [E3]
  linear_combination -hS + 2 * hU - ((k : Γ(G.left, Wo)) * g ^ k) * hsym

end GlobalTheory.HeatConj
end
end
