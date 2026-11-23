module

public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle013
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueTorsionPointFrobeniusLocal
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.UnifLieBasis

open TangentOrigin
open ReciprocityTheory.ChartRestriction.G.Chart (jetAug qD rD scaleD IsTan isTan_iff prodPts isLieComb_iff)

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem spMap_jetAug_surjective :
    Function.Surjective (spMap (jetAug ℂ (Fin 2) 1).toRingHom) := by
  intro q
  have : q ∈ Set.range (PrimeSpectrum.comap (jetAug ℂ (Fin 2) 1).toRingHom) := by
    rw [range_comap_of_surjective _ _ (fun a => ⟨algebraMap ℂ _ a, (jetAug ℂ (Fin 2) 1).commutes a⟩)]
    intro b hb
    refine q.2.mem_of_pow_mem (1 + 1) ?_
    have h := Ideal.pow_mem_pow (I := RingHom.ker (jetAug ℂ (Fin 2) 1)) hb (1 + 1)
    rw [Chart.ker_jetAug_pow, Ideal.mem_bot] at h
    rw [h]
    exact zero_mem _
  exact this


omit u in
theorem snd_evalPt_mul {v v' : epsR ℂ ⟶ A} (hv : IsTan (R := ℂ) (G := A) v) (hv' : IsTan (R := ℂ) (G := A) v')
    (U : A.left.Opens) (h0 : ⊤ ≤ (1 : Chart.sp (R₀ := ℂ) ℂ ⟶ A).left ⁻¹ᵁ U)
    (h : ⊤ ≤ v.left ⁻¹ᵁ U) (h' : ⊤ ≤ v'.left ⁻¹ᵁ U) (h'' : ⊤ ≤ (v * v').left ⁻¹ᵁ U) (f : Γ(A.left, U)) :
    (evalPt (R := DualNumber ℂ) (v * v').left U h'' f).snd =
      (evalPt (R := DualNumber ℂ) v.left U h f).snd + (evalPt (R := DualNumber ℂ) v'.left U h' f).snd := by
  let P : Chart.sp (R₀ := ℂ) (Chart.JetR ℂ (Fin 2) 1) ⟶ A := (Chart.spMap (qD 0) ≫ v) * (Chart.spMap (qD 1) ≫ v')
  have hP : Chart.spMap (jetAug ℂ (Fin 2) 1) ≫ P = 1 := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, Chart.spMap_comp, Chart.spMap_comp,
      Chart.jetAug_comp_qD, Chart.jetAug_comp_qD, hv, hv', _root_.mul_one]
  have hPU : ⊤ ≤ P.left ⁻¹ᵁ U := fun p _ => by
    obtain ⟨q, rfl⟩ := spMap_jetAug_surjective p
    rw [← hP] at h0
    exact h0 (Set.mem_univ q)
  have hval : ∀ l : ℂ × ℂ →ₗ[ℂ] ℂ, Chart.spMap (rD l) ≫ P =
      (Chart.spMap (scaleD (l ((1 : ℂ), (0 : ℂ)))) ≫ v) * (Chart.spMap (scaleD (l ((0 : ℂ), (1 : ℂ)))) ≫ v') := by
    intro l
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, Chart.spMap_comp, Chart.spMap_comp,
      Chart.restrictDiag_comp_incl_fst, Chart.restrictDiag_comp_incl_snd]
  have key : ∀ (l : ℂ × ℂ →ₗ[ℂ] ℂ) (w : epsR ℂ ⟶ A) (hw : ⊤ ≤ w.left ⁻¹ᵁ U), Chart.spMap (rD l) ≫ P = w →
      evalPt (R := DualNumber ℂ) w.left U hw f = rD l (evalPt (R := Chart.JetR ℂ (Fin 2) 1) P.left U hPU f) := by
    rintro l w hw rfl
    exact evalPt_spMap_comp (rD l : Chart.JetR ℂ (Fin 2) 1 →+* DualNumber ℂ) P.left U hPU hw f
  rw [key (LinearMap.fst ℂ ℂ ℂ) v h, key (LinearMap.snd ℂ ℂ ℂ) v' h',
    key (LinearMap.fst ℂ ℂ ℂ + LinearMap.snd ℂ ℂ ℂ) (v * v') h'', Chart.snd_rD_add]
  · rw [hval]
    simp only [LinearMap.add_apply, LinearMap.fst_apply, LinearMap.snd_apply, add_zero, zero_add]
    rw [Chart.scaleD_one, Chart.spMap_id, Category.id_comp, Category.id_comp]
  · rw [hval]
    simp only [LinearMap.fst_apply, LinearMap.snd_apply]
    rw [Chart.scaleD_one, Chart.spMap_id, Category.id_comp, Chart.spMap_scaleD_zero hv, _root_.one_mul]
  · rw [hval]
    simp only [LinearMap.fst_apply, LinearMap.snd_apply]
    rw [Chart.scaleD_one, Chart.spMap_id, Category.id_comp, Chart.spMap_scaleD_zero hv', _root_.mul_one]

theorem isDiff_add {w w' : Fin g → ℂ} {v v' : epsR ℂ ⟶ A} (hv : IsTan (R := ℂ) (G := A) v)
    (hv' : IsTan (R := ℂ) (G := A) v') (hd : u.IsDiff w v) (hd' : u.IsDiff w' v') : u.IsDiff (w + w') (v * v') := by
  intro U h'' f
  have ht := Chart.isTan_mul hv hv'
  have h0 := (tangent_mem_iff (u := u) ((isTan_iff _).1 ht) U).1 h''
  have h := (tangent_mem_iff (u := u) ((isTan_iff _).1 hv) U).2 h0
  have h' := (tangent_mem_iff (u := u) ((isTan_iff _).1 hv') U).2 h0
  have h1 : ⊤ ≤ (1 : Chart.sp (R₀ := ℂ) ℂ ⟶ A).left ⁻¹ᵁ U := by
    rw [← hv]
    exact fun p _ => h (Set.mem_univ _)
  rw [map_add (f := _), ← hd U h f, ← hd' U h' f]
  exact snd_evalPt_mul hv hv' U h1 h h' h'' f

theorem isDiff_smul {w : Fin g → ℂ} {v : epsR ℂ ⟶ A} (hv : IsTan (R := ℂ) (G := A) v) (hd : u.IsDiff w v) (c : ℂ) :
    u.IsDiff (c • w) (Chart.spMap (scaleD c) ≫ v) := by
  intro U h' f
  have h0 := (tangent_mem_iff (u := u) ((isTan_iff _).1 (Chart.isTan_scale c hv)) U).1 h'
  have h := (tangent_mem_iff (u := u) ((isTan_iff _).1 hv) U).2 h0
  rw [map_smul, ← hd U h f]
  refine (congrArg TrivSqZeroExt.snd
    (evalPt_spMap_comp (scaleD c : DualNumber ℂ →+* DualNumber ℂ) v.left U h h' f)).trans ?_
  exact TrivSqZeroExt.snd_map _ _

theorem isDiff_zero : u.IsDiff 0 (1 : epsR ℂ ⟶ A) := by
  intro U h f
  have ht : IsTan (R := ℂ) (G := A) (1 : epsR ℂ ⟶ A) := Chart.isTan_one
  have h1 : ⊤ ≤ (1 : Chart.sp (R₀ := ℂ) ℂ ⟶ A).left ⁻¹ᵁ U := by
    rw [← ht]
    exact fun p _ => h (Set.mem_univ _)
  have key : ∀ (w : epsR ℂ ⟶ A) (hw : ⊤ ≤ w.left ⁻¹ᵁ U), w = 1 →
      (evalPt (R := DualNumber ℂ) w.left U hw f).snd = (evalPt (R := DualNumber ℂ) (1 : epsR ℂ ⟶ A).left U h f).snd := by
    rintro w hw rfl
    rfl
  have h2 : ⊤ ≤ (1 * 1 : epsR ℂ ⟶ A).left ⁻¹ᵁ U := by rwa [_root_.mul_one]
  have := snd_evalPt_mul ht ht U h1 h h h2 f
  rw [key _ h2 (_root_.mul_one _)] at this
  rw [map_zero]
  exact left_eq_add.1 this

theorem isDiff_list_prod : ∀ {k : ℕ} (w : Fin k → Fin g → ℂ) (v : Fin k → (epsR ℂ ⟶ A)),
    (∀ i, IsTan (R := ℂ) (G := A) (v i)) → (∀ i, u.IsDiff (w i) (v i)) →
    IsTan (R := ℂ) (G := A) (List.ofFn v).prod ∧ u.IsDiff (∑ i, w i) (List.ofFn v).prod := by
  intro k
  induction k with
  | zero =>
    intro w v _ _
    simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
    exact ⟨Chart.isTan_one, isDiff_zero u⟩
  | succ k ih =>
    intro w v hv hd
    obtain ⟨h1, h2⟩ := ih (fun i => w i.succ) (fun i => v i.succ)
      (fun i => hv i.succ) (fun i => hd i.succ)
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact ⟨Chart.isTan_mul (hv 0) h1, isDiff_add u (hv 0) h1 (hd 0) h2⟩

theorem isTangent_comp (f : A ⟶ A) [IsMonHom f] {v : epsR ℂ ⟶ A} (hv : IsTangent v) : IsTangent (v ≫ f) := by
  unfold IsTangent at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, IsMonHom.one_hom]

theorem isDiff_comp (f : A ⟶ A) [IsMonHom f] (F : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ))
    (hF : ∀ z, u.ex (F z) = u.ex z ≫ f) {w : Fin g → ℂ} {v : epsR ℂ ⟶ A}
    (hv : IsTangent v) (hd : u.IsDiff w v) : u.IsDiff (F w) (v ≫ f) := by
  intro U h s
  have h1 := hd (f.left ⁻¹ᵁ U) h ((f.left.app U).hom s)
  have e : ((v ≫ f).left.appLE U ⊤ h).hom s =
      (v.left.appLE (f.left ⁻¹ᵁ U) ⊤ h).hom ((f.left.app U).hom s) := by
    have := Scheme.Hom.comp_appLE v.left f.left U ⊤ h
    exact congrArg (fun φ => φ.hom s) this
  have hdiff := differentiableAt_val u ((tangent_mem_iff (u := u) (isTangent_comp f hv) U).1 h) s
  have hfun : (fun z => valAt' (u.ex z).left (f.left ⁻¹ᵁ U) ((f.left.app U).hom s)) =
      (fun z => valAt' (u.ex z).left U s) ∘ F := by
    funext z
    rw [valAt'_comp, Function.comp_apply, hF]
    rfl
  have hch := (HasFDerivAt.comp (0 : Fin g → ℂ) (f := F)
    (by rw [map_zero]; exact hdiff.hasFDerivAt) F.hasFDerivAt).fderiv
  rw [hfun, hch] at h1
  rw [e]
  exact h1

end GlobalTheory.UnifLieBasis


open GlobalTheory.UnifLieBasis in
open ReciprocityTheory.ChartRestriction.G.Chart (IsTan isTan_iff prodPts isLieComb_iff isTan_scale) in
theorem GlobalTheory.exists_lieBasis_of_holUnif : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g), Smooth A.hom → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → ∃ v : Fin g → (epsR ℂ ⟶ A), IsLieBasis v ∧ ∀ (f : A ⟶ A) (c : Fin g → ℂ), IsMonHom f → (∀ z, u.ex (fun k => c k * z k) = u.ex z ≫ f) → ∀ i, (v i ≫ f).left = spMap (epsScale (c i)) ≫ (v i).left := by
  intro A _ L g u _ h1 h2
  choose v hv using fun i : Fin g => (h2 (Pi.single i 1)).exists
  have ht : ∀ i, IsTan (R := ℂ) (G := A) (v i) := fun i => (isTan_iff _).2 (hv i).1
  have hp : ∀ c : Fin g → ℂ, IsTangent (prodPts (R := ℂ) (G := A) c v) ∧ u.IsDiff c (prodPts (R := ℂ) (G := A) c v) := by
    intro c
    obtain ⟨a, b⟩ := isDiff_list_prod u (fun i => c i • (Pi.single i 1 : Fin g → ℂ)) _
      (fun i => isTan_scale (c i) (ht i)) (fun i => isDiff_smul u (ht i) (hv i).2 (c i))
    rw [← pi_eq_sum_univ' c] at b
    exact ⟨(isTan_iff _).1 a, b⟩
  refine ⟨v, ⟨fun i => (hv i).1, fun w hw => ?_⟩, fun f c hf hF i => ?_⟩
  · obtain ⟨c, hc, hcu⟩ := h1 w hw
    refine ⟨c, (isLieComb_iff c v w).2 ((h2 c).unique ⟨hw, hc⟩ (hp c)), fun c' hc' => hcu c' ?_⟩
    rw [(isLieComb_iff c' v w).1 hc']
    exact (hp c').2
  · let F : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) := ContinuousLinearMap.pi fun k => c k • ContinuousLinearMap.proj k
    have hd := isDiff_comp u f F hF (hv i).1 (hv i).2
    have e : F (Pi.single i 1) = c i • (Pi.single i 1 : Fin g → ℂ) := by
      funext k
      by_cases hk : k = i <;> simp [F, hk]
    rw [e] at hd
    exact congrArg CommaMorphism.left ((h2 _).unique ⟨isTangent_comp f (hv i).1, hd⟩
      ⟨(isTan_iff _).1 (isTan_scale (c i) (ht i)), isDiff_smul u (ht i) (hv i).2 (c i)⟩)
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.TameDescent

theorem specMap_fromSpec_comp_eq_iff {X : Scheme.{0}} (t : X ⟶ X) {U : X.Opens}
    (hU : IsAffineOpen U) (h : U ≤ t ⁻¹ᵁ U) {k : CommRingCat.{0}} (a : Γ(X, U) ⟶ k) :
    (Spec.map a ≫ hU.fromSpec) ≫ t = Spec.map a ≫ hU.fromSpec ↔
      ∀ b, a.hom ((t.appLE U U h).hom b - b) = 0 := by
  rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec t hU hU h, ← Category.assoc,
    cancel_mono, ← Spec.map_comp, Spec.map_injective.eq_iff]
  simp only [map_sub, sub_eq_zero]
  exact ⟨fun e b => congr(($e).hom b), fun e => CommRingCat.hom_ext (RingHom.ext e)⟩

theorem appLE_sub_mem_map {X Y : Scheme.{0}} (p : Y ⟶ X) [Flat p] (t : Y ⟶ Y) {U : X.Opens}
    {W : Y.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W) (e : W ≤ p ⁻¹ᵁ U)
    (h : W ≤ t ⁻¹ᵁ W) {k : Type} [Field k] (a : Γ(X, U) →+* k)
    (ht : pullback.fst p (Spec.map (CommRingCat.ofHom a) ≫ hU.fromSpec) ≫ t =
      pullback.fst p (Spec.map (CommRingCat.ofHom a) ≫ hU.fromSpec)) (c : Γ(Y, W)) :
    (t.appLE W W h).hom c - c ∈ (RingHom.ker a).map (p.appLE U W e).hom := by
  let := a.toAlgebra
  let := (p.appLE U W e).hom.toAlgebra
  have : Module.Flat Γ(X, U) Γ(Y, W) := p.flat_appLE hU hW e
  refine mem_map_ker_of_one_tmul_eq_zero_of_flat Γ(X, U) Γ(Y, W) k _ ?_
  let r : Γ(Y, W) ⟶ CommRingCat.of (k ⊗[Γ(X, U)] Γ(Y, W)) :=
    CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom
  let l : CommRingCat.of k ⟶ CommRingCat.of (k ⊗[Γ(X, U)] Γ(Y, W)) :=
    CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  have w : (Spec.map r ≫ hW.fromSpec) ≫ p =
      Spec.map l ≫ Spec.map (CommRingCat.ofHom a) ≫ hU.fromSpec := by
    rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec p hU hW e,
      ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    congr 2
    exact (CommRingCat.isPushout_tensorProduct Γ(X, U) k Γ(Y, W)).w.symm
  refine (specMap_fromSpec_comp_eq_iff t hW h r).1 ?_ c
  rw [← pullback.lift_fst _ _ w, Category.assoc, ht]

theorem isPullback_specMap_app {X X' : Scheme.{0}} (π : X ⟶ X') [IsAffineHom π] {V : X'.Opens}
    (hV : IsAffineOpen V) :
    IsPullback (Spec.map (π.app V)) (hV.preimage π).fromSpec hV.fromSpec π :=
  IsOpenImmersion.isPullback _ _ _ _
    (by rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec]) (by simp)

theorem isPullback_of_isPushout_app {X X' Y Y' : Scheme.{0}} (π : X ⟶ X') (φ : Y ⟶ Y')
    (p : Y ⟶ X) (p' : Y' ⟶ X') [IsAffineHom π] [IsAffineHom φ] (w : φ ≫ p' = p ≫ π)
    (H : ∀ (V : X'.Opens) (W : Y'.Opens), IsAffineOpen V → IsAffineOpen W →
      ∀ (e : W ≤ p' ⁻¹ᵁ V) (e' : φ ⁻¹ᵁ W ≤ p ⁻¹ᵁ π ⁻¹ᵁ V),
      IsPushout (p'.appLE V W e) (π.app V) (φ.app W) (p.appLE _ _ e')) :
    IsPullback φ p p' π := by
  have h : ∀ y : Y', ∃ (V : X'.Opens) (W : Y'.Opens), IsAffineOpen V ∧ IsAffineOpen W ∧
      y ∈ W ∧ W ≤ p' ⁻¹ᵁ V := fun y => by
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (p' y)) isOpen_univ
    obtain ⟨_, ⟨W, hW, rfl⟩, hy, hle⟩ := Y'.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ p' ⁻¹ᵁ V from hx) (p' ⁻¹ᵁ V).isOpen
    exact ⟨V, W, hV, hW, hy, hle⟩
  choose V W hV hW hy hle using h
  let 𝒰 : Y'.OpenCover := Scheme.Cover.mkOfCovers Y' (fun y => Spec Γ(Y', W y))
    (fun y => (hW y).fromSpec) (fun y => ⟨y, by
      have : y ∈ Set.range (hW y).fromSpec := by
        rw [IsAffineOpen.range_fromSpec]; exact hy y
      exact this⟩)
  refine Scheme.isPullback_of_openCover φ p p' π 𝒰 fun y => ?_
  have e' : φ ⁻¹ᵁ W y ≤ p ⁻¹ᵁ π ⁻¹ᵁ V y := by
    rw [← Scheme.Hom.comp_preimage, ← w, Scheme.Hom.comp_preimage]
    exact φ.preimage_mono (hle y)
  have H1 := isPullback_specMap_app φ (hW y)
  have H2 := (isPullback_SpecMap_of_isPushout _ _ _ _
    (H _ _ (hV y) (hW y) (hle y) e')).paste_vert (isPullback_specMap_app π (hV y)).flip.flip
  rw [IsAffineOpen.SpecMap_appLE_fromSpec p _ ((hW y).preimage φ),
    IsAffineOpen.SpecMap_appLE_fromSpec p' _ (hW y)] at H2
  refine H2.of_iso H1.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ((Category.comp_id _).trans (Category.id_comp _).symm)
    (by simp)
  · exact (Category.comp_id _).trans (H1.flip.isoPullback_hom_snd).symm
  · rw [Iso.refl_hom, Category.comp_id, ← Category.assoc]
    congr 1
    exact (H1.flip.isoPullback_hom_fst).symm

theorem isPushout_and_flat {Γ : Type} [Group Γ] [Finite Γ] {X X' Y Y' : Scheme.{0}}
    [IsLocallyNoetherian Y'] (ρ : Γ →* Aut X) (τ : Γ →* Aut Y) (π : X ⟶ X') (φ : Y ⟶ Y')
    (p : Y ⟶ X) (p' : Y' ⟶ X') [IsFinite π] [IsFinite φ] [Flat p]
    (hπ : ∀ g, (ρ g).asIso.hom ≫ π = π)
    (hπ' : ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V),
      (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) →
        f ∈ Set.range (π.app V).hom)
    (hφ : ∀ g, (τ g).asIso.hom ≫ φ = φ)
    (hφ' : ∀ V : Y'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(Y, φ ⁻¹ᵁ V),
      (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).asIso.hom ⁻¹ᵁ (φ ⁻¹ᵁ V)), ((τ g).asIso.hom.appLE _ _ h).hom f = f) →
        f ∈ Set.range (φ.app V).hom)
    (w : φ ≫ p' = p ≫ π) (hp : ∀ g, (τ g).asIso.hom ≫ p = p ≫ (ρ g).asIso.hom)
    (htame : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X),
      (Nat.card {g // x ≫ (ρ g).asIso.hom = x} : k) ≠ 0)
    (hfix : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).asIso.hom = x →
      pullback.fst p x ≫ (τ g).asIso.hom = pullback.fst p x)
    (V : X'.Opens) (W : Y'.Opens) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (e : W ≤ p' ⁻¹ᵁ V) (e' : φ ⁻¹ᵁ W ≤ p ⁻¹ᵁ π ⁻¹ᵁ V) :
    IsPushout (p'.appLE V W e) (π.app V) (φ.app W) (p.appLE _ _ e') ∧
      (p'.appLE V W e).hom.Flat := by
  have hU : IsAffineOpen (π ⁻¹ᵁ V) := hV.preimage π
  have hU' : IsAffineOpen (φ ⁻¹ᵁ W) := hW.preimage φ
  have hst := preimage_le_of_invariant ρ π hπ V
  have hst' := preimage_le_of_invariant τ φ hφ W
  let := sectionsAction ρ _ hst
  let := sectionsAction τ _ hst'
  let := (π.app V).hom.toAlgebra
  let := (φ.app W).hom.toAlgebra
  let := (p'.appLE V W e).hom.toAlgebra
  let := (p.appLE _ _ e').hom.toAlgebra
  let := (p'.appLE V W e ≫ φ.app W).hom.toAlgebra
  have sq : p'.appLE V W e ≫ φ.app W = π.app V ≫ p.appLE _ _ e' := by
    simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, w]
  have : IsScalarTower Γ(X', V) Γ(Y', W) Γ(Y, φ ⁻¹ᵁ W) := .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(X', V) Γ(X, π ⁻¹ᵁ V) Γ(Y, φ ⁻¹ᵁ W) :=
    .of_algebraMap_eq' congr(($sq).hom)
  have : SMulCommClass Γ Γ(X', V) Γ(X, π ⁻¹ᵁ V) := ⟨fun g a s ↦ by
    have hfix : g • algebraMap Γ(X', V) Γ(X, π ⁻¹ᵁ V) a = algebraMap _ _ a :=
      (isInvariantSection_app ρ π hπ V a g⁻¹).2
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hfix]⟩
  have : SMulCommClass Γ Γ(Y', W) Γ(Y, φ ⁻¹ᵁ W) := ⟨fun g a s ↦ by
    have hfix : g • algebraMap Γ(Y', W) Γ(Y, φ ⁻¹ᵁ W) a = algebraMap _ _ a :=
      (isInvariantSection_app τ φ hφ W a g⁻¹).2
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hfix]⟩
  have : Algebra.IsInvariant Γ(X', V) Γ(X, π ⁻¹ᵁ V) Γ := ⟨fun s hs ↦
    (hπ' V).2 s fun g _ ↦ by simpa only [inv_inv] using
      (show (ρ g⁻¹⁻¹).asIso.hom.appLE _ _ (hst _) s = s from hs g⁻¹)⟩
  have : Algebra.IsInvariant Γ(Y', W) Γ(Y, φ ⁻¹ᵁ W) Γ := ⟨fun s hs ↦
    (hφ' W).2 s fun g _ ↦ by simpa only [inv_inv] using
      (show (τ g⁻¹⁻¹).asIso.hom.appLE _ _ (hst' _) s = s from hs g⁻¹)⟩
  have heq : ∀ (g : Γ) (b : Γ(X, π ⁻¹ᵁ V)), g • algebraMap _ Γ(Y, φ ⁻¹ᵁ W) b =
      algebraMap _ Γ(Y, φ ⁻¹ᵁ W) (g • b) := fun g b => by
    change (τ g⁻¹).asIso.hom.appLE _ _ (hst' _) (p.appLE _ _ e' b) =
      p.appLE _ _ e' ((ρ g⁻¹).asIso.hom.appLE _ _ (hst _) b)
    simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, hp]
  have hflat : Module.Flat Γ(X, π ⁻¹ᵁ V) Γ(Y, φ ⁻¹ᵁ W) := p.flat_appLE hU hU' e'
  have key : ∀ q : Ideal Γ(X, π ⁻¹ᵁ V), q.IsPrime → ((Nat.card (q.inertia Γ) : Γ(X, π ⁻¹ᵁ V)) ∉ q) ∧
      ∀ g ∈ q.inertia Γ, ∀ c : Γ(Y, φ ⁻¹ᵁ W), g • c - c ∈ q.map (algebraMap _ Γ(Y, φ ⁻¹ᵁ W)) := by
    intro q hq
    let k := AlgebraicClosure q.ResidueField
    let a : Γ(X, π ⁻¹ᵁ V) →+* k := (algebraMap q.ResidueField k).comp (algebraMap _ _)
    have ha : ∀ b, a b = 0 ↔ b ∈ q := fun b => by
      simp [a]
    have hker : RingHom.ker a = q := Ideal.ext ha
    let x : Sp k ⟶ X := Spec.map (CommRingCat.ofHom a) ≫ hU.fromSpec
    have hx : ∀ g, x ≫ (ρ g⁻¹).asIso.hom = x ↔ g ∈ q.inertia Γ := fun g =>
      (specMap_fromSpec_comp_eq_iff _ hU (hst _) _).trans (forall_congr' fun b => ha _)
    refine ⟨fun h => htame k x ?_, fun g hg c => ?_⟩
    · rw [← Nat.card_congr ((Equiv.inv Γ).subtypeEquiv (p := fun g => g ∈ q.inertia Γ)
        (q := fun g => x ≫ (ρ g).asIso.hom = x) fun g => (hx g).symm), ← map_natCast a]
      exact (ha _).2 h
    · rw [← hker]
      exact appLE_sub_mem_map p _ hU hU' e' (hst' _) a (hfix k x _ ((hx g).2 hg)) c
  have hpo : Algebra.IsPushout Γ(X', V) Γ(X, π ⁻¹ᵁ V) Γ(Y', W) Γ(Y, φ ⁻¹ᵁ W) :=
    GlobalTheory.T.invariant_tower_isPushout Γ _ _ _ _ (hπ' V).1 (hφ' W).1 heq
      (IsLocallyNoetherian.component_noetherian ⟨W, hW⟩) (π.finite_app V hV) (φ.finite_app W hW)
      hflat (fun q hq => (key q hq).1) (fun q hq => (key q hq).2)
  refine ⟨CommRingCat.isPushout_iff_isPushout.2 hpo.symm, ?_⟩
  exact flat_of_tame_descent Γ _ _ _ _ (hπ' V).1 (hφ' W).1 heq hpo hflat
    (exists_finsum_smul_eq_one_of_tame Γ _ fun q hq => (key q hq).1)

theorem isPullback_flat_of_tame :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' Y Y' : Scheme.{0}) [IsLocallyNoetherian X'] (ρ : Γ →* Aut X) (τ : Γ →* Aut Y) (π : X ⟶ X') (φ : Y ⟶ Y') (p : Y ⟶ X) (p' : Y' ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → (IsAffineHom φ ∧ (∀ g, (τ g).asIso.hom ≫ φ = φ) ∧ ∀ V : Y'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(Y, φ ⁻¹ᵁ V), (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).asIso.hom ⁻¹ᵁ (φ ⁻¹ᵁ V)), ((τ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (φ.app V).hom) → φ ≫ p' = p ≫ π → (∀ g, (τ g).asIso.hom ≫ p = p ≫ (ρ g).asIso.hom) → IsFinite π → Flat p → LocallyOfFiniteType p → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).asIso.hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).asIso.hom = x → pullback.fst p x ≫ (τ g).asIso.hom = pullback.fst p x) → IsPullback φ p p' π ∧ Flat p' ∧ LocallyOfFiniteType p' := by
  intro Γ _ _ X X' Y Y' _ ρ τ π φ p p' hπ hφ w hp _ _ _ htame hfix
  obtain ⟨_, _, -⟩ := GlobalTheory.T.quotient_isFinite_and_descends_finiteness_properties Γ Y Y' τ φ hφ X' p' (by rw [w]; infer_instance)
  have : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian p'
  have H := isPushout_and_flat ρ τ π φ p p' hπ.2.1 hπ.2.2 hφ.2.1 hφ.2.2 w hp htame hfix
  refine ⟨isPullback_of_isPushout_app π φ p p' w fun V W hV hW e e' => (H V W hV hW e e').1,
    ⟨fun {V} hV {W} hW e => (H V W hV hW e ?_).2⟩, inferInstance⟩
  rw [← Scheme.Hom.comp_preimage, ← w, Scheme.Hom.comp_preimage]
  exact φ.preimage_mono e

end GlobalTheory.TameDescent
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM

namespace GlobalTheory

theorem smoothOfRelativeDimension_genericFibre_of_affine :
    ∀ (o : Type) [CommRing o] [IsDomain o] (X : Scheme.{0}) (s : X ⟶ Sp o) (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ X), IsOpenImmersion x → x ≫ s = spMap (algebraMap o R) → SmoothOfRelativeDimension d (spMap (algebraMap (FractionRing o) (FractionRing o ⊗[o] R)))) → SmoothOfRelativeDimension d (pullback.snd s (spMap (algebraMap o (FractionRing o)))) := by
  intro o _ _ X s d h
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension d) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension d)
    (Scheme.Pullback.openCoverOfLeft X.affineOpenCover.openCover s
      (spMap (algebraMap o (FractionRing o)))) fun i => ?_
  let R : CommRingCat.{0} := X.affineOpenCover.X i
  let x : Spec R ⟶ X := X.affineOpenCover.f i
  have hx : IsOpenImmersion x := X.affineOpenCover.map_prop i
  let φ : CommRingCat.of o ⟶ R := Spec.preimage (x ≫ s)
  letI : Algebra o R := φ.hom.toAlgebra
  have hφ : x ≫ s = spMap (algebraMap o R) := (Spec.map_preimage (x ≫ s)).symm
  have H := h R x hx hφ
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct o (FractionRing o) R)
  have sq' : IsPullback (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := o) (A := FractionRing o) (B := R)).toRingHom))
      (spMap (algebraMap (FractionRing o) (FractionRing o ⊗[o] R))) (x ≫ s)
      (spMap (algebraMap o (FractionRing o))) := by
    rw [hφ]
    exact sq.flip
  have e : (Scheme.Pullback.openCoverOfLeft X.affineOpenCover.openCover s
      (spMap (algebraMap o (FractionRing o)))).f i ≫ pullback.snd s _ =
      sq'.isoPullback.inv ≫ spMap (algebraMap (FractionRing o) (FractionRing o ⊗[o] R)) := by
    rw [IsPullback.isoPullback_inv_snd]
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  rw [e]
  have : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension d) := hloc.1
  exact @MorphismProperty.RespectsIso.precomp _ _ (@SmoothOfRelativeDimension d) this _ _ _
    sq'.isoPullback.inv sq'.isoPullback.isIso_inv _ H

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.exists_diagonal_element_lmul_eq_nonzero_geometric_points : ∀ (O : Type) [CommRing O] [IsLocalRing O] (G : Over (Sp O)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (H : Type) [CommRing H] [Algebra O H] [Module.Finite O H] [Module.Free O H] (y : specO O H ⟶ G), y ^ n = 1 → (∀ (S : Type) [CommRing S] [Algebra O S] (z : specO O S ⟶ G), z ^ n = 1 → ∃! φ : H →ₐ[O] S, ptMap φ ≫ y = z) → ∀ (ε : H →ₐ[O] O) (l : H) (c : O), ptMap ε ≫ y = 1 → (∀ h, ε h = 0 → h * l = 0) → ε l = c → l ∉ (IsLocalRing.maximalIdeal O).map (algebraMap O H) → ∃ Θ : H ⊗[O] H, (∀ h : H, (h ⊗ₜ[O] (1 : H)) * Θ = ((1 : H) ⊗ₜ[O] h) * Θ) ∧ Algebra.TensorProduct.lmul' O Θ = algebraMap O H c ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra O K], (∀ a ∈ IsLocalRing.maximalIdeal O, algebraMap O K a = 0) → ∀ ga : H →ₐ[O] K, Algebra.TensorProduct.map (AlgHom.id O H) ga Θ ≠ 0 := by
  first | exact @GlobalTheory.TorsionTheta.exists_theta | exact GlobalTheory.TorsionTheta.exists_theta | (intros; apply GlobalTheory.TorsionTheta.exists_theta <;> assumption)
end
