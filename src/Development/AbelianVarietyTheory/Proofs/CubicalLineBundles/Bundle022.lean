module

public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
public import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsHomogeneousOfEquivariant
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle021
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct
open GlobalTheory.GrpTangent

namespace GlobalTheory.SerreLie

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

theorem isLieComb_one_iff (c : R) (v x : epsR R ⟶ G) :
    IsLieComb ![c] ![v] x ↔ x = GrpTangent.epsScale c ≫ v := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    have h : u 0 = GrpTangent.epsScale c ≫ v := Over.OverMorphism.ext (hu 0)
    simp [h]
  · rintro rfl
    refine ⟨![GrpTangent.epsScale c ≫ v], fun i => ?_, by simp⟩
    fin_cases i
    rfl

variable [IsCommMonObj G] {O : Type} [CommRing O] [Algebra O R]

def multiples (a : OAct O G) {v : epsR R ⟶ G} (hv : IsTangent v)
    (ha : ∀ c, v ≫ a.act c = GrpTangent.epsScale (algebraMap O R c) ≫ v) : R →ₗ[O] Pts a (epsR R) where
  toFun r := Pts.mk a (GrpTangent.epsScale r ≫ v)
  map_add' r s := Pts.ext (epsScale_add_comp r s hv)
  map_smul' c r := Pts.ext (by
    simp only [Pts.hom_mk, RingHom.id_apply, Pts.hom_smul, Category.assoc, ha]
    rw [epsScale_mul_assoc, Algebra.smul_def, mul_comm])

theorem hom_multiples (a : OAct O G) {v : epsR R ⟶ G} (hv : IsTangent v)
    (ha : ∀ c, v ≫ a.act c = GrpTangent.epsScale (algebraMap O R c) ≫ v) (r : R) :
    (multiples a hv ha r).hom = GrpTangent.epsScale r ≫ v := rfl

omit [Algebra O R] in
theorem pre_eq_zero_iff (a : OAct O G) (x : Pts a (epsR R)) :
    Pts.pre a (toUnit (epsR R) ≫ epsZero R) x = 0 ↔ IsTangent x.hom := by
  rw [isTangent_iff]
  constructor
  · intro h
    have h1 : (toUnit (epsR R) ≫ epsZero R) ≫ x.hom = 1 := congrArg Pts.hom h
    have h2 := congrArg (epsZero R ≫ ·) h1
    simp only [← Category.assoc, MonObj.comp_one] at h2
    rwa [toUnit_unique (epsZero R ≫ toUnit _) (𝟙 _), Category.id_comp] at h2
  · intro h
    exact Pts.ext (by rw [Pts.hom_pre, Category.assoc, h, MonObj.comp_one]; rfl)

omit [Algebra O R] in
theorem isTangent_sub_pre (a : OAct O G) (x : Pts a (epsR R)) :
    IsTangent (x - Pts.pre a (toUnit (epsR R) ≫ epsZero R) x).hom := by
  rw [← pre_eq_zero_iff, map_sub, sub_eq_zero]
  apply Pts.ext
  simp only [Pts.hom_pre, ← Category.assoc]
  rw [Category.assoc (toUnit _) (epsZero R) (toUnit _),
    toUnit_unique (epsZero R ≫ toUnit _) (𝟙 _), Category.comp_id]

theorem exists_retraction (a : OAct O G) {v : epsR R ⟶ G} (hv : IsLieBasis ![v])
    (ha : ∀ c, v ≫ a.act c = GrpTangent.epsScale (algebraMap O R c) ≫ v) :
    ∃ ρ : Pts a (epsR R) →ₗ[O] R, ρ ∘ₗ multiples a (hv.1 0) ha = LinearMap.id ∧
      multiples a (hv.1 0) ha ∘ₗ ρ = LinearMap.id - Pts.pre a (toUnit (epsR R) ≫ epsZero R) := by
  have hinj : Function.Injective (multiples a (hv.1 0) ha) := fun r s h => by
    have h' : GrpTangent.epsScale r ≫ v = GrpTangent.epsScale s ≫ v := congrArg Pts.hom h
    have := (hv.2 _ (isTangent_epsScale r (hv.1 0))).unique
      ((isLieComb_one_iff r v _).2 rfl) ((isLieComb_one_iff s v _).2 h')
    exact congrFun this 0
  have hsur : ∀ x : Pts a (epsR R), ∃ r, multiples a (hv.1 0) ha r =
      (LinearMap.id - Pts.pre a (toUnit (epsR R) ≫ epsZero R) : _ →ₗ[O] _) x := fun x => by
    obtain ⟨c, hc, -⟩ := hv.2 _ (isTangent_sub_pre a x)
    have e : c = ![c 0] := by ext i; fin_cases i; rfl
    rw [e, isLieComb_one_iff] at hc
    exact ⟨c 0, Pts.ext hc.symm⟩
  choose ρ hρ using hsur
  refine ⟨⟨⟨ρ, fun x y => hinj ?_⟩, fun c x => hinj ?_⟩, LinearMap.ext fun r => hinj ?_,
    LinearMap.ext hρ⟩
  · rw [map_add (f := _), hρ, hρ, hρ, map_add (f := _)]
  · simp only [RingHom.id_apply, map_smul, hρ]
  · change multiples a (hv.1 0) ha (ρ _) = _
    rw [hρ, LinearMap.sub_apply, (pre_eq_zero_iff a (multiples a (hv.1 0) ha r)).2
      (isTangent_epsScale r (hv.1 0)), sub_zero]
    rfl

theorem exists_lie_tensor : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (O : Type) [CommRing O] [Algebra O R] (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M] [Module.Projective O M] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (a : OAct O G) (b : OAct O A) (t : IsTensor A b G a M) (v : epsR R ⟶ G), IsLieBasis ![v] → (∀ c, IsLieComb ![algebraMap O R c] ![v] (v ≫ a.act c)) → ∃ Φ : R ⊗[O] M → (epsR R ⟶ A), Function.Injective Φ ∧ (∀ x, IsTangent x ↔ x ∈ Set.range Φ) ∧ (∀ y z, Φ (y + z) = Φ y * Φ z) ∧ (∀ (c : R) y, IsLieComb ![c] ![Φ y] (Φ (c • y))) ∧ (∀ m, Φ (1 ⊗ₜ m) = v ≫ t.tmul m) ∧ ∀ (φ : M →ₗ[O] M) y, Φ (φ.baseChange R y) = Φ y ≫ t.mapLeft t φ := by
  intro R _ G _ _ O _ _ M _ _ _ _ A _ _ a b t v hv ha'
  have ha : ∀ c, v ≫ a.act c = GrpTangent.epsScale (algebraMap O R c) ≫ v :=
    fun c => (isLieComb_one_iff _ _ _).1 (ha' c)
  obtain ⟨ρ, h₁, h₂⟩ := exists_retraction a hv ha
  set j := multiples a (hv.1 0) ha with hj
  let Ψ : R ⊗[O] M →ₗ[O] Pts b (epsR R) :=
    (t.equiv _).toLinearMap ∘ₗ j.lTensor M ∘ₗ (TensorProduct.comm O R M).toLinearMap
  have hΨ : ∀ (r : R) (m : M), (Ψ (r ⊗ₜ m)).hom = GrpTangent.epsScale r ≫ v ≫ t.tmul m := fun r m => by
    simp [Ψ, hj, hom_multiples]
  refine ⟨fun y => (Ψ y).hom, fun y z h => ?_, fun x => ⟨fun hx => ?_, ?_⟩, fun y z => ?_,
    fun c y => ?_, fun m => ?_, fun φ y => ?_⟩
  · have h' : j.lTensor M (TensorProduct.comm O R M y) = j.lTensor M (TensorProduct.comm O R M z) :=
      (t.equiv _).injective (Pts.ext h)
    have h'' := congrArg (ρ.lTensor M) h'
    simp only [← LinearMap.lTensor_comp_apply, h₁, LinearMap.lTensor_id, LinearMap.id_apply] at h''
    exact (TensorProduct.comm O R M).injective h''
  · obtain ⟨z, hz⟩ := (t.equiv (epsR R)).surjective (Pts.mk b x)
    have h0 : (Pts.pre a (toUnit (epsR R) ≫ epsZero R)).lTensor M z = 0 := by
      apply (t.equiv _).injective
      rw [t.natural, hz, map_zero]
      exact (pre_eq_zero_iff b _).2 hx
    refine ⟨(TensorProduct.comm O R M).symm (ρ.lTensor M z), ?_⟩
    simp only [Ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rw [← LinearMap.lTensor_comp_apply, h₂, LinearMap.lTensor_sub, LinearMap.sub_apply, h0,
      sub_zero, LinearMap.lTensor_id, LinearMap.id_apply, hz, Pts.hom_mk]
  · rintro ⟨y, rfl⟩
    rw [← pre_eq_zero_iff]
    induction y with
    | tmul r m =>
      rw [pre_eq_zero_iff, hΨ]
      exact isTangent_epsScale r (isTangent_comp (hv.1 0) _)
    | add y z hy hz => rw [map_add (f := _), map_add (f := _), hy, hz, add_zero]
  · simp only [map_add (f := _), Pts.hom_add]
  · rw [isLieComb_one_iff]
    induction y with
    | tmul r m =>
      simp only [TensorProduct.smul_tmul', hΨ, smul_eq_mul]
      rw [epsScale_mul_assoc]
    | add y z hy hz =>
      simp only [smul_add, map_add (f := _), Pts.hom_add, MonObj.comp_mul] at hy hz ⊢
      rw [hy, hz]
  · simp only [hΨ, epsScale_one, Category.id_comp]
  · induction y with
    | tmul r m => simp only [LinearMap.baseChange_tmul, hΨ, Category.assoc, IsTensor.tmul_mapLeft]
    | add y z hy hz =>
      simp only [map_add (f := _), Pts.hom_add, MonObj.mul_comp] at hy hz ⊢
      rw [hy, hz]

end GlobalTheory.SerreLie
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.LatData

section General

variable {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M] [Module.Finite R M]

theorem exists_span_smul_mem {r : ℕ} (hr : Module.finrank R M = r) :
    ∃ (v : Fin r → M) (c : R), c ≠ 0 ∧ ∀ m : M, ∃ s : Fin r → R, c • m = ∑ i, s i • v i := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := R) (M := M) hr.ge
  have h1 := (Submodule.span R (Set.range v)).finrank_quotient_add_finrank
  rw [finrank_span_eq_card hv, Fintype.card_fin, hr] at h1
  have h2 : Module.IsTorsion R (M ⧸ Submodule.span R (Set.range v)) :=
    Module.finrank_eq_zero_iff_isTorsion.1 (by omega)
  obtain ⟨c, hc, hc0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors h2
  refine ⟨v, c, nonZeroDivisors.ne_zero hc0, fun m => ?_⟩
  have h3 := Submodule.mem_annihilator.1 hc (Submodule.Quotient.mk m) trivial
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_span_range_iff_exists_fun] at h3
  obtain ⟨s, hs⟩ := h3
  exact ⟨s, hs.symm⟩

theorem finrank_add_le_of_disjoint {A B : Submodule R M} (h : Disjoint A B) :
    Module.finrank R A + Module.finrank R B ≤ Module.finrank R M := by
  have h1 := A.finrank_quotient_add_finrank
  have h2 : Module.finrank R B ≤ Module.finrank R (M ⧸ A) := by
    refine LinearMap.finrank_le_finrank_of_injective (f := A.mkQ ∘ₗ B.subtype) ?_
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro b hb
    exact Subtype.ext (Submodule.disjoint_def.1 h _ ((Submodule.Quotient.mk_eq_zero A).1 hb) b.2)
  omega

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem rt0_ne_neg (H : Host E) : H.rt0 ≠ -H.rt0 := fun h => by
  have h0 : H.rt0 = 0 := by linear_combination h / 2
  have := H.sqrt_neg_disc_sq
  rw [h0] at this
  exact H.d_prime.ne_zero (by simpa using this)

theorem exists_embedding (H : Host E) {ρ : ℂ} (hρ : ρ ^ 2 = -(H.d : ℂ)) : ∃ τ : E →+* ℂ, τ (H.rt : E) = ρ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have := congrArg (fun x : 𝓞 E => τ (x : E)) H.rt_sq
    simpa using this
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (h1.trans hρ.symm) with h | h
  · exact ⟨τ, h⟩
  · refine ⟨(starRingEnd ℂ).comp τ, ?_⟩
    have hre : ρ.re = 0 := by
      have e1 := congrArg Complex.re hρ
      have e2 := congrArg Complex.im hρ
      have hd : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
      simp [pow_two] at e1 e2
      have e3 : ρ.re * ρ.im = 0 := by linarith
      rcases mul_eq_zero.1 e3 with e | e
      · exact e
      · rw [e] at e1
        nlinarith [mul_self_nonneg ρ.re]
    rw [RingHom.comp_apply, h]
    apply Complex.ext <;> simp [hre]

variable {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe)

theorem card_le_finrank_lat {ρ ρ' : ℂ} (hne : ρ ≠ ρ') {n : ℕ} (hn : 0 < n)
    (hs : ∀ a : D.La, n • a ∈ PureType.lat hP ρ ⊔ PureType.lat hP ρ') {τ : E →+* ℂ} (hτ : τ (H.rt : E) = ρ) :
    Nat.card {i // ty i = τ} ≤ Module.finrank (𝓞 E) (PureType.lat hP ρ) := by
  classical
  have := D.fin
  obtain ⟨v, c, hc, hv⟩ := exists_span_smul_mem (R := 𝓞 E) (M := PureType.lat hP ρ) rfl
  let pr : (Fin g → ℂ) →ₗ[ℂ] ({i // ty i = τ} → ℂ) := LinearMap.funLeft ℂ ℂ Subtype.val
  have hsm : ∀ (s : 𝓞 E) (a : D.La), pr (Pe (s • a)) = τ (s : E) • pr (Pe a) := fun s a => by
    funext i
    simp only [pr, LinearMap.funLeft_apply, Pi.smul_apply, smul_eq_mul]
    rw [hP.1, i.2]
  let W : Submodule ℂ ({i // ty i = τ} → ℂ) := Submodule.span ℂ (Set.range fun i => pr (Pe (v i)))
  have h1 : ∀ a : PureType.lat hP ρ, pr (Pe a) ∈ W := fun a => by
    obtain ⟨s, hs⟩ := hv a
    have hc' : τ (c : E) ≠ 0 := by simpa using hc

    rw [← W.smul_mem_iff hc', ← hsm, ← Submodule.coe_smul, hs, Submodule.coe_sum, map_sum, map_sum]
    refine W.sum_mem fun i _ => ?_
    rw [Submodule.coe_smul, hsm]
    exact W.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have h2 : ∀ a : D.La, pr (Pe a) ∈ W := fun a => by
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 (hs a)
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hy0 : pr (Pe y) = 0 := funext fun i => hy i (by rw [i.2, hτ]; exact hne)
    rw [← W.smul_mem_iff hn', Nat.cast_smul_eq_nsmul, ← map_nsmul, ← map_nsmul, ← hxy, map_add (f := _), map_add (f := _), hy0,
      add_zero]
    exact h1 ⟨x, hx⟩
  have h3 : W = ⊤ := by
    rw [eq_top_iff]
    rintro w -
    obtain ⟨z, rfl⟩ := LinearMap.funLeft_surjective_of_injective ℂ ℂ
      (Subtype.val : {i // ty i = τ} → Fin g) Subtype.val_injective w
    have hz : z ∈ Submodule.span ℝ (Set.range Pe) := by rw [hP.2.2.2.1]; trivial
    have : Submodule.span ℝ (Set.range Pe) ≤ (W.comap pr).restrictScalars ℝ :=
      Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact h2 a)
    exact this hz
  have h4 := finrank_le_of_span_eq_top h3
  simpa [Nat.card_eq_fintype_card] using h4

theorem finrank_lat (ht : IsTypeFn H D.p D.q ty) {n : ℕ} (hn : 0 < n)
    (hs : ∀ a : D.La, n • a ∈ PureType.lat hP H.rt0 ⊔ PureType.lat hP (-H.rt0)) :
    Module.finrank (𝓞 E) (PureType.lat hP H.rt0) = D.p ∧
      Module.finrank (𝓞 E) (PureType.lat hP (-H.rt0)) = D.q := by
  have := D.fin
  have hne := rt0_ne_neg H
  obtain ⟨τ, hτ⟩ := exists_embedding H H.sqrt_neg_disc_sq
  obtain ⟨τ', hτ'⟩ := exists_embedding H (ρ := -H.rt0) (by rw [neg_sq, H.sqrt_neg_disc_sq])
  have h1 := card_le_finrank_lat hP hne hn hs hτ
  have h2 := card_le_finrank_lat hP hne.symm hn (fun a => sup_comm (PureType.lat hP H.rt0) _ ▸ hs a) hτ'
  rw [(ht τ).1 hτ] at h1
  rw [(ht τ').2 (by rw [hτ']; exact hne.symm)] at h2
  have h3 := finrank_add_le_of_disjoint (PureType.disjoint_lat hP hne)
  rw [D.rank] at h3
  omega

end GlobalTheory.CM.LatData

namespace GlobalTheory.CM

end GlobalTheory.CM
end

section

set_option autoImplicit false

open MvPolynomial Formalism.L2.LamCM

namespace GlobalTheory.FrameDet

open GlobalTheory.BorelAlg

theorem exists_lower {K : Type} [Field K] {n : ℕ} (x y : Matrix (Fin n) (Fin n) K) (l : Fin n) (hl : ∀ i, i ≤ l)
    (hx : x.det ≠ 0) (h : ∀ i, i ≠ l → y i = x i) :
    ∃ b : Matrix (Fin n) (Fin n) K, y = b * x ∧ (∀ i j, i < j → b i j = 0) ∧ (∀ i, i ≠ l → b i i = 1) ∧
      b.det = b l l := by
  have hrow : ∀ i, i ≠ l → ∀ j, (y * x⁻¹) i j = (1 : Matrix _ _ K) i j := by
    intro i hi j
    rw [← Matrix.mul_nonsing_inv _ hx.isUnit]
    simp only [Matrix.mul_apply, h i hi]
  have hb : ∀ i j, i < j → (y * x⁻¹) i j = 0 := fun i j hij => by
    rw [hrow i (hij.trans_le (hl j)).ne, Matrix.one_apply_ne hij.ne]
  refine ⟨y * x⁻¹, ?_, hb, fun i hi => by rw [hrow i hi, Matrix.one_apply_eq], ?_⟩
  · rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hx.isUnit, Matrix.mul_one]
  · rw [Matrix.det_of_lowerTriangular _ (fun i j hij => hb i j hij), Finset.prod_eq_single l]
    · intro i _ hi; rw [hrow i hi, Matrix.one_apply_eq]
    · simp

theorem det_dvd_of_equivariant : ∀ (K : Type) [Field K] [Infinite K] (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (P : MvPolynomial (FrVar m) K) (a : ∀ b, Fin (m b) → ℕ), (∀ (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) (b : B) (t : Matrix (Fin (m b)) (Fin (m b)) K), (∀ b', (X b').det ≠ 0) → t.det ≠ 0 → t.BlockTriangular id → evalFr P (Function.update X b (X b * t)) = (∏ i, t i i ^ (a b i)) * evalFr P X) → ∀ b : B, (∀ i, 1 ≤ a b i) → ∃ Q : MvPolynomial (FrVar m) K, P = (Matrix.of fun i k : Fin (m b) => (MvPolynomial.X ⟨b, (k, i)⟩ : MvPolynomial (FrVar m) K)).det * Q := by
  intro K _ _ B _ _ m P a hP τ₀ ha
  have hT : (Matrix.of fun i k : Fin (m τ₀) => (MvPolynomial.X ⟨τ₀, (k, i)⟩ : MvPolynomial (FrVar m) K)).det =
      (gen m K τ₀).det := by
    rw [← Matrix.det_transpose]; rfl
  rw [hT]
  change (gen m K τ₀).det ∣ P
  by_cases h0 : m τ₀ = 0
  · haveI : IsEmpty (Fin (m τ₀)) := by rw [h0]; infer_instance
    rw [Matrix.det_isEmpty]; exact one_dvd _
  let l : Fin (m τ₀) := ⟨m τ₀ - 1, by omega⟩
  have hl : ∀ i, i ≤ l := fun i => by
    have := i.2
    simp only [Fin.le_def, l]; omega
  obtain ⟨hM0, hrel⟩ := minor_isRelPrime' (R := K) _ (inj_block m τ₀) l hl
  change ((gen m K τ₀).updateRow l (Pi.single l 1)).det ≠ 0 at hM0
  change IsRelPrime ((gen m K τ₀).updateRow l (Pi.single l 1)).det (gen m K τ₀).det at hrel
  set M := (gen m K τ₀).updateRow l (Pi.single l 1) with hM
  let x₀ : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) (MvPolynomial (Lt m) K) :=
    Function.update (gen m K) τ₀ M
  let P₀ : MvPolynomial (Lt m) K := eval₂Hom C (fun p : Lt m => x₀ p.1 p.2.1 p.2.2) P
  let D : MvPolynomial (Lt m) K := (∏ τ, (gen m K τ).det) * M.det
  have hD : D ≠ 0 := mul_ne_zero (Finset.prod_ne_zero_iff.2 fun τ _ => gen_det_ne_zero m K τ) hM0
  have k3 : P * M.det ^ a τ₀ l = (gen m K τ₀).det ^ a τ₀ l * P₀ := by
    apply mul_left_cancel₀ hD
    apply MvPolynomial.funext
    intro z
    by_cases hz : eval z D = 0
    · rw [map_mul, map_mul (eval z) D, hz, zero_mul, zero_mul]
    rw [map_mul, map_mul (eval z) D]
    congr 1
    let g : MvPolynomial (Lt m) K →+* K := eval z
    let x := fun τ => g.mapMatrix (x₀ τ)
    let y := fun τ => g.mapMatrix (gen m K τ)
    have hxd : ∀ τ, (x τ).det = g (x₀ τ).det := fun τ => (RingHom.map_det _ _).symm
    have hyd : ∀ τ, (y τ).det = g (gen m K τ).det := fun τ => (RingHom.map_det _ _).symm
    have hxM : (x τ₀).det = g M.det := by rw [hxd]; simp [x₀]
    have hz' : (∏ τ, g (gen m K τ).det) * g M.det ≠ 0 := by
      rw [← map_prod, ← map_mul]; exact hz
    have hy : ∀ τ, (y τ).det ≠ 0 := fun τ =>
      hyd τ ▸ Finset.prod_ne_zero_iff.1 (left_ne_zero_of_mul hz') τ (Finset.mem_univ _)
    have hne : ∀ τ, τ ≠ τ₀ → y τ = x τ := fun τ h => by simp [x, y, x₀, h]
    have hx : ∀ τ, (x τ).det ≠ 0 := fun τ => by
      by_cases h : τ = τ₀
      · subst h; rw [hxM]; exact right_ne_zero_of_mul hz'
      · rw [← hne τ h]; exact hy τ
    have hl' : ∀ i, i ≠ l → y τ₀ i = x τ₀ i := fun i h => by
      ext j; simp [x, y, x₀, M, Matrix.updateRow_ne h]
    obtain ⟨b, hxy, hb, hb1, hdet⟩ := exists_lower (x τ₀) (y τ₀) l hl (hx τ₀) hl'
    have hs : (y τ₀).det = b l l * (x τ₀).det := by rw [← hdet, ← Matrix.det_mul, ← hxy]
    have key := hP (fun τ => (x τ).transpose) τ₀ b.transpose
      (fun τ => by rw [Matrix.det_transpose]; exact hx τ)
      (by rw [Matrix.det_transpose, hdet]; exact left_ne_zero_of_mul (hs ▸ hy τ₀))
      (fun i j hij => hb j i hij)
    have e0 : Function.update (fun τ => (x τ).transpose) τ₀ ((x τ₀).transpose * b.transpose) =
        fun τ => (y τ).transpose := by
      funext τ
      by_cases h : τ = τ₀
      · subst h; rw [Function.update_self, ← Matrix.transpose_mul, ← hxy]
      · rw [Function.update_of_ne h, hne τ h]
    have e1 : evalFr P (fun τ => (y τ).transpose) = g P := by
      unfold evalFr
      congr 2
      funext v
      simp [y, g, gen]
    have e2 : evalFr P (fun τ => (x τ).transpose) = g P₀ := by
      have : (eval (fun v : FrVar m => (x v.1).transpose v.2.2 v.2.1) : MvPolynomial (Lt m) K →+* K) =
          g.comp (eval₂Hom C (fun p : Lt m => x₀ p.1 p.2.1 p.2.2)) := by
        ext <;> simp [x, g]
      unfold evalFr
      rw [this]; rfl
    have hc : (∏ i, b.transpose i i ^ a τ₀ i) = b l l ^ a τ₀ l := by
      rw [Finset.prod_eq_single l]
      · rfl
      · intro i _ hi; rw [Matrix.transpose_apply, hb1 i hi, one_pow]
      · simp
    rw [e0, e1, e2, hc] at key
    change g _ = g _
    rw [map_mul, map_mul, map_pow, map_pow, ← hxM, ← hyd, key, hs]
    ring
  have hd : (gen m K τ₀).det ^ a τ₀ l ∣ P :=
    (hrel.symm.pow (m := a τ₀ l) (n := a τ₀ l)).dvd_of_dvd_mul_right ⟨_, k3⟩
  exact (dvd_pow_self _ (by have := ha l; omega)).trans hd

end GlobalTheory.FrameDet
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.PowQuotient

variable {S S' : Scheme.{0}}

theorem isMonHom_prod {G H : Over S} [GrpObj G] [GrpObj H] [IsCommMonObj H] {n : ℕ} (a : Fin n → (G ⟶ H))
    (ha : ∀ i, IsMonHom (a i)) : IsMonHom (∏ i, a i) :=
  Finset.prod_induction a (fun z => IsMonHom z) (fun x y _ _ => isMonHom_mul x y) isMonHom_one fun i _ => ha i

end GlobalTheory.PowQuotient

namespace GlobalTheory

open PowQuotient

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.exists_torsion_injective_weil_compatible : Out.Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S) (k k' : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field k'] [IsAlgClosed k'] (j : k →+* k') (t : Sp k ⟶ S), ∃ r : (Over.mk t ⟶ P.A) →* (Over.mk (spMap j ≫ t) ⟶ P.A), (∀ x, (r x).left = spMap j ≫ x.left) ∧ Function.Injective r ∧ (∀ (n : ℕ) y, 0 < n → y ^ n = 1 → ∃ x, r x = y) ∧ ∀ (n : ℕ) x y (c : kˣ), 0 < n → x ^ n = 1 → y ^ n = 1 → (Out.WeilIs P.A P.L n x y (unitOn c) ↔ Out.WeilIs P.A P.L n (r x) (r y) (unitOn (Units.map j.toMonoidHom c))) := by
  first | exact @GlobalTheory.exists_torsion_fieldExt | exact GlobalTheory.exists_torsion_fieldExt | (intros; apply GlobalTheory.exists_torsion_fieldExt <;> assumption)
end
