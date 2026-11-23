module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.Tactic.Monotonicity.Lemmas
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HasBasisOfBasis
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle040
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBTransport
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FlatSec

theorem exists_equiv_of_isPushout {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {A A' : CommRingCat.{0}}
    [Algebra R A] (p : A ⟶ A') (s' : R' →+* A')
    (H : IsPushout (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R R')) p
      (CommRingCat.ofHom s')) :
    ∃ e : R' ⊗[R] A ≃+ A', ∀ c v, e (c ⊗ₜ v) = s' c * p.hom v := by
  let _ : Algebra A A' := p.hom.toAlgebra
  let _ : Algebra R' A' := s'.toAlgebra
  let _ : Algebra R A' := (s'.comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' A' := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R A A' := .of_algebraMap_eq fun r => (congrArg (fun q => q.hom r) H.w).symm
  have h : Algebra.IsPushout R R' A A' := (CommRingCat.isPushout_iff_isPushout.mp H).symm
  exact ⟨h.out.equiv.toAddEquiv, fun c v => (h.out.equiv_tmul c v).trans (Algebra.smul_def _ _)⟩

theorem exists_comb_ker {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R']
    {I J : Type} [Fintype I] [Fintype J] {A : I → Type} {B : J → Type} {A' : I → Type} {B' : J → Type}
    [∀ a, AddCommGroup (A a)] [∀ a, Module R (A a)] [∀ b, AddCommGroup (B b)] [∀ b, Module R (B b)]
    [∀ a, AddCommGroup (A' a)] [∀ b, AddCommGroup (B' b)]
    (e : ∀ a, R' ⊗[R] A a ≃+ A' a) (e' : ∀ b, R' ⊗[R] B b ≃+ B' b) (d : (∀ a, A a) →ₗ[R] (∀ b, B b))
    (x : ∀ a, A' a)
    (hx : ∀ (n : ℕ) (c : Fin n → R') (v : Fin n → ∀ a, A a), (∀ a, x a = ∑ i, e a (c i ⊗ₜ v i a)) →
      ∀ b, ∑ i, e' b (c i ⊗ₜ d (v i) b) = 0) :
    ∃ (n : ℕ) (c : Fin n → R') (v : Fin n → ∀ a, A a), (∀ a, x a = ∑ i, e a (c i ⊗ₜ v i a)) ∧ ∀ i, d (v i) = 0 := by
  classical
  obtain ⟨t, ht⟩ := (TensorProduct.piRight R R R' A).surjective (fun a => (e a).symm (x a))
  have key : ∀ (n : ℕ) (c : Fin n → R') (v : Fin n → ∀ a, A a), t = ∑ i, c i ⊗ₜ v i →
      ∀ a, x a = ∑ i, e a (c i ⊗ₜ v i a) := fun n c v h a => by
    have := congrFun ht a

    rw [h, map_sum, Finset.sum_apply, AddEquiv.eq_symm_apply, map_sum] at this
    rw [← this]
    rfl
  have h0 : d.lTensor R' t = 0 := by
    obtain ⟨n, c, v, h⟩ := TensorProduct.exists_sum_tmul_eq t
    apply (TensorProduct.piRight R R R' B).injective
    funext b
    apply (e' b).injective

    rw [map_zero, Pi.zero_apply, map_zero, ← hx n c v (key n c v h) b, h, map_sum, map_sum, Finset.sum_apply, map_sum]
    rfl
  obtain ⟨w, hw⟩ := (Module.Flat.lTensor_exact R' (LinearMap.exact_subtype_ker_map d) t).1 h0
  obtain ⟨n, c, v, rfl⟩ := TensorProduct.exists_sum_tmul_eq w
  refine ⟨n, c, fun i => (v i).1, key n c _ ?_, fun i => (v i).2⟩

  rw [← hw, map_sum]
  rfl

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' Z : Scheme.{0}}

theorem isPushout_app {g : R →+* R'} (hg : g.Flat) {f : X ⟶ Spec (CommRingCat.of R)} {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of R')} (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    {U : X.Opens} (hU : IsCompact (U : Set X)) (hU' : IsQuasiSeparated (U : Set X)) :
    IsPushout (CommRingCat.ofHom (cst f U)) (CommRingCat.ofHom g) (π.app U)
      (CommRingCat.ofHom (cst f' (π ⁻¹ᵁ U))) := by
  have : Flat (Spec.map (CommRingCat.ofHom g)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact hg
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := π ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU hU')
  refine po.of_iso (Scheme.ΓSpecIso (.of R)) (Iso.refl _) (Scheme.ΓSpecIso (.of R')) (Iso.refl _) ?_ ?_ ?_ ?_
  · ext x; simp [AbLaw.cst, Scheme.Hom.appLE]; rfl
  · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  · simp [Scheme.Hom.app_eq_appLE]
  · ext x; simp [AbLaw.cst, Scheme.Hom.appLE]; rfl

theorem gs_sum (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) {n : ℕ} (a : Fin n → Γ(X, U)) :
    gs r z U (∑ i, a i) = ∑ i, gs r z U (a i) := by simp only [gs_eq r z U h, map_sum]

theorem gs_cst (f : X ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (c : R) :
    gs r z U (cst f U c) = gs r z ⊤ (cst f ⊤ c) := by
  rw [← rs_cst f (le_top : U ≤ ⊤) c]
  exact gs_res r z _ h _

theorem gs_comb (f' : X' ⟶ Spec (CommRingCat.of R')) (π : X' ⟶ X) (U : X.Opens) (z : X') (h : π z ∈ U) {n : ℕ}
    (c : Fin n → R') (v : Fin n → Γ(X, U)) :
    gs (𝟙 X') z (π ⁻¹ᵁ U) (∑ i, cst f' (π ⁻¹ᵁ U) (c i) * (π.app U).hom (v i)) =
      ∑ i, gs (𝟙 X') z ⊤ (cst f' ⊤ (c i)) * gs π z U (v i) := by
  rw [gs_sum (𝟙 X') z (π ⁻¹ᵁ U) h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_mul (𝟙 X') z (π ⁻¹ᵁ U) h, gs_cst f' (𝟙 X') z (π ⁻¹ᵁ U) h, gs_pull (𝟙 X') π z U h, Category.id_comp]

theorem gs_pull_trans {M : LB X} {π : X' ⟶ X} (σ : LB.Sec (M.pull π)) (z : X') {k l : M.ι} (hk : π z ∈ M.U k)
    (hl : π z ∈ M.U l) : gs (𝟙 X') z _ (σ.f (fun _ => k)) =
      (gm π z (M.U k ⊓ M.U l) (M.g k l)).val * gs (𝟙 X') z _ (σ.f (fun _ => l)) := by
  refine (sec_trans σ (𝟙 X') z (j := fun _ => k) (j' := fun _ => l) (Set.mem_iInter.2 fun _ => hk)
    (Set.mem_iInter.2 fun _ => hl)).trans ?_
  rw [trF, Fintype.prod_unique, zpow_one, Category.id_comp]
  rfl

theorem gs_sec_trans {M : LB X} (s : LB.Sec M) (r : Z ⟶ X) (z : Z) {k l : M.ι} (hk : r z ∈ M.U k)
    (hl : r z ∈ M.U l) : gs r z _ (s.f k) = (gm r z (M.U k ⊓ M.U l) (M.g k l)).val * gs r z _ (s.f l) := by
  have hm : r z ∈ M.U k ⊓ M.U l := ⟨hk, hl⟩
  exact (gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (s.compat k l)).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit r z _ hm _) (gs_res r z _ hm _))))

theorem gs_diff {M : LB X} {V W : X.Opens} {k l : M.ι} (hV : V ≤ M.U k) (hW : W ≤ M.U l) (a : Γ(X, V)) (b : Γ(X, W))
    (r : Z ⟶ X) (z : Z) (h : r z ∈ V ⊓ W) :
    gs r z (V ⊓ W) (rs X inf_le_left a - rs X (inf_le_inf hV hW) (M.g k l).val * rs X inf_le_right b) =
      gs r z V a - (gm r z (M.U k ⊓ M.U l) (M.g k l)).val * gs r z W b := by
  rw [LBGerm.gs_sub r z _ h, gs_mul r z _ h, gs_res r z _ h, gs_res r z _ h, gs_res r z _ h,
    gs_unit r z (M.U k ⊓ M.U l) ⟨hV h.1, hW h.2⟩]

theorem exists_comb_of_flat : ∀ (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R'), g.Flat → ∀ (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X] (f : X ⟶ Spec (CommRingCat.of R)) (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → ∀ M : LB X, M.IsLB → ∀ σ : LB.Sec (M.pull π), ∃ (n : ℕ) (c : Fin n → R') (u : Fin n → LB.Sec M), ∀ (z : X') (k : M.ι), π z ∈ M.U k → gs (𝟙 X') z _ (σ.f (fun _ => k)) = ∑ i, gs (𝟙 X') z ⊤ (cst f' ⊤ (c i)) * gs π z _ ((u i).f k) := by
  intro R R' _ _ g hg X _ _ f X' π f' H M hM σ
  obtain ⟨α, _, W, j, hA, hW, hc⟩ := exists_finite_affine_refinement hM
  let _ : Algebra R R' := g.toAlgebra
  have : Module.Flat R R' := hg
  let _ : ∀ U : X.Opens, Algebra R Γ(X, U) := fun U => (cst f U).toAlgebra
  choose e he using fun a => exists_equiv_of_isPushout (R := R) (π.app (W a)) (cst f' (π ⁻¹ᵁ W a))
    (isPushout_app hg H (hA a).isCompact (hA a).isQuasiSeparated)
  choose e' he' using fun p : α × α => exists_equiv_of_isPushout (R := R) (π.app (W p.1 ⊓ W p.2))
    (cst f' (π ⁻¹ᵁ (W p.1 ⊓ W p.2))) (isPushout_app hg H
      (QuasiSeparatedSpace.inter_isCompact _ _ (W p.1).isOpen (hA p.1).isCompact (W p.2).isOpen (hA p.2).isCompact)
      (IsQuasiSeparated.of_quasiSeparatedSpace _))
  let d : (∀ a, Γ(X, W a)) →ₗ[R] (∀ p : α × α, Γ(X, W p.1 ⊓ W p.2)) :=
    { toFun := fun v p => rs X inf_le_left (v p.1) -
        rs X (inf_le_inf (hW p.1) (hW p.2)) (M.g (j p.1) (j p.2)).val * rs X inf_le_right (v p.2)
      map_add' := fun v w => funext fun p => by
        simp only [Pi.add_apply, map_add (f := _)]; ring
      map_smul' := fun r v => funext fun p => by
        simp only [Pi.smul_apply, Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra, rs_cst,
          RingHom.id_apply]; ring }
  have hx : ∀ {n : ℕ} {c : Fin n → R'} {v : Fin n → ∀ a, Γ(X, W a)},
      (∀ a, rs X' (le_pull M π (hW a)) (σ.f fun _ => j a) = ∑ i, e a (c i ⊗ₜ v i a)) →
      ∀ a z, π z ∈ W a → gs (𝟙 X') z _ (σ.f fun _ => j a) =
        ∑ i, gs (𝟙 X') z ⊤ (cst f' ⊤ (c i)) * gs π z _ (v i a) := fun {n c v} h a z hz => by
    have h' := congrArg (gs (𝟙 X') z (π ⁻¹ᵁ W a)) (h a)
    simp only [he] at h'
    rw [gs_comb f' π _ z hz] at h'
    exact (gs_res (𝟙 X') z _ hz _).symm.trans h'
  obtain ⟨n, c, v, hv, hd⟩ := exists_comb_ker e e' d (fun a => rs X' (le_pull M π (hW a)) (σ.f fun _ => j a))
    (fun n c v h p => fn_ext fun z hz => by
      simp only [he']
      rw [gs_comb f' π _ z hz, LBGerm.gs_zero (𝟙 X') z _ hz]
      have h₁ := gs_pull_trans σ z (hW _ hz.1) (hW _ hz.2)
      rw [hx h p.1 z hz.1, hx h p.2 z hz.2, Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h₁
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h₁
      refine (congrArg _ (gs_diff (hW p.1) (hW p.2) (v i p.1) (v i p.2) π z hz)).trans ?_
      ring)
  choose u hu using fun i => exists_sec_of_refinement hM W j hW hc (v i) fun y a b ha hb => by
    have h := congrArg (gs (𝟙 X) y (W a ⊓ W b)) (congrFun (hd i) (a, b))
    exact sub_eq_zero.1 ((gs_diff (hW a) (hW b) (v i a) (v i b) (𝟙 X) y ⟨ha, hb⟩).symm.trans
      (h.trans (LBGerm.gs_zero (𝟙 X) y _ ⟨ha, hb⟩)))
  have hu' : ∀ i a, rs X (hW a) ((u i).f (j a)) = v i a := fun i a => fn_ext fun y hy => by
    rw [gs_res (𝟙 X) y _ hy, hu i y (j a) a (hW a hy) hy, gm_self hM (𝟙 X) y (hW a hy), Units.val_one,
      _root_.one_mul]
  refine ⟨n, c, u, fun z k hk => ?_⟩
  obtain ⟨a, ha⟩ := hc (π z)
  rw [gs_pull_trans σ z hk (hW a ha), hx hv a z ha, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_sec_trans (u i) π z hk (hW a ha), ← hu' i a, gs_res π z _ ha]
  ring

end GlobalTheory.FlatSec
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Square

section General
variable {X Y : Scheme.{0}} {L : LB X} {K K' K'' : Type} [Fintype K] [Fintype K'] [Fintype K'']

private theorem map_zpow_zpow {M N : Type} [Group M] [Group N] (F : M →* N) (x : M) (n e : ℤ) :
    F (x ^ n) ^ e = F x ^ (n * e) := by
  rw [map_zpow, ← zpow_mul]

theorem linComb_pw (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (n : ℤ) :
    LB.LinComb (pw L n) φ ε = LB.LinComb L φ (fun k => n * ε k) := by
  unfold LB.LinComb GlobalTheory.AbLaw.pw
  congr 1
  funext j j'
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow]
  exact map_zpow_zpow _ _ _ _

private theorem sameSum_of_prod_pow_eq' {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] {φ₁ : K₁ → (Y ⟶ X)} {ε₁ : K₁ → ℤ}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ}
    (h : ∀ (U : Type) [CommGroup U] (f : (Y ⟶ X) → U), ∏ k, f (φ₁ k) ^ ε₁ k = ∏ k, f (φ₂ k) ^ ε₂ k) :
    LB.SameSum φ₁ ε₁ φ₂ ε₂ := by
  classical
  intro ψ
  have e := congrArg Multiplicative.toAdd
    (h (Multiplicative ℤ) (fun χ => Multiplicative.ofAdd (if χ = ψ then (1 : ℤ) else 0)))
  simp only [toAdd_prod, toAdd_zpow, toAdd_ofAdd, smul_eq_mul, mul_ite, mul_zero] at e
  convert e <;> simp

theorem triv_mul (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {φ'' : K'' → (Y ⟶ X)} {ε'' : K'' → ℤ} (h₁ : Triv (LB.LinComb L φ ε)) (h₂ : Triv (LB.LinComb L φ' ε'))
    (h : ∀ (U : Type) [CommGroup U] (f : (Y ⟶ X) → U),
      (∏ k, f (φ k) ^ ε k) * ∏ k, f (φ' k) ^ ε' k = ∏ k, f (φ'' k) ^ ε'' k) : Triv (LB.LinComb L φ'' ε'') := by
  obtain ⟨t₁, ht₁⟩ := h₁
  obtain ⟨t₂, ht₂⟩ := h₂
  have hs : LB.SameSum (Sum.elim φ φ') (Sum.elim ε ε') φ'' ε'' := sameSum_of_prod_pow_eq' fun U _ f => by
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
    exact h U f
  obtain ⟨t, ht, -⟩ := DVR.gen_transport hL hs (LB.mulGen L φ ε φ' ε' t₁ t₂)
    (DVR.mulGen_isGen L φ ε φ' ε' t₁ t₂ ht₁ ht₂)
  exact ⟨t, ht⟩

theorem triv_inv {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Triv (LB.LinComb L φ ε)) :
    Triv (LB.LinComb L φ fun k => -ε k) := by
  obtain ⟨t, ht⟩ := h
  exact ⟨LB.invGen L φ ε t, DVR.invGen_isGen L φ ε t ht⟩

end General

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {L : RigLB B}
  {A : Type} [CommRing A] [IsLocalRing A] {t : Spec (CommRingCat.of A) ⟶ S}


omit [IsCommMonObj B] in
theorem triv_const {K : Type} [Fintype K] (x : K → (Over.mk t ⟶ B)) (ε : K → ℤ) :
    Triv (LB.LinComb L.L (fun k => (fst (Over.mk t) B ≫ x k).left) ε) := by
  obtain ⟨e, he⟩ := DVR.exists_gen_of_local (V := A) L.L L.isLB (fun k => (x k).left) ε
  exact ⟨LB.pullGen L.L (fun k => (x k).left) ε e (fst (Over.mk t) B).left,
    DVR.pullGen_isGen L.L _ ε e he _⟩

private theorem translPt_eq_fst_comp_mul_snd {T : Over S} (w : T ⟶ B) : translPt B w = (fst T B ≫ w) * snd T B := by
  unfold translPt
  rw [Hom.mul_def]

private theorem over_comp_mul {T T' : Over S} (f : T' ⟶ T) (g h : T ⟶ B) : f ≫ (g * h) = (f ≫ g) * (f ≫ h) := by
  rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]

private theorem over_comp_one {T T' : Over S} (f : T' ⟶ T) : f ≫ (1 : T ⟶ B) = 1 := by
  simp [Hom.one_def]

theorem triv_square (c : CubicalStr B L) (x y : Over.mk t ⟶ B) :
    Triv (LB.LinComb L.L (K := Fin 4) ![(translPt B (x * y)).left, (snd (Over.mk t) B).left, (translPt B x).left,
      (translPt B y).left] ![1, 1, -1, -1]) := by
  have h₁ : Triv (LB.LinComb L.L (fun k => (lift (fst (Over.mk t) B ≫ x)
      (lift (fst (Over.mk t) B ≫ y) (snd (Over.mk t) B))).left ≫ thφ B (x3 B) k) thε) :=
    ⟨LB.pullGen L.L (thφ B (x3 B)) thε c.t _, DVR.pullGen_isGen L.L _ _ c.t c.isGen _⟩
  have h₂ := triv_const (L := L) (t := t) (K := Fin 4) ![x * y, x, y, 1] ![1, -1, -1, 1]
  refine triv_mul L.isLB h₁ h₂ fun U _ f => ?_
  rw [Geo.Tor.prod_cub]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    zpow_one, zpow_neg]
  simp only [translPt_eq_fst_comp_mul_snd, over_comp_mul, over_comp_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem triv_pow (c : CubicalStr B L) (r : ℕ) (x : Over.mk t ⟶ B) :
    Triv (LB.LinComb L.L (K := Fin 3) ![(translPt B (x ^ r)).left, (translPt B x).left, (snd (Over.mk t) B).left]
      ![1, -r, r - 1]) := by
  induction r with
  | zero =>
    have h₀ := triv_const (L := L) (t := t) (K := Fin 0) ![] ![]
    refine triv_mul L.isLB h₀ h₀ fun U _ f => ?_
    rw [pow_zero, translPt_eq_fst_comp_mul_snd, over_comp_one, _root_.one_mul]
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, _root_.mul_one]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_one]
    push_cast
    module
  | succ r ih =>
    have hs := triv_square c (x ^ r) x
    refine triv_mul L.isLB hs ih fun U _ f => ?_
    rw [pow_succ]
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, _root_.mul_one]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow]
    push_cast
    module

theorem square_of_cubical : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B] (L : RigLB B) (_ : CubicalStr B L) (A : Type) [CommRing A] [IsLocalRing A] (t : Spec (CommRingCat.of A) ⟶ S), (∀ x y : Over.mk t ⟶ B, Triv (LB.LinComb L.L (K := Fin 4) ![(translPt B (x * y)).left, (snd (Over.mk t) B).left, (translPt B x).left, (translPt B y).left] ![1, 1, -1, -1])) ∧ ∀ (r : ℕ) (x : Over.mk t ⟶ B), Triv (translDiff B (pw L.L r) x) ↔ Triv (translDiff B L.L (x ^ r)) := by
  intro S B _ _ L c A _ _ t
  refine ⟨fun x y => triv_square c x y, fun r x => ?_⟩
  have hP := triv_pow c r x
  unfold translDiff
  rw [linComb_pw]
  simp only [← Hom.mul_def]
  simp only [translPt_eq_fst_comp_mul_snd] at hP
  constructor
  · intro h
    refine triv_mul L.isLB h hP fun U _ f => ?_
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_one]
    module
  · intro h
    refine triv_mul L.isLB h (triv_inv hP) fun U _ f => ?_
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_one]
    module

end GlobalTheory.Square
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExpansionCriterion

private lemma sum_smul_sum_smul_eq_sum_mul_smul {K S J : Type} [Field K] {Λ : J → Type} [∀ j, CommRing (Λ j)]
    (ρ : ∀ j, K →+* Λ j) (f : S → ∀ j, Λ j) {n : ℕ} (b t : Fin n → S)
    (D : Matrix (Fin n) (Fin n) K) (hD : ∀ k j, f (t k) j = ∑ i, ρ j (D k i) * f (b i) j)
    (c : Fin n → K) (j : J) :
    ∑ k, ρ j (c k) * f (t k) j = ∑ i, ρ j (Matrix.vecMul c D i) * f (b i) j := by

  simp only [hD, Matrix.vecMul, dotProduct, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

theorem total_of_onto {K S V J : Type} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    {Λ : J → Type} [∀ j, CommRing (Λ j)] (ρ : ∀ j, K →+* Λ j) (f : S → ∀ j, Λ j)
    (E : S → V → Prop) {n : ℕ} (hn : Module.finrank K V = n) (b : Fin n → S)
    (hb₁ : ∀ c : Fin n → K, ∃ s : S, ∀ j, f s j = ∑ i, ρ j (c i) * f (b i) j)
    (hb₂ : ∀ s : S, ∃ c : Fin n → K, ∀ j, f s j = ∑ i, ρ j (c i) * f (b i) j)
    (hlin : ∀ (t : Fin n → S) (F : Fin n → V) (c : Fin n → K) (s : S), (∀ i, E (t i) (F i)) →
      (∀ j, f s j = ∑ i, ρ j (c i) * f (t i) j) → E s (∑ i, c i • F i))
    (hfun : ∀ s F F', E s F → E s F' → F = F')
    (hon : ∀ F, ∃ s, E s F) (s : S) : ∃ F, E s F := by
  classical

  let v := Module.finBasisOfFinrankEq K V hn
  choose t ht using fun k => hon (v k)
  choose D hD using fun k => hb₂ (t k)
  have key := sum_smul_sum_smul_eq_sum_mul_smul ρ f b t (D : Matrix (Fin n) (Fin n) K) hD

  have hinj : Function.Injective (Matrix.vecMulLinear (D : Matrix (Fin n) (Fin n) K)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have hc' : Matrix.vecMul c (D : Matrix (Fin n) (Fin n) K) = 0 := hc
    obtain ⟨s₀, hs₀⟩ := hb₁ 0
    have h1 : E s₀ (∑ k, c k • v k) :=
      hlin t (fun k => v k) c s₀ ht (fun j => by rw [key c j, hc', hs₀ j])
    have h0 : E s₀ (∑ k, (0 : Fin n → K) k • v k) :=
      hlin t (fun k => v k) 0 s₀ ht (fun j => by rw [hs₀ j]; simp)
    have hsum : ∑ k, c k • v k = 0 := by simpa using hfun _ _ _ h1 h0
    funext k
    exact Fintype.linearIndependent_iff.mp v.linearIndependent c hsum k
  obtain ⟨a, ha⟩ := hb₂ s
  obtain ⟨c, hc⟩ := (LinearMap.injective_iff_surjective.mp hinj) a
  have hc' : Matrix.vecMul c (D : Matrix (Fin n) (Fin n) K) = a := hc
  exact ⟨_, hlin t (fun k => v k) c s ht (fun j => by rw [key c j, hc']; exact ha j)⟩

noncomputable def scalRes {R : Type} [CommRing R] {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of R)) (W : Y.Opens) : R →+* Γ(Y, W) :=
  ((Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom.comp p.appTop.hom).comp
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem expBij_of_onto : SecBaseChangeSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GeometricallyConnected G.hom] (U : UnifPre I D A G) (k : ℕ), 1 ≤ k → Module.Finite (FractionRing R) (Fam D.toPre (FractionRing R) k) → Module.finrank (FractionRing R) (Fam D.toPre (FractionRing R) k) = k ^ A.g → (∀ F : Fam D.toPre (FractionRing R) k, ∃ s : U.SecK k, U.Expands k s F) → U.ExpBij k := by
  intro hS R _ _ I hR D A G _ _ _ U k hk _ hrank honto
  obtain ⟨b, hb₁, hb₂⟩ := GlobalTheory.GenericSectionBasis.exists_secK_basis hS R I D A G U k hk
  have resTop_scal_lemma_2 : ∀ (W : (pullback G.hom (jK R)).Opens) (r : FractionRing R),
      resTop W (scal (pullback.snd G.hom (jK R)) r) = scalRes (pullback.snd G.hom (jK R)) W r :=
    fun W r => (GlobalTheory.ExpandsLinear.scalOn_apply _ W r).trans rfl

  have huniq := GlobalTheory.T.uniformisation_eq_iff_expansion_eq R I hR D A G U k
  have htot : ∀ s : U.SecK k, ∃ F, U.Expands k s F := by
    intro s
    refine total_of_onto (K := FractionRing R) (f := fun (s : U.SecK k) j => s.f j)
      (ρ := fun j => scalRes (pullback.snd G.hom (jK R)) _) (E := U.Expands k) hrank b
      (fun c => ?_) (fun s => ?_) (fun t F c s ht hs => ?_)
      (fun s F F' h h' => (huniq s s F F' h h').mp rfl) honto s
    · obtain ⟨s, hs⟩ := hb₁ c
      exact ⟨s, fun j => by simpa only [resTop_scal_lemma_2] using hs j⟩
    · obtain ⟨c, hc, _⟩ := hb₂ s
      exact ⟨c, fun j => by simpa only [resTop_scal_lemma_2] using hc j⟩
    · exact GlobalTheory.expands_linear R I hR D A G U k _ t F c s ht
        (fun j => by simpa only [resTop_scal_lemma_2] using hs j)

  refine ⟨fun s => ?_, fun F => ?_⟩
  · obtain ⟨F, hF⟩ := htot s
    exact ⟨F, hF, fun F' hF' => (huniq s s F' F hF' hF).mp rfl⟩
  · obtain ⟨s, hs⟩ := honto F
    exact ⟨s, hs, fun s' hs' => (huniq s' s F F hs' hs).mpr rfl⟩

end GlobalTheory.ExpansionCriterion
end
