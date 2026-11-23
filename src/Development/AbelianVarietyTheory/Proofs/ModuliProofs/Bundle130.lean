module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle060
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle050
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle094
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle014
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle124
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle095
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle125
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleDiagonalBiadditiveOfE8Form
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle127
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle128
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

noncomputable section
namespace GlobalTheory.CubNondeg

theorem gs_appLE {Y Y' : Scheme.{0}} (τ : Y' ⟶ Y) (W : Y.Opens) (W' : Y'.Opens)
    (h : W' ≤ τ ⁻¹ᵁ W) (a : Γ(Y, W)) (x : Y') (hx : x ∈ W') :
    gs (𝟙 Y') x W' ((τ.appLE W W' h).hom a) = gs τ x W a := by
  have e := (gs_res (𝟙 Y') x h hx ((τ.app W).hom a)).trans (gs_pull (𝟙 Y') τ x W (h hx) a)
  rw [Category.id_comp] at e
  exact e

theorem descend_linComb {X Y Y' : Scheme.{0}} (m : Y' ⟶ Y) {T : Type} (τ : T → (Y' ⟶ Y'))
    (hτ : ∀ t, τ t ≫ m = m)
    (H : ∀ (V : Y.Opens) (a : Γ(Y', m ⁻¹ᵁ V)),
      (∀ t, ∀ h : m ⁻¹ᵁ V ≤ τ t ⁻¹ᵁ (m ⁻¹ᵁ V), ((τ t).appLE _ _ h).hom a = a) →
      ∃! a' : Γ(Y, V), (m.app V).hom a' = a)
    (M : LB X) (hM : M.IsLB) {K : Type} [Fintype K] (ψ : K → (Y ⟶ X)) (ε : K → ℤ)
    (σ : LB.Gen (LB.LinComb M (fun k => m ≫ ψ k) ε)) (hσ : σ.IsGen)
    (inv : ∀ t (z : Y') (J : (Y' ⟶ X) → M.1), Good M z J → val σ (τ t) z J = val σ (𝟙 Y') z J) :
    ∃ t : (LB.LinComb M ψ ε).Gen, t.IsGen := by
  have inj : ∀ V : Y.Opens, Function.Injective (m.app V).hom := by
    intro V a b e
    obtain ⟨c, -, hc⟩ := H V ((m.app V).hom a) (fun t h => fn_ext fun x hx => by
      rw [gs_appLE (τ t) _ _ h _ x hx, gs_pull (τ t) m x V (h hx), gs_pull (𝟙 Y') m x V hx, hτ,
        Category.id_comp])
    exact (hc a rfl).trans (hc b e.symm).symm
  have injU : ∀ V : Y.Opens, Function.Injective (pullU m V) := fun V a b e =>
    Units.ext (inj V (congrArg Units.val e))
  have descU : ∀ (V : Y.Opens) (u : Γ(Y', m ⁻¹ᵁ V)ˣ),
      (∀ t x, x ∈ m ⁻¹ᵁ V → gm (τ t) x _ u = gm (𝟙 Y') x _ u) → ∃ v : Γ(Y, V)ˣ, pullU m V v = u := by
    intro V u hu
    have key : ∀ u : Γ(Y', m ⁻¹ᵁ V)ˣ, (∀ t x, x ∈ m ⁻¹ᵁ V → gm (τ t) x _ u = gm (𝟙 Y') x _ u) →
        ∃ a : Γ(Y, V), (m.app V).hom a = u.val := fun u hu =>
      (H V u.val (fun t h => fn_ext fun x hx => by
        rw [gs_appLE (τ t) _ _ h _ x hx, gs_unit (τ t) x (m ⁻¹ᵁ V) (h hx),
          gs_unit (𝟙 Y') x (m ⁻¹ᵁ V) hx,
          hu t x hx])).exists
    obtain ⟨a, ha⟩ := key u hu
    obtain ⟨b, hb⟩ := key u⁻¹ (fun t x hx => by rw [map_inv, map_inv, hu t x hx])
    have e : a * b = 1 := inj V (by rw [map_mul, map_one, ha, hb]; exact u.mul_inv)
    exact ⟨⟨a, b, e, (mul_comm _ _).trans e⟩, Units.ext ha⟩
  have le : ∀ j : K → M.ι, m ⁻¹ᵁ LB.wchart M ψ j ≤ LB.wchart M (fun k => m ≫ ψ k) j :=
    fun j x hx => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k
  have loc : ∀ j : K → M.ι, ∃ v : Γ(Y, LB.wchart M ψ j)ˣ, pullU m _ v = res (le j) (σ.s j) := by
    intro j
    refine descU _ _ fun t x hx => ?_
    have hx' : τ t x ∈ m ⁻¹ᵁ LB.wchart M ψ j :=
      (congrArg (fun q : Y' ⟶ Y => q x ∈ LB.wchart M ψ j) (hτ t)).mpr hx
    obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt hM x
    have this := inv t x J hJ
    have e : ∀ k, τ t ≫ m ≫ ψ k = 𝟙 Y' ≫ m ≫ ψ k := fun k => by rw [Category.id_comp, ← Category.assoc, hτ]
    have g₁ := gen_trans hσ (τ t) x (le j hx') (hJ.mem (fun k => m ≫ ψ k) (τ t))
    have g₂ := gen_trans hσ (𝟙 Y') x (le j hx) (hJ.mem (fun k => m ≫ ψ k) (𝟙 Y'))
    refine (gm_res (τ t) x (le j) hx' _).trans ((g₁.trans (Eq.trans (congrArg₂ (· * ·) ?_ this) g₂.symm)).trans
      (gm_res (𝟙 Y') x (le j) hx _).symm)
    exact congrArg (fun q : K → (Y' ⟶ X) => ∏ k, gm (q k) x (M.U (j k) ⊓ M.U (J (q k))) (M.g (j k) (J (q k))) ^ ε k)
      (funext e)
  choose v hv using loc
  refine ⟨⟨v⟩, fun i j => injU _ (unit_ext fun x hx => ?_)⟩
  have hv' : ∀ j : K → M.ι, m x ∈ LB.wchart M ψ j →
      gm (𝟙 Y' ≫ m) x _ (v j) = gm (𝟙 Y') x (LB.wchart M (fun k => m ≫ ψ k) j) (σ.s j) := fun j hj =>
    (gm_pull (𝟙 Y') m x _ hj _).symm.trans ((congrArg (gm (𝟙 Y') x _) (hv j)).trans (gm_res (𝟙 Y') x (le j) hj _))
  have hx' : (𝟙 Y' ≫ m) x ∈ LB.wchart M ψ i ⊓ LB.wchart M ψ j := hx
  refine (gm_pull (𝟙 Y') m x _ hx _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') m x _ hx _).symm)
  refine (gm_res _ x _ hx' _).trans ((hv' i hx.1).trans ((gen_trans hσ (𝟙 Y') x (le i hx.1) (le j hx.2)).trans
    (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_linComb M ψ ε (𝟙 Y' ≫ m) x i j hx'.1 hx'.2).trans ?_)
      ((gm_res _ x _ hx' _).trans (hv' j hx.2)))))))
  simp only [trF, Category.assoc]

theorem ratio_translate {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ) (n : ℕ)
    (x a y : A) (hx : x ^ n = 1) (hy : y ^ n = 1) (e : cubN θ n 1 x y = cubN θ n 1 y x) :
    cubN θ n 1 (a * y) x * (cubN θ n 1 x (a * y))⁻¹ = cubN θ n 1 a x * (cubN θ n 1 x a)⁻¹ := by
  have e₁ := GlobalTheory.UU.cubN_mul_left h n a y x
  have e₂ := h.N_add n 1 x a y
  rw [hy, h.face₂, _root_.one_mul] at e₁
  rw [hx, _root_.mul_one, h.face, _root_.one_mul, _root_.mul_one, h.s01 x, h.s12 a x] at e₂
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul e₁
  have a₂ := congrArg Additive.ofMul e₂
  have a₃ := congrArg Additive.ofMul e
  simp only [ofMul_mul, ofMul_inv] at a₁ a₂ a₃ ⊢
  linear_combination (norm := abel) a₁ - a₂ - a₃

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L)

theorem exists_sigma {T : Over S} (n : ℕ) (a x : T ⟶ A) (hx : x ^ n = 1) (φ : Fin 4 → (T.left ⟶ A.left))
    (hφ : φ = ![(a ^ n * x).left, (a ^ n).left, x.left, (1 : T ⟶ A).left]) :
    ∃ σ : LB.Gen (LB.LinComb L.L φ ![1, -1, -1, 1]), σ.IsGen ∧
      ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good L.L z J → val σ ρ.left z J =
        cubN (cubV c z J) n 1 (ρ ≫ a) (ρ ≫ x) * (cubN (cubV c z J) n 1 (ρ ≫ x) (ρ ≫ a))⁻¹ := by
  obtain ⟨t₁, g₁, v₁⟩ := exists_cubN c (1 : T ⟶ A) a x n
  obtain ⟨t₂, g₂, v₂⟩ := GlobalTheory.WeilCube.exists_gen_torsion c n x a hx
  obtain ⟨σ, hσ, hv⟩ := exists_gen L.isLB (φ' := φ) (ε' := ![1, -1, -1, 1]) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      rw [hφ, mul_comm x a]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_pow]
      abel)
    (LB.mulGen L.L _ _ _ _ t₁ (LB.invGen L.L _ _ t₂))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ g₁ (DVR.invGen_isGen _ _ _ _ g₂))
  refine ⟨σ, hσ, fun T' ρ z J hJ => ?_⟩
  rw [hv _ _ z J hJ, val_mul hJ, val_inv, v₁ T' ρ z J hJ, v₂ T' ρ z J hJ, MonObj.comp_one]

theorem main : Out.Laws → ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (L : RigLB A) (c : CubicalStr A L) (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ S) (n : ℕ), (n : K) ≠ 0 → IsFinite ((𝟙 A) ^ n : A ⟶ A).left → Flat ((𝟙 A) ^ n : A ⟶ A).left → Surjective ((𝟙 A) ^ n : A ⟶ A).left → ∀ x : Over.mk t ⟶ A, x ^ n = 1 → (∀ y : Over.mk t ⟶ A, y ^ n = 1 → GlobalTheory.UU.CubWeil c n x y 1) → Triv (Out.translDiff A L.L x) := by
  intro _ S A _ _ hA L c K _ _ t n hn h₁ h₂ h₃ x hx hp
  let T : Over S := Over.mk t
  let m : A ⊗ T ⟶ A ⊗ T := ((𝟙 A) ^ n : A ⟶ A) ▷ T
  have m₁ : m ≫ fst A T = fst A T ^ n := by
    rw [whiskerRight_fst, MonObj.comp_pow, Category.comp_id]
  have m₂ : m ≫ snd A T ≫ x = snd A T ≫ x := by rw [whiskerRight_snd_assoc]
  let ψ : Fin 4 → ((A ⊗ T).left ⟶ A.left) :=
    ![(fst A T * (snd A T ≫ x)).left, (fst A T).left, (snd A T ≫ x).left, (1 : A ⊗ T ⟶ A).left]
  obtain ⟨σ, hσ, hv⟩ := exists_sigma c n (fst A T) (snd A T ≫ x)
    (by rw [← MonObj.comp_pow, hx, MonObj.comp_one]) (fun k => m.left ≫ ψ k) (by
      funext k
      fin_cases k
      · show (m ≫ (fst A T * (snd A T ≫ x))).left = (fst A T ^ n * (snd A T ≫ x)).left
        rw [MonObj.comp_mul, m₁, m₂]
      · exact congrArg (fun q => q.left) m₁
      · exact congrArg (fun q => q.left) m₂
      · exact congrArg (fun q : A ⊗ T ⟶ A => q.left) (MonObj.comp_one m))
  obtain ⟨u, hu⟩ := descend_linComb m.left (T := {y : T ⟶ A // y ^ n = 1})
    (fun y => (lift (fst A T * (snd A T ≫ y.1)) (snd A T)).left) (fun y => by
      rw [← Over.comp_left]
      congr 1
      ext1
      · rw [Category.assoc, m₁, MonObj.comp_pow, lift_fst, mul_pow, ← MonObj.comp_pow, y.2, MonObj.comp_one,
          _root_.mul_one]
      · simp [m])
    (fun V a ha => GlobalTheory.torsion_invariant_descends_fibre S A K t n hn hA.smooth h₁ h₂ h₃ V a
      (fun y hy => ha ⟨y, hy⟩)) L.L L.isLB ψ _ σ hσ (fun y z J hJ => by
      have e₁ := hv _ (lift (fst A T * (snd A T ≫ y.1)) (snd A T)) z J hJ
      have e₂ := hv _ (𝟙 (A ⊗ T)) z J hJ
      rw [lift_fst, lift_snd_assoc] at e₁
      rw [Category.id_comp, Category.id_comp] at e₂
      have w := (hp y.1 y.2).comp (snd A T)
      have w' := w.2.2 z J hJ
      rw [map_one, map_one, _root_.one_mul] at w'
      exact e₁.trans ((ratio_translate (isCub_cubV c hJ) n _ _ _ w.1 w.2.1 w').trans e₂.symm))
  obtain ⟨g, hg⟩ := DVR.exists_gen_of_local (V := K) L.L L.isLB (![x.left, (1 : T ⟶ A).left] : Fin 2 → _) ![1, -1]
  let s : T ⊗ A ⟶ A ⊗ T := lift (snd T A) (fst T A)
  have s₀ : s.left ≫ ψ 0 = (lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left := by
    show (s ≫ (fst A T * (snd A T ≫ x))).left = ((fst T A ≫ x) * snd T A).left
    rw [MonObj.comp_mul, lift_fst, lift_snd_assoc, mul_comm]
  have s₁ : s.left ≫ ψ 1 = (snd T A).left := congrArg (fun q : T ⊗ A ⟶ A => q.left) (lift_fst _ _)
  have s₂ : s.left ≫ ψ 2 = (fst T A).left ≫ x.left := congrArg (fun q : T ⊗ A ⟶ A => q.left) (lift_snd_assoc _ _ x)
  have s₃ : s.left ≫ ψ 3 = (fst T A).left ≫ (1 : T ⟶ A).left :=
    congrArg (fun q : T ⊗ A ⟶ A => q.left) ((MonObj.comp_one s).trans (MonObj.comp_one (fst T A)).symm)
  obtain ⟨w, hw, -⟩ := exists_gen L.isLB
    (φ' := (![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left, (snd T A).left] : Fin 2 → _)) (ε' := ![1, -1])
    (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      rw [Fin.prod_univ_four, Fin.prod_univ_two, Fin.prod_univ_two]
      show h (s.left ≫ ψ 0) ^ (1 : ℤ) * h (s.left ≫ ψ 1) ^ (-1 : ℤ) * h (s.left ≫ ψ 2) ^ (-1 : ℤ) *
        h (s.left ≫ ψ 3) ^ (1 : ℤ) * (h ((fst T A).left ≫ x.left) ^ (1 : ℤ) *
        h ((fst T A).left ≫ (1 : T ⟶ A).left) ^ (-1 : ℤ)) =
        h (lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left ^ (1 : ℤ) * h (snd T A).left ^ (-1 : ℤ)
      rw [s₀, s₁, s₂, s₃]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ u s.left) (LB.pullGen L.L _ _ g (fst T A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) (DVR.pullGen_isGen _ _ _ _ hg _))
  exact ⟨w, hw⟩

end GlobalTheory.CubNondeg
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS

private lemma constFn_sub' {K : Type} [Field K] {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) (a b : K) :
    constFn q O (a - b) = constFn q O a - constFn q O b := by
  unfold constFn
  simp only [map_sub]

private lemma constFn_mul_moduli {K : Type} [Field K] {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) (a b : K) :
    constFn q O (a * b) = constFn q O a * constFn q O b := by
  unfold constFn
  simp only [map_mul]

private lemma constFn_sum {K : Type} [Field K] {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) {n : ℕ}
    (f : Fin n → K) : constFn q O (∑ k, f k) = ∑ k, constFn q O (f k) := by
  unfold constFn

  simp only [map_sum]

private lemma sum_sub_sum_mul_eq_sub_sub_sum {R : Type*} [CommRing R] {n : ℕ} (A B u v : Fin n → R) (M N : Fin n → Fin n → R) :
    ∑ a, (∑ b, A b * M b a - ∑ b, B b * N a b) * v a =
      (∑ a, A a * u a - ∑ a, B a * ∑ b, N b a * v b) - ∑ a, A a * (u a - ∑ b, M a b * v b) := by
  have h1 : ∑ a, ∑ b, A b * M b a * v a = ∑ a, ∑ b, A a * (M a b * v b) := by
    rw [Finset.sum_comm]; simp only [_root_.mul_assoc]
  have h2 : ∑ a, ∑ b, B b * N a b * v a = ∑ a, ∑ b, B a * (N b a * v b) := by
    rw [Finset.sum_comm]; simp only [_root_.mul_assoc]
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, mul_sub, Finset.mul_sum]
  rw [h1, h2]
  abel

theorem lc_row_mul_sub {K : Type} [Field K] {Y : Scheme.{0}} {I : Type} {U : I → Y.Opens} (q : Y ⟶ Sp K) {g : ℕ}
    (F Θ F' : Matrix (Fin g) (Fin g) K) (θ φ : Fin g → C1 U) (x : Fin g) :
    lc q ((F * Θ - Θ * F'.transpose) x) φ =
      (lc q (F x) θ - lc q (Θ x) (fun c => lc q (fun y => F' y c) φ)) -
        lc q (F x) (fun b => θ b - lc q (Θ b) φ) := by
  funext i j
  simp only [lc, Pi.sub_apply, Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
    constFn_sub', constFn_sum, constFn_mul_moduli]
  exact sum_sub_sum_mul_eq_sub_sub_sum (fun b => constFn q (U i ⊓ U j) (F x b)) (fun b => constFn q (U i ⊓ U j) (Θ x b))
    (fun b => θ b i j) (fun b => φ b i j) (fun a b => constFn q (U i ⊓ U j) (Θ a b))
    (fun a b => constFn q (U i ⊓ U j) (F' a b))

theorem matrix_intertwines_adjoint : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)) (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)), IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (P : Out.PolAV (Sp R)) (m : P₀.A.left ⟶ P.A.left) (L : LB P.A.left) [Finite L.ι] (D : R → K) (d : L.ι → ∀ O : P.A.left.Opens, Γ(P.A.left, O) → Γ(P₀.A.left, m ⁻¹ᵁ O)) (θ φ : Fin g → C1 (fun i => m ⁻¹ᵁ L.U i)), IsGrpPullback P₀.A P.A (spMap x₀) m → L.IsLB → (∀ i, IsAffineOpen (L.U i)) → LBIso P₀.L (L.pull m) → KSCoc P₀.A.hom P.A.hom m D L.U dd d θ → IsDlog m L dd φ → ∀ (Θ : Matrix (Fin g) (Fin g) K) (f : P.A ⟶ P.A) (f₀ f₀' : P₀.A ⟶ P₀.A) (F F' : Matrix (Fin g) (Fin g) K), (∀ b, IsCob (fun i => m ⁻¹ᵁ L.U i) (θ b - lc P₀.A.hom (Θ b) φ)) → IsMonHom f₀ → IsMonHom f₀' → f₀.left ≫ m = m ≫ f.left → LBIso (cubeLB P₀.A ![fst P₀.A P₀.A ≫ f₀, snd P₀.A P₀.A] P₀.L) (cubeLB P₀.A ![fst P₀.A P₀.A, snd P₀.A P₀.A ≫ f₀'] P₀.L) → (∀ j, IsLieComb (fun i => F i j) v (v j ≫ f₀)) → (∀ j, IsLieComb (fun i => F' i j) v (v j ≫ f₀')) → F * Θ = Θ * F'.transpose := by
  intro K _ P₀ g v dd hv hdd R _ x₀ P m L _ D d θ φ hpb hL hLaff hLB hKS hφ Θ f f₀ f₀' F F' hcob hf₀ hf₀' hfm hcube hF hF'
  have hsm : Smooth P₀.A.hom := @IsAbelianScheme.smooth _ P₀.A P₀.grp P₀.isAb
  have hA := GlobalTheory.T.kodairaSpencerClass_cohomologous_along_endomorphism K P₀.A g v dd hsm hv hdd R x₀ P.A.left P.A.hom m hpb.1 L.ι L.U D d θ f.left f₀ F hKS hf₀
    (Over.w f) hfm hF
  have hB := GlobalTheory.T.cohomology_logDerivative_adjoint_endomorphisms K P₀ g v dd hv hdd P.A.left m L φ f₀ f₀' F' hL hLB hφ hf₀ hf₀' hcube hF'
  have hI := (GlobalTheory.T.logDerivative_principalPolarisation_independent K P₀ g v dd hv hdd P.A.left m L hL hLB).2 φ hφ |>.2
  have hcov : ⨆ i, m ⁻¹ᵁ L.U i = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hL.cover]; rfl
  have hrow : ∀ x, (F * Θ - Θ * F'.transpose) x = 0 := by
    intro x
    apply hI
    rw [lc_row_mul_sub]
    refine IsCob.sub (Cohom.isCob_sub f₀.left hcov (hA x)
      (cohom_lc P₀.A.hom f₀.left (Over.w f₀) (Θ x) _ φ hB) (hcob x)) ?_
    exact isCob_lc P₀.A.hom (F x) _ hcob
  rw [← sub_eq_zero]
  ext x y
  exact congrFun (hrow x) y

end GlobalTheory.KS
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.shape_of_uniformised_theta_object : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (t : TObj g k J b (spMap em)) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (lam : Fin (2 * g) → La) (ac : J → La → La) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ), (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → (∀ j i, ∃ y, ac j (lam i) = ∑ i', Mat j i' i • lam i' + k • y) → (∀ j, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (ac j x)) ∧ ∀ y, y ≠ 0 → (hermForm Hm (F y) (F y)).re < κ * (hermForm Hm y y).re) → t.Shape Mat κ := by
  first | exact @GlobalTheory.ZM.shape_of_uniformised | exact GlobalTheory.ZM.shape_of_uniformised | (intros; apply GlobalTheory.ZM.shape_of_uniformised <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem TObj.HasTh.unit_mul {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
    {S : Scheme.{0}} {s : S ⟶ Sp o} {t : TObj g (N' ^ 2) J b s} {R : Type} [CommRing R]
    {x : Sp R ⟶ S} {v : Ix g (N' ^ 2) → R} (h : t.HasTh x v) (c : R) (hc : IsUnit c) :
    t.HasTh x (fun a => c * v a) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun p => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w, u, k1, k2, k3, k4, k5, k6, k7, k8⟩ := h3 p
  have hu : IsUnit (V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) :=
    (hc.map _).map _
  obtain ⟨u', hu'⟩ : ∃ u' : Γ((Out.overRes (T := Over.mk x) V).left, ⊤)ˣ,
      u'.val = V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) := hu
  refine ⟨V, hV, th, s1, α, τ, U, s2, w, u' * u, k1, k2, k3, k4, k5, k6, k7, fun i => ?_⟩
  have e := k8 i
  have e1 : V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c * v i)) =
      V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) *
        V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v i)) := by
    rw [map_mul]
    exact map_mul _ _ _
  refine e1.trans ?_
  rw [Units.val_mul, _root_.mul_assoc, hu']
  exact congrArg (fun y => V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * y) e

theorem exists_object_at_minimalPrime :
    ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) Mat κ w w' d, Out.Laws → Out.Laws2 → 3 ≤ N' → Odd N' → Countable o → GoodClass em C Mat κ w w' d → ∀ 𝔭 ∈ (thIdeal em C).minimalPrimes, ∃ t v, C t ∧ t.HasTh (𝟙 _) v ∧ RingHom.ker (MvPolynomial.eval₂Hom em v) = 𝔭 := by
  intro o _ g N' J b em C Mat κ w w' d hL hL2 h3 _ _ hG 𝔭 h𝔭
  classical
  obtain ⟨r, B, θ, hB, hC⟩ := hG.fam
  have : NeZero (N' ^ 2) := ⟨pow_ne_zero _ (by omega)⟩
  have hvg := fun i : {i : Fin r // (B i).Nonempty} =>
    GlobalTheory.exists_veryGeneral_point_of_holomorphic_family o em (Ix g (N' ^ 2)) d (B i) (θ i)
      (hB i).1 (hB i).2.1 i.2 (hB i).2.2.1
  choose z hz c hc hgen using hvg
  let p : {i : Fin r // (B i).Nonempty} → Ideal (MvPolynomial (Ix g (N' ^ 2)) o) := fun i =>
    RingHom.ker (MvPolynomial.eval₂Hom em (c i • θ i (z i)))
  have hobj : ∀ i, ∃ t, C t ∧ t.HasTh (𝟙 _) (c i • θ i (z i)) := by
    intro i
    obtain ⟨t, ht, hth⟩ := ((hB i).2.2.2 (z i) (hz i)).1
    exact ⟨t, ht, hth.unit_mul (c i) (hc i).isUnit⟩
  have hle : ∀ i, thIdeal em C ≤ p i := by
    intro i
    obtain ⟨t, ht⟩ := hobj i
    exact iInf_le_of_le t (iInf_le_of_le _ (iInf_le_of_le ht le_rfl))
  have hge : Finset.univ.inf p ≤ thIdeal em C := by
    refine le_iInf fun t => le_iInf fun v => le_iInf fun htv => ?_
    obtain ⟨i, z', hz', hth⟩ := hC t htv.1
    have hspan : Ideal.span (Set.range (θ i z')) = ⊤ := by
      obtain ⟨a, ha⟩ := GlobalTheory.T.thetaCosetNonvanishing_of_hasTh hL hL2 o g N' J b _ _ t N' ℂ (𝟙 _) (θ i z') ⊥ (by omega)
        dvd_rfl hth Ideal.isPrime_bot 0
      rw [Ideal.mem_bot] at ha
      exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨_, rfl⟩) (Ne.isUnit ha)
    obtain ⟨u, hu⟩ := GlobalTheory.T.thetaConstants_unique_up_to_unit hL hL2 o g N' J b _ _ t ℂ (𝟙 _) (θ i z') v hth htv.2 hspan
    have hv : v = (u : ℂ) • θ i z' := funext fun a => hu a
    intro F hF
    have hF' : F ∈ p ⟨i, z', hz'⟩ := Finset.inf_le (f := p) (Finset.mem_univ _) hF
    rw [RingHom.mem_ker, hv]
    exact hgen ⟨i, z', hz'⟩ F hF' z' hz' u u.ne_zero
  have hp : 𝔭.IsPrime := h𝔭.1.1
  obtain ⟨i, -, hi⟩ := hp.inf_le'.mp (hge.trans h𝔭.1.2)
  obtain ⟨t, ht, hth⟩ := hobj i
  refine ⟨t, _, ht, hth, le_antisymm hi ?_⟩
  exact h𝔭.2 ⟨RingHom.ker_isPrime _, hle i⟩ hi

end GlobalTheory.ZM
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.exists_join_normal_projective_models : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (I : Type) [Finite I] [Nonempty I] (R : I → Type) [∀ i, CommRing (R i)] (a : I → O) (b : ∀ i, O →+* R i) (ω : ∀ i, R i →+* F) (C : ∀ i, Cpt c t (ω i)), IsDedFrac β → (∀ i, IsDedFrac (ω i) ∧ (ω i).comp (b i) = β ∧ @IsLocalization.Away O _ (a i) (R i) _ (b i).toAlgebra) → Ideal.span (Set.range a) = ⊤ → CharZero O → ∃ (X : Scheme.{0}) (s : X ⟶ Sp O) (jQ : U ⟶ pullback s (spMap β)) (f : ∀ i, pullback s (spMap (b i)) ⟶ (C i).X), IsNormalScheme X ∧ IsProjOver s ∧ Flat s ∧ jQ ≫ pullback.snd _ _ = c ∧ IsOpenImmersion jQ ∧ Dense (Set.range jQ) ∧ ∀ i, f i ≫ (C i).s = pullback.snd _ _ ∧ (∀ g : U ⟶ pullback s (spMap (b i)), g ≫ pullback.fst _ _ = jQ ≫ pullback.fst _ _ → g ≫ f i = (C i).j) ∧ ∀ x : ↥(pullback s (spMap (b i))), f i x ∈ Set.range (C i).j → pullback.fst s (spMap (b i)) x ∈ Set.range (jQ ≫ pullback.fst s (spMap β)) := by
  first | exact @GlobalTheory.JoinModels.exists_join_scheme | exact GlobalTheory.JoinModels.exists_join_scheme | (intros; apply GlobalTheory.JoinModels.exists_join_scheme <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.sharpClass_prim_and_closed_under_tMap : (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (h : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (t : TObj g k J b (spMap em)), SharpClass W a bas em t → (IsE8 W → (W + W.transpose) * a w = W → (W + W.transpose) * a w' = W.transpose → t.Prim w w') ∧ ∀ t' : TObj g k J b (spMap em), TMap t' t (𝟙 _) → SharpClass W a bas em t' := by
  first | exact @GlobalTheory.sharpClass_prim_and_iso | exact GlobalTheory.sharpClass_prim_and_iso | (intros; apply GlobalTheory.sharpClass_prim_and_iso <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.exists_compactModel_above_fullLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N) (l : Level H) (h : l.A = N) (S e : ℕ) (β : RZ H S N →+* KA l) (b : RZ H n N →+* RZ H S N), 0 < S → n ∣ S → N ∣ S ^ e → IsInc (RZ H S N).subtype (KA l).val.toRingHom β → IsInc (RZ H n N).subtype (RZ H S N).subtype b → ∃ (C : Cpt (Xo l).s (Xo l).univ.t β) (q : C.X ⟶ T.Z) (hq : q ≫ T.s = C.s ≫ spMap b) (qm : SABMap C.t T.t q), IsFinite (pullback.lift q C.s hq) ∧ C.j ≫ q = T.a l h ∧ C.m.φ ≫ qm.φ = (T.m l h).φ ∧ IsQProjOver (C.t.G.hom ≫ C.s) := by
  first | exact @GlobalTheory.Models.Top.exists_cpt_above | exact GlobalTheory.Models.Top.exists_cpt_above | (intros; apply GlobalTheory.Models.Top.exists_cpt_above <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.exists_normal_model_above_finite_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (C : Cpt c t β) (b : O →+* O') (k : F →+* F') (r : U' ⟶ U) (hr : r ≫ c = c' ≫ spMap k) (ν : SABMap t' t r), IsDedFrac β → IsDedFrac β' → β'.comp b = k.comp β → IsNormalScheme U' → IsFinite (pullback.lift r c' hr) → ∃ C' : Cpt c' t' β', Nonempty (C'.Above C b r ν) := by
  first | exact @GlobalTheory.Models.Cpt.exists_above | exact GlobalTheory.Models.Cpt.exists_above | (intros; apply GlobalTheory.Models.Cpt.exists_above <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.relAmple_diagonal_biadditive_of_e8Form : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (S : Scheme.{0}) [IsLocallyNoetherian S] (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (G ⟶ A)) (L : LB G.left) (P : LB (G2 A).left), IsE8 W → IsAbelianScheme G → IsAbelianScheme A → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → L.IsLB → P.IsLB → (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb P (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) → LBIso L (LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → Out.RelAmple G L → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) := by
  first | exact @GlobalTheory.PowerForm.relAmple_diag | exact GlobalTheory.PowerForm.relAmple_diag | (intros; apply GlobalTheory.PowerForm.relAmple_diag <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_nonzeroCoordinate_affineChart : ∀ (R σ : Type) [CommRing R] (I : Ideal (MvPolynomial σ R)) (Z : Scheme.{0}) (s : Z ⟶ Sp R) (M : LB Z) (th : σ → M.Sec) (i : σ), ProjRep I s M th → ∃ x : Sp (MvPolynomial σ R ⧸ (I ⊔ Ideal.span {MvPolynomial.X i - 1})) ⟶ Z, IsOpenImmersion x ∧ Set.range x = (Out.nonzeroLocus (th i) : Set Z) ∧ x ≫ s = spMap ((Ideal.Quotient.mk _).comp MvPolynomial.C) ∧ SecCoord M th x (fun a => Ideal.Quotient.mk _ (MvPolynomial.X a)) := by
  first | exact @GlobalTheory.ZM.CoordChart.exists_chart | exact GlobalTheory.ZM.CoordChart.exists_chart | (intros; apply GlobalTheory.ZM.CoordChart.exists_chart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.projRep_graph_segre_coordinates_fibre : ∀ (R K σ₁ σ₂ : Type) [CommRing R] [CommRing K] [Finite σ₁] [Finite σ₂] (x : R →+* K) (I₁ : Ideal (MvPolynomial σ₁ R)) (I₂ : Ideal (MvPolynomial σ₂ R)) (Z₁ Z₂ : Over (Sp R)) (M₁ : LB Z₁.left) (M₂ : LB Z₂.left) (th₁ : σ₁ → M₁.Sec) (th₂ : σ₂ → M₂.Sec) (Y : Scheme.{0}) (s : Y ⟶ Sp K) (a₁ : Y ⟶ Z₁.left) (a₂ : Y ⟶ Z₂.left), ProjRep I₁ Z₁.hom M₁ th₁ → ProjRep I₂ Z₂.hom M₂ th₂ → IsPullback a₁ s Z₁.hom (spMap x) → a₂ ≫ Z₂.hom = s ≫ spMap x → ∃ (N : LB Y) (ty : σ₁ × σ₂ → N.Sec), ProjRep (graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂) s N ty ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (v₁ : σ₁ → T) (v₂ : σ₂ → T), SecCoord M₁ th₁ (y ≫ a₁) v₁ → SecCoord M₂ th₂ (y ≫ a₂) v₂ → SecCoord N ty y (fun i => v₁ i.1 * v₂ i.2) := by
  first | exact @GlobalTheory.ZM.GraphSegre.projRep_graph | exact GlobalTheory.ZM.GraphSegre.projRep_graph | (intros; apply GlobalTheory.ZM.GraphSegre.projRep_graph <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.lbIso_generic_spreads_out_alt : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (B : Scheme.{0}) (pB : B ⟶ Sp R) (M N : LB B), QuasiCompact pB → QuasiSeparated pB → M.IsLB → N.IsLB → LBIso (M.pull (pullback.fst pB (spMap (algebraMap R K)))) (N.pull (pullback.fst pB (spMap (algebraMap R K)))) → ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) → LBIso (M.pull (pullback.fst pB (spMap φ))) (N.pull (pullback.fst pB (spMap φ))) := by
  first | exact @GlobalTheory.lbIso_generic_spreads_out | exact GlobalTheory.lbIso_generic_spreads_out | (intros; apply GlobalTheory.lbIso_generic_spreads_out <;> assumption)
end
