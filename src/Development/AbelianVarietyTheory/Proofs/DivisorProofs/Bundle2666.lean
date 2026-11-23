module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2630
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle821
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle157
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle060
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExOfHodgeWt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDeterminantLinearisationEquivariantPullback
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorInvLePowHolomorphicOrbitPeriodBound
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.LinearAlgebra.Basis.Bilinear
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings

@[expose] public section

section

open GlobalTheory.MonoHom

noncomputable section

namespace GlobalTheory.PerRoot

variable {X : Type} [AddCommGroup X]

def halfForm {r : ℕ} (e : Module.Basis (Fin r) ℤ X) (i j : Fin r) : LinearMap.BilinForm ℤ X :=
  if i < j then pform e i j + pform e j i else if i = j then pform e i i else 0

theorem halfForm_symm {r : ℕ} (e : Module.Basis (Fin r) ℤ X) (i j : Fin r) (x y : X) :
    halfForm e i j x y = halfForm e i j y x := by
  unfold halfForm; split_ifs <;> simp [pform_apply] <;> ring

theorem halfForm_basis {r : ℕ} (e : Module.Basis (Fin r) ℤ X) (i j i₀ j₀ : Fin r) :
    halfForm e i j (e i₀) (e j₀) = if i = min i₀ j₀ ∧ j = max i₀ j₀ then 1 else 0 := by
  unfold halfForm
  rcases lt_trichotomy i₀ j₀ with h | rfl | h
  · rw [min_eq_left h.le, max_eq_right h.le]
    split_ifs <;> simp [pform_apply, Module.Basis.coord_apply, Finsupp.single_apply] <;> (try split_ifs) <;> (try subst_vars) <;> omega
  · simp only [min_self, max_self]
    split_ifs <;> simp [pform_apply, Module.Basis.coord_apply, Finsupp.single_apply] <;> (try split_ifs) <;> (try subst_vars) <;> omega
  · rw [min_eq_right h.le, max_eq_left h.le]
    split_ifs <;> simp [pform_apply, Module.Basis.coord_apply, Finsupp.single_apply] <;> (try split_ifs) <;> (try subst_vars) <;> omega

theorem eq_sum_halfForm {r : ℕ} (e : Module.Basis (Fin r) ℤ X) (β : LinearMap.BilinForm ℤ X)
    (hβ : ∀ x y, β x y = β y x) :
    β = ∑ p : Fin r × Fin r, β (e p.1) (e p.2) • halfForm e p.1 p.2 := by
  refine LinearMap.ext_basis e e fun i₀ j₀ => ?_
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, halfForm_basis, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (min i₀ j₀, max i₀ j₀)]
  · simp only [and_self, if_true]
    rcases le_total i₀ j₀ with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h, hβ]
  · intro p _ hp; rw [if_neg]; rintro ⟨h1, h2⟩; exact hp (Prod.ext h1 h2)
  · intro h; exact absurd (Finset.mem_univ _) h

theorem bimul_ext {G : Type} [CommGroup G] {r : ℕ} (e : Module.Basis (Fin r) ℤ X) (f g : X → X → G)
    (hf : ∀ a a' b, f (a + a') b = f a b * f a' b) (hf' : ∀ a b b', f a (b + b') = f a b * f a b')
    (hg : ∀ a a' b, g (a + a') b = g a b * g a' b) (hg' : ∀ a b b', g a (b + b') = g a b * g a b')
    (h : ∀ i j, f (e i) (e j) = g (e i) (e j)) : f = g := by
  have key : ∀ (φ ψ : X → G), (∀ a a', φ (a + a') = φ a * φ a') → (∀ a a', ψ (a + a') = ψ a * ψ a') →
      (∀ i, φ (e i) = ψ (e i)) → φ = ψ := by
    intro φ ψ hφ hψ hi
    let Φ : X →+ Additive G := AddMonoidHom.mk' (fun a => Additive.ofMul (φ a)) (fun a a' => by simp [hφ])
    let Ψ : X →+ Additive G := AddMonoidHom.mk' (fun a => Additive.ofMul (ψ a)) (fun a a' => by simp [hψ])
    have hL : Φ.toIntLinearMap = Ψ.toIntLinearMap := e.ext fun i => by simp [Φ, Ψ, hi]
    funext a
    have := congrArg (fun L : X →ₗ[ℤ] Additive G => Additive.toMul (L a)) hL
    simpa [Φ, Ψ] using this
  have h1 : ∀ j a, f a (e j) = g a (e j) := fun j => congrFun
    (key (fun a => f a (e j)) (fun a => g a (e j)) (fun a a' => hf a a' _) (fun a a' => hg a a' _) (fun i => h i j))
  funext a
  exact key (f a) (g a) (hf' a) (hg' a) (fun j => h1 j a)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def IsSymBasis (ε : ι → LinearMap.BilinForm ℤ X) : Prop :=
  (∀ k x y, ε k x y = ε k y x) ∧ LinearIndependent ℤ ε ∧
    ∀ β : LinearMap.BilinForm ℤ X, (∀ x y, β x y = β y x) → β ∈ Submodule.span ℤ (Set.range ε)

theorem exists_coords {ε : ι → LinearMap.BilinForm ℤ X} (hε : IsSymBasis ε) {r : ℕ} (e : Module.Basis (Fin r) ℤ X) :
    ∃ c : Fin r × Fin r → ι → ℤ, ∀ p, ∑ k, c p k • ε k = halfForm e p.1 p.2 := by
  have : ∀ p : Fin r × Fin r, ∃ c : ι → ℤ, ∑ k, c k • ε k = halfForm e p.1 p.2 := fun p =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).1 (hε.2.2 _ (halfForm_symm e p.1 p.2))
  choose c hc using this
  exact ⟨c, hc⟩

theorem dual_coords {ε : ι → LinearMap.BilinForm ℤ X} (hε : IsSymBasis ε) {r : ℕ} (e : Module.Basis (Fin r) ℤ X)
    {c : Fin r × Fin r → ι → ℤ} (hc : ∀ p, ∑ k, c p k • ε k = halfForm e p.1 p.2) (k' k : ι) :
    ∑ p, ε k' (e p.1) (e p.2) * c p k = if k' = k then 1 else 0 := by
  have h1 : ε k' = ∑ k, (∑ p, ε k' (e p.1) (e p.2) * c p k) • ε k := by
    conv_lhs => rw [eq_sum_halfForm e (ε k') (hε.1 k')]
    simp_rw [← hc, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have h2 : ε k' = ∑ k, (if k' = k then (1 : ℤ) else 0) • ε k := by simp
  have h3 : ∑ k, ((∑ p, ε k' (e p.1) (e p.2) * c p k) - (if k' = k then 1 else 0)) • ε k = 0 := by
    simp_rw [sub_smul, Finset.sum_sub_distrib, ← h1, ← h2, sub_self]
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hε.2.1 _ h3 k)

variable {G : Type} [CommGroup G]

theorem zpow_sumF {κ : Type} (s : Finset κ) (a : G) (f : κ → ℤ) : a ^ (∑ p ∈ s, f p) = ∏ p ∈ s, a ^ f p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, zpow_add, ih]

theorem eq_one_of_prod_zpow {ε : ι → LinearMap.BilinForm ℤ X} (hε : IsSymBasis ε) [Module.Free ℤ X] [Module.Finite ℤ X]
    (u : ι → G) (h : ∀ x y, ∏ k, u k ^ ε k x y = 1) (k : ι) : u k = 1 := by
  let e := Module.finBasis ℤ X
  obtain ⟨c, hc⟩ := exists_coords hε e
  calc u k = ∏ k', u k' ^ (if k' = k then (1 : ℤ) else 0) := by simp
    _ = ∏ k', u k' ^ (∑ p, ε k' (e p.1) (e p.2) * c p k) := by simp_rw [dual_coords hε e hc]
    _ = ∏ p, (∏ k', u k' ^ ε k' (e p.1) (e p.2)) ^ c p k := by
      simp_rw [← Finset.prod_zpow, zpow_sumF, ← zpow_mul]
      exact Finset.prod_comm
    _ = 1 := by simp [h]

theorem existsUnique_coeff {ε : ι → LinearMap.BilinForm ℤ X} (hε : IsSymBasis ε) [Module.Free ℤ X] [Module.Finite ℤ X]
    (q : X → X → G) (hsym : ∀ x y, q x y = q y x) (hadd : ∀ x x' y, q (x + x') y = q x y * q x' y) :
    ∃! σ : ι → G, ∀ x y, q x y = ∏ k, σ k ^ ε k x y := by
  let e := Module.finBasis ℤ X
  obtain ⟨c, hc⟩ := exists_coords hε e
  have hadd' : ∀ x y y', q x (y + y') = q x y * q x y' := fun x y y' => by
    rw [hsym, hadd, hsym y, hsym y']
  have hF : ∀ x y, ∏ k, (∏ p, q (e p.1) (e p.2) ^ c p k) ^ ε k x y =
      ∏ p : Fin (Module.finrank ℤ X) × Fin (Module.finrank ℤ X), q (e p.1) (e p.2) ^ halfForm e p.1 p.2 x y := by
    intro x y
    simp_rw [← Finset.prod_zpow, ← zpow_mul]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← zpow_sumF, ← hc p]
    simp [LinearMap.sum_apply, mul_comm]
  refine ⟨fun k => ∏ p, q (e p.1) (e p.2) ^ c p k, fun x y => ?_, fun σ hσ => funext fun k => ?_⟩
  · rw [hF]
    have := bimul_ext e q (fun x y => ∏ p : Fin (Module.finrank ℤ X) × Fin (Module.finrank ℤ X),
        q (e p.1) (e p.2) ^ halfForm e p.1 p.2 x y) hadd hadd'
      (fun a a' b => by simp only [map_add (f := _), LinearMap.add_apply, zpow_add, Finset.prod_mul_distrib])
      (fun a b b' => by simp only [map_add (f := _), zpow_add, Finset.prod_mul_distrib])
      (fun i j => by
        simp only [halfForm_basis]
        rw [Finset.prod_eq_single (min i j, max i j)]
        · simp only [and_self, if_true, zpow_one]
          rcases le_total i j with h | h
          · rw [min_eq_left h, max_eq_right h]
          · rw [min_eq_right h, max_eq_left h, hsym]
        · intro p _ hp; rw [if_neg, zpow_zero]; rintro ⟨h1, h2⟩; exact hp (Prod.ext h1 h2)
        · intro h; exact absurd (Finset.mem_univ _) h)
    exact congrFun (congrFun this x) y
  · have h0 : ∀ x y, ∏ k, (σ k / ∏ p, q (e p.1) (e p.2) ^ c p k) ^ ε k x y = 1 := fun x y => by
      simp_rw [div_zpow, Finset.prod_div_distrib, ← hσ, hF]
      rw [div_eq_one]
      have := bimul_ext e q (fun x y => ∏ p : Fin (Module.finrank ℤ X) × Fin (Module.finrank ℤ X),
          q (e p.1) (e p.2) ^ halfForm e p.1 p.2 x y) hadd hadd'
        (fun a a' b => by simp only [map_add (f := _), LinearMap.add_apply, zpow_add, Finset.prod_mul_distrib])
        (fun a b b' => by simp only [map_add (f := _), zpow_add, Finset.prod_mul_distrib])
        (fun i j => by
          simp only [halfForm_basis]
          rw [Finset.prod_eq_single (min i j, max i j)]
          · simp only [and_self, if_true, zpow_one]
            rcases le_total i j with h | h
            · rw [min_eq_left h, max_eq_right h]
            · rw [min_eq_right h, max_eq_left h, hsym]
          · intro p _ hp; rw [if_neg, zpow_zero]; rintro ⟨h1, h2⟩; exact hp (Prod.ext h1 h2)
          · intro h; exact absurd (Finset.mem_univ _) h)
      exact congrFun (congrFun this x) y
    exact div_eq_one.1 (eq_one_of_prod_zpow hε _ h0 k)

theorem eq_of_prod_zpow {ε : ι → LinearMap.BilinForm ℤ X} (hε : IsSymBasis ε) [Module.Free ℤ X] [Module.Finite ℤ X]
    (s s' : ι → G) (h : ∀ x y, ∏ k, s k ^ ε k x y = ∏ k, s' k ^ ε k x y) : s = s' := by
  funext k
  refine div_eq_one.1 (eq_one_of_prod_zpow hε (fun k => s k / s' k) (fun x y => ?_) k)
  simp_rw [div_zpow, Finset.prod_div_distrib, h, div_self']

theorem pow_eq_pow_of_prod {ε : ι → LinearMap.BilinForm ℤ X} (hε : IsSymBasis ε) [Module.Free ℤ X] [Module.Finite ℤ X]
    (n : ℕ) (s s' : ι → G) (h : ∀ x y, ∏ k, s k ^ ((n : ℤ) * ε k x y) = ∏ k, s' k ^ ((n : ℤ) * ε k x y)) (k : ι) :
    s k ^ n = s' k ^ n := by
  have := congrFun (eq_of_prod_zpow hε (fun k => s k ^ n) (fun k => s' k ^ n) fun x y => by
    simp_rw [← zpow_natCast, ← zpow_mul]; exact h x y) k
  exact this

theorem isSymBasis_mul : IsSymBasis (fun _ : Fin 1 => (LinearMap.mul ℤ ℤ : LinearMap.BilinForm ℤ ℤ)) := by
  refine ⟨fun _ x y => mul_comm x y, ?_, fun β _ => ?_⟩
  · rw [linearIndependent_unique_iff]
    intro h
    have := LinearMap.congr_fun₂ h 1 1
    simp at this
  · refine (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨fun _ => β 1 1, ?_⟩
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    simp only [Finset.univ_unique, Finset.sum_singleton, LinearMap.smul_apply, LinearMap.mul_apply', smul_eq_mul]
    have hx : x = x • (1 : ℤ) := by simp
    have hy : y = y • (1 : ℤ) := by simp
    rw [hx, hy, LinearMap.map_smul₂, LinearMap.map_smul]
    simp only [smul_eq_mul]; ring

end GlobalTheory.PerRoot
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

noncomputable section

namespace GlobalTheory.UPoinc.USum

theorem exists_isTwVal_of_subsingleton : ∀ {B : Scheme.{0}} (P : PolAV B) (N m : ℕ) {T₀ T : Over B} (θ : LB.Sec (LPow P.A P.L 1 T₀)) {z₀ : T₀ ⟶ P.A} (τ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => z₀.left) (fun _ => 1))) (β : T ⟶ T₀) (x h : T ⟶ P.A), Subsingleton T.left → Odd m → N = m ^ 2 → τ.IsGen → x ^ N = 1 → h ^ m = β ≫ z₀ → ∃ v, IsTwVal P N m θ τ β x h v := by
  intro B P N m T₀ T θ z₀ τ β x h hT hm hN hτ hx hh
  subst hN
  have hG := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have hL := P.isLB
  obtain ⟨α, hα⟩ : ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left]
      ![((m ^ 2 : ℕ) : ℤ), -1]), α.IsGen := by
    rw [Nat.cast_pow]
    exact GlobalTheory.EmbLocal.exists_mulPull hG P m T
  obtain ⟨U, hU⟩ : ∃ U : ThetaGrp P.A P.L ((m ^ 2 : ℕ) : ℤ) T, SymLift P.A P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x U := by
    rcases isEmpty_or_nonempty T.left with he | ⟨⟨p⟩⟩
    · exact GlobalTheory.GlobalLift.exists_symLift_empty hL (m ^ 2) x
    · obtain ⟨V, hV, H⟩ := GlobalTheory.EmbLocal.exists_symLift_near hG P (k := m ^ 2) hm.pow x hx p
      obtain ⟨θ', hθ'⟩ := H T (𝟙 T) (by
        rintro _ ⟨q, rfl⟩
        rwa [Subsingleton.elim ((𝟙 T : T ⟶ T).left q) p])
      rw [Category.id_comp] at hθ'
      exact ⟨θ', hθ'⟩
  rcases U with ⟨pt, φU, hφU⟩
  obtain rfl : x = pt := hU.pt_eq.symm
  obtain ⟨s, hs⟩ := GlobalTheory.VVRank.exists_isTwistPull P.A (ψ := mulT P.A T m) (m := snd T P.A ^ m) (hm := lift_snd _ _)
    (a := ((m ^ 2 : ℕ) : ℤ)) (b := 1) hL hα (GlobalTheory.VVRank.pullS P.A 1 β θ)
  obtain ⟨σ, hσ⟩ := GlobalTheory.VVRank.exists_isTwistPull P.A (ψ := translT P.A x) (m := translPt P.A x)
    (hm := lift_snd _ _) hL hφU s
  have e₁ : (ptSecT P.A h).left ≫ (snd T P.A).left = h.left := GlobalTheory.ThetaPtMove.ptSecT_snd h
  have e₂ : (ptSecT P.A h).left ≫ (snd T P.A ^ m).left = (h ^ m).left := by
    rw [← Over.comp_left, MonObj.comp_pow, GlobalTheory.ThetaCompare.pt_snd]
  have e₃ : β.left ≫ z₀.left = (h ^ m).left := by rw [← Over.comp_left, hh]
  obtain ⟨τ', hτ', vτ'⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hL (φ' := fun _ : Fin 1 => h.left)
    (ε' := fun _ => ((m ^ 2 : ℕ) : ℤ))
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fin.prod_univ_one,
        Matrix.cons_val_zero, Matrix.cons_val_one, e₁, e₂, e₃, zpow_neg, zpow_one]
      group)
    (LB.mulGen P.L _ _ _ _ (LB.pullGen P.L _ _ α (ptSecT P.A h).left) (LB.pullGen P.L _ _ τ β.left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _) (DVR.pullGen_isGen _ _ _ _ hτ _))
  obtain ⟨v, hv⟩ := GlobalTheory.ThetaPtExist.exists_isValueAt hL σ h τ' hτ'
  refine ⟨v, α, ⟨x, φU, hφU⟩, hα, hU, fun Z r z J hJ => ?_⟩
  have q1 := GlobalTheory.ThetaPtMove.sv_of_isValueAt hv r z hJ
  have q2 := GlobalTheory.VVRank.sv_of_isTwistPull P.A hσ (r ≫ (ptSecT P.A h).left) z hJ
  have q3 := GlobalTheory.VVRank.sv_of_isTwistPull P.A hs (r ≫ (ptSecT P.A (x * h)).left) z hJ
  have q4 := GlobalTheory.VVRank.sv_pullS P.A 1 β θ (r ≫ (ptSecT P.A ((x * h) ^ m)).left) z hJ
  rw [Category.assoc, GlobalTheory.ThetaCompare.pt_translT] at q2
  rw [Category.assoc, GlobalTheory.ThetaCompare.pt_mulT] at q3
  rw [vτ' Z r z J hJ, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_mul hJ, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull hJ,
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull hJ] at q1
  rw [← q1, q2, q3, q4, Units.val_mul, Category.assoc, _root_.mul_assoc]
  rfl

end GlobalTheory.UPoinc.USum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

namespace GlobalTheory.UPoinc.USum


open GlobalTheory.ThetaCompare GlobalTheory.CommPairing in
theorem isTwVal_transl : ∀ {B : Scheme.{0}} (P : PolAV B) (N m : ℕ) {T₀ T : Over B} (θ : LB.Sec (LPow P.A P.L 1 T₀)) {z₀ : T₀ ⟶ P.A} (τ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => z₀.left) (fun _ => 1))) (β : T ⟶ T₀) (x h : T ⟶ P.A) (v : Γ(T.left, ⊤)) (k : T ⟶ P.A), k ^ m = 1 → WeilIs P.A P.L N x k 1 → IsTwVal P N m θ τ β x h v → IsTwVal P N m θ τ β x (h * k) v := by
  intro B P N m T₀ T θ z₀ τ β x h v k hk hw H
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have := P.isAb.comm
  obtain ⟨α, U, hα, hU, H⟩ := H
  refine ⟨α, U, hα, hU, fun Z r z J hJ => ?_⟩
  have e₀ : (translT P.A k).left ≫ (snd T P.A).left = (translPt P.A k).left := by
    rw [← Over.comp_left, translT, lift_snd]
  have e₁ : (translT P.A k).left ≫ (snd T P.A ^ m).left = (snd T P.A ^ m).left := by
    rw [← Over.comp_left, SymLiftOdd.comp_pow', translT, lift_snd,
      show translPt P.A k = (fst T P.A ≫ k) * snd T P.A from rfl, mul_pow, ← SymLiftOdd.comp_pow', hk,
      MonObj.comp_one, _root_.one_mul]
  obtain ⟨d, hd, hv⟩ := exists_gen P.isLB (K' := Fin 2) (φ' := ![(snd T P.A).left, (translPt P.A k).left])
    (ε' := ![(N : ℤ), -(N : ℤ)]) (fun V _ g => by
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
        Matrix.cons_val_one, e₀, e₁, neg_neg, zpow_neg, zpow_one, _root_.mul_assoc]
      rw [inv_inv, mul_left_comm (g (snd T P.A ^ m).left)⁻¹, inv_mul_cancel, _root_.mul_one])
    (LB.mulGen P.L _ _ _ _ α (LB.invGen P.L _ _ (LB.pullGen P.L _ _ α (translT P.A k).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hα (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _)))
  let D : ThetaGrp P.A P.L N T := ⟨k, d, hd⟩
  have hD : ∀ s : Z ⟶ (T ⊗ P.A).left,
      tval D s z J = val α s z J * (val α (s ≫ (translT P.A k).left) z J)⁻¹ := fun s =>
    (hv Z s z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg (val α s z J * ·)
      ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _)))))
  have hx : U.pt = x := hU.pt_eq
  have hc : CommIsOf P.A P.L N U D 1 :=
    (GlobalLift.weilIs_iff_commIsOf hG P.isAb P.isLB U D 1).1 (hx ▸ hw)
  have q := val_corr hJ hc (r ≫ (ptSecT P.A h).left)
  have q₁ : val (constGen P.A P.L (1 : Γ(T.left, ⊤)ˣ)) (r ≫ (ptSecT P.A h).left) z J = 1 := by
    refine ((gm_res _ z le_top (Set.mem_iInter.2 fun k => k.elim) _).trans
      (gm_pull _ (fst T P.A).left z ⊤ trivial 1)).trans (map_one _)
  have q₂ : tval U (r ≫ (ptSecT P.A h).left) z J * tval D ((r ≫ (ptSecT P.A h).left) ≫ (translT P.A U.pt).left) z J =
      tval D (r ≫ (ptSecT P.A h).left) z J * tval U ((r ≫ (ptSecT P.A h).left) ≫ (translT P.A k).left) z J * 1 :=
    ((val_mul hJ _ _ _).trans (congrArg (_ * ·) (val_pull hJ _ _ _))).symm.trans (q.trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg (_ * ·) (val_pull hJ _ _ _))) q₁)))
  simp only [hD, Category.assoc, pt_translT, hx, _root_.mul_one] at q₂
  have p₁ : (x * (h * k)) ^ m = (x * h) ^ m := by
    rw [← _root_.mul_assoc, mul_pow, hk, _root_.mul_one]
  have p₂ : k * (x * h) = x * (h * k) := by rw [mul_comm k, _root_.mul_assoc]
  rw [p₂, mul_comm k h] at q₂
  rw [p₁]
  have H' := H Z r z J hJ
  set a₁ := val α (r ≫ (ptSecT P.A h).left) z J
  set a₂ := val α (r ≫ (ptSecT P.A (h * k)).left) z J
  set a₃ := val α (r ≫ (ptSecT P.A (x * h)).left) z J
  set a₄ := val α (r ≫ (ptSecT P.A (x * (h * k))).left) z J
  set u₁ := tval U (r ≫ (ptSecT P.A h).left) z J
  set u₂ := tval U (r ≫ (ptSecT P.A (h * k)).left) z J
  set t := val τ (r ≫ β.left) z J
  have f₁ : a₂ * t = (a₂ * a₁⁻¹) * (a₁ * t) := by
    rw [_root_.mul_assoc, inv_mul_cancel_left]
  have f₂ : u₂ * a₄ = (a₂ * a₁⁻¹) * (u₁ * a₃) := by
    apply Additive.ofMul.injective
    replace q₂ := congrArg Additive.ofMul q₂
    simp only [ofMul_mul, ofMul_inv] at q₂ ⊢
    linear_combination (norm := module) -q₂
  rw [f₁, f₂, Units.val_mul _ (a₁ * t), Units.val_mul _ (u₁ * a₃), mul_left_comm, H', _root_.mul_assoc]

end GlobalTheory.UPoinc.USum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UPoinc.USum

theorem ptSecT_comp_whisker {B : Scheme.{0}} {A : Over B} [GrpObj A] {T T' : Over B} (c : T' ⟶ T) (y : T ⟶ A) :
    (ptSecT A (c ≫ y)).left ≫ (c ▷ A).left = c.left ≫ (ptSecT A y).left := by
  rw [← Over.comp_left, ← Over.comp_left, ptSecT, ptSecT, lift_whiskerRight, comp_lift, Category.id_comp,
    Category.comp_id]

theorem isTwVal_pull {B : Scheme.{0}} (P : PolAV B) (N m : ℕ) {T₀ T : Over B} (θ : LB.Sec (LPow P.A P.L 1 T₀))
    {z₀ : T₀ ⟶ P.A} (τ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => z₀.left) (fun _ => 1)))
    (β : T ⟶ T₀) (x h : T ⟶ P.A) (v : Γ(T.left, ⊤)) {T' : Over B} (c : T' ⟶ T) :
    IsTwVal P N m θ τ β x h v → IsTwVal P N m θ τ (c ≫ β) (c ≫ x) (c ≫ h) (c.left.appTop.hom v) := by
  rintro ⟨α, U, hα, hU, H⟩
  obtain ⟨α', hα', vα⟩ := GlobalTheory.VVRank.exists_gen_pullTo
    (φ' := ![(snd T' P.A).left, (snd T' P.A ^ m).left]) α hα (c ▷ P.A).left (fun k => by
      fin_cases k
      · exact GlobalTheory.VVRank.whisker_snd_left P.A c
      · change (c ▷ P.A).left ≫ (snd T P.A ^ m).left = (snd T' P.A ^ m).left
        rw [← Over.comp_left, MonObj.comp_pow, whiskerRight_snd])
  obtain ⟨U', hU', vU⟩ := GlobalTheory.SymLiftGlobal.exists_symLift_pull_val P.isLB c hU
  refine ⟨α', U', hα', hU', fun Z r z J hJ => ?_⟩
  have eq₁ : (c ≫ x) * (c ≫ h) = c ≫ (x * h) := (MonObj.comp_mul _ _ _).symm
  have q := H Z (r ≫ c.left) z J hJ
  have g : gs r z ⊤ (c.left.appTop.hom v) = gs (r ≫ c.left) z ⊤ v := gs_pull r c.left z ⊤ trivial v
  have w : ∀ (y : T ⟶ P.A) {W : Scheme.{0}} (k : (T ⊗ P.A).left ⟶ W),
      (ptSecT P.A (c ≫ y)).left ≫ (c ▷ P.A).left ≫ k = c.left ≫ (ptSecT P.A y).left ≫ k := fun y W k => by
    rw [← Category.assoc, ptSecT_comp_whisker, Category.assoc]
  have eq₃ : (c ≫ (x * h)) ^ m = c ≫ (x * h) ^ m := (MonObj.comp_pow _ _ _).symm
  rw [g, vα _ _ z J hJ, vα _ _ z J hJ, vU _ _ z J hJ, eq₁, eq₃]
  simp only [Category.assoc, ptSecT_comp_whisker, comp_whiskerRight, Over.comp_left, w]
  simpa only [Category.assoc] using q

end GlobalTheory.UPoinc.USum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UnifTorsK.psiNormAt_pull : ∀ (p : ℕ) [Fact p.Prime] (V V' : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V'] [Algebra (FractionRing V) (PadicAlgCl p)] [Algebra (FractionRing V') (PadicAlgCl p)] (φ : V →+* V'), (∀ v : V, algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V _ v) = algebraMap (FractionRing V') (PadicAlgCl p) (algebraMap V' _ (φ v))) → (∀ v : V', ‖algebraMap (FractionRing V') (PadicAlgCl p) (algebraMap V' _ v)‖ ≤ 1) → ∀ (D : DegPre V) (D' : DegPre V') (hD : IsPullDeg φ D D') (χ : D'.X) (r : ℝ), GlobalTheory.UnifTorsK.PsiNormAt p D (hD.xe χ) r ↔ GlobalTheory.UnifTorsK.PsiNormAt p D' χ r := by
  intro p _ V V' _ _ _ _ _ _ _ _ φ hφ hn D D' hD χ r
  have key := GlobalTheory.T.norm_psi_pull_localRingsOfIntegers p V V' φ hφ hn D D' hD χ
  refine ⟨fun H j' hj' => ?_, fun H j hj => ?_⟩
  · obtain ⟨i, hi⟩ := exists_chart D.P.isLB ((D.c (hD.xe χ)).left (IsLocalRing.closedPoint V))
    have hi' := ((IsLocalRing.closedPoint_mem_iff (R := V) ((D.c (hD.xe χ)).left ⁻¹ᵁ D.P.L.U i)).1 hi).ge
    exact (key i (j' PUnit.unit) hi' hj').trans (H (fun _ => i) hi')
  · obtain ⟨i, hi⟩ := exists_chart D'.P.isLB ((D'.c χ).left (IsLocalRing.closedPoint V'))
    have hi' := ((IsLocalRing.closedPoint_mem_iff (R := V') ((D'.c χ).left ⁻¹ᵁ D'.P.L.U i)).1 hi).ge
    exact (key (j PUnit.unit) i hj hi').symm.trans (H (fun _ => i) hi')
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

theorem _root_.GlobalTheory.T.lieDeterminant_linearisation_equivariant_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] (φ₀ : c.F →+* (X₀ TF.Y Z).functionField) (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι)) (a : (E →+* ℂ) → ℤ) (D : CartierDiv (X₀ TF.Y Z)), (show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ s₀ TF.Y Z = spMap φ₀ → GlobalTheory.HodgeLin.DetEqns TF Z φ₀ f₀ a D → ∀ (Γ : Type) [Group Γ] (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ρ' : Γ →* Aut X'), IsDominant φ → (∀ γ, (ρ' γ).asIso.hom ≫ φ ≫ s₀ TF.Y Z = φ ≫ s₀ TF.Y Z) → ∀ (G' : Over X') [GrpObj G'] (ψ : G'.left ⟶ TF.Y.t.G.left) (act' : OAct (𝓞 E) G') (m : Γ → (G'.left ⟶ G'.left)), GlobalTheory.HodgeLin.EqvLin TF.Y.t (φ ≫ (barComp TF.Y Z).ι) ρ' G' ψ act' m → RatLin ρ' ((toLB D).pull φ) (LB.isLB_pull (isLB_toLB D) φ) := by
  first | exact @GlobalTheory.HodgeLin.ratLin_pull | exact GlobalTheory.HodgeLin.ratLin_pull | (intros; apply GlobalTheory.HodgeLin.ratLin_pull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

theorem _root_.GlobalTheory.T.normFactor_inv_le_pow_holomorphicOrbit_periodBound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (x : ℂ → Frame X.Ψ N) (la : Wt X.Ψ N) (n : ℕ) (v : Fin n → Fin N → E) (Lp : Fin n → X.Ψ → Fin (N - X.p0) → ℂ) (Lm : Fin n → X.Ψ → Fin X.p0 → ℂ), IsOrbit X T M γ x → ((∀ j (τ : X.Ψ) (i : Fin (N - X.p0)), Tendsto (fun w => perFr X (x w) (v j) τ.1 i) imTop (𝓝 (Lp j τ i))) ∧ (∀ j (τ : X.Ψ) (i : Fin X.p0), Tendsto (fun w => perFr X (x w) (v j) (conjEmb τ.1) i) imTop (𝓝 (Lm j τ i))) ∧ ∀ τ : X.Ψ, Submodule.span ℂ (Set.range fun j => Lp j τ) = ⊤ ∧ Submodule.span ℂ (Set.range fun j => Lm j τ) = ⊤) → (∀ (u : Fin N → E) (R : ℝ), ∃ (C : ℝ) (B : ℕ), ∀ᶠ w in imTop, |w.re| ≤ R → ∀ (ρ : E →+* ℂ) (i : ℕ), ‖perFr X (x w) u ρ i‖ ≤ C * w.im ^ B) → ∃ (C : ℝ) (B : ℕ), ∀ᶠ w in imTop, 0 < X.nfac la (x w) ∧ (X.nfac la (x w))⁻¹ ≤ C * w.im ^ B := by
  first | exact @GlobalTheory.nfac_inv_le_pow_of_isOrbit_of_perBound | exact GlobalTheory.nfac_inv_le_pow_of_isOrbit_of_perBound | (intros; apply GlobalTheory.nfac_inv_le_pow_of_isOrbit_of_perBound <;> assumption)
end
