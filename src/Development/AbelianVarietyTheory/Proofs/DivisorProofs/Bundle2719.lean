module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsChartOfMemRedKer
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2653
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2635
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle669
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2648
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2649
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeClassSumsOfTermsPrescribedNorms
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2654
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle686
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle821

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
open GlobalTheory.TangentOrigin


theorem _root_.GlobalTheory.T.existsUnique_lieBasis_coeffs_of_derivation_affineOpen : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {n : ℕ} (v : Fin n → (epsR R ⟶ G)), IsLieBasis v → ∀ (dd : Fin n → Fld G.left),
    (∀ (B : Type) [CommRing B] [Algebra R B] (e : Fin n → B) (he : ∀ i j, e i * e j = 0) (z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ G) (O : G.left.Opens) (h : ⊤ ≤ z.left ⁻¹ᵁ O),
      ∃ h' : ⊤ ≤ (GlobalTheory.SqZero.lieExp v e (fun i => he i i) * z).left ⁻¹ᵁ O, ∀ f,
        GlobalTheory.TangentOrigin.evalPt _ O h' f = GlobalTheory.TangentOrigin.evalPt z.left O h f + ∑ i, e i * GlobalTheory.TangentOrigin.evalPt z.left O h (dd i O f)) →
    ∀ (V V' : G.left.Opens), IsAffineOpen V → IsAffineOpen V' → V' ≤ V → ∀ (δ : Γ(G.left, V) → Γ(G.left, V')),
    (∀ f f', δ (f + f') = δ f + δ f') → (∀ f f', δ (f * f') = rsT f V' * δ f' + rsT f' V' * δ f) →
    (∀ r, δ (constFn G.hom V r) = 0) →
    ∃! c : Fin n → Γ(G.left, V'), ∀ f, δ f = ∑ a, c a * rsT (dd a V f) V' := by
  first | exact @GlobalTheory.VertCoeffRing.existsUnique_coeff_affine_ring | exact GlobalTheory.VertCoeffRing.existsUnique_coeff_affine_ring | (intros; apply GlobalTheory.VertCoeffRing.existsUnique_coeff_affine_ring <;> assumption)
end

section

open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc.Gap

section Bound

variable {X : Type} [AddCommGroup X] {m : ℕ} {a : Fin m → X}

theorem exists_abs_apply_le (ha : Submodule.span ℤ (Set.range a) = ⊤) (x y : X) :
    ∃ C : ℕ, ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) → (∀ y, 0 ≤ β y y) →
      |β x y| ≤ C * ∑ i, β (a i) (a i) := by
  have hx : x ∈ Submodule.span ℤ (Set.range a) := ha ▸ Submodule.mem_top
  have hy : y ∈ Submodule.span ℤ (Set.range a) := ha ▸ Submodule.mem_top
  have hl : ∀ β : LinearMap.BilinForm ℤ X, (∀ y, 0 ≤ β y y) → 0 ≤ ∑ i, β (a i) (a i) :=
    fun β hp => Finset.sum_nonneg fun i _ => hp _
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      refine ⟨1, fun β hs hp => ?_⟩
      have h1 := hp (a i + a j)
      have h2 := hp (a i - a j)
      simp only [map_add (f := _), map_sub, LinearMap.add_apply, LinearMap.sub_apply, hs (a j) (a i)] at h1 h2
      have h3 := Finset.single_le_sum (f := fun i => β (a i) (a i)) (fun i _ => hp _) (Finset.mem_univ i)
      have h4 := Finset.single_le_sum (f := fun i => β (a i) (a i)) (fun i _ => hp _) (Finset.mem_univ j)
      rw [abs_le]
      constructor <;> push_cast <;> linarith
    | zero => exact ⟨0, fun β _ _ => by simp⟩
    | add y z _ _ h1 h2 =>
      obtain ⟨C, hC⟩ := h1
      obtain ⟨C', hC'⟩ := h2
      refine ⟨C + C', fun β hs hp => ?_⟩
      rw [map_add (f := _), Nat.cast_add, add_mul]
      exact (abs_add_le _ _).trans (add_le_add (hC β hs hp) (hC' β hs hp))
    | smul n y _ h1 =>
      obtain ⟨C, hC⟩ := h1
      refine ⟨n.natAbs * C, fun β hs hp => ?_⟩
      rw [map_smul, smul_eq_mul, abs_mul, Nat.cast_mul, Int.natCast_natAbs, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hC β hs hp) (abs_nonneg _)
  | zero => exact ⟨0, fun β _ _ => by simp⟩
  | add x z _ _ h1 h2 =>
    obtain ⟨C, hC⟩ := h1
    obtain ⟨C', hC'⟩ := h2
    refine ⟨C + C', fun β hs hp => ?_⟩
    rw [map_add (f := _), LinearMap.add_apply, Nat.cast_add, add_mul]
    exact (abs_add_le _ _).trans (add_le_add (hC β hs hp) (hC' β hs hp))
  | smul n x _ h1 =>
    obtain ⟨C, hC⟩ := h1
    refine ⟨n.natAbs * C, fun β hs hp => ?_⟩
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, abs_mul, Nat.cast_mul, Int.natCast_natAbs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC β hs hp) (abs_nonneg _)

theorem exists_abs_lin_le [Module.Free ℤ X] [Module.Finite ℤ X] (ha : Submodule.span ℤ (Set.range a) = ⊤)
    (lam : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) :
    ∃ C : ℕ, ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) → (∀ y, 0 ≤ β y y) →
      |lam β| ≤ C * ∑ i, β (a i) (a i) := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  let E : _ → _ → LinearMap.BilinForm ℤ X := fun i j => (LinearMap.mul ℤ ℤ).compl₁₂ (b.coord i) (b.coord j)
  have hE : ∀ β : LinearMap.BilinForm ℤ X, β = ∑ i, ∑ j, β (b i) (b j) • E i j := fun β =>
    b.ext fun k => b.ext fun l => by
      simp [E, LinearMap.sum_apply, Finsupp.single_apply]
  choose C hC using exists_abs_apply_le ha
  refine ⟨∑ i, ∑ j, C (b i) (b j) * (lam (E i j)).natAbs, fun β hs hp => ?_⟩
  conv_lhs => rw [hE β]

  simp only [map_sum, map_smul, smul_eq_mul]
  push_cast
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, mul_right_comm]
  exact mul_le_mul_of_nonneg_right (hC _ _ β hs hp) (abs_nonneg _)

end Bound

section Fan

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X]

theorem exists_ray_bound (hF : IsPolFanOn bar φ X) :
    ∃ M : ℕ, ∀ ρ : LinearMap.BilinForm ℤ X, IsCone bar φ ![ρ] → φ.evalZ ρ ≤ M := by
  obtain ⟨S, hS, h⟩ := hF.finite
  obtain ⟨M, hM⟩ := (hS.image fun β => φ.evalZ β).bddAbove
  obtain ⟨N, hN⟩ := exists_nat_ge M
  refine ⟨N, fun ρ hρ => ?_⟩
  obtain ⟨e, he⟩ := h 1 _ hρ
  have h1 := hM ⟨_, he 0, rfl⟩
  simp only [evalZ_pull φ (r := e.toLinearMap) e.surjective, Matrix.cons_val_zero] at h1
  exact h1.trans hN

theorem exists_cone_nat [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (hF : IsPolFanOn bar φ X)
    {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms bar X) (hp : ∀ y, 0 ≤ β y y) :
    ∃ (s : ℕ) (δ : Fin s → LinearMap.BilinForm ℤ X) (n : Fin s → ℕ), IsCone bar φ δ ∧ β = ∑ i, n i • δ i := by
  have hB : toReal β ∈ psdCone (bar := bar) (X := X) := by
    simpa using ConeSub.sum_smul_toReal_mem_psdCone O bar X 1 ![β] ![1] (by simp [hβ]) (by simp [hp]) (by simp)
  obtain ⟨m, γ, c, hγ, hc, hsum⟩ := hF.cover _ hB
  obtain ⟨nZ, hnZ⟩ := Cover.coeff_int hγ.mem hγ.basis hβ hsum
  have hn0 : ∀ i, 0 ≤ nZ i := fun i => by exact_mod_cast (hnZ i) ▸ hc i
  let n : Fin m → ℕ := fun i => (nZ i).toNat
  have hn : ∀ i, ((n i : ℤ) : ℝ) = c i := fun i => by simp [n, Int.toNat_of_nonneg (hn0 i), hnZ i]
  refine ⟨m, γ, n, hγ, LinearMap.ext₂ fun a b => ?_⟩
  have h1 := LinearMap.congr_fun₂ hsum a b
  simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, ← hn] at h1
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, nsmul_eq_mul]
  exact_mod_cast h1

end Fan

theorem exists_gap : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (φ : InvFun O) (d : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] [Module.Free ℤ X] [Module.Finite ℤ X], IsPolFanOn bar φ X → ∀ (r m : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X) (a : Fin m → X), IsCone bar φ γ → Supports bar φ d γ a → ∀ lam : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (∀ j, 0 ≤ lam (γ j)) → ∀ K : ℤ, ∃ D₀ : ℕ, ∀ D, D₀ ≤ D → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → (D * d : ℝ) * φ.evalZ β ≤ (D * ∑ i, β (a i) (a i) + lam β : ℤ)) ∧ ∀ (ρ : LinearMap.BilinForm ℤ X), IsCone bar φ ![ρ] → (∀ j, ρ ≠ γ j) → (D * d : ℝ) * φ.evalZ ρ + K ≤ (D * ∑ i, ρ (a i) (a i) + lam ρ : ℤ) := by
  intro O _ _ _ _ bar φ d X _ _ _ _ _ _ hF r m γ a hγ hS lam hlam K
  obtain ⟨C, hC⟩ := exists_abs_lin_le hS.span lam
  obtain ⟨M, hM⟩ := exists_ray_bound hF
  refine ⟨C + K.natAbs + C * d * M, fun D hD => ?_⟩
  have hray : ∀ ρ : LinearMap.BilinForm ℤ X, IsCone bar φ ![ρ] → (∀ j, ρ ≠ γ j) →
      (D * d : ℝ) * φ.evalZ ρ + (K.natAbs : ℕ) ≤ (D * ∑ i, ρ (a i) (a i) + lam ρ : ℤ) := by
    intro ρ hρ hne
    have hm : ρ ∈ balForms bar X := hρ.mem 0
    have hp : ∀ y, 0 ≤ ρ y y := hρ.nonneg 0
    obtain ⟨n, hn⟩ := hF.exists_nat hm hp
    have h1 := hS.le ρ hm hp
    have h2 : (d : ℝ) * φ.evalZ ρ ≠ (∑ i, ρ (a i) (a i) : ℤ) := fun he => by
      obtain ⟨k, c, hk, hc⟩ := hS.only ρ hm hp he
      obtain ⟨j, hj⟩ := intCone_face O bar φ X hF 1 r ![ρ] γ hρ hγ ![k] c (by simp [hk]) (by simpa using hc) 0
      exact hne j hj
    have h3 := hM ρ hρ
    have h4 := (abs_le.1 (hC ρ hm.1 hp)).1
    rw [hn] at h1 h2 h3 ⊢
    generalize ∑ i, ρ (a i) (a i) = L at *
    have h1' : (d : ℤ) * n ≤ L := by exact_mod_cast h1
    have h2' : (d : ℤ) * n ≠ L := by exact_mod_cast h2
    have h3' : (n : ℤ) ≤ M := by exact_mod_cast h3
    have hD' : (C : ℤ) + (K.natAbs : ℕ) + C * d * M ≤ D := by exact_mod_cast hD
    have h5 : 0 ≤ L - d * n - 1 := by omega
    have h6 : (C : ℤ) * d * n ≤ C * d * M := mul_le_mul_of_nonneg_left h3' (by positivity)
    have h7 : (0 : ℤ) ≤ C * d * M := by positivity
    have h8 : (0 : ℤ) ≤ (K.natAbs : ℕ) := by positivity
    have h9 : 0 ≤ ((D : ℤ) - C) * (L - d * n - 1) := mul_nonneg (by linarith) h5
    have : (D * d : ℤ) * n + (K.natAbs : ℕ) ≤ D * L + lam ρ := by nlinarith
    have h10 := (Int.cast_le (R := ℝ)).2 this
    rwa [Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, Int.cast_natCast,
      Int.cast_natCast] at h10
  refine ⟨fun β hβ hp => ?_, fun ρ hρ hne => le_trans ?_ (hray ρ hρ hne)⟩
  · obtain ⟨s, δ, n, hδ, rfl⟩ := exists_cone_nat hF hβ hp
    have hall : ∀ i, (D * d : ℝ) * φ.evalZ (δ i) ≤ (D * ∑ l, δ i (a l) (a l) + lam (δ i) : ℤ) := by
      intro i
      by_cases h : ∃ j, δ i = γ j
      · obtain ⟨j, hj⟩ := h
        rw [hj, mul_assoc, hS.eq j]
        have := hlam j
        exact_mod_cast (le_add_of_nonneg_right this)
      · push_neg at h
        have hc : IsCone bar φ ![δ i] := by
          have := hF.face _ _ δ ⟨fun _ : Fin 1 => i, fun _ _ _ => Subsingleton.elim _ _⟩ hδ
          convert this using 1
          funext u
          fin_cases u
          rfl
        exact le_trans (le_add_of_nonneg_right (Nat.cast_nonneg _)) (hray _ hc h)
    rw [intCone_evalZ_sum hδ.linear, Finset.mul_sum]
    have e : (D * ∑ l, (∑ i, n i • δ i) (a l) (a l) + lam (∑ i, n i • δ i) : ℤ) =
        ∑ i, (n i : ℤ) * (D * ∑ l, δ i (a l) (a l) + lam (δ i)) := by

      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_nsmul, nsmul_eq_mul, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [e, Int.cast_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Int.cast_mul, Int.cast_natCast, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hall i) (Nat.cast_nonneg _)
  · have : (K : ℝ) ≤ (K.natAbs : ℕ) := by
      have h := (Int.cast_le (R := ℝ)).2 (Int.le_natAbs : K ≤ (K.natAbs : ℕ))
      rwa [Int.cast_natCast] at h
    linarith

end GlobalTheory.Poinc.Gap
end

section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.exists_transport_minimisers_latticeAutomorphism : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (N : ℕ) [NeZero N] (r : ℕ) (μ : ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ))), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → ∀ e : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ), ∃ σ : Equiv.Perm (Fin 8 → Fin r → ZMod N), (∀ c u i, ((e.symm (μ (σ c) u) i : ℤ) : ZMod N) = c u i) ∧ ∀ b' : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b' (μ c) ≤ qW W b' α) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W (pull e.toLinearMap b') ((fun c u => e.symm (μ (σ c) u)) c) ≤ qW W (pull e.toLinearMap b') α) := by
  first | exact @GlobalTheory.relabel_minimisers | exact GlobalTheory.relabel_minimisers | (intros; apply GlobalTheory.relabel_minimisers <;> assumption)
end

section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.isometry_eq_refl_of_congr_mod_ge_three : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (β : LinearMap.BilinForm ℤ X), (∀ x, x ≠ 0 → 0 < β x x) → ∀ (e : X ≃ₗ[ℤ] X), (∀ x y, β (e x) (e y) = β x y) → ∀ N : ℕ, 3 ≤ N → (∀ x, CongMod N (e x) x) → e = LinearEquiv.refl ℤ X := by
  first | exact @GlobalTheory.Poinc.eq_refl_of_isometry_congMod | exact GlobalTheory.Poinc.eq_refl_of_isometry_congMod | (intros; apply GlobalTheory.Poinc.eq_refl_of_isometry_congMod <;> assumption)
end

section

open GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.eq_adjoint_apply_of_weightedQuadraticSum_polar : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (X₀ : Type) [AddCommGroup X₀] (β : LinearMap.BilinForm ℤ X₀), (∀ a b, β a b = β b a) → (∀ a, a ≠ 0 → 0 < β a a) → ∀ (E E' : Matrix (Fin 8) (Fin 8) ℤ), (W + W.transpose) * E' = E.transpose * (W + W.transpose) → ∀ z z' : Fin 8 → X₀, (∀ y : Fin 8 → X₀, qW W β ((fun a => ∑ b, E a b • y b) + z) - qW W β (fun a => ∑ b, E a b • y b) - qW W β z = qW W β (y + z') - qW W β y - qW W β z') → z' = fun a => ∑ b, E' a b • z b := by
  first | exact @GlobalTheory.Poinc.eq_adjoint_apply_of_qW_polar | exact GlobalTheory.Poinc.eq_adjoint_apply_of_qW_polar | (intros; apply GlobalTheory.Poinc.eq_adjoint_apply_of_qW_polar <;> assumption)
end

section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.symm_bilinForm_eq_zero_of_weightedQuadraticSum_lifts : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → ∀ r : ℕ, (∃ ε : Fin 8 → ℤ, Nat.Coprime N (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs)) → ∀ μ : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → ∀ b : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b x y = b y x) → (∀ c, qW W b (μ c) = 0) → b = 0 := by
  first | exact @GlobalTheory.Poinc.symm_eq_zero_of_qW_lifts | exact GlobalTheory.Poinc.symm_eq_zero_of_qW_lifts | (intros; apply GlobalTheory.Poinc.symm_eq_zero_of_qW_lifts <;> assumption)
end

section

open GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.lattice_automorphism_congr_one_mod_det_eq_one : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (k : X ≃+ X) (m : ℕ), 3 ≤ m → (∀ x, CongMod m (k x) x) → LinearMap.det (k.toIntLinearEquiv : X →ₗ[ℤ] X) = 1 := by
  first | exact @GlobalTheory.Poinc.det_eq_one_of_congMod | exact GlobalTheory.Poinc.det_eq_one_of_congMod | (intros; apply GlobalTheory.Poinc.det_eq_one_of_congMod <;> assumption)
end

section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.weightedLatticeQuadraticSum_ge_diagonal : ∀ (s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ), PosW W → ∃ c : ℝ, 0 < c ∧ ∀ (X : Type) [AddCommGroup X] (β : LinearMap.BilinForm ℤ X), (∀ a b, β a b = β b a) → (∀ y, 0 ≤ β y y) → ∀ y : Fin s → X, c * (∑ u, β (y u) (y u) : ℤ) ≤ (qW W β y : ℤ) := by
  first | exact @GlobalTheory.Poinc.QWDom.qW_ge | exact GlobalTheory.Poinc.QWDom.qW_ge | (intros; apply GlobalTheory.Poinc.QWDom.qW_ge <;> assumption)
end

section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc.MinSys

open Matrix

theorem finite_of_pos {r : ℕ} (G : LinearMap.BilinForm ℤ (Fin r → ℤ)) (hs : ∀ a b, G a b = G b a)
    (hn : ∀ x, 0 ≤ G x x) (hp : ∀ x, x ≠ 0 → 0 < G x x) (B : ℤ) : {x | G x x ≤ B}.Finite := by
  classical
  set S : Matrix (Fin r) (Fin r) ℤ := LinearMap.BilinForm.toMatrix' G with hS
  have hGS : ∀ x, G x x = x ⬝ᵥ S *ᵥ x := fun x => by
    rw [← Matrix.toBilin'_apply', hS, Matrix.toBilin'_toMatrix']
  have hdet : S.det ≠ 0 := by
    intro h
    obtain ⟨z, hz, hSz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    have h1 := hp z hz
    rw [hGS, hSz, dotProduct_zero] at h1
    exact lt_irrefl _ h1
  have hpsd : (S.map (Int.cast : ℤ → ℝ)).PosSemidef := by
    have h := GlobalTheory.Poinc.QWDom.gram_posSemidef G hs hn (fun u => Pi.single u 1)
    convert h using 1
    ext u v
    simp [hS, LinearMap.BilinForm.toMatrix'_apply]
  have hpd : (S.map (Int.cast : ℤ → ℝ)).PosDef := by
    rw [hpsd.posDef_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ← Int.cast_det]
    exact_mod_cast hdet
  obtain ⟨c, hc, hP⟩ := GlobalTheory.Poinc.QWDom.exists_pos_posSemidef_sub_smul_one hpd
  have key : ∀ x : Fin r → ℤ, c * ∑ u, ((x u : ℝ)) ^ 2 ≤ (G x x : ℝ) := by
    intro x
    have h := hP.dotProduct_mulVec_nonneg (fun u => (x u : ℝ))
    simp only [star_trivial, sub_mulVec, dotProduct_sub, sub_nonneg] at h
    have e1 : (fun u => (x u : ℝ)) ⬝ᵥ (S.map (Int.cast : ℤ → ℝ)) *ᵥ (fun u => (x u : ℝ)) = ((x ⬝ᵥ S *ᵥ x : ℤ) : ℝ) := by
      simp [dotProduct, mulVec, Matrix.map_apply]
    have e2 : (fun u => (x u : ℝ)) ⬝ᵥ (c • (1 : Matrix (Fin r) (Fin r) ℝ)) *ᵥ (fun u => (x u : ℝ)) =
        c * ∑ u, ((x u : ℝ)) ^ 2 := by
      simp [dotProduct, Matrix.mulVec, Matrix.one_apply, Finset.mul_sum, sq]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e1, e2] at h
    rw [hGS]
    exact h
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (B : ℝ) / c ≤ M := exists_nat_ge _
  rw [div_le_iff₀ hc] at hM
  refine (Set.Finite.pi' (fun _ : Fin r => Set.finite_Icc (-(M : ℤ)) M)).subset fun x hx => ?_
  intro u
  have hxB : (G x x : ℝ) ≤ B := by exact_mod_cast hx
  have h1 : ((x u : ℝ)) ^ 2 ≤ ∑ v, ((x v : ℝ)) ^ 2 :=
    Finset.single_le_sum (f := fun v => ((x v : ℝ)) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ u)
  have h2 : c * ((x u : ℝ)) ^ 2 ≤ c * M := by
    have := (mul_le_mul_of_nonneg_left h1 hc.le).trans ((key x).trans hxB)
    linarith
  have h3 : ((x u : ℝ)) ^ 2 ≤ M := le_of_mul_le_mul_left h2 hc
  have h4 : (x u) ^ 2 ≤ (M : ℤ) := by exact_mod_cast h3
  have h5 := Int.le_self_sq (x u)
  have h6 := Int.le_self_sq (-(x u))
  rw [neg_sq] at h6
  exact ⟨by linarith, by linarith⟩

theorem qW_sum_nsmul {s m : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X] (cf : Fin m → ℕ)
    (γ : Fin m → LinearMap.BilinForm ℤ X) (y : Fin s → X) :
    qW W (∑ j, cf j • γ j) y = ∑ j, (cf j : ℤ) * qW W (γ j) y := by
  simp only [qW, LinearMap.sum_apply, LinearMap.smul_apply, nsmul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem qW_nsmul {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X] (k : ℕ)
    (b : LinearMap.BilinForm ℤ X) (y : Fin s → X) : qW W (k • b) y = (k : ℤ) * qW W b y := by
  simp only [qW, LinearMap.smul_apply, nsmul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  ring

theorem finite_minimiser_systems : ∀ (φ : InvFun ℤ), ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → ∀ r : ℕ, ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ)), IsCone id φ γ → (∀ x, x ≠ 0 → 0 < ∑ j, γ j x x) → ∃ Sμ : Finset ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)), ∀ (b : LinearMap.BilinForm ℤ (Fin r → ℤ)) (k : ℕ) (cf : Fin m → ℕ), 0 < k → (∀ j, 0 < cf j) → k • b = ∑ j, cf j • γ j → ∀ μ : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b (μ c) ≤ qW W b α) → μ ∈ Sμ := by
  intro φ W hW N _ _ r m γ hC hdef
  classical
  obtain ⟨c0, hc0, hge⟩ := GlobalTheory.Poinc.QWDom.qW_ge 8 W hW
  have hsym : ∀ j a b, γ j a b = γ j b a := fun j => (hC.mem j).1
  have hnn : ∀ j y, 0 ≤ γ j y y := hC.nonneg
  have hq0 : ∀ j (α : Fin 8 → Fin r → ℤ), 0 ≤ qW W (γ j) α := fun j α => by
    have h := hge (Fin r → ℤ) (γ j) (hsym j) (hnn j) α
    have h1 : (0 : ℝ) ≤ c0 * ((∑ u, γ j (α u) (α u) : ℤ) : ℝ) :=
      mul_nonneg hc0.le (by exact_mod_cast Finset.sum_nonneg fun u _ => hnn j (α u))
    exact_mod_cast h1.trans h
  set G : LinearMap.BilinForm ℤ (Fin r → ℤ) := ∑ j, γ j with hG
  have hGapp : ∀ a b, G a b = ∑ j, γ j a b := fun a b => by simp [hG, LinearMap.sum_apply]
  have hGsym : ∀ a b, G a b = G b a := fun a b => by simp only [hGapp, hsym _ a b]
  have hGnn : ∀ y, 0 ≤ G y y := fun y => by rw [hGapp]; exact Finset.sum_nonneg fun j _ => hnn j y
  have hGpos : ∀ x, x ≠ 0 → 0 < G x x := fun x hx => by rw [hGapp]; exact hdef x hx
  have hGq : ∀ α, qW W G α = ∑ j, qW W (γ j) α := fun α => by
    have := qW_sum_nsmul W (fun _ => 1) γ α
    simpa [hG] using this
  have hfinG : ∀ B : ℤ, {α : Fin 8 → Fin r → ℤ | qW W G α ≤ B}.Finite := by
    intro B
    obtain ⟨M, hM⟩ : ∃ M : ℕ, (B : ℝ) / c0 ≤ M := exists_nat_ge _
    rw [div_le_iff₀ hc0] at hM
    refine (Set.Finite.pi' fun _ : Fin 8 => finite_of_pos G hGsym hGnn hGpos M).subset fun α hα u => ?_
    have h := hge (Fin r → ℤ) G hGsym hGnn α
    have h1 : G (α u) (α u) ≤ ∑ v, G (α v) (α v) :=
      Finset.single_le_sum (f := fun v => G (α v) (α v)) (fun v _ => hGnn (α v)) (Finset.mem_univ u)
    have hα' : (qW W G α : ℝ) ≤ B := by exact_mod_cast hα
    have h1' : ((G (α u) (α u) : ℤ) : ℝ) ≤ ((∑ v, G (α v) (α v) : ℤ) : ℝ) := by exact_mod_cast h1
    have h2 : c0 * (G (α u) (α u) : ℝ) ≤ c0 * M := by
      have := (mul_le_mul_of_nonneg_left h1' hc0.le).trans (h.trans hα')
      linarith
    have h3 : (G (α u) (α u) : ℝ) ≤ M := le_of_mul_le_mul_left h2 hc0
    show G (α u) (α u) ≤ ((M : ℕ) : ℤ)
    exact_mod_cast h3
  let T : (Fin 8 → Fin r → ZMod N) → Type := fun c =>
    {α : Fin 8 → Fin r → ℤ // ∀ u i, ((α u i : ℤ) : ZMod N) = c u i}
  have hD : ∀ c, ∃ F : Finset (T c), ∀ α : T c, ∃ β ∈ F,
      (fun j => (qW W (γ j) β.1).toNat) ≤ (fun j => (qW W (γ j) α.1).toNat) :=
    fun c => GlobalTheory.dickson_finite_below_every m (fun (α : T c) j => (qW W (γ j) α.1).toNat)
  choose F hF using hD
  let Bd : (Fin 8 → Fin r → ZMod N) → ℤ := fun c => ∑ β ∈ F c, qW W G β.1
  have hfin : {μ : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ) | ∀ c, μ c ∈ {α | qW W G α ≤ Bd c}}.Finite :=
    Set.Finite.pi' fun c => hfinG (Bd c)
  refine ⟨hfin.toFinset, fun b k cf hk hcf hkb μ hμ hmin => ?_⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  intro c
  obtain ⟨β, hβF, hβ⟩ := hF c ⟨μ c, hμ c⟩
  have hle : ∀ j, qW W (γ j) β.1 ≤ qW W (γ j) (μ c) := fun j => by
    have h1 : (qW W (γ j) β.1).toNat ≤ (qW W (γ j) (μ c)).toNat := hβ j
    have := hq0 j β.1
    have := hq0 j (μ c)
    omega
  have hkq : ∀ α, (k : ℤ) * qW W b α = ∑ j, (cf j : ℤ) * qW W (γ j) α := fun α => by
    rw [← qW_nsmul, hkb, qW_sum_nsmul]
  have h2 : ∑ j, (cf j : ℤ) * qW W (γ j) (μ c) ≤ ∑ j, (cf j : ℤ) * qW W (γ j) β.1 := by
    rw [← hkq, ← hkq]
    exact mul_le_mul_of_nonneg_left (hmin c β.1 β.2) (by positivity)
  have h3 : ∀ j, qW W (γ j) (μ c) - qW W (γ j) β.1 ≤
      (cf j : ℤ) * qW W (γ j) (μ c) - (cf j : ℤ) * qW W (γ j) β.1 := fun j => by
    have h4 := hle j
    have h5 : (1 : ℤ) ≤ cf j := by exact_mod_cast hcf j
    nlinarith
  have h6 : ∑ j, qW W (γ j) (μ c) ≤ ∑ j, qW W (γ j) β.1 := by
    have h7 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => h3 j
    simp only [Finset.sum_sub_distrib] at h7
    linarith
  have h8 : qW W G β.1 ≤ Bd c :=
    Finset.single_le_sum (f := fun β : T c => qW W G β.1)
      (fun β _ => by rw [hGq]; exact Finset.sum_nonneg fun j _ => hq0 j β.1) hβF
  rw [hGq] at h8 ⊢
  linarith

end GlobalTheory.Poinc.MinSys
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum


theorem _root_.GlobalTheory.T.lattice_class_sums_of_terms_prescribed_norms : ∀ (p : ℕ) [Fact p.Prime] (Y K : Type) [AddCommGroup Y] [Nonempty K] (m : ℕ) (q : Y → ℝ) (s : PadicAlgCl p) (n : Y → ℕ), Filter.Tendsto q Filter.cofinite Filter.atTop → (∀ χ, ‖s‖ ^ n χ = Real.exp (-q χ)) → ∀ F : Y → K → PadicAlgCl p, (∀ ν ν' κ, CongMod m ν ν' → F ν κ = F ν' κ) → (∀ ν κ, (∀ χ, CongMod m χ ν → q ν ≤ q χ) → ‖F ν κ‖ ≤ Real.exp (-q ν)) → (∀ ν, (∀ χ, CongMod m χ ν → χ ≠ ν → q ν < q χ) → ∃ κ, ‖F ν κ‖ = Real.exp (-q ν)) → ∃ t : Y → K → PadicAlgCl p, (∀ χ κ, ‖t χ κ‖ ≤ Real.exp (-q χ)) ∧ (∀ χ, ∃ κ, ‖t χ κ‖ = Real.exp (-q χ)) ∧ ∀ ν κ (δ : ℝ), 0 < δ → ∃ S₀ : Finset Y, ∀ S : Finset Y, (∀ χ ∈ S, CongMod m χ ν) → (∀ χ ∈ S₀, CongMod m χ ν → χ ∈ S) → ‖F ν κ - ∑ χ ∈ S, t χ κ‖ ≤ δ := by
  first | exact @GlobalTheory.UPoinc.USum.classSum_of_terms | exact GlobalTheory.UPoinc.USum.classSum_of_terms | (intros; apply GlobalTheory.UPoinc.USum.classSum_of_terms <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompHS

theorem _root_.GlobalTheory.T.geometricallyConnected_smoothProjModification_offOpen : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (sX : X ⟶ Sp F) (n : ℕ) [SmoothOfRelativeDimension n sX] (U : X.Opens) (M : Modif sX U n) [IsIntegral M.X] [GeometricallyConnected sX], (U : Set X).Nonempty → GeometricallyConnected M.str := by
  first | exact @GlobalTheory.ModifGeomConn.geometricallyConnected_modif | exact GlobalTheory.ModifGeomConn.geometricallyConnected_modif | (intros; apply GlobalTheory.ModifGeomConn.geometricallyConnected_modif <;> assumption)
end
