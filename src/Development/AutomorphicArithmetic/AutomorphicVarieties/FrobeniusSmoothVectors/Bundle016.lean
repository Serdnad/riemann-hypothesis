module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LeAdicClosure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle005
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle039
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle010
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.CharP.Algebra

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem lc_of_ker {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    (φ : G →* H) (h : IsOpen (φ.ker : Set G)) : IsLocallyConstant φ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker φ h

private theorem diag_mul {n : ℕ} {Q : Type} [CommRing Q] (a b : Matrix (Fin n) (Fin n) Q)
    (ha : ∀ i j, i < j → a i j = 0) (hb : ∀ i j, i < j → b i j = 0) (i : Fin n) :
    (a * b) i i = a i i * b i i :=
  _root_.UpperTheory.Reformulated.B.Qk64.diag_mul a b ha hb i

private theorem key {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}
    (hF : F.Ok C₀) {Q : Type} [CommRing Q] [IsDomain Q] [IsLocalRing Q] [IsNoetherianRing Q]
    [Finite (ResidueField Q)] (f : k →+* Q) (ρ : NRep F n Q) (hc : ρ.Cont (maximalIdeal Q))
    (hb : (ρ.map (residue Q)).IsBar ((residue Q).comp f)) (ht : ρ.triM = ⊥) (h : ℕ) (h0 : h ≠ 0) (i : Fin n)
    (H : ∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ ψ : F.G0 →* A, IsOpen (ψ.ker : Set F.G0) →
      (∀ g g', ρ.r g i i = ρ.r g' i i → F.Ψ g ^ w n i = F.Ψ g' ^ w n i → ψ g = ψ g') → ∀ g, ψ g ^ h = 1)
    (g : F.G0) : ρ.r g i i = f ((F.Ψ g ^ w n i : kˣ) : k) := by
  haveI : CharP Q l := charP_of_injective_ringHom f.injective l
  have hz : ∀ g i j, i < j → ρ.r g i j = 0 := fun g i j hij => by
    have : ρ.r g i j ∈ ρ.triM := Ideal.subset_span ⟨g, i, j, hij, rfl⟩
    rwa [ht, Ideal.mem_bot] at this
  let χ : F.G0 →* Q :=
    { toFun := fun g => ρ.r g i i * f (((F.Ψ g ^ w n i)⁻¹ : kˣ) : k)
      map_one' := by simp
      map_mul' := fun a b => by
        rw [map_mul, diag_mul _ _ (hz a) (hz b), Subgroup.coe_mul, map_mul, mul_zpow, mul_inv, Units.val_mul,
          map_mul]
        ring }
  have hχ : ∀ g, χ g = ρ.r g i i * f (((F.Ψ g ^ w n i)⁻¹ : kˣ) : k) := fun _ => rfl
  have hinv : ∀ g : F.G0, f (((F.Ψ g ^ w n i)⁻¹ : kˣ) : k) * f ((F.Ψ g ^ w n i : kˣ) : k) = 1 := fun g => by
    rw [← map_mul, Units.inv_mul, map_one]
  have hΨ : IsLocallyConstant fun g : F.G0 => F.Ψ g :=
    (lc_of_ker F.Ψ hF.Ψ_open).comp_continuous continuous_subtype_val
  have h1 : χ g = 1 := by
    refine adic_char_unipotent_pgroup_quotient (l := l) χ h h0 (fun N => ?_) (fun g => ?_) (fun A _ _ hA ψ hψ hh => H A hA ψ hψ ?_) g
    · have := (hc.1 i i N).mul (hΨ.comp fun u : kˣ =>
        Ideal.Quotient.mk (maximalIdeal Q ^ N) (f (((u ^ w n i)⁻¹ : kˣ) : k)))
      convert this using 1
      ext x
      simp [χ, map_mul]
    · rw [← residue_eq_zero_iff, map_sub, map_one, sub_eq_zero, hχ, map_mul]
      have h2 : residue Q (ρ.r g i i) = residue Q (f ((F.Ψ g ^ w n i : kˣ) : k)) := hb.1 g i
      rw [h2, ← map_mul, mul_comm, hinv, map_one]
    · intro g g' e1 e2
      exact hh g g' (by rw [hχ, hχ, e1, e2])
  rw [hχ] at h1
  calc ρ.r g i i = ρ.r g i i * (f (((F.Ψ g ^ w n i)⁻¹ : kˣ) : k) * f ((F.Ψ g ^ w n i : kˣ) : k)) := by
        rw [hinv, mul_one]
    _ = _ := by rw [← mul_assoc, h1, one_mul]

theorem UpperTheory.V.Fr.triangular_representation_diagonal :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ {Q : Type} [CommRing Q] [IsDomain Q] [IsLocalRing Q] [IsNoetherianRing Q] [Finite (ResidueField Q)] (f : k →+* Q) (ρ : NRep F n Q), ρ.Cont (maximalIdeal Q) → (ρ.map (residue Q)).IsBar ((residue Q).comp f) → ρ.triM = ⊥ → ∀ {ι ι' : Type} (s : ι → F.G0) (s' : ι' → F.G0) (h : ℕ), h ≠ 0 → (∀ a, F.Ψ (s a) = 1) → (∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ χ : F.G0 →* A, IsOpen (χ.ker : Set F.G0) → ((∀ a, χ (s a) = 1) → ∀ g, χ g ^ h = 1) ∧ ((∀ g, χ (F.star g) = χ g) → (∀ a, χ (s' a) = 1) → ∀ g, χ g ^ h = 1)) → (∀ a (i : Fin n), (i : ℕ) = 0 → ρ.r (s a) i i = 1) → (∀ a (i : Fin n), w n i = 0 → ρ.r (s' a) i i = 1) → ∀ (g : F.G0) (i : Fin n), ρ.r g i i = f ((F.Ψ g ^ w n i : kˣ) : k) := by
  intro l _ k _ _ F C₀ n hF hn Q _ _ _ _ _ f ρ hc hb ht ι ι' s s' h h0 hs H h1 h2
  obtain ⟨-, -, sΨ, -, sr⟩ := UpperTheory.V.Fr.star hF
  have A0 : ∀ (i : Fin n), (i : ℕ) = 0 → ∀ g, ρ.r g i i = f ((F.Ψ g ^ w n i : kˣ) : k) := fun i hi =>
    key hF f ρ hc hb ht h h0 i fun A _ _ hA ψ hψ hh => (H A hA ψ hψ).1 fun a => by
      rw [← map_one ψ]
      refine hh _ _ ?_ ?_
      · rw [h1 a i hi]; simp
      · rw [hs a]; simp
  have A1 : ∀ (i : Fin n), w n i = 0 → i.rev = i → ∀ g, ρ.r g i i = f ((F.Ψ g ^ w n i : kˣ) : k) :=
    fun i hi hr => key hF f ρ hc hb ht h h0 i fun A _ _ hA ψ hψ hh => (H A hA ψ hψ).2
      (fun g => hh _ _ (by rw [sr, hr]) (by simp [hi])) fun a => by
      rw [← map_one ψ]
      refine hh _ _ ?_ ?_
      · rw [h2 a i hi]; simp
      · simp [hi]
  have A2 : ∀ (i : Fin n), (i : ℕ) = 0 → w n i.rev = - w n i →
      ∀ g, ρ.r g i.rev i.rev = f ((F.Ψ g ^ w n i.rev : kˣ) : k) := fun i hi hw g => by
    rw [← sr, A0 i hi, sΨ, hw, _root_.zpow_neg, _root_.inv_zpow]
  intro g i
  rcases hn with rfl | rfl
  · fin_cases i
    · exact A0 0 rfl g
    · exact A2 0 rfl (by decide) g
  · fin_cases i
    · exact A0 0 rfl g
    · exact A1 1 (by decide) (by decide) g
    · exact A2 0 rfl (by decide) g
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem zpow_w_ne' {k : Type} [Field k] {n : ℕ} (hn : n = 2 ∨ n = 3) (a : kˣ) (ha : a ^ 2 ≠ 1)
    (i j : Fin n) (hij : i ≠ j) : a ^ w n i ≠ a ^ w n j := by
  have h1 : a ≠ 1 := fun h => ha (by rw [h, one_pow])
  have h2 : a ≠ a⁻¹ := fun h => ha (by rw [sq]; nth_rewrite 2 [h]; exact mul_inv_cancel a)
  have h3 : (1 : kˣ) ≠ a⁻¹ := fun h => h1 (by rw [← inv_inv a, ← h, inv_one])
  rcases hn with rfl | rfl
  · fin_cases i <;> fin_cases j <;> simp_all [UpperTheory.V.Fr.w] <;> simp_all [eq_comm]
  · fin_cases i <;> fin_cases j <;> simp_all [UpperTheory.V.Fr.w] <;> simp_all [eq_comm]

private theorem residue_eq {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    {x y : R} (h : res O R x = res O R y) : residue R x = residue R y := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ← res_eq_zero_iff O R, map_sub, h, sub_self]

private theorem charpoly_flag' {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* Matrix (Fin n) (Fin n) k)
    (κ : Fin n → H →* kˣ) (h : UpperTheory.V.W.HasFlag r.toHomUnits κ) (s : H) :
    (r s).charpoly = ∏ i, (Polynomial.X - Polynomial.C (κ i s : k)) := by
  obtain ⟨g, hg⟩ := h
  have e : ((g * r.toHomUnits s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
      = (g : Matrix (Fin n) (Fin n) k) * r s * (g : Matrix (Fin n) (Fin n) k)⁻¹ := by
    simp [Matrix.coe_units_inv]
  have hc := Matrix.charpoly_units_conj g (r s)
  rw [← hc, ← e, Matrix.charpoly_of_isUpperTriangular]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [(hg s).2 i]
  · intro i j hij
    exact (hg s).1 i j hij

theorem UpperTheory.V.Fr.o1 :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ v g, (S.u.r (F.loc0 v g)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (S.u.ψ v i g : S.A)) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S v g
  obtain ⟨g₀, hg⟩ := hF.f3 v
  have h4 : ∀ i, res O S.R (S.ρ.ψ v i g₀) = ((F.Ψ (F.loc v g₀) ^ w n i : (ResidueField O)ˣ) : ResidueField O) :=
    fun i => S.lift.2.1.2 v i g₀
  have hfl : UpperTheory.V.W.HasFlag (S.ρ.r.comp (F.loc0 v)).toHomUnits (S.ρ.ψ v) := by
    refine flag_loc _ _ g₀ (fun i j hij => ?_) ?_ (fun s => S.ρ.ord v s)
    · by_contra hu
      have h2 : (S.ρ.ψ v i g₀ : S.R) - S.ρ.ψ v j g₀ ∈ maximalIdeal S.R := hu
      have h3 := (res_eq_zero_iff O S.R _).2 h2
      rw [map_sub, h4, h4, sub_eq_zero] at h3
      exact zpow_w_ne' hn _ hg i j hij (Units.ext h3)
    · have hd : ((S.ρ.r.comp (F.loc0 v)) g₀).map (residue S.R) =
          Matrix.diagonal fun i => residue S.R (S.ρ.ψ v i g₀) := by
        ext i j
        by_cases hij : i = j
        · subst hij
          rw [Matrix.diagonal_apply_eq]
          refine residue_eq (O := O) ?_
          rw [h4]
          exact S.lift.2.1.1 (F.loc0 v g₀) i
        · rw [Matrix.diagonal_apply_ne _ hij, ← map_zero (residue S.R)]
          refine residue_eq (O := O) ?_
          rw [map_zero]
          exact S.lift.2.2 (F.loc0 v g₀) i j hij
      rw [hd, Matrix.charpoly_diagonal]
  have h := charpoly_flag' _ _ hfl g
  refine Polynomial.map_injective (S.A.val : S.A →+* S.R) Subtype.val_injective ?_
  rw [← Matrix.charpoly_map, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  exact h
end
