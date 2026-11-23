module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle005
import Formalism.LocalToGlobal.IndefiniteReal.Bundle014
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section



noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix NumberField
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_nsmul_mem_cpt' {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (K : Set X) (hK : IsCompact K) (hKs : ∀ y ∈ K, ∀ n : ℕ, n • y ∈ K) (H : AddSubgroup X)
    (hH : IsOpen (H : Set X)) : ∃ m : ℕ, 0 < m ∧ ∀ y ∈ K, m • y ∈ H := by
  classical
  let U : X → Set X := fun y => (fun x => x - y) ⁻¹' (H : Set X)
  have hU : ∀ y, IsOpen (U y) := fun y => hH.preimage (continuous_id.sub continuous_const)
  have hcov : K ⊆ ⋃ y ∈ K, U y := fun x hx => Set.mem_biUnion hx (by simp [U, H.zero_mem])
  obtain ⟨t, -, htf, hcov'⟩ := hK.elim_finite_subcover_image (fun y _ => hU y) hcov
  obtain ⟨t', rfl⟩ : ∃ t' : Finset X, (t' : Set X) = t := ⟨htf.toFinset, by simp⟩
  refine ⟨t'.card.factorial, Nat.factorial_pos _, fun y hy => ?_⟩
  have hmaps : ∀ j ∈ Finset.range (t'.card + 1), ∃ i ∈ t', j • y ∈ U i := fun j _ => by
    have := hcov' (hKs y hy j)
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, hji⟩ := this
    exact ⟨i, by simpa using hi, hji⟩
  choose! f hf using hmaps
  obtain ⟨j1, hj1, j2, hj2, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (t'.card + 1)) (t := t') (by simp) (f := f) (fun j hj => (hf j hj).1)
  have h1 := (hf j1 hj1).2
  have h2 := (hf j2 hj2).2
  rw [heq] at h1
  have hdiff : ((j1 : ℤ) - j2) • y ∈ H := by
    convert H.sub_mem h1 h2 using 1
    show _ = (j1 • y - f j2) - (j2 • y - f j2)
    rw [sub_zsmul, natCast_zsmul, natCast_zsmul]
    abel
  have hj1' : j1 ≤ t'.card := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj1)
  have hj2' : j2 ≤ t'.card := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj2)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hk : ((j2 - j1 : ℕ) : ℤ) • y ∈ H := by
      have := H.neg_mem hdiff
      rw [← neg_zsmul, neg_sub] at this
      rwa [Nat.cast_sub hlt.le]
    rw [natCast_zsmul] at hk
    obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.sub_pos_of_lt hlt) (le_trans (Nat.sub_le _ _) hj2')
    rw [hc, mul_comm, ← smul_smul]
    exact H.nsmul_mem hk c
  · have hk : ((j1 - j2 : ℕ) : ℤ) • y ∈ H := by rwa [Nat.cast_sub hlt.le]
    rw [natCast_zsmul] at hk
    obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.sub_pos_of_lt hlt) (le_trans (Nat.sub_le _ _) hj1')
    rw [hc, mul_comm, ← smul_smul]
    exact H.nsmul_mem hk c

def LatLevel (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f →
      ∃ k : ℕ, 0 < k ∧ ∀ u ∈ latAll S T ΛS ΛT, heisO ψ S T (k • u) f = f

theorem latAll_inf (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) {u : WO S T} (hu : u ∈ latAll S T ΛS ΛT) :
    u.map (infPart D) = 0 := by
  induction hu using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, -, -, a, -, s, -, t, -, rfl⟩ := hx
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.zero_apply]
    show fstA D.host.F (pairA D.host.F 0 α) ⊗ₜ[D.host.F] _ = 0
    rw [show fstA D.host.F (pairA D.host.F 0 α) = 0 from rfl, TensorProduct.zero_tmul]
  | zero => ext i j; simp
  | add x y _ _ hx hy =>
    ext i j
    have h1 : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
    have h2 : infPart D (y i j) = 0 := congrFun (congrFun hy i) j
    show infPart D (x i j + y i j) = 0
    rw [(infPart D).map_add, h1, h2, add_zero]
  | neg x _ hx =>
    ext i j
    have h1 : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
    show infPart D (-x i j) = 0
    rw [(infPart D).map_neg, h1, neg_zero]

theorem latLevel_of (hL : LatSelfDual D) : LatLevel D := by
  intro ψ hψ S T ΛS ΛT hS hT f hf
  obtain ⟨U, hUo, hU⟩ := hf.level
  obtain ⟨hcpt, -, -, -⟩ := hL ψ hψ S T ΛS ΛT hS hT
  obtain ⟨m, hm, hmU⟩ := exists_nsmul_mem_cpt' _ hcpt (fun y hy n => AddSubgroup.nsmul_mem _ hy n) U hUo
  refine ⟨m, hm, fun u hu => hU _ (hmU u hu) ?_⟩
  have h0 := latAll_inf S T ΛS ΛT hu
  ext i j
  have h1 : infPart D (u i j) = 0 := congrFun (congrFun h0 i) j
  show infPart D ((m • u) i j) = 0
  rw [Matrix.smul_apply, nsmul_eq_mul, (infPart D).map_mul, h1, mul_zero]

end Formalism.IndefR.Fin

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct ComplexOrder

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def PlaceLatDualIi (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
      (∀ y : WO S T, IsHalf (cA D e) y →
        ((∀ x ∈ latAll S T ΛS ΛT, IsHalf e x → ψ (symplO S T x y) = 1) ↔ y ∈ latAll S T ΛS ΛT))

def PlaceLatDualIii (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
      (∀ x : WO S T, IsHalf e x →
        ((∀ y ∈ latAll S T ΛS ΛT, IsHalf (cA D e) y → ψ (symplO S T x y) = 1) ↔ x ∈ latAll S T ΛS ΛT))

end Formalism.IndefR.Fin

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct ComplexOrder

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def PlaceLatDualIv (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
      ∀ k : ℕ, 0 < k → ∀ e₁ : AE D, (e₁ = e ∨ e₁ = cA D e) →
        ∃ R : Finset (WO S T), ∀ u ∈ latAll S T ΛS ΛT, IsHalf e₁ u →
          ∃ r ∈ R, ∃ v ∈ latAll S T ΛS ΛT, IsHalf e₁ v ∧ u = r + k • v

def PlaceLatDualV (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
      ∀ e₁ : AE D, (e₁ = e ∨ e₁ = cA D e) → ∀ x : WO S T, IsHalf e₁ x → ∃ k : ℕ, 0 < k ∧ k • x ∈ latAll S T ΛS ΛT

def PlaceLatDualVi (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ e' : AE D, IsSplitIdem D e' → ∀ (g : GA D S) (h : GA D T), SuppAt e' S g → SuppAt e' T h →
      ∃ k : ℕ, 0 < k ∧ ∀ t ∈ latAll S T ΛS ΛT, k • actO S T g h t ∈ latAll S T ΛS ΛT

end Formalism.IndefR.Fin

end
end

section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {R : Ranks}

def alphaH (H : Host R) : H.E := (1 + H.sqrtMinusD) / 2

theorem alphaH_sq (H : Host R) :
    alphaH H * (alphaH H - 1) = -(((H.d + 1) / 4 : ℕ) : H.E) := by
  have hd16 : H.d % 16 = 7 := H.hyp.2.2.2.1
  have hb : H.sqrtMinusD ^ 2 = -(H.d : H.E) := H.sqd_sq
  have h4 : ((H.d + 1) / 4 : ℕ) * 4 = H.d + 1 := by omega
  have h4' : ((((H.d + 1) / 4 : ℕ) : H.E)) * 4 = (H.d : H.E) + 1 := by exact_mod_cast h4
  unfold alphaH
  linear_combination (1 / 4 : H.E) * hb + (1 / 4 : H.E) * h4'

theorem alphaH_integral (H : Host R) : IsIntegral ℤ (alphaH H) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (((H.d + 1) / 4 : ℕ) : ℤ), by monicity!, ?_⟩
  have h := alphaH_sq H
  rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
    algebraMap_int_eq, eq_intCast, Int.cast_natCast]
  linear_combination h

theorem star_alphaH (H : Host R) : (letI := H.cmStar; star (alphaH H)) = 1 - alphaH H := by
  rw [Formalism.BasicNotions.Examples₂.star_eq_conj]
  unfold alphaH
  rw [map_div₀, map_add (f := _), map_one, Formalism.MainNotions.UnusedSlot33.HK.conj_b]
  have h2 : H.conj (2 : H.E) = 2 := map_ofNat _ 2
  rw [h2]
  ring

theorem twoSplits (D : D7) : TwoSplits D := by
  intro P h2 hconj
  obtain ⟨a, ha⟩ : ∃ a : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E a = alphaH D.host :=
    ⟨⟨alphaH D.host, alphaH_integral D.host⟩, rfl⟩
  have inj := FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
  have coe : ∀ x : 𝓞 D.host.E, (x : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E x := fun _ => rfl
  have hP := P.isPrime
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  have hprod : a * (a - 1) ∈ P.asIdeal := by
    have heven : ((D.host.d + 1) / 4 : ℕ) = 2 * (((D.host.d + 1) / 4 : ℕ) / 2) := by omega
    have hk : ((((D.host.d + 1) / 4 : ℕ) : D.host.E)) = 2 * ((((D.host.d + 1) / 4 / 2 : ℕ) : D.host.E)) := by
      conv_lhs => rw [heven]
      push_cast; ring
    have he : a * (a - 1) = 2 * (-((((D.host.d + 1) / 4 / 2 : ℕ) : 𝓞 D.host.E))) := by
      apply inj
      have h := alphaH_sq D.host
      rw [hk] at h
      simp only [map_mul, map_sub, map_one, map_neg, map_natCast, map_ofNat, ha]
      linear_combination h
    rw [he]
    exact P.asIdeal.mul_mem_right _ h2
  have hstar : ∀ x : 𝓞 D.host.E, x ∈ P.asIdeal →
      ∃ c' ∈ P.asIdeal, algebraMap (𝓞 D.host.E) D.host.E c' = star (algebraMap (𝓞 D.host.E) D.host.E x) := hconj
  have hsa := star_alphaH D.host
  rcases hP.mem_or_mem hprod with hm | hm
  · obtain ⟨c', hc', hc'e⟩ := hstar a hm
    have h1 : a + c' = 1 := by
      apply inj
      rw [map_add (f := _), map_one, hc'e, ha, hsa]; ring
    exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (h1 ▸ P.asIdeal.add_mem hm hc'))
  · obtain ⟨c', hc', hc'e⟩ := hstar _ hm
    have h1 : -c' - (a - 1) = 1 := by
      apply inj
      rw [map_sub, map_neg, map_sub, map_one, hc'e, map_sub, map_one, star_sub, star_one, ha, hsa]; ring
    exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (h1 ▸ P.asIdeal.sub_mem (P.asIdeal.neg_mem hc') hm))

end Formalism.IndefR.Fin

end
end
