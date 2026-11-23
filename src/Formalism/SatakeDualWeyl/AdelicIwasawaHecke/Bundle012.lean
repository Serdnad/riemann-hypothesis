module

public import Formalism.SatakeDualWeyl.Bundle001
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Adelstab
public import Formalism.SatakeDualWeyl.DefsCS
public import Formalism.HermitianLattices.HermitianLatticesProofs.ClassSetAssembly
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle002
public import Formalism.HermitianLattices.HermitianLatticesProofs.ShortVectors
public import Formalism.HermitianLattices.HermitianLatticesProofs.TraceReal
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG

section L

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

omit [NumberField F] [Algebra F E] in
theorem adelstabL_den {κ : Type} [Fintype κ] (f : κ → E) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ i, IsIntegral ℤ ((m : E) * f i) := by
  classical
  have h1 : ∀ i, ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ ((m : E) * f i) := by
    intro i
    obtain ⟨⟨m, hm⟩, hint⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (nonZeroDivisors ℤ) (Rₘ := ℚ) (f i) (Algebra.IsIntegral.isIntegral (R := ℚ) (f i))
    refine ⟨m, nonZeroDivisors.ne_zero hm, ?_⟩
    simpa [Submonoid.smul_def, zsmul_eq_mul] using hint
  choose m hm0 hmi using h1
  refine ⟨∏ i, m i, Finset.prod_ne_zero_iff.mpr fun i _ => hm0 i, fun i => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ m (Finset.mem_univ i), Int.cast_mul,
    mul_comm ((m i : ℤ) : E), mul_assoc]
  refine IsIntegral.mul ?_ (hmi i)
  simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := ∏ j ∈ Finset.univ.erase i, m j)

theorem adelstabL_incl_int (e : E) (he : IsIntegral ℤ e) : ι e ∈ 𝒮 := by
  unfold inclE tensInt
  apply Subring.subset_closure
  left
  refine ⟨⟨e, ?_⟩, rfl⟩
  exact ⟨⟨e, he⟩, rfl⟩

theorem adelstabL_upper (Λ : Submodule (𝓞 E) (n → E)) (hfin : Module.Finite (𝓞 E) Λ) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ v ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ, ∀ i,
      levelafC E c * v i ∈ 𝒮 := by
  classical
  obtain ⟨s, hs⟩ : Λ.FG := Module.Finite.iff_fg.mp hfin
  obtain ⟨m, hm0, hm⟩ := adelstabL_den (fun p : s × n => (p.1 : n → E) p.2)
  have hΛ : ∀ x ∈ Λ, ∀ k, IsIntegral ℤ ((m : E) * x k) := by
    intro x hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => intro k; exact hm (⟨x, hx⟩, k)
    | zero => intro k; simp [isIntegral_zero]
    | add x y _ _ hx hy => intro k; simpa [mul_add] using (hx k).add (hy k)
    | smul r x _ hx =>
      intro k
      have : (m : E) * (r • x) k = algebraMap (𝓞 E) E r * ((m : E) * x k) := by
        simp [Algebra.smul_def]; ring
      rw [this]
      exact (RingOfIntegers.isIntegral_coe r).mul (hx k)
  refine ⟨(m : 𝓞 F), Int.cast_ne_zero.2 hm0, fun v hv => ?_⟩
  have hC : levelafC E (m : 𝓞 F) = ι (m : E) := by
    rw [← adelstab_incl_C, map_intCast]
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨x, hx, rfl⟩ := hv
    intro i
    rw [hC, ← map_mul]
    exact adelstabL_incl_int _ (hΛ x hx i)
  | zero => intro i; simp
  | add v w _ _ hv hw => intro i; rw [Pi.add_apply, mul_add]; exact add_mem (hv i) (hw i)
  | smul s v _ hv =>
    intro i
    rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, mul_left_comm]
    exact mul_mem s.2 (hv i)

theorem adelstabL_lower (Λ : Submodule (𝓞 E) (n → E))
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ v : n → 𝒜, (∀ i, v i ∈ 𝒮) →
      (fun i => levelafC E c * v i) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ := by
  classical
  have hk : ∀ k : n, ∃ N : ℕ, ∃ f : Fin N → E, ∃ w : Fin N → Λ,
      ∑ j, f j • (w j : n → E) = Pi.single k 1 := by
    intro k
    have : (Pi.single k 1 : n → E) ∈ Submodule.span E (Λ : Set (n → E)) := by
      rw [hspan]; exact Submodule.mem_top
    obtain ⟨N, f, w, h⟩ := Submodule.mem_span_set'.1 this
    exact ⟨N, f, fun j => ⟨w j, (w j).2⟩, h⟩
  choose N f w hw using hk
  obtain ⟨m, hm0, hm⟩ := adelstabL_den (fun p : Σ k : n, Fin (N k) => f p.1 p.2)
  have hsingle : ∀ k, (Pi.single k (m : E) : n → E) ∈ Λ := by
    intro k
    have : (Pi.single k (m : E) : n → E) =
        ∑ j, (⟨(m : E) * f k j, hm ⟨k, j⟩⟩ : 𝓞 E) • (w k j : n → E) := by
      have h1 : (Pi.single k (m : E) : n → E) = (m : E) • (Pi.single k 1 : n → E) := by
        rw [← Pi.single_smul', smul_eq_mul, mul_one]
      rw [h1, ← hw k, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← algebraMap_smul E, smul_smul]
      rfl
    rw [this]
    exact sum_mem fun j _ => Λ.smul_mem _ (w k j).2
  refine ⟨(m : 𝓞 F), Int.cast_ne_zero.2 hm0, fun v hv => ?_⟩
  have hC : levelafC E (m : 𝓞 F) = ι (m : E) := by
    rw [← adelstab_incl_C, map_intCast]
  have : (fun i => levelafC E (m : 𝓞 F) * v i) =
      ∑ k, (⟨v k, hv k⟩ : 𝒮) • (fun i => ι ((Pi.single k (m : E) : n → E) i)) := by
    ext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · show _ = (_ : 𝒮) • ι ((Pi.single i (m : E) : n → E) i)
      rw [Pi.single_eq_same, Subring.smul_def, smul_eq_mul, ← hC, mul_comm]
    · intro k _ hki
      show (_ : 𝒮) • ι ((Pi.single k (m : E) : n → E) i) = 0
      rw [Pi.single_apply, if_neg (Ne.symm hki), map_zero, smul_zero]
    · exact fun h => absurd (Finset.mem_univ i) h
  rw [this]
  exact sum_mem fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hsingle k, rfl⟩)

end L

theorem adelic_stabilizer_finite_lattice_holds : Formalism.UG.AdelicStabFiniteL := by
  intro F E _ _ _ _ _ n _ _ σ J hτ hH hdet hdef Λ hfin hspan g
  obtain ⟨c₁, hc₁, h₁⟩ := adelstabL_lower (F := F) Λ hspan
  obtain ⟨c₂, hc₂, h₂⟩ := adelstabL_upper (F := F) Λ hfin
  exact adelstab_core σ J hτ hH hdet hdef _ (levelAfL σ J Λ) inf_le_right c₁ c₂ hc₁ hc₂ h₁ h₂ g

end Formalism.UG.P
end
end

section

noncomputable section

open NumberField

namespace Formalism.UG.P

theorem csBdd_nat_mul {K : Type} [Field K] [NumberField K] (d : 𝓞 K) (hd : d ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ ∃ t : 𝓞 K, (m : 𝓞 K) = d * t := by
  classical
  refine ⟨Ideal.absNorm (Ideal.span {d}), ?_, ?_⟩
  · refine Nat.pos_of_ne_zero ?_
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hd
  · obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {d}))
    exact ⟨t, by rw [← ht, mul_comm]⟩

theorem class_set_finite_bounded_holds (hCovolOfDual : Formalism.UG.CS.CovolOfDual) :
    Formalism.UG.CS.ClassSetFiniteBdd := by
  intro K V _ _ _ _ _ _ _ _ h hsymm hpos d e hd he
  obtain ⟨N, ι, hι, hmul, hlat⟩ := Formalism.HermitianLatticesTheory.traceReal_main h hsymm hpos
  obtain ⟨C, hC⟩ := hCovolOfDual K V h hsymm hpos N ι hι e he
  obtain ⟨m, hm, t, ht⟩ := csBdd_nat_mul d hd
  let S : Set (Submodule (𝓞 K) V) := {M | Submodule.IsLattice K M ∧
    (∀ x ∈ M, ∀ y ∈ M, (d : K) * h x y ∈ (1 : Submodule (𝓞 K) K)) ∧
    (∀ x ∈ Formalism.HermitianLatticesTheory.dual h M, (e : K) • x ∈ M)}
  have hfull : ∀ M ∈ S, Submodule.IsFullLattice K M := by
    intro M hM
    let W := Submodule.span K (M : Set V)
    let b := Module.finBasis K W
    let f : V →ₗ[K] (Fin (Module.finrank K W) → K) := LinearMap.pi (fun i => h (b i : V))
    have hf : Function.Injective f := by
      apply LinearMap.ker_eq_bot.mp
      rw [Submodule.eq_bot_iff]
      intro x hx
      have hzero : (h.flip x).comp W.subtype = 0 := by
        apply b.ext
        intro i
        exact congrFun (LinearMap.mem_ker.mp hx) i
      have hz (y : V) (hy : y ∈ M) : h y x = 0 :=
        LinearMap.congr_fun hzero ⟨y, Submodule.subset_span hy⟩
      have hxd : x ∈ Formalism.HermitianLatticesTheory.dual h M := by
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf,
          Submodule.mem_comap, LinearMap.restrictScalars_apply]
        intro y hy
        rw [hz y hy]
        exact Submodule.zero_mem _
      -- The dual bound puts a nonzero scalar multiple of x in M, so positivity forces x = 0.
      have hxx := hsymm.eq_iff.mp (hz _ (hM.2.2 x hxd))
      rw [map_smul, smul_eq_mul] at hxx
      have heK : (e : K) ≠ 0 := fun he0 => he (RingOfIntegers.ext he0)
      have hxx0 := (mul_eq_zero.mp hxx).resolve_left heK
      by_contra hx0
      simpa [hxx0] using hpos x hx0
    have hdim := LinearMap.finrank_le_finrank_of_injective hf
    exact { hM.1 with
      span_eq_top := Submodule.eq_of_le_of_finrank_le le_top
        (by simpa only [finrank_top, Module.finrank_fin_fun] using hdim) }
  have hSd : ∀ M ∈ S, ∀ x ∈ M, ∀ y ∈ M, (m : K) * h x y ∈ (1 : Submodule (𝓞 K) K) := by
    intro M hM x hx y hy
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp (hM.2.1 x hx y hy)
    refine Submodule.mem_one.mpr ⟨t * a, ?_⟩
    have hmK : (m : K) = (d : K) * (t : K) := by
      have := congrArg (algebraMap (𝓞 K) K) ht
      simpa using this
    rw [map_mul, ha, hmK]
    have htc : algebraMap (𝓞 K) K t = (t : K) := rfl
    rw [htc]
    ring
  obtain ⟨s, -, hs⟩ := Formalism.HermitianLatticesTheory.classSetFinite_core Formalism.HermitianLatticesTheory.shortVectors
    Formalism.HermitianLatticesTheory.finIntermediate Formalism.HermitianLatticesTheory.isomOfTrace h hpos N ι hι hmul m hm C S hSd
    (fun M hM => hlat M (hfull M hM)) (fun M hM _ _ => hC M hM.1 hM.2.2)
  exact ⟨s, fun M hM hdM heM => hs M ⟨hM, hdM, heM⟩⟩

end Formalism.UG.P
end
end
