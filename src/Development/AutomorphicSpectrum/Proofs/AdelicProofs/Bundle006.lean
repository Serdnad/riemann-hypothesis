module

public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle003
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle004
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

theorem _root_.GlobalTheory.T.log_ideal_mul_span_map : ∀ (E : Type) [Field E] [NumberField E] (p : Nat.Primes) (j : 𝓞 E →+* ℂ_[p]), Function.Injective j → (∀ I J : Ideal (𝓞 E), I ≠ ⊥ → J ≠ ⊥ → logIdeal j (I * J) = logIdeal j I + logIdeal j J) ∧ (∀ a : 𝓞 E, logIdeal j (Ideal.span {a}) = Real.log ‖j a‖) ∧ ∀ e : 𝓞 E ≃+* 𝓞 E, ∀ I : Ideal (𝓞 E), logIdeal j (I.map (e : 𝓞 E →+* 𝓞 E)) = logIdeal (j.comp (e : 𝓞 E →+* 𝓞 E)) I := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.logIdeal_mul_span_map | exact GlobalTheory.CompanionTheory.Ar.Fl.logIdeal_mul_span_map | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.logIdeal_mul_span_map <;> assumption)
end

section

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

theorem _root_.GlobalTheory.T.logIdeal_support_finite : ∀ (E : Type) [Field E] [NumberField E] (I : Ideal (𝓞 E)), I ≠ ⊥ → {p : Nat.Primes | ∃ j : 𝓞 E →+* ℂ_[p], logIdeal j I ≠ 0}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.finite_logIdeal_ne_zero | exact GlobalTheory.CompanionTheory.Ar.Fl.finite_logIdeal_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.finite_logIdeal_ne_zero <;> assumption)
end

section

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

theorem _root_.GlobalTheory.T.logNorms_ext_degree_adelic : ∀ (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (f : k →+* k') (N : LogNorms k), (N.ext f).deg = N.deg ∧ ((N.ext f).IsAdelic ↔ N.IsAdelic) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.logNorms_ext_deg_isAdelic | exact GlobalTheory.CompanionTheory.Ar.Fl.logNorms_ext_deg_isAdelic | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.logNorms_ext_deg_isAdelic <;> assumption)
end

section

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

theorem _root_.GlobalTheory.T.padic_logIdeal_max_element : ∀ (E : Type) [Field E] [NumberField E] (p : Nat.Primes) (j : 𝓞 E →+* ℂ_[p]) (I : Ideal (𝓞 E)), Function.Injective j → I ≠ ⊥ → ∃ a ∈ I, a ≠ 0 ∧ (∀ b ∈ I, ‖j b‖ ≤ ‖j a‖) ∧ logIdeal j I = Real.log ‖j a‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.exists_logIdeal_attained | exact GlobalTheory.CompanionTheory.Ar.Fl.exists_logIdeal_attained | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.exists_logIdeal_attained <;> assumption)
end

section

open NumberField TensorProduct GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.Lines Matrix
open scoped ComplexOrder nonZeroDivisors

theorem _root_.GlobalTheory.T.hermitian_lattice_degree_eq_bundle_degree : ∀ (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L) (F : Submodule (𝓞 L) B.carrier) (i : ℕ) (f : Fin i → F) (c : F →ₗ[𝓞 L] (Fin i → L)) (Fl : HermLattice L i), LinearIndependent (𝓞 L) f → i = B.rank F → Function.Injective c → (∀ j, c (f j) = Pi.single j 1) → Fl.lattice = LinearMap.range c → (∀ σ, Fl.metric σ = gramMat B σ (fun j => (f j : B.carrier))) → Fl.degree = B.degreeWith F f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Lines.degree_eq_degreeWith | exact GlobalTheory.CompanionTheory.Ar.Lines.degree_eq_degreeWith | (intros; apply GlobalTheory.CompanionTheory.Ar.Lines.degree_eq_degreeWith <;> assumption)
end

section

open NumberField GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.Adelic.SatLine

section aux

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem smul_field (c : 𝓞 K) (y : K) : c • y = (c : K) * y := Algebra.smul_def c y

theorem smul_coord (c : 𝓞 K) (x : Fin n → K) (i : Fin n) : (c • x) i = (c : K) * x i :=
  smul_field c (x i)

theorem exists_smul_mem (M : Submodule (𝓞 K) (Fin n → K)) {x : Fin n → K}
    (hx : x ∈ Submodule.span K (M : Set (Fin n → K))) :
    ∃ c : 𝓞 K, c ≠ 0 ∧ c • x ∈ M :=
  _root_.UpperTheory.Reformulated.B.P6.r03a.GlobalTheory.CompanionTheory.Adelic.SatLine.exists_smul_mem M hx

theorem exists_denominator {M : Submodule (𝓞 K) (Fin n → K)} (hM : M.FG) (j : Fin n) (a : K) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ x ∈ M, ∃ t : 𝓞 K, (d : K) * (a * x j) = t := by
  classical
  obtain ⟨S, hS⟩ := hM
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (𝓞 K)⁰
    (S.image fun x : Fin n → K => a * x j)
  refine ⟨b, nonZeroDivisors.ne_zero b.2, fun x hx => ?_⟩
  rw [← hS] at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨t, ht⟩ := hb _ (Finset.mem_image_of_mem _ (Finset.mem_coe.mp h))
    refine ⟨t, ?_⟩
    have h1 : algebraMap (𝓞 K) K t = (b : 𝓞 K) • (a * x j) := ht
    rw [Algebra.smul_def] at h1
    exact h1.symm
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    refine ⟨s + t, ?_⟩
    have : ((s + t : 𝓞 K) : K) = (s : K) + (t : K) := rfl
    rw [this, ← hs, ← ht, Pi.add_apply]
    ring
  | smul r x _ hx =>
    obtain ⟨s, hs⟩ := hx
    refine ⟨r * s, ?_⟩
    have : ((r * s : 𝓞 K) : K) = (r : K) * (s : K) := rfl
    rw [this, ← hs, smul_coord]
    ring

end aux

theorem saturatedLine_eq_ideal_div :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (M : Submodule (𝓞 K) (Fin n → K)), M.FG →
      Submodule.span K (M : Set (Fin n → K)) = ⊤ → ∀ v : Fin n → K, v ≠ 0 →
      ∃ (I : Ideal (𝓞 K)) (d : 𝓞 K), I ≠ ⊥ ∧ d ≠ 0 ∧ (∀ t ∈ I, ((t : K) / (d : K)) • v ∈ M) ∧
        genIndex (M ⊓ (Submodule.span K (Set.range fun _ : Fin 1 => v)).restrictScalars (𝓞 K)).toAddSubgroup
          (Submodule.span (𝓞 K) (Set.range fun _ : Fin 1 => v)).toAddSubgroup =
        |((Algebra.norm ℚ (d : K) : ℚ) : ℝ)| / (I.absNorm : ℝ) := by
  intro K _ _ n M hM hspan v hv
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := Function.ne_iff.mp hv
  obtain ⟨d, hd, hden⟩ := exists_denominator hM j (v j)⁻¹
  have hdK : (d : K) ≠ 0 := fun h => hd (RingOfIntegers.ext h)
  let g : 𝓞 K →ₗ[𝓞 K] (Fin n → K) := LinearMap.toSpanSingleton (𝓞 K) _ ((d : K)⁻¹ • v)
  have hg_apply : ∀ t : 𝓞 K, g t = ((t : K) / (d : K)) • v := by
    intro t
    ext i
    simp only [g, LinearMap.toSpanSingleton_apply, Pi.smul_apply, smul_field, smul_eq_mul]
    rw [div_eq_mul_inv, mul_assoc]
  have hginj : Function.Injective g := by
    intro s t h
    have h1 := congrFun h j
    rw [hg_apply, hg_apply] at h1
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    exact RingOfIntegers.ext ((div_left_inj' hdK).mp (mul_right_cancel₀ hj h1))
  let I : Ideal (𝓞 K) := M.comap g
  have hmemI : ∀ t, t ∈ I ↔ ((t : K) / (d : K)) • v ∈ M := fun t => by
    change g t ∈ M ↔ _
    rw [hg_apply]
  have hI : I ≠ ⊥ := by
    obtain ⟨c, hc, hcv⟩ := exists_smul_mem M (show v ∈ Submodule.span K (M : Set (Fin n → K)) by
      rw [hspan]; exact Submodule.mem_top)
    intro h
    have hcd : c * d ∈ I := by
      rw [hmemI]
      have e : (((c * d : 𝓞 K) : K) / (d : K)) • v = c • v := by
        ext i
        have : ((c * d : 𝓞 K) : K) = (c : K) * (d : K) := rfl
        rw [smul_coord, Pi.smul_apply, this, smul_eq_mul]
        field_simp
      rw [e]
      exact hcv
    rw [h, Ideal.mem_bot] at hcd
    exact mul_ne_zero hc hd hcd
  refine ⟨I, d, hI, hd, fun t ht => (hmemI t).1 ht, ?_⟩
  have hline : M ⊓ (Submodule.span K (Set.range fun _ : Fin 1 => v)).restrictScalars (𝓞 K) =
      Submodule.map g I := by
    ext x
    simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, Set.range_const,
      Submodule.mem_span_singleton, Submodule.mem_map]
    constructor
    · rintro ⟨hx, c, rfl⟩
      obtain ⟨t, ht⟩ := hden _ hx
      have hc : (t : K) / (d : K) = c := by
        rw [← ht, Pi.smul_apply, smul_eq_mul]
        field_simp
      have hgt : g t = c • v := by rw [hg_apply, hc]
      exact ⟨t, (show g t ∈ M by rw [hgt]; exact hx), hgt⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨ht, (t : K) / (d : K), (hg_apply t).symm⟩
  have hN : Submodule.span (𝓞 K) (Set.range fun _ : Fin 1 => v) =
      Submodule.map g (Ideal.span {d}) := by
    have e : g d = v := by rw [hg_apply, div_self hdK, one_smul]
    rw [Set.range_const, Ideal.span, Submodule.map_span, Set.image_singleton, e]
  have hd0 : (Ideal.span {d} : Ideal (𝓞 K)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hd
  have hnorm : (((Ideal.span {d} : Ideal (𝓞 K))).absNorm : ℝ) =
      |((Algebra.norm ℚ (d : K) : ℚ) : ℝ)| := by
    rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs, ← Rat.cast_intCast,
      Algebra.coe_norm_int]
  rw [hline, hN, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup, genIndex,
    AddSubgroup.relIndex_map_map_of_injective _ _ hginj,
    AddSubgroup.relIndex_map_map_of_injective _ _ hginj, ← genIndex,
    IdealIndexPlaces.genIndex_ideal hI hd0, hnorm]

end GlobalTheory.CompanionTheory.Adelic.SatLine
end

section

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

theorem _root_.GlobalTheory.T.sum_embeddings_base_change : ∀ (k k' A : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] [Field A] [CharZero A] [IsAlgClosed A] (f : k →+* k') (F : (k →+* A) → ℝ), (Module.finrank ℚ k : ℝ) * ∑ j : k' →+* A, F (j.comp f) = (Module.finrank ℚ k' : ℝ) * ∑ j : k →+* A, F j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.finrank_mul_sum_comp_eq | exact GlobalTheory.CompanionTheory.Ar.Fl.finrank_mul_sum_comp_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.finrank_mul_sum_comp_eq <;> assumption)
end
