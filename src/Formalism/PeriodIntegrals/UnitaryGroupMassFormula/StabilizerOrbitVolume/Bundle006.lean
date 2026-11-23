module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle005
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
import Formalism.PeriodIntegrals.Bundle018

@[expose] public section

section

noncomputable section

namespace PI.VolStabSW

namespace LatFactsW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))

instance contSMul_herm (σ : E →ₐ[F] E) (a : ℕ) : ContinuousSMul (Fv F v) (HermR (Fv F v) σ a) := by
  refine ⟨continuous_induced_rng.2 ?_⟩
  show Continuous fun p : Fv F v × HermR (Fv F v) σ a =>
    p.1 • (p.2 : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))
  exact continuous_fst.smul (continuous_subtype_val.comp continuous_snd)

end LatFactsW

open scoped TensorProduct
open NumberField IsDedekindDomain Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW LatFactsW

end PI.VolStabSW
end
end

section

noncomputable section

namespace PI.VolStabSW

namespace SdUniqW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW

def ann {V : Type} (χ : V → V → ℂ) (L : Set V) : Set V := {y | ∀ x ∈ L, χ x y = 1}

section Lattice

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (χ : V → V → ℂ)
  (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (L : AddSubgroup V)


include hχ in
theorem transform_indicator (hLo : IsOpen (L : Set V)) (y : V) :
    ∫ x, (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y ∂μ =
      (ann χ L).indicator (fun _ => ((μ.real (L : Set V) : ℝ) : ℂ)) y := by
  classical
  by_cases hy : y ∈ ann χ L
  · rw [Set.indicator_of_mem hy]
    have e : (fun x => (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y) =
        (L : Set V).indicator (fun _ => (1 : ℂ)) := by
      funext x
      by_cases hx : x ∈ (L : Set V)
      · simp [Set.indicator, hx, hy x hx]
      · simp [Set.indicator, hx]
    rw [e, integral_indicator_const _ hLo.measurableSet]
    simp
  · rw [Set.indicator_apply, if_neg hy]
    simp only [ann, Set.mem_setOf_eq, not_forall] at hy
    obtain ⟨t, ht, hty⟩ := hy
    set f : V → ℂ := fun x => (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y with hf
    have key : ∫ x, f x ∂μ = χ t y * ∫ x, f x ∂μ := by
      calc ∫ x, f x ∂μ = ∫ x, f (t + x) ∂μ := (integral_add_left_eq_self f t).symm
        _ = ∫ x, χ t y * f x ∂μ := by
          congr 1
          funext x
          by_cases hx : x ∈ (L : Set V)
          · have htx : t + x ∈ L := L.add_mem ht hx
            have hx' : x ∈ L := hx
            simp [hf, Set.indicator, hx', htx, hχ]
          · have htx : t + x ∉ L := fun h => hx (by simpa using L.sub_mem h ht)
            have hx' : x ∉ L := hx
            simp [hf, Set.indicator, hx', htx]
        _ = χ t y * ∫ x, f x ∂μ := integral_const_mul _ _
    have h2 : (1 - χ t y) * ∫ x, f x ∂μ = 0 := by rw [sub_mul, one_mul, ← key, sub_self]
    rcases mul_eq_zero.mp h2 with h1 | h1
    · exact absurd (sub_eq_zero.mp h1).symm hty
    · exact h1


end Lattice

section Triv

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (χ : V → V → ℂ)

end Triv

section Nontriv

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

def DualAt {V : Type} [AddCommGroup V] [TopologicalSpace V] (B : V → V → Fv F v) : Prop :=
  ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧
    (∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ L, ∃ x' ∈ L, ∀ y, B x' y = s * B x y) ∧
    ∀ c : Fv F v, ∃ K, IsCompact K ∧
      {y | ∀ x ∈ L, B x y ∈ (fun s => c * s) '' (v.adicCompletionIntegers F : Set (Fv F v))} ⊆ K

theorem mem_of_psi (ψ0 : Fv F v → ℂ) (r0 t : Fv F v) (h0 : ψ0 r0 ≠ 1)
    (ht : ∀ s ∈ v.adicCompletionIntegers F, ψ0 (s * t) = 1) :
    t ∈ (fun s => r0 * s) '' (v.adicCompletionIntegers F : Set (Fv F v)) := by
  by_contra hn
  have ht0 : t ≠ 0 := fun h => hn ⟨0, zero_mem _, by simp [h]⟩
  have hs : r0 * t⁻¹ ∉ v.adicCompletionIntegers F := fun hs => h0 (by
    have := ht _ hs
    rwa [inv_mul_cancel_right₀ ht0] at this)
  have hs0 : r0 * t⁻¹ ≠ 0 := fun h => hs (by rw [h]; exact zero_mem _)
  have hr0 : r0 ≠ 0 := fun h => hs0 (by rw [h, zero_mul])
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, not_le] at hs
  have hlt := ((Valued.v : Valuation (Fv F v) _).one_lt_val_iff hs0).mp hs
  refine hn ⟨(r0 * t⁻¹)⁻¹, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (le_of_lt hlt), ?_⟩
  field_simp

end Nontriv

section Add

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

open Classical in
theorem singleV_add (v : HeightOneSpectrum (𝓞 F)) (r s : Fv F v) :
    singleV F v (r + s) = singleV F v r + singleV F v s := by
  apply Subtype.ext
  exact Pi.single_add v r s

theorem psiV_add (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (r s : Fv F v) :
    psiV F ψ v (r + s) = psiV F ψ v r * psiV F ψ v s := by
  have e : pairA F 0 (singleV F v (r + s)) =
      pairA F 0 (singleV F v r) + pairA F 0 (singleV F v s) := by
    rw [singleV_add]
    show ((0 : Ainf F), singleV F v r + singleV F v s) =
      ((0 : Ainf F) + 0, singleV F v r + singleV F v s)
    rw [add_zero]
  unfold psiV
  rw [e, AddChar.map_add_eq_mul]

theorem continuous_singleV (v : HeightOneSpectrum (𝓞 F)) : Continuous (singleV F v) := by
  classical
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let s0 : Fv F v → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
      (Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F)))) := fun y =>
    ⟨Pi.single v y, Filter.eventually_principal.2 fun w hw => by
      rw [Pi.single_eq_of_ne (by simpa using hw)]
      exact zero_mem _⟩
  have hc : Continuous s0 := by
    rw [RestrictedProduct.continuous_rng_of_principal_iff_forall]
    intro w
    by_cases hw : w = v
    · subst hw
      exact continuous_id.congr fun y => (Pi.single_eq_same _ _).symm
    · exact (continuous_const (y := (0 : Fv F w))).congr fun y => (Pi.single_eq_of_ne hw y).symm
  have e : singleV F v = fun y => RestrictedProduct.inclusion _ _ hS (s0 y) := by
    funext y
    apply RestrictedProduct.ext
    intro j
    rfl
  rw [e]
  exact (RestrictedProduct.continuous_inclusion hS).comp hc

theorem continuous_psiV (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (psiV F ψ v) := by
  unfold psiV
  exact hψ.comp (continuous_const.prodMk (continuous_singleV v))

variable (R : Type) [CommRing R] [Algebra F R]

theorem BR_add (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X T Y : Fin n → Fin M → R ⊗[F] E) : BR R σ J (T + X) Y = BR R σ J T Y + BR R σ J X Y := by
  simp only [BR, hR, Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem pairHerm_add (σ : E →ₐ[F] E) (n : ℕ) (S T U : HermR R σ n) :
    pairHerm R σ n (T + S) U = pairHerm R σ n T U + pairHerm R σ n S U := by
  simp only [pairHerm, AddSubgroup.coe_add, Matrix.add_apply, add_mul, Finset.sum_add_distrib,
    map_add, mul_add]

end Add

section ContY

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [T2Space R]

theorem continuous_trace_tens : Continuous (Algebra.trace R (R ⊗[F] E)) :=
  IsModuleTopology.continuous_of_linearMap _

end ContY

end SdUniqW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW SdUniqW

end PI.VolStabSW
end
end

section

noncomputable section

namespace PI.VolStabSW

namespace PositiveNearLattice

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

def crd (R : Type) [CommRing R] [Algebra F R] (y : R ⊗[F] E) (k : Fin d) : R :=
  (Algebra.TensorProduct.basis R b).repr y k

theorem crd_map {R S : Type} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]
    (f : R →ₐ[F] S) (y : R ⊗[F] E) (k : Fin d) :
    crd b S (Algebra.TensorProduct.map f (AlgHom.id F E) y) k = f (crd b R y k) := by
  induction y using TensorProduct.induction_on with
  | zero => simp [crd]
  | tmul r e =>
    simp [crd, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.map_tmul]
  | add x y hx hy =>
    simp only [crd] at hx hy ⊢
    rw [map_add (f := _), map_add (f := _), Finsupp.add_apply, hx, hy, map_add (f := _), Finsupp.add_apply, map_add (f := _)]

theorem crd_incl (R : Type) [CommRing R] [Algebra F R] (x : E) (k : Fin d) :
    crd b R (inclR R x) k = algebraMap F R (b.repr x k) := by
  simp [crd, inclR, Algebra.TensorProduct.basis_repr_tmul]

theorem eq_sum_crd (R : Type) [CommRing R] [Algebra F R] (y : R ⊗[F] E) :
    y = ∑ i, crd b R y i • ((1 : R) ⊗ₜ[F] b i) := by
  have := (Algebra.TensorProduct.basis R b).sum_repr y
  simp only [Algebra.TensorProduct.basis_apply] at this
  exact this.symm

variable [FiniteDimensional F E]

theorem continuous_crd (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] (k : Fin d) : Continuous (fun y : R ⊗[F] E => crd b R y k) :=
  IsModuleTopology.continuous_of_linearMap ((Algebra.TensorProduct.basis R b).coord k)

include b in
theorem continuous_map_tens {R S : Type} [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [CommRing S] [Algebra F S] [TopologicalSpace S] [IsTopologicalRing S]
    (f : R →ₐ[F] S) (hf : Continuous f) :
    Continuous (Algebra.TensorProduct.map f (AlgHom.id F E)) := by
  have e : (⇑(Algebra.TensorProduct.map f (AlgHom.id F E))) =
      fun y => ∑ k, f (crd b R y k) • ((1 : S) ⊗ₜ[F] b k) := by
    funext y
    rw [eq_sum_crd b S (Algebra.TensorProduct.map f (AlgHom.id F E) y)]
    simp only [crd_map]
  rw [e]
  refine continuous_finsetSum _ fun k _ => ?_
  exact continuous_smul.comp ((hf.comp (continuous_crd b R k)).prodMk continuous_const)

end Coord

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))

theorem isClosed_int : IsClosed (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
  (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).isClosed

theorem isClopen_latV (a M : ℕ) : IsClopen (latV (M := M) (n := a) b v) := by
  have hc : ∀ (x : Fin a) (i : Fin M) (k : Fin d),
      Continuous (fun Y : Fin a → Fin M → Fv F v ⊗[F] E => crd b (Fv F v) (Y x i) k) :=
    fun x i k => (continuous_crd b (Fv F v) k).comp ((continuous_apply i).comp (continuous_apply x))
  have e : latV (M := M) (n := a) b v = ⋂ x, ⋂ i, ⋂ k,
      (fun Y : Fin a → Fin M → Fv F v ⊗[F] E => crd b (Fv F v) (Y x i) k) ⁻¹'
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    ext Y
    simp [latV, crd]
  rw [e]
  refine ⟨isClosed_iInter fun x => isClosed_iInter fun i => isClosed_iInter fun k =>
    (isClosed_int v).preimage (hc x i k), isOpen_iInter_of_finite fun x =>
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k =>
    (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers v).preimage (hc x i k)⟩

theorem isCompact_latV (a M : ℕ) : IsCompact (latV (M := M) (n := a) b v) := by
  let L : (Fin a → Fin M → Fin d → Fv F v) → (Fin a → Fin M → Fv F v ⊗[F] E) :=
    fun c x i => ∑ k, c x i k • ((1 : Fv F v) ⊗ₜ[F] b k)
  have hL : Continuous L := by
    refine continuous_pi fun x => continuous_pi fun i => continuous_finsetSum _ fun k _ => ?_
    exact continuous_smul.comp
      (((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply x))).prodMk
        continuous_const)
  let K : Set (Fin a → Fin M → Fin d → Fv F v) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.pi Set.univ fun _ =>
      (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v
  refine (hK.image hL).of_isClosed_subset (isClopen_latV b v a M).isClosed ?_
  intro Y hY
  refine ⟨fun x i k => crd b (Fv F v) (Y x i) k, ?_, ?_⟩
  · simp only [K, Set.mem_pi, Set.mem_univ, true_implies]
    intro x i k
    exact hY x i k
  · funext x i
    exact (eq_sum_crd b (Fv F v) (Y x i)).symm

end Loc

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

variable [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E)



end Main

end PositiveNearLattice

open PositiveNearLattice
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

end PI.VolStabSW
end
end

section

noncomputable section

namespace PI.VolStabSW

open MeasureTheory Measure Topology Set Function
open scoped Pointwise ENNReal NNReal

section Gen

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]

end Gen

section Spec

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW PI.AdicCompletionValuation NumberField
open scoped TensorProduct

theorem um_countable_HFinIn (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) :
    Countable (HFinIn (AF F) σ J) := by
  have : Countable E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have : Countable (Matrix (Fin M) (Fin M) E) := inferInstanceAs (Countable (Fin M → Fin M → E))
  have : Countable (GL (Fin M) E) :=
    Function.Injective.countable (f := fun u : GL (Fin M) E => (u : Matrix (Fin M) (Fin M) E))
      (fun _ _ h => Units.ext h)
  have hx : ∀ x : HFinIn (AF F) σ J, ∃ u : GL (Fin M) E,
      Formalism.UG.bc (inclR (AF F)) u = ((x : HR (AF F) σ J) : GL (Fin M) (AF F ⊗[F] E)) := by
    intro x
    have h : ((x : HR (AF F) σ J) : GL (Fin M) (AF F ⊗[F] E)) ∈ HFin (AF F) σ J :=
      Subgroup.mem_subgroupOf.1 x.2
    unfold HFin at h
    obtain ⟨u, -, hu⟩ := Subgroup.mem_map.1 h
    exact ⟨u, hu⟩
  refine Function.Injective.countable (f := fun x => (hx x).choose) ?_
  intro x y hxy
  have h1 := (hx x).choose_spec
  have h2 := (hx y).choose_spec
  simp only at hxy
  rw [hxy] at h1
  exact Subtype.ext (Subtype.ext (h1.symm.trans h2))

end Spec

end PI.VolStabSW
end
end

section

noncomputable section

namespace PI.VolStabSW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW

def hermO {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ) :
    AddSubgroup (HermR (Fv F v) σ a) where
  carrier := {S | ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr
    ((S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j) k ∈ v.adicCompletionIntegers F}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    intro i j k
    simp only [AddSubgroup.coe_add, Matrix.add_apply, map_add (f := _), Finsupp.add_apply]
    exact add_mem (hx i j k) (hy i j k)
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    intro i j k
    simp only [ZeroMemClass.coe_zero, Matrix.zero_apply, map_zero, Finsupp.zero_apply]
    exact zero_mem _
  neg_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    intro i j k
    simp only [NegMemClass.coe_neg, Matrix.neg_apply, map_neg, Finsupp.neg_apply]
    exact neg_mem (hx i j k)

end PI.VolStabSW
end
end
