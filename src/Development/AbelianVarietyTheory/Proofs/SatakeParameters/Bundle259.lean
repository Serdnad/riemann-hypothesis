module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeScalarOnSphericalVectors
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle016
public import Formalism.AlgebraicWeights.IsAlgWeight
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle110
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle411
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle068
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.ParaLevel

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem trivOutside_one (T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) :
    TrivOutside T (1 : GAf L n) := by
  intro w _
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem detDD_one (s : SplitPlace L) (r : ℕ) :
    NG.detDD s r (1 : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) = 1 := by
  unfold NG.detDD
  have : (Matrix.of fun a b : {x : Fin n // r ≤ x.val} =>
      ((1 : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
        Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a.1 b.1) = 1 := by
    ext a b
    simp [Matrix.one_apply, Subtype.ext_iff]
  rw [this, Matrix.det_one]

theorem continuous_detDD (s : SplitPlace L) (r : ℕ) :
    Continuous (NG.detDD (n := n) s r) := by
  unfold NG.detDD
  refine Continuous.matrix_det ?_
  refine continuous_pi fun a => continuous_pi fun b => ?_
  exact (Units.continuous_val (M := Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))).matrix_elem a.1 b.1

section main
variable (s : SplitPlace L) (r : ℕ) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ)
  (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ)

def paraSub (hP : NG.LevelPara J χ s r ξ) :
    Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) where
  carrier := {g | NG.ParaRT s r g}
  one_mem' := by
    have h := (hP.mem 1 (trivOutside_one _)).1 J.one_mem
    change NG.ParaRT s r 1
    rw [map_one] at h
    exact h
  mul_mem' := by
    intro g h hg hh
    obtain ⟨x, hx, rfl⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s g
    obtain ⟨y, hy, rfl⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s h
    have hxy := GlobalTheory.SatInd.CosetFin.trivOutside_mul hx hy
    rw [← map_mul]
    exact (hP.mem _ hxy).1 (J.mul_mem ((hP.mem x hx).2 hg) ((hP.mem y hy).2 hh))
  inv_mem' := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s g
    have hi := GlobalTheory.SatInd.CosetFin.trivOutside_inv hx
    show NG.ParaRT s r (s.loc n x)⁻¹
    rw [← map_inv]
    exact (hP.mem _ hi).1 (J.inv_mem ((hP.mem x hx).2 hg))

end main
end GlobalTheory.ParaLevel

namespace GlobalTheory.ParaLevel
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
section main2
variable {s : SplitPlace L} {r : ℕ} {J : Subgroup (GAf L n)} {χ : J →* ℂˣ}
  {ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ}

def lift (s : SplitPlace L) (g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : GAf L n :=
  (GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s g).choose

theorem lift_triv (g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
    TrivOutside {s.v} (lift s g) :=
  (GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s g).choose_spec.1

theorem loc_lift (g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
    s.loc n (lift s g) = g :=
  (GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s g).choose_spec.2

theorem lift_mem (hP : NG.LevelPara J χ s r ξ) (g : paraSub s r J χ ξ hP) : lift s g.1 ∈ J :=
  (hP.mem _ (lift_triv g.1)).2 (by rw [loc_lift]; exact g.2)

def thetaFun (hP : NG.LevelPara J χ s r ξ) (g : paraSub s r J χ ξ hP) : ℂˣ :=
  χ ⟨lift s g.1, lift_mem hP g⟩

theorem chi_eq (hP : NG.LevelPara J χ s r ξ) (κ : GAf L n) (hκ : TrivOutside {s.v} κ) (hJ : κ ∈ J)
    (h : s.loc n κ ∈ paraSub s r J χ ξ hP) : χ ⟨κ, hJ⟩ = thetaFun hP ⟨s.loc n κ, h⟩ := by
  unfold thetaFun
  set κ₀ := lift s (s.loc n κ) with hκ₀
  have h0 : κ₀ ∈ J := lift_mem hP ⟨s.loc n κ, h⟩
  have ht : TrivOutside {s.v} (κ * κ₀⁻¹) :=
    GlobalTheory.SatInd.CosetFin.trivOutside_mul hκ (GlobalTheory.SatInd.CosetFin.trivOutside_inv (lift_triv _))
  have hl : s.loc n (κ * κ₀⁻¹) = 1 := by
    rw [map_mul, map_inv, hκ₀, loc_lift, mul_inv_cancel]
  have hδ : κ * κ₀⁻¹ ∈ J := J.mul_mem hJ (J.inv_mem h0)
  have hc : χ ⟨κ * κ₀⁻¹, hδ⟩ = 1 := by
    rw [hP.chr _ hδ ht 1 (by rw [hl, detDD_one]; rfl), map_one]
  have hprod : (⟨κ, hJ⟩ : J) = ⟨κ * κ₀⁻¹, hδ⟩ * ⟨κ₀, h0⟩ := by
    apply Subtype.ext; simp
  rw [hprod, map_mul, hc, one_mul]

def theta (hP : NG.LevelPara J χ s r ξ) : paraSub s r J χ ξ hP →* ℂˣ where
  toFun := thetaFun hP
  map_one' := by
    have h1 : s.loc n (1 : GAf L n) ∈ paraSub s r J χ ξ hP := by rw [map_one]; exact (paraSub s r J χ ξ hP).one_mem
    have := chi_eq hP 1 (trivOutside_one _) J.one_mem h1
    have e : (⟨s.loc n 1, h1⟩ : paraSub s r J χ ξ hP) = 1 := by apply Subtype.ext; simp
    rw [e] at this
    rw [← this]
    exact map_one χ
  map_mul' := by
    intro g h
    set x := lift s g.1
    set y := lift s h.1
    have hx := lift_mem hP g
    have hy := lift_mem hP h
    have hxy : TrivOutside {s.v} (x * y) :=
      GlobalTheory.SatInd.CosetFin.trivOutside_mul (lift_triv _) (lift_triv _)
    have hm : s.loc n (x * y) ∈ paraSub s r J χ ξ hP := by
      rw [map_mul, loc_lift, loc_lift]; exact (g * h).2
    have := chi_eq hP (x * y) hxy (J.mul_mem hx hy) hm
    have e : (⟨s.loc n (x * y), hm⟩ : paraSub s r J χ ξ hP) = g * h := by
      apply Subtype.ext; simp [x, y, loc_lift]
    rw [e] at this
    rw [← this]
    have e2 : (⟨x * y, J.mul_mem hx hy⟩ : J) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [e2, map_mul]
    rfl

end main2
end GlobalTheory.ParaLevel

namespace GlobalTheory.ParaLevel

theorem exists_parahoric_char : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (r : ℕ) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), NG.LevelPara J χ s r ξ → (∃ N : ℕ, ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1) → ∃ (K : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))) (θ : K →* ℂˣ), (∀ g, g ∈ K ↔ NG.ParaRT s r g) ∧ (∀ g (h : g ∈ K) (d : (s.v.adicCompletion (maximalRealSubfield L))ˣ), (d : s.v.adicCompletion (maximalRealSubfield L)) = NG.detDD s r g → θ ⟨g, h⟩ = ξ d) ∧ (∀ g ∈ K, g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) ∧ IsOpen (θ.ker : Set K) ∧ ∀ κ, TrivOutside {s.v} κ → ∀ (hJ : κ ∈ J) (h : s.loc n κ ∈ K), χ ⟨κ, hJ⟩ = θ ⟨s.loc n κ, h⟩ := by
  intro L _ _ _ n s r J χ ξ hP hξ
  obtain ⟨N, hN⟩ := hξ
  refine ⟨paraSub s r J χ ξ hP, theta hP, fun g => Iff.rfl, ?_, fun g hg => hg.1, ?_, ?_⟩
  · intro g h d hd
    show χ ⟨lift s g, lift_mem hP ⟨g, h⟩⟩ = ξ d
    exact hP.chr _ _ (lift_triv g) d (by rw [loc_lift]; exact hd)
  · apply Subgroup.isOpen_of_mem_nhds
    have hc : Continuous fun g : paraSub s r J χ ξ hP => NG.detDD s r g.1 :=
      (continuous_detDD s r).comp continuous_subtype_val
    have h1 : NG.detDD s r ((1 : paraSub s r J χ ξ hP) : GL (Fin n) _) = 1 := detDD_one s r
    obtain ⟨π, hπ⟩ := s.v.valuation_exists_uniformizer (maximalRealSubfield L)
    set a : s.v.adicCompletion (maximalRealSubfield L) := ((π : maximalRealSubfield L) : s.v.adicCompletion (maximalRealSubfield L)) ^ N
    have ha : Valued.v a = WithZero.exp (-(N : ℤ)) := by
      simp only [a, map_pow, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ, ← WithZero.exp_nsmul]
      congr 1; simp
    have ha0 : (Valued.v a) ≠ 0 := by rw [ha]; simp
    have hnhds : {x : s.v.adicCompletion (maximalRealSubfield L) |
        Valued.v (x - 1) < WithZero.exp (-(N : ℤ))} ∈ nhds (1 : s.v.adicCompletion (maximalRealSubfield L)) := by
      refine Valued.mem_nhds.2 ⟨Units.mk0 (Valued.v.restrict a) (by rwa [ne_eq, Valuation.restrict_eq_zero_iff]), ?_⟩
      intro y hy
      simp only [Set.mem_setOf_eq, Units.val_mk0] at hy ⊢
      rw [← ha]
      exact (Valuation.restrict_lt_iff _).1 hy
    have hpre := hc.tendsto 1 (by rw [h1]; exact hnhds)
    refine Filter.mem_of_superset hpre ?_
    intro g hg
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hg
    have hne : NG.detDD s r g.1 ≠ 0 := by
      intro h0
      rw [h0, zero_sub, Valuation.map_neg, Valuation.map_one] at hg
      exact absurd hg (not_lt.2 (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega))
    have hθ : theta hP g = ξ (Units.mk0 _ hne) := by
      show χ ⟨lift s g.1, lift_mem hP g⟩ = _
      exact hP.chr _ _ (lift_triv g.1) _ (by rw [loc_lift]; rfl)
    show theta hP g = 1
    rw [hθ]
    exact hN _ (le_of_lt hg)
  · intro κ hκ hJ h
    exact chi_eq hP κ hκ hJ h

end GlobalTheory.ParaLevel
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BiInvScalar

open GlobalTheory.SphLabelOps GlobalTheory.HeckeScalarSph

theorem biInv_scalar : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)), NG.IsIrrRep ρ S → ∀ (s : SplitPlace L) (Ds : Set (GAf L n)), (∀ x ∈ Ds, TrivOutside {s.v} x) → (∀ x ∈ Ds, ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → x * κ ∈ Ds ∧ κ * x ∈ Ds) → ∀ R : Finset (GAf L n), (∀ γ ∈ R, γ ∈ Ds) → (∀ x ∈ Ds, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n) → ∃ c : ℂ, ∀ f ∈ S, (∀ κ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f := by
  intro L _ _ _ n W _ _ ρ S hS s Ds hDt hDs R hRD hRu
  classical
  obtain ⟨hdec, hcomm, -⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  choose Rb hRb using exists_repsU (L := L) (n := n) s.v
  let K := locK (L := L) n s.v
  let dc : GAf L n → Set (GAf L n) := fun a => {x | ∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * a * k₂}

  have hdcD : ∀ a ∈ Ds, ∀ x ∈ dc a, x ∈ Ds := by
    rintro a ha _ ⟨k₁, h₁, k₂, h₂, rfl⟩
    exact (hDs _ (hDs a ha k₁ h₁.1 h₁.2).2 k₂ h₂.1 h₂.2).1
  have hdc_eq : ∀ a b, b ∈ dc a → dc b = dc a := by
    rintro a _ ⟨k₁, h₁, k₂, h₂, rfl⟩
    ext x
    constructor
    · rintro ⟨l₁, i₁, l₂, i₂, rfl⟩
      exact ⟨l₁ * k₁, K.mul_mem i₁ h₁, k₂ * l₂, K.mul_mem h₂ i₂, by group⟩
    · rintro ⟨l₁, i₁, l₂, i₂, rfl⟩
      exact ⟨l₁ * k₁⁻¹, K.mul_mem i₁ (K.inv_mem h₁), k₂⁻¹ * l₂, K.mul_mem (K.inv_mem h₂) i₂, by group⟩
  have hself : ∀ a, a ∈ dc a := fun a => ⟨1, K.one_mem, 1, K.one_mem, by group⟩

  let fib : GAf L n → Finset (GAf L n) := fun a => R.filter (fun γ => dc γ = dc a)
  have hfib : ∀ α ∈ R, (∀ γ ∈ fib α, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * α * k₂) ∧
      ∀ x, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * α * k₂) → ∃! γ, γ ∈ fib α ∧ γ⁻¹ * x ∈ Umax L n := by
    intro α hα
    refine ⟨fun γ hγ => ?_, fun x hx => ?_⟩
    · have e := (Finset.mem_filter.1 hγ).2
      have : γ ∈ dc α := e ▸ hself γ
      exact this
    · have hxD : x ∈ Ds := hdcD α (hRD α hα) x hx
      obtain ⟨γ, ⟨hγ, hu⟩, huniq⟩ := hRu x hxD
      have ht : TrivOutside {s.v} (γ⁻¹ * x) := triv_mul (triv_inv (hDt γ (hRD γ hγ))) (hDt x hxD)
      have hγdc : γ ∈ dc x := ⟨1, K.one_mem, (γ⁻¹ * x)⁻¹, K.inv_mem ⟨hu, ht⟩, by group⟩
      have e : dc γ = dc α := (hdc_eq x γ hγdc).trans (hdc_eq α x hx)
      exact ⟨γ, ⟨Finset.mem_filter.2 ⟨hγ, e⟩, hu⟩, fun δ hδ => huniq δ ⟨(Finset.mem_filter.1 hδ.1).1, hδ.2⟩⟩
  have hfibTriv : ∀ α ∈ R, TrivOutside {s.v} α := fun α hα => hDt α (hRD α hα)
  have conv : ∀ {b x : GAf L n}, (∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ x = k₁ * b * k₂) ↔
      ∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, x = k₁ * b * k₂ :=
    ⟨fun ⟨k₁, h₁, k₂, h₂, t₁, t₂, e⟩ => ⟨k₁, ⟨h₁, t₁⟩, k₂, ⟨h₂, t₂⟩, e⟩,
      fun ⟨k₁, h₁, k₂, h₂, e⟩ => ⟨k₁, h₁.1, k₂, h₂.1, h₁.2, h₂.2, e⟩⟩

  have hsplit : ∀ (F : GAf L n → (GAf L n → W)), ∑ γ ∈ R, F γ = ∑ D ∈ R.image dc, ∑ γ ∈ R.filter (fun γ => dc γ = D), F γ :=
    fun F => (Finset.sum_fiberwise_of_maps_to (fun γ hγ => Finset.mem_image_of_mem dc hγ) F).symm
  have hD : ∀ D ∈ R.image dc, ∃ α ∈ R, R.filter (fun γ => dc γ = D) = fib α := by
    intro D hD
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 hD
    exact ⟨α, hα, rfl⟩
  let T : (GAf L n → W) →ₗ[ℂ] (GAf L n → W) := ∑ γ ∈ R, rtHom L n W γ
  have hT : ∀ x, T x = ∑ γ ∈ R, rtHom L n W γ x := fun x => LinearMap.sum_apply _ _ _
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ x ∈ GlobalTheory.SphScalar.fixS (rtHom L n W) S (locK n s.v), T x = c • x := by
    refine GlobalTheory.SphScalar.abs_scalar (rtHom L n W) S hS.1.stable
      (fun S' hle hst => hS.2.2 S' ⟨hle.trans hS.1.le, hst⟩ hle) (rank_le hS) (locK n s.v)
      {x | TrivOutside {s.v} x} {y | TrivOutside {s.v}ᶜ y}
      (fun g => by obtain ⟨x, y, hx, hy, e⟩ := hdec g; exact ⟨x, hx, y, hy, e⟩)
      (fun κ hκ b hb => (hcomm κ b hκ.2 hb).eq) Rb (fun b hb => reps_of_repsU hb (hRb b)) T ?_ ?_ ?_
    · intro x hx
      rw [hT]
      refine ⟨S.sum_mem fun γ _ => hS.1.stable γ x hx.1, fun κ hκ => ?_⟩

      rw [hsplit, map_sum]
      refine Finset.sum_congr rfl fun D hDm => ?_
      obtain ⟨α, hα, e⟩ := hD D hDm
      rw [e]
      have hRα := reps_of_repsU (hfibTriv α hα) (hfib α hα)

      rw [map_sum]
      have := hRα.sum_eq hRα hκ (fun g => rtHom L n W g x)
        (fun y l hl => by rw [map_mul, Module.End.mul_apply, hx.2 l hl])
      simpa only [map_mul, Module.End.mul_apply] using this
    · intro b hb x _

      rw [hT, hT, map_sum]
      refine Finset.sum_congr rfl fun γ hγ => ?_
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, (hcomm γ b (hfibTriv γ hγ) hb).eq]
    · intro b hb x hx
      rw [hT, hT]
      rw [hsplit (fun γ => rtHom L n W γ (∑ δ ∈ Rb b, rtHom L n W δ x)), hsplit (fun γ => rtHom L n W γ x)]
      refine Eq.trans ?_ ((Finset.sum_congr rfl fun δ _ => map_sum (rtHom L n W δ) _ _).trans Finset.sum_comm).symm
      refine Finset.sum_congr rfl fun D hDm => ?_
      obtain ⟨α, hα, e⟩ := hD D hDm
      rw [e]
      exact GlobalTheory.T.splitPlace_doubleCosetOperators_commute_spherical L n W s α b (fib α) (Rb b) (hfibTriv α hα) hb (fun y hy => (hfib α hα).2 y (conv.1 hy))
        (fun γ hγ => conv.2 ((hfib α hα).1 γ hγ)) (fun y hy => (hRb b).2 y (conv.1 hy))
        (fun γ hγ => conv.2 ((hRb b).1 γ hγ)) x (fun κ h1 h2 => hx.2 κ ⟨h1, h2⟩)
  refine ⟨c, fun f hf hfix => ?_⟩
  have e := hc f ⟨hf, fun κ hκ => hfix κ hκ⟩
  rw [hT] at e
  exact e

end GlobalTheory.BiInvScalar

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open TensorProduct

namespace GlobalTheory.ConjLoc

theorem proj_conjSP {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (a : AL L) :
    (GlobalTheory.TypeTame.conjSP s).proj a = s.proj (conjAL L a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x b =>
    simp [SplitPlace.proj, conjAL, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.map_tmul]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem loc_conjSP : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (x : GAf L n), ((GlobalTheory.TypeTame.conjSP s).loc n x).val = ((s.loc n x)⁻¹ : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))).val.transpose := by
  intro L _ _ _ n s x
  have hx : (x.1 : Matrix (Fin n) (Fin n) (AL L)) * conjT (conjAL L) (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := x.2
  have h1 : (s.loc n x).val * ((GlobalTheory.TypeTame.conjSP s).loc n x).val.transpose = 1 := by
    have e : ((GlobalTheory.TypeTame.conjSP s).loc n x).val.transpose
        = (conjT (conjAL L) (x.1 : Matrix (Fin n) (Fin n) (AL L))).map s.proj := by
      refine Matrix.ext fun i j => ?_
      exact proj_conjSP s _
    have e' : (s.loc n x).val = (x.1 : Matrix (Fin n) (Fin n) (AL L)).map s.proj := rfl
    rw [e, e', ← Matrix.map_mul, hx, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 := Units.inv_eq_of_mul_eq_one_right h1
  rw [h2, Matrix.transpose_transpose]

end GlobalTheory.ConjLoc
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TypeTame

def invTranspose {R : Type} [CommRing R] (n : ℕ) : GL (Fin n) R →* GL (Fin n) R where
  toFun g := ⟨(g⁻¹).val.transpose, g.val.transpose,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' a b := by
    apply Units.ext
    simp only [Units.val_mul, mul_inv_rev, Matrix.transpose_mul]

theorem invTranspose_val {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) :
    (invTranspose n g).val = (g⁻¹).val.transpose := rfl

theorem invTranspose_inv_val {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) :
    ((invTranspose n g)⁻¹).val = g.val.transpose := rfl

theorem invTranspose_invTranspose {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) :
    invTranspose n (invTranspose n g) = g := by
  apply Units.ext
  rw [invTranspose_val, invTranspose_inv_val, Matrix.transpose_transpose]

theorem continuous_invTranspose {R : Type} [CommRing R] [TopologicalSpace R] (n : ℕ) :
    Continuous (invTranspose (R := R) n) := by
  rw [Units.continuous_iff]
  exact ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

theorem invTranspose_mem_GLint {F : Type} [Field F] (n : ℕ) (O : Subring F) {g : GL (Fin n) F}
    (hg : g ∈ Formalism.UG.GLint (Fin n) O) : invTranspose n g ∈ Formalism.UG.GLint (Fin n) O := by
  obtain ⟨h, rfl⟩ := hg
  exact ⟨invTranspose n h, Units.ext rfl⟩

theorem conjSP_proj {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (x : AL L) :
    (conjSP s).proj x = s.proj (conjAL L x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => simp [SplitPlace.proj, conjAL, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.map_tmul]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]

theorem conjSP_loc {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (κ : GA L n) :
    (conjSP s).loc n κ = invTranspose n (s.loc n κ) := by
  have hm : κ.1.val * conjT (conjAL L) κ.1.val = 1 := κ.2
  have h1 : (κ.1⁻¹).val = conjT (conjAL L) κ.1.val := Units.inv_eq_of_mul_eq_one_right hm
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  change (conjSP s).proj (κ.1.val i j) = s.proj ((κ.1⁻¹).val j i)
  rw [h1, conjSP_proj]
  rfl

theorem exists_conj_level : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (K : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))) (θ : K →* ℂˣ), (∀ g ∈ K, g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) → IsOpen (θ.ker : Set K) → ∃ (K' : Subgroup (GL (Fin n) ((GlobalTheory.TypeTame.conjSP s).v.adicCompletion (maximalRealSubfield L)))) (θ' : K' →* ℂˣ), (∀ g ∈ K', g ∈ Formalism.UG.GLint (Fin n) ((GlobalTheory.TypeTame.conjSP s).v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) ∧ IsOpen (θ'.ker : Set K') ∧ (∀ κ : GAf L n, (GlobalTheory.TypeTame.conjSP s).loc n κ ∈ K' ↔ s.loc n κ ∈ K) ∧ (∀ (κ : GAf L n) (h : s.loc n κ ∈ K) (h' : (GlobalTheory.TypeTame.conjSP s).loc n κ ∈ K'), θ' ⟨(GlobalTheory.TypeTame.conjSP s).loc n κ, h'⟩ = θ ⟨s.loc n κ, h⟩) ∧ ∀ g (hg : g ∈ K) (g' : GL (Fin n) ((GlobalTheory.TypeTame.conjSP s).v.adicCompletion (maximalRealSubfield L))), g'.val = (g⁻¹).val.transpose → ∃ h' : g' ∈ K', θ' ⟨g', h'⟩ = θ ⟨g, hg⟩ := by
  intro L _ _ _ n s K θ hK hθ
  have key : ∀ (g' : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) (g) (hg : g ∈ K),
      g' = invTranspose n g → ∃ h' : g' ∈ K.comap (invTranspose n),
        θ.comp ((invTranspose n).subgroupComap K) ⟨g', h'⟩ = θ ⟨g, hg⟩ := by
    rintro g' g hg rfl
    refine ⟨by rw [Subgroup.mem_comap, invTranspose_invTranspose]; exact hg, ?_⟩
    rw [MonoidHom.comp_apply]
    exact congrArg θ (Subtype.ext (invTranspose_invTranspose n g))
  refine ⟨K.comap (invTranspose n), θ.comp ((invTranspose n).subgroupComap K), ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    have := invTranspose_mem_GLint n _ (hK _ hg)
    rwa [invTranspose_invTranspose] at this
  · have hc : Continuous ((invTranspose n).subgroupComap K) :=
      Continuous.subtype_mk ((continuous_invTranspose n).comp continuous_subtype_val) _
    exact hθ.preimage hc
  · intro κ
    rw [conjSP_loc]
    change invTranspose n (invTranspose n (s.loc n κ)) ∈ K ↔ _
    rw [invTranspose_invTranspose]
  · intro κ h h'
    exact (key _ _ h (conjSP_loc n s κ)).2
  · intro g hg g' hg'
    exact key g' g hg (Units.ext hg')

end GlobalTheory.TypeTame
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GoodOffBad

theorem conj_eq_complexConj (D : D7) (x : D.host.E) : D.host.conj x = IsCMField.complexConj D.host.E x :=
  D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])

theorem isConjPl_conjPlE_left {D : D7} (P : PlE D.host) : IsConjPl D.host (GlobalTheory.SplitConjPlace.conjPlE P) P := by
  intro x y hxy
  rw [GlobalTheory.SplitConjPlace.mem_conjPlE]
  have : IsCMField.ringOfIntegersComplexConj D.host.E x = y := by
    apply RingOfIntegers.ext
    rw [IsCMField.coe_ringOfIntegersComplexConj, hxy, conj_eq_complexConj]
  rw [this]

theorem conjPlE_mem_placesOver {D : D7} (P : PlE D.host) (p : ℕ) :
    GlobalTheory.SplitConjPlace.conjPlE P ∈ placesOver D.host.E p ↔ P ∈ placesOver D.host.E p := by
  show ((p : ℕ) : 𝓞 D.host.E) ∈ (GlobalTheory.SplitConjPlace.conjPlE P).asIdeal ↔ ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
  rw [GlobalTheory.SplitConjPlace.mem_conjPlE, map_natCast]

end GlobalTheory.GoodOffBad
end
