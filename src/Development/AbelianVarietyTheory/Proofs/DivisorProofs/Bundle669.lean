module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle625
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import GroundTheory.AutomorphicForms.ReductionSiegel
import GroundTheory.AutomorphicForms.ReductionCore
import GroundTheory.GlobalFields.IdeleGroups.NormOneCompact
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle626
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isIsogenyOfDegree_torsion_coprime_ideals_product : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (O : Type) [CommRing O] (ρ : ReciprocityTheory.ChartRestriction.G.Out.RingAct A O) (𝔞 𝔟 : Ideal O), 𝔞 ⊔ 𝔟 = ⊤ → ∀ (K₁ K₂ K₃ : Over S) (i₁ : K₁ ⟶ A) (i₂ : K₂ ⟶ A) (i₃ : K₃ ⟶ A), Mono i₁ → Mono i₂ → Mono i₃ → (∀ (T : Over S) (x : T ⟶ A), GlobalTheory.IwLevel.InSub i₁ x ↔ GlobalTheory.IwLevel.KilledBy ρ 𝔞 x) → (∀ (T : Over S) (x : T ⟶ A), GlobalTheory.IwLevel.InSub i₂ x ↔ GlobalTheory.IwLevel.KilledBy ρ 𝔟 x) → (∀ (T : Over S) (x : T ⟶ A), GlobalTheory.IwLevel.InSub i₃ x ↔ GlobalTheory.IwLevel.KilledBy ρ (𝔞 * 𝔟) x) → ∀ (d e : ℕ), 0 < e → GlobalTheory.IwLevel.IsIsogDeg (toUnit K₃) (d * e) → GlobalTheory.IwLevel.IsIsogDeg (toUnit K₂) e → GlobalTheory.IwLevel.IsIsogDeg (toUnit K₁) d := by
  first | (exact @GlobalTheory.IwLevel.CoprimeTors.isIsogDeg_of_coprime) | (exact GlobalTheory.IwLevel.CoprimeTors.isIsogDeg_of_coprime) | (intros; apply GlobalTheory.IwLevel.CoprimeTors.isIsogDeg_of_coprime  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.isogeny_degree_of_point_count : ∀ {S : Scheme.{0}} (A K : Over S) (i : K ⟶ A), Mono i → IsFinite K.hom → Etale K.hom → ∀ (d : ℕ), 1 ≤ d → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), Nat.card {y : Over.mk t ⟶ A // GlobalTheory.IwLevel.InSub i y} = d) → GlobalTheory.IwLevel.IsIsogDeg (toUnit K) d := by
  first | (exact @GlobalTheory.FinEtRank.isIsogDeg_of_card) | (exact GlobalTheory.FinEtRank.isIsogDeg_of_card) | (intros; apply GlobalTheory.FinEtRank.isIsogDeg_of_card <;> assumption)
end

section

namespace GlobalTheory.StandardLatticeSpan

open NumberField

variable {E E' : Type} [Field E] [Field E'] (f : E ≃+* E') {n : ℕ}

theorem mem_range_iff (a : E) :
    f a ∈ (algebraMap (𝓞 E') E').range ↔ a ∈ (algebraMap (𝓞 E) E).range := by
  constructor
  · rintro ⟨c, hc⟩
    have h1 : IsIntegral ℤ (f a) := hc ▸ c.isIntegral_coe
    have h2 : IsIntegral ℤ (f.symm (f a)) :=
      map_isIntegral_int (f.symm : E' →+* E) h1
    rw [f.symm_apply_apply] at h2
    exact ⟨⟨a, h2⟩, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨⟨f (algebraMap _ _ c), map_isIntegral_int (f : E →+* E') c.isIntegral_coe⟩, rfl⟩

theorem mem_span_iff (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E') :
    y ∈ Submodule.span (𝓞 E') ((fun (x : Fin n → E) (i : Fin n) ↦ f (x i)) '' (L : Set (Fin n → E)))
      ↔ ∃ x ∈ L, (fun i ↦ f (x i)) = y := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => exact ⟨0, L.zero_mem, by ext i; simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨a, ha, rfl⟩ := hy
      obtain ⟨b, hb, rfl⟩ := hz
      exact ⟨a + b, L.add_mem ha hb, by ext i; simp⟩
    | smul c y _ hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      obtain ⟨d, hd⟩ := (mem_range_iff f (f.symm (algebraMap (𝓞 E') E' c))).1
        ⟨c, by rw [f.apply_symm_apply]⟩
      refine ⟨d • a, L.smul_mem d ha, ?_⟩
      ext i
      simp only [Pi.smul_apply, Algebra.smul_def, map_mul, hd, RingEquiv.apply_symm_apply]
  · rintro ⟨x, hx, rfl⟩
    exact Submodule.subset_span ⟨x, hx, rfl⟩

theorem map_mem_span_int (s : Set (Fin n → E)) {x : Fin n → E}
    (hx : x ∈ Submodule.span (𝓞 E) s) :
    (fun i ↦ f (x i)) ∈
      Submodule.span (𝓞 E') ((fun (x : Fin n → E) (i : Fin n) ↦ f (x i)) '' s) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero =>
    have : (fun i ↦ f ((0 : Fin n → E) i)) = 0 := by ext i; simp
    rw [this]; exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    have : (fun i ↦ f ((y + z) i)) = (fun i ↦ f (y i)) + (fun i ↦ f (z i)) := by ext i; simp
    rw [this]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    obtain ⟨d, hd⟩ := (mem_range_iff f (algebraMap (𝓞 E) E c)).2 ⟨c, rfl⟩
    have : (fun i ↦ f ((c • y) i)) = d • (fun i ↦ f (y i)) := by
      ext i
      simp only [Pi.smul_apply, Algebra.smul_def, map_mul, hd]
    rw [this]; exact Submodule.smul_mem _ _ hy

theorem map_mem_span_field (s : Set (Fin n → E)) {x : Fin n → E}
    (hx : x ∈ Submodule.span E s) :
    (fun i ↦ f (x i)) ∈
      Submodule.span E' ((fun (x : Fin n → E) (i : Fin n) ↦ f (x i)) '' s) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero =>
    have : (fun i ↦ f ((0 : Fin n → E) i)) = 0 := by ext i; simp
    rw [this]; exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    have : (fun i ↦ f ((y + z) i)) = (fun i ↦ f (y i)) + (fun i ↦ f (z i)) := by ext i; simp
    rw [this]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    have : (fun i ↦ f ((c • y) i)) = f c • (fun i ↦ f (y i)) := by
      ext i
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    rw [this]; exact Submodule.smul_mem _ _ hy

theorem stdH_map [StarRing E] [StarRing E'] (hf : ∀ x : E, f (star x) = star (f x))
    (x y : Fin n → E) :
    Formalism.BasicNotions.stdH E' n (fun i ↦ f (x i)) (fun i ↦ f (y i)) = f (Formalism.BasicNotions.stdH E n x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.BasicNotions.stdH, map_sum, map_mul, hf]

theorem isSDLat_map {E E' : Type} [Field E] [Field E'] (f : E ≃+* E') {n : ℕ}
    [NumberField E] [NumberField E'] [StarRing E] [StarRing E']
    (hf : ∀ x : E, f (star x) = star (f x)) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Formalism.BasicNotions.IsSDLat E n L) :
    Formalism.BasicNotions.IsSDLat E' n (Submodule.span (𝓞 E')
      ((fun (x : Fin n → E) (i : Fin n) ↦ f (x i)) '' (L : Set (Fin n → E)))) := by
  obtain ⟨⟨s, hs⟩, htop, hdual⟩ := hL
  have surj : ∀ y : Fin n → E', ∃ x : Fin n → E, (fun i ↦ f (x i)) = y :=
    fun y => ⟨fun i => f.symm (y i), by ext i; simp⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [Submodule.fg_def]
    refine ⟨(fun (x : Fin n → E) (i : Fin n) ↦ f (x i)) '' (s : Set (Fin n → E)),
      s.finite_toSet.image _, le_antisymm ?_ ?_⟩
    · apply Submodule.span_mono
      apply Set.image_mono
      rw [← hs]; exact Submodule.subset_span
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      exact map_mem_span_int f _ (hs ▸ hx)
  · rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := surj y
    have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := htop ▸ Submodule.mem_top
    exact Submodule.span_mono Submodule.subset_span (map_mem_span_field f _ hx)
  · intro y
    obtain ⟨y, rfl⟩ := surj y
    constructor
    · intro hy x hx
      obtain ⟨y', hy', e⟩ := (mem_span_iff f L _).1 hy
      obtain ⟨x, hx', rfl⟩ := (mem_span_iff f L _).1 hx
      rw [← e, stdH_map f hf, mem_range_iff]
      exact (hdual y').1 hy' x hx'
    · intro h
      refine (mem_span_iff f L _).2 ⟨y, (hdual y).2 fun x hx => ?_, rfl⟩
      rw [← mem_range_iff f, ← stdH_map f hf]
      exact h _ ((mem_span_iff f L _).2 ⟨x, hx, rfl⟩)

end GlobalTheory.StandardLatticeSpan
end

section

noncomputable section

open Formalism.BasicNotions

namespace GlobalTheory.ClassCount

def hBd (D : D7) (n : ℕ) : ℝ := (12 * (D.R.f : ℝ) ^ 2 * (n : ℝ) ^ 4 * D.host.rdE ^ 2) ^ (6 * D.R.f * n ^ 2)

theorem hBd_mono {D : D7} {n N : ℕ} (hn : n ≤ N) (h1 : 1 ≤ 12 * (D.R.f : ℝ) ^ 2 * (N : ℝ) ^ 4 * D.host.rdE ^ 2)
    (hrd : 0 ≤ D.host.rdE) : hBd D n ≤ hBd D N := by
  unfold hBd
  have hb : 12 * (D.R.f : ℝ) ^ 2 * (n : ℝ) ^ 4 * D.host.rdE ^ 2 ≤ 12 * (D.R.f : ℝ) ^ 2 * (N : ℝ) ^ 4 * D.host.rdE ^ 2 := by
    have : (n : ℝ) ^ 4 ≤ (N : ℝ) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hn) 4
    gcongr
  calc _ ≤ (12 * (D.R.f : ℝ) ^ 2 * (N : ℝ) ^ 4 * D.host.rdE ^ 2) ^ (6 * D.R.f * n ^ 2) :=
        pow_le_pow_left₀ (by positivity) hb _
    _ ≤ _ := pow_le_pow_right₀ h1 (by gcongr)

end GlobalTheory.ClassCount

end
end

section

open NumberField MeasureTheory Matrix
open scoped NumberField.AdeleRing Pointwise
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.IdeleGroup

noncomputable section

namespace GlobalTheory.SiegelDiagNormOne

theorem exists_siegelSet_diag_normOne : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), ∃ ω : Set (AdelicGLn.AdelicGL K n),
    IsCompact ω ∧ ω ⊆ ((adelicBorel (K := K) (n := n) : Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n)) ∧
    (∀ b ∈ ω, ∀ i, ∃ u : IdeleGroup K, (b : Matrix (Fin n) (Fin n) 𝔸[K]) i i = u ∧ (ideleModule K u : ℝ) = 1) ∧
    ∃ t : ℝ, 0 < t ∧ ∀ g : AdelicGLn.AdelicGL K n, ∃ γ : GL (Fin n) K,
      AdelicGLn.diagonal K n γ * g ∈ Reduction.siegelSet n ω t := by
  intro K _ _ n
  classical
  obtain ⟨t₀, ht₀, hred⟩ := exists_reduced (K := K)
  obtain ⟨D, hD, hDmem⟩ := exists_isCompact_add_mem (K := K)
  obtain ⟨S, hS, hS1, hSmem⟩ := exists_isCompact_normOneSubgroup K
  set d : ℕ := Module.finrank ℚ K with hd
  have hd0 : 0 < d := Module.finrank_pos
  set FN : Set (AdelicGLn.AdelicGL K n) :=
    unitriangularGL n '' (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => D) with hFN
  set FT : Set (AdelicGLn.AdelicGL K n) := diagUnits n '' (Set.pi Set.univ fun _ => S) with hFT
  have hFNc : IsCompact FN := (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hD).image
    (continuous_unitriangularGL n)
  have hFTc : IsCompact FT := (isCompact_univ_pi fun _ => hS).image (continuous_diagUnits n)
  refine ⟨FN * FT, hFNc.mul hFTc, ?_, ?_, t₀ ^ ((d : ℝ)⁻¹), Real.rpow_pos_of_pos ht₀ _, fun g => ?_⟩
  · rintro _ ⟨x, ⟨p, -, rfl⟩, y, ⟨e, -, rfl⟩, rfl⟩
    exact mul_mem (unitriangularGL_mem_adelicBorel n p) (diagUnits_mem_adelicBorel n e)
  · rintro _ ⟨x, ⟨p, -, rfl⟩, y, ⟨e, he, rfl⟩, rfl⟩ i
    refine ⟨e i, ?_, ?_⟩
    · rw [Units.val_mul, coe_diagUnits, Matrix.mul_diagonal]
      change unitriangular p i i * _ = _
      simp [unitriangular]
    · have h1 := hS1 (he i (Set.mem_univ _))
      rw [normOneSubgroup, SetLike.mem_coe, MonoidHom.mem_ker] at h1
      rw [h1]
      rfl
  obtain ⟨γ, b, hb, k, hk, hγ, hratio⟩ := hred n g
  set B : Matrix (Fin n) (Fin n) 𝔸[K] := (b : Matrix (Fin n) (Fin n) 𝔸[K]) with hB
  set dU : Fin n → IdeleGroup K := fun i => (isUnit_apply_self_of_mem_adelicBorel hb i).unit
    with hdU
  have hdUv : ∀ i, ((dU i : IdeleGroup K) : 𝔸[K]) = B i i := fun i => IsUnit.unit_spec _
  set r : Fin n → ℝ := fun i => (ideleModule K (dU i) : ℝ) ^ ((d : ℝ)⁻¹) with hr
  have hrpos : ∀ i, 0 < r i := fun i => Real.rpow_pos_of_pos (ideleModule K (dU i)).2 _
  have hrd : ∀ i, r i ^ d = ideleModule K (dU i) := fun i =>
    Real.rpow_inv_natCast_pow (ideleModule K (dU i)).2.le hd0.ne'
  have heqmod : ∀ i, ideleModule K (dU i) = ideleModule K (posIdele (r i) (hrpos i)) := fun i =>
    Subtype.ext (by rw [ideleModule_posIdele, ← hd, hrd i])
  have hnorm : ∀ i, dU i * (posIdele (r i) (hrpos i))⁻¹ ∈ normOneSubgroup K := fun i => by
    rw [normOneSubgroup, MonoidHom.mem_ker, map_mul, map_inv, heqmod i, mul_inv_cancel]
  choose c hc using fun i => hSmem _ (hnorm i)
  set σ : Fin n → IdeleGroup K :=
    fun i => IdeleGroup.diagonal K (c i) * (dU i * (posIdele (r i) (hrpos i))⁻¹) with hσ
  set e : Fin n → IdeleGroup K := fun i => IdeleGroup.diagonal K (c i) with he
  set δA : AdelicGLn.AdelicGL K n := diagUnits n e with hδA
  have hδ : AdelicGLn.diagonal K n (diagUnits n c) = δA := diagonal_diagUnits n c
  set u : AdelicGLn.AdelicGL K n := δA * b * (diagUnits n dU)⁻¹ * δA⁻¹ with hu
  have hu_apply : ∀ i j, (u : Matrix (Fin n) (Fin n) 𝔸[K]) i j =
      (e i : 𝔸[K]) * B i j * (((dU j)⁻¹ : IdeleGroup K) : 𝔸[K]) * (((e j)⁻¹ : IdeleGroup K) : 𝔸[K]) := by
    intro i j
    rw [hu, ← map_inv, ← map_inv]
    simp only [Units.val_mul, hδA, coe_diagUnits, Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.inv_apply]
    rfl
  have huu : IsUnitriangular (u : Matrix (Fin n) (Fin n) 𝔸[K]) := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hu_apply, show B i j = 0 from hb hij]
      simp
    · rw [hu_apply, ← hdUv i]
      calc (e i : 𝔸[K]) * (dU i : 𝔸[K]) * (((dU i)⁻¹ : IdeleGroup K) : 𝔸[K]) *
            (((e i)⁻¹ : IdeleGroup K) : 𝔸[K])
          = ((e i * dU i * (dU i)⁻¹ * (e i)⁻¹ : IdeleGroup K) : 𝔸[K]) := by simp [Units.val_mul]
        _ = 1 := by rw [mul_inv_cancel_right, mul_inv_cancel, Units.val_one]
  obtain ⟨ν, hν, hνD⟩ := exists_unitriangular_mul_mem hDmem n _ huu
  set νGL : GL (Fin n) K := GeneralLinearGroup.mkOfDetNeZero ν
    (by rw [hν.det_eq_one]; exact one_ne_zero) with hνGL
  set νA : AdelicGLn.AdelicGL K n := AdelicGLn.diagonal K n νGL with hνA
  have hνAmat : (νA : Matrix (Fin n) (Fin n) 𝔸[K]) = ν.map (algebraMap K 𝔸[K]) := rfl
  obtain ⟨d₀, hd₀⟩ : D.Nonempty := let ⟨k₀, hk₀⟩ := hDmem 0; ⟨_, hk₀⟩
  set p : Fin n → Fin n → 𝔸[K] := fun i j =>
    if i < j then ((νA * u : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) i j else d₀
    with hp
  have hpD : p ∈ Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => D := by
    intro i _ j _
    simp only [hp]
    split_ifs with hij
    · rw [Units.val_mul, hνAmat]
      exact hνD i j hij
    · exact hd₀
  have hνu : νA * u = unitriangularGL n p := by
    refine Units.ext ?_
    have h1 : IsUnitriangular ((νA * u : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) := by
      rw [Units.val_mul, hνAmat]
      exact IsUnitriangular.mul ⟨fun i j hij => by simp [hν.1 hij],
        fun i => by simp [hν.2 i]⟩ huu
    rw [h1.eq_unitriangular]
    change unitriangular _ = unitriangular p
    ext i j
    simp only [unitriangular, of_apply, hp]
    split_ifs <;> rfl
  have hdiag : δA * diagUnits n dU = diagUnits n σ * diagUnits n (fun i => posIdele (r i) (hrpos i)) := by
    rw [hδA, ← map_mul, ← map_mul]
    congr 1
    funext i
    simp [hσ, he, mul_assoc]
  refine ⟨νGL * diagUnits n c * γ, unitriangularGL n p * diagUnits n σ,
    ⟨_, ⟨p, hpD, rfl⟩, _, ⟨σ, fun i _ => hc i, rfl⟩, rfl⟩,
    diagUnits n (fun i => posIdele (r i) (hrpos i)), ⟨r, hrpos, fun i j hij => ?_, rfl⟩, k, hk, ?_⟩
  · have h := hratio i j hij
    rw [← hdUv j, ← hdUv i, adeleAbs_units, adeleAbs_units, ← hrd i, ← hrd j] at h
    have hrj := (hrpos j).le
    have hri := (hrpos i).le
    have ht : (t₀ ^ ((d : ℝ)⁻¹)) ^ d = t₀ := Real.rpow_inv_natCast_pow ht₀.le hd0.ne'
    have htn : 0 ≤ t₀ ^ ((d : ℝ)⁻¹) := (Real.rpow_pos_of_pos ht₀ _).le
    rw [← pow_le_pow_iff_left₀ (mul_nonneg htn hrj) hri hd0.ne', mul_pow, ht]
    exact h
  · have h1 : δA * b = u * (δA * diagUnits n dU) := by
      rw [hu]; group
    calc AdelicGLn.diagonal K n (νGL * diagUnits n c * γ) * g
        = νA * δA * (AdelicGLn.diagonal K n γ * g) := by
          rw [map_mul, map_mul, hδ, ← hνA]; simp only [mul_assoc]
      _ = νA * (δA * b) * k := by rw [hγ]; simp only [mul_assoc]
      _ = νA * u * (δA * diagUnits n dU) * k := by rw [h1]; simp only [mul_assoc]
      _ = (νA * u) * diagUnits n σ * diagUnits n (fun i => posIdele (r i) (hrpos i)) * k := by
          rw [hdiag]; simp only [mul_assoc]
      _ = _ := by rw [hνu]

end GlobalTheory.SiegelDiagNormOne
end
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.GalDiff

open scoped Pointwise

variable (E : Type) [Field E] [NumberField E]

theorem mem_differentIdeal_iff_one (x : 𝓞 E) :
    x ∈ differentIdeal ℤ (𝓞 E) ↔
      ∀ y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E), (x : E) * y ∈ (1 : Submodule (𝓞 E) E) := by
  rw [← Submodule.mem_div_iff_forall_mul_mem, ← coeSubmodule_differentIdeal ℤ ℚ (L := E) (𝓞 E),
    IsLocalization.mem_coeSubmodule]
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨y, hy, h⟩
    have : y = x := FaithfulSMul.algebraMap_injective (𝓞 E) E h
    exact this ▸ hy

theorem galois_smul_mem_differentIdeal (σ : E ≃ₐ[ℚ] E) {x : 𝓞 E}
    (hx : x ∈ differentIdeal ℤ (𝓞 E)) : σ • x ∈ differentIdeal ℤ (𝓞 E) := by
  have hone : ∀ (τ : E ≃ₐ[ℚ] E) (a : E), a ∈ (1 : Submodule (𝓞 E) E) →
      τ a ∈ (1 : Submodule (𝓞 E) E) := by
    intro τ a ha
    rw [Submodule.mem_one] at ha ⊢
    obtain ⟨b, rfl⟩ := ha
    exact ⟨τ • b, rfl⟩
  rw [mem_differentIdeal_iff_one] at hx ⊢
  intro y hy
  have hy' : σ.symm y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_traceDual] at hy ⊢
    intro a ha
    have := hy (σ a) (hone σ a ha)
    rw [Algebra.traceForm_apply] at this ⊢
    rw [← Algebra.trace_eq_of_algEquiv σ, map_mul, AlgEquiv.apply_symm_apply]
    exact this
  have := hone σ _ (hx _ hy')
  rw [map_mul, AlgEquiv.apply_symm_apply] at this
  exact this

theorem differentIdeal_pow_finrank_eq_span_discr :
    ∀ (F : Type) [Field F] [NumberField F] [IsGalois ℚ F],
      differentIdeal ℤ (𝓞 F) ^ Module.finrank ℚ F = Ideal.span {((discr F : ℤ) : 𝓞 F)} := by
  intro E _ _ _
  classical
  have hmap : Ideal.span {((discr E : ℤ) : 𝓞 E)} = (Ideal.span {discr E}).map (algebraMap ℤ (𝓞 E)) := by
    rw [Ideal.map_span, Set.image_singleton, eq_intCast]
  rw [hmap]
  set D := differentIdeal ℤ (𝓞 E) with hD
  have hN : Ideal.absNorm D = (discr E).natAbs := absNorm_differentIdeal E (𝓞 E)
  have hrel : Ideal.relNorm ℤ D = Ideal.span {discr E} := by
    rw [Ideal.relNorm_int, hN, Ideal.span_singleton_eq_span_singleton]
    exact (Int.associated_natAbs _).symm
  have hle : (Ideal.span {discr E}).map (algebraMap ℤ (𝓞 E)) ≤ D ^ Module.finrank ℚ E := by
    rw [← hrel, Ideal.map_le_iff_le_comap, Ideal.relNorm_apply, Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have h1 : algebraMap ℤ (𝓞 E) (Algebra.intNorm ℤ (𝓞 E) x) = ∏ σ : E ≃ₐ[ℚ] E, σ • x := by
      apply FaithfulSMul.algebraMap_injective (𝓞 E) E
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ ℚ E,
        Algebra.algebraMap_intNorm (L := E), Algebra.norm_eq_prod_automorphisms, map_prod]
      rfl
    change algebraMap ℤ (𝓞 E) (Algebra.intNorm ℤ (𝓞 E) x) ∈ D ^ Module.finrank ℚ E
    rw [h1, ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card, ← Finset.card_univ,
      ← Finset.prod_const]
    exact Ideal.prod_mem_prod fun σ _ => galois_smul_mem_differentIdeal E σ hx
  obtain ⟨L, hL⟩ := Ideal.dvd_iff_le.mpr hle
  have h2 := congrArg Ideal.absNorm hL
  rw [Ideal.absNorm_algebraMap, map_mul, map_pow, hN, RingOfIntegers.rank,
    Ideal.absNorm_span_singleton, Algebra.norm_self] at h2
  have h0 : (discr E).natAbs ^ Module.finrank ℚ E ≠ 0 :=
    pow_ne_zero _ (Int.natAbs_ne_zero.mpr (discr_ne_zero E))
  have h3 : Ideal.absNorm L = 1 := by
    apply mul_left_cancel₀ h0
    rw [mul_one]
    exact h2.symm
  rw [hL, Ideal.absNorm_eq_one_iff.mp h3, Ideal.mul_top]

end GlobalTheory.GalDiff
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.map_comap_idealSheaf_eq_of_isIso_restrict : ∀ (W W' : Scheme.{0}) (π : W' ⟶ W) (U : W.Opens), QuasiCompact π → IsIso (π ∣_ U) → ∀ (τ : W.IdealSheafData) (V : W.affineOpens), V.1 ≤ U → ((τ.comap π).map π).ideal V = τ.ideal V := by
  first | exact @GlobalTheory.MapComapIso.map_comap_ideal_eq_of_isIso_restrict | exact GlobalTheory.MapComapIso.map_comap_ideal_eq_of_isIso_restrict | (intros; apply GlobalTheory.MapComapIso.map_comap_ideal_eq_of_isIso_restrict <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem _root_.GlobalTheory.T.exists_pushout_of_nilpotent_thickenings' : ∀ (Y₀ Y₁ Y₂ : Scheme.{0}) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂), IsClosedImmersion i₁ → IsClosedImmersion i₂ → Surjective i₁ → Surjective i₂ → (∀ U : Y₁.Opens, IsAffineOpen U → IsNilpotent (RingHom.ker (i₁.app U).hom)) → (∀ U : Y₂.Opens, IsAffineOpen U → IsNilpotent (RingHom.ker (i₂.app U).hom)) → ∃ (Y : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂), IsPushout i₁ i₂ j₁ j₂ ∧ IsClosedImmersion j₁ ∧ IsClosedImmersion j₂ ∧ ∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl)) := by
  first | exact @GlobalTheory.exists_pushout_of_nilpotent_thickenings | exact GlobalTheory.exists_pushout_of_nilpotent_thickenings | (intros; apply GlobalTheory.exists_pushout_of_nilpotent_thickenings <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

theorem _root_.GlobalTheory.T.etale_isFinite_of_comp_etale_surjective' : ∀ (X Y Z : Scheme.{0}) (h : X ⟶ Y) (f : Y ⟶ Z), Etale h → Surjective h → Etale (h ≫ f) → IsFinite (h ≫ f) → IsSeparated f → LocallyOfFiniteType f → Etale f ∧ IsFinite f := by
  first | (exact @GlobalTheory.etale_isFinite_of_comp_etale_surjective) | (exact GlobalTheory.etale_isFinite_of_comp_etale_surjective) | (intros; apply GlobalTheory.etale_isFinite_of_comp_etale_surjective <;> assumption)
end
