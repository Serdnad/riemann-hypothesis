module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle154
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle153
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartFormsBaseChange
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BisimplicialActionSecondFactor
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle032
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle155
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle084
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockLowerBoundTorsion
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle101
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle117
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle156
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.OmBasis

def allE {n d : ℕ} : Gam n d := ∑ e, oneE e

theorem allE_mem {n d : ℕ} : (allE : Gam n d) ∈ (cone ∅ : AddSubmonoid (Gam n d)) := by
  unfold allE
  exact AddSubmonoid.sum_mem _ (fun e _ => oneE_mem ∅ e)

theorem allE_apply {n d : ℕ} (e : E n d) : (allE : Gam n d) e = 1 := by
  unfold allE
  rw [Finset.sum_apply]
  simp [oneE, Pi.single_apply]

theorem exists_add_mem {n d : ℕ} (g : Gam n d) :
    ∃ N : ℕ, g + N • allE ∈ (cone ∅ : AddSubmonoid (Gam n d)) := by
  refine ⟨∑ e, (g e).natAbs, ?_⟩
  have hnn : ∀ e, 0 ≤ (g + (∑ e, (g e).natAbs) • (allE : Gam n d)) e := by
    intro e
    have h1 : (g + (∑ e, (g e).natAbs) • (allE : Gam n d)) e
        = g e + ((∑ e, (g e).natAbs : ℕ) : ℤ) := by
      change g e + (∑ e, (g e).natAbs) • (allE : Gam n d) e = _
      rw [allE_apply, nsmul_one]
    have h2 : (g e).natAbs ≤ ∑ e, (g e).natAbs :=
      Finset.single_le_sum (f := fun e => (g e).natAbs) (fun i _ => Nat.zero_le _) (Finset.mem_univ e)
    have h3 : ((g e).natAbs : ℤ) ≤ ((∑ e, (g e).natAbs : ℕ) : ℤ) := by exact_mod_cast h2
    rw [h1]
    have h4 := Int.natCast_natAbs (g e)
    have h5 := neg_abs_le (g e)
    linarith
  have key := PolyBij.coe_mem_cone (n := n) (d := d)
    (Finsupp.equivFunOnFinite.symm fun e => ((g + (∑ e, (g e).natAbs) • (allE : Gam n d)) e).toNat)
  convert key using 2
  rename_i e
  exact (Int.toNat_of_nonneg (hnn e)).symm

theorem monL_neg_oneE_mul {K : Type} [Field K] {n d : ℕ} (e : E n d) : monL K (-oneE e) * monL K (oneE e) = 1 := by
  rw [monL, monL, mon_mul]
  change AddMonoidAlgebra.single _ (1 : K) = AddMonoidAlgebra.single 0 1
  congr 1
  exact Subtype.ext (neg_add_cancel (oneE e))

theorem exists_basis_dl : ∀ {K : Type} [Field K] {n d : ℕ},
    ∃ b : Module.Basis (E n d) (Lr K n d) Ω[Lr K n d⁄K], ∀ e, b e = dl e := by
  intro K _ n d
  have hle : (cone ∅ : AddSubmonoid (Gam n d)) ≤ ⊤ := le_top
  let φ : MvPolynomial (E n d) K →ₐ[K] Lr K n d := (incl (K := K) hle).comp (poly n K ∅)
  letI : Algebra (MvPolynomial (E n d) K) (Lr K n d) := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K (MvPolynomial (E n d) K) (Lr K n d) := IsScalarTower.of_algHom φ
  let s0 : MvPolynomial (E n d) K := (PolyBij.polyEquiv K).symm (mon K (allE : Gam n d) allE_mem)
  have hpe : ∀ a, poly n K ∅ ((PolyBij.polyEquiv (n := n) (d := d) K).symm a) = a := by
    intro a
    rw [PolyBij.poly_eq_polyEquiv, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
  have e1 : φ s0 = incl (K := K) hle (mon K (allE : Gam n d) allE_mem) := by
    change incl (K := K) hle (poly n K ∅ s0) = _
    rw [hpe]
  have hmul : φ s0 * mon K (-(allE : Gam n d)) (AddSubmonoid.mem_top _) = 1 := by
    rw [e1, incl_mon, mon_mul]
    change AddMonoidAlgebra.single _ (1 : K) = AddMonoidAlgebra.single 0 1
    congr 1
    exact Subtype.ext (add_neg_cancel (allE : Gam n d))
  have hunit : IsUnit (φ s0) := ⟨⟨φ s0, _, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩
  have hinj : Function.Injective φ :=
    (Away.incl_injective (K := K) hle).comp (PolyBij.poly_bijective (K := K) (n := n) (d := d)).1
  haveI : IsLocalization (Submonoid.powers s0) (Lr K n d) := by
    refine ⟨?_, ?_, ?_⟩
    · intro y
      obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp y.2
      rw [← hk]
      change IsUnit (φ (s0 ^ k))
      rw [map_pow]
      exact hunit.pow k
    · intro z
      obtain ⟨N, a, ha⟩ := Away.exists_mul_pow_eq_incl (K := K) hle (allE : Gam n d) allE_mem
        (fun g _ => exists_add_mem g) z
      refine ⟨((PolyBij.polyEquiv K).symm a, ⟨s0 ^ N, N, rfl⟩), ?_⟩
      change z * φ (s0 ^ N) = φ ((PolyBij.polyEquiv K).symm a)
      have e2 : φ ((PolyBij.polyEquiv K).symm a) = incl (K := K) hle a := by
        change incl (K := K) hle (poly n K ∅ _) = _
        rw [hpe]
      rw [map_pow, e1, e2, ← map_pow]
      exact ha
    · intro x y hxy
      have hxy' : φ x = φ y := hxy
      exact ⟨1, by rw [hinj hxy']⟩
  let b0 := (KaehlerDifferential.mvPolynomialBasis K (E n d)).ofIsLocalizedModule (Lr K n d)
    (Submonoid.powers s0) (KaehlerDifferential.map K K (MvPolynomial (E n d) K) (Lr K n d))
  let w : E n d → (Lr K n d)ˣ := fun e =>
    ⟨monL K (-oneE e), monL K (oneE e), monL_neg_oneE_mul e, by rw [mul_comm]; exact monL_neg_oneE_mul e⟩
  refine ⟨b0.unitsSMul w, fun e => ?_⟩
  have e4 : KaehlerDifferential.mvPolynomialBasis K (E n d) e
      = KaehlerDifferential.D K (MvPolynomial (E n d) K) (MvPolynomial.X e) :=
    Module.Basis.apply_eq_iff.mpr (by rw [KaehlerDifferential.mvPolynomialBasis_repr_D_X])
  rw [Module.Basis.unitsSMul_apply, Module.Basis.ofIsLocalizedModule_apply, e4, KaehlerDifferential.map_D]
  have e3 : φ (MvPolynomial.X e) = monL K (oneE e) := by
    change incl (K := K) hle (poly n K ∅ (MvPolynomial.X e)) = _
    rw [poly_X, incl_mon]
    rfl
  change monL K (-oneE e) • KaehlerDifferential.D K (Lr K n d) (φ (MvPolynomial.X e)) = dl e
  rw [e3]
  rfl

end GlobalTheory.CompanionTheory.SurjectionOntoH4.OmBasis
end
end

section

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaEmpty
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

theorem toR_empty_bijective {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A]
    (C : ChartRings K A n d) : Function.Bijective (toR C ∅) := by
  have h : (toR C ∅ : A → C.R ∅) = C.base.symm := funext fun a => C.res_id ∅ _ _
  rw [h]
  exact C.base.symm.bijective

theorem theta_empty : ∀ {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d),
    ∃ (θ : R0 K n d ∅ →ₐ[K] C.R ∅) (hθ : ∀ b, θ (poly n K ∅ b) = toR C ∅ (phi C b)),
      IsBaseChange (Aa C) (thetaLin C θ hθ) := by
  intro K _ n d A _ _ C
  let e : Bp K n d ≃ₐ[K] R0 K n d ∅ := AlgEquiv.ofBijective (poly n K ∅) PolyBij.poly_bijective
  let θ : R0 K n d ∅ →ₐ[K] C.R ∅ := (toR C ∅).comp ((phi C).comp e.symm.toAlgHom)
  have hθ : ∀ b, θ (poly n K ∅ b) = toR C ∅ (phi C b) := fun b => by
    have hb : e.symm (poly n K ∅ b) = b := e.symm_apply_apply b
    change toR C ∅ (phi C (e.symm (poly n K ∅ b))) = _
    rw [hb]
  refine ⟨θ, hθ, ?_⟩
  let eM : Bp K n d ≃ₗ[Bp K n d] R0 K n d ∅ :=
    LinearEquiv.ofBijective (Algebra.linearMap (Bp K n d) (R0 K n d ∅)) PolyBij.poly_bijective
  let eN : Aa C ≃ₗ[Aa C] Rb C ∅ :=
    LinearEquiv.ofBijective (Algebra.linearMap (Aa C) (Rb C ∅)) (toR_empty_bijective C)
  refine (IsBaseChange.iff_of_equiv_comm (f := Algebra.linearMap (Bp K n d) (Aa C)) eM eN ?_).mp
    (IsBaseChange.linearMap (Bp K n d) (Aa C))
  refine LinearMap.ext fun b => ?_
  exact hθ b

end GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaEmpty
end
end

section

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.FreeOm
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

theorem free_of_formallyEtale (K A B : Type) [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    [Algebra A B] [IsScalarTower K A B] [Algebra.FormallyEtale A B] [Module.Free A Ω[A⁄K]] :
    Module.Free B Ω[B⁄K] :=
  (KaehlerDifferential.isBaseChange_of_formallyEtale K A B).free

theorem free_of_bijective {K A B : Type} [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (φ : A →ₐ[K] B) (hφ : Function.Bijective φ) [Module.Free A Ω[A⁄K]] : Module.Free B Ω[B⁄K] := by
  letI : Algebra A B := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K A B := IsScalarTower.of_algHom φ
  haveI : Algebra.FormallyEtale A B :=
    Algebra.FormallyEtale.of_equiv (AlgEquiv.ofBijective (Algebra.ofId A B) hφ)
  exact free_of_formallyEtale K A B

variable {K : Type} [Field K] {n d : ℕ}

theorem free_Bp : Module.Free (Bp K n d) Ω[Bp K n d⁄K] :=
  Module.Free.of_basis (KaehlerDifferential.mvPolynomialBasis K (E n d))

def cS (k : Fin d) (S : Finset (Fin d)) : Gam n d := ∑ j ∈ S, ratE k j

theorem ratE_inl (k j : Fin d) (l : Fin n) : (ratE k j : Gam n d) (Sum.inl l) = 0 := by
  simp [ratE, oneE]

theorem ratE_inr (k j j' : Fin d) :
    (ratE k j : Gam n d) (Sum.inr j') = (if j' = j then 1 else 0) - (if j' = k then 1 else 0) := by
  simp [ratE, oneE, Pi.single_apply]

theorem cS_inl (k : Fin d) (S : Finset (Fin d)) (l : Fin n) : (cS k S : Gam n d) (Sum.inl l) = 0 := by
  simp [cS, Finset.sum_apply, ratE_inl]

theorem cS_inr (k : Fin d) (S : Finset (Fin d)) {j : Fin d} (hj : j ≠ k) :
    (cS k S : Gam n d) (Sum.inr j) = if j ∈ S then 1 else 0 := by
  simp [cS, Finset.sum_apply, ratE_inr, hj]

theorem tdeg_cS (k : Fin d) (S : Finset (Fin d)) : tdeg (cS k S : Gam n d) = 0 := by
  unfold cS tdeg
  simp only [Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  exact ChartBij.tdeg_ratE k j

theorem cS_mem (k : Fin d) (S : Finset (Fin d)) : (cS k S : Gam n d) ∈ (cone {k} : AddSubmonoid (Gam n d)) :=
  AddSubmonoid.sum_mem _ fun j _ => ratE_mem (Finset.mem_singleton_self k) j

theorem neg_cS_mem {k : Fin d} {S : Finset (Fin d)} (hk : k ∈ S) :
    -(cS k S : Gam n d) ∈ (cone S : AddSubmonoid (Gam n d)) := by
  refine ⟨fun l => by simp [cS_inl], fun j hj => ?_, ?_⟩
  · have hne : j ≠ k := fun h => hj (h ▸ hk)
    simp [cS_inr k S hne, hj]
  · have h := tdeg_add (cS k S : Gam n d) (-cS k S)
    rw [add_neg_cancel, tdeg_cS] at h
    have h0 : tdeg (0 : Gam n d) = 0 := by simp [tdeg]
    rw [h0] at h
    linarith

theorem exists_add_nsmul_mem {k : Fin d} {S : Finset (Fin d)} (hk : k ∈ S) (g : Gam n d)
    (hg : g ∈ (cone S : AddSubmonoid (Gam n d))) :
    ∃ N : ℕ, g + N • (cS k S : Gam n d) ∈ (cone {k} : AddSubmonoid (Gam n d)) := by
  refine ⟨∑ j, (g (Sum.inr j)).natAbs, fun l => ?_, fun j hj => ?_, ?_⟩
  · simpa [cS_inl] using hg.1 l
  · have hne : j ≠ k := by simpa using hj
    have hle : (g (Sum.inr j)).natAbs ≤ ∑ j, (g (Sum.inr j)).natAbs :=
      Finset.single_le_sum (f := fun j => (g (Sum.inr j)).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    simp only [Pi.add_apply, Pi.smul_apply, cS_inr k S hne]
    by_cases hS : j ∈ S
    · simp only [hS, if_true, nsmul_eq_mul, mul_one]
      omega
    · simpa [hS] using hg.2.1 j hS
  · rw [tdeg_add]
    have h : tdeg ((∑ j, (g (Sum.inr j)).natAbs) • (cS k S : Gam n d)) = 0 := by
      have hs : ∀ N : ℕ, tdeg (N • (cS k S : Gam n d)) = 0 := fun N => by
        induction N with
        | zero => simp [tdeg]
        | succ N ih => rw [succ_nsmul, tdeg_add, ih, tdeg_cS, add_zero]
      exact hs _
    rw [h, add_zero]
    exact hg.2.2

theorem free_singleton (k : Fin d) : Module.Free (R0 K n d {k}) Ω[R0 K n d {k}⁄K] := by
  haveI : Module.Free (Bp K n d) Ω[Bp K n d⁄K] := free_Bp
  exact free_of_bijective _ (ChartBij.chart_bijective (K := K) (n := n) k)

theorem free_of_mem {k : Fin d} {S : Finset (Fin d)} (hk : k ∈ S) :
    Module.Free (R0 K n d S) Ω[R0 K n d S⁄K] := by
  have hle : (cone {k} : AddSubmonoid (Gam n d)) ≤ cone S :=
    cone_mono (Finset.singleton_subset_iff.2 hk)
  letI : Algebra (R0 K n d {k}) (R0 K n d S) := (incl (K := K) hle).toRingHom.toAlgebra
  haveI : IsScalarTower K (R0 K n d {k}) (R0 K n d S) := IsScalarTower.of_algHom (incl (K := K) hle)
  haveI : IsLocalization.Away (mon K (cS k S) (cS_mem k S)) (R0 K n d S) :=
    Away.isLocalization_away hle (cS k S) (cS_mem k S) (neg_cS_mem hk) fun g hg => exists_add_nsmul_mem hk g hg
  haveI : Algebra.FormallyEtale (R0 K n d {k}) (R0 K n d S) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (mon K (cS k S) (cS_mem k S)))
  haveI : Module.Free (R0 K n d {k}) Ω[R0 K n d {k}⁄K] := free_singleton k
  exact free_of_formallyEtale K (R0 K n d {k}) (R0 K n d S)

theorem free_om : ∀ {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d)),
    Module.Free (R0 K n d S) Ω[R0 K n d S⁄K] := by
  intro K _ n d S
  rcases S.eq_empty_or_nonempty with rfl | ⟨k, hk⟩
  · haveI : Module.Free (Bp K n d) Ω[Bp K n d⁄K] := free_Bp
    exact free_of_bijective _ (PolyBij.poly_bijective (K := K) (n := n) (d := d))
  · exact free_of_mem hk

end GlobalTheory.CompanionTheory.SurjectionOntoH4.FreeOm
end
end

section

open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

theorem _root_.GlobalTheory.T.finset_system_scalar_tower_ext : ∀ {B A : Type} [CommRing B] [CommRing A] [Algebra B A] [Module.Flat B A] {ι : Type} [DecidableEq ι] [Fintype ι] (M N : Finset ι → Type) [∀ S, AddCommGroup (M S)] [∀ S, Module B (M S)] [∀ S, AddCommGroup (N S)] [∀ S, Module A (N S)] [∀ S, Module B (N S)] [∀ S, IsScalarTower B A (N S)] (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T), (∀ {S T : Finset ι} (h : S ⊆ T), IsLinearMap B (r h)) → ∀ (r' : ∀ {S T : Finset ι}, S ⊆ T → N S → N T), (∀ {S T : Finset ι} (h : S ⊆ T), IsLinearMap A (r' h)) → ∀ (ψ : ∀ S, M S →ₗ[B] N S), (∀ S, IsBaseChange A (ψ S)) → (∀ {S T : Finset ι} (h : S ⊆ T) x, r' h (ψ S x) = ψ T (r h x)) → ExP M r → ExP N r' := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.ExFlat.exP_flat | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.ExFlat.exP_flat | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.ExFlat.exP_flat <;> assumption)
end

section

open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

theorem _root_.GlobalTheory.T.chart_forms_base_change : ∀ {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d) {S : Finset (Fin d)} (θ : R0 K n d S →ₐ[K] C.R S) (hθ : ∀ b, θ (poly n K S b) = toR C S (phi C b)), IsBaseChange (Aa C) (thetaLin C θ hθ) → ∀ a : ℕ, IsBaseChange (Aa C) (psi C θ hθ a) := by
  intro K _ n d A _ _ C S θ hθ hb a
  exact GlobalTheory.CompanionTheory.SurjectionOntoH4.isBaseChange_psi C θ hθ hb a
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct GlobalTheory.CatCoh MainStatements.Hodge GlobalTheory.CompanionTheory.HodgeCx GlobalTheory.CompanionTheory.HopfLe

namespace GlobalTheory.CompanionTheory.HopfLe

theorem coboundary_cup0 {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {n : ℕ}
    (f : Cn F 0) (z : Cn F n) :
    dn F n (cup0 F f z) = cup1 F (dn F 0 f) z + cup0 F f (dn F n z) := by
  have hs : ∀ i : Fin (n + 1),
      (Fin.succAboveOrderEmb i.succ).toOrderHom.comp (vert0 n) = vert0 (n + 1) := by
    intro i
    ext j
    exact congrArg Fin.val (Fin.succ_succAbove_zero i)
  have h0 : (Fin.succAboveOrderEmb (0 : Fin (n + 2))).toOrderHom.comp (vert0 n) =
      (front n).comp (Fin.succAboveOrderEmb (0 : Fin 2)).toOrderHom := by
    ext j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    rfl
  have h1 : (front n).comp (Fin.succAboveOrderEmb (1 : Fin 2)).toOrderHom = vert0 (n + 1) := by
    ext j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    rfl
  have hL : dn F n (cup0 F f z) =
      act F (front n) (cof F 0 0 f) * cof F n 0 z +
        ∑ i : Fin (n + 1), ((-1 : R) ^ ((i : ℕ) + 1)) •
          (act F (vert0 (n + 1)) f * cof F n i.succ z) := by
    simp only [dn, cup0, LinearMap.sum_apply, LinearMap.smul_apply]
    rw [Fin.sum_univ_succ]
    simp only [cof_eq, act_mul, ← act_comp, hs, h0, Fin.val_zero, pow_zero, one_smul, Fin.val_succ]
  have hd0 : dn F 0 f = cof F 0 0 f - cof F 0 1 f := by
    simp [dn, Fin.sum_univ_two, sub_eq_add_neg]
  have hR : dn F n z = cof F n 0 z +
      ∑ i : Fin (n + 1), ((-1 : R) ^ ((i : ℕ) + 1)) • cof F n i.succ z := by
    simp only [dn, LinearMap.sum_apply, LinearMap.smul_apply]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ]
  have hf1 : act F (front n) (cof F 0 1 f) = act F (vert0 (n + 1)) f := by
    rw [cof_eq, ← h1, act_comp]
  have hb : act F (back n) z = cof F n 0 z := rfl
  rw [hL, cup1, hd0, map_sub, hf1, hb, cup0, hR, sub_mul, mul_add, Finset.mul_sum]
  simp only [mul_smul_comm]
  abel

end GlobalTheory.CompanionTheory.HopfLe
end
end

section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens

theorem exists_congr_one : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε →
    ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), cT τ T = T → IsUnit T.det →
      ∃ g : Matrix (Fin n) (Fin n) E, IsUnit g.det ∧ cT τ g * T * g = 1 := by
  intro E _ τ q ε hR n T hT hdet
  have hinv : ∀ a : E, τ (τ a) = a := hR.inv
  have hq : 1 < q := hR.one_lt
  have hcard : Nat.card (Fin n → E) = q ^ (2 * n) := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin, hR.card, ← pow_mul]
  have hcnt := GlobalTheory.T.card_orthonormal_frames_hermitian_space E τ q ε hR n n le_rfl (Fin n → E) (HermSp.ofMatrix hinv T hT hdet) hcard
  have hε : ε = -1 ∨ ε = 1 := by
    rcases hR.eps with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hne : Nat.card {x : Fin n → Fin n → E // ∀ i j : Fin n,
      (HermSp.ofMatrix hinv T hT hdet).h (x i) (x j) = if i = j then 1 else 0} ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero, eq_comm, Finset.prod_eq_zero_iff] at hcnt
    obtain ⟨i, -, hi⟩ := hcnt
    have hk : n - (i : ℕ) ≠ 0 := Nat.sub_ne_zero_of_lt i.isLt
    rcases mul_eq_zero.mp hi with h | h
    · rw [div_eq_zero_iff] at h
      rcases h with h | h
      · have h' := pow_eq_zero_iff (n := 2 * (n - (i : ℕ))) (by omega) |>.mp h
        rw [Nat.cast_eq_zero] at h'
        omega
      · rw [Nat.cast_eq_zero] at h
        omega
    · rw [sub_eq_zero] at h
      have h2 := congrArg abs h
      rw [abs_one, abs_pow, abs_div, Nat.abs_cast] at h2
      have key : ∀ {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F] (e : ℤ) (k : ℕ),
          (e = -1 ∨ e = 1) → k ≠ 0 → (1 : F) ≠ (|(e : F)| / (q : F)) ^ k := by
        intro F _ _ _ e k he hk' hh
        have hqF : (1 : F) < q := by exact_mod_cast hq
        have habs : |(e : F)| = 1 := by
          rcases he with rfl | rfl <;> simp
        rw [habs] at hh
        have hlt : (1 / (q : F)) ^ k < 1 :=
          pow_lt_one₀ (by positivity) ((div_lt_one (by linarith)).mpr hqF) hk'
        linarith
      exact key ε _ hε hk h2
  obtain ⟨⟨x, hx⟩⟩ := (Nat.card_ne_zero.mp hne).1
  have hg : cT τ (Matrix.of fun a i => x i a) * T * (Matrix.of fun a i => x i a) = 1 := by
    ext i j
    rw [gram_apply hinv T hT hdet]
    show (HermSp.ofMatrix hinv T hT hdet).h (x j) (x i) = (1 : Matrix (Fin n) (Fin n) E) i j
    rw [hx j i, Matrix.one_apply]
    by_cases h : i = j
    · subst h
      simp
    · rw [if_neg (Ne.symm h), if_neg h]
  exact ⟨_, Matrix.isUnit_det_of_left_inverse hg, hg⟩

end GlobalTheory.CompanionTheory.UnrDens
end

section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix


theorem _root_.GlobalTheory.T.delta_block_lower_bound_torsion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (m : ℕ) (c : Matrix (Fin m) (Fin m) E), (∀ a b, σ (c b a) = c a b) → ∀ (u : Fin m → E) (t : 𝓞 E), t ∈ tor c u → t ≠ 0 → ∃ f : F, ∀ d : F, delta c * Ideal.absNorm (tor c u) ^ 2 * Ideal.absNorm (den F (f + ((RingOfIntegers.norm F t : 𝓞 F) : F) * d)) ^ 2 ≤ delta (blk σ c u (algebraMap F E d)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LocalBound.local_bound | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LocalBound.local_bound | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LocalBound.local_bound <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

theorem _root_.GlobalTheory.T.haar_measure_local_ball : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (k : ℕ) (a : Fv F v), lam ((fun z => z - a) ⁻¹' ballV v k) = ENNReal.ofReal (((Ideal.absNorm v.asIdeal : ℝ) ^ k)⁻¹) := by
  first | exact @GlobalTheory.CompanionTheory.Equi.BallVol.measure_translate_ballV | exact GlobalTheory.CompanionTheory.Equi.BallVol.measure_translate_ballV | (intros; apply GlobalTheory.CompanionTheory.Equi.BallVol.measure_translate_ballV <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier

theorem _root_.GlobalTheory.T.smooth_vector_fixed_by_small_box : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Multiplicative (Fin n → k)) V), IsSmooth ρ → ∀ v : V, ∃ N : ℤ, ∀ x ∈ box k n N, ρ x v = v := by
  first | exact @GlobalTheory.CompanionTheory.MirFourier.exists_box_fixed | exact GlobalTheory.CompanionTheory.MirFourier.exists_box_fixed | (intros; apply GlobalTheory.CompanionTheory.MirFourier.exists_box_fixed <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier

theorem _root_.GlobalTheory.T.uniform_twisted_invariance_on_ball : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Multiplicative (Fin n → k)) V) (v : V) (M : ℤ), (∀ a : Fin n → k, ∃ j : ℤ, ∀ j' ≤ j, v ∈ twKer ρ (box k n j') (chiOn k ψ a (box k n j'))) → ∃ J : ℤ, ∀ J' ≤ J, ∀ a : Fin n → k, (∀ i, a i ∈ valBall k M) → v ∈ twKer ρ (box k n J') (chiOn k ψ a (box k n J')) := by
  first | exact @GlobalTheory.CompanionTheory.MirFourier.exists_box_forall_chi | exact GlobalTheory.CompanionTheory.MirFourier.exists_box_forall_chi | (intros; apply GlobalTheory.CompanionTheory.MirFourier.exists_box_forall_chi <;> assumption)
end
