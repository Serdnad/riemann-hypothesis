module

public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInNormalAt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle020
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle014
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle023
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle030
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle037
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BasisPowerSectionsLocalBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusVia
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
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.GenMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd
import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle001
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyConst

theorem exists_rescale (P : Out.PolAV (Sp ℂ)) (hg rig hr th hth v hv)
    (τ M : Matrix (Fin P.g) (Fin P.g) ℂ) (a b : Fin P.g → ℂ) (c : ℂ) (hc : c ≠ 0) (hM : M.det ≠ 0)
    (hx : NormalAt ⟨P, hg, rig, hr, th, hth, v, hv⟩ τ M a b c) :
    ∃ th₀ hth₀ v₀ hv₀, NormalAt ⟨P, hg, rig, hr, th₀, hth₀, v₀, hv₀⟩ τ 1 a b 1 ∧
      (∀ i, LB.Sec.f th i = constFn P.A.hom _ c * LB.Sec.f th₀ i) ∧ ∀ i, IsLieComb (M i) v₀ (v i) := by
  obtain ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩ := hx
  haveI := P.isAb.comm
  obtain ⟨ex, tan, comp, sgl, bas⟩ := GlobalTheory.LieComb.lieComb_algebra ℂ P.A P.g v hv.1
  choose v₀ hv₀ using fun i => (ex (M⁻¹ i)).exists
  have hb₀ : IsLieBasis v₀ := (bas M⁻¹ v₀ hv hv₀).2 (Matrix.isUnit_nonsing_inv_det M hM.isUnit)
  obtain ⟨ex₀, -, -, -, -⟩ := GlobalTheory.LieComb.lieComb_algebra ℂ P.A P.g v₀ hb₀.1
  have hMv : ∀ i, IsLieComb (M i) v₀ (v i) := fun i => by
    obtain ⟨w, hw⟩ := (ex₀ (M i)).exists
    have h1 := comp _ (fun i => M⁻¹ i) v₀ (M i) w hv₀ hw
    have e : ∑ j, M i j • M⁻¹ j = Pi.single i 1 := by
      rw [← Matrix.vecMul_eq_sum]
      refine (congrFun (Matrix.mul_nonsing_inv M hM.isUnit) i).trans ?_
      simpa using smul_one_row (1 : ℂ) i
    rw [e] at h1
    rwa [(ex _).unique (sgl i) h1]
  obtain ⟨th₀, e₀, e₁, hle⟩ := exists_sec_div P.A.hom (mul_inv_cancel₀ hc) th
  have hth₀ : ∀ s : Sp ℂ, ∃ y : P.A.left, P.A.hom y = s ∧ y ∈ Out.nonzeroLocus th₀ :=
    fun s => (hth s).imp fun y hy => ⟨hy.1, hle hy.2⟩
  refine ⟨th₀, hth₀, v₀, hb₀, ⟨u, h₁, h₂, h₃, h₄, ?_, ?_⟩, e₁, hMv⟩
  · intro i z hz
    have e := h₅ i z hz
    refine ((congrArg (valAt' _ _) (e₀ i)).trans (valAt'_mul _ _ _ _)).trans ?_
    rw [valAt'_constFn _ _ (Over.w (u.ex z)) _ _ hz]
    refine (congrArg (c⁻¹ * ·) e).trans ?_
    beta_reduce
    rw [_root_.one_mul, ← _root_.mul_assoc, inv_mul_cancel_left₀ hc]
  · intro i
    have h1 := GlobalTheory.UnifDifferential.isDiff_of_isLieComb P.A P.L P.g P.g u _ v _ _ hv.1 h₆ (hv₀ i)
    have e : ∑ j, M⁻¹ i j • ((2 * Real.pi * Complex.I : ℂ)⁻¹ • M j) =
        (2 * Real.pi * Complex.I : ℂ)⁻¹ • (1 : Matrix (Fin P.g) (Fin P.g) ℂ) i := by
      simp only [smul_comm (M⁻¹ i _) (2 * Real.pi * Complex.I : ℂ)⁻¹]
      rw [← Finset.smul_sum, ← Matrix.vecMul_eq_sum, ← Matrix.nonsing_inv_mul M hM.isUnit]
      rfl
    rwa [e] at h1

theorem value_eq {g c N : ℕ} {ka : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ} (hk : KaRuleK g c N ka)
    (a b : Fin g → ℂ) (U : Matrix (Fin g) (Fin g) ℂ → ℂ)
    (hU : ∀ (x : KeyIn ℂ) (h : x.P.g = g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ),
        NormalAt x τ 1 (fun i => a (i.cast h)) (fun i => b (i.cast h)) 1 →
        (ka ℂ x : ℂ) = U (τ.submatrix (Fin.cast h.symm) (Fin.cast h.symm)))
    (x : KeyIn ℂ) (h : x.P.g = g) (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c₀ : ℂ) (hc : c₀ ≠ 0)
    (hM : M.det ≠ 0) (hx : NormalAt x τ M (fun i => a (i.cast h)) (fun i => b (i.cast h)) c₀) :
    (ka ℂ x : ℂ) = U (τ.submatrix (Fin.cast h.symm) (Fin.cast h.symm)) * (M.det ^ 4 / c₀ ^ 8) ^ c := by
  obtain ⟨P, hg, rig, hr, th, hth, v, hv⟩ := x
  obtain ⟨th₀, hth₀, v₀, hv₀, hN, e₁, hMv⟩ := exists_rescale P hg rig hr th hth v hv τ M _ _ c₀ hc hM hx
  have h0 := hU ⟨P, hg, rig, hr, th₀, hth₀, v₀, hv₀⟩ h τ hN
  have h1 := hk.1 ℂ P hg rig hr _ hth₀ v₀ hv₀ th hth v hv c₀ M h e₁ hMv
  rw [h0] at h1
  rw [div_pow, ← pow_mul, ← pow_mul, ← mul_div_assoc, eq_div_iff (pow_ne_zero _ hc), mul_comm, mul_comm (U _)]
  exact h1

theorem value_spAct {g c N : ℕ} {ka : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ} (hk : KaRuleK g c N ka)
    (n n' k k' : Fin g → ℤ) (U V : Matrix (Fin g) (Fin g) ℂ → ℂ)
    (hU : ∀ (x : KeyIn ℂ) (h : x.P.g = g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ),
        NormalAt x τ 1 (fun i => (n (i.cast h) : ℂ) / 2) (fun i => (n' (i.cast h) : ℂ) / 2) 1 →
        (ka ℂ x : ℂ) = U (τ.submatrix (Fin.cast h.symm) (Fin.cast h.symm)))
    (hV : ∀ (x : KeyIn ℂ) (h : x.P.g = g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ),
        NormalAt x τ 1 (fun i => (k (i.cast h) : ℂ) / 2) (fun i => (k' (i.cast h) : ℂ) / 2) 1 →
        (ka ℂ x : ℂ) = V (τ.submatrix (Fin.cast h.symm) (Fin.cast h.symm)))
    (sp : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (hsp : sp ∈ Matrix.symplecticGroup (Fin g) ℤ)
    (hL : ThetaLaw g sp n n' k k') (τ : Matrix (Fin g) (Fin g) ℂ) (x : KeyIn ℂ) (h : x.P.g = g)
    (hx : NormalAt x (τ.submatrix (Fin.cast h) (Fin.cast h)) 1 (fun i => (n (i.cast h) : ℂ) / 2)
      (fun i => (n' (i.cast h) : ℂ) / 2) 1) :
    U τ = V (Key.Chi.spAct sp τ) := by
  subst h
  have hx' : NormalAt x τ 1 (fun i => (n i : ℂ) / 2) (fun i => (n' i : ℂ) / 2) 1 := hx
  obtain ⟨M', c', hc', e, hN⟩ := GlobalTheory.SpMove.normalAt_spAct x τ 1 1 sp n n' k k' hsp hL one_ne_zero hx'
  have e' : M'.det ^ 4 / c' ^ 8 = 1 := by rw [e]; simp
  have hM' : M'.det ≠ 0 := fun h0 => by rw [h0] at e'; simp at e'
  have h1 : (ka ℂ x : ℂ) = U τ := hU x rfl τ hx'
  have h2 : (ka ℂ x : ℂ) = V (Key.Chi.spAct sp τ) * (M'.det ^ 4 / c' ^ 8) ^ c :=
    value_eq hk (fun i => (k i : ℂ) / 2) (fun i => (k' i : ℂ) / 2) V hV x rfl _ M' c' hc' hM' hN
  rw [e', _root_.one_pow, _root_.mul_one] at h2
  rw [← h1, h2]

abbrev Bits (g : ℕ) : Type := {n : Fin g → ℤ // ∀ i, n i = 0 ∨ n i = 1}

instance finite_bits (g : ℕ) : Finite (Bits g) := by
  have h : {n : Fin g → ℤ | ∀ i, n i ∈ ({0, 1} : Set ℤ)}.Finite :=
    Set.Finite.pi' fun _ => Set.toFinite _
  exact h.to_subtype

theorem charHalf_bits {g : ℕ} (n n' : Bits g) :
    charHalf g (fun i => (n.1 i : ℂ) / 2) (fun i => (n'.1 i : ℂ) / 2) :=
  ⟨fun i => (n.2 i).imp (fun h => by simp [h]) (fun h => by simp [h]),
    fun i => (n'.2 i).imp (fun h => by simp [h]) (fun h => by simp [h])⟩

def IsValueFn {g : ℕ} (κ : KeyIn ℂ → ℂˣ) (n n' : Fin g → ℤ) (U : Matrix (Fin g) (Fin g) ℂ → ℂ) : Prop :=
  ∀ (x : KeyIn ℂ) (h : x.P.g = g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ),
    NormalAt x τ 1 (fun i => (n (i.cast h) : ℂ) / 2) (fun i => (n' (i.cast h) : ℂ) / 2) 1 →
    (κ x : ℂ) = U (τ.submatrix (Fin.cast h.symm) (Fin.cast h.symm))

theorem exists_valueFn {g c N : ℕ} {ka : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ}
    (hk : KaRuleK g c N ka) (p : Bits g × Bits g) :
    ∃ U, Key.IsHoloSiegel g U ∧ IsValueFn (ka ℂ) p.1.1 p.2.1 U := by
  obtain ⟨-, -, -, h⟩ := hk
  obtain ⟨U, h₁, h₂⟩ := h (fun i => (p.1.1 i : ℂ) / 2) (fun i => (p.2.1 i : ℂ) / 2) (charHalf_bits p.1 p.2)
  exact ⟨U, h₁, fun x hx τ hN => h₂ x hx τ hN⟩

theorem valueFn_perm (hT : ThetaUnifAV) (hI : Key.Chi.InversionStatement) (hA : GlobalTheory.TorusAlgebraic)
    {g c N : ℕ} {ka : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ} (hg : 1 ≤ g) (hk : KaRuleK g c N ka)
    (U : Bits g × Bits g → Matrix (Fin g) (Fin g) ℂ → ℂ) (hU : ∀ p, IsValueFn (ka ℂ) p.1.1 p.2.1 (U p)) :
    ∀ sp ∈ Matrix.symplecticGroup (Fin g) ℤ, ∀ i, ∃ j,
      ∀ τ ∈ ReciprocityTheory.PTheta.SiegelH (Fin g), U i τ = U j (Key.Chi.spAct sp τ) := by
  intro sp hsp i
  obtain ⟨k, k', hk₁, hk₂, hL⟩ :=
    (chiAt_iff_thetaLaw g sp).1 (Key.Chi.chi_of hI Key.Chi.spGen g sp hsp) i.1.1 i.2.1
  refine ⟨(⟨k, hk₁⟩, ⟨k', hk₂⟩), fun τ hτ => ?_⟩
  obtain ⟨x, h, hx⟩ := GlobalTheory.KeyOfPeriod.exists_keyIn_normalAt hT hA g τ _ _ hg hτ.1 hτ.2 (charHalf_bits i.1 i.2)
  exact value_spAct hk i.1.1 i.2.1 k k' _ _ (hU i) (hU (⟨k, hk₁⟩, ⟨k', hk₂⟩)) sp hsp hL τ x h hx

theorem value_zero {c N : ℕ} {ka : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ} (x : KeyIn ℂ)
    (hk : KaRuleK x.P.g c N ka) (U : Matrix (Fin x.P.g) (Fin x.P.g) ℂ → ℂ) (hU : IsValueFn (ka ℂ) 0 0 U)
    (τ Mx : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c₀ : ℂ) (hc : c₀ ≠ 0) (hM : Mx.det ≠ 0)
    (hx : NormalAt x τ Mx 0 0 c₀) : (ka ℂ x : ℂ) = U τ * (Mx.det ^ 4 / c₀ ^ 8) ^ c := by
  have e : (fun i : Fin x.P.g => (((0 : Fin x.P.g → ℤ) i : ℤ) : ℂ) / 2) = 0 := by
    funext i; simp
  have hx' : NormalAt x τ Mx (fun i => (((0 : Fin x.P.g → ℤ) i : ℤ) : ℂ) / 2)
      (fun i => (((0 : Fin x.P.g → ℤ) i : ℤ) : ℂ) / 2) c₀ := by
    rw [e]; exact hx
  exact value_eq hk (fun i => (((0 : Fin x.P.g → ℤ) i : ℤ) : ℂ) / 2)
    (fun i => (((0 : Fin x.P.g → ℤ) i : ℤ) : ℂ) / 2) U hU x rfl τ Mx c₀ hc hM hx'

theorem exists_const : ThetaUnifAV → Key.Chi.InversionStatement → Key.PhHoloStatement → GlobalTheory.TorusAlgebraic → ∀ (g c M : ℕ) (ka : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ), 2 ≤ g → KaRuleK g c M ka → ∃ a₀ : ℂ, ∀ (x : KeyIn ℂ) (τ Mx : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c₀ : ℂ), x.P.g = g → c₀ ≠ 0 → Mx.det ≠ 0 → NormalAt x τ Mx 0 0 c₀ → (ka ℂ x : ℂ) = a₀ * (Mx.det ^ 4 / c₀ ^ 8) ^ c := by
  intro hT hI hP hA g c N ka hg hk
  choose U hUh hU using exists_valueFn hk
  obtain ⟨a₀, ha⟩ := GlobalTheory.const_of_finite_family_spAct hP g _ U hg hUh (valueFn_perm hT hI hA (by omega) hk U hU)
    (⟨0, fun _ => Or.inl rfl⟩, ⟨0, fun _ => Or.inl rfl⟩)
  refine ⟨a₀, fun x τ Mx c₀ h hc hM hx => ?_⟩
  subst h
  rw [← ha τ hx.mem_siegelH]
  exact value_zero x hk _ (hU (⟨0, fun _ => Or.inl rfl⟩, ⟨0, fun _ => Or.inl rfl⟩)) τ Mx c₀ hc hM hx

end GlobalTheory.KeyConst
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory

theorem locallyOfFinitePresentation_pspace_str (R : Type) [CommRing R] (N : ℕ) :
    LocallyOfFinitePresentation (PSpace.str R N) := by
  have hloc : IsZariskiLocalAtSource @LocallyOfFinitePresentation :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation)
  refine IsZariskiLocalAtSource.of_openCover (ProjSpace.chartCover R N) fun (i : Fin (N + 1)) => ?_
  change LocallyOfFinitePresentation (ProjSpace.chartι R N i ≫ PSpace.str R N)
  rw [ProjSpace.chartι_str]
  change LocallyOfFinitePresentation
    (Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial {j // j ≠ i} R)))
  rw [LocallyOfFinitePresentation.SpecMap_iff, CommRingCat.hom_ofHom, ← MvPolynomial.algebraMap_eq,
    RingHom.finitePresentation_algebraMap]
  infer_instance

theorem isProjOver_descends_to_subring :
    ∀ (S : Type) [CommRing S] (R₀ : Subring S) (X X₀ : Scheme.{0}) (f : X ⟶ Sp S) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀] [LocallyOfFiniteType f₀], IsPullback π f f₀ (spMap R₀.subtype) → IsProjOver f → ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion h)) → IsProjOver f₁ := by
  intro S _ R₀ X X₀ f f₀ π _ _ _ hX hP
  classical
  have hsub : ∀ {A B : Subring S} (hAB : A ≤ B), B.subtype.comp (Subring.inclusion hAB) = A.subtype :=
    fun _ => RingHom.ext fun _ => rfl
  have hincl : ∀ {A B C : Subring S} (hAB : A ≤ B) (hBC : B ≤ C) (hAC : A ≤ C),
      (Subring.inclusion hBC).comp (Subring.inclusion hAB) = Subring.inclusion hAC :=
    fun _ _ _ => RingHom.ext fun _ => rfl
  have hsp : ∀ {A B : Subring S} (hAB : A ≤ B),
      spMap B.subtype ≫ spMap (Subring.inclusion hAB) = spMap A.subtype := by
    intro A B hAB
    rw [← spMap_comp, hsub]
  have hsp2 : ∀ {A B C : Subring S} (hAB : A ≤ B) (hBC : B ≤ C) (hAC : A ≤ C),
      spMap (Subring.inclusion hBC) ≫ spMap (Subring.inclusion hAB) = spMap (Subring.inclusion hAC) := by
    intro A B C hAB hBC hAC
    rw [← spMap_comp, hincl]
  obtain ⟨M, i, hci, hif⟩ := hP
  have : LocallyOfFinitePresentation (PSpace.str R₀ M) := locallyOfFinitePresentation_pspace_str R₀ M
  have hφ : (i ≫ ProjSpace.baseChange M R₀.subtype) ≫ PSpace.str R₀ M = π ≫ f₀ := by
    rw [Category.assoc, ProjSpace.baseChange_str, ← Category.assoc, hif, hX.w]
  obtain ⟨F₁, hF₁⟩ := morphism_descends_to_subring S R₀ X X₀ (PSpace R₀ M) f f₀ (PSpace.str R₀ M) π
    (i ≫ ProjSpace.baseChange M R₀.subtype) hX hφ
  set R₀' : Subring S := R₀ ⊔ Subring.closure (F₁ : Set S) with hR₀'
  have h₀ : R₀ ≤ R₀' := le_sup_left
  have hF₁' : (F₁ : Set S) ⊆ R₀' := fun x hx =>
    (le_sup_right : Subring.closure (F₁ : Set S) ≤ R₀') (Subring.subset_closure hx)
  obtain ⟨X₀', π₀', f₀', hX₀'⟩ : ∃ (X₀' : Scheme.{0}) (π₀' : X₀' ⟶ X₀) (f₀' : X₀' ⟶ Sp R₀'),
      IsPullback π₀' f₀' f₀ (spMap (Subring.inclusion h₀)) :=
    ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  obtain ⟨j, hjπ, hjf⟩ : ∃ j : X ⟶ X₀', j ≫ π₀' = π ∧ j ≫ f₀' = f ≫ spMap R₀'.subtype :=
    ⟨hX₀'.lift π (f ≫ spMap R₀'.subtype) (by rw [Category.assoc, hsp h₀, hX.w]),
      hX₀'.lift_fst _ _ _, hX₀'.lift_snd _ _ _⟩
  obtain ⟨ψ, hjψ, hψq⟩ := hF₁ R₀' h₀ hF₁' X₀' f₀' π₀' j hX₀' hjπ hjf
  have hbc₀ := ProjSpace.isPullback_baseChange M (Subring.inclusion h₀)
  obtain ⟨g₀, hg₀b, hg₀q⟩ : ∃ g₀ : X₀' ⟶ PSpace R₀' M,
      g₀ ≫ ProjSpace.baseChange M (Subring.inclusion h₀) = ψ ∧ g₀ ≫ PSpace.str R₀' M = f₀' :=
    ⟨hbc₀.lift ψ f₀' (by rw [hψq, hX₀'.w]), hbc₀.lift_fst _ _ _, hbc₀.lift_snd _ _ _⟩
  have : IsProper (PSpace.str R₀' M) := isProper_str R₀' M
  have : QuasiCompact f₀' := MorphismProperty.of_isPullback (P := @QuasiCompact) hX₀' inferInstance
  have : QuasiSeparated f₀' := MorphismProperty.of_isPullback (P := @QuasiSeparated) hX₀' inferInstance
  have : LocallyOfFiniteType f₀' :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hX₀' inferInstance
  have : LocallyOfFiniteType (g₀ ≫ PSpace.str R₀' M) := by rw [hg₀q]; infer_instance
  have : QuasiSeparated (g₀ ≫ PSpace.str R₀' M) := by rw [hg₀q]; infer_instance
  have : QuasiCompact (g₀ ≫ PSpace.str R₀' M) := by rw [hg₀q]; infer_instance
  have : LocallyOfFiniteType g₀ := locallyOfFiniteType_of_comp g₀ (PSpace.str R₀' M)
  have : QuasiSeparated g₀ := QuasiSeparated.of_comp g₀ (PSpace.str R₀' M)
  have : QuasiCompact g₀ := QuasiCompact.of_comp g₀ (PSpace.str R₀' M)
  have hY := ProjSpace.isPullback_baseChange M R₀'.subtype
  have hbc : ProjSpace.baseChange M R₀'.subtype ≫ ProjSpace.baseChange M (Subring.inclusion h₀) =
      ProjSpace.baseChange M R₀.subtype := by
    rw [← ProjSpace.baseChange_comp, hsub]
  have hleft : IsPullback j f f₀' (spMap R₀'.subtype) := by
    refine IsPullback.of_right ?_ hjf hX₀'
    rw [hjπ, hsp h₀]
    exact hX
  have hsq : IsPullback j i g₀ (ProjSpace.baseChange M R₀'.subtype) := by
    refine IsPullback.of_bot ?_ ?_ hY
    · rw [hif, hg₀q]
      exact hleft
    · apply hbc₀.hom_ext
      · rw [Category.assoc, hg₀b, hjψ, Category.assoc, hbc]
      · rw [Category.assoc, hg₀q, hjf, Category.assoc, ProjSpace.baseChange_str, ← Category.assoc, hif]
  obtain ⟨F₂, hF₂⟩ := GlobalTheory.T.isClosedImmersion_descends_to_subring' S R₀' X₀' (PSpace R₀' M) X (PSpace S M) g₀ (PSpace.str R₀' M)
    i j (ProjSpace.baseChange M R₀'.subtype) (PSpace.str S M) hY hsq hci
  refine ⟨F₁ ∪ F₂, fun R₁ h hF X₁ f₁ π₁ hX₁ => ?_⟩
  have h' : R₀' ≤ R₁ := sup_le h (Subring.closure_le.2 fun x hx =>
    hF (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 hx))))
  have hF₂' : (F₂ : Set S) ⊆ R₁ := fun x hx =>
    hF (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_coe.1 hx)))
  obtain ⟨πX₁, hπ₁, hf₁⟩ : ∃ πX₁ : X₁ ⟶ X₀',
      πX₁ ≫ π₀' = π₁ ∧ πX₁ ≫ f₀' = f₁ ≫ spMap (Subring.inclusion h') :=
    ⟨hX₀'.lift π₁ (f₁ ≫ spMap (Subring.inclusion h')) (by rw [Category.assoc, hsp2 h₀ h' h, hX₁.w]),
      hX₀'.lift_fst _ _ _, hX₀'.lift_snd _ _ _⟩
  have hleft₁ : IsPullback πX₁ f₁ f₀' (spMap (Subring.inclusion h')) := by
    refine IsPullback.of_right ?_ hf₁ hX₀'
    rw [hπ₁, hsp2 h₀ h' h]
    exact hX₁
  have hY₁ := ProjSpace.isPullback_baseChange M (Subring.inclusion h')
  obtain ⟨g₁, hg₁b, hg₁q⟩ : ∃ g₁ : X₁ ⟶ PSpace R₁ M,
      g₁ ≫ ProjSpace.baseChange M (Subring.inclusion h') = πX₁ ≫ g₀ ∧ g₁ ≫ PSpace.str R₁ M = f₁ :=
    ⟨hY₁.lift (πX₁ ≫ g₀) f₁ (by rw [Category.assoc, hg₀q, hf₁]), hY₁.lift_fst _ _ _,
      hY₁.lift_snd _ _ _⟩
  have hsq₁ : IsPullback πX₁ g₁ g₀ (ProjSpace.baseChange M (Subring.inclusion h')) := by
    refine IsPullback.of_bot ?_ hg₁b.symm hY₁
    rw [hg₁q, hg₀q]
    exact hleft₁
  have := hF₂ R₁ h' hF₂' X₁ (PSpace R₁ M) g₁ πX₁ (ProjSpace.baseChange M (Subring.inclusion h'))
    (PSpace.str R₁ M) hY₁ hsq₁
  rw [← hg₁q]
  exact ProjSpace.isProjOver_comp_of_isClosedImmersion g₁ (ProjSpace.isProjOver_pspace_str R₁ M)

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.exists_principalPolarization_section_nonzero_near_two_primes : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Q : Out.PolAV (Sp R)) (p q : PrimeSpectrum R), ∃ (th : Q.L.Sec) (r : R), r ∉ p.asIdeal ∧ r ∉ q.asIdeal ∧ ∀ z : Sp R, r ∉ z.asIdeal → ∃ x : Q.A.left, Q.A.hom x = z ∧ x ∈ Out.nonzeroLocus th := by
  first | exact @GlobalTheory.TwoPrimeSection.main | exact GlobalTheory.TwoPrimeSection.main | (intros; apply GlobalTheory.TwoPrimeSection.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyBaseChangeData

theorem via_mul {X Y : Scheme.{0}} {L : LB X} {L' : LB Y} {φ : Y ⟶ X} {w : LB.Iso L' (L.pull φ)} {l l' k : ℕ}
    (hk : l + l' = k) {a' b' : ∀ i, Γ(Y, L'.U i)} {a b : ∀ j, Γ(X, L.U j)} (ha : KeyVia.Via w l a' a)
    (hb : KeyVia.Via w l' b' b) : KeyVia.Via w k (fun i => a' i * b' i) (fun j => a j * b j) := by
  intro j i h
  rw [map_mul, map_mul, ha j i h, hb j i h, ← hk, pow_add, _root_.mul_mul_mul_comm]

theorem coords_mul {R R' : Type} [CommRing R] [CommRing R'] {x : KeyIn R} {x' : KeyIn R'} {f : R →+* R'} {φ w}
    (hx : KeyVia x' x f φ w) {n l k N : ℕ} (hk : n + l = k) {s : RR x n} {s' : RR x' n} {e : RR x l} {e' : RR x' l}
    {b : Fin N → RR x k} {b' : Fin N → RR x' k} {c : Fin N → R} (hs : SecVia x' x φ w s' s)
    (he : SecVia x' x φ w e' e) (hb : ∀ i, SecVia x' x φ w (b' i) (b i))
    (hc : Coords x b c (fun i => (show Γ(x.P.A.left, x.P.L.U i) from s.f i) * (show Γ(x.P.A.left, x.P.L.U i) from e.f i))) :
    Coords x' b' (fun i => f (c i))
      (fun i => (show Γ(x'.P.A.left, x'.P.L.U i) from s'.f i) * (show Γ(x'.P.A.left, x'.P.L.U i) from e'.f i)) := by
  obtain ⟨-, -, -, ⟨hP, -⟩, -⟩ := hx
  have H := KeyVia.Via.comb (w := w) (l := k) (b' := fun i => (b' i).f) (b := fun i => (b i).f) f x.P.A.hom
    x'.P.A.hom hP.w hb c
  have H' := via_mul (w := w) hk (a' := s'.f) (b' := e'.f) (a := s.f) (b := e.f) hs he
  have H'' := (congrArg (KeyVia.Via w k _) (funext hc)).mp H'
  exact fun i => congrFun (KeyVia.Via.unique x.P.isLB H'' H) i

theorem exists_baseChange_data : Out.Laws → ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (R' : Type) [CommRing R'] (f : O →+* R') (x : KeyIn O) (n l : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (m), x.P.g * n < l → (∀ j ≤ x.P.g, IsBasis x (b j)) → IsMul x l s b m → ∃ (x' : KeyIn R') (φ : x'.P.A.left ⟶ x.P.A.left) (w : LB.Iso x'.P.L (x.P.L.pull φ)) (hg : x'.P.g = x.P.g) (s' : Fin x'.P.g → RR x' n) (b' : ∀ j, Fin ((l - j * n) ^ x'.P.g) → RR x' (l - j * n)) (m' : _), KeyVia x' x f φ w ∧ (∀ i, SecVia x' x φ w (s' i) (s (i.cast hg))) ∧ (∀ j k, SecVia x' x φ w (b' j k) (b j (k.cast (congrArg (fun r => (l - j * n) ^ r) hg)))) ∧ (∀ j ≤ x'.P.g, IsBasis x' (b' j)) ∧ IsMul x' l s' b' m' ∧ (∀ i j j' k k', m' i j j' k k' = f (m (i.cast hg) j j' (k.cast (congrArg (fun r => (l - j * n) ^ r) hg)) (k'.cast (congrArg (fun r => (l - j' * n) ^ r) hg)))) ∧ (Finite (Sp R') → FinZ x s → FinZ x' s') := by
  intro laws O _ _ _ R' _ f x n l s b m hl hb hm
  obtain ⟨x', hx'⟩ := KeyPow.exists_keyPB_ring x f
  obtain ⟨φ, w, hx⟩ := (KeyVia.main O R' x x' f).1.1 hx'
  have hg : x'.P.g = x.P.g := by
    obtain ⟨-, hg, -⟩ := hx
    exact hg
  obtain ⟨⟨A', ab, g', sm, L', hL', p₁, p₂, p₃, p₄⟩, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩ := x'
  obtain rfl : g' = x.P.g := hg
  let x' : KeyIn R' := ⟨⟨A', ab, x.P.g, sm, L', hL', p₁, p₂, p₃, p₄⟩, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩
  have hex := ((KeyVia.main O R' x x' f).2 φ w hx).1
  choose s' hs' using fun i => (hex _ (s i)).exists
  choose b' hb' using fun j k => (hex _ (b j k)).exists
  refine ⟨x', φ, w, rfl, s', b', fun i j j' => (m i j j').map f, hx, hs', hb', fun j hj => ?_,
    fun i j hj k => ?_, fun _ _ _ _ _ => rfl, fun hfin hz => ?_⟩
  · have h₁ : j * n ≤ x.P.g * n := Nat.mul_le_mul_right n hj
    exact (KeyBasis.main laws O x (l - j * n) (by omega)).2 (b j) (hb j hj) R' f x' φ w (b' j) hx (hb' j)
  · have h₁ : (j + 1) * n ≤ x.P.g * n := Nat.mul_le_mul_right n hj
    have h₂ : n + (l - (j + 1) * n) = l - j * n := by
      rw [Nat.add_mul, Nat.one_mul] at h₁ ⊢
      omega
    exact coords_mul hx h₂ (hs' i) (hb' (j + 1) k) (hb' j) (hm i j hj k)
  · obtain ⟨-, -, -, ⟨hP, -⟩, -⟩ := hx
    have hc : IsClosed {y : x.P.A.left | ∀ i, y ∉ Out.nonzeroLocus (s i)} := by
      rw [Set.setOf_forall]
      exact isClosed_iInter fun i => (Out.nonzeroLocus (s i)).isOpen.isClosed_compl
    haveI : IsProper x.P.A.hom := x.P.isAb.proper
    refine (KeyFin.finite_preimage_of_isPullback_of_finite_base _ _ _ _ _ _ _ _ _ inferInstance inferInstance
      hP hfin hc hz).subset fun y hy i h => hy i ?_
    exact EtBaseChange.mem_nonzeroLocus_via (hs' i) y h

end GlobalTheory.KeyBaseChangeData
end
end
