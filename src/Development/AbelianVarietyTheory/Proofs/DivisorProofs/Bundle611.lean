module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUniMat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle562
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle560
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle571
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle402
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle459
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp ValuativeRel NumberField IsDedekindDomain
open scoped NNReal

noncomputable section
namespace GlobalTheory.LGrp.BorelCompletion

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem ordV_eq (x : v.adicCompletion F) : Formalism.UG.ordV F v x = -WithZero.log (Valued.v x) := by
  unfold Formalism.UG.ordV
  split_ifs with h
  · simp [h]
  · rw [WithZero.toAdd_unzero_eq_log]

theorem nabs_completion (x : (v.adicCompletion F)ˣ) :
    letI := GlobalTheory.LocalData.complRel v
    haveI := GlobalTheory.LocalData.isLocalField v
    GlobalTheory.SplitWeil.nabs (v.adicCompletion F) x =
      (Formalism.UG.qV F v : ℝ) ^ (WithZero.log (Valued.v (x : v.adicCompletion F))) := by
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  haveI : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (v.adicCompletion F))
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))
  have hO : 𝒪[v.adicCompletion F] = (v.adicCompletionIntegers F).toSubring := by
    ext y
    rw [Valuation.mem_integer_iff, he.le_one_iff_le_one]
    exact Iff.rfl
  have hq : GlobalTheory.SplitWeil.resCard (v.adicCompletion F) = Formalism.UG.qV F v := by
    rw [← Formalism.UG.P.tjcosets_card_residue]
    exact Nat.card_congr (IsLocalRing.ResidueField.mapEquiv (RingEquiv.subringCongr hO)).toEquiv
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (-1 : ℤ))
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact WithZero.exp_ne_zero (hπ.symm.trans (map_zero _))
  have hle : ∀ y : 𝒪[v.adicCompletion F], Valued.v (y : v.adicCompletion F) ≤ 1 := fun y =>
    he.le_one_iff_le_one.1 ((Valuation.mem_integer_iff _ _).1 y.2)
  have hunit : ∀ y : 𝒪[v.adicCompletion F], IsUnit y ↔ Valued.v (y : v.adicCompletion F) = 1 := fun y => by
    rw [← he.eq_one_iff_eq_one]
    exact (Valuation.integer.integers (valuation (v.adicCompletion F))).isUnit_iff_valuation_eq_one
  have hπO : π ∈ 𝒪[v.adicCompletion F] := by
    rw [Valuation.mem_integer_iff, he.le_one_iff_le_one, hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  have hirr : Irreducible (⟨π, hπO⟩ : 𝒪[v.adicCompletion F]) := by
    refine ⟨?_, fun a b hab => ?_⟩
    · rw [hunit]
      show Valued.v π ≠ 1
      rw [hπ, ← WithZero.exp_zero, Ne, WithZero.exp_inj]
      norm_num
    · have h1 : Valued.v (a : v.adicCompletion F) * Valued.v (b : v.adicCompletion F) =
          WithZero.exp (-1 : ℤ) := by
        rw [← hπ, ← map_mul]
        exact congrArg _ (congrArg Subtype.val hab).symm
      have ha : Valued.v (a : v.adicCompletion F) ≠ 0 := left_ne_zero_of_mul (by rw [h1]; simp)
      have hb : Valued.v (b : v.adicCompletion F) ≠ 0 := right_ne_zero_of_mul (by rw [h1]; simp)
      have ha1 := hle a
      have hb1 := hle b
      rw [hunit, hunit]
      rw [← WithZero.exp_log ha] at h1 ha1 ⊢
      rw [← WithZero.exp_log hb] at h1 hb1 ⊢
      rw [← WithZero.exp_add, WithZero.exp_inj] at h1
      rw [← WithZero.exp_zero, WithZero.exp_le_exp] at ha1 hb1
      rw [← WithZero.exp_zero, WithZero.exp_inj, WithZero.exp_inj]
      omega
  have h1 := GlobalTheory.SplitWeil.nabs_uniformiser hirr (x := Units.mk0 π hπ0) rfl
  rw [hq] at h1
  set m := WithZero.log (Valued.v (x : v.adicCompletion F)) with hm
  have hx : Valued.v (x : v.adicCompletion F) = WithZero.exp m := (WithZero.exp_log (by simp)).symm
  have h2 : GlobalTheory.SplitWeil.nabs (v.adicCompletion F) (x * (Units.mk0 π hπ0) ^ m) = 1 := by
    apply GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one
    rw [he.eq_one_iff_eq_one, Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, Units.val_mk0,
      hπ, hx, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have h3 : GlobalTheory.SplitWeil.nabs (v.adicCompletion F) ((Units.mk0 π hπ0) ^ m) = ((Formalism.UG.qV F v : ℝ)⁻¹) ^ m := by
    rw [← h1]
    simp only [GlobalTheory.SplitWeil.nabs, map_zpow, NNReal.coe_zpow]
  rw [GlobalTheory.SplitWeil.nabs_mul, h3, inv_zpow] at h2
  exact (eq_inv_of_mul_eq_one_left h2).trans (inv_inv _)

theorem sqrt_zpow_eq (q : ℕ) (m e : ℤ) :
    ((Real.sqrt (((q : ℝ) ^ m) ^ e) : ℝ) : ℂ) = (q : ℂ) ^ ((m : ℂ) * ((e : ℂ) / 2)) := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  rw [Real.sqrt_eq_rpow, ← zpow_mul, ← Real.rpow_intCast, ← Real.rpow_mul hq, Complex.ofReal_cpow hq]
  congr 1
  push_cast
  ring

theorem deltaHalf_mul_unrTorus : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) [LocallyCompactSpace (v.adicCompletion F)] (n : ℕ) (α : Fin n → ℂˣ) (b : (borelGL (v.adicCompletion F) (Fin n)).Q), (((borelGL (v.adicCompletion F) (Fin n)).deltaHalf b : ℂˣ) : ℂ) * ((unrTorus (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).toMonoidWithZeroHom α ((borelGL (v.adicCompletion F) (Fin n)).p b) : ℂˣ) : ℂ) = Formalism.UG.chiDelta F v (fun i => (α i : ℂ)) b.1 := by
  intro F _ _ v _ n α b
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  have h := GlobalTheory.BorelModulus.delta_borelGL (v.adicCompletion F) n b
  rw [LeviDatum.deltaHalf_coe, h, Real.sqrt_prod _ (fun i _ => zpow_nonneg (GlobalTheory.SplitWeil.nabs_pos _ _).le _),
    unrTorus_apply, Formalism.UG.chiDelta, Complex.ofReal_prod, Units.coe_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have e : (((borelGL (v.adicCompletion F) (Fin n)).p b i : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      (b.1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i := rfl
  rw [nabs_completion, sqrt_zpow_eq, unrChar_apply, ordV_eq, e, mul_comm, Units.val_zpow_eq_zpow_val]
  congr 2
  push_cast
  ring

end GlobalTheory.LGrp.BorelCompletion
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.augmentation_sigma_map_basic_properties : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (σ : R₁ ⊗[R₀] B₀ →+ B), α.IsSig p σ → (∀ y, σ y ∈ I.map (algebraMap R B)) ∧ (∀ b y, σ ((1 ⊗ₜ p b) * y) = b * σ y) ∧ (∀ b₀ : B₀, σ (1 ⊗ₜ b₀) = 0) ∧ ∀ x ∈ I.map (algebraMap R B), ∃ y, α.KerQ y ∧ σ y = x := by
  first | exact @GlobalTheory.Obs.sig_basic | exact GlobalTheory.Obs.sig_basic | (intros; apply GlobalTheory.Obs.sig_basic <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.augmentation_sigma_map_injective_of_flat : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) [Module.Flat R B] (σ : R₁ ⊗[R₀] B₀ →+ B), α.IsSig p σ → ∀ y, α.KerQ y → σ y = 0 → y = 0 := by
  first | exact @GlobalTheory.Obs.sig_inj_of_flat | exact GlobalTheory.Obs.sig_inj_of_flat | (intros; apply GlobalTheory.Obs.sig_inj_of_flat <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.augmentation_sigma_map_natural : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) (ρ : B →ₐ[R] B') (φ : B₀ →ₐ[R₀] B₀'), (∀ b, p' (ρ b) = φ (p b)) → ∀ (σ : R₁ ⊗[R₀] B₀ →+ B) (σ' : R₁ ⊗[R₀] B₀' →+ B'), α.IsSig p σ → α.IsSig p' σ' → (∀ y, ρ (σ y) = σ' (extHom R₁ φ y)) ∧ ∀ y, α.KerQ y → α.KerQ (extHom R₁ φ y) := by
  first | exact @GlobalTheory.Obs.sig_natural | exact GlobalTheory.Obs.sig_natural | (intros; apply GlobalTheory.Obs.sig_natural <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_squareZeroAugmentedAlgebra : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I), ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R₀ R₁), Nonempty (Aug I π R₁) := by
  first | exact @GlobalTheory.Obs.exists_aug | exact GlobalTheory.Obs.exists_aug | (intros; apply GlobalTheory.Obs.exists_aug <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_augmentation_tensor_sigma_map : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)), ∃ σ : R₁ ⊗[R₀] B₀ →+ B, α.IsSig p σ := by
  first | exact @GlobalTheory.Obs.exists_isSig | exact GlobalTheory.Obs.exists_isSig | (intros; apply GlobalTheory.Obs.exists_isSig <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_natural_chart_lifts_of_morphism : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ Z₀ X Z : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (t₀ : Z₀ ⟶ Sp R₀) (s : X ⟶ Sp R) (t : Z ⟶ Sp R) (i : X₀ ⟶ X) (k : Z₀ ⟶ Z) (hi : IsPullback i s₀ s (spMap π)) (hkk : IsPullback k t₀ t (spMap π)) (S : Sys I π s₀) (S' : Sys I π t₀) (P : S.Presents s i) (P' : S'.Presents t k) (f₀ : Z₀ ⟶ X₀) (h : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (f : Z ⟶ X), f ≫ s = t → k ≫ f = f₀ ≫ i → ∃ (l : ∀ T : (Pair f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj T) →ₐ[R] (pairPre S' f₀).B T), (ofSys S).IsLift (pairPre S' f₀) (pairPull h) l ∧ (ofSys S).IsNat (pairPre S' f₀) (pairPull h) l := by
  first | exact @GlobalTheory.Obs.exists_chart_lifts | exact GlobalTheory.Obs.exists_chart_lifts | (intros; apply GlobalTheory.Obs.exists_chart_lifts <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.nonempty_squareZeroSmoothLiftSystem_of_isFun : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (L : Pre I π (OAff s₀)), L.IsFun → Nonempty (Sys I π s₀) := by
  first | exact @GlobalTheory.Obs.nonempty_sys_of_isFun | exact GlobalTheory.Obs.nonempty_sys_of_isFun | (intros; apply GlobalTheory.Obs.nonempty_sys_of_isFun <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.ProdCoh

theorem cpull_bijective_of_isIso {R : Type} [CommRing R] {K L : Cx R} (c : K ⟶ L) [IsIso c] (I : Cx R) (n : ℤ) :
    Function.Bijective (cpull c I n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨cpull (inv c) I n, fun x => ?_, fun x => ?_⟩
  · rw [BiprodCls.cpull_cpull, IsIso.inv_hom_id, BiprodCls.cpull_id]
  · rw [BiprodCls.cpull_cpull, IsIso.hom_inv_id, BiprodCls.cpull_id]

theorem bij_of_eq {α β : Sort*} {f g : α → β} (h : ∀ x, f x = g x) (hg : Function.Bijective g) :
    Function.Bijective f := by
  rw [show f = g from funext h]; exact hg

theorem ht_prod_bijective : ∀ (q : ℕ) (A B : Type) [CommRing A] [CommRing B] (n i : ℤ),
    Function.Bijective (fun x : Ht q (sp (A × B)) n i =>
      (pull _ (spMap (RingHom.fst A B)) _ _ x, pull _ (spMap (RingHom.snd A B)) _ _ x)) := by
  intro q A B _ _ n i
  have h2 := GlobalTheory.T.freeEtaleSheaf_biprodDesc_isIso_of_res_bijective (ZMod q) _ _ (GlobalTheory.T.etaleSheafSections_specProd_bijective (ZMod q) A B)
  have h3 := GlobalTheory.T.etaleChains_disc_biprod_desc_isIso (ZMod q) _ _ h2
  have hc := @cpull_bijective_of_isIso _ _ _ _ _ h3 (res (ZMod q) (tw q i)) n
  have := (cpull_biprod_bijective (ZMod q) _ _ (res (ZMod q) (tw q i)) n).comp hc
  refine bij_of_eq (fun x => ?_) this
  dsimp only [Function.comp]
  erw [BiprodCls.cpull_cpull, BiprodCls.cpull_cpull, biprod.inl_desc, biprod.inr_desc]
  rfl

end GlobalTheory.EtC.ProdCoh
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.cupProduct_discreteSpace_fibre_eq_pairing : ∀ (q N : ℕ) (F : PSh) {n m i₁ i₂ : ℤ} (α : Cocycle ((chains (ZMod q)).obj (disc.obj F)) (res (ZMod q) (tw q i₁)) n) (z : Cocycle ((chains (ZMod q)).obj (fibQ q N)) (res (ZMod q) (tw q i₂)) m), (∀ (p : ℕ), 0 < p → ∀ (s : ℤ) (h : -(p : ℤ) + n = s), α.1.v (-(p : ℤ)) s h = 0) → ∃ γ : Cocycle ((chains (ZMod q)).obj (disc.obj F ⨯ fibQ q N)) (res (ZMod q) (tw q (i₁ + i₂))) (n + m), CohomologyClass.mk γ = cup q (pull _ (prod.fst : disc.obj F ⨯ fibQ q N ⟶ _) _ _ (CohomologyClass.mk α)) (pull _ (prod.snd : disc.obj F ⨯ fibQ q N ⟶ _) _ _ (CohomologyClass.mk z)) ∧ ∀ (k : ℕ) (s : ℤ) (hs : -(k : ℤ) + (n + m) = s) (V : Scheme.{0}) (w : Sx (disc.obj F ⨯ fibQ q N) k V), _root_.GlobalTheory.EtC.ev (R := ZMod q) γ.1 k s hs V w = (twPair q i₁ i₂).mul V n (-(k : ℤ) + m) s (by omega) (_root_.GlobalTheory.EtC.ev (R := ZMod q) α.1 0 n (by simp) V (show Sx (disc.obj F) 0 V from Sx.map (p := k) (prod.fst : disc.obj F ⨯ fibQ q N ⟶ _) w)) (_root_.GlobalTheory.EtC.ev (R := ZMod q) z.1 k (-(k : ℤ) + m) rfl V (Sx.map prod.snd w)) := by
  first | (exact @GlobalTheory.EtC.disc_cup_fibre) | (exact GlobalTheory.EtC.disc_cup_fibre) | (intros; apply GlobalTheory.EtC.disc_cup_fibre  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC
open CupSpec

variable {R : Type} [CommRing R]

section Build
variable (q N : ℕ) (I : Cx R) (n : ℤ) {B : Shv R}
  (χ : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ V : Scheme.{0}, Sx (fibQ q N) p V → Sec B V →ₗ[ULift.{1} R] Sec (I.X s) V)
  (hχ : ∀ p s h (V W : Scheme.{0}) (w : W ⟶ V) (x : Sx (fibQ q N) p V) (b : Sec B V),
      Sec.res w (χ p s h V x b) = χ p s h W (x.res w) (Sec.res w b))
include hχ in
theorem buildC_exists (U : Scheme.{0}) (b : Sec B U) :
    ∃ α : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n, ∀ p s h W y,
      _root_.GlobalTheory.EtC.ev (R := R) α p s h W y =
        χ p s h W (y.map prod.snd) (Sec.res (show W ⟶ U from y.map prod.fst) b) := by
  let E : Spc := sch.obj U ⨯ fibQ q N
  let a (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (W : Scheme.{0}) (y : Sx E p W) :=
    χ p s h W (y.map prod.snd) (Sec.res (show W ⟶ U from y.map prod.fst) b)
  have ha (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (V W : Scheme.{0})
      (g : V ⟶ W) (y : Sx E p W) : Sec.res g (a p s h W y) = a p s h V (y.res g) := by
    dsimp only [a]
    erw [hχ, secRes_res, sxMap_res, sxMap_res]
    rfl
  have components (i j : ℤ) (hij : i + n = j) :
      ∃ φ : ((chains R).obj E).X i ⟶ I.X j, ∀ (p : ℕ) (hp : i = -(p : ℤ)) W y,
        Sec.map ((chainsXIso R E p).inv ≫ eqToHom (congrArg ((chains R).obj E).X hp.symm) ≫ φ)
          (freeGen R _ W y) = a p j (hp ▸ hij) W y := by
    by_cases hi : i ≤ 0
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = -(k : ℤ) := ⟨(-i).toNat, by omega⟩
      obtain ⟨φ, hφ⟩ := free_exists (R := R) _ _ (a k j hij) (ha k j hij)
      refine ⟨(chainsXIso R E k).hom ≫ φ, fun p hp W y => ?_⟩
      obtain rfl : k = p := by omega
      rw [eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]
      exact hφ W y
    · exact ⟨0, fun p hp => by omega⟩
  choose φ hφ using components
  refine ⟨Cochain.mk φ, fun p s h W y => ?_⟩
  have he := hφ _ _ h p rfl W y
  rw [eqToHom_refl, Category.id_comp] at he
  exact he

def cochainOfSection (U : Scheme.{0}) (b : Sec B U) : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n :=
  (buildC_exists q N I n χ hχ U b).choose

theorem buildC_ev (U : Scheme.{0}) (b : Sec B U) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (W : Scheme.{0})
    (y : Sx (sch.obj U ⨯ fibQ q N) p W) :
    _root_.GlobalTheory.EtC.ev (R := R) (cochainOfSection q N I n χ hχ U b) p s h W y =
      χ p s h W (y.map prod.snd) (Sec.res (show W ⟶ U from y.map prod.fst) b) :=
  (buildC_exists q N I n χ hχ U b).choose_spec p s h W y

include χ hχ in
def buildMor : B.obj ⟶ cotPre R q N I n := by
  have evExt {E : Spc} (α β : Cochain ((chains R).obj E) I n)
      (he : ∀ p s h W y, ev (R := R) α p s h W y = ev (R := R) β p s h W y) : α = β := by
    ext i s h : 1
    by_cases hi : i ≤ 0
    · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
      rw [← cancel_epi (chainsXIso R E p).inv]
      exact free_ext _ _ (fun W y => he p s h W y)
    · exact (isZero_chains E i (by omega)).eq_of_src _ _
  have evAdd {E : Spc} (α β : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
      (h : -(p : ℤ) + n = s) (W : Scheme.{0}) (y : Sx E p W) :
      ev (R := R) (α + β) p s h W y = ev (R := R) α p s h W y + ev (R := R) β p s h W y := by
    simp [ev, Cochain.add_v]
  have evSmul {E : Spc} (r : ULift.{1} R) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
      (h : -(p : ℤ) + n = s) (W : Scheme.{0}) (y : Sx E p W) :
      ev (R := R) (r • α) p s h W y = r • ev (R := R) α p s h W y := by
    unfold ev
    rw [Cochain.smul_v, Linear.comp_smul]
    rfl
  refine
    { app := fun U => ModuleCat.ofHom
        { toFun := cochainOfSection q N I n χ hχ U.unop
          map_add' := fun b b' => evExt _ _ (fun p s h W y => by
            simp only [evAdd, buildC_ev, Sec.res, map_add])
          map_smul' := fun r b => evExt _ _ (fun p s h W y => by
            simp only [RingHom.id_apply, evSmul, buildC_ev, Sec.res, map_smul]) }
      naturality := ?_ }
  intro U U' g
  have evPull {E E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
      (h : -(p : ℤ) + n = s) (W : Scheme.{0}) (y : Sx E' p W) :
      ev (R := R) ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h W y =
        ev (R := R) α p s h W (y.map f) := by
    unfold ev
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, chains_map, Category.assoc]
    change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h) (Sec.map ((free R).map _) (freeGen R _ W y)) = _
    rw [freeGen_map]
    rfl
  ext b : 2
  refine evExt _ _ (fun p s h W y => ?_)
  change ev (R := R) (cochainOfSection q N I n χ hχ U'.unop (Sec.res g.unop b)) p s h W y =
    ev (R := R) (((cotPre R q N I n).map g.unop.op).hom (cochainOfSection q N I n χ hχ U.unop b)) p s h W y
  have e2 := evPull (prod.map (sch.map g.unop) (𝟙 (fibQ q N)))
    (cochainOfSection q N I n χ hχ U.unop b) p s h W y
  refine Eq.trans ?_ e2.symm
  let f := prod.map (sch.map g.unop) (𝟙 (fibQ q N))
  have hsnd : (y.map f).map prod.snd = y.map prod.snd := by
    rw [← sxMap_comp, prod.map_snd, Category.comp_id]
  have hfst : (show W ⟶ U.unop from (y.map f).map prod.fst) =
      (show W ⟶ U'.unop from y.map prod.fst) ≫ g.unop := by
    change (y.map f).map prod.fst = schSx ((show W ⟶ U'.unop from y.map prod.fst) ≫ g.unop) p
    rw [← sxMap_comp, prod.map_fst, sxMap_comp]
    exact schSx_map (show W ⟶ U'.unop from y.map prod.fst) g.unop p
  erw [buildC_ev, buildC_ev, secRes_res, hsnd, hfst]

end Build

theorem injective_cotSheaf (q N : ℕ) (I : Cx R) (hI : ∀ m, Injective (I.X m)) (n : ℤ)
    (hS : Presheaf.IsSheaf Scheme.etaleTopology.{0} (cotPre R q N I n)) :
    Injective (⟨cotPre R q N I n, hS⟩ : Shv R) := by
  constructor
  intro A B g f hf
  let eval {E : Spc} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (V : Scheme.{0}) (x : Sx E p V) :
      Cochain ((chains R).obj E) I n →ₗ[ULift.{1} R] Sec (I.X s) V :=
    { toFun := fun α => ev (R := R) α p s h V x
      map_add' := fun α β => by simp [ev, Cochain.add_v]
      map_smul' := fun r α => by
        unfold ev
        rw [Cochain.smul_v, Linear.comp_smul]
        rfl }
  have evRes {E : Spc} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s)
      {V W : Scheme.{0}} (w : W ⟶ V) (x : Sx E p V) :
      Sec.res w (ev (R := R) α p s h V x) = ev (R := R) α p s h W (x.res w) := by
    change Sec.res w (Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h) (freeGen R _ V x)) = _
    rw [map_res, freeGen_res]
    rfl
  have evPull {E E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
      (h : -(p : ℤ) + n = s) (W : Scheme.{0}) (y : Sx E' p W) :
      ev (R := R) ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h W y =
        ev (R := R) α p s h W (y.map f) := by
    unfold ev
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, chains_map, Category.assoc]
    change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h) (Sec.map ((free R).map _) (freeGen R _ W y)) = _
    rw [freeGen_map]
    rfl
  let ψ : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ V : Scheme.{0}, Sx (fibQ q N) p V → Sec A V →ₗ[ULift.{1} R] Sec (I.X s) V :=
    fun p s h V x => (eval p s h V (sxPair (schSx (𝟙 V) p) x)).comp (g.hom.app (op V)).hom
  have hψ : ∀ p s h (V W : Scheme.{0}) (w : W ⟶ V) (x : Sx (fibQ q N) p V) (a : Sec A V),
      Sec.res w (ψ p s h V x a) = ψ p s h W (x.res w) (Sec.res w a) := by
    intro p s h V W w x a
    have hn : (g.hom.app (op W)).hom (Sec.res w a) = ((cotPre R q N I n).map w.op).hom ((g.hom.app (op V)).hom a) :=
      ConcreteCategory.congr_hom (g.hom.naturality w.op) a
    refine (evRes (E := sch.obj V ⨯ fibQ q N)
      ((g.hom.app (op V)).hom a) p s h w _).trans ?_
    refine Eq.trans ?_ (congrArg (fun c => _root_.GlobalTheory.EtC.ev (R := R) (E := sch.obj W ⨯ fibQ q N) (I := I) c p s h W
      (sxPair (schSx (𝟙 W) p) (x.res w))) hn).symm
    have e2 := evPull (prod.map (sch.map w) (𝟙 (fibQ q N))) ((g.hom.app (op V)).hom a) p s h W
      (sxPair (schSx (𝟙 W) p) (x.res w))
    refine Eq.trans ?_ e2.symm
    rw [sxPair_res, sxPair_map]
    congr 2
  have hχ := fun p s h => GlobalTheory.T.natural_sections_linear_extension R ((fibQ q N).obj (op (SimplexCategory.mk p))) (I.X s) (hI s) f hf (ψ p s h) (hψ p s h)
  choose χ hχn hχf using hχ
  refine ⟨⟨buildMor q N I n χ hχn⟩, ?_⟩
  ext U : 4
  refine LinearMap.ext fun a => ?_
  change cochainOfSection q N I n χ hχn U.unop (Sec.map f a) = (g.hom.app U).hom a
  have evExt {E : Spc} (α β : Cochain ((chains R).obj E) I n)
      (he : ∀ p s h W y, ev (R := R) α p s h W y = ev (R := R) β p s h W y) : α = β := by
    ext i s h : 1
    by_cases hi : i ≤ 0
    · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
      rw [← cancel_epi (chainsXIso R E p).inv]
      exact free_ext _ _ (fun W y => he p s h W y)
    · exact (isZero_chains E i (by omega)).eq_of_src _ _
  refine evExt _ _ (fun p s h W y => ?_)
  refine (buildC_ev q N I n χ hχn U.unop (Sec.map f a) p s h W y).trans ?_
  refine (congrArg (χ p s h W (y.map prod.snd))
    (_root_.GlobalTheory.EtC.CupSpec.map_res f (show W ⟶ U.unop from y.map prod.fst) a)).trans ?_
  refine (hχf p s h W _ _).trans ?_
  have hn := ConcreteCategory.congr_hom (g.hom.naturality (show W ⟶ U.unop from y.map prod.fst).op) a
  refine (congrArg (fun c => _root_.GlobalTheory.EtC.ev (R := R) (E := sch.obj W ⨯ fibQ q N) (I := I) c p s h W
    (sxPair (schSx (𝟙 W) p) (y.map prod.snd))) hn).trans ?_
  refine (evPull (prod.map (sch.map (show W ⟶ U.unop from y.map prod.fst)) (𝟙 (fibQ q N)))
    ((g.hom.app U).hom a) p s h W _).trans ?_
  congr 1
  rw [sxPair_map]
  exact sxPair_eta y

theorem Jcx_X_injective : ∀ (R : Type) [CommRing R] (q N : ℕ) (I : Cx R), (∀ n, CategoryTheory.Injective (I.X n)) →
    ∀ n, CategoryTheory.Injective ((Jcx R q N I).X n) := by
  intro R _ q N I hI n
  have hS := GlobalTheory.T.isSheaf_projBundleCochainPresheaf_etale R q N I n
  exact Injective.of_iso (sheafificationIso (⟨cotPre R q N I n, hS⟩ : Shv R)) (injective_cotSheaf q N I hI n hS)

end GlobalTheory.EtC

end
end
