module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle043
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle050
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle040
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle053
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle062
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle071
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle131
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle066
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle002
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.LinearModelFourier

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def flat (n r : ℕ) : Matrix (Fin n) (Fin r) k ≃ₜ (Fin n × Fin r → k) where
  toFun z p := z p.1 p.2
  invFun y := Matrix.of (Function.curry y)
  left_inv z := rfl
  right_inv y := rfl
  continuous_toFun := continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)
  continuous_invFun := continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)

def flatT (n r : ℕ) : Matrix (Fin r) (Fin n) k ≃ₜ (Fin n × Fin r → k) where
  toFun x p := x p.2 p.1
  invFun y := Matrix.of fun j i => y (i, j)
  left_inv x := rfl
  right_inv y := rfl
  continuous_toFun := continuous_pi fun p => (continuous_apply p.1).comp (continuous_apply p.2)
  continuous_invFun := continuous_pi fun j => continuous_pi fun i => continuous_apply (i, j)

theorem trace_mul_eq_dotProduct {n r : ℕ} (x : Matrix (Fin r) (Fin n) k) (y : Matrix (Fin n) (Fin r) k) :
    trace (x * y) = flat n r y ⬝ᵥ flatT n r x := by
  simp only [trace, diag, Matrix.mul_apply, dotProduct, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  show x j i * y i j = y i j * x j i
  ring

theorem comp_mem_SB {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : Y ≃ₜ X) {f : X → ℂ}
    (hf : f ∈ GlobalTheory.SplitWeil.SB X) : (f ∘ e) ∈ GlobalTheory.SplitWeil.SB Y :=
  ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩

variable [MeasurableSpace k]

def fou (ψ : AddChar k Circle) (ν : Measure k) (n r : ℕ) (Φ : Matrix (Fin n) (Fin r) k → ℂ)
    (x : Matrix (Fin r) (Fin n) k) : ℂ :=
  ∫ y, Φ y * (ψ (trace (x * y)) : ℂ) ∂(volM ν (Fin n) (Fin r))

variable [BorelSpace k] {ψ : AddChar k Circle} (ν : Measure k) [ν.IsAddHaarMeasure] {n r : ℕ}

theorem fou_eq_pi (Φ : Matrix (Fin n) (Fin r) k → ℂ) (x : Matrix (Fin r) (Fin n) k) :
    fou ψ ν n r Φ x = ∫ z, (Φ ∘ (flat n r).symm) z * (ψ (z ⬝ᵥ flatT n r x) : ℂ) ∂(Measure.pi fun _ => ν) := by
  rw [fou, integral_volM_eq_pi]
  congr 1
  funext z
  rw [trace_mul_eq_dotProduct]
  rfl

theorem integrable_fou (hψ : Continuous ψ) {f : Matrix (Fin n) (Fin r) k → ℂ}
    (hf : f ∈ SB (Matrix (Fin n) (Fin r) k)) (x : Matrix (Fin r) (Fin n) k) :
    Integrable (fun y => f y * (ψ (trace (x * y)) : ℂ)) (volM ν (Fin n) (Fin r)) := by
  haveI := secondCountable k
  letI : MeasurableSpace (Matrix (Fin n) (Fin r) k) := GlobalTheory.SplitWeil.matrixMeasurableSpace
  haveI : BorelSpace (Matrix (Fin n) (Fin r) k) := inferInstanceAs (BorelSpace (Fin n → Fin r → k))
  haveI : (volM ν (Fin n) (Fin r)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : IsFiniteMeasureOnCompacts (volM ν (Fin n) (Fin r)) := inferInstance
  have hc : Continuous fun y : Matrix (Fin n) (Fin r) k => f y * (ψ (trace (x * y)) : ℂ) :=
    hf.1.continuous.mul (continuous_subtype_val.comp
      (hψ.comp ((continuous_const.matrix_mul continuous_id).matrix_trace)))
  exact hc.integrable_of_hasCompactSupport (μ := volM ν (Fin n) (Fin r)) hf.2.mul_right

theorem fou_mem (hψ : Continuous ψ) (h1 : ψ ≠ 1) {f : Matrix (Fin n) (Fin r) k → ℂ}
    (hf : f ∈ SB (Matrix (Fin n) (Fin r) k)) : fou ψ ν n r f ∈ SB (Matrix (Fin r) (Fin n) k) := by
  haveI := secondCountable k
  obtain ⟨c, hc⟩ := (conductor_exists k).1 ψ hψ h1
  have h2 := FourierPi.fourier_mem_SB (Measure.pi fun _ : Fin n × Fin r => ν) hc
    (comp_mem_SB (flat n r).symm hf)
  have h3 : fou ψ ν n r f = (fun y => ∫ z, (f ∘ (flat n r).symm) z * (ψ (z ⬝ᵥ y) : ℂ)
      ∂(Measure.pi fun _ => ν)) ∘ flatT n r := funext fun x => fou_eq_pi ν f x
  rw [h3]
  exact comp_mem_SB _ h2

theorem nabs_det_inv {m : ℕ} (g : GL (Fin m) k) :
    nabs k (Matrix.GeneralLinearGroup.det g⁻¹) = (nabs k (Matrix.GeneralLinearGroup.det g))⁻¹ := by
  simp [nabs, map_inv]

theorem fou_om (μ : kˣ →* ℂˣ) (gk : GL (Fin n) k) (hk : GL (Fin r) k) (Φ : Matrix (Fin n) (Fin r) k → ℂ) :
    fou ψ ν n r (om μ hk gk Φ) = om μ⁻¹ gk hk (fou ψ ν n r Φ) := by
  funext x
  set F : Matrix (Fin n) (Fin r) k → ℂ :=
    fun z => Φ z * (ψ (trace (((hk⁻¹ : GL (Fin r) k).val * x * gk.val) * z)) : ℂ) with hF
  have key := integral_comp_mul_mul_volM ν hk gk⁻¹ F
  have htr : ∀ y : Matrix (Fin n) (Fin r) k,
      trace ((hk⁻¹ : GL (Fin r) k).val * x * gk.val * ((gk⁻¹ : GL (Fin n) k).val * y * hk.val)) =
        trace (x * y) := by
    intro y
    have e : (hk⁻¹ : GL (Fin r) k).val * x * gk.val * ((gk⁻¹ : GL (Fin n) k).val * y * hk.val) =
        (hk⁻¹ : GL (Fin r) k).val * (x * y * hk.val) := by
      calc _ = (hk⁻¹ : GL (Fin r) k).val * (x * (gk.val * (gk⁻¹ : GL (Fin n) k).val) * y * hk.val) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [Units.mul_inv, Matrix.mul_one]
    rw [e, trace_mul_comm]
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  set A : ℂ := (μ (Matrix.GeneralLinearGroup.det hk) : ℂ) * ((μ (Matrix.GeneralLinearGroup.det gk))⁻¹ : ℂˣ) *
    ((nabs k (Matrix.GeneralLinearGroup.det hk) ^ ((Fintype.card (Fin n) : ℝ) / 2) : ℝ) : ℂ) *
    ((nabs k (Matrix.GeneralLinearGroup.det gk) ^ (-(Fintype.card (Fin r) : ℝ) / 2) : ℝ) : ℂ) with hA
  have lhs : fou ψ ν n r (om μ hk gk Φ) x =
      A * ∫ y, F ((gk⁻¹ : GL (Fin n) k).val * y * hk.val) ∂(volM ν (Fin n) (Fin r)) := by
    rw [fou, ← integral_const_mul]
    congr 1
    funext y
    simp only [om, hA, hF, htr]
    ring
  have hFint : ∫ z, F z ∂(volM ν (Fin n) (Fin r)) =
      fou ψ ν n r Φ ((hk⁻¹ : GL (Fin r) k).val * x * gk.val) := rfl
  rw [lhs, key, hFint, nabs_det_inv]
  simp only [om, hA, MonoidHom.inv_apply, inv_inv, Complex.real_smul, Fintype.card_fin]
  set a := nabs k (Matrix.GeneralLinearGroup.det gk) with ha
  set b := nabs k (Matrix.GeneralLinearGroup.det hk) with hb
  have ha0 : 0 < a := nabs_pos' _
  have hb0 : 0 < b := nabs_pos' _
  have h1 : ((b ^ ((n : ℝ) / 2) : ℝ) : ℂ) * ((b ^ (-(n : ℝ)) : ℝ) : ℂ) = ((b ^ (-(n : ℝ) / 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add hb0]
    ring_nf
  have h2 : ((a ^ (-(r : ℝ) / 2) : ℝ) : ℂ) * ((a⁻¹ ^ (-(r : ℝ)) : ℝ) : ℂ) = ((a ^ ((r : ℝ) / 2) : ℝ) : ℂ) := by
    rw [Real.inv_rpow ha0.le, ← Real.rpow_neg ha0.le, neg_neg, ← Complex.ofReal_mul, ← Real.rpow_add ha0]
    ring_nf
  rw [Complex.ofReal_mul]
  linear_combination
    ((μ (Matrix.GeneralLinearGroup.det hk) : ℂ) * ((μ (Matrix.GeneralLinearGroup.det gk))⁻¹ : ℂˣ) *
      fou ψ ν n r Φ ((hk⁻¹ : GL (Fin r) k).val * x * gk.val)) *
    (((a ^ (-(r : ℝ) / 2) : ℝ) : ℂ) * ((a⁻¹ ^ (-(r : ℝ)) : ℝ) : ℂ) * h1 + ((b ^ (-(n : ℝ) / 2) : ℝ) : ℂ) * h2)

def fouL (hψ : Continuous ψ) (h1 : ψ ≠ 1) :
    SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] SB (Matrix (Fin r) (Fin n) k) where
  toFun Φ := ⟨fou ψ ν n r Φ.1, fou_mem ν hψ h1 Φ.2⟩
  map_add' Φ Ψ := by
    apply Subtype.ext
    funext x
    show fou ψ ν n r (Φ.1 + Ψ.1) x = fou ψ ν n r Φ.1 x + fou ψ ν n r Ψ.1 x
    simp only [fou, Pi.add_apply, add_mul]
    exact integral_add (integrable_fou ν hψ Φ.2 x) (integrable_fou ν hψ Ψ.2 x)
  map_smul' c Φ := by
    apply Subtype.ext
    funext x
    show fou ψ ν n r (c • Φ.1) x = c * fou ψ ν n r Φ.1 x
    simp only [fou, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul _ _

theorem fouL_surjective (hψ : Continuous ψ) (h1 : ψ ≠ 1) (hν : IsSelfDual ψ ν) :
    Function.Surjective (fouL (n := n) (r := r) ν hψ h1) := by
  intro G
  obtain ⟨Φ₀, hΦ₀⟩ := (FourierSurj.hat_surjective k (Fin n × Fin r) ψ hψ h1 ν hν).2
    ⟨_, comp_mem_SB (flatT n r).symm G.2⟩
  refine ⟨⟨Φ₀.1 ∘ flat n r, comp_mem_SB _ Φ₀.2⟩, Subtype.ext (funext fun x => ?_)⟩
  show fou ψ ν n r (Φ₀.1 ∘ flat n r) x = G.1 x
  have h2 := congrFun hΦ₀ (flatT n r x)
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat, Function.comp_apply, Homeomorph.symm_apply_apply] at h2
  rw [fou_eq_pi, ← h2]
  congr 1
  funext z
  simp only [Function.comp_apply, Homeomorph.apply_symm_apply, dotProduct_comm]

end GlobalTheory.LinearModelFourier

theorem GlobalTheory.linearModel_fourier : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n r : ℕ), ∃ τ : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] GlobalTheory.SplitWeil.SB (Matrix (Fin r) (Fin n) k), Function.Surjective τ ∧ ∀ (μ : kˣ →* ℂˣ) (gk : GL (Fin n) k) (hk : GL (Fin r) k) (Φ Φ' : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) k)), Φ'.1 = GlobalTheory.SplitWeil.om μ hk gk Φ.1 → (τ Φ').1 = GlobalTheory.SplitWeil.om μ⁻¹ gk hk (τ Φ).1 := by
  intro k _ _ _ _ n r
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  obtain ⟨ψ, hψ, h1, -⟩ := (conductor_exists k).2.1
  obtain ⟨ν, hν⟩ := (selfDual_measure k ψ hψ h1).1
  haveI := hν.1
  refine ⟨GlobalTheory.LinearModelFourier.fouL ν hψ h1, GlobalTheory.LinearModelFourier.fouL_surjective ν hψ h1 hν,
    fun μ gk hk Φ Φ' hΦ => ?_⟩
  show GlobalTheory.LinearModelFourier.fou ψ ν n r Φ'.1 = om μ⁻¹ gk hk (GlobalTheory.LinearModelFourier.fou ψ ν n r Φ.1)
  rw [hΦ]
  exact GlobalTheory.LinearModelFourier.fou_om ν μ gk hk Φ.1
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.ParIndSubquot

theorem parInd_isSubquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ (Levi k m) W) (ρ' : Representation ℂ (Levi k m) W'), IsSmooth ρ' → IsSubquotient ρ ρ' → IsSubquotient (parInd e ρ) (parInd e ρ') := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e W W' _ _ _ _ ρ ρ' hρ' h
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨-, -, -, -, -, hcont, hP, -, hPK⟩ := GlobalTheory.SmGL.LeviInt.levi_integral_facts k α n m e
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  let ι : S.toRepresentation.IntertwiningMap ρ' :=
    { toLinearMap := S.toSubmodule.subtype, isIntertwining' := fun _ => rfl }
  have hι : Function.Injective ι := Subtype.val_injective
  have hS : IsSmooth S.toRepresentation := (IsSubquotient.of_injective ι hι).isSmooth hρ'
  have hinj : Function.Injective (parIndMap e ι) := by
    intro φ ψ hφψ
    refine Subtype.ext (Subtype.ext (funext fun g => hι ?_))
    exact congrFun (congrArg (fun χ : IndSp e ρ' => χ.1.1) hφψ) g
  let σ₀ : Representation ℂ (parab k e) S.toSubmodule := (_root_.GlobalTheory.SmGL.twist S.toRepresentation (deltaHalf k m)).comp (leviProj k e)
  let z : Representation.IntertwiningMap σ₀ σ₀ :=
    { toLinearMap := 0, isIntertwining' := fun _ => by ext; simp }
  have hsurj : Function.Surjective (parIndMap e f) := by
    refine (GlobalTheory.SmGL.IndCoinv.smInd_coinvariants (GL n k) (parab k e) (KO k n) hP SplitFlip.isCompact_KO
      hPK (GlobalTheory.SmGL.exists_open_normalised_subgroup_subset k n) _ _ _ _
      (isSmooth_comp (isSmooth_twist hS (isSmoothChar_deltaHalf k)) _ hcont)
      (compMap (twistMap f _) _) Unit (fun _ => z) hf ?_).1
    intro x _
    refine Submodule.subset_span ⟨(), -x, ?_⟩
    show x = (0 : _) - -x
    simp
  exact (IsSubquotient.of_surjective (parIndMap e f) hsurj).trans (IsSubquotient.of_injective (parIndMap e ι) hinj)

end GlobalTheory.ParIndSubquot
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.JacGL1


open GlobalTheory.SmGL GlobalTheory.PRep Matrix in
theorem jac_mulSingle_scalar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin d) k) V) (ω : kˣ →* ℂˣ) (s' : ℕ) (b : Fin s' → ℕ) (f : (Σ j, Fin (b j)) ≃ Fin d) (j : Fin s'), d = 1 → b j = 1 → GlobalTheory.SmGL.HasCentralChar σ ω → ∀ (z : kˣ) (x : GlobalTheory.PRep.Jacquet σ (GlobalTheory.SmGL.unipRad k f)), GlobalTheory.SmGL.jac f σ (Pi.mulSingle j (Matrix.GeneralLinearGroup.scalar (Fin (b j)) z)) x = (ω z : ℂ) • x := by
  intro k _ _ _ _ d V _ _ σ ω s' b f j hd hj hω z x
  have hsum : ∑ i, b i = 1 := by
    have := Fintype.card_congr f
    simpa [Fintype.card_sigma, hd] using this
  have hsplit := Finset.add_sum_erase Finset.univ b (Finset.mem_univ j)
  have ha : ∀ i, i ≠ j → IsEmpty (Fin (b i)) := fun i hi => by
    have h0 : ∑ i ∈ Finset.univ.erase j, b i = 0 := by omega
    rw [Finset.sum_eq_zero_iff.1 h0 i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩)]
    infer_instance
  have h1 : leviEmb k f (Pi.mulSingle j (GeneralLinearGroup.scalar (Fin (b j)) z)) =
      GeneralLinearGroup.scalar (Fin d) z := by
    ext i i'
    obtain ⟨⟨a, y⟩, rfl⟩ := f.surjective i
    obtain ⟨⟨a', y'⟩, rfl⟩ := f.surjective i'
    obtain rfl : a = j := by_contra fun h => (ha a h).elim y
    obtain rfl : a' = a := by_contra fun h => (ha a' h).elim y'
    rw [leviEmb_apply_same]
    simp [GeneralLinearGroup.scalar, diagonal_apply]
  have h2 : modExp (fun i => Fin (b i)) j = 0 := by
    unfold modExp
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, sub_zero]
    · intro a hb
      have := ha a (Finset.mem_filter.1 hb).2.ne
      exact Nat.cast_eq_zero.2 Fintype.card_eq_zero
    · intro a hb
      have := ha a (Finset.mem_filter.1 hb).2.ne'
      exact Nat.cast_eq_zero.2 Fintype.card_eq_zero
  have h3 : deltaHalf k (fun i => Fin (b i))
      (Pi.mulSingle j (GeneralLinearGroup.scalar (Fin (b j)) z)) = 1 := by
    rw [deltaHalf_apply]
    refine Finset.prod_eq_one fun a _ => ?_
    by_cases hb : a = j
    · subst hb
      simp [h2]
    · rw [Pi.mulSingle_eq_of_ne hb, map_one, map_one]
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine (jac_mk f σ _ v).trans ?_
  rw [h3, h1, hω z v, inv_one, Units.val_one, one_smul]
  exact map_smul (Submodule.mkQ _) _ _

end GlobalTheory.JacGL1
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil


namespace GlobalTheory.ParIndExact

theorem parInd_exact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (X Y : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (ξ : Representation ℂ (Levi k m) X) (η : Representation ℂ (Levi k m) Y) (i : ξ.IntertwiningMap η), Function.Injective i → Function.Injective (parIndMap e i) ∧ ∀ (Z : Type) [AddCommGroup Z] [Module ℂ Z] (ζ : Representation ℂ (Levi k m) Z) (q : η.IntertwiningMap ζ), (∀ y, q y = 0 → ∃ x, i x = y) → ∀ φ, parIndMap e q φ = 0 → ∃ ψ, parIndMap e i ψ = φ := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e X Y _ _ _ _ ξ η i hi
  have hval : ∀ (φ : IndSp e ξ) (g : GL n k), (parIndMap e i φ).1.1 g = i (φ.1.1 g) := fun _ _ => rfl
  refine ⟨?_, ?_⟩
  · intro φ ψ hφψ
    refine Subtype.ext (Subtype.ext (funext fun g => hi ?_))
    rw [← hval, ← hval, hφψ]
  · intro Z _ _ ζ q hex φ hφ
    have h0 : ∀ g, q (φ.1.1 g) = 0 := fun g =>
      congrFun (congrArg (fun χ : IndSp e ζ => χ.1.1) hφ) g
    choose x hx using fun g => hex _ (h0 g)
    have hlaw : x ∈ indSpace (parab k e) ((_root_.GlobalTheory.SmGL.twist ξ (deltaHalf k m)).comp (leviProj k e)) := by
      intro p g
      apply hi
      rw [hx]
      have h1 := parInd_law e η φ p g
      rw [h1, ← hx g]
      show _ = i ((deltaHalf k m (leviProj k e p) : ℂ) • ξ (leviProj k e p) (x g))
      rw [map_smul, i.isIntertwining]
    let x' : indSpace (parab k e) ((_root_.GlobalTheory.SmGL.twist ξ (deltaHalf k m)).comp (leviProj k e)) := ⟨x, hlaw⟩
    have hset : {g : GL n k | ind (parab k e) ((_root_.GlobalTheory.SmGL.twist ξ (deltaHalf k m)).comp (leviProj k e)) g x' = x'} =
        {g : GL n k | ind (parab k e) ((_root_.GlobalTheory.SmGL.twist η (deltaHalf k m)).comp (leviProj k e)) g φ.1 = φ.1} := by
      ext g
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h
        apply Subtype.ext
        funext y
        have hy := congrFun (congrArg Subtype.val h) y
        change x (y * g) = x y at hy
        change φ.1.1 (y * g) = φ.1.1 y
        rw [← hx, ← hx, hy]
      · intro h
        apply Subtype.ext
        funext y
        have hy := congrFun (congrArg Subtype.val h) y
        change φ.1.1 (y * g) = φ.1.1 y at hy
        change x (y * g) = x y
        apply hi
        rw [hx, hx, hy]
    have hsm : x' ∈ smoothPart (ind (parab k e) ((_root_.GlobalTheory.SmGL.twist ξ (deltaHalf k m)).comp (leviProj k e))) := by
      have ho : IsOpen {g : GL n k | ind (parab k e) ((_root_.GlobalTheory.SmGL.twist ξ (deltaHalf k m)).comp (leviProj k e)) g x' = x'} := by
        rw [hset]; exact φ.2
      exact ho
    refine ⟨⟨x', hsm⟩, ?_⟩
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    rw [hval]
    exact hx g

end GlobalTheory.ParIndExact
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.GLOneChar

open GlobalTheory.SmGL

theorem equiv_detRep_of_isIrreducible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin d) k) V) (ω : kˣ →* ℂˣ), d = 1 → σ.IsIrreducible → GlobalTheory.SmGL.HasCentralChar σ ω → Nonempty (σ.Equiv (GlobalTheory.SmGL.detRep (Fin d) ω)) := by
  intro k _ _ _ _ d V _ _ σ ω hd hirr hω
  have hact : ∀ (g : GL (Fin d) k) (v : V), σ g v = (ω (Matrix.GeneralLinearGroup.det g) : ℂ) • v := by
    intro g v
    conv_lhs => rw [GlobalTheory.ProdSupport.eq_scalar_det hd g]
    exact hω _ v
  haveI : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    have : (⊥ : Subrepresentation σ) = ⊤ :=
      Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _)
    exact bot_ne_top this
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let S : Subrepresentation σ := ⟨ℂ ∙ v, fun g w hw => by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    rw [hact, smul_smul]
    exact Submodule.mem_span_singleton.2 ⟨_, rfl⟩⟩
  have hS : S = ⊤ := by
    rcases eq_bot_or_eq_top S with h | h
    · exfalso
      have : v ∈ S.toSubmodule := Submodule.mem_span_singleton_self v
      rw [h] at this
      exact hv this
    · exact h
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton ℂ V v) := by
    intro w
    have hw : w ∈ S.toSubmodule := by rw [hS]; trivial
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    exact ⟨c, rfl⟩
  have hinj : Function.Injective (LinearMap.toSpanSingleton ℂ V v) := by
    intro a b hab
    simp only [LinearMap.toSpanSingleton_apply] at hab
    exact smul_left_injective ℂ hv hab
  let e : ℂ ≃ₗ[ℂ] V := LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩
  refine ⟨(Representation.Equiv.mk e fun g => ?_).symm⟩
  ext c
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, e,
    LinearEquiv.ofBijective_apply, LinearMap.toSpanSingleton_apply, detRep, ofChar_apply,
    detChar_apply, hact, smul_smul, smul_eq_mul]
  rw [mul_one, ← LinearEquiv.map_smul, smul_eq_mul, mul_one]

end GlobalTheory.GLOneChar
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SmGL.CuspRow

theorem block_unique_of_isCuspidal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin d) k) V) (s' : ℕ) (b : Fin s' → ℕ) (f : (Σ j, Fin (b j)) ≃ Fin d) (X : Fin s' → Type) [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)] (ρ : ∀ j, Representation ℂ (GL (Fin (b j)) k) (X j)), GlobalTheory.SmGL.IsCuspidal σ → (∀ j, Nontrivial (X j)) → GlobalTheory.SmGL.IsSubquotient (GlobalTheory.SmGL.piTensor ρ) (GlobalTheory.SmGL.jac f σ) → ∀ j j', 0 < b j → 0 < b j' → j = j' := by
  intro k _ _ _ _ d V _ _ σ s' b f X _ _ ρ hσ hX hsub j j' hj hj'
  by_contra hne
  have hU : GlobalTheory.SmGL.unipRad k f ≠ ⊥ := by
    refine GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.2 ?_
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨f ⟨j, ⟨0, hj⟩⟩, f ⟨j', ⟨0, hj'⟩⟩, by rwa [GlobalTheory.SmGL.blk_apply, GlobalTheory.SmGL.blk_apply]⟩
    · exact ⟨f ⟨j', ⟨0, hj'⟩⟩, f ⟨j, ⟨0, hj⟩⟩, by rwa [GlobalTheory.SmGL.blk_apply, GlobalTheory.SmGL.blk_apply]⟩
  have hs := hσ.2 s' b f hU
  have hn := GlobalTheory.ProdSupport.nontrivial_piTensor X hX
  obtain ⟨S, g, hg⟩ := hsub
  have hS : Subsingleton S.toSubmodule := inferInstance
  exact not_subsingleton _ (Function.Surjective.subsingleton hg)

end GlobalTheory.SmGL.CuspRow
end
