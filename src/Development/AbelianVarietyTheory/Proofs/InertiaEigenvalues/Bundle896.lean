module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle567
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceInvariantFormsSeparateThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle612
public import GroundTheory.AutomorphicForms.FourierWhittaker.PartialCoeffDiagonalBlockGLEqVecCoeff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle763
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle884
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle797
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle879
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle849
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1299
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1173
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import GroundTheory.AutomorphicForms.MultiplicityOne.Equivariance
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle827
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle872
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle889
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle873
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle885
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasFDerivAtRealChartRapidKernelOperator
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle534
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle068
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

theorem _root_.GlobalTheory.T.splitPlace_invariantForms_separate_thetaFunctions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ a : AE D, IsSplitIdem D a → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x f) = 0) → f = 0 := by
  first | exact @GlobalTheory.DownLift.SplitSep.invForms_separate | exact GlobalTheory.DownLift.SplitSep.invForms_separate | (intros; apply GlobalTheory.DownLift.SplitSep.invForms_separate <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)

theorem _root_.GlobalTheory.T.partial_coeff_good_of_cuspidal : ∀ (E : Type) [Field E] [NumberField E] (k m : ℕ) (hmk : m + 1 ≤ k) (φ : GA E (k + 1) → ℂ),
    Continuous φ → (∀ γ g, φ (ratGL E (k + 1) γ * g) = φ g) →
    (∀ r, 0 < r → r ≤ k → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (k + 1) r k)) (fun x => φ (blkU x * g)) = 0) →
    Good (GlobalTheory.StdCharConductor.psi E) m (fun h => partialCoeff φ (m + 1) (blockGL (by omega : m + 1 ≤ k + 1) h)) := by
  first | (exact @GlobalTheory.PartialBlock.good_partialCoeff_blockGL) | (exact GlobalTheory.PartialBlock.good_partialCoeff_blockGL) | (intros; apply GlobalTheory.PartialBlock.good_partialCoeff_blockGL  <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

theorem _root_.GlobalTheory.T.cmPlaceOperator_preserves_type_averages_shape : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.thP_ωP → ∀ (i : Fin D.R.m) (t : T) (Sb : Finset (FinPl D)) (v : FinPl D), v ∈ Sb → ∀ (h : GA D (Wc D i)), (∀ a b, idem D (.inl v) * (Formalism.L2.Theta.mt (Wc D i) h - 1) a b = (Formalism.L2.Theta.mt (Wc D i) h - 1) a b) → ∀ (c : WO (Vc D i) (Wc D i) →₀ ℂ), (∀ y ∈ c.support, IsHalf (idem D (.inl v)) y) → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), TypeIn R i t Sb f → CleanIn R i t Sb f → LikeOff R i t Sb f → TypeIn R i t (dropPl Sb v) (comb R.ψ (Vc D i) (Wc D i) c (R.ωP i t (1, h) f)) ∧ CleanIn R i t (dropPl Sb v) (comb R.ψ (Vc D i) (Wc D i) c (R.ωP i t (1, h) f)) ∧ LikeOff R i t Sb (comb R.ψ (Vc D i) (Wc D i) c (R.ωP i t (1, h) f)) := by
  first | exact @GlobalTheory.DownLift.GenSplit.placeOp_keep | exact GlobalTheory.DownLift.GenSplit.placeOp_keep | (intros; apply GlobalTheory.DownLift.GenSplit.placeOp_keep <;> assumption)
end

section

noncomputable section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun

namespace GlobalTheory.JSW.ShiftWhit
open GlobalTheory.IwaCell
variable {k : Type} [Field k] {n : ℕ}

theorem val_tD' (ϖ : kˣ) (a : Fin n → ℤ) : (tD ϖ a).val = Matrix.diagonal fun i => ((ϖ ^ a i : kˣ) : k) :=
  GlobalTheory.SmGL.val_diagT k _

theorem conj_tD_apply (ϖ : kˣ) (c : Fin n → ℤ) (u : GL (Fin n) k) (i j : Fin n) :
    ((tD ϖ c * u * tD ϖ (-c) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      ((ϖ ^ c i : kˣ) : k) * (u : Matrix (Fin n) (Fin n) k) i j * ((ϖ ^ (-c) j : kˣ) : k) := by
  rw [Units.val_mul, Units.val_mul, val_tD', val_tD', Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem tD_eq_diagPow (ϖ : kˣ) (ν : Fin n → ℤ) (h : ∀ i, 0 ≤ ν i) :
    tD ϖ ν = GlobalTheory.JSW.diagPow ϖ (fun i => (ν i).toNat) := by
  have e : (fun i => ((ϖ ^ ν i : kˣ) : k)) = fun i => ((ϖ ^ (ν i).toNat : kˣ) : k) :=
    funext fun i => by rw [← zpow_natCast, Int.toNat_of_nonneg (h i)]
  ext i j
  rw [val_tD', e]
  rfl

theorem commute_tD_const (ϖ : kˣ) (c : ℤ) (x : GL (Fin n) k) : Commute (tD ϖ (fun _ : Fin n => c)) x := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, val_tD']
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

theorem conj_mem_unipB (ϖ : kˣ) (c : Fin n → ℤ) {u : GL (Fin n) k} (hu : u ∈ GlobalTheory.SmGL.unipB k (Fin n)) :
    tD ϖ c * u * tD ϖ (-c) ∈ GlobalTheory.SmGL.unipB k (Fin n) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB k).1 hu
  refine (GlobalTheory.SmGL.mem_unipB k).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [conj_tD_apply, h1 i j hij, mul_zero, zero_mul]
  · rw [conj_tD_apply, h2 i, mul_one, ← Units.val_mul, Pi.neg_apply, ← _root_.zpow_add, add_neg_cancel, zpow_zero, Units.val_one]

theorem superDiag_conj (ϖ : kˣ) (e : ℤ) (m : ℕ) (u : GL (Fin (m + 1)) k) :
    GlobalTheory.Whittaker.superDiag (tD ϖ (fun i : Fin (m + 1) => e * ((m : ℤ) - ((i : ℕ) : ℤ))) * u *
      tD ϖ (-(fun i : Fin (m + 1) => e * ((m : ℤ) - ((i : ℕ) : ℤ))))) =
      ((ϖ ^ e : kˣ) : k) * GlobalTheory.Whittaker.superDiag u := by
  rw [GlobalTheory.Whittaker.superDiag, GlobalTheory.Whittaker.superDiag, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : (j : ℕ) = (i : ℕ) + 1 := (Finset.mem_filter.1 hj).2
  rw [conj_tD_apply]
  have hz : (ϖ ^ (e * ((m : ℤ) - ((i : ℕ) : ℤ))) : kˣ) * ϖ ^ ((-(fun i : Fin (m + 1) => e * ((m : ℤ) - ((i : ℕ) : ℤ)))) j) = ϖ ^ e := by
    rw [← _root_.zpow_add]
    congr 1
    simp only [Pi.neg_apply, hj']
    push_cast
    ring
  rw [← hz, Units.val_mul]
  ring

end GlobalTheory.JSW.ShiftWhit

namespace GlobalTheory.JSW.ShiftWhit
open GlobalTheory.IwaCell GlobalTheory.JSW GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.MultiplicityOne GlobalTheory.PRep
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

def psiScaled (w : HeightOneSpectrum (𝓞 E)) (c : w.adicCompletion E) : AddChar (w.adicCompletion E) ℂ :=
  (psiLocChar w).compAddMonoidHom (AddMonoidHom.mulLeft c)

theorem psiScaled_apply (w : HeightOneSpectrum (𝓞 E)) (c x : w.adicCompletion E) :
    psiScaled w c x = psiLoc w (c * x) := rfl

theorem main_of_fixed (m : ℕ) (π : CuspSub E (m + 1)) (w : HeightOneSpectrum (𝓞 E))
    (α : Fin (m + 1) → ℂˣ) (hα : HasSatGL w (π.locRep w) (Finset.univ.val.map α))
    (φ : π.V) (hφ : φ ∈ fixed (π.locRep w) (KGL w (n := (m + 1))))
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifV E w (ϖ : w.adicCompletion E)) (e : ℤ)
    (hc : GlobalTheory.RamShift.CondOne w ((ϖ ^ e : (w.adicCompletion E)ˣ) : w.adicCompletion E))
    (g : GA E (m + 1)) (hg : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g = 1)
    (ν : Fin (m + 1) → ℤ) (hν : 0 ≤ ν (Fin.last m)) :
    whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ (fun i => e * ((m : ℤ) - ((i : ℕ) : ℤ)) + ν i)))) =
      GlobalTheory.RSCell.sphZ (qV E w) (fun i => (α i : ℂ)) ν *
        whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ (fun i => e * ((m : ℤ) - ((i : ℕ) : ℤ)))))) := by
  classical
  set c : Fin (m + 1) → ℤ := fun i => e * ((m : ℤ) - ((i : ℕ) : ℤ)) with hcdef
  have hsplit : tD ϖ (fun i => c i + ν i) = tD ϖ c * tD ϖ ν := by rw [← tD_add]; rfl
  have hcont : ∀ ψ : π.V, Continuous ψ.1.1 := fun ψ => (π.cusp _ ψ.2).1.continuous
  have hleft : AutomorphicForm.IsLeftInvariant φ.1.1 := fun γ y => by
    rw [show AdelicGLn.diagonal E (m + 1) γ = ratGL E (m + 1) γ from Units.ext (Matrix.ext fun _ _ => rfl)]
    exact (π.cusp _ φ.2).1.left γ y
  let f : π.V →ₗ[ℂ] (GL (Fin (m + 1)) (w.adicCompletion E) → ℂ) :=
    { toFun := fun ψ h => whit ψ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * h)))
      map_add' := fun ψ ψ' => funext fun h => whit_add (hcont ψ) (hcont ψ') _
      map_smul' := fun c ψ => funext fun h => whit_smul c ψ.1.1 _ }
  have hmul : ∀ h k : GL (Fin (m + 1)) (w.adicCompletion E),
      g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * (h * k))) =
        (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * h))) * finGL E (m + 1) (locGL E (m + 1) w k) := by
    intro h k
    rw [← mul_assoc (tD ϖ c) h k, map_mul (locGL E (m + 1) w), map_mul (finGL E (m + 1)), mul_assoc]
  have hf : ∀ k (ψ : π.V), f (π.locRep w k ψ) = rightReg ℂ _ ℂ k (f ψ) := by
    intro k ψ
    funext h
    change whit (fun z => ψ.1.1 (z * finGL E (m + 1) (locGL E (m + 1) w k)))
        (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * h))) =
      whit ψ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * (h * k))))
    rw [hmul, whit_mul_right ψ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * h)))]

  have hN0 : ∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin (m + 1)), ∀ h : GL (Fin (m + 1)) (w.adicCompletion E),
      whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (u * h))) =
        psiLoc w (GlobalTheory.Whittaker.superDiag u) * whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w h)) := by
    intro u hu h
    rw [map_mul, map_mul, ← mul_assoc, commute_finGL_locGL w hg u, mul_assoc, finGL_locGL_eq_uGL w hu, whit,
      whittaker_uGL_mul (hcont φ) hleft, supSum_sLoc]
    rfl
  have hN : ∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin (m + 1)), ∀ h,
      f φ (u * h) = psiScaled w ((ϖ ^ e : (w.adicCompletion E)ˣ) : w.adicCompletion E)
        (GlobalTheory.Whittaker.superDiag u) * f φ h := by
    intro u hu h
    change whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * (u * h)))) =
      _ * whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * h)))
    have e1 : tD ϖ c * (u * h) = (tD ϖ c * u * tD ϖ (-c)) * (tD ϖ c * h) := by rw [tD_neg]; group
    rw [e1, hN0 _ (conj_mem_unipB ϖ c hu), psiScaled_apply, hcdef, superDiag_conj]
  have hK : ∀ h, ∀ k ∈ KGL w (n := (m + 1)), f φ (h * k) = f φ h := by
    intro h k hk
    change whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * (h * k)))) =
      whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * h)))
    rw [hmul, whit_mul_right φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * h)))]
    congr 1
    funext z
    exact congrArg (fun ψ : π.V => ψ.1.1 z) (GlobalTheory.LGrp.mem_fixed.1 hφ k hk)
  have hψ : ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w,
      psiScaled w ((ϖ ^ e : (w.adicCompletion E)ˣ) : w.adicCompletion E) (x * y) = 1) ↔ x ∈ Ov E w := by
    intro x
    simp only [psiScaled_apply, ← mul_assoc]
    exact hc x
  have hgoal : f φ (tD ϖ ν) = GlobalTheory.RSCell.sphZ (qV E w) (fun i => (α i : ℂ)) ν * f φ 1 := by
    by_cases h0 : φ = 0
    · subst h0
      have hz : ∀ h, f 0 h = 0 := fun h => by rw [map_zero]; rfl
      rw [hz, hz, mul_zero]
    by_cases hanti : Antitone ν
    · have hpos : ∀ i, 0 ≤ ν i := fun i => hν.trans (hanti (Fin.le_last i))
      have hsat := hα.2 φ hφ h0
      have hmain := GlobalTheory.T.shintani_formula_alt E w (m + 1) _ hψ (f φ) α hN hK ?_ ϖ hϖ (fun i => (ν i).toNat)
      · rw [GlobalTheory.RSCell.sphZ, if_pos hanti, tD_eq_diagPow ϖ ν hpos]
        exact hmain
      · intro ϖ' hϖ' j hj
        rw [← map_heckeVec (Final.GLintComm E w (m + 1)) (Tj_mem_hecke hϖ' j) f hf, hsat.2.2.2 ϖ' hϖ' j hj, map_smul]
    · rw [GlobalTheory.RSCell.sphZ, if_neg hanti, zero_mul]
      set M : ℕ := ∑ i, (ν i).natAbs
      have hM : ∀ i, (ν i).natAbs ≤ M := fun i =>
        Finset.single_le_sum (f := fun i => (ν i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      set ν' : Fin (m + 1) → ℤ := fun i => ν i + M
      have hpos : ∀ i, 0 ≤ ν' i := fun i => by have := hM i; simp only [ν']; omega
      set z := tD ϖ (fun _ : Fin (m + 1) => -(M : ℤ))
      have hνz : tD ϖ ν = tD ϖ ν' * z := by
        rw [← tD_add]; congr 1; funext i; simp only [ν', Pi.add_apply]; ring
      have hanti' : ¬ Antitone (fun i => (ν' i).toNat) := by
        intro ha
        refine hanti fun i j hij => ?_
        have := ha hij
        have h1 := Int.toNat_of_nonneg (hpos i)
        have h2 := Int.toNat_of_nonneg (hpos j)
        simp only [ν'] at this h1 h2
        omega
      have hz := GlobalTheory.T.whittaker_diagonal_eq_zero_of_not_antitone E w (m + 1) _ hψ (fun h => f φ (h * z))
        (fun u hu h => by simp only [mul_assoc]; exact hN u hu (h * z))
        (fun h k hk => by
          show f φ (h * k * z) = f φ (h * z)
          rw [mul_assoc, ← (commute_tD_const ϖ _ k).eq, ← mul_assoc, hK _ k hk])
        ϖ hϖ (fun i => (ν' i).toNat) hanti'
      rw [hνz, tD_eq_diagPow ϖ ν' hpos]
      exact hz
  have e2 := hgoal
  change whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * tD ϖ ν))) = _ *
    whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * 1))) at e2
  rw [mul_one, ← hsplit] at e2
  exact e2

end GlobalTheory.JSW.ShiftWhit

namespace GlobalTheory.JSW

theorem whit_mul_locGL_tD_shift : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (π : CuspSub E (m + 1)) (w : HeightOneSpectrum (𝓞 E)) (α : Fin (m + 1) → ℂˣ), HasSatGL w (π.locRep w) (Finset.univ.val.map α) → ∀ φ ∈ π.V, (∀ k ∈ KGL w (n := (m + 1)), act (.fin (locGL E (m + 1) w k)) φ = φ) → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ e : ℤ, GlobalTheory.RamShift.CondOne w ((ϖ ^ e : (w.adicCompletion E)ˣ) : w.adicCompletion E) → ∀ g : GA E (m + 1), GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g = 1 → ∀ ν : Fin (m + 1) → ℤ, 0 ≤ ν (Fin.last m) → GlobalTheory.JSW.whit φ.1 (g * finGL E (m + 1) (locGL E (m + 1) w (GlobalTheory.IwaCell.tD ϖ (fun i => e * ((m : ℤ) - ((i : ℕ) : ℤ)) + ν i)))) = GlobalTheory.RSCell.sphZ (qV E w) (fun i => (α i : ℂ)) ν * GlobalTheory.JSW.whit φ.1 (g * finGL E (m + 1) (locGL E (m + 1) w (GlobalTheory.IwaCell.tD ϖ (fun i => e * ((m : ℤ) - ((i : ℕ) : ℤ)))))) := by
  intro E _ _ _ m π w α hα φ hφV hφ ϖ hϖ e hc g hg ν hν
  exact GlobalTheory.JSW.ShiftWhit.main_of_fixed m π w α hα ⟨φ, hφV⟩
    (GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (hφ k hk)) ϖ hϖ e hc g hg ν hν

end GlobalTheory.JSW
end
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.splitPlace_idempotent_eq_completionEmbedding_one : ∀ (D : D7) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P → ∀ ι : P.adicCompletion D.host.E →+ AE D, GlobalTheory.DivPtLocal.IsIotaAt (rfl : P.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)) ι → e = ι 1 := by
  first | exact @GlobalTheory.IdemIota.idemAt_eq_iota_one | exact GlobalTheory.IdemIota.idemAt_eq_iota_one | (intros; apply GlobalTheory.IdemIota.idemAt_eq_iota_one <;> assumption)
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.weilOperator_inv_centralFlip_invariantForm_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χV χW om → ∀ (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (m : ℕ) (g : GA D V) (x : (AE D)ˣ) (ℓ : (WO V W → ℂ) →ₗ[ℂ] ℂ), Formalism.L2.NTheta.IsIdemAt e P → m ≠ 0 → Formalism.L2.Theta.mt V g = flipElt e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → IsFlipDet V e m x → (∀ y : WO V W, IsHalf (cA D e) y → ∀ φ : WO V W → ℂ, IsThetaFunO ψ V W φ → ℓ (heisO ψ V W y φ) = ℓ φ) → ∃ r : ℝ, 0 < r ∧ ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f → ℓ (om (g⁻¹, 1) f) = (r : ℂ) * ((χW x : Circle) : ℂ)⁻¹ * ℓ f := by
  first | exact @GlobalTheory.LevelSeries.FlipScalStep.om_inv_flip_eq | exact GlobalTheory.LevelSeries.FlipScalStep.om_inv_flip_eq | (intros; apply GlobalTheory.LevelSeries.FlipScalStep.om_inv_flip_eq <;> assumption)
end

section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

theorem _root_.GlobalTheory.T.hasFDerivAt_realChart_rapidKernelOperator : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (G : GA E a → ℂ) (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.MSpanDecay.Good G → ∀ (g : GA E a) (y : GL (Fin a) (Cinf E)), ∃ L : Lie E a →L[ℝ] ℂ, HasFDerivAt (chart (fun g : GA E a => ∫ x, k x * G (g * infGL E a (γ x)) ∂ν) g) L (toL y.val) ∧ ∀ Z : Lie E a, L Z = ∫ x, k x * lieD (toL (((γ x)⁻¹).val * ((y⁻¹).val * Matrix.of Z) * (γ x).val)) G (g * infGL E a (y * γ x)) ∂ν := by
  first | exact @GlobalTheory.MSpanDecay.KernelDeriv.hasFDerivAt_chart_kernel | exact GlobalTheory.MSpanDecay.KernelDeriv.hasFDerivAt_chart_kernel | (intros; apply GlobalTheory.MSpanDecay.KernelDeriv.hasFDerivAt_chart_kernel <;> assumption)
end

section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

theorem _root_.GlobalTheory.T.goodSmoothDecayModerateGrowth_rightTranslate : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ) (h : GA E a), GlobalTheory.MSpanDecay.Good F → GlobalTheory.MSpanDecay.Good (fun g => F (g * h)) := by
  first | exact @GlobalTheory.RtGood.good_mul_right | exact GlobalTheory.RtGood.good_mul_right | (intros; apply GlobalTheory.RtGood.good_mul_right <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.RSCell

theorem bInt_tl_last_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (F : GA E (m + 1) → ℂ) (Φ : (Fin (m + 1) → Cinf E) → ℂ)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (l₀ : GlobalTheory.CellDec.abelian₂ E (m + 1) T), (∀ w, l₀.1 w (Fin.last m) = 0) →
    GlobalTheory.JSW.whit F (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 → Φ (Pi.single (Fin.last m) 1) ≠ 0 → ∀ x : ℝ, GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 := by
  intro E _ _ _ m T ϖ F Φ J l₀ hl hW hΦ x
  have h0 : Finsupp.mapRange (fun y : Fin (m+1) → ℤ => y (Fin.last m)) rfl l₀.1 = 0 := by
    ext w; simp [hl w]
  have hadl : GlobalTheory.CellDec.adl ϖ (Finsupp.mapRange (fun y : Fin (m+1) → ℤ => y (Fin.last m)) rfl l₀.1) = 1 := by
    rw [h0]; apply Units.ext; apply FiniteAdeleRing.ext; intro v
    simp [GlobalTheory.CellDec.adl]; rfl
  have hrow : (GlobalTheory.CellDec.tl (m+1) ϖ l₀.1).val (Fin.last m) = Pi.single (Fin.last m) 1 := by
    rw [GlobalTheory.CellDec.tl_eq_diagT, GlobalTheory.SmGL.val_diagT]
    funext j
    simp [Matrix.diagonal_apply, Pi.single_apply, hadl, eq_comm]
  set g := GlobalTheory.CellDec.tl (m+1) ϖ l₀.1 with hg
  have hpi : (fun i => pInf E ((Pi.single (Fin.last m) (1 : Ad E) : Fin (m+1) → Ad E) i)) = Pi.single (Fin.last m) 1 := by
    funext i; by_cases h : i = Fin.last m
    · subst h; simp
    · simp [h]
  have hpf : (fun i => pFin E ((Pi.single (Fin.last m) (1 : Ad E) : Fin (m+1) → Ad E) i)) = Pi.single (Fin.last m) 1 := by
    funext i; by_cases h : i = Fin.last m
    · subst h; simp
    · simp [h]
  have hlat : (0 : Fin (m+1) → Af E) ∈ GlobalTheory.ThetaPoisson.latt (m+1) J := fun i => zero_mem _
  have hpsi : GlobalTheory.RSTheta.rsPsi (Fin.last m) (GlobalTheory.JSW.whit F) (GlobalTheory.JSW.whit F) Φ J (Pi.single (Fin.last m) 1) g (g.val (Fin.last m))
      = GlobalTheory.JSW.whit F g * (starRingEnd ℂ) (GlobalTheory.JSW.whit F g) * Φ (Pi.single (Fin.last m) 1) := by
    rw [hrow, GlobalTheory.RSTheta.rsPsi, GlobalTheory.ThetaPoisson.thetaFn, hpi, hpf, sub_self, Set.indicator_of_mem hlat,
      GlobalTheory.RSTheta.rsInf, GlobalTheory.RSTheta.rowGL_single, map_one, inv_one, mul_one]
    simp
  rw [bInt, hpsi]
  refine mul_ne_zero ?_ ?_
  · rw [enorm_ne_zero]
    exact mul_ne_zero (mul_ne_zero hW (by simpa using hW)) hΦ
  · rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.rpow_pos_of_pos (ideleModule E _).2 x

end GlobalTheory.RSCell
end
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.RSCellB

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem row_mul_of_mem_NA {ℓ : Fin a} (hℓ : (ℓ : ℕ) + 1 = a) {u : GA E a} (hu : u ∈ GlobalTheory.CellDec.NA E a)
    (g : GA E a) : (u * g).val ℓ = g.val ℓ := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
  funext j
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single ℓ]
  · rw [h2 ℓ, one_mul]
  · intro k _ hk
    have hlt : k < ℓ := by
      rcases lt_or_gt_of_ne hk with h | h
      · exact h
      · exact absurd k.2 (by have : (ℓ : ℕ) < k := h; omega)
    rw [h1 ℓ k hlt, zero_mul]
  · intro h; exact absurd (Finset.mem_univ ℓ) h

theorem det_of_mem_NA {u : GA E a} (hu : u ∈ GlobalTheory.CellDec.NA E a) : GeneralLinearGroup.det u = 1 := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, Units.val_one, Matrix.det_of_upperTriangular (fun i j h => h1 i j h)]
  simp [h2]

end GlobalTheory.RSCellB

namespace GlobalTheory.RSCellB

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem rsPsi_self_mul (ℓ : Fin a) {W : GA E a → ℂ} {u : GA E a} (hW : ∀ g, ‖W (u * g)‖ = ‖W g‖)
    (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (g : GA E a)
    (y : Fin a → Ad E) :
    GlobalTheory.RSTheta.rsPsi ℓ W W Φ J η (u * g) y = GlobalTheory.RSTheta.rsPsi ℓ W W Φ J η g y := by
  simp only [GlobalTheory.RSTheta.rsPsi, GlobalTheory.ThetaPoisson.thetaFn, GlobalTheory.RSTheta.rsInf, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, mul_assoc u g, hW]

theorem bInt_continuous_invariant_finite : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ℓ : Fin a), (ℓ : ℕ) + 1 = a →
    ∀ (F : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E),
    Continuous (GlobalTheory.JSW.whit F) → (∀ u ∈ GlobalTheory.CellDec.NA E a, ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖) →
    Continuous Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ →
    Continuous (fun p : ℝ × GA E a => GlobalTheory.RSCell.bInt ℓ F Φ J η p.1 p.2) ∧
      (∀ x, ∀ u ∈ GlobalTheory.CellDec.NA E a, ∀ g, GlobalTheory.RSCell.bInt ℓ F Φ J η x (u * g) = GlobalTheory.RSCell.bInt ℓ F Φ J η x g) ∧
      ∀ x g, GlobalTheory.RSCell.bInt ℓ F Φ J η x g ≠ ⊤ := by
  intro E _ _ _ a ℓ hℓ F Φ J η hWc hWu hΦc hΦs
  have hdet : Continuous fun g : GA E a => (ideleModule E (GeneralLinearGroup.det g) : ℝ) :=
    continuous_subtype_val.comp (continuous_ideleModule.comp (GroundTheory.Automorphic.AdelicGLn.continuous_det E a))
  refine ⟨?_, ?_, ?_⟩
  · have h1 : Continuous fun p : ℝ × GA E a => (p.2, p.2.val ℓ) :=
      continuous_snd.prodMk ((continuous_apply ℓ).comp ((Units.continuous_val (M := Matrix (Fin a) (Fin a) (Ad E))).comp continuous_snd))
    have h2 := (GlobalTheory.RSTheta.continuous_rsPsi hWc hWc hΦc hΦs J η).comp h1
    have h3 : Continuous fun p : ℝ × GA E a => (ideleModule E (GeneralLinearGroup.det p.2) : ℝ) ^ p.1 :=
      (hdet.comp continuous_snd).rpow continuous_fst fun p => Or.inl (ideleModule E (GeneralLinearGroup.det p.2)).2.ne'
    exact h2.enorm.ennreal_mul (ENNReal.continuous_ofReal.comp h3) (fun _ => Or.inr ENNReal.ofReal_ne_top)
      (fun _ => Or.inr enorm_ne_top)
  · intro x u hu g
    simp only [GlobalTheory.RSCell.bInt, row_mul_of_mem_NA hℓ hu, map_mul, det_of_mem_NA hu, one_mul]
    rw [rsPsi_self_mul ℓ (hWu u hu)]
  · intro x g
    exact ENNReal.mul_ne_top enorm_ne_top ENNReal.ofReal_ne_top

end GlobalTheory.RSCellB

end
end
