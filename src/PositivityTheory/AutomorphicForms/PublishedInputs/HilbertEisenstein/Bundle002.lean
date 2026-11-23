module

public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.Bundle001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle001
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RChar2

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne

namespace EisensteinCentralCharacter

variable {F : Type} [Field F] [NumberField F]

theorem thetaS_scalar_diagonal (Ψ : (Fin 2 → Ad F) → ℂ) (k : Fˣ) (h : GA F 2) :
    thetaS Ψ (Matrix.GeneralLinearGroup.scalar (Fin 2) (diagonal F k : Ideles F) * h) = thetaS Ψ h := by
  unfold thetaS
  let e : {ξ : Fin 2 → F // ξ ≠ 0} ≃ {ξ : Fin 2 → F // ξ ≠ 0} :=
    { toFun := fun ξ => ⟨(k : F) • ξ.1, smul_ne_zero k.ne_zero ξ.2⟩
      invFun := fun ξ => ⟨((k⁻¹ : Fˣ) : F) • ξ.1, smul_ne_zero (k⁻¹).ne_zero ξ.2⟩
      left_inv := fun ξ => Subtype.ext (by simp [smul_smul])
      right_inv := fun ξ => Subtype.ext (by simp [smul_smul]) }
  have key : ∀ ξ : Fin 2 → F,
      rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) (diagonal F k : Ideles F) * h : GA F 2) :
        Matrix (Fin 2) (Fin 2) (Ad F)) = rowA ((k : F) • ξ) ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F)) := by
    intro ξ
    rw [Units.val_mul, ← Matrix.vecMul_vecMul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    congr 1
    funext i
    rw [Matrix.vecMul_diagonal]
    simp [rowA, coe_diagonal, mul_comm]
  refine Eq.trans ?_ (e.tsum_eq fun ξ => Ψ (rowA ξ.1 ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F))))
  exact tsum_congr fun ξ => by rw [key]; rfl

theorem hchar_diagonal (ω : HChar F) (k : Fˣ) : ω.1 (diagonal F k) = 1 := ω.2.2 k

theorem absD_nonneg (g : GA F 2) : 0 ≤ absD g := (IdeleGroup.ideleModule F _).2.le

theorem absD_scalar_mul (z : Ideles F) (g : GA F 2) :
    absD (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) =
      ((IdeleGroup.ideleModule F z : ℝ)) ^ 2 * absD g := by
  unfold absD
  rw [map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, map_mul, map_pow]
  rfl

theorem eisInt_mul_diag [IsTotallyReal F] (ω : HChar F) (Ψ : (Fin 2 → Ad F) → ℂ) (g : GA F 2) (t : {r : ℝ // 0 < r})
    (u : normOneSubgroup F) (k : Fˣ) :
    eisInt ω Ψ g t (u * diagonalToNormOne F k) = eisInt ω Ψ g t u := by
  unfold eisInt
  have h : moduleSection (w0 F) t * ((u * diagonalToNormOne F k : normOneSubgroup F) : Ideles F) =
      diagonal F k * (moduleSection (w0 F) t * (u : Ideles F)) := by
    rw [Subgroup.coe_mul, coe_diagonalToNormOne]
    ac_rfl
  rw [h, map_mul (Matrix.GeneralLinearGroup.scalar (Fin 2)),
    mul_assoc (Matrix.GeneralLinearGroup.scalar (Fin 2) (diagonal F k)), thetaS_scalar_diagonal,
    map_mul ω.1, hchar_diagonal, one_mul]

theorem eisInt_scalar [IsTotallyReal F] (ω : HChar F) (Ψ : (Fin 2 → Ad F) → ℂ) (z : Ideles F) (g : GA F 2)
    (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) :
    eisInt ω Ψ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) t u =
      ((ω.1 z : ℂˣ) : ℂ) * eisInt ω Ψ g (t * (normOneSplitting (w0 F) z).2)
        (u * (normOneSplitting (w0 F) z).1) := by
  set p := normOneSplitting (w0 F) z with hp
  have hz : z = (p.1 : Ideles F) * moduleSection (w0 F) p.2 := by
    rw [← normOneSplitting_symm_apply, hp, ContinuousMulEquiv.symm_apply_apply]
  have ht0 : (p.2 : ℝ) = (IdeleGroup.ideleModule F z : ℝ) := rfl
  have hmul : moduleSection (w0 F) (t * p.2) * ((u * p.1 : normOneSubgroup F) : Ideles F) =
      (moduleSection (w0 F) t * (u : Ideles F)) * z := by
    rw [hz, map_mul, Subgroup.coe_mul]
    ac_rfl
  have hsc : Matrix.GeneralLinearGroup.scalar (Fin 2) ((moduleSection (w0 F) t * (u : Ideles F)) * z) * g =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) *
        (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) := by
    rw [map_mul, mul_assoc]
  have hω : ((ω.1 ((moduleSection (w0 F) t * (u : Ideles F)) * z) : ℂˣ) : ℂ) =
      ((ω.1 (moduleSection (w0 F) t * (u : Ideles F)) : ℂˣ) : ℂ) * ((ω.1 z : ℂˣ) : ℂ) := by
    rw [map_mul ω.1, Units.val_mul]
  have habs : ((IdeleGroup.ideleModule F z : ℝ) ^ 2 * absD g) ^ ((1 : ℝ) / 2) =
      (IdeleGroup.ideleModule F z : ℝ) * absD g ^ ((1 : ℝ) / 2) := by
    have h0 : 0 ≤ (IdeleGroup.ideleModule F z : ℝ) := (IdeleGroup.ideleModule F z).2.le
    rw [Real.mul_rpow (by positivity) (absD_nonneg g), ← Real.rpow_natCast,
      ← Real.rpow_mul h0]
    norm_num
  have hc : (((t * p.2 : {r : ℝ // 0 < r}) : ℝ) : ℂ) =
      ((t : ℝ) : ℂ) * ((IdeleGroup.ideleModule F z : ℝ) : ℂ) := by
    rw [← ht0, ← Complex.ofReal_mul]
    rfl
  unfold eisInt
  rw [hmul, hsc, absD_scalar_mul, habs, hω, hc]
  have hωz : ((ω.1 z : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hωA : ((ω.1 (moduleSection (w0 F) t * (u : Ideles F)) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  generalize thetaS Ψ (Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) *
    (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g)) = T
  generalize ((ω.1 z : ℂˣ) : ℂ) = a at hωz ⊢
  generalize ((ω.1 (moduleSection (w0 F) t * (u : Ideles F)) : ℂˣ) : ℂ) = b at hωA ⊢
  push_cast
  field_simp

theorem setIntegral_fd_mul (f : normOneSubgroup F → ℂ)
    (hf : ∀ (k : Fˣ) (u : normOneSubgroup F), f (u * diagonalToNormOne F k) = f u) (u0 : normOneSubgroup F) :
    ∫ u in normOneFundamentalDomain F, f (u * u0) ∂normOneMeasure F =
      ∫ u in normOneFundamentalDomain F, f u ∂normOneMeasure F := by
  have hE := isFundamentalDomain_normOneFundamentalDomain F (normOneMeasure F)
  have hE' : IsFundamentalDomain (diagonalNormOne F).op
      ((fun u => u * u0⁻¹) ⁻¹' normOneFundamentalDomain F) (normOneMeasure F) := by
    refine hE.preimage_of_equiv (e := id)
      (measurePreserving_mul_right (normOneMeasure F) u0⁻¹).quasiMeasurePreserving Function.bijective_id ?_
    intro γ x
    show (γ • x) * u0⁻¹ = γ • (x * u0⁻¹)
    simp only [Subgroup.smul_def, MulOpposite.smul_eq_mul_unop]
    exact mul_right_comm _ _ _
  have h1 : ∫ u in normOneFundamentalDomain F, f (u * u0) ∂normOneMeasure F =
      ∫ v in (fun u => u * u0⁻¹) ⁻¹' normOneFundamentalDomain F, f v ∂normOneMeasure F := by
    have := (measurePreserving_mul_right (normOneMeasure F) u0).setIntegral_preimage_emb
      (measurableEmbedding_mulRight u0) f ((fun u => u * u0⁻¹) ⁻¹' normOneFundamentalDomain F)
    rw [← this]
    congr 2
    ext x
    simp
  rw [h1]
  refine hE'.setIntegral_eq hE ?_
  intro γ x
  rw [Subgroup.smul_def, MulOpposite.smul_eq_mul_unop]
  have hm : ((γ : (normOneSubgroup F)ᵐᵒᵖ)).unop ∈ diagonalNormOne F := Subgroup.mem_op.1 γ.2
  obtain ⟨k, hk⟩ := Subgroup.mem_subgroupOf.1 hm
  have he : ((γ : (normOneSubgroup F)ᵐᵒᵖ)).unop = diagonalToNormOne F k := Subtype.ext hk.symm
  rw [he, hf]

end EisensteinCentralCharacter

open EisensteinCentralCharacter in
theorem central_character_holds : SPois → SInt → SSmooth → SCent := by
  intro _ _ _ F _ _ _ ω c _ z g
  have h1 : ∀ t : {r : ℝ // 0 < r},
      ∫ u in normOneFundamentalDomain F, eisInt ω (Phi c) (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) t u
        ∂normOneMeasure F =
      ((ω.1 z : ℂˣ) : ℂ) * ∫ u in normOneFundamentalDomain F,
        eisInt ω (Phi c) g (t * (normOneSplitting (w0 F) z).2) u ∂normOneMeasure F := by
    intro t
    simp only [eisInt_scalar ω (Phi c) z g t]
    rw [integral_const_mul, setIntegral_fd_mul _ (fun k u => eisInt_mul_diag ω (Phi c) g _ u k)]
  unfold Eis
  simp only [h1]
  rw [integral_const_mul]
  exact congrArg (((ω.1 z : ℂˣ) : ℂ) * ·) (integral_mul_right_eq_self
    (fun t => ∫ u in normOneFundamentalDomain F, eisInt ω (Phi c) g t u ∂normOneMeasure F)
    (normOneSplitting (w0 F) z).2)

end UpperTheory.HilbertEisensteinWeightOne
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.KFinitenessEisenstein

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def sgn (b : Bool) : ℝ := if b then 1 else -1

def archE (ε : InfinitePlace F → Bool) (x y : UpperTheory.V.TR.Rinf F) : ℂ :=
  ∏ v, (((x v : ℂ) + (sgn (ε v) : ℂ) * Complex.I * (y v : ℂ)) *
    Complex.exp (-(Real.pi : ℂ) * ((x v : ℂ) ^ 2 + (y v : ℂ) ^ 2)))


open Classical in
def PhiE (c : HeightOneSpectrum (𝓞 F) → ℕ) (ε : InfinitePlace F → Bool) (ξ : Fin 2 → Ad F) : ℂ :=
  archE ε (UpperTheory.V.TR.pInf F (ξ 0)) (UpperTheory.V.TR.pInf F (ξ 1)) *
    if ∀ w, Valued.v (pLoc F w (pFin F (ξ 0))) ≤ WithZero.exp (-(c w : ℤ)) ∧
        Valued.v (pLoc F w (pFin F (ξ 1)) - 1) ≤ WithZero.exp (-(c w : ℤ)) then 1 else 0

def lam (k : UpperTheory.V.TR.Kinf F 2) : ℂ := ∏ w, ((k.1 0 0 w : ℂ) + Complex.I * (k.1 0 1 w : ℂ))

def eps (k : UpperTheory.V.TR.Kinf F 2) (w : InfinitePlace F) : Bool :=
  decide (0 < k.1 0 0 w * k.1 1 1 w - k.1 0 1 w * k.1 1 0 w)

theorem place (a b c d x y : ℝ) (h1 : a * a + c * c = 1) (h2 : b * b + d * d = 1) (h3 : a * b + c * d = 0)
    (h4 : a * a + b * b = 1) (h5 : c * c + d * d = 1) (h6 : a * c + b * d = 0) :
    (((x * a + y * c : ℝ) : ℂ) + Complex.I * ((x * b + y * d : ℝ) : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * (((x * a + y * c : ℝ) : ℂ) ^ 2 + ((x * b + y * d : ℝ) : ℂ) ^ 2)) =
    ((a : ℂ) + Complex.I * (b : ℂ)) * (((x : ℂ) + (sgn (decide (0 < a * d - b * c)) : ℂ) * Complex.I * (y : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2))) := by
  have hsq : (x * a + y * c) ^ 2 + (x * b + y * d) ^ 2 = x ^ 2 + y ^ 2 := by
    linear_combination x ^ 2 * h4 + y ^ 2 * h5 + 2 * x * y * h6
  have hC : (((x * a + y * c : ℝ) : ℂ) ^ 2 + ((x * b + y * d : ℝ) : ℂ) ^ 2) = (x : ℂ) ^ 2 + (y : ℂ) ^ 2 := by
    exact_mod_cast hsq
  rw [hC]
  generalize Complex.exp (-(Real.pi : ℂ) * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2)) = E
  have hs2 : (a * d - b * c) * (a * d - b * c) = 1 := by
    linear_combination (c * c + d * d) * h4 + h5 - (a * c + b * d) * h6
  have hsg : ((sgn true : ℝ) : ℂ) = 1 := by simp [sgn]
  have hsg' : ((sgn false : ℝ) : ℂ) = -1 := by simp [sgn]
  rcases mul_self_eq_one_iff.mp hs2 with hs | hs
  · have hc : c = -b := by linear_combination (-c) * h4 + a * h6 - b * hs
    have hd : d = a := by linear_combination (-d) * h4 + b * h6 + a * hs
    have hpos : 0 < a * d - b * c := by
      rw [hs]
      norm_num
    rw [decide_eq_true hpos, hsg]
    subst hc hd
    push_cast
    linear_combination (-((b : ℂ) * (y : ℂ) * E)) * Complex.I_sq
  · have hc : c = b := by linear_combination (-c) * h4 + a * h6 - b * hs
    have hd : d = -a := by linear_combination (-d) * h4 + b * h6 + a * hs
    have hneg : ¬ 0 < a * d - b * c := by
      rw [hs]
      norm_num
    rw [decide_eq_false hneg, hsg']
    subst hc hd
    push_cast
    linear_combination ((c : ℂ) * (y : ℂ) * E) * Complex.I_sq

theorem rels (k : UpperTheory.V.TR.Kinf F 2) (w : InfinitePlace F) :
    k.1 0 0 w * k.1 0 0 w + k.1 1 0 w * k.1 1 0 w = 1 ∧ k.1 0 1 w * k.1 0 1 w + k.1 1 1 w * k.1 1 1 w = 1 ∧
    k.1 0 0 w * k.1 0 1 w + k.1 1 0 w * k.1 1 1 w = 0 ∧ k.1 0 0 w * k.1 0 0 w + k.1 0 1 w * k.1 0 1 w = 1 ∧
    k.1 1 0 w * k.1 1 0 w + k.1 1 1 w * k.1 1 1 w = 1 ∧ k.1 0 0 w * k.1 1 0 w + k.1 0 1 w * k.1 1 1 w = 0 := by
  have hA := Unitary.coe_star_mul_self k
  have hB := Unitary.coe_mul_star_self k
  have e : ∀ (M N : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)), M = N → ∀ i j, M i j w = N i j w :=
    fun M N h i j => by rw [h]
  have a1 := e _ _ hA 0 0
  have a2 := e _ _ hA 1 1
  have a3 := e _ _ hA 0 1
  have b1 := e _ _ hB 0 0
  have b2 := e _ _ hB 1 1
  have b3 := e _ _ hB 0 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] at a1 a2 a3 b1 b2 b3
  exact ⟨a1, a2, a3, b1, b2, b3⟩

theorem arch_rot (k : UpperTheory.V.TR.Kinf F 2) (X Y : UpperTheory.V.TR.Rinf F) :
    arch (fun w => X w * k.1 0 0 w + Y w * k.1 1 0 w) (fun w => X w * k.1 0 1 w + Y w * k.1 1 1 w) =
      lam k * archE (eps k) X Y := by
  unfold arch archE lam
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := rels k w
  exact place (k.1 0 0 w) (k.1 0 1 w) (k.1 1 0 w) (k.1 1 1 w) (X w) (Y w) h1 h2 h3 h4 h5 h6

theorem phi_rot (c : HeightOneSpectrum (𝓞 F) → ℕ) (k : UpperTheory.V.TR.Kinf F 2) (v : Fin 2 → Ad F) :
    Phi c (v ᵥ* ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) =
      lam k * PhiE c (eps k) v := by
  have hK : ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map
      (UpperTheory.V.TR.pInf F) = k.1 := by
    have h := congrArg Units.val (UpperTheory.V.TR.pInf_infGL (E := F) (Unitary.toUnits k))
    exact h
  have hKf : ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map
      (pFin F) = 1 := by
    have h := congrArg Units.val (UpperTheory.V.TR.pFin_infGL (E := F) (Unitary.toUnits k))
    exact h
  have ef : ∀ i, pFin F ((v ᵥ* ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F))) i) = pFin F (v i) := by
    intro i
    rw [RingHom.map_vecMul, hKf, Matrix.vecMul_one]
    rfl
  have e0 : UpperTheory.V.TR.pInf F ((v ᵥ* ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F))) 0) =
      fun w => UpperTheory.V.TR.pInf F (v 0) w * k.1 0 0 w + UpperTheory.V.TR.pInf F (v 1) w * k.1 1 0 w := by
    rw [RingHom.map_vecMul, hK]
    funext w
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  have e1 : UpperTheory.V.TR.pInf F ((v ᵥ* ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F))) 1) =
      fun w => UpperTheory.V.TR.pInf F (v 0) w * k.1 0 1 w + UpperTheory.V.TR.pInf F (v 1) w * k.1 1 1 w := by
    rw [RingHom.map_vecMul, hK]
    funext w
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  unfold Phi PhiE
  rw [ef 0, ef 1, e0, e1, arch_rot k, mul_assoc]

theorem absD_mul (g h : GA F 2) : absD (g * h) = absD g * absD h := by
  unfold absD
  rw [map_mul, map_mul]
  rfl

theorem absD_nonneg (g : GA F 2) : 0 ≤ absD g := by
  unfold absD
  exact ((IdeleGroup.ideleModule F) (Matrix.GeneralLinearGroup.det g)).2.le

theorem eis_smul (ω : HChar F) (a : ℂ) (Ψ : (Fin 2 → Ad F) → ℂ) (g : GA F 2) :
    Eis ω (fun v => a * Ψ v) g = a * Eis ω Ψ g := by
  unfold Eis
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  try dsimp only
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  try dsimp only
  unfold eisInt thetaS
  simp only [tsum_mul_left]
  ring

theorem eis_mul_right (ω : HChar F) (Ψ : (Fin 2 → Ad F) → ℂ) (g K : GA F 2) :
    Eis ω Ψ (g * K) = ((absD K ^ ((1 : ℝ) / 2) : ℝ) : ℂ) *
      Eis ω (fun v => Ψ (v ᵥ* (K : Matrix (Fin 2) (Fin 2) (Ad F)))) g := by
  unfold Eis
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  try dsimp only
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  try dsimp only
  unfold eisInt thetaS
  rw [absD_mul, Real.mul_rpow (absD_nonneg g) (absD_nonneg K)]
  simp only [← mul_assoc (Matrix.GeneralLinearGroup.scalar (Fin 2) _) g K, Units.val_mul, ← Matrix.vecMul_vecMul]
  push_cast
  ring

theorem cpt_eq (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (hs : Eis ω (Phi c) ∈ UpperTheory.V.TR.Sm F 2)
    (k : UpperTheory.V.TR.Kinf F 2) (g : GA F 2) :
    (UpperTheory.V.TR.cptRep F 2 k ⟨Eis ω (Phi c), hs⟩).1 g =
      ((((absD (UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2)) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) * lam k) *
        Eis ω (PhiE c (eps k)) g := by
  change Eis ω (Phi c) (g * UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k)) = _
  rw [eis_mul_right, show (fun v => Phi c (v ᵥ* ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F)))) = fun v => lam k * PhiE c (eps k) v from funext (phi_rot c k), eis_smul]
  ring

end UpperTheory.HilbertEisensteinWeightOne.KFinitenessEisenstein

open UpperTheory.HilbertEisensteinWeightOne.KFinitenessEisenstein in
theorem UpperTheory.HilbertEisensteinWeightOne.K_finiteness_holds : SPois → SInt → SSmooth → SKfin := by
  intro _ _ _ F _ _ _ ω c _ hs
  haveI : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun ε : InfinitePlace F → Bool => Eis ω (PhiE c ε))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hle : (Submodule.span ℂ (Set.range fun k => UpperTheory.V.TR.cptRep F 2 k ⟨Eis ω (Phi c), hs⟩)).map
      (UpperTheory.V.TR.Sm F 2).subtype ≤
      Submodule.span ℂ (Set.range fun ε : InfinitePlace F → Bool => Eis ω (PhiE c ε)) := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    have e : (UpperTheory.V.TR.Sm F 2).subtype (UpperTheory.V.TR.cptRep F 2 k ⟨Eis ω (Phi c), hs⟩) =
        ((((absD (UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2)) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) * lam k) •
          Eis ω (PhiE c (eps k)) :=
      funext fun g => by rw [Pi.smul_apply, smul_eq_mul]; exact cpt_eq ω c hs k g
    rw [SetLike.mem_coe, e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨eps k, rfl⟩)
  haveI := Submodule.finiteDimensional_of_le hle
  exact LinearEquiv.finiteDimensional
    (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) _).symm
end
end

section

open NumberField Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.TR Matrix

private theorem infGL_scalar {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (u : (Rinf F)ˣ) :
    infGL F 2 (GeneralLinearGroup.scalar (Fin 2) u) = GeneralLinearGroup.scalar (Fin 2) (infId F u) := by
  have h : ∀ x, pInf F (sInf F x) = x := fun x => (infEq F).symm_apply_apply x
  have h1 : pInf F (infId F u : Ideles F) = u := by
    change pInf F (1 - sInf F 1 + sInf F _) = _
    simp [h]
  have h2 : pFin F (infId F u : Ideles F) = 1 := by
    change (1 : Af F) - 0 + 0 = 1
    simp
  refine ga_ext ?_ ?_
  · rw [TR.pInf_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h1]
  · rw [TR.pFin_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h2]

private theorem fin_expU {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {ω : HChar F} (h : IsOfFinOrder ω)
    (z : Rinf F) : ω.1 (infId F (expU z)) = 1 := by
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e1 : expU z = expU ((n : ℝ)⁻¹ • z) ^ n := by
    refine Units.ext (funext fun i => ?_)
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [Units.val_pow_eq_pow_val, Pi.pow_apply, expU_val, ← Real.exp_nat_mul, Pi.smul_apply, smul_eq_mul]
    congr 1
    field_simp
  rw [e1, map_pow, map_pow]
  have e2 : ω.1 ^ n = 1 := congrArg Subtype.val e
  exact DFunLike.congr_fun e2 _

private theorem lie_scalar {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {ω : HChar F} (h : IsOfFinOrder ω)
    {φ : Sm F 2} (hφ : ∀ (z : Ideles F) (g : GA F 2), φ.1 (GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g) (z : Rinf F) : lie F 2 (toL (Matrix.scalar (Fin 2) z)) φ = 0 := by
  refine Subtype.ext (funext fun g => ?_)
  have h1 := hasDerivAt_curve φ g (fun t => GeneralLinearGroup.scalar (Fin 2) (expU (t • z)))
    (toL (Matrix.scalar (Fin 2) z)) (by simp [TR.expU_zero]) (by
      refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
      by_cases e : i = j
      · subst e
        have := ((hasDerivAt_id (0 : ℝ)).mul_const (z v)).exp
        simpa using this
      · simpa [Matrix.diagonal_apply, e] using hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have h2 : (fun t : ℝ => φ.1 (g * infGL F 2 (GeneralLinearGroup.scalar (Fin 2) (expU (t • z))))) = fun _ => φ.1 g := by
    funext t
    rw [infGL_scalar, ← GeneralLinearGroup.scalar_commute, hφ, fin_expU h]
    simp
  rw [h2] at h1
  exact h1.unique (hasDerivAt_const _ _)

private theorem casimir {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin 2 → Fin 2 → Module.End ℂ V)
    (hE : Formalism.REAL.GlRel E) (k : ℂ) (φ : V) (h0 : E 0 0 φ + E 1 1 φ = 0)
    (h1 : E 0 1 φ - E 1 0 φ = (Complex.I * k) • φ) (h2 : E 0 0 φ - E 1 1 φ = Complex.I • (E 0 1 φ + E 1 0 φ)) (u : ℂ) :
    Formalism.REAL.qdet E (u + 1 / 2) φ = ((u + (k - 1) / 2) * (u - (k - 1) / 2)) • φ :=
  _root_.UpperTheory.Reformulated.B.Qf10.casimir E hE k φ h0 h1 h2 u

theorem UpperTheory.HilbertEisensteinWeightOne.center_finiteness_holds : SPois → SInt → SSmooth → SZfin := by
  intro _ _ _ F _ _ _ ω c hω φ hc hw hl
  have hcap : ∀ v u, ∃ c : ℂ, TR.cap v u φ = c • φ := fun v u => by
    have h0 : Eop v 0 0 φ + Eop v 1 1 φ = 0 := by
      classical
      rw [← lie_scalar hω hc (Pi.single v 1), TR.Eop, TR.Eop, ← LinearMap.add_apply, ← map_add (f := _)]
      congr 2
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have := casimir _ (TR.glRel_Eop v) ((1 : ℕ) : ℂ) φ h0 (hw v) (hl v) u
    refine ⟨_, Eq.trans ?_ this⟩
    rw [TR.cap]
    norm_num
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {φ}) (Submodule.span_le.2 ?_)
  rintro _ ⟨z, hz, rfl⟩
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨v, u, rfl⟩ := hx
    obtain ⟨c, e⟩ := hcap v u
    exact Submodule.mem_span_singleton.2 ⟨c, e.symm⟩
  | algebraMap c => exact Submodule.mem_span_singleton.2 ⟨c, rfl⟩
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy =>
    obtain ⟨c, e⟩ := Submodule.mem_span_singleton.1 hy
    have e' : c • φ = y φ := e
    change x (y φ) ∈ Submodule.span ℂ {φ}
    rw [← e', map_smul]
    exact Submodule.smul_mem _ _ hx
end
