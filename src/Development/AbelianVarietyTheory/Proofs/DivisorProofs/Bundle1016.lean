module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle003
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle003
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothInExponentialCoordsIffFirstSecondKind
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle122
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.LocalToGlobal.Divisibility.Numbers
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualWeylEqSpanColProd
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RenameMemDualWeyl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle781
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle252
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle265
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle062
import Formalism.GradedWeylDivisibility.FinalC
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle011
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.PosDef
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.BadPrimesPeriodBound
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

section

noncomputable section

open GlobalTheory.SmoothForms NormedSpace
open scoped ContDiff Topology InnerProductSpace

namespace GlobalTheory.DerivedAction

variable {𝔸 H : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]

def dOp (π : 𝔸 → (H →L[ℂ] H)) (X : 𝔸) (v : H) : H := deriv (fun t : ℝ => π (exp (t • X)) v) 0

theorem abstract (σ : 𝔸 →ₗ[ℝ] 𝔸) (anti : ∀ a b, σ (a * b) = σ b * σ a) (one : σ 1 = 1) (invol : ∀ a, σ (σ a) = a)
    (π : 𝔸 → (H →L[ℂ] H)) (π1 : π 1 = 1) (πm : ∀ a b, σ a * a = 1 → σ b * b = 1 → π (a * b) = π a * π b) (v : H)
    (hv : ∀ (k : ℕ) (Xs : Fin k → 𝔸), (∀ i, σ (Xs i) = -Xs i) →
      ContDiff ℝ ∞ fun t : Fin k → ℝ => π ((List.ofFn fun i => exp (t i • Xs i)).prod) v)
    (X : 𝔸) (hX : σ X = -X) (Y : 𝔸) (hY : σ Y = -Y) :
    dOp π (X + Y) v = dOp π X v + dOp π Y v ∧
      dOp π (X * Y - Y * X) v = dOp π X (dOp π Y v) - dOp π Y (dOp π X v) := by
  classical
  let L : Submodule ℝ 𝔸 := LinearMap.ker (σ + LinearMap.id)
  have hL : ∀ Z, Z ∈ L ↔ σ Z = -Z := fun Z => by
    simp only [L, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, add_eq_zero_iff_eq_neg]
  have hunit : ∀ a, σ a * a = 1 → IsUnit (π a) := fun a ha => by
    have hr : a * σ a = 1 := by
      have : IsArtinianRing 𝔸 := IsArtinianRing.of_finite ℝ 𝔸
      exact mul_eq_one_comm.1 ha
    have hs : σ (σ a) * σ a = 1 := by rw [invol, hr]
    exact ⟨⟨π a, π (σ a), by rw [← πm _ _ ha hs, hr, π1], by rw [← πm _ _ hs ha, ha, π1]⟩, rfl⟩
  have hmul : ∀ a b, σ a * a = 1 → σ b * b = 1 → σ (a * b) * (a * b) = 1 := fun a b ha hb => by
    rw [anti, mul_assoc, ← mul_assoc (σ a), ha, one_mul, hb]
  let s : 𝔸 → (H →L[ℂ] H)ˣ := fun a => if h : IsUnit (π a) then h.unit else 1
  have hs : ∀ a, σ a * a = 1 → (s a : H →L[ℂ] H) = π a := fun a ha => by
    simp only [s, dif_pos (hunit a ha), IsUnit.unit_spec]
  have hD : IsLieData σ L.subtype s :=
    ⟨anti, one, invol, L.injective_subtype,
      fun Z => ⟨fun h => ⟨⟨Z, (hL Z).2 h⟩, rfl⟩, by rintro ⟨Z, rfl⟩; exact (hL _).1 Z.2⟩,
      fun a b ha hb => Units.ext (by rw [Units.val_mul, hs _ ha, hs _ hb, hs _ (hmul a b ha hb), πm _ _ ha hb])⟩
  have hl := hasLog_of_isLieData _ _ _ _ _ _ hD
  have hu : ∀ Z : L, σ (exp Z.1) * exp Z.1 = 1 := fun Z => SecondKind.exp_unitary hD Z
  have he : ∀ Z : L, ((expMap L.subtype s Z : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) = π (exp Z.1) := fun Z => hs _ (hu Z)
  have hprod : ∀ l : List L, σ (l.map fun Z => exp Z.1).prod * (l.map fun Z => exp Z.1).prod = 1 ∧
      (((l.map (expMap L.subtype s)).prod : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) = π (l.map fun Z => exp Z.1).prod := fun l => by
    induction l with
    | nil => simp [one, π1]
    | cons Z l ih =>
      simp only [List.map_cons, List.prod_cons, Units.val_mul]
      exact ⟨hmul _ _ (hu Z) ih.1, by rw [he, ih.2, πm _ _ (hu Z) ih.1]⟩

  have d1 : ∀ Z : L, DifferentiableAt ℝ (fun t : ℝ => π (exp (t • Z.1)) v) 0 := fun Z => by
    have h := (hv 1 (fun _ => Z.1) fun _ => (hL _).1 Z.2).comp
      (contDiff_pi.2 fun _ => contDiff_id : ContDiff ℝ ∞ fun (t : ℝ) (_ : Fin 1) => t)
    have := (h.differentiable (by simp)).differentiableAt (x := 0)
    simpa [Function.comp_def] using this
  have hlin : ∀ (A : H →L[ℂ] H) (Z : L) (u : H), DifferentiableAt ℝ (fun t : ℝ => π (exp (t • Z.1)) u) 0 →
      HasDerivAt (fun t : ℝ => A (π (exp (t • Z.1)) u)) (A (dOp π Z.1 u)) 0 := fun A Z u h =>
    (A.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h.hasDerivAt
  have d2 : ∀ Z Z' : L, DifferentiableAt ℝ (fun t : ℝ => π (exp (t • Z.1)) (dOp π Z'.1 v)) 0 := fun Z Z' => by
    have h := (hv 2 ![Z.1, Z'.1] (by
      intro i; fin_cases i
      · exact (hL _).1 Z.2
      · exact (hL _).1 Z'.2)).comp
      (contDiff_pi.2 (by
        intro i; fin_cases i
        · exact contDiff_fst
        · exact contDiff_snd) : ContDiff ℝ ∞ fun (p : ℝ × ℝ) => ![p.1, p.2])
    have h' : ContDiff ℝ ∞ (Function.uncurry fun (t r : ℝ) => π (exp (t • Z.1)) (π (exp (r • Z'.1)) v)) := by
      convert h using 1
      funext p
      have := πm _ _ (hu (p.1 • Z)) (hu (p.2 • Z'))
      simp only [Submodule.coe_smul] at this
      simp [Function.uncurry, this]
    have h3 : ContDiff ℝ ∞ fun t : ℝ =>
        fderiv ℝ (fun r : ℝ => π (exp (t • Z.1)) (π (exp (r • Z'.1)) v)) 0 (1 : ℝ) :=
      (ContDiff.fderiv (m := ∞) h' contDiff_const (by simp)).clm_apply contDiff_const
    have h4 := (h3.differentiable (by simp)).differentiableAt (x := 0)
    exact h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => (hlin _ Z' v (d1 Z')).deriv.symm)

  let φ : H → H → (H →L[ℂ] H)ˣ → ℂ := fun w u g => ⟪w, (g : H →L[ℂ] H) u⟫_ℂ
  have hder : ∀ (w : H) (Z : L) (u : H), DifferentiableAt ℝ (fun t : ℝ => π (exp (t • Z.1)) u) 0 →
      Der (expMap L.subtype s) Z (φ w u) = φ w (dOp π Z.1 u) := fun w Z u h => by
    funext g
    have h1 := ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (hlin g Z u h)
    refine Eq.trans ?_ h1.deriv
    simp only [Der, φ, Units.val_mul, he]
    rfl
  have hsm : ∀ w, Sm (expMap L.subtype s) (φ w v) := fun w => by
    refine (SecondKind.main _ _ _ _ _ _ hD hl Set.univ Submodule.span_univ _).2 fun k Z _ g => ?_
    have h1 := (((innerSL ℂ w).comp (g : H →L[ℂ] H)).restrictScalars ℝ).contDiff.comp
      (hv k (fun i => (Z i).1) fun i => (hL _).1 (Z i).2)
    convert h1 using 1
    funext t
    have h2 := (hprod (List.ofFn fun i => t i • Z i)).2
    rw [List.map_ofFn, List.map_ofFn] at h2
    simp only [φ, Units.val_mul]
    exact congrArg (fun A : H →L[ℂ] H => ⟪w, (g : H →L[ℂ] H) (A v)⟫_ℂ) h2
  let X' : L := ⟨X, (hL _).2 hX⟩
  let Y' : L := ⟨Y, (hL _).2 hY⟩
  let Z' : L := ⟨X * Y - Y * X, (hL _).2 (by rw [map_sub, anti, anti, hX, hY]; noncomm_ring)⟩
  refine ⟨ext_inner_left ℂ fun w => ?_, ext_inner_left ℂ fun w => ?_⟩
  · have h := (der_smooth_and_linear _ _ _ _ _ _ hD hl _ (hsm w)).2.1 X' Y'
    rw [hder w _ _ (d1 _), hder w _ _ (d1 _), hder w _ _ (d1 _)] at h
    rw [inner_add_right]
    exact congrFun h 1
  · have h := Bracket.der_bracket _ _ _ _ _ _ hD hl _ (hsm w) X' Y' Z' rfl
    rw [hder w _ _ (d1 _), hder w _ _ (d1 _), hder w _ _ (d1 _), hder w _ _ (d2 _ _), hder w _ _ (d2 _ _)] at h
    rw [inner_sub_right]
    exact (congrFun h 1).symm

open Matrix Formalism.MainNotions.S Formalism.L2.Theta


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem dRep_add_and_bracket : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (J : Matrix (Fin n) (Fin n) ℂ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Jᴴ = J → IsUnit J.det → IsURepOn (Formalism.QuantumDeterminants.UH J) π → ∀ v, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π v → ∀ X ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0}, ∀ Y ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0}, dRep π (X + Y) v = dRep π X v + dRep π Y v ∧ dRep π (X * Y - Y * X) v = dRep π X (dRep π Y v) - dRep π Y (dRep π X v) := by
  intro n H _ _ J π hJ hd hπ v hv X hX Y hY
  let σ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun X => J⁻¹ * Xᴴ * J
      map_add' := fun X Y => by rw [conjTranspose_add, mul_add, add_mul]
      map_smul' := fun c X => by
        rw [conjTranspose_smul, star_trivial, mul_smul_comm, smul_mul_assoc]; rfl }
  have hσ : ∀ Z, σ Z = J⁻¹ * Zᴴ * J := fun _ => rfl
  have hskew : ∀ Z, σ Z = -Z ↔ Zᴴ * J + J * Z = 0 := fun Z => by
    rw [hσ]
    constructor
    · intro h1
      rw [← mul_nonsing_inv_cancel_left _ (Zᴴ * J) hd, ← mul_assoc J⁻¹, h1, mul_neg, neg_add_cancel]
    · intro h1
      rw [mul_assoc, eq_neg_of_add_eq_zero_left h1, mul_neg, nonsing_inv_mul_cancel_left _ _ hd]
  have hun : ∀ u, σ u * u = 1 → u ∈ Formalism.QuantumDeterminants.UH J := fun u h1 => by
    change uᴴ * J * u = J
    have := congrArg (J * ·) h1
    simpa only [hσ, ← mul_assoc, mul_nonsing_inv _ hd, one_mul, mul_one] using this
  refine abstract σ (fun a b => ?_) ?_ (fun a => ?_) π hπ.1.1 (fun a b ha hb => hπ.1.2 _ (hun a ha) _ (hun b hb)) v
    (fun k Xs h => hv k Xs fun i => (hskew _).1 (h i)) X ((hskew _).2 hX) Y ((hskew _).2 hY)
  · simp only [hσ, conjTranspose_mul, mul_assoc]
    rw [mul_nonsing_inv_cancel_left _ _ hd]
  · rw [hσ, conjTranspose_one, mul_one, nonsing_inv_mul _ hd]
  · rw [hσ, hσ, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hJ]
    simp only [mul_assoc]
    rw [nonsing_inv_mul_cancel_left _ _ hd, nonsing_inv_mul _ hd, mul_one]

end GlobalTheory.DerivedAction

end
end

section

noncomputable section

namespace GlobalTheory.ColumnNormCompare

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)

@[reducible] def numDatumOfParameters (D : D7) (large₂ : SizeData₂ D) : NumDatum where
  R := D.R
  sc := large₂.sc
  H := D.host.toHostAx
  g := D.host.g
  g_prime := D.host.g_prime
  TT := D.host.TT
  Del := ⌊D.s.Del⌋₊
  h0 := ⌈LevelStarExponents.h0 large₂⌉₊
  hc := fun z => D.hc (tauPl D z)

def plRec (D : D7) : RPl D.R ≃ D.what₂.Tau := GlobalTheory.InertCompare.plEquiv D

def codeRec {D : D7} (large₂ : SizeData₂ D) (u : D.what₂.Word) : Code (numDatumOfParameters D large₂) := D.s.letter u

section Rec

variable {D : D7} (large₂ : SizeData₂ D) {EX : ErrX D} (Ch : _root_.Formalism.L2.Col.Chars (recFields D) (recPrimes EX) D.R.m)
  (mu0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E) (eta : Formalism.L2.Host.HChar D.host.E)
  (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))

end Rec

end GlobalTheory.ColumnNormCompare
end
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions Formalism.L2.DIV
open Formalism.REAL (fockF)
open GlobalTheory.SubstMem (padRows)
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.JetBlock

abbrev incl {a b : ℕ} (h : a ≤ b) : Fin a × Fin a → Fin b × Fin b := Prod.map (Fin.castLE h) (Fin.castLE h)

theorem incl_injective {a b : ℕ} (h : a ≤ b) : Function.Injective (incl h) :=
  (Fin.castLE_injective h).prodMap (Fin.castLE_injective h)

theorem fockF_rename {σ τ : Type} {e : σ → τ} (he : Function.Injective e) (f g : MvPolynomial σ ℂ) :
    fockF (rename e f) (rename e g) = fockF f g := by
  rw [GlobalTheory.LvT.PtNorm.fockF_eq, GlobalTheory.LvT.PtNorm.fockF_eq, fockL_apply, fockL_apply, GlobalTheory.Proof.ColumnInclusionRenaming.fockS_rename he]

theorem fockF_rowAct {r n : ℕ} (g : Matrix (Fin r) (Fin r) ℂ) (f : MvPolynomial (Fin r × Fin n) ℂ) :
    fockF (rowAct ℂ g f) (rowAct ℂ g f) = fockF f (rowAct ℂ (g * gᴴ) f) := by
  rw [fockRowAdj, ← rowActMul ℂ r n]
  rfl

theorem sum_castLE {M : Type} [AddCommMonoid M] {a b : ℕ} (h : a ≤ b) (F : Fin b → M)
    (hF : ∀ t : Fin b, a ≤ t.val → F t = 0) : ∑ t, F t = ∑ q : Fin a, F (Fin.castLE h q) := by
  symm
  refine Finset.sum_of_injOn (Fin.castLE h) (fun _ _ _ _ e => Fin.castLE_injective h e)
    (fun _ _ => Finset.mem_univ _) ?_ (fun _ _ => rfl)
  intro t _ ht
  refine hF t ?_
  by_contra h'
  exact ht ⟨⟨t.val, by omega⟩, by simp, by ext; simp⟩

theorem rowAct_pad {a b : ℕ} (h : a ≤ b) (A : Matrix (Fin a) (Fin b) ℂ) (f : MvPolynomial (Fin a × Fin a) ℂ) :
    rowAct ℂ (padRows A * (padRows A)ᴴ) (rename (incl h) f) = rename (incl h) (rowAct ℂ (A * Aᴴ) f) := by
  have e : (rowAct ℂ (padRows A * (padRows A)ᴴ)).comp (rename (incl h)) =
      (rename (incl h)).comp (rowAct ℂ (A * Aᴴ)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨p, q⟩

    simp only [AlgHom.comp_apply, rename_X, rowAct, aeval_X, map_sum, map_mul, rename_C, Prod.map]
    rw [sum_castLE h]
    · refine Finset.sum_congr rfl fun β _ => ?_
      simp [Matrix.mul_apply, padRows]
    · intro t ht
      simp [Matrix.mul_apply, padRows, not_lt.mpr ht]
  exact DFunLike.congr_fun e f

theorem exists_sing {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) :
    ∃ (U : Matrix (Fin a) (Fin a) ℂ) (t : Fin a → ℝ), U * Uᴴ = 1 ∧ Antitone t ∧ (∀ i, 0 ≤ t i) ∧
      A * Aᴴ = (U * Matrix.diagonal fun i => (t i : ℂ)) * (U * Matrix.diagonal fun i => (t i : ℂ))ᴴ ∧
      ∑ i, t i ^ 2 = ∑ β, ∑ α, ‖A α β‖ ^ 2 := by
  have hP : (A * Aᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose A
  have hH := hP.isHermitian
  set ev := hH.eigenvalues with hev
  have h0 : ∀ i, 0 ≤ ev i := hP.eigenvalues_nonneg
  set σ := Tuple.sort (fun i => -ev i) with hσ
  have hm : Monotone ((fun i => -ev i) ∘ σ) := Tuple.monotone_sort _
  set V : Matrix (Fin a) (Fin a) ℂ := hH.eigenvectorUnitary.1 with hV
  have hVV : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
  have hs : A * Aᴴ = V * Matrix.diagonal (fun i => (ev i : ℂ)) * Vᴴ := by
    have := hH.spectral_theorem
    exact this
  refine ⟨V.submatrix id σ, fun i => √(ev (σ i)), ?_, ?_, fun i => Real.sqrt_nonneg _, ?_, ?_⟩
  · rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hVV]
    simp
  · intro i j hij
    have := hm hij
    simp only [Function.comp] at this
    exact Real.sqrt_le_sqrt (by linarith)
  · rw [hs]
    ext i j
    simp only [Matrix.mul_apply (M := _ * _), Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id]
    rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : ((ev (σ k) : ℝ) : ℂ) = (√(ev (σ k)) : ℝ) * (√(ev (σ k)) : ℝ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (h0 _)]
    rw [star_mul']
    simp only [Complex.star_def, Complex.conj_ofReal]
    conv_lhs => rw [this]
    ring
  · simp only [Real.sq_sqrt (h0 _)]
    rw [Equiv.sum_comp σ ev]
    have h1 := hH.trace_eq_sum_eigenvalues
    apply Complex.ofReal_injective
    push_cast
    rw [hev]
    erw [← h1]
    rw [Finset.sum_comm]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
      Complex.mul_conj']

theorem dominance {n : ℕ} (ν : Fin n → ℕ) {f : MvPolynomial (Fin n × Fin n) ℂ} (hf : f ∈ dualWeyl ℂ n n ν) :
    ∀ m ∈ f.support, (∀ k : ℕ, (∑ a : Fin n with a.val < k, rowDeg m a) ≤ ∑ t : Fin n with t.val < k, ν t) ∧
      ∑ a : Fin n, rowDeg m a = ∑ t : Fin n, ν t := by
  classical
  rw [standardMonomialSpanDomain ℂ n n ν] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, rfl, rfl⟩ := hx
    exact fun m hm => bidetDominance ℂ n n K sz hsz I m hm
  | zero => simp
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.mp (support_add hm) with h | h
    · exact hx m h
    · exact hy m h
  | smul c x _ hx => exact fun m hm => hx m (support_smul hm)

theorem fock_subst_le {a b : ℕ} (h : a ≤ b) (A : Matrix (Fin a) (Fin b) ℂ) :
    ∃ t : Fin a → ℝ, (∀ i, 0 ≤ t i) ∧ ∑ i, t i ^ 2 = ∑ β, ∑ α, ‖A α β‖ ^ 2 ∧
      ∀ (ν : Fin a → ℕ), ∀ f ∈ dualWeyl ℂ a a ν,
        (fockF (rowAct ℂ (padRows A) (rename (incl h) f)) (rowAct ℂ (padRows A) (rename (incl h) f))).re ≤
          (∏ i, t i ^ (2 * ν i)) * (fockF f f).re := by
  obtain ⟨U, t, hU, ht, h0, hA, hs⟩ := exists_sing A
  refine ⟨t, h0, hs, fun ν f hf => ?_⟩
  have hd := dominance ν (dualWeylRowStable ℂ a a ν U f hf)
  have h1 := fockDiagBound a a t ν h0 ht (rowAct ℂ U f) (fun m hm => (hd m hm).1) (fun m hm => (hd m hm).2)
  rw [fockF_rowAct U, hU, ldlat_rowAct_one, ← AlgHom.comp_apply, rowActMul, fockF_rowAct, ← hA] at h1
  rw [fockF_rowAct, rowAct_pad, fockF_rename (incl_injective h)]
  exact h1

theorem rename_hw {a b : ℕ} (h : a ≤ b) (ν : Fin a → ℕ) :
    rename (incl h) (hw ℂ (le_refl a) ν) = hw ℂ (le_refl b) (rowNu (r := b) ν) := by
  rw [← GlobalTheory.Proof.ColumnInclusionRenaming.rename_hw h]
  unfold hw
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, map_pow]
  congr 1
  unfold lpMinor
  rw [AlgHom.map_det, AlgHom.map_det]
  congr 1
  ext p q : 2
  simp [GlobalTheory.Proof.ColumnInclusionRenaming.colIncl]


open GlobalTheory.DualWeyl GlobalTheory.WeylMinorDual in
theorem fock_mul_det {n : ℕ} (μ : Fin n → ℕ) (hμ : Antitone μ) (e : ℕ) {f : MvPolynomial (Fin n × Fin n) ℂ}
    (hf : f ∈ dualWeyl ℂ n n μ) :
    fockF (f * gdet ℂ n ^ e) (f * gdet ℂ n ^ e) /
        fockF (hw ℂ (le_refl n) fun i => μ i + e) (hw ℂ (le_refl n) fun i => μ i + e) =
      fockF f f / fockF (hw ℂ (le_refl n) μ) (hw ℂ (le_refl n) μ) := by
  have hν : Antitone fun i => μ i + e := fun i j hij => Nat.add_le_add_right (hμ hij) e
  have hm : f * gdet ℂ n ^ e ∈ dualWeyl ℂ n n fun i => μ i + e :=
    (dualWeylMul ℂ n n _ _ _ _).1 hf (GlobalTheory.SubstMem.det_pow_mem n e)
  have hn : ∀ (g : UN n) (p : Pol n ℂ), ‖evalAt g.1 (p * gdet ℂ n ^ e)‖ = ‖evalAt g.1 p‖ := by
    intro g p
    have h1 : evalAt g.1 (gdet ℂ n) = g.1.det := by
      unfold gdet
      rw [AlgHom.map_det]
      congr 1
      ext i j
      simp
    rw [map_mul, map_pow, h1, norm_mul, norm_pow,
      CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary g.2), one_pow, mul_one]
  have h1 := (GlobalTheory.T.dualWeyl_extremal_reproducing_normSq_one n μ hμ).2
  have h2 := (GlobalTheory.T.dualWeyl_extremal_reproducing_normSq_one n _ hν).2
  rw [GlobalTheory.DualWeyl.extremal, hw_add] at h2
  simp only [GlobalTheory.DualWeyl.normSq, hn] at h2
  rw [GlobalTheory.DualWeyl.normSq, GlobalTheory.DualWeyl.extremal] at h1
  have hd : (dim (fun i => μ i + e) : ℝ) = dim μ := by
    refine mul_right_cancel₀ (fun h0 => ?_) (h2.trans h1.symm)
    rw [h0, mul_zero] at h1
    exact zero_ne_one h1
  have e1 := GlobalTheory.DualWeylFock.form_eq_fock_div n μ hμ f hf f hf
  have e2 := GlobalTheory.DualWeylFock.form_eq_fock_div n _ hν _ hm _ hm
  rw [form_self] at e1 e2
  refine e2.symm.trans (Eq.trans ?_ e1)
  simp only [GlobalTheory.DualWeyl.normSq, hn, hd]

end GlobalTheory.JetBlock
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocusPull

theorem exists_gen_of_nonzeroLocus_eq_top {Y : Scheme.{0}} {M : LB Y} (s : M.Sec) (h : ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s = ⊤) :
    ∃ t : LB.Gen M, t.IsGen := by
  have hu : ∀ j, IsUnit (s.f j) := fun j =>
    Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
      have hy' : y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s := h ▸ trivial
      exact (Y.mem_basicOpen _ y hy).1 ((GlobalTheory.mem_nonzeroLocus_iff_basicOpen s hy).1 hy')
  exact ⟨⟨fun j => (hu j).unit⟩, fun i j => Units.ext (s.compat i j)⟩

theorem isLocus_pull {X Y : Scheme.{0}} (f : Y ⟶ X) {c : Pic X} {V : X.Opens} (h : IsLocus c V) :
    IsLocus (GlobalTheory.CechPic.pull f c) (f ⁻¹ᵁ V) := by
  obtain ⟨L, hL, s, rfl, rfl⟩ := h
  exact ⟨_, pull_isLB hL f, GlobalTheory.secPull s f, rfl, GlobalTheory.nonzeroLocus_secPull s f⟩

theorem pull_eq_zero_of_isLocus {X Y : Scheme.{0}} (f : Y ⟶ X) {c : Pic X} {V : X.Opens} (h : IsLocus c V)
    (hf : ∀ y, f y ∈ V) : GlobalTheory.CechPic.pull f c = 0 := by
  obtain ⟨L, hL, s, rfl, rfl⟩ := h
  have htop : ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (GlobalTheory.secPull s f) = ⊤ := by
    rw [GlobalTheory.nonzeroLocus_secPull]
    exact top_unique fun y _ => hf y
  exact (cls_eq_zero_iff (pull_isLB hL f)).2 (exists_gen_of_nonzeroLocus_eq_top _ htop)

theorem locus_pull :
    (∀ (X Y : Scheme.{0}) (f : Y ⟶ X) (c : Pic X) (V : X.Opens), IsLocus c V → IsLocus (GlobalTheory.CechPic.pull f c) (f ⁻¹ᵁ V)) ∧ (∀ (X Y : Scheme.{0}) (f : Y ⟶ X) (c : Pic X) (V : X.Opens), IsLocus c V → (∀ y, f y ∈ V) → GlobalTheory.CechPic.pull f c = 0) :=
  ⟨fun _ _ f _ _ h => isLocus_pull f h, fun _ _ f _ _ h hf => pull_eq_zero_of_isLocus f h hf⟩

end GlobalTheory.LocusPull
end
end
