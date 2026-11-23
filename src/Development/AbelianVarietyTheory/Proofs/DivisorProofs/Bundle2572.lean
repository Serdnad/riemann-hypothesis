module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2558
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2564
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2567
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2093
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1940
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio


theorem _root_.GlobalTheory.T.localIndex_localNorm_normalizingFactor_eq_partial : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)), GoodMod D 𝔪 Sf → ∀ a a' : ℕ, 1 ≤ a' →
  (locIdx D 𝔪 a a' : ℂ) * (locNorm D 𝔪 a a' : ℂ) * GlobalTheory.LFun.dSfun D.host.E (∅ : Set (FinPl D)) a (a + a') ((a' : ℂ) / 2) =
    GlobalTheory.LFun.dSfun D.host.E (Sf : Set (FinPl D)) a (a + a') ((a' : ℂ) / 2) := by
  first | exact @GlobalTheory.NormRatio.locIdx_mul_locNorm_mul_dSfun | exact GlobalTheory.NormRatio.locIdx_mul_locNorm_mul_dSfun | (intros; apply GlobalTheory.NormRatio.locIdx_mul_locNorm_mul_dSfun <;> assumption)
end

section

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio


theorem _root_.GlobalTheory.T.card_transversal_congruence_mul_norm_eq_localNorm : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ → ∀ (a a' : ℕ) (R : Finset (Formalism.MainNotions.StandardLatticesGL3.GA D a)),
  (∀ r ∈ R, r ∈ intG D a) → (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) →
    (R.card : ℝ) * ((Ideal.absNorm 𝔪 : ℝ) ^ (a * (a + a')))⁻¹ = locNorm D 𝔪 a a' := by
  first | exact @GlobalTheory.NormRatio.card_transversal_mul | exact GlobalTheory.NormRatio.card_transversal_mul | (intros; apply GlobalTheory.NormRatio.card_transversal_mul <;> assumption)
end

section

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

noncomputable section

namespace GlobalTheory.CosetOrth

variable {D : D7}

theorem hO_single_of_gram_one {S T : HSp D} (hS : S.gram = 1) (hT : T.gram = 1) (p : Fin T.rank) (q : Fin S.rank)
    (x : AE D) (y : WO S T) : hO S T (Matrix.single p q x) y = cA D (y p q) * x := by
  unfold hO
  rw [hS, hT, inv_one, Finset.sum_eq_single q, Finset.sum_eq_single q, Finset.sum_eq_single p, Finset.sum_eq_single p]
  · rw [Matrix.one_apply_eq, Matrix.one_apply_eq, Matrix.single_apply_same, map_one, one_mul, mul_one]
  · intro b _ hb; simp [Matrix.one_apply_ne hb.symm]
  · exact fun h => absurd (Finset.mem_univ _) h
  · intro b _ hb
    refine Finset.sum_eq_zero fun d _ => ?_
    by_cases h : d = p
    · subst h; simp [Matrix.one_apply_ne hb]
    · simp [Matrix.single_apply_of_row_ne (Ne.symm h)]
  · exact fun h => absurd (Finset.mem_univ _) h
  · intro b _ hb; simp [Matrix.one_apply_ne hb.symm]
  · exact fun h => absurd (Finset.mem_univ _) h
  · intro b _ hb; simp [Matrix.single_apply_of_col_ne _ _ (Ne.symm hb)]
  · exact fun h => absurd (Finset.mem_univ _) h

theorem fe_incA_mul (a : D.host.E) (z : AE D) : fe D (incA D a * z) = algebraMap D.host.E (FA D) a * fe D z := by
  rw [map_mul, fe_apply (incA D a), GlobalTheory.LatVac.finPart_incA, GlobalTheory.FinIdlRead.finAdEquiv_one_tmul]

theorem inHat_one_fe_iff (z : AE D) : InHat 1 (fe D z) ↔ finPart D z ∈ intAE D := by
  rw [inHat_one_iff, GlobalTheory.FinIdlRead.mem_intAE_iff_finAdEquiv]
  rfl

theorem inHat_of_char_dual : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (r : D.host.E) (LB : Lat T) (n : ℕ), IsStdChar D ψ (-1) →
  S.gram = 1 → T.gram = 1 → IsSelfDualC S (stdLat S) → IsSelfDualC T LB → r ≠ 0 →
  (∀ u ∈ (latO S T (stdLat S) LB fun _ => True), HatPt ((n : D.host.E) * r) 1 u) →
  ∀ (p : Fin T.rank) (q : Fin S.rank) (c : AE D), infPart D c = 0 →
  (∀ t : AE D, infPart D t = 0 → InHat 1 (fe D t) →
    ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (incA D (star r⁻¹) * (t * c)))) = 1) →
  InHat 1 (algebraMap D.host.E (FA D) ((n : D.host.E) * n * r) * fe D c) := by
  intro D ψ S T r LB n hψ hS hT hΛS hΛT hr hL p q c hc h
  have hmem : (Matrix.single p q (incA D (n : D.host.E) * c) : WO S T) ∈
      latO S T (stdLat S) LB fun _ => True := by
    refine GlobalTheory.LatVac.mem_of_char hψ hΛS hΛT ?_ fun u' hu' => ?_
    · rw [Matrix.map_single, map_mul, hc, mul_zero, Matrix.single_zero]
    · obtain ⟨h0, h1⟩ := hL u' hu'
      have h0' : infPart D (u' p q) = 0 := congrFun (congrFun h0 p) q
      have ht := h (cA D (incA D ((n : D.host.E) * r) * u' p q))
        (by rw [(GlobalTheory.IdemSupport.parts_cA _).1, map_mul, h0', mul_zero, map_zero])
        (by
          rw [inHat_one_fe_iff]
          refine GlobalTheory.IdemSupport.finPart_cA_mem ?_
          rw [← inHat_one_fe_iff, fe_incA_mul]
          exact h1 p q)
      have e : incA D (star r⁻¹) * (cA D (incA D ((n : D.host.E) * r) * u' p q) * c) =
          cA D (u' p q) * (incA D (n : D.host.E) * c) := by
        have e1 : incA D (star r⁻¹) * incA D (star ((n : D.host.E) * r)) = incA D (n : D.host.E) := by
          rw [← map_mul, ← star_mul, mul_assoc, mul_inv_cancel₀ hr, mul_one, star_natCast]
        rw [map_mul, GlobalTheory.IdemSupport.cA_incA, ← e1]
        ring
      rw [e] at ht
      unfold symplO
      rw [hO_single_of_gram_one hS hT]
      exact ht
  have h2 := (hL _ hmem).2 p q
  rw [Matrix.single_apply_same, fe_incA_mul, ← mul_assoc, ← map_mul] at h2
  rw [mul_right_comm]
  exact h2

end GlobalTheory.CosetOrth
end
end

section

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

noncomputable section

namespace GlobalTheory.CosetOrth.Cong

theorem count_coe_ne_zero_iff {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {J : Ideal (𝓞 E)}
    (hJ : J ≠ ⊥) : FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 ↔ J ≤ w.asIdeal := by
  rw [FractionalIdeal.count_coe E w hJ, Nat.cast_ne_zero, Associates.count_ne_zero_iff_dvd hJ w.irreducible,
    Ideal.dvd_iff_le]

theorem val_le_one_of_mul_eq_one {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {n : ℕ}
    (G H : Matrix (Fin n) (Fin n) K) (hHG : H * G = 1) (hH : ∀ i j, v ((1 - H) i j) < 1) (i j : Fin n) : v (G i j) ≤ 1 := by
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n)) (fun k => v (G k j)) ⟨i, Finset.mem_univ _⟩
  refine (hp i (Finset.mem_univ _)).trans ?_
  by_contra hlt
  rw [not_le] at hlt
  have h0 : v (G p j) ≠ 0 := (zero_lt_one.trans hlt).ne'
  have e : G = 1 + (1 - H) * G := by rw [sub_mul, hHG, one_mul]; abel
  have e2 : G p j = (1 : Matrix (Fin n) (Fin n) K) p j + ∑ k, (1 - H) p k * G k j := by
    conv_lhs => rw [e]
    rw [Matrix.add_apply, Matrix.mul_apply]
  have h1 : v ((1 : Matrix (Fin n) (Fin n) K) p j) < v (G p j) := by
    refine lt_of_le_of_lt ?_ hlt
    rw [Matrix.one_apply]; split_ifs <;> simp
  have h2 : v (∑ k, (1 - H) p k * G k j) < v (G p j) := by
    refine v.map_sum_lt h0 fun k _ => ?_
    rw [map_mul]
    calc v ((1 - H) p k) * v (G k j) ≤ v ((1 - H) p k) * v (G p j) := by
          gcongr; exact hp k (Finset.mem_univ _)
      _ < 1 * v (G p j) := mul_lt_mul_of_pos_right (hH p k) (zero_lt_one.trans hlt)
      _ = _ := one_mul _
  have := v.map_add_lt h1 h2
  rw [← e2] at this
  exact lt_irrefl _ this

variable {D : D7}

def evAt (w : HeightOneSpectrum (𝓞 D.host.E)) : FA D →+* w.adicCompletion D.host.E where
  toFun x := x w
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem inv_apply {n : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D n) (i j : Fin n) :
    (((y⁻¹ : Formalism.MainNotions.StandardLatticesGL3.GA D n) : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j =
      Formalism.MainNotions.StandardLatticesGL3.sgA D (((y : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) j i) := by
  have hh : Formalism.UG.cT (Formalism.MainNotions.StandardLatticesGL3.sgA D) (y.1 : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * y.1 = 1 := by
    have h2 := y.2
    change Formalism.UG.cT _ (y.1 : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * _ * _ = _ at h2
    rw [Matrix.map_one _ (map_zero _) (map_one _), mul_one] at h2
    exact h2
  rw [Subgroup.coe_inv, Units.inv_eq_of_mul_eq_one_left hh]
  rfl

theorem finMat_inv_mul {n : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D n) : finMat y⁻¹ * finMat y = 1 := by
  unfold finMat
  have := (Matrix.map_mul (f := GlobalTheory.BotFormula.toFinE D)
    (L := (((y⁻¹ : Formalism.MainNotions.StandardLatticesGL3.GA D n) : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)))
    (M := ((y : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)))).symm
  rw [this, Subgroup.coe_inv, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]

theorem val_one_le {n : ℕ} (i j : Fin n) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    Valued.v ((1 : Matrix (Fin n) (Fin n) (FA D)) i j w) ≤ 1 := by
  change Valued.v (evAt w ((1 : Matrix (Fin n) (Fin n) (FA D)) i j)) ≤ 1
  rw [Matrix.one_apply]; split_ifs <;> simp

theorem val_sub_le {x y : FA D} {w : HeightOneSpectrum (𝓞 D.host.E)} (hx : Valued.v (x w) ≤ 1) (hy : Valued.v (y w) ≤ 1) :
    Valued.v ((x - y) w) ≤ 1 := by
  change Valued.v (evAt w (x - y)) ≤ 1
  rw [map_sub]
  exact (Valued.v.map_sub _ _).trans (max_le hx hy)

theorem integral_of_cong {n : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D n) (w : HeightOneSpectrum (𝓞 D.host.E))
    (h : ∀ i j, Valued.v ((1 - finMat y⁻¹) i j w) < 1) (i j : Fin n) :
    Valued.v (finMat y i j w) ≤ 1 ∧ Valued.v (finMat y⁻¹ i j w) ≤ 1 := by
  constructor
  · refine val_le_one_of_mul_eq_one Valued.v ((finMat y).map (evAt w)) ((finMat y⁻¹).map (evAt w)) ?_ (fun a b => ?_) i j
    · rw [← Matrix.map_mul, finMat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    · have : (1 - (finMat y⁻¹).map (evAt w)) a b = evAt w ((1 - finMat y⁻¹) a b) := by
        rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      rw [this]; exact h a b
  · have : finMat y⁻¹ i j = (1 : Matrix (Fin n) (Fin n) (FA D)) i j - (1 - finMat y⁻¹) i j := by
      rw [Matrix.sub_apply, sub_sub_cancel]
    rw [this]
    exact val_sub_le (val_one_le i j w) (h i j).le

theorem inHat_of_inv_cong : ∀ {D : D7}, (∀ w : HeightOneSpectrum (𝓞 D.host.E), ∃ w' : HeightOneSpectrum (𝓞 D.host.E), w'.asIdeal = D.host.conj • w.asIdeal ∧
    (∀ x : Formalism.MainNotions.StandardLatticesGL3.AE D, Valued.v (GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.sgA D x) w') = Valued.v (GlobalTheory.BotFormula.toFinE D x w)) ∧
    (∀ 𝔞 : Ideal (𝓞 D.host.E), 𝔞 ≠ ⊥ → FractionalIdeal.count D.host.E w' ((D.host.conj • 𝔞 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      FractionalIdeal.count D.host.E w (𝔞 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) ∧
    ∀ w'' : HeightOneSpectrum (𝓞 D.host.E), w''.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) ↔ w'' = w ∨ w'' = w') →
  ∀ (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)), GoodMod D 𝔪 Sf → ∀ {n : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D n),
  (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ Sf → ∀ i j,
    Valued.v (finMat y i j w) ≤ 1 ∧ Valued.v (finMat y⁻¹ i j w) ≤ 1) →
  (∀ w : HeightOneSpectrum (𝓞 D.host.E), D.host.conj • 𝔪 ≤ w.asIdeal → ∀ i j,
    Valued.v ((1 - finMat y⁻¹) i j w) ≤ WithZero.exp (-(FractionalIdeal.count D.host.E w
      ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)))) →
  ∀ i j, InHat 1 (finMat y i j) ∧ InHat 1 (finMat y⁻¹ i j) ∧
    InHat (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ((finMat y - 1) i j) := by
  intro D hc 𝔪 Sf hG n y hoff hcong
  obtain ⟨h0, hsup, -, hS⟩ := hG
  have h0' : D.host.conj • 𝔪 ≠ ⊥ := fun h => h0 (by
    have := congrArg (fun I => D.host.conj⁻¹ • I) h
    simpa using this)
  have hb : ∀ w : HeightOneSpectrum (𝓞 D.host.E), D.host.conj • 𝔪 ≤ w.asIdeal → ∀ i j,
      Valued.v (finMat y i j w) ≤ 1 ∧ Valued.v (finMat y⁻¹ i j w) ≤ 1 := by
    intro w hw
    refine integral_of_cong y w fun i j => (hcong w hw i j).trans_lt ?_
    have h1 := (count_coe_ne_zero_iff w h0').2 hw
    have h2 := FractionalIdeal.count_coe_nonneg D.host.E w (D.host.conj • 𝔪)
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have key : ∀ w : HeightOneSpectrum (𝓞 D.host.E), ∀ i j, Valued.v (finMat y i j w) ≤ 1 ∧ Valued.v (finMat y⁻¹ i j w) ≤ 1 ∧
      Valued.v ((finMat y - 1) i j w) ≤ WithZero.exp (-(FractionalIdeal.count D.host.E w
        (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))) := by
    intro w i j
    by_cases hw : 𝔪 ≤ w.asIdeal
    · obtain ⟨w', e', hv, hcnt, -⟩ := hc w
      have hw' : D.host.conj • 𝔪 ≤ w'.asIdeal := by
        rw [e']; exact Ideal.pointwise_smul_le_pointwise_smul_iff.2 hw
      have t : ∀ (z : Formalism.MainNotions.StandardLatticesGL3.GA D n) (a b : Fin n), Valued.v (finMat z a b w) = Valued.v (finMat z⁻¹ b a w') := by
        intro z a b
        unfold finMat
        rw [Matrix.map_apply, Matrix.map_apply, inv_apply, hv]
      refine ⟨(t y i j).trans_le (hb w' hw' j i).2, (t y⁻¹ i j).trans_le (by rw [inv_inv]; exact (hb w' hw' j i).1), ?_⟩
      rw [← hcnt 𝔪 h0]
      refine le_of_eq_of_le ?_ (hcong w' hw' j i)
      have e1 : (finMat y - 1) i j = GlobalTheory.BotFormula.toFinE D
          ((((y : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) - 1) i j) := by
        unfold finMat
        rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      have e2 : (1 - finMat y⁻¹) j i = -GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.sgA D
          ((((y : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) - 1) i j)) := by
        unfold finMat
        rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, map_sub, Matrix.map_apply, inv_apply, neg_sub, Matrix.one_apply,
          Matrix.one_apply]
        by_cases hij : i = j
        · subst hij; simp
        · rw [if_neg hij, if_neg (Ne.symm hij)]; simp
      rw [e1, e2, ← hv]
      exact (Valuation.map_neg _ _).symm
    · have hint : Valued.v (finMat y i j w) ≤ 1 ∧ Valued.v (finMat y⁻¹ i j w) ≤ 1 := by
        by_cases hu : w.under (𝓞 D.host.F) ∈ Sf
        · obtain ⟨w₀, hw₀, e₀⟩ := (hS _).1 hu
          obtain ⟨w', e', -, -, hun⟩ := hc w₀
          rcases (hun w).1 e₀.symm with rfl | rfl
          · exact absurd hw₀ hw
          · exact hb _ (by rw [e']; exact Ideal.pointwise_smul_le_pointwise_smul_iff.2 hw₀) i j
        · exact hoff w hu i j
      refine ⟨hint.1, hint.2, ?_⟩
      have hz : FractionalIdeal.count D.host.E w (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = 0 := by
        by_contra h; exact hw ((count_coe_ne_zero_iff w h0).1 h)
      rw [hz, neg_zero, WithZero.exp_zero, Matrix.sub_apply]
      exact val_sub_le hint.1 (val_one_le i j w)
  exact fun i j => ⟨(inHat_one_iff _).2 fun w => (key w i j).1, (inHat_one_iff _).2 fun w => (key w i j).2.1,
    fun w => (key w i j).2.2⟩

end GlobalTheory.CosetOrth.Cong
end
end

section

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

noncomputable section

open scoped TensorProduct Matrix

namespace GlobalTheory.CosetOrth

section Local

open GlobalTheory.AdelicU GlobalTheory.LFun

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem valued_toCompl_le_one {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v)
    {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) : Valued.v (toCompl h y) ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 <|
    intLoc_induction (p := fun y => toCompl h y ∈ w.adicCompletionIntegers E)
      (fun _ ha x => mul_mem (complMap_mem h ha) (GlobalTheory.AdeleBaseChange.algebraMap_int_mem x w))
      (by rw [map_zero]; exact zero_mem _) (fun _ _ h h' => by rw [map_add]; exact add_mem h h')
      (fun _ h => by rw [map_neg]; exact neg_mem h) hy

theorem map_evalV_map_sndA (v : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) =
      Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a e => rfl
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

end Local

variable {D : D7}

theorem valued_finMat_finStd_le_one (V : HSp D) (hG : V.gram = 1) (k : GA D V)
    (w : HeightOneSpectrum (𝓞 D.host.E))
    (hk : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (w.under (𝓞 D.host.F)) k ∈
      GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (stdLat V) (w.under (𝓞 D.host.F))) (i j : Fin V.rank) :
    Valued.v (finMat (GlobalTheory.BotClassDict.finStd V hG k) i j w) ≤ 1 := by
  have hL : stdLat V = GlobalTheory.AdelicU.stdLattice D.host.E V.rank := by
    ext x
    exact ⟨fun h i _ => Submodule.mem_one.1 (h i trivial), fun h i _ => Submodule.mem_one.2 (h i trivial)⟩
  rw [hL] at hk
  have h1 := (GlobalTheory.AdelicU.mem_stabLoc_stdLattice_iff.1 hk).1 i j
  have e : finMat (GlobalTheory.BotClassDict.finStd V hG k) i j =
      GlobalTheory.LFun.finAdEquiv D.host.F D.host.E ((finHom V k).1 i j) := by
    rw [← GlobalTheory.BotClassDict.toAfE_finStd V hG, GlobalTheory.BotClassDict.finAdEquiv_toAfE]
    rfl
  rw [e, GlobalTheory.LFun.finAdEquiv_apply rfl]
  refine valued_toCompl_le_one rfl ?_
  have e2 := map_evalV_map_sndA (w.under (𝓞 D.host.F)) ((matHom V k).1 i j)
  exact e2 ▸ h1

end GlobalTheory.CosetOrth

theorem GlobalTheory.CosetOrth.valued_finMat_le_one_of_mem_openOff : ∀ {D : D7} (V : HSp D) (g : GA D V) (y : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank) (Sf : Finset (FinPl D)), V.gram = 1 →
  GlobalTheory.BotFormula.IsFinPt V g y → g ∈ openOff V (stdLat V) Sf →
  ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ Sf → ∀ i j,
    Valued.v (finMat y i j w) ≤ 1 ∧ Valued.v (finMat y⁻¹ i j w) ≤ 1 := by
  intro D V g y Sf hG hy hg w hw i j
  have hfy := GlobalTheory.BotClassDict.finStd_of_isFinPt V hG hy
  subst hfy
  have h := hg _ hw
  refine ⟨GlobalTheory.CosetOrth.valued_finMat_finStd_le_one V hG g w h i j, ?_⟩
  rw [← map_inv]
  refine GlobalTheory.CosetOrth.valued_finMat_finStd_le_one V hG g⁻¹ w ?_ i j
  have h' := inv_mem h
  rwa [← map_inv] at h'
end
end
