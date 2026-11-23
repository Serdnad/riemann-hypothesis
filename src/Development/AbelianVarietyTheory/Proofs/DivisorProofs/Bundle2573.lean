module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingNormSqEqVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingSphericalOffModulus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLineReadingAdelicNormEqTorusMeanSquare
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle311
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatIn

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


theorem _root_.GlobalTheory.T.thetaCosetIndicatorReading_normSq_eq_absNorm_inv_mul_vacuum : ∀ {D : D7} {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (X : Data P) (r : D.host.E), IsExact P X r →
  ∀ (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)) (o : ℕ), GoodMod D 𝔪 Sf →
  ∀ LB : Lat X.B, IsSelfDualC X.B LB →
    (∀ z : Matrix (Fin P.d) (Fin P.a) D.host.E, z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D P.a) (Formalism.MainNotions.StandardLatticesGL3.stdL D P.d) ↔
      finPt X.rkA X.rkB r z ∈ latO X.A X.B (stdLat X.A) LB fun _ => True) →
  ∀ f₀ φ, Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r P.e0 f₀ → IsSphOff X.ψ X.A X.B (stdLat X.A) LB ∅ f₀ →
    Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r (cosetVec P 𝔪 o) φ →
  ∀ (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)), IsCovolOne (ratL X.B X.A) ν 𝓕 →
    ip X.A X.B ν 𝓕 φ φ = ((Ideal.absNorm 𝔪 : ℂ) ^ (P.a * P.d))⁻¹ * ip X.A X.B ν 𝓕 f₀ f₀ := by
  first | exact @GlobalTheory.NormRatio.CosetNorm.ip_cosetVec | exact GlobalTheory.NormRatio.CosetNorm.ip_cosetVec | (intros; apply GlobalTheory.NormRatio.CosetNorm.ip_cosetVec <;> assumption)
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


theorem _root_.GlobalTheory.T.thetaCosetIndicatorReading_spherical_off_modulus : ∀ {D : D7} {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (X : Data P) (r : D.host.E), IsExact P X r →
  ∀ (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)) (o : ℕ), GoodMod D 𝔪 Sf →
  ∀ LB : Lat X.B, IsSelfDualC X.B LB →
    (∀ z : Matrix (Fin P.d) (Fin P.a) D.host.E, z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D P.a) (Formalism.MainNotions.StandardLatticesGL3.stdL D P.d) ↔
      finPt X.rkA X.rkB r z ∈ latO X.A X.B (stdLat X.A) LB fun _ => True) →
  ∀ f₀ φ, Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r P.e0 f₀ → IsSphOff X.ψ X.A X.B (stdLat X.A) LB ∅ f₀ →
    Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r (cosetVec P 𝔪 o) φ →
    IsSphOff X.ψ X.A X.B (stdLat X.A) LB Sf φ := by
  first | exact @GlobalTheory.NormRatio.SphCoset.sph | exact GlobalTheory.NormRatio.SphCoset.sph | (intros; apply GlobalTheory.NormRatio.SphCoset.sph <;> assumption)
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


theorem _root_.GlobalTheory.T.thetaLineReading_adelicNorm_eq_torusMeanSquare : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (δ : ℂ) (r : D.host.E), Setup ψ θ S T ⊤ δ r →
  ∀ LT : Lat T, IsSelfDualC T LT →
    (∀ z : Matrix (Fin d) (Fin a) D.host.E, z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d) ↔
      finPt hS hT r z ∈ latO S T (stdLat S) LT fun _ => True) →
  ∀ e0 ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D ⊤ δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d), ∀ f₀,
    Reads ψ θ hS hT ⊤ δ r e0 f₀ → IsSphOff ψ S T (stdLat S) LT ∅ f₀ →
  ∀ (ν : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) ν 𝓕 →
    ip S T ν 𝓕 f₀ f₀ = (Formalism.MainNotions.TaylorLogMetric.normSq D (Formalism.MainNotions.TaylorLogMetric.tor0 D ⊤ δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (Formalism.MainNotions.TaylorLogMetric.tor0 D ⊤ δ) a d) e0 : ℝ) := by
  first | exact @GlobalTheory.VacNormMean.ip_eq_normSq | exact GlobalTheory.VacNormMean.ip_eq_normSq | (intros; apply GlobalTheory.VacNormMean.ip_eq_normSq <;> assumption)
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

open scoped TensorProduct

namespace GlobalTheory.CosetOrth.LatInt

theorem exists_pow_mem (D : D7) : ∃ k : ℕ, (((D.host.QS * D.host.q) ^ k : ℕ) : 𝓞 D.host.E) ∈ D.host.𝔟 := by
  have hb := ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.bb_ne_bot D
  have h : ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∈ D.host.𝔟.radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro J ⟨hJ, hp⟩
    have hne : J ≠ ⊥ := fun e => hb (le_bot_iff.1 (e ▸ hJ))
    exact GlobalTheory.HalfCompare.two_q_mem (P := ⟨J, hp, hne⟩) (Ideal.dvd_iff_le.2 hJ)
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by rw [Nat.cast_pow]; exact hk⟩

theorem homL_entry {D : D7} {N N' : ℕ} {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ Formalism.MainNotions.TaylorLogMetric.homL D (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) (i : Fin N') (j : Fin N) :
    A i j ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    have h1 : (Pi.single j (1 : D.host.E) : Fin N → D.host.E) ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N := by
      intro l _
      by_cases h : l = j
      · subst h
        rw [Pi.single_eq_same]
        exact Submodule.mem_one.2 ⟨1, map_one _⟩
      · rw [Pi.single_eq_of_ne h]
        exact zero_mem _
    have h2 := hA _ h1 i trivial
    rw [Matrix.mulVec_single_one] at h2
    exact h2
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

theorem YYl_entry {D : D7} {N N' : ℕ} {B : Matrix (Fin N') (Fin N) D.host.E}
    (hB : B ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) (i : Fin N') (j : Fin N) :
    B i j ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
  induction hB using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hB
    obtain ⟨c, hc⟩ := Submodule.mem_one.1 (homL_entry hA i j)
    have : (a • A) i j = c • a := by
      rw [Matrix.smul_apply, smul_eq_mul, ← hc, Algebra.smul_def, mul_comm]
    rw [this]
    exact Submodule.smul_mem _ c ha
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

theorem mul_int {D : D7} {n : 𝓞 D.host.E} (hn : n ∈ D.host.𝔟) {x : D.host.E}
    (hx : x ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) :
    ∃ b : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E b = algebraMap (𝓞 D.host.E) D.host.E n * x := by
  have hb := ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.bb_ne_bot D
  have h1 : algebraMap (𝓞 D.host.E) D.host.E n * x ∈
      (D.host.𝔟 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) * D.host.AA0 :=
    FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hn) hx
  rw [Formalism.BasicNotions.Host.AA0, mul_inv_cancel₀ (FractionalIdeal.coeIdeal_ne_zero.2 hb)] at h1
  exact (FractionalIdeal.mem_one_iff _).1 h1

theorem inHat_tmul {D : D7} {α : Af D.host.F} (hα : α ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F) (c x : D.host.E) (b : 𝓞 D.host.E)
    (hb : algebraMap (𝓞 D.host.E) D.host.E b = c * x) :
    InHat 1 (algebraMap D.host.E (FA D) c * fe D (pairA D.host.F 0 α ⊗ₜ[D.host.F] x)) := by
  have e : fe D (pairA D.host.F 0 α ⊗ₜ[D.host.F] x) =
      GlobalTheory.AdeleBaseChange.adMap D.host.F D.host.E α * algebraMap D.host.E (FA D) x := rfl
  rw [e, mul_left_comm, ← map_mul, ← hb]
  refine InHat.mul_left ((inHat_one_iff _).2 fun w => ?_) ((inHat_one_iff _).2 fun w => ?_)
  · exact GlobalTheory.AdeleBaseChange.adMap_int (F := D.host.F) (E := D.host.E) hα w
  · change Valued.v ((algebraMap (𝓞 D.host.E) D.host.E b : D.host.E) : w.adicCompletion D.host.E) ≤ 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact w.valuation_le_one b

theorem exists_hatPt_of_mem_latO : ∀ {D : D7} (S T : HSp D) (r : D.host.E) (LB : Lat T), r ≠ 0 →
  (∀ z : Matrix (Fin T.rank) (Fin S.rank) D.host.E, finPt (S := S) (T := T) rfl rfl r z ∈ (latO S T (stdLat S) LB fun _ => True) →
    z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D S.rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D T.rank)) →
  ∃ k : ℕ, ∀ u ∈ (latO S T (stdLat S) LB fun _ => True), HatPt ((((D.host.QS * D.host.q) ^ k : ℕ) : D.host.E) * r) 1 u := by
  intro D S T r LB hr hz
  obtain ⟨k, hk⟩ := exists_pow_mem D
  refine ⟨k, fun u hu => ⟨Matrix.ext fun i j => GlobalTheory.LatVac.infPart_of_mem hu i j, fun i j => ?_⟩⟩
  refine GlobalTheory.LatVac.latO_induction (p := fun u => InHat 1
    (algebraMap D.host.E (FA D) ((((D.host.QS * D.host.q) ^ k : ℕ) : D.host.E) * r) * fe D (u i j))) ?_ ?_ ?_ ?_ hu
  · intro α hα M hM
    have h1 := GlobalTheory.LatVac.finTens_mem_latO (GlobalTheory.LatVac.one_mem_intAf _) hM
    have e : finPt (S := S) (T := T) rfl rfl r (-r • M) = GlobalTheory.LatVac.finTens 1 M := by
      have : (Matrix.of fun i j => -(r⁻¹ * (-r • M) (Fin.cast rfl i) (Fin.cast rfl j))) = M := by
        ext i j
        simp [hr]
      unfold finPt
      rw [this]
      rfl
    obtain ⟨b, hb⟩ := mul_int hk (YYl_entry (hz _ (e ▸ h1)) i j)
    refine inHat_tmul hα _ _ (-b) ?_
    rw [map_neg, hb, map_natCast, Matrix.smul_apply, smul_eq_mul]
    ring
  · rw [Matrix.zero_apply, map_zero, mul_zero]
    exact inHat_zero _
  · intro x y hx hy
    rw [Matrix.add_apply, map_add (f := _), mul_add]
    exact hx.add hy
  · intro x hx
    rw [Matrix.neg_apply, map_neg, mul_neg]
    exact hx.neg

end GlobalTheory.CosetOrth.LatInt
end
end
