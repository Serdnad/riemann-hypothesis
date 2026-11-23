module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2561
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharEqOfFinitePartPowerInverse
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.AddDense
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2558

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


theorem _root_.GlobalTheory.T.heckeCharEq_of_finitePart_power_inverse : ∀ {D : D7} (χ : (AE D)ˣ →* Circle) {N : ℕ} (c : Formalism.MainNotions.StandardLatticesGL3.HeckeU D N) (e : ℤ) (ν : Formalism.L2.Host.HChar D.host.E),
  IsHeckeChar D χ → HasFinPart χ c (-e) → (∀ x, c.f x ^ e = (ν⁻¹).1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D x)) → ChrEq χ ν := by
  first | exact @GlobalTheory.NormRatio.ChrFin.chrEq_of_finPart | exact GlobalTheory.NormRatio.ChrFin.chrEq_of_finPart | (intros; apply GlobalTheory.NormRatio.ChrFin.chrEq_of_finPart <;> assumption)
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

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CosetOrth.Pairing

variable {D : D7}

theorem cA_fin_mul (e : D.host.E) (σ : AE D) (hσ : infPart D σ = 0) :
    cA D ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] e) * σ = incA D (star e) * σ := by
  refine sub_eq_zero.1 (GlobalTheory.LatVac.eq_zero_of_parts _ ?_ ?_)
  · rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, hσ, mul_zero, mul_zero, sub_self]
  · have e1 : finPart D (cA D ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] e)) = finPart D (incA D (star e)) := rfl
    rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, e1, sub_self]

theorem hO_of_gram_one (S T : HSp D) (hS : S.gram = 1) (hT : T.gram = 1) (x y : WO S T) :
    hO S T x y = ∑ a, ∑ c, cA D (y c a) * x c a := by
  unfold hO
  rw [hS, hT, inv_one]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_eq_single c]
    · rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one, one_mul, mul_one]
    · intro d _ hd
      rw [Matrix.one_apply_ne (Ne.symm hd), RingHom.map_zero, mul_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
    rw [Matrix.one_apply_ne (Ne.symm hb), RingHom.map_zero, zero_mul, zero_mul, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

def rowMat (S T : HSp D) (p : Fin T.rank) (f : Fin S.rank → AE D) : WO S T :=
  Matrix.of fun c a => if c = p then f a else 0

theorem hO_rowMat (S T : HSp D) (hS : S.gram = 1) (hT : T.gram = 1) (r : D.host.E) (o : ℕ) (j : Fin S.rank)
    (p : Fin T.rank) (hp : p.1 = o + j.1) (f : Fin S.rank → AE D) (hf : ∀ a, infPart D (f a) = 0) :
    hO S T (rowMat S T p f) (finPt (S := S) (T := T) rfl rfl r (unitBlock D o S.rank T.rank)) =
      -(incA D (star r⁻¹) * f j) := by
  rw [hO_of_gram_one S T hS hT]
  have h1 : ∀ a, (∑ c, cA D (finPt (S := S) (T := T) rfl rfl r (unitBlock D o S.rank T.rank) c a) * rowMat S T p f c a) =
      incA D (star (-(r⁻¹ * if p.1 = o + a.1 then 1 else 0))) * f a := by
    intro a
    rw [Finset.sum_eq_single p]
    · have : rowMat S T p f p a = f a := if_pos rfl
      rw [this]
      exact cA_fin_mul _ _ (hf a)
    · intro c _ hc
      have : rowMat S T p f c a = 0 := if_neg hc
      rw [this, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl fun a _ => h1 a, Finset.sum_eq_single j]
  · rw [if_pos hp, mul_one, star_neg, RingHom.map_neg, neg_mul]
  · intro a _ ha
    have : ¬ p.1 = o + a.1 := fun h => ha (Fin.ext (by omega))
    rw [if_neg this, mul_zero, neg_zero, star_zero, RingHom.map_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem actO_rowMat (S T : HSp D) (g : GA D S) (p : Fin T.rank) (i : Fin S.rank) (σ : AE D) :
    actO S T g 1 (rowMat S T p (Pi.single i σ)) = rowMat S T p fun a => σ * mt S g⁻¹ i a := by
  have h1 : mt T 1 = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [MonoidHom.map_one]; rfl
  unfold actO
  rw [h1, Matrix.one_mul]
  funext c a
  rw [Matrix.mul_apply]
  by_cases hc : c = p
  · have e : ∀ k, rowMat S T p (Pi.single i σ) c k = (Pi.single i σ : Fin S.rank → AE D) k := fun k => if_pos hc
    have e' : rowMat S T p (fun a => σ * mt S g⁻¹ i a) c a = σ * mt S g⁻¹ i a := if_pos hc
    rw [e', Finset.sum_eq_single i]
    · rw [e, Pi.single_eq_same]
    · intro k _ hk
      rw [e, Pi.single_eq_of_ne hk, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have e : ∀ k, rowMat S T p (Pi.single i σ) c k = 0 := fun k => if_neg hc
    have e' : rowMat S T p (fun a => σ * mt S g⁻¹ i a) c a = 0 := if_neg hc
    rw [e']
    exact Finset.sum_eq_zero fun k _ => by rw [e, zero_mul]

theorem two_smul_rowMat (S T : HSp D) (p : Fin T.rank) (i : Fin S.rank) (σ : AE D) :
    2 • rowMat S T p (Pi.single i σ) = rowMat S T p (Pi.single i (2 * σ)) := by
  funext c a
  show 2 • (if c = p then (Pi.single i σ : Fin S.rank → AE D) a else 0) =
    if c = p then (Pi.single i (2 * σ) : Fin S.rank → AE D) a else 0
  by_cases hc : c = p
  · rw [if_pos hc, if_pos hc]
    by_cases ha : a = i
    · rw [ha, Pi.single_eq_same, Pi.single_eq_same, two_nsmul, two_mul]
    · rw [Pi.single_eq_of_ne ha, Pi.single_eq_of_ne ha, nsmul_zero]
  · rw [if_neg hc, if_neg hc, nsmul_zero]

theorem hatPt_rowMat (S T : HSp D) (r : D.host.E) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (p : Fin T.rank)
    (f : Fin S.rank → AE D) (h0 : ∀ a, infPart D (f a) = 0) (h1 : ∀ a, InHat I (algebraMap D.host.E (FA D) r * fe D (f a))) :
    HatPt r I (rowMat S T p f) := by
  refine ⟨?_, fun c a => ?_⟩
  · funext c a
    show infPart D (if c = p then f a else 0) = 0
    split_ifs
    · exact h0 a
    · exact RingHom.map_zero _
  · show InHat I (algebraMap D.host.E (FA D) r * fe D (if c = p then f a else 0))
    split_ifs
    · exact h1 a
    · rw [RingHom.map_zero, mul_zero]; exact inHat_zero I

theorem units_mul_relation_rearrange_commRing {R : Type} [CommRing R] (x y s a b : R) : x * (y * (s * (a - b))) = x * -(y * (s * b)) + -(x * -(y * (s * a))) := by
  ring

theorem addChar_linearMap_neg_add_eq_one {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (ψ : AddChar R ℂ) (t : M →ₗ[R] R) (A B : M)
    (h : ψ (t A) = ψ (t B)) : ψ (t (B + -A)) = 1 := by
  rw [map_add (f := _), map_neg, AddChar.map_add_eq_mul, ← h, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]

theorem symplO_rowMat (S T : HSp D) (hS : S.gram = 1) (hT : T.gram = 1) (r : D.host.E) (o : ℕ) (j : Fin S.rank)
    (p : Fin T.rank) (hp : p.1 = o + j.1) (f : Fin S.rank → AE D) (hf : ∀ a, infPart D (f a) = 0) :
    symplO S T (rowMat S T p f) (finPt (S := S) (T := T) rfl rfl r (unitBlock D o S.rank T.rank)) =
      Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * -(incA D (star r⁻¹) * f j)) :=
  congrArg (fun z => Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * z)) (hO_rowMat S T hS hT r o j p hp f hf)

theorem single_inf {n : ℕ} (i : Fin n) (s : AE D) (hs : infPart D s = 0) (a : Fin n) :
    infPart D ((Pi.single i s : Fin n → AE D) a) = 0 := by
  by_cases ha : a = i
  · rw [ha, Pi.single_eq_same]; exact hs
  · rw [Pi.single_eq_of_ne ha]; exact RingHom.map_zero _

theorem hatPt_single (S T : HSp D) (r : D.host.E) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (p : Fin T.rank)
    (i : Fin S.rank) (σ : AE D) (hσ : infPart D σ = 0) (h1 : InHat I (algebraMap D.host.E (FA D) r * fe D σ)) :
    HatPt r I (rowMat S T p (Pi.single i σ)) :=
  hatPt_rowMat S T r I p _ (single_inf i σ hσ) fun a => by
    by_cases ha : a = i
    · rw [ha, Pi.single_eq_same]; exact h1
    · rw [Pi.single_eq_of_ne ha, RingHom.map_zero, mul_zero]; exact inHat_zero I

theorem hatPt_act (S T : HSp D) (r : D.host.E) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (p : Fin T.rank) (g : GA D S)
    (i : Fin S.rank) (σ : AE D) (hσ : infPart D σ = 0)
    (h2 : ∀ k, InHat I (algebraMap D.host.E (FA D) r * fe D σ * fe D (mt S g⁻¹ i k))) :
    HatPt r I (actO S T g 1 (rowMat S T p (Pi.single i σ))) := by
  rw [actO_rowMat]
  refine hatPt_rowMat S T r I p _ (fun a => by rw [RingHom.map_mul, hσ, zero_mul]) fun a => ?_
  rw [RingHom.map_mul, ← mul_assoc]; exact h2 a

theorem single_eq_mul_one {R : Type} [CommRing R] {n : ℕ} (i j : Fin n) (s : R) :
    (Pi.single i s : Fin n → R) j = s * (1 : Matrix (Fin n) (Fin n) R) i j := by
  by_cases ha : j = i
  · rw [ha, Pi.single_eq_same, Matrix.one_apply_eq, mul_one]
  · rw [Pi.single_eq_of_ne ha, Matrix.one_apply_ne (Ne.symm ha), mul_zero]

theorem degree_lower_bound_of_rank_split {R M : Type} [CommRing R] [CommRing M] [Algebra R M] (ψ : AddChar R ℂ) {n : ℕ} (x y s : M) (i j : Fin n)
    (N : Matrix (Fin n) (Fin n) M)
    (h : ψ (Algebra.trace R M (x * -(y * (Pi.single i s : Fin n → M) j))) = ψ (Algebra.trace R M (x * -(y * (s * N i j))))) :
    ψ (Algebra.trace R M (x * (y * (s * (1 - N) i j)))) = 1 := by
  rw [single_eq_mul_one] at h
  rw [Matrix.sub_apply, units_mul_relation_rearrange_commRing]
  exact addChar_linearMap_neg_add_eq_one ψ _ _ _ h

theorem char_trace_eq_one : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (r : D.host.E) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
  (o : ℕ) (g : GA D S), S.gram = 1 → T.gram = 1 → o + S.rank ≤ T.rank →
  (∀ u : WO S T, HatPt r I u → HatPt r I (actO S T g 1 u) →
    ψ (symplO S T (2 • u) (finPt (S := S) (T := T) rfl rfl r (unitBlock D o S.rank T.rank))) =
      ψ (symplO S T (actO S T g 1 (2 • u)) (finPt (S := S) (T := T) rfl rfl r (unitBlock D o S.rank T.rank)))) →
  ∀ (σ : AE D) (i j : Fin S.rank), infPart D σ = 0 → InHat I (algebraMap D.host.E (FA D) r * fe D σ) →
  (∀ k, InHat I (algebraMap D.host.E (FA D) r * fe D σ * fe D (mt S g⁻¹ i k))) →
  ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (incA D (star r⁻¹) * (2 * σ * (1 - mt S g⁻¹) i j)))) = 1 := by
  intro D ψ S T r I o g hS hT ho H σ i j hσ h1 h2
  obtain ⟨p, hp⟩ : ∃ p : Fin T.rank, p.1 = o + j.1 := ⟨⟨o + j.1, by have := j.2; omega⟩, rfl⟩
  have h2σ : infPart D (2 * σ) = 0 := by rw [RingHom.map_mul, hσ, mul_zero]
  have key := H (rowMat S T p (Pi.single i σ)) (hatPt_single S T r I p i σ hσ h1) (hatPt_act S T r I p g i σ hσ h2)
  rw [two_smul_rowMat, actO_rowMat] at key
  have a1 := symplO_rowMat S T hS hT r o j p hp _ (single_inf i _ h2σ)
  have a2 := symplO_rowMat S T hS hT r o j p hp (fun a => 2 * σ * mt S g⁻¹ i a)
    (fun a => by rw [RingHom.map_mul, h2σ, zero_mul])
  exact degree_lower_bound_of_rank_split ψ _ _ _ i j _ ((congrArg ψ a1).symm.trans (key.trans (congrArg ψ a2)))

end GlobalTheory.CosetOrth.Pairing
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

namespace GlobalTheory.CosetOrthDens

section General

variable {E : Type} [Field E] [NumberField E]

theorem inHat_algebraMap_iff {I : FractionalIdeal (𝓞 E)⁰ E} (hI : I ≠ 0) (x : E) :
    InHat I (algebraMap E (FiniteAdeleRing (𝓞 E) E) x) ↔ x ∈ I :=
  (GlobalTheory.Idele.mem_adelicIdeal_iff hI).symm.trans (GlobalTheory.Idele.algebraMap_mem_adelicIdeal hI x)

theorem isOpen_inHat_one : IsOpen {x : FiniteAdeleRing (𝓞 E) E | InHat 1 x} := by
  have h := RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (A := fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) fun v => Valued.isOpen_valuationSubring _
  have e : {x : FiniteAdeleRing (𝓞 E) E | InHat 1 x} =
      {x : FiniteAdeleRing (𝓞 E) E | ∀ v, x v ∈ (v.adicCompletionIntegers E : Set (v.adicCompletion E))} := by
    ext x
    exact inHat_one_iff x
  rw [e]
  exact h

theorem isOpen_inHat {I : FractionalIdeal (𝓞 E)⁰ E} (hI : I ≠ 0) : IsOpen {x : FiniteAdeleRing (𝓞 E) E | InHat I x} := by
  obtain ⟨c, hc0, hc⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger hI
  set a : E := algebraMap (𝓞 E) E c with ha
  have ha0 : a ≠ 0 := by simpa [ha] using hc0
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hcont : Continuous fun x : FiniteAdeleRing (𝓞 E) E => (x - y) * algebraMap E (FiniteAdeleRing (𝓞 E) E) a⁻¹ :=
    (continuous_id.sub continuous_const).mul continuous_const
  refine Filter.mem_of_superset ((isOpen_inHat_one.preimage hcont).mem_nhds ?_) fun x hx => ?_
  · show InHat 1 ((y - y) * _)
    rw [sub_self, zero_mul]
    exact inHat_zero 1
  · have h1 := InHat.mul_left hx ((inHat_algebraMap_iff hI a).2 hc)
    rw [mul_assoc, ← map_mul, inv_mul_cancel₀ ha0, map_one, mul_one] at h1
    have h2 := h1.add hy
    rwa [sub_add_cancel] at h2

end General

variable {D : D7}

def lift (D : D7) (s : FA D) : AE D :=
  GlobalTheory.LFun.extZero D.host.F D.host.E ((GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm s)

theorem continuous_lift : Continuous (lift D) :=
  GlobalTheory.LFun.continuous_extZero.comp GlobalTheory.LFun.continuous_finAdEquiv_symm

theorem infPart_lift (s : FA D) : infPart D (lift D s) = 0 := GlobalTheory.LFun.infTens_extZero _

theorem fe_lift (s : FA D) : fe D (lift D s) = s := by
  have : finPart D (lift D s) = (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm s := GlobalTheory.LFun.finTens_extZero _
  rw [fe_apply, this, RingEquiv.apply_symm_apply]

theorem lift_fe {x : AE D} (hx : infPart D x = 0) : lift D (fe D x) = x := by
  refine sub_eq_zero.1 (GlobalTheory.LatVac.eq_zero_of_parts _ ?_ ?_)
  · rw [RingHom.map_sub, infPart_lift, hx, sub_self]
  · apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
    rw [map_zero, ← fe_apply, map_sub, fe_lift, sub_self]

theorem lift_algebraMap (γ : D.host.E) :
    lift D (algebraMap D.host.E (FA D) γ) = pairA D.host.F 0 1 ⊗ₜ[D.host.F] γ := by
  have h1 : infPart D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] γ) = 0 := by
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] γ = 0
    exact TensorProduct.zero_tmul _ _
  have h2 : fe D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] γ) = algebraMap D.host.E (FA D) γ := by
    show GlobalTheory.LFun.toFinAd D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] γ) = _
    rw [GlobalTheory.LFun.toFinAd_tmul, map_one, one_mul]
  rw [← h2, lift_fe h1]

theorem exists_finPt_sub_mem : ∀ {D : D7} (S T : HSp D) (r : D.host.E) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), r ≠ 0 → I ≠ 0 →
  ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ u : WO S T, HatPt r I u →
  ∃ z : Matrix (Fin T.rank) (Fin S.rank) D.host.E, (∀ i j, z i j ∈ I) ∧ u - finPt (S := S) (T := T) rfl rfl r z ∈ U := by
  intro D S T r I hr hI U hU u hu
  haveI hg : IsTopologicalAddGroup (WO S T) := inferInstance
  haveI : ContinuousSub (WO S T) := IsTopologicalAddGroup.to_continuousSub
  let Φ : (Fin T.rank → Fin S.rank → FA D) → WO S T := fun y =>
    Matrix.of fun i j => lift D (algebraMap D.host.E (FA D) r⁻¹ * y i j)
  have hΦ : Continuous Φ := continuous_matrix fun i j =>
    continuous_lift.comp (continuous_const.mul ((continuous_apply j).comp (continuous_apply i)))
  have hd : DenseRange (Pi.map fun (_ : Fin T.rank) => Pi.map fun (_ : Fin S.rank) => algebraMap D.host.E (FA D)) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ =>
      PI.UnipApproxD.IntegersDenseFiniteAdeles.denseRange (R := 𝓞 D.host.E) (K := D.host.E)
  have hO : IsOpen ({y | u - Φ y ∈ U} ∩ ⋂ i, ⋂ j, {y : Fin T.rank → Fin S.rank → FA D | InHat I (y i j)}) :=
    (hU.preimage (continuous_const.sub hΦ)).inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (isOpen_inHat hI).preimage (f := fun y : Fin T.rank → Fin S.rank → FA D => y i j)
        ((continuous_apply j).comp (continuous_apply i)))
  have h0 : Φ (fun i j => algebraMap D.host.E (FA D) r * fe D (u i j)) = u := by
    funext i j
    show lift D (algebraMap D.host.E (FA D) r⁻¹ * (algebraMap D.host.E (FA D) r * fe D (u i j))) = u i j
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hr, map_one, one_mul]
    exact lift_fe (congrFun (congrFun hu.1 i) j)
  obtain ⟨z, hz1, hz2⟩ := hd.exists_mem_open hO ⟨fun i j => algebraMap D.host.E (FA D) r * fe D (u i j), by
    show u - Φ _ ∈ U
    rw [h0, sub_self]
    exact U.zero_mem, Set.mem_iInter.2 fun i => Set.mem_iInter.2 fun j => hu.2 i j⟩
  refine ⟨Matrix.of fun i j => -z i j, fun i j => ?_, ?_⟩
  · have : z i j ∈ I := (inHat_algebraMap_iff hI _).1 (Set.mem_iInter.1 (Set.mem_iInter.1 hz2 i) j)
    exact (I : Submodule (𝓞 D.host.E) D.host.E).neg_mem this
  · have e : finPt (S := S) (T := T) rfl rfl r (Matrix.of fun i j => -z i j) =
        Φ (Pi.map (fun (_ : Fin T.rank) => Pi.map fun (_ : Fin S.rank) => algebraMap D.host.E (FA D)) z) := by
      funext i j
      show pairA D.host.F 0 1 ⊗ₜ[D.host.F] (-(r⁻¹ * -z i j)) =
        lift D (algebraMap D.host.E (FA D) r⁻¹ * algebraMap D.host.E (FA D) (z i j))
      rw [← map_mul, lift_algebraMap, mul_neg, neg_neg]
    rw [e]
    exact hz1

end GlobalTheory.CosetOrthDens
end
end

section

open GlobalTheory.SqTop

theorem _root_.GlobalTheory.T.bottomPairs_exist_baseTuple : (∀ D, GlobalTheory.NormSum.Inp D) → BotEx := by
  first | exact @GlobalTheory.SqTop.botEx_holds | exact GlobalTheory.SqTop.botEx_holds | (intros; apply GlobalTheory.SqTop.botEx_holds <;> assumption)
end

section

open GlobalTheory.SqTop

theorem _root_.GlobalTheory.T.bottomPairsExistEveryTuple_of_cmThetaHypotheses : (∀ D, GlobalTheory.NormSum.Inp D) → BotExT := by
  first | exact @GlobalTheory.SqTop.botExT_holds | exact GlobalTheory.SqTop.botExT_holds | (intros; apply GlobalTheory.SqTop.botExT_holds <;> assumption)
end
